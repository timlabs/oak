require_relative 'parser.rb'
require_relative 'commands.rb'
require_relative 'utilities.rb'

class Proof
	def self.process input, is_filename = false, options = {}
		instance_options = options.select {|k,v| k != :wait}
		proof = Proof.new instance_options
		tracker = Tracker.new
		my_options = {:tracker => tracker, :wait_on_unknown => options[:wait]}
		exited = include proof, input, is_filename, my_options

		message = case proof.scopes.last
			when :suppose then 'error at end of input: active supposition'
			when :now then 'error at end of input: active "now" block'
			when Array then 'error at end of input: active "proof" block'
			when :assume then 'error at end of input: active assume block'
		end
		if message
			puts message
			raise ProofException, message
		end

		if exited
			puts "all lines accepted prior to exit"
		else
			puts "all lines accepted"
		end

		if not tracker.assumptions.empty?
			print_assumptions tracker
		else
			print_axioms tracker
			if exited
				puts 'proof incomplete due to exit'
			else
				puts 'proof successful!'
			end
		end
	end

	def self.include proof, input, is_path = false, options = {}
		include_internal proof, input, is_path, options, nil
	end

	def self.include_internal proof, input, is_path, options, include_line
		tracker = options[:tracker]
		if is_path
			dirname = File.dirname input
			filename = File.basename input
			begin
				input = File.read input
			rescue
				puts "error: could not open file \"#{input}\""
				raise ProofException
			end
		else
			filename = ''
		end
		begin
			tracker.begin_file filename, include_line if tracker
			wrapper = WordWrapper.new ' ', 2
			line_number = nil # external scope, for error reporting
			from_include = false
			exited = false
			wrapper.print "#{filename}: processing line "
			Parser.new.parse_each(input) {|sentence, action, content, reasons, label,
																		 fileline|
				next if action == :empty
				line_number = fileline
				wrapper.print "#{line_number} "
				if action == :exit
					wrapper.puts
					wrapper.puts "exit at line #{line_number}: skipping remaining lines"
					exited = true
					break
				end
				if content.is_a? Content
					is_schema = [:assume_schema, :axiom_schema].include? action
					content = process_content content, proof.theses[-1], is_schema
				end
				# puts "content for line #{fileline} is: #{content.inspect}"
				id = {:label => label, :filename => filename, :fileline => fileline}
				result = case action
					when :include then
						# include relative to path of current proof file
						content = File.expand_path content, dirname if is_path
						wrapper.puts
						from_include = true
						exited = include_internal proof, content, :is_filename, options,
																			fileline
						from_include = false
						break if exited
						wrapper.print "#{filename}: processing line "
					when :suppose then proof.suppose content, id
					when :now then proof.now
					when :end then proof.end_block
					when :assume
						proof.assume content, id
						tracker.assume filename, fileline if tracker
					when :assume_schema
						proof.assume_schema content, id
						tracker.assume filename, fileline if tracker
					when :axiom
						proof.axiom content, id
						tracker.axiom filename if tracker
					when :axiom_schema
						proof.axiom_schema content, id
						tracker.axiom filename if tracker
					when :derive then proof.derive content, reasons, id
					when :so then proof.so content, reasons, id
					when :so_assume
						proof.so_assume content, id
						tracker.assume filename, fileline if tracker
					when :proof then proof.proof content, id
					when :begin_assume
						proof.begin_assume
						tracker.begin_assume fileline if tracker
					when :end_assume
						proof.end_assume
						tracker.end_assume fileline if tracker
					else raise "unrecognized action #{action}"
				end
				if result.is_a? InfoException
					wrapper.puts; wrapper.puts
					wrapper.puts "line #{line_number}: #{result}"
					wrapper.puts
					wrapper.print "#{filename}: processing line "
				end
			}
			tracker.end_file if tracker
			wrapper.puts unless exited
			exited
		rescue ProofException => e
			message = case e # update the message (but don't print it)
				when ParseException then e.message
				when DeriveException then e.message line_number
				else "error at line #{line_number}: #{e}"
			end
			if not from_include # already done otherwise
				wrapper.puts e.line_number if e.is_a? ParseException
				wrapper.puts if not e.is_a? ParseException
				wrapper.puts message
				if e.is_a? DeriveException and e.result == :unknown and
					 options[:wait_on_unknown]
					wrapper.puts "line #{line_number}: -w option: checking validity " \
											 "without work limit (may never finish, press ctrl-c " \
											 "to abort)"
					result = ExternalProver.valid_e? e.checked, true
					message = case result
						when :invalid then 'invalid derivation'
						when Numeric then "valid derivation, but took #{result.round 1} " \
															"times the work limit"
						when :unknown then 'eprover gave up'
						else raise '' # new exception
					end
					wrapper.puts "line #{line_number}: -w option: #{message}"
					wrapper.puts 'proof unsuccessful'
				end
			end
			raise e, message # preserve exception class
		end
	end

	def self.print_assumptions tracker
		# assumption locations
		wrapper = WordWrapper.new ',', 2
		tracker.assumptions.each {|filename, assumptions|
			if assumptions.size == 1 and assumptions[0].is_a? Numeric
				wrapper.print "#{filename}: assumption on line "
			else
				wrapper.print "#{filename}: assumptions on lines "
			end
			values = assumptions.collect {|x| x.is_a?(Numeric) ? x : x.join('-')}
			wrapper.puts values.join ', '
		}
		# assumption counts
		blocks, lines = 0, 0
		tracker.assumptions.values.each {|assumptions|
			assumptions.each {|x|
				if x.is_a? Numeric
					lines += 1
				elsif x.first.is_a? Numeric # to skip :start
					blocks += 1
				end
			}
		}
		counts = []
		counts << "#{blocks} assume block" if blocks == 1
		counts << "#{blocks} assume blocks" if blocks > 1
		counts << "#{lines} assumption" if lines == 1
		counts << "#{lines} assumptions" if lines > 1
		return if counts.empty?
		wrapper.puts "proof incomplete due to #{counts.join ' and '}"
	end

	def self.print_axioms tracker
		tracker.axioms.each {|filename, axiom_count|
			s = (axiom_count == 1 ? 'axiom' : 'axioms')
			puts "#{axiom_count} #{s} in #{filename}"
		}
	end

	def self.process_content content, thesis, is_schema
		if is_schema
			# free_variables and substitute don't work for schemas, so use contains?
			return content unless content.sentence.contains? 'thesis'
			raise ProofException, 'cannot use thesis in schema'
		elsif thesis
			if content.binding?
				if content.sentence.free_variables.include? 'thesis'
					raise ProofException, "cannot use thesis in binding"
				end
				intersect = content.binding.variables & thesis.sentence.free_variables
				conflict = intersect.first
				return content unless conflict
				raise ProofException, "cannot bind variable #{conflict}: part of thesis"
			else
				begin
					tree = substitute content.sentence, {'thesis' => thesis.sentence}
				rescue SubstituteException => e
					message = "cannot quantify variable #{e}: conflicts with thesis"
					raise ProofException, message
				end
				Content.new tree
			end
		elsif content.sentence.free_variables.include? 'thesis'
			raise ProofException, 'thesis used outside of proof block'
		else
			content
		end
	end

	private_class_method :include_internal, :process_content
end

class Tracker
	# keeps track of assumptions and axioms

	attr_reader :assumptions, :axioms

	def initialize
		@assumptions = Hash.new {|hash, key| hash[key] = []}
		@axioms = Hash.new 0

		@file_stack = []
		@assume_stack = []
	end

	def assume filename, fileline
		@assumptions[filename] << fileline if @assume_stack.empty?
	end

	def axiom filename
		@axioms[filename] += 1
	end

	def begin_assume fileline
		if @assume_stack.empty?
			@assume_stack << [@file_stack.last[0], fileline]
		else
			@assume_stack << :nested
		end
	end

	def begin_file filename, include_line
		@file_stack << [filename, include_line]
	end

	def end_file
		raise if @file_stack.empty? # nothing to end
		filename, line = @file_stack.pop
		return if @assume_stack.empty?
		if @assume_stack[0][0] == filename # assume began in or under this file
			@assumptions[filename] << [@assume_stack[0][1], :end]
			# make the assume begin at the include line in the file above
			@assume_stack[0] = [@file_stack.last[0], line] unless @file_stack.empty?
		else # assume began before this file
			@assumptions[filename] << [:start, :end]
		end
	end

	def end_assume fileline
		raise if @assume_stack.empty? # nothing to end
		if @assume_stack.last == :nested
			@assume_stack.pop
		else
			assume_filename, assume_line = @assume_stack.pop
			@file_stack.each_index.reverse_each {|i|
				stack_filename = @file_stack[i][0]
				# include line in this file
				include_line = (@file_stack[i+1] ? @file_stack[i+1][1] : fileline)
				if stack_filename != assume_filename # assume began before here
					@assumptions[stack_filename] << [:start, include_line]
				else # assume began here
					@assumptions[stack_filename] << [assume_line, include_line]
					break
				end
			}
		end
	end
end