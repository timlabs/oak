require_relative 'parser.rb'
require_relative 'commands.rb'
require_relative 'utilities.rb'

class Proof
	def self.process input, is_filename = false, options = {}
		proof = Proof.new options
		include proof, input, is_filename

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

		puts "all lines accepted"

		if proof.makes_assumptions?
			proof.print_assumptions
			puts 'proof incomplete due to assumptions'
		else
			proof.print_axioms
			puts 'proof successful!'
		end
	end

	def self.include proof, input, is_path = false
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
			wrapper = WordWrapper.new ' ', 2
			line_number = nil # external scope, for error reporting
			from_include = false
			wrapper.print "#{filename}: processing line "
			Parser.new.parse_each(input) {|sentence, action, content, reasons, label, fileline|
				next if action == :empty
				line_number = fileline
				wrapper.print "#{line_number} "
				if action == :exit
					wrapper.puts
					wrapper.print "exit at line #{line_number}: skipping remaining lines"
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
						include proof, content, :is_filename
						from_include = false
						wrapper.print "#{filename}: processing line "
					when :suppose then proof.suppose content, id
					when :now then proof.now
					when :end then proof.end_block
					when :assume then proof.assume content, id
					when :assume_schema then proof.assume_schema content, id
					when :axiom then proof.axiom content, id
					when :axiom_schema then proof.axiom_schema content, id
					when :derive then proof.derive content, reasons, id
					when :so then proof.so content, reasons, id
					when :so_assume then proof.so_assume content, id
					when :proof then proof.proof content, id
					when :begin_assume then proof.begin_assume id
					when :end_assume then proof.end_assume
					else raise "unrecognized action #{action}"
				end
				if result.is_a? InfoException
					wrapper.puts; wrapper.puts
					wrapper.puts "line #{line_number}: #{result}"
					wrapper.puts
					wrapper.print "#{filename}: processing line "
				end
			}
		rescue ProofException => e
			message = case e
				when ParseException then e.message
				when DeriveException then e.message line_number
				else "error at line #{line_number}: #{e}"
			end
			if not from_include # already printed otherwise
				wrapper.puts e.line_number if e.is_a? ParseException
				wrapper.puts if not e.is_a? ParseException
				wrapper.puts message
			end
			raise e, message # preserve exception class
		end
		puts
	end

	def self.process_content content, thesis, is_schema
		if is_schema
			# free_variables and substitute don't work for schemas, so use contains?
			return content unless content.sentence.contains? 'thesis'
			raise ProofException, 'cannot use thesis in schema'
		elsif thesis
			if content.binding?
				return content if not content.sentence.free_variables.include? 'thesis'
				raise ProofException, "cannot use thesis in binding"
			else
				begin
					tree = substitute content.sentence, {'thesis' => thesis.sentence}
				rescue SubstituteException => e
					raise ProofException, "cannot quantify variable #{e}: part of thesis"
				end
				Content.new tree
			end
		elsif content.sentence.free_variables.include? 'thesis'
			raise ProofException, 'thesis used outside of proof block'
		else
			content
		end
	end

	private_class_method :process_content
end