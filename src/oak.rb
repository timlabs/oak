if RUBY_VERSION < '2'
	puts "Oak requires Ruby version >= 2.0.  (You have Ruby #{RUBY_VERSION}.)"
	exit
end

require_relative 'parser.rb'
require_relative 'external prover.rb'
require_relative 'schema.rb'
require_relative 'utilities.rb'

class Proof
	class Line
		attr_reader :sentence, :reason, :suppositions, :bindings,
								:label, :filename, :fileline

		def initialize sentence, reason, suppositions, bindings, id
			@sentence, @reason = sentence, reason
			@suppositions, @bindings = suppositions, bindings
			@label, @filename, @fileline = id[:label], id[:filename], id[:fileline]
			sentence_string = @sentence.to_s.rstrip
			reason_string = @reason.to_s.rstrip
			if sentence_string.empty?
				raise ProofException, 'cannot add line with empty sentence' 
			end
			raise ProofException, 'cannot add line with empty reason' if reason_string.empty?
			illegal = ['%%', "\t", "\n"]
			found = illegal.find {|string|
				sentence_string.include?(string) or reason_string.include?(string)
			}
			if found
			  raise ProofException, "cannot add line containing illegal substring #{found.inspect}"
			end
		end

    def binding?
      not schema? and @sentence.operator == :for_some
    end
    
		def rows supposition_space = nil, sentence_space = nil, reason_space = nil
			rows = []
			suppositions, sentence, reason = supposition_string, @sentence.to_s.dup, @reason.to_s.dup
			if not supposition_space and not sentence_space and not reason_space
				supposition_space = [suppositions.size, 15].min
				remaining = 79 - supposition_space - 8 # 8 for two instances of ' %% '
				sentence_space = [sentence.size, remaining / 2].min
				reason_space = remaining - sentence_space
			end
			until suppositions.empty? and sentence.empty? and reason.empty?
				row = suppositions.slice! 0...supposition_space
				row << ' ' * (supposition_space - row.size) if row.size < supposition_space
				row << ' %% '
				pad = (sentence.size < sentence_space) ? ' ' * (sentence_space - sentence.size) : ''
				row << sentence.slice!(0...sentence_space) + pad + ' %% '
				row << reason.slice!(0...reason_space)
				rows << row
			end
			rows
		end

		def schema?
			@reason == :'assumption schema' or @reason == :'axiom schema'
		end

    def supposition?
      @reason == :supposition
    end
    
		def supposition_string
			@suppositions.collect {|supposition| supposition + 1}.sort.join ','
		end
	
		def to_s
			rows.join "\n"
		end
	end
end

class Proof
  class ScopeTree
    attr_reader :line, :branches
    
    def initialize line, branches, lines
      @line, @branches, @lines = line, branches, lines
    end
    
    def inspect level = 1
			text = @line ? @lines[@line].sentence.to_s : @line.inspect
  		@branches.inject(text) {|result, branch|
  	    result + "\n" + '  ' * level + branch.inspect(level + 1)
  		}
  	end
  end
end

### start of Proof class #################################################

class Proof
	def initialize
		@lines = []
		#@definitions = []
		@assumptions = []
		@assume_blocks = []
		@axioms = []
		@active_suppositions = []
		@active_bindings = {}
		@active_reason_sets = [[]]
		@scopes = []
		@theses = []
		@label_stack = [[]]
    @line_numbers_by_label = {}
		@inactive_labels = Set[]
	end

	def assume sentence, id = nil
		check_admission sentence
		@assumptions << @lines.size unless @scopes.include? :assume
		add sentence, :assumption, id
	end

	def assume_schema schema, id = nil
		if not @active_suppositions.empty?
			raise ProofException, '"assume schema" not allowed in supposition'
		end
		@assumptions << @lines.size unless @scopes.include? :assume
		add schema, :'assumption schema', id
	end

	def axiom_schema schema, id = nil
		message = case @scopes.last
			when :suppose then 'axiom schema not allowed in supposition'
			when :now then 'axiom schema not allowed in "now" block'
			when Array then 'axiom schema not allowed in "proof" block'
		end
		raise ProofException, message if message
		@axioms << @lines.size
		add schema, :'axiom schema', id
	end

	def axiom sentence, id = nil
		message = case @scopes.last
			when :suppose then 'axiom not allowed in supposition'
			when :now then 'axiom not allowed in "now" block'
			when Array then 'axiom not allowed in "proof" block'
		end
		raise ProofException, message if message
		check_admission sentence
		@axioms << @lines.size
		add sentence, :axiom, id
	end

	def begin_assume id
		@scopes << :assume
		@assume_blocks << id
	end

	def check_admission sentence
 		variables, body = read_binding sentence
		variables.each {|variable|
			@lines.each {|line|
				next if line.schema?
				free_variables = line.sentence.free_variables
				next unless (free_variables - line.bindings.keys).include? variable
				raise ProofException, "cannot bind #{variable}: already occurred as a constant"
			}
		}
		scopes = get_scopes
		still_active = @active_bindings.dup
		(variables & @active_bindings.keys).each {|variable|
			last_start = @active_bindings[variable]
			last_stop = scopes[@active_bindings[variable]]
			if not (@active_suppositions & (last_start..last_stop).to_a).empty?
				raise ProofException, "cannot bind #{variable}: previous binding would interleave active supposition"
			end
			still_active.delete_if {|v, i| i >= last_start and i <= last_stop}
		}
 		(sentence.free_variables - still_active.keys).each {|variable|
			if @lines.find {|line| line.bindings[variable]}
				if @active_bindings[variable]
					raise ProofException, "placement of variable #{variable} causes scope interleaving"
				else
					raise ProofException, "variable #{variable} is no longer in scope"
				end
			end
		}
=begin
		constants = sentence.free_variables - @active_bindings.keys
		intersection = constants & sentence.bound_variables
		if not intersection.empty?
			name = intersection[0] # pick one for the error message
			raise ProofException, "#{name} appears as both a variable and a constant"
		end

		# clear binding if :for_all or :for_some occurs in sentence?
=end
	end

	def derive sentence, reasons = [], id = nil
    return assume sentence, id if @scopes.include? :assume # assume block
		line_numbers = process_reasons reasons
		derive_internal sentence, line_numbers, id
	end

	def end_assume
		if not @scopes.include? :assume
			raise ProofException, 'no assume block to end'
		elsif @scopes[-1] == :suppose
			raise ProofException, 'assume block interleaves supposition'
		elsif @scopes[-1] == :now
			raise ProofException, 'assume block interleaves "now" block'
		elsif @scopes[-1].is_a? Array
			raise ProofException, 'assume block interleaves "proof" block'
		elsif @scopes[-1] != :assume
			raise
		end
		@scopes.pop
	end
	
	def end_block
		raise ProofException, 'nothing to end' if @scopes.empty?
		if @scopes[-1] == :assume
			raise ProofException, '"begin assume" must end with "end assume"'
		end
		last_scope = @scopes.pop
		last_reason_set = @active_reason_sets.pop
		last_thesis = @theses.pop
		if last_scope.is_a? Array # end of proof block
			@label_stack[-1].each {|label|
				@line_numbers_by_label.delete label
				@inactive_labels << label
			}
			@label_stack.pop
			content, id, lines_size_before = last_scope
			# delete any bindings made in the proof block
			@active_bindings.delete_if {|variable, line_number|
				line_number >= lines_size_before
			}
      if @scopes.include? :assume then assume content, id # assume block
      else derive_internal content, last_reason_set, id end
		else
			if last_scope == :suppose
				# delete any bindings made while this supposition was active
				supposition = @active_suppositions.last
				@active_bindings.delete_if {|variable, line_number|
					@lines[line_number].suppositions.include? supposition
				}
				@active_suppositions.pop
			end
			@active_reason_sets.last.concat last_reason_set
		end
	end

	def include input, is_path = false
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
				break if action == :exit
				line_number = fileline
				wrapper.print "#{line_number} "
				content = process_content content, @theses[-1] if content.is_a? Tree
				id = {:label => label, :filename => filename, :fileline => fileline}
				case action
					when :include then
						# include relative to path of current proof file
						content = File.expand_path content, dirname if is_path
						wrapper.puts
						from_include = true
						include content, :is_filename
						from_include = false
						wrapper.print "#{filename}: processing line "
					when :suppose then suppose content, id
					when :now then now
					when :end then end_block
					when :assume then assume content, id
					when :assume_schema then assume_schema content, id
					when :axiom then axiom content, id
					when :axiom_schema then axiom_schema content, id
					when :derive then derive content, reasons, id
					when :so then so content, reasons, id
					when :so_assume then so_assume content, id
					when :proof then proof content, id
					when :begin_assume then begin_assume id
					when :end_assume then end_assume
					else raise "unrecognized action #{action}"
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

	def now
		@scopes << :now
		@active_reason_sets << []
		@theses << @theses[-1] # inherit thesis if it exists
	end

	def print_assumptions
		ids = @assumptions.collect {|i| [@lines[i].filename, @lines[i].fileline]}
		ids.concat @assume_blocks.collect {|id| [id[:filename], id[:fileline]]}
		groups = {}
		ids.each {|filename, fileline|
			groups[filename] = [] if not groups.has_key? filename
			groups[filename] << fileline
		}
		wrapper = WordWrapper.new ',', 2
		groups.each {|filename, filelines|
			if filelines.size == 1
				wrapper.print "#{filename}: assumption on line "
			else
				wrapper.print "#{filename}: assumptions on lines "
			end
			wrapper.puts filelines.sort.join ', '
		}
	end

	def process input, is_filename = false
		message = case @scopes.last
			when :suppose then '"process" not allowed in supposition'
			when :now then '"process" not allowed in "now" block'
			when Array then '"process" not allowed in "proof" block'
			when :assume then '"process" not allowed in assume block'
		end
		raise ProofException, message if message

		include input, is_filename

		message = case @scopes.last
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

		if @assumptions.empty? and @assume_blocks.empty?
			groups = @axioms.group_by {|i| @lines[i].filename}
			groups.each {|filename, axioms|
				s = (axioms.size == 1 ? 'axiom' : 'axioms')
				puts "#{axioms.size} #{s} in #{filename}"
			}
			puts 'proof successful!'
		else
			print_assumptions
			puts 'proof incomplete due to assumptions'
		end
	end

	def proof content, id = nil
		@scopes << [content, id, @lines.size]
		@active_reason_sets << []
		@theses << content
		@label_stack << []
	end

	def so sentence, reasons = [], id = nil
    return so_assume sentence, id if @scopes.include? :assume # assume block
		if @active_reason_sets[-1].empty?
			raise ProofException, 'nothing for "so" to use'
		end
		line_numbers = process_reasons reasons
		line_numbers.concat @active_reason_sets[-1]
		@active_reason_sets[-1] = []
		derive_internal sentence, line_numbers, id
	end

	def so_assume sentence, id = nil
		if @active_reason_sets[-1].empty?
			raise ProofException, 'nothing for "so" to use'
		end
		@active_reason_sets[-1] = []
		assume sentence, id
	end
	
	def suppose sentence, id = nil
		@scopes << :suppose
		@active_reason_sets << []
		@theses << @theses[-1] # inherit thesis if it exists
		check_admission sentence
		@active_suppositions << @lines.size
		add sentence, :supposition, id
	end

	def to_s # handle newlines and tabs?
		number_space = @lines.size.to_s.size + 2 # 2 for '. '
		max_supposition, max_sentence = 0, 0
		@lines.each {|line|
		  max_supposition = [max_supposition, line.supposition_string.size].max
		  max_sentence = [max_sentence, line.sentence.to_s.size].max
		}
		supposition_space = [max_supposition, 15].min
		remaining = 79 - number_space - supposition_space - 8 # 8 for two instances of ' %% '
		sentence_space = [max_sentence, remaining / 2].min
		reason_space = remaining - sentence_space
	  string = ''
		@lines.each_with_index {|line, index|
		  rows = line.rows supposition_space, sentence_space, reason_space
			string << ' ' * (@lines.size.to_s.size - (index + 1).to_s.size)
			string << (index + 1).to_s + '. ' + rows[0] + "\n"
			rows[1..-1].each {|row| string << ' ' * number_space + row + "\n"}
		}
		string
	end

	private #####################################################################

	def add sentence, reason, id
		unless reason == :'assumption schema' or reason == :'axiom schema'
			variables, body = read_binding sentence
			scopes = get_scopes
			variables.each {|variable|
				if @active_bindings[variable]
					# deactivate any variables forced to be in the last one's scope
					last_start = @active_bindings[variable]
					last_stop = scopes[@active_bindings[variable]]
					@active_bindings.delete_if {|variable, i|
						i >= last_start and i <= last_stop
					}
				end
				@active_bindings[variable] = @lines.size
			}
		end
		label = id[:label]
    if @line_numbers_by_label[label]
      raise ProofException, "label #{label} already in scope"
    end
		@lines << Line.new(
			sentence, reason, @active_suppositions.dup, @active_bindings.dup, id
		)
    n = @lines.size - 1
		if label
			@label_stack[-1] << label
    	@line_numbers_by_label[label] = n 
		else
    	@active_reason_sets[-1] << n
		end
    n
  end

  def bind_variables variables, body, quantifier
		(variables.reverse & body.free_variables).each {|variable|
			body = Tree.new quantifier, [Tree.new(variable, []), body]
		}
		body
  end

	def check tree, line_numbers
#		puts "tree:"
#		p tree
#   puts "\nline numbers are #{line_numbers.inspect}"
#   puts "active suppositions are #{@active_suppositions}"
#   puts "active bindings are #{@active_bindings}"

		schema_line_numbers = line_numbers.select {|i| @lines[i].schema?}
		raise ProofException, 'cannot cite multiple schemas' if schema_line_numbers.size > 1
		schema_line_number = schema_line_numbers[0]
    line_numbers -= [schema_line_number] if schema_line_number
		
    antecedent = cited_tree line_numbers

		tree = Tree.new :implies, [antecedent, tree] if antecedent

		if schema_line_number
			schema = @lines[schema_line_number].sentence
			begin
				tree = instantiate_schema schema, tree
			rescue ProofException => e
				raise unless e.message == 'ProofException' # re-raise with original message
				raise ProofException, 'could not instantiate schema'
			end
		end

#		puts 'checking tree:'
#		p tree

#		result = valid_cvc4? tree
		result = valid_e? tree
#		result = valid_iprover? tree
#		result = valid_prover9? tree
#		result = valid_spass? tree
#	  result = EnglishChecker.valid? tree
#   puts
#   if result == :valid
#     puts 'tree is valid:'
#   elsif result == :invalid
#			puts 'tree is not valid:'
#   elsif result == :unknown
#			puts 'could not tell whether tree is valid'
#		end
#		$stdin.gets
#		p tree
#   puts

		if schema_line_number and result != :valid
			raise ProofException, 'could not instantiate schema'
		end

	  result
	end

  def cited_tree cited_lines, scope_tree = nil

		scope_tree = make_scope_tree if not scope_tree

		# make trees recursively
		trees = scope_tree.branches.collect {|branch|
			cited_tree cited_lines, branch
		}.compact

		# top scope		
    return conjunction_tree trees if not scope_tree.line

    line = @lines[scope_tree.line]
    cited = cited_lines.include? scope_tree.line
    if line.binding?
      variables, body = read_binding line.sentence
      if @active_bindings.values.include? scope_tree.line
				trees.unshift body if body and cited # add to start
				tree = conjunction_tree trees
			else
				tree = conjunction_tree trees
				if not tree
					return nil unless body and not line.supposition? and cited
					tree = bind_variables variables, body, :for_some
				elsif line.supposition?
					tree = Tree.new :implies, [body, tree] if body
					# generalize the binding
					tree = bind_variables variables, tree, :for_all
				else
					tree = Tree.new :and, [body, tree] if body and cited
					tree = bind_variables variables, tree, :for_some
				end
			end
		elsif line.supposition?
			active_supposition = @active_suppositions.include? scope_tree.line
			if active_supposition
				trees.unshift line.sentence if cited # add to start
				tree = conjunction_tree trees
			else
				tree = conjunction_tree trees
				tree = Tree.new :implies, [line.sentence, tree] if tree
			end
		else
			raise unless trees.empty?
			tree = line.sentence if cited
    end
    tree
	end

	def derive_internal sentence, line_numbers, id
		check_admission sentence
		result = check sentence, line_numbers
		if result == :valid
			add sentence, :derivation, id
		elsif result == :invalid
			raise DeriveException.new 'invalid derivation', sentence
		elsif result == :unknown
			raise DeriveException.new 'could not determine validity of derivation', sentence
		else
			raise
		end
	end

  def get_scopes
		last_used = make_last_used
		scopes = {}
		(@lines.size-1).downto(0) {|n|
		  line = @lines[n]
		  if line.supposition?
		    after = (n+1...@lines.size).find {|i| not @lines[i].suppositions.include? n}
		    scopes[n] = (after ? after - 1 : @lines.size - 1)
		  elsif line.binding?
				last = last_used[n]
		    if not last
#					puts "no last, so setting scopes[#{n}] to #{n}"
		      scopes[n] = n
		    else
#					puts "last = #{last}"
		      added_suppositions = @lines[last].suppositions - @lines[n].suppositions
		      added_bindings = @lines[last].bindings.values - @lines[n].bindings.values
		      added = added_suppositions + added_bindings
		      scopes[n] = ([last] + added.collect {|i| scopes[i]}).max
#					puts "now set scopes[#{n}] to #{scopes[n]}"
		    end
		  end
#			if n == 0
#				puts "scopes are:"
#				p scopes.sort
#			end
		}
		scopes
  end

	def make_last_used
		# for each line l, gives the last line at which any variables bound
		# at l are referenced
		last_used = {}
		@lines.each_with_index {|line, i|
			line.sentence.free_variables.each {|variable|
				next if not line.bindings[variable]
				last_used[line.bindings[variable]] = i
			}
		}
		last_used
	end

  def make_scope_tree line_numbers = nil, scopes = nil
    scopes = get_scopes if not scopes
    if not line_numbers
			line_numbers = @lines.each_index.to_a 
			result = make_scope_tree line_numbers, scopes
#     puts 'scope_tree:'
#			p result
#			puts
			return result
		end
#   puts "make_scope_tree running with line numbers = #{line_numbers}"
    branches = []
    until line_numbers.empty?
      n = line_numbers.shift # take from start
#     puts "line number is #{n}"
#     line = @lines[line_number]
      if (@lines[n].supposition? or @lines[n].binding?) and scopes[n] > n
        last = line_numbers.index scopes[n]
        subtree = make_scope_tree line_numbers[0..last], scopes
        branches << ScopeTree.new(n, subtree.branches, @lines)
        line_numbers = line_numbers[last+1..-1]
      else
        branches << ScopeTree.new(n, [], @lines)
      end
    end
    ScopeTree.new nil, branches, @lines
  end

	def process_content tree, thesis
		if thesis
			begin
				substitute tree, {'thesis' => thesis}
			rescue SubstituteException => e
				raise ProofException, "cannot bind variable #{e}: part of thesis"
			end
		elsif tree.free_variables.include? 'thesis'
			raise ProofException, 'thesis used outside of proof block'
		else
			tree
		end
	end

	def process_reasons reasons
		line_numbers = []
		line_numbers.concat reasons.collect {|reason|
			i = @line_numbers_by_label[reason]
			if not i
				if @inactive_labels.include? reason
					raise ProofException, "label #{reason} is no longer in scope"
				else				
					raise ProofException, "unknown label #{reason}" 
				end
			end
			if @lines[i].supposition? and not @active_suppositions.include? i
				raise ProofException, "supposition cited outside itself"
			end
			i
		}
    line_numbers
	end

  def read_binding tree
    variables = []
		body = tree
    while body and body.operator == :for_some
      variables << body.subtrees[0].operator
      body = body.subtrees[1]
    end
    [variables, body]
  end
end

### end of Proof class ###################################################

class ProofException < StandardError; end

class DeriveException < ProofException
	def initialize type, sentence
		@type, @sentence = type, sentence
	end
	
	def message line_number
		"line #{line_number}: #{@type} \"#{@sentence}\""
#		"#{@type} at line #{line_number}: \"#{@sentence}\""
	end
end

class ParseException < ProofException
	attr_reader :line_number

	def initialize message, line_number = nil
		@line_number = line_number
		super message
	end
end

class SubstituteException < ProofException; end

##########################################################################

if $0 == __FILE__
	name_version = 'Oak version 0.2pre'
	issues_url = 'https://github.com/smithtim/oak/issues'

	if ARGV.delete '-v'
		puts name_version
		exit if ARGV.size == 0
	end

	if ARGV.size != 1 or ARGV[0].start_with? '-'
		puts "usage: oak [-v] [filename]"
		exit
	end

	begin
		Proof.new.process ARGV[0], :is_filename
	rescue => e
		exit if e.is_a? ProofException # already printed
		puts "\n\n#{e.message} (#{e.class}) [#{name_version}]"
	  puts "\tfrom #{e.backtrace.join "\n\tfrom "}"
		puts "\nBUG: You have found a bug in the proof checker!  It would be greatly appreciated if you could report it at #{issues_url} so that it can be fixed."
	end
end
