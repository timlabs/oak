require_relative 'bindings.rb'
require_relative 'external prover.rb'
require_relative 'schema.rb'

class Proof
	class Line
		attr_reader :sentence, :reason, :suppositions, :label, :filename, :fileline,
		 						:node
								
		def initialize sentence, reason, suppositions, id, node
			@sentence, @reason, @suppositions = sentence, reason, suppositions
			@label, @filename, @fileline = id[:label], id[:filename], id[:fileline]
			@node = node
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

### start of Proof class #################################################

class Proof
	attr_reader :scopes, :theses

	def initialize
		@lines = []
		#@definitions = []
		@assumptions = []
		@assume_blocks = []
		@axioms = []
		@active_suppositions = []
		@active_reason_sets = [[]]
		@scopes = []
		@theses = []
		@label_stack = [[]]
    @line_numbers_by_label = {}
		@inactive_labels = Set[]
		@bindings = Bindings.new @lines
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
		@bindings.check_admission sentence
		return

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
#			@active_bindings.delete_if {|variable, line_number|
#				line_number >= lines_size_before
#			}

			@bindings.end_block

      if @scopes.include? :assume then assume content, id # assume block
      else derive_internal content, last_reason_set, id end
		else
			if last_scope == :suppose
				# delete any bindings made while this supposition was active
				supposition = @active_suppositions.last
#				@active_bindings.delete_if {|variable, line_number|
#					@lines[line_number].suppositions.include? supposition
#				}
				@active_suppositions.pop

				@bindings.end_block

			end
			@active_reason_sets.last.concat last_reason_set
		end
	end

	def makes_assumptions?
		not (@assumptions.empty? and @assume_blocks.empty?)
	end

	def now
		@scopes << :now
		@active_reason_sets << []
		@theses << @theses[-1] # inherit thesis if it exists
	end

	def print_axioms
		groups = @axioms.group_by {|i| @lines[i].filename}
		groups.each {|filename, axioms|
			s = (axioms.size == 1 ? 'axiom' : 'axioms')
			puts "#{axioms.size} #{s} in #{filename}"
		}
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

	def proof content, id = nil
		@scopes << [content, id, @lines.size]
		@active_reason_sets << []
		@theses << content
		@label_stack << []

		@bindings.begin_block
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

			# think about moving check_admission in here?  (will have to move derive_internal as well,
			#	not sure if that works)

			@bindings.begin_block if reason == :axiom or reason == :supposition
			node = @bindings.admit sentence, @lines.size

			defines, sentence = read_defines sentence
=begin
			# replace defines with for somes
			defines, replaced = read_defines sentence
			defines.reverse.each {|v|
				replaced = Tree.new :for_some, [Tree.new(v, []), replaced]
			}
			sentence = replaced
=end
		end
		label = id[:label]
    if @line_numbers_by_label[label]
      raise ProofException, "label #{label} already in scope"
    end
		@lines << Line.new(
			sentence, reason, @active_suppositions.dup, id, node
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

    antecedent = @bindings.cited_tree line_numbers

		tree = Tree.new :implies, [antecedent, tree] if antecedent

		if schema_line_number
			schema = @lines[schema_line_number].sentence
			begin
				tree = Schema.instantiate_schema schema, tree
			rescue ProofException => e
				raise unless e.message == 'ProofException' # re-raise with original message
				raise ProofException, 'could not instantiate schema'
			end
		end

#		puts 'checking tree:'
#		p tree

#		result = ExternalProver.valid_cvc4? tree
		result = ExternalProver.valid_e? tree
#		result = ExternalProver.valid_iprover? tree
#		result = ExternalProver.valid_prover9? tree
#		result = ExternalProver.valid_spass? tree
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

	def derive_internal sentence, line_numbers, id
		check_admission sentence

		# replace defines with for somes
		defines, replaced = read_defines sentence
		defines.reverse.each {|v|
			replaced = Tree.new :for_some, [Tree.new(v, []), replaced]
		}

		result = check replaced, line_numbers
		if result == :valid
			add sentence, :derivation, id
		elsif result == :invalid
			raise DeriveException.new 'invalid derivation', replaced
		elsif result == :unknown
			raise DeriveException.new 'could not determine validity of derivation', replaced
		else
			raise
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