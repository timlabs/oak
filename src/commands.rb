require_relative 'bindings.rb'
require_relative 'external prover.rb'
require_relative 'schema.rb'

class Proof
	class Line < Content
		attr_reader :label, :filename, :fileline

		def initialize content, type, suppositions, id
			super content.binding # carries all information about content
			types = [:assumption, :axiom, :derivation, :supposition,
							 :'assumption schema', :'axiom schema']
			raise "unknown type #{type.inspect}" unless types.include? type
			@type, @suppositions = type, suppositions
			@label, @filename, @fileline = id[:label], id[:filename], id[:fileline]
			sentence_string = @sentence.to_s.rstrip
			if sentence_string.empty?
				raise ProofException, 'cannot add line with empty sentence'
			end
			illegal = ['%%', "\t", "\n"]
			found = illegal.find {|string| sentence_string.include? string}
			if found
			  raise ProofException, "cannot add line containing illegal substring #{found.inspect}"
			end
		end

		def rows supposition_space = nil, sentence_space = nil, type_space = nil
			rows = []
			suppositions, sentence, type = supposition_string, @sentence.to_s.dup, @type.to_s.dup
			if not supposition_space and not sentence_space and not type_space
				supposition_space = [suppositions.size, 15].min
				remaining = 79 - supposition_space - 8 # 8 for two instances of ' %% '
				sentence_space = [sentence.size, remaining / 2].min
				type_space = remaining - sentence_space
			end
			until suppositions.empty? and sentence.empty? and type.empty?
				row = suppositions.slice! 0...supposition_space
				row << ' ' * (supposition_space - row.size) if row.size < supposition_space
				row << ' %% '
				pad = (sentence.size < sentence_space) ? ' ' * (sentence_space - sentence.size) : ''
				row << sentence.slice!(0...sentence_space) + pad + ' %% '
				row << type.slice!(0...type_space)
				rows << row
			end
			rows
		end

		def schema?
			@type == :'assumption schema' or @type == :'axiom schema'
		end

    def supposition?
      @type == :supposition
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

	def initialize options = {}
		@options = options
		@lines = []
		@active_suppositions = []
		@active_contexts = [[]]
		@scopes = []
		@theses = []
		@label_stack = [[]]
    @line_numbers_by_label = {}
		@inactive_labels = Set[]
		@bindings = Bindings.new
	end

	def assume content, id = nil
		check_admission content
		add content, :assumption, id
	end

	def assume_schema schema, id = nil
		if not @active_suppositions.empty?
			raise ProofException, '"assume schema" not allowed in supposition'
		end
		add schema, :'assumption schema', id
	end

	def axiom_schema schema, id = nil
		message = case @scopes.last
			when :suppose then 'axiom schema not allowed in supposition'
			when :now then 'axiom schema not allowed in "now" block'
			when Array then 'axiom schema not allowed in "proof" block'
		end
		raise ProofException, message if message
		add schema, :'axiom schema', id
	end

	def axiom content, id = nil
		message = case @scopes.last
			when :suppose then 'axiom not allowed in supposition'
			when :now then 'axiom not allowed in "now" block'
			when Array then 'axiom not allowed in "proof" block'
		end
		raise ProofException, message if message
		check_admission content
		add content, :axiom, id
	end

	def begin_assume
		@scopes << :assume
	end

	def check_admission content
		@bindings.check_admission content
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

	def derive content, reasons = [], id = nil
    return assume content, id if @scopes.include? :assume # assume block
		line_numbers = process_reasons reasons
		derive_internal content, line_numbers, id
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
		last_context = @active_contexts.pop
		last_thesis = @theses.pop
		if last_scope.is_a? Array # end of proof block
			@label_stack[-1].each {|label|
				@line_numbers_by_label.delete label
				@inactive_labels << label
			}
			@label_stack.pop

			@bindings.end_block

			content, id = last_scope
      if @scopes.include? :assume then assume content, id # assume block
      else derive_internal content, last_context, id end
		else
			if last_scope == :suppose
				@active_suppositions.pop
				@bindings.end_block
			end
			@active_contexts.last.concat last_context
		end
	end

	def now
		@scopes << :now
		@active_contexts << []
		@theses << @theses[-1] # inherit thesis if it exists
	end

	def proof content, id = nil
		@scopes << [content, id]
		@active_contexts << []
		@theses << content
		@label_stack << []

		@bindings.begin_block
	end

	def so content, reasons = [], id = nil
    return so_assume content, id if @scopes.include? :assume # assume block
		if @active_contexts[-1].empty?
			raise ProofException, 'nothing for "so" to use'
		end
		line_numbers = process_reasons reasons
		line_numbers.concat @active_contexts[-1]
		@active_contexts[-1] = []
		derive_internal content, line_numbers, id
	end

	def so_assume content, id = nil
		if @active_contexts[-1].empty?
			raise ProofException, 'nothing for "so" to use'
		end
		@active_contexts[-1] = []
		assume content, id
	end

	def suppose content, id = nil
		@scopes << :suppose
		@active_contexts << []
		@theses << @theses[-1] # inherit thesis if it exists
		check_admission content
		@active_suppositions << @lines.size
		add content, :supposition, id
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
		type_space = remaining - sentence_space
	  string = ''
		@lines.each_with_index {|line, index|
		  rows = line.rows supposition_space, sentence_space, type_space
			string << ' ' * (@lines.size.to_s.size - (index + 1).to_s.size)
			string << (index + 1).to_s + '. ' + rows[0] + "\n"
			rows[1..-1].each {|row| string << ' ' * number_space + row + "\n"}
		}
		string
	end

	private #####################################################################

	def add content, type, id
		line = Line.new content, type, @active_suppositions.dup, id
		unless line.schema?
			@bindings.begin_block if type == :axiom or type == :supposition
			@bindings.admit line
		end
		label = id[:label]
    if @line_numbers_by_label[label]
      raise ProofException, "label #{label} already in scope"
    end
		@lines << line
    n = @lines.size - 1
		if label
			@label_stack[-1] << label
			@line_numbers_by_label[label] = n
		else
			@active_contexts[-1] << n
		end
    n
  end

	def check tree, line_numbers
		schema_line_numbers = line_numbers.select {|i| @lines[i].schema?}
		raise ProofException, 'cannot cite multiple schemas' if schema_line_numbers.size > 1
		schema_line_number = schema_line_numbers[0]
    line_numbers -= [schema_line_number] if schema_line_number

		lines = @lines.values_at *line_numbers
		antecedent = if schema_line_number
			@bindings.cited_tree_without_tie_ins lines
		else
			@bindings.cited_tree lines, tree.free_variables
		end
		tree = Tree.new :implies, [antecedent, tree] if antecedent

		if schema_line_number
			schema = @lines[schema_line_number].sentence
			begin
				# puts "\n\ninstantiating schema with tree:\n#{tree}"
				tree = Schema.instantiate_schema schema, tree
			rescue ProofException => e
				raise unless e.message == 'ProofException' # re-raise with original message
				raise ProofException, 'could not instantiate schema'
			end
		end

		if tree.operator == :implies and equal_up_to_variable_names? *tree.subtrees
			tree = tree_for_true # make things easy for external prover
		end

		# puts 'checking tree:'
		# puts tree

		result = ExternalProver.valid_e? tree

		if schema_line_number and result != :valid
			raise ProofException, 'could not instantiate schema'
		end

	  [result, tree]
	end

	def citation_string line_numbers
		line_numbers.collect {|i|
			@lines[i].label or "line #{@lines[i].fileline}"
		}.join ', '
	end

	def derive_internal content, line_numbers, id
		check_admission content

		result, checked = check content.sentence, line_numbers

		if result != :valid
			message = case result
				when :invalid then 'invalid derivation'
				when :unknown then 'could not determine validity of derivation'
				else raise
			end
			raise DeriveException.new message, content.sentence, result, checked
		end

		if @options[:reduce]
			labeled = line_numbers.select {|i| @lines[i].label}
			unlabeled = line_numbers - labeled
			minimal = find_minimal_subsets(labeled) {|subset|
				begin
					# note: order and duplicates do not matter to check
					result, checked = check content.sentence, unlabeled + subset
					{:valid => true, :invalid => false}[result]
				rescue ProofException # e.g. "could not instantiate schema"
					false
				end
			}
			if minimal != [labeled]
				from = citation_string labeled
				to = minimal.collect {|set| citation_string set}.join "\n  "
				message = "citation can be reduced from:\n  #{from}\nto:\n  #{to}"
				info = InfoException.new message
			end
		end

		add content, :derivation, id
		info
	end

	def process_reasons reasons
		reasons.collect {|reason|
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
	end
end

### end of Proof class ###################################################

class ProofException < StandardError; end

class DeriveException < ProofException
	attr_reader :result, :checked

	def initialize message, sentence, result, checked
		@message, @sentence, @result, @checked = message, sentence, result, checked
	end

	def message line_number
		"line #{line_number}: #{@message} \"#{@sentence}\""
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

class InfoException < ProofException; end