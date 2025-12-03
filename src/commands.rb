require_relative 'bindings.rb'
require_relative 'external prover.rb'
require_relative 'schema.rb'

class Proof
	class Line < Content
		attr_reader :label, :filename, :fileline

		def initialize content, type, id
			super content # set instance variables from content
			types = [:assumption, :axiom, :derivation, :supposition]
			raise "unknown type #{type.inspect}" unless types.include? type
			@type = type
			@label, @filename, @fileline = id[:label], id[:filename], id[:fileline]
		end

    def supposition?
      @type == :supposition
    end
	end
end

### start of Proof class #################################################

class Proof
	attr_reader :scopes, :theses

	def initialize manager, options = {}
		@lines = []
		@active_suppositions = []
		@active_buffers = [[]]
		@scopes = []
		@theses = []
		@label_stack = [[]]
    @line_numbers_by_label = {}
		@inactive_labels = Set[]
		@bindings = Bindings.new
    @manager = manager
    @marker = :waiting if options[:marker]
	end

	def assume content, id = nil
		if content.schema and not @active_suppositions.empty?
			raise ProofException, '"assume schema" not allowed in supposition'
		end
		check_admission content
		add content, :assumption, id
	end

  def assuming?
    @scopes.include? :assume or @marker == :waiting
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
    return assume content, id if assuming?
		line_numbers, question_mark = process_reasons reasons
		derive_internal content, line_numbers, question_mark, id
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
		last_buffer = @active_buffers.pop
		last_thesis = @theses.pop
		if last_scope.is_a? Array # end of proof block
			@label_stack[-1].each {|label|
				@line_numbers_by_label.delete label
				@inactive_labels << label
			}
			@label_stack.pop

			@bindings.end_block

			content, id = last_scope
      if assuming? then
        assume content, id
      else
        derive_internal content, last_buffer, false, id
      end
		else
			if last_scope == :suppose
				@active_suppositions.pop
				@bindings.end_block
			end
			@active_buffers.last.concat last_buffer
		end
	end

  def marker
    case @marker
      when :waiting then @marker = :seen
      when :seen then raise ProofException, 'duplicate marker'
      when nil then raise ProofException, 'marker used without -m option'
      else raise
    end
  end

	def now
		@scopes << :now
		@active_buffers << []
		@theses << @theses[-1] # inherit thesis if it exists
	end

	def proof content, id = nil
		@scopes << [content, id]
		@active_buffers << []
		@theses << content
		@label_stack << []

		@bindings.begin_block
	end

	def so content, reasons = [], id = nil
    return so_assume content, id if assuming?
		if @active_buffers[-1].empty?
			raise ProofException, 'nothing for "so" to use'
		end
		line_numbers, question_mark = process_reasons reasons
		line_numbers.concat @active_buffers[-1]
		@active_buffers[-1] = []
		derive_internal content, line_numbers, question_mark, id
	end

	def so_assume content, id = nil
		if @active_buffers[-1].empty?
			raise ProofException, 'nothing for "so" to use'
		end
		@active_buffers[-1] = []
		assume content, id
	end

	def suppose content, id = nil
		@scopes << :suppose
		@active_buffers << []
		@theses << @theses[-1] # inherit thesis if it exists
		check_admission content
		@active_suppositions << @lines.size
		add content, :supposition, id
	end

	def check content, line_numbers
		to_check = @bindings.to_check content, @lines.values_at(*line_numbers)
		schema, tree = to_check.values_at :schema, :tree

		if schema
			begin
				tree = SchemaModule.instantiate_schema schema, tree
			rescue ProofException => e
				raise unless e.message == 'ProofException' # re-raise original message
				raise ProofException, 'could not instantiate schema'
			end
		end

		# puts "\nchecking tree:\n#{tree.pretty_to_s}"

		result = ExternalProver.valid_e? tree

		if schema and result != :valid
			raise ProofException, 'could not instantiate schema'
		end

	  [result, tree]
	end

  def check_wait_forever tree
    ExternalProver.valid_e? tree, true
  end

  def reduce content, line_numbers
    # find the minimal subsets of the line numbers which make the content valid
		labeled = line_numbers.select {|i| @lines[i].label}
		unlabeled = line_numbers - labeled
		minimal = find_minimal_subsets(labeled) {|subset|
			begin
				# note: order and duplicates do not matter to check
				result, checked = check content, unlabeled + subset
				{:valid => true, :invalid => false}[result]
			rescue ProofException # e.g. "could not instantiate schema"
				false
			end
		}
    return nil if minimal == [labeled]
    [labeled, minimal]
  end

  def fix content, line_numbers
    # look for additional line numbers that make the content valid
    originals = line_numbers
    lines_with_label_not_schema = @line_numbers_by_label.values.select {|i|
      not @lines[i].schema
    }
    additions = lines_with_label_not_schema - originals
    return nil if additions.empty?
    seek_valid_subset(additions) {|subset|
      result, checked = check content, originals + subset
      result
    }
  end

  def reduce_fix fix_line_numbers, content, original_line_numbers
    # look for a subset of the fix line numbers that makes the content valid
    reduce_subset(fix_line_numbers) {|subset|
      result, checked = check content, original_line_numbers + subset
      result == :valid
    }
  end

  def resolve_question_mark content, line_numbers
    # look for a single additional line number that makes the content valid
    originals = line_numbers
    lines_with_label_not_schema = @line_numbers_by_label.values.select {|i|
      not @lines[i].schema
    }
    additions = lines_with_label_not_schema - originals
    return [] if additions.empty?
    find_valid_elements(additions) {|subset|
      result, checked = check content, originals + subset
      result
    }
  end

	def citation_string line_numbers
		line_numbers.collect {|i|
			@lines[i].label or "line #{@lines[i].fileline}"
		}.join ', '
	end

	private #####################################################################

	def add content, type, id
		line = Line.new content, type, id
		@bindings.begin_block if type == :axiom or type == :supposition
		@bindings.admit line
		label = id[:label]
    if @line_numbers_by_label[label]
      raise ProofException, "label #{label} already in scope"
    end
		@lines << line
    n = @lines.size - 1
		if label
			@label_stack[-1] << label
			@line_numbers_by_label[label] = n
		elsif content.tie_ins.empty? or not content.binds.empty?
			@active_buffers[-1] << n
		end
    n
  end

	def derive_internal content, line_numbers, question_mark, id
		check_admission content
    @manager.derive self, content, line_numbers, question_mark
		add content, :derivation, id
	end

	def process_reasons reasons
    line_numbers, question_mark = [], false, false
    reasons.each {|reason|
      if reason == :question_mark
        raise ProofException, 'cannot use ? twice in "by"' if question_mark
        question_mark = true
      else
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
        line_numbers << i
      end
		}
    [line_numbers, question_mark]
	end
end

### end of Proof class ###################################################

class ProofException < StandardError; end

class ParseException < ProofException
	attr_reader :line_number

	def initialize message, line_number = nil
		@line_number = line_number
		super message
	end
end

class DeriveException < ProofException; end

class BaseException < ProofException; end

class EndException < ProofException; end

class SubstituteException < ProofException; end