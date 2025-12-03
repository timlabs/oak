require_relative 'parser.rb'
require_relative 'commands.rb'
require_relative 'utilities.rb'

class Proof
  def self.process_file input, options = {}
    process input, :file, options
  end

  def self.process_text input, options = {}
    process input, :text, options
  end

	def self.process input, type, options
    addons = {printer: Printer.new, tracker: Tracker.new}
    addons[:tracker].begin_assume nil if options[:marker]
    manager = DerivationManager.new addons[:printer], options
		proof = Proof.new manager, {marker: options[:marker]}
    begin
	    status = include proof, input, type, nil, addons
      finalize proof, status, addons, {marker: options[:marker]}
    rescue ProofException => e
      print_exception e, addons[:printer]
      raise
    end
  end

	def self.include proof, input, type, include_line, addons
		printer, tracker = addons.values_at :printer, :tracker
    case type
      when :file
        dirname = File.dirname input
        filename = File.basename input
        begin
          input = File.read input
        rescue
          exception = (include_line ? ProofException : BaseException)
          raise exception, "could not open file \"#{input}\""
        end
      when :text
        filename = ''
      else raise
    end
    printer.begin_file filename
		tracker.begin_file filename, include_line
		status = :ok
		Parser.new.parse_each(input) {|sentence, action, content, reasons, label,
																	 fileline|
			next if action == :empty
      printer.line fileline
			if action == :exit
        printer.exit
				status = :exited
				break
			end
			if content.is_a? Content
				content = process_content content, proof.theses[-1]
			end
			# puts "content for line #{fileline} is: #{content.inspect}"
			id = {label: label, filename: filename, fileline: fileline}
			case action
				when :include then
					# include relative to path of current proof file
					content = File.expand_path content, dirname if type == :file
					status = include proof, content, :file, fileline, addons
					break if status != :ok
				when :suppose then proof.suppose content, id
				when :now then proof.now
				when :end then proof.end_block
				when :assume
					proof.assume content, id
					tracker.assume fileline
				when :axiom
					proof.axiom content, id
					tracker.axiom
				when :derive then proof.derive content, reasons, id
				when :so then proof.so content, reasons, id
				when :so_assume
					proof.so_assume content, id
					tracker.assume fileline
				when :proof then proof.proof content, id
				when :begin_assume
					proof.begin_assume
					tracker.begin_assume fileline
				when :end_assume
					proof.end_assume
					tracker.end_assume fileline
        when :marker
          proof.marker
          tracker.end_assume fileline
				else raise "unrecognized action #{action}"
			end
		}
    printer.end_file
		tracker.end_file
		status
  end

  def self.finalize proof, status, addons, options
		printer, tracker = addons.values_at :printer, :tracker

    if not proof.scopes.empty?
      message = case proof.scopes.last
        when :suppose then 'active supposition'
        when :now then 'active "now" block'
        when Array then 'active "proof" block'
        when :assume then 'active assume block'
      end
		elsif options[:marker] and proof.assuming?
      message = '-m option used without marker'
    end
    raise EndException, message if message

    printer.accepted status
		if not tracker.assumptions.empty?
      printer.assumptions tracker.assumptions, options[:marker]
		else
      printer.axioms tracker.axioms
      printer.conclude status
    end
	end

  def self.print_exception e, printer
    case e
      when ParseException
        if e.line_number
          printer.line e.line_number
          printer.parse_error e.message
        else
          printer.file_message e.message
        end
      when DeriveException # already printed
      when BaseException then printer.base_error e.message
      when EndException then printer.end_error e.message
      else printer.line_error e.message
    end
  end

	def self.process_content content, thesis
		if not thesis
			return content unless content.uses.include? 'thesis'
			raise ProofException, 'thesis used outside of proof block'
		elsif content.uses.include? 'thesis'
			if content.schema
				raise ProofException, 'cannot use thesis in schema'
			elsif not content.binds.empty?
				raise ProofException, "cannot use thesis in binding"
			elsif not content.tie_ins.empty?
				raise ProofException, "cannot use thesis in tie-in"
			end
			begin # content was just a Tree
				tree = substitute content.sentence, {'thesis' => thesis.sentence}
			rescue SubstituteException => e
				message = "cannot quantify variable #{e}: conflicts with thesis"
				raise ProofException, message
			end
			return Content.new tree
		else
			conflict = (thesis.uses & content.binds).first
			return content unless conflict
			raise ProofException, "cannot bind variable #{conflict}: part of thesis"
		end
	end

	private_class_method :process, :include, :finalize, :print_exception,
    :process_content
end

class DerivationManager
  def initialize printer, options
    @printer = printer
    @fix, @reduce, @wait_on_unknown, @print_failed_tree =
      options.values_at :fix, :reduce, :wait, :print_failed_tree
  end

  def derive proof, content, line_numbers, question_mark
		result, checked = proof.check content, line_numbers
    if question_mark
      if result == :valid
        @printer.line_message 'derivation is already valid, no need for ?'
      else
        @printer.line_message 'trying to resolve ?'
        results = proof.resolve_question_mark content, line_numbers
        if results.empty?
          @printer.line_message 'could not resolve ?'
        else
          to = results.collect {|i| proof.citation_string [i]}.join "\n  "
          @printer.line_message_block "resolved ? into:\n  #{to}"
          @printer.message 'proof incomplete due to ?'
        end
      end
      raise DeriveException
    end
    if result == :valid
      if @reduce
        reduction = proof.reduce content, line_numbers
        if reduction
          from_lines, to_sets = reduction
          from = proof.citation_string from_lines
          to = to_sets.collect {|set| proof.citation_string set}.join "\n  "
          message = "citation can be reduced from:\n  #{from}\nto:\n  #{to}"
          @printer.line_message_block message
        end
      end
    else
      if @print_failed_tree
        message = "full tree below\n\n#{checked.pretty_to_s}\n"
        @printer.option_message '-p', message
      end
			message = case result
				when :invalid then 'invalid derivation'
				when :unknown then 'could not determine validity of derivation'
				else raise
			end
      @printer.line_message message + " \"#{content.sentence}\""
      if @fix
        @printer.option_message '-f', 'looking for a fix'
        result = proof.fix content, line_numbers
        if result
          @printer.option_message '-f', 'found a fix, reducing'
          result = proof.reduce_fix result, content, line_numbers
          to = proof.citation_string result
          @printer.option_message '-f',
            "derivation will work if you add:\n  #{to}"
        else
          @printer.option_message '-f', 'no fix found'
        end
      elsif result == :unknown and @wait_on_unknown
        @printer.option_message '-w', 'checking validity without work limit'
        @printer.option_message '-w',
          '(may never finish, press ctrl-c to abort)'
        result = proof.check_wait_forever checked
        message = case result
          when :invalid then 'invalid derivation'
          # use ceil rather than round to avoid "1.0 times the work limit"
          when Numeric then "valid derivation, but took #{result.ceil 1} " \
                            "times the work limit"
          when :unknown then 'eprover gave up'
          else raise result.inspect
        end
        @printer.option_message '-w', message
        @printer.message 'proof unsuccessful'
      end
			raise DeriveException
    end
  end
end

class Printer
  # maintains the invariant: if @stack is empty, @wrapper is clear

  def initialize
		@wrapper = WordWrapper.new
    @stack = []
  end

  def accepted status
    raise if not @stack.empty?
    case status
      when :exited then @wrapper.puts 'all lines accepted prior to exit'
      when :ok then @wrapper.puts 'all lines accepted'
      else raise
    end
  end

  def assumptions assumptions, marker
    raise if not @stack.empty?
		# assumption locations
		assumptions.each {|filename, assumptions|
			if assumptions.size == 1 and assumptions[0].is_a? Numeric
				@wrapper.print "#{filename}: assumption on line "
			else
				@wrapper.print "#{filename}: assumptions on lines "
			end
			values = assumptions.collect {|x| x.is_a?(Numeric) ? x : x.join('-')}
			@wrapper.puts values.join ', '
		}
		# assumption counts
		blocks, lines = 0, 0
		assumptions.values.each {|assumptions|
			assumptions.each {|x|
				if x.is_a? Numeric
					lines += 1
        elsif x.first != :start and x.last != :end
					blocks += 1
				end
			}
		}
		counts = []
    counts << 'marker' if marker
		counts << "#{blocks} assume block" if blocks == 1
		counts << "#{blocks} assume blocks" if blocks > 1
		counts << "#{lines} assumption" if lines == 1
		counts << "#{lines} assumptions" if lines > 1
		raise if counts.empty?
		@wrapper.puts "proof incomplete due to #{counts.join ' and '}"
	end

  def axioms axioms
    raise if not @stack.empty?
		axioms.each {|filename, axiom_count|
			s = (axiom_count == 1 ? 'axiom' : 'axioms')
			@wrapper.puts "#{axiom_count} #{s} in #{filename}"
		}
	end

  def base_error message
    raise if not @stack.empty?
    @wrapper.puts "error: #{message}"
  end

  def begin_file filename
    @wrapper.puts if not @wrapper.clear?
		@stack << {file: filename, line: nil}
  end

  def conclude status
    raise if not @stack.empty?
    case status
      when :exited then @wrapper.puts 'proof incomplete due to exit'
      when :ok then @wrapper.puts 'proof successful!'
      else raise
    end
  end

  def end_error message
    raise if not @stack.empty?
    @wrapper.puts "error at end of input: #{message}"
  end

  def end_file
    raise if @stack.empty?
    if not @stack[-1][:line]
      @wrapper.puts "#{@stack[-1][:file]}: no lines to process"
    elsif not @wrapper.clear?
      @wrapper.puts
    end
    @stack.pop
  end

  def exit
    line = current_line
		@wrapper.puts if not @wrapper.clear?
		@wrapper.puts "exit at line #{line}: skipping remaining lines"
  end

  def file_message message
    raise if @stack.empty?
    @wrapper.puts if not @wrapper.clear?
		@wrapper.puts "#{@stack[-1][:file]}: #{message}"
  end

  def line i
    raise if @stack.empty?
    @wrapper.print "#{@stack[-1][:file]}: processing line" if @wrapper.clear?
		@wrapper.print " #{i}"
    @stack[-1][:line] = i
  end

  def line_error message
    line = current_line
    @wrapper.puts if not @wrapper.clear?
		@wrapper.puts "error at line #{line}: #{message}"
  end

  def line_message message
    line = current_line
    @wrapper.puts if not @wrapper.clear?
		@wrapper.puts "line #{line}: #{message}"
  end

  def line_message_block message
    line = current_line
    @wrapper.puts if not @wrapper.clear?
    @wrapper.puts
		@wrapper.puts "line #{line}: #{message}"
		@wrapper.puts
	end

  def message message
    @wrapper.puts if not @wrapper.clear?
		@wrapper.puts message
  end

  def option_message option, message
    line = current_line
    @wrapper.puts if not @wrapper.clear?
		@wrapper.puts "line #{line}: #{option} option: #{message}"
  end

  def parse_error message
    line = current_line
    @wrapper.puts if not @wrapper.clear?
    @wrapper.puts "parse failed at line #{line}: #{message}"
  end

	private #####################################################################

  def current_line
    raise if @stack.empty?
    @stack[-1][:line] or raise
  end
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

	def assume fileline
		@assumptions[current_file] << fileline if @assume_stack.empty?
	end

	def axiom
		@axioms[current_file] += 1
	end

	def begin_assume fileline
    if not @assume_stack.empty?
			@assume_stack << :nested
    elsif not @file_stack.empty?
			@assume_stack << [current_file, fileline]
    else
			@assume_stack << [nil, nil]
    end
	end

	def begin_file filename, include_line
		@file_stack << [filename, include_line]
	end

  def current_file
    @file_stack.last[0]
  end

	def end_file
		raise if @file_stack.empty? # nothing to end
		filename, line = @file_stack.pop
		return if @assume_stack.empty?
		if @assume_stack[0][0] == filename # assume began in or under this file
			@assumptions[filename] << [@assume_stack[0][1], :end]
			# make the assume begin at the include line in the file above
			@assume_stack[0] = [current_file, line] unless @file_stack.empty?
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