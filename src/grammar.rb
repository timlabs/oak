require 'set'
require 'strscan'

class Grammar
	attr_reader :non_terminals, :start_symbol

	class Rule
		attr_reader :state, :input, :next_state, :catch, :multiple

		def initialize state, input, next_state, catch, multiple = nil
			@state, @input, @next_state, @catch, @multiple = 
				state, input, next_state, catch, multiple
			@input = Regexp.new Regexp.escape(@input) if @input.is_a? String
		end
	end

  def initialize rules
		@rules = []
		rules.each {|rule|
			state, inputs, next_state, catch = rule
			raise "bad rule format: #{rule}" if not state or (catch and catch != :catch)
			if not inputs.is_a? Array
				@rules << Rule.new(state, inputs, next_state, catch)
			else
				# make a dummy state which can be used to catch errors from the real inputs
				dummy = @rules.size.to_s.to_sym
				@rules << Rule.new(state, dummy, next_state, catch, :multiple)
				inputs.each_with_index {|input, index|
					# here we generate symbols for implicit states in input arrays
					this_state = (index == 0) ? dummy : @rules.size.to_s.to_sym
					if index == inputs.size - 1
						this_next_state = :end
					else
						this_next_state = (@rules.size + 1).to_s.to_sym
					end
					@rules << Rule.new(this_state, input, this_next_state, catch)
				}
			end
		}
		@non_terminals = @rules.collect {|rule| rule.state}.to_set
		inputs = @rules.collect {|rule| rule.input}
		symbol_inputs = inputs.select {|input| input.is_a? Symbol}
		unrecognized = symbol_inputs - @non_terminals.to_a - [:else, :eof]
		raise "unrecognized inputs: #{unrecognized}" unless unrecognized.empty?
		@start_symbol = @rules[0].state
		@rules = @rules.group_by {|rule| rule.state}
	end

	def [] non_terminal
		@rules[non_terminal] or []
	end
end

class GrammarParser
	def initialize grammar
		@grammar = grammar
	end

	def match input
		if input == :else
			true
		elsif input == :eof
			@scanner.eos?
		elsif @grammar.non_terminals.include? input
			parse_from input
		elsif match_string = @scanner.scan(input)
			@tree.bloom match_string
			true
		else
			false
		end
	end

=begin
	def parse program
		@scanner = StringScanner.new program
		@tree = GrammarTree.new
		parse_from @grammar.start_symbol, true
		@tree
	end
=end

	def parse_each program
		@scanner = StringScanner.new program
		last_pos = @scanner.charpos
		until @scanner.eos?
			@tree = GrammarTree.new
			parse_from @grammar.start_symbol, true
			yield @tree, program[last_pos...@scanner.charpos], last_pos
			last_pos = @scanner.charpos
		end
	end

	def parse_from state, top = false
		top ? @tree.root(state) : @tree.branch(state)
		parsed = while true
			last_pos = @scanner.pos
			last_active = @tree.active
			found = @grammar[state].find {|rule|
				begin
					match rule.input
				rescue GrammarParseException => exception
					unless rule.catch
						if rule.multiple
							# remove dummy branch which was just added, replacing it with its children
							last_active.branches[-1..-1] = last_active.branches[-1].branches
							# take responsibility for exception if exception state is a dummy value
							if exception.state.to_s.to_i.to_s == exception.state.to_s
								exception.state = state 
							end
						end
						raise 
					end
					@scanner.pos = last_pos
					@tree.prune until @tree.active == last_active
					false
				end
			}
			break false if not found
			if found.multiple
				# remove dummy branch which was just added, replacing it with its children
				last_active.branches[-1..-1] = last_active.branches[-1].branches
			end
			break true if found.next_state == :end
			state = found.next_state
		end
		committed = (not @tree.active.branches.empty?)
		@tree.retract if parsed
		@tree.prune if not parsed and not committed
		return parsed if parsed or (not top and not committed)
		raise GrammarParseException.new @tree, state, @scanner
	end
end

class GrammarParseException < StandardError
	attr_reader :scanner, :tree
	attr_accessor :state
	
	def initialize tree, state, scanner
		@tree = tree
		@state = state
		@scanner = scanner
	end
	
	def position
		@scanner.charpos
	end

	def to_s
		rest_to_show = @scanner.rest.inspect[0..80]
		"\n#{@tree}parse failed in #{@state.inspect} at #{rest_to_show}"
	end
end

class GrammarTree
	attr_reader :active

	class Node
		attr_accessor :branches, :parent, :value

		def initialize value, parent, leaf = nil
			@value, @parent = value, parent
			@branches = [] unless leaf
		end

		def text
			return @value if not @branches
			@branches.collect {|branch| branch.text}.join
		end

		def to_s prefix = '1'
			result = prefix + ' ' + @value.inspect + "\n"
			if @branches
				@branches.each_with_index {|branch, index|
					new_prefix = prefix + '.' + (index + 1).to_s
					result << branch.to_s(new_prefix)
				}
			end
			result
		end

#		def to_s indent = 0
#			result = ' ' * indent + @value.inspect + "\n"
#			@branches.each {|branch| result << branch.to_s(indent + 1)} if @branches
#			result
#		end
	end

	def bloom string
		@active.branches << Node.new(string, @active, :leaf)
	end

	def branch symbol
		@active.branches << Node.new(symbol, @active)
		@active = @active.branches[-1]
	end

  def prune
		if @active == @root
			@active, @root = nil, nil
		else
			@active.parent.branches.delete @active
			@active = @active.parent
		end
	end

	def retract
		@active = @active.parent
	end

	def root value = nil
		return @root if not value
		@root = Node.new value, nil
		@active = @root
	end

	def to_s
		@root.to_s
	end
end
