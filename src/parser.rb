require_relative 'grammar.rb'
require_relative 'grammar rules.rb'

class Parser
	def initialize
		array = grammar_rules
		grammar = Grammar.new array
		@grammar_parser = GrammarParser.new grammar
	end

	def block_comment input
		# returns blocks to be kept after removing block comments
		blocks = []
		nested = 0
		position = 0
		while true
			opening = input.index '/#', position
			closing = input.index '#/', position
			last_position = position
			if opening and (not closing or opening < closing) # opening is next
				blocks << [position, opening-1] if nested == 0 and opening > position
				nested += 1
				position = opening + 2
			elsif (closing and nested == 0) or (not closing and nested > 0)
				raise ParseException, 'parse failed: mismatched block comments'
			elsif closing # closing is next
				nested -= 1
				position = closing + 2
			else
				blocks << [position, input.length-1] if input.length > position
				break
			end
		end
		blocks
	end

	def convert_inequality relation, subtrees
		case relation
			when '<'
				operator = :predicate
				subtrees = [Tree.new('<', []), *subtrees]
			when '≤', '<='
				operator = :or
				subtrees = [
					Tree.new(:predicate, [Tree.new('<', []), *subtrees]),
					Tree.new(:equals, subtrees)
				]
      when '>'
				operator = :predicate
				subtrees = [Tree.new('<', []), *subtrees.reverse]
			when '≥', '>='
				operator = :or
				subtrees = [
					Tree.new(:predicate, [Tree.new('<', []), *subtrees.reverse]),
					Tree.new(:equals, subtrees)
				]
		end
		Tree.new operator, subtrees
	end

	def convert_set relation, subtrees
		case relation
			# any of {⊆, ⊊}, {⊆, ⊂}, {⊂, ⊊} may be desired, so we do not translate
			# between relations, other than flipping them
			when '⊆'
				operator = :predicate
				subtrees = [Tree.new('⊆', []), *subtrees]
      when '⊇'
				operator = :predicate
				subtrees = [Tree.new('⊆', []), *subtrees.reverse]
			when '⊊'
				operator = :predicate
				subtrees = [Tree.new('⊊', []), *subtrees]
			when '⊋'
				operator = :predicate
				subtrees = [Tree.new('⊊', []), *subtrees.reverse]
			when '⊂'
				operator = :predicate
				subtrees = [Tree.new('⊂', []), *subtrees]
      when '⊃'
				operator = :predicate
				subtrees = [Tree.new('⊂', []), *subtrees.reverse]
		end
		Tree.new operator, subtrees
	end

	def label_from_branch branch
		if branch.value == :label or branch.value == :label_same_line
			branch = branch.branches[0] 
		end
		raise unless [:label_name, :label_name_same_line].include? branch.value
		words = branch.branches.select {|branch|
      next false unless branch.value.is_a? Symbol
      (branch.value == :atom) ? true : raise
    }
		words.collect {|word| word.text}.join ' '		
	end

	def line_comment input
		# returns blocks to be kept after removing line comments
		blocks = []
		position = 0
		while true
			opening = input.index '#', position
			if opening
				blocks << [position, opening-1] if opening > position
				position = input.index "\n", opening
				break if not position
			else
				blocks << [position, input.length-1] if input.length > position
				break
			end
		end
		blocks
	end

	def normalize_whitespace! input
		node = (input.is_a?(GrammarTree) ? input.root : input)
		if node.value.is_a? String
			# strip and contract whitespace sequences to single spaces
			node.value = node.value.strip.gsub /\s+/, ' '
		end
		if node.branches
			node.branches.each {|branch| normalize_whitespace! branch}
		end
	end

	def parse_each input
		text, line_numbers = strip_comments input
		last_end = 0
		begin
			@grammar_parser.parse_each(text) {|grammar_tree, sentence, position|
=begin
				puts "sentence: #{sentence.inspect}\n\n"
				puts "grammar tree:"
				puts grammar_tree
				puts
=end
				line = line_numbers.call position
				begin
					action, content, reasons, label = process_statement grammar_tree
				rescue ParseException => e
					# The exceptions being caught here should perhaps be
					# thrown as ProofExceptions, so that ParseExceptions are reserved for
					# actual exceptions from the grammar parser.  Problem is giving
					# ProofExceptions a line number.
					raise ParseException.new "parse failed at line #{line}: #{e}", line
				end
=begin
				if content.is_a? Tree
					puts "parsed Tree:"
					p content
					puts
				end
=end
				yield sentence, action, content, reasons, label, line
				last_end = position + sentence.length
			}
		rescue GrammarParseException => e
=begin
      puts "\n", e.tree
=end
      # find first character after the last successful parse
			p = (last_end...text.length).find {|i| text[i].strip != ''}
			# report error between that character and current position
			line = line_numbers.call p
			newline = text.index "\n", p
			stop = (newline ? [e.position, newline].max : text.size)
			context = text[p...stop].strip.gsub /\s+/, ' '
			raise ParseException.new "parse failed at line #{line}: \"#{context}\"", line
		end
	end

	def process_atom_list node
		raise unless node.value == :atom_list
		variables, pending, condition_trees = [], [], []
		node.branches[0].branches.each {|branch|
			next if branch.value == ',' or branch.value.downcase == 'and'
			if branch.value == :definable or branch.value == :definable_raw
				pending << tree_from_grammar(branch)
			elsif branch.value == :condition
				right_side = tree_from_grammar branch.branches[1]
				condition_trees.concat pending.collect {|variable|
					if branch.branches[0].value == :inequality
						relation = branch.branches[0].branches[0].value
						convert_inequality relation, [variable, right_side]
					elsif branch.branches[0].value == :not_equal
						subtrees = [Tree.new(:equals, [variable, right_side])]
						Tree.new :not, subtrees
					elsif branch.branches[0].value.downcase == 'in'
						condition_subtrees = [Tree.new('in', []), variable, right_side]
						Tree.new :predicate, condition_subtrees
					elsif branch.branches[0].value == :set_relation
						relation = branch.branches[0].branches[0].value
						convert_set relation, [variable, right_side]
					else
						raise "unknown condition #{branch.branches[0].value.inspect}"
					end
				}
				variables.concat pending
				pending = []
			else
				raise "unknown branch value #{branch.value.inspect}"
			end
		}
		variables.concat pending
		if condition_trees.size >= 2
			condition_tree = Tree.new :and, condition_trees
		elsif condition_trees.size == 1
			condition_tree = condition_trees[0]
		end
		[variables, condition_tree]
	end

	def process_list_with_such node
		variables, condition = process_atom_list node.branches[0]
		raise if condition and contains_quantifiers? condition
		if (i = node.branches.index {|branch| branch.value == :with})
			with = tree_from_grammar node.branches[i+1]
			if with and contains_quantifiers? with
				raise ParseException.new '"with" cannot contain quantifiers'
			end
		end
		if (i = node.branches.index {|branch| branch.value == :such_that})
			such_that = tree_from_grammar node.branches[i+1]
		end
		[variables, condition, with, such_that]
	end

	def process_statement grammar_tree
		tree = grammar_tree
		normalize_whitespace! tree
		raise unless tree.root.value == :start
		first_branch = tree.root.branches[0]
		return :empty if first_branch.value == :ending
		return :now if first_branch.value == :now
		return :end if first_branch.value == :end
		return :exit if first_branch.value == :exit
		action, content, label = nil
		reasons = []

		label_branch = tree.root.branches.find {|branch| branch.value == :label}
		label = label_from_branch label_branch if label_branch
		update_label = proc {|branch|
			next unless branch.value == :label_same_line
			raise ParseException, 'multiple labels' if label
			label = label_from_branch branch
		}

		actions = [
			:include, :assume, :axiom, :suppose, :take, :derive, :so,
			:begin_assume, :end_assume
		]
		action_branch = tree.root.branches.find {|branch|
			actions.include? branch.value
		}
		raise 'could not find an action!' if not action_branch
		action = action_branch.value

		return action if action == :begin_assume or action == :end_assume

		if action == :include
			raise unless action_branch.branches.size == 4 # command, quotes around content
			return :include, action_branch.branches[2].text
		end

		content_branch = case action
			when :assume
				update_label.call action_branch.branches[1]
				action = :assume_schema if action_branch.branches[-2].text == 'schema'
				action_branch.branches[-1]
			when :axiom
				update_label.call action_branch.branches[1]
				action = :axiom_schema if action_branch.branches[-2].text == 'schema'
				action_branch.branches[-1]
			when :suppose
				update_label.call action_branch.branches[1]
				action_branch.branches[-1]
			when :take
				action = :suppose
				branch = action_branch.branches[0]
				raise unless branch.value == :take_label
				update_label.call branch.branches[1] if branch.branches.size > 1
				action_branch
			when :derive
				action_branch.branches[0]
			when :so
				if action_branch.branches[1].value == :assume
					action = :so_assume
					action_branch = action_branch.branches[1]
					update_label.call action_branch.branches[1]
					if action_branch.branches[-2].text == 'schema'
						raise ParseException, 'cannot use "so" with schema'
					end
					action_branch.branches[-1]
				else
					action = :so
					update_label.call action_branch.branches[1]
					action_branch.branches[-1]
				end
		end

		content = Content.new tree_from_grammar content_branch, true

		proof_branch = tree.root.branches.find {|branch| branch.value == :proof}
		if proof_branch
			if action == :so or action == :so_assume
				raise ParseException, 'cannot use "so" with proof block'
			end
			raise unless action == :derive
			action = :proof
		end

		by_branch = tree.root.branches.find {|branch| branch.value == :by}
		if by_branch
			if action == :assume_schema
				raise ParseException, 'cannot use "by" with schema'
			end
			branches = by_branch.branches.select {|branch| branch.value == :label_name}
      raise if branches.empty?
			reasons.concat branches.collect {|branch| label_from_branch branch}
		end

		if action == :assume_schema or action == :axiom_schema
			if not Schema.check_schema_format content.sentence
				raise ParseException, 'unrecognized schema format'
			end
		else
			if content.sentence.contains? :quote
				raise ParseException, 'cannot use `...` outside schema'
			elsif content.sentence.contains? :for_all_meta
				raise ParseException, 'cannot use "for all meta" outside schema'
			elsif content.sentence.contains? :substitution
				raise ParseException, 'cannot use {...} outside schema'
			end
		end

		[action, content, reasons, label]
	end

  def standardize_operator operator
    case operator
      when '/' then '÷'
      when '**' then '^'
      else operator
    end
  end

	def strip_comments input
		manager = LineNumberManager.new input
		blocks = block_comment manager.text
		manager.use blocks
		blocks = line_comment manager.text
		manager.use blocks
		[manager.text, manager.line_numbers]
	end

	def tree_for_subject subject, node
		subtrees = case node.value
			when :category then node.branches
			when :quantified then node.branches[1].branches
			when :word then [node]
		end
		if subtrees.length >= 2 and subtrees[-2].value == :preposition
			predicate = tree_from_grammar subtrees[-3]
			other = tree_from_grammar subtrees[-1]
			preposition_tree = Tree.new :predicate, [
				predicate, subject, other
			]
			subtrees = subtrees[0...-3]
		end
		subtrees = subtrees.collect {|subtree|
			predicate = tree_from_grammar subtree
			Tree.new :predicate, [predicate, subject]
		}
		subtrees << preposition_tree if preposition_tree
		conjunction_tree subtrees
	end

	def tree_from_grammar node, open_to_bind = false
		case node.value
			when :exp, :exp1, :exp2, :exp3, :exp4, :exp5, :exp6
				if node.branches.size == 1
					return tree_from_grammar(node.branches[0], open_to_bind)
        elsif node.branches.size == 3 and [:is, :is_not].include? node.branches[1].value
					subject = tree_from_grammar node.branches[0]
					tree = tree_for_subject subject, node.branches[2]
					return case node.branches[1].value
						when :is then tree
						when :is_not then Tree.new :not, [tree]
					end
				elsif node.branches.size >= 3 and [:and, :or].include? node.branches[1].value
					operator = node.branches[1].value
					branches = node.branches.select.each_with_index {|branch, i| i.even?}
					subtrees = branches.collect {|branch| tree_from_grammar branch}

					# check that "is" is not used with "and/or" plus an atom
					subtrees.each_with_index {|subtree, i|
						next unless subtree.subtrees.empty? and i > 0 # atom
						prev = node.branches[(i-1)*2]
						is = false
						is = true if [:every, :some, :no].include? prev.branches[0].value
						if prev.branches.size >= 2 and
								[:is, :is_not, :is_in, :is_not_in].include? prev.branches[1].value
							is = true 
						end
						raise ParseException, 'ambiguous expression' if is
					}
				elsif node.branches.size >= 3 and [
						:plus, :union, :intersection, :times
					].include? node.branches[1].value
					operator = node.branches[1].branches[0].value
					branches = node.branches.select.each_with_index {|branch, i| i.even?}
					subtrees = branches.collect {|branch| tree_from_grammar branch}
					operator_tree = Tree.new operator, []
					tree = Tree.new :predicate, [operator_tree, subtrees[0], subtrees[1]]
					subtrees[2..-1].each {|subtree|
						tree = Tree.new :predicate, [operator_tree, tree, subtree]
					}
					return tree
				elsif node.branches.size == 3
					operator = node.branches[1].value.downcase.to_sym
					subtrees = [
						tree_from_grammar(node.branches[0]),
						tree_from_grammar(node.branches[2])
					]
					if [:'-', :'/', :'÷', :'**', :'^'].include? operator
            operator = standardize_operator operator.to_s
						subtrees = [Tree.new(operator, [])] + subtrees
						operator = :predicate
					elsif operator == :'='
						operator = :equals
					elsif operator == :not_equal
						operator = :not
						subtrees = [Tree.new(:equals, subtrees)]
					elsif operator == :inequality
						relation = node.branches[1].branches[0].value
						inequality_tree = convert_inequality relation, subtrees
						operator, subtrees = inequality_tree.operator, inequality_tree.subtrees
          elsif operator == :is_in
            operator = :predicate
            subtrees = [Tree.new('in', []), *subtrees]
          elsif operator == :is_not_in
            operator = :not
            subsubtrees = [Tree.new('in', []), *subtrees]
            subtrees = [Tree.new(:predicate, subsubtrees)]
          elsif operator == :set_relation
						relation = node.branches[1].branches[0].value
						set_tree = convert_set relation, subtrees
						operator, subtrees = set_tree.operator, set_tree.subtrees
          elsif operator == :custom
						operator = :predicate
						custom = tree_from_grammar node.branches[1].branches[0]
						subtrees = [custom, *subtrees]
          end
        end
			when :every, :some, :no
				subject = Tree.new ':x', [] # can never appear in a proof
				t1 = tree_for_subject subject, node.branches[1]
				case node.branches[2].value
					when :is, :is_not
						t2 = tree_for_subject subject, node.branches[3]
						t2 = Tree.new :not, [t2] if node.branches[2].value == :is_not
					when :is_in, :is_not_in
						t2 = tree_from_grammar node.branches[3]
						t2 = Tree.new :predicate, [Tree.new('in', []), subject, t2]
						t2 = Tree.new :not, [t2] if node.branches[2].value == :is_not_in
				end
				return case node.value
					when :every
						Tree.new :for_all, [subject, Tree.new(:implies, [t1, t2])]
					when :some
						Tree.new :for_some, [subject, Tree.new(:and, [t1, t2])]
					when :no
						t2 = Tree.new :not, [t2]
						Tree.new :for_all, [subject, Tree.new(:implies, [t1, t2])]
				end
			when :operand
				tree = tree_from_grammar node.branches[0]
				return tree unless node.branches[0].value == :operand_base
				node.branches[1..-1].each {|branch|
					if branch.value == :subst
						map = tree_from_grammar branch
						tree = Tree.new :substitution, [tree, map]
					elsif branch.value == :params
						list = tree_from_grammar branch
						tree = Tree.new :predicate, [tree, *(list.subtrees[1..-1])]
					else
						raise
					end
				}
				return tree
			when :operand_base
				if node.branches.size == 3 and node.branches[0].value == '(' and node.branches[2].value == ')'
					return tree_from_grammar(node.branches[1])
				elsif node.branches.size == 3 and node.branches[0].value == '|' and node.branches[2].value == '|'
					tree = tree_from_grammar node.branches[1]
					operator = :predicate
					subtrees = [Tree.new('||', []), tree]
				elsif node.branches.size == 1
					return tree_from_grammar(node.branches[0])
				end
			when :string
				# for now strings are predicates, but maybe they could just be
				# atoms in quotation marks?
				raise unless node.branches[0].value == '"'
				raise unless node.branches[-1].value == '"'
				if node.branches.size == 2
					return Tree.new :predicate, [
						Tree.new('string', []), Tree.new('""', [])
					]
				end
				subtrees = node.branches[1...-1].collect {|subtree|
#					if subtree.value == :meta
#						tree_from_grammar subtree
#					else
						Tree.new :predicate, [
							Tree.new('string', []),
							Tree.new('"' + subtree.text + '"', [])
						]
#					end
				}
				tree = subtrees[0]
				subtrees[1..-1].each {|subtree|
					tree = Tree.new :predicate, [Tree.new('+',[]), tree, subtree]
				}
				return tree
#			when :meta
#				raise unless node.branches.size == 2
#				raise unless node.branches[0].value == '$'
#				operator = :meta
#				subtrees = [tree_from_grammar(node.branches[1])]
			when :quote
				raise unless node.branches.size == 3
				raise unless node.branches[0].value == '`' and node.branches[2].value == '`'
        operator = :quote
        subtrees = [tree_from_grammar(node.branches[1])]
			when :list, :params
				if node.branches.size == 2
					# empty list is not a predicate because predicates need >= 1 arguments
					operator = '[]' 
					subtrees = []
				else
					operator = :predicate
					branches = node.branches.select.each_with_index {|branch, i| i.odd?}
					subtrees = branches.collect {|branch| tree_from_grammar branch}
					subtrees.unshift Tree.new('list', [])
				end
			when :set
				if node.branches.size == 2
					# empty set is not a predicate because predicates need >= 1 arguments
					operator = '{}'
					subtrees = []
				else
					operator = :predicate
					branches = node.branches.select.each_with_index {|branch, i| i.odd?}
					subtrees = branches.collect {|branch| tree_from_grammar branch}
					subtrees.unshift Tree.new('{}', [])
				end
			when :map, :subst
				operator = :predicate
				subtrees = node.branches[1..-1].each_slice(4).collect {|branches|
					Tree.new :predicate, [
						Tree.new('list', []),
						tree_from_grammar(branches[0]),
						tree_from_grammar(branches[2]),
					]
				}
				subtrees.unshift Tree.new('map', [])
=begin
			when :predicate
				return tree_from_grammar(node.branches[0]) if node.branches.size == 1
				operator = :predicate
				if node.branches[0].value == '['
					subtrees = node.branches.select.each_with_index {|branch, i| i.odd?}
					subtrees.collect! {|subtree| tree_from_grammar subtree}
					subtrees.unshift Tree.new('list', [])
				else
					subtrees = node.branches.select.each_with_index {|branch, i| i.even?}
					subtrees.collect! {|subtree| tree_from_grammar subtree}
				end
=end
			when :word, :word_same_line, :definable, :definable_raw, :atom
				operator = standardize_operator node.text
				subtrees = []
			when :boolean
				case node.branches[0].text
					when 'true'
						return tree_for_true
					when 'false', 'contradiction'
						return tree_for_false
				end
			when :negative
				operator = :predicate
				if node.branches.size == 2
					subtree = tree_from_grammar node.branches[1]
				else
					raise unless node.branches[1].text == '[' and node.branches[3].text == ']'
					subtree = tree_from_grammar node.branches[2]
				end
				subtrees = [Tree.new('-',[]), subtree]
			when :square_root
				operator = :predicate
				raise unless node.branches.size == 2
				subtree = tree_from_grammar node.branches[1]
				subtrees = [Tree.new('√',[]), subtree]
			when :thesis
				operator = node.text
				subtrees = []
			when :prefix
				return tree_from_grammar(node.branches[0], open_to_bind)
			when :not
				operator = :not
				subtrees = [tree_from_grammar(node.branches[1])]
			when :if
				operator = :implies
				subtrees = [
					tree_from_grammar(node.branches[1]), tree_from_grammar(node.branches[3])
				]
			when :universal, :existential, :take, :no_existential, :define, :universal_meta
				variables, condition, with, such_that = process_list_with_such node.branches[1]
				if node.branches.size > 2
					raise unless node.branches[2].value == ','
					raise if node.branches.size > 4 # multiple expressions after comma
          body = tree_from_grammar node.branches[3]
				end
				return case node.value
					when :universal, :universal_meta
						raise ParseException, '"with" not allowed in universal quantifier' if with
						antecedent = conjunction_tree [condition, such_that].compact
						tree = antecedent ? Tree.new(:implies, [antecedent, body]) : body
						operator = :for_all if node.value == :universal
						operator = :for_all_meta if node.value == :universal_meta
		        variables.reverse.each {|variable|
							tree = Tree.new operator, [variable, tree]
						}
						tree
					when :no_existential
						raise ParseException, '"with" not allowed in negative quantifier' if with
						tree = conjunction_tree [condition, such_that, body].compact
		        variables.reverse.each {|variable|
							tree = Tree.new :for_some, [variable, tree].compact
						}
						Tree.new :not, [tree]
					when :define, :take
						raise unless open_to_bind and not body
						tie_in = conjunction_tree [condition, with].compact
						variables = variables.collect {|tree| tree.operator}
						Bind.new variables, such_that, tie_in, (node.value == :define)
					when :existential
						if open_to_bind
							tie_in = conjunction_tree [condition, with].compact
							without_tie_in = conjunction_tree [such_that, body].compact
							variables = variables.collect {|tree| tree.operator}
							Bind.new variables, without_tie_in, tie_in, false
						else
							raise ParseException, '"with" not allowed in nested quantifier' if with
							tree = conjunction_tree [condition, such_that, body].compact
			        variables.reverse.each {|variable|
								tree = Tree.new :for_some, [variable, tree].compact
							}
							tree
						end
				end
			when :let
				raise unless open_to_bind
				left = tree_from_grammar node.branches[1]
				right = tree_from_grammar node.branches[3]
				without_tie_in = Tree.new :equals, [left, right]
				return Bind.new [left.operator], without_tie_in, nil, false
		end
		# make sure something actually made the tree
		raise "#{node.value.inspect} not handled" unless operator and subtrees
		Tree.new operator, subtrees
	end
end

class Tree
	attr_reader :operator, :subtrees

  def initialize operator, subtrees
		subtrees.each {|subtree|
			next if subtree.is_a? self.class				
			raise "tree is a #{self.class}, but subtree is a #{subtree.class}!"
		}
    raise if not operator
		case operator
			when :not
				raise unless subtrees.size == 1
			when :for_all, :for_all_meta
				raise unless subtrees.size == 2 and not subtrees[0].operator.is_a? Symbol
			when :for_some
				raise unless [1, 2].include? subtrees.size
				raise if subtrees[0].operator.is_a? Symbol
			when :and, :or
				raise unless subtrees.size >= 2
			when :implies, :iff
				raise unless subtrees.size == 2
			when :equals
				raise unless subtrees.size == 2
				if subtrees.any? {|subtree| subtree.boolean?}
					raise ParseException, 'boolean operator used as a term'
				end
			when :predicate
				raise unless subtrees.size >= 2 # and not subtrees[0].operator.is_a? Symbol
				if subtrees.any? {|subtree| subtree.boolean?}
					raise ParseException, 'boolean operator used as a term'
				end
      when :quote
        raise unless subtrees.size == 1
			when :substitution
				raise unless subtrees.size >= 2
				raise unless subtrees[1].operator == :predicate
				raise unless subtrees[1].subtrees[0].operator == 'map'
			else
				raise "unknown operator #{operator.inspect}" if operator.is_a? Symbol
				raise "leaf #{operator} initialized with subtrees" unless subtrees.empty?
				raise "unexpected '=' instead of :equals" if operator == '='
		end
	  @operator = operator
		@subtrees = subtrees
	end

	def boolean?
		booleans = [:not, :for_all, :for_some, :and, :or, :implies, :iff, :equals]
		booleans.include? @operator
	end

  # def bound_variables
	# 	result = []
	# 	result << @subtrees[0].operator if [:for_all, :for_some].include? @operator
	# 	result << @subtrees.collect {|subtree| subtree.bound_variables}
	# 	result.flatten.uniq
  # end

	def contains? x
		return true if @operator == x
		@subtrees.any? {|subtree| subtree.contains? x}
	end
	
  def eql? other # hash/set equality, also used by uniq, &, -
    other.is_a?(self.class) and to_s == other.to_s
  end

	def free_variables
		return [@operator] unless @operator.is_a? Symbol
#		subtrees = (@operator == :predicate ? @subtrees[1..-1] : @subtrees)
#		result = subtrees.collect {|subtree| subtree.free_variables}.flatten.uniq	
		result = @subtrees.collect {|subtree| subtree.free_variables}.flatten.uniq
		result.delete @subtrees[0].operator if [:for_all, :for_some].include? @operator
		result
	end

  def hash # has to be overriden along with eql?, apparently
    to_s.hash
  end

  def inspect level = 0, result = ''
		result << '  ' * level << @operator.to_s << "\n"
		@subtrees.each {|subtree|	subtree.inspect level+1, result}
		result.chomp! if level == 0
		result
	end

=begin
	def predicates
		return [] unless @operator.is_a? Symbol
		result = []
		if @operator == :predicate
			result = [[@subtrees[0].operator, @subtrees.size-1]]
		end
		result.concat(@subtrees.collect {|subtree| subtree.predicates}.flatten(1))
		result.uniq
	end
=end

  def to_s
		infixes = [:and, :or, :implies, :iff, :equals]
		case @operator
			when :not
				operand = @subtrees[0].to_s
				if infixes.include? @subtrees[0].operator
					operand = '(' + operand + ')'
				end
				'not ' + operand
			when :for_all, :for_some, :for_all_meta
				return "there is a #{@subtrees[0]}" if @subtrees.size == 1
				operator = @operator.to_s.gsub '_', ' '
				variable = @subtrees[0].to_s
				expression = @subtrees[1].to_s
				if infixes.include? @subtrees[1].operator
					expression = '(' + expression + ')'
				end
				"#{operator} #{variable}, #{expression}"
			when :predicate
				if @subtrees[0].operator == 'map'
					arguments = @subtrees[1..-1].collect {|subtree|
						raise unless subtree.operator == :predicate
						raise unless subtree.subtrees.size == 3
						raise unless subtree.subtrees[0].operator == 'list'
						subtree.subtrees[1].to_s + ':' + subtree.subtrees[2].to_s
					}.join ', '
					"{#{arguments}}"
				else
					arguments = @subtrees[1..-1].collect {|subtree| subtree.to_s}.join ', '
					if @subtrees[0].operator == '||' and @subtrees[0].subtrees.empty?
						raise unless @subtrees.size == 2
						"|#{arguments}|"
					else
						needs_parens = true
						needs_parens = false if @subtrees[0].operator == :predicate
						needs_parens = false if not @subtrees[0].operator.is_a? Symbol
						result = (needs_parens ? "(#{@subtrees[0]})" : "#{@subtrees[0]}")
						result + "[#{arguments}]"
					end
				end
			when *infixes
				operands = @subtrees.each_with_index.collect {|subtree, i|
					if subtree.operator == :predicate or subtree.operator == :substitution
						subtree.to_s
					elsif not subtree.operator.is_a?(Symbol)
						subtree.to_s
					elsif i == @subtrees.size - 1 and not infixes.include?(subtree.operator)
						subtree.to_s
					else
						'(' + subtree.to_s + ')'
					end
				}
				operator_string = (@operator == :equals ? '=' : @operator.to_s)
				operands.join(' ' + operator_string + ' ')
#      when :meta
#				operand = @subtrees[0].to_s
#				if @subtrees[0].operator.is_a? Symbol
#					operand = '(' + operand + ')'
#				end
#		  	'$' + operand
      when :quote
			  '`' + @subtrees[0].to_s + '`'
			when :substitution
				@subtrees[0].to_s + @subtrees[1].to_s
			else
				raise "unknown operator #{@operator.inspect}" if @operator.is_a? Symbol
				@operator
		end
  end
end

class Bind
	attr_reader :variables, :body_with_tie_in, :tie_in

  def initialize variables, body_without_tie_in, tie_in, is_definition
		if variables.empty?
			raise unless body_without_tie_in
			raise if tie_in or is_definition
		end
		raise if tie_in and contains_quantifiers? tie_in
		@variables = variables
		@body_with_tie_in = conjunction_tree [tie_in, body_without_tie_in].compact
		@tie_in = tie_in
		@is_definition = is_definition
	end

	def definition?
		@is_definition
	end
end

class Content # or Statement
	attr_reader :sentence, :binding

	def initialize input
		case input
			when Tree
				@sentence = input
				@binding = Bind.new [], @sentence, nil, false
			when Bind
				@binding = input
				if @binding.body_with_tie_in
					@sentence = bind_variables @binding.variables, @binding.body_with_tie_in, :for_some
				else
					@sentence = tree_for_true
				end
			else raise
		end
	end

  def binding?
		@binding.variables.any?
  end
end

class LineNumberManager
	# keeps track of line numbers after removing blocks (e.g. comments)

	attr_reader :text

	def initialize input
		@input = input
		@line_positions = []
		input.chars.each_index {|i|
			@line_positions << i if i == 0 or input[i-1] == "\n"
		}

		@blocks = [[0, input.size-1]]
		@text = input
	end

	def input_positions
		passed = 0
		k = 0
		lambda {|i_in_text|
			while k < @blocks.size
				i,j = @blocks[k]
				if passed + j-i+1 > i_in_text
					return i + i_in_text - passed
				else
					passed += j-i+1
				end
				k += 1
			end
			raise "no position #{i_in_text} (length of text is #{@text.length})"
		}
	end

	def line_numbers
		positions = input_positions
		line_index = 0
		lambda {|i_in_text|
			i_in_input = positions.call i_in_text
			line_index = (line_index...@line_positions.size).find {|i|
				next true if i == @line_positions.size-1
				@line_positions[i+1] > i_in_input
			}
			line_index + 1
		}
	end

	def use blocks
		# first we map the text positions in blocks to input positions
		positions = input_positions
		blocks = blocks.collect {|i,j|
			[positions.call(i), positions.call(j)]
		}
		# now we split up the blocks to fit in the existing @blocks
		new_blocks = []
		k = 0
		blocks.each {|i,j|
			# find the block which contains the start of this one
			k += 1 until @blocks[k][1] >= i
			if @blocks[k][1] >= j 
				# the block we found completely contains this one
				new_blocks << [i,j]
			else
				# the block we found only partially contains this one
				new_blocks << [i, @blocks[k][1]]
				k += 1
				# find the block which contains the end of this one, adding the
				# intervening blocks
				until @blocks[k][1] >= j
					new_blocks << @blocks[k]
					k += 1
				end
				# add the block which contains the end of this one
				new_blocks << [@blocks[k][0], j]
			end
		}
		# finally, we update @blocks and @text
		@blocks = new_blocks
		@text = @blocks.collect {|i,j| @input[i..j]}.join
	end
end
