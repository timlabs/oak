require 'io/console'

class WordWrapper
	def initialize
    @indent = 2
		@width = IO.console.winsize[1] - 1 # subtract 1 for portability
		@position = 0
	end

  def clear?
    @position == 0
  end

	def print s
    s.to_s.each_line {|line|
      if line.end_with? "\n"
        puts line.chomp
      else
        word_wrap line
      end
    }
	end

	def puts s = ''
		print s
		$stdout.puts
		@position = 0
	end

	def word_wrap s
    if @position == :wrapping # waiting to go to next line and indent
      s = s.lstrip
      return if s.empty?
      $stdout.puts
      $stdout.print ' ' * @indent
      @position = @indent
      word_wrap s
    elsif s.length <= @width-@position # fits on this line
      $stdout.print s
      @position += s.length
    else # wrap to next line
			i = s.rindex ' ', @width-@position
			if i # break it at the space
				$stdout.print s[0...i].rstrip
        s = s[i..-1]
      elsif @position <= @indent # no choice but to truncate it
				$stdout.print s[0...@width-@position]
        s = s[@width-@position..-1]
      end
      @position = :wrapping
			word_wrap s
    end
  end
end

def bind_variables variables, body, quantifier
	if body
		to_bind = variables & body.free_variables # only bind those that need it
	else
		raise unless quantifier == :for_some
		to_bind = variables
	end
	return body if to_bind.empty?
	variables_tree = Tree.new to_bind, []
	Tree.new quantifier, [variables_tree, body].compact
end

def conjuncts trees
	# seems to have no effect on the prover, and is easier to read!
	trees.collect {|tree|
		next [tree] unless tree.operator == :and
		conjuncts tree.subtrees
	}.flatten
end

def conjunction_tree trees
	trees = conjuncts trees
	return nil if trees.empty?
	return trees[0] if trees.size == 1
	Tree.new :and, trees
end

def contains_quantifiers? tree
	Tree::Quantifiers.any? {|quantifier| tree.contains? quantifier}
end

def equal_up_to_variable_names? tree1, tree2, refs1 = {}, refs2 = {}, level = 0
	# check whether tree1 and tree2 are equal up to variable renaming
	return false unless tree1.operator.class == tree2.operator.class
	if tree1.operator.is_a? Symbol
		return false unless tree1.operator == tree2.operator
		return false unless tree1.subtrees.size == tree2.subtrees.size
		pairs = [tree1.subtrees, tree2.subtrees].transpose
		case tree1.operator
			when *Tree::Quantifiers
				last1, last2 = {}, {}
				zipped = tree1.subtrees[0].operator.zip tree2.subtrees[0].operator
				zipped.each_with_index {|(var1, var2), i|
					refs1[var1], last1[var1] = [level,i], refs1[var1]
					refs2[var2], last2[var2] = [level,i], refs2[var2]
				}
				result = pairs[1..-1].all? {|subtree1, subtree2|
					equal_up_to_variable_names? subtree1, subtree2, refs1, refs2, level+1
				}
				zipped.each_with_index {|(var1, var2), i|
					last1[var1] ? (refs1[var1] = last1[var1]) : (refs1.delete var1)
					last2[var2] ? (refs2[var2] = last2[var2]) : (refs2.delete var2)
				}
				result
			when :not, :and, :or, :implies, :iff, :equals, :predicate
				pairs.all? {|subtree1, subtree2|
					equal_up_to_variable_names? subtree1, subtree2, refs1, refs2, level+1
				}
			else raise
		end
	elsif tree1.operator.is_a? String
		if refs1[tree1.operator] and refs2[tree2.operator]
			refs1[tree1.operator] == refs2[tree2.operator] # both variables
		elsif refs1[tree1.operator] or refs2[tree2.operator]
			false # one is a constant, the other is a variable
		else
			tree1.operator == tree2.operator # both constants
		end
	else
		raise
	end
end

def find_minimal_subsets_from_results array, results = {}
	# find the minimal subsets of array which are true in results, assuming that
	# if a given set is false, all of its subsets are false
	set = array.to_set
	raise unless results.has_key? set
	result = results[set]
	return [] if result == false
	subarrays = array.combination array.size-1
	minimal = subarrays.collect {|subarray|
		find_minimal_subsets_from_results subarray, results
	}.flatten(1).uniq
	(minimal.empty? and result == true) ? [array] : minimal
end

def find_minimal_subsets input_array
	# find the minimal subsets for which yield returns true, assuming that if it
	# returns false for a given set, it will return false for all of its subsets,
	# and that order and duplicates do not matter
	input_array = input_array.uniq
	pending, results = [input_array], {}
	until pending.empty?
		array = pending.shift
		set = array.to_set
		next if results.has_key? set
		if results.any? {|key, result| result == false and set.subset? key}
			results[set] = false
		else
			results[set] = yield array
		end
		next if results[set] == false
		array.combination(array.size-1).each {|subarray| pending << subarray}
	end
	find_minimal_subsets_from_results input_array, results
end

def first_orderize tree, by_arity = false
	subtrees = tree.subtrees.collect {|subtree| first_orderize subtree, by_arity}
	if tree.operator == :predicate
		i = (by_arity ? subtrees.size.to_s : '')
		Tree.new :predicate, [Tree.new("apply#{i}", []), *subtrees]
	else
		Tree.new tree.operator, subtrees
	end
end

def implication_tree antecedents, consequent
	antecedent = conjunction_tree antecedents.compact
	return consequent if not antecedent
	Tree.new :implies, [antecedent, consequent]
end

def new_name names, prefix = 'x'
	# make a guess, for speed!
	name = "#{prefix}_#{names.size}"
	return name if not names.include? name
	# otherwise, find the lowest available
	options = (0..names.size).collect {|i| "#{prefix}_#{i}"}
	available = options - names
	raise if available.empty?
	available.first
end

def new_names used, count, prefix = 'x'
	used = used.dup
	count.times.collect {
		name = new_name used, prefix
		used << name
		name
	}
end

def replace_empty_quantifiers tree
  # we assume that the domain is not empty, and replace
  # each occurrence of "there is an x" with a tautology
  if tree.operator == :for_some and not tree.subtrees[1]
		tree_for_true
  else
    subtrees = tree.subtrees.collect {|subtree|
      replace_empty_quantifiers subtree
    }
    Tree.new tree.operator, subtrees
  end
end

def replace_for_at_most_one tree
	# for at most one a,b,c, p[a,b,c]
	#   becomes
	# for some a',b',c',
	# 	for all a,b,c,
	#     p[a,b,c] implies (a=a' and b=b' and c=c')
  subtrees = tree.subtrees.collect {|subtree| replace_for_at_most_one subtree}
	if tree.operator == :for_at_most_one
		variables, body = tree.subtrees[0].operator, tree.subtrees[1]
		used = tree.free_variables + variables
		primes = new_names used, variables.size, 'at_most_one'
		equalities = conjunction_tree variables.each_index.collect {|i|
			Tree.new :equals, [Tree.new(variables[i],[]), Tree.new(primes[i],[])]
		}
		tree = body ? Tree.new(:implies, [body, equalities]) : equalities
		tree = Tree.new :for_all, [Tree.new(variables,[]), tree]
		Tree.new :for_some, [Tree.new(primes,[]), tree]
	else
    Tree.new tree.operator, subtrees
	end
end

def self_implication? tree
	tree.operator == :implies and equal_up_to_variable_names? *tree.subtrees
end

def substitute tree, substitution, bound = [] # faster than Set for some reason
	# performs substitution on tree, where substitution keys are strings and
	# values are trees.  does not substitute again within the values.
  case tree.operator
		when *Tree::Quantifiers
			return tree if tree.subtrees.size == 1 # empty quantifier body
      variables = tree.subtrees[0].operator
			subtree = substitute tree.subtrees[1], substitution, (bound + variables)
			if subtree.equal? tree.subtrees[1]
				tree
			else
				Tree.new tree.operator, [tree.subtrees[0], subtree]
			end
		when :and, :or, :not, :implies, :iff, :equals, :predicate
			subtrees = tree.subtrees.collect {|subtree|
				substitute subtree, substitution, bound
			}
			if subtrees.each_index.all? {|i| subtrees[i].equal? tree.subtrees[i]}
				tree
			else
				Tree.new tree.operator, subtrees
			end
    when String
			return tree if not substitution.has_key? tree.operator
			return tree if bound.include? tree.operator
			replacement = substitution[tree.operator]
			conflict = (bound & replacement.free_variables).first
      # error if substitution contains quantified variable
			raise SubstituteException, conflict if conflict
			replacement
		else
			raise "unexpected operator #{tree.operator.inspect}"
  end
end

def tree_for_false
	Tree.new :and, [
		Tree.new('false', []),
		Tree.new(:not, [Tree.new('false', [])])
	]
end

def tree_for_true
	Tree.new :or, [
		Tree.new('true', []),
		Tree.new(:not, [Tree.new('true', [])])
	]
end