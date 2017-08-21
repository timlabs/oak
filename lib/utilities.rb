require 'io/console'

class WordWrapper
	def initialize flag = ' ', indent = 0
		@flag, @indent = flag, indent
		@width = IO.console.winsize[1]
		@position = 0
	end

	def print s
#		word_wrap s.to_s
		s = s.to_s
		return if s.empty?
		lines = s.split "\n"
		lines[0...-1].each {|line| puts line}
		word_wrap lines[-1]
	end

	def puts s = ''
		print s
		$stdout.puts
		@position = 0
	end

	def word_wrap s
		while s.length > @width-@position
			line = s[0...@width-@position]
			i = line.rindex @flag
			if i # break it after the flag
				$stdout.puts line[0...i+@flag.length]
				s = s[i+@flag.length..-1].lstrip
			elsif @position > 0 # try to fit it on the next line
				$stdout.puts
			else # no choice but to truncate it
				$stdout.puts line
				s = s[@width-@position..-1].lstrip
			end
			s = ' ' * @indent + s
			@position = 0
		end
		$stdout.print s
		@position += s.length
	end
end

def conjunction_tree trees
	return nil if trees.empty?
	return trees[0] if trees.size == 1
	Tree.new :and, trees
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

def substitute tree, substitution, repeatedly = false
	# note: expects substitution keys to be strings!
  case tree.operator
    when :for_all, :for_some
      variable = tree.subtrees[0].operator
      occurs = false
      occurs = true if substitution.keys.include? variable
      occurs = true if substitution.values.find {|replacement|
        next (replacement == variable) if replacement.is_a? String
        replacement.free_variables.include? variable
      }
			if occurs
#	      raise "substitution contains quantified variable #{variable}"
				raise SubstituteException, variable
			end
			return tree if tree.subtrees.size == 1 # empty :for_some
    	subtree = substitute tree.subtrees[1], substitution, repeatedly
      Tree.new tree.operator, [tree.subtrees[0], subtree]
		when :and, :or, :not, :implies, :iff, :equals, :quote
			subtrees = tree.subtrees.collect {|subtree|
				substitute subtree, substitution, repeatedly
			}
			Tree.new tree.operator, subtrees
    when :predicate
      subtrees = tree.subtrees.collect {|subtree|
				substitute subtree, substitution, repeatedly
			}
      Tree.new :predicate, subtrees
    when String
			return tree if not substitution.has_key? tree.operator
      replacement = substitution[tree.operator]
      replacement = Tree.new replacement, [] if replacement.is_a? String
      if repeatedly
        substitute replacement, substitution, repeatedly
      else
        replacement
      end
		else
			raise "unexpected operator #{tree.operator.inspect}"
  end
end

=begin
def substitute_meta tree, substitution
	# substitute disregarding semantics (even substitutes quantified variables)
	if tree.operator.is_a? String
		return tree if not substitution.has_key? tree.operator
		substitution[tree.operator]
	else
    subtrees = tree.subtrees.collect {|subtree|
			substitute_meta subtree, substitution
		}
    Tree.new tree.operator, subtrees
	end
end
=end

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
