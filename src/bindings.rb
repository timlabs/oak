=begin

This class supports "scopes" and "blocks".

Scopes are tracked automatically, while blocks are set manually.

When a variable is bound, its scope begins.  Whenever it is used, its scope is
extended through that point.  Its scope can end anywhere after its last use, as
long as it is (1) before the block it was bound in ends, and (2) before it is
rebound.

Blocks are set with begin_block and end_block.

Scopes cannot interleave blocks.  That is, a scope cannot begin outside a block
and end inside it, or begin inside a block and end outside it.

This guarantees that if you bind a variable outside a block, and extend its
scope into the block (by using it in the block), it will "mean" the same thing
for the whole block.

Definitions are handled automatically with internal blocks.

=end

class Proof

class Bindings
	class Node
		attr_reader :line, :branches
		attr_accessor :parent, :active

		def initialize line, parent
			@line, @parent = line, parent
			@branches = []
			@active = true
		end

		def to_s prefix = ''
			type = case
				when not(@line) then 'block'
				when @line.binding.definition? then "define block (line #{@line.fileline})"
				else "line #{@line.fileline}"
			end
			variables = @line ? @line.binding.variables : []
			me = "#{prefix}#{type}, variables #{variables}, active #{@active}"
			them = branches.collect {|node| node.to_s prefix + '  '}
			[me, *them].join "\n"
		end
	end
end

class Bindings
	def initialize
		@constants = Set[]
		@bound = {}
		@unbound = Set[]
		@root = Node.new nil, nil
		@blocks = [@root]
		@node_for_line = Hash.new {raise}
	end

	def admit line
		# assumes check_admission has already been called!

		binds = line ? line.binding.variables : []
		uses = line ? line.sentence.free_variables : []

		# unbind any of the variables to be bound which were already bound
		binds.each {|variable| deactivate_node @bound[variable] if @bound[variable]}

		# add the new bindings
		node = Node.new line, @blocks.last
		@blocks.last.branches << node
		binds.each {|variable| @bound[variable] = node}
		@unbound.subtract binds

		uses.each {|variable|
			if @bound[variable]
				# shift so that this appearance of variable will be in the binding scope
				shift_under_variable variable
			else
				# variable was never bound, so register it as a constant
				@constants << variable
			end
		}

		@node_for_line[line] = node if line
		@blocks << node if not line or line.binding.definition?
	end

	def begin_block
		admit nil
	end

	def check_admission content
		binds = content.binding.variables
		uses = content.sentence.free_variables

		unless (@constants & binds).empty?
			variable = (@constants & binds).first
			raise ProofException, "cannot bind #{variable}: already occurred as a constant"
		end

		unless (@unbound & uses).empty?
			variable = (@unbound & uses).first
			raise ProofException, "variable #{variable} is no longer in scope"
		end

		binds.each {|variable|
			next unless @bound[variable]
			begin
				to_unbind = variables_for_unbinding @bound[variable]
			rescue ProofException
				raise ProofException, "binding of variable #{variable} causes scope interleaving"
			end
			unless (uses & to_unbind).empty?
				culprit = (uses & to_unbind).first
				raise ProofException, "placement of variable #{culprit} causes scope interleaving"
			end
		}
	end

	def cited_tree cited_lines, uses
		cited_nodes = cited_lines.collect {|line| @node_for_line[line]}
		if uses # enable tie-ins
			uses_nodes = uses.collect {|variable| @bound[variable]}.compact
			ancestors = get_ancestors(cited_nodes + uses_nodes)
		else # disable tie-ins
			uses_nodes = nil
			ancestors = get_ancestors cited_nodes
		end
		# puts "bindings:\n#{to_s}"
		tree, vars = cited_tree_internal @root, cited_nodes, uses_nodes, ancestors
		raise "missed tie-ins for #{vars}" unless vars.empty?
		tree
	end

	def cited_tree_without_tie_ins cited_lines
		cited_tree cited_lines, nil
	end

	def end_block
		@blocks.pop while @blocks.last.line # pop define blocks
		node = @blocks.pop
		deactivate_node node
	end

	def to_s
		@root.to_s
	end

	private ###################################################################

  def cited_tree_internal scope_tree, cited_nodes, uses_nodes, ancestors
		# if nothing under it was cited or used, there will be nothing to return
		return nil, Set[] unless ancestors.include? scope_tree

		# make trees recursively
		trees, need_tie_ins = [], Set[]
		scope_tree.branches.reverse_each {|branch| # most recent first, for readability
			tree, vars = cited_tree_internal branch, cited_nodes, uses_nodes, ancestors
			trees << tree if tree
			need_tie_ins.merge vars
		}

		# supposition start block (first branch is the supposition itself)
		# handled "one level up" because supposition may be wider than its binding
		if scope_tree.branches[0] and scope_tree.branches[0].line
			line = scope_tree.branches[0].line
			if line.supposition?
				raise if scope_tree.line # should be a supposition block
				tree = conjunction_tree trees
				if tree and not scope_tree.active # otherwise, handled already
					variables = line.binding.variables
					body = line.binding.body_with_tie_in
					if body
						tree = Tree.new :implies, [body, tree]
						need_tie_ins.merge body.free_variables.to_set - @constants
					end
					# generalize the binding
					tree = bind_variables variables, tree, :for_all
					need_tie_ins.subtract variables
				end
				return tree, need_tie_ins
			end
		end

		# rest
		active = scope_tree.active
		if scope_tree.line
			line = scope_tree.line
			if line.supposition? and not active
				variables = [] # will be handled next level up
			else
		    cited = cited_nodes.include? scope_tree
				variables = line.binding.variables
				if cited
					addition = line.binding.body_with_tie_in
				elsif uses_nodes # nil (as opposed to empty) means disable tie-ins
					if (variables.to_set & need_tie_ins).any? or uses_nodes.include? scope_tree
						addition = line.binding.tie_in
					end
				end
				if addition
					trees << addition # most recent first, for readability
					need_tie_ins.merge addition.free_variables.to_set - @constants
				end
			end
		else
			# one of: proof/axiom/supposition/root block (nothing to do)
			variables = []
		end
		tree = conjunction_tree trees
		tree = bind_variables variables, tree, :for_some if tree and not active
		need_tie_ins.subtract variables
    [tree, need_tie_ins]
	end

	def deactivate_node n
		return if not n.active
		n.branches.each {|branch| deactivate_node branch}
		if n.line
			n.line.binding.variables.each {|v| @bound.delete v}
			@unbound.merge n.line.binding.variables
		end
		n.active = false
	end

	def get_ancestors nodes
		result = Set[]
		nodes.each {|node|
			while node
				result << node
				node = node.parent
			end
		}
		result
	end

	def shift_under_variable v
		# shift everything after the binding of v to be in v's scope
		holder = @bound[v]
		while holder != @root
			parent = holder.parent
			i = parent.branches.index holder
			nodes = parent.branches[i+1..-1]
			parent.branches.slice! i+1..-1
			@bound[v].branches.concat nodes
			nodes.each {|node| node.parent = @bound[v]}
			holder = parent
		end
	end

	def variables_for_unbinding n
		return [] if not n.active
		raise ProofException if @blocks.include? n # can't unbind a block
		result = n.line.binding.variables.dup
		n.branches.each {|branch| result.concat variables_for_unbinding(branch)}
		result
	end
end

end