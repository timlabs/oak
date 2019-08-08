class Proof

class Bindings
	class Node
		attr_reader :variables, :branches, :line
		attr_accessor :parent, :active

		def initialize variables, branches, parent, line
			@variables, @branches, @parent, @line = variables, branches, parent, line
			@active = true
		end
	end
end

class Bindings
	def initialize lines
		@constants = Set[]
		@bound = {}
		@unbound = Set[]
		@root = Node.new [], [], nil, nil
		@blocks = [@root]
		@lines = lines
	end

	def admit sentence, line
		# assumes check_admission has already been called!

		defines, sentence = read_defines sentence
		begin_block defines unless defines.empty?

		binds, body = read_binding sentence
		uses = sentence.free_variables
		admit_internal binds, uses, line
	end

	def begin_block defines = []
		node = admit_internal defines, []
		@blocks << node
		node
	end

	def check_admission sentence
		defines, sentence = read_defines sentence
		binds, body = read_binding sentence
		uses = sentence.free_variables

		unless (binds & defines).empty?
			variable = (binds & defines).first
			raise ProofException, "cannot bind #{variable} inside its own definition"
		end

		# having checked defines, merge it into binds
		binds = defines + binds
		uses = uses - defines

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
#					raise ProofException, "cannot bind #{variable}: previous binding would interleave active supposition"
				raise ProofException, "binding of variable #{variable} causes scope interleaving"
			end
			unless (uses & to_unbind).empty?
				culprit = (uses & to_unbind).first
				raise ProofException, "placement of variable #{culprit} causes scope interleaving"
			end
		}
	end

	def cited_tree cited_lines
		cited_tree_internal @root, cited_lines, get_cited_ancestors(cited_lines)
	end

	def end_block
		@blocks.pop until @blocks.last.variables.empty? # pop define blocks
		node = @blocks.pop
		deactivate_node node
	end

	private ###################################################################

	def admit_internal binds, uses, line = nil
		# unbind any of the variables to be bound which were already bound
		binds.each {|variable| deactivate_node @bound[variable] if @bound[variable]}

		# add the new bindings
		node = Node.new binds, [], @blocks.last, line
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

		node
	end

  def bind_variables variables, body, quantifier
		(variables.reverse & body.free_variables).each {|variable|
			body = Tree.new quantifier, [Tree.new(variable, []), body]
		}
		body
  end

  def cited_tree_internal scope_tree, cited_lines, cited_ancestors
		# nothing under it was cited, so there will be nothing to return
		return nil unless cited_ancestors.include? scope_tree

		# make trees recursively
		trees = scope_tree.branches.collect {|branch|
			cited_tree_internal branch, cited_lines, cited_ancestors
		}.compact

		# top scope
    return conjunction_tree trees if not scope_tree.parent

		# supposition start block (determined by checking if first branch is the supposition itself)
		if scope_tree.branches[0] and scope_tree.branches[0].line
			line = @lines[scope_tree.branches[0].line]
			if line.supposition?
				# if supposition is active, nothing further to do
				return conjunction_tree trees if scope_tree.active

				tree = conjunction_tree trees
				return nil if not tree
				if line.binding?
			    variables, body = read_binding line.sentence
					tree = Tree.new :implies, [body, tree] if body
					# generalize the binding
					tree = bind_variables variables, tree, :for_all
				else
					tree = Tree.new :implies, [line.sentence, tree]
				end
				return tree
			end
		end

		# start of proof block (nothing to do)
		return conjunction_tree trees if not scope_tree.line and scope_tree.variables.empty?

		# start of define block (contains defined variables, without a body)
		if not scope_tree.line
			tree = conjunction_tree trees
			if tree and not scope_tree.active
				tree = bind_variables scope_tree.variables, tree, :for_some
			end
			return tree
		end

		# normal line
    line = @lines[scope_tree.line]
    cited = cited_lines.include? scope_tree.line
    if line.binding?
      variables, body = read_binding line.sentence
      if scope_tree.active
				trees.unshift body if body and cited # add to start
				tree = conjunction_tree trees
			else
				tree = conjunction_tree trees
				return tree if line.supposition? # will be handled next level up
				if not tree
					return nil unless body and not line.supposition? and cited
					tree = bind_variables variables, body, :for_some
				else
					tree = Tree.new :and, [body, tree] if body and cited
					tree = bind_variables variables, tree, :for_some
				end
			end
		else
			raise unless trees.empty?
			tree = line.sentence if cited
    end
    tree
	end

	def deactivate_node n
		return if not n.active
		n.branches.each {|branch| deactivate_node branch}
		n.variables.each {|v| @bound.delete v}
		@unbound.merge n.variables
		n.active = false
	end

	def get_cited_ancestors cited_lines
		result = Set[]
		cited_lines.each {|line|
			node = @lines[line].node
			while node
				result << node
				node = node.parent
			end
		}
		result
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
		result = n.variables.dup
		n.branches.each {|branch| result.concat variables_for_unbinding(branch)}
		result
	end
end

end