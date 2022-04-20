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
		attr_reader :line, :branches, :depth
		attr_accessor :parent, :active

		def initialize line, parent
			@line, @parent = line, parent
			@branches = []
			@active = true
			@depth = parent ? (parent.depth + 1) : 0
		end

		def to_s prefix = ''
			type = case
				when not(@line) then 'block'
				when @line.definition? then "define block (line #{@line.fileline})"
				else "line #{@line.fileline}"
			end
			variables = @line ? @line.binds : []
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
		@tie_ins = {}
		@root = Node.new nil, nil
		@blocks = [@root]
		@node_for_line = Hash.new {raise}
	end

	def admit line # is nil when called by begin_block
		# assumes check_admission has already been called!

		binds = line ? line.binds : []
		uses = line ? line.uses : []

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
				shift_under_node @bound[variable]
			else
				# variable was never bound, so register it as a constant
				@constants << variable
			end
		}

		# set tie-ins to start retroactively, as far back as possible
		if line and not line.tie_ins.empty?
			starter = most_recent_binding uses
			@tie_ins[starter] = [] if not @tie_ins[starter]
			@tie_ins[starter] << node
		end

		# Tie-ins that are part of bindings only apply to the variables being bound,
		# so their position in the tree is handled by the "uses" logic above.  For
		# other tie-ins, we cannot easily tell (due to their mutually recursive
		# nature) whether they apply to the line being added or not.  So we have to
		# assume they do, and call shift_under_node to put the line in their scope.
		if line and line.binds.empty?
			@tie_ins.each {|starter, tie_ins|
				tie_ins.each {|tie_in| shift_under_node tie_in}
			}
		end

		@node_for_line[line] = node if line
		@blocks << node if not line or line.definition?
	end

	def begin_block
		admit nil
	end

	def check_admission content
		binds = content.binds
		uses = content.uses

		unless (@constants & binds).empty?
			variable = (@constants & binds).first
			msg = "cannot bind #{variable}: already occurred as a constant"
			raise ProofException, msg
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
				msg = "binding of variable #{variable} causes scope interleaving"
				raise ProofException, msg
			end
			unless (uses & to_unbind).empty?
				culprit = (uses & to_unbind).first
				msg = "placement of variable #{culprit} causes scope interleaving"
				raise ProofException, msg
			end
		}
	end

	def end_block
		@blocks.pop while @blocks.last.line # pop define blocks
		node = @blocks.pop
		deactivate_node node
	end

	def to_check content, cited_lines
		# adjust if schema is being cited
		schema_lines = cited_lines.select {|line| line.schema}
		if schema_lines.size > 1
			raise ProofException, 'cannot cite multiple schemas'
		elsif not schema_lines.empty?
			if not @node_for_line[schema_lines[0]].active
				raise ProofException, 'cannot cite inactive schema'
			end
			cited_lines -= [schema_lines[0]]
			schema = schema_lines[0].schema
		end

		# handle cases that don't need tie-ins
		cited = cited_tree cited_lines, false
		tree = implication_tree [cited], content.sentence
		if schema
			return {:schema => schema, :tree => tree}
		elsif self_implication? tree
			tree = tree_for_true # make things easy for external prover
			return {:tree => tree}
		end

		# finally, handle tie-ins
		cited = cited_tree cited_lines, true
		tree = nil
		if content.body
			# apply active tie-ins to the body, as long as they do not use vars which
			# content is rebinding
			tie_ins = @tie_ins.values.flatten.delete_if {|tie_in|
				not (tie_in.line.uses & content.binds).empty?
			}
			tied_in = tied_in_for content.body, tie_ins
			tied_in = tied_in.collect {|match, used| match}
			tree = implication_tree tied_in, content.body
		end
		tree = bind_variables content.binds, tree, :for_some
		tree = implication_tree [cited], tree
		tree = deduplicate tree
		{:tree => tree}
	end

	def to_s
		@root.to_s
	end

	private ###################################################################

	# tie-ins are a bit tricky.  here are two of the main ideas.
	#
	# (1) for any line, there are two classes of tie-ins that can apply to it:
	# those that were in effect at the time the line was added, and those which
	# are in effect now.  to handle the second class, we place them
	# "retroactively" at the earliest nodes in the tree they can apply to.  these
	# placements are kept in @tie_ins.  they stay there for as long as they are
	# active, then fall back to their placement in the line that created them.
	#
	# (2) matches for a tie-in cannot be computed "high" in the tree, because
	# there may be lower tie-ins that could apply to them.  but they cannot be
	# added to the tree "low", because they may then be encompassed in a binding
	# or supposition context which need not apply to them.  so we have to compute
	# them "low" and add them "high".  to do this, we pass the tie-ins down
	# through the tree, compute their matches on the way back up, but store the
	# results as pending and only add them when we cannot retract them any further
	# up the tree.

	def cited_tree cited_lines, add_tied_in
		cited_nodes = cited_lines.collect {|line| @node_for_line[line]}
		ancestors = get_ancestors cited_nodes
		tie_ins = (add_tied_in ? [] : nil)
		tree, pending = cited_tree_internal @root, cited_nodes, ancestors, tie_ins
		raise if not pending.empty? # sanity check
		tree
	end

  def cited_tree_internal scope_tree, cited_nodes, ancestors, tie_ins
		# if nothing under it was cited, there will be nothing to return
		return [nil, []] unless ancestors.include? scope_tree

		active = scope_tree.active
		line = scope_tree.line
		delay = (line and line.supposition? and not active) # handle next level up

		if tie_ins and not delay
			tie_in_precount = tie_ins.size
			# add tie-ins defined here, unless they are active, in which case they
			# are handled by the retroactive placement
			tie_ins += [scope_tree] if line and not line.tie_ins.empty? and not active
			# add any tie-ins that have been retroactively placed here
			tie_ins += @tie_ins[scope_tree] if @tie_ins[scope_tree]
		end

		# make trees recursively
		trees, pending = [], []
		scope_tree.branches.each {|branch|
			result = cited_tree_internal branch, cited_nodes, ancestors, tie_ins
			trees << result[0] if result[0]
			pending.concat result[1]
		}

		return [conjunction_tree(trees), pending] if delay

		# supposition start block (first branch is the supposition itself)
		# handled "one level up" because supposition may be wider than its binding
		branch = scope_tree.branches[0]
		if branch and branch.line and branch.line.supposition? and not active
			raise if line # should be a supposition block
			line = branch.line
			tree = conjunction_tree trees
			tree = Tree.new :implies, [line.body, tree] if line.body and tree
			pending.concat tied_in_for line.body, tie_ins if line.body and tie_ins
			readies = release_pending pending, line, tie_in_precount if tie_ins
			tree = conjunction_tree [*readies, tree].compact
			# generalize the binding
			tree = bind_variables line.binds, tree, :for_all if tree
			return [tree, pending]
		end

		if line and line.body and cited_nodes.include? scope_tree
			trees.unshift line.body
			pending.concat tied_in_for line.body, tie_ins if tie_ins
		end
		trees.unshift *release_pending(pending, line, tie_in_precount) if tie_ins
		tree = conjunction_tree trees
		tree = bind_variables line.binds, tree, :for_some if line and not active
    [tree, pending]
	end

	def deactivate_node n
		return if not n.active
		n.branches.each {|branch| deactivate_node branch}
		if n.line
			n.line.binds.each {|v| @bound.delete v}
			@unbound.merge n.line.binds
			@tie_ins.each {|starter, tie_ins| tie_ins.delete n}
		end
		n.active = false
	end

	def deduplicate tree, facts = [], top = true
		# does some simplifying to reduce duplication in the tree
		tree = case tree.operator
			when :for_all, :for_some
				vars, body = tree.subtrees
				return tree if not body
				facts = facts.select {|fact|
					(fact.free_variables & vars.operator).empty?
				}
				body = deduplicate body, facts, false
				Tree.new tree.operator, [vars, body] if body
			when :and
				subtrees = tree.subtrees.uniq - facts.to_a
				subtrees = subtrees.collect.with_index {|subtree, i|
					new_facts = facts + subtrees[0...i] + subtrees[i+1..-1]
					deduplicate subtree, new_facts, false
				}.compact
				if subtrees.empty?
					nil
				elsif subtrees.size == 1
					subtrees[0]
				else
					Tree.new :and, subtrees
				end
			when :implies
				antecedent = deduplicate tree.subtrees[0], facts, false
				if tree.subtrees[0].operator == :and
					new_facts = facts + tree.subtrees[0].subtrees
				else
					new_facts = facts + [tree.subtrees[0]]
				end
				consequent = deduplicate tree.subtrees[1], new_facts, false
				consequent ? implication_tree([antecedent], consequent) : nil
			else
				tree
		end
		(top and not tree) ? tree_for_true : tree
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

	def matches_in tie_in, tree
		# find all matches in the tree and its subtrees for the tie-in
		matches = matches_in_internal tie_in, tree, Set[]
		matches.uniq
	end

	def matches_in_internal tie_in, tree, quantified
		if [:for_all, :for_some, :for_at_most_one].include? tree.operator
			return [] if tree.subtrees.size == 1
			# start = Time.now
			vars = tree.subtrees[0].operator
			# if pattern contains quantified variables, it cannot match
			return [] if not (vars & tie_in.pattern.free_variables).empty?
			quantified += Set[*vars]
			return matches_in_internal tie_in, tree.subtrees[1], quantified
		end
		matches = []
		tree.subtrees.each {|subtree|
			matches.concat matches_in_internal tie_in, subtree, quantified
		}
		begin # check tree as a whole
			params = [tie_in.pattern, tree, tie_in.metas]
			constraints = SchemaModule.find_constraints *params
			next if not constraints

			resolved = SchemaModule.resolve_constraints constraints
			next if not resolved
			next unless (tie_in.metas - resolved.keys).empty?

			# tie-ins must be terms
			next unless resolved.values.none? {|v| v.boolean?}

			# tie-ins cannot instantiate quantified variables
			used_metas = tie_in.metas & tie_in.body.free_variables
			found = used_metas.find {|meta|
				not (quantified & resolved[meta].free_variables).empty?
			}
			next if found

			matches << substitute(tie_in.body, resolved)
		rescue ProofException # tree as a whole didn't match
		end while false # for next to work!
		matches
	end

	def most_recent_binding vars
		# assumes bound vars are on same root-to-leaf path
		nodes = vars.collect {|v| @bound[v] or @root}
		nodes.max_by {|node| node.depth}
	end

	def shift_under_node n
		# shift everything after n to be under n
		holder = n
		while holder != @root
			parent = holder.parent
			i = parent.branches.index holder
			nodes = parent.branches[i+1..-1]
			parent.branches.slice! i+1..-1
			n.branches.concat nodes
			nodes.each {|node| node.parent = n}
			holder = parent
		end
	end

	def tied_in_for tree, tie_in_nodes, used = [], calls = {}
		# find all tie-ins for the tree
		calls[tree] = [] if not calls[tree]
		return [] if calls[tree].find {|call| (used - call).empty?}
		calls[tree] << used
		results = []
		tie_in_nodes.each_with_index {|node, i|
			node.line.tie_ins.each_with_index {|tie_in, j|
				next if used.include? [i,j]
				matches_in(tie_in, tree).each {|match|
					new_used = used + [[i,j]]
					results << [match, new_used.transpose[0]]
					results.concat tied_in_for match, tie_in_nodes, new_used, calls
				}
			}
		}
		results
	end

	def release_pending pending, line, threshold
		# find any pending tie-in matches that cannot be retracted further upward,
		# remove them from pending, and return them
		readies = []
		vars = line ? line.binds : []
		pending.delete_if {|match, used|
			ready = false
			# match uses a variable that this line binds
			ready = true if not (match.free_variables & vars).empty?
			# match uses a tie-in added by this line
			ready = true if used.max >= threshold
			readies << match if ready
			ready
		}
		readies
	end

	def variables_for_unbinding n
		return [] if not n.active
		raise ProofException if @blocks.include? n # can't unbind a block
		result = n.line.binds.dup
		n.branches.each {|branch| result.concat variables_for_unbinding(branch)}
		result
	end
end

end