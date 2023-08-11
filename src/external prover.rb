require 'tempfile'

module ExternalProver
extend self

def valid_e? tree, wait_forever = false
	tb_insert_limit = 100000
	valid_tptp?(tree) {|file_path|
		settings = []
		settings << "--tb-insert-limit=#{tb_insert_limit}" unless wait_forever
		settings << '--detsort-rw --detsort-new' # make it deterministic
		settings << '--print-statistics' if wait_forever

		# use local copy if there is one, otherwise call it without a path
		local = File.expand_path '../eprover/PROVER/eprover', File.dirname(__FILE__)
		location = File.exist?(local) ? local : 'eprover'

		command = %{"#{location}" #{settings.join ' '} --auto --tptp3-format } +
							%{-s #{file_path} 2>&1}
		output = `#{command}`

		if output.include? '# Proof found!'
			next :valid unless wait_forever
			work = output.match(/# Termbank termtop insertions\s+: (\d+)/).to_a[1]
			next :valid if (Integer work) <= tb_insert_limit
			next Float(work) / tb_insert_limit
		end
		next :invalid if output.include? '# No proof found!'
		next :unknown if output.include? '# Failure: User resource limit exceeded!'
		next :unknown if output.include? '# Failure: Out of unprocessed clauses!'

		message = "unexpected output when calling eprover:\n  #{output.strip}\n"
		if $?.exitstatus == 127 or 					# command not found
			 output.include? 'Unknown Option' # happens with version < 2.0
			message << "check that E Theorem Prover version >= 2.0 is installed"
			raise ProofException, message
		end
		raise message # no idea what happened, so treat it as a bug
	}
end

private #######################################################################

def make_booleans_explicit tree, booleanize_now = true
	case tree.operator
		when :for_all, :for_some
			body = make_booleans_explicit tree.subtrees[1], true
			Tree.new tree.operator, [tree.subtrees[0], body]
		when :not, :and, :or, :implies, :iff
			subtrees = tree.subtrees.collect {|subtree|
				make_booleans_explicit subtree, true
			}
			Tree.new tree.operator, subtrees
		when :equals
			subtrees = tree.subtrees.collect {|subtree|
				make_booleans_explicit subtree, false
			}
			Tree.new tree.operator, subtrees
		when :predicate
			subtrees = tree.subtrees.collect {|subtree|
				make_booleans_explicit subtree, false
			}
			tree = Tree.new :predicate, subtrees
			return tree if not booleanize_now
			Tree.new :predicate, [Tree.new('boolean', []), tree]
		when String
			return tree if not booleanize_now
			Tree.new :predicate, [Tree.new('boolean', []), tree]
		else
			raise "unexpected operator #{tree.operator.inspect}"
	end
end

def rename_for_tptp_internal tree, used, replace = {}
	case tree.operator
		when :for_all, :for_some
			variables = tree.subtrees[0].operator
			old_replacements = variables.collect {|variable| replace[variable]}
			new_replacements = new_names used, variables.size, 'V'
			variables.zip(new_replacements) {|v, r| replace[v] = r}
			used.concat new_replacements
			variables_tree = Tree.new new_replacements, []
			body = rename_for_tptp_internal tree.subtrees[1], used, replace
			variables.zip(old_replacements) {|v, r| replace[v] = r}
			tree = Tree.new tree.operator, [variables_tree, body]
		when :not, :and, :or, :implies, :iff, :equals
			subtrees = tree.subtrees.collect {|subtree|
				rename_for_tptp_internal subtree, used, replace
			}
			Tree.new tree.operator, subtrees
		when :predicate
			# assume that predicate names don't need replacing, e.g. because they
			# were first-orderized
			subtrees = tree.subtrees[1..-1].collect {|subtree|
				rename_for_tptp_internal subtree, used, replace
			}
			Tree.new tree.operator, [tree.subtrees[0], *subtrees]
		when String
			if not replace[tree.operator]
				replace[tree.operator] = new_name used, 'c'
				used << replace[tree.operator]
			end
			Tree.new replace[tree.operator], []
		else
			raise "unexpected operator #{tree.operator.inspect}"
	end
end

def rename_for_tptp tree
	used = strings_from tree
	rename_for_tptp_internal tree, used
end

def strings_from tree
	if tree.operator.is_a? String
		[tree.operator]
	elsif tree.operator.is_a? Array
		tree.operator
	else
		tree.subtrees.collect {|subtree| strings_from subtree}.flatten.uniq
	end
end

def tptp_from_internal tree
	subtrees = tree.subtrees.collect {|subtree| tptp_from_internal subtree}
	case tree.operator
		when :for_all
			"(! [#{subtrees[0]}] : #{subtrees[1]})"
		when :for_some
			"(? [#{subtrees[0]}] : #{subtrees[1]})"
		when :not
			"~(#{subtrees[0]})"
		when :and
			"(#{subtrees.join ' & '})"
		when :or
			"(#{subtrees.join ' | '})"
		when :implies
			"(#{subtrees[0]} => #{subtrees[1]})"
		when :iff
			"(#{subtrees[0]} <=> #{subtrees[1]})"
		when :equals
			"(#{subtrees[0]} = #{subtrees[1]})"
		when :predicate
			"#{subtrees[0]}(#{subtrees[1..-1].join ','})"
		when String
			tree.operator
		when Array
			tree.operator.join ','
		else
			raise "unexpected operator #{tree.operator.inspect}"
	end
end

def tptp_from tree
	tree = replace_for_at_most_one tree
	tree = replace_empty_quantifiers tree
	tree = first_orderize tree, true
	tree = rename_for_tptp tree
	tree = make_booleans_explicit tree
	# puts "tree for tptp_from_internal:"
	# p tree
	tptp_from_internal tree
end

def valid_tptp? tree
	input = tptp_from tree
	input = "fof(query,conjecture,#{input})."
	# puts "\ntptp:"
	# puts input
	file = Tempfile.new ''
	file.write input
	file.close # ensures that input is written
	result = yield file.path
	file.unlink # best practice
	result
end

end