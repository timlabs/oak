require 'tempfile'

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
			variable_name = tree.subtrees[0].operator
			old_replacement = replace[variable_name]
			new_replacement = new_name used, 'V'
			replace[variable_name] = new_replacement
			used << new_replacement
			variable = Tree.new new_replacement, []
			body = rename_for_tptp_internal tree.subtrees[1], used, replace
			replace[variable_name] = old_replacement
			tree = Tree.new tree.operator, [variable, body]
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
				replace[tree.operator] = new_name used, 'x'
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
		else
			raise "unexpected operator #{tree.operator.inspect}"
	end
end

def tptp_from tree
	tree = replace_empty_quantifiers tree
	tree = first_orderize tree, true
	tree = rename_for_tptp tree
	tree = make_booleans_explicit tree
#	puts "tree for tptp_from_internal:"
#	p tree
	tptp_from_internal tree
end

def valid_tptp? tree
	input = tptp_from tree
	input = "fof(query,conjecture,#{input})."
#	puts 'tptp:'
#	puts input
#	$stdin.gets
	file = Tempfile.new ''
	file.write input
	file.close # ensures that input is written
	result = yield file.path
	file.unlink # best practice
	result
end

def valid_cvc4? tree
	valid_tptp?(tree) {|file_path|
		options = []
		options << '--lang=tptp'
		options << '--finite-model-find'
#		options << '-vvvvv'
		output = `~/Desktop/tools/CVC4/cvc4 #{options.join ' '} #{file_path}`
		next :valid if output.include? '% SZS status Theorem'
		next :invalid if output.include? '% SZS status CounterSatisfiable'
		# why does it keep giving "SZS status GaveUp"?
		# it happens on cfl.txt, as well as on "for some x, p[x]"
		# so it doesn't indicate validity or invalidity.
		#
		# update: adding --finite-model-find fixed this, but now it just takes
		# a really long time, even on simple proofs like "g proof.txt"
		raise output
	}
end

def valid_e? tree
	valid_tptp?(tree) {|file_path|
		# tried with -m 1, but this uses way more than 1 MB on "L systems.txt"!
		# possibilities: -C 1500, or -T 10000
		# -C 180 takes about 0.5s on hard example
		# -C 72 can do everything but conjugates and L systems
		# -T 69 can do everything but conjugates and L systems
		# conjugates needs -C 523, L systems needs -C 1038
		# conjugates needs -T 556, L systems needs -T 8177
		# conjugates needs -P 267, L systems needs -P 309 *

		settings = []
#		settings << '-C 122' # 588 # 486
#		settings << '-P 29'
#		settings << '-T 1481'
#		settings << '-U 8'
#		settings << '--generated-limit=45'

		settings << '--tb-insert-limit=60000'
		settings << '-m 128' # memory limit for safety
		settings << '--detsort-rw --detsort-new' # make it deterministic

		# use local copy if there is one, otherwise call it without a path
		local = File.expand_path '../eprover/eprover', File.dirname(__FILE__)
		location = File.exist?(local) ? local : 'eprover'

		output = `"#{location}" #{settings.join ' '} --auto --tptp3-format -s #{file_path} 2>&1`
#		puts output
		next :valid if output.include? '# Proof found!'
		next :invalid if output.include? '# No proof found!'
		next :unknown if output.include? '# Failure: User resource limit exceeded!'
		message = "unexpected output when calling eprover:\n  #{output.strip}\n"
		if 	$?.exitstatus == 127 or 					# command not found
				output.include? 'Unknown Option' 	# happens with version < 2.0
			message << "check that E Theorem Prover version >= 2.0 is installed"
		end
		raise ProofException, message
	}
end

def valid_iprover? tree
	valid_tptp?(tree) {|file_path|
		output = `~/Desktop/tools/iProver/iproveropt #{file_path}`
		next :valid if output.include? '% SZS status Theorem'
		next :invalid if output.include? '% SZS status CounterSatisfiable'
		# note: there is a bug where "x and not x" gives an error
		# unfortunately there is no cut-off option other than a time limit!
		raise output
	}
end

def valid_prover9? tree
	valid_tptp?(tree) {|file_path|
		settings = ''

		# sos_limit=34 works on everything but conjugates
		# problem is that with this you cannot distinguish
		# invalid from unknown validity! (both return sos_empty)
		# -1 means no limit.
		settings << 'assign(sos_limit, -1).'

		# max_given=79 works on everything but conjugates
		settings << 'assign(max_given, 221).'

		# max_kept=161 works on everything but conjugates (373 was good)
		settings << 'assign(max_kept, 1631).'

		# max_megs=1 takes 10s on conjugates
#		settings << 'assign(max_megs, 0).'

		# strange behavior otherwise, looks for multiple proofs?
		settings << 'clear(auto_denials).'
		# hide some output apparently going to stderr
		settings << 'set(quiet).'

		tptp = "tptp_to_ladr < #{file_path}"
		output = `((#{tptp}; echo "#{settings}") | prover9) 2>&1`
		not_found = 'tptp_to_ladr: not found'
		raise not_found if output.include? not_found
		next :valid if output.include? 'Exiting with 1 proof.'
		next :invalid if output.include? ' exit (sos_empty) '
		next :unknown if output.include? ' exit (max_given) '
		next :unknown if output.include? ' exit (max_kept) '
		next :unknown if output.include? ' exit (max_megs) '
		raise output
	}
end

def valid_spass? tree
	valid_tptp?(tree) {|file_path|
		# -Memory=6500000 handles everything but L systems and conjugates
    #   but this takes 30s each on L systems and conjugates
		# -CNFProofSteps=1 takes >= 3 min on conjugates
		# -Loops=47 handles everything but L systems and conjugates
		#   but this takes >= 3 min on LT 1
		options = []
#		options << '-Memory=6500000'
#		options << '-Loops=26'
#		options << '-CNFProofSteps=1'
		output = `SPASS #{options.join ' '} -TPTP #{file_path} 2>&1`
		next :valid if output.include? 'SPASS beiseite: Proof found.'
		next :invalid if output.include? 'SPASS beiseite: Completion found.'
		next :unknown if output.include? 'SPASS beiseite: Maximal number of loops exceeded.'
		next :unknown if output.include? 'Terminated by user given memory restriction'
		raise output
	}
end
