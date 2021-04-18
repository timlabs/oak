module Schema
extend self

def check_schema_format tree, state = :top, vars = []
	case state
		when :top
			unless tree.operator  == :for_all_meta
				raise ParseException, 'schema must begin with "for all meta"'
			end
			vars.concat tree.subtrees[0].operator
			check_schema_format tree.subtrees[1], :meta, vars
		when :meta
			if tree.operator == :for_all_meta
				vars.concat tree.subtrees[0].operator
				check_schema_format tree.subtrees[1], :meta, vars
			elsif tree.operator == :implies
				return false if not check_schema_format tree.subtrees[0], :with, vars
				check_schema_format tree.subtrees[1], :quote, vars
			else
				check_schema_format tree, :quote, vars
			end
		when :with
			case tree.operator
				when :and, :or, :not, :implies, :iff
					tree.subtrees.all? {|subtree| check_schema_format subtree, :with, vars}
				when :predicate
					return false unless tree.subtrees.size == 3
					return false unless tree.subtrees[0].operator == 'free'
					return false unless tree.subtrees[1].subtrees.empty?
					return false unless tree.subtrees[2].subtrees.empty?
					return false unless vars.include? tree.subtrees[1].operator
					return false unless vars.include? tree.subtrees[2].operator
					true
				else
					return false
			end
		when :quote
			return false unless tree.operator == :quote
			check_schema_format tree.subtrees[0], :normal, vars
		when :normal
			case tree.operator
				when :for_all_meta, :quote
					false
				when :substitution
					vars.include? tree.subtrees[0].operator
				else
					tree.subtrees.all? {|subtree| check_schema_format subtree, :normal, vars}
			end
	end
end

def instantiate_schema schema, instance
	# puts "schema: #{schema}"

	variables, pattern, requirements = parse_schema schema
	# puts "variables: #{variables}"
	# puts "pattern: #{pattern}"
	# puts "requirements: #{requirements}"
	# puts "instance: #{instance}"

	constraints = find_constraints pattern, instance, variables
	raise ProofException if not constraints
	# puts "constraints are:"
	# constraints.each {|constraint| puts "#{constraint[0]} = #{constraint[1]}"}
	# puts

	resolved = resolve_constraints constraints
	raise ProofException if not resolved
	# puts "resolved:"
	# p resolved

	# every variable must have an assignment
	raise ProofException unless (variables - resolved.keys).empty?

	requirements_tree requirements, resolved
end

private #######################################################################

def apply_resolved requirement, resolved
	case requirement.operator
		when :and, :or, :not, :implies, :iff
			subtrees = requirement.subtrees.collect {|subtree|
				apply_resolved subtree, resolved
			}
			Tree.new requirement.operator, subtrees
		when :predicate
			raise unless requirement.subtrees[0].operator == 'free'
			variable = resolved[requirement.subtrees[1].operator].operator
			formula = resolved[requirement.subtrees[2].operator]
			raise ProofException unless variable.is_a? String
#			puts "variable = #{variable}"
#			puts "formula = #{formula}"
#			puts "formula free vars = #{formula.free_variables}"
			if formula.free_variables.include? variable
				tree_for_true
			else
				tree_for_false
			end
		else raise
	end
end

def find_constraints pattern, instance, variables
	# find constraints for meta variables, and make sure everything else matches
	if pattern.operator.is_a? Array # list of quantified variables
		return nil unless instance.operator.is_a? Array
		return nil unless pattern.operator.size == instance.operator.size
		constraints = []
		pattern.operator.zip(instance.operator) {|v1, v2|
			if variables.include? v1 # meta variable generates a constraint
				constraints << [v1, Tree.new(v2, [])]
			else
				return nil unless v1 == v2 # others must match exactly
			end
		}
		constraints
	elsif variables.include? pattern.operator
		[[pattern.operator, instance]]
	elsif pattern.operator == :substitution
		[[pattern, instance]]
	else
		return nil if pattern.operator != instance.operator
		return nil if pattern.subtrees.size != instance.subtrees.size
		constraints = []
		pattern.subtrees.zip(instance.subtrees) {|s1, s2|
			result = find_constraints s1, s2, variables
			return nil if not result
			constraints.concat result
		}
		constraints
	end
end

def parse_schema schema
	case schema.operator
		when :for_all_meta
			variables, pattern, requirements = parse_schema schema.subtrees[1]
			variables.concat schema.subtrees[0].operator
			[variables, pattern, requirements]
		when :implies
			variables, pattern, requirements = parse_schema schema.subtrees[1]
			requirements.unshift schema.subtrees[0]
			[variables, pattern, requirements]
		when :quote
			[[], schema.subtrees[0], []]
		else raise
	end
end

def requirements_tree requirements, resolved
	return tree_for_true if requirements.empty?
	conjunction_tree requirements.collect {|requirement|
		apply_resolved requirement, resolved
	}
end

def resolve_constraints constraints
	absolutes = constraints.select {|target, x| target.is_a? String}
	relatives = constraints - absolutes

#	puts "absolutes:"
#	absolutes.each {|constraint| puts "#{constraint[0]}  =  #{constraint[1]}"}
#	puts "relatives:"
#	relatives.each {|constraint| puts "#{constraint[0]}  =  #{constraint[1]}"}
#	puts

	substitution = {}
	absolutes.each {|variable, x|
		if substitution[variable]
			return nil unless substitution[variable].eql? x
		else
			substitution[variable] = x
		end
	}

	relatives.each {|relative_substitution, x|
		variable = relative_substitution.subtrees[0].operator
		map = relative_substitution.subtrees[1]

		# multi-substitute not supported yet
		return nil if map.subtrees.size > 2	

		list = map.subtrees[1]
		left = list.subtrees[1]
		right = list.subtrees[2]

		# schema must include all relative variables in absolute form
		if not substitution[variable] 
			raise ProofException, "could not resolve schema variable #{variable}"
		end

		left = substitute(left, substitution).operator
		return nil unless left.is_a? String
		right = substitute right, substitution

#		puts "substituted was #{substitution[variable]}"
		substituted = substitute substitution[variable], {left => right}
#		puts "x is #{x}"
#		puts "substituted is #{substituted}"
#		puts "for variable #{variable}"
#		puts "left = #{left}"
#		puts "right = #{right}"
		return nil unless substituted.eql? x
	}

	substitution
end

end