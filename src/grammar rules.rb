def grammar_rules
[
	[:start, :ending, :end], # needed to preserve line numbers
	[:start, :begin_assume, :start5],
	[:start, :end_assume, :start5],
	[:start, :include, :start5],
	[:start, :now, :start5],
	[:start, :end, :start5],
	[:start, :exit, :start5],
	[:start, :tie_in, :start3],
	[:start, :label, :start2],
	[:start, :else, :start2],

	# things that can have labels
	[:start2, :assume, :start4],
	[:start2, :axiom, :start5],
	[:start2, :suppose, :start5],
	[:start2, :take, :start5],
	[:start2, :so, :start3],
	[:start2, :derive, :start3],

	[:start3, :by, :start5],
	[:start3, :proof, :start5],
	[:start3, :else, :start5],
	[:start4, :by, :start5],
	[:start4, :else, :start5],
	[:start5, :ending, :end],

	[:label, [:label_name, /\s*:/], :end, :catch],

	[:label_same_line, [:label_name_same_line, /\s*:/], :end, :catch],

	[:include, /\s*include\b/i, :filename],

	[:begin_assume, /\s*begin assume\b/i, :end],

	[:end_assume, /\s*end assume\b/i, :end],

	[:filename, [/\s*"/, /[^"\n]+/, /"/], :end],

	[:tie_in, /\s*tie-in\b/i, :tie_in2],
	[:tie_in2, [:quote, :with, :quote], :tie_in3],
	[:tie_in3, /\s*for (all|any|each|every)\b/i, :tie_in4],
	[:tie_in3, :else, :end],
	[:tie_in4, :atom_list_adjacent, :end],

	[:assume, /\s*assume\b/i, :assume2],
	[:assume2, :tie_in, :end],
	[:assume2, :else, :label_schema],

	[:axiom, /\s*axiom\b/i, :label_schema],

	[:label_schema, :label_same_line, :label_schema2],
	[:label_schema, :else, :label_schema2],
	[:label_schema2, :schema, :end],
	[:label_schema2, :define, :end],
	[:label_schema2, :exp, :end],

	[:schema, [/\s*schema\b/i, :universal_meta], :end],

	[:suppose, /\s*suppose\b/i, :suppose2],
	[:suppose2, :label_same_line, :suppose3],
	[:suppose2, :else, :suppose3],
	[:suppose3, :exp, :end],

	[:take, :take_label, :post_quantifier],
	[:take_label, /\s*take any\b/i, :end],
	[:take_label, [/\s*take\b/i, :label_same_line, /\s*any\b/i], :end],

	[:so, /\s*so\b/i, :so2],
	[:so2, :assume, :end],
	[:so2, :label_same_line, :so3],
	[:so2, :else, :so3],
	[:so3, :define, :end],
	[:so3, :exp, :end],

	[:now, /\s*now\b/i, :end],

	[:end, /\s*end\b/i, :end],

	[:derive, :exp, :end],
	[:derive, :let, :end],
	[:derive, :define, :end],

	[:exit, /\s*exit\b/i, :end],

	[:by, /\s*(by|from)\b/i, :by2],
	[:by2, :label_name, :by3],
	[:by3, /\s*,/, :by2],
	[:by3, /\s*and\b/i, :by2],
	[:by3, :else, :end],

	[:proof, /\s*proof\b/i, :end],
	
	[:ending, /\s*\.\s|\s*\.\z/, :end],
  [:ending, /\s*;/, :end],
  [:ending, /\s*\n/, :end],
	[:ending, /\s*\z/, :end],

	# prefix can have any prefix under it
	# prefix can have any infix of higher level under it

	# infix can have any prefix of higher level to left of it
	# infix can have any infix of higher level to left of it

	# infix can have any prefix to right of it
	# infix can have any infix of higher level to right of it

	[:exp, :exp_, :end],

	[:prefix_, :universal, :end],
	[:prefix_, :for_at_most_one, :end],
	[:prefix_, :no_existential, :end],
	[:prefix_, :existential, :end],

	# no infix at this level
	[:exp_, :prefix_, :end],
	[:exp_, :exp0, :end],

	[:prefix0, :if, :end],

	[:exp0, :prefix0, :end],
	[:exp0, :exp1, :exp0a],
	[:exp0a, /\s*(iff|if and only if)\b/i, :exp0b],
	[:exp0a, /\s*implies( that)?\b/i, :exp0b],
	[:exp0a, :else, :end],
	[:exp0b, :exp1, :end],
	[:exp0b, :prefix0, :end],
	[:exp0b, :prefix_, :end],

	[:prefix1, :not, :end],

	[:exp1, :prefix1, :end],
	[:exp1, :exp2, :exp1a],
	[:exp1a, :and, :and1],
		[:and, /\s*and\b/i, :end],
		[:and1, :exp2, :and2],
		[:and1, :else, :exp1c],
		[:and2, :and, :and1],
		[:and2, :else, :end],
	[:exp1a, :or, :or1],
		[:or, /\s*or\b/i, :end],
		[:or1, :exp2, :or2],
		[:or1, :else, :exp1c],
		[:or2, :or, :or1],
		[:or2, :else, :end],
	[:exp1a, :else, :end],
	[:exp1b, :exp2, :end],
	[:exp1b, :else, :exp1c],
	[:exp1c, :prefix1, :end],
	[:exp1c, :prefix0, :end],
	[:exp1c, :prefix_, :end],

	[:prefix2, :every, :end],
	[:prefix2, :no, :end],
	[:prefix2, :some, :end],
	[:prefix2, :at_most_one, :end],

	[:exp2, :prefix2, :end],
	[:exp2, :exp3, :exp2a],
	[:exp2a, /\s*=/i, :exp2b],
	[:exp2a, :not_equal, :exp2b],
	[:exp2a, :inequality, :exp2b],
	[:exp2a, :is_in, :exp2b],
	[:exp2a, :is_not_in, :exp2b],
	[:exp2a, :is_not, :is_predicate],
	[:exp2a, :is, :is_predicate],
	[:exp2a, :set_relation, :exp2b],
	[:exp2a, :custom, :exp2b], # not sure about this, move or remove?
	[:exp2a, :else, :end],
	[:exp2b, :exp3, :end],

	# addition, subtraction, union, and intersection
	[:exp3, :exp4, :exp3a],
	[:exp3a, :plus, :plus1],
		[:plus, /\s*\+/i, :end],
		[:plus1, :exp4, :plus2],
		[:plus2, :plus, :plus1],
		[:plus2, :else, :end],
	[:exp3a, /\s*\-/i, :exp3b],
	[:exp3a, :union, :union1],
		[:union, /\s*\∪/i, :end],
		[:union1, :exp4, :union2],
		[:union2, :union, :union1],
		[:union2, :else, :end],
	[:exp3a, :intersection, :intersection1],
		[:intersection, /\s*\∩/i, :end],
		[:intersection1, :exp4, :intersection2],
		[:intersection2, :intersection, :intersection1],
		[:intersection2, :else, :end],
	[:exp3a, :else, :end],
	[:exp3b, :exp4, :end],

	# multiplication and division
	[:exp4, :exp5, :exp4a],
	[:exp4a, :times, :times1],
		[:times, /\s*\*/i, :end],
		[:times1, :exp5, :times2],
		[:times2, :times, :times1],
		[:times2, :else, :end],
	[:exp4a, /\s*\//i, :exp4b],
	[:exp4a, /\s*÷/i, :exp4b],	
	[:exp4a, :else, :end],
	[:exp4b, :exp5, :end],

	# exponentiation
	[:exp5, :exp6, :exp5a],
	[:exp5a, /\s*\^/i, :exp5b],
	[:exp5a, /\s*\*\*/i, :exp5b],
	[:exp5a, :else, :end],
	[:exp5b, :exp6, :end],

	[:exp6, :operand, :end],

	[:if, [/\s*if\b/i, :exp, /\s*,?\s*then\b/i], :exp0b],

	[:not, /\s*not\b/i, :exp1b],

	[:atom_list, :atom_block, :atom_list2],
	[:atom_list2, [/\s*and\b/i, :atom_block], :atom_list2],
	[:atom_list2, :else, :end],

	[:atom_block, :word, :atom_block2],
	[:atom_block, :else, :atom_list_adjacent],
	[:atom_block2, :word_same_line, :atom_block2],
	[:atom_block2, :condition, :end, :catch],
	[:atom_block2, :definable_same_line, :atom_list_adjacent2],
	[:atom_block2, :else, :atom_list_adjacent2],

	[:atom_list_adjacent, :definable, :atom_list_adjacent2],
	[:atom_list_adjacent2, [/,/, :definable_raw,], :atom_list_adjacent2, :catch],
	[:atom_list_adjacent2, :condition, :end],
	[:atom_list_adjacent2, :else, :end],

	[:universal, /\s*for (all|any|each|every) meta\b/i, :null],
	[:universal, /\s*for (all|any|each|every)\b/i, :post_quantifier_exp],

	[:universal_meta, /\s*for (all|any|each|every) meta\b/i, :universal_meta2],
	[:universal_meta2, [:list_with_such, /,\s/, :quote], :end],

	[:existential, /\s*for (at least one|some)\b/i, :post_quantifier_exp],
	[:existential, /\s*there (exist|exists|is|are)( (a|an|at least one|some))?\b/i, :post_quantifier],
	[:for_at_most_one, /\s*for at most one\b/i, :post_quantifier_exp],
	[:for_at_most_one, /\s*there (exist|exists|is|are) at most one\b/i, :post_quantifier],
	[:no_existential, /\s*for no\b/i, :post_quantifier_exp],
	[:no_existential, /\s*there (exist|exists|is|are) no\b/i, :post_quantifier],

	[:post_quantifier_exp, :list_with_such, :post_quantifier_exp2],
	[:post_quantifier_exp2, [/,\s/, :exp], :end],

	[:post_quantifier, :list_with_such, :end],

	[:list_with_such, :atom_list, :list_with_such2],
	[:list_with_such2, [:with, :exp], :list_with_such3],
	[:list_with_such2, :else, :list_with_such3],
	[:list_with_such3, [:such_that, :exp], :end],
	[:list_with_such3, :else, :end],

	[:with, /\s*with\b/i, :end],

	[:such_that, /\s*(such that|where)\b/i, :end],

	[:let, /\s*let\b/i, :let2],
	[:let2, :definable, :let3],
	[:let3, /\s*=/i, :let4],
	[:let4, :exp, :end],

	[:define, /\s*define\b/i, :post_quantifier],

  [:condition, [/\s*in\b/i, :exp3], :end],
  [:condition, [/\s*not in\b/i, :exp3], :end],
  [:condition, [:inequality, :exp3], :end],
	[:condition, [:set_relation, :exp3], :end],
  [:condition, [:not_equal, :exp3], :end],

  [:inequality, /\s*<=/i, :end],
	[:inequality, /\s*≤/i, :end],
	[:inequality, /\s*</i, :end],
  [:inequality, /\s*>=/i, :end],
	[:inequality, /\s*≥/i, :end],
	[:inequality, /\s*>/i, :end],

	[:set_relation, /\s*\⊆/i, :end],
	[:set_relation, /\s*\⊊/i, :end],
	[:set_relation, /\s*\⊇/i, :end],
	[:set_relation, /\s*\⊋/i, :end],
	[:set_relation, /\s*\⊂/i, :end],
	[:set_relation, /\s*\⊃/i, :end],

	[:not_equal, /\s*!=/i, :end],
	[:not_equal, /\s*≠/i, :end],

	[:custom, [:word_same_line, /[ \t]/], :end],

	[:is, /\s*is\b/i, :end],
	[:is_not, /\s*is not\b/i, :end],

	[:is_in, /\s*is in\b/i, :end],
	[:is_not_in, /\s*is not in\b/i, :end],

	[:preposition, /\s*(of|on)\b/i, :end],

	[:category, :word, :category2],
	[:category2, [:preposition, :exp3], :end],
	[:category2, :word_same_line, :category2],
	[:category2, :else, :end],

	[:article, /\s*(a|an)\b/i, :end],
	
	[:quantified, [:article, :category], :end],
	
	[:is_predicate, :quantified, :end],
	[:is_predicate, :word, :end],

	[:every, /\s*every\b/i, :category_is],

	[:no, /\s*no\b/i, :category_is],

	[:some, /\s*(some|at least one)\b/i, :category_is_with_not],

	[:at_most_one, /\s*at most one\b/i, :category_is_with_not],

	[:category_is, :category, :category_is2],
	[:category_is2, :is_in, :exp2b],
	[:category_is2, :is, :is_predicate],

	[:category_is_with_not, :category, :category_is_with_not2],
	[:category_is_with_not2, :is_in, :exp2b],
	[:category_is_with_not2, :is_not_in, :exp2b],
	[:category_is_with_not2, :is_not, :is_predicate],
	[:category_is_with_not2, :is, :is_predicate],

	[:boolean, /\s*(true|false|contradiction)\b/i, :end],

	[:thesis, /\s*thesis\b/i, :end],

#	[:meta, [/\$/, :operand_base], :end],

	[:quote, [/\s*`/, :exp, /\s*`/], :end],

	[:string, /\s*"/, :string2],
	[:string2, /"/, :end],
#	[:string2, :meta, :string2],
#	[:string2, /[^"$]*/, :string2],
	[:string2, /[^"]*/, :string2],
	
	[:negative, /\s*-/, :negative2],
	[:negative2, :atom, :end],
	[:negative2, [/\[/, :exp, /\s*\]/], :end],
	
	[:square_root, /\s*√/, :square_root2],
	[:square_root2, :atom, :end],
#	[:square_root2, [/\[/, :exp, /\s*\]/], :end],
	
	[:operand, :boolean, :end],
	[:operand, :thesis, :end],
	[:operand, :string, :end],
	[:operand, :negative, :end],
	[:operand, :square_root, :end, :catch],
	[:operand, :operand_base, :operand2],
	[:operand2, :subst, :operand3],
	[:operand2, :else, :operand3],
	[:operand3, :params, :operand3],
	[:operand3, :else, :end],

	[:operand_base, [/\s*\(/, :exp, /\s*\)/], :end],
	[:operand_base, [/\s*\|/, :exp, /\s*\|/], :end],
	[:operand_base, :list, :end],
	[:operand_base, :set, :end],
	[:operand_base, :word, :end],

	[:list, /\s*\[/, :list1a],
	[:list1a, /\s*\]/, :end],
	[:list1a, :else, :list2],
	[:list2, :exp, :list3],
	[:list3, /,/, :list2],
	[:list3, :else, :list4],
	[:list4, /\s*\]/, :end],

	[:params, /\[/, :list2],
	[:params, /\(/, :params2],
	[:params2, :exp, :params3],
	[:params3, /,/, :params2],
	[:params3, :else, :params4],
	[:params4, /\s*\)/, :end],

	[:set, /\s*{/, :set1a],
	[:set1a, /\s*}/, :end],
	[:set1a, :else, :set2],
	[:set2, :exp, :set3],
	[:set3, /,/, :set2],
	[:set3, :else, :set4],
	[:set4, /\s*}/, :end],

	[:map, /\s*{/, :map2],
	[:map2, [:word, /\s*:/, :exp], :map3],
	[:map3, /\s*,/, :map2],
	[:map3, /\s*}/, :end],

	[:subst, /{/, :map2],

	[:word, [/\s*/, :atom], :end, :catch],

	[:word_same_line, [/[ \t]*/, :atom], :end, :catch],

	[:label_name, [/\s*/, :atom], :label_name2],
	[:label_name2, [/ ?/, :atom], :label_name2, :catch],
	[:label_name2, :else, :end],

	[:label_name_same_line, [/[ \t]*/, :atom], :label_name2, :catch],

	[:definable, [/\s*/, :definable_raw], :end, :catch],

	[:definable_same_line, [/[ \t]*/, :definable_raw], :end, :catch],

  [:definable_raw, /\+|\-|\*|\÷|\/|\^|⊆|⊊|⊂|\|\||{}|\[\]|∪|∩|</, :end],
  [:definable_raw, :atom, :end],

	[:atom, /for (all|any|at least one|at most one)\b/i, :null],
	[:atom, /for (each|every|no|some)\b/i, :null],
	[:atom, /there (are|exist|exists|is)\b/i, :null],
	[:atom, /(at least one|at most one|every|some|no)\b/i, :null],
	[:atom, /(and|any|define|if|iff|implies|in|is|let|not|of|on|or)\b/i, :null],
	[:atom, /(such that|then|where|with)\b/i, :null],
	[:atom, /(assume|axiom|begin assume|by|end|exit|from|include|now)\b/i, :null],
	[:atom, /(proof|schema|so|suppose|take)\b/i, :null],
	[:atom, /(contradiction|false|thesis|true)\b/i, :null],
	[:atom, /((?!
			\(|\)|\[|\]|,|;|\.\s|\.\z|=|!=|≠|\+|\-|\*|÷|\^
			|<=|≤|<|>=|≥|>|:|"|`|{|}|\$|\||⊆|⊇|⊊|⊋|⊂|⊃|\/
		)\S)+/x, :end],
]
end