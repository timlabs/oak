def grammar_rules
[
	[:start, :ending, :end],
	[:start, :begin_assume, :start5],
	[:start, :end_assume, :start5],
	[:start, :include, :start5],
	[:start, :now, :start5],
	[:start, :end, :start5],
#	[:start, [:now, :ending], :end, :catch],
	[:start, :exit, :start5],
	[:start, :label, :start2],
	[:start, :else, :start2],
#	[:start2, :assume_schema, :start5],
#	[:start2, :axiom_schema, :start5],
	[:start2, :assume, :start4],
	[:start2, :axiom, :start5],
	[:start2, :suppose, :start5],
	[:start2, :take, :start5],
	[:start2, :so, :start3],
#	[:start2, :now_exp, :start3],
#	[:start2, :then, :start3],
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

	[:filename, [/\s*'/, /[^'\n]+/, /'/], :end],
	[:filename, [/\s*"/, /[^"\n]+/, /"/], :end],
	
	[:assume, /\s*assume\b/i, :label_schema],

	[:axiom, /\s*axiom\b/i, :label_schema],

	[:label_schema, :label_same_line, :label_schema2],
	[:label_schema, :else, :label_schema2],
	[:label_schema2, [/\s*schema\b/i, :exp], :end],
	[:label_schema2, :define, :end],
	[:label_schema2, :exp, :end],

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
#	[:derive, :take, :end],
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
	
#	[:start, [:exp, :eof], :end],

	[:exp, :prefix, :end],
	[:exp, :exp1, :end],

	[:exp1, :exp2, :exp1a],
	[:exp1a, :and, :and1],
		[:and, /\s*and\b/i, :end],
		[:and1, :prefix, :end],
		[:and1, :exp2, :and2],
		[:and2, :and, :and1],
		[:and2, :else, :end],
#	[:exp1a, [/\s*and\b/i, :exp2], :and],
#		[:and, [/\s*and\b/i, :exp2], :and],
#		[:and, :else, :end],
	[:exp1a, :or, :or1],
		[:or, /\s*or\b/i, :end],
		[:or1, :prefix, :end],
		[:or1, :exp2, :or2],
		[:or2, :or, :or1],
		[:or2, :else, :end],
#	[:exp1a, [/\s*or\b/i, :exp2], :or],
#		[:or, [/\s*or\b/i, :exp2], :or],
#		[:or, :else, :end],
	[:exp1a, /\s*implies( that)?\b/i, :exp1b],
	[:exp1a, /\s*(iff|if and only if)\b/i, :exp1b],
	[:exp1a, :else, :end],
	[:exp1b, :exp2, :end],
	[:exp1b, :prefix, :end],
	
	[:exp2, :every, :end],
	[:exp2, :some, :end],
	[:exp2, :no, :end],

	[:exp2, :exp3, :exp2a],
	[:exp2a, /\s*=/i, :exp2b],
	[:exp2a, :not_equal, :exp2b],
	[:exp2a, :inequality, :exp2b],
	[:exp2a, :is_in, :exp2b],
	[:exp2a, :is_not_in, :exp2b],
	[:exp2a, :is_not, :is_predicate],
	[:exp2a, :is, :is_predicate],
	[:exp2a, :set, :exp2b],

	# putting this here for now, not sure about it though.
	# should it have a different precedence?  should it be removed entirely?
	[:exp2a, :custom, :exp2b],

	[:exp2a, :else, :end],
	[:exp2b, :exp3, :end],

	# addition and subtraction
	[:exp3, :exp4, :exp3a],
	[:exp3a, :plus, :plus1],
		[:plus, /\s*\+/i, :end],
		[:plus1, :exp4, :plus2],
		[:plus2, :plus, :plus1],
		[:plus2, :else, :end],
	[:exp3a, /\s*\-/i, :exp3b],
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

	[:prefix, :not, :end],
	[:prefix, :if, :end],
	[:prefix, :universal_meta, :end],
	[:prefix, :universal, :end],
	[:prefix, :no_existential, :end],
	[:prefix, :existential, :end],

	[:not, /\s*not\b/i, :not1],
	[:not1, :prefix, :end],
	[:not1, :exp2, :end],
	
	[:if, [/\s*if\b/i, :exp, /\s*,?\s*then\b/i], :if2],
	[:if2, :prefix, :end],
	[:if2, :exp2, :end],
	
	[:atom_list, :atom_list_commas, :end, :catch],
	[:atom_list, :atom_list_adjacent, :end, :catch],
	[:atom_list, :atom_list_base, :end],

	[:atom_list_commas, :definable, :atom_list_commas2],
	[:atom_list_commas2, :condition, :atom_list_commas3],
	[:atom_list_commas2, :else, :atom_list_commas5],
	
	[:atom_list_commas3, [/\s*,/, :definable, :condition, /\s*,/], :atom_list_commas4],
	[:atom_list_commas4, [:definable, :condition, /\s*,/], :atom_list_commas4],
	[:atom_list_commas4, [/\s*and\b/i, :definable, :condition], :end],
	
	[:atom_list_commas5, [/\s*,/, :definable, /\s*,/], :atom_list_commas6],
	[:atom_list_commas6, [:definable, /\s*,/], :atom_list_commas6],
	[:atom_list_commas6, [/\s*and\b/i, :definable], :atom_list_commas7],
	[:atom_list_commas7, :condition, :end],
	[:atom_list_commas7, :else, :end],

	[:atom_list_adjacent, [:definable, /,/, :definable_raw], :atom_list_adjacent2],
	[:atom_list_adjacent2, [/,/, :definable_raw,], :atom_list_adjacent2, :catch],
	[:atom_list_adjacent2, :condition, :end],
	[:atom_list_adjacent2, :else, :end],

  [:atom_list_base, :definable, :atom_list_base2],
  [:atom_list_base2, :condition, :atom_list_base3],
  [:atom_list_base2, :else, :atom_list_base4],
	[:atom_list_base3, [/\s*and\b/i, :definable, :condition], :end],
  [:atom_list_base3, :else, :end],
	[:atom_list_base4, [/\s*and\b/i, :definable], :atom_list_base5],
  [:atom_list_base4, :else, :end],
	[:atom_list_base5, :condition, :end],
	[:atom_list_base5, :else, :end],

	[:universal, /\s*for (all|any|each|every)\b/i, :post_quantifier_exp],

	[:universal_meta, /\s*for (all|any|each|every) meta\b/i, :post_quantifier_exp],

	[:existential, /\s*for (at least one|some)\b/i, :post_quantifier_exp],
	[:existential, /\s*there (exist|exists|is|are)( (a|an|at least one|some))?\b/i, :post_quantifier],
	[:no_existential, /\s*for no\b/i, :post_quantifier_exp],
	[:no_existential, /\s*there (exist|exists|is|are) no\b/i, :post_quantifier],

	[:post_quantifier_exp, :list_with_such, :post_quantifier_exp2],
	[:post_quantifier_exp2, [/,/, :exp], :end],

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

  [:condition, [/\s*in\b/i, :operand], :end],
  [:condition, [:inequality, :operand], :end],
	[:condition, [:set, :operand], :end],
  [:condition, [:not_equal, :operand], :end],

  [:inequality, /\s*<=/i, :end],
	[:inequality, /\s*≤/i, :end],
	[:inequality, /\s*</i, :end],
  [:inequality, /\s*>=/i, :end],
	[:inequality, /\s*≥/i, :end],
	[:inequality, /\s*>/i, :end],

	[:set, /\s*\⊆/i, :end],
	[:set, /\s*\⊊/i, :end],
	[:set, /\s*\⊇/i, :end],
	[:set, /\s*\⊋/i, :end],
	[:set, /\s*\⊂/i, :end],
	[:set, /\s*\⊃/i, :end],

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

	[:every, /\s*every\b/i, :every2],
	[:every2, :category, :every3],
	[:every3, :is_in, :exp2b], 
	[:every3, :is, :is_predicate],
	
	[:some, /\s*some\b/i, :some2],
	[:some2, :category, :some3],
	[:some3, :is_in, :exp2b],
	[:some3, :is_not_in, :exp2b],
	[:some3, :is_not, :is_predicate],
	[:some3, :is, :is_predicate],

	[:no, /\s*no\b/i, :no2],
	[:no2, :category, :no3],
	[:no3, :is_in, :exp2b],
	[:no3, :is, :is_predicate],

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
	[:operand_base, :word, :end],
	[:operand_base, :quote, :end],
	
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
	
	[:map, /\s*{/, :map2],
	[:map2, [:word, /\s*:/, :exp], :map3],
	[:map3, /\s*,/, :map2],
	[:map3, /\s*}/, :end],
	
	[:subst, /{/, :map2],
	
#	[:atom, [/\s+/, :atom], :end, :catch],
#	[:atom, :atom, :end, :catch],

	[:word, [/\s*/, :atom], :end, :catch],

	[:word_same_line, [/[ \t]*/, :atom], :end, :catch],
	
#	[:atom, [/\s+/, :atom_word], :atom2, :catch],
#	[:atom, :atom_word, :atom2, :catch],
#	[:atom2, [/[ \t]*/, :atom_word], :atom2, :catch],
#	[:atom2, :else, :end],

#	[:atom_word, :meta, :end],
#	[:atom_word, :atom, :end],
	
	[:label_name, [/\s*/, :atom], :label_name2],
	[:label_name2, [/ ?/, :atom], :label_name2, :catch],
	[:label_name2, :else, :end],

	[:label_name_same_line, [/[ \t]*/, :atom], :label_name2, :catch],
	
#  [:definable, /\+|\-|\*|\÷|\/|\^/, :end],
#  [:definable, :atom, :end],

	[:definable, [/\s*/, :definable_raw], :end, :catch],

  [:definable_raw, /\+|\-|\*|\÷|\/|\^/, :end],
  [:definable_raw, :atom, :end],

	[:atom, /(so|now|then|proof|end proof)\b/i, :null],
	[:atom, /(if|is|let)\b/i, :null],
	[:atom, /(true|false|contradiction|thesis)\b/i, :null],
	[:atom, /(not|and|or|implies|iff|then)\b/i, :null],
	[:atom, /(for (at least one|some)|for (all|any|each|every)|for no)\b/i, :null],
	[:atom, /(such that|where|with|in|there (is|are|exist|exists))\b/i, :null],
	[:atom, /(assume|suppose|by|from|exit|take|define|axiom|schema)\b/i, :null],
	[:atom, /(every|some|no)\b/i, :null],
	[:atom, /((?!
			\(|\)|\[|\]|,|;|\.\s|\.\z|=|!=|≠|\+|\-|\*|÷|\^
			|<=|≤|<|>=|≥|>|:|"|`|{|}|\$|\||⊆|⊇|⊊|⊋|⊂|⊃|\/
		)\S)+/x, :end],
]
end
