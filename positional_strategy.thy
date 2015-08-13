theory positional_strategy
imports
  Main
  parity_game strategy attractor
begin

context ParityGame begin

theorem positional_strategy_exist_for_single_prio_games:
  assumes "v0 \<in> V" and "\<forall>v \<in> V. \<omega>(v) = n"
  shows "\<exists>p \<sigma>. valid_strategy_from p \<sigma> v0 \<and> strategy_on p \<sigma> V \<and> winning_strategy p \<sigma> v0"
proof -
  let ?deadends = "\<lambda>p. {v \<in> VV p. deadend v}"
  have deadends_in_V: "\<And>p. ?deadends p \<subseteq> V" by auto
  { fix p
    def A \<equiv> "attractor p (?deadends p**)"
    assume "?deadends p** \<noteq> {}"
    then obtain \<sigma> where \<sigma>: "valid_strategy p \<sigma>" "strategy_only_on p \<sigma> (A - (?deadends p**))" "strategy_attracts_from_to p \<sigma> A (?deadends p**)"
      using attractor_has_strategy_weak[of "?deadends p**" "p"] A_def deadends_in_V by blast

    have "A \<subseteq> V" using A_def using attractor_is_bounded_by_V deadends_in_V by blast
    hence "A - ?deadends p** \<subseteq> V" by auto
    moreover have "strategy_on p \<sigma> (A - ?deadends p**)" using \<sigma> by blast
    ultimately obtain \<sigma>' where \<sigma>': "valid_strategy p \<sigma>'" "strategy_on p \<sigma>' V" "strategy_less_eq \<sigma> \<sigma>'"
      using \<sigma>(1) strategy_less_eq_extensible[of "A - ?deadends p**" "V"] by blast
    hence \<sigma>'_attracts: "strategy_attracts_from_to p \<sigma>' A (?deadends p**)" using \<sigma>(3) strategy_attracts_from_to_extends by blast

    assume v_in_attractor: "v0 \<in> attractor p (?deadends p**)"
    have "winning_strategy p \<sigma>' v0" proof (unfold winning_strategy_def, clarify)
      fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "v0 = P $ 0"
      obtain i where i_def: "enat i < llength P \<and> P $ i \<in> ?deadends p**"
        using \<sigma>'_attracts A_def v_in_attractor strategy_attracts_from_to_def P lset_intersect_lnth[of P "?deadends p**"] by blast
      have *: "enat (Suc i) = llength P" using P(2) i_def valid_path_ends_on_deadend by auto
      hence "lfinite P" using llength_eq_enat_lfiniteD by force
      moreover have "llast P \<in> VV p**" proof-
        from * have "eSuc (enat i) = llength P" by (simp add: eSuc_enat)
        moreover have "P $ i \<in> VV p**" using i_def by blast
        ultimately show ?thesis by (metis llast_conv_lnth)
      qed
      ultimately show "winning_path p P" using winning_path_def P(1) by blast
    qed
    hence "\<exists>p \<sigma>. valid_strategy p \<sigma> \<and> strategy_on p \<sigma> V \<and> winning_strategy p \<sigma> v0" using \<sigma>' by blast
  } note lemma_path_to_deadend = this
  def p \<equiv> "if even n then Even else Odd"
  {
    def W \<equiv> "?deadends p"
    hence W_in_V: "W \<subseteq> V" by auto
    let ?A = "attractor p** W"
    assume v_not_in_attractor: "v0 \<in> V - ?A"
    then obtain \<sigma> where \<sigma>_def: "valid_strategy p \<sigma>" "strategy_only_on p \<sigma> (V - ?A)" "strategy_avoids p \<sigma> (V - ?A) ?A"
      using W_in_V attractor_has_outside_strategy[of p W] by blast

    have "\<forall>P n. \<not>lnull P \<and> valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P $ 0 \<in> V - ?A
      \<longrightarrow> (\<forall>i \<le> n. enat i < llength P \<longrightarrow> P $ i \<notin> ?A)" by (insert \<sigma>_def(3); unfold strategy_avoids_def)

    have "\<And>P. \<lbrakk> \<not>lnull P; valid_path P; maximal_path P; path_conforms_with_strategy p P \<sigma>; P $ 0 \<in> V - ?A \<rbrakk> \<Longrightarrow> winning_path p P" proof-
      fix P
      assume "\<not>lnull P"
        and P_valid: "valid_path P"
        and P_maximal: "maximal_path P"
        and P_conforms: "path_conforms_with_strategy p P \<sigma>"
        and P_valid_start: "P $ 0 \<in> V - ?A"
      show "winning_path p P" proof (cases)
        assume P_finite: "lfinite P"
        then obtain j where j_def: "enat j = llength P" by (metis lfinite_conv_llength_enat)
        with `\<not>lnull P` have "j \<noteq> 0" by (metis llength_eq_0 zero_enat_def)
        then obtain i where i_def: "enat (Suc i) = llength P" using j_def by (metis nat.exhaust)
        have "P $ i \<in> VV p**" proof-
          from i_def have deadend: "deadend (P $ i)" by (metis P_maximal enat_ord_simps(2) lessI less_not_refl maximal_path_impl1)
          have "\<And>i. enat i < llength P \<Longrightarrow> P $ i \<notin> ?A" using strategy_avoids_strongly P_conforms P_valid P_valid_start \<sigma>_def(3) by presburger
          hence no_bad_deadends: "\<And>i. enat i < llength P \<Longrightarrow> P $ i \<notin> ?deadends p" using W_def by (metis attractor_set_base subsetCE)
          hence "P $ i \<notin> ?deadends p" using i_def(1) by (metis (no_types, lifting) enat_ord_simps(2) lessI)
          hence "P $ i \<notin> VV p \<or> \<not>deadend (P $ i)" by blast
          hence "P $ i \<notin> VV p" using deadend by simp
          thus ?thesis using i_def(1) P_valid by (metis DiffI Player.distinct(1) enat_ord_simps(2) lessI valid_path_finite_in_V')
        qed
        moreover from i_def have "eSuc (enat i) = llength P" by (simp add: eSuc_enat)
        ultimately have "llast P \<in> VV p**" using llast_conv_lnth[OF sym, of i P] by simp
        thus ?thesis using winning_path_def P_finite `\<not>lnull P` by blast
      next
        assume infinite: "\<not>lfinite P"
        have *: "\<And>a. a \<in> path_inf_priorities P \<Longrightarrow> winning_priority p a" proof-
          fix a assume "a \<in> path_inf_priorities P"
          hence "a \<in> lset (lmap \<omega> P)" using path_inf_priorities_def in_lset_ldropnD by fastforce
          then obtain w where w_def: "w \<in> lset P" "a = \<omega> w" by auto
          hence "w \<in> V" by (meson P_valid set_rev_mp valid_path_in_V)
          hence "a = n" using assms w_def(2) by simp
          thus "winning_priority p a" using p_def assms by simp
        qed
        obtain a where a_def: "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using P_valid infinite path_inf_priorities_has_minimum by blast
        hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" by (metis `\<not>lnull P` infinite le_antisym winning_path_def)
        thus ?thesis using * a_def by blast
      qed
    qed
    hence *: "winning_strategy p \<sigma> v0" using winning_strategy_def v_not_in_attractor by presburger
    have "strategy_on p \<sigma> (V - ?A)" using \<sigma>_def by blast
    then obtain \<sigma>' where \<sigma>'_def: "valid_strategy p \<sigma>'" "strategy_less_eq \<sigma> \<sigma>'" "strategy_on p \<sigma>' V"
      by (meson \<sigma>_def(1) Diff_subset strategy_less_eq_extensible)
    have "strategy_avoids p \<sigma> (V - ?A) (V - (V - ?A))" using \<sigma>_def(3) by (simp add: W_in_V attractor_is_bounded_by_V double_diff)
    hence "valid_strategy_from p \<sigma> v0" using \<sigma>_def valid_strategy_is_valid_strategy_from[of p \<sigma> "V - ?A" v0] v_not_in_attractor by blast
    hence "winning_strategy p \<sigma>' v0" using winning_strategy_preserved_under_extension \<sigma>_def(1) * \<sigma>'_def(2) by blast
    hence "\<exists>p \<sigma>. valid_strategy p \<sigma> \<and> strategy_on p \<sigma> V \<and> winning_strategy p \<sigma> v0" using \<sigma>'_def(1) \<sigma>'_def(3) * by blast
  } note lemma_no_path_to_deadend = this
  hence "\<exists>p \<sigma>. valid_strategy p \<sigma> \<and> strategy_on p \<sigma> V \<and> winning_strategy p \<sigma> v0" proof (cases)
    assume "v0 \<in> attractor p** (?deadends p)"
    hence "v0 \<in> attractor p** (?deadends p****)" by simp
    thus ?thesis using lemma_path_to_deadend[of "p**"] by (metis (no_types, lifting) attractor_set_empty equals0D)
  next
    assume "v0 \<notin> attractor p** (?deadends p)"
    hence "v0 \<in> V - attractor p** (?deadends p)" using `v0 \<in> V` by blast
    thus ?thesis using lemma_no_path_to_deadend by blast
  qed
  thus ?thesis using valid_strategy_is_valid_strategy_from_V using assms(1) by blast
qed

(*
theorem positional_strategy_exists:
  assumes "v \<in> V"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    show ?thesis sorry
  qed
*)

end -- "context ParityGame"

end
