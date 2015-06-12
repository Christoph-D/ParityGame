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
      obtain \<sigma> where \<sigma>: "valid_strategy p \<sigma>" "attractor_strategy_on p \<sigma> A (?deadends p**)"
        using attractor_has_strategy[of "?deadends p**" "p"] A_def by auto

      have "A \<subseteq> V" using A_def using attractor_is_bounded_by_V deadends_in_V by blast
      hence "A - ?deadends p** \<subseteq> V" by auto
      moreover have "strategy_on p \<sigma> (A - ?deadends p**)" using \<sigma> by blast
      ultimately obtain \<sigma>' where \<sigma>': "valid_strategy p \<sigma>'" "strategy_on p \<sigma>' V" "strategy_less_eq \<sigma> \<sigma>'"
        using \<sigma>(1) strategy_less_eq_extensible[of "A - ?deadends p**" "V"] by blast
      hence \<sigma>'_attracts: "strategy_attracts_from_to p \<sigma>' A (?deadends p**)" using \<sigma>(2) by blast

      assume v_in_attractor: "v0 \<in> attractor p (?deadends p**)"
      have "winning_strategy p \<sigma>' v0" proof (unfold winning_strategy_def, clarify)
        fix P assume P: "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "v0 = the (P 0)"
        have P_infinite_or_finite: "infinite_path P \<or> finite_path P" using P(1) valid_path_def by blast
        obtain i where i_def: "P i \<noteq> None \<and> the (P i) \<in> ?deadends p**" using \<sigma>'_attracts A_def v_in_attractor strategy_attracts_from_to_def P by blast
        have "P (Suc i) = None" by (metis (no_types, lifting) i_def CollectD P(1) valid_path_def)
        moreover hence "finite_path P" using infinite_path_def P_infinite_or_finite by blast
        moreover have "i \<in> path_dom P \<and> the (P i) \<in> VV p**" using i_def by blast
        ultimately show "winning_path p P" using winning_path_def by blast
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

      have "\<forall>P n. valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> the (P 0) \<in> (V - ?A)
        \<longrightarrow> (\<forall>i \<le> n. P i \<noteq> None \<longrightarrow> the (P i) \<notin> ?A)" apply (insert \<sigma>_def(3); unfold strategy_avoids_def) .

      have "\<And>P. \<lbrakk> valid_path P; maximal_path P; path_conforms_with_strategy p P \<sigma>; the (P 0) \<in> (V - ?A) \<rbrakk> \<Longrightarrow> winning_path p P" proof-
        fix P
        assume P_valid: "valid_path P"
          and P_maximal: "maximal_path P"
          and P_conforms: "path_conforms_with_strategy p P \<sigma>"
          and P_valid_start: "the (P 0) \<in> V - ?A"
        show "winning_path p P" proof (cases)
          assume infinite: "infinite_path P"
          have *: "\<And>a. a \<in> path_inf_priorities P \<Longrightarrow> winning_priority p a" proof-
            fix a assume "a \<in> path_inf_priorities P"
            then obtain w where w_def: "w \<in> path_inf P" "a = \<omega> w" using path_inf_priorities_def by blast
            then obtain i where i_def: "P i = Some w" using path_inf_is_from_P[of w] by blast
            hence "the (P i) \<in> V" by (meson P_valid domI domIff valid_path_def)
            hence "w \<in> V" using i_def by simp
            hence "a = n" using assms w_def(2) by simp
            thus "winning_priority p a" using p_def assms by simp
          qed
          obtain a where a_def: "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using P_valid infinite path_inf_priorities_has_minimum by blast
          hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" using infinite winning_path_def by (metis (no_types, lifting) infinite_path_def le_antisym)
          thus ?thesis using * a_def by blast
        next
          assume "\<not>infinite_path P"
          hence P_finite: "finite_path P" using P_valid valid_path_def by blast
          {
            fix i assume i_def: "i \<in> path_dom P" "P (Suc i) = None"
            hence deadend: "deadend (the (P i))" by (metis (mono_tags, lifting) CollectD P_maximal maximal_path_def)
            have "\<And>i. P i \<noteq> None \<Longrightarrow> the (P i) \<notin> ?A" using strategy_avoids_strongly P_conforms P_valid P_valid_start \<sigma>_def(3) by presburger
            hence no_bad_deadends: "\<And>i. P i \<noteq> None \<Longrightarrow> the (P i) \<notin> ?deadends p" using W_def by blast
            hence "the (P i) \<notin> ?deadends p" using i_def(1) by blast
            hence "the (P i) \<notin> VV p \<or> \<not>deadend (the (P i))" by blast
            hence "the (P i) \<notin> VV p" using deadend by simp
            hence "the (P i) \<in> VV p**" by (metis (mono_tags, lifting) CollectD DiffI P_valid Player.distinct(1) i_def(1) valid_path_def)
          }
          moreover have "\<exists>!i \<in> path_dom P. P (Suc i) = None" using P_finite path_dom_ends_on_finite_paths by simp
          ultimately have "\<exists>i \<in> path_dom P. P (Suc i) = None \<and> the (P i) \<in> VV p**" by blast
          thus ?thesis using P_finite winning_path_def by blast
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
      thus ?thesis using lemma_path_to_deadend[of "p**"] by blast
    next
      assume "v0 \<notin> attractor p** (?deadends p)"
      hence *: "v0 \<in> V - attractor p** (?deadends p)" using `v0 \<in> V` by blast
      show ?thesis apply (insert lemma_no_path_to_deadend *) .
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
