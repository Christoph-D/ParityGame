theory positional_strategy
imports
  Main
  parity_game strategy attractor
begin

context ParityGame begin

theorem positional_strategy_exist_for_single_prio_games:
  assumes "v0 \<in> V" and "\<forall>v \<in> V. \<omega>(v) = n"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0"
proof -
  let ?deadends = "\<lambda>p. {v \<in> VV p. deadend v}"
  have deadends_in_V: "\<And>p. ?deadends p \<subseteq> V" by auto
  { fix p
    def A \<equiv> "attractor p (?deadends p**)"
    assume "?deadends p** \<noteq> {}"
    then obtain \<sigma> where \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> A (?deadends p**)"
      using attractor_has_strategy[of "?deadends p**" "p"] A_def deadends_in_V by blast

    have "A \<subseteq> V" using A_def using attractor_is_bounded_by_V deadends_in_V by blast
    hence "A - ?deadends p** \<subseteq> V" by auto

    assume v_in_attractor: "v0 \<in> attractor p (?deadends p**)"
    have "winning_strategy p \<sigma> v0" proof (unfold winning_strategy_def, clarify)
      fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "v0 = P $ 0"
      with \<sigma>(2) v_in_attractor obtain i where i_def: "enat i < llength P" "P $ i \<in> ?deadends p**" "lset (ltake (enat i) P) \<subseteq> A"
        unfolding strategy_attracts_def strategy_attracts_via_def using A_def by blast
      have *: "enat (Suc i) = llength P" using P(2) i_def valid_path_ends_on_deadend by auto
      hence "lfinite P" using llength_eq_enat_lfiniteD by force
      moreover have "llast P \<in> VV p**" proof-
        from * have "eSuc (enat i) = llength P" by (simp add: eSuc_enat)
        moreover have "P $ i \<in> VV p**" using i_def by blast
        ultimately show ?thesis by (metis llast_conv_lnth)
      qed
      ultimately show "winning_path p P" using winning_path_def P(1) by blast
    qed
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0" using \<sigma> by blast
  } note lemma_path_to_deadend = this
  def p \<equiv> "if even n then Even else Odd"
  {
    def W \<equiv> "?deadends p"
    hence W_in_V: "W \<subseteq> V" by auto
    let ?A = "attractor p** W"
    assume v_not_in_attractor: "v0 \<in> V - ?A"
    then obtain \<sigma> where \<sigma>_def: "strategy p \<sigma>" "strategy_avoids p \<sigma> (V - ?A) ?A"
      using W_in_V attractor_has_outside_strategy[of p W] by blast

    {
      fix P
      assume "\<not>lnull P"
        and P_valid: "valid_path P"
        and P_maximal: "maximal_path P"
        and P_conforms: "path_conforms_with_strategy p P \<sigma>"
        and P_valid_start: "P $ 0 \<in> V - ?A"
      hence "lset P \<inter> ?A = {}" using \<sigma>_def(2) strategy_avoids_def by auto
      have "winning_path p P" proof (cases)
        assume P_finite: "lfinite P"
        with `\<not>lnull P` have "llast P \<in> lset P" using lfinite_lset by blast
        have "llast P \<notin> VV p" proof (rule ccontr)
          assume "\<not>llast P \<notin> VV p"
          hence "llast P \<in> VV p" by simp
          have "llast P \<in> ?A" proof-
            from `\<not>lnull P` P_maximal P_finite have "deadend (llast P)" using maximal_ends_on_deadend by blast
            with `llast P \<in> VV p` have "llast P \<in> ?deadends p" by auto
            thus ?thesis using W_def attractor_set_base by force
          qed
          with `llast P \<in> lset P` `lset P \<inter> ?A = {}` show False by blast
        qed
        moreover have "llast P \<in> VV p**" proof-
          from `llast P \<in> lset P` P_valid have "llast P \<in> V" by (meson contra_subsetD valid_path_in_V)
          with `llast P \<notin> VV p` show ?thesis by blast
        qed
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
    }
    hence "winning_strategy p \<sigma> v0" using winning_strategy_def v_not_in_attractor by presburger
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0" using \<sigma>_def(1) by blast
  } note lemma_no_path_to_deadend = this
  hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0" proof (cases)
    assume "v0 \<in> attractor p** (?deadends p)"
    hence "v0 \<in> attractor p** (?deadends p****)" by simp
    thus ?thesis using lemma_path_to_deadend[of "p**"] by (metis (no_types, lifting) attractor_set_empty equals0D)
  next
    assume "v0 \<notin> attractor p** (?deadends p)"
    hence "v0 \<in> V - attractor p** (?deadends p)" using `v0 \<in> V` by blast
    thus ?thesis using lemma_no_path_to_deadend by blast
  qed
  thus ?thesis using assms(1) by blast
qed

lemma positional_strategy_induction_step:
  assumes "v \<in> V"
    and IH: "\<And>(G :: ('a, 'b) ParityGame_scheme) v.
      \<lbrakk> card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>) < card (\<omega> ` V); v \<in> V\<^bsub>G\<^esub>; ParityGame G \<rbrakk>
        \<Longrightarrow> \<exists>p \<sigma>. ParityGame.strategy G p \<sigma> \<and> ParityGame.winning_strategy G p \<sigma> v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
proof-
  {
    def k \<equiv> "Min (\<omega> ` V)"
    fix p assume p: "winning_priority p k"
    def W0 \<equiv> "{ v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v}"
    def W1 \<equiv> "{ v \<in> V. \<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v}"
    def U \<equiv> "V - W1"
    def K \<equiv> "U \<inter> (\<omega> -` {k})"
    def V' \<equiv> "U - attractor p K"

    def G' \<equiv> "G\<lparr> verts := V', arcs := E \<inter> (V' \<times> V'), priority := \<omega>, player0 := V0 \<inter> V' \<rparr>"

    have "V' \<subseteq> V" unfolding U_def V'_def by blast
    hence "V\<^bsub>G'\<^esub> \<subseteq> V" unfolding G'_def by simp

    have "E\<^bsub>G'\<^esub> \<subseteq> E" "\<omega>\<^bsub>G'\<^esub> = \<omega>" unfolding G'_def by simp_all

    have VVp_subset: "\<And>p. ParityGame.VV G' p = V' \<inter> VV p" proof-
      fix p
      have "ParityGame.VV G' Even = V' \<inter> VV Even" unfolding G'_def by auto
      moreover have "ParityGame.VV G' Odd = V' \<inter> VV Odd" proof-
        have "V' - (V0 \<inter> V') = V' \<inter> (V - V0)" using `V' \<subseteq> V` by blast
        thus ?thesis unfolding G'_def by simp
      qed
      ultimately show "ParityGame.VV G' p = V' \<inter> VV p" by simp
    qed

    {
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"
      hence "V' \<noteq> {}" unfolding G'_def by auto

      have "ParityGame G'" proof (unfold_locales)
        have "finite (\<omega> ` V')" using `V' \<subseteq> V` priorities_finite by (meson finite_subset image_mono)
        thus "finite (\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>)" by (simp add: G'_def)
      qed (simp_all add: G'_def `V' \<noteq> {}`)

      (* Apply the induction hypothesis to get the winning regions of G'. *)
      have G'_winning_regions: "\<exists>p \<sigma>. ParityGame.strategy G' p \<sigma> \<and> ParityGame.winning_strategy G' p \<sigma> v" proof-
        have "card (\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>) < card (\<omega> ` V)" proof-
          have "k \<notin> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>" sorry
          moreover have "k \<in> \<omega> ` V" unfolding k_def by (simp add: non_empty_vertex_set priorities_finite)
          moreover have "\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub> \<subseteq> \<omega> ` V" unfolding G'_def using `V' \<subseteq> V` by auto
          ultimately show ?thesis by (metis priorities_finite psubsetI psubset_card_mono)
        qed
        with `ParityGame G'` show ?thesis using IH[of G'] `v \<in> V\<^bsub>G'\<^esub>` by blast
      qed

      (* It turns out the winning region of player p** is empty. *)
      have "\<exists>\<sigma>. ParityGame.strategy G' p \<sigma> \<and> ParityGame.winning_strategy G' p \<sigma> v" proof (rule ccontr)
        assume "\<not>?thesis"
        moreover obtain p' \<sigma> where p': "ParityGame.strategy G' p' \<sigma>" "ParityGame.winning_strategy G' p' \<sigma> v" using G'_winning_regions by blast
        ultimately have "p' \<noteq> p" by blast
        hence "p' = p**" using Player.exhaust by auto
        with p' have \<sigma>: "ParityGame.strategy G' p** \<sigma>" "ParityGame.winning_strategy G' p** \<sigma> v" by simp_all

        have "\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v" proof (rule exI, rule conjI)
          def \<sigma>' \<equiv> "override_on \<sigma>_arbitrary \<sigma> V'"
          show "strategy p** \<sigma>'" proof-
            {
              fix v assume v: "v \<in> VV p**" "\<not>deadend v"
              have "v \<rightarrow> \<sigma>' v" proof (cases)
                assume "v \<in> V'"
                hence "v \<in> ParityGame.VV G' p**" using VVp_subset[of "p**"] `v \<in> VV p**` by blast
                moreover have "\<not>Digraph.deadend G' v" sorry
                ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma> v" using \<sigma>(1) ParityGame.strategy_def[of G' "p**" \<sigma>] `ParityGame G'` by blast
                moreover have "\<sigma> v = \<sigma>' v" unfolding \<sigma>'_def using `v \<in> V'` by simp
                ultimately show ?thesis using `E\<^bsub>G'\<^esub> \<subseteq> E` by auto
              next
                assume "v \<notin> V'"
                thus ?thesis unfolding \<sigma>'_def using v valid_arbitrary_strategy unfolding strategy_def by simp
              qed
            }
            thus ?thesis unfolding strategy_def by blast
          qed
          show "winning_strategy p** \<sigma>' v" proof-
            {
              fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p** P \<sigma>'" "P $ 0 = v"
              have "Digraph.valid_path G' P" proof-
                show ?thesis sorry
              qed
              moreover have "Digraph.maximal_path G' P" proof-
                show ?thesis sorry
              qed
              moreover have "ParityGame.path_conforms_with_strategy G' p** P \<sigma>" proof-
                show ?thesis sorry
              qed
              ultimately have "ParityGame.winning_path G' p** P"
                using `\<not>lnull P` `P $ 0 = v` \<sigma>(2) `ParityGame G'` ParityGame.winning_strategy_def[of G' "p**" \<sigma>] by blast
              moreover have "ParityGame G" by unfold_locales
              moreover have "ParityGame.VV G' p**** \<subseteq> ParityGame.VV G p****" using VVp_subset by blast
              ultimately have "winning_path p** P"
                using ParityGame.winning_path_supergame[of G' "p**" P G] `ParityGame G'` `\<omega>\<^bsub>G'\<^esub> = \<omega>` by blast
            }
            thus ?thesis unfolding winning_strategy_def by blast
          qed
        qed
        moreover have "v \<in> V" using `V\<^bsub>G'\<^esub> \<subseteq> V` `v \<in> V\<^bsub>G'\<^esub>` by blast
        ultimately have "v \<in> W1" unfolding W1_def by blast
        thus False using `v \<in> V\<^bsub>G'\<^esub>` unfolding G'_def V'_def U_def by simp
      qed
    } note recursion = this

    print_statement recursion

    have "\<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" sorry
  }
  moreover have "\<exists>p. winning_priority p (Min (\<omega> ` V))" by auto
  ultimately show ?thesis by blast
qed

theorem positional_strategy_exists:
  assumes "v \<in> V"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
proof-
  have "ParityGame G" by unfold_locales
  with `v \<in> V` show ?thesis
    by (induct "card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>)" arbitrary: G v rule: nat_less_induct)
       (rule ParityGame.positional_strategy_induction_step, simp_all)
qed

end -- "context ParityGame"

end
