theory positional_strategy
imports
  Main
  parity_game strategy attractor merge_strategies attractor_strategy
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

lemma paths_stay_in_winning_region:
  assumes \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
    and \<sigma>': "\<And>v. v \<in> V \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v \<Longrightarrow> \<sigma> v = \<sigma>' v"
    and P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "P $ 0 = v0"
  shows "lset P \<subseteq> { v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }" (is "lset P \<subseteq> ?W0")
proof
  fix x assume "x \<in> lset P"
  thus "x \<in> ?W0" using assms proof (induct arbitrary: v0 rule: llist_set_induct)
    case (find P v0)
    have "lhd P \<in> V" using find(1) find(6) valid_path_in_V[of P] by auto
    moreover have "lhd P = v0" using find(1) find(9) lnth_0_conv_lhd[of P] by auto
    ultimately show ?case using find(3) assms(1) by blast
  next
    case (step P x v0)
    have "lhd P = v0" using step(1) step(11) lnth_0_conv_lhd[of P] by auto
    have "lhd P \<in> V" using step(1) step(8) valid_path_in_V[of P] by auto
    show ?case proof (cases)
      assume "lnull (ltl P)"
      hence "P = LCons v0 LNil" using step(1) `lhd P = v0` lhd_LCons_ltl llist.collapse(1) by fastforce
      thus ?thesis using step(2) step(4) step(5) `lhd P \<in> V` by auto
    next
      assume "\<not>lnull (ltl P)"
      then obtain w Ps where w: "P = LCons v0 (LCons w Ps)" using `\<not>lnull P` `lhd P = v0` by (metis lhd_LCons_ltl)
      hence "ltl P $ 0 = w" by simp
      moreover have "winning_strategy p \<sigma> w" proof (cases)
        assume "v0 \<in> VV p"
        moreover have "\<not>deadend v0" using edges_are_in_V step.prems(5) valid_path_edges' w by blast
        ultimately have "winning_strategy p \<sigma> (\<sigma> v0)" using strategy_extends_VVp step(4) step(5) by blast
        moreover have "\<sigma>' v0 = w" using step(10) w path_conforms_with_strategy_start[of p v0 w Ps] `v0 \<in> VV p` by blast
        moreover have "\<sigma> v0 = \<sigma>' v0" using \<sigma>' `lhd P = v0` `lhd P \<in> V` assms(1) step.prems(2) by blast
        ultimately show ?thesis by simp
      next
        assume "v0 \<notin> VV p"
        hence "v0 \<in> VV p**" using `lhd P = v0` `lhd P \<in> V` by blast
        moreover have "v0\<rightarrow>w" using step(8) w by (simp add: valid_path_edges')
        ultimately show ?thesis using strategy_extends_VVpstar step(4) step(5) by blast
      qed
      moreover have "valid_path (ltl P)" using step(8) valid_path_ltl by blast
      moreover have "maximal_path (ltl P)" using step(9) maximal_ltl by blast
      moreover have "path_conforms_with_strategy p (ltl P) \<sigma>'" using step(10) path_conforms_with_strategy_ltl by blast
      ultimately show ?thesis using step.hyps(3) step(4) `\<not>lnull (ltl P)` \<sigma>' by blast
    qed
  qed
qed

(* corollary paths_conforms_in_winning_region:
  assumes \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
    and P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
    and v: "\<not>(\<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v)" "v\<rightarrow>w"
  shows "path_conforms_with_strategy p P (\<sigma>(v := w))"
proof-
  from \<sigma> P have "lset P \<subseteq> { v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }" using paths_stay_in_winning_region by blast
  hence "v \<notin> lset P" using v by blast
  thus ?thesis using path_conforms_with_strategy_irrelevant P(4) by blast
qed *)

lemma winning_strategy_updates:
  assumes \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
    and v: "\<not>(\<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v)" "v\<rightarrow>w"
  shows "winning_strategy p (\<sigma>(v := w)) v0"
proof-
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P (\<sigma>(v := w))" "P $ 0 = v0"
    moreover have "\<And>v'. v' \<in> V \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v' \<Longrightarrow> \<sigma> v' = (\<sigma>(v := w)) v'" using v by auto
    ultimately have "lset P \<subseteq> { v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }" using paths_stay_in_winning_region[of p \<sigma> v0 "\<sigma>(v := w)" P] assms(1) assms(2) by blast
    hence "v \<notin> lset P" using v by blast
    hence "path_conforms_with_strategy p P \<sigma>" using P(4) path_conforms_with_strategy_irrelevant' by blast
    hence "winning_path p P" using \<sigma>(2) winning_strategy_def P by blast
  }
  thus ?thesis unfolding winning_strategy_def by blast
qed

lemma path_helper_ltl:
  assumes P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
    and P': "P = LCons v0 P'" "\<not>deadend v0"
  shows "\<not>lnull P'" "valid_path P'" "maximal_path P'" "path_conforms_with_strategy p P' \<sigma>" "P' $ 0 = lhd P'" "v0 \<rightarrow> lhd P'"
proof-
  have P_ltl: "ltl P = P'" using P'(1) by auto
  show "\<not>lnull P'" using P' P(3) maximal_no_deadend by blast
  then obtain w Ps where w: "P = LCons v0 (LCons w Ps)" using P' by (metis lhd_LCons_ltl)
  show "valid_path P'" using P_ltl P(2) valid_path_ltl by blast
  show "maximal_path P'" using P_ltl P(3) maximal_ltl by blast
  show "path_conforms_with_strategy p P' \<sigma>" using P_ltl P(4) path_conforms_with_strategy_ltl by blast
  have "P' $ 0 = w" using w by (simp add: P')
  thus "P' $ 0 = lhd P'" using w P'(1) by simp
  show "v0 \<rightarrow> lhd P'" using P(2) w P' by (simp add: assms(6) valid_path_edges')
qed

(* TODO: the following two lemmas are backwards, they have too many **. *)
lemma strategy_extends_backwards_VVp:
  assumes v0: "v0 \<in> VV p"
    and \<sigma>: "strategy p** \<sigma>" "\<And>w. v0\<rightarrow>w \<Longrightarrow> winning_strategy p** \<sigma> w"
  shows "winning_strategy p** \<sigma> v0"
proof-
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p** P \<sigma>" "P $ 0 = v0"
    obtain P' where P': "P = LCons v0 P'" using P(1) P(5) by (metis lhd_LCons_ltl lnth_0)
    hence P_ltl: "ltl P = P'" by auto
    have "winning_path p** P" proof (cases)
      assume "deadend v0"
      hence "P = LCons v0 LNil" using P' P(2) valid_path_cons_simp by auto
      thus ?thesis using winning_path_def v0 `\<not>lnull P` by auto
    next
      assume "\<not>deadend v0"
      have "winning_path p** P'" using \<sigma>(2)[unfolded winning_strategy_def, of "lhd P'"] path_helper_ltl[OF P P' `\<not>deadend v0`] by blast
      thus "winning_path p** P" using winning_path_LCons P' path_helper_ltl(1)[OF P P' `\<not>deadend v0`] by blast
    qed
  }
  thus ?thesis unfolding winning_strategy_def by blast
qed

lemma strategy_extends_backwards_VVpstar:
  assumes v0: "v0 \<in> VV p**" "\<sigma> v0 = w" "v0\<rightarrow>w"
    and \<sigma>: "strategy p** \<sigma>" "winning_strategy p** \<sigma> w"
  shows "winning_strategy p** \<sigma> v0"
proof-
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p** P \<sigma>" "P $ 0 = v0"
    obtain P' where P': "P = LCons v0 P'" using P(1) P(5) by (metis lhd_LCons_ltl lnth_0)
    hence P_ltl: "ltl P = P'" by auto
    have "\<not>deadend v0" using `v0\<rightarrow>w` edges_are_in_V by blast
    have "\<not>lnull P'" using path_helper_ltl(1)[OF P P' `\<not>deadend v0`] by blast
    have "P' $ 0 = w" proof-
      obtain w' Ps where w': "P = LCons v0 (LCons w' Ps)" using `\<not>lnull P'` P' by (metis lhd_LCons_ltl)
      hence "\<sigma> v0 = w'" using v0(1) P(4) path_conforms_with_strategy_start by blast
      hence "lhd P' = w" using v0(2) w' P' by auto
      thus ?thesis by (simp add: `\<not>lnull P'` lnth_0_conv_lhd)
    qed
    hence "winning_path p** P'" using path_helper_ltl[OF P P' `\<not>deadend v0`] \<sigma>(2)[unfolded winning_strategy_def] P P' by blast
    hence "winning_path p** P" using winning_path_LCons P' `\<not>lnull P'` by blast
  }
  thus ?thesis unfolding winning_strategy_def by blast
qed

lemma positional_strategy_induction_step:
  assumes "v \<in> V"
    and no_deadends: "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
    and IH: "\<And>(G :: ('a, 'b) ParityGame_scheme) v.
      \<lbrakk> card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>) < card (\<omega> ` V); v \<in> V\<^bsub>G\<^esub>; ParityGame G; \<And>v. v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<not>Digraph.deadend G v  \<rbrakk>
        \<Longrightarrow> \<exists>p \<sigma>. ParityGame.strategy G p \<sigma> \<and> ParityGame.winning_strategy G p \<sigma> v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
proof-
  {
    def min_prio \<equiv> "Min (\<omega> ` V)"
    fix p assume p: "winning_priority p min_prio"
    def W0 \<equiv> "{ v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }"
    def W1 \<equiv> "{ v \<in> V. \<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v }"
    def U \<equiv> "V - W1"
    def K \<equiv> "U \<inter> (\<omega> -` {min_prio})"
    def V' \<equiv> "U - attractor p K"

    def [simp]: G' \<equiv> "subgame V'"

    have "V' \<subseteq> V" unfolding U_def V'_def by blast
    hence [simp]: "V\<^bsub>G'\<^esub> = V'" unfolding G'_def by simp

    have "V\<^bsub>G'\<^esub> \<subseteq> V" "E\<^bsub>G'\<^esub> \<subseteq> E" "\<omega>\<^bsub>G'\<^esub> = \<omega>" unfolding G'_def by (simp_all add: subgame_\<omega>)
    have "ParityGame.VV G' p = V' \<inter> VV p" unfolding G'_def using subgame_VV by simp

    have V_decomp: "V = attractor p K \<union> V' \<union> W1" proof-
      have "V - W1 \<subseteq> attractor p K \<union> V'" unfolding V'_def U_def by auto
      hence "V \<subseteq> attractor p K \<union> V' \<union> W1" by blast
      moreover have "attractor p K \<subseteq> V" by (metis Diff_subset K_def U_def attractor_is_bounded_by_V inf_le1 subset_trans)
      ultimately show ?thesis unfolding W1_def using `V' \<subseteq> V` by blast
    qed
    hence V_decomp': "V = (attractor p K - K) \<union> V' \<union> K \<union> W1" using attractor_set_base by blast
    obtain \<sigma>W1 where \<sigma>W1: "strategy p** \<sigma>W1" "\<And>v. v \<in> W1 \<Longrightarrow> winning_strategy p** \<sigma>W1 v"
      using merge_winning_strategies[of W1 "p**"] W1_def by fastforce

    have G'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>Digraph.deadend G' v" proof-
      fix v assume v: "v \<in> V\<^bsub>G'\<^esub>"
      {
        assume "Digraph.deadend G' v"
        hence not_in_V': "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<notin> V'" proof-
          fix w assume "v\<rightarrow>w"
          { assume "w \<in> V'"
            hence "w \<in> V\<^bsub>G'\<^esub>" using `V\<^bsub>G'\<^esub> = V'` by blast
            moreover hence "v \<rightarrow>\<^bsub>G'\<^esub> w" unfolding G'_def using `V' \<subseteq> V` `v \<in> V\<^bsub>G'\<^esub>` `v\<rightarrow>w` by simp
            ultimately have False using `Digraph.deadend G' v` by blast
          }
          thus "w \<notin> V'" by blast
        qed
        have "v \<in> V" using `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> \<subseteq> V` by blast
        have "v \<in> V'" using `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> = V'` by blast
        hence "v \<notin> W1" unfolding V'_def U_def by blast
        have "\<not>deadend v" using no_deadends v `V\<^bsub>G'\<^esub> \<subseteq> V` by blast
        moreover {
          assume "v \<in> VV p"
          {
            fix w assume "v\<rightarrow>w"
            {
              assume "w \<in> attractor p K"
              hence "v \<in> attractor p K" using `v \<in> VV p` `v\<rightarrow>w` attractor_set_VVp by blast
              hence False using `v \<in> V'` V'_def by blast
            }
            hence "w \<notin> attractor p K" by blast
            hence "w \<in> W1" using not_in_V' V_decomp `v\<rightarrow>w` edges_are_in_V by blast
          }
          (* All successors of v point to W1, so v \<in> W1 *)
          hence "winning_strategy p** \<sigma>W1 v" using strategy_extends_backwards_VVp[of v p \<sigma>W1] \<sigma>W1 `v \<in> VV p` by blast
          hence False using W1_def \<sigma>W1(1) `v \<in> VV p` `v \<notin> W1` by blast
        }
        moreover {
          assume "v \<notin> VV p"
          hence "v \<in> VV p**" using `\<not>deadend v` edges_are_in_V by auto
          {
            fix w assume "v\<rightarrow>w"
            {
              assume "w \<in> W1"
              let ?\<sigma>W1 = "\<sigma>W1(v := w)"
              have "strategy p** ?\<sigma>W1" by (simp add: \<sigma>W1(1) `v\<rightarrow>w` valid_strategy_updates)
              moreover have "winning_strategy p** ?\<sigma>W1 v" proof-
                have "\<not>(\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v)" using `v \<notin> W1` `v \<in> V` W1_def by auto
                moreover have "winning_strategy p** \<sigma>W1 w" using `w \<in> W1` \<sigma>W1(2) by blast
                ultimately have "winning_strategy p** ?\<sigma>W1 w" using winning_strategy_updates[of "p**" \<sigma>W1 w v w] \<sigma>W1 `v\<rightarrow>w` by blast
                thus ?thesis using strategy_extends_backwards_VVpstar[of v p ?\<sigma>W1 w] `v \<in> VV p**` `v\<rightarrow>w` `strategy p** ?\<sigma>W1` by auto
              qed
              ultimately have "v \<in> W1" using W1_def \<sigma>W1(1) `v \<in> VV p**` by blast
              hence False using `v \<in> V'` V'_def U_def by blast
            }
            hence "w \<notin> W1" by blast
            hence "w \<in> attractor p K" using not_in_V' V_decomp `v\<rightarrow>w` edges_are_in_V by blast
          }
          (* All successors of v point to attractor p K, so v \<in> attractor p K *)
          hence "v \<in> attractor p K" using `v \<in> VV p**` attractor_set_VVpstar `\<not>deadend v` by blast
          hence False using `v \<in> V'` V'_def by blast
        }
        ultimately have False by blast
      }
      thus "\<not>Digraph.deadend G' v" by blast
    qed

    {
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"
      hence "V' \<inter> V \<noteq> {}" using `V' \<subseteq> V` by auto
      hence "Digraph G'" "ParityGame G'" using subgame_Digraph subgame_ParityGame by simp_all

      (* Apply the induction hypothesis to get the winning regions of G'. *)
      have G'_winning_regions: "\<exists>p \<sigma>. ParityGame.strategy G' p \<sigma> \<and> ParityGame.winning_strategy G' p \<sigma> v" proof-
        have "card (\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>) < card (\<omega> ` V)" proof-
          { assume "min_prio \<in> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>"
            then obtain v where v: "v \<in> V\<^bsub>G'\<^esub>" "\<omega>\<^bsub>G'\<^esub> v = min_prio" by blast
            hence "v \<in> \<omega> -` {min_prio}" using `\<omega>\<^bsub>G'\<^esub> = \<omega>` by simp
            hence False using V'_def K_def attractor_set_base `V\<^bsub>G'\<^esub> = V'` v(1) by (metis DiffD1 DiffD2 IntI contra_subsetD)
          }
          hence "min_prio \<notin> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>" by blast
          moreover have "min_prio \<in> \<omega> ` V" unfolding min_prio_def by (simp add: non_empty_vertex_set priorities_finite)
          moreover have "\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub> \<subseteq> \<omega> ` V" unfolding G'_def by simp
          ultimately show ?thesis by (metis priorities_finite psubsetI psubset_card_mono)
        qed
        with `ParityGame G'` show ?thesis using IH[of G'] `v \<in> V\<^bsub>G'\<^esub>` G'_no_deadends by blast
      qed

      (* It turns out the winning region of player p** is empty. *)
      have "\<exists>\<sigma>. ParityGame.strategy G' p \<sigma> \<and> ParityGame.winning_strategy G' p \<sigma> v" proof (rule ccontr)
        assume "\<not>?thesis"
        moreover obtain p' \<sigma> where p': "ParityGame.strategy G' p' \<sigma>" "ParityGame.winning_strategy G' p' \<sigma> v" using G'_winning_regions by blast
        ultimately have "p' \<noteq> p" by blast
        hence "p' = p**" using Player.exhaust by auto
        with p' have \<sigma>: "ParityGame.strategy G' p** \<sigma>" "ParityGame.winning_strategy G' p** \<sigma> v" by simp_all

        have "\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v" proof (rule exI, rule conjI)
          def \<sigma>' \<equiv> "override_on (override_on \<sigma>_arbitrary \<sigma>W1 W1) \<sigma> V'"
          show "strategy p** \<sigma>'" proof-
            {
              fix v assume v: "v \<in> VV p**" "\<not>deadend v"
              have "v \<rightarrow> \<sigma>' v" proof (cases)
                assume "v \<in> V'"
                hence "v \<in> ParityGame.VV G' p**" using subgame_VV[of "p**"] `v \<in> VV p**` G'_def by fastforce
                moreover have "\<not>Digraph.deadend G' v" using G'_no_deadends `v \<in> V'` `V\<^bsub>G'\<^esub> = V'` by blast
                ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma> v" using \<sigma>(1) ParityGame.strategy_def[of G' "p**" \<sigma>] `ParityGame G'` by blast
                moreover have "\<sigma> v = \<sigma>' v" unfolding \<sigma>'_def using `v \<in> V'` by simp
                ultimately show ?thesis using `E\<^bsub>G'\<^esub> \<subseteq> E` G'_def by fastforce
              next
                assume "v \<notin> V'"
                thus ?thesis unfolding \<sigma>'_def using v valid_arbitrary_strategy \<sigma>W1(1) unfolding strategy_def by (metis (no_types, lifting) override_on_def)
              qed
            }
            thus ?thesis unfolding strategy_def by blast
          qed
          show "winning_strategy p** \<sigma>' v"
          proof (unfold winning_strategy_def, intro allI impI, elim conjE, rule ccontr)
            fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p** P \<sigma>'" "P $ 0 = v"
            assume "\<not>winning_path p** P"
            (* First we show that P stays in V', because if it stays in V', then it conforms to \<sigma>,
            so it must be winning for p**. *)
            have "lset P \<subseteq> V'" proof (rule ccontr)
              (* Assume P does not stay in V'. *)
              assume "\<not>lset P \<subseteq> V'"
              (* Then there exists a minimal n where it leaves V', which cannot be 0. *)
              hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> V'" by (simp add: lset_subset)
              then obtain n where n: "enat n < llength P" "P $ n \<notin> V'" "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> V')"
                using obtain_min[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> V'"] by metis
              have n_min: "\<And>i. i < n \<Longrightarrow> P $ i \<in> V'" using n(1) n(3) dual_order.strict_trans enat_ord_simps(2) by blast
              have "n \<noteq> 0" using n(2) P(5) `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> = V'` by metis
              then obtain n' where n': "Suc n' = n" using nat.exhaust by metis
              hence "P $ n' \<in> V'" using n_min by blast
              show False proof (cases)
                assume "P $ n' \<in> VV p"
                show False proof (cases)
                  (* P leaves V' to enter W1.  This is fatal for player p. *)
                  assume "P $ n \<in> W1"
                  def P' \<equiv> "ldropn n P"
                  (* P' is winning in W1 because \<sigma>' is \<sigma>W1 on W1. *)
                  have "\<not>lnull P'" using P'_def n(1) by auto
                  moreover have "valid_path P'" using P'_def P(2) valid_path_drop by blast
                  moreover have "maximal_path P'" using P'_def P(3) maximal_drop by blast
                  moreover have "P' $ 0 = P $ n" unfolding P'_def by (simp add: n(1))
                  moreover have "path_conforms_with_strategy p** P' \<sigma>W1" proof-
                    have *: "path_conforms_with_strategy p** P' \<sigma>'" using P'_def P(4) path_conforms_with_strategy_drop by blast
                    have "\<And>v. v \<in> V \<Longrightarrow> \<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v \<Longrightarrow> \<sigma>W1 v = \<sigma>' v" proof-
                      fix v assume "v \<in> V" "\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v"
                      hence "v \<in> W1" unfolding W1_def by blast
                      thus "\<sigma>W1 v = \<sigma>' v" by (simp add: U_def V'_def \<sigma>'_def)
                    qed
                    hence "lset P' \<subseteq> W1"
                      using W1_def paths_stay_in_winning_region[of "p**" \<sigma>W1 "P $ n" \<sigma>' P']
                      \<sigma>W1 `P $ n \<in> W1` `\<not>lnull P'` `valid_path P'` `maximal_path P'` "*" `P' $ 0 = P $ n`
                      by blast
                    moreover have "\<And>v. v \<in> W1 \<Longrightarrow> \<sigma>' v = \<sigma>W1 v" by (simp add: U_def V'_def \<sigma>'_def)
                    ultimately show ?thesis by (metis "*" path_conforms_with_strategy_irrelevant_updates subsetCE)
                  qed
                  ultimately have "winning_path p** P'" using \<sigma>W1(2)[unfolded winning_strategy_def, of "P $ n"] `P $ n \<in> W1` by blast
                  thus False using P'_def winning_path_drop_add[OF P(2)] n(1) `\<not>winning_path p** P` by blast
                next
                  (* P leaves V' to enter attractor p K.  Then P $ n' must already be in the
                  attractor because there is an edge, which is a contradiction to P $ n' \<in> V'. *)
                  assume "P $ n \<notin> W1"
                  hence "P $ n \<in> attractor p K" using V_decomp n(2) P(2) n(1) valid_path_finite_in_V' by blast
                  moreover have "P $ n' \<rightarrow> P $ n" using P(2) n' n(1) valid_path_impl1 by blast
                  ultimately have "P $ n' \<in> attractor p K" using `P $ n' \<in> VV p` attractor_set_VVp by blast
                  thus False using `P $ n' \<in> V'` V'_def by blast
                qed
              next
                (* P leaves V' from a p** node. P conforms to \<sigma> on V'.  On p** nodes \<sigma> always
                chooses a successor in V', so this cannot be a p** node. *)
                assume "P $ n' \<notin> VV p"
                hence "P $ n' \<in> VV p**" using `P $ n' \<in> V'` `V' \<subseteq> V` by auto
                moreover have "enat (Suc n') < llength P" using n' n(1) by blast
                ultimately have "\<sigma>' (P $ n') = P $ Suc n'"
                  using P(2) P(4) path_conforms_with_strategy_conforms[of P "p**" \<sigma>' n'] by blast
                hence *: "\<sigma> (P $ n') = P $ Suc n'"
                  using \<sigma>'_def `P $ n' \<in> V'` by auto
                have "\<not>Digraph.deadend G' (P $ n')"
                  using `P $ n' \<in> V'` G'_no_deadends `V\<^bsub>G'\<^esub> = V'` by blast
                moreover have "P $ n' \<in> ParityGame.VV G' p**"
                  using `P $ n' \<in> VV p**` `P $ n' \<in> V'` subgame_VV[of "p**" V'] G'_def by fastforce
                ultimately have "P $ n' \<rightarrow>\<^bsub>G'\<^esub> \<sigma> (P $ n')"
                  using \<sigma>(1)[unfolded ParityGame.strategy_def[OF `ParityGame G'`]] `P $ n' \<in> VV p**` by blast
                hence "P $ n' \<rightarrow>\<^bsub>G'\<^esub> P $ n" using * n' by simp
                hence "P $ n \<in> V'"
                  using `V\<^bsub>G'\<^esub> = V'` Digraph.edges_are_in_V[OF `Digraph G'`] by blast
                thus False using n(2) by blast
              qed
            qed (* lset P \<subseteq> V' *)
            hence "Digraph.valid_path G' P" using G'_def subgame_valid_path P(2) `V' \<inter> V \<noteq> {}` by blast
            moreover have "Digraph.maximal_path G' P" using `lset P \<subseteq> V'` G'_def subgame_maximal_path P(3) `V' \<inter> V \<noteq> {}` `V' \<subseteq> V` by blast
            moreover have "ParityGame.path_conforms_with_strategy G' p** P \<sigma>" proof-
              have "ParityGame.path_conforms_with_strategy G' p** P \<sigma>'"
                using subgame_path_conforms_with_strategy `V' \<inter> V \<noteq> {}` `V' \<subseteq> V` `lset P \<subseteq> V'` P(4) by auto
              moreover have "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma>' v = \<sigma> v"
                using `lset P \<subseteq> V'` \<sigma>'_def by auto
              ultimately show ?thesis
                using ParityGame.path_conforms_with_strategy_irrelevant_updates `ParityGame G'` by blast
            qed
            ultimately have "ParityGame.winning_path G' p** P"
              using `\<not>lnull P` `P $ 0 = v` \<sigma>(2) `ParityGame G'` ParityGame.winning_strategy_def[of G' "p**" \<sigma>] by blast
            moreover have "ParityGame G" by unfold_locales
            moreover have "ParityGame.VV G' p**** \<subseteq> ParityGame.VV G p****" using subgame_VV_subset G'_def by blast
            ultimately show False
              using ParityGame.winning_path_supergame[of G' "p**" P G] `ParityGame G'` `\<omega>\<^bsub>G'\<^esub> = \<omega>` `\<not>winning_path p** P` by blast
          qed
        qed
        moreover have "v \<in> V" using `V\<^bsub>G'\<^esub> \<subseteq> V` `v \<in> V\<^bsub>G'\<^esub>` by blast
        ultimately have "v \<in> W1" unfolding W1_def by blast
        thus False using `v \<in> V\<^bsub>G'\<^esub>` using U_def V'_def `V\<^bsub>G'\<^esub> = V'` `v \<in> V\<^bsub>G'\<^esub>` by blast
      qed
    } note recursion = this

    {
      assume "V\<^bsub>G'\<^esub> \<noteq> {}"
      hence "V' \<inter> V \<noteq> {}" using `V' \<subseteq> V` by auto
      hence "ParityGame G'" using subgame_ParityGame by simp
    } note G'_ParityGame = this

    obtain \<sigma>1 where \<sigma>1: "strategy p \<sigma>1" "strategy_attracts p \<sigma>1 (attractor p K) K" using attractor_has_strategy[of K p] K_def U_def by auto
    obtain \<sigma>2 where \<sigma>2: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> ParityGame.strategy G' p \<sigma>2" "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> ParityGame.winning_strategy G' p \<sigma>2 v"
      using ParityGame.merge_winning_strategies[of G' "V\<^bsub>G'\<^esub>"] recursion G'_ParityGame by blast

    def choose \<equiv> "\<lambda>v. SOME w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)"
    def \<sigma> \<equiv> "override_on (override_on choose \<sigma>2 V') \<sigma>1 (attractor p K - K)"

    have "attractor p K \<inter> W1 = {}" proof (rule ccontr)
      assume "attractor p K \<inter> W1 \<noteq> {}"
      then obtain v where v: "v \<in> attractor p K" "v \<in> W1" by blast
      hence "v \<in> V" using W1_def by blast
      obtain P where P: "\<not>lnull P" "P $ 0 = v" "valid_path P" "maximal_path P"
        and P_conforms_\<sigma>1: "path_conforms_with_strategy p P \<sigma>1"
        and P_conforms_\<sigma>W1: "path_conforms_with_strategy p** P \<sigma>W1"
        using strategy_conforming_path_exists \<sigma>W1(1) \<sigma>1(1) `v \<in> V` by blast
      have "strategy_attracts_via p \<sigma>1 v (attractor p K) K" using v(1) \<sigma>1(2) strategy_attracts_def by blast
      hence "\<exists>n. enat n < llength P \<and> P $ n \<in> K" unfolding strategy_attracts_via_def using P P_conforms_\<sigma>1 by blast
      moreover have "K \<inter> W1 = {}" using K_def U_def by blast
      ultimately have "\<not>lset P \<subseteq> W1" by (meson disjoint_iff_not_equal lset_lnth)
      thus False unfolding W1_def
        using paths_stay_in_winning_region[of "p**" \<sigma>W1 v \<sigma>W1 P] \<sigma>W1 P P_conforms_\<sigma>W1 v(2) by blast
    qed

    have \<sigma>_\<sigma>1 [simp]: "\<And>v. v \<in> attractor p K - K \<Longrightarrow> \<sigma> v = \<sigma>1 v" unfolding \<sigma>_def by simp
    have \<sigma>_\<sigma>2 [simp]: "\<And>v. v \<in> V' \<Longrightarrow> \<sigma> v = \<sigma>2 v" unfolding \<sigma>_def V'_def by auto
    have \<sigma>_K [simp]: "\<And>v. v \<in> K \<union> W1 \<Longrightarrow> \<sigma> v = choose v" proof-
      fix v assume "v \<in> K \<union> W1"
      moreover hence "v \<notin> V'" unfolding V'_def U_def using attractor_set_base by auto
      ultimately show "\<sigma> v = choose v" unfolding \<sigma>_def U_def using `attractor p K \<inter> W1 = {}`
        by (metis (mono_tags, lifting) Diff_iff IntI UnE override_on_def override_on_emptyset)
    qed

    { fix v assume v: "v \<in> VV p"
      hence "\<not>deadend v" using no_deadends by blast
      have "\<exists>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)" proof (cases)
        assume "v \<in> W1"
        thus ?thesis using no_deadends `\<not>deadend v` by blast
      next
        assume "v \<notin> W1"
        show ?thesis proof (rule ccontr)
          assume "\<not>(\<exists>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1))"
          hence "\<And>w. v\<rightarrow>w \<Longrightarrow> winning_strategy p** \<sigma>W1 w" using \<sigma>W1(2) by blast
          hence "winning_strategy p** \<sigma>W1 v" using strategy_extends_backwards_VVp \<sigma>W1(1) `v \<in> VV p` by blast
          hence "v \<in> W1" unfolding W1_def using \<sigma>W1(1) edges_are_in_V `\<not>deadend v` by blast
          thus False using `v \<notin> W1` by blast
        qed
      qed
      hence "v\<rightarrow>choose v" "v \<in> W1 \<or> choose v \<notin> W1" unfolding choose_def
        using someI_ex[of "\<lambda>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)"] by blast+
    } note choose_works = this

    have "strategy p \<sigma>" proof-
      { fix v assume v: "v \<in> VV p" "\<not>deadend v"
        hence "v \<in> attractor p K - K \<Longrightarrow> v\<rightarrow>\<sigma> v" using \<sigma>_\<sigma>1 \<sigma>1(1) v unfolding strategy_def by auto
        moreover have "v \<in> V' \<Longrightarrow> v\<rightarrow>\<sigma> v" proof-
          assume "v \<in> V'"
          moreover have "v \<in> V\<^bsub>G'\<^esub>" using `v \<in> V'` `V\<^bsub>G'\<^esub> = V'` by blast
          moreover hence "ParityGame G'" using G'_ParityGame by blast
          moreover have "v \<in> ParityGame.VV G' p" using `ParityGame.VV G' p = V' \<inter> VV p` `v \<in> V'` `v \<in> VV p` by blast
          moreover have "\<not>Digraph.deadend G' v" using G'_no_deadends `v \<in> V\<^bsub>G'\<^esub>` by blast
          ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma>2 v" using \<sigma>2(1) ParityGame.strategy_def[of G' p \<sigma>2] by blast
          with `v \<in> V'` show "v\<rightarrow>\<sigma> v" using `E\<^bsub>G'\<^esub> \<subseteq> E` \<sigma>_\<sigma>2 by (metis subsetCE)
        qed
        moreover have "v \<in> K \<union> W1 \<Longrightarrow> v\<rightarrow>\<sigma> v" using choose_works(1) v by auto
        moreover have "v \<in> V" using `v \<in> VV p` by blast
        ultimately have "v\<rightarrow>\<sigma> v" using `V = (attractor p K - K) \<union> V' \<union> K \<union> W1` by blast
      }
      thus ?thesis unfolding strategy_def by blast
    qed

    have \<sigma>_attracts: "strategy_attracts p \<sigma> (attractor p K) K" proof-
      have "strategy_attracts p (override_on \<sigma> \<sigma>1 (attractor p K - K)) (attractor p K) K"
        using strategy_attracts_irrelevant_override \<sigma>1 `strategy p \<sigma>` by blast
      moreover have "\<sigma> = override_on \<sigma> \<sigma>1 (attractor p K - K)" by (rule ext) (simp add: override_on_def)
      ultimately show ?thesis by simp
    qed

    have "\<forall>v \<in> V - W1. winning_strategy p \<sigma> v" proof-
      {
        fix v P assume P: "v \<in> V - W1"
          "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v"
        have "lset P \<subseteq> V" using P(3) valid_path_in_V by blast
        hence "\<not>lfinite P" using no_deadends P(2) P(4) lfinite_lset maximal_ends_on_deadend by blast
        have "lset P \<subseteq> V - W1" proof
          fix v' assume "v' \<in> lset P"
          thus "v' \<in> V - W1" using P proof (induct arbitrary: v rule: llist_set_induct)
            case (find P')
            thus ?case by (simp add: lhd_conv_lnth)
          next
            case (step P' v')
            have "lset (ltl P') \<subseteq> V" by (simp add: step.prems(3) valid_path_in_V valid_path_ltl)
            hence "v' \<in> V" using step.hyps(2) by blast
            hence "\<not>deadend v'" using no_deadends by blast
            have "\<not>lnull (ltl P')" by (metis DiffE Diff_empty lset_eq_empty step.hyps(2))
            moreover have "valid_path (ltl P')" using step.prems(3) valid_path_ltl by blast
            moreover have "maximal_path (ltl P')" using step.prems(4) maximal_ltl by blast
            moreover have "path_conforms_with_strategy p (ltl P') \<sigma>" using step.prems(5) path_conforms_with_strategy_ltl by blast
            moreover have "ltl P' $ 0 = lhd (ltl P')" using `\<not>lnull (ltl P')` lnth_0_conv_lhd by blast
            moreover have "lhd (ltl P') \<in> V - W1" proof (rule ccontr)
              assume "lhd (ltl P') \<notin> V - W1"
              hence "lhd (ltl P') \<in> W1" using `lset (ltl P') \<subseteq> V` `\<not>lnull (ltl P')` by (meson DiffI llist.set_sel(1) subsetCE)
              moreover obtain w Ps where w: "ltl P' = LCons w Ps" using `\<not>lnull (ltl P')` by (meson not_lnull_conv step.prems(2))
              ultimately have "w \<in> W1" by simp
              have P'_cons: "P' = LCons v (LCons w Ps)"
                using w step.prems(2) step.prems(6) lnth_0_conv_lhd lhd_LCons_ltl by fastforce
              hence "v\<rightarrow>w" using step.prems(3) by (simp add: valid_path_edges')
              show False proof (cases)
                assume "v \<in> VV p"
                hence "\<sigma> v = w" using step.prems(5) P'_cons path_conforms_with_strategy_start by blast
                { assume *: "v \<in> attractor p K - K"
                  hence "\<sigma>1 v = w" using `\<sigma> v = w` by simp
                  have "strategy_attracts_via p \<sigma> v (attractor p K) K" using * strategy_attracts_def \<sigma>_attracts by blast
                  hence "\<exists>n. enat n < llength P' \<and> P' $ n \<in> K \<and> lset (ltake (enat n) P') \<subseteq> attractor p K"
                    using strategy_attracts_via_def step.prems by blast
                  then obtain n where n: "enat n < llength P' \<and> P' $ n \<in> K \<and> lset (ltake (enat n) P') \<subseteq> attractor p K"
                    "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P' \<and> P' $ i \<in> K \<and> lset (ltake (enat i) P') \<subseteq> attractor p K)"
                    using obtain_min[of "\<lambda>n. enat n < llength P' \<and> P' $ n \<in> K \<and> lset (ltake (enat n) P') \<subseteq> attractor p K"] by blast
                  hence n_min: "\<And>i. i < n \<Longrightarrow> P' $ i \<notin> K" proof-
                    fix i assume "i < n"
                    moreover hence "enat i < llength P'" using n(1) dual_order.strict_trans enat_ord_simps(2) by blast
                    moreover have "lset (ltake (enat i) P') \<subseteq> lset (ltake (enat n) P')" using `i < n` lprefix_lset' by simp
                    ultimately show "P' $ i \<notin> K" using n by blast
                  qed
                  have "v \<notin> K" using * by blast
                  hence "n \<noteq> 0" using n(1) step.prems(6) by meson
                  have "w \<in> K" proof (rule ccontr)
                    assume "w \<notin> K"
                    hence "Suc 0 \<noteq> n" using P'_cons n(1) by auto
                    hence "Suc (Suc 0) \<le> n" using `n \<noteq> 0` by presburger
                    hence "lset (ltake (enat (Suc (Suc 0))) P') \<subseteq> attractor p K" using n by (meson enat_ord_simps(1) lprefix_lset' subset_trans)
                    hence "lset (ltake (eSuc (eSuc 0)) P') \<subseteq> attractor p K" by (simp add: eSuc_enat zero_enat_def)
                    hence "ltake (eSuc (eSuc 0)) P' $ Suc 0 \<in> attractor p K" by (metis `\<not>lnull (ltl P')` enat_ltl_Suc i0_less llength_eq_0 lset_lnth ltake.disc(2) ltake_ltl zero_enat_def zero_ne_eSuc)
                    hence "w \<in> attractor p K" using P'_cons by simp
                    thus False using `w \<in> W1` `attractor p K \<inter> W1 = {}` by blast
                  qed
                  hence False using `w \<in> W1` K_def U_def by blast
                }
                moreover { assume "v \<in> V'"
                  hence "\<sigma>2 v = w" using `\<sigma> v = w` by simp
                  moreover have "v \<in> V\<^bsub>G'\<^esub>" using `V\<^bsub>G'\<^esub> = V'` `v \<in> V'` by simp
                  moreover hence "ParityGame G'" using G'_ParityGame by blast
                  moreover have "ParityGame.strategy G' p \<sigma>2" using \<sigma>2(1) `v \<in> V\<^bsub>G'\<^esub>` by blast
                  ultimately have "w \<in> V\<^bsub>G'\<^esub>"
                    using G'_no_deadends ParityGame.valid_strategy_in_V `v \<in> V'` `v \<in> VV p` by fastforce
                  hence False using `V\<^bsub>G'\<^esub> = V'` `w \<in> W1` V'_def U_def by blast
                }
                moreover { assume "v \<in> K"
                  hence "choose v = w" using `\<sigma> v = w` by simp
                  hence False using choose_works(2) `v \<in> VV p` `v \<in> V - W1` `w \<in> W1` by blast
                }
                ultimately show False using `v \<in> V - W1` V_decomp' by blast
              next
                assume "v \<notin> VV p"
                hence "v \<in> VV p**" using step.prems(1) by blast
                let ?\<sigma> = "\<sigma>W1(v := w)"
                have "winning_strategy p** \<sigma>W1 w" using `w \<in> W1` \<sigma>W1(2) by blast
                moreover have "\<not>(\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v)" using `v \<in> V - W1` W1_def by blast
                ultimately have "winning_strategy p** ?\<sigma> w" using winning_strategy_updates[of "p**" \<sigma>W1 w v w] \<sigma>W1(1) `v\<rightarrow>w` by blast
                moreover have "strategy p** ?\<sigma>" using `v\<rightarrow>w` \<sigma>W1(1) valid_strategy_updates by blast
                ultimately have "winning_strategy p** ?\<sigma> v" using strategy_extends_backwards_VVpstar[of v p ?\<sigma> w] `v \<in> VV p**` `v\<rightarrow>w` by auto
                hence "v \<in> W1" unfolding W1_def using `strategy p** ?\<sigma>` `v \<in> V - W1` by blast
                thus False using `v \<in> V - W1` by blast
              qed
            qed
            ultimately show "v' \<in> V - W1" using step.hyps(3) `lset (ltl P') \<subseteq> V` by blast
          qed
        qed
        hence "lset P \<subseteq> attractor p K \<union> V'" using V_decomp by blast
        have "winning_path p P" proof (cases)
          assume "\<exists>n. lset (ldropn n P) \<subseteq> V'"
          (* P eventually stays in V'. *)
          then obtain n where n: "lset (ldropn n P) \<subseteq> V'" by blast
          def P' \<equiv> "ldropn n P"
          have "\<not>lnull P'" using P'_def `\<not>lfinite P` infinite_no_deadend lfinite_ldropn by blast
          moreover have "lset P' \<subseteq> V'" using P'_def n by simp
          ultimately have "lhd P' \<in> V'" by auto
          hence "V' \<inter> V \<noteq> {}" using `V' \<subseteq> V` by auto
          have "Digraph.valid_path G' P'" proof-
            have "valid_path P'" using P'_def P(3) valid_path_drop by blast
            thus ?thesis using subgame_valid_path `lset P' \<subseteq> V'` `V' \<inter> V \<noteq> {}` G'_def by blast
          qed
          moreover have "Digraph.maximal_path G' P'" proof-
            have "maximal_path P'" using P'_def P(4) maximal_drop by blast
            thus ?thesis using subgame_maximal_path `lset P' \<subseteq> V'` `V' \<inter> V \<noteq> {}` `V' \<subseteq> V` G'_def by blast
          qed
          moreover have "ParityGame.path_conforms_with_strategy G' p P' \<sigma>2" proof-
            have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def using P(5) path_conforms_with_strategy_drop by blast
            hence "path_conforms_with_strategy p P' \<sigma>2" using path_conforms_with_strategy_irrelevant_updates `lset P' \<subseteq> V'` \<sigma>_\<sigma>2 by blast
            thus ?thesis using subgame_path_conforms_with_strategy `lset P' \<subseteq> V'` `V' \<inter> V \<noteq> {}` `V' \<subseteq> V` G'_def by blast
          qed
          moreover have "P' $ 0 = lhd P'" using `\<not>lnull P'` lnth_0_conv_lhd by blast
          moreover have "ParityGame.winning_strategy G' p \<sigma>2 (lhd P')"
            using `lset P' \<subseteq> V'` `\<not>lnull P'` \<sigma>2(2)[of "lhd P'"] `V\<^bsub>G'\<^esub> = V'` llist.set_sel(1) by blast
          moreover have "ParityGame G'" using `lhd P' \<in> V'` G'_ParityGame `V\<^bsub>G'\<^esub> = V'` by blast
          ultimately have "ParityGame.winning_path G' p P'" using ParityGame.winning_strategy_def[OF `ParityGame G'`] `\<not>lnull P'` by blast
          moreover have "ParityGame G" by unfold_locales
          moreover have "ParityGame.VV G' p** \<subseteq> VV p**" unfolding G'_def using subgame_VV by simp
          ultimately have "winning_path p P'" using ParityGame.winning_path_supergame[OF `ParityGame G'`, of p P' G] `\<omega>\<^bsub>G'\<^esub> = \<omega>` by blast
          thus ?thesis using P'_def `\<not>lfinite P` winning_path_drop_add[of P p n] P(3) infinite_small_llength by blast
        next
          assume "\<not>(\<exists>n. lset (ldropn n P) \<subseteq> V')"
          (* P visits K infinitely often. *)
          hence *: "\<And>n. \<not>lset (ldropn n P) \<subseteq> V'" by blast
          have *: "\<And>n. \<exists>k \<ge> n. P $ k \<notin> V'" proof-
            fix n
            obtain k where k: "ldropn n P $ k \<notin> V'" using * by (metis path_set_at subsetI)
            hence "P $ k + n \<notin> V'" using lnth_ldropn[of n k P] infinite_small_llength `\<not>lfinite P` by metis
            thus "\<exists>k \<ge> n. P $ k \<notin> V'" using le_add2 by blast
          qed
          have "\<And>n. \<exists>k \<ge> n. P $ k \<in> attractor p K" proof-
            fix n obtain k where "k \<ge> n" "P $ k \<notin> V'" using * by blast
            thus "\<exists>k \<ge> n. P $ k \<in> attractor p K" using `\<not>lfinite P` `lset P \<subseteq> V - W1`
              by (metis DiffI U_def V'_def llist_set_nth)
          qed
          moreover have "\<And>k. P $ k \<in> attractor p K \<Longrightarrow> \<exists>n \<ge> k. P $ n \<in> K" proof-
            fix k assume *: "P $ k \<in> attractor p K"
            def P' \<equiv> "ldropn k P"
            hence "P' $ 0 \<in> attractor p K" using * by (simp add: `\<not>lfinite P` infinite_small_llength)
            hence "strategy_attracts_via p \<sigma> (P' $ 0) (attractor p K) K" using strategy_attracts_def \<sigma>_attracts P'_def by blast
            moreover have "\<not>lnull P'" unfolding P'_def using `\<not>lfinite P` infinite_no_deadend lfinite_ldropn by blast
            moreover have "valid_path P'" unfolding P'_def using P(3) valid_path_drop by blast
            moreover have "maximal_path P'" unfolding P'_def using P(4) maximal_drop by blast
            moreover have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def using P(5) path_conforms_with_strategy_drop by blast
            ultimately obtain n where n: "P' $ n \<in> K" using strategy_attracts_via_def by blast
            hence "P $ n + k \<in> K" using P'_def lnth_ldropn[of k n P] infinite_small_llength `\<not>lfinite P` by metis
            thus "\<exists>n \<ge> k. P $ n \<in> K" using le_add2 by blast
          qed
          ultimately have *: "\<And>n. \<exists>k \<ge> n. P $ k \<in> K" by (meson dual_order.trans)
          hence *: "\<And>n. lset (ldropn n P) \<inter> K \<noteq> {}" proof-
            fix n
            obtain k where k: "k \<ge> n" "P $ k \<in> K" using * by blast
            have "ldropn n P $ k - n = P $ (k - n) + n" using k(1) lnth_ldropn[of n "k - n" P] infinite_small_llength `\<not>lfinite P` by blast
            hence "ldropn n P $ k - n \<in> K" using k by simp
            thus "lset (ldropn n P) \<inter> K \<noteq> {}" by (meson `\<not>lfinite P` disjoint_iff_not_equal lfinite_ldropn llist_nth_set)
          qed
          have "\<And>n. min_prio \<in> lset (ldropn n (lmap \<omega> P))" proof-
            fix n
            obtain v where v: "v \<in> lset (ldropn n P)" "v \<in> K" using * by blast
            have "\<omega> v = min_prio" using K_def v(2) by blast
            thus "min_prio \<in> lset (ldropn n (lmap \<omega> P))" using v(1) by auto
          qed
          hence "min_prio \<in> path_inf_priorities P" unfolding path_inf_priorities_def by blast
          moreover have "\<And>a. a \<in> path_inf_priorities P \<Longrightarrow> min_prio \<le> a" proof-
            fix a assume "a \<in> path_inf_priorities P"
            hence "a \<in> lset (ldropn 0 (lmap \<omega> P))" unfolding path_inf_priorities_def by blast
            hence "a \<in> \<omega> ` lset P" by simp
            then obtain v where "v \<in> lset P" "\<omega> v = a" by blast
            thus "min_prio \<le> a" unfolding min_prio_def using `lset P \<subseteq> V` priorities_finite by auto
          qed
          ultimately show ?thesis unfolding winning_path_def
            using `winning_priority p min_prio` `\<not>lfinite P` by blast
        qed
      }
      thus ?thesis unfolding winning_strategy_def by blast
    qed
    hence "\<forall>v \<in> V. \<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" using W1_def `strategy p \<sigma>` by blast
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" using `v \<in> V` by simp
  }
  moreover have "\<exists>p. winning_priority p (Min (\<omega> ` V))" by auto
  ultimately show ?thesis by blast
qed

theorem positional_strategy_exists:
  assumes "v \<in> V" "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
proof-
  have "ParityGame G" by unfold_locales
  with assms show ?thesis
    by (induct "card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>)" arbitrary: G v rule: nat_less_induct)
       (rule ParityGame.positional_strategy_induction_step, simp_all)
qed

end -- "context ParityGame"

end
