(* Theorems about attractor strategies. *)
theory attractor_strategy
imports
  Main
  parity_game strategy attractor merge_strategies
begin

context ParityGame begin

lemma strategy_attracts_extends_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> S W"
    and v0: "v0 \<in> VV p" "v0 \<in> directly_attracted p S" "v0 \<notin> S"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
proof-
  from v0(1) v0(2) obtain w where "v0\<rightarrow>w" "w \<in> S" using directly_attracted_def by blast
  hence "\<not>deadend v0" using edges_are_in_V by blast
  from `w \<in> S` \<sigma>(2) have "strategy_attracts_via p \<sigma> w S W" unfolding strategy_attracts_def by blast
  let ?\<sigma> = "\<sigma>(v0 := w)" (* Extend \<sigma> to the new node. *)
  have "strategy p ?\<sigma>" using \<sigma>(1) `v0\<rightarrow>w` valid_strategy_updates by blast
  moreover have "strategy_attracts_via p ?\<sigma> v0 (insert v0 S) W" proof-
    { fix P
      assume P: "\<not>lnull P" "valid_path P" "maximal_path P"
        "path_conforms_with_strategy p P ?\<sigma>" "P $ 0 = v0"

      def [simp]: P'' \<equiv> "ltl P"
      have "\<not>lnull P''" proof-
        from P(1) have "enat 0 < llength P" using lnull_0_llength by blast
        moreover from P(5) `\<not>deadend v0` have "\<not>deadend (P $ 0)" by blast
        ultimately have "enat (Suc 0) < llength P" using P(3) maximal_path_impl1 by blast
        hence "enat 0 < llength P''" using enat_Suc_ltl P''_def by blast
        then show "\<not>lnull P''" by auto
      qed
      have "P'' $ 0 = w" proof-
        from P(1) P(5) have "P = LCons v0 P''" by (metis P''_def lnth_0 ltl_simps(2) not_lnull_conv)
        with P(4) `v0 \<in> VV p` `\<not>lnull P''` have "lhd P'' = ?\<sigma> v0" by (metis lhd_LCons_ltl path_conforms_with_strategy_start)
        thus "P'' $ 0 = w" using `\<not> lnull P''` lhd_conv_lnth by force
      qed
      from P(2) P(3) P(4) have P'': "valid_path P''" "maximal_path P''" "path_conforms_with_strategy p P'' ?\<sigma>"
        using valid_path_ltl maximal_ltl path_conforms_with_strategy_ltl by auto

      have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S" proof (cases)
        assume "v0 \<in> lset P'' \<and> ?\<sigma> v0 \<noteq> \<sigma> v0"

        with \<sigma>(1) `strategy p ?\<sigma>` `v0 \<in> VV p` P'' `\<not>lnull P''` `\<not>deadend v0`
          obtain P' n where
            P': "\<not>lnull P'" "valid_path P'" "maximal_path P'" "path_conforms_with_strategy p P' \<sigma>"
            and n_valid: "enat (Suc n) < llength P'" "enat (Suc n) < llength P''"
            and P'_P''_same_prefix: "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P''"
            and P''_n: "P'' $ n \<in> VV p" "\<not>deadend (P'' $ n)" "?\<sigma> (P'' $ n) \<noteq> \<sigma> (P'' $ n)"
          using path_conforms_with_strategy_update_path by blast

        from P''_n(3) have "P'' $ n = v0" by (meson fun_upd_apply)
        from `P'' $ 0 = w` P'_P''_same_prefix have "P' $ 0 = w" using ltake_lnth[of "enat (Suc n)" P' P'' 0] by simp

        with P' `strategy_attracts_via p \<sigma> w S W`
          obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> S"
          unfolding strategy_attracts_via_def by blast

        have "m \<le> n" proof (rule ccontr)
          assume "\<not>m \<le> n"
          hence "Suc n \<le> m" by presburger
          hence "enat (Suc n) \<le> enat m" by simp
          with m(3) have "lset (ltake (enat (Suc n)) P') \<subseteq> S" by (meson lprefix_lset' order_trans)
          with P'_P''_same_prefix have *: "lset (ltake (enat (Suc n)) P'') \<subseteq> S" by simp
          with n_valid(2) have "enat n < llength P''" using Suc_ile_eq le_less by blast
          hence "enat n < llength (ltake (enat (Suc n)) P'')" by simp
          with * have "P'' $ n \<in> S"
            using lset_lnth[of "ltake (enat (Suc n)) P''" S n]
            by (metis (no_types) lprefix_lnthD ltake_is_lprefix)
          with `P'' $ n = v0` `v0 \<notin> S` show False by blast
        qed
        with P'_P''_same_prefix have "P' $ m = P'' $ m" using ltake_lnth[of "enat (Suc n)" P' P'' m] by simp
        with m(2) have "P'' $ m \<in> W" by simp
        hence 1: "P $ Suc m \<in> W" by (simp add: P(1) lnth_ltl)

        from P'_P''_same_prefix `m \<le> n` m(3)
          have "lset (ltake (enat m) P'') \<subseteq> S"
          using ltake_eq_ltake_antimono by fastforce
        hence "lset (ltake (eSuc (enat m)) P) \<subseteq> insert v0 S"
          by (metis P''_def P(1) P(5) lnth_0 ltl_simps(2) lset_ltake_Suc not_lnull_conv)
        hence 2: "lset (ltake (enat (Suc m)) P) \<subseteq> insert v0 S" by (simp add: eSuc_enat)

        from `m \<le> n` n_valid(2) have "enat (Suc m) < llength P''"
          by (metis Suc_ile_eq dual_order.strict_iff_order dual_order.strict_trans enat_ord_simps(2))
        hence 3: "enat (Suc m) < llength P" using dual_order.strict_trans enat_ltl_Suc by force

        with 1 2 3 show "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S" by blast
      next
        assume "\<not>(v0 \<in> lset P'' \<and> ?\<sigma> v0 \<noteq> \<sigma> v0)"
        with P''(3)
          have "path_conforms_with_strategy p P'' \<sigma>"
          using path_conforms_with_strategy_irrelevant'[of p P'' \<sigma> v0 w] by auto
        with P'' `strategy_attracts_via p \<sigma> w S W` `P'' $ 0 = w` `\<not>lnull P''`
          have "\<exists>n. enat n < llength P'' \<and> P'' $ n \<in> W \<and> lset (ltake (enat n) P'') \<subseteq> S"
          unfolding strategy_attracts_via_def by auto
        with P(1) P(5)
          show ?thesis
          unfolding P''_def using lset_ltake_Suc' enat_ltl_Suc lnth_ltl by metis
      qed
    }
    thus ?thesis unfolding strategy_attracts_via_def by blast
  qed
  ultimately show ?thesis by blast
qed

lemma strategy_attracts_extends_VVpstar:
  assumes \<sigma>: "strategy_attracts p \<sigma> S W"
    and v0: "v0 \<notin> VV p" "v0 \<in> directly_attracted p S"
  shows "strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
proof-
  from v0(2) have "\<not>deadend v0" using directly_attracted_contains_no_deadends by blast
  from v0 have "\<forall>w. v0\<rightarrow>w \<longrightarrow> w \<in> S" by (simp add: directly_attracted_def)
  { fix P
    assume P: "\<not>lnull P" "valid_path P" "maximal_path P"
      "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
    def [simp]: P' \<equiv> "ltl P"
    from P(2) P(3) P(4) have ltl_P: "valid_path P'" "maximal_path P'" "path_conforms_with_strategy p P' \<sigma>"
      using valid_path_ltl maximal_ltl path_conforms_with_strategy_ltl by auto
    moreover have "\<not>lnull P'" proof-
      from P(1) have "enat 0 < llength P" using lnull_0_llength by blast
      moreover from P(5) `\<not>deadend v0` have "\<not>deadend (P $ 0)" by blast
      ultimately have "enat (Suc 0) < llength P" using P(3) maximal_path_impl1 by blast
      hence "enat 0 < llength P'" using enat_Suc_ltl P'_def by blast
      thus ?thesis by auto
    qed
    moreover have "P' $ 0 \<in> S" proof-
      from `\<not>lnull P'` ltl_P P(1) P(2) have "P $ 0 \<rightarrow> P' $ 0" by (metis P'_def lhd_LCons_ltl lnth_0_conv_lhd valid_path_edges')
      with P(5) `\<forall>w. v0\<rightarrow>w \<longrightarrow> w \<in> S` show ?thesis by blast
    qed
    ultimately have "\<exists>n. enat n < llength P' \<and> P' $ n \<in> W \<and> lset (ltake (enat n) P') \<subseteq> S"
      using \<sigma> unfolding strategy_attracts_def strategy_attracts_via_def by blast
    with P(1) P(5) have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S"
      unfolding P'_def using lset_ltake_Suc' enat_ltl_Suc lnth_ltl by metis
  }
  thus ?thesis unfolding strategy_attracts_via_def by blast
qed

theorem attractor_has_strategy_single:
  assumes "W \<subseteq> V"
    and v0_def: "v0 \<in> attractor p W" (is "_ \<in> ?A")
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 ?A W"
using v0_def proof (induct arbitrary: v0 rule: attractor_set_induction)
  case base thus ?case using `W \<subseteq> V` .
next
  case (step S)
  have "v0 \<in> W \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 {} W"
    using strategy_attracts_via_trivial valid_arbitrary_strategy by blast
  moreover {
    assume *: "v0 \<in> directly_attracted p S" "v0 \<notin> S"
    from assms(1) step.hyps(1) step.hyps(2)
      have "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
      using merge_attractor_strategies by auto
    with *
      have "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
      using strategy_attracts_extends_VVp strategy_attracts_extends_VVpstar by blast
  }
  ultimately show ?case
    using step.prems step.hyps(2)
    attractor_strategy_on_extends[of p _ v0 "insert v0 S" W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "S" W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "{}" W "W \<union> S \<union> directly_attracted p S"]
    by blast
next
  case (union M)
  hence "\<exists>S. S \<in> M \<and> v0 \<in> S" by blast
  thus ?case by (meson Union_upper attractor_strategy_on_extends union.hyps)
qed

corollary attractor_has_strategy:
  assumes "W \<subseteq> V"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> (attractor p W) W"
proof-
  let ?A = "attractor p W"
  from `W \<subseteq> V`
    have "?A \<subseteq> V"
    by (simp add: attractor_is_bounded_by_V)
  moreover from `W \<subseteq> V`
    have "\<And>v. v \<in> ?A \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v ?A W"
    using attractor_has_strategy_single by blast
  ultimately show ?thesis using merge_attractor_strategies `W \<subseteq> V` by blast
qed

(* If A is the p-attractor of a set W, then p** has a strategy on V - A avoiding A. *)
theorem attractor_has_outside_strategy:
  fixes W p
  defines "A \<equiv> attractor p** W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_avoids p \<sigma> (V - A) A"
proof (intro exI conjI)
  (*  \<sigma>' simply chooses an arbitrary node not in A as the successor. *)
  def \<sigma>' \<equiv> "\<lambda>v. SOME w. w \<notin> A \<and> v\<rightarrow>w"
  def \<sigma> \<equiv> "override_on \<sigma>_arbitrary \<sigma>' (V - A)"
  (* We need to show that \<sigma> is well-defined.  This means we have to show that \<sigma> always applies
  the SOME quantifier to a non-empty set (for the nodes that matter). *)
  {
    fix v assume v: "v \<in> V - A" "v \<in> VV p" "\<not>deadend v"
    have "\<exists>w. w \<notin> A \<and> v\<rightarrow>w" proof (rule ccontr)
      assume "\<not>(\<exists>w. w \<notin> A \<and> v\<rightarrow>w)"
      hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p** W" using A_def by blast
      hence "v \<in> attractor p** W" using v A_def attractor_set_VVpstar by auto
      thus False using v A_def by blast
    qed
    with v(1) have "\<sigma>' v \<notin> A" "v\<rightarrow>\<sigma>' v" unfolding \<sigma>'_def using someI_ex[of "\<lambda>w. w \<notin> A \<and> v\<rightarrow>w"] by auto
  } note \<sigma>'_correct = this

  from \<sigma>'_correct(2)
    show "strategy p \<sigma>"
    unfolding \<sigma>_def using valid_strategy_updates_set valid_arbitrary_strategy by blast

  show "strategy_avoids p \<sigma> (V - A) A" proof (cases "V - A = {}", simp del: Diff_eq_empty_iff)
    case False
    {
      fix P v
      have "v \<in> lset P \<Longrightarrow> \<not>lnull P \<and> valid_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 \<in> V - A \<longrightarrow> v \<notin> A"
      proof (induct rule: llist_set_induct, simp add: lnth_0_conv_lhd)
        case (step P w)
        show ?case proof (intro impI, elim conjE, cases "lnull (ltl P)")
          case True
          thus "w \<notin> A" using lset_lnull step.hyps(2) by fastforce
        next
          case False
          assume P: "valid_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 \<in> V - A"
          from `\<not>lnull (ltl P)` obtain v u P' where u: "P = LCons v (LCons u P')" by (metis lhd_LCons_ltl step.hyps(1))
          with P(1) have "\<not>deadend v" using edges_are_in_V valid_path_edges' by blast
          from P(3) u have "v \<in> V - A" by simp
          have "u \<notin> A" proof (cases)
            assume "v \<in> VV p"
            with u P(2)
              have "path_conforms_with_strategy p (LCons v (LCons u P')) \<sigma>" by blast
            with `v \<in> VV p`
              have "\<sigma> v = u" using path_conforms_with_strategy_start by blast
            from `v \<in> VV p` `\<not>deadend v` `v \<in> V - A`
              have "\<sigma>' v \<notin> A" using \<sigma>'_correct(1) by blast
            with \<sigma>_def `\<sigma> v = u` `v \<in> V - A`  
              show "u \<notin> A" by auto
          next
            assume "v \<notin> VV p"
            { assume "u \<in> A"
              from `v \<notin> VV p` `v \<in> V - A`
                have "v \<in> VV p**" by auto
              moreover from `u \<in> A` u P(1)
                have "\<exists>w. v\<rightarrow>w \<and> w \<in> A" using valid_path_edges' by blast
              ultimately
                have "v \<in> directly_attracted p** A"
                using `\<not>deadend v` `v \<in> V - A` unfolding directly_attracted_def by auto
              with `v \<in> V - A` assms
                have False unfolding A_def using attractor_unfolding by fastforce
            }
            thus "u \<notin> A" by blast
          qed
          with P(1) u have "u \<in> V - A" by (metis DiffI in_mono llist.set_intros(1) ltl_simps(2) valid_path_in_V valid_path_ltl)
          with u have "ltl P $ 0 \<in> V - A" by simp
          with `\<not>lnull (ltl P)` P(1) P(2) step.hyps(3)
            show "w \<notin> A" using valid_path_ltl path_conforms_with_strategy_ltl by blast
        qed
      qed
    }
    thus ?thesis unfolding strategy_avoids_def by blast
  qed
qed

end -- "context ParityGame"

(* ML_val {*
(*proof body with digest*)
val body = Proofterm.strip_thm (Thm.proof_body_of @{thm obtain_min});
(*proof term only*)
val prf = Proofterm.proof_of body;
Pretty.writeln (Proof_Syntax.pretty_proof @{context} prf);
(*all theorems used in the graph of nested proofs*)
val all_thms =
Proofterm.fold_body_thms
(fn (name, _, _) => insert (op =) name) [body] [];
*} *)

end
