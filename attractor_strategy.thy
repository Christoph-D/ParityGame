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
  from v0(1,2) obtain w where "v0\<rightarrow>w" "w \<in> S" using directly_attracted_def by blast
  from `w \<in> S` \<sigma>(2) have "strategy_attracts_via p \<sigma> w S W" unfolding strategy_attracts_def by blast
  let ?\<sigma> = "\<sigma>(v0 := w)" (* Extend \<sigma> to the new node. *)
  have "strategy p ?\<sigma>" using \<sigma>(1) `v0\<rightarrow>w` valid_strategy_updates by blast
  moreover have "strategy_attracts_via p ?\<sigma> v0 (insert v0 S) W" proof-
    { fix P
      assume "vmc_path G P v0 p ?\<sigma>"
      then interpret vmc_path G P v0 p ?\<sigma> .
      have "\<not>deadend v0" using `v0\<rightarrow>w` by blast
      then interpret vmc_path_no_deadend G P v0 p ?\<sigma> by unfold_locales

      def [simp]: P'' \<equiv> "ltl P"
      have "lhd P'' = w" using v0(1) v0_conforms w0_def by auto
      hence "vmc_path G P'' w p ?\<sigma>" using vmc_path_ltl by (simp add: w0_def)
      then interpret vmc_path G P'' w p ?\<sigma> .

      have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S" proof (cases)
        assume "v0 \<in> lset P'' \<and> ?\<sigma> v0 \<noteq> \<sigma> v0"

        with \<sigma>(1) `strategy p ?\<sigma>` `v0 \<in> VV p` `\<not>deadend v0`
          obtain P' n where
            "vmc_path G P' w p \<sigma>"
            and n_valid: "enat (Suc n) < llength P'" "enat (Suc n) < llength P''"
            and P'_P''_same_prefix: "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P''"
            and P''_n: "P'' $ n \<in> VV p" "\<not>deadend (P'' $ n)" "?\<sigma> (P'' $ n) \<noteq> \<sigma> (P'' $ n)"
          using path_conforms_with_strategy_update_path by blast
        then interpret vmc_path G P' w p \<sigma> by blast

        have "P'' $ n = v0" using P''_n(3) by (meson fun_upd_apply)
        have "P' $ 0 = w" by simp

        obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> S"
          using `strategy_attracts_via p \<sigma> w S W` strategy_attracts_viaE by blast

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
        with P'_P''_same_prefix have "P' $ m = P'' $ m"
          using ltake_lnth[of "enat (Suc n)" P' P'' m] by simp
        with m(2) have "P'' $ m \<in> W" by simp
        hence 1: "P $ Suc m \<in> W" by (simp add: lnth_ltl)

        from P'_P''_same_prefix `m \<le> n` m(3)
          have "lset (ltake (enat m) P'') \<subseteq> S"
          using ltake_eq_ltake_antimono by fastforce
        hence 2: "lset (ltake (enat (Suc m)) P) \<subseteq> insert v0 S"
          unfolding P''_def using lset_ltake_Suc'[of P] by simp

        from `m \<le> n` n_valid(2) have "enat (Suc m) < llength P''"
          by (metis Suc_ile_eq dual_order.strict_iff_order dual_order.strict_trans enat_ord_simps(2))
        moreover have "llength P'' \<le> llength P"
          unfolding P''_def by (metis Coinductive_List.ltl_ldrop eq_refl lnull_ldrop lnull_ltlI)
        ultimately have 3: "enat (Suc m) < llength P" by simp

        with 1 2 3 show ?thesis by blast
      next
        assume "\<not>(v0 \<in> lset P'' \<and> ?\<sigma> v0 \<noteq> \<sigma> v0)"
        then interpret vmc_path G P'' w p \<sigma>
          using path_conforms_with_strategy_irrelevant'[of p P'' \<sigma> v0 w] P_conforms P_v0
          by unfold_locales fastforce
        have "\<exists>n. enat n < llength P'' \<and> P'' $ n \<in> W \<and> lset (ltake (enat n) P'') \<subseteq> S"
          using strategy_attracts_viaE[OF `strategy_attracts_via p \<sigma> w S W`] by metis
        thus ?thesis
          by (metis P''_def P_LCons' enat_ltl_Suc llist.disc(2) lnth_0 lnth_ltl lset_ltake_Suc')
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
  { fix P
    assume "vmc_path G P v0 p \<sigma>"
    then interpret vmc_path G P v0 p \<sigma> .
    have "\<not>deadend v0" using v0(2) directly_attracted_contains_no_deadends by blast
    then interpret vmc_path_no_deadend G P v0 p \<sigma> by unfold_locales
    interpret vmc_path G "ltl P" w0 p \<sigma> using vmc_path_ltl by blast
    have "\<exists>n. enat n < llength (ltl P) \<and> (ltl P) $ n \<in> W \<and> lset (ltake (enat n) (ltl P)) \<subseteq> S"
      using strategy_attractsE[OF \<sigma>] v0 directly_attracted_def by simp
    hence "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S"
      by (metis P_LCons' Ptl_LCons enat_ltl_Suc llist.discI(2) lnth_0 lnth_Suc_LCons lset_ltake_Suc')
  }
  thus ?thesis unfolding strategy_attracts_via_def by blast
qed

theorem attractor_has_strategy_single:
  assumes "W \<subseteq> V"
    and v0_def: "v0 \<in> attractor p W" (is "_ \<in> ?A")
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 ?A W"
using `W \<subseteq> V` v0_def proof (induct arbitrary: v0 rule: attractor_set_induction)
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
    attractor_strategy_on_extends[of p _ v0 "S"           W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "{}"          W "W \<union> S \<union> directly_attracted p S"]
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
  have "?A \<subseteq> V" by (simp add: `W \<subseteq> V` attractor_is_bounded_by_V)
  moreover
    have "\<And>v. v \<in> ?A \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v ?A W"
    using `W \<subseteq> V` attractor_has_strategy_single by blast
  ultimately show ?thesis using merge_attractor_strategies `W \<subseteq> V` by blast
qed

(* If A is the p-attractor of a set W, then p** has a strategy on V - A avoiding A.
   Note that this theorem is not required to prove positional_strategy_exists later. *)
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

  show "strategy p \<sigma>"
    unfolding \<sigma>_def using \<sigma>'_correct(2) valid_strategy_updates_set valid_arbitrary_strategy by blast

  show "strategy_avoids p \<sigma> (V - A) A" proof (cases "V - A = {}")
    case False
    {
      fix P v v0 assume v0: "v0 \<in> V - A" "vmc_path G P v0 p \<sigma>"
      then interpret vmc_path G P v0 p \<sigma> by blast
      have "v \<in> lset P \<Longrightarrow> v \<in> V - A" proof (insert v0, induct arbitrary: v0 rule: llist_set_induct)
        case (find P v0)
        interpret vmc_path G P v0 p \<sigma> using find.prems(2) .
        show ?case using P_v0 find.prems(1) by blast
      next
        case (step P v v0)
        interpret vmc_path G P v0 p \<sigma> using step.prems(2) .
        show ?case proof (cases "lnull (ltl P)")
          case True
          thus "v \<in> V - A" using lset_lnull step.hyps(2) by blast
        next
          case False
          then interpret vmc_path_no_deadend G P v0 p \<sigma> using P_no_deadend_v0 by unfold_locales
          have "w0 \<notin> A" proof (cases)
            assume "v0 \<in> VV p"
            moreover hence "\<sigma>' v0 \<notin> A" using \<sigma>'_correct(1) step.prems(1) v0_edge_w0 w0_V by blast
            ultimately show "w0 \<notin> A" using \<sigma>_def step.prems(1) v0_conforms by auto
          next
            assume "v0 \<notin> VV p"
            { assume "w0 \<in> A"
              have "v0 \<in> VV p**" using `v0 \<notin> VV p` `v0 \<in> V - A` by blast
              moreover have "v0 \<notin> VV p****" using `v0 \<notin> VV p` other_other_player[of p] by metis
              moreover have "\<exists>w. v0\<rightarrow>w \<and> w \<in> A" using `w0 \<in> A` using v0_edge_w0 by blast
              ultimately have "v0 \<in> directly_attracted p** A"
                unfolding directly_attracted_def
                using `\<not>deadend v0` `v0 \<in> V - A`
                by blast
              hence False
                unfolding A_def using `v0 \<in> V - A` assms attractor_unfolding[of "p**" W] by blast
            }
            thus "w0 \<notin> A" by blast
          qed
          thus "v \<in> V - A" using w0_V w0_def vmc_path_ltl w0_def step.hyps(3) by simp
        qed
      qed
    }
    thus ?thesis unfolding strategy_avoids_def by blast
  qed (simp del: Diff_eq_empty_iff)
qed

end -- "context ParityGame"

end
