(* Theorems about attractor strategies. *)
theory attractor_strategy
imports
  Main
  parity_game merge_strategies
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

      have *: "v0 \<notin> S - W" using `v0 \<notin> S` by blast
      have "override_on (\<sigma>(v0 := w)) \<sigma> (S - W) = ?\<sigma>"
        by (rule ext) (metis * fun_upd_def override_on_def)
      hence "strategy_attracts p ?\<sigma> S W"
        using strategy_attracts_irrelevant_override[OF \<sigma>(2,1) `strategy p ?\<sigma>`] by simp
      hence "strategy_attracts_via p ?\<sigma> w S W" unfolding strategy_attracts_def using `w \<in> S` by blast
      then obtain n where n: "enat n < llength P''" "P'' $ n \<in> W" "lset (ltake (enat n) P'') \<subseteq> S"
        unfolding strategy_attracts_via_def using vmc_path by blast

      have "enat (Suc n) < llength P" using P''_def enat_ltl_Suc n(1) by blast
      moreover have "P $ Suc n \<in> W" using P''_def n(2) by (metis P_LCons' Ptl_LCons lnth_Suc_LCons)
      moreover have "lset (ltake (enat (Suc n)) P) \<subseteq> insert v0 S" proof-
        have "ltake (eSuc (enat n)) P = LCons v0 (ltake (enat n) P'')"
          unfolding P''_def by (metis P_LCons' Ptl_LCons ltake_eSuc_LCons)
        thus ?thesis using n(3) eSuc_enat by auto
      qed
      ultimately have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S"
        by blast
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

end -- "context ParityGame"

end
