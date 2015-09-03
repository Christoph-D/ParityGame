(* Introduces the concept of attracting strategies. *)
theory strategy_attracts
imports
  Main
  parity_game strategy
begin

context ParityGame begin

(* All \<sigma>-paths starting from v0 visit W and until then they stay in A. *)
definition strategy_attracts_via :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_via p \<sigma> v0 A W \<equiv> \<forall>P.
      \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0
    \<longrightarrow> (\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"

(* All \<sigma>-paths starting from A visit W and until then they stay in A. *)
definition strategy_attracts :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts p \<sigma> A W \<equiv> \<forall>v0 \<in> A. strategy_attracts_via p \<sigma> v0 A W"

(* All \<sigma>-paths starting from A never visit W. *)
(* "\<exists>\<sigma>. strategy_avoids p \<sigma> A (V - A)" = A is a p-trap. *)
definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv> (\<forall>P.
      \<not>lnull P \<and> valid_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 \<in> A
    \<longrightarrow> lset P \<inter> W = {})"

(* strategy_attracts *)

lemma strategy_attracts_trivial [simp]: "strategy_attracts p \<sigma> W W"
  unfolding strategy_attracts_def strategy_attracts_via_def using lnull_0_llength zero_enat_def by fastforce

lemma strategy_attracts_empty [simp]: "strategy_attracts p \<sigma> {} W"
  unfolding strategy_attracts_def by simp

lemma strategy_attracts_invalid_path:
  assumes P: "P = LCons v (LCons w P')" "v \<in> A - W" "w \<notin> A \<union> W"
  shows "\<not>(\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)" (is "\<not>?A")
proof
  assume ?A
  then obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A" by blast
  have "n \<noteq> 0" using `v \<in> A - W` n(2) P(1) DiffD2 by force
  moreover have "n \<noteq> Suc 0" using `w \<notin> A \<union> W` n(2) P(1) by auto
  ultimately have "Suc (Suc 0) \<le> n" by presburger
  hence "lset (ltake (enat (Suc (Suc 0))) P) \<subseteq> A" using n(3)
    by (meson contra_subsetD enat_ord_simps(1) lprefix_lset' lset_lnth lset_subset)
  moreover have "enat (Suc 0) < llength (ltake (eSuc (eSuc 0)) P)" proof-
    have *: "enat (Suc (Suc 0)) < llength P"
      using `Suc (Suc 0) \<le> n` n(1) by (meson enat_ord_simps(2) le_less_linear less_le_trans neq_iff)
    have "llength (ltake (enat (Suc (Suc 0))) P) = min (enat (Suc (Suc 0))) (llength P)" by simp
    hence "llength (ltake (enat (Suc (Suc 0))) P) = enat (Suc (Suc 0))" using * by (simp add: min_absorb1)
    thus ?thesis by (simp add: eSuc_enat zero_enat_def)
  qed
  ultimately have "ltake (enat (Suc (Suc 0))) P $ Suc 0 \<in> A" by (simp add: lset_lnth)
  hence "P $ Suc 0 \<in> A" by (simp add: lnth_ltake)
  thus False using P(1) P(3) by auto
qed
lemma strategy_attracts_irrelevant_override:
  assumes "strategy_attracts p \<sigma> A W" "strategy p \<sigma>" "strategy p \<sigma>'"
  shows "strategy_attracts p (override_on \<sigma>' \<sigma> (A - W)) A W"
proof-
  let ?\<sigma> = "override_on \<sigma>' \<sigma> (A - W)"
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P ?\<sigma>" "P $ 0 \<in> A"
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A" sorry
  }
  thus ?thesis unfolding strategy_attracts_def strategy_attracts_via_def by blast
qed

lemma strategy_attracts_irrelevant:
  assumes "strategy_attracts p \<sigma> A W" "v \<notin> A" "v\<rightarrow>w" "strategy p \<sigma>"
  shows "strategy_attracts p (\<sigma>(v := w)) A W" proof-
  let ?\<sigma> = "\<sigma>(v := w)"
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P (\<sigma>(v := w))" "P $ 0 \<in> A"
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A" proof (cases)
      assume v: "v \<in> lset P \<and> v \<in> VV p \<and> \<not>deadend v \<and> ?\<sigma> v \<noteq> \<sigma> v"

      have "strategy p ?\<sigma>" by (simp add: assms(3) assms(4) valid_strategy_updates)
      with v P assms(4) obtain P' n where P': "\<not>lnull P'"
        "valid_path P'" "maximal_path P'" "path_conforms_with_strategy p P' \<sigma>"
        "enat (Suc n) < llength P'"
        "enat (Suc n) < llength P"
        and prefix: "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P"
        and n: "P $ n \<in> VV p" "\<not>deadend (P $ n)" "?\<sigma> (P $ n) \<noteq> \<sigma> (P $ n)"
          using path_conforms_with_strategy_update_path[of p ?\<sigma> \<sigma> P v] by blast
      hence "P' $ 0 = P $ 0" using ltake_lnth by fastforce
      with P' obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> A"
        by (metis P(5) assms(1) strategy_attracts_def strategy_attracts_via_def)

      have "m \<le> n" proof (rule ccontr)
        assume "\<not>m \<le> n"
        have "P $ n \<in> A" proof-
          from `\<not>m \<le> n` have "path_prefix (ltake (enat (Suc n)) P') (ltake (enat m) P')" by simp
          with m(3) have "lset (ltake (enat (Suc n)) P') \<subseteq> A" using lprefix_lsetD by blast
          with prefix have *: "lset (ltake (enat (Suc n)) P) \<subseteq> A" by simp
          moreover have "llength (ltake (enat (Suc n)) P) = min (enat (Suc n)) (llength P)" using llength_ltake by blast
          ultimately have "ltake (enat (Suc n)) P $ n \<in> A" using P'(6) by (simp add: lset_lnth min.absorb1)
          thus ?thesis by (simp add: lnth_ltake)
        qed
        moreover with n(3) have "P $ n = v" by (meson fun_upd_apply)
        ultimately show False using `v \<notin> A` by blast
      qed

      have "lset (ltake (enat m) P) \<subseteq> A" proof-
        from `m \<le> n` prefix have "ltake (enat m) P' = ltake (enat m) P" by (meson enat_ord_simps(1) le_imp_less_Suc less_imp_le_nat ltake_eq_ltake_antimono)
        with m(3) show ?thesis by simp
      qed
      moreover from `m \<le> n` P'(6) have "enat m < llength P"
        using dual_order.strict_trans by fastforce
      moreover have "P $ m \<in> W" proof-
        from `m \<le> n` have "enat m < enat (Suc n)" by simp
        with prefix have "P' $ m = P $ m" using ltake_lnth by blast
        with m(2) show ?thesis by simp
      qed
      ultimately show ?thesis using m(3) by blast
    next
      assume "\<not>(v \<in> lset P \<and> v \<in> VV p \<and> \<not>deadend v \<and> ?\<sigma> v \<noteq> \<sigma> v)"
      moreover from P(2) P(4)
        have "v \<notin> lset P \<or> v \<notin> VV p \<or> deadend v \<Longrightarrow> path_conforms_with_strategy p P \<sigma>"
          using path_conforms_with_strategy_irrelevant' path_conforms_with_strategy_irrelevant_deadend' by blast
      moreover from P(4)
        have "?\<sigma> v = \<sigma> v \<Longrightarrow> path_conforms_with_strategy p P \<sigma>" by simp
      ultimately have "path_conforms_with_strategy p P \<sigma>" by blast
      thus ?thesis
        using P(1) P(2) P(3) P(5) assms(1) strategy_attracts_def strategy_attracts_via_def by auto
    qed
  }
  thus ?thesis unfolding strategy_attracts_def strategy_attracts_via_def by blast
qed

(* strategy_avoids *)

lemma strategy_avoids_trivial [simp]: "strategy_avoids p \<sigma> {} W"
  unfolding strategy_avoids_def by simp

(* strategy_attracts_via *)

lemma attractor_strategy_on_extends: "\<lbrakk> strategy_attracts_via p \<sigma> v0 A W; A \<subseteq> A' \<rbrakk> \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A' W"
  unfolding strategy_attracts_via_def by blast

lemma strategy_attracts_via_trivial: "v0 \<in> W \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A W"
  unfolding strategy_attracts_via_def using zero_enat_def by (intro allI impI exI[of _ 0]) auto

lemma strategy_attracts_via_successor:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v0: "v0 \<in> A - W"
    and w0: "v0\<rightarrow>w0" "v0 \<in> VV p \<Longrightarrow> \<sigma> v0 = w0"
  shows "strategy_attracts_via p \<sigma> w0 A W"
proof-
  {
    fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = w0"
    then obtain Ps where Ps: "P = LCons w0 Ps" by (metis lnth_0 not_lnull_conv)
    def [simp]: P' \<equiv> "LCons v0 P"
    have "\<not>lnull P'" "P' $ 0 = v0" by simp_all
    moreover have "valid_path P'" unfolding P'_def using P(1) P(2) `v0\<rightarrow>w0` Ps valid_path_cons' by auto
    moreover have "maximal_path P'" unfolding P'_def by (simp add: P(1) P(3) maximal_path.intros(3))
    moreover have "path_conforms_with_strategy p P' \<sigma>"
      unfolding P'_def using w0(2) P(4) Ps path_conforms_VVp path_conforms_VVpstar by blast
    ultimately obtain n where n: "enat n < llength P'" "P' $ n \<in> W" "lset (ltake (enat n) P') \<subseteq> A"
      using \<sigma>(2) unfolding strategy_attracts_via_def by blast
    have "n \<noteq> 0" by (metis DiffD2 `P' $ 0 = v0` n(2) v0(1))
    then obtain n' where n': "Suc n' = n" by (metis nat.exhaust)
    have "enat n' < llength P" using n(1) n' unfolding P'_def by (metis ldropn_Suc_LCons ldropn_Suc_conv_ldropn ldropn_eq_LConsD)
    moreover have "P $ n' \<in> W" using n(2) n' unfolding P'_def by auto
    moreover have "lset (ltake (enat n') P) \<subseteq> A" proof-
      have "ltake (eSuc (enat n')) P' = LCons v0 (ltake (enat n') P)" using n(3) unfolding P'_def by simp
      hence "ltake (enat n) P' = LCons v0 (ltake (enat n') P)" using n' by (simp add: eSuc_enat)
      hence "lset (ltake (enat n') P) \<subseteq> lset (ltake (enat n) P')" by (simp add: subsetI)
      thus ?thesis using n(3) by blast
    qed
    ultimately have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A" by blast
  }
  thus ?thesis unfolding strategy_attracts_via_def by blast
qed

lemma strategy_attracts_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 S W"
    and v: "v0 \<in> S - W" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 \<in> S \<union> W"
proof-
  obtain P where P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
    using assms strategy_conforming_path_exists_single by blast
  have "enat (Suc 0) < llength P" using v(3) P(1) P(3) P(5) lnull_0_llength maximal_path_impl1 by blast
  hence "\<sigma> v0 = P $ Suc 0" using path_conforms_with_strategy_conforms[of P p \<sigma> 0] P(2) P(4) P(5) v(2) by fastforce
  moreover have "P $ Suc 0 \<in> S \<union> W" proof-
    obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> S" using P \<sigma>(2) unfolding strategy_attracts_via_def by blast
    have "n \<noteq> 0" using DiffE P(5) n(2) v(1) by force
    {
      assume "P $ Suc 0 \<notin> W"
      hence "Suc 0 < n" using `n \<noteq> 0` n(2) Suc_lessI by blast
      hence "ltake (enat n) P $ Suc 0 = P $ Suc 0" by (simp add: lnth_ltake)
      moreover have "ltake (enat n) P $ Suc 0 \<in> S" proof-
        have "llength (ltake (enat n) P) = min (enat n) (llength P)" using llength_ltake by blast
        with n(1) have "enat n = llength (ltake (enat n) P)" by (simp add: min.strict_order_iff)
        with `Suc 0 < n` have "enat (Suc 0) < llength (ltake (enat n) P)" by auto
        with n(3) show ?thesis using lset_lnth by blast
      qed
      ultimately have "P $ Suc 0 \<in> S" by simp
    }
    thus ?thesis by blast
  qed
  ultimately show ?thesis by simp
qed

lemma strategy_attracts_not_outside:
  assumes "v0 \<in> V - S - W" "strategy p \<sigma>"
  shows "\<not>strategy_attracts_via p \<sigma> v0 S W"
proof-
  obtain P where P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
    using assms strategy_conforming_path_exists_single by blast
  {
    fix n assume n: "enat n < llength P" "P $ n \<in> W"
    hence "n \<noteq> 0" using assms(1) DiffD2 P(5) by force
    moreover have "lhd P \<notin> S" using assms(1) P(5) by (simp add: P(1) lhd_conv_lnth)
    ultimately have "lhd (ltake (enat n) P) \<notin> S" "\<not>lnull (ltake (enat n) P)" by (simp_all add: P(1) enat_0_iff(1))
    hence "\<not>lset (ltake (enat n) P) \<subseteq> S" using llist.set_sel(1) by blast
  }
  with P show ?thesis unfolding strategy_attracts_via_def by blast
qed

lemma strategy_attracts_VVpstar:
  assumes "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 S W"
    and "v0 \<in> S - W" "v0 \<notin> VV p" "w0 \<in> V - S - W"
  shows "\<not>v0 \<rightarrow> w0"
  by (metis assms strategy_attracts_not_outside strategy_attracts_via_successor)

end -- "context ParityGame"

end
