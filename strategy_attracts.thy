(* Introduces the concept of attracting strategies. *)
theory strategy_attracts
imports
  Main
  parity_game strategy
begin

lemma (in vmc_path) valid_maximal_conforming_ldropn_lappend:
  assumes "enat (Suc n) < llength P" "vmc_path G P' (P $ n) p \<sigma>"
  shows "ldropn n (lappend (ltake (enat (Suc n)) P) (ltl P')) = P'" (is "ldropn _ ?P = _")
proof-
  interpret P': vmc_path G P' "P $ n" p \<sigma> using assms(2) .
  have len1: "llength (ltake (enat (Suc n)) P) = enat (Suc n)" using assms(1) llength_ltake' by blast
  hence len2: "enat n < llength (ltake (enat (Suc n)) P)" by simp
  hence "ldropn n ?P = lappend (ldropn n (ltake (enat (Suc n)) P)) (ltl P')"
    using ldropn_lappend[of n "ltake (enat (Suc n)) P" "ltl P'"] by simp
  moreover have "ldropn n (ltake (enat (Suc n)) P) = LCons (P $ n) LNil" proof-
    have "ldropn n (ltake (enat (Suc n)) P) = ltake (enat (Suc 0)) (ldropn n P)"
      by (simp add: ldropn_ltake)
    moreover hence "ltake (eSuc 0) (ldropn n P) = LCons (P $ n) LNil"
      by (metis LNil_eq_ltake_iff len1 len2 assms(1) co.enat.distinct(1) dual_order.strict_trans eSuc_enat ldropn_Suc_conv_ldropn lhd_ldropn lhd_ltake ltake_ltl ltl_simps(2) zero_enat_def)
    ultimately show ?thesis by (simp add: eSuc_enat zero_enat_def)
  qed
  ultimately show "ldropn n ?P = P'" using P'.P_LCons by simp
qed
corollary (in vmc_path) valid_maximal_conforming_lset_lappend:
  assumes "enat (Suc n) < llength P" "vmc_path G P' (P $ n) p \<sigma>"
  shows "lset P' \<subseteq> lset (lappend (ltake (enat (Suc n)) P) (ltl P'))"
  using assms valid_maximal_conforming_ldropn_lappend lset_ldropn_subset by metis

locale vmc2_path_no_deadend =
  comp: vmc_path_no_deadend G P v0 "p**" \<sigma>' + vmc_path_no_deadend G P v0 p \<sigma>
  for G P v0 p \<sigma> \<sigma>'

context ParityGame begin

(* All \<sigma>-paths starting from v0 visit W and until then they stay in A. *)
definition strategy_attracts_via :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_via p \<sigma> v0 A W \<equiv> \<forall>P. vmc_path G P v0 p \<sigma>
    \<longrightarrow> (\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"

lemma (in vmc_path) strategy_attracts_viaE:
  assumes "strategy_attracts_via p \<sigma> v0 A W"
  shows "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
  using strategy_attracts_via_def assms vmc_path by blast

lemma (in vmc_path) strategy_attracts_via_SucE:
  assumes "strategy_attracts_via p \<sigma> v0 A W" "v0 \<notin> W"
  shows "\<exists>n. enat (Suc n) < llength P \<and> P $ Suc n \<in> W \<and> lset (ltake (enat (Suc n)) P) \<subseteq> A"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    using strategy_attracts_viaE assms(1) by blast
  have "n \<noteq> 0" using assms(2) n(2) by (metis P_0)
  thus ?thesis using n nat.exhaust by metis
qed

lemma (in vmc_path) strategy_attracts_via_lset_negative:
  assumes "strategy_attracts_via p \<sigma> v0 A W"
  shows "\<not>lset P \<subseteq> A - W"
proof-
  obtain n where "enat n < llength P" "P $ n \<in> W" by (meson assms strategy_attracts_viaE)
  thus ?thesis by (meson DiffE lset_lnth)
qed

lemma (in vmc_path) strategy_attracts_via_lset:
  assumes "strategy_attracts_via p \<sigma> v0 A W"
  shows "lset P \<inter> W \<noteq> {}"
proof-
  obtain n where "enat n < llength P" "P $ n \<in> W" using strategy_attracts_viaE assms by blast
  thus ?thesis by (meson disjoint_iff_not_equal in_lset_conv_lnth)
qed

lemma strategy_attracts_viaI:
  assumes "\<And>P. vmc_path G P v0 p \<sigma>
    \<Longrightarrow> \<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
  shows "strategy_attracts_via p \<sigma> v0 A W"
  unfolding strategy_attracts_via_def using assms by blast

(* All \<sigma>-paths starting from A visit W and until then they stay in A. *)
definition strategy_attracts :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts p \<sigma> A W \<equiv> \<forall>v0 \<in> A. strategy_attracts_via p \<sigma> v0 A W"

lemma (in vmc_path) strategy_attractsE:
  assumes "strategy_attracts p \<sigma> A W" "v0 \<in> A"
  shows "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
  using assms strategy_attracts_viaE strategy_attracts_def by blast

lemma strategy_attractsI:
  assumes "\<And>P v. \<lbrakk> v \<in> A; vmc_path G P v p \<sigma> \<rbrakk>
    \<Longrightarrow> \<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
  shows "strategy_attracts p \<sigma> A W"
  unfolding strategy_attracts_def using strategy_attracts_viaI assms by blast

lemma (in vmc_path) strategy_attracts_lset:
  assumes "strategy_attracts p \<sigma> A W" "v0 \<in> A"
  shows "lset P \<inter> W \<noteq> {}"
  using assms(1)[unfolded strategy_attracts_def] assms(2)
        strategy_attracts_via_lset[of A W] by blast

(* All \<sigma>-paths starting from A never visit W. *)
(* "\<exists>\<sigma>. strategy_avoids p \<sigma> A (V - A)" = A is a p-trap. *)
definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv>
    (\<forall>P v0. v0 \<in> A \<and> vmc_path G P v0 p \<sigma> \<longrightarrow> lset P \<inter> W = {})"

(* strategy_attracts *)

lemma strategy_attracts_empty [simp]: "strategy_attracts p \<sigma> {} W"
  using strategy_attractsI by blast

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
    hence "llength (ltake (enat (Suc (Suc 0))) P) = enat (Suc (Suc 0))"
      using * by (simp add: min_absorb1)
    thus ?thesis by (simp add: eSuc_enat zero_enat_def)
  qed
  ultimately have "ltake (enat (Suc (Suc 0))) P $ Suc 0 \<in> A" by (simp add: lset_lnth)
  hence "P $ Suc 0 \<in> A" by (simp add: lnth_ltake)
  thus False using P(1) P(3) by auto
qed

(* If A is an attractor set of W and an edge leaves A without going through W, then v belongs to
   VV p and the attractor strategy \<sigma> avoids this edge.  All other cases give a contradiction. *)
lemma strategy_attracts_does_not_leave:
  assumes \<sigma>: "strategy_attracts p \<sigma> A W" "strategy p \<sigma>"
    and v: "v\<rightarrow>w" "v \<in> A - W" "w \<notin> A \<union> W"
  shows "v \<in> VV p \<and> \<sigma> v \<noteq> w"
proof (rule ccontr)
  assume contra: "\<not>(v \<in> VV p \<and> \<sigma> v \<noteq> w)"
  (* A strategy for p** which tries to take this edge. *)
  def \<sigma>' \<equiv> "\<sigma>_arbitrary(v := w)"
  hence "strategy p** \<sigma>'" using `v\<rightarrow>w` by (simp add: valid_strategy_updates)
  moreover have "v \<in> V" using `v\<rightarrow>w` edges_are_in_V by blast
  ultimately obtain P where P: "vmc2_path G P v p \<sigma> \<sigma>'"
    using strategy_conforming_path_exists \<sigma>(2) by blast
  then interpret vmc2_path G P v p \<sigma> \<sigma>' .
  have "\<not>deadend v" using `v\<rightarrow>w` edges_are_in_V by blast
  then interpret vmc2_path_no_deadend G P v p \<sigma> \<sigma>' by (unfold_locales)
  have "w = w0" using contra \<sigma>'_def v0_conforms comp.v0_conforms by (cases "v \<in> VV p") auto
  hence "\<not>(\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"
    using strategy_attracts_invalid_path[of P v w "ltl (ltl P)"] v(2) v(3) P_LCons' by simp
  thus False by (meson DiffE \<sigma>(1) strategy_attractsE v(2))
qed

lemma strategy_attracts_no_deadends:
  assumes \<sigma>: "strategy_attracts p \<sigma> A W" "strategy p \<sigma>"
    and v: "v0 \<in> V" "v0 \<in> A - W"
  shows "\<not>deadend v0"
proof
  assume "deadend v0"
  obtain P where "vmc_path G P v0 p \<sigma>"
    using v(1) \<sigma>(2) strategy_conforming_path_exists_single by blast
  then interpret vmc_path G P v0 p \<sigma> .
  have "lset P \<inter> W \<noteq> {}"
    using \<sigma>(1) v(2) strategy_attracts_via_lset unfolding strategy_attracts_def by auto
  moreover have "lset P = {v0}" using `deadend v0` P_deadend_v0_LCons by simp
  ultimately show False using v(2) by simp
qed

lemma strategy_attracts_irrelevant_override:
  assumes "strategy_attracts p \<sigma> A W" "strategy p \<sigma>" "strategy p \<sigma>'"
  shows "strategy_attracts p (override_on \<sigma>' \<sigma> (A - W)) A W"
proof (rule strategy_attractsI, rule ccontr)
  fix P v
  let ?\<sigma> = "override_on \<sigma>' \<sigma> (A - W)"
  assume "vmc_path G P v p ?\<sigma>"
  then interpret vmc_path G P v p ?\<sigma> .
  assume "v \<in> A"
  hence "P $ 0 \<in> A" using `v \<in> A` by simp
  moreover assume contra: "\<not>(\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"
  ultimately have "P $ 0 \<in> A - W" by (meson DiffI P_len not_less0 parity_game.lset_ltake)
  have "\<not>lset P \<subseteq> A - W" proof
    assume "lset P \<subseteq> A - W"
    hence "\<And>v. v \<in> lset P \<Longrightarrow> override_on \<sigma>' \<sigma> (A - W) v = \<sigma> v" by auto
    hence "path_conforms_with_strategy p P \<sigma>"
      using path_conforms_with_strategy_irrelevant_updates[OF P_conforms, of \<sigma>] by blast
    hence "vmc_path G P (P $ 0) p \<sigma>"
      using conforms_to_another_strategy P_0 by blast
    thus False
      using contra `P $ 0 \<in> A` assms(1)
      by (meson vmc_path.strategy_attractsE)
  qed
  hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> A - W" by (meson lset_subset)
  then obtain n where n: "enat n < llength P \<and> P $ n \<notin> A - W"
    "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> A - W)"
    using obtain_min[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> A - W"] by blast
  hence n_min: "\<And>i. i < n \<Longrightarrow> P $ i \<in> A - W"
    using dual_order.strict_trans enat_ord_simps(2) by blast
  have "n \<noteq> 0" using `P $ 0 \<in> A - W` n(1) by meson
  then obtain n' where n': "Suc n' = n" using nat.exhaust by metis
  hence "P $ n' \<in> A - W" using n_min by blast
  moreover have "P $ n' \<rightarrow> P $ Suc n'" using P_valid n(1) n' valid_path_edges by blast
  moreover have "P $ Suc n' \<notin> A \<union> W" proof-
    have "P $ n \<notin> W" using contra n(1) n_min by (meson Diff_subset parity_game.lset_ltake subsetCE)
    thus ?thesis using n(1) n' by blast
  qed
  ultimately have "P $ n' \<in> VV p \<and> \<sigma> (P $ n') \<noteq> P $ Suc n'"
    using strategy_attracts_does_not_leave[of p \<sigma> A W "P $ n'" "P $ Suc n'"]
          assms(1) assms(2) by blast
  thus False
    using P_valid P_conforms n(1) n' path_conforms_with_strategy_conforms `P $ n' \<in> A - W`
    by (metis override_on_apply_in)
qed

lemma strategy_attracts_irrelevant:
  assumes "strategy_attracts p \<sigma> A W" "v \<notin> A" "v\<rightarrow>w" "strategy p \<sigma>"
  shows "strategy_attracts p (\<sigma>(v := w)) A W"
proof (rule strategy_attractsI)
  fix P v0 assume "v0 \<in> A"
  let ?\<sigma> = "\<sigma>(v := w)"
  assume "vmc_path G P v0 p ?\<sigma>"
  then interpret vmc_path G P v0 p ?\<sigma> .
  show "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A" proof (cases)
    assume v: "v \<in> lset P \<and> v \<in> VV p \<and> \<not>deadend v \<and> ?\<sigma> v \<noteq> \<sigma> v"

    have "strategy p ?\<sigma>" by (simp add: assms(3) assms(4) valid_strategy_updates)
    with v assms(4) obtain P' n where P':
      "vmc_path G P' v0 p \<sigma>"
      "enat (Suc n) < llength P'"
      "enat (Suc n) < llength P"
      and prefix: "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P"
      and n: "P $ n \<in> VV p" "\<not>deadend (P $ n)" "?\<sigma> (P $ n) \<noteq> \<sigma> (P $ n)"
        using path_conforms_with_strategy_update_path by blast
    then interpret P': vmc_path G P' v0 p \<sigma> by blast
    have "P' $ 0 = P $ 0" by simp
    with P' obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> A"
      by (metis P'.strategy_attractsE `v0 \<in> A` assms(1))

    have "m \<le> n" proof (rule ccontr)
      assume "\<not>m \<le> n"
      have "P $ n \<in> A" proof-
        from `\<not>m \<le> n` have "path_prefix (ltake (enat (Suc n)) P') (ltake (enat m) P')" by simp
        with m(3) have "lset (ltake (enat (Suc n)) P') \<subseteq> A" using lprefix_lsetD by blast
        with prefix have *: "lset (ltake (enat (Suc n)) P) \<subseteq> A" by simp
        hence "ltake (enat (Suc n)) P $ n \<in> A"
          by (metis P'(3) enat_ord_simps(2) lessI llength_ltake' lset_lnth)
        thus ?thesis by (simp add: lnth_ltake)
      qed
      moreover with n(3) have "P $ n = v" by (meson fun_upd_apply)
      ultimately show False using `v \<notin> A` by blast
    qed

    have "lset (ltake (enat m) P) \<subseteq> A" proof-
      from `m \<le> n` prefix have "ltake (enat m) P' = ltake (enat m) P"
        by (meson enat_ord_simps(1) le_imp_less_Suc less_imp_le_nat ltake_eq_ltake_antimono)
      with m(3) show ?thesis by simp
    qed
    moreover from `m \<le> n` P'(3) have "enat m < llength P"
      using dual_order.strict_trans by (metis enat_ord_simps(2) le_imp_less_Suc)
    moreover have "P $ m \<in> W" proof-
      from `m \<le> n` have "enat m < enat (Suc n)" by simp
      with prefix have "P' $ m = P $ m" using ltake_lnth by blast
      with m(2) show ?thesis by simp
    qed
    ultimately show ?thesis using m(3) by blast
  next
    assume "\<not>(v \<in> lset P \<and> v \<in> VV p \<and> \<not>deadend v \<and> ?\<sigma> v \<noteq> \<sigma> v)"
    moreover from P_valid P_conforms
      have "v \<notin> lset P \<or> v \<notin> VV p \<or> deadend v \<Longrightarrow> path_conforms_with_strategy p P \<sigma>"
        using path_conforms_with_strategy_irrelevant' path_conforms_with_strategy_irrelevant_deadend'
        by blast
    moreover from P_conforms
      have "?\<sigma> v = \<sigma> v \<Longrightarrow> path_conforms_with_strategy p P \<sigma>" by simp
    ultimately have "path_conforms_with_strategy p P \<sigma>" by blast
    thus ?thesis
      using assms(1)
      by (meson vmc_path.strategy_attractsE `v0 \<in> A` conforms_to_another_strategy)
  qed
qed

(* strategy_avoids *)

lemma strategy_avoids_trivial [simp]: "strategy_avoids p \<sigma> {} W"
  unfolding strategy_avoids_def by simp

(* strategy_attracts_via *)

lemma attractor_strategy_on_extends:
  "\<lbrakk> strategy_attracts_via p \<sigma> v0 A W; A \<subseteq> A' \<rbrakk> \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A' W"
  unfolding strategy_attracts_via_def by blast

lemma strategy_attracts_via_trivial: "v0 \<in> W \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A W"
proof (rule strategy_attracts_viaI)
  fix P assume "v0 \<in> W" "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> by blast
  show "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
    by (rule exI[of _ 0]) (simp add: `v0 \<in> W` parity_game.lset_ltake)
qed

lemma strategy_attracts_trivial [simp]: "strategy_attracts p \<sigma> W W"
  by (simp add: strategy_attracts_def strategy_attracts_via_trivial)

lemma strategy_attracts_via_successor:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v0: "v0 \<in> A - W"
    and w0: "v0\<rightarrow>w0" "v0 \<in> VV p \<Longrightarrow> \<sigma> v0 = w0"
  shows "strategy_attracts_via p \<sigma> w0 A W"
proof (rule strategy_attracts_viaI)
  fix P assume "vmc_path G P w0 p \<sigma>"
  then interpret vmc_path G P w0 p \<sigma> .
  def [simp]: P' \<equiv> "LCons v0 P"
  then interpret P': vmc_path G P' v0 p \<sigma>
    using extension_valid_maximal_conforming w0 by blast
  obtain n where
    n: "enat (Suc n) < llength P'" "P' $ Suc n \<in> W" "lset (ltake (enat (Suc n)) P') \<subseteq> A"
    using \<sigma>(2) P'.strategy_attracts_via_SucE v0 by blast
  show "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
    apply (rule exI[of _ n])
    using n P'.P_len_Suc P'.P_lnth_Suc P'.P_lset by auto
qed

lemma strategy_attracts_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 S W"
    and v: "v0 \<in> S - W" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 \<in> S \<union> W"
proof-
  obtain P where "vmc_path G P v0 p \<sigma>" using assms strategy_conforming_path_exists_single by blast
  then interpret vmc_path G P v0 p \<sigma> .
  have "enat (Suc 0) < llength P" using v(3) lnull_0_llength maximal_path_impl1 by simp
  hence "\<sigma> v0 = P $ Suc 0" using vmc_path_conforms[of 0] v(2) by simp
  moreover have "P $ Suc 0 \<in> S \<union> W" proof-
    obtain n where n: "enat (Suc n) < llength P" "P $ Suc n \<in> W" "lset (ltake (enat (Suc n)) P) \<subseteq> S"
      using \<sigma>(2) strategy_attracts_via_SucE using v(1) by blast
    {
      assume "P $ Suc 0 \<notin> W"
      hence "Suc 0 < Suc n" using n(2) Suc_lessI neq0_conv by blast
      moreover have "ltake (enat (Suc n)) P $ Suc 0 \<in> S" proof-
        have "enat (Suc 0) < llength (ltake (enat (Suc n)) P)"
          by (metis `Suc 0 < Suc n` enat_ord_simps(2) llength_ltake' n(1))
        thus ?thesis using lset_lnth n(3) by blast
      qed
      ultimately have "P $ Suc 0 \<in> S" by (metis enat_ord_simps(2) lnth_ltake)
    }
    thus ?thesis by blast
  qed
  ultimately show ?thesis by simp
qed

lemma strategy_attracts_not_outside:
  assumes "v0 \<in> V - S - W" "strategy p \<sigma>"
  shows "\<not>strategy_attracts_via p \<sigma> v0 S W"
proof-
  obtain P where "vmc_path G P v0 p \<sigma>" using assms strategy_conforming_path_exists_single by blast
  then interpret vmc_path G P v0 p \<sigma> .
  {
    fix n assume n: "enat n < llength P" "P $ n \<in> W"
    hence "n \<noteq> 0" using assms(1) DiffD2 by force
    hence "lhd (ltake (enat n) P) \<notin> S" "\<not>lnull (ltake (enat n) P)"
      using assms(1) by (simp_all add: enat_0_iff(1))
    hence "\<not>lset (ltake (enat n) P) \<subseteq> S" using llist.set_sel(1) by blast
  }
  thus ?thesis using strategy_attracts_viaE by metis
qed

lemma strategy_attracts_VVpstar:
  assumes "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 S W"
    and "v0 \<in> S - W" "v0 \<notin> VV p" "w0 \<in> V - S - W"
  shows "\<not>v0 \<rightarrow> w0"
  by (metis assms strategy_attracts_not_outside strategy_attracts_via_successor)

lemma attracted_path:
  assumes "W \<subseteq> V"
    and \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> S W"
    and P: "\<not>lfinite P" "valid_path P" "path_conforms_with_strategy p P \<sigma>" "lset P \<inter> S \<noteq> {}"
  shows "lset P \<inter> W \<noteq> {}"
proof-
  obtain n where n: "P $ n \<in> S" using P(4) path_set_at[of _ P] by blast
  def P' \<equiv> "ldropn n P"
  have "\<not>lfinite P'" unfolding P'_def using P(1) by auto
  hence "\<not>lnull P'" by auto
  moreover have "valid_path P'" unfolding P'_def using P(2) valid_path_drop by blast
  moreover hence "maximal_path P'" using `\<not>lfinite P'` infinite_path_is_maximal by blast
  moreover have "path_conforms_with_strategy p P' \<sigma>"
    unfolding P'_def using P(3) path_conforms_with_strategy_drop by blast
  moreover have "P' $ 0 \<in> S" unfolding P'_def by (simp add: P(1) n infinite_small_llength)
  ultimately interpret vmc_path G P' "P' $ 0" p \<sigma>
    using valid_maximal_conforming_path_0 by blast
  obtain m where "enat m < llength P'" "P' $ m \<in> W"
    using \<sigma>(2) by (meson `P' $ 0 \<in> S` strategy_attractsE)
  hence "lset P' \<inter> W \<noteq> {}" by (meson disjoint_iff_not_equal in_lset_conv_lnth)
  thus ?thesis unfolding P'_def using in_lset_ldropnD[of _ n P] by blast
qed

lemma attracted_path_VVpstar:
  assumes "W \<subseteq> V"
    and \<sigma>: "strategy p \<sigma>"
    and \<sigma>': "strategy p** \<sigma>'" "strategy_attracts p** \<sigma>' S W"
    and P: "\<not>lfinite P" "valid_path P" "path_conforms_with_strategy p P \<sigma>" "lset P \<inter> S \<noteq> {}"
  shows "\<exists>P'. valid_path P' \<and> maximal_path P' \<and> path_conforms_with_strategy p P' \<sigma> \<and> P' $ 0 = P $ 0 \<and> lset P' \<inter> W \<noteq> {}"
proof-
  obtain n where n: "P $ n \<in> S" using P(4) path_set_at[of _ P] by (meson lset_intersect_lnth)
  interpret vmc_path G P "P $ 0" p \<sigma> proof
    show "\<not>lnull P" using P(1) by auto
    show "maximal_path P" using P(1) by (simp add: assms(6) infinite_path_is_maximal)
    show "lhd P = P $ 0" by (simp add: `\<not>lnull P` lnth_0_conv_lhd)
  qed (simp_all add: P(2) P(3))

  have "P $ n \<in> V" by (simp add: P(1) valid_path_in_V')
  obtain P'' where "vmc2_path G P'' (P $ n) p \<sigma> \<sigma>'"
    using strategy_conforming_path_exists `P $ n \<in> V` \<sigma> \<sigma>'(1) by blast
  then interpret P'': vmc2_path G P'' "P $ n" p \<sigma> \<sigma>' .

  def P2 \<equiv> "lappend (ltake (enat (Suc n)) P) (ltl P'')"
  then interpret P2:
    vmc_path G P2 "P $ 0" p \<sigma>
    using valid_maximal_conforming_lappend[of n P'']
    using P(1) local.P''.vmc_path by blast

  have "lset P2 \<inter> W \<noteq> {}" proof-
    have "ltake (enat (Suc n)) P $ n \<in> S" using n by (simp add: lnth_ltake)
    hence "lset P'' \<inter> W \<noteq> {}"
      using \<sigma>'(2) P''.comp.strategy_attracts_via_lset using n strategy_attracts_def by blast
    moreover have "lset P'' \<subseteq> lset P2"
      unfolding P2_def
      using valid_maximal_conforming_lset_lappend[of n P''] valid_maximal_conforming_path_0
            P''.P_maximal P''.P_not_null P''.P_valid P(1) P''.vmc_path by blast
    ultimately show ?thesis by blast
  qed
  thus ?thesis using P2.P_0 P2.P_conforms P2.P_maximal P2.P_valid by blast
qed

(* Winning strategies *)

lemma strategy_extends_VVp:
  assumes v0: "v0 \<in> VV p" "\<not>deadend v0"
  and \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
  shows "winning_strategy p \<sigma> (\<sigma> v0)"
proof (unfold winning_strategy_def, intro allI impI)
  fix P assume "vmc_path G P (\<sigma> v0) p \<sigma>"
  then interpret vmc_path G P "\<sigma> v0" p \<sigma> .
  have "v0\<rightarrow>\<sigma> v0" using v0 \<sigma>(1) strategy_def by blast
  hence "winning_path p (LCons v0 P)"
    using \<sigma>(2) extension_valid_maximal_conforming winning_strategy_def by blast
  thus "winning_path p P" using winning_path_ltl[of p "LCons v0 P"] by simp
qed

lemma strategy_extends_VVpstar:
  assumes v0: "v0 \<in> VV p**" "v0\<rightarrow>w0"
  and \<sigma>: "winning_strategy p \<sigma> v0"
  shows "winning_strategy p \<sigma> w0"
proof (unfold winning_strategy_def, intro allI impI)
  fix P assume "vmc_path G P w0 p \<sigma>"
  then interpret vmc_path G P w0 p \<sigma> .
  have "winning_path p (LCons v0 P)"
    using extension_valid_maximal_conforming VV_impl1 \<sigma> v0 winning_strategy_def
    by auto
  thus "winning_path p P" using winning_path_ltl[of p "LCons v0 P"] by auto
qed

end -- "context ParityGame"

end
