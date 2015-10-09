(* Introduces the concept of attracting strategies. *)
theory strategy_attracts
imports
  Main
  strategy
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
      by (metis LNil_eq_ltake_iff len1 len2 assms(1) co.enat.distinct(1) dual_order.strict_trans
                eSuc_enat ldropn_Suc_conv_ldropn lhd_ldropn lhd_ltake ltake_ltl ltl_simps(2) zero_enat_def)
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
  thus ?thesis using n not0_implies_Suc by blast
qed

lemma (in vmc_path) strategy_attracts_via_lset:
  assumes "strategy_attracts_via p \<sigma> v0 A W"
  shows "lset P \<inter> W \<noteq> {}"
    and "\<not>lset P \<subseteq> A - W"
  by (meson assms strategy_attracts_viaE DiffE lset_lnth disjoint_iff_not_equal in_lset_conv_lnth)+

lemma strategy_attracts_via_v0:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v0: "v0 \<in> V"
  shows "v0 \<in> A \<union> W"
proof-
  obtain P where "vmc_path G P v0 p \<sigma>" using strategy_conforming_path_exists_single assms by blast
  then interpret vmc_path G P v0 p \<sigma> .
  obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    using \<sigma>(2) strategy_attracts_via_def vmc_path by blast
  show ?thesis proof (cases "n = 0")
    case True thus ?thesis using n(2) by simp
  next
    case False
    hence "lhd (ltake (enat n) P) = lhd P" by (simp add: enat_0_iff(1))
    hence "v0 \<in> lset (ltake (enat n) P)"
      by (metis `n \<noteq> 0` P_not_null P_v0 enat_0_iff(1) llist.set_sel(1) ltake.disc(2))
    thus ?thesis using n(3) by blast
  qed
qed
corollary strategy_attracts_not_outside:
  "\<lbrakk> v0 \<in> V - A - W; strategy p \<sigma> \<rbrakk> \<Longrightarrow> \<not>strategy_attracts_via p \<sigma> v0 A W"
  using strategy_attracts_via_v0 by blast


lemma strategy_attracts_viaI:
  assumes "\<And>P. vmc_path G P v0 p \<sigma>
    \<Longrightarrow> \<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
  shows "strategy_attracts_via p \<sigma> v0 A W"
  unfolding strategy_attracts_via_def using assms by blast

lemma strategy_attracts_via_no_deadends:
  assumes "v \<in> V" "v \<in> A - W" "strategy_attracts_via p \<sigma> v A W"
  shows "\<not>deadend v"
proof
  assume "deadend v"
  def [simp]: P \<equiv> "LCons v LNil"
  interpret vmc_path G P v p \<sigma> proof
    show "valid_path P" using `v \<in> A - W` `v \<in> V` valid_path_base' by auto
    show "maximal_path P" using `deadend v` by (simp add: maximal_path.intros(2))
    show "path_conforms_with_strategy p P \<sigma>" by (simp add: path_conforms_LCons_LNil)
  qed simp_all
  have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
    using assms(3) strategy_attracts_viaE by blast
  moreover have "llength P = eSuc 0" by simp
  ultimately have "P $ 0 \<in> W" by (simp add: enat_0_iff(1))
  with `v \<in> A - W` show False by auto
qed

lemma attractor_strategy_on_extends:
  "\<lbrakk> strategy_attracts_via p \<sigma> v0 A W; A \<subseteq> A' \<rbrakk> \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A' W"
  unfolding strategy_attracts_via_def by blast

lemma strategy_attracts_via_trivial: "v0 \<in> W \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A W"
proof (rule strategy_attracts_viaI)
  fix P assume "v0 \<in> W" "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> by blast
  show "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"
    by (rule exI[of _ 0]) (simp add: `v0 \<in> W` lset_ltake)
qed

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
    using n enat_Suc_ltl[of n P'] P'.P_lnth_Suc lset_ltake_ltl[of n P'] by auto
qed

lemma strategy_attracts_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v: "v0 \<in> A - W" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 \<in> A \<union> W"
proof-
  have "v0\<rightarrow>\<sigma> v0" using \<sigma>(1)[unfolded strategy_def] v(2,3) by blast
  hence "strategy_attracts_via p \<sigma> (\<sigma> v0) A W"
    using strategy_attracts_via_successor \<sigma> v(1) by blast
  thus ?thesis using strategy_attracts_via_v0 `v0\<rightarrow>\<sigma> v0` \<sigma>(1) by blast
qed

lemma strategy_attracts_VVpstar:
  assumes "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and "v0 \<in> A - W" "v0 \<notin> VV p" "w0 \<in> V - A - W"
  shows "\<not>v0 \<rightarrow> w0"
  by (metis assms strategy_attracts_not_outside strategy_attracts_via_successor)

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
  using assms(1)[unfolded strategy_attracts_def] assms(2) strategy_attracts_via_lset(1)[of A W]
  by blast

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
  thus False using P(1,3) by auto
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
  then obtain P where P: "vmc2_path G P v p \<sigma> \<sigma>'"
    using `v\<rightarrow>w` strategy_conforming_path_exists \<sigma>(2) by blast
  then interpret vmc2_path G P v p \<sigma> \<sigma>' .
  have "\<not>deadend v" using `v\<rightarrow>w` by blast
  then interpret vmc2_path_no_deadend G P v p \<sigma> \<sigma>' by unfold_locales
  have "w = w0" using contra \<sigma>'_def v0_conforms comp.v0_conforms by (cases "v \<in> VV p") auto
  hence "\<not>(\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"
    using strategy_attracts_invalid_path[of P v w "ltl (ltl P)"] v(2) v(3) P_LCons' by simp
  thus False by (meson DiffE \<sigma>(1) strategy_attractsE v(2))
qed

lemma strategy_attracts_no_deadends:
  assumes "v \<in> V" "v \<in> A - W" "strategy_attracts p \<sigma> A W"
  shows "\<not>deadend v"
  using assms strategy_attracts_via_no_deadends unfolding strategy_attracts_def by blast

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
  ultimately have "P $ 0 \<in> A - W" by (meson DiffI P_len not_less0 lset_ltake)
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
    using ex_least_nat_le[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> A - W"] by blast
  hence n_min: "\<And>i. i < n \<Longrightarrow> P $ i \<in> A - W"
    using dual_order.strict_trans enat_ord_simps(2) by blast
  have "n \<noteq> 0" using `P $ 0 \<in> A - W` n(1) by meson
  then obtain n' where n': "Suc n' = n" using not0_implies_Suc by blast
  hence "P $ n' \<in> A - W" using n_min by blast
  moreover have "P $ n' \<rightarrow> P $ Suc n'" using P_valid n(1) n' valid_path_edges by blast
  moreover have "P $ Suc n' \<notin> A \<union> W" proof-
    have "P $ n \<notin> W" using contra n(1) n_min by (meson Diff_subset lset_ltake subsetCE)
    thus ?thesis using n(1) n' by blast
  qed
  ultimately have "P $ n' \<in> VV p \<and> \<sigma> (P $ n') \<noteq> P $ Suc n'"
    using strategy_attracts_does_not_leave[of p \<sigma> A W "P $ n'" "P $ Suc n'"]
          assms(1,2) by blast
  thus False
    using n(1) n' vmc_path_conforms `P $ n' \<in> A - W` by (metis override_on_apply_in)
qed

lemma strategy_attracts_trivial [simp]: "strategy_attracts p \<sigma> W W"
  by (simp add: strategy_attracts_def strategy_attracts_via_trivial)

(* If a \<sigma>-conforming path P hits an attractor A, it will visit W. *)
lemma (in vmc_path) attracted_path:
  assumes "W \<subseteq> V"
    and \<sigma>: "strategy_attracts p \<sigma> A W"
    and P_hits_A: "lset P \<inter> A \<noteq> {}"
  shows "lset P \<inter> W \<noteq> {}"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> A" using P_hits_A by (meson lset_intersect_lnth)
  def P' \<equiv> "ldropn n P"
  interpret vmc_path G P' "P $ n" p \<sigma> unfolding P'_def using vmc_path_ldropn n(1) by blast
  obtain m where "enat m < llength P'" "P' $ m \<in> W"
    using \<sigma> n(2) by (meson strategy_attractsE)
  hence "lset P' \<inter> W \<noteq> {}" by (meson disjoint_iff_not_equal in_lset_conv_lnth)
  thus ?thesis unfolding P'_def using in_lset_ldropnD[of _ n P] by blast
qed

(* If a path P hits an attractor A of the other player, the other player can force a visit of W. *)
lemma (in vmc_path) attracted_path_VVpstar:
  assumes "W \<subseteq> V"
    and \<sigma>: "strategy p \<sigma>"
    and \<sigma>': "strategy p** \<sigma>'" "strategy_attracts p** \<sigma>' A W"
    and P_hits_A: "lset P \<inter> A \<noteq> {}"
  shows "\<exists>P'. vmc_path G P v0 p \<sigma> \<and> lset P' \<inter> W \<noteq> {}"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> A" using P_hits_A by (meson lset_intersect_lnth)

  have "P $ n \<in> V" by (simp add: n(1) valid_path_finite_in_V')

  show ?thesis proof (cases)
    assume "enat (Suc n) = llength P"
    hence "deadend (P $ n)" using suc_n_deadend by blast
    hence "P $ n \<in> W" using strategy_attracts_no_deadends[OF `P $ n \<in> V` _ \<sigma>'(2)] n(2) by blast
    hence "lset P \<inter> W \<noteq> {}" using n(1) by (meson disjoint_iff_not_equal in_lset_conv_lnth)
    thus ?thesis using vmc_path by blast
  next
    assume "enat (Suc n) \<noteq> llength P"
    hence P_len: "enat (Suc n) < llength P"
      using n(1) P_ends_on_deadend P_maximal maximal_path_impl1 by blast
    obtain P'' where "vmc2_path G P'' (P $ n) p \<sigma> \<sigma>'"
      using strategy_conforming_path_exists `P $ n \<in> V` \<sigma> \<sigma>'(1) by blast
    then interpret P'': vmc2_path G P'' "P $ n" p \<sigma> \<sigma>' .
    def P2 \<equiv> "lappend (ltake (enat (Suc n)) P) (ltl P'')"
    then interpret P2:
      vmc_path G P2 v0 p \<sigma>
      using valid_maximal_conforming_lappend[of n P''] P_len local.P''.vmc_path by blast
 
    have "lset P2 \<inter> W \<noteq> {}" proof-
      have "ltake (enat (Suc n)) P $ n \<in> A" using n by (simp add: lnth_ltake)
      hence "lset P'' \<inter> W \<noteq> {}"
        using \<sigma>'(2) P''.comp.strategy_attracts_via_lset n strategy_attracts_def by blast
      moreover have "lset P'' \<subseteq> lset P2"
        unfolding P2_def
        using valid_maximal_conforming_lset_lappend[of n P''] valid_maximal_conforming_path_0
              P''.P_maximal P''.P_not_null P''.P_valid P''.vmc_path P_len by blast
      ultimately show ?thesis by blast
    qed
    thus ?thesis using vmc_path by blast
  qed
qed

end -- "context ParityGame"

end
