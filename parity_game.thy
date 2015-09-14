theory parity_game
imports
  Main
  pigeon_hole_principle
  "Coinductive/Coinductive_List"
begin

lemma option_the_simp [simp]: "x = Some y \<Longrightarrow> the x = y" by simp
lemma option_the_simp2 [simp]: "x \<noteq> None \<Longrightarrow> \<exists>y. x = Some y" by simp
lemma obtain_min:
  assumes "\<exists>n :: nat. P n"
  obtains n where "P n" "\<And>i. i < n \<Longrightarrow> \<not>P i"
  using assms ex_least_nat_le by blast
lemma fun_iter_induct: "P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P (f x)) \<Longrightarrow> P ((f^^n) x)" by (induct n) simp_all
lemma llist_set_nth: "\<lbrakk> \<not>lfinite x; lset x \<subseteq> X \<rbrakk> \<Longrightarrow> lnth x i \<in> X" by (metis contra_subsetD inf_llist_lnth lset_inf_llist rangeI)
lemma enat_Suc_ltl: assumes "enat (Suc i) < llength xs" shows "enat i < llength (ltl xs)" proof-
  from assms have "eSuc (enat i) < llength xs" by (simp add: eSuc_enat)
  hence "enat i < epred (llength xs)" using eSuc_le_iff ileI1 by fastforce
  thus ?thesis by (simp add: epred_llength)
qed
lemma enat_ltl_Suc: "enat i < llength (ltl xs) \<Longrightarrow> enat (Suc i) < llength xs"
  by (metis assms eSuc_enat ldrop_ltl leD leI lnull_ldrop)
lemma lset_intersect_lnth: "lset xs \<inter> A \<noteq> {} \<Longrightarrow> \<exists>i. enat i < llength xs \<and> lnth xs i \<in> A"
  by (metis assms disjoint_iff_not_equal in_lset_conv_lnth)
lemma infinite_small_llength [intro]: "\<not>lfinite xs \<Longrightarrow> enat i < llength xs"
  using enat_iless lfinite_conv_llength_enat neq_iff by blast
lemma lnull_0_llength: "\<not>lnull xs \<Longrightarrow> enat 0 < llength xs"
  using zero_enat_def by auto
lemma ltake_lnth: "ltake n xs = ltake n ys \<Longrightarrow> enat m < n \<Longrightarrow> lnth xs m = lnth ys m"
  by (metis lnth_ltake)
lemma enat_0_lt_Suc [simp]: "0 < enat (Suc n)"
  by (simp add: enat_0_iff(1))
lemma lprefix_lset' [simp]: "n \<le> m \<Longrightarrow> lset (ltake n xs) \<subseteq> lset (ltake m xs)"
  by (simp add: lprefix_lsetD)
lemma lset_lnth: "lset xs \<subseteq> A \<Longrightarrow> enat n < llength xs \<Longrightarrow> lnth xs n \<in> A"
  by (meson contra_subsetD in_lset_conv_lnth)
lemma lset_ltake_Suc: "lset (ltake n xs) \<subseteq> A \<Longrightarrow> lset (ltake (eSuc n) (LCons x xs)) \<subseteq> insert x A"
  by auto
lemma lset_ltake_Suc':
  assumes "\<not>lnull xs" "lnth xs 0 = x" "lset (ltake (enat n) (ltl xs)) \<subseteq> A"
  shows "lset (ltake (enat (Suc n)) xs) \<subseteq> insert x A"
proof-
  from assms(3) have "lset (ltake (eSuc (enat n)) (LCons x (ltl xs))) \<subseteq> insert x A" using lset_ltake_Suc[of "enat n" "ltl xs" A x] by blast
  moreover from assms have "LCons x (ltl xs) = xs" by (metis lnth_0 ltl_simps(2) not_lnull_conv)
  ultimately show ?thesis by (simp add: eSuc_enat)
qed
lemma lnth_lprefix: "\<not>lnull xs \<Longrightarrow> lprefix xs ys \<Longrightarrow> lnth xs 0 = lnth ys 0"
  by (simp add: lnth_0_conv_lhd lprefix_lhdD lprefix_not_lnullD)
lemma lfinite_lset: "lfinite xs \<Longrightarrow> \<not>lnull xs \<Longrightarrow> llast xs \<in> lset xs" proof (induct rule: lfinite_induct, simp)
  case (LCons xs)
  show ?case proof (cases "lnull (ltl xs)")
    case True
    thus ?thesis by (metis LCons.prems lhd_LCons_ltl llast_LCons llist.set_sel(1))
  next
    case False
    hence "llast (ltl xs) \<in> lset (ltl xs)" using LCons.hyps(3) by blast
    hence "llast (ltl xs) \<in> lset xs" by (simp add: in_lset_ltlD)
    thus ?thesis by (metis False LCons.prems lhd_LCons_ltl llast_LCons2)
  qed
qed
lemma ltl_ldrop: "(\<And>xs. P xs \<Longrightarrow> P (ltl xs)) \<Longrightarrow> P xs \<Longrightarrow> P (ldropn n xs)"
  unfolding ldropn_def by (rule fun_iter_induct)
lemma lset_subset: "\<not>(lset xs \<subseteq> A) \<Longrightarrow> \<exists>n. enat n < llength xs \<and> lnth xs n \<notin> A"
  by (metis in_lset_conv_lnth subsetI)

lemma lset_ltake: "(\<And>i. i < n \<Longrightarrow> lnth xs i \<in> A) \<Longrightarrow> lset (ltake (enat n) xs) \<subseteq> A"
proof (induct n arbitrary: xs)
  case 0
  have "ltake (enat 0) xs = LNil" by (simp add: zero_enat_def)
  thus ?case by simp
next
  case (Suc n)
  show ?case proof (cases "xs = LNil", simp)
    assume "xs \<noteq> LNil"
    then obtain x xs' where xs: "xs = LCons x xs'" by (meson neq_LNil_conv)
    have "\<And>i. i < n \<Longrightarrow> lnth xs' i \<in> A" proof-
      fix i assume "i < n"
      hence "Suc i < Suc n" by simp
      hence "lnth xs (Suc i) \<in> A" using Suc.prems by presburger
      thus "lnth xs' i \<in> A" using xs by simp
    qed
    hence "lset (ltake (enat n) xs') \<subseteq> A" using Suc.hyps by blast
    moreover have "ltake (enat (Suc n)) xs = LCons x (ltake (enat n) xs')" using xs ltake_eSuc_LCons[of _ x xs'] by (metis (no_types) eSuc_enat)
    moreover have "x \<in> A" using Suc.prems xs by force
    ultimately show ?thesis by simp
  qed
qed

lemma llength_ltake': "enat n < llength xs \<Longrightarrow> llength (ltake (enat n) xs) = enat n"
  by (metis assms llength_ltake min.strict_order_iff)
lemma llast_ltake:
  assumes "enat (Suc n) < llength xs"
  shows "llast (ltake (enat (Suc n)) xs) = lnth xs n" (is "llast ?A = _")
  unfolding llast_def using llength_ltake'[OF assms] by (auto simp add: lnth_ltake)

(* 'a is the vertex type. *)
type_synonym 'a Edge = "'a \<times> 'a"
(* A path is a possibly infinite list of vertices. *)
type_synonym 'a Path = "'a llist"

notation lnth (infix "$" 61)

(* The set of nodes that occur infinitely often on a given path. *)
definition path_inf :: "'a Path \<Rightarrow> 'a set" where
  "path_inf P \<equiv> {v. \<forall>i. v \<in> lset (ldropn i P)}"

lemma LCons_suc_is_P2: "i \<noteq> 0 \<Longrightarrow> LCons v P $ i = P $ i - 1" by (simp add: lnth_LCons')
lemma infinite_no_deadend: "\<not>lfinite P \<Longrightarrow> \<not>lnull P" by auto
lemma ltl_inf: "\<not>lfinite P \<Longrightarrow> P $ Suc i = ltl P $ i" by (simp add: infinite_no_deadend lnth_ltl)
lemma path_set_at: "v \<in> lset P \<Longrightarrow> \<exists>n. P $ n = v" by (induct rule: llist.set_induct, meson lnth_0, meson lnth_Suc_LCons)
lemma lfinite_drop: "lfinite P \<Longrightarrow> \<exists>n. ldrop n P = LNil" by auto
lemma lfinite_drop_set: "lfinite P \<Longrightarrow> \<exists>n. v \<notin> lset (ldrop n P)" by (metis ldrop_inf lmember_code(1) lset_lmember)

(* abbreviation path_dom :: "'a Path \<Rightarrow> nat set" where "path_dom P \<equiv> {i. enat i < llength P}" *)

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

locale Digraph =
  fixes G (structure)
  assumes (* finite_vertex_set: "finite V"
    and *) non_empty_vertex_set: "V \<noteq> {}"
    and valid_edge_set: "E \<subseteq> V \<times> V"
begin
lemma Digraph [simp]: "Digraph G" by unfold_locales

lemma edges_are_in_V: "v\<rightarrow>w \<Longrightarrow> v \<in> V \<and> w \<in> V" using valid_edge_set by blast

abbreviation deadend :: "'a \<Rightarrow> bool" where "deadend v \<equiv> \<not>(\<exists>w \<in> V. v \<rightarrow> w)"
lemma deadend_no_edge: "\<lbrakk> \<not>P \<Longrightarrow> v\<rightarrow>w ; deadend v \<rbrakk> \<Longrightarrow> P" using edges_are_in_V by blast

coinductive valid_path :: "'a Path \<Rightarrow> bool" where
  valid_path_base: "valid_path LNil"
| valid_path_base': "v \<in> V \<Longrightarrow> valid_path (LCons v LNil)"
| valid_path_cons: "\<lbrakk> v \<in> V; w \<in> V; v\<rightarrow>w; valid_path Ps; \<not>lnull Ps; lhd Ps = w \<rbrakk> \<Longrightarrow> valid_path (LCons v Ps)"

inductive_simps valid_path_cons_simp: "valid_path (LCons x xs)"

lemma valid_path_cons': "\<lbrakk> v\<rightarrow>w; valid_path Ps; \<not>lnull Ps; lhd Ps = w \<rbrakk> \<Longrightarrow> valid_path (LCons v Ps)" using edges_are_in_V valid_path_cons by auto
lemma valid_path_ltl': "valid_path (LCons v Ps) \<Longrightarrow> valid_path Ps" using valid_path.simps by blast
lemma valid_path_ltl: "valid_path P \<Longrightarrow> valid_path (ltl P)" by (metis llist.exhaust_sel ltl_simps(1) valid_path_ltl')
lemma valid_path_drop: "valid_path P \<Longrightarrow> valid_path (ldropn n P)" by (simp add: valid_path_ltl ltl_ldrop)

lemma valid_path_in_V: assumes "valid_path P" shows "lset P \<subseteq> V" proof
  fix x assume "x \<in> lset P" thus "x \<in> V" using assms by (induct rule: llist.set_induct) (auto intro: valid_path.cases edges_are_in_V)
qed
lemma valid_path_in_V': "\<lbrakk> valid_path P; \<not>lfinite P \<rbrakk> \<Longrightarrow> P $ i \<in> V" by (simp add: llist_set_nth valid_path_in_V)
lemma valid_path_finite_in_V': "\<lbrakk> valid_path P; enat i < llength P \<rbrakk> \<Longrightarrow> P $ i \<in> V"
  by (metis (no_types, lifting) ldropn_Suc_conv_ldropn llist.distinct(1) llist.inject valid_path.cases valid_path_drop)

lemma valid_path_edges': "valid_path (LCons v (LCons w Ps)) \<Longrightarrow> v\<rightarrow>w" using valid_path.cases by fastforce
lemma valid_path_edges:
  assumes "valid_path P" "enat (Suc n) < llength P"
  shows "P $ n \<rightarrow> (P $ Suc n)"
proof-
  def P' \<equiv> "ldropn n P"
  have "enat n < llength P" using assms(2) enat_ord_simps(2) less_trans by blast
  hence "P' $ 0 = P $ n" by (simp add: P'_def)
  moreover have "P' $ Suc 0 = P $ Suc n" by (metis One_nat_def P'_def Suc_eq_plus1 add.commute assms(2) lnth_ldropn)
  ultimately have "\<exists>Ps. P' = LCons (P $ n) (LCons (P $ Suc n) Ps)" by (metis P'_def `enat n < llength P` assms(2) ldropn_Suc_conv_ldropn)
  moreover have "valid_path P'" by (simp add: P'_def assms(1) valid_path_drop)
  ultimately show ?thesis using valid_path_edges' by blast
qed

lemma valid_path_impl1: "valid_path P \<Longrightarrow> lset P \<subseteq> V \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w)"
  using valid_path_edges valid_path_in_V by blast
lemma valid_path_impl2: "\<lbrakk> lset P \<subseteq> V; \<And>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w \<rbrakk> \<Longrightarrow> valid_path P"
proof (coinduction arbitrary: P rule: valid_path.coinduct)
  case (valid_path P)
  { assume "\<not>P = LNil" "\<not>(\<exists>v. P = LCons v LNil \<and> v \<in> V)"
    hence "\<not>(\<exists>v. P = LCons v LNil)" using valid_path(1) by auto
    then obtain v Ps where v: "P = LCons v Ps" "\<not>lnull Ps" by (metis `P \<noteq> LNil` lnull_def not_lnull_conv)
    then obtain w Ps' where w: "Ps = LCons w Ps'" by (meson not_lnull_conv)
    hence "lhd Ps = w" by simp
    moreover have "v\<rightarrow>w" proof-
      have "P = LCons v (LCons w Ps')" by (simp add: v(1) w)
      hence "enat (Suc 0) < llength P" by (metis ldropn_0 ldropn_Suc_LCons ldropn_eq_LConsD)
      moreover have "P $ 0 = v \<and> P $ (Suc 0) = w" by (simp add: v w lnth_0_conv_lhd)
      ultimately show ?thesis using valid_path(2) by blast
    qed
    moreover hence "v \<in> V \<and> w \<in> V" using edges_are_in_V by blast
    moreover have "lset Ps \<subseteq> V" using v(1) valid_path(1) by auto
    moreover have "\<And>i v w. \<lbrakk> enat (Suc i) < llength Ps; Ps $ i = v; Ps $ Suc i = w \<rbrakk> \<Longrightarrow> v \<rightarrow> w" proof-
      fix i v w assume asm: "enat (Suc i) < llength Ps" "Ps $ i = v" "Ps $ Suc i = w"
      hence "enat (Suc (Suc i)) < llength P" by (metis ldropn_Suc_LCons ldropn_eq_LNil leD leI v(1))
      moreover have "P $ (Suc i) = v" by (simp add: asm(2) v(1))
      moreover have "P $ (Suc (Suc i)) = w" by (simp add: asm(3) v(1))
      ultimately show "v\<rightarrow>w" using valid_path(2) by blast
    qed
    ultimately have "\<exists>v w Ps. P = LCons v Ps \<and> v \<in> V \<and> w \<in> V \<and> v \<rightarrow> w \<and>
      ((\<exists>P. Ps = P \<and> lset P \<subseteq> V \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v \<rightarrow> w)) \<or> valid_path Ps) \<and> \<not> lnull Ps \<and> lhd Ps = w"
      using v w by simp
  }
  thus ?case by blast
qed
lemma valid_path_equiv: "valid_path P \<longleftrightarrow> lset P \<subseteq> V \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w)" using valid_path_impl1 valid_path_impl2 by blast

lemma valid_path_no_deadends: "\<lbrakk> valid_path P; enat (Suc i) < llength P; P $ Suc i = w \<rbrakk> \<Longrightarrow> \<not>deadend (P $ i)"
  using edges_are_in_V valid_path_equiv by blast
lemma valid_path_ends_on_deadend: "\<lbrakk> valid_path P; enat i < llength P; deadend (P $ i) \<rbrakk> \<Longrightarrow> enat (Suc i) = llength P"
  by (meson Suc_ile_eq antisym_conv le_less_linear valid_path_no_deadends)

lemma valid_path_prefix: "valid_path P \<Longrightarrow> lprefix P' P \<Longrightarrow> valid_path P'"
  apply (subst valid_path_equiv, subst (asm) valid_path_equiv)
  apply (intro conjI, blast dest: lprefix_lsetD)
  by (metis Suc_ile_eq less_le_trans lprefix_llength_le lprefix_lnthD order.strict_implies_order)

lemma valid_path_lappend:
  assumes P: "lfinite P" "valid_path P"
    and P': "\<not>lnull P'" "valid_path P'"
    and edge: "llast P\<rightarrow>lhd P'"
  shows "valid_path (lappend P P')"
proof-
  let ?P = "lappend P P'"
  have "lset ?P \<subseteq> V" by (simp add: P P'(2) valid_path_in_V)
  moreover have "\<forall>i v w. enat (Suc i) < llength ?P \<and> ?P $ i = v \<and> ?P $ Suc i = w \<longrightarrow> v\<rightarrow>w" proof (clarify)
    fix i assume "enat (Suc i) < llength ?P"
    have "enat (Suc i) < llength P \<Longrightarrow> ?P $ i \<rightarrow> ?P $ Suc i"
      by (metis P(2) dual_order.strict_trans enat_ord_simps(2) lessI lnth_lappend1 valid_path_edges)
    moreover {
      assume *: "enat (Suc i) = llength P"
      from * have "?P $ i = llast P" by (metis eSuc_enat enat_ord_simps(2) lessI llast_conv_lnth lnth_lappend1)
      moreover from * have "?P $ Suc i = P' $ 0" by (simp add: lnth_lappend2[of P "Suc i" "Suc i" P'] "*")
      ultimately have "?P $ i \<rightarrow> ?P $ Suc i" using P'(1) edge lhd_conv_lnth by force
    }
    moreover {
      assume *: "enat (Suc i) > llength P"
      then obtain j where j: "llength P = enat j" using enat_iless by fastforce
      with * have "j \<le> i" by (metis enat_ord_simps(2) leI not_less_eq)
      hence **: "?P $ i = P' $ (i - j) \<and> ?P $ (Suc i) = P' $ (Suc i - j)"
        using j lnth_lappend2[of P "j" "i" P'] lnth_lappend2[of P "j" "Suc i" P'] by simp
      have "enat (Suc i) < llength P + llength P'" using `enat (Suc i) < llength ?P` by auto
      with j have "enat (Suc i - j) < llength P'"
        by (metis `j \<le> i` add.commute enat_ord_simps(2) infinite_small_llength le_Suc_eq less_diff_conv2 lfinite_llength_enat plus_enat_simps(1))
      moreover hence "enat (i - j) < llength P'"
        using Suc_diff_le[OF `j \<le> i`] Suc_ile_eq order.strict_implies_order by auto
      ultimately have "P' $ (i - j) \<rightarrow> P' $ (Suc i - j)"
        by (simp add: Suc_diff_le `j \<le> i` P'(2) valid_path_edges)
      with ** have "?P $ i \<rightarrow> ?P $ Suc i" by simp
    }
    ultimately show "?P $ i \<rightarrow> ?P $ Suc i" using linorder_cases by blast
  qed
  ultimately show ?thesis using valid_path_equiv by blast
qed

lemma valid_path_supergame:
  assumes "valid_path P" and G': "Digraph G'" "V \<subseteq> V\<^bsub>G'\<^esub>" "E \<subseteq> E\<^bsub>G'\<^esub>"
  shows "Digraph.valid_path G' P"
using assms(1) assms(3) proof (coinduction arbitrary: P rule: Digraph.valid_path.coinduct[OF `Digraph G'`, case_names IH])
  case (IH P)
  show ?case proof (cases)
    assume "P = LNil" thus ?thesis by simp
  next
    assume "P \<noteq> LNil"
    then obtain v P' where P': "P = LCons v P'" by (meson neq_LNil_conv)
    show ?thesis proof (cases)
      assume "P' = LNil"
      thus ?thesis using IH valid_path_cons_simp P' by blast
    next
      assume "P' \<noteq> LNil"
      then obtain w Ps where *: "P = LCons v (LCons w Ps)" using P' llist.exhaust by auto
      hence "v \<in> V\<^bsub>G'\<^esub>" using IH valid_path_cons_simp by blast
      moreover have "w \<in> V\<^bsub>G'\<^esub>" using IH valid_path_ltl valid_path_cons_simp by (metis "*" subsetCE valid_path_ltl')
      moreover have "v \<rightarrow>\<^bsub>G'\<^esub> w" using IH(1) `E \<subseteq> E\<^bsub>G'\<^esub>` * valid_path_edges' by blast
      ultimately show ?thesis using * IH(1) assms(3) valid_path_cons_simp by auto
    qed
  qed
qed

coinductive maximal_path where
maximal_path_base: "maximal_path LNil"
| maximal_path_base': "deadend v \<Longrightarrow> maximal_path (LCons v LNil)"
| maximal_path_cons: "\<not>lnull Ps \<Longrightarrow> maximal_path Ps \<Longrightarrow> maximal_path (LCons v Ps)"

lemma maximal_no_deadend: "maximal_path (LCons v Ps) \<Longrightarrow> \<not>deadend v \<Longrightarrow> \<not>lnull Ps" by (metis lhd_LCons llist.distinct(1) ltl_simps(2) maximal_path.simps)
lemma maximal_ltl: "maximal_path P \<Longrightarrow> maximal_path (ltl P)" by (metis ltl_simps(1) ltl_simps(2) maximal_path.simps)
lemma maximal_drop: "maximal_path P \<Longrightarrow> maximal_path (ldropn n P)" by (simp add: maximal_ltl ltl_ldrop)
lemma maximal_path_impl1:
  assumes "maximal_path P" "enat n < llength P" "\<not>deadend (P $ n)"
  shows "enat (Suc n) < llength P"
proof-
  def P' \<equiv> "ldropn n P"
  hence "\<not>lnull P'" using assms(2) by auto
  then obtain v Ps where v: "P' = LCons v Ps" by (meson not_lnull_conv)
  have "P $ n = lhd P'" by (simp add: P'_def assms(2) lhd_ldropn)
  hence "\<not>deadend v" using assms(3) v by auto
  hence "\<not>lnull Ps" using P'_def assms(1) maximal_drop maximal_no_deadend v by force
  thus ?thesis using P'_def ldropn_Suc_conv_ldropn ldropn_eq_LConsD v by fastforce
qed
lemma maximal_path_impl2: "(\<And>n. enat n < llength P \<and> \<not>deadend (P $ n) \<longrightarrow> enat (Suc n) < llength P) \<Longrightarrow> maximal_path P"
proof (coinduction arbitrary: P rule: maximal_path.coinduct)
  case (maximal_path P)
  show ?case proof (cases "P = LNil \<or> (\<exists>v. P = LCons v LNil \<and> deadend v)", blast)
    case False
    then obtain Ps v where P: "P = LCons v Ps" by (meson neq_LNil_conv)
    hence "\<And>n. enat n < llength Ps \<Longrightarrow> \<not>deadend (Ps $ n) \<Longrightarrow> enat (Suc n) < llength Ps" proof-
      fix n assume asm: "enat n < llength Ps" "\<not>deadend (Ps $ n)"
      have "enat (Suc n) < llength P" using P asm(1) eSuc_enat ileI1 by force
      moreover have "\<not>deadend (P $ Suc n)" using P asm(2) by auto
      ultimately have "enat (Suc (Suc n)) < llength P" using maximal_path by blast
      thus "enat (Suc n) < llength Ps" by (metis P asm(1) dual_order.strict_iff_order eSuc_enat ileI1 llength_LCons)
    qed
    moreover have "\<not>lnull Ps" proof (rule ccontr, simp)
      assume "lnull Ps"
      hence "\<not>deadend (P $ 0)" using False P by auto
      moreover have "0 < llength P" by (simp add: P)
      ultimately have "enat (Suc 0) < llength P" by (simp add: maximal_path zero_enat_def)
      thus False by (simp add: P `lnull Ps` zero_enat_def)
    qed
    ultimately show ?thesis using P by blast
  qed
qed
lemma maximal_path_equiv: "maximal_path P \<longleftrightarrow> (\<forall>n. enat n < llength P \<and> \<not>deadend (P $ n) \<longrightarrow> enat (Suc n) < llength P)"
  using maximal_path_impl1 maximal_path_impl2 by blast

lemma maximal_path_lappend:
  assumes "\<not>lnull P'" "maximal_path P'"
  shows "maximal_path (lappend P P')"
proof-
  let ?P = "lappend P P'"
  { fix n assume "enat n < llength ?P" "\<not>deadend (?P $ n)"
    have len_sum: "llength ?P = llength P + llength P'" by simp
    {
      assume "enat (Suc n) \<le> llength P"
      moreover from `\<not>lnull P'` have "llength P' \<noteq> 0" by simp
      ultimately have "enat (Suc n) < llength ?P"
        by (metis add.right_neutral dual_order.strict_iff_order enat_add1_eq enat_le_plus_same(1) len_sum less_le_trans)
    }
    moreover {
      assume *: "enat (Suc n) > llength P"
      then obtain j where j: "llength P = enat j" using enat_iless by fastforce
      with *
        have "j \<le> n" by (metis enat_ord_simps(2) leI not_less_eq)
      with j len_sum `enat n < llength ?P`
        have "enat (n - j) < llength P'" by (metis enat_add_mono le_add_diff_inverse plus_enat_simps(1))
      moreover from j `j \<le> n`
        have "?P $ n = P' $ (n - j)" using lnth_lappend2[of P "j" "n" P'] by fastforce
      ultimately have "enat (Suc (n - j)) < llength P'"
        using `\<not>deadend (?P $ n)` `maximal_path P'` by (simp add: maximal_path_impl1)
      hence "enat (Suc n - j) < llength P'" by (simp add: Suc_diff_le `j \<le> n`)
      with `j \<le> n` have "enat (Suc n) < enat j + llength P'" by (metis enat_less_enat_plusI2 le_SucI le_add_diff_inverse)
      with len_sum j have "enat (Suc n) < llength ?P" by simp
    }
    ultimately have "enat (Suc n) < llength ?P" using not_le by blast
  }
  thus ?thesis using maximal_path_equiv by blast
qed

lemma maximal_ends_on_deadend:
  assumes "maximal_path P" "lfinite P" "\<not>lnull P"
  shows "deadend (llast P)"
proof (rule ccontr)
  assume *: "\<not>deadend (llast P)"
  from `lfinite P` `\<not>lnull P` obtain i where i: "llength P = enat (Suc i)"
    by (metis enat_ord_simps(2) gr0_implies_Suc lfinite_llength_enat lnull_0_llength)
  hence "llength P = eSuc (enat i)" by (simp add: eSuc_enat)
  hence "llast P = P $ i" using llast_conv_lnth by blast
  with * have "\<not>deadend (P $ i)" by simp
  from i have "enat i < llength P" by simp
  with assms(1) `\<not>deadend (P $ i)` have "enat (Suc i) < llength P" using maximal_path_impl1 by blast
  with i show False by simp
qed

lemma infinite_path_is_maximal: "\<lbrakk> valid_path P; \<not>lfinite P \<rbrakk> \<Longrightarrow> maximal_path P"
  apply (coinduction arbitrary: P rule: maximal_path.coinduct)
  apply (cases rule: valid_path.cases, simp)
  by simp_all

end -- "locale Digraph"

datatype Player = Even | Odd
abbreviation other_player :: "Player \<Rightarrow> Player" where "other_player p \<equiv> (if p = Even then Odd else Even)"
notation other_player ("(_**)" [1000] 1000)
lemma other_other_player [simp]: "p**** = p" using Player.exhaust by auto

record 'a ParityGame = "'a Graph" +
  priority :: "'a \<Rightarrow> nat" ("\<omega>\<index>")
  player0 :: "'a set" ("V0\<index>")

abbreviation winning_priority :: "Player \<Rightarrow> nat \<Rightarrow> bool" where
  "winning_priority p \<equiv> (if p = Even then even else odd)"
lemma winning_priority_for_one_player: "winning_priority p i \<longleftrightarrow> \<not>winning_priority p** i" by simp

locale ParityGame = Digraph G for G :: "('a, 'b) ParityGame_scheme" (structure) +
  assumes valid_player0_set: "V0 \<subseteq> V"
    and priorities_finite: "finite (\<omega> ` V)"
begin
lemma ParityGame [simp]: "ParityGame G" by unfold_locales

abbreviation VV :: "Player \<Rightarrow> 'a set" where "VV p \<equiv> (if p = Even then V0 else V - V0)"
lemma VVp_to_V [intro]: "v \<in> VV p \<Longrightarrow> v \<in> V" by (metis (full_types) Diff_subset subsetCE valid_player0_set)
lemma VV_impl1 [intro]: "v \<in> VV p \<Longrightarrow> v \<notin> VV p**" by auto
lemma VV_impl2 [intro]: "v \<in> VV p** \<Longrightarrow> v \<notin> VV p" by auto
lemma VV_equivalence [iff]: "v \<in> V \<Longrightarrow> v \<notin> VV p \<longleftrightarrow> v \<in> VV p**" by auto
lemma VV_cases: "\<lbrakk> v \<in> V ; v \<in> VV p \<Longrightarrow> P ; v \<in> VV p** \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by fastforce

lemma \<omega>_upperbound: "\<exists>n. \<forall>v \<in> V. \<omega>(v) \<le> n" using finite_nat_set_iff_bounded_le priorities_finite by auto

definition subgame where
  "subgame V' \<equiv> G\<lparr> verts := V' \<inter> V, arcs := E \<inter> (V' \<times> V'), priority := \<omega>, player0 := V0 \<inter> V' \<rparr>"

lemma subgame_V [simp]: "V\<^bsub>subgame V'\<^esub> \<subseteq> V"
  and subgame_E [simp]: "E\<^bsub>subgame V'\<^esub> \<subseteq> E"
  and subgame_\<omega>: "\<omega>\<^bsub>subgame V'\<^esub> = \<omega>"
  unfolding subgame_def by simp_all

lemma subgame_V' [simp]: "V' \<subseteq> V \<Longrightarrow> V\<^bsub>subgame V'\<^esub> = V'" unfolding subgame_def by auto
lemma subgame_E' [simp]: "V' \<subseteq> V \<Longrightarrow> E\<^bsub>subgame V'\<^esub> = E \<inter> (V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>)" unfolding subgame_def by auto

lemma subgame_VV [simp]: "ParityGame.VV (subgame V') p = V' \<inter> VV p" proof-
  have "ParityGame.VV (subgame V') Even = V' \<inter> VV Even" unfolding subgame_def by auto
  moreover have "ParityGame.VV (subgame V') Odd = V' \<inter> VV Odd" proof-
    have "V' \<inter> V - (V0 \<inter> V') = V' \<inter> V \<inter> (V - V0)" by blast
    thus ?thesis unfolding subgame_def by auto
  qed
  ultimately show ?thesis by simp
qed
corollary subgame_VV_subset [simp]: "ParityGame.VV (subgame V') p \<subseteq> VV p" by simp

lemma subgame_finite [simp]: "finite (\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub>)" proof-
  have "finite (\<omega> ` V\<^bsub>subgame V'\<^esub>)" using subgame_V priorities_finite by (meson finite_subset image_mono)
  thus ?thesis by (simp add: subgame_def)
qed

lemma subgame_\<omega>_subset [simp]: "\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub> \<subseteq> \<omega> ` V" by (simp add: image_mono subgame_\<omega>)

lemma subgame_Digraph:
  assumes "V' \<inter> V \<noteq> {}"
  shows "Digraph (subgame V')"
proof (unfold_locales)
  show "V\<^bsub>subgame V'\<^esub> \<noteq> {}" unfolding subgame_def using assms by simp
  show "E\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using valid_edge_set by auto
qed

lemma subgame_ParityGame:
  assumes "V' \<inter> V \<noteq> {}"
  shows "ParityGame (subgame V')"
proof (unfold_locales)
  show "V\<^bsub>subgame V'\<^esub> \<noteq> {}" "E\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>" using subgame_Digraph[unfolded Digraph_def, OF assms] by auto
  show "V0\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using valid_player0_set by auto
  show "finite (\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub>)" by simp
qed

lemma subgame_deadend [simp]: "\<not>Digraph.deadend (subgame V') v \<Longrightarrow> \<not>deadend v"
  by (meson subgame_E subgame_V subsetCE)

lemma subgame_valid_path:
  assumes "V' \<inter> V \<noteq> {}" and P: "valid_path P" "lset P \<subseteq> V'"
  shows "Digraph.valid_path (subgame V') P"
proof-
  have *: "Digraph (subgame V')" using assms(1) subgame_Digraph by blast
  have "lset P \<subseteq> V" using P(1) valid_path_in_V by blast
  hence "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) by auto
  with P(1) show ?thesis proof (coinduction arbitrary: P rule: Digraph.valid_path.coinduct[OF "*", case_names IH])
    case IH
    thus ?case proof (cases rule: valid_path.cases)
      case (valid_path_cons v w Ps)
      moreover hence "v \<in> V\<^bsub>subgame V'\<^esub>" "w \<in> V\<^bsub>subgame V'\<^esub>" using IH(2) by auto
      moreover hence "v \<rightarrow>\<^bsub>subgame V'\<^esub> w" using local.valid_path_cons(4) subgame_def by auto
      moreover have "valid_path Ps" using IH(1) valid_path_ltl' local.valid_path_cons(1) by blast
      ultimately show ?thesis using IH(2) by auto
    qed auto
  qed
qed

lemma subgame_maximal_path:
  assumes V': "V' \<inter> V \<noteq> {}" "V' \<subseteq> V" and P: "maximal_path P" "lset P \<subseteq> V'"
  shows "Digraph.maximal_path (subgame V') P"
proof-
  have *: "Digraph (subgame V')" using assms(1) subgame_Digraph by blast
  have "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) V'(2) by auto
  with P(1) assms(2) show ?thesis
    by (coinduction arbitrary: P rule: Digraph.maximal_path.coinduct[OF "*"])
       (cases rule: maximal_path.cases, auto)
qed

definition path_priorities :: "'a Path \<Rightarrow> nat \<Rightarrow> nat" where
  "path_priorities P i \<equiv> \<omega> (P $ i)"
(* The set of priorities that occur infinitely often on a given path. *)
definition path_inf_priorities :: "'a Path \<Rightarrow> nat set" where
  "path_inf_priorities P \<equiv> {k. \<forall>n. k \<in> lset (ldropn n (lmap \<omega> P))}"

lemma path_priorities_equiv: assumes "\<not>lfinite P" shows "path_priorities P i = lmap \<omega> P $ i" proof-
  have "enat i < llength P" using assms enat_iless llength_eq_enat_lfiniteD neq_iff by blast
  thus ?thesis by (simp add: path_priorities_def)
qed

lemma llist_nth_set: "\<lbrakk> \<not>lfinite x; x $ i = y \<rbrakk> \<Longrightarrow> y \<in> lset x" using llist_set_nth by blast
lemma index_infinite_set: "\<lbrakk> \<not>lfinite x; x $ i = y; \<And>i. x $ i = y \<Longrightarrow> (\<exists>j > i. x $ j = y) \<rbrakk> \<Longrightarrow> y \<in> lset (ldropn n x)"
proof (induct n arbitrary: x i)
  case 0 thus ?case using llist_nth_set by fastforce
next
  case (Suc n)
  obtain a xs where x: "x = LCons a xs" by (meson Suc.prems(1) lnull_imp_lfinite not_lnull_conv)
  obtain j where j: "j > i" "x $ j = y" using Suc.prems(2) Suc.prems(3) by blast
  have "xs $ j - 1 = y" by (metis LCons_suc_is_P2 j(1) j(2) not_less0 x)
  moreover have "\<And>i. xs $ i = y \<Longrightarrow> \<exists>j>i. xs $ j = y" proof-
    fix i assume "xs $ i = y"
    hence "x $ Suc i = y" by (simp add: x)
    thus "\<exists>j>i. xs $ j = y" by (metis Suc.prems(3) Suc_lessE lnth_Suc_LCons x)
  qed
  ultimately show ?case using Suc.hyps Suc.prems(1) x by auto
qed

lemma path_priorities_in_\<omega>V: "\<lbrakk> valid_path P; \<not>lfinite P \<rbrakk> \<Longrightarrow> path_priorities P i \<in> \<omega> ` V"
  using assms path_priorities_def valid_path_in_V' by auto

lemma LCons_extends:
  assumes "\<exists>i. P $ i = w"
  shows "\<exists>i. LCons v P $ i = w"
proof-
  from assms obtain i where "P $ i = w" by auto
  hence "LCons v P $ Suc i = w" by simp
  thus ?thesis by blast
qed

lemma path_inf_priorities_is_nonempty:
  assumes "valid_path P" "\<not>lfinite P"
  shows "\<exists>k. k \<in> path_inf_priorities P"
  proof -
    have "\<forall>i. path_priorities P i \<in> \<omega>`V" using assms path_priorities_in_\<omega>V by blast
    then obtain k i where "path_priorities P i = k" "\<forall>i. path_priorities P i = k \<longrightarrow> (\<exists>j > i. path_priorities P j = k)"
      using pigeon_hole_principle[of "\<omega>`V" "path_priorities P"] priorities_finite by blast
    hence "\<And>n. k \<in> lset (ldropn n (lmap \<omega> P))" using index_infinite_set[of "lmap \<omega> P" i k] by (metis assms(2) lfinite_lmap path_priorities_equiv)
    thus ?thesis using path_inf_priorities_def by auto
  qed

lemma path_inf_priorities_has_minimum:
  assumes "valid_path P" "\<not>lfinite P"
  obtains a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)"
  proof -
    have "\<exists>a. a \<in> path_inf_priorities P" using assms path_inf_priorities_is_nonempty by blast
    then obtain a where "a \<in> path_inf_priorities P" "(\<And>z. z < a \<Longrightarrow> z \<notin> path_inf_priorities P)"
      by (metis less_eq less_than_def wf_less_than wfE_min)
    thus ?thesis by (metis leI that)
  qed

lemma in_set_ldropn: "x \<in> lset (ldropn (Suc n) xs) \<Longrightarrow> x \<in> lset (ldropn n xs)"
  by (simp add: in_lset_ltlD ldrop_eSuc_ltl ltl_ldropn)

lemma path_inf_priorities_LCons: "path_inf_priorities P = path_inf_priorities (LCons v P)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" proof
    fix a assume "a \<in> ?A"
    hence "\<forall>n. a \<in> lset (ldropn n (lmap \<omega> (LCons v P)))" using path_inf_priorities_def in_set_ldropn[of a _ "lmap \<omega> (LCons v P)"] by auto
    thus "a \<in> ?B" using path_inf_priorities_def by blast
  qed
next
  show "?B \<subseteq> ?A" proof
    fix a assume "a \<in> ?B"
    hence "\<forall>n. a \<in> lset (ldropn (Suc n) (lmap \<omega> (LCons v P)))" using path_inf_priorities_def by blast
    hence "\<forall>n. a \<in> lset (ldropn n (lmap \<omega> P))" by auto
    thus "a \<in> ?A" using path_inf_priorities_def by blast
  qed
qed
corollary path_inf_priorities_ltl: "path_inf_priorities P = path_inf_priorities (ltl P)"
  by (metis llist.exhaust ltl_simps(1) ltl_simps(2) path_inf_priorities_LCons)

(* True iff the path is winning for the given player. *)
definition winning_path :: "Player \<Rightarrow> 'a Path \<Rightarrow> bool" where
  "winning_path p P \<equiv>
    (\<not>lfinite P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (\<not>lnull P \<and> lfinite P \<and> llast P \<in> VV p**)
    \<or> (lnull P \<and> p = Even)"

lemma paths_are_winning_for_exactly_one_player:
  assumes "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
proof (cases)
  assume "lnull P" thus ?thesis using winning_path_def by auto
next
  assume "\<not>lnull P"
  show ?thesis proof (cases)
    assume finite: "lfinite P"
    have 1: "winning_path p P \<longleftrightarrow> llast P \<in> VV p**" by (simp add: `\<not>lnull P` local.finite winning_path_def)
    have 2: "winning_path p** P \<longleftrightarrow> llast P \<in> VV p" by (simp add: `\<not>lnull P` local.finite winning_path_def)
    have "llast P \<in> V" proof-
      obtain n where n: "llength P = enat (Suc n)" by (metis `\<not>lnull P` lfinite_llength_enat llength_eq_0 local.finite nat.exhaust zero_enat_def)
      hence "P $ n = llast P \<and> enat n < llength P" by (simp add: eSuc_enat llast_conv_lnth)
      thus ?thesis using assms valid_path_finite_in_V' by force
    qed
    thus ?thesis by (simp add: "1" "2")
  next
    assume infinite: "\<not>lfinite P"
    then obtain a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using assms path_inf_priorities_has_minimum by blast
    hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" using infinite winning_path_def by (metis `\<not>lnull P` le_antisym)
    thus ?thesis using winning_priority_for_one_player by blast
  qed
qed

corollary paths_are_winning_for_one_player: "valid_path P \<Longrightarrow> \<exists>!p. winning_path p P"
  by (metis (full_types) Player.exhaust assms paths_are_winning_for_exactly_one_player)

lemma winning_path_ltl:
  assumes P: "winning_path p P" "\<not>lnull P" "\<not>lnull (ltl P)"
  shows "winning_path p (ltl P)"
proof (cases)
  assume "lfinite P"
  moreover have "llast P = llast (ltl P)" using P(2) P(3) by (metis llast_LCons2 ltl_simps(2) not_lnull_conv)
  ultimately show ?thesis using P by (simp add: winning_path_def)
next
  assume "\<not>lfinite P"
  thus ?thesis using winning_path_def path_inf_priorities_ltl using P(1) P(2) by auto
qed

corollary winning_path_drop:
  assumes "winning_path p P" "enat n < llength P"
  shows "winning_path p (ldropn n P)"
using assms proof (induct n, simp)
  case (Suc n)
  hence "winning_path p (ldropn n P)" using dual_order.strict_trans enat_ord_simps(2) by blast
  moreover have "ltl (ldropn n P) = ldropn (Suc n) P" by (simp add: ldrop_eSuc_ltl ltl_ldropn)
  moreover hence "\<not>lnull (ldropn n P)" using Suc.prems(2) by (metis leD lnull_ldropn lnull_ltlI)
  ultimately show ?case using winning_path_ltl[of p "ldropn n P"] Suc.prems(2) by auto
qed

corollary winning_path_drop_add:
  assumes "valid_path P" "winning_path p (ldropn n P)" "enat n < llength P"
  shows "winning_path p P"
  using assms paths_are_winning_for_exactly_one_player valid_path_drop winning_path_drop by blast

lemma winning_path_LCons:
  assumes P: "winning_path p P" "\<not>lnull P"
  shows "winning_path p (LCons v P)"
proof (cases)
  assume "lfinite P"
  moreover have "llast P = llast (LCons v P)" using P(2) by (metis llast_LCons2 not_lnull_conv)
  ultimately show ?thesis using P by (simp add: winning_path_def)
next
  assume "\<not>lfinite P"
  thus ?thesis using winning_path_def path_inf_priorities_LCons using P(1) P(2) by auto
qed

lemma winning_path_supergame:
  assumes "winning_path p P"
  and G': "ParityGame G'" "VV p** \<subseteq> ParityGame.VV G' p**" "\<omega> = \<omega>\<^bsub>G'\<^esub>"
  shows "ParityGame.winning_path G' p P"
proof-
  { assume "\<not>lfinite P"
    moreover hence "\<not>lnull P" by auto
    ultimately have "\<exists>a. a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a"
      using assms(1) unfolding winning_path_def by blast
    moreover have "path_inf_priorities P = ParityGame.path_inf_priorities G' P"
      unfolding path_inf_priorities_def using ParityGame.path_inf_priorities_def[of G' P] G'(1) G'(3) by auto
    ultimately have "\<exists>a. a \<in> ParityGame.path_inf_priorities G' P \<and> (\<forall>b \<in> ParityGame.path_inf_priorities G' P. a \<le> b) \<and> winning_priority p a" by blast
  }
  moreover {
    assume "lfinite P" "\<not>lnull P"
    hence "llast P \<in> VV p**" using assms(1) unfolding winning_path_def by blast
    hence "llast P \<in> ParityGame.VV G' p**" using G'(2) by blast
  }
  moreover {
    assume "lnull P" hence "p = Even" using assms(1) unfolding winning_path_def by simp
  }
  ultimately show ?thesis using ParityGame.winning_path_def[of G' p P] G'(1) by blast
qed

end -- "locale ParityGame"

locale vm_path = ParityGame +
  fixes P v0
  assumes P_not_null [simp]: "\<not>lnull P"
      and P_valid    [simp]: "valid_path P"
      and P_maximal  [simp]: "maximal_path P"
      and P_v0       [simp]: "lhd P = v0"
lemma (in vm_path) vm_path [simp]: "vm_path G P v0" by unfold_locales

lemma (in ParityGame) vm_pathI:
  assumes "\<not>lnull P" "valid_path P" "maximal_path P" "lhd P = v0"
  shows "vm_path G P v0"
  using assms by unfold_locales blast

lemma (in ParityGame) vm_pathI0:
  assumes "\<not>lnull P" "valid_path P" "maximal_path P"
  shows "vm_path G P (P $ 0)"
  using assms vm_pathI by (simp add: lnth_0_conv_lhd)

context vm_path begin
lemma P_LCons: "P = LCons v0 (ltl P)" using lhd_LCons_ltl[OF P_not_null] by simp

lemma P_len [simp]: "enat 0 < llength P" by (simp add: lnull_0_llength)
lemma P_0 [simp]: "P $ 0 = v0" by (simp add: lnth_0_conv_lhd)
lemma P_len_Suc: "enat (Suc n) < llength P \<Longrightarrow> enat n < llength (ltl P)"
  using enat_Suc_ltl by auto
lemma P_lnth_Suc: "P $ Suc n = ltl P $ n" by (simp add: lnth_ltl)
lemma P_lset: "lset (ltake (enat n) (ltl P)) \<subseteq> lset (ltake (enat (Suc n)) P)"
proof-
  have "ltake (eSuc (enat n)) P = LCons v0 (ltake (enat n) (ltl P))"
    by (metis assms P_LCons ltake_eSuc_LCons)
  hence "lset (ltake (enat (Suc n)) P) = lset (LCons v0 (ltake (enat n) (ltl P)))"
    by (simp add: eSuc_enat)
  thus ?thesis using lset_LCons[of v0 "ltake (enat n) (ltl P)"] by blast
qed
lemma P_no_deadends: "enat (Suc n) < llength P \<Longrightarrow> \<not>deadend (P $ n)"
  using valid_path_no_deadends by simp
lemma P_no_deadend_v0: "\<not>lnull (ltl P) \<Longrightarrow> \<not>deadend v0"
  by (metis P_LCons P_valid edges_are_in_V not_lnull_conv valid_path_edges')
lemma P_no_deadend_v0_llength: "enat (Suc n) < llength P \<Longrightarrow> \<not>deadend v0"
  by (metis P_0 P_len P_valid enat_ord_simps(2) not_less_eq valid_path_ends_on_deadend zero_less_Suc)
lemma P_ends_on_deadend: "enat n < llength P \<Longrightarrow> deadend (P $ n) \<Longrightarrow> enat (Suc n) = llength P"
  using P_valid valid_path_ends_on_deadend by blast

lemma P_lnull_ltl_deadend_v0: "lnull (ltl P) \<Longrightarrow> deadend v0"
  using P_LCons maximal_no_deadend by force
lemma P_lnull_ltl_LCons: "lnull (ltl P) \<Longrightarrow> P = LCons v0 LNil"
  using P_LCons lnull_def by metis
lemma P_deadend_v0_LCons: "deadend v0 \<Longrightarrow> P = LCons v0 LNil"
  using P_lnull_ltl_LCons P_no_deadend_v0 by blast

lemma Ptl_valid [simp]: "valid_path (ltl P)" using valid_path_ltl by auto
lemma Ptl_maximal [simp]: "maximal_path (ltl P)" using maximal_ltl by auto

lemma Pdrop_valid [simp]: "valid_path (ldropn n P)" using valid_path_drop by auto
lemma Pdrop_maximal [simp]: "maximal_path (ldropn n P)" using maximal_drop by auto

lemma prefix_valid [simp]: "valid_path (ltake n P)"
  using valid_path_prefix[of P] by auto

lemma extension_valid [simp]: "v'\<rightarrow>v0 \<Longrightarrow> valid_path (LCons v' P)"
  by (simp add: valid_path_cons')
lemma extension_maximal [simp]: "maximal_path (LCons v' P)"
  by (simp add: maximal_path_cons)
lemma lappend_maximal [simp]: "maximal_path (lappend P' P)"
  by (simp add: maximal_path_lappend)

lemma v0_V [simp]: "v0 \<in> V" by (metis P_LCons P_valid valid_path_cons_simp)
lemma v0_VV: "v0 \<in> VV p \<or> v0 \<in> VV p**" by simp
lemma lset_P_V [simp]: "lset P \<subseteq> V" by (simp add: valid_path_in_V)
lemma lset_ltl_P_V [simp]: "lset (ltl P) \<subseteq> V" by (simp add: valid_path_in_V)

lemma finite_llast_deadend [simp]: "lfinite P \<Longrightarrow> deadend (llast P)"
  using P_maximal P_not_null maximal_ends_on_deadend by blast
lemma finite_llast_V [simp]: "lfinite P \<Longrightarrow> llast P \<in> V"
  using P_not_null lfinite_lset lset_P_V by blast

lemma suc_n_deadend: "enat (Suc n) = llength P \<Longrightarrow> deadend (P $ n)"
  by (metis P_maximal enat_ord_simps(2) lessI maximal_path_impl1 min.strict_order_iff)

end

end
