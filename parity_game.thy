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
lemma infinite_small_llength: "\<not>lfinite xs \<Longrightarrow> enat i < llength xs"
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
lemma valid_path_drop: "valid_path P \<Longrightarrow> valid_path (ldropn n P)"  unfolding ldropn_def by (induct rule: fun_iter_induct; simp add: valid_path_ltl)

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

lemma valid_path_impl1: "valid_path P \<Longrightarrow> lset P \<subseteq> V \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w)" using valid_path_edges valid_path_in_V by blast
lemma valid_path_impl2: "\<lbrakk> lset P \<subseteq> V; \<And>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w \<rbrakk> \<Longrightarrow> valid_path P" proof (coinduction arbitrary: P rule: valid_path.coinduct)
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
      hence **: "?P $ i = P' $ (i - j) \<and> ?P $ (Suc i) = P' $ (Suc i - j)" using j lnth_lappend2[of P "j" "i" P'] lnth_lappend2[of P "j" "Suc i" P'] by simp
      have "enat (Suc i) < llength P + llength P'" using `enat (Suc i) < llength ?P` by auto
      with j have "enat (Suc i - j) < llength P'" by (metis `j \<le> i` add.commute enat_ord_simps(2) infinite_small_llength le_Suc_eq less_diff_conv2 lfinite_llength_enat plus_enat_simps(1))
      moreover hence "enat (i - j) < llength P'" using Suc_diff_le Suc_ile_eq `j \<le> i` by fastforce
      ultimately have "P' $ (i - j) \<rightarrow> P' $ (Suc i - j)" by (simp add: Suc_diff_le `j \<le> i` P'(2) valid_path_edges)
      with ** have "?P $ i \<rightarrow> ?P $ Suc i" by simp
    }
    ultimately show "?P $ i \<rightarrow> ?P $ Suc i" using linorder_cases by blast
  qed
  ultimately show ?thesis using valid_path_equiv by blast
qed

coinductive maximal_path where
  "maximal_path LNil"
| "deadend v \<Longrightarrow> maximal_path (LCons v LNil)"
| "\<not>lnull Ps \<Longrightarrow> maximal_path Ps \<Longrightarrow> maximal_path (LCons v Ps)"

lemma maximal_no_deadend: "maximal_path (LCons v Ps) \<Longrightarrow> \<not>deadend v \<Longrightarrow> \<not>lnull Ps" by (metis lhd_LCons llist.distinct(1) ltl_simps(2) maximal_path.simps)
lemma maximal_tail: "maximal_path P \<Longrightarrow> maximal_path (ltl P)" by (metis ltl_simps(1) ltl_simps(2) maximal_path.simps)
lemma maximal_drop: "maximal_path P \<Longrightarrow> maximal_path (ldropn n P)" unfolding ldropn_def by (induct rule: fun_iter_induct; simp add: maximal_tail)
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
end -- "locale Digraph"

datatype Player = Even | Odd
abbreviation other_player :: "Player \<Rightarrow> Player" where "other_player p \<equiv> (if p = Even then Odd else Even)"
notation other_player ("(_**)" [1000] 1000)
lemma [simp]: "p**** = p" using Player.exhaust by auto

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

abbreviation VV :: "Player \<Rightarrow> 'a set" where "VV p \<equiv> (if p = Even then V0 else V - V0)"
lemma VVp_to_V [intro]: "v \<in> VV p \<Longrightarrow> v \<in> V" by (metis (full_types) Diff_subset subsetCE valid_player0_set)
lemma VV_impl1 [intro]: "v \<in> VV p \<Longrightarrow> v \<notin> VV p**" by auto
lemma VV_impl2 [intro]: "v \<in> VV p** \<Longrightarrow> v \<notin> VV p" by auto
lemma VV_equivalence [iff]: "v \<in> V \<Longrightarrow> v \<notin> VV p \<longleftrightarrow> v \<in> VV p**" by auto
lemma VV_cases: "\<lbrakk> v \<in> V ; v \<in> VV p \<Longrightarrow> P ; v \<in> VV p** \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by fastforce

lemma \<omega>_upperbound: "\<exists>n. \<forall>v \<in> V. \<omega>(v) \<le> n" using finite_nat_set_iff_bounded_le priorities_finite by auto

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

(* True iff the path is winning for the given player. *)
definition winning_path :: "Player \<Rightarrow> 'a Path \<Rightarrow> bool" where
  "winning_path p P \<equiv>
    (\<not>lfinite P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (\<not>lnull P \<and> lfinite P \<and> llast P \<in> VV p**)
    \<or> (lnull P \<and> p = Even)"

lemma paths_are_winning_for_exactly_one_player:
  assumes "\<not>lnull P" "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
proof (cases)
  assume finite: "lfinite P"
  have 1: "winning_path p P \<longleftrightarrow> llast P \<in> VV p**" by (simp add: assms(1) local.finite winning_path_def)
  have 2: "winning_path p** P \<longleftrightarrow> llast P \<in> VV p" by (simp add: assms(1) local.finite winning_path_def)
  have "llast P \<in> V" proof-
    obtain n where n: "llength P = enat (Suc n)" by (metis assms(1) lfinite_llength_enat llength_eq_0 local.finite nat.exhaust zero_enat_def)
    hence "P $ n = llast P \<and> enat n < llength P" by (simp add: eSuc_enat llast_conv_lnth)
    thus ?thesis using assms(2) valid_path_finite_in_V' by force
  qed
  thus ?thesis by (simp add: "1" "2")
next
  assume infinite: "\<not>lfinite P"
  then obtain a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using assms path_inf_priorities_has_minimum by blast
  hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" using infinite winning_path_def by (metis assms(1) le_antisym)
  thus ?thesis using winning_priority_for_one_player by blast
qed

lemma paths_are_winning_for_one_player:
  assumes "\<not>lnull P" "valid_path P"
  shows "\<exists>!p. winning_path p P"
  by (metis (full_types) Player.exhaust assms paths_are_winning_for_exactly_one_player)

end -- "locale ParityGame"

end
