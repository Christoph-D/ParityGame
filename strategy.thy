theory strategy
imports
  Main
  parity_game
begin

type_synonym 'a Strategy = "'a \<Rightarrow> 'a"

context ParityGame begin

(* A strategy for player p is a function on VV p assigning a successor to each node. *)
definition strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> v\<rightarrow>\<sigma> v"

(* If path_conforms_with_strategy p P \<sigma> is True, then we call P a \<sigma>-path.
This means that P follows \<sigma> on all nodes of player p except maybe the last node on the path. *)
coinductive path_conforms_with_strategy :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
path_conforms_LNil:  "path_conforms_with_strategy p LNil \<sigma>"
| path_conforms_LCons_LNil: "path_conforms_with_strategy p (LCons v LNil) \<sigma>"
| path_conforms_VVp: "\<lbrakk> v \<in> VV p; w = \<sigma> v; path_conforms_with_strategy p (LCons w Ps) \<sigma> \<rbrakk> \<Longrightarrow> path_conforms_with_strategy p (LCons v (LCons w Ps)) \<sigma>"
| path_conforms_VVpstar: "\<lbrakk> v \<notin> VV p; path_conforms_with_strategy p Ps \<sigma> \<rbrakk> \<Longrightarrow> path_conforms_with_strategy p (LCons v Ps) \<sigma>"

(* A strategy is winning for player p from v0 if every maximal \<sigma>-path starting in v0 is winning. *)
definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  "winning_strategy p \<sigma> v0 \<equiv> \<forall>P. \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0 \<longrightarrow> winning_path p P"

(* All \<sigma>-paths starting from v0 visit W and until then they stay in A. *)
definition strategy_attracts_via :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_via p \<sigma> v0 A W \<equiv> \<forall>P.
      \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0
    \<longrightarrow> (\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"

(* All \<sigma>-paths starting from A visit W and until then they stay in A. *)
definition strategy_attracts :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts p \<sigma> A W \<equiv> \<forall>v0 \<in> A. strategy_attracts_via p \<sigma> v0 A W"

(* All \<sigma>-paths starting from A never visit W. *)
definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv> (\<forall>P.
      \<not>lnull P \<and> valid_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 \<in> A
    \<longrightarrow> lset P \<inter> W = {})"

abbreviation path_prefix :: "'a Path \<Rightarrow> 'a Path \<Rightarrow> bool" where "path_prefix \<equiv> lprefix"

lemma path_prefix_length: "\<lbrakk> path_prefix P P'; i < llength P \<rbrakk> \<Longrightarrow> i < llength P'" by (metis dual_order.strict_trans lstrict_prefix_def lstrict_prefix_llength_less)
lemma path_prefix_included: "\<lbrakk> path_prefix P P'; enat i < llength P \<rbrakk> \<Longrightarrow> P $ i = P' $ i" using lprefix_lnthD by blast
lemma path_prefix_infinite: "\<lbrakk> path_prefix P P'; \<not>lfinite P \<rbrakk> \<Longrightarrow> P $ i = P' $ i" by (simp add: not_lfinite_lprefix_conv_eq)
lemma path_prefix_valid:
  assumes "valid_path P'" "path_prefix P P'"
  shows "valid_path P"
proof (subst valid_path_equiv, intro conjI)
  show "lset P \<subseteq> V" by (meson assms(1) assms(2) dual_order.trans lprefix_lsetD valid_path_in_V)
  show "\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v \<rightarrow> w" proof (clarify)
    fix i v w assume *: "enat (Suc i) < llength P"
    hence "enat (Suc i) < llength P'" using assms(2) path_prefix_length by blast
    thus "P $ i \<rightarrow> (P $ Suc i)" using "*" assms(1) assms(2) dual_order.strict_trans path_prefix_included valid_path_edges by fastforce
  qed
qed

(* An arbitrary strategy.  Useful to define other strategies. *)
definition "\<sigma>_arbitrary \<equiv> \<lambda>v. SOME w. v\<rightarrow>w"

lemma valid_arbitrary_strategy [simp]: "strategy p \<sigma>_arbitrary" proof-
  { fix v assume "\<not>deadend v"
    hence "\<not>deadend v \<Longrightarrow> v \<rightarrow> \<sigma>_arbitrary v" unfolding \<sigma>_arbitrary_def using someI_ex[of "\<lambda>w. v\<rightarrow>w"] by blast
  }
  thus ?thesis unfolding strategy_def by blast
qed

lemma valid_strategy_updates: "\<lbrakk> strategy p \<sigma>; v0\<rightarrow>w0 \<rbrakk> \<Longrightarrow> strategy p (\<sigma>(v0 := w0))"
  unfolding strategy_def by auto

lemma valid_strategy_updates_set:
  assumes "strategy p \<sigma>" "\<And>v. \<lbrakk> v \<in> A; v \<in> VV p; \<not>deadend v \<rbrakk> \<Longrightarrow> v\<rightarrow>\<sigma>' v"
  shows "strategy p (override_on \<sigma> \<sigma>' A)"
  unfolding strategy_def by (metis assms override_on_def strategy_def)

lemma valid_strategy_in_V: "\<lbrakk> strategy p \<sigma>; v \<in> VV p; \<not>deadend v \<rbrakk> \<Longrightarrow> \<sigma> v \<in> V"
  unfolding strategy_def using valid_edge_set by auto

lemma one_step_path_exists:
  assumes "v0 \<in> V"
  shows "\<exists>P. valid_path P \<and> lfinite P \<and> path_conforms_with_strategy p P \<sigma> \<and> \<not>lnull P \<and> P $ 0 = v0"
  by (meson assms lfinite_code(1) lfinite_code(2) llist.disc(2) lnth_0 path_conforms_with_strategy.intros(2) valid_path_base')

lemma path_conforms_with_strategy_ltl [intro]:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ltl P) \<sigma>"
  by (drule path_conforms_with_strategy.cases) (simp_all add: path_conforms_with_strategy.intros(1))

lemma path_conforms_with_strategy_drop:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ldropn n P) \<sigma>"
  by (simp add: path_conforms_with_strategy_ltl ltl_ldrop[of "\<lambda>P. path_conforms_with_strategy p P \<sigma>"])

lemma path_conforms_with_strategy_prefix:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_prefix P' P \<Longrightarrow> path_conforms_with_strategy p P' \<sigma>"
proof (coinduction arbitrary: P P')
  case (path_conforms_with_strategy P P')
  thus ?case proof (cases rule: path_conforms_with_strategy.cases)
    case path_conforms_LNil
    thus ?thesis using path_conforms_with_strategy(2) by auto
  next
    case path_conforms_LCons_LNil
    thus ?thesis by (metis lprefix_LCons_conv lprefix_antisym lprefix_code(1) path_conforms_with_strategy(2))
  next
    case (path_conforms_VVp v w)
    thus ?thesis proof (cases "P' = LNil \<or> P' = LCons v LNil")
      case True thus ?thesis by auto
    next
      case False
      hence "\<exists>Q. P' = LCons v (LCons w Q)" by (metis local.path_conforms_VVp(1) lprefix_LCons_conv path_conforms_with_strategy(2))
      thus ?thesis using local.path_conforms_VVp(1) local.path_conforms_VVp(3) local.path_conforms_VVp(4) path_conforms_with_strategy(2) by force
    qed
  next
    case (path_conforms_VVpstar v)
    thus ?thesis proof (cases "P' = LNil", simp)
      case False
      hence "\<exists>Q. P' = LCons v Q" using local.path_conforms_VVpstar(1) lprefix_LCons_conv path_conforms_with_strategy(2) by fastforce
      thus ?thesis using local.path_conforms_VVpstar path_conforms_with_strategy(2) by auto
    qed
  qed
qed

lemma path_conforms_with_strategy_irrelevant:
  assumes "path_conforms_with_strategy p P \<sigma>" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P (\<sigma>(v := w))"
  using assms apply (coinduction arbitrary: P) by (drule path_conforms_with_strategy.cases) auto

lemma path_conforms_with_strategy_irrelevant_deadend:
  assumes "path_conforms_with_strategy p P \<sigma>" "deadend v \<or> v \<notin> VV p" "valid_path P"
  shows "path_conforms_with_strategy p P (\<sigma>(v := w))"
using assms proof (coinduction arbitrary: P)
  let ?\<sigma> = "\<sigma>(v := w)"
  case (path_conforms_with_strategy P)
  thus ?case proof (cases rule: path_conforms_with_strategy.cases)
    case path_conforms_LNil thus ?thesis by simp
  next
    case path_conforms_LCons_LNil thus ?thesis by auto
  next
    case (path_conforms_VVp v' w Ps)
    have "w = ?\<sigma> v'" proof-
      from `valid_path P` have "\<not>deadend v'" using local.path_conforms_VVp(1) valid_path_cons_simp by blast
      with assms(2) have "v' \<noteq> v" using local.path_conforms_VVp(2) by blast
      thus "w = ?\<sigma> v'" by (simp add: local.path_conforms_VVp(3))
    qed
    moreover have "\<exists>P. LCons w Ps = P \<and> path_conforms_with_strategy p P \<sigma> \<and> (deadend v \<or> v \<notin> VV p) \<and> valid_path P" proof-
      have "valid_path (LCons w Ps)" using local.path_conforms_VVp(1) path_conforms_with_strategy(3) valid_path_ltl' by blast
      thus ?thesis using local.path_conforms_VVp(4) path_conforms_with_strategy(2) by blast
    qed
    ultimately show ?thesis using local.path_conforms_VVp(1) local.path_conforms_VVp(2) by blast
  next
    case (path_conforms_VVpstar v' Ps)
    have "\<exists>P. path_conforms_with_strategy p Ps \<sigma> \<and> (deadend v \<or> v \<notin> VV p) \<and> valid_path Ps"
      using local.path_conforms_VVpstar(1) local.path_conforms_VVpstar(3) path_conforms_with_strategy(2) path_conforms_with_strategy(3) valid_path_ltl' by blast
    thus ?thesis by (simp add: local.path_conforms_VVpstar(1) local.path_conforms_VVpstar(2))
  qed
qed

lemma path_conforms_with_strategy_irrelevant':
  assumes "path_conforms_with_strategy p P (\<sigma>(v := w))" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P \<sigma>"
  by (metis assms fun_upd_triv fun_upd_upd path_conforms_with_strategy_irrelevant)

lemma path_conforms_with_strategy_irrelevant_deadend':
  assumes "path_conforms_with_strategy p P (\<sigma>(v := w))" "deadend v \<or> v \<notin> VV p" "valid_path P"
  shows "path_conforms_with_strategy p P \<sigma>"
  by (metis assms fun_upd_triv fun_upd_upd path_conforms_with_strategy_irrelevant_deadend)

lemma path_conforms_with_strategy_start:
  "path_conforms_with_strategy p (LCons v (LCons w P)) \<sigma> \<Longrightarrow> v \<in> VV p \<Longrightarrow> \<sigma> v = w"
  by (drule path_conforms_with_strategy.cases) simp_all

lemma path_conforms_with_strategy_conforms:
  assumes "valid_path P" "path_conforms_with_strategy p P \<sigma>" "enat (Suc n) < llength P" "P $ n \<in> VV p"
  shows "\<sigma> (P $ n) = P $ Suc n"
proof-
  def P' \<equiv> "ldropn n P"
  have "valid_path P'" by (simp add: P'_def assms(1) valid_path_drop)
  have "path_conforms_with_strategy p P' \<sigma>" by (simp add: P'_def assms(2) path_conforms_with_strategy_drop)
  from assms(3) have "\<not>lnull P'" using P'_def less_le_trans by fastforce
  moreover from assms(3) have "\<not>lnull (ltl P')" by (metis P'_def enat_Suc_ltl leD lnull_ldropn ltl_ldropn)
  ultimately obtain v w P'' where P'': "P' = LCons v (LCons w P'')" by (metis lhd_LCons_ltl)
  from assms(3) have "enat n < llength P" using dual_order.strict_trans enat_ord_simps(2) by blast
  with assms(4) have "v \<in> VV p" by (metis P'' P'_def ldropn_Suc_conv_ldropn llist.inject)
  hence "\<sigma> v = w" using P'' `path_conforms_with_strategy p P' \<sigma>` path_conforms_with_strategy_start by blast
  thus ?thesis by (metis P'' P'_def `enat n < llength P` assms(3) ldropn_Suc_conv_ldropn llist.inject)
qed

lemma path_conforms_with_strategy_lappend:
  assumes
    P: "lfinite P" "\<not>lnull P" "path_conforms_with_strategy p P \<sigma>"
    and P': "\<not>lnull P'" "path_conforms_with_strategy p P' \<sigma>"
    and conforms: "llast P \<in> VV p" "\<sigma> (llast P) = lhd P'"
  shows "path_conforms_with_strategy p (lappend P P') \<sigma>"
using assms proof (induct P rule: lfinite_induct, simp)
  case (LCons P)
  show ?case proof (cases)
    assume "lnull (ltl P)"
    then obtain v0 where v0: "P = LCons v0 LNil" by (metis LCons.prems(1) lhd_LCons_ltl llist.collapse(1))
    have "path_conforms_with_strategy p (LCons (lhd P) P') \<sigma>" proof (cases)
      assume "lhd P \<in> VV p"
      moreover with v0 have "lhd P' = \<sigma> (lhd P)"
        using LCons.prems(6) by auto
      ultimately show ?thesis
        using path_conforms_VVp[of "lhd P" p "lhd P'" \<sigma>] by (metis (no_types) LCons.prems(4) `\<not>lnull P'` lhd_LCons_ltl)
    next
      assume "lhd P \<notin> VV p"
      thus ?thesis using path_conforms_VVpstar using LCons.prems(5) v0 by auto
    qed
    thus ?thesis by (simp add: v0)
  next
    assume "\<not>lnull (ltl P)"
    hence *: "path_conforms_with_strategy p (lappend (ltl P) P') \<sigma>"
      by (metis LCons.hyps(3) LCons.prems(1) LCons.prems(2) LCons.prems(5) LCons.prems(6) assms(4) assms(5) lhd_LCons_ltl llast_LCons2 path_conforms_with_strategy_ltl)
    have "path_conforms_with_strategy p (LCons (lhd P) (lappend (ltl P) P')) \<sigma>" proof (cases)
      assume "lhd P \<in> VV p"
      moreover hence "lhd (ltl P) = \<sigma> (lhd P)"
        by (metis LCons.prems(1) LCons.prems(2) `\<not>lnull (ltl P)` lhd_LCons_ltl path_conforms_with_strategy_start)
      ultimately show ?thesis
        using path_conforms_VVp[of "lhd P" p "lhd (ltl P)" \<sigma>] * `\<not>lnull (ltl P)` by (metis lappend_code(2) lhd_LCons_ltl)
    next
      assume "lhd P \<notin> VV p"
      thus ?thesis by (simp add: "*" path_conforms_VVpstar)
    qed
    with `\<not>lnull P` show "path_conforms_with_strategy p (lappend P P') \<sigma>"
      by (metis lappend_code(2) lhd_LCons_ltl)
  qed
qed

lemma path_conforms_with_strategy_VVpstar:
  assumes "lset P \<subseteq> VV p**"
  shows "path_conforms_with_strategy p P \<sigma>"
using assms proof (coinduction arbitrary: P)
  case (path_conforms_with_strategy P)
  moreover have "\<And>v Ps. P = LCons v Ps \<Longrightarrow> ?case" using path_conforms_with_strategy by auto
  ultimately show ?case by (cases "P = LNil", simp) (metis lnull_def not_lnull_conv)
qed

(* strategy_attracts_from_to *)

lemma strategy_attracts_from_to_trivial [simp]: "strategy_attracts p \<sigma> W W"
  unfolding strategy_attracts_def strategy_attracts_via_def using lnull_0_llength zero_enat_def by fastforce

lemma strategy_attracts_from_to_empty [simp]: "strategy_attracts p \<sigma> {} W"
  unfolding strategy_attracts_def by simp

(* strategy_avoids *)

lemma strategy_avoids_trivial [simp]: "strategy_avoids p \<sigma> {} W"
  unfolding strategy_avoids_def by simp

primcorec greedy_conforming_path :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a Path" where
  "greedy_conforming_path p \<sigma> \<sigma>' v0 =
    LCons v0 (if deadend v0
      then LNil
      else if v0 \<in> VV p
        then greedy_conforming_path p \<sigma> \<sigma>' (\<sigma> v0)
        else greedy_conforming_path p \<sigma> \<sigma>' (\<sigma>' v0))"

lemma greedy_path_LNil [simp]: "greedy_conforming_path p \<sigma> \<sigma>' v0 \<noteq> LNil"
  using greedy_conforming_path.disc_iff llist.discI(1) by blast

lemma greedy_path_lhd: "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P \<Longrightarrow> v = v0"
  using greedy_conforming_path.code by auto

lemma greedy_path_deadend_v0: "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P \<Longrightarrow> P = LNil \<longleftrightarrow> deadend v0"
  by (metis (no_types, lifting) greedy_conforming_path.disc_iff greedy_conforming_path.simps(3) llist.disc(1) ltl_simps(2))
corollary greedy_path_deadend_v0': "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v LNil \<Longrightarrow> deadend v0"
  using greedy_path_deadend_v0 by blast

corollary greedy_path_deadend_v: "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P \<Longrightarrow> P = LNil \<longleftrightarrow> deadend v"
  using greedy_path_deadend_v0 greedy_path_lhd by metis
corollary greedy_path_deadend_v': "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v LNil \<Longrightarrow> deadend v"
  using greedy_path_deadend_v by blast
(* corollary greedy_path_deadend': "greedy_conforming_path p \<sigma> v0 = LCons v LNil \<Longrightarrow> deadend v"
  using greedy_path_deadend greedy_path_lhd by blast *)

lemma greedy_path_ltl:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P"
  shows "P = LNil \<or> P = greedy_conforming_path p \<sigma> \<sigma>' (\<sigma> v0) \<or> P = greedy_conforming_path p \<sigma> \<sigma>' (\<sigma>' v0)"
  apply (insert assms, frule greedy_path_lhd)
  apply (cases "deadend v0", simp add: greedy_conforming_path.code)
  by (metis (no_types, lifting) greedy_conforming_path.sel(2) ltl_simps(2))

lemma greedy_path_ltl_ex:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P"
  shows "P = LNil \<or> (\<exists>v. P = greedy_conforming_path p \<sigma> \<sigma>' v)"
  using assms greedy_path_ltl by blast

lemma greedy_path_ltl_VVp:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v0 P" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 = lhd P"
  using assms greedy_conforming_path.code by auto

lemma greedy_path_ltl_VVpstar:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v0 P" "v0 \<in> VV p**" "\<not>deadend v0"
  shows "\<sigma>' v0 = lhd P"
  using assms greedy_conforming_path.code by auto

theorem greedy_conforming_path_properties [simp]:
  assumes "v0 \<in> V" "strategy p \<sigma>" "strategy p** \<sigma>'"
  shows
    "\<not>lnull (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    "greedy_conforming_path p \<sigma> \<sigma>' v0 $ 0 = v0"
    "valid_path (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    "maximal_path (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    "path_conforms_with_strategy p (greedy_conforming_path p \<sigma> \<sigma>' v0) \<sigma>"
    "path_conforms_with_strategy p** (greedy_conforming_path p \<sigma> \<sigma>' v0) \<sigma>'"
proof-
  def [simp]: P \<equiv> "greedy_conforming_path p \<sigma> \<sigma>' v0"

  show "\<not>lnull P" "P $ 0 = v0" by (simp_all add: lnth_0_conv_lhd)

  {
    fix v0 assume "v0 \<in> V"
    let ?P = "greedy_conforming_path p \<sigma> \<sigma>' v0"
    assume asm: "\<not>(\<exists>v. ?P = LCons v LNil)"
    obtain P' where P': "?P = LCons v0 P'" by (metis greedy_path_LNil greedy_path_lhd neq_LNil_conv)
    hence "\<not>deadend v0" using asm greedy_path_deadend_v0 `v0 \<in> V` by blast
    from P' have 1: "\<not>lnull P'" using asm llist.collapse(1) `v0 \<in> V` greedy_path_deadend_v0 by blast
    moreover from P' `\<not>deadend v0` assms(2) assms(3) `v0 \<in> V`
      have 2: "v0\<rightarrow>lhd P'"
      unfolding strategy_def using greedy_path_ltl_VVp greedy_path_ltl_VVpstar by (cases "v0 \<in> VV p") auto
    moreover hence "lhd P' \<in> V" using edges_are_in_V by auto
    moreover have "\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V"
      by (metis P' calculation(1) calculation(3) greedy_conforming_path.simps(2) greedy_path_ltl_ex lnull_def)
    (* The conjunction of all the above *)
    ultimately
      have "\<exists>P'. ?P = LCons v0 P' \<and> \<not>lnull P' \<and> v0\<rightarrow>lhd P' \<and> lhd P' \<in> V \<and> (\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V)"
      using P' by blast
  } note coinduction_helper = this

  show "valid_path P" using assms unfolding P_def proof (coinduction arbitrary: v0)
    case (valid_path v0)
    from `v0 \<in> V` assms(2) assms(3) edges_are_in_V
      show ?case using coinduction_helper[of v0] greedy_path_lhd by metis
  qed

  show "maximal_path P" using assms unfolding P_def proof (coinduction arbitrary: v0)
    case (maximal_path v0)
    from `v0 \<in> V` assms(2) assms(3) edges_are_in_V
      show ?case using coinduction_helper[of v0] greedy_path_deadend_v' by blast
  qed

  {
    fix p'' \<sigma>'' assume p'': "(p'' = p \<and> \<sigma>'' = \<sigma>) \<or> (p'' = p** \<and> \<sigma>'' = \<sigma>')"
    moreover with assms have "strategy p'' \<sigma>''" by blast
    hence "path_conforms_with_strategy p'' P \<sigma>''" using `v0 \<in> V` unfolding P_def proof (coinduction arbitrary: v0)
      case (path_conforms_with_strategy v0)
      show ?case proof (cases "v0 \<in> VV p''")
        case True
        { assume "\<not>(\<exists>v. greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v LNil)"
          with `v0 \<in> V` obtain P' where
            P': "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v0 P'" "\<not>lnull P'" "v0\<rightarrow>lhd P'" "lhd P' \<in> V" "\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V"
            using coinduction_helper by blast
          with `v0 \<in> VV p''` p'' have "\<sigma>'' v0 = lhd P'"
            using greedy_path_ltl_VVp greedy_path_ltl_VVpstar by blast
          with `v0 \<in> VV p''` P'(1) P'(2) P'(5) have ?path_conforms_VVp
            using greedy_conforming_path.code path_conforms_with_strategy(1) by fastforce
        }
        thus ?thesis by auto
      next
        case False thus ?thesis using coinduction_helper[of v0] path_conforms_with_strategy by auto
      qed
    qed
  }
  thus "path_conforms_with_strategy p P \<sigma>" "path_conforms_with_strategy p** P \<sigma>'" by blast+
qed

corollary strategy_conforming_path_exists:
  assumes "v0 \<in> V" "strategy p \<sigma>" "strategy p** \<sigma>'"
  obtains P where
    "\<not>lnull P" "P $ 0 = v0" "valid_path P" "maximal_path P"
    "path_conforms_with_strategy p P \<sigma>" "path_conforms_with_strategy p** P \<sigma>'"
  using assms greedy_conforming_path_properties by metis

corollary strategy_conforming_path_exists_single:
  assumes "v0 \<in> V" "strategy p \<sigma>"
  obtains P where
    "\<not>lnull P" "P $ 0 = v0" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>"
  using assms strategy_conforming_path_exists[of v0 p \<sigma> \<sigma>_arbitrary] valid_arbitrary_strategy by metis

lemma attractor_strategy_on_extends: "\<lbrakk> strategy_attracts_via p \<sigma> v0 A W; A \<subseteq> A' \<rbrakk> \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A' W"
  unfolding strategy_attracts_via_def by blast

lemma strategy_attracts_via_trivial: "v0 \<in> W \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A W"
  unfolding strategy_attracts_via_def using zero_enat_def by (intro allI impI exI[of _ 0]) auto

lemma path_conforms_with_strategy_update_path:
  assumes \<sigma>: "strategy p \<sigma>" and \<sigma>': "strategy p \<sigma>'"
    and P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>"
    (* P is influenced by changing \<sigma> to \<sigma>'. *)
    and v: "v \<in> lset P" "v \<in> VV p" "\<not>deadend v" "\<sigma> v \<noteq> \<sigma>' v"
  shows "\<exists>P' n.
    \<not>lnull P' \<and> valid_path P' \<and> maximal_path P' \<and> path_conforms_with_strategy p P' \<sigma>'
    \<and> enat (Suc n) < llength P' \<and> enat (Suc n) < llength P
    \<and> ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P
    \<and> P $ n \<in> VV p \<and> \<not>deadend (P $ n)
    \<and> \<sigma> (P $ n) \<noteq> \<sigma>' (P $ n)"
proof-
  (* Determine the first index where P fails to follow \<sigma>'. *)
  def fail \<equiv> "\<lambda>P n. enat (Suc n) < llength P \<and> P $ n \<in> VV p \<and> \<not>deadend (P $ n) \<and> \<sigma>' (P $ n) \<noteq> P $ Suc n"
  hence "\<exists>n. fail P n" proof-
    from v(1) obtain n where n: "enat n < llength P" "P $ n = v" by (meson in_lset_conv_lnth)
    with v(3) `maximal_path P`
      have "enat (Suc n) < llength P" using maximal_path_impl1 by blast
    moreover from n(2) v(2)
      have "P $ n \<in> VV p" by simp
    moreover with P(4) `enat (Suc n) < llength P` n(2) v(4) assms(4)
      have "\<sigma>' (P $ n) \<noteq> P $ Suc n" using path_conforms_with_strategy_conforms by auto
    ultimately show ?thesis unfolding fail_def using n(2) v(3) by blast
  qed
  then obtain n where "fail P n" and n_min: "\<And>m. m < n \<Longrightarrow> \<not>fail P m" using obtain_min[of "\<lambda>n. fail P n"] by blast
  hence n: "enat (Suc n) < llength P" "P $ n \<in> VV p" "\<not>deadend (P $ n)" "\<sigma>' (P $ n) \<noteq> P $ Suc n" unfolding fail_def by blast+
  def P' \<equiv> "lappend (ltake (enat (Suc n)) P) (greedy_conforming_path p \<sigma>' \<sigma>_arbitrary (\<sigma>' (P $ n)))" (is "lappend ?A ?B")

  have "llength ?A = min (enat (Suc n)) (llength P)" using llength_ltake by blast
  with n(1) have "llength ?A = enat (Suc n)" by (simp add: min.strict_order_iff)

  from n(2) n(3) \<sigma>' have "\<sigma>' (P $ n) \<in> V" using valid_strategy_in_V by blast

  have "llast ?A = P $ n" proof-
    have "llast ?A = ?A $ n" using `llength ?A = enat (Suc n)` unfolding llast_def by simp
    moreover have "enat n < llength ?A" using `llength ?A = enat (Suc n)` by simp
    ultimately show ?thesis using lnth_lappend1[of n ?A ?B] by (simp add: lnth_ltake)
  qed

  from P(4) n(1) n(2) n(4) assms(4)
    have "\<sigma> (P $ n) \<noteq> \<sigma>' (P $ n)" using path_conforms_with_strategy_conforms by auto
  moreover have "\<not>lnull P'" unfolding P'_def by simp
  moreover have "enat (Suc n) < llength P'" unfolding P'_def using `llength ?A = enat (Suc n)` by simp
  moreover have "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P" unfolding P'_def using `llength ?A = enat (Suc n)`
    by (metis P'_def `enat (Suc n) < llength P'` llength_ltake lprefix_lappendD lprefix_llength_eq_imp_eq ltake_is_lprefix min.strict_order_iff)

  moreover have "valid_path P'" proof-
    have "lfinite ?A" "\<not>lnull ?B" by simp_all
    moreover have "valid_path ?A" using assms(4) path_prefix_valid by blast
    moreover from \<sigma>' `\<sigma>' (P $ n) \<in> V`
      have "valid_path ?B"
        using greedy_conforming_path_properties(3)[of "\<sigma>' (P $ n)" p \<sigma>' \<sigma>_arbitrary] valid_arbitrary_strategy by blast
    moreover have "llast ?A \<rightarrow> lhd ?B" proof-
      have "lhd ?B = \<sigma>' (P $ n)" by simp
      moreover from n(2) n(3) \<sigma>'
        have "P $ n \<rightarrow> \<sigma>' (P $ n)" using strategy_def by blast
      ultimately show ?thesis using `llast ?A = P $ n` by simp
    qed
    ultimately show ?thesis unfolding P'_def using valid_path_lappend[of ?A ?B] by blast
  qed

  moreover have "maximal_path P'" proof-
    have "\<not>lnull ?B" by simp
    moreover from \<sigma>' `\<sigma>' (P $ n) \<in> V`
      have "maximal_path ?B"
        using greedy_conforming_path_properties(4)[of "\<sigma>' (P $ n)" p \<sigma>' \<sigma>_arbitrary] valid_arbitrary_strategy by blast
    ultimately show ?thesis unfolding P'_def using maximal_path_lappend by blast
  qed

  moreover have "path_conforms_with_strategy p P' \<sigma>'" proof-
    have "lfinite ?A" "\<not>lnull ?B" by simp_all
    moreover have "\<not>lnull ?A" using assms(3) enat_0_iff(2) by auto
    moreover have "llast ?A \<in> VV p" by (simp add: `llast ?A = P $ n` n(2))
    moreover have "\<sigma>' (llast ?A) = lhd ?B" using `llast ?A = P $ n` by simp
    moreover have "path_conforms_with_strategy p ?A \<sigma>'" proof-
      have "path_prefix ?A P" by simp
      moreover from `valid_path P` `\<not>lnull P` `path_conforms_with_strategy p P \<sigma>` n n_min have "path_conforms_with_strategy p ?A \<sigma>'"
      proof (induct n arbitrary: P)
        case 0
        have "ltake (enat (Suc 0)) P = LCons (lhd P) LNil" by (simp add: "0.prems"(2) lnth_0_conv_lhd lnull_0_llength ltake.ctr(1) ltake_Suc_conv_snoc_lnth zero_enat_def)
        thus ?case by (simp add: path_conforms_LCons_LNil)
      next
        case (Suc n P)
        from Suc.prems(1) have "valid_path (ltl P)" by (simp add: valid_path_ltl)
        moreover from Suc.prems(4) have "\<not>lnull (ltl P)" using enat_Suc_ltl by force
        moreover from Suc.prems(3) have "path_conforms_with_strategy p (ltl P) \<sigma>" by (simp add: path_conforms_with_strategy_ltl)
        moreover from Suc.prems(4) have "enat (Suc n) < llength (ltl P)" using enat_Suc_ltl by blast
        moreover from Suc.prems(5) have "ltl P $ n \<in> VV p" by (simp add: Suc.prems(2) lnth_ltl)
        moreover from Suc.prems(6) have "\<not>deadend (ltl P $ n)" by (simp add: Suc.prems(2) lnth_ltl)
        moreover have "\<sigma>' (ltl P $ n) \<noteq> ltl P $ Suc n" by (simp add: Suc.prems(2) Suc.prems(7) lnth_ltl)
        moreover have "\<And>m. m < n \<Longrightarrow> \<not>fail (ltl P) m" proof-
          fix m assume "m < n"
          hence "\<not>fail P (Suc m)" by (simp add: Suc.prems(8))
          hence *: "\<lbrakk> enat (Suc (Suc m)) < llength P;
              P $ Suc m \<in> VV p;
              \<not>deadend (P $ Suc m) \<rbrakk> \<Longrightarrow>
              \<sigma>' (P $ Suc m) = P $ Suc (Suc m)" unfolding fail_def by blast
          {
            assume **: "enat (Suc m) < llength (ltl P)"
              "ltl P $ m \<in> VV p"
              "\<not>deadend (ltl P $ m)"
            have A: "ltl P $ m = P $ Suc m" by (simp add: Suc.prems(2) lnth_ltl)
            from **(1) have "enat (Suc (Suc m)) < llength P" using enat_ltl_Suc by blast
            moreover from **(2) have "P $ Suc m \<in> VV p" by (simp add: A)
            moreover from **(3) have "\<not>deadend (P $ Suc m)" by (simp add: A)
            ultimately have "\<sigma>' (P $ Suc m) = P $ Suc (Suc m)" using * by blast
            hence "\<sigma>' (ltl P $ m) = ltl P $ Suc m" by (simp add: A Suc.prems(2) lnth_ltl)
          }
          thus "\<not>fail (ltl P) m" unfolding fail_def by blast
        qed
        ultimately have *: "path_conforms_with_strategy p (ltake (enat (Suc n)) (ltl P)) \<sigma>'" using Suc.hyps[of "ltl P"] by blast
        have "path_conforms_with_strategy p (LCons (lhd P) (ltake (enat (Suc n)) (ltl P))) \<sigma>'" proof (cases)
          assume "lhd P \<in> VV p"
          hence "lhd (ltl P) = \<sigma> (lhd P)" by (metis Suc.prems(2) Suc.prems(3) `\<not>lnull (ltl P)` lhd_LCons_ltl path_conforms_with_strategy_start)
          have "\<not>deadend (lhd P)" by (metis Suc.prems(1) Suc.prems(2) `\<not>lnull (ltl P)` eq_LConsD lnull_def valid_path.cases)
          moreover have "enat (Suc 0) < llength P" using `\<not>lnull (ltl P)` enat_ltl_Suc lnull_0_llength by blast
          moreover have "\<not>fail P 0" by (simp add: Suc.prems(8))
          ultimately have "\<sigma>' (P $ 0) = P $ Suc 0" unfolding fail_def by (metis Suc.prems(2) `lhd P \<in> VV p` lhd_LCons_ltl lnth_0)
          with `lhd (ltl P) = \<sigma> (lhd P)`
            have "\<sigma>' (P $ 0) = \<sigma> (P $ 0)" by (metis Suc.prems(2) `\<not>lnull (ltl P)` lnth_0_conv_lhd lnth_ltl)
          with `lhd (ltl P) = \<sigma> (lhd P)`
            have 1: "lhd (ltl P) = \<sigma>' (lhd P)" by (simp add: Suc.prems(2) lhd_conv_lnth)
          obtain w Ps where w: "ltake (enat (Suc n)) (ltl P) = LCons w Ps"
            by (metis `\<not>lnull (ltl P)` enat_ord_simps(2) lessI less_irrefl lhd_LCons_ltl lnull_ltake min_enat_simps(2) min_less_iff_conj)
          moreover from w have "path_conforms_with_strategy p (LCons w Ps) \<sigma>'" using * by simp
          moreover from w 1 have "w = \<sigma>' (lhd P)" by (metis `\<not>lnull (ltl P)` enat_ord_simps(2) lnth_0 lnth_0_conv_lhd lnth_ltake zero_less_Suc)
          ultimately show ?thesis using path_conforms_VVp[of "lhd P" p w \<sigma>' Ps] `lhd P \<in> VV p` by force
        next
          assume "lhd P \<notin> VV p"
          thus ?thesis by (simp add: `path_conforms_with_strategy p (ltake (enat (Suc n)) (ltl P)) \<sigma>'` path_conforms_VVpstar)
        qed
        moreover have "LCons (lhd P) (ltake (enat (Suc n)) (ltl P)) = ltake (eSuc (enat (Suc n))) P" by (metis Suc.prems(2) lhd_LCons_ltl ltake_eSuc_LCons)
        ultimately show "path_conforms_with_strategy p (ltake (enat (Suc (Suc n))) P) \<sigma>'" by (simp add: eSuc_enat)
      qed
      ultimately show ?thesis using path_conforms_with_strategy_prefix by blast
    qed
    moreover from \<sigma>' `\<sigma>' (P $ n) \<in> V`
      have "path_conforms_with_strategy p ?B \<sigma>'"
        using greedy_conforming_path_properties(5)[of "\<sigma>' (P $ n)" p \<sigma>' \<sigma>_arbitrary] valid_arbitrary_strategy by blast
    ultimately show ?thesis unfolding P'_def using path_conforms_with_strategy_lappend by blast
  qed

  ultimately show ?thesis using n by blast
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

end -- "context ParityGame"

end
