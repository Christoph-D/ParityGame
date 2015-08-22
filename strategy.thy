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

(*
lemma path_conforms_with_strategy_maximally_start:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and "P $ 0 = v0" "v0 \<in> VV p" "\<sigma> v0 = Some w"
    and "\<not>lnull P"
  shows "enat (Suc 0) < llength P \<and> \<sigma> v0 = Some (P $ Suc 0)"
proof-
  have *: "P $ 0 \<in> VV p \<and> \<sigma> (P $ 0) = Some w" by (simp add: assms(2) assms(3) assms(4))
  { assume "path_conforms_with_strategy p P \<sigma>"
    moreover have "enat 0 < llength P" using `\<not>lnull P` zero_enat_def by auto
    ultimately have "enat (Suc 0) < llength P \<and> P $ Suc 0 = w" using * path_conforms_with_strategy_def by blast
    hence ?thesis using assms(4) by blast
  }
  moreover
  { assume "\<exists>n v. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat (Suc n) = llength P \<and> P $ n = v \<and> v \<in> VV p \<and> \<sigma> v = None"
    then obtain n v where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "enat (Suc n) = llength P" "P $ n = v" "v \<in> VV p" "\<sigma> v = None" by blast
    have ?thesis proof (cases)
      assume "n = 0"
      thus ?thesis using assms(2) assms(4) n_def(2) n_def(3) n_def(5) by auto
    next
      assume "n \<noteq> 0"
      hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" using n_def(1) by simp
      hence "enat (Suc 0) < llength P \<and> P $ Suc 0 = w" unfolding path_conforms_with_strategy_up_to_def using * `\<not>lnull P` zero_enat_def by auto
      thus ?thesis using assms(4) by blast
    qed
  }
  ultimately show ?thesis using assms(1) path_conforms_with_strategy_maximally_def by blast
qed

lemma path_conforms_with_strategy_maximally_start_VVpstar:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and P: "P $ 0 \<in> VV p**" "\<not>deadend (P $ 0)" "\<not>lnull P"
  shows "enat (Suc 0) < llength P"
proof-
  have "P $ 0 \<notin> VV p \<and> enat 0 < llength P" using P(1) P(3) zero_enat_def by auto
  thus ?thesis using path_conforms_with_strategy_maximally_def assms(1) P(2) by metis
qed

lemma maximal_path_conforms_maximally:
  assumes P_conforms: "path_conforms_with_strategy p P \<sigma>"
    and P_maximal: "maximal_path P"
  shows "path_conforms_with_strategy_maximally p P \<sigma>"
proof-
  { fix i assume "enat i < llength P" "\<not>deadend (P $ i)"
    with P_maximal have "enat (Suc i) < llength P" using maximal_path_impl1 by blast
  }
  with P_conforms show ?thesis unfolding path_conforms_with_strategy_maximally_def by blast
qed *)

(*
lemma valid_strategy_none_on_VVpstar: "valid_strategy p \<sigma> \<Longrightarrow> v \<notin> VV p \<Longrightarrow> \<sigma> v = None" by (metis not_None_eq valid_strategy_def)
lemma valid_strategy_none_on_VVpstar2: "valid_strategy p \<sigma> \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<sigma> v = None" by (metis DiffD2 Player.distinct(1) valid_strategy_none_on_VVpstar)
lemma valid_strategy_none_on_deadends: "valid_strategy p \<sigma> \<Longrightarrow> deadend v \<Longrightarrow> \<sigma> v = None" by (meson edges_are_in_V not_Some_eq valid_strategy_def)
lemma valid_empty_strategy: "valid_strategy p (\<lambda>_. None)" using valid_strategy_def by simp
*)

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

lemma path_conforms_with_strategy_irrelevant':
  assumes "path_conforms_with_strategy p P (\<sigma>(v := w))" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P \<sigma>"
  by (metis assms fun_upd_triv fun_upd_upd path_conforms_with_strategy_irrelevant)

lemma path_conforms_with_strategy_start:
  "path_conforms_with_strategy p (LCons v (LCons w P)) \<sigma> \<Longrightarrow> v \<in> VV p \<Longrightarrow> \<sigma> v = w"
  by (drule path_conforms_with_strategy.cases) simp_all

(* strategy_attracts_from_to *)

lemma strategy_attracts_irrelevant:
  assumes "strategy_attracts p \<sigma> A W" "v \<notin> A" "strategy p \<sigma>"
  shows "strategy_attracts p (\<sigma>(v := w)) A W" proof-
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P (\<sigma>(v := w))" "P $ 0 \<in> A"
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A" proof (cases)
      assume "v \<in> lset P"
      then obtain n where n: "enat n < llength P" "P $ n = v" by (meson in_lset_conv_lnth)
      (* obtain the minimal n, etc. *)
      show ?thesis sorry
    next
      assume "v \<notin> lset P"
      with P(4) have "path_conforms_with_strategy p P \<sigma>" using path_conforms_with_strategy_irrelevant' by blast
      with P(1) P(2) P(3) P(5) assms(1) show ?thesis unfolding strategy_attracts_def strategy_attracts_via_def by blast
    qed
  }
  thus ?thesis unfolding strategy_attracts_def strategy_attracts_via_def by blast
qed

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

theorem strategy_conforming_path_exists:
  assumes "v0 \<in> V" "strategy p \<sigma>" "strategy p** \<sigma>'"
  obtains P where
    "\<not>lnull P" "P $ 0 = v0" "valid_path P" "maximal_path P"
    "path_conforms_with_strategy p P \<sigma>" "path_conforms_with_strategy p** P \<sigma>'"
proof
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
  sorry

end -- "context ParityGame"

end
