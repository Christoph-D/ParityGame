theory strategy
imports
  Main
  parity_game
begin

type_synonym 'a Strategy = "'a \<Rightarrow> 'a"

(* A strategy for player p is a function on VV p assigning a successor to each node. *)
definition (in ParityGame) strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> v\<rightarrow>\<sigma> v"

(* If path_conforms_with_strategy p P \<sigma> is True, then we call P a \<sigma>-path.
This means that P follows \<sigma> on all nodes of player p except maybe the last node on the path. *)
coinductive (in ParityGame) path_conforms_with_strategy
  :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  path_conforms_LNil:  "path_conforms_with_strategy p LNil \<sigma>"
| path_conforms_LCons_LNil: "path_conforms_with_strategy p (LCons v LNil) \<sigma>"
| path_conforms_VVp: "\<lbrakk> v \<in> VV p; w = \<sigma> v; path_conforms_with_strategy p (LCons w Ps) \<sigma> \<rbrakk>
    \<Longrightarrow> path_conforms_with_strategy p (LCons v (LCons w Ps)) \<sigma>"
| path_conforms_VVpstar: "\<lbrakk> v \<notin> VV p; path_conforms_with_strategy p Ps \<sigma> \<rbrakk>
    \<Longrightarrow> path_conforms_with_strategy p (LCons v Ps) \<sigma>"

(* A valid maximal path that conforms to a strategy *)
locale vmc_path = vm_path +
  fixes p \<sigma> assumes P_conforms [simp]: "path_conforms_with_strategy p P \<sigma>"
lemma (in vmc_path) vmc_path [simp]: "vmc_path G P v0 p \<sigma>" by unfold_locales

(* A valid maximal path that conforms to two strategies *)
locale vmc2_path = comp: vmc_path G P v0 "p**" \<sigma>' + vmc_path G P v0 p \<sigma>
  for G P v0 p \<sigma> \<sigma>'
lemma (in vmc2_path) vmc2_path [simp]: "vmc2_path G P v0 p \<sigma> \<sigma>'" by unfold_locales

context ParityGame begin

(* An arbitrary strategy.  Useful to define other strategies. *)
definition "\<sigma>_arbitrary \<equiv> \<lambda>v. SOME w. v\<rightarrow>w"

lemma valid_arbitrary_strategy [simp]: "strategy p \<sigma>_arbitrary" proof-
  { fix v assume "\<not>deadend v"
    hence "v \<rightarrow> \<sigma>_arbitrary v" unfolding \<sigma>_arbitrary_def using someI_ex[of "\<lambda>w. v\<rightarrow>w"] by blast
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

lemma path_conforms_with_strategy_ltl [intro]:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ltl P) \<sigma>"
  by (drule path_conforms_with_strategy.cases) (simp_all add: path_conforms_with_strategy.intros(1))

lemma path_conforms_with_strategy_drop:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ldropn n P) \<sigma>"
  by (simp add: path_conforms_with_strategy_ltl ltl_ldrop[of "\<lambda>P. path_conforms_with_strategy p P \<sigma>"])

lemma path_conforms_with_strategy_prefix:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> lprefix P' P \<Longrightarrow> path_conforms_with_strategy p P' \<sigma>"
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
      hence "\<exists>Q. P' = LCons v (LCons w Q)"
        by (metis local.path_conforms_VVp(1) lprefix_LCons_conv path_conforms_with_strategy(2))
      thus ?thesis using local.path_conforms_VVp(1,3,4) path_conforms_with_strategy(2) by force
    qed
  next
    case (path_conforms_VVpstar v)
    thus ?thesis proof (cases "P' = LNil", simp)
      case False
      hence "\<exists>Q. P' = LCons v Q"
        using local.path_conforms_VVpstar(1) lprefix_LCons_conv path_conforms_with_strategy(2) by fastforce
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
    case (path_conforms_VVp v' w Ps)
    have "w = ?\<sigma> v'" proof-
      from `valid_path P` have "\<not>deadend v'"
        using local.path_conforms_VVp(1) valid_path_cons_simp by blast
      with assms(2) have "v' \<noteq> v" using local.path_conforms_VVp(2) by blast
      thus "w = ?\<sigma> v'" by (simp add: local.path_conforms_VVp(3))
    qed
    moreover
      have "\<exists>P. LCons w Ps = P \<and> path_conforms_with_strategy p P \<sigma> \<and> (deadend v \<or> v \<notin> VV p) \<and> valid_path P"
    proof-
      have "valid_path (LCons w Ps)"
        using local.path_conforms_VVp(1) path_conforms_with_strategy(3) valid_path_ltl' by blast
      thus ?thesis using local.path_conforms_VVp(4) path_conforms_with_strategy(2) by blast
    qed
    ultimately show ?thesis using local.path_conforms_VVp(1,2) by blast
  next
    case (path_conforms_VVpstar v' Ps)
    have "\<exists>P. path_conforms_with_strategy p Ps \<sigma> \<and> (deadend v \<or> v \<notin> VV p) \<and> valid_path Ps"
      using local.path_conforms_VVpstar(1,3) path_conforms_with_strategy(2,3) valid_path_ltl' by blast
    thus ?thesis by (simp add: local.path_conforms_VVpstar(1,2))
  qed simp_all
qed

lemma path_conforms_with_strategy_irrelevant_updates:
  assumes "path_conforms_with_strategy p P \<sigma>" "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma> v = \<sigma>' v"
  shows "path_conforms_with_strategy p P \<sigma>'"
using assms proof (coinduction arbitrary: P)
  case (path_conforms_with_strategy P)
  thus ?case proof (cases rule: path_conforms_with_strategy.cases)
    case (path_conforms_VVp v' w Ps)
    have "w = \<sigma>' v'" using local.path_conforms_VVp(1,3) path_conforms_with_strategy(2) by auto
    thus ?thesis using local.path_conforms_VVp(1,4) path_conforms_with_strategy(2) by auto
  qed simp_all
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

lemma path_conforms_with_strategy_lappend:
  assumes
    P: "lfinite P" "\<not>lnull P" "path_conforms_with_strategy p P \<sigma>"
    and P': "\<not>lnull P'" "path_conforms_with_strategy p P' \<sigma>"
    and conforms: "llast P \<in> VV p \<Longrightarrow> \<sigma> (llast P) = lhd P'"
  shows "path_conforms_with_strategy p (lappend P P') \<sigma>"
using assms proof (induct P rule: lfinite_induct, simp)
  case (LCons P)
  show ?case proof (cases)
    assume "lnull (ltl P)"
    then obtain v0 where v0: "P = LCons v0 LNil"
      by (metis LCons.prems(1) lhd_LCons_ltl llist.collapse(1))
    have "path_conforms_with_strategy p (LCons (lhd P) P') \<sigma>" proof (cases)
      assume "lhd P \<in> VV p"
      moreover with v0 have "lhd P' = \<sigma> (lhd P)"
        using LCons.prems(5) by auto
      ultimately show ?thesis
        using path_conforms_VVp[of "lhd P" p "lhd P'" \<sigma>]
        by (metis (no_types) LCons.prems(4) `\<not>lnull P'` lhd_LCons_ltl)
    next
      assume "lhd P \<notin> VV p"
      thus ?thesis using path_conforms_VVpstar using LCons.prems(4) v0 by blast
    qed
    thus ?thesis by (simp add: v0)
  next
    assume "\<not>lnull (ltl P)"
    hence *: "path_conforms_with_strategy p (lappend (ltl P) P') \<sigma>"
      by (metis LCons.hyps(3) LCons.prems(1) LCons.prems(2) LCons.prems(5) LCons.prems(5)
                assms(4) assms(5) lhd_LCons_ltl llast_LCons2 path_conforms_with_strategy_ltl)
    have "path_conforms_with_strategy p (LCons (lhd P) (lappend (ltl P) P')) \<sigma>" proof (cases)
      assume "lhd P \<in> VV p"
      moreover hence "lhd (ltl P) = \<sigma> (lhd P)"
        by (metis LCons.prems(1) LCons.prems(2) `\<not>lnull (ltl P)`
                  lhd_LCons_ltl path_conforms_with_strategy_start)
      ultimately show ?thesis
        using path_conforms_VVp[of "lhd P" p "lhd (ltl P)" \<sigma>] * `\<not>lnull (ltl P)`
        by (metis lappend_code(2) lhd_LCons_ltl)
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

lemma subgame_path_conforms_with_strategy:
  assumes V': "V' \<subseteq> V" and P: "path_conforms_with_strategy p P \<sigma>" "lset P \<subseteq> V'"
  shows "ParityGame.path_conforms_with_strategy (subgame V') p P \<sigma>"
proof-
  have "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) V' by auto
  with P(1) show ?thesis
    by (coinduction arbitrary: P rule: ParityGame.path_conforms_with_strategy.coinduct[OF subgame_ParityGame])
       (cases rule: path_conforms_with_strategy.cases, auto)
qed

lemma (in vmc_path) subgame_path_vmc_path:
  assumes V': "V' \<subseteq> V" and P: "lset P \<subseteq> V'"
  shows "vmc_path (subgame V') P v0 p \<sigma>"
proof-
  interpret G': ParityGame "subgame V'" using subgame_ParityGame by blast
  show ?thesis proof
    show "G'.valid_path P" using subgame_valid_path P_valid P by blast
    show "G'.maximal_path P" using subgame_maximal_path V' P_maximal P by blast
    show "G'.path_conforms_with_strategy p P \<sigma>"
      using subgame_path_conforms_with_strategy V' P_conforms P by blast
  qed simp_all
qed

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
        greedy_path_not_null:  "\<not>lnull (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    and greedy_path_v0:        "greedy_conforming_path p \<sigma> \<sigma>' v0 $ 0 = v0"
    and greedy_path_valid:     "valid_path (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    and greedy_path_maximal:   "maximal_path (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    and greedy_path_conforms:  "path_conforms_with_strategy p (greedy_conforming_path p \<sigma> \<sigma>' v0) \<sigma>"
    and greedy_path_conforms': "path_conforms_with_strategy p** (greedy_conforming_path p \<sigma> \<sigma>' v0) \<sigma>'"
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
    moreover hence "lhd P' \<in> V" by blast
    moreover hence "\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V"
      by (metis P' calculation(1) greedy_conforming_path.simps(2) greedy_path_ltl_ex lnull_def)
    (* The conjunction of all the above *)
    ultimately
      have "\<exists>P'. ?P = LCons v0 P' \<and> \<not>lnull P' \<and> v0\<rightarrow>lhd P' \<and> lhd P' \<in> V \<and> (\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V)"
      using P' by blast
  } note coinduction_helper = this

  show "valid_path P" using assms unfolding P_def proof (coinduction arbitrary: v0)
    case (valid_path v0)
    from `v0 \<in> V` assms(2,3) show ?case using coinduction_helper[of v0] greedy_path_lhd by blast
  qed

  show "maximal_path P" using assms unfolding P_def proof (coinduction arbitrary: v0)
    case (maximal_path v0)
    from `v0 \<in> V` assms(2,3) show ?case using coinduction_helper[of v0] greedy_path_deadend_v' by blast
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
          with `v0 \<in> VV p''` P'(1,2,5) have ?path_conforms_VVp
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
  obtains P where "vmc2_path G P v0 p \<sigma> \<sigma>'"
proof
  show "vmc2_path G (greedy_conforming_path p \<sigma> \<sigma>' v0) v0 p \<sigma> \<sigma>'"
    using assms by unfold_locales simp_all
qed

corollary strategy_conforming_path_exists_single:
  assumes "v0 \<in> V" "strategy p \<sigma>"
  obtains P where "vmc_path G P v0 p \<sigma>"
proof
  show "vmc_path G (greedy_conforming_path p \<sigma> \<sigma>_arbitrary v0) v0 p \<sigma>"
    using assms by unfold_locales simp_all
qed

end

context vmc_path begin
lemma Ptl_conforms [simp]: "path_conforms_with_strategy p (ltl P) \<sigma>"
  using P_conforms path_conforms_with_strategy_ltl by blast
lemma Pdrop_conforms [simp]: "path_conforms_with_strategy p (ldropn n P) \<sigma>"
  using P_conforms path_conforms_with_strategy_drop by blast
lemma prefix_conforms [simp]: "path_conforms_with_strategy p (ltake n P) \<sigma>"
  using P_conforms path_conforms_with_strategy_prefix by blast
lemma extension_conforms [simp]:
  "(v' \<in> VV p \<Longrightarrow> \<sigma> v' = v0) \<Longrightarrow> path_conforms_with_strategy p (LCons v' P) \<sigma>"
  by (metis P_LCons P_conforms path_conforms_VVp path_conforms_VVpstar)

lemma extension_valid_maximal_conforming:
  assumes "v'\<rightarrow>v0" "v' \<in> VV p \<Longrightarrow> \<sigma> v' = v0"
  shows "vmc_path G (LCons v' P) v' p \<sigma>"
  using assms by unfold_locales simp_all

lemma vmc_path_ldropn:
  assumes "enat n < llength P"
  shows "vmc_path G (ldropn n P) (P $ n) p \<sigma>"
  using assms by unfold_locales (simp_all add: lhd_ldropn)

lemma conforms_to_another_strategy:
  "path_conforms_with_strategy p P \<sigma>' \<Longrightarrow> vmc_path G P v0 p \<sigma>'"
  using P_not_null P_valid P_maximal P_v0 by unfold_locales blast+
end

lemma (in ParityGame) valid_maximal_conforming_path_0:
  assumes "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>"
  shows "vmc_path G P (P $ 0) p \<sigma>"
  using assms by unfold_locales (simp_all add: lnth_0_conv_lhd)

locale vmc_path_no_deadend = vmc_path +
  assumes v0_no_deadend [simp]: "\<not>deadend v0"
begin
lemma vmc_path_no_deadend [simp]: "vmc_path_no_deadend G P v0 p \<sigma>" by unfold_locales
definition "w0 \<equiv> lhd (ltl P)"

lemma Ptl_not_null [simp]: "\<not>lnull (ltl P)"
  using P_LCons P_maximal maximal_no_deadend v0_no_deadend by metis
lemma Ptl_LCons: "ltl P = LCons w0 (ltl (ltl P))" unfolding w0_def by simp
lemma P_LCons': "P = LCons v0 (LCons w0 (ltl (ltl P)))" using P_LCons Ptl_LCons by simp
lemma v0_edge_w0 [simp]: "v0\<rightarrow>w0" using P_valid P_LCons' by (metis valid_path_edges')

lemma Ptl_0: "ltl P $ 0 = lhd (ltl P)" by (simp add: lhd_conv_lnth)
lemma P_Suc_0: "P $ Suc 0 = w0" by (simp add: P_lnth_Suc Ptl_0 w0_def)
lemma Ptl_edge [simp]: "v0 \<rightarrow> lhd (ltl P)" by (metis P_LCons' P_valid valid_path_edges' w0_def)

lemma v0_conforms: "v0 \<in> VV p \<Longrightarrow> \<sigma> v0 = w0"
  using path_conforms_with_strategy_start by (metis P_LCons' P_conforms)

lemma w0_V [simp]: "w0 \<in> V" by (metis Ptl_LCons Ptl_valid valid_path_cons_simp)
lemma w0_lset_P [simp]: "w0 \<in> lset P" by (metis P_LCons' lset_intros(1) lset_intros(2))
lemma w0_VV: "w0 \<in> VV p \<or> w0 \<in> VV p**" by simp

lemma vmc_path_ltl [simp]: "vmc_path G (ltl P) w0 p \<sigma>" by (unfold_locales) (simp_all add: w0_def)
end

lemma (in vmc_path) vmc_path_llength_no_deadend:
  assumes "enat (Suc n) < llength P"
  shows "vmc_path_no_deadend G P v0 p \<sigma>"
  using assms P_0 P_no_deadends
  by (unfold_locales)
     (metis enat_Suc_ltl enat_ltl_Suc ldropn_Suc_conv_ldropn ldropn_lnull llist.distinct(1) lnull_0_llength)

lemma (in vmc_path) vmc_path_lnull_ltl_no_deadend:
  assumes "\<not>lnull (ltl P)"
  shows "vmc_path_no_deadend G P v0 p \<sigma>"
  using assms P_0 P_no_deadends
  by (unfold_locales) (metis enat_ltl_Suc lnull_0_llength)

lemma (in vmc_path) valid_maximal_conforming_lappend:
  assumes "enat (Suc n) < llength P" "vmc_path G P' (P $ n) p \<sigma>"
  shows "vmc_path G (lappend (ltake (enat (Suc n)) P) (ltl P')) v0 p \<sigma>"
proof (unfold_locales)
  let ?A = "ltake (enat (Suc n)) P"
  let ?P = "lappend ?A (ltl P')"
  have len_Suc_P: "llength ?A = enat (Suc n)"
    using assms(1) llength_ltake' by blast
  hence "enat (Suc n) \<le> llength ?P" by simp
  thus "\<not>lnull ?P" using Suc_ile_eq by auto
  interpret P': vmc_path G P' "P $ n" p \<sigma> using assms(2) .
  have "\<not>deadend (P $ n)" using P_no_deadends assms(1) by blast
  then interpret P': vmc_path_no_deadend G P' "P $ n" p \<sigma> by unfold_locales
  show "valid_path ?P" using valid_path_lappend llast_ltake[OF assms(1)] by simp
  show "maximal_path ?P" using maximal_path_lappend by simp
  show "path_conforms_with_strategy p (lappend ?A (ltl P')) \<sigma>" proof-
    have "\<not>lnull ?A" by (metis P_not_null enat_ord_simps(2) lessI lnull_ltake not_iless0)
    thus ?thesis
      using path_conforms_with_strategy_lappend[of ?A]
      by (simp add: P'.v0_conforms P'.w0_def llast_ltake[OF assms(1)])
  qed
  show "lhd (lappend ?A (ltl P')) = v0"
    by (metis P_v0 Suc_ile_eq len_Suc_P dual_order.irrefl enat_ltl_Suc lappend_ltake_enat_ldropn
              lhd_lappend llist.expand lnull_ltlI order_refl)
qed

lemma (in vmc_path) vmc_path_conforms:
  assumes "enat (Suc n) < llength P" "P $ n \<in> VV p"
  shows "\<sigma> (P $ n) = P $ Suc n"
proof-
  def P' \<equiv> "ldropn n P"
  then interpret P': vmc_path G P' "P $ n" p \<sigma> using vmc_path_ldropn assms(1) Suc_llength by blast
  have "\<not>deadend (P $ n)" using assms(1) P_no_deadends by blast
  then interpret P': vmc_path_no_deadend G P' "P $ n" p \<sigma> by unfold_locales
  have "\<sigma> (P $ n) = P'.w0" using P'.v0_conforms assms(2) by blast
  thus ?thesis using P'_def P'.P_Suc_0 assms(1) by simp
qed

end