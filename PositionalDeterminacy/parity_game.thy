section {* Parity Games *}

theory parity_game
imports
  Main
  More_Coinductive_List
begin

subsection {* Basic definitions *}

text {* @{typ "'a"} is the vertex type.  Edges are pairs of vertices. *}
type_synonym 'a Edge = "'a \<times> 'a"

text {* A path is a possibly infinite list of vertices. *}
type_synonym 'a Path = "'a llist"

subsection {* Graphs *}

text {*
  We define graphs as a locale over a record.
  The record contains vertices and edges, the locale adds the assumption that the edges are pairs
  of vertices.
*}

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

locale Digraph =
  fixes G (structure)
  assumes valid_edge_set: "E \<subseteq> V \<times> V"
begin
text {*
  When we define a locale, we usually add a simplification lemma of the same name.
  Otherwise @{term "Digraph G"} would not easily be available in proofs, although here the proof
  is trivial.
*}
lemma Digraph [simp]: "Digraph G" by unfold_locales

lemma edges_are_in_V [intro]: "v\<rightarrow>w \<Longrightarrow> v \<in> V" "v\<rightarrow>w \<Longrightarrow> w \<in> V" using valid_edge_set by blast+

abbreviation deadend :: "'a \<Rightarrow> bool" where "deadend v \<equiv> \<not>(\<exists>w \<in> V. v \<rightarrow> w)"

subsection {* Valid paths *}

text {*
  We say that a path is \emph{valid} if it is empty or if it starts in @{term V} and walks along edges.
*}
coinductive valid_path :: "'a Path \<Rightarrow> bool" where
  valid_path_base: "valid_path LNil"
| valid_path_base': "v \<in> V \<Longrightarrow> valid_path (LCons v LNil)"
| valid_path_cons: "\<lbrakk> v \<in> V; w \<in> V; v\<rightarrow>w; valid_path Ps; \<not>lnull Ps; lhd Ps = w \<rbrakk> \<Longrightarrow> valid_path (LCons v Ps)"

inductive_simps valid_path_cons_simp: "valid_path (LCons x xs)"

lemma valid_path_ltl': "valid_path (LCons v Ps) \<Longrightarrow> valid_path Ps"
  using valid_path.simps by blast
lemma valid_path_ltl: "valid_path P \<Longrightarrow> valid_path (ltl P)"
  by (metis llist.exhaust_sel ltl_simps(1) valid_path_ltl')
lemma valid_path_drop: "valid_path P \<Longrightarrow> valid_path (ldropn n P)"
  by (simp add: valid_path_ltl ltl_ldrop)

lemma valid_path_in_V: assumes "valid_path P" shows "lset P \<subseteq> V" proof
  fix x assume "x \<in> lset P" thus "x \<in> V"
    using assms by (induct rule: llist.set_induct) (auto intro: valid_path.cases)
qed
lemma valid_path_finite_in_V: "\<lbrakk> valid_path P; enat i < llength P \<rbrakk> \<Longrightarrow> P $ i \<in> V"
  using valid_path_in_V lset_lnth_member by blast

lemma valid_path_edges': "valid_path (LCons v (LCons w Ps)) \<Longrightarrow> v\<rightarrow>w"
  using valid_path.cases by fastforce
lemma valid_path_edges:
  assumes "valid_path P" "enat (Suc n) < llength P"
  shows "P $ n \<rightarrow> P $ Suc n"
proof-
  def P' \<equiv> "ldropn n P"
  have "enat n < llength P" using assms(2) enat_ord_simps(2) less_trans by blast
  hence "P' $ 0 = P $ n" by (simp add: P'_def)
  moreover have "P' $ Suc 0 = P $ Suc n"
    by (metis One_nat_def P'_def Suc_eq_plus1 add.commute assms(2) lnth_ldropn)
  ultimately have "\<exists>Ps. P' = LCons (P $ n) (LCons (P $ Suc n) Ps)"
    by (metis P'_def `enat n < llength P` assms(2) ldropn_Suc_conv_ldropn)
  moreover have "valid_path P'" by (simp add: P'_def assms(1) valid_path_drop)
  ultimately show ?thesis using valid_path_edges' by blast
qed

lemma valid_path_impl1:
lemma valid_path_coinduct [consumes 1, case_names base step]:
  assumes major: "Q P"
    and head: "\<And>v P. Q (LCons v LNil) \<Longrightarrow> v \<in> V"
    and step: "\<And>v w P. Q (LCons v (LCons w P)) \<Longrightarrow> v\<rightarrow>w \<and> (Q (LCons w P) \<or> valid_path (LCons w P))"
  shows "valid_path P"
using major proof (coinduction arbitrary: P rule: valid_path.coinduct)
  case valid_path
  { assume "P \<noteq> LNil"
    then obtain v P' where P': "P = LCons v P'" by (meson neq_LNil_conv)
    assume "\<not>(\<exists>v. P = LCons v LNil \<and> v \<in> V)"
    hence "P' \<noteq> LNil" using head valid_path P' by blast
    then obtain w P'' where P'': "P' = LCons w P''" by (meson neq_LNil_conv)
    hence "v\<rightarrow>w" "Q (LCons w P'') \<or> valid_path (LCons w P'')" using step valid_path P' P'' by blast+
    hence ?case using P' P'' by auto
  }
  thus ?case by blast
qed

  "valid_path P \<Longrightarrow> lset P \<subseteq> V \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w)"
  using valid_path_edges valid_path_in_V by blast
lemma valid_path_impl2:
  "\<lbrakk> lset P \<subseteq> V; \<And>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w \<rbrakk> \<Longrightarrow> valid_path P"
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
    moreover have "lset Ps \<subseteq> V" using v(1) valid_path(1) by auto
    moreover have "\<And>i v w. \<lbrakk> enat (Suc i) < llength Ps; Ps $ i = v; Ps $ Suc i = w \<rbrakk> \<Longrightarrow> v \<rightarrow> w" proof-
      fix i v w assume asm: "enat (Suc i) < llength Ps" "Ps $ i = v" "Ps $ Suc i = w"
      hence "enat (Suc (Suc i)) < llength P" by (metis ldropn_Suc_LCons ldropn_eq_LNil leD leI v(1))
      moreover have "P $ (Suc i) = v" by (simp add: asm(2) v(1))
      moreover have "P $ (Suc (Suc i)) = w" by (simp add: asm(3) v(1))
      ultimately show "v\<rightarrow>w" using valid_path(2) by blast
    qed
    ultimately have "\<exists>v w Ps. P = LCons v Ps \<and> v \<in> V \<and> w \<in> V \<and> v \<rightarrow> w
      \<and> ((\<exists>P. Ps = P \<and> lset P \<subseteq> V
           \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v \<rightarrow> w))
         \<or> valid_path Ps)
      \<and> \<not> lnull Ps \<and> lhd Ps = w"
      using v w by blast
  }
  thus ?case by blast
qed
lemma valid_path_equiv:
  "valid_path P \<longleftrightarrow> lset P \<subseteq> V \<and> (\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v\<rightarrow>w)"
  using valid_path_impl1 valid_path_impl2 by blast

lemma valid_path_no_deadends:
  "\<lbrakk> valid_path P; enat (Suc i) < llength P; P $ Suc i = w \<rbrakk> \<Longrightarrow> \<not>deadend (P $ i)"
  using valid_path_impl1 by blast
lemma valid_path_ends_on_deadend:
  "\<lbrakk> valid_path P; enat i < llength P; deadend (P $ i) \<rbrakk> \<Longrightarrow> enat (Suc i) = llength P"
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
        by (metis `j \<le> i` add.commute enat_ord_simps(2) infinite_small_llength
                  le_Suc_eq less_diff_conv2 lfinite_llength_enat plus_enat_simps(1))
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

text {* A valid path is still valid in a supergame. *}
lemma valid_path_supergame:
  assumes "valid_path P" and G': "Digraph G'" "V \<subseteq> V\<^bsub>G'\<^esub>" "E \<subseteq> E\<^bsub>G'\<^esub>"
  shows "Digraph.valid_path G' P"
using `valid_path P`
proof (coinduction arbitrary: P rule: Digraph.valid_path.coinduct[OF `Digraph G'`, case_names IH])
  case (IH P)
  show ?case proof (cases)
    assume "P \<noteq> LNil"
    then obtain v P' where P': "P = LCons v P'" by (meson neq_LNil_conv)
    show ?thesis proof (cases)
      assume "P' = LNil"
      thus ?thesis using IH G'(2) valid_path_cons_simp P' by auto
    next
      assume "P' \<noteq> LNil"
      then obtain w Ps where *: "P = LCons v (LCons w Ps)" using P' llist.exhaust by auto
      moreover hence "v \<rightarrow>\<^bsub>G'\<^esub> w" using IH G'(3) valid_path_edges' by blast
      ultimately show ?thesis using IH G'(2) valid_path_cons_simp by auto
    qed
  qed simp
qed


subsection {* Maximal paths *}

text {*
  We say that a path is \emph{maximal} if it is empty or if it ends in a deadend.
*}
coinductive maximal_path where
  maximal_path_base: "maximal_path LNil"
| maximal_path_base': "deadend v \<Longrightarrow> maximal_path (LCons v LNil)"
| maximal_path_cons: "\<not>lnull Ps \<Longrightarrow> maximal_path Ps \<Longrightarrow> maximal_path (LCons v Ps)"

lemma maximal_no_deadend: "maximal_path (LCons v Ps) \<Longrightarrow> \<not>deadend v \<Longrightarrow> \<not>lnull Ps"
  by (metis lhd_LCons llist.distinct(1) ltl_simps(2) maximal_path.simps)
lemma maximal_ltl: "maximal_path P \<Longrightarrow> maximal_path (ltl P)"
  by (metis ltl_simps(1) ltl_simps(2) maximal_path.simps)
lemma maximal_drop: "maximal_path P \<Longrightarrow> maximal_path (ldropn n P)"
  by (simp add: maximal_ltl ltl_ldrop)

lemma maximal_path_lappend:
  assumes "\<not>lnull P'" "maximal_path P'"
  shows "maximal_path (lappend P P')"
proof (cases)
  assume "\<not>lnull P"
  thus ?thesis using assms proof (coinduction arbitrary: P' P rule: maximal_path.coinduct)
    case (maximal_path P' P)
    let ?P = "lappend P P'"
    show ?case proof (cases "?P = LNil \<or> (\<exists>v. ?P = LCons v LNil \<and> deadend v)")
      case False
      then obtain Ps v where P: "?P = LCons v Ps" by (meson neq_LNil_conv)
      hence "Ps = lappend (ltl P) P'" by (simp add: lappend_ltl maximal_path(1))
      hence "\<exists>Ps1 P'. Ps = lappend Ps1 P' \<and> \<not>lnull P' \<and> maximal_path P'"
        using maximal_path(2) maximal_path(3) by auto
      thus ?thesis using P lappend_lnull1 by fastforce
    qed blast
  qed
qed (simp add: assms(2) lappend_lnull1[of P P'])

lemma maximal_ends_on_deadend:
  assumes "maximal_path P" "lfinite P" "\<not>lnull P"
  shows "deadend (llast P)"
proof-
  from `lfinite P` `\<not>lnull P` obtain n where n: "llength P = enat (Suc n)"
    by (metis enat_ord_simps(2) gr0_implies_Suc lfinite_llength_enat lnull_0_llength)
  def P' \<equiv> "ldropn n P"
  hence "maximal_path P'" using assms(1) maximal_drop by blast
  thus ?thesis proof (cases rule: maximal_path.cases)
    case (maximal_path_base' v)
    hence "deadend (llast P')" unfolding P'_def by simp
    thus ?thesis unfolding P'_def using llast_ldropn[of n P] n
      by (metis P'_def ldropn_eq_LConsD local.maximal_path_base'(1))
  next
    case (maximal_path_cons P'' v)
    hence "ldropn (Suc n) P = P''" unfolding P'_def by (metis ldrop_eSuc_ltl ltl_ldropn ltl_simps(2))
    thus ?thesis using n maximal_path_cons(2) by auto
  qed (simp add: P'_def n ldropn_eq_LNil)
qed

lemma maximal_ends_on_deadend': "\<lbrakk> lfinite P; deadend (llast P) \<rbrakk> \<Longrightarrow> maximal_path P"
proof (coinduction arbitrary: P rule: maximal_path.coinduct)
  case (maximal_path P)
  show ?case proof (cases)
    assume "P \<noteq> LNil"
    then obtain v P' where P': "P = LCons v P'" by (meson neq_LNil_conv)
    show ?thesis proof (cases)
      assume "P' = LNil" thus ?thesis using P' maximal_path(2) by auto
    qed (metis P' lfinite_LCons llast_LCons llist.collapse(1) maximal_path(1,2))
  qed simp
qed

lemma infinite_path_is_maximal: "\<lbrakk> valid_path P; \<not>lfinite P \<rbrakk> \<Longrightarrow> maximal_path P"
  apply (coinduction arbitrary: P rule: maximal_path.coinduct)
  apply (cases rule: valid_path.cases, simp)
  by simp_all

end -- "locale Digraph"

subsection {* Parity games *}

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

text {* @{text "VV p"} is the set of nodes belonging to player @{term p}. *}
abbreviation VV :: "Player \<Rightarrow> 'a set" where "VV p \<equiv> (if p = Even then V0 else V - V0)"
lemma VVp_to_V [intro]: "v \<in> VV p \<Longrightarrow> v \<in> V" by (metis (full_types) Diff_subset subsetCE valid_player0_set)
lemma VV_impl1 [intro]: "v \<in> VV p \<Longrightarrow> v \<notin> VV p**" by auto
lemma VV_impl2 [intro]: "v \<in> VV p** \<Longrightarrow> v \<notin> VV p" by auto
lemma VV_equivalence [iff]: "v \<in> V \<Longrightarrow> v \<notin> VV p \<longleftrightarrow> v \<in> VV p**" by auto
lemma VV_cases: "\<lbrakk> v \<in> V ; v \<in> VV p \<Longrightarrow> P ; v \<in> VV p** \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by fastforce

subsection {* Subgames *}

text {* We define a subgame by restricting the set of vertices to a given subset. *}

definition subgame where
  "subgame V' \<equiv> G\<lparr> verts := V' \<inter> V, arcs := E \<inter> (V' \<times> V'), player0 := V0 \<inter> V' \<rparr>"

lemma subgame_V [simp]: "V\<^bsub>subgame V'\<^esub> \<subseteq> V"
  and subgame_E [simp]: "E\<^bsub>subgame V'\<^esub> \<subseteq> E"
  and subgame_\<omega>: "\<omega>\<^bsub>subgame V'\<^esub> = \<omega>"
  unfolding subgame_def by simp_all

lemma subgame_V' [simp]: "V' \<subseteq> V \<Longrightarrow> V\<^bsub>subgame V'\<^esub> = V'" unfolding subgame_def by auto
lemma subgame_E' [simp]: "V' \<subseteq> V \<Longrightarrow> E\<^bsub>subgame V'\<^esub> = E \<inter> (V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>)"
  unfolding subgame_def by auto

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
  shows "Digraph (subgame V')"
proof (unfold_locales)
  show "E\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using valid_edge_set by auto
qed

lemma subgame_ParityGame:
  shows "ParityGame (subgame V')"
proof (unfold_locales)
  show "E\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>"
    using subgame_Digraph[unfolded Digraph_def, OF assms] .
  show "V0\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using valid_player0_set by auto
  show "finite (\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub>)" by simp
qed

lemma subgame_deadend [simp]: "\<not>Digraph.deadend (subgame V') v \<Longrightarrow> \<not>deadend v"
  by (meson subgame_E subgame_V subsetCE)

lemma subgame_valid_path:
  assumes P: "valid_path P" "lset P \<subseteq> V'"
  shows "Digraph.valid_path (subgame V') P"
proof-
  have "lset P \<subseteq> V" using P(1) valid_path_in_V by blast
  hence "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) by auto
  with P(1) show ?thesis
  proof (coinduction arbitrary: P rule: Digraph.valid_path.coinduct[OF subgame_Digraph, case_names IH])
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
  assumes V': "V' \<subseteq> V" and P: "maximal_path P" "lset P \<subseteq> V'"
  shows "Digraph.maximal_path (subgame V') P"
proof-
  have "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) V' by auto
  with P(1) V' show ?thesis
    by (coinduction arbitrary: P rule: Digraph.maximal_path.coinduct[OF subgame_Digraph])
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

lemma path_priorities_in_\<omega>V: "\<lbrakk> valid_path P; \<not>lfinite P \<rbrakk> \<Longrightarrow> path_priorities P i \<in> \<omega> ` V"
  unfolding path_priorities_def using lset_nth_member_inf[of P V i] valid_path_in_V by blast

lemma path_inf_priorities_is_nonempty:
  assumes "valid_path P" "\<not>lfinite P"
  shows "\<exists>k. k \<in> path_inf_priorities P"
proof-
  have "range (path_priorities P) \<subseteq> \<omega> ` V"
    by (simp add: path_priorities_in_\<omega>V assms image_subsetI)
  hence "finite (range (path_priorities P))"
    using priorities_finite finite_subset by blast
  then obtain n0 where n0: "\<not>(finite {n. path_priorities P n = path_priorities P n0})"
    using pigeonhole_infinite[of UNIV "path_priorities P"] by auto
  def k \<equiv> "path_priorities P n0"
  hence "lmap \<omega> P $ n0 = k" using assms(2) path_priorities_equiv by simp
  moreover {
    fix n assume "lmap \<omega> P $ n = k"
    have "\<exists>n' > n. path_priorities P n' = k" using n0 k_def infinite_nat_iff_unbounded by auto
    hence "\<exists>n' > n. lmap \<omega> P $ n' = k" using assms(2) path_priorities_equiv by auto
  }
  ultimately have "\<forall>n. k \<in> lset (ldropn n (lmap \<omega> P))"
    using index_infinite_set[of "lmap \<omega> P" n0 k] assms(2) lfinite_lmap
    by blast
  thus ?thesis using path_inf_priorities_def by blast
qed

lemma path_inf_priorities_LCons: "path_inf_priorities P = path_inf_priorities (LCons v P)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" proof
    fix a assume "a \<in> ?A"
    hence "\<forall>n. a \<in> lset (ldropn n (lmap \<omega> (LCons v P)))"
      using path_inf_priorities_def in_set_ldropn[of a _ "lmap \<omega> (LCons v P)"] by auto
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
  by (metis llist.exhaust ltl_simps(1,2) path_inf_priorities_LCons)

(* True iff the path is winning for the given player. *)
definition winning_path :: "Player \<Rightarrow> 'a Path \<Rightarrow> bool" where
  "winning_path p P \<equiv>
    (\<not>lfinite P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (\<not>lnull P \<and> lfinite P \<and> llast P \<in> VV p**)
    \<or> (lnull P \<and> p = Even)"

lemma paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
proof (cases)
  assume "\<not>lnull P"
  show ?thesis proof (cases)
    assume finite: "lfinite P"
    hence "llast P \<in> V" using assms `\<not>lnull P` lfinite_lset valid_path_in_V by blast
    thus ?thesis by (simp add: `\<not>lnull P` local.finite winning_path_def)
  next
    assume infinite: "\<not>lfinite P"
    then obtain a where "a \<in> path_inf_priorities P" "\<And>b. b < a \<Longrightarrow> b \<notin> path_inf_priorities P"
      using assms ex_least_nat_le[of "\<lambda>a. a \<in> path_inf_priorities P"] path_inf_priorities_is_nonempty
      by blast
    hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P"
      unfolding infinite winning_path_def using `\<not>lnull P` infinite by (metis le_antisym not_le)
    thus ?thesis using winning_priority_for_one_player by blast
  qed
qed (simp add: winning_path_def)

lemma winning_path_ltl:
  assumes P: "winning_path p P" "\<not>lnull P" "\<not>lnull (ltl P)"
  shows "winning_path p (ltl P)"
proof (cases)
  assume "lfinite P"
  moreover have "llast P = llast (ltl P)" using P(2,3) by (metis llast_LCons2 ltl_simps(2) not_lnull_conv)
  ultimately show ?thesis using P by (simp add: winning_path_def)
next
  assume "\<not>lfinite P"
  thus ?thesis using winning_path_def path_inf_priorities_ltl using P(1,2) by auto
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
  using assms paths_are_winning_for_one_player valid_path_drop winning_path_drop by blast

lemma winning_path_LCons:
  assumes P: "winning_path p P" "\<not>lnull P"
  shows "winning_path p (LCons v P)"
proof (cases)
  assume "lfinite P"
  moreover have "llast P = llast (LCons v P)" using P(2) by (metis llast_LCons2 not_lnull_conv)
  ultimately show ?thesis using P by (simp add: winning_path_def)
next
  assume "\<not>lfinite P"
  thus ?thesis using winning_path_def path_inf_priorities_LCons using P by auto
qed

lemma winning_path_supergame:
  assumes "winning_path p P"
  and G': "ParityGame G'" "VV p** \<subseteq> ParityGame.VV G' p**" "\<omega> = \<omega>\<^bsub>G'\<^esub>"
  shows "ParityGame.winning_path G' p P"
proof-
  { assume "\<not>lfinite P"
    moreover hence "\<not>lnull P" by auto
    ultimately
      have "\<exists>a. a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a"
      using assms(1) unfolding winning_path_def by blast
    moreover have "path_inf_priorities P = ParityGame.path_inf_priorities G' P"
      unfolding path_inf_priorities_def using ParityGame.path_inf_priorities_def[of G' P] G'(1,3)
      by auto
    ultimately
      have "\<exists>a. a \<in> ParityGame.path_inf_priorities G' P
            \<and> (\<forall>b \<in> ParityGame.path_inf_priorities G' P. a \<le> b) \<and> winning_priority p a" by blast
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

subsection {* Valid maximal paths *}

text {* Define a locale for valid maximal paths, because we need them often. *}

locale vm_path = ParityGame +
  fixes P v0
  assumes P_not_null [simp]: "\<not>lnull P"
      and P_valid    [simp]: "valid_path P"
      and P_maximal  [simp]: "maximal_path P"
      and P_v0       [simp]: "lhd P = v0"
begin
lemma vm_path [simp]: "vm_path G P v0" by unfold_locales

lemma P_LCons: "P = LCons v0 (ltl P)" using lhd_LCons_ltl[OF P_not_null] by simp

lemma P_len [simp]: "enat 0 < llength P" by (simp add: lnull_0_llength)
lemma P_0 [simp]: "P $ 0 = v0" by (simp add: lnth_0_conv_lhd)
lemma P_lnth_Suc: "P $ Suc n = ltl P $ n" by (simp add: lnth_ltl)
lemma P_no_deadends: "enat (Suc n) < llength P \<Longrightarrow> \<not>deadend (P $ n)"
  using valid_path_no_deadends by simp
lemma P_no_deadend_v0: "\<not>lnull (ltl P) \<Longrightarrow> \<not>deadend v0"
  by (metis P_LCons P_valid edges_are_in_V(2) not_lnull_conv valid_path_edges')
lemma P_no_deadend_v0_llength: "enat (Suc n) < llength P \<Longrightarrow> \<not>deadend v0"
  by (metis P_0 P_len P_valid enat_ord_simps(2) not_less_eq valid_path_ends_on_deadend zero_less_Suc)
lemma P_ends_on_deadend: "\<lbrakk> enat n < llength P; deadend (P $ n) \<rbrakk> \<Longrightarrow> enat (Suc n) = llength P"
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

lemma extension_valid [simp]: "v\<rightarrow>v0 \<Longrightarrow> valid_path (LCons v P)"
  using P_not_null P_v0 P_valid valid_path_cons by blast
lemma extension_maximal [simp]: "maximal_path (LCons v P)"
  by (simp add: maximal_path_cons)
lemma lappend_maximal [simp]: "maximal_path (lappend P' P)"
  by (simp add: maximal_path_lappend)

lemma v0_V [simp]: "v0 \<in> V" by (metis P_LCons P_valid valid_path_cons_simp)
lemma v0_lset_P [simp]: "v0 \<in> lset P" using P_not_null P_v0 llist.set_sel(1) by blast
lemma v0_VV: "v0 \<in> VV p \<or> v0 \<in> VV p**" by simp
lemma lset_P_V [simp]: "lset P \<subseteq> V" by (simp add: valid_path_in_V)
lemma lset_ltl_P_V [simp]: "lset (ltl P) \<subseteq> V" by (simp add: valid_path_in_V)

lemma finite_llast_deadend [simp]: "lfinite P \<Longrightarrow> deadend (llast P)"
  using P_maximal P_not_null maximal_ends_on_deadend by blast
lemma finite_llast_V [simp]: "lfinite P \<Longrightarrow> llast P \<in> V"
  using P_not_null lfinite_lset lset_P_V by blast

end

end
