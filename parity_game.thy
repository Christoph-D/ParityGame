theory parity_game
imports
  Main
  pigeon_hole_principle
begin

lemma option_the_simp [simp]: "x = Some y \<Longrightarrow> the x = y" by simp
lemma option_the_simp2 [simp]: "x \<noteq> None \<Longrightarrow> \<exists>y. x = Some y" by simp
lemma obtain_min:
  assumes "\<exists>n :: nat. P n"
  obtains n where "P n" "\<And>i. i < n \<Longrightarrow> \<not>P i"
  using assms ex_least_nat_le by blast

(* 'a is the vertex type. *)
type_synonym 'a Edge = "'a \<times> 'a"
codatatype (Pset: 'a) Path = path_cons 'a (path_tail: "'a Path") | path_deadend: PEnd 'a

inductive finite_path :: "'a Path \<Rightarrow> bool" where
  finite_path_deadend: "finite_path (PEnd _)"
  | finite_path_cons: "finite_path Ps \<Longrightarrow> finite_path (path_cons _ Ps)"
definition infinite_path :: "'a Path \<Rightarrow> bool" where [simp]: "infinite_path P \<equiv> \<not>finite_path P"
(* The set of nodes that occur infinitely often on a given path. *)
(* definition path_inf :: "'a Path \<Rightarrow> 'a set" where
  "path_inf P \<equiv> {v. (\<exists>i. P i = Some v) \<and> (\<forall>i. P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v))}" *)

fun path_head :: "'a Path \<Rightarrow> 'a" where
  "path_head (path_cons v _) = v"
  | "path_head (PEnd v) = v"

fun path_at :: "'a Path \<Rightarrow> nat \<Rightarrow> 'a option" (infix "$" 60) where
  "path_at (PEnd v) 0 = Some v"
  | "path_at (PEnd _) _ = None"
  | "path_at (path_cons v _) 0 = Some v"
  | "path_at (path_cons v Ps) (Suc n) = path_at Ps n"

lemma path_at_0 [simp]: "P $ 0 = Some (path_head P)" by (metis path_at.simps(1) path_at.simps(3) path_head.elims)
lemma path_at_0' [simp]: "P $ 0 \<noteq> None" by simp
lemma path_cons_0 [simp]: "path_head (path_cons v P) = v" by simp
lemma path_cons_suc_is_P [simp]: "path_cons v P $ (Suc i) = P $ i" by simp
lemma path_cons_suc_is_P2: "i \<noteq> 0 \<Longrightarrow> path_cons v P $ i = P $ i - 1" by (metis Suc_diff_1 gr0I path_cons_suc_is_P)

lemma infinite_path_no_deadend: "infinite_path P \<Longrightarrow> \<not>path_deadend P" using finite_path.simps path_deadend_def by fastforce
lemma infinite_path_tail: "infinite_path (path_cons v Ps) \<Longrightarrow> infinite_path Ps" by (meson finite_path_cons infinite_path_def)
lemma infinite_path_at:
  assumes P_inf: "infinite_path P"
  shows "P $ i \<noteq> None"
using assms proof (induct i arbitrary: P, simp)
  fix i and P :: "'a Path"
  assume IH: "\<And>P :: 'a Path. infinite_path P \<Longrightarrow> P $ i \<noteq> None" "infinite_path P"
  then obtain v Ps where Ps: "P = path_cons v Ps" using infinite_path_no_deadend by (metis Path.collapse(1))
  hence "Ps $ i \<noteq> None" using IH by (meson infinite_path_tail)
  thus "P $ Suc i \<noteq> None" by (simp add: Ps)
qed
lemma finite_path_at:
  assumes P_fin: "finite_path P"
  shows "\<exists>i. P $ i = None"
proof (rule finite_path.induct, insert P_fin, assumption)
  fix v :: 'a
  have "PEnd v $ 1 = None" by simp
  thus "\<exists>i. PEnd v $ i = None" by blast
next
  fix v :: 'a and Ps :: "'a Path"
  assume "\<exists>i. Ps $ i = None"
  then obtain i where "Ps $ i = None" by blast
  hence "path_cons v Ps $ (Suc i) = None" by simp
  thus "\<exists>i. path_cons v Ps $ i = None" by blast
qed
lemma finite_path_none_Suc: "P $ i = None \<Longrightarrow> P $ (Suc i) = None" proof (induct i arbitrary: P)
  case 0 thus "P $ Suc 0 = None" by simp
next
  case (Suc i) thus "P $ Suc (Suc i) = None" by (metis path_at.simps(2) path_cons_suc_is_P path_head.cases)
qed

lemma finite_path_at2: "\<lbrakk> P $ i = None; i \<le> j \<rbrakk> \<Longrightarrow> P $ j = None" proof (induct "j - i" arbitrary: i j)
  case 0 thus "P $ j = None" by simp
next
  case (Suc d)
  thus "P $ j = None" by (metis Suc_diff_Suc diff_diff_cancel diff_le_self finite_path_none_Suc leD le_eq_less_or_eq not_less_eq)
qed

lemma finite_path_eventually_none: "finite_path P \<Longrightarrow> \<exists>i. \<forall>j. (j > i \<longrightarrow> P $ j = None)" by (meson finite_path_at finite_path_at2 less_or_eq_imp_le)
lemma finite_path_eventually_none': assumes P_fin: "finite_path P" shows "\<exists>i. \<forall>j. (j > i \<longleftrightarrow> P $ j = None)" proof-
  def Q \<equiv> "\<lambda>i. P $ i = None"
  hence "\<exists>i'. Q i'" using finite_path_at P_fin by blast
  then obtain i' where i': "Q i'" "\<And>j. j < i' \<Longrightarrow> \<not>Q j" using obtain_min by blast
  hence "i' \<noteq> 0" by (meson Q_def path_at_0')
  then obtain i where i: "Suc i = i'" using Suc_pred by blast
  have "\<And>j. j > i \<Longrightarrow> P $ j = None" proof-
    fix j assume "j > i"
    have "P $ Suc i = None" using Q_def i i'(1) by blast
    hence "\<And>j. j \<ge> Suc i \<Longrightarrow> P $ j = None" using finite_path_at2 by blast
    thus "P $ j = None" using Suc_leI `i < j` by blast
  qed
  moreover have "\<And>j. P $ j = None \<Longrightarrow> j > i" using Q_def i i'(2) not_less_eq by blast
  ultimately show "\<exists>i. \<forall>j. (j > i \<longleftrightarrow> P $ j = None)" by blast
qed

lemma infinite_path_equiv: "infinite_path P \<longleftrightarrow> (\<forall>i. P $ i \<noteq> None)" using finite_path_at infinite_path_at infinite_path_def by blast
lemma finite_path_equiv': "finite_path P \<longleftrightarrow> (\<exists>i. \<forall>j. (j > i \<longrightarrow> P $ j = None))" by (meson finite_path_eventually_none gt_ex infinite_path_at infinite_path_def)
lemma finite_path_equiv: "finite_path P \<longleftrightarrow> (\<exists>i. \<forall>j. (j > i \<longleftrightarrow> P $ j = None))" using finite_path_equiv' finite_path_eventually_none' by blast

abbreviation path_dom :: "'a Path \<Rightarrow> nat set" where "path_dom P \<equiv> {i. P $ i \<noteq> None}"

lemma paths_are_contiguous: "P $ i = Some v \<Longrightarrow> j \<le> i \<Longrightarrow> \<exists>w. P $ j = Some w" using finite_path_at2 by fastforce
lemma paths_are_contiguous_suc: "P $ Suc i = Some w \<Longrightarrow> \<exists>v. P $ i = Some v" by (simp add: paths_are_contiguous)
lemma path_dom_ends_on_finite_paths:
  assumes P_fin: "finite_path P"
  shows "\<exists>!i \<in> path_dom P. P $ Suc i = None"
  proof -
    obtain i where i_def: "\<forall>j. (j > i \<longleftrightarrow> P $ j = None)" using P_fin finite_path_equiv by blast
    hence "i \<in> path_dom P \<and> P $ Suc i = None" by auto
    thus ?thesis by (metis (mono_tags) CollectD i_def less_antisym)
  qed
(* lemma path_inf_is_from_P: "v \<in> path_inf P \<Longrightarrow> \<exists>i. P i = Some v" apply (unfold path_inf_def; fastforce) done *)

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
  valid_path_deadend: "v \<in> V \<Longrightarrow> valid_path (PEnd v)"
  | valid_path_cons: "v\<rightarrow>w \<Longrightarrow> valid_path Ps \<Longrightarrow> path_head Ps = w \<Longrightarrow> valid_path (path_cons v Ps)"

lemma valid_path_equiv [simp]: "valid_path P \<Longrightarrow> Pset P \<subseteq> V" proof-
  print_statement
qed
lemma valid_path_equiv: "valid_path P \<Longrightarrow> \<forall>i v w. P $ i = Some v \<and> P $ Suc i = Some w \<longrightarrow> v\<rightarrow>w"
lemma valid_path_equiv [simp]: "valid_path P \<Longrightarrow> Pset P \<subseteq> V \<and> (\<forall>i v w. P $ i = Some v \<and> P $ Suc i = Some w \<longrightarrow> v\<rightarrow>w)"

lemma valid_path_is_infinite_or_finite: "valid_path P \<Longrightarrow> infinite_path P \<or> finite_path P" by simp
lemma valid_path_is_contiguous_suc: "valid_path P \<Longrightarrow> P (Suc i) = Some w \<Longrightarrow> \<exists>v. P i = Some v"
  using paths_are_contiguous_suc valid_path_is_infinite_or_finite by metis
lemma valid_paths_are_nonempty: "valid_path P \<Longrightarrow> P 0 \<noteq> None" by auto
lemma valid_path_no_deadends: "valid_path P \<Longrightarrow> P (Suc i) = Some w \<Longrightarrow> \<not>deadend (the (P i))"
  by (metis option.distinct(2) option.exhaust_sel valid_path_def valid_path_is_contiguous_suc)
lemma valid_path_ends_on_deadend: "valid_path P \<Longrightarrow> P i = Some v \<Longrightarrow> deadend v \<Longrightarrow> P (Suc i) = None"
  by (metis option.collapse valid_path_def)
lemma valid_path_contiguous_deadends: "valid_path P \<Longrightarrow> P i = None \<Longrightarrow> i \<le> j \<Longrightarrow> P j = None"
  by (meson finite_path_def infinite_path_def less_le_trans valid_path_is_infinite_or_finite)

definition maximal_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "maximal_path P \<equiv> \<forall>i. P i \<noteq> None \<and> \<not>deadend (the (P i)) \<longrightarrow> P (Suc i) \<noteq> None"
lemma maximal_infinite_path_tail [intro]: "maximal_path P \<Longrightarrow> maximal_path (path_tail P)" by auto

definition path_last :: "'a Path \<Rightarrow> 'a" where
  "path_last P = the (P (THE i. P i \<noteq> None \<and> (\<forall>j > i. P j = None)))"
lemma path_last_unique:
  "finite_path P \<Longrightarrow> \<exists>!i. P i \<noteq> None \<and> (\<forall>j > i. P j = None)" by (meson finite_path_def nat_neq_iff)
lemma path_last_exists:
  assumes P_finite: "finite_path P"
  shows "\<exists>i. P i \<noteq> None \<and> P (Suc i) = None \<and> path_last P = the (P i)" proof-
    def Q \<equiv> "\<lambda>i. P i \<noteq> None \<and> (\<forall>j > i. P j = None)"
    let ?i = "THE i. Q i"
    have *: "path_last P = the (P ?i)" using path_last_def Q_def by auto
    have "\<exists>!i. Q i" unfolding Q_def using path_last_unique P_finite by blast
    hence "Q ?i" by (simp add: theI')
    thus ?thesis using * Q_def by blast
  qed
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
  "path_priorities P i \<equiv> \<omega> (the (P i))"
(* The set of priorities that occur infinitely often on a given path. *)
definition path_inf_priorities :: "'a Path \<Rightarrow> nat set" where
  "path_inf_priorities P \<equiv> {k. (\<exists>i. path_priorities P i = k) \<and> (\<forall>i. path_priorities P i = k \<longrightarrow> (\<exists>j > i. path_priorities P j = k))}"

lemma path_priorities_in_\<omega>V:
  "\<lbrakk> valid_path P; infinite_path P \<rbrakk> \<Longrightarrow> path_priorities P i \<in> \<omega> ` V" using path_priorities_def by auto

lemma path_cons_non_empty [simp]: "path_cons v P 0 \<noteq> None" by simp

lemma path_cons_finite:
  assumes "finite_path P"
  shows "finite_path (path_cons v P)" proof-
    from assms obtain i where "\<forall>j. (j > i \<longleftrightarrow> P j = None)" by auto
    moreover have "path_cons v P 0 \<noteq> None" by simp
    ultimately have "\<forall>j. (j > (Suc i) \<longleftrightarrow> path_cons v P j = None)" by (metis not_less0 not_less_eq old.nat.exhaust path_cons_suc_is_P)
    thus ?thesis using finite_path_def by blast
  qed
lemma path_cons_infinite:
  assumes "infinite_path P"
  shows "infinite_path (path_cons v P)" by (metis assms infinite_path_def path_cons_def path_cons_non_empty)

lemma path_cons_valid:
  assumes "valid_path P" "P 0 = Some w0" "v0 \<rightarrow> w0"
  shows "valid_path (path_cons v0 P)" (is "valid_path ?P") proof-
    have "?P 0 \<noteq> None" by simp
    moreover have "infinite_path ?P \<or> finite_path ?P" by (meson assms(1) path_cons_finite path_cons_infinite valid_path_def)
    moreover have "\<forall>i v. ?P i = Some v \<longrightarrow> v \<in> V" proof (clarify)
      fix i v assume *: "?P i = Some v"
      show "v \<in> V" proof (cases)
        assume "i = 0" thus ?thesis using * assms(3) edges_are_in_V by auto
        next assume "i \<noteq> 0" thus ?thesis by (metis * assms(1) not0_implies_Suc path_cons_suc_is_P valid_path_def)
      qed
    qed
    moreover have "\<forall>i v w. ?P i = Some v \<and> ?P (Suc i) = Some w \<longrightarrow> v\<rightarrow>w" proof (clarify)
      fix i v w assume *: "path_cons v0 P i = Some v" "path_tail (path_cons v0 P) i = Some w"
      show "v\<rightarrow>w" proof (cases)
        assume "i = 0" thus ?thesis using * assms(2) assms(3) by auto
        next assume "i \<noteq> 0" thus ?thesis by (metis * assms(1) lessI less_Suc_eq_0_disj path_cons_suc_is_P valid_path_def)
      qed
    qed
    ultimately show ?thesis using valid_path_def by blast
  qed

lemma path_cons_extends:
  assumes "\<exists>i. P i = Some w"
  shows "\<exists>i. path_cons v P i = Some w" proof-
    from assms obtain i where "P i = Some w" by auto
    hence "path_cons v P (Suc i) = Some w" by (simp add: path_cons_def)
    thus ?thesis by blast
  qed

lemma infinite_path_tail [intro]:
  "infinite_path P \<Longrightarrow> infinite_path (path_tail P)" by auto
lemma finite_path_tail [intro]:
  assumes "finite_path P" "P (Suc 0) \<noteq> None" shows "finite_path (path_tail P)"
  proof -
    obtain i where i_def: "\<forall>j. (i < j) = (P j = None)" using assms(1) finite_path_def by blast
    hence "i > 0" using assms(2) by force
    hence "\<forall>j. (i - 1 < j) = (path_tail P j = None)" by (simp add: i_def Suc_leI less_diff_conv2)
    thus ?thesis by auto
  qed

lemma valid_path_tail [intro]:
  assumes "valid_path P" "P (Suc 0) \<noteq> None"
  shows "valid_path (path_tail P)"
  proof -
    have "path_tail P 0 \<noteq> None" using assms(2) by auto
    moreover have "infinite_path (path_tail P) \<or> finite_path (path_tail P)" using assms valid_path_def by blast
    ultimately show ?thesis using assms by auto
  qed

lemma path_inf_priorities_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>k. k \<in> path_inf_priorities P"
  proof -
    have "\<forall>i. path_priorities P i \<in> \<omega>`V" using assms path_priorities_in_\<omega>V by blast
    hence "\<exists>k. (\<exists>i. path_priorities P i = k) \<and> (\<forall>i. path_priorities P i = k \<longrightarrow> (\<exists>j > i. path_priorities P j = k))"
      using pigeon_hole_principle[of "\<omega>`V" "path_priorities P"] priorities_finite by blast
    thus ?thesis by (simp add: path_inf_priorities_def)
  qed

lemma path_inf_priorities_has_minimum:
  assumes "valid_path P" "infinite_path P"
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
    (infinite_path P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (finite_path P \<and> (\<exists>i \<in> path_dom P. P (Suc i) = None \<and> the (P i) \<in> VV p**))"

lemma paths_are_winning_for_exactly_one_player:
  assumes "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
  proof (cases)
    assume infinite: "infinite_path P"
    then obtain a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using assms path_inf_priorities_has_minimum by blast
    hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" using infinite winning_path_def by (metis (no_types, lifting) infinite_path_def le_antisym)
    thus ?thesis using winning_priority_for_one_player by blast
  next
    assume not_infinite: "\<not>infinite_path P"
    hence finite: "finite_path P" using assms valid_path_def by blast
    then obtain i where i_def: "i \<in> path_dom P \<and> P (Suc i) = None" using assms path_dom_ends_on_finite_paths by metis
    def v \<equiv> "the (P i)" (* the last vertex in the path *)
    hence "v \<in> V" using valid_path_def using assms i_def by auto (* TODO: make faster *)
    have "\<And>q. winning_path q P \<longleftrightarrow> (\<exists>i \<in> path_dom P. P (Suc i) = None \<and> the (P i) \<in> VV q**)"
      using not_infinite finite winning_path_def by metis
    hence "\<And>q. winning_path q P \<longleftrightarrow> v \<in> VV q**"
      using not_infinite finite path_dom_ends_on_finite_paths i_def v_def by blast
    hence "v \<in> VV p** \<longleftrightarrow> \<not>v \<in> VV p \<Longrightarrow> ?thesis"
      by (metis (full_types) Player.exhaust)
    thus ?thesis using VV_equivalence`v \<in> V` by blast
  qed

lemma paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "\<exists>!p. winning_path p P"
  by (metis (full_types) Player.exhaust assms paths_are_winning_for_exactly_one_player)

end -- "locale ParityGame"

end
