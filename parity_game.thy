theory parity_game
imports
  Main
  pigeon_hole_principle
begin

lemma option_the_simp: "x = Some y \<Longrightarrow> the x = y" by simp

(* 'a is the vertex type. *)
type_synonym 'a Edge = "'a \<times> 'a"
type_synonym 'a Path = "nat \<Rightarrow> 'a option"

definition infinite_path :: "'a Path \<Rightarrow> bool" where [simp]: "infinite_path P \<equiv> \<forall>i. P i \<noteq> None"
definition finite_path :: "'a Path \<Rightarrow> bool" where [simp]: "finite_path P \<equiv> \<exists>i. \<forall>j. (j > i \<longleftrightarrow> P j = None)"
abbreviation path_dom :: "'a Path \<Rightarrow> nat set" where "path_dom P \<equiv> {i. P i \<noteq> None}"
(* The set of nodes that occur infinitely often on a given path. *)
(* definition path_inf :: "'a Path \<Rightarrow> 'a set" where
  "path_inf P \<equiv> {v. (\<exists>i. P i = Some v) \<and> (\<forall>i. P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v))}" *)
abbreviation path_tail :: "'a Path \<Rightarrow> 'a Path" where "path_tail P \<equiv> \<lambda>i. P (Suc i)"

lemma paths_are_contiguous:
  assumes "infinite_path P \<or> finite_path P"
  shows "P i \<noteq> None \<Longrightarrow> j \<le> i \<Longrightarrow> P j \<noteq> None"
  by (metis assms finite_path_def infinite_path_def leD le_less_linear le_trans)
lemma paths_are_contiguous_suc:
  assumes "infinite_path P \<or> finite_path P"
  shows "P (Suc i) \<noteq> None \<Longrightarrow> P i \<noteq> None"
  using assms paths_are_contiguous[of _ "Suc i" i] le_Suc_eq by blast
lemma path_dom_ends_on_finite_paths:
  assumes finite: "finite_path P"
  shows "\<exists>!i \<in> path_dom P. P (Suc i) = None"
  proof -
    obtain i where i_def: "\<forall>j. (j > i \<longleftrightarrow> P j = None)" using finite by fastforce
    hence "i \<in> path_dom P \<and> P (Suc i) = None" by auto
    thus ?thesis by (metis (mono_tags, lifting) i_def le_imp_less_or_eq less_Suc_eq_le mem_Collect_eq)
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

abbreviation deadend :: "'a \<Rightarrow> bool" where "deadend v \<equiv> \<not>(\<exists>w \<in> V. v \<rightarrow> w)"

definition valid_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "valid_path P \<equiv> P 0 \<noteq> None \<and> (infinite_path P \<or> finite_path P)
      \<and> (\<forall>i. P i \<noteq> None \<longrightarrow> the (P i) \<in> V)
      \<and> (\<forall>i. P i \<noteq> None \<and> P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i)))"

lemma valid_path_is_infinite_or_finite: "valid_path P \<Longrightarrow> infinite_path P \<or> finite_path P" by simp
lemma valid_path_is_contiguous_suc: "valid_path P \<Longrightarrow> P (Suc i) \<noteq> None \<Longrightarrow> P i \<noteq> None"
  using paths_are_contiguous_suc valid_path_is_infinite_or_finite by blast
lemma valid_paths_are_nonempty: "valid_path P \<Longrightarrow> P 0 \<noteq> None" by auto
lemma valid_path_no_deadends: "valid_path P \<Longrightarrow> P (Suc i) \<noteq> None \<Longrightarrow> \<not>deadend (the (P i))"
  by (meson valid_path_def valid_path_is_contiguous_suc)

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

lemma infinite_path_tail [intro]:
  "infinite_path P \<Longrightarrow> infinite_path (path_tail P)" using assms by auto
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
