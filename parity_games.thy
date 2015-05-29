theory parity_games
imports
  Main
  pigeon_hole_principle
begin

type_synonym Vertex = "nat"
type_synonym Edge = "nat \<times> nat"

record Graph =
  verts :: "Vertex set"
  arcs :: "Edge set"

locale Digraph = fixes G :: "Graph"
  assumes finite_vertex_set: "finite (verts G)"
    and non_empty_vertex_set: "\<exists>v. v \<in> verts G"
    and valid_edge_set: "arcs G \<subseteq> verts G \<times> verts G"
begin
  abbreviation "V \<equiv> verts G"
  abbreviation "E \<equiv> arcs G"
end

record ParityGameVertex =
  player0 :: bool
  priority :: nat

datatype Player = Even | Odd
fun other_player :: "Player \<Rightarrow> Player" where "other_player Even = Odd" | "other_player Odd = Even"
notation other_player ("(_**)" [1000] 1000)

locale ParityGame = Digraph +
  fixes priority :: "Vertex \<Rightarrow> nat"
    and player0 :: "Vertex set"
  assumes
     valid_player0_set "player0 \<subseteq> verts G"
begin
  abbreviation "V0 \<equiv> player0"
  fun VV :: "Player \<Rightarrow> Vertex set" where "VV Even = V0" | "VV Odd = V - V0"
  abbreviation "\<omega> \<equiv> priority"
end

type_synonym Path = "nat \<Rightarrow> Vertex option"
type_synonym Strategy = "Vertex \<Rightarrow> Vertex option"

definition (in Digraph) deadend :: "Vertex \<Rightarrow> bool" where
  "deadend v == \<not>(\<exists>w \<in> V. (v,w) \<in> E)"

definition (in Digraph) infinite_path :: "Path \<Rightarrow> bool" where
  "infinite_path P == \<forall>i. P i  \<noteq> None"

definition (in Digraph) finite_path :: "Path \<Rightarrow> bool" where
  "finite_path P == \<exists>i. \<forall>j. (j > i \<longleftrightarrow> P j = None)"

definition (in Digraph) path_dom :: "Path \<Rightarrow> nat set" where
  "path_dom P = {i. P i \<noteq> None}"

definition (in Digraph) valid_path :: "Path \<Rightarrow> bool" where
  "valid_path P == (infinite_path P \<or> finite_path P)
    \<and> (\<forall>i \<in> path_dom P.
      the (P i) \<in> V
      \<and> (\<not>deadend (the (P i)) \<longrightarrow> (the (P i), the (P (i+1))) \<in> E))"

lemma (in Digraph) paths_are_contiguous:
  assumes "valid_path P"
  shows "P i \<noteq> None \<Longrightarrow> \<forall>j < i. P j \<noteq> None"
  by (metis assms finite_path_def infinite_path_def le_less_trans less_imp_le valid_path_def)

lemma (in Digraph) path_dom_ends_on_finite_paths:
  assumes "valid_path P" "finite_path P"
  obtains i where "i \<in> path_dom P \<and> P (i + 1) = None"
  by (metis (mono_tags, lifting) Suc_eq_plus1 assms(2) finite_path_def lessI less_imp_le mem_Collect_eq not_less path_dom_def)

(* The set of nodes that occur infinitely often on a given path. *)
definition (in ParityGame) path_inf :: "Path \<Rightarrow> Vertex set" where
  "path_inf P == {v. (\<exists>i. P i = Some v) \<and> (\<forall>i. P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v))}"

(* The set of priorities that occur infinitely often on a given path. *)
definition (in ParityGame) path_inf_priorities :: "Path \<Rightarrow> nat set" where
  "path_inf_priorities P == {i. \<exists>v \<in> path_inf P. i = priority v}"

(* True iff \<sigma> is a positional strategy for the given player. *)
definition (in ParityGame) positional_strategy :: "Player \<Rightarrow> Strategy \<Rightarrow> bool" where
  "positional_strategy p \<sigma> == \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"

definition (in ParityGame) path_conforms_with_strategy :: "Player \<Rightarrow> Path \<Rightarrow> Strategy \<Rightarrow> bool" where
  "path_conforms_with_strategy p P \<sigma> = (\<forall>i \<in> path_dom P. the (P i) \<in> VV p \<longrightarrow> \<sigma>(the (P i)) = P (i+1))"

lemma (in "ParityGame") path_inf_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>v. v \<in> path_inf P"
  proof -
    from assms have "\<forall>i. the (P i) \<in> V" by (simp add: infinite_path_def path_dom_def valid_path_def)
    hence "\<exists>v \<in> V. (\<exists>i. the (P i) = v) \<and> (\<forall>i. (the (P i) = v \<longrightarrow> (\<exists>j > i. the (P j) = v)))"
      using pigeon_hole_principle[of "V" "\<lambda>i. the (P i)"] finite_vertex_set by blast
    hence "\<exists>v \<in> V. (\<exists>i. P i = Some v) \<and> (\<forall>i. (P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v)))" by (metis assms(2) infinite_path_def option.collapse)
    thus "?thesis" using path_inf_def valid_path_def assms by auto
  qed

lemma (in "ParityGame") path_inf_priorities_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>a. a \<in> path_inf_priorities P"
  using assms path_inf_is_nonempty path_inf_priorities_def by fastforce

lemma (in "ParityGame") path_inf_priorities_has_minimum:
  assumes "valid_path P" "infinite_path P"
  obtains a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)"
  proof -
    have "\<exists>a. a \<in> path_inf_priorities P" using assms path_inf_priorities_is_nonempty by blast
    then obtain a where "a \<in> path_inf_priorities P" "(\<And>z. z < a \<Longrightarrow> z \<notin> path_inf_priorities P)"
      by (metis less_eq less_than_def wf_less_than wfE_min)
    thus ?thesis by (meson leI that)
  qed

fun winning_priority :: "Player \<Rightarrow> nat \<Rightarrow> bool" where
  "winning_priority Even = even"
  | "winning_priority Odd = odd"

lemma winning_priority_for_one_player:
  shows "winning_priority p i \<or> winning_priority p** i"
  by (metis (full_types) Player.distinct(1) other_player.simps(1) other_player.simps(2) winning_priority.elims)

(* True iff the path is winning for the given player. *)
definition (in ParityGame) winning_path :: "Player \<Rightarrow> Path \<Rightarrow> bool" where
  "winning_path p P ==
    (infinite_path P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (finite_path P \<and> (\<exists>i \<in> path_dom P. P (i+1) = None \<and> the (P i) \<in> VV p**))"

lemma (in "ParityGame") paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "\<exists>p. winning_path p P"
  proof (cases)
    assume infinite: "infinite_path P"
    then obtain a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using assms path_inf_priorities_has_minimum by blast
    thus ?thesis by (meson infinite winning_path_def winning_priority_for_one_player)
  next
    assume "\<not>infinite_path P"
    hence finite: "finite_path P" using assms valid_path_def by blast
    then obtain i where "i \<in> path_dom P \<and> P (i+1) = None" using assms path_dom_ends_on_finite_paths by blast
    thus ?thesis by (metis Diff_iff VV.simps(1) VV.simps(2) assms local.finite other_player.simps(1) other_player.simps(2) valid_path_def winning_path_def)
  qed

definition (in ParityGame) winning_strategy :: "Player \<Rightarrow> Strategy \<Rightarrow> Vertex \<Rightarrow> bool" where
  "winning_strategy p \<sigma> v == \<forall>P. P 0 = Some v \<longrightarrow> path_conforms_with_strategy p P \<sigma> \<longrightarrow> winning_path p P"

theorem (in "ParityGame") positional_strategy_exists:
  assumes "v \<in> V"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    show ?thesis sorry
  qed

end
