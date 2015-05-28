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
  assumes finite_vertex_set "finite (verts G)"
    and non_empty_vertex_set "\<exists>v. v \<in> verts G"
    and valid_edge_set "arcs G \<subseteq> verts G \<times> verts G"

record ParityGameVertex =
  player0 :: bool
  priority :: nat

locale ParityGame = Digraph +
  fixes priority :: "Vertex \<Rightarrow> nat"
    and player0 :: "Vertex set"
  assumes
     valid_player0_set "player0 \<subseteq> verts G"

type_synonym Path = "nat \<Rightarrow> Vertex"

definition (in ParityGame) strategy :: "Edge set \<Rightarrow> bool" where
  "strategy s == True"

definition (in ParityGame) valid_path :: "Path \<Rightarrow> bool" where
  "valid_path P == \<forall>i. P(i) \<in> verts G"
definition (in ParityGame) path_inf :: "Path \<Rightarrow> Vertex set" where
  "path_inf P == {v. (\<exists>i. P(i) = v) \<and> (\<forall>i. P(i) = v \<longrightarrow> (\<exists>j > i. P(j) = v))}"
definition (in ParityGame) isMinimumPriority :: "Vertex set \<Rightarrow> nat \<Rightarrow> bool" where
  "isMinimumPriority X p \<equiv> \<forall>q \<in> X. priority p \<le> priority q"

definition (in ParityGame) winningStrategy :: "Edge set \<Rightarrow> bool" where
  "winningStrategy s == True"

definition (in ParityGame) winning :: "Vertex \<Rightarrow> bool" where
  "winning v == \<exists>s. strategy s \<and> winningStrategy s"

lemma (in "ParityGame") path_inf_is_nonempty:
  assumes "valid_path P"
  shows "\<exists>v. v \<in> path_inf P"
  proof -
    show "?thesis" sorry
  qed

end
