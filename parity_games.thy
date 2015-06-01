theory parity_games
imports
  Main
  pigeon_hole_principle
begin

typedecl Vertex
type_synonym Edge = "Vertex \<times> Vertex"
type_synonym Path = "nat \<Rightarrow> Vertex option"
type_synonym Strategy = "Vertex \<Rightarrow> Vertex option"

definition infinite_path :: "Path \<Rightarrow> bool" where [simp]: "infinite_path P \<equiv> \<forall>i. P i  \<noteq> None"
definition finite_path :: "Path \<Rightarrow> bool" where [simp]: "finite_path P \<equiv> \<exists>i. \<forall>j. (j > i \<longleftrightarrow> P j = None)"
definition path_dom :: "Path \<Rightarrow> nat set" where [simp]: "path_dom P = {i. P i \<noteq> None}"
(* The set of nodes that occur infinitely often on a given path. *)
definition path_inf :: "Path \<Rightarrow> Vertex set" where
  "path_inf P \<equiv> {v. (\<exists>i. P i = Some v) \<and> (\<forall>i. P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v))}"

lemma paths_are_contiguous:
  assumes "infinite_path P \<or> finite_path P"
  shows "P i \<noteq> None \<Longrightarrow> \<forall>j \<le> i. P j \<noteq> None"
  by (metis assms finite_path_def infinite_path_def leD le_less_linear le_trans)
lemma path_dom_ends_on_finite_paths:
  assumes finite: "finite_path P"
  shows "\<exists>!i \<in> path_dom P. P (i + 1) = None"
  proof -
    obtain i where "\<forall>j. (j > i \<longleftrightarrow> P j = None)" using finite by fastforce
    hence "i \<in> path_dom P \<and> P (i + 1) = None" by auto
    thus ?thesis
      by (metis (mono_tags, lifting) One_nat_def add.right_neutral add_Suc_right finite finite_path_def less_Suc_eq mem_Collect_eq path_dom_def)
  qed

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
definition deadend :: "Vertex \<Rightarrow> bool" where [simp]: "deadend v \<equiv> \<not>(\<exists>w \<in> V. (v,w) \<in> E)"
definition valid_path :: "Path \<Rightarrow> bool" where
  [simp]: "valid_path P \<equiv> (infinite_path P \<or> finite_path P)
    \<and> (\<forall>i \<in> path_dom P. the (P i) \<in> V
      \<and> (\<not>deadend (the (P i)) \<longrightarrow> (the (P i), the (P (i+1))) \<in> E))"
end

datatype Player = Even | Odd
fun other_player :: "Player \<Rightarrow> Player" where "other_player Even = Odd" | "other_player Odd = Even"
notation other_player ("(_**)" [1000] 1000)
fun winning_priority :: "Player \<Rightarrow> nat \<Rightarrow> bool" where
  "winning_priority Even = even"
  | "winning_priority Odd = odd"
lemma winning_priority_for_one_player:
  shows "winning_priority p i \<longleftrightarrow> \<not>winning_priority p** i"
  by (metis (full_types) Player.distinct(1) other_player.simps(1) other_player.simps(2) winning_priority.elims)

locale ParityGame = Digraph +
  fixes priority :: "Vertex \<Rightarrow> nat" ("\<omega>")
    and player0 :: "Vertex set"
  assumes valid_player0_set: "player0 \<subseteq> V"
begin
  fun VV :: "Player \<Rightarrow> Vertex set" where "VV Even = player0" | "VV Odd = V - player0"
end

(* The set of priorities that occur infinitely often on a given path. *)
definition (in ParityGame) path_inf_priorities :: "Path \<Rightarrow> nat set" where
  "path_inf_priorities P \<equiv> {\<omega> v | v. v \<in> path_inf P}"

(* True iff \<sigma> is defined on all non-deadend nodes of the given player. *)
definition (in ParityGame) positional_strategy :: "Player \<Rightarrow> Strategy \<Rightarrow> bool" where
  "positional_strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"

definition (in ParityGame) path_conforms_with_strategy :: "Player \<Rightarrow> Path \<Rightarrow> Strategy \<Rightarrow> bool" where
  "path_conforms_with_strategy p P \<sigma> \<equiv> (\<forall>i \<in> path_dom P. the (P i) \<in> VV p \<longrightarrow> \<sigma>(the (P i)) = P (i+1))"

lemma (in "ParityGame") path_inf_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>v. v \<in> path_inf P"
  proof -
    from assms have "\<forall>i. the (P i) \<in> V" by simp
    hence "\<exists>v \<in> V. (\<exists>i. the (P i) = v) \<and> (\<forall>i. (the (P i) = v \<longrightarrow> (\<exists>j > i. the (P j) = v)))"
      using pigeon_hole_principle[of "V" "\<lambda>i. the (P i)"] finite_vertex_set by blast
    hence "\<exists>v \<in> V. (\<exists>i. P i = Some v) \<and> (\<forall>i. (P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v)))" by (metis assms(2) infinite_path_def option.collapse)
    thus "?thesis" using path_inf_def valid_path_def assms by auto
  qed

lemma (in "ParityGame") path_inf_priorities_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>a. a \<in> path_inf_priorities P"
  using assms path_inf_is_nonempty[of P] path_inf_priorities_def by auto

lemma (in "ParityGame") path_inf_priorities_has_minimum:
  assumes "valid_path P" "infinite_path P"
  obtains a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)"
  proof -
    have "\<exists>a. a \<in> path_inf_priorities P" using assms path_inf_priorities_is_nonempty by blast
    then obtain a where "a \<in> path_inf_priorities P" "(\<And>z. z < a \<Longrightarrow> z \<notin> path_inf_priorities P)"
      by (metis less_eq less_than_def wf_less_than wfE_min)
    thus ?thesis by (metis leI that)
  qed

(* True iff the path is winning for the given player. *)
definition (in ParityGame) winning_path :: "Player \<Rightarrow> Path \<Rightarrow> bool" where
  [simp]: "winning_path p P \<equiv>
    (infinite_path P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (finite_path P \<and> (\<exists>i \<in> path_dom P. P (i+1) = None \<and> the (P i) \<in> VV p**))"

lemma (in "ParityGame") paths_are_winning_for_exactly_one_player:
  assumes "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
  proof (cases)
    assume infinite: "infinite_path P"
    then obtain a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using assms path_inf_priorities_has_minimum by blast
    thus ?thesis by (metis infinite infinite_path_def le_antisym winning_path_def winning_priority_for_one_player)
  next
    assume not_infinite: "\<not>infinite_path P"
    hence finite: "finite_path P" using assms valid_path_def by blast
    then obtain i where i_def: "i \<in> path_dom P \<and> P (i+1) = None" using assms path_dom_ends_on_finite_paths by blast
    def v \<equiv> "the (P i)" (* the last vertex in the path *)
    have "\<And>q. winning_path q P \<longleftrightarrow> (\<exists>i \<in> path_dom P. P (i+1) = None \<and> the (P i) \<in> VV q**)"
      using not_infinite finite winning_path_def by blast
    hence "\<And>q. winning_path q P \<longleftrightarrow> v \<in> VV q**"
      using not_infinite finite path_dom_ends_on_finite_paths i_def v_def by blast
    hence "v \<in> VV p** \<longleftrightarrow> \<not>v \<in> VV p \<Longrightarrow> ?thesis"
      by (metis (full_types) Player.exhaust other_player.simps(1) other_player.simps(2))
    thus ?thesis
      by (metis (full_types) Diff_iff Player.exhaust VV.simps(1) VV.simps(2) assms i_def other_player.simps(1) other_player.simps(2) valid_path_def v_def)
  qed

lemma (in "ParityGame") paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "\<exists>!p. winning_path p P"
  by (metis (full_types) VV.elims assms paths_are_winning_for_exactly_one_player)

definition (in ParityGame) winning_strategy :: "Player \<Rightarrow> Strategy \<Rightarrow> Vertex \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v \<equiv> \<forall>P. P 0 = Some v \<longrightarrow> path_conforms_with_strategy p P \<sigma> \<longrightarrow> winning_path p P"

definition (in ParityGame) trap :: "Player \<Rightarrow> Vertex set \<Rightarrow> bool" where
  "trap p A \<equiv> (\<forall>v \<in> A. \<not>deadend v \<longrightarrow>
    (v \<in> VV p** \<longrightarrow> (\<exists>(v,w) \<in> E. w \<in> A))
    \<and> (v \<in> VV p \<longrightarrow> (\<forall>(v,w) \<in> E. w \<in> A)))"

(* The attractor set of a given set of vertices. *)
inductive_set (in ParityGame) attractor :: "Player \<Rightarrow> Vertex set \<Rightarrow> Vertex set"
  for p :: Player and W :: "Vertex set" where
  [intro!]: "v \<in> W \<Longrightarrow> v \<in> attractor p W" |
  "v \<in> VV p \<Longrightarrow> \<exists>(v,w) \<in> E. w \<in> attractor p W \<Longrightarrow> v \<in> attractor p W" |
  "\<not>deadend v \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<forall>(v,w) \<in> E. w \<in> attractor p W \<Longrightarrow> v \<in> attractor p W"

lemma (in "ParityGame") attractor_is_superset:
  shows "W \<subseteq> attractor p W" by (simp add: attractor.intros(1) subsetI)

lemma (in "ParityGame") attractor_is_bounded_by_V:
  assumes "W \<subseteq> V" shows "attractor p W \<subseteq> V"
  proof -
    { fix v assume "v \<in> attractor p W"
      hence "v \<in> W \<or> v \<in> VV p \<or> v \<in> VV p**" using attractor.simps by blast
      hence "v \<in> V" by (metis (full_types) Diff_subset VV.elims assms subsetCE valid_player0_set)
    }
    thus ?thesis by blast
  qed

lemma (in "ParityGame") attractor_is_finite:
  assumes "W \<subseteq> V" shows "finite (attractor p W)" by (metis assms attractor_is_bounded_by_V finite_vertex_set rev_finite_subset)

(* True iff the given set is attractor closed. *)
definition (in ParityGame) attractor_closed :: "Player \<Rightarrow> Vertex set \<Rightarrow> bool" where
  "attractor_closed p W \<equiv> \<forall>v \<in> V.
    (v \<in> VV p - W \<longrightarrow> (\<forall>(v,w) \<in> E. w \<notin> W))
    \<and> (\<not>deadend v \<and> v \<in> VV p** - W \<longrightarrow> (\<exists>(v,w) \<in> E. w \<notin> W))"

(* Show that the attractor set is indeed attractor closed. *)
lemma (in "ParityGame") attractor_is_attractor_closed:
  shows "attractor_closed p (attractor p W)"
  proof -
    def A \<equiv> "attractor p W"
    {
      fix v assume "v \<in> VV p - A"
      hence "\<forall>(v,w) \<in> E. w \<notin> A" by (metis A_def DiffD1 DiffD2 attractor.intros(2) case_prodI2 splitI)
    } moreover
    {
      fix v assume "v \<in> VV p** - A" "\<not>deadend v"
      hence "\<exists>(v,w) \<in> E. w \<notin> A" by (metis A_def DiffD1 DiffD2 attractor.intros(3) case_prodI2 splitI)
    }
    ultimately show ?thesis using A_def by (metis Diff_iff attractor_closed_def)
  qed

(* Maybe something like the following is useful for proofs by induction? *)
lemma (in "ParityGame")
  assumes "W \<subseteq> V" and "A = attractor p W" and "W \<noteq> {}"
  shows "\<exists>x \<in> V. \<forall>v \<in> A. v \<in> W
    \<or> (v \<in> VV p \<and> (\<exists>(v,w) \<in> E. w \<in> A))
    \<or> (\<not>deadend v \<and> v \<in> VV p** \<and> (\<forall>(v,w) \<in> E. w \<in> A))"
  proof-
    show ?thesis sorry
  qed

definition (in ParityGame) absorbed :: "Vertex \<Rightarrow> (Vertex list) set \<Rightarrow> bool" where
  "absorbed v T \<equiv> (\<exists>q \<in> T. hd q = v) \<or> (\<forall>(v,w) \<in> E. \<exists>q \<in> T. hd q = w)"

lemma (in ParityGame) absorbed_mono:
  assumes "A \<subseteq> B"
  shows "absorbed v A \<longrightarrow> absorbed v B"
  proof-
    { fix v assume 0: "absorbed v A"
      have "absorbed v B" proof cases
        assume "\<exists>q \<in> A. hd q = v"
        thus ?thesis using absorbed_def assms by blast
      next
        assume "\<not>(\<exists>q \<in> A. hd q = v)"
        thus ?thesis using 0 absorbed_def assms by fastforce
      qed
    }
    thus ?thesis using assms by blast
  qed

inductive_set (in ParityGame) attractor_pre_strategy :: "Player \<Rightarrow> Vertex set \<Rightarrow> (Vertex list) set"
  for p :: Player and W :: "Vertex set" where
  "v \<in> W \<Longrightarrow> [v] \<in> attractor_pre_strategy p W" |
  "w#rest \<in> attractor_pre_strategy p W \<Longrightarrow> v \<in> VV p \<Longrightarrow> (v,w) \<in> E
    \<Longrightarrow> v#(w#rest) \<in> attractor_pre_strategy p W" |
  "w#rest \<in> attractor_pre_strategy p W \<Longrightarrow> v \<in> VV p** \<Longrightarrow> (v,w) \<in> E
    \<Longrightarrow> absorbed v (attractor_pre_strategy p W)
    \<Longrightarrow> v#(w#rest) \<in> attractor_pre_strategy p W"
  monos absorbed_mono

lemma (in ParityGame)
  assumes "v \<in> attractor p W" and "v \<notin> W"
  shows "\<exists>q \<in> attractor_pre_strategy p W. hd q = v"
  sorry

lemma (in ParityGame)
  assumes "q \<in> attractor_pre_strategy p W" and "last q = v"
  shows "v \<in> W"
  sorry

lemma (in "ParityGame") attractor_has_strategy:
  shows "\<exists>\<sigma>. positional_strategy p \<sigma> \<and> (\<forall>v \<in> attractor p W. \<forall>P. P 0 = Some v \<and> path_conforms_with_strategy p P \<sigma> \<longrightarrow> (\<exists>v \<in> path_dom P. v \<in> W))"
  proof -
    have closed: "attractor_closed p (attractor p W)" using attractor_is_attractor_closed by simp
    {
      assume "v \<in> attractor p W" and "v \<notin> W"
      hence "v \<in> VV p - W \<or> v \<in> VV p** - W" using attractor.simps by blast
      {
        assume "v \<in> VV p - W"
        hence "\<exists>(v,w) \<in> E. w \<in> attractor p W" using closed sorry
      }
    }
  qed

theorem (in "ParityGame") positional_strategy_exist_for_single_prio_games:
  assumes "v \<in> V"
  and "\<forall>w \<in> V. \<omega>(w) = 0"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    {
      fix P :: "Path"
      assume "valid_path P" "infinite_path P"
      then obtain v where "v \<in> path_inf P" using path_inf_is_nonempty by blast
      then obtain i where "P i = Some v" using path_inf_def by auto
      hence "v \<in> V" using assms using `valid_path P`
        by (metis (no_types) domI dom_def option.sel path_dom_def valid_path_def)
      hence "\<omega>(v) = 0" using assms by blast
      hence "winning_path Even P" sorry
      obtain p where "winning_path p P" using paths_are_winning_for_one_player by blast
      hence "p = Even" sorry
    }
    show ?thesis sorry
  qed

theorem (in "ParityGame") positional_strategy_exists:
  assumes "v \<in> V"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    show ?thesis sorry
  qed

end
