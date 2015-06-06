theory parity_games
imports
  Main
  pigeon_hole_principle
begin

(* 'a is the vertex type. *)

type_synonym 'a Edge = "'a \<times> 'a"
type_synonym 'a Path = "nat \<Rightarrow> 'a option"
type_synonym 'a Strategy = "'a \<Rightarrow> 'a option"
definition infinite_path :: "'a Path \<Rightarrow> bool" where [simp]: "infinite_path P \<equiv> \<forall>i. P i \<noteq> None"
definition finite_path :: "'a Path \<Rightarrow> bool" where [simp]: "finite_path P \<equiv> \<exists>i. \<forall>j. (j > i \<longleftrightarrow> P j = None)"
definition path_dom :: "'a Path \<Rightarrow> nat set" where [simp]: "path_dom P = {i. P i \<noteq> None}"
(* The set of nodes that occur infinitely often on a given path. *)
definition path_inf :: "'a Path \<Rightarrow> 'a set" where
  "path_inf P \<equiv> {v. (\<exists>i. P i = Some v) \<and> (\<forall>i. P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v))}"
definition path_tail :: "'a Path \<Rightarrow> 'a Path" where [simp]: "path_tail P \<equiv> \<lambda>i. P (i+1)"

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

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
definition is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  [simp]: "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

locale Digraph =
  fixes G (structure)
  assumes finite_vertex_set: "finite V"
    and non_empty_vertex_set: "V \<noteq> {}"
    and valid_edge_set: "E \<subseteq> V \<times> V"
begin

definition deadend :: "'a \<Rightarrow> bool" where "deadend v \<equiv> \<not>(\<exists>w \<in> V. v \<rightarrow> w)"
definition valid_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "valid_path P \<equiv> P 0 \<noteq> None \<and> (infinite_path P \<or> finite_path P)
      \<and> (\<forall>i. P i \<noteq> None \<longrightarrow> the (P i) \<in> V)
      \<and> (\<forall>i. P i \<noteq> None \<and> P (i+1) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (i+1)))"
definition maximal_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "maximal_path P \<equiv> \<forall>i. P i \<noteq> None \<and> \<not>deadend (the (P i)) \<longrightarrow> P (i+1) \<noteq> None"
end

lemma (in Digraph) maximal_infinite_path_tail [intro]:
  "maximal_path P \<Longrightarrow> maximal_path (path_tail P)"
  using assms by auto

datatype Player = Even | Odd
fun other_player :: "Player \<Rightarrow> Player" where "other_player Even = Odd" | "other_player Odd = Even"
notation other_player ("(_**)" [1000] 1000)
lemma [simp]: "p**** = p" by (metis other_player.elims)

record 'a ParityGame = "'a Graph" +
  priority :: "'a \<Rightarrow> nat" ("\<omega>\<index>")
  player0 :: "'a set" ("V0\<index>")

fun winning_priority :: "Player \<Rightarrow> nat \<Rightarrow> bool" where
  "winning_priority Even = even"
  | "winning_priority Odd = odd"
lemma winning_priority_for_one_player:
  shows "winning_priority p i \<longleftrightarrow> \<not>winning_priority p** i"
  by (metis (full_types) Player.distinct(1) other_player.simps(1) other_player.simps(2) winning_priority.elims)

locale ParityGame = Digraph G for G :: "('a, 'b) ParityGame_scheme" (structure) +
  assumes valid_player0_set: "V0 \<subseteq> V"

fun (in ParityGame) VV :: "Player \<Rightarrow> 'a set" where "VV Even = V0" | "VV Odd = V - V0"
lemma (in ParityGame) [intro]: "v \<in> VV p \<Longrightarrow> v \<in> V" by (metis (full_types) Diff_subset VV.elims subsetCE valid_player0_set)

(* The set of priorities that occur infinitely often on a given path. *)
definition (in ParityGame) path_inf_priorities :: "'a Path \<Rightarrow> nat set" where
  "path_inf_priorities P \<equiv> {\<omega> v | v. v \<in> path_inf P}"

definition (in ParityGame) strategy_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_on p \<sigma> W \<equiv> \<forall>v \<in> W \<inter> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"
definition (in ParityGame) strategy_only_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_only_on p \<sigma> W \<equiv> (\<forall>v \<in> W \<inter> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None) \<and> (\<forall>v. v \<notin> W \<inter> VV p \<longrightarrow> \<sigma> v = None)"

lemma (in ParityGame) strategy_subset [intro]:
  "\<lbrakk> W' \<subseteq> W; strategy_on p \<sigma> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'" using strategy_on_def by auto
lemma (in ParityGame) strategy_on_empty_set [simp]:
  "strategy_on p \<sigma> {}" by (simp add: strategy_on_def)
lemma (in ParityGame) strategy_only_on_empty_set_exists:
  "\<exists>\<sigma>. strategy_only_on p \<sigma> {}" proof -
    have "strategy_only_on p (\<lambda>_. None) {}" using strategy_only_on_def by auto
    thus ?thesis by auto
  qed
lemma (in ParityGame) strategy_only_on_on [intro]:
  "strategy_only_on p \<sigma> W \<Longrightarrow> strategy_on p \<sigma> W" by (simp add: strategy_on_def strategy_only_on_def)
lemma (in ParityGame) strategy_only_on_on_subset [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; W' \<subseteq> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'" by (simp add: strategy_only_on_on strategy_subset)
lemma (in ParityGame) strategy_only_on_elements [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<notin> W \<rbrakk> \<Longrightarrow> \<sigma> v = None" using strategy_only_on_def by auto
lemma (in ParityGame) strategy_only_on_case_rule [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<in> VV p - W \<rbrakk> \<Longrightarrow> strategy_only_on p (\<sigma>(v \<mapsto> w)) (insert v W)" using strategy_only_on_def by auto
lemma (in ParityGame) strategy_only_on_case_rule2 [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<notin> VV p \<rbrakk> \<Longrightarrow> strategy_only_on p \<sigma> (insert v W)" using strategy_only_on_def by auto

definition restrict_path :: "'a Path \<Rightarrow> 'a set \<Rightarrow> 'a Path" (infixl "\<restriction>\<^sub>P" 80) where
  "restrict_path P W \<equiv> \<lambda>i. if the (P i) \<in> W then P i else None"
definition restrict_strategy :: "'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a Strategy" (infixl "\<restriction>\<^sub>S" 80) where
  "restrict_strategy \<sigma> W \<equiv> \<lambda>v. if v \<in> W \<and> the (\<sigma> v) \<in> W then \<sigma> v else None"

lemma (in ParityGame) restricted_strategy_invariant [simp]:
  assumes "v \<in> W" "the (\<sigma> v) \<in> W"
  shows "(\<sigma> \<restriction>\<^sub>S W) v = \<sigma> v"
  by (simp add: assms restrict_strategy_def)

(* lemma (in ParityGame) restricted_strategy [intro]:
  assumes "strategy_on p (\<sigma> :: 'a Strategy) (W :: 'a set)"
  shows "strategy_on p (\<sigma> \<restriction>\<^sub>S W) W"
  using assms strategy_on_def by auto
*)

lemma (in ParityGame) restricted_path_invariant [simp]:
  assumes "the (P i) \<in> W"
  shows "(P \<restriction>\<^sub>P W) i = P i"
  by (simp add: assms restrict_path_def)

lemma (in ParityGame) restricted_path_dom [simp]:
  assumes "i \<in> path_dom (P \<restriction>\<^sub>P W)"
  shows "i \<in> path_dom P"
  by (metis (mono_tags, lifting) assms mem_Collect_eq path_dom_def restrict_path_def)

(* True iff \<sigma> is defined on all non-deadend nodes of the given player. *)
definition (in ParityGame) positional_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "positional_strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"

definition (in ParityGame) path_conforms_with_strategy :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy p P \<sigma> \<equiv> (\<forall>i. P i \<noteq> None \<and> the (P i) \<in> VV p \<longrightarrow> \<sigma> (the (P i)) = P (i+1))"

lemma (in ParityGame) infinite_path_tail [intro]:
  "infinite_path P \<Longrightarrow> infinite_path (path_tail P)" using assms by auto
lemma (in ParityGame) finite_path_tail [intro]:
  assumes "finite_path P" "P 1 \<noteq> None" shows "finite_path (path_tail P)"
  proof -
    obtain i where i_def: "\<forall>j. (i < j) = (P j = None)" using assms(1) finite_path_def by blast
    hence "i > 0" using assms(2) by force
    hence "\<forall>j. (i-1 < j) = (path_tail P j = None)" unfolding path_tail_def by (simp add: i_def Suc_leI less_diff_conv2)
    thus ?thesis by auto
  qed

lemma (in ParityGame) valid_path_tail [simp]:
  assumes "valid_path P" "P 1 \<noteq> None"
  shows "valid_path (path_tail P)"
  proof -
    have "path_tail P 0 \<noteq> None" using assms(2) by auto
    moreover have "infinite_path (path_tail P) \<or> finite_path (path_tail P)" using assms valid_path_def by blast
    ultimately show ?thesis using assms by auto
  qed

lemma (in ParityGame) infinite_path_tail_conforms [intro]:
  assumes "path_conforms_with_strategy p P \<sigma>"
  shows "path_conforms_with_strategy p (path_tail P) \<sigma>"
  using assms path_conforms_with_strategy_def by auto

lemma (in ParityGame) infinite_path_tail_head [simp]:
  assumes "P 0 = Some v" "v \<in> VV p" "\<sigma> v = Some w" "path_conforms_with_strategy p P \<sigma>"
  shows "Some w = P 1"
  using assms by auto

definition (in ParityGame) strategy_less_eq :: "'a Strategy \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy_less_eq \<sigma> \<sigma>' \<equiv> \<forall>v. case \<sigma> v of Some y \<Rightarrow> \<sigma>' v = Some y | None \<Rightarrow> True"

lemma (in ParityGame) strategy_less_eq_updates:
  assumes "\<sigma> v = None"
  shows "strategy_less_eq \<sigma> (\<sigma>(v \<mapsto> w))"
  by (simp add: assms option.case_eq_if strategy_less_eq_def)

lemma (in ParityGame) strategy_on_is_monotone:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_on p \<sigma> W"
  shows "strategy_on p \<sigma>' W"
  proof-
    { fix v assume "v \<in> W \<inter> VV p" "\<not>deadend v"
      hence "\<sigma> v \<noteq> None" using assms(2) strategy_on_def by blast
      hence "\<sigma>' v \<noteq> None" using assms(1) by (simp add: strategy_less_eq_def option.case_eq_if)
    }
    thus ?thesis by (simp add: strategy_on_def)
  qed

lemma (in ParityGame) strategy_less_eq_tran:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_less_eq \<sigma>' \<sigma>''"
  shows "strategy_less_eq \<sigma> \<sigma>''" proof (unfold strategy_less_eq_def; clarify)
    fix v show "case \<sigma> v of None \<Rightarrow> True | Some y \<Rightarrow> \<sigma>'' v = Some y" proof (cases)
      assume "\<sigma> v = None" thus ?thesis by simp
    next
      assume "\<sigma> v \<noteq> None"
      then obtain y where y_def: "\<sigma> v = Some y" by auto
      hence "\<sigma>' v = Some y" using assms(1) by (simp add: option.case_eq_if strategy_less_eq_def)
      hence "\<sigma>'' v = Some y" using assms(2) by (simp add: option.case_eq_if strategy_less_eq_def)
      thus ?thesis by (simp add: y_def)
    qed
  qed

(*
lemma (in ParityGame) restricted_strategy_paths:
  assumes "path_conforms_with_strategy p P \<sigma>"
  shows "path_conforms_with_strategy p (P \<restriction>\<^sub>P W) (\<sigma> \<restriction>\<^sub>S W)"
  proof (unfold path_conforms_with_strategy_def; clarify)
    let ?P' = "P \<restriction>\<^sub>P W"
    let ?\<sigma>' = "\<sigma> \<restriction>\<^sub>S W"
    fix i v assume i: "i \<in> path_dom ?P'" and Pi: "the (?P' i) \<in> VV p" "?P' i = Some v"
    hence "v \<in> W" by (metis option.distinct(1) option.sel restrict_path_def)
    moreover
    have Pii: "?P' i = P i" by (metis Pi(2) option.distinct(1) restrict_path_def)
    moreover
    hence "the (P i) \<in> VV p" using Pi(1) by auto
    moreover
    have "i \<in> path_dom P" using i restricted_path_dom by blast
    ultimately have \<sigma>: "\<sigma>(the (P i)) = P (i+1)" using Pi(2) assms path_conforms_with_strategy_def by auto

    show "?\<sigma>'(the (?P' i)) = ?P' (i+1)" proof (cases)
      assume "the (P (i+1)) \<in> W" thus ?thesis using Pi(2) Pii \<sigma> `v \<in> W` by auto
    next
      assume "the (P (i+1)) \<notin> W" thus ?thesis using Pi(2) Pii \<sigma> `v \<in> W` by (simp add: restrict_path_def restrict_strategy_def)
    qed
  qed

lemma (in ParityGame) restricted_strategy_paths_inv:
  assumes "path_conforms_with_strategy p P (\<sigma> \<restriction>\<^sub>S W)"
    "\<forall>i \<in> path_dom P. the (P i) \<in> W"
  shows "path_conforms_with_strategy p P \<sigma>"
  proof (unfold path_conforms_with_strategy_def; clarify)
    fix i v assume i: "i \<in> path_dom P" and Pi: "the (P i) \<in> VV p" "P i = Some v"
    hence "the (P i) \<in> W" using assms(2) by auto
    { assume "P (i+1) = None"
      have "\<sigma>(the (P i)) = P (i+1)" by sledgehamme
      have "(\<sigma> \<restriction>\<^sub>S W)(the (P i)) = P (i+1)" using Pi(1) assms(1) i path_conforms_with_strategy_def by auto
    }
    { assume "P (i+1) \<noteq> None"
      have "(\<sigma> \<restriction>\<^sub>S W)(the (P i)) = P (i+1)" using Pi(1) assms(1) i path_conforms_with_strategy_def by auto
    }
    show "\<sigma>(the (P i)) = P (i+1)" sorry
  qed
*)

lemma (in ParityGame) VV_impl1 [intro]: "v \<in> VV p \<Longrightarrow> v \<notin> VV p**"
  by (metis (full_types) Diff_iff VV.elims VV.simps(1) VV.simps(2) other_player.simps(1) other_player.simps(2))
lemma (in ParityGame) VV_impl2 [intro]: "v \<in> VV p** \<Longrightarrow> v \<notin> VV p"
  using VV_impl1 by blast
lemma (in ParityGame) VV_equivalence [simp]:
  "v \<in> V \<Longrightarrow> v \<notin> VV p \<longleftrightarrow> v \<in> VV p**"
  by (metis (full_types) Diff_iff assms local.VV.simps(1) local.VV.simps(2) other_player.simps(1) other_player.simps(2) winning_priority.cases)
lemma (in ParityGame) VV_cases:
  "\<lbrakk> v \<in> V ; v \<in> VV p \<Longrightarrow> P ; v \<in> VV p** \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using assms by (metis (full_types) Diff_iff VV.elims VV.simps(1) VV.simps(2) other_player.simps(1) other_player.simps(2))

lemma (in ParityGame) path_inf_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>v. v \<in> path_inf P"
  proof -
    from assms have P_total: "\<And>i v. the (P i) = v \<longleftrightarrow> P i = Some v" by auto
    from assms have "\<forall>i. the (P i) \<in> V" by simp
    hence "\<exists>v. (\<exists>i. the (P i) = v) \<and> (\<forall>i. (the (P i) = v \<longrightarrow> (\<exists>j > i. the (P j) = v)))"
      using pigeon_hole_principle[of "V" "\<lambda>i. the (P i)"] finite_vertex_set by blast
    hence "\<exists>v. (\<exists>i. P i = Some v) \<and> (\<forall>i. (P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v)))" using P_total by auto
    thus ?thesis by (simp add: path_inf_def)
  qed

lemma (in ParityGame) path_inf_priorities_is_nonempty:
  assumes "valid_path P" "infinite_path P"
  shows "\<exists>a. a \<in> path_inf_priorities P"
  using assms path_inf_is_nonempty[of P] path_inf_priorities_def by auto

lemma (in ParityGame) path_inf_priorities_has_minimum:
  assumes "valid_path P" "infinite_path P"
  obtains a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)"
  proof -
    have "\<exists>a. a \<in> path_inf_priorities P" using assms path_inf_priorities_is_nonempty by blast
    then obtain a where "a \<in> path_inf_priorities P" "(\<And>z. z < a \<Longrightarrow> z \<notin> path_inf_priorities P)"
      by (metis less_eq less_than_def wf_less_than wfE_min)
    thus ?thesis by (metis leI that)
  qed

(* True iff the path is winning for the given player. *)
definition (in ParityGame) winning_path :: "Player \<Rightarrow> 'a Path \<Rightarrow> bool" where
  [simp]: "winning_path p P \<equiv>
    (infinite_path P \<and> (\<exists>a \<in> path_inf_priorities P. (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (finite_path P \<and> (\<exists>i \<in> path_dom P. P (i+1) = None \<and> the (P i) \<in> VV p**))"

lemma (in ParityGame) valid_paths_are_nonempty: "valid_path P \<Longrightarrow> P 0 \<noteq> None" by auto

lemma (in ParityGame) paths_are_winning_for_exactly_one_player:
  assumes "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
  proof (cases)
    assume infinite: "infinite_path P"
    then obtain a where "a \<in> path_inf_priorities P \<and> (\<forall>b \<in> path_inf_priorities P. a \<le> b)" using assms path_inf_priorities_has_minimum by blast
    hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" using infinite winning_path_def by (metis infinite_path_def le_antisym)
    thus ?thesis using winning_priority_for_one_player by blast
  next
    assume not_infinite: "\<not>infinite_path P"
    hence finite: "finite_path P" using assms valid_path_def by blast
    then obtain i where i_def: "i \<in> path_dom P \<and> P (i+1) = None" using assms path_dom_ends_on_finite_paths by metis
    def v \<equiv> "the (P i)" (* the last vertex in the path *)
    hence "v \<in> V" using valid_path_def using assms i_def by auto
    have "\<And>q. winning_path q P \<longleftrightarrow> (\<exists>i \<in> path_dom P. P (i+1) = None \<and> the (P i) \<in> VV q**)"
      using not_infinite finite winning_path_def by metis
    hence "\<And>q. winning_path q P \<longleftrightarrow> v \<in> VV q**"
      using not_infinite finite path_dom_ends_on_finite_paths i_def v_def by blast
    hence "v \<in> VV p** \<longleftrightarrow> \<not>v \<in> VV p \<Longrightarrow> ?thesis"
      by (metis (full_types) Player.exhaust other_player.simps(1) other_player.simps(2))
    thus ?thesis using VV_equivalence`v \<in> V` by blast
  qed

lemma (in ParityGame) paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "\<exists>!p. winning_path p P"
  by (metis (full_types) VV.elims assms paths_are_winning_for_exactly_one_player)

definition (in ParityGame) winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v \<equiv> \<forall>P. P 0 = Some v \<longrightarrow> path_conforms_with_strategy p P \<sigma> \<longrightarrow> winning_path p P"

(* The attractor set of a given set of vertices. *)
inductive_set (in ParityGame) attractor :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for p :: Player and W :: "'a set" where
  Base [intro!]: "v \<in> W \<Longrightarrow> v \<in> attractor p W" |
  VVp: "v \<in> VV p \<Longrightarrow> \<exists>w. v\<rightarrow>w \<and> w \<in> attractor p W \<Longrightarrow> v \<in> attractor p W" |
  VVpstar: "\<not>deadend v \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p W \<Longrightarrow> v \<in> attractor p W"

lemma (in ParityGame) attractor_is_superset [simp]:
  shows "W \<subseteq> attractor p W" by (simp add: attractor.intros(1) subsetI)

lemma (in ParityGame) attractor_is_bounded_by_V:
  assumes "W \<subseteq> V" shows "attractor p W \<subseteq> V"
  proof -
    { fix v assume "v \<in> attractor p W"
      hence "v \<in> W \<or> v \<in> VV p \<or> v \<in> VV p**" using attractor.simps by blast
      hence "v \<in> V" by (metis (full_types) Diff_subset VV.elims assms subsetCE valid_player0_set)
    }
    thus ?thesis by blast
  qed

lemma (in ParityGame) attractor_is_finite:
  "W \<subseteq> V \<Longrightarrow> finite (attractor p W)" by (metis assms attractor_is_bounded_by_V finite_vertex_set rev_finite_subset)

definition (in ParityGame) directly_attracted :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "directly_attracted p W \<equiv> {v \<in> V - W. \<not>deadend v \<and>
    (v \<in> VV p \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> W))
    \<and> (v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W))}"

lemma (in ParityGame) directly_attracted_is_bounded_by_V:
  shows "directly_attracted p W \<subseteq> V" using directly_attracted_def by blast
lemma (in ParityGame) directly_attracted_is_finite [simp]:
  shows "finite (directly_attracted p W)" using directly_attracted_is_bounded_by_V finite_subset finite_vertex_set by blast
lemma (in ParityGame) directly_attracted_is_disjoint_from_W [simp]:
  shows "W \<inter> directly_attracted p W = {}" using directly_attracted_def by blast
lemma (in ParityGame) directly_attracted_is_eventually_empty [simp]:
  shows "directly_attracted p V = {}" using directly_attracted_def by blast
lemma (in ParityGame) directly_attracted_contains_no_deadends [elim]:
  shows "v \<in> directly_attracted p W \<Longrightarrow> \<not>deadend v" using directly_attracted_def by blast
lemma (in ParityGame) directly_attracted_empty_set:
  shows "directly_attracted p {} = {}" proof (rule ccontr)
    assume "directly_attracted p {} \<noteq> {}"
    then obtain v where v: "v \<in> directly_attracted p {}" by auto
    have "v \<in> V" using directly_attracted_def v by blast
    thus False proof (cases rule: VV_cases)
      assume "v \<in> VV p" thus "False" using directly_attracted_def v by blast
    next
      assume "v \<in> VV p**"
      have "\<not>deadend v" using directly_attracted_def v by blast
      moreover have "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> {}" using directly_attracted_def v by blast
      ultimately show "False" using deadend_def by blast
    qed
  qed

lemma (in ParityGame) attractor_contains_no_deadends:
  assumes "v \<in> attractor p W"
  shows "v \<in> W \<or> \<not>deadend v"
  using assms
  proof (induct rule: attractor.induct)
    fix v assume "v \<in> W" thus "v \<in> W \<or> \<not>deadend v" by simp
  next
    fix v assume "v \<in> VV p" and "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p W \<and> (w \<in> W \<or> \<not>deadend w)"
    thus "v \<in> W \<or> \<not>deadend v" using local.deadend_def local.valid_edge_set by auto
  next
    fix v assume "\<not>deadend v"
    thus "v \<in> W \<or> \<not>deadend v" by simp
  qed

lemma (in ParityGame) attractor_as_lfp:
  "attractor p W = lfp (\<lambda>A. W \<union> A \<union> (directly_attracted p A))"
  proof -
    show ?thesis sorry
  qed

(* True iff the given set is attractor closed. *)
definition (in ParityGame) attractor_closed :: "Player \<Rightarrow> 'a set \<Rightarrow> bool" where
  "attractor_closed p W \<equiv> directly_attracted p W = {}"

(* Show that the attractor set is indeed attractor closed. *)
(*
lemma (in ParityGame) attractor_is_attractor_closed [simp]:
  shows "attractor_closed p (attractor p W)"
  proof -
    def A \<equiv> "attractor p W"
    {
      fix v assume v_assm: "v \<in> V - A"
      hence "v \<in> V" by auto
      hence "v \<in> VV p \<or> v \<in> VV p**" by (metis (full_types) DiffI Player.distinct(1) local.VV.elims other_player.simps(1) other_player.simps(2))
      hence "v \<in> VV p - A \<or> v \<in> VV p** - A" using v_assm by auto
    } note VV_A_disjoint = this
    have "directly_attracted p A = {}" proof -
      { fix v assume v_def: "v \<in> directly_attracted p A"
        hence v_dom: "v \<in> V - A" using directly_attracted_def by auto
        hence False proof (cases)
          assume v_in_VVp: "v \<in> VV p - A"
          hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<notin> A" by (metis A_def DiffD1 DiffD2 local.attractor.intros(2))
          thus ?thesis using v_def directly_attracted_def v_in_VVp by blast
        next
          assume "v \<notin> VV p - A"
          hence v_in_VVp_star: "v \<in> VV p** - A" using VV_A_disjoint v_dom by blast
          hence "\<not>deadend v \<Longrightarrow> \<exists>w. v\<rightarrow>w \<and> w \<notin> A" by (metis A_def DiffD1 DiffD2 local.attractor.intros(3))
          thus ?thesis using v_def directly_attracted_def v_in_VVp_star by blast
        qed
      }
      thus ?thesis by auto
    qed
    thus ?thesis by (simp add: A_def local.attractor_closed_def)
  qed
*)

lemma (in ParityGame) attractor_set_induction:
  fixes p :: Player and W :: "'a set" and P :: "'a set \<Rightarrow> bool"
  assumes "W \<subseteq> V" and "P W"
    and "\<And>W'. W \<subseteq> W' \<Longrightarrow> W' \<subseteq> V \<Longrightarrow> P W' \<Longrightarrow> P (W' \<union> (directly_attracted p W'))"
    and "\<And>M. \<forall>W'\<in>M. W \<subseteq> W' \<and> W' \<subseteq> V \<and> P W' \<Longrightarrow> P (\<Union>M)"
  shows "P (attractor p W)"
  proof -
    def f \<equiv> "\<lambda>A. W \<union> A \<union> (directly_attracted p A)"
    have "P (lfp f)" proof (induct rule: lfp_ordinal_induct)
      show "mono f" sorry
      show "\<And>S. P S \<Longrightarrow> P (f S)" sorry
      show "\<And>M. \<forall>S\<in>M. P S \<Longrightarrow> P (\<Union>M)" sorry
    qed
    thus ?thesis using attractor_as_lfp f_def by simp
  qed

lemma (in ParityGame) attractor_induction:
  fixes p :: Player and W :: "'a set" and P :: "'a set \<Rightarrow> bool"
  assumes "W \<subseteq> V" and "P W"
    and "\<And>W' v. W \<subseteq> W' \<Longrightarrow> W' \<subseteq> V \<Longrightarrow> P W' \<Longrightarrow> v \<in> directly_attracted p W' \<Longrightarrow> P (insert v W')"
    and "\<And>M. \<forall>W'\<in>M. W \<subseteq> W' \<and> W' \<subseteq> V \<and> P W' \<Longrightarrow> P (\<Union>M)"
  shows "P (attractor p W)"
  proof (induct rule: attractor_set_induction)
    show "W \<subseteq> V" using assms(1) .
    show "P W" using assms(2) .
    show "\<And>M. \<forall>W'\<in>M. W \<subseteq> W' \<and> W' \<subseteq> V \<and> P W' \<Longrightarrow> P (\<Union>M)" using assms(4) .
    fix W' assume IH: "W \<subseteq> W'" "W' \<subseteq> V" "P W'"
    hence "finite W'" using finite_vertex_set rev_finite_subset by blast
    thus "P (W' \<union> (directly_attracted p W'))" using IH proof (induct W' rule: finite_induct)
      case empty
      moreover have "directly_attracted p {} = {}" by (simp add: directly_attracted_empty_set)
      ultimately show "P ({} \<union> directly_attracted p {})" by simp
    next
      case (insert v W')
      show ?case sorry
    qed
  qed

lemma (in ParityGame) attractor_has_strategy:
  fixes W p v
  defines "A \<equiv> attractor p W"
  assumes "W \<subseteq> V" "v \<in> A"
  shows "\<exists>\<sigma>. strategy_only_on p \<sigma> (A - W)
    \<and> (\<forall>\<sigma>' P. strategy_less_eq \<sigma> \<sigma>' \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> A
      \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))"
  proof -
    def P \<equiv> "\<lambda>A. \<exists>\<sigma>. strategy_only_on p \<sigma> (A - W) \<and> (\<forall>\<sigma>' P. strategy_less_eq \<sigma> \<sigma>' \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> A \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))"
    have "P (attractor p W)" proof (rule attractor_induction, simp add: assms)
      obtain \<sigma> where \<sigma>_empty: "strategy_only_on p \<sigma> {}" using strategy_only_on_empty_set_exists by auto
      { fix \<sigma>' :: "'a Strategy" and P :: "'a Path"
        assume "valid_path P"
        hence "P 0 \<noteq> None" using valid_path_def by auto
        moreover assume "the (P 0) \<in> W"
        ultimately have "\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W" by auto
      }
      hence "\<forall>\<sigma>' P. strategy_less_eq \<sigma> \<sigma>' \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> W \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W)" by auto
      thus "P W" using \<sigma>_empty P_def by auto
    next
      fix W' v assume W': "W' \<subseteq> V" "P W'" and v: "v \<in> directly_attracted p W'"
      then obtain \<sigma> where \<sigma>: "strategy_only_on p \<sigma> (W' - W)" "\<forall>\<sigma>' P. strategy_less_eq \<sigma> \<sigma>' \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> W' \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W)" using P_def W'(2) by blast
      have "\<exists>\<sigma>. strategy_only_on p \<sigma> ((insert v W') - W) \<and> (\<forall>\<sigma>' P. strategy_less_eq \<sigma> \<sigma>' \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> (insert v W') \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))" proof (cases)
        assume "v \<in> W'"
        hence "insert v W' = W'" by auto
        thus ?thesis using \<sigma> by auto
      next
        assume "v \<notin> W'" note v = v this
        show ?thesis proof(cases)
          assume "v \<in> VV p" note v = v this
          show ?thesis proof (cases)
            assume "v \<in> W" thus ?thesis by (metis \<sigma>(1) \<sigma>(2) insert_Diff_if insert_iff valid_paths_are_nonempty)
          next
            assume "v \<notin> W" note v = v this
            then obtain w where w: "w \<in> W'" "v \<rightarrow> w" using directly_attracted_def by blast
            let ?\<sigma>' = "\<sigma>(v \<mapsto> w)"
            have \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> ?\<sigma>'" by (metis DiffE IntI \<sigma>(1) directly_attracted_is_disjoint_from_W empty_iff strategy_less_eq_updates strategy_only_on_elements v(1))
            hence "\<forall>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P ?\<sigma>' \<and> the (P 0) \<in> W' \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W)" using \<sigma> by blast
            have insert_eq: "(insert v W') - W = insert v (W' - W)" by (simp add: insert_Diff_if v(4))
            have "strategy_only_on p ?\<sigma>' (insert v (W' - W))" using strategy_only_on_case_rule by (simp add: v(2) v(3) \<sigma>(1))
            hence "strategy_only_on p ?\<sigma>' ((insert v W') - W)" by (simp add: insert_eq)
            moreover
            have "\<forall>\<sigma>'. strategy_less_eq ?\<sigma>' \<sigma>' \<longrightarrow> (\<forall>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> insert v W' \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))" proof (clarify)
              fix \<sigma>'' assume \<sigma>'_less_eq_\<sigma>'': "strategy_less_eq ?\<sigma>' \<sigma>''"
              fix P assume P: "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>''" "the (P 0) \<in> insert v W'"
              have \<sigma>_less_eq_\<sigma>'': "strategy_less_eq \<sigma> \<sigma>''" using strategy_less_eq_tran using \<sigma>_less_eq_\<sigma>' \<sigma>'_less_eq_\<sigma>'' by blast
              thus "\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W" proof (cases)
                assume "the (P 0) \<in> W'" thus ?thesis using P(1) P(2) P(3) \<sigma>(2) \<sigma>_less_eq_\<sigma>'' by blast
              next
                assume "the (P 0) \<notin> W'"
                hence "the (P 0) = v" using P(4) by blast
                have "\<sigma>'' v = ?\<sigma>' v" using \<sigma>'_less_eq_\<sigma>'' by (simp add: option.case_eq_if strategy_less_eq_def)
                hence "\<sigma>'' v = Some w" by simp
                have "P 1 \<noteq> None" by (metis One_nat_def P(1) P(2) Suc_eq_plus1 `the (P 0) = v` directly_attracted_contains_no_deadends maximal_path_def v(1) valid_paths_are_nonempty)
                hence "\<sigma>'' v = P 1" by (metis P(1) P(3) `\<sigma>'' v = Some w` `the (P 0) = v` infinite_path_tail_head option.collapse v(3) valid_paths_are_nonempty)
                hence "w = the (P 1)" using `\<sigma>'' v = Some w` by (metis option.sel)
                hence "the (P 1) \<in> W'" using w(1) by blast
                hence "the (path_tail P 0) \<in> W'" by simp
                moreover have "valid_path (path_tail P)" using P(1) `P 1 \<noteq> None` valid_path_tail by blast
                moreover have "maximal_path (path_tail P)" using P(2) by blast
                moreover have "path_conforms_with_strategy p (path_tail P) \<sigma>''" using P(3) by blast
                ultimately have "\<exists>i. path_tail P i \<noteq> None \<and> the (path_tail P i) \<in> W" using \<sigma>(2) \<sigma>_less_eq_\<sigma>'' by blast
                thus ?thesis by (metis path_tail_def)
              qed
            qed
            ultimately show ?thesis by blast
          qed
        next
          assume "v \<notin> VV p" note v = v this
          show ?thesis proof (cases)
            assume "v \<in> W" thus ?thesis by (metis \<sigma>(1) \<sigma>(2) insert_Diff_if insert_iff valid_paths_are_nonempty)
          next
            assume "v \<notin> W" note v = v this
            have insert_eq: "(insert v W') - W = insert v (W' - W)" by (simp add: insert_Diff_if v(4))
            hence "strategy_only_on p \<sigma> ((insert v W') - W)" by (simp add: \<sigma>(1) strategy_only_on_case_rule2 v(3))
            moreover
            have "\<forall>\<sigma>' P. strategy_less_eq \<sigma> \<sigma>' \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma>' \<and> the (P 0) \<in> insert v W' \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W)" proof (clarify)
              fix \<sigma>' assume \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> \<sigma>'"
              fix P assume P: "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "the (P 0) \<in> insert v W'"
              thus "\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W" proof (cases "the (P 0) \<in> W'")
                assume "the (P 0) \<in> W'"
                thus ?thesis using P(1) P(2) P(3) \<sigma>(2) \<sigma>_less_eq_\<sigma>' by blast
              next
                assume "the (P 0) \<notin> W'"
                hence "P 0 = Some v" using P(4) by (metis P(1) insertE option.collapse valid_paths_are_nonempty)
                have "v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W')" using directly_attracted_def using v(1) by blast
                hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W'" using VV_equivalence directly_attracted_is_bounded_by_V v(1) v(3) by blast
                have "P 1 \<noteq> None" by (metis One_nat_def P(1) P(2) P(4) Suc_eq_plus1 `the (P 0) \<notin> W'` directly_attracted_contains_no_deadends insertE maximal_path_def v(1) valid_paths_are_nonempty)
                have "\<not>deadend v" using directly_attracted_contains_no_deadends v(1) by blast
                hence "the (P 0) \<rightarrow> the (P 1)" by (metis One_nat_def P(1) P(2) P(4) Suc_eq_plus1 `the (P 0) \<notin> W'` insertE maximal_path_def valid_path_def)
                hence "the (P 1) \<in> W'" using P(4) `\<forall>w. v \<rightarrow> w \<longrightarrow> w \<in> W'` `the (P 0) \<notin> W'` by blast
                hence "the (path_tail P 0) \<in> W'" by simp
                moreover have "valid_path (path_tail P)" using P(1) `P 1 \<noteq> None` valid_path_tail by blast
                moreover have "maximal_path (path_tail P)" using P(2) by blast
                moreover have "path_conforms_with_strategy p (path_tail P) \<sigma>'" using P(3) by blast
                ultimately have "\<exists>i. path_tail P i \<noteq> None \<and> the (path_tail P i) \<in> W" using \<sigma>(2) \<sigma>_less_eq_\<sigma>' by blast
                thus ?thesis by (metis path_tail_def)
              qed
            qed
            ultimately show ?thesis by blast
          qed
        qed
      qed
      thus "P (insert v W')" by (simp add: P_def)
    next
      fix M assume "\<forall>W' \<in> M. W \<subseteq> W' \<and> W' \<subseteq> V \<and> P W'"
      show "P (\<Union>M)" sorry (* doesn't seem possible *)
    qed
    thus ?thesis using P_def A_def by simp
  qed

(*
lemma (in ParityGame) attractor_strategy_domain_is_W:
  assumes "W \<subseteq> V" shows "strategy_on p (attractor_strategy p W) (attractor p W - W)"
  proof -
    def P \<equiv> "\<lambda>W'. strategy_on p (attractor_strategy p W) (W' - W)"
    let ?\<sigma> = "attractor_strategy p W"
    have "P (attractor p W)" proof (induct rule: attractor_induction, simp add: assms)
      show "P {}" by (simp add: P_def)
    next
      fix W' v assume W': "W' \<subseteq> V" "P W'" and v: "v \<in> directly_attracted p W'"
      have "strategy_on p ?\<sigma> ((insert v W') - W)" proof (unfold strategy_on_def, clarify)
        fix v' assume v': "v' \<in> VV p" "v' \<in> insert v W'" "v' \<notin> W" "\<not>deadend v'"
        show "\<exists>y. ?\<sigma> v' = Some y" proof (cases)
          assume "v' = v"
          have "directly_attracted p W' \<noteq> {}" using v by auto
          hence "attractor_strategy p W' = "
            using attractor_strategy_def by sledgehamme
          show ?thesis sledgehamme
        next
          assume "v' \<noteq> v"
          hence "v' \<in> W' - W" using v' by auto note v' = v' this
          have "strategy_on p ?\<sigma> (W' - W)" using W'(2) P_def by auto
          hence "?\<sigma> v' \<noteq> None" using strategy_on_def v' by force
          thus ?thesis by simp
        qed
      qed
      thus "P (insert v W')" by (simp add: P_def)
    qed
    thus ?thesis by (simp add: P_def)
  qed
*)

(*
theorem (in ParityGame) positional_strategy_exist_for_single_prio_games:
  assumes "v \<in> V"
  and "\<forall>w \<in> V. \<omega>(w) = 0"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: 'a Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    {
      fix P :: "'a Path"
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

theorem (in ParityGame) positional_strategy_exists:
  assumes "v \<in> V"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    show ?thesis sorry
  qed
*)

end
