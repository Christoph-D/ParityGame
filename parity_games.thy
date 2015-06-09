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
abbreviation path_dom :: "'a Path \<Rightarrow> nat set" where "path_dom P \<equiv> {i. P i \<noteq> None}"
(* The set of nodes that occur infinitely often on a given path. *)
definition path_inf :: "'a Path \<Rightarrow> 'a set" where
  "path_inf P \<equiv> {v. (\<exists>i. P i = Some v) \<and> (\<forall>i. P i = Some v \<longrightarrow> (\<exists>j > i. P j = Some v))}"
abbreviation path_tail :: "'a Path \<Rightarrow> 'a Path" where "path_tail P \<equiv> \<lambda>i. P (Suc i)"

lemma paths_are_contiguous:
  assumes "infinite_path P \<or> finite_path P"
  shows "P i \<noteq> None \<Longrightarrow> j \<le> i \<Longrightarrow> P j \<noteq> None"
  by (metis assms finite_path_def infinite_path_def leD le_less_linear le_trans)
lemma path_dom_ends_on_finite_paths:
  assumes finite: "finite_path P"
  shows "\<exists>!i \<in> path_dom P. P (i + 1) = None"
  proof -
    obtain i where "\<forall>j. (j > i \<longleftrightarrow> P j = None)" using finite by fastforce
    hence "i \<in> path_dom P \<and> P (i + 1) = None" by auto
    thus ?thesis
      by (metis (mono_tags, lifting) One_nat_def add.right_neutral add_Suc_right finite finite_path_def less_Suc_eq mem_Collect_eq)
  qed

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

locale Digraph =
  fixes G (structure)
  assumes finite_vertex_set: "finite V"
    and non_empty_vertex_set: "V \<noteq> {}"
    and valid_edge_set: "E \<subseteq> V \<times> V"
begin

abbreviation deadend :: "'a \<Rightarrow> bool" where "deadend v \<equiv> \<not>(\<exists>w \<in> V. v \<rightarrow> w)"
definition valid_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "valid_path P \<equiv> P 0 \<noteq> None \<and> (infinite_path P \<or> finite_path P)
      \<and> (\<forall>i. P i \<noteq> None \<longrightarrow> the (P i) \<in> V)
      \<and> (\<forall>i. P i \<noteq> None \<and> P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i)))"
definition maximal_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "maximal_path P \<equiv> \<forall>i. P i \<noteq> None \<and> \<not>deadend (the (P i)) \<longrightarrow> P (Suc i) \<noteq> None"
end

lemma (in Digraph) maximal_infinite_path_tail [intro]:
  "maximal_path P \<Longrightarrow> maximal_path (path_tail P)"
  using assms by auto

datatype Player = Even | Odd
abbreviation other_player :: "Player \<Rightarrow> Player" where "other_player p \<equiv> (if p = Even then Odd else Even)"
notation other_player ("(_**)" [1000] 1000)
lemma [simp]: "p**** = p" using Player.exhaust by auto

record 'a ParityGame = "'a Graph" +
  priority :: "'a \<Rightarrow> nat" ("\<omega>\<index>")
  player0 :: "'a set" ("V0\<index>")

abbreviation winning_priority :: "Player \<Rightarrow> nat \<Rightarrow> bool" where
  "winning_priority p \<equiv> (if p = Even then even else odd)"
lemma winning_priority_for_one_player:
  shows "winning_priority p i \<longleftrightarrow> \<not>winning_priority p** i"
  by auto

locale ParityGame = Digraph G for G :: "('a, 'b) ParityGame_scheme" (structure) +
  assumes valid_player0_set: "V0 \<subseteq> V"

abbreviation (in ParityGame) VV :: "Player \<Rightarrow> 'a set" where "VV p \<equiv> (if p = Even then V0 else V - V0)"
lemma (in ParityGame) [intro]: "v \<in> VV p \<Longrightarrow> v \<in> V" by (metis (full_types) Diff_subset subsetCE valid_player0_set)

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

lemma (in ParityGame) restricted_path_invariant [simp]:
  assumes "the (P i) \<in> W"
  shows "(P \<restriction>\<^sub>P W) i = P i"
  by (simp add: assms restrict_path_def)

lemma (in ParityGame) restricted_path_dom [simp]:
  assumes "i \<in> path_dom (P \<restriction>\<^sub>P W)"
  shows "i \<in> path_dom P"
  by (metis (mono_tags, lifting) assms mem_Collect_eq restrict_path_def)

(* True iff \<sigma> is defined on all non-deadend nodes of the given player. *)
definition (in ParityGame) positional_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "positional_strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"

definition (in ParityGame) path_conforms_with_strategy :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy p P \<sigma> \<equiv> (\<forall>i. P i \<noteq> None \<and> the (P i) \<in> VV p \<longrightarrow> \<sigma> (the (P i)) = P (Suc i))"

lemma (in ParityGame) infinite_path_tail [intro]:
  "infinite_path P \<Longrightarrow> infinite_path (path_tail P)" using assms by auto
lemma (in ParityGame) finite_path_tail [intro]:
  assumes "finite_path P" "P 1 \<noteq> None" shows "finite_path (path_tail P)"
  proof -
    obtain i where i_def: "\<forall>j. (i < j) = (P j = None)" using assms(1) finite_path_def by blast
    hence "i > 0" using assms(2) by force
    hence "\<forall>j. (i-1 < j) = (path_tail P j = None)" by (simp add: i_def Suc_leI less_diff_conv2)
    thus ?thesis by auto
  qed

lemma (in ParityGame) valid_path_tail [intro]:
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
  "strategy_less_eq \<sigma> \<sigma>' \<equiv> \<forall>v. \<sigma> v \<noteq> None \<longrightarrow> \<sigma> v = \<sigma>' v"

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
  shows "strategy_less_eq \<sigma> \<sigma>''" by (unfold strategy_less_eq_def; metis assms strategy_less_eq_def)
lemma (in ParityGame) strategy_less_eq_refl [simp]:
  "strategy_less_eq \<sigma> \<sigma>" by (simp add: option.case_eq_if strategy_less_eq_def)
lemma (in ParityGame) strategy_less_eq_least [simp]:
  "strategy_only_on p \<sigma> {} \<Longrightarrow> strategy_less_eq \<sigma> \<sigma>'" by (simp add: strategy_less_eq_def strategy_only_on_elements)
lemma (in ParityGame) strategy_less_eq_extensible:
  assumes "W \<subseteq> W'" "strategy_on p \<sigma> W"
  shows "\<exists>\<sigma>'. strategy_less_eq \<sigma> \<sigma>' \<and> strategy_on p \<sigma>' W'" proof-
    let ?\<sigma>' = "\<lambda>v. if \<sigma> v \<noteq> None then \<sigma> v else (if v \<in> VV p \<and> \<not>deadend v then Some (SOME w. v\<rightarrow>w) else None)"
    have "strategy_less_eq \<sigma> ?\<sigma>'" proof-
      have "\<And>v. \<sigma> v \<noteq> None \<Longrightarrow> \<sigma> v = ?\<sigma>' v" by simp
      thus ?thesis using strategy_less_eq_def by blast
    qed
    moreover have "strategy_on p ?\<sigma>' W'" proof (unfold strategy_on_def; rule; rule)
      fix v assume v: "v \<in> W' \<inter> VV p" "\<not>deadend v"
      show "?\<sigma>' v \<noteq> None" proof (cases)
        assume "\<sigma> v = None"
        hence "?\<sigma>' v = Some (SOME w. v\<rightarrow>w)" using v by auto
        thus "?\<sigma>' v \<noteq> None" by blast
      next
        assume "\<sigma> v \<noteq> None"
        moreover hence "?\<sigma>' v = \<sigma> v" by auto
        ultimately show ?thesis by auto
      qed
    qed
    ultimately show ?thesis by auto
  qed

(*
lemma (in ParityGame) restricted_strategy_paths:
  assumes "path_conforms_with_strategy p P \<sigma>"
  shows "path_conforms_with_strategy p (P \<restriction>\<^sub>P W) (\<sigma> \<restriction>\<^sub>S W)"d
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

lemma (in ParityGame) VV_impl1 [intro]: "v \<in> VV p \<Longrightarrow> v \<notin> VV p**" by auto
lemma (in ParityGame) VV_impl2 [intro]: "v \<in> VV p** \<Longrightarrow> v \<notin> VV p" by auto
lemma (in ParityGame) VV_equivalence [simp]: "v \<in> V \<Longrightarrow> v \<notin> VV p \<longleftrightarrow> v \<in> VV p**" by auto
lemma (in ParityGame) VV_cases: "\<lbrakk> v \<in> V ; v \<in> VV p \<Longrightarrow> P ; v \<in> VV p** \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by fastforce

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
    hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P" using infinite winning_path_def by (metis (no_types, lifting) infinite_path_def le_antisym)
    thus ?thesis using winning_priority_for_one_player by blast
  next
    assume not_infinite: "\<not>infinite_path P"
    hence finite: "finite_path P" using assms valid_path_def by blast
    then obtain i where i_def: "i \<in> path_dom P \<and> P (i+1) = None" using assms path_dom_ends_on_finite_paths by metis
    def v \<equiv> "the (P i)" (* the last vertex in the path *)
    hence "v \<in> V" using valid_path_def using assms i_def by auto (* TODO: make faster *)
    have "\<And>q. winning_path q P \<longleftrightarrow> (\<exists>i \<in> path_dom P. P (i+1) = None \<and> the (P i) \<in> VV q**)"
      using not_infinite finite winning_path_def by metis
    hence "\<And>q. winning_path q P \<longleftrightarrow> v \<in> VV q**"
      using not_infinite finite path_dom_ends_on_finite_paths i_def v_def by blast
    hence "v \<in> VV p** \<longleftrightarrow> \<not>v \<in> VV p \<Longrightarrow> ?thesis"
      by (metis (full_types) Player.exhaust)
    thus ?thesis using VV_equivalence`v \<in> V` by blast
  qed

lemma (in ParityGame) paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "\<exists>!p. winning_path p P"
  by (metis (full_types) Player.exhaust assms paths_are_winning_for_exactly_one_player)

definition (in ParityGame) winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v \<equiv> \<forall>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) = v \<longrightarrow> winning_path p P"

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
      hence "v \<in> V" by (metis (full_types) Diff_subset assms subsetCE valid_player0_set)
    }
    thus ?thesis by blast
  qed

lemma (in ParityGame) attractor_is_finite:
  "W \<subseteq> V \<Longrightarrow> finite (attractor p W)" by (metis assms attractor_is_bounded_by_V finite_vertex_set rev_finite_subset)

definition (in ParityGame) directly_attracted :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "directly_attracted p W \<equiv> {v \<in> V - W. \<not>deadend v \<and>
      (v \<in> VV p   \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> W))
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
lemma (in ParityGame) directly_attracted_empty_set [simp]:
  shows "directly_attracted p {} = {}" proof (rule ccontr)
    assume "directly_attracted p {} \<noteq> {}"
    then obtain v where v: "v \<in> directly_attracted p {}" by auto
    have "v \<in> V" using directly_attracted_def v by blast
    thus False proof (cases rule: VV_cases)
      assume "v \<in> VV p" thus "False" using directly_attracted_def v by blast
    next
      assume "v \<in> VV p**"
      have "\<not>deadend v" using directly_attracted_def v by blast
      moreover have "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> {}" using directly_attracted_def v `v \<in> VV p**` by blast
      ultimately show "False" by blast
    qed
  qed
lemma (in ParityGame) directly_attracted_union:
  assumes "v \<in> directly_attracted p W" "v \<notin> U"
  shows "v \<in> directly_attracted p (W \<union> U)"
  proof -
    have v1: "\<not>deadend v" using assms(1) directly_attracted_def by auto
    have v2: "v \<in> V - (W \<union> U)" using assms directly_attracted_def by auto
    hence "v \<in> V" by simp
    thus ?thesis proof (cases rule: VV_cases)
      assume "v \<in> VV p"
      hence "v \<notin> VV p**" by (simp add: VV_impl1)
      hence "\<exists>w. v\<rightarrow>w \<and> w \<in> W" using directly_attracted_def assms(1) by auto
      hence "\<exists>w. v\<rightarrow>w \<and> w \<in> W \<union> U" by auto
      thus ?thesis using v1 v2 `v \<notin> VV p**` directly_attracted_def by blast
    next
      assume "v \<in> VV p**"
      hence "v \<notin> VV p" by (simp add: VV_impl2)
      hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W" using directly_attracted_def assms(1) by auto
      hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W \<union> U" by auto
      thus ?thesis using v1 v2 `v \<notin> VV p` directly_attracted_def by blast
    qed
  qed

lemma (in ParityGame) attractor_contains_no_deadends:
  "v \<in> attractor p W \<Longrightarrow> v \<in> W \<or> \<not>deadend v"
  proof (induct rule: attractor.induct)
    fix v assume "v \<in> W" thus "v \<in> W \<or> \<not>deadend v" by simp
  next
    fix v assume "v \<in> VV p" and "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p W \<and> (w \<in> W \<or> \<not>deadend w)"
    thus "v \<in> W \<or> \<not>deadend v" using local.valid_edge_set by auto
  next
    fix v assume "\<not>deadend v"
    thus "v \<in> W \<or> \<not>deadend v" by simp
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

function (in ParityGame) attractor_set_fun :: "nat \<Rightarrow> Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "attractor_set_fun 0 p W = W"
  | "attractor_set_fun (Suc n) p W = (if directly_attracted p W = {} then W else attractor_set_fun n p (W \<union> directly_attracted p W))"
  by pat_completeness auto
  termination (in ParityGame) by lexicographic_order

lemma (in ParityGame) attractor_set_fun_subset [simp]:
  "W \<subseteq> attractor_set_fun n p W" proof (induct n arbitrary: W)
    case 0 thus ?case by auto
    case (Suc n) thus ?case by (metis Un_subset_iff attractor_set_fun.simps(2) eq_iff)
  qed
lemma (in ParityGame) attractor_set_fun_monotone:
  "attractor_set_fun n p W \<subseteq> attractor_set_fun (Suc n) p W" by (induct n arbitrary: W; auto)
lemma (in ParityGame) attractor_set_fun_monotone_generalized [simp]:
  "attractor_set_fun n p W \<subseteq> attractor_set_fun (n + m) p W" by (induct n arbitrary: W m; simp)
lemma (in ParityGame) attractor_set_fun_bounded_by_V:
  "attractor_set_fun n p W \<subseteq> V \<union> W" proof (induct n arbitrary: W)
    case 0 thus ?case by auto
    case (Suc n)
    have "directly_attracted p W \<subseteq> V" by (simp add: directly_attracted_is_bounded_by_V)
    thus ?case using Suc.hyps by auto
  qed
lemma (in ParityGame) attractor_set_fun_finite:
  "finite W \<Longrightarrow> finite (attractor_set_fun n p W)" by (metis attractor_set_fun_bounded_by_V finite_UnI finite_vertex_set rev_finite_subset)
lemma (in ParityGame) attractor_set_fun_equivalence [iff]:
  "attractor_set_fun (Suc n) p W = attractor_set_fun n p (W \<union> directly_attracted p W)"
  by (metis Un_empty_right attractor_set_fun.elims attractor_set_fun.simps(2))

lemma (in ParityGame) attractor_set_fun_directly_attracted:
  "attractor_set_fun n p W \<union> directly_attracted p (attractor_set_fun n p W) = attractor_set_fun (Suc n) p W"
  by (induct n arbitrary: W; auto)

lemma (in ParityGame) attractor_set_fun_eventually_constant:
  assumes "W \<subseteq> V"
  shows "\<exists>n. attractor_set_fun n p W = attractor_set_fun (Suc n) p W"
  proof-
    have finite: "finite W" using assms finite_vertex_set rev_finite_subset by blast
    have "card (attractor_set_fun 0 p W) \<ge> 0" by auto
    {
    fix n :: nat and W :: "'a set"
    assume finite: "finite W"
    have "attractor_set_fun n p W \<noteq> attractor_set_fun (Suc n) p W \<Longrightarrow>
      card (attractor_set_fun n p W) < card (attractor_set_fun (Suc n) p W)" proof (induct n)
      case 0
      have "attractor_set_fun 1 p W = W \<union> directly_attracted p W" by auto
      hence "W \<noteq> W \<union> directly_attracted p W" using "0.prems" by fastforce
      hence "card W < card (W \<union> directly_attracted p W)" by (simp add: finite psubsetI psubset_card_mono)
      thus ?case by auto
    next
      case (Suc n)
      assume IH: "attractor_set_fun n p W \<noteq> attractor_set_fun (Suc n) p W \<Longrightarrow>
          card (attractor_set_fun n p W) < card (attractor_set_fun (Suc n) p W)"
        "attractor_set_fun (Suc n) p W \<noteq> attractor_set_fun (Suc (Suc n)) p W"
      let ?DA = "directly_attracted p W"
      from IH(2) have "?DA \<noteq> {}" by auto
      have "attractor_set_fun (Suc n) p W \<subseteq> attractor_set_fun (Suc (Suc n)) p W" using attractor_set_fun_monotone by blast
      moreover have "finite (attractor_set_fun (Suc n) p W)" using finite attractor_set_fun_finite by blast
      ultimately show ?case by (metis Suc.prems attractor_set_fun_finite local.finite psubsetI psubset_card_mono)
    qed
    } note lemma1 = this
    show ?thesis proof (rule ccontr)
      assume contr: "\<not>(\<exists>n. attractor_set_fun n p W = attractor_set_fun (Suc n) p W)"
      hence "\<forall>n. attractor_set_fun n p W < attractor_set_fun (Suc n) p W" using attractor_set_fun_monotone by (metis psubsetI)
      { fix n
      have "card (attractor_set_fun n p W) \<ge> n" proof (induct n)
        case 0 thus ?case by simp
        case (Suc n) thus ?case by (metis Suc_leI contr add_lessD1 le_Suc_ex lemma1 local.finite)
      qed
      }
      thus False by (metis assms attractor_set_fun_bounded_by_V attractor_set_fun_monotone card_seteq contr finite_vertex_set subset_antisym sup.orderE)
    qed
  qed

lemma (in ParityGame) attractor_set_fun_attractor:
  assumes "W \<subseteq> V"
  shows "\<exists>n. attractor_set_fun n p W = attractor p W"
  proof -
    obtain n where n_def: "attractor_set_fun n p W = attractor_set_fun (Suc n) p W" using assms attractor_set_fun_eventually_constant by blast
    hence "attractor p W \<subseteq> attractor_set_fun n p W" proof -
      {fix v
      have "v \<in> attractor p W \<Longrightarrow> v \<in> attractor_set_fun n p W" proof (induct rule: attractor.induct)
        case Base thus ?case using attractor_set_fun_subset by blast
      next
        case VVp
        fix v assume v: "v \<in> VV p" "\<exists>w. v \<rightarrow> w \<and> w \<in> attractor p W \<and> w \<in> attractor_set_fun n p W"
        then obtain w where w: "v \<rightarrow> w \<and> w \<in> attractor p W \<and> w \<in> attractor_set_fun n p W" by auto
        hence "w \<in> V" using `W \<subseteq> V` attractor_is_bounded_by_V by blast
        hence v2: "v \<in> VV p \<and> (\<exists>w \<in> V. v \<rightarrow> w \<and> w \<in> attractor_set_fun n p W)" using v(1) w by blast
        hence "v \<notin> VV p**" using VV_impl2 by blast
        hence v3: "\<not>deadend v" using `w \<in> V` w by blast
        have "v \<in> attractor_set_fun (Suc n) p W" proof (rule ccontr)
          assume assm: "v \<notin> attractor_set_fun (Suc n) p W"
          hence "v \<notin> attractor_set_fun n p W" using n_def by blast
          hence "v \<in> V - attractor_set_fun n p W" using v(1) by blast
          hence "v \<in> directly_attracted p (attractor_set_fun n p W)"
            using v2 v3 `v \<notin> VV p**` directly_attracted_def[of p "attractor_set_fun n p W"] by blast
          hence "v \<in> attractor_set_fun (Suc n) p W" using attractor_set_fun_directly_attracted by fastforce
          thus "False" using assm by simp
        qed
        thus "v \<in> attractor_set_fun n p W" using n_def by blast
      next
        case VVpstar
        fix v assume v: "\<not>deadend v" "v \<in> VV p**" "\<forall>w. v \<rightarrow> w \<longrightarrow> w \<in> attractor p W \<and> w \<in> attractor_set_fun n p W"
        hence "v \<in> V" by blast
        hence "v \<notin> VV p" using v(2) by simp
        have w: "\<forall>w. v \<rightarrow> w \<longrightarrow> w \<in> attractor_set_fun n p W" by (simp add: v(3))
        have "v \<in> attractor_set_fun (Suc n) p W" proof (rule ccontr)
          assume assm: "v \<notin> attractor_set_fun (Suc n) p W"
          hence "v \<notin> attractor_set_fun n p W" using n_def by blast
          hence "v \<in> V - attractor_set_fun n p W" by (simp add: `v \<in> V`)
          hence "v \<in> directly_attracted p (attractor_set_fun n p W)"
            using v(1) w `v \<notin> VV p` directly_attracted_def[of p "attractor_set_fun n p W"] by blast
          hence "v \<in> attractor_set_fun (Suc n) p W" using attractor_set_fun_directly_attracted by fastforce
          thus "False" using assm by auto
        qed
        thus "v \<in> attractor_set_fun n p W" using n_def by blast
      qed
      } thus ?thesis by auto
    qed
    moreover
    have "attractor_set_fun n p W \<subseteq> attractor p W" proof (induct n)
      case 0 thus ?case by simp
      case (Suc n)
      assume IH: "attractor_set_fun n p W \<subseteq> attractor p W"
      have "directly_attracted p (attractor_set_fun n p W) \<subseteq> attractor p W" proof (intro subsetI)
        fix v assume v_direct: "v \<in> directly_attracted p (attractor_set_fun n p W)"
        hence no_deadend: "\<not>deadend v" using directly_attracted_contains_no_deadends by blast
        have "v \<in> V" using v_direct directly_attracted_def by auto
        thus "v \<in> attractor p W" proof (cases rule: VV_cases)
          assume "v \<in> VV p"
          hence "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor_set_fun n p W" using v_direct directly_attracted_def by blast
          hence "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p W" using IH by auto
          thus ?thesis by (simp add: `v \<in> VV p` attractor.VVp)
        next
          assume "v \<in> VV p**"
          hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor_set_fun n p W" using v_direct directly_attracted_def by blast
          hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p W" using IH by (metis subsetCE)
          thus ?thesis using `v \<in> VV p**` attractor.VVpstar no_deadend by auto
        qed
      qed
      thus ?case using attractor_set_fun_directly_attracted by (metis Suc.hyps Un_subset_iff)
    qed
    ultimately show ?thesis by auto
  qed

lemma (in ParityGame) attractor_set_induction:
  fixes p :: Player and W :: "'a set" and P :: "'a set \<Rightarrow> bool"
  assumes "W \<subseteq> V" "P W"
    "\<And>W'. W \<subseteq> W' \<Longrightarrow> W' \<subseteq> V \<Longrightarrow> P W' \<Longrightarrow> P (W' \<union> (directly_attracted p W'))"
  shows "P (attractor p W)"
  proof -
    obtain n where "attractor_set_fun n p W = attractor p W" using assms(1) attractor_set_fun_attractor by blast
    moreover have "P (attractor_set_fun n p W)" proof (induct n)
      case 0 thus ?case by (simp add: assms(2))
    next
      case (Suc n)
      let ?W' = "attractor_set_fun n p W"
      have "W \<subseteq> ?W'" by simp
      moreover have "?W' \<subseteq> V" using attractor_set_fun_bounded_by_V assms(1) by blast
      moreover have "P ?W'" by (simp add: Suc.hyps)
      ultimately show ?case by (metis attractor_set_fun_directly_attracted assms(3))
    qed
    ultimately show ?thesis by simp
  qed

lemma (in ParityGame) attractor_induction:
  fixes p :: Player and W :: "'a set" and P :: "'a set \<Rightarrow> bool"
  assumes "W \<subseteq> V" and base: "P W"
    and insert: "\<And>W' v. W \<subseteq> W' \<Longrightarrow> W' \<subseteq> V \<Longrightarrow> P W' \<Longrightarrow> v \<in> directly_attracted p W' \<Longrightarrow> P (insert v W')"
  shows "P (attractor p W)"
  using assms(1) assms(2) proof (induct rule: attractor_set_induction; simp)
    fix W' assume IH: "W \<subseteq> W'" "W' \<subseteq> V" "P W'"
    def D \<equiv> "directly_attracted p W'"
    hence "finite D" by auto
    hence "D \<subseteq> directly_attracted p W' \<Longrightarrow> P (W' \<union> D)" using IH proof (induct D rule: finite_induct)
      case empty thus "P (W' \<union> {})" by simp
    next
      case (insert v D)
      assume D: "finite D" "v \<notin> D"
        "\<lbrakk> D \<subseteq> directly_attracted p W'; W \<subseteq> W'; W' \<subseteq> V; P W' \<rbrakk> \<Longrightarrow> P (W' \<union> D)"
        "insert v D \<subseteq> directly_attracted p W'"
        "W \<subseteq> W'" "W' \<subseteq> V" "P W'"
      hence "D \<subseteq> directly_attracted p W'" by auto
      hence "P (W' \<union> D)" by (simp add: insert.hyps(3) insert.prems(2) insert.prems(3) insert.prems(4))
      moreover have "v \<in> directly_attracted p W'" using D(4) by auto
      moreover have "W \<subseteq> W' \<union> D" by (simp add: insert.prems(2) le_supI1)
      moreover have "W' \<union> D \<subseteq> V" using `D \<subseteq> directly_attracted p W'` directly_attracted_is_bounded_by_V insert.prems(3) by blast 
      moreover have "v \<in> directly_attracted p (W' \<union> D)" by (simp add: directly_attracted_union calculation(2) insert.hyps(2))
      ultimately have "P (insert v (W' \<union> D))" using assms(3)[of "W' \<union> D" v] by blast
      thus "P (W' \<union> (insert v D))" by auto
    qed
    thus "P (W' \<union> D)" by (simp add: D_def)
  qed

definition (in ParityGame) strategy_attracts_from_to :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_from_to p \<sigma> A W \<equiv> (\<forall>P.
      valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) \<in> A
    \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))"
lemma (in ParityGame) strategy_attracts_from_to_trivial [simp]:
  "strategy_attracts_from_to p \<sigma> W W" by (meson strategy_attracts_from_to_def valid_paths_are_nonempty)
definition (in ParityGame) strategy_does_not_attract_from_to :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_does_not_attract_from_to p \<sigma> A W \<equiv>
    \<exists>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) \<in> A
      \<longrightarrow> (\<forall>i. P i \<noteq> None \<longrightarrow> the (P i) \<notin> W)"

abbreviation (in ParityGame) attractor_strategy_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "attractor_strategy_on p \<sigma> A W \<equiv> strategy_only_on p \<sigma> (A - W) \<and>
    (\<forall>\<sigma>'. strategy_less_eq \<sigma> \<sigma>' \<longrightarrow> strategy_attracts_from_to p \<sigma>' A W)"

lemma (in ParityGame) attractor_strategy_can_be_extended:
  assumes W': "W \<subseteq> W'" "W' \<subseteq> V" "\<exists>\<sigma>. attractor_strategy_on p \<sigma> W' W"
    and v_directly_attracted: "v \<in> directly_attracted p W'"
  shows "\<exists>\<sigma>. attractor_strategy_on p \<sigma> (insert v W') W"
proof-
  obtain \<sigma> where \<sigma>: "attractor_strategy_on p \<sigma> W' W" using W'(3) by blast
  have "v \<notin> W'" using directly_attracted_is_disjoint_from_W v_directly_attracted by blast
  hence "v \<notin> W" using W'(1) by auto
  show ?thesis proof (cases rule: VV_cases)
    show "v \<in> V" using v_directly_attracted directly_attracted_def by auto
  next
    assume "v \<in> VV p" note v = this
    then obtain w where w: "w \<in> W'" "v \<rightarrow> w" using v_directly_attracted directly_attracted_def by blast
    let ?\<sigma>' = "\<sigma>(v \<mapsto> w)"
    have "\<sigma> v = None" using \<sigma> `v \<notin> W'` by blast
    hence \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> ?\<sigma>'" using strategy_less_eq_updates by blast
    hence "strategy_attracts_from_to p ?\<sigma>' W' W" using \<sigma> by blast
    have "(insert v W') - W = insert v (W' - W)" by (simp add: insert_Diff_if `v \<notin> W`)
    moreover have "strategy_only_on p ?\<sigma>' (insert v (W' - W))" using strategy_only_on_case_rule using \<sigma> v `v \<notin> W'` by blast
    ultimately have "strategy_only_on p ?\<sigma>' ((insert v W') - W)" by simp
    moreover
    have "\<forall>\<sigma>'. strategy_less_eq ?\<sigma>' \<sigma>' \<longrightarrow> strategy_attracts_from_to p \<sigma>' (insert v W') W" proof (unfold strategy_attracts_from_to_def, clarify)
      fix \<sigma>'' assume \<sigma>'_less_eq_\<sigma>'': "strategy_less_eq ?\<sigma>' \<sigma>''"
      fix P assume P: "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>''" "the (P 0) \<in> insert v W'"
      have \<sigma>_less_eq_\<sigma>'': "strategy_less_eq \<sigma> \<sigma>''" using strategy_less_eq_tran using \<sigma>_less_eq_\<sigma>' \<sigma>'_less_eq_\<sigma>'' by blast
      thus "\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W" proof (cases)
        assume "the (P 0) \<in> W'" thus ?thesis using P(1) P(2) P(3) \<sigma> \<sigma>_less_eq_\<sigma>'' strategy_attracts_from_to_def by blast
      next
        assume "the (P 0) \<notin> W'"
        hence "the (P 0) = v" using P(4) by blast
        have "\<sigma>'' v = ?\<sigma>' v" using \<sigma>'_less_eq_\<sigma>'' by (simp add: option.case_eq_if strategy_less_eq_def)
        hence "\<sigma>'' v = Some w" by simp
        have "P 1 \<noteq> None" by (metis One_nat_def P(1) P(2) `the (P 0) = v` directly_attracted_contains_no_deadends maximal_path_def v_directly_attracted valid_paths_are_nonempty)
        hence "\<sigma>'' v = P 1" by (metis P(1) P(3) `\<sigma>'' v = Some w` `the (P 0) = v` infinite_path_tail_head option.collapse v valid_paths_are_nonempty)
        hence "w = the (P 1)" using `\<sigma>'' v = Some w` by (metis option.sel)
        hence "the (P 1) \<in> W'" using w(1) by blast
        hence "the (path_tail P 0) \<in> W'" by simp
        moreover have "valid_path (path_tail P)" using P(1) `P 1 \<noteq> None` valid_path_tail by blast
        moreover have "maximal_path (path_tail P)" using P(2) by blast
        moreover have "path_conforms_with_strategy p (path_tail P) \<sigma>''" using P(3) by blast
        ultimately have "\<exists>i. path_tail P i \<noteq> None \<and> the (path_tail P i) \<in> W" using \<sigma> \<sigma>_less_eq_\<sigma>'' strategy_attracts_from_to_def by blast
        thus ?thesis by auto
      qed
    qed
    ultimately show ?thesis by blast
  next
    assume "v \<in> VV p**" note v = this
    have insert_eq: "(insert v W') - W = insert v (W' - W)" by (simp add: insert_Diff_if `v \<notin> W`)
    hence "strategy_only_on p \<sigma> ((insert v W') - W)" by (simp add: VV_impl2 \<sigma> strategy_only_on_case_rule2 v)
    moreover
    have "\<forall>\<sigma>'. strategy_less_eq \<sigma> \<sigma>' \<longrightarrow> strategy_attracts_from_to p \<sigma>' (insert v W') W" proof (unfold strategy_attracts_from_to_def, clarify)
      fix \<sigma>' assume \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> \<sigma>'"
      fix P assume P: "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "the (P 0) \<in> insert v W'"
      thus "\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W" proof (cases "the (P 0) \<in> W'")
        assume "the (P 0) \<in> W'" thus ?thesis using P(1) P(2) P(3) \<sigma> \<sigma>_less_eq_\<sigma>' strategy_attracts_from_to_def by blast
      next
        assume "the (P 0) \<notin> W'"
        hence "P 0 = Some v" using P(4) by (metis P(1) insertE option.collapse valid_paths_are_nonempty)
        have "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W'" using directly_attracted_def `v \<in> VV p**` v_directly_attracted by blast
        have "P 1 \<noteq> None" by (metis One_nat_def P(1) P(2) P(4) `the (P 0) \<notin> W'` directly_attracted_contains_no_deadends insertE maximal_path_def v_directly_attracted valid_paths_are_nonempty)
        have "\<not>deadend v" using directly_attracted_contains_no_deadends v_directly_attracted by blast
        hence "the (P 0) \<rightarrow> the (P 1)" by (metis One_nat_def P(1) P(2) P(4) `the (P 0) \<notin> W'` insertE maximal_path_def valid_path_def)
        hence "the (P 1) \<in> W'" using P(4) `\<forall>w. v \<rightarrow> w \<longrightarrow> w \<in> W'` `the (P 0) \<notin> W'` by blast
        hence "the (path_tail P 0) \<in> W'" by simp
        moreover have "valid_path (path_tail P)" using P(1) `P 1 \<noteq> None` valid_path_tail by blast
        moreover have "maximal_path (path_tail P)" using P(2) by blast
        moreover have "path_conforms_with_strategy p (path_tail P) \<sigma>'" using P(3) by blast
        ultimately have "\<exists>i. path_tail P i \<noteq> None \<and> the (path_tail P i) \<in> W" using \<sigma> \<sigma>_less_eq_\<sigma>' strategy_attracts_from_to_def by blast
        thus ?thesis by auto
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

theorem (in ParityGame) attractor_has_strategy:
  fixes W p
  assumes "W \<subseteq> V"
  shows "\<exists>\<sigma>. attractor_strategy_on p \<sigma> (attractor p W) W"
  proof -
    def strategy_exists_for \<equiv> "\<lambda>A. \<exists>\<sigma>. attractor_strategy_on p \<sigma> A W"
    have "strategy_exists_for (attractor p W)" proof (induct rule: attractor_induction, simp add: assms)
      show "strategy_exists_for W" by (simp add: strategy_exists_for_def strategy_only_on_empty_set_exists)
    next
      fix W' v assume W': "W \<subseteq> W'" "W' \<subseteq> V" "strategy_exists_for W'" and v: "v \<in> directly_attracted p W'"
      thus "strategy_exists_for (insert v W')" using attractor_strategy_can_be_extended strategy_exists_for_def by blast
    qed
    thus ?thesis using strategy_exists_for_def by blast
  qed

corollary (in ParityGame) attractor_has_strategy_weak:
  fixes W p
  defines "A \<equiv> attractor p W"
  assumes "W \<subseteq> V"
  shows "\<exists>\<sigma>. strategy_only_on p \<sigma> (A - W) \<and> strategy_attracts_from_to p \<sigma> A W"
proof -
  obtain \<sigma> where "strategy_only_on p \<sigma> (A - W) \<and> strategy_attracts_from_to p \<sigma> A W" using assms attractor_has_strategy by (metis (full_types) strategy_less_eq_refl)
  thus ?thesis using strategy_less_eq_refl by blast
qed

primrec (in ParityGame) path_avoiding_a_set :: "nat \<Rightarrow> Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a option" where
  "path_avoiding_a_set 0 p \<sigma> v0 A = Some v0"
  | "path_avoiding_a_set (Suc n) p \<sigma> v0 A = (
    if path_avoiding_a_set n p \<sigma> v0 A = None
    then None
    else if (the (path_avoiding_a_set n p \<sigma> v0 A)) \<in> VV p
      then \<sigma> (the (path_avoiding_a_set n p \<sigma> v0 A))
      else if deadend (the (path_avoiding_a_set n p \<sigma> v0 A))
        then None
        else Some (SOME w. w \<in> V - A \<and> (the (path_avoiding_a_set n p \<sigma> v0 A))\<rightarrow>w))"

(* If A is the p-attractor of a set W, then p** has a strategy on V - A such that p** always
   has a way to avoid going to A. *)
theorem (in ParityGame) attractor_has_outside_strategy:
  fixes W p
  defines "A \<equiv> attractor p** W"
  assumes "W \<subseteq> V" and v0_def: "v0 \<in> V - A"
  shows "\<exists>\<sigma>. strategy_only_on p \<sigma> (V - A) \<and> \<not>strategy_attracts_from_to p \<sigma> {v0} A"
  proof (intro exI conjI)
    (* Define a strategy on the p-Nodes in V - A.  \<sigma> simply chooses an arbitrary node not in A as
    the successor. *)
    def \<sigma> \<equiv> "\<lambda>v. (
      if v \<in> (V - A) \<and> v \<in> VV p \<and> \<not>deadend v
        then Some (SOME w. w \<notin> A \<and> v\<rightarrow>w)
        else None)"
    (* We need to show that \<sigma> is well-defined.  This means we have to show that \<sigma> always applies
    the SOME quantifier to a non-empty set. *)
    have \<sigma>_correct: "\<And>v w. \<sigma> v = Some w \<Longrightarrow> w \<notin> A \<and> v\<rightarrow>w" using \<sigma>_def proof-
      fix v w assume assm: "\<sigma> v = Some w"
      have "\<not>(v \<in> (V - A) \<inter> VV p \<and> \<not>deadend v) \<Longrightarrow> \<sigma> v = None" using \<sigma>_def by auto
      hence v_not_in_A_no_deadend: "v \<in> (V - A) \<inter> VV p \<and> \<not>deadend v" by (metis assm option.distinct(1))
      hence "\<sigma> v = Some (SOME w. w \<notin> A \<and> v\<rightarrow>w)" using \<sigma>_def by auto
      hence "Some w = Some (SOME w. w \<notin> A \<and> v\<rightarrow>w)" using assm by metis
      hence *: "w = (SOME w. w \<notin> A \<and> v\<rightarrow>w)" by auto
      have "\<exists>w. w \<notin> A \<and> v\<rightarrow>w" proof (rule ccontr)
        assume "\<not>(\<exists>w. w \<notin> A \<and> v\<rightarrow>w)"
        hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> A" by auto
        hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p** W" using A_def by simp
        hence "v \<in> attractor p** W" using v_not_in_A_no_deadend attractor.VVpstar by auto
        hence "v \<in> A" using A_def by simp
        thus False using v_not_in_A_no_deadend by blast
      qed
      thus "w \<notin> A \<and> v\<rightarrow>w" using * by (metis (mono_tags, lifting) someI_ex)
    qed

    (* First, the easy part of the thesis. *)
    show "strategy_only_on p \<sigma> (V - A)" using \<sigma>_def strategy_only_on_def[of p \<sigma> "V - A"] by auto

    (* To show the second part, we recursively construct a path starting from v0 that avoids A.
    Then we prove that P is valid, maximal \<sigma>-conforming path avoiding A. *)
    def P \<equiv> "\<lambda>i. path_avoiding_a_set i p \<sigma> v0 A"
    (* We need a simplification rule on P (not on path_avoiding_a_set) for the proofs below. *)
    have P_simp [simp]: "\<And>n. P (Suc n) = (
      if P n = None
      then None
      else if (the (P n)) \<in> VV p
        then \<sigma> (the (P n))
        else if deadend (the (P n)) then None else Some (SOME w. w \<in> V - A \<and> (the (P n))\<rightarrow>w))"
        apply (subst P_def)+ by simp

    have P_valid_start: "the (P 0) = v0" unfolding P_def using v0_def by auto

    (* The key lemma.  We show simultaneously that
      1) the path is only in V - A and
      2) there is an edge between every two successive entries. *)
    moreover have edges_exist: "\<And>i. P i \<noteq> None \<Longrightarrow> the (P i) \<in> V - A \<and> (P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i)))" proof-
      have *:
        "\<And>i. \<lbrakk> P i \<noteq> None; the (P i) \<in> V - A; P (Suc i) \<noteq> None \<rbrakk> \<Longrightarrow> the (P (Suc i)) \<in> V - A \<and> the (P i)\<rightarrow>the (P (Suc i))" proof-
        fix i
        assume P_i: "P i \<noteq> None" "the (P i) \<in> V - A" and P_Suc_i: "P (Suc i) \<noteq> None"
        have no_deadend: "\<not>deadend (the (P i))" by (metis (no_types, lifting) P_Suc_i P_simp \<sigma>_def)
        obtain w where w_def: "P (Suc i) = Some w" using P_Suc_i by blast

        show "the (P (Suc i)) \<in> V - A \<and> the (P i)\<rightarrow>the (P (Suc i))" proof(cases)
          assume "the (P i) \<in> VV p"
          hence "P (Suc i) = \<sigma> (the (P i))" by (simp add: P_i(1))
          hence "\<sigma> (the (P i)) = Some w" using w_def by presburger
          hence "w \<notin> A \<and> the (P i)\<rightarrow>w" using \<sigma>_correct by blast
          hence "w \<in> V - A \<and> the (P i)\<rightarrow>w" using valid_edge_set by auto
          thus ?thesis using w_def by (metis option.sel)
        next
          assume "the (P i) \<notin> VV p"
          hence "P (Suc i) = (if deadend (the (P i)) then None else Some (SOME w. w \<in> V - A \<and> (the (P i))\<rightarrow>w))" by (simp add: P_i)
          hence "P (Suc i) = Some (SOME w. w \<in> V - A \<and> (the (P i))\<rightarrow>w)" using no_deadend by auto
          hence "w = (SOME w. w \<in> V - A \<and> (the (P i))\<rightarrow>w)" by (metis (no_types, lifting) option.inject w_def)
          moreover have "\<exists>w. w \<in> V - A \<and> the (P i)\<rightarrow>w" proof (rule ccontr)
            assume "\<not>(\<exists>w. w \<in> V - A \<and> the (P i)\<rightarrow>w)"
            hence "\<forall>w. the (P i)\<rightarrow>w \<longrightarrow> w \<notin> V - A" by auto
            hence "\<forall>w. the (P i)\<rightarrow>w \<longrightarrow> w \<in> A" using valid_edge_set by auto
            hence w_attracted: "\<exists>w. the (P i)\<rightarrow>w \<and> w \<in> A" using no_deadend by blast
            have "the (P i) \<in> VV p**" using `the (P i) \<in> V - A` `the (P i) \<notin> VV p` by auto
            hence "the (P i) \<in> A" apply (insert w_attracted; unfold A_def) by (simp add: attractor.VVp)
            thus False using P_i(2) by simp
          qed
          ultimately have "w \<in> V - A \<and> (the (P i))\<rightarrow>w" by (metis (no_types, lifting) someI_ex)
          thus ?thesis using w_def by (metis option.sel)
        qed
      qed
      fix i show "P i \<noteq> None \<Longrightarrow> the (P i) \<in> V - A \<and> (P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i)))" proof (induct i)
        case 0 thus ?case using P_valid_start v0_def * by blast
      next
        case (Suc i) thus ?case using * by (meson DiffD1 P_simp)
      qed
    qed

    moreover have P_conforms: "path_conforms_with_strategy p P \<sigma>" proof (unfold path_conforms_with_strategy_def; intro allI impI; elim conjE)
      fix i assume i_def: "P i \<noteq> None" "the (P i) \<in> VV p"
      show "\<sigma> (the (P i)) = P (Suc i)" by (simp add: i_def)
    qed

    moreover have P_valid: "valid_path P" proof (unfold valid_path_def; intro conjI)
      show P_0_not_None: "P 0 \<noteq> None" using P_def by auto
      show "infinite_path P \<or> finite_path P" proof (subst disj_comms; rule disjCI)
        let ?Q = "{i. P i = None}"
        assume "\<not>infinite_path P"
        then obtain i where "i \<in> ?Q" by auto
        then obtain i where i_def: "i \<in> ?Q" and i_min: "\<And>j. j < i \<longrightarrow> j \<notin> ?Q" by (meson less_than_iff wf_less_than wfE_min)
        hence "i \<noteq> 0" using P_0_not_None by (meson CollectD)
        then obtain n where n_def: "Suc n = i" using gr0_conv_Suc by auto
        show "finite_path P" proof (unfold finite_path_def; rule_tac x="n" in exI; intro allI)
          fix j
          have "j > n \<Longrightarrow> P j = None" proof (induct j, simp)
            case (Suc j)
            show ?case proof (cases)
              assume "j = n" thus ?thesis using i_def n_def by auto
            next
              assume "j \<noteq> n" thus ?thesis using Suc.hyps Suc.prems P_def by auto
            qed
          qed
          moreover have "\<not>j > n \<Longrightarrow> P j \<noteq> None" using n_def i_min by auto
          ultimately show "j > n \<longleftrightarrow> P j = None" by blast
        qed
      qed
      show "\<forall>i. P i \<noteq> None \<longrightarrow> the (P i) \<in> V" using edges_exist by simp
      show "\<forall>i. P i \<noteq> None \<and> P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i))" using edges_exist by simp
    qed

    moreover have "maximal_path P" proof (unfold maximal_path_def; intro allI impI; elim conjE)
      fix i assume P_i: "P i \<noteq> None" and P_i_no_deadend: "\<not>deadend (the (P i))"
      show "P (Suc i) \<noteq> None" proof (cases)
        assume P_i_VV_p: "the (P i) \<in> VV p"
        hence "\<sigma> (the (P i)) \<noteq> None" by (metis (no_types, lifting) P_i \<sigma>_def edges_exist option.distinct(1) P_i_no_deadend)
        moreover have "P (Suc i) = \<sigma> (the (P i))" by (simp add: P_i P_i_VV_p)
        ultimately show "P (Suc i) \<noteq> None" by simp
      next
        assume "the (P i) \<notin> VV p"
        hence "P (Suc i) = Some (SOME w. w \<in> V - A \<and> (the (P i))\<rightarrow>w)" using P_i P_i_no_deadend P_simp by presburger
        thus "P (Suc i) \<noteq> None" by auto
      qed
    qed

    ultimately have "\<exists>P. valid_path P \<and> maximal_path P
      \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) = v0
      \<and> \<not>(\<exists>i. P i \<noteq> None \<and> the (P i) \<in> A)" by blast
    thus "\<not>strategy_attracts_from_to p \<sigma> {v0} A" using strategy_attracts_from_to_def by blast
  qed

theorem (in ParityGame) positional_strategy_exist_for_single_prio_games:
  assumes "v \<in> V"
  and "\<forall>w \<in> V. \<omega>(w) = 0"
  shows "\<exists>p \<sigma>. strategy_on p \<sigma> V \<and> winning_strategy p \<sigma> v"
  proof -
    let ?deadends = "\<lambda>p. {v \<in> VV p. deadend v}"
    { fix p
      def A \<equiv> "attractor p (?deadends p**)"
      obtain \<sigma> where \<sigma>: "attractor_strategy_on p \<sigma> A (?deadends p**)"
        using attractor_has_strategy[of "?deadends p**" "p"] A_def by auto

      have "?deadends p** \<subseteq> V" by auto
      hence "A \<subseteq> V" using A_def using attractor_is_bounded_by_V by blast
      hence "A - ?deadends p** \<subseteq> V" by auto
      moreover have "strategy_on p \<sigma> (A - ?deadends p**)" using \<sigma> by blast
      ultimately obtain \<sigma>' where \<sigma>': "strategy_on p \<sigma>' V" "strategy_less_eq \<sigma> \<sigma>'"
        using strategy_less_eq_extensible[of "A - ?deadends p**" "V"] by blast
      hence \<sigma>'_attracts: "strategy_attracts_from_to p \<sigma>' A (?deadends p**)" using \<sigma> by blast

      assume v_in_attractor: "v \<in> attractor p (?deadends p**)"
      have "winning_strategy p \<sigma>' v" proof (unfold winning_strategy_def, clarify)
        fix P assume P: "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "v = the (P 0)"
        have P_infinite_or_finite: "infinite_path P \<or> finite_path P" using P(1) valid_path_def by blast
        obtain i where i_def: "P i \<noteq> None \<and> the (P i) \<in> ?deadends p**" using \<sigma>'_attracts A_def v_in_attractor strategy_attracts_from_to_def P by blast
        have "P (Suc i) = None" by (metis (no_types, lifting) i_def CollectD P(1) valid_path_def)
        moreover hence "finite_path P" using infinite_path_def P_infinite_or_finite by blast
        moreover have "i \<in> path_dom P \<and> the (P i) \<in> VV p**" using i_def by blast
        ultimately show "winning_path p P" using winning_path_def sorry
      qed
      hence "\<exists>\<sigma>. strategy_on p \<sigma> V \<and> winning_strategy p \<sigma> v" using \<sigma>' by blast
    } note lemma1 = this
    {
      assume "v \<notin> attractor Odd (?deadends Even)"
      have "\<exists>\<sigma>. strategy_on Even \<sigma> V \<and> winning_strategy Even \<sigma> v" sorry
    }
    thus ?thesis using lemma1[of Odd] by meson
  qed

(*
theorem (in ParityGame) positional_strategy_exists:
  assumes "v \<in> V"
  shows "\<exists>p :: Player. \<exists>\<sigma> :: Strategy. positional_strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  proof -
    show ?thesis sorry
  qed
*)

end
