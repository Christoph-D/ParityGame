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
codatatype (Pset: 'a) Path = path_null: PNil | PCons (path_head: 'a) (path_tail: "'a Path")

inductive finite_path :: "'a Path \<Rightarrow> bool" where
  finite_nil: "finite_path PNil"
| finite_cons: "finite_path Ps \<Longrightarrow> finite_path (PCons _ Ps)"
definition infinite_path :: "'a Path \<Rightarrow> bool" where [simp]: "infinite_path P \<equiv> \<not>finite_path P"

lemma path_head_cons: "\<not>path_null P \<Longrightarrow> path_head P = v \<Longrightarrow> PCons v (path_tail P) = P" by auto

fun path_at :: "'a Path \<Rightarrow> nat \<Rightarrow> 'a option" (infix "$" 60) where
  "path_at PNil _ = None"
| "path_at (PCons v _) 0 = Some v"
| "path_at (PCons v Ps) (Suc n) = path_at Ps n"

(* The set of nodes that occur infinitely often on a given path. *)
definition path_inf :: "'a Path \<Rightarrow> 'a set" where
  "path_inf P \<equiv> {v. (\<exists>i. P $ i = Some v) \<and> (\<forall>i. P $ i = Some v \<longrightarrow> (\<exists>j > i. P $ j = Some v))}"

primrec Pdrop :: "nat \<Rightarrow> 'a Path \<Rightarrow> 'a Path" where
  "Pdrop 0 P = P"
| "Pdrop (Suc n) P = Pdrop n (path_tail P)"

lemma path_at_0 [simp]: "\<not>path_null P \<Longrightarrow> P $ 0 = Some (path_head P)" by (metis Path.collapse(2) path_at.simps(2))
lemma path_at_0': "\<not>path_null P \<Longrightarrow> P $ 0 \<noteq> None" by simp
lemma path_at_0'': "P $ 0 \<noteq> None \<Longrightarrow> \<not>path_null P" using Path.disc(1) Path.expand by fastforce
lemma path_at_0_head: "P $ 0 = Some v \<Longrightarrow> path_head P = v" using path_at_0'' by force
lemma PCons_0 [simp]: "path_head (PCons v P) = v" by simp
lemma PCons_suc_is_P [simp]: "PCons v P $ (Suc i) = P $ i" by simp
lemma PCons_suc_is_P2: "i \<noteq> 0 \<Longrightarrow> PCons v P $ i = P $ i - 1" by (metis Suc_diff_1 gr0I PCons_suc_is_P)

lemma infinite_path_no_deadend: "infinite_path P \<Longrightarrow> \<not>path_null P" using finite_path.simps path_null_def by fastforce
lemma infinite_path_tail: "infinite_path (PCons v Ps) \<Longrightarrow> infinite_path Ps" by (meson finite_cons infinite_path_def)
lemma infinite_path_at: "infinite_path P \<Longrightarrow> P $ i \<noteq> None" proof (induct i arbitrary: P, simp add: infinite_path_no_deadend)
  fix i and P :: "'a Path"
  assume IH: "\<And>P :: 'a Path. infinite_path P \<Longrightarrow> P $ i \<noteq> None" "infinite_path P"
  then obtain v Ps where Ps: "P = PCons v Ps" using infinite_path_no_deadend by (metis (no_types) Path.collapse(2))
  hence "Ps $ i \<noteq> None" using IH by (meson infinite_path_tail)
  thus "P $ Suc i \<noteq> None" by (simp add: Ps)
qed

lemma path_tail_suc: "P $ Suc i \<noteq> None \<Longrightarrow> P $ Suc i = path_tail P $ i"
  by (metis PCons_suc_is_P Path.exhaust_sel path_at.simps(1))
lemma path_tail_inf: "infinite_path P \<Longrightarrow> P $ Suc i = path_tail P $ i"
  by (meson infinite_path_at path_tail_suc)
lemma path_drop_suc: "Pdrop n P $ Suc i \<noteq> None \<Longrightarrow> Pdrop n P $ Suc i = Pdrop (Suc n) P $ i"
  by (induct n arbitrary: P, insert path_tail_suc; fastforce)
lemma path_drop_diff: "\<lbrakk> n \<le> i; P $ i \<noteq> None \<rbrakk> \<Longrightarrow> P $ i = Pdrop n P $ i - n"
  by (induct n, simp, metis Suc_diff_le Suc_leD diff_Suc_Suc path_drop_suc)
lemma path_drop_comm: "P $ Suc n \<noteq> None \<Longrightarrow> Pdrop n (path_tail P) = path_tail (Pdrop n P)"
  by (induct n arbitrary: P, simp, metis Pdrop.simps(2) path_tail_suc)
lemma path_drop_head: "P $ n = Some v \<Longrightarrow> path_head (Pdrop n P) = v"
  by (induct n arbitrary: P, simp add: path_at_0_head, insert path_tail_suc, force)
lemma path_drop_no_deadend: "P $ Suc n \<noteq> None \<Longrightarrow> \<not>path_null (Pdrop n P)"
  apply (induct n arbitrary: P)
   apply (metis Pdrop.simps(1) path_at.simps(1) path_null_def)
  by (metis Pdrop.simps(2) path_tail_suc)
lemma path_at_in_pset: "P $ n \<noteq> None \<Longrightarrow> the (P $ n) \<in> Pset P"
  apply (induct n arbitrary: P)
   apply (metis Path.set_sel(1) option.exhaust_sel path_at_0'' path_at_0_head)
  by (metis Path.collapse(1) Path.set_sel(2) path_at.simps(1) path_tail_suc)
lemma path_pset_at: "v \<in> Pset P \<Longrightarrow> \<exists>n. P $ n = Some v"
  by (induct v P rule: Path.set_induct, meson path_at.simps(2), metis PCons_suc_is_P)

lemma finite_path_at:
  assumes P_fin: "finite_path P"
  shows "\<exists>i. P $ i = None"
proof (rule finite_path.induct, insert P_fin, assumption)
  fix v :: 'a
  have "PNil $ 1 = None" by simp
  thus "\<exists>i. PNil $ i = None" by blast
next
  fix v :: 'a and Ps :: "'a Path"
  assume "\<exists>i. Ps $ i = None"
  then obtain i where "Ps $ i = None" by blast
  hence "PCons v Ps $ (Suc i) = None" by simp
  thus "\<exists>i. PCons v Ps $ i = None" by blast
qed

lemma finite_path_none_Suc: "P $ i = None \<Longrightarrow> P $ (Suc i) = None"
  apply (induct i arbitrary: P)
   apply (metis Path.expand path_at.simps(1) path_at_0')
  by (metis PCons_suc_is_P Path.exhaust_sel path_at.simps(1))
lemma finite_path_at2: "\<lbrakk> P $ i = None; i \<le> j \<rbrakk> \<Longrightarrow> P $ j = None" by (induct "j - i" arbitrary: i, simp, metis Suc_diff_Suc diff_diff_cancel diff_le_self finite_path_none_Suc leD le_eq_less_or_eq not_less_eq)

lemma finite_path_eventually_none: "finite_path P \<Longrightarrow> \<exists>i. \<forall>j. (j \<ge> i \<longrightarrow> P $ j = None)" by (meson finite_path_at finite_path_at2 less_or_eq_imp_le)
lemma finite_path_eventually_none':
  assumes P_fin: "finite_path P"
  shows "\<exists>i. \<forall>j. (j \<ge> i \<longleftrightarrow> P $ j = None)"
proof-
  def Q \<equiv> "\<lambda>i. P $ i = None"
  hence "\<exists>i. Q i" using finite_path_at P_fin by blast
  then obtain i where i: "Q i" "\<And>j. j < i \<Longrightarrow> \<not>Q j" using obtain_min by blast
  have "\<And>j. j \<ge> i \<Longrightarrow> P $ j = None" using Q_def finite_path_at2 i(1) by blast
  moreover have "\<And>j. P $ j = None \<Longrightarrow> j \<ge> i" using Q_def i(2) leI by blast
  ultimately show ?thesis by blast
qed

lemma infinite_path_equiv: "infinite_path P \<longleftrightarrow> (\<forall>i. P $ i \<noteq> None)" using finite_path_at infinite_path_at infinite_path_def by blast
lemma finite_path_equiv': "finite_path P \<longleftrightarrow> (\<exists>i. \<forall>j. (j \<ge> i \<longrightarrow> P $ j = None))" by (meson Suc_n_not_le_n finite_path_at2 infinite_path_def infinite_path_equiv not_less_eq_eq)
lemma finite_path_equiv: "finite_path P \<longleftrightarrow> (\<exists>i. \<forall>j. (j \<ge> i \<longleftrightarrow> P $ j = None))" using finite_path_equiv' finite_path_eventually_none' by blast

abbreviation path_dom :: "'a Path \<Rightarrow> nat set" where "path_dom P \<equiv> {i. P $ i \<noteq> None}"

lemma paths_are_contiguous: "P $ i = Some v \<Longrightarrow> j \<le> i \<Longrightarrow> \<exists>w. P $ j = Some w" using finite_path_at2 by fastforce
lemma paths_are_contiguous_suc: "P $ Suc i = Some w \<Longrightarrow> \<exists>v. P $ i = Some v" by (simp add: paths_are_contiguous)
lemma path_dom_ends_on_finite_paths:
  assumes P_fin: "finite_path P" "\<not>path_null P"
  shows "\<exists>!i \<in> path_dom P. P $ Suc i = None"
  proof-
    obtain i where i_def: "\<forall>j. (j \<ge> i \<longleftrightarrow> P $ j = None)" using P_fin finite_path_equiv by blast
    then obtain i' where "Suc i' = i" by (metis assms(2) le0 nat.exhaust path_at_0')
    hence "i' \<in> path_dom P \<and> P $ Suc i' = None" using Suc_n_not_le_n i_def by blast
    thus ?thesis by (metis (mono_tags, lifting) i_def le_antisym mem_Collect_eq not_less_eq_eq)
  qed
lemma path_2_no_deadend: "P $ i \<noteq> None \<Longrightarrow> \<not>path_null P" using Path.collapse(1) by fastforce
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
  valid_path_base: "v \<in> V \<Longrightarrow> valid_path (PCons v PNil)"
| valid_path_cons: "\<lbrakk> v \<in> V; w \<in> V; v\<rightarrow>w; valid_path Ps; \<not>path_null Ps; path_head Ps = w \<rbrakk> \<Longrightarrow> valid_path (PCons v Ps)"

lemma valid_path_not_null: "valid_path P \<Longrightarrow> \<not>path_null P" using path_null_def valid_path.cases by auto
lemma valid_path_cons': "\<lbrakk> v\<rightarrow>w; valid_path Ps; path_head Ps = w \<rbrakk> \<Longrightarrow> valid_path (PCons v Ps)" using edges_are_in_V valid_path_cons valid_path_not_null by auto
lemma valid_path_tail': "\<lbrakk> \<not>path_null Ps; valid_path (PCons v Ps) \<rbrakk> \<Longrightarrow> valid_path Ps" using valid_path.cases Path.disc(1) by blast
lemma valid_path_tail: "\<lbrakk> \<not>path_null P; \<not>path_null (path_tail P); valid_path P \<rbrakk> \<Longrightarrow> valid_path (path_tail P)" by (metis Path.collapse(2) valid_path_tail')

lemma valid_path_in_V: assumes "valid_path P" shows "Pset P \<subseteq> V" proof
  fix x assume "x \<in> Pset P" thus "x \<in> V" using assms by (induct rule: Path.set_induct) (auto intro: valid_path.cases edges_are_in_V)
qed

lemma valid_path_drop: assumes "valid_path P" "P $ i \<noteq> None" shows "valid_path (Pdrop i P)" using assms proof (induct i)
  case 0 thus ?case by (simp add: assms(1))
next
  case (Suc n)
  hence "valid_path (Pdrop n P)" by (meson finite_path_none_Suc)
  moreover have "\<not>path_null (Pdrop n P)" proof-
    have "Pdrop n P $ Suc n - n \<noteq> None" by (metis Suc.prems(2) lessI less_imp_le path_drop_diff)
    thus ?thesis by (simp add: path_2_no_deadend)
  qed
  moreover have "\<not>path_null (path_tail (Pdrop n P))" proof-
    have "path_tail (Pdrop n P) $ 0 \<noteq> None" by (metis Pdrop.simps(2) Suc.prems(2) le_refl path_at.simps(1) path_at_0' path_drop_comm path_drop_diff path_null_def)
    thus ?thesis by (simp add: path_2_no_deadend)
  qed
  ultimately have "valid_path (path_tail (Pdrop n P))" using valid_path_tail by blast
  thus ?case by (simp add: Suc.prems(2) path_drop_comm)
qed

lemma valid_path_edges:
  assumes "valid_path P" "P $ i = Some v" "P $ Suc i = Some w"
  shows "v\<rightarrow>w" proof-
  def Ps \<equiv> "path_tail (Pdrop i P)"
  hence "path_head Ps = w" by (metis assms(3) option.distinct(2) path_drop_comm path_drop_head path_tail_suc)
  moreover have "valid_path (PCons v Ps)" proof-
    have "path_head (Pdrop i P) = v" by (simp add: assms(2) path_drop_head)
    moreover have "valid_path (Pdrop i P)" by (simp add: assms(1) assms(2) valid_path_drop)
    moreover have "\<not>path_null (Pdrop i P)" by (simp add: assms(3) path_drop_no_deadend)
    ultimately show ?thesis by (simp add: Ps_def path_head_cons)
  qed
  ultimately show "v\<rightarrow>w" using valid_path.cases by (metis PCons_0 Path.disc(1) Path.sel(2) Pdrop.simps(2) Ps_def assms(1) assms(3) option.distinct(1) path_drop_comm valid_path_drop valid_path_not_null)
qed

lemma valid_path_impl1: "valid_path P \<Longrightarrow> \<not>path_null P \<and> Pset P \<subseteq> V \<and> (\<forall>i v w. P $ i = Some v \<and> P $ Suc i = Some w \<longrightarrow> v\<rightarrow>w)" using valid_path_edges valid_path_in_V valid_path_not_null by blast
lemma valid_path_impl2: "\<lbrakk> \<not>path_null P; Pset P \<subseteq> V; \<And>i v w. P $ i = Some v \<and> P $ Suc i = Some w \<longrightarrow> v\<rightarrow>w \<rbrakk> \<Longrightarrow> valid_path P" proof (coinduction arbitrary: P rule: valid_path.coinduct)
  case (valid_path P)
  { assume "\<not>(\<exists>v. P = PCons v PNil \<and> v \<in> V)"
    hence "\<not>(\<exists>v. P = PCons v PNil)" using valid_path(2) by auto
    then obtain v Ps where P: "P = PCons v Ps" "\<not>path_null Ps" by (metis Path.exhaust path_null_def valid_path(1))
    then obtain w where w: "path_head Ps = w" by blast
    have "v\<rightarrow>w" proof-
      have "P $ 0 = Some v \<and> P $ (Suc 0) = Some w" by (simp add: P(1) P(2) w)
      thus ?thesis using valid_path(3) by blast
    qed
    moreover have "Pset Ps \<subseteq> V \<and> (\<forall>i v w. Ps $ i = Some v \<and> Ps $ Suc i = Some w \<longrightarrow> v\<rightarrow>w)" by (metis P(1) Path.set_intros(2) contra_subsetD PCons_suc_is_P subsetI valid_path(2) valid_path(3))
    ultimately have "\<exists>v w Ps. P = PCons v Ps \<and> v \<in> V \<and> w \<in> V \<and> v \<rightarrow> w \<and> ((\<exists>P. Ps = P \<and> \<not> path_null P \<and> Pset P \<subseteq> V \<and> (\<forall>i v w. P $ i = Some v \<and> P $ Suc i = Some w \<longrightarrow> v \<rightarrow> w)) \<or> valid_path Ps) \<and> \<not> path_null Ps \<and> path_head Ps = w"
      using P edges_are_in_V using w by blast
  }
  thus ?case by blast
qed
lemma valid_path_equiv: "valid_path P \<longleftrightarrow> \<not>path_null P \<and> Pset P \<subseteq> V \<and> (\<forall>i v w. P $ i = Some v \<and> P $ Suc i = Some w \<longrightarrow> v\<rightarrow>w)" using valid_path_impl1 valid_path_impl2 by blast

lemma valid_path_is_infinite_or_finite: "valid_path P \<Longrightarrow> infinite_path P \<or> finite_path P" by simp
lemma valid_path_is_contiguous_suc: "valid_path P \<Longrightarrow> P $ Suc i = Some w \<Longrightarrow> \<exists>v. P $ i = Some v"
  using paths_are_contiguous_suc valid_path_is_infinite_or_finite by metis
lemma valid_paths_are_nonempty: "valid_path P \<Longrightarrow> P $ 0 \<noteq> None" using valid_path_not_null by auto
lemma valid_path_no_deadends: "valid_path P \<Longrightarrow> P $ Suc i = Some w \<Longrightarrow> \<not>deadend (the (P $ i))"
  by (metis edges_are_in_V option_the_simp valid_path_edges valid_path_is_contiguous_suc)
lemma valid_path_ends_on_deadend: "valid_path P \<Longrightarrow> P $ i = Some v \<Longrightarrow> deadend v \<Longrightarrow> P $ Suc i = None"
  by (meson deadend_no_edge option.exhaust valid_path_edges)
lemma valid_path_contiguous_deadends: "valid_path P \<Longrightarrow> P $ i = None \<Longrightarrow> i \<le> j \<Longrightarrow> P $ j = None"
  using finite_path_at2 by blast

coinductive maximal_path where
  "deadend v \<Longrightarrow> maximal_path (PCons v PNil)"
| "maximal_path Ps \<Longrightarrow> maximal_path (PCons v Ps)"

(* definition maximal_path :: "'a Path \<Rightarrow> bool" where
  [simp]: "maximal_path P \<equiv> \<forall>i. P $ i \<noteq> None \<and> \<not>deadend (the (P $ i)) \<longrightarrow> P $ Suc i \<noteq> None"
*)
lemma maximal_infinite_path_tail: "\<not>path_null (path_tail P) \<Longrightarrow> maximal_path P \<Longrightarrow> maximal_path (path_tail P)"
  by (metis Path.sel(2) maximal_path.cases path_null_def)
lemma maximal_path_not_null: "maximal_path P \<Longrightarrow> \<not>path_null P" using Path.collapse(1) maximal_path.simps by blast
lemma maximal_path_impl1: "maximal_path P \<Longrightarrow> P $ n \<noteq> None \<Longrightarrow> \<not>deadend (the (P $ n)) \<Longrightarrow> P $ Suc n \<noteq> None"
  apply (induct n arbitrary: P)
   apply (metis maximal_path.simps option.distinct(1) option.sel path_at.simps(2) path_at.simps(3))
  by (metis maximal_path.simps path_at.simps(1) path_at.simps(3))
lemma maximal_path_impl2: "\<not>path_null P \<Longrightarrow> (\<And>n. P $ n \<noteq> None \<and> \<not>deadend (the (P $ n)) \<longrightarrow> P $ Suc n \<noteq> None) \<Longrightarrow> maximal_path P"
proof (coinduction arbitrary: P rule: maximal_path.coinduct)
  case (maximal_path P)
  show ?case proof (cases "\<exists>v. P = PCons v PNil \<and> deadend v", blast)
    case False
    hence *: "\<not>path_null (path_tail P)" by (metis PCons_suc_is_P Path.collapse(1) Path.collapse(2) Path.set_sel(1) maximal_path(1) maximal_path(2) option.distinct(1) option_the_simp path_2_no_deadend path_pset_at)
    hence "\<exists>v Ps. P = PCons v Ps" by (metis Path.collapse(2) maximal_path(1))
    thus ?thesis by (metis PCons_suc_is_P Path.sel(2) "*" maximal_path(2))
  qed
qed
lemma maximal_path_equiv: "maximal_path P \<longleftrightarrow> (\<not>path_null P \<and> (\<forall>i. P $ i \<noteq> None \<and> \<not>deadend (the (P $ i)) \<longrightarrow> P $ Suc i \<noteq> None))"
  using maximal_path_impl1 maximal_path_impl2 maximal_path_not_null by blast

definition path_last :: "'a Path \<Rightarrow> 'a" where
  "path_last P = the (P $ (THE i. P $ i \<noteq> None \<and> (\<forall>j > i. P $ j = None)))"
lemma path_last_unique:
  "finite_path P \<Longrightarrow> \<exists>!i. P $ i \<noteq> None \<and> (\<forall>j > i. P $ j = None)" sorry
lemma path_last_exists:
  assumes P_finite: "finite_path P"
  shows "\<exists>i. P $ i \<noteq> None \<and> P $ Suc i = None \<and> path_last P = the (P $ i)" proof-
    def Q \<equiv> "\<lambda>i. P $ i \<noteq> None \<and> (\<forall>j > i. P $ j = None)"
    let ?i = "THE i. Q i"
    have *: "path_last P = the (P $ ?i)" using path_last_def Q_def by auto
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
  "path_priorities P i \<equiv> \<omega> (the (P $ i))"
(* The set of priorities that occur infinitely often on a given path. *)
definition path_inf_priorities :: "'a Path \<Rightarrow> nat set" where
  "path_inf_priorities P \<equiv> {k. (\<exists>i. path_priorities P i = k) \<and> (\<forall>i. path_priorities P i = k \<longrightarrow> (\<exists>j > i. path_priorities P j = k))}"

lemma path_priorities_in_\<omega>V:
  assumes "valid_path P" "infinite_path P"
  shows "path_priorities P i \<in> \<omega> ` V"
proof-
  have "the (P $ i) \<in> V" by (meson assms infinite_path_at path_at_in_pset rev_subsetD valid_path_in_V)
  thus ?thesis using path_priorities_def by auto
qed

lemma PCons_non_empty [simp]: "PCons v P $ 0 \<noteq> None" by simp

lemma PCons_infinite: "infinite_path P \<Longrightarrow> infinite_path (PCons v P)" using finite_path.simps by fastforce

(* TODO: probably redundant now *)
lemma PCons_valid:
  assumes "valid_path P" "P $ 0 = Some w0" "v0 \<rightarrow> w0"
  shows "valid_path (PCons v0 P)" using assms(1) assms(2) assms(3) valid_path_cons' valid_path_not_null by auto

lemma PCons_extends:
  assumes "\<exists>i. P $ i = Some w"
  shows "\<exists>i. PCons v P $ i = Some w" proof-
    from assms obtain i where "P $ i = Some w" by auto
    hence "PCons v P $ Suc i = Some w" by simp
    thus ?thesis by blast
  qed

lemma infinite_path_tail [intro]:
  "infinite_path P \<Longrightarrow> infinite_path (path_tail P)" by (metis Path.collapse(2) infinite_path_no_deadend infinite_path_tail)
lemma finite_path_tail [intro]:
  assumes "finite_path P" "P $ Suc 0 \<noteq> None" shows "finite_path (path_tail P)"
  by (meson finite_nil path_at.simps(1) path_last_unique)

lemma valid_path_tail2 [intro]:
  assumes "valid_path P" "P $ Suc 0 \<noteq> None"
  shows "valid_path (path_tail P)"
  by (meson assms(1) infinite_path_def infinite_path_no_deadend path_2_no_deadend path_last_unique valid_path_tail)

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
    \<or> (finite_path P \<and> (\<exists>i \<in> path_dom P. P $ Suc i = None \<and> the (P $ i) \<in> VV p**))"

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
    hence finite: "finite_path P" by simp
    then obtain i where i_def: "i \<in> path_dom P \<and> P $ Suc i = None" using assms path_dom_ends_on_finite_paths valid_path_not_null by blast
    def v \<equiv> "the (P $ i)" (* the last vertex in the path *)
    hence "v \<in> V" using valid_path_def using assms i_def by (metis (mono_tags, lifting) CollectD path_at_in_pset subsetCE valid_path_in_V)
    have "\<And>q. winning_path q P \<longleftrightarrow> (\<exists>i \<in> path_dom P. P $ Suc i = None \<and> the (P $ i) \<in> VV q**)"
      using not_infinite finite winning_path_def by metis
    hence "\<And>q. winning_path q P \<longleftrightarrow> v \<in> VV q**"
      using not_infinite finite path_dom_ends_on_finite_paths i_def v_def by (metis (no_types, lifting) Collect_cong assms valid_path_not_null)
    hence "v \<in> VV p** \<longleftrightarrow> \<not>v \<in> VV p \<Longrightarrow> ?thesis"
      by (metis (full_types) Player.exhaust)
    thus ?thesis using VV_equivalence `v \<in> V` by blast
  qed

lemma paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "\<exists>!p. winning_path p P"
  by (metis (full_types) Player.exhaust assms paths_are_winning_for_exactly_one_player)

end -- "locale ParityGame"

end
