theory attractor
imports
  Main
  parity_game strategy
begin

context ParityGame begin

definition directly_attracted :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "directly_attracted p W \<equiv> {v \<in> V - W. \<not>deadend v \<and>
      (v \<in> VV p   \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> W))
    \<and> (v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W))}"
lemma directly_attracted_disjoint:
  "directly_attracted p W \<inter> W = {}" using directly_attracted_def by auto

abbreviation "attractor_step p W S \<equiv> W \<union> S \<union> directly_attracted p S"
lemma attractor_step_empty:
  "attractor_step p {} {} = {}" using directly_attracted_def by auto
lemma attractor_step_bounded_by_V:
  "\<lbrakk> W \<subseteq> V; S \<subseteq> V \<rbrakk> \<Longrightarrow> attractor_step p W S \<subseteq> V" using directly_attracted_def by auto
lemma attractor_step_mono:
  shows "mono (attractor_step p W)"
  proof (unfold mono_def; intro allI impI)
    fix S T :: "'a set" assume "S \<subseteq> T"
    show "W \<union> S \<union> directly_attracted p S \<subseteq> W \<union> T \<union> directly_attracted p T" proof
      fix v assume v_assm: "v \<in> W \<union> S \<union> directly_attracted p S"
      show "v \<in> W \<union> T \<union> directly_attracted p T" proof (cases)
        assume "v \<in> W \<or> v \<in> T" thus ?thesis by simp
      next
        assume "\<not>(v \<in> W \<or> v \<in> T)"
        hence v_assm2: "v \<notin> W \<and> v \<notin> T" by simp
        hence v_S_attracted: "v \<in> directly_attracted p S" using v_assm `S \<subseteq> T` by blast
        hence "\<not>deadend v" using directly_attracted_def by blast
        have "v \<in> V - T" using v_S_attracted by (simp add: v_assm2 directly_attracted_def)
        hence "v \<in> directly_attracted p T" proof (cases rule: VV_cases[of v p]; simp)
          assume "v \<in> VV p"
          hence "v \<notin> VV p**" by auto
          have "\<exists>w. v\<rightarrow>w \<and> w \<in> S" using `v \<in> VV p` v_S_attracted directly_attracted_def by blast
          hence "\<exists>w. v\<rightarrow>w \<and> w \<in> T" using `S \<subseteq> T` by blast
          thus ?thesis using `v \<in> V - T` `v \<in> VV p` `v \<notin> VV p**` `\<not>deadend v` directly_attracted_def by blast
        next
          assume "v \<in> VV p**"
          hence "v \<notin> VV p" by auto
          have "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> S" using `v \<in> VV p**` v_S_attracted directly_attracted_def by blast
          hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> T" using `S \<subseteq> T` by blast
          thus ?thesis using `v \<in> V - T` `v \<in> VV p**` `v \<notin> VV p` `\<not>deadend v` directly_attracted_def by blast
        qed
        thus ?thesis by simp
      qed
    qed
  qed

lemma mono_restriction_is_mono:
  assumes "mono (f :: 'a set \<Rightarrow> 'a set)"
  shows "mono (\<lambda>S. f (S \<inter> V))" (is "mono ?f")
  proof-
    {
      fix S T :: "'a set" assume "S \<subseteq> T"
      have "?f S \<subseteq> ?f T" by (meson `S \<subseteq> T` assms inf_mono monoD subset_refl)
    }
    thus ?thesis using mono_def by blast
  qed

definition attractor :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "attractor p W = lfp (attractor_step p W)"

lemma attractor_unfolding:
  "attractor p W = attractor_step p W (attractor p W)" unfolding attractor_def using attractor_step_mono lfp_unfold by blast
lemma attractor_lowerbound:
  "attractor_step p W S \<subseteq> S \<Longrightarrow> attractor p W \<subseteq> S" unfolding attractor_def using attractor_step_mono by (simp add: lfp_lowerbound)

lemma attractor_set_induction [case_names base step union]:
  assumes base: "W \<subseteq> V" -- "This assumption might be unnecessary."
    and step: "\<And>S. S \<subseteq> V \<Longrightarrow> P S \<Longrightarrow> P (attractor_step p W S)"
    and union: "\<And>M. \<forall>S \<in> M. S \<subseteq> V \<and> P S \<Longrightarrow> P (\<Union>M)"
  shows "P (attractor p W)"
  proof-
    let ?P = "\<lambda>S. P (S \<inter> V)"
    let ?f = "\<lambda>S. attractor_step p W (S \<inter> V)"
    let ?A = "lfp ?f"
    let ?B = "lfp (attractor_step p W)"
    have f_mono: "mono ?f" using mono_restriction_is_mono[of "attractor_step p W"] attractor_step_mono by simp
    have P_A: "?P ?A" proof (rule lfp_ordinal_induct_set, simp add: f_mono)
      show "\<And>S. ?P S \<Longrightarrow> ?P (W \<union> (S \<inter> V) \<union> directly_attracted p (S \<inter> V))"
        by (metis assms(1) attractor_step_bounded_by_V inf.absorb1 inf_le2 local.step)
      show "\<And>M. \<forall>S \<in> M. ?P S \<Longrightarrow> ?P (\<Union>M)" proof-
        fix M
        let ?M = "{S \<inter> V | S. S \<in> M}"
        assume "\<forall>S\<in>M. ?P S"
        hence "\<And>S. S \<in> M \<Longrightarrow> P (S \<inter> V)" by simp
        hence "\<forall>S \<in> ?M. S \<subseteq> V \<and> P S" by auto
        hence *: "P (\<Union>?M)" by (simp add: union)
        have "\<Union>?M = (\<Union>M) \<inter> V" by blast
        thus "?P (\<Union>M)" using * by simp
      qed
    qed

    have *: "W \<union> (V \<inter> V) \<union> directly_attracted p (V \<inter> V) \<subseteq> V" using `W \<subseteq> V` attractor_step_bounded_by_V by auto
    have "?A \<subseteq> V" using * by (simp add: lfp_lowerbound)
    have "?B \<subseteq> V" using * by (simp add: lfp_lowerbound)

    have "?A = ?f ?A" using f_mono lfp_unfold by blast
    hence "?A = W \<union> (?A \<inter> V) \<union> directly_attracted p (?A \<inter> V)" using `?A \<subseteq> V` by simp
    hence *: "attractor_step p W ?A \<subseteq> ?A" using `?A  \<subseteq> V` inf.absorb1 by fastforce

    have "?B = attractor_step p W ?B" using attractor_step_mono lfp_unfold by blast
    hence "?f ?B \<subseteq> ?B" using `?B \<subseteq> V` by (metis (no_types, lifting) equalityD2 le_iff_inf)

    have "?A = ?B" proof
      show "?A \<subseteq> ?B" using `?f ?B \<subseteq> ?B` by (simp add: lfp_lowerbound)
      show "?B \<subseteq> ?A" using * by (simp add: lfp_lowerbound)
    qed
    hence "?P ?B" using P_A by (simp add: attractor_def)
    thus ?thesis using `?B \<subseteq> V` by (simp add: attractor_def le_iff_inf)
  qed

lemma attractor_set_non_empty: "W \<noteq> {} \<Longrightarrow> attractor p W \<noteq> {}"
  using attractor_unfolding by auto
lemma attractor_set_empty: "attractor p {} = {}"
  by (metis attractor_lowerbound attractor_step_empty bot.extremum_uniqueI subset_refl)

lemma attractor_set_base: "W \<subseteq> attractor p W" using attractor_unfolding by blast
lemma attractor_set_VVp:
  assumes "v \<in> VV p" "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p W"
  shows "v \<in> attractor p W"
  proof (rule ccontr)
    assume contra: "v \<notin> attractor p W"
    hence "v \<in> V - attractor p W" using assms(1) by blast
    moreover have "v \<notin> VV p**" using assms(1) by auto
    moreover have "\<not>deadend v" using assms(2) using valid_edge_set by auto
    ultimately have "v \<in> directly_attracted p (attractor p W)"
      unfolding directly_attracted_def using assms(2) by blast
    thus False using contra attractor_unfolding by auto
  qed
lemma attractor_set_VVpstar:
  assumes "v \<in> VV p**" "\<not>deadend v" "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p W"
  shows "v \<in> attractor p W"
  proof (rule ccontr)
    assume contra: "v \<notin> attractor p W"
    hence "v \<in> V - attractor p W" using assms(1) by blast
    moreover have "v \<notin> VV p" using assms(1) by auto
    ultimately have "v \<in> directly_attracted p (attractor p W)"
      unfolding directly_attracted_def using assms(2) assms(3) by blast
    thus False using contra attractor_unfolding by auto
  qed

(* The attractor set of a given set of vertices. *)
inductive_set attractor_inductive :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for p :: Player and W :: "'a set" where
  Base [intro!]: "v \<in> W \<Longrightarrow> v \<in> attractor_inductive p W" |
  VVp: "v \<in> VV p \<Longrightarrow> \<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor_inductive p W" |
  VVpstar: "\<not>deadend v \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor_inductive p W"

lemma attractor_inductive_is_attractor:
  assumes "W \<subseteq> V"
  shows "attractor_inductive p W = attractor p W"
  proof
    show "attractor_inductive p W \<subseteq> attractor p W" proof
      fix v show "v \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor p W" proof (induct rule: attractor_inductive.induct)
      case (Base v) thus ?case using attractor_set_base by auto
      next case (VVp v) thus ?case using attractor_set_VVp by auto
      next case (VVpstar v) thus ?case using attractor_set_VVpstar by auto
      qed
    qed
    show "attractor p W \<subseteq> attractor_inductive p W" proof-
      def P \<equiv> "\<lambda>S. S \<subseteq> attractor_inductive p W"
      have "P (attractor p W)" proof (induct rule: attractor_set_induction, simp add: `W \<subseteq> V`)
        show "\<And>S. S \<subseteq> V \<Longrightarrow> P S \<Longrightarrow> P (W \<union> S \<union> directly_attracted p S)" proof-
          fix S assume "S \<subseteq> V" "P S"
          hence "S \<subseteq> attractor_inductive p W" using P_def by simp
          have "W \<union> S \<union> directly_attracted p S \<subseteq> attractor_inductive p W" proof
            fix v assume "v \<in> W \<union> S \<union> directly_attracted p S"
            moreover
            { assume "v \<in> W" hence "v \<in> attractor_inductive p W" by blast }
            moreover
            { assume "v \<in> S" hence "v \<in> attractor_inductive p W" by (meson `S \<subseteq> attractor_inductive p W` set_rev_mp) }
            moreover
            { assume v_attracted: "v \<in> directly_attracted p S"
              hence "v \<in> V" using `S \<subseteq> V` attractor_step_bounded_by_V by blast
              hence "v \<in> attractor_inductive p W" proof (cases rule: VV_cases)
                assume "v \<in> VV p"
                hence "\<exists>w. v\<rightarrow>w \<and> w \<in> S" using v_attracted directly_attracted_def by blast
                hence "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W" using `S \<subseteq> attractor_inductive p W` by blast
                thus ?thesis by (simp add: `v \<in> VV p` attractor_inductive.VVp)
              next
                assume "v \<in> VV p**"
                hence *: "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> S" using v_attracted directly_attracted_def by blast
                have "\<not>deadend v" using v_attracted directly_attracted_def by blast
                show ?thesis proof (rule ccontr)
                  assume "v \<notin> attractor_inductive p W"
                  hence "\<exists>w. v\<rightarrow>w \<and> w \<notin> attractor_inductive p W" by (metis attractor_inductive.VVpstar `v \<in> VV p**` `\<not>deadend v`)
                  hence "\<exists>w. v\<rightarrow>w \<and> w \<notin> S" using `S \<subseteq> attractor_inductive p W` by (meson subsetCE)
                  thus False using * by blast
                qed
              qed
            }
            ultimately show "v \<in> attractor_inductive p W" by (meson UnE)
          qed
          thus "P (W \<union> S \<union> directly_attracted p S)" using P_def by simp
        qed
        show "\<And>M. \<forall>S\<in>M. S \<subseteq> V \<and> P S \<Longrightarrow> P (\<Union>M)" by (simp add: P_def Sup_least)
      qed
      thus ?thesis using P_def by simp
    qed
  qed

lemma attractor_is_superset [simp]:
  shows "W \<subseteq> attractor_inductive p W" by (simp add: attractor_inductive.intros(1) subsetI)

lemma attractor_is_bounded_by_V:
  assumes "W \<subseteq> V" shows "attractor_inductive p W \<subseteq> V"
  proof -
    { fix v assume "v \<in> attractor_inductive p W"
      hence "v \<in> W \<or> v \<in> VV p \<or> v \<in> VV p**" using attractor_inductive.simps by blast
      hence "v \<in> V" by (metis (full_types) Diff_subset assms subsetCE valid_player0_set)
    }
    thus ?thesis by blast
  qed

(* lemma attractor_is_finite:
  "W \<subseteq> V \<Longrightarrow> finite (attractor p W)" by (metis assms attractor_is_bounded_by_V finite_vertex_set rev_finite_subset)
*)

lemma attractor_inductive_outside: "\<lbrakk> v \<notin> attractor_inductive p W; v \<in> VV p; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<notin> attractor_inductive p W" by (metis attractor_inductive.VVp)
lemma attractor_outside: "\<lbrakk> v \<notin> attractor p W; v \<in> VV p; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<notin> attractor p W" using attractor_set_VVp by blast

lemma directly_attracted_is_bounded_by_V:
  shows "directly_attracted p W \<subseteq> V" using directly_attracted_def by blast
(* lemma directly_attracted_is_finite [simp]:
  shows "finite (directly_attracted p W)" using directly_attracted_is_bounded_by_V finite_subset finite_vertex_set by blast
*)
lemma directly_attracted_is_disjoint_from_W [simp]:
  shows "W \<inter> directly_attracted p W = {}" using directly_attracted_def by blast
lemma directly_attracted_is_eventually_empty [simp]:
  shows "directly_attracted p V = {}" using directly_attracted_def by blast
lemma directly_attracted_contains_no_deadends [elim]:
  shows "v \<in> directly_attracted p W \<Longrightarrow> \<not>deadend v" using directly_attracted_def by blast
lemma directly_attracted_empty_set [simp]:
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
lemma directly_attracted_union:
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

lemma attractor_inductive_contains_no_deadends:
  "v \<in> attractor_inductive p W \<Longrightarrow> v \<in> W \<or> \<not>deadend v"
  proof (induct rule: attractor_inductive.induct)
    fix v assume "v \<in> W" thus "v \<in> W \<or> \<not>deadend v" by simp
  next
    fix v assume "v \<in> VV p" and "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W \<and> (w \<in> W \<or> \<not>deadend w)"
    thus "v \<in> W \<or> \<not>deadend v" using local.valid_edge_set by auto
  next
    fix v assume "\<not>deadend v"
    thus "v \<in> W \<or> \<not>deadend v" by simp
  qed

lemma attractor_contains_no_deadends:
  "\<lbrakk> W \<subseteq> V; v \<in> attractor p W \<rbrakk> \<Longrightarrow> v \<in> W \<or> \<not>deadend v"
  using attractor_inductive_contains_no_deadends attractor_inductive_is_attractor by auto

(* True iff the given set is attractor closed. *)
definition attractor_closed :: "Player \<Rightarrow> 'a set \<Rightarrow> bool" where
  "attractor_closed p W \<equiv> directly_attracted p W = {}"

(* Show that the attractor set is indeed attractor closed. *)
(*
lemma attractor_is_attractor_closed [simp]:
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

(* function attractor_set_fun :: "nat \<Rightarrow> Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "attractor_set_fun 0 p W = W"
  | "attractor_set_fun (Suc n) p W = (if directly_attracted p W = {} then W else attractor_set_fun n p (W \<union> directly_attracted p W))"
  by pat_completeness auto
  termination by lexicographic_order

lemma attractor_set_fun_subset [simp]:
  "W \<subseteq> attractor_set_fun n p W" proof (induct n arbitrary: W)
    case 0 thus ?case by auto
    case (Suc n) thus ?case by (metis Un_subset_iff attractor_set_fun.simps(2) eq_iff)
  qed
lemma attractor_set_fun_monotone:
  "attractor_set_fun n p W \<subseteq> attractor_set_fun (Suc n) p W" by (induct n arbitrary: W; auto)
lemma attractor_set_fun_monotone_generalized [simp]:
  "attractor_set_fun n p W \<subseteq> attractor_set_fun (n + m) p W" by (induct n arbitrary: W m; simp)
lemma attractor_set_fun_bounded_by_V:
  "attractor_set_fun n p W \<subseteq> V \<union> W" proof (induct n arbitrary: W)
    case 0 thus ?case by auto
    case (Suc n)
    have "directly_attracted p W \<subseteq> V" by (simp add: directly_attracted_is_bounded_by_V)
    thus ?case using Suc.hyps by auto
  qed
*)

(* lemma attractor_set_fun_finite:
  "finite W \<Longrightarrow> finite (attractor_set_fun n p W)" by (metis attractor_set_fun_bounded_by_V finite_UnI finite_vertex_set rev_finite_subset)
*)

(* lemma attractor_set_fun_equivalence [iff]:
  "attractor_set_fun (Suc n) p W = attractor_set_fun n p (W \<union> directly_attracted p W)"
  by (metis Un_empty_right attractor_set_fun.elims attractor_set_fun.simps(2))

lemma attractor_set_fun_directly_attracted:
  "attractor_set_fun n p W \<union> directly_attracted p (attractor_set_fun n p W) = attractor_set_fun (Suc n) p W"
  by (induct n arbitrary: W; auto)

lemma attractor_set_fun_eventually_constant:
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

lemma attractor_set_fun_attractor:
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

lemma attractor_set_induction:
  fixes p :: Player and W :: "'a set" and P :: "'a set \<Rightarrow> bool"
  assumes "W \<subseteq> V" "P W"
    and step: "\<And>W'. W \<subseteq> W' \<Longrightarrow> W' \<subseteq> V \<Longrightarrow> P W' \<Longrightarrow> P (W' \<union> (directly_attracted p W'))"
    and union: "\<And>M. \<forall>S \<in> M. W \<subseteq> S \<and> S \<subseteq> V \<and> P S \<Longrightarrow> P (\<Union>M)"
  shows "P (attractor p W)"
  proof -
    print_statement attractorp.induct
    have "P (attractor p W)" proof (induct rule: lfp_ordinal_induct_set[of attractor])
    qed
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

*)

(* lemma attractor_induction:
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
*)

(*
lemma attractor_strategy_can_be_extended:
  assumes W': "W \<subseteq> W'" "W' \<subseteq> V" "\<exists>\<sigma>. valid_strategy p \<sigma> \<and> attractor_strategy_on p \<sigma> W' W"
    and v_directly_attracted: "v \<in> directly_attracted p W'"
  shows "\<exists>\<sigma>. valid_strategy p \<sigma> \<and> attractor_strategy_on p \<sigma> (insert v W') W"
proof-
  obtain \<sigma> where \<sigma>: "valid_strategy p \<sigma>" "attractor_strategy_on p \<sigma> W' W" using W'(3) by blast
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
    moreover have "strategy_only_on p ?\<sigma>' (insert v (W' - W))" using strategy_only_on_case_rule \<sigma> v `v \<notin> W'` `v\<rightarrow>w` by blast
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
        have "P (Suc 0) \<noteq> None" by (metis P(1) P(2) `the (P 0) = v` directly_attracted_contains_no_deadends maximal_path_def v_directly_attracted valid_paths_are_nonempty)
        have "the (P 0) \<in> VV p" by (simp add: `the (P 0) = v` v)
        hence "\<sigma>'' (the (P 0)) = P (Suc 0)" using P(1) P(3) path_conforms_with_strategy_def valid_paths_are_nonempty by blast
        hence "\<sigma>'' v = P (Suc 0)" using `the (P 0) = v` by blast
        hence "w = the (P (Suc 0))" using `\<sigma>'' v = Some w` by (metis option.sel)
        hence "the (P (Suc 0)) \<in> W'" using w(1) by blast
        hence "the (path_tail P 0) \<in> W'" by simp
        moreover have "valid_path (path_tail P)" using P(1) `P (Suc 0) \<noteq> None` valid_path_tail by blast
        moreover have "maximal_path (path_tail P)" using P(2) by blast
        moreover have "path_conforms_with_strategy p (path_tail P) \<sigma>''" using P(3) by blast
        ultimately have "\<exists>i. path_tail P i \<noteq> None \<and> the (path_tail P i) \<in> W" using \<sigma> \<sigma>_less_eq_\<sigma>'' strategy_attracts_from_to_def by blast
        thus ?thesis by auto
      qed
    qed
    moreover have "valid_strategy p ?\<sigma>'" proof-
      { fix u assume "u \<in> VV p" "?\<sigma>' u \<noteq> None"
        have "u \<rightarrow> the (?\<sigma>' u)" proof (cases "u = v"; insert w(2); simp)
          assume "u \<noteq> v"
          hence "\<sigma> u \<noteq> None" by (metis `?\<sigma>' u \<noteq> None` fun_upd_apply)
          thus "u \<rightarrow> the (\<sigma> u)" using \<sigma>(1) `u \<in> VV p` valid_strategy_def by blast
        qed
      }
      thus ?thesis using valid_strategy_def by blast
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
        have "P (Suc 0) \<noteq> None" by (metis P(1) P(2) P(4) `the (P 0) \<notin> W'` directly_attracted_contains_no_deadends insertE maximal_path_def v_directly_attracted valid_paths_are_nonempty)
        have "\<not>deadend v" using directly_attracted_contains_no_deadends v_directly_attracted by blast
        hence "the (P 0) \<rightarrow> the (P (Suc 0))" by (metis P(1) P(2) P(4) `the (P 0) \<notin> W'` insertE maximal_path_def valid_path_def)
        hence "the (P (Suc 0)) \<in> W'" using P(4) `\<forall>w. v \<rightarrow> w \<longrightarrow> w \<in> W'` `the (P 0) \<notin> W'` by blast
        hence "the (path_tail P 0) \<in> W'" by simp
        moreover have "valid_path (path_tail P)" using P(1) `P (Suc 0) \<noteq> None` valid_path_tail by blast
        moreover have "maximal_path (path_tail P)" using P(2) by blast
        moreover have "path_conforms_with_strategy p (path_tail P) \<sigma>'" using P(3) by blast
        ultimately have "\<exists>i. path_tail P i \<noteq> None \<and> the (path_tail P i) \<in> W" using \<sigma> \<sigma>_less_eq_\<sigma>' strategy_attracts_from_to_def by blast
        thus ?thesis by auto
      qed
    qed
    ultimately show ?thesis using \<sigma>(1) by blast
  qed
qed
*)

abbreviation strategy_attracts_to :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_to p \<sigma> v0 W \<equiv> \<forall>P \<sigma>'. valid_strategy p \<sigma>' \<and> strategy_less_eq \<sigma> \<sigma>'
        \<and> valid_path P \<and> P 0 = Some v0 \<and> path_conforms_with_strategy_maximally p P \<sigma>'
        \<longrightarrow> (\<exists>n. P n \<noteq> None \<and> the (P n) \<in> W)"
definition attractor_strategy_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "attractor_strategy_on p \<sigma> v0 A W \<equiv>
    valid_strategy p \<sigma> \<and> strategy_only_on p \<sigma> (A - W) \<and> strategy_attracts_to p \<sigma> v0 W"

lemma strategy_attracts_to_extends:
  "\<lbrakk> strategy_attracts_to p \<sigma> v0 W; strategy_less_eq \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> strategy_attracts_to p \<sigma>' v0 W"
  using strategy_less_eq_tran by blast
lemma attractor_strategy_on_extends:
  assumes "attractor_strategy_on p \<sigma> v0 S W" "S \<subseteq> A"
  shows "\<exists>\<sigma>'. strategy_less_eq \<sigma> \<sigma>' \<and> attractor_strategy_on p \<sigma>' v0 A W"
  proof-
    have \<sigma>: "valid_strategy p \<sigma> \<and> strategy_only_on p \<sigma> (S - W) \<and> strategy_attracts_to p \<sigma> v0 W"
      using attractor_strategy_on_def assms(1) by blast
    then obtain \<sigma>' where \<sigma>'_def: "valid_strategy p \<sigma>'" "strategy_less_eq \<sigma> \<sigma>'"
      "strategy_only_on p \<sigma>' (A - W)"
      using strategy_only_on_extensible assms by blast
    moreover have "strategy_attracts_to p \<sigma>' v0 W" using strategy_attracts_to_extends \<sigma>(1) \<sigma>'_def(2) by blast
    ultimately have "attractor_strategy_on p \<sigma>' v0 A W" using attractor_strategy_on_def by blast
    thus ?thesis using \<sigma>'_def(2) by blast
  qed
(* ML_val {*
(*proof body with digest*)
val body = Proofterm.strip_thm (Thm.proof_body_of @{thm obtain_min});
(*proof term only*)
val prf = Proofterm.proof_of body;
Pretty.writeln (Proof_Syntax.pretty_proof @{context} prf);
(*all theorems used in the graph of nested proofs*)
val all_thms =
Proofterm.fold_body_thms
(fn (name, _, _) => insert (op =) name) [body] [];
*} *)

lemma merge_attractor_strategies:
  fixes W p S
  assumes "W \<subseteq> V"
    and "S \<subseteq> V"
    and "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. attractor_strategy_on p \<sigma> v S W"
  shows "\<exists>\<sigma>. \<forall>v \<in> S. attractor_strategy_on p \<sigma> v S W"
  proof-
    let ?good = "\<lambda>v. {\<sigma>. attractor_strategy_on p \<sigma> v S W}"
    def G \<equiv> "{ \<sigma>. \<exists>v \<in> S. attractor_strategy_on p \<sigma> v S W }"
    obtain r where "well_order_on G r" using well_order_on by blast
    def choose \<equiv> "\<lambda>v. THE \<sigma>. \<sigma> \<in> ?good v \<and> (\<forall>\<sigma>'. (\<sigma>', \<sigma>) \<in> r \<longrightarrow> \<sigma>' \<notin> ?good v)"
    def \<sigma> \<equiv> "\<lambda>v. if v \<in> S - W
      then Some (choose v)
      else None"
    (* have "\<And>v. v \<in> S - W \<Longrightarrow> \<exists>!\<sigma>. ?good \<sigma> v \<and> (\<forall>\<sigma>'. ?good \<sigma>' v \<and> \<sigma> \<noteq> \<sigma>' \<longrightarrow> (\<sigma>,\<sigma>') \<in> r)" proof
      fix v assume "v \<in> S - W"
      have "\<exists>\<sigma>. ?good \<sigma> v" using `v \<in> S - W` assms(3) by auto
      hence "\<exists>\<sigma>. ?good \<sigma> v \<and> (\<forall>\<sigma>'. ?good \<sigma>' v \<and> \<sigma> \<noteq> \<sigma>' \<longrightarrow> (\<sigma>,\<sigma>') \<in> r)" sorry
    qed *)
    show ?thesis sorry
  qed

theorem attractor_has_strategy:
  fixes W p
  assumes "W \<subseteq> V"
    and v0_def: "v0 \<in> attractor p W" (is "_ \<in> ?A")
  shows "\<exists>\<sigma>. attractor_strategy_on p \<sigma> v0 ?A W"
  proof-
    from v0_def have "\<exists>\<sigma>. attractor_strategy_on p \<sigma> v0 ?A W" proof (induct arbitrary: v0 rule: attractor_set_induction)
      case base thus ?case using `W \<subseteq> V` .
    next
      case (step S)
      { assume "v0 \<in> S"
        then obtain \<sigma> where \<sigma>_def: "attractor_strategy_on p \<sigma> v0 S W" using step.hyps by blast
        moreover have "S \<subseteq> W \<union> S \<union> directly_attracted p S" by blast
        ultimately have "\<exists>\<sigma>'. attractor_strategy_on p \<sigma>' v0 (W \<union> S \<union> directly_attracted p S) W"
          using attractor_strategy_on_extends by blast
      }
      moreover { assume "v0 \<in> W"
        let ?\<sigma> = "\<lambda>_. None"
        have "valid_strategy p ?\<sigma>" using valid_empty_strategy by blast
        moreover have "strategy_only_on p ?\<sigma> ({} - W)" using strategy_only_on_def by blast
        moreover have "strategy_attracts_to p ?\<sigma> v0 W" by (metis `v0 \<in> W` option.distinct(1) option.sel)
        ultimately have "attractor_strategy_on p ?\<sigma> v0 {} W" using attractor_strategy_on_def by blast
        hence "\<exists>\<sigma>'. attractor_strategy_on p \<sigma>' v0 (W \<union> S \<union> directly_attracted p S) W" using attractor_strategy_on_extends by blast
      }
      moreover { assume attracted: "v0 \<in> directly_attracted p S" "v0 \<notin> W" "v0 \<notin> S"
        hence "v0 \<in> V" using directly_attracted_is_bounded_by_V by blast
        have "\<exists>\<sigma>'. attractor_strategy_on p \<sigma>' v0 (W \<union> S \<union> directly_attracted p S) W" proof (cases)
          assume "v0 \<in> VV p"
          hence *: "\<exists>w. v0\<rightarrow>w \<and> w \<in> S" using attracted directly_attracted_def by blast
          hence v0_no_deadend: "\<not>deadend v0" using step.hyps(1) by auto
          from * obtain w where w_def: "v0 \<rightarrow> w" "w \<in> S" by blast
          hence "\<exists>\<sigma>. attractor_strategy_on p \<sigma> w S W" using step.hyps by blast
          then obtain \<sigma> where \<sigma>_def: "valid_strategy p \<sigma>" "strategy_only_on p \<sigma> (S - W)" "strategy_attracts_to p \<sigma> w W" using attractor_strategy_on_def by blast
          let ?\<sigma> = "\<sigma>(v0 \<mapsto> w)" (* Extend \<sigma> to the new node. *)
          have "?\<sigma> v0 = Some w" by simp
          have "\<sigma> v0 = None" using \<sigma>_def(2) attracted(3) by auto
          hence less_eq: "strategy_less_eq \<sigma> ?\<sigma>" using strategy_less_eq_updates by blast
          have "valid_strategy p ?\<sigma>" using \<sigma>_def w_def(1) valid_strategy_updates `v0 \<in> VV p` by blast
          moreover have "strategy_only_on p ?\<sigma> (S \<union> {v0} - W)" proof-
            have "strategy_only_on p ?\<sigma> ((S - W) \<union> {v0})"
              using strategy_only_on_updates \<sigma>_def(2) `v0 \<in> VV p` by blast
            moreover have "(S - W) \<union> {v0} = S \<union> {v0} - W" using `v0 \<notin> W` by blast
            ultimately show ?thesis by simp
          qed
          moreover have "strategy_attracts_to p ?\<sigma> v0 W" proof-
            { fix P \<sigma>'
              assume \<sigma>': "valid_strategy p \<sigma>'" "strategy_less_eq ?\<sigma> \<sigma>'"
                "valid_path P" "P 0 = Some v0" "path_conforms_with_strategy_maximally p P \<sigma>'"

              have 1: "P 0 \<noteq> None" by (simp add: \<sigma>'(4))
              have 2: "the (P 0) \<in> VV p" by (simp add: \<sigma>'(4) `v0 \<in> VV p`)
              have 3: "\<not>deadend (the (P 0))" using \<sigma>'(4) v0_no_deadend by auto
              have 4: "\<sigma>' v0 \<noteq> None" proof-
                have "?\<sigma> v0 \<noteq> None" by (simp add: \<sigma>'(4))
                thus ?thesis using strategy_less_eq_not_none2 \<sigma>'(2) by blast
              qed
              note P = 1 2 3 4

              have less_eq: "strategy_less_eq \<sigma> \<sigma>'" using local.less_eq strategy_less_eq_tran \<sigma>'(2) by blast
              moreover have tail_start: "(path_tail P) 0 = Some w" proof-
                have "\<sigma>' v0 = P (Suc 0)" using P \<sigma>'(5) path_conforms_with_strategy_maximally_start \<sigma>'(4) `v0 \<in> VV p` by blast
                moreover have "\<sigma>' v0 = Some w" using \<sigma>'(2) by (metis (mono_tags, lifting) `(\<sigma>(v0 \<mapsto> w)) v0 = Some w` strategy_less_eq_def)
                ultimately show ?thesis by presburger
              qed
              moreover have tail_valid: "valid_path (path_tail P)" by (metis \<sigma>'(3) option.distinct(1) tail_start valid_path_tail)
              moreover have tail_conforms: "path_conforms_with_strategy_maximally p (path_tail P) \<sigma>'" using P \<sigma>'(4) \<sigma>'(5) `v0 \<in> VV p` path_conforms_with_strategy_maximally_tail by blast
              ultimately obtain P' where P'_def: "path_prefix P' (path_tail P)" "path_conforms_with_strategy_maximally p P' \<sigma>"
                using paths_can_be_restricted \<sigma>' by blast

              have "P' 0 = Some w" by (metis P'_def(1) `path_tail P 0 = Some w` path_prefix_first)
              moreover have "valid_path P'" using P'_def(1) tail_valid path_prefix_valid by blast
              ultimately obtain n where n_def: "P' n \<noteq> None" "the (P' n) \<in> W" using P'_def(2) using \<sigma>_def(1) \<sigma>_def(3) strategy_less_eq_refl by blast
              have "P' n = (path_tail P) n" using n_def(1) P'_def(1) path_prefix_included by blast
              hence "(path_tail P) n \<noteq> None \<and> the ((path_tail P) n) \<in> W" using n_def by presburger
              hence "\<exists>n. P n \<noteq> None \<and> the (P n) \<in> W" by blast
            }
            thus ?thesis by blast
          qed
          ultimately have "attractor_strategy_on p ?\<sigma> v0 (S \<union> {v0}) W"
            apply (unfold attractor_strategy_on_def; intro conjI) apply (assumption)+ done
          moreover have "S \<union> {v0} \<subseteq> W \<union> S \<union> directly_attracted p S" using step.prems by blast
          ultimately show ?thesis
            using attractor_strategy_on_extends[of p ?\<sigma> v0 "S \<union> {v0}" W "W \<union> S \<union> directly_attracted p S"] by blast
        next
          assume "v0 \<notin> VV p"
          hence "v0 \<in> VV p**" using `v0 \<in> V` by blast
          have "\<not>deadend v0" using attracted directly_attracted_contains_no_deadends by blast
          have "\<forall>w. v0\<rightarrow>w \<longrightarrow> w \<in> S" using attracted by (simp add: directly_attracted_def `v0 \<in> VV p**`)
          obtain \<sigma> where \<sigma>_def: "\<And>v. v \<in> S \<Longrightarrow> attractor_strategy_on p \<sigma> v S W"
            using merge_attractor_strategies[of W S p] assms(1) step.hyps(1) step.hyps(2) by blast
          have "strategy_only_on p \<sigma> (S - W)" using \<sigma>_def `\<forall>w. v0 \<rightarrow> w \<longrightarrow> w \<in> S` `\<not>deadend v0` attractor_strategy_on_def by blast
          hence "strategy_only_on p \<sigma> ((S - W) \<union> {v0})" by (simp add: `v0 \<notin> VV p` strategy_only_on_case_rule2)
          hence "strategy_only_on p \<sigma> ((S \<union> {v0}) - W)" by (simp add: attracted(2) insert_Diff_if)
          moreover have "valid_strategy p \<sigma>" using \<sigma>_def `\<forall>w. v0 \<rightarrow> w \<longrightarrow> w \<in> S` `\<not> deadend v0` attractor_strategy_on_def by blast
          moreover have "strategy_attracts_to p \<sigma> v0 W" proof-
            { fix P \<sigma>' assume \<sigma>': "valid_strategy p \<sigma>'" "strategy_less_eq \<sigma> \<sigma>'"
                "valid_path P" "P 0 = Some v0" "path_conforms_with_strategy_maximally p P \<sigma>'"
              have "path_tail P 0 \<noteq> None" using path_conforms_with_strategy_maximally_start_VVpstar \<sigma>'(4) \<sigma>'(5) `\<not>deadend v0` `v0 \<in> VV p**` by (metis option.distinct(1))
              hence tail_valid: "valid_path (path_tail P)" using \<sigma>'(3) by blast
              have "the (path_tail P 0) \<in> S" using \<sigma>'(3) \<sigma>'(4) `\<forall>w. v0 \<rightarrow> w \<longrightarrow> w \<in> S` `path_tail P 0 \<noteq> None` valid_path_def by (metis option.collapse)
              then obtain w where w_def: "w \<in> S" and tail_start: "path_tail P 0 = Some w" using `path_tail P 0 \<noteq> None` by (metis option.collapse)
              have tail_conforms: "path_conforms_with_strategy_maximally p (path_tail P) \<sigma>'" using path_conforms_with_strategy_maximally_tail_VVpstar
                by (metis \<sigma>'(4) \<sigma>'(5) `\<And>thesis. (\<And>w. \<lbrakk>w \<in> S; path_tail P 0 = Some w\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis` `v0 \<in> VV p**`)
              have "attractor_strategy_on p \<sigma> w S W" using w_def \<sigma>_def by blast
              hence "\<exists>n. path_tail P n \<noteq> None \<and> the (path_tail P n) \<in> W" using tail_valid tail_start tail_conforms
                using \<sigma>'(1) \<sigma>'(2) attractor_strategy_on_def by blast
              hence "\<exists>n. P n \<noteq> None \<and> the (P n) \<in> W" by blast
            }
            thus ?thesis by blast
          qed
          ultimately have "attractor_strategy_on p \<sigma> v0 (S \<union> {v0}) W" using attractor_strategy_on_def by blast
          moreover have "S \<union> {v0} \<subseteq> W \<union> S \<union> directly_attracted p S" using step.prems by blast
          ultimately show ?thesis
            using attractor_strategy_on_extends[of p \<sigma> v0 "S \<union> {v0}" W "W \<union> S \<union> directly_attracted p S"] by blast
        qed
      }
      ultimately show ?case using step.prems by blast
    next
      case (union M)
      then obtain S where "S \<in> M" "v0 \<in> S" by blast
      thus ?case by (meson Union_upper attractor_strategy_on_extends union.hyps)
    qed
    thus ?thesis by blast
  qed

corollary attractor_has_strategy_weak:
  fixes W p
  defines "A \<equiv> attractor p W"
  assumes "W \<subseteq> V" "W \<noteq> {}"
  shows "\<exists>\<sigma>. strategy_only_on p \<sigma> (A - W) \<and> strategy_attracts_from_to p \<sigma> A W"
proof -
  have "A \<subseteq> V" by (simp add: A_def assms(2) attractor_lowerbound)
  moreover have "\<And>v. v \<in> A \<Longrightarrow> \<exists>\<sigma>. attractor_strategy_on p \<sigma> v A W" using assms attractor_has_strategy by blast
  ultimately obtain \<sigma> where \<sigma>_def: "\<forall>v \<in> A. attractor_strategy_on p \<sigma> v A W" using merge_attractor_strategies `W \<subseteq> V` by blast
  have "A \<noteq> {}" by (simp add: A_def assms(3) attractor_set_non_empty)
  hence "\<exists>v \<in> A. attractor_strategy_on p \<sigma> v A W" using \<sigma>_def by blast
  hence "strategy_only_on p \<sigma> (A - W)" using attractor_strategy_on_def by blast
  moreover have "strategy_attracts_from_to p \<sigma> A W" using assms sorry
  ultimately show ?thesis using strategy_less_eq_refl by blast
qed

(* If A is the p-attractor of a set W, then p** has a strategy on V - A avoiding A. *)
theorem attractor_has_outside_strategy:
  fixes W p
  defines "A \<equiv> attractor p** W"
  shows "\<exists>\<sigma>. valid_strategy p \<sigma> \<and> strategy_only_on p \<sigma> (V - A) \<and> strategy_avoids p \<sigma> (V - A) A"
  proof (intro exI conjI)
    (* Define a strategy on the p-Nodes in V - A.  \<sigma> simply chooses an arbitrary node not in A as
    the successor. *)
    def \<sigma> \<equiv> "\<lambda>v. (
      if v \<in> (V - A) \<and> v \<in> VV p \<and> \<not>deadend v
        then Some (SOME w. w \<notin> A \<and> v\<rightarrow>w)
        else None)"
    (* We need to show that \<sigma> is well-defined.  This means we have to show that \<sigma> always applies
    the SOME quantifier to a non-empty set. *)
    have \<sigma>_correct: "\<And>v. \<sigma> v \<noteq> None \<Longrightarrow> the (\<sigma> v) \<notin> A \<and> v\<rightarrow>(the (\<sigma> v))" using \<sigma>_def proof-
      fix v assume \<sigma>_v_not_None: "\<sigma> v \<noteq> None"
      have "\<not>(v \<in> (V - A) \<inter> VV p \<and> \<not>deadend v) \<Longrightarrow> \<sigma> v = None" using \<sigma>_def by auto
      hence v_not_in_A_no_deadend: "v \<in> (V - A) \<inter> VV p \<and> \<not>deadend v" using \<sigma>_v_not_None by blast
      hence "the (\<sigma> v) = (SOME w. w \<notin> A \<and> v\<rightarrow>w)" using \<sigma>_def by auto
      moreover have "\<exists>w. w \<notin> A \<and> v\<rightarrow>w" proof (rule ccontr)
        assume "\<not>(\<exists>w. w \<notin> A \<and> v\<rightarrow>w)"
        hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> A" by auto
        hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p** W" using A_def by simp
        hence "v \<in> attractor p** W" using v_not_in_A_no_deadend attractor.VVpstar by auto
        hence "v \<in> A" using A_def by simp
        thus False using v_not_in_A_no_deadend by blast
      qed
      ultimately show "the (\<sigma> v) \<notin> A \<and> v\<rightarrow>(the (\<sigma> v))" by (metis (mono_tags, lifting) someI_ex)
    qed

    show "valid_strategy p \<sigma>" using \<sigma>_correct valid_strategy_def by blast

    show "strategy_only_on p \<sigma> (V - A)" using \<sigma>_def strategy_only_on_def[of p \<sigma> "V - A"] by auto

    show "strategy_avoids p \<sigma> (V - A) A" proof (cases)
      assume "V - A = {}"
      show ?thesis by (simp add: `V - A = {}`)
    next
      assume "V - A \<noteq> {}"
      show ?thesis proof (unfold strategy_avoids_def; intro allI impI; elim conjE)
        fix P n i
        assume P_valid: "valid_path P"
          and P_conforms: "path_conforms_with_strategy_up_to p P \<sigma> n"
          and P_valid_start: "the (P 0) \<in> V - A"
        show "i \<le> n \<Longrightarrow> P i \<noteq> None \<Longrightarrow> the (P i) \<notin> A" proof (induct i)
          case 0 thus ?case using P_valid_start by auto
        next
          case (Suc i)
          have "i \<le> n" using Suc.prems(1) by presburger
          have P_i_not_None: "P i \<noteq> None" using Suc.prems P_valid valid_path_is_contiguous_suc by blast
          hence P_i_not_in_A: "the (P i) \<notin> A" using Suc.hyps `i \<le> n` by blast
          have "the (P i) \<in> V" using P_i_not_None P_valid valid_path_def by blast
          thus "the (P (Suc i)) \<notin> A" proof (cases rule: VV_cases)
            assume "the (P i) \<in> VV p"
            hence *: "\<sigma> (the (P i)) = P (Suc i)" using P_conforms P_i_not_None path_conforms_with_strategy_up_to_def Suc.prems(1) by (metis Suc_le_lessD)
            hence "\<sigma> (the (P i)) \<noteq> None" by (simp add: Suc.prems)
            hence "the (\<sigma> (the (P i))) \<notin> A" using \<sigma>_correct[of "the (P i)"] by blast
            thus ?thesis by (simp add: *)
          next
            assume "the (P i) \<in> VV p**"
            moreover have "the (P i)\<rightarrow>the (P (Suc i))" using P_i_not_None P_valid Suc.prems valid_path_def by blast
            ultimately show "the (P (Suc i)) \<notin> A" apply (insert P_i_not_in_A; unfold A_def) using attractor_outside[of "the (P i)" "p**" W "the (P (Suc i))"] by simp
          qed
        qed
      qed
    qed
  qed

end -- "context ParityGame"

end
