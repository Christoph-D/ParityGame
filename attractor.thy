(* Definition of the attractor. *)
theory attractor
imports
  Main
  strategy_attracts
begin

context ParityGame begin

definition directly_attracted :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "directly_attracted p W \<equiv> {v \<in> V - W. \<not>deadend v \<and>
      (v \<in> VV p   \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> W))
    \<and> (v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> W))}"

abbreviation "attractor_step p W S \<equiv> W \<union> S \<union> directly_attracted p S"

(* The attractor set of a given set of vertices, defined as a least fixed point *)
definition attractor :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "attractor p W = lfp (attractor_step p W)"

(* The attractor set of a given set of vertices, defined inductively. *)
inductive_set attractor_inductive :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for p :: Player and W :: "'a set" where
  Base [intro!]: "v \<in> W \<Longrightarrow> v \<in> attractor_inductive p W" |
  VVp: "v \<in> VV p \<Longrightarrow> \<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor_inductive p W" |
  VVpstar: "\<not>deadend v \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor_inductive p W"

definition attractor_strategy_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "attractor_strategy_on p \<sigma> A W \<equiv> strategy p \<sigma> \<and> strategy_attracts p \<sigma> A W"

lemma directly_attracted_disjoint [simp]: "directly_attracted p W \<inter> W = {}"
  and directly_attracted_empty [simp]: "directly_attracted p {} = {}"
  and directly_attracted_V_empty [simp]: "directly_attracted p V = {}"
  and directly_attracted_bounded_by_V [simp]: "directly_attracted p W \<subseteq> V"
  and directly_attracted_contains_no_deadends [elim]: "v \<in> directly_attracted p W \<Longrightarrow> \<not>deadend v"
  using directly_attracted_def by auto

lemma directly_attracted_union:
  assumes "v \<in> directly_attracted p W" "v \<notin> U"
  shows "v \<in> directly_attracted p (W \<union> U)"
proof-
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

(* attractor_step *)

lemma attractor_step_empty: "attractor_step p {} {} = {}"
  and attractor_step_bounded_by_V: "\<lbrakk> W \<subseteq> V; S \<subseteq> V \<rbrakk> \<Longrightarrow> attractor_step p W S \<subseteq> V"
  by simp_all

lemma mono_restriction_is_mono: "mono f \<Longrightarrow> mono (\<lambda>S. f (S \<inter> V))"
  unfolding mono_def by (meson inf_mono monoD subset_refl)

lemma attractor_step_mono: "mono (attractor_step p W)"
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
      hence "v \<in> directly_attracted p T" proof (cases rule: VV_cases[of v p], simp)
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

(* attractor *)

lemma attractor_unfolding: "attractor p W = attractor_step p W (attractor p W)"
  unfolding attractor_def using attractor_step_mono lfp_unfold by blast
lemma attractor_lowerbound: "attractor_step p W S \<subseteq> S \<Longrightarrow> attractor p W \<subseteq> S"
  unfolding attractor_def using attractor_step_mono by (simp add: lfp_lowerbound)

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
  and attractor_set_base: "W \<subseteq> attractor p W"
  using attractor_unfolding by auto
lemma attractor_set_empty: "attractor p {} = {}"
  by (metis attractor_lowerbound attractor_step_empty bot.extremum_uniqueI subset_refl)

lemma attractor_set_VVp:
  assumes "v \<in> VV p" "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p W"
  shows "v \<in> attractor p W"
proof (rule ccontr)
  assume *: "v \<notin> attractor p W"
  hence "v \<in> V - attractor p W" using assms(1) by blast
  moreover have "v \<notin> VV p**" using assms(1) by auto
  moreover have "\<not>deadend v" using assms(2) using valid_edge_set by auto
  ultimately have "v \<in> directly_attracted p (attractor p W)"
    unfolding directly_attracted_def using assms(2) by blast
  thus False using * attractor_unfolding by auto
qed

lemma attractor_set_VVpstar:
  assumes "v \<in> VV p**" "\<not>deadend v" "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p W"
  shows "v \<in> attractor p W"
proof (rule ccontr)
  assume *: "v \<notin> attractor p W"
  hence "v \<in> V - attractor p W" using assms(1) by blast
  moreover have "v \<notin> VV p" using assms(1) by auto
  ultimately have "v \<in> directly_attracted p (attractor p W)"
    unfolding directly_attracted_def using assms(2) assms(3) by blast
  thus False using * attractor_unfolding by auto
qed

lemma attractor_is_bounded_by_V: "W \<subseteq> V \<Longrightarrow> attractor p W \<subseteq> V"
  using attractor_lowerbound attractor_step_bounded_by_V by auto
lemma attractor_outside: "\<lbrakk> v \<notin> attractor p W; v \<in> VV p; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<notin> attractor p W"
  using attractor_set_VVp by blast

(* attractor_inductive *)

(* Show that the inductive definition and the definition via lfp are the same. *)
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

lemma attractor_is_superset [simp]: "W \<subseteq> attractor_inductive p W" by blast
lemma attractor_inductive_outside: "\<lbrakk> v \<notin> attractor_inductive p W; v \<in> VV p; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<notin> attractor_inductive p W"
  by (metis attractor_inductive.VVp)

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

lemma attractor_contains_no_deadends: "\<lbrakk> W \<subseteq> V; v \<in> attractor p W \<rbrakk> \<Longrightarrow> v \<in> W \<or> \<not>deadend v"
  using attractor_inductive_contains_no_deadends attractor_inductive_is_attractor by auto

end -- "context ParityGame"

(* ML_val {*
(*proof body with digest*)
val body = Proofterm.strip_thm (Thm.proof_body_of @{thm llist_set_nth});
(*proof term only*)
val prf = Proofterm.proof_of body;
Pretty.writeln (Proof_Syntax.pretty_proof @{context} prf);
(*all theorems used in the graph of nested proofs*)
val all_thms =
Proofterm.fold_body_thms
(fn (name, _, _) => insert (op =) name) [body] [];
*} *)

end
