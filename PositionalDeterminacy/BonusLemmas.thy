theory BonusLemmas
imports
  Main
  Attractor
begin

context ParityGame begin

subsection {* @{term attractor_inductive} *}

text {* The attractor set of a given set of vertices, defined inductively. *}
inductive_set attractor_inductive :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for p :: Player and W :: "'a set" where
  Base [intro!]: "v \<in> W \<Longrightarrow> v \<in> attractor_inductive p W" |
  VVp: "v \<in> VV p \<Longrightarrow> \<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor_inductive p W" |
  VVpstar: "\<not>deadend v \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor_inductive p W \<Longrightarrow> v \<in> attractor_inductive p W"

text {*
  We show that the inductive definition and the definition via least fixed point are the same.
*}
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
    from `W \<subseteq> V` have "P (attractor p W)" proof (induct rule: attractor_set_induction)
      case (step S)
      hence "S \<subseteq> attractor_inductive p W" using P_def by simp
      have "W \<union> S \<union> directly_attracted p S \<subseteq> attractor_inductive p W" proof
        fix v assume "v \<in> W \<union> S \<union> directly_attracted p S"
        moreover
        { assume "v \<in> W" hence "v \<in> attractor_inductive p W" by blast }
        moreover
        { assume "v \<in> S" hence "v \<in> attractor_inductive p W"
            by (meson `S \<subseteq> attractor_inductive p W` set_rev_mp) }
        moreover
        { assume v_attracted: "v \<in> directly_attracted p S"
          hence "v \<in> V" using `S \<subseteq> V` attractor_step_bounded_by_V by blast
          hence "v \<in> attractor_inductive p W" proof (cases rule: VV_cases)
            assume "v \<in> VV p"
            hence "\<exists>w. v\<rightarrow>w \<and> w \<in> S" using v_attracted directly_attracted_def by blast
            hence "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W"
              using `S \<subseteq> attractor_inductive p W` by blast
            thus ?thesis by (simp add: `v \<in> VV p` attractor_inductive.VVp)
          next
            assume "v \<in> VV p**"
            hence *: "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> S" using v_attracted directly_attracted_def by blast
            have "\<not>deadend v" using v_attracted directly_attracted_def by blast
            show ?thesis proof (rule ccontr)
              assume "v \<notin> attractor_inductive p W"
              hence "\<exists>w. v\<rightarrow>w \<and> w \<notin> attractor_inductive p W"
                by (metis attractor_inductive.VVpstar `v \<in> VV p**` `\<not>deadend v`)
              hence "\<exists>w. v\<rightarrow>w \<and> w \<notin> S" using `S \<subseteq> attractor_inductive p W` by (meson subsetCE)
              thus False using * by blast
            qed
          qed
        }
        ultimately show "v \<in> attractor_inductive p W" by (meson UnE)
      qed
      thus "P (W \<union> S \<union> directly_attracted p S)" using P_def by simp
    next
      case (union M) thus ?case by (simp add: P_def Sup_least)
    qed
    thus ?thesis using P_def by simp
  qed
qed

end

end
