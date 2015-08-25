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

lemma strategy_attracts_VVp:
  assumes "W \<subseteq> V" "S \<subseteq> V"
    and \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 S W"
    and v: "v0 \<in> S - W" "v0 \<in> VV p"
  shows "\<sigma> v0 \<in> S \<union> W"
proof-
  show ?thesis sorry
qed

lemma strategy_attracts_not_outside:
  assumes "v0 \<in> V - S - W" "strategy p \<sigma>"
  shows "\<not>strategy_attracts_via p \<sigma> v0 S W"
proof-
  {
    obtain P where P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
      using assms strategy_conforming_path_exists_single by blast
    {
      fix n assume n: "enat n < llength P" "P $ n \<in> W"
      hence "n \<noteq> 0" using assms(1) DiffD2 P(5) by force
      moreover have "lhd P \<notin> S" using assms(1) P(5) by (simp add: P(1) lhd_conv_lnth)
      ultimately have "lhd (ltake (enat n) P) \<notin> S" "\<not>lnull (ltake (enat n) P)" by (simp_all add: P(1) enat_0_iff(1))
      hence "\<not>lset (ltake (enat n) P) \<subseteq> S" using llist.set_sel(1) by blast
    }
    with P have "\<exists>P. \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0 \<and> (\<forall>n. enat n < llength P \<and> P $ n \<in> W \<longrightarrow> \<not>lset (ltake (enat n) P) \<subseteq> S)" by blast
  }
  thus ?thesis unfolding strategy_attracts_via_def by blast
qed

lemma strategy_attracts_VVpstar:
  assumes "W \<subseteq> V" "S \<subseteq> V"
    and \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 S W"
    and v: "v0 \<in> S - W" "v0 \<notin> VV p" and w: "w0 \<in> V - S - W"
  shows "\<not>v0 \<rightarrow> w0"
  by (metis assms(3) assms(4) strategy_attracts_not_outside strategy_attracts_via_successor v(1) v(2) w)

(* attractor_strategy_on *)

lemma merge_attractor_strategies:
  fixes W p S
  assumes "W \<subseteq> V" "S \<subseteq> V"
    and "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
proof-
  let ?good = "\<lambda>v. { \<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W }"
  def G \<equiv> "{ \<sigma>. \<exists>v \<in> S. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W }"
  obtain r where r: "well_order_on G r" using well_order_on by blast
  hence wf: "wf (r - Id)" using well_order_on_def by blast

  def [simp]: choose' \<equiv> "\<lambda>v \<sigma>. \<sigma> \<in> ?good v \<and> (\<forall>\<sigma>'. (\<sigma>', \<sigma>) \<in> r - Id \<longrightarrow> \<sigma>' \<notin> ?good v)"
  def [simp]: choose \<equiv> "\<lambda>v. THE \<sigma>. choose' v \<sigma>"
  def \<sigma> \<equiv> "override_on \<sigma>_arbitrary (\<lambda>v. choose v v) (S - W)"

  { fix v assume "v \<in> S"
    hence "\<exists>\<sigma>. \<sigma> \<in> ?good v" using assms(3) by blast
    then obtain \<sigma> where \<sigma>: "choose' v \<sigma>" unfolding choose'_def by (meson local.wf wf_eq_minimal)
    { fix \<sigma>' assume \<sigma>': "choose' v \<sigma>'"
      have "(\<sigma>, \<sigma>') \<notin> r - Id" using \<sigma> \<sigma>' by auto
      moreover have "(\<sigma>', \<sigma>) \<notin> r - Id" using \<sigma> \<sigma>' by auto
      moreover have "\<sigma> \<in> G" using G_def \<sigma>(1) `v \<in> S` by auto
      moreover have "\<sigma>' \<in> G" using G_def \<sigma>'(1) `v \<in> S` by auto
      ultimately have "\<sigma>' = \<sigma>" using r Linear_order_in_diff_Id well_order_on_Field well_order_on_def by fastforce
    }
    with \<sigma> have "\<exists>!\<sigma>. choose' v \<sigma>" by blast
    hence "choose' v (choose v)" using theI'[of "choose' v"] choose_def by fastforce
  } note choose_works = this

  have \<sigma>_valid: "strategy p \<sigma>" proof-
    {
      fix v assume *: "v \<in> S" "v \<in> VV p" "\<not>deadend v"
      from `v \<in> S` have "strategy p (choose v)" using choose_works choose'_def by blast
      with * have "v\<rightarrow>(\<lambda>v. choose v v) v" using strategy_def by blast
    }
    thus ?thesis using valid_strategy_updates_set \<sigma>_def by force
  qed

  have S_W_no_deadends: "\<And>v. v \<in> S - W \<Longrightarrow> \<not>deadend v" proof (rule ccontr, subst (asm) not_not)
    fix v assume "v \<in> S - W" "deadend v"
    def [simp]: P \<equiv> "LCons v LNil"
    obtain \<sigma>' where \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' v S W" using `v \<in> S - W` assms(3) by auto
    moreover have "\<not>lnull P \<and> P $ 0 = v" by simp
    moreover have "valid_path P" using `v \<in> S - W` assms(2) valid_path_base' by auto
    moreover have "maximal_path P" using `deadend v` by (simp add: maximal_path.intros(2))
    moreover have "path_conforms_with_strategy p P \<sigma>'" by (simp add: path_conforms_LCons_LNil)
    ultimately have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> S"
      using \<sigma>'(2) unfolding strategy_attracts_via_def by blast
    moreover have "llength P = eSuc 0" by simp
    ultimately have "P $ 0 \<in> W" by (simp add: enat_0_iff(1))
    with `v \<in> S - W` show False by auto
  qed

  {
    fix v0 assume "v0 \<in> S"
    fix P assume "\<not>lnull P"
      and P_valid: "valid_path P"
      and P_maximal: "maximal_path P"
      and P_conforms: "path_conforms_with_strategy p P \<sigma>"
      and P_valid_start: "P $ 0 = v0"
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> S" proof (rule ccontr)
      assume "\<not>?thesis"
      hence contra: "\<And>n. enat n < llength P \<Longrightarrow> P $ n \<in> W \<Longrightarrow> \<not>lset (ltake (enat n) P) \<subseteq> S" by blast
      have "lset P \<subseteq> S - W" proof (rule ccontr)
        assume "\<not>lset P \<subseteq> S - W"
        hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> S - W" by (meson lset_subset)
        then obtain n where n: "enat n < llength P" "P $ n \<notin> S - W" "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> S - W)"
          using obtain_min[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> S - W"] by metis
        from n(1) n(3) have "\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W" using dual_order.strict_trans enat_ord_simps(2) by blast
        hence "lset (ltake (enat n) P) \<subseteq> S - W" using lset_ltake by blast
        hence "P $ n \<notin> W" using contra n(1) by blast
        moreover have "P $ n \<notin> V - S - W" proof (rule ccontr, subst (asm) not_not)
          assume "P $ n \<in> V - S - W"
          hence "n \<noteq> 0" using P_valid_start `v0 \<in> S` n(2) by force
          then obtain n' where n': "Suc n' = n" by (metis nat.exhaust)
          hence "P $ n' \<in> S - W" using `\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W` by blast
          def [simp]: P' \<equiv> "ldropn n' P"
          def [simp]: \<sigma>' \<equiv> "choose (P $ n')"
          hence \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' (P $ n') S W"
            using `P $ n' \<in> S - W` choose_works unfolding choose'_def by blast+
          have "enat n' < llength P" using n(1) n' using dual_order.strict_trans enat_ord_simps(2) by blast
          show False proof (cases)
            assume "P $ n' \<in> VV p"
            hence "\<sigma> (P $ n') \<in> S \<union> W" using \<sigma>'(1) \<sigma>'(2) \<sigma>_def `P $ n' \<in> S - W` assms(1) assms(2) strategy_attracts_VVp by auto
            moreover have "\<sigma> (P $ n') = P $ n" proof-
              have "enat (Suc n') < llength P" using n' n(1) by simp
              hence "\<sigma> (P $ n') = P $ Suc n'" using P_conforms P_valid `P $ n' \<in> VV p` path_conforms_with_strategy_conforms by blast
              thus ?thesis using n' by simp
            qed
            ultimately show False using `P $ n \<in> V - S - W` by auto
          next
            assume "P $ n' \<notin> VV p"
            hence "\<not>(P $ n')\<rightarrow>(P $ n)" using strategy_attracts_VVpstar \<sigma>'(1) \<sigma>'(2) `P $ n \<in> V - S - W` `P $ n' \<in> S - W` assms(1) assms(2) by blast
            hence "\<not>(P $ n')\<rightarrow>(P $ Suc n')" using n' by simp
            moreover have "enat (Suc n') < llength P" using n' n(1) by simp
            ultimately show False using P_valid `enat n' < llength P` valid_path_impl1 by blast
          qed
        qed
        moreover have "P $ n \<in> V" using n(1) P_valid valid_path_finite_in_V' by blast
        ultimately show False using n(2) by blast
      qed
      have "\<not>lfinite P" proof (rule ccontr, subst (asm) not_not)
        assume "lfinite P"
        hence "deadend (llast P)" using P_maximal `\<not>lnull P` maximal_ends_on_deadend by blast
        moreover have "llast P \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lnull P` `lfinite P` lfinite_lset by blast
        ultimately show False using S_W_no_deadends by blast
      qed
      have P_no_deadends: "\<And>n. \<not>deadend (P $ n)"
        using `\<not>lfinite P` S_W_no_deadends `lset P \<subseteq> S - W` llist_nth_set by fastforce
      show False proof (cases "\<exists>n. lset (ldropn n P) \<subseteq> VV p**")
        case True
        then obtain n where n: "lset (ldropn n P) \<subseteq> VV p**" by blast
        def [simp]: P' \<equiv> "ldropn n P"
        have "lset P' \<subseteq> S - W" using `lset P \<subseteq> S - W` P'_def lset_ldropn_subset by force
        moreover have "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
        ultimately have "P' $ 0 \<in> S" by (metis Diff_subset P'_def `\<not>lfinite P` lfinite_ldropn llist_set_nth subset_trans)
        then obtain \<sigma>' where \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' (P' $ 0) S W" using assms(3) by blast
        moreover have "valid_path P'" using P_valid by (simp add: valid_path_drop)
        moreover have "maximal_path P'" using P_maximal by (simp add: maximal_drop)
        moreover have "path_conforms_with_strategy p P' \<sigma>'" using n path_conforms_with_strategy_VVpstar by simp
        ultimately obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> S"
          unfolding strategy_attracts_via_def using `\<not>lnull P'` by blast
        thus False by (meson Diff_iff `lset P' \<subseteq> S - W` lset_lnth)
      next
        case False
        have always_again_in_VVp: "\<And>n. \<exists>m. n \<le> m \<and> P $ m \<in> VV p" proof-
          fix n
          have "\<not>lset (ldropn n P) \<subseteq> VV p**" using False by blast
          then obtain m where m: "ldropn n P $ m \<notin> VV p**" using lset_subset[of "ldropn n P" "VV p**"] by blast
          hence "ldropn n P $ m \<in> VV p" using P_valid VV_cases `\<not>lfinite P` lfinite_ldropn valid_path_drop valid_path_in_V' by blast
          hence "P $ m + n \<in> VV p" using lnth_ldropn `\<not>lfinite P` by (simp add: infinite_small_llength)
          thus "\<exists>m. n \<le> m \<and> P $ m \<in> VV p" using le_add2 by blast
        qed
        def [simp]: \<sigma>_map \<equiv> "\<lambda>n. choose (P $ n)"
        have "\<And>n. P $ n \<in> S" using `lset P \<subseteq> S - W` `\<not>lfinite P` llist_set_nth by blast
        {
          fix n
          let ?v = "P $ n"
          have "choose' ?v (\<sigma>_map n)" using choose_works[of ?v] `\<And>n. P $ n \<in> S` unfolding \<sigma>_map_def by blast
          hence "strategy p (\<sigma>_map n) \<and> strategy_attracts_via p (\<sigma>_map n) ?v S W" unfolding choose'_def by blast
        } note \<sigma>_map_choose' = this
        hence \<sigma>_map_in_G: "\<And>n. \<sigma>_map n \<in> G" unfolding G_def using `\<And>n. P $ n \<in> S` by blast
        have \<sigma>_map_monotone: "\<And>n m. n < m \<Longrightarrow> (\<sigma>_map m, \<sigma>_map n) \<in> r" proof-
          {
            fix n
            have "(\<sigma>_map (Suc n), \<sigma>_map n) \<in> r" proof-
              have "strategy p (\<sigma>_map n)" using \<sigma>_map_choose' by blast
              moreover have *: "P $ n \<in> VV p \<Longrightarrow> \<sigma>_map n (P $ n) = P $ Suc n" proof-
                assume "P $ n \<in> VV p"
                hence "\<sigma> (P $ n) = P $ Suc n" using P_conforms P_valid path_conforms_with_strategy_conforms infinite_small_llength `\<not>lfinite P` by fastforce
                moreover have "\<sigma> (P $ n) = \<sigma>_map n (P $ n)" proof-
                  have "P $ n \<in> S - W" using `\<not>lfinite P` `lset P \<subseteq> S - W` llist_set_nth by blast
                  thus ?thesis by (simp add: \<sigma>_def)
                qed
                ultimately show "\<sigma>_map n (P $ n) = P $ Suc n" by simp
              qed
              moreover have "P $ n \<in> S - W" using `\<not>lfinite P` `lset P \<subseteq> S - W` llist_set_nth by blast
              moreover have "P $ n \<rightarrow> P $ Suc n" using P_valid `\<not>lfinite P` infinite_small_llength valid_path_edges by blast
              moreover have "strategy_attracts_via p (\<sigma>_map n) (P $ n) S W" using \<sigma>_map_choose' by blast
              ultimately have "strategy_attracts_via p (\<sigma>_map n) (P $ Suc n) S W" using strategy_attracts_via_successor[of p "\<sigma>_map n" "P $ n" S W "P $ Suc n"] \<sigma>_def `strategy p (\<sigma>_map n)` by force
              hence "\<sigma>_map n \<in> ?good (P $ Suc n)" using `strategy p (\<sigma>_map n)` by blast
              hence *: "(\<sigma>_map n, choose (P $ Suc n)) \<notin> r - Id" using `\<And>n. P $ n \<in> S` choose'_def choose_works by blast
              have "(choose (P $ Suc n), \<sigma>_map n) \<in> r" proof (cases)
                assume "\<sigma>_map n = choose (P $ Suc n)"
                moreover have "refl_on G r" using r unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by blast
                ultimately show ?thesis using \<sigma>_map_in_G refl_onD by fastforce
              next
                assume "\<sigma>_map n \<noteq> choose (P $ Suc n)"
                moreover with * have "(\<sigma>_map n, choose (P $ Suc n)) \<notin> r" by blast
                moreover have "total_on G r" using r unfolding well_order_on_def linear_order_on_def by blast
                ultimately show ?thesis by (metis \<sigma>_map_def \<sigma>_map_in_G total_on_def)
              qed
              thus ?thesis unfolding \<sigma>_map_def by blast
            qed
          } note case_Suc' = this
          {
            fix n m assume "(\<sigma>_map m, \<sigma>_map n) \<in> r"
            moreover have "(\<sigma>_map (Suc m), \<sigma>_map m) \<in> r" using case_Suc' by blast
            moreover have "trans r" using r unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by blast
            ultimately have "(\<sigma>_map (Suc m), \<sigma>_map n) \<in> r" by (meson transE)
          } note case_Suc = this

          fix n m :: nat assume "n < m"
          thus "(\<sigma>_map m, \<sigma>_map n) \<in> r" proof (induct "m - n" arbitrary: n m)
            case 0 thus ?case by simp
          next
            case (Suc d)
            show ?case proof (cases)
              assume "d = 0"
              thus ?thesis using case_Suc' by (metis Suc.hyps(2) Suc.prems Suc_diff_Suc Suc_inject Suc_leI diff_is_0_eq diffs0_imp_equal)
            next
              assume "d \<noteq> 0"
              have "m \<noteq> 0" using Suc.hyps(2) by linarith
              then obtain m' where m': "Suc m' = m" by (metis nat.exhaust)
              hence "d = m' - n" using Suc.hyps(2) by linarith
              hence "(\<sigma>_map m', \<sigma>_map n) \<in> r" using Suc.hyps(1) `d \<noteq> 0` zero_less_diff by blast
              thus ?thesis using m' case_Suc by blast
            qed
          qed
        qed
        def [simp]: \<sigma>_set \<equiv> "\<sigma>_map ` UNIV"
        have "\<exists>\<sigma>. \<sigma> \<in> \<sigma>_set" using \<sigma>_set_def by blast
        then obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> \<sigma>_set" "\<And>\<tau>. (\<tau>, \<sigma>') \<in> r - Id \<Longrightarrow> \<tau> \<notin> \<sigma>_set" using wfE_min[of "r - Id" _ \<sigma>_set] wf by blast
        then obtain n where n: "\<sigma>_map n = \<sigma>'" by auto
        have \<sigma>_map_constant: "\<And>m. n \<le> m \<Longrightarrow> \<sigma>_map n = \<sigma>_map m" proof-
          fix m assume "n \<le> m"
          show "\<sigma>_map n = \<sigma>_map m" proof (rule ccontr)
            assume *: "\<sigma>_map n \<noteq> \<sigma>_map m"
            with `n \<le> m` have "n < m" using le_imp_less_or_eq by blast
            with \<sigma>_map_monotone have "(\<sigma>_map m, \<sigma>_map n) \<in> r" by blast
            with * have "(\<sigma>_map m, \<sigma>_map n) \<in> r - Id" by simp
            with \<sigma>'(2) n have "\<sigma>_map m \<notin> \<sigma>_set" by blast
            thus False unfolding \<sigma>_set_def by blast
          qed
        qed
        def [simp]: P' \<equiv> "ldropn n P"
        have "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
        moreover have "valid_path P'" using P_valid by (simp add: valid_path_drop)
        moreover have "maximal_path P'" using P_maximal by (simp add: maximal_drop)
        moreover have "path_conforms_with_strategy p P' \<sigma>'" proof-
          have "\<And>v. v \<in> lset P' \<Longrightarrow> \<sigma> v = \<sigma>' v" proof-
            fix v assume "v \<in> lset P'"
            hence "v \<in> S - W" using `lset P \<subseteq> S - W` by (metis P'_def contra_subsetD in_lset_ldropnD)
            from `v \<in> lset P'` obtain m where m: "enat m < llength P'" "P' $ m = v" by (meson in_lset_conv_lnth)
            hence "P $ m + n = P' $ m" unfolding P'_def by (simp add: `\<not>lfinite P` infinite_small_llength)
            moreover have "\<sigma> v = choose v v" unfolding \<sigma>_def using `v \<in> S - W` by auto
            ultimately have "\<sigma> v = \<sigma>_map (m + n) v" unfolding \<sigma>_map_def using m(2) by auto
            thus "\<sigma> v = \<sigma>' v" using n \<sigma>_map_constant[of "m + n"] by simp
          qed
          moreover have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def by (simp add: P_conforms path_conforms_with_strategy_drop)
          ultimately show ?thesis using path_conforms_with_strategy_irrelevant_updates by blast
        qed
        moreover have "strategy p \<sigma>'" unfolding \<sigma>_set_def using \<sigma>'(1) G_def \<sigma>_map_in_G by auto
        moreover have "strategy_attracts_via p \<sigma>' (P' $ 0) S W" proof-
          have "P $ n \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lfinite P` llist_set_nth by blast
          hence "choose' (P $ n) (choose (P $ n))" using choose_works by blast
          hence "strategy_attracts_via p \<sigma>' (P $ n) S W" unfolding choose'_def using n \<sigma>_map_def by blast
          moreover have "P $ n = P' $ 0" unfolding P'_def by (simp add: `\<not>lfinite P` infinite_small_llength)
          ultimately show ?thesis by simp
        qed
        ultimately obtain m where m: "enat m < llength P'" "P' $ m \<in> W"
          unfolding strategy_attracts_via_def using `\<not>lnull P'` by blast
        moreover from `lset P \<subseteq> S - W` have "lset P' \<subseteq> S - W" using lset_ldropn_subset by fastforce
        ultimately show False by (meson Diff_iff lset_lnth)
      qed
    qed
  }
  hence "strategy_attracts p \<sigma> S W" using strategy_attracts_def strategy_attracts_via_def by auto
  thus ?thesis using \<sigma>_valid by auto
qed

lemma strategy_attracts_extends_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> S W"
    and v0: "v0 \<in> VV p" "v0 \<in> directly_attracted p S" "v0 \<notin> S"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
proof-
  from v0(1) v0(2) obtain w where "v0\<rightarrow>w" "w \<in> S" using directly_attracted_def by blast
  hence "\<not>deadend v0" using edges_are_in_V by blast
  from `w \<in> S` \<sigma>(2) have "strategy_attracts_via p \<sigma> w S W" unfolding strategy_attracts_def by blast
  let ?\<sigma> = "\<sigma>(v0 := w)" (* Extend \<sigma> to the new node. *)
  have "strategy p ?\<sigma>" using \<sigma>(1) `v0\<rightarrow>w` valid_strategy_updates by blast
  moreover have "strategy_attracts_via p ?\<sigma> v0 (insert v0 S) W" proof-
    { fix P
      assume P: "\<not>lnull P" "valid_path P" "maximal_path P"
        "path_conforms_with_strategy p P ?\<sigma>" "P $ 0 = v0"

      def [simp]: P'' \<equiv> "ltl P"
      have "\<not>lnull P''" proof-
        from P(1) have "enat 0 < llength P" using lnull_0_llength by blast
        moreover from P(5) `\<not>deadend v0` have "\<not>deadend (P $ 0)" by blast
        ultimately have "enat (Suc 0) < llength P" using P(3) maximal_path_impl1 by blast
        hence "enat 0 < llength P''" using enat_Suc_ltl P''_def by blast
        then show "\<not>lnull P''" by auto
      qed
      have "P'' $ 0 = w" proof-
        from P(1) P(5) have "P = LCons v0 P''" by (metis P''_def lnth_0 ltl_simps(2) not_lnull_conv)
        with P(4) `v0 \<in> VV p` `\<not>lnull P''` have "lhd P'' = ?\<sigma> v0" by (metis lhd_LCons_ltl path_conforms_with_strategy_start)
        thus "P'' $ 0 = w" using `\<not> lnull P''` lhd_conv_lnth by force
      qed
      from P(2) P(3) P(4) have P'': "valid_path P''" "maximal_path P''" "path_conforms_with_strategy p P'' ?\<sigma>"
        using valid_path_ltl maximal_ltl path_conforms_with_strategy_ltl by auto

      have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S" proof (cases)
        assume "v0 \<in> lset P'' \<and> ?\<sigma> v0 \<noteq> \<sigma> v0"

        with \<sigma>(1) `strategy p ?\<sigma>` `v0 \<in> VV p` P'' `\<not>lnull P''` `\<not>deadend v0`
          obtain P' n where
            P': "\<not>lnull P'" "valid_path P'" "maximal_path P'" "path_conforms_with_strategy p P' \<sigma>"
            and n_valid: "enat (Suc n) < llength P'" "enat (Suc n) < llength P''"
            and P'_P''_same_prefix: "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P''"
            and P''_n: "P'' $ n \<in> VV p" "\<not>deadend (P'' $ n)" "?\<sigma> (P'' $ n) \<noteq> \<sigma> (P'' $ n)"
          using path_conforms_with_strategy_update_path by blast

        from P''_n(3) have "P'' $ n = v0" by (meson fun_upd_apply)
        from `P'' $ 0 = w` P'_P''_same_prefix have "P' $ 0 = w" using ltake_lnth[of "enat (Suc n)" P' P'' 0] by simp

        with P' `strategy_attracts_via p \<sigma> w S W`
          obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> S"
          unfolding strategy_attracts_via_def by blast

        have "m \<le> n" proof (rule ccontr)
          assume "\<not>m \<le> n"
          hence "Suc n \<le> m" by presburger
          hence "enat (Suc n) \<le> enat m" by simp
          with m(3) have "lset (ltake (enat (Suc n)) P') \<subseteq> S" by (meson lprefix_lset' order_trans)
          with P'_P''_same_prefix have *: "lset (ltake (enat (Suc n)) P'') \<subseteq> S" by simp
          with n_valid(2) have "enat n < llength P''" using Suc_ile_eq le_less by blast
          hence "enat n < llength (ltake (enat (Suc n)) P'')" by simp
          with * have "P'' $ n \<in> S"
            using lset_lnth[of "ltake (enat (Suc n)) P''" S n]
            by (metis (no_types) lprefix_lnthD ltake_is_lprefix)
          with `P'' $ n = v0` `v0 \<notin> S` show False by blast
        qed
        with P'_P''_same_prefix have "P' $ m = P'' $ m" using ltake_lnth[of "enat (Suc n)" P' P'' m] by simp
        with m(2) have "P'' $ m \<in> W" by simp
        hence 1: "P $ Suc m \<in> W" by (simp add: P(1) lnth_ltl)

        from P'_P''_same_prefix `m \<le> n` m(3)
          have "lset (ltake (enat m) P'') \<subseteq> S"
          using ltake_eq_ltake_antimono by fastforce
        hence "lset (ltake (eSuc (enat m)) P) \<subseteq> insert v0 S"
          by (metis P''_def P(1) P(5) lnth_0 ltl_simps(2) lset_ltake_Suc not_lnull_conv)
        hence 2: "lset (ltake (enat (Suc m)) P) \<subseteq> insert v0 S" by (simp add: eSuc_enat)

        from `m \<le> n` n_valid(2) have "enat (Suc m) < llength P''"
          by (metis Suc_ile_eq dual_order.strict_iff_order dual_order.strict_trans enat_ord_simps(2))
        hence 3: "enat (Suc m) < llength P" using dual_order.strict_trans enat_ltl_Suc by force

        with 1 2 3 show "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S" by blast
      next
        assume "\<not>(v0 \<in> lset P'' \<and> ?\<sigma> v0 \<noteq> \<sigma> v0)"
        with P''(3)
          have "path_conforms_with_strategy p P'' \<sigma>"
          using path_conforms_with_strategy_irrelevant'[of p P'' \<sigma> v0 w] by auto
        with P'' `strategy_attracts_via p \<sigma> w S W` `P'' $ 0 = w` `\<not>lnull P''`
          have "\<exists>n. enat n < llength P'' \<and> P'' $ n \<in> W \<and> lset (ltake (enat n) P'') \<subseteq> S"
          unfolding strategy_attracts_via_def by auto
        with P(1) P(5)
          show ?thesis
          unfolding P''_def using lset_ltake_Suc' enat_ltl_Suc lnth_ltl by metis
      qed
    }
    thus ?thesis unfolding strategy_attracts_via_def by blast
  qed
  ultimately show ?thesis by blast
qed

lemma strategy_attracts_extends_VVpstar:
  assumes \<sigma>: "strategy_attracts p \<sigma> S W"
    and v0: "v0 \<notin> VV p" "v0 \<in> directly_attracted p S"
  shows "strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
proof-
  from v0(2) have "\<not>deadend v0" using directly_attracted_contains_no_deadends by blast
  from v0 have "\<forall>w. v0\<rightarrow>w \<longrightarrow> w \<in> S" by (simp add: directly_attracted_def)
  { fix P
    assume P: "\<not>lnull P" "valid_path P" "maximal_path P"
      "path_conforms_with_strategy p P \<sigma>" "P $ 0 = v0"
    def [simp]: P' \<equiv> "ltl P"
    from P(2) P(3) P(4) have ltl_P: "valid_path P'" "maximal_path P'" "path_conforms_with_strategy p P' \<sigma>"
      using valid_path_ltl maximal_ltl path_conforms_with_strategy_ltl by auto
    moreover have "\<not>lnull P'" proof-
      from P(1) have "enat 0 < llength P" using lnull_0_llength by blast
      moreover from P(5) `\<not>deadend v0` have "\<not>deadend (P $ 0)" by blast
      ultimately have "enat (Suc 0) < llength P" using P(3) maximal_path_impl1 by blast
      hence "enat 0 < llength P'" using enat_Suc_ltl P'_def by blast
      thus ?thesis by auto
    qed
    moreover have "P' $ 0 \<in> S" proof-
      from `\<not>lnull P'` ltl_P P(1) P(2) have "P $ 0 \<rightarrow> P' $ 0" by (metis P'_def lhd_LCons_ltl lnth_0_conv_lhd valid_path_edges')
      with P(5) `\<forall>w. v0\<rightarrow>w \<longrightarrow> w \<in> S` show ?thesis by blast
    qed
    ultimately have "\<exists>n. enat n < llength P' \<and> P' $ n \<in> W \<and> lset (ltake (enat n) P') \<subseteq> S"
      using \<sigma> unfolding strategy_attracts_def strategy_attracts_via_def by blast
    with P(1) P(5) have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> insert v0 S"
      unfolding P'_def using lset_ltake_Suc' enat_ltl_Suc lnth_ltl by metis
  }
  thus ?thesis unfolding strategy_attracts_via_def by blast
qed

theorem attractor_has_strategy_single:
  assumes "W \<subseteq> V"
    and v0_def: "v0 \<in> attractor p W" (is "_ \<in> ?A")
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 ?A W"
using v0_def proof (induct arbitrary: v0 rule: attractor_set_induction)
  case base thus ?case using `W \<subseteq> V` .
next
  case (step S)
  have "v0 \<in> W \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 {} W"
    using strategy_attracts_via_trivial valid_arbitrary_strategy by blast
  moreover {
    assume *: "v0 \<in> directly_attracted p S" "v0 \<notin> S"
    from assms(1) step.hyps(1) step.hyps(2)
      have "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
      using merge_attractor_strategies by auto
    with *
      have "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
      using strategy_attracts_extends_VVp strategy_attracts_extends_VVpstar by blast
  }
  ultimately show ?case
    using step.prems step.hyps(2)
    attractor_strategy_on_extends[of p _ v0 "insert v0 S" W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "S" W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "{}" W "W \<union> S \<union> directly_attracted p S"]
    by blast
next
  case (union M)
  hence "\<exists>S. S \<in> M \<and> v0 \<in> S" by blast
  thus ?case by (meson Union_upper attractor_strategy_on_extends union.hyps)
qed

corollary attractor_has_strategy:
  assumes "W \<subseteq> V"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> (attractor p W) W"
proof-
  let ?A = "attractor p W"
  from `W \<subseteq> V`
    have "?A \<subseteq> V"
    by (simp add: attractor_is_bounded_by_V)
  moreover from `W \<subseteq> V`
    have "\<And>v. v \<in> ?A \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v ?A W"
    using attractor_has_strategy_single by blast
  ultimately show ?thesis using merge_attractor_strategies `W \<subseteq> V` by blast
qed

(* If A is the p-attractor of a set W, then p** has a strategy on V - A avoiding A. *)
theorem attractor_has_outside_strategy:
  fixes W p
  defines "A \<equiv> attractor p** W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_avoids p \<sigma> (V - A) A"
proof (intro exI conjI)
  (*  \<sigma>' simply chooses an arbitrary node not in A as the successor. *)
  def \<sigma>' \<equiv> "\<lambda>v. SOME w. w \<notin> A \<and> v\<rightarrow>w"
  def \<sigma> \<equiv> "override_on \<sigma>_arbitrary \<sigma>' (V - A)"
  (* We need to show that \<sigma> is well-defined.  This means we have to show that \<sigma> always applies
  the SOME quantifier to a non-empty set (for the nodes that matter). *)
  {
    fix v assume v: "v \<in> V - A" "v \<in> VV p" "\<not>deadend v"
    have "\<exists>w. w \<notin> A \<and> v\<rightarrow>w" proof (rule ccontr)
      assume "\<not>(\<exists>w. w \<notin> A \<and> v\<rightarrow>w)"
      hence "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor p** W" using A_def by blast
      hence "v \<in> attractor p** W" using v A_def attractor_set_VVpstar by auto
      thus False using v A_def by blast
    qed
    with v(1) have "\<sigma>' v \<notin> A" "v\<rightarrow>\<sigma>' v" unfolding \<sigma>'_def using someI_ex[of "\<lambda>w. w \<notin> A \<and> v\<rightarrow>w"] by auto
  } note \<sigma>'_correct = this

  from \<sigma>'_correct(2)
    show "strategy p \<sigma>"
    unfolding \<sigma>_def using valid_strategy_updates_set valid_arbitrary_strategy by blast

  show "strategy_avoids p \<sigma> (V - A) A" proof (cases "V - A = {}", simp del: Diff_eq_empty_iff)
    case False
    {
      fix P v
      have "v \<in> lset P \<Longrightarrow> \<not>lnull P \<and> valid_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 \<in> V - A \<longrightarrow> v \<notin> A"
      proof (induct rule: llist_set_induct, simp add: lnth_0_conv_lhd)
        case (step P w)
        show ?case proof (intro impI, elim conjE, cases "lnull (ltl P)")
          case True
          thus "w \<notin> A" using lset_lnull step.hyps(2) by fastforce
        next
          case False
          assume P: "valid_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 \<in> V - A"
          from `\<not>lnull (ltl P)` obtain v u P' where u: "P = LCons v (LCons u P')" by (metis lhd_LCons_ltl step.hyps(1))
          with P(1) have "\<not>deadend v" using edges_are_in_V valid_path_edges' by blast
          from P(3) u have "v \<in> V - A" by simp
          have "u \<notin> A" proof (cases)
            assume "v \<in> VV p"
            with u P(2)
              have "path_conforms_with_strategy p (LCons v (LCons u P')) \<sigma>" by blast
            with `v \<in> VV p`
              have "\<sigma> v = u" using path_conforms_with_strategy_start by blast
            from `v \<in> VV p` `\<not>deadend v` `v \<in> V - A`
              have "\<sigma>' v \<notin> A" using \<sigma>'_correct(1) by blast
            with \<sigma>_def `\<sigma> v = u` `v \<in> V - A`  
              show "u \<notin> A" by auto
          next
            assume "v \<notin> VV p"
            { assume "u \<in> A"
              from `v \<notin> VV p` `v \<in> V - A`
                have "v \<in> VV p**" by auto
              moreover from `u \<in> A` u P(1)
                have "\<exists>w. v\<rightarrow>w \<and> w \<in> A" using valid_path_edges' by blast
              ultimately
                have "v \<in> directly_attracted p** A"
                using `\<not>deadend v` `v \<in> V - A` unfolding directly_attracted_def by auto
              with `v \<in> V - A` assms
                have False unfolding A_def using attractor_unfolding by fastforce
            }
            thus "u \<notin> A" by blast
          qed
          with P(1) u have "u \<in> V - A" by (metis DiffI in_mono llist.set_intros(1) ltl_simps(2) valid_path_in_V valid_path_ltl)
          with u have "ltl P $ 0 \<in> V - A" by simp
          with `\<not>lnull (ltl P)` P(1) P(2) step.hyps(3)
            show "w \<notin> A" using valid_path_ltl path_conforms_with_strategy_ltl by blast
        qed
      qed
    }
    thus ?thesis unfolding strategy_avoids_def by blast
  qed
qed

end -- "context ParityGame"

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

end
