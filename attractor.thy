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

(* attractor_strategy_on *)

lemma merge_attractor_strategies:
  fixes W p S
  assumes "W \<subseteq> V" "S \<subseteq> V"
    and "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
  sorry
(* proof-
  let ?good = "\<lambda>v. {\<sigma>. attractor_strategy_on p \<sigma> v S W}"
  def G \<equiv> "{ \<sigma>. \<exists>v \<in> S. attractor_strategy_on p \<sigma> v S W }"
  obtain r where r: "well_order_on G r" using well_order_on by blast
  hence wf: "wf (r - Id)" using well_order_on_def by blast

  def [simp]: choose' \<equiv> "\<lambda>v \<sigma>. \<sigma> \<in> ?good v \<and> (\<forall>\<sigma>'. (\<sigma>', \<sigma>) \<in> r - Id \<longrightarrow> \<sigma>' \<notin> ?good v)"
  def [simp]: choose \<equiv> "\<lambda>v. THE \<sigma>. choose' v \<sigma>"
  def \<sigma> \<equiv> "\<lambda>v. if v \<in> (S - W) \<inter> VV p
    then (choose v) v
    else None"

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
  
  have \<sigma>_valid: "valid_strategy p \<sigma>" proof (unfold valid_strategy_def, intro allI impI)
    fix v w assume "\<sigma> v = Some w"
    hence "v \<in> (S - W) \<inter> VV p" by (metis \<sigma>_def option.distinct(2))
    hence "valid_strategy p (choose v)" using choose_works choose'_def attractor_strategy_on_def by blast
    moreover have "(choose v) v = Some w" using \<sigma>_def `\<sigma> v = Some w` `v \<in> (S - W) \<inter> VV p` by auto
    ultimately show "v \<in> VV p \<and> v \<rightarrow> w" using valid_strategy_def by blast
  qed

  have S_W_no_deadends: "\<And>v. v \<in> S - W \<Longrightarrow> \<not>deadend v" proof (rule ccontr, subst (asm) not_not)
    fix v assume "v \<in> S - W" "deadend v"
    def [simp]: P \<equiv> "LCons v LNil"
    obtain \<sigma>' where \<sigma>': "valid_strategy p \<sigma>'" "strategy_attracts_to p \<sigma>' v W" using `v \<in> S - W` assms attractor_strategy_on_def by (metis Diff_iff)
    moreover have "valid_path P" using `v \<in> S - W` assms(2) valid_path_base' by auto
    moreover have "\<not>lnull P \<and> P $ 0 = v" by simp
    moreover have "path_conforms_with_strategy_maximally p P \<sigma>'" proof-
      have "llength P = eSuc 0" by simp
      hence *: "\<And>i. enat i < llength P \<Longrightarrow> i = 0" by (simp add: enat_0_iff(1))
      moreover from \<sigma>'(1) `deadend v` have "v \<in> VV p \<Longrightarrow> \<sigma>' v = None"
        using valid_strategy_none_on_deadends by blast
      ultimately have "path_conforms_with_strategy p P \<sigma>'"
        unfolding path_conforms_with_strategy_def by (metis `\<not>lnull P \<and> P $ 0 = v` option.distinct(1))
      with * `\<not>lnull P \<and> P $ 0 = v` `deadend v` show ?thesis
        unfolding path_conforms_with_strategy_maximally_def by blast
    qed
    ultimately have "lset P \<inter> W \<noteq> {}" unfolding strategy_attracts_to_def using strategy_less_eq_def by blast
    with `v \<in> S - W` show False by auto
  qed

  { fix v0 assume "v0 \<in> S"
    {
      { fix v assume v: "v \<in> (S - W) \<inter> VV p" "\<not>deadend v"
        from v(1) have "strategy_only_on p (choose v) (S - W)" using choose_works choose'_def attractor_strategy_on_def by blast
        moreover from v(1) have "\<sigma> v = choose v v" by (simp add: \<sigma>_def)
        ultimately have "\<exists>w. \<sigma> v = Some w" using strategy_only_on_def v(1) v(2) by auto
      }
      moreover have "\<And>v. v \<notin> (S - W) \<inter> VV p \<Longrightarrow> \<sigma> v = None" using \<sigma>_def by auto
      ultimately have "strategy_only_on p \<sigma> (S - W)" unfolding strategy_only_on_def by blast
    }
    moreover {
      fix P \<sigma>' assume \<sigma>': "valid_strategy p \<sigma>'" "strategy_less_eq \<sigma> \<sigma>'"
        and P: "valid_path P" "\<not>lnull P" "path_conforms_with_strategy_maximally p P \<sigma>'" "P $ 0 = v0"
      (* Towards a contradiction... *)
      assume "lset P \<inter> W = {}"

      have "\<not>lfinite P" sorry
      have "lset P \<subseteq> S - W" sorry
      have "lset P \<inter> W \<noteq> {}" proof (cases)
        assume "v0 \<in> S - W"
        show "lset P \<inter> W \<noteq> {}" proof (cases)
          assume "\<exists>n. lset (ldropn n P) \<subseteq> VV p**"
          then obtain n where n: "lset (ldropn n P) \<subseteq> VV p**" by blast
          def [simp]: P' \<equiv> "ldropn n P"
          from `\<not>lfinite P` have "\<not>lfinite P'" by simp
          from `\<not>lfinite P` have "\<not>lnull P'" using P'_def infinite_no_deadend lfinite_ldropn by blast
          with `lset P \<subseteq> S - W` `\<not>lfinite P'` have "P' $ 0 \<in> S - W" using llist_nth_set by fastforce
          with assms obtain \<sigma>'' where \<sigma>'': "attractor_strategy_on p \<sigma>'' (P' $ 0) S W" by blast
          have "path_conforms_with_strategy_maximally p P' \<sigma>''" proof-
            from n `\<not>lfinite P'` have "\<And>i. P' $ i \<in> VV p**" using P'_def llist_set_nth by blast
            hence "\<And>i. P' $ i \<notin> VV p" by auto
            hence "path_conforms_with_strategy p P' \<sigma>''" using path_conforms_with_strategy_def by blast
            with `\<not>lfinite P'` show ?thesis unfolding path_conforms_with_strategy_maximally_def using infinite_small_llength by blast
          qed
          moreover from P(1) have "valid_path P'" by (simp add: valid_path_drop)
          ultimately have "lset P' \<inter> W \<noteq> {}"
            using \<sigma>'' `\<not>lnull P'` strategy_less_eq_refl attractor_strategy_on_def strategy_attracts_to_def by blast
          thus ?thesis using in_lset_ldropnD by fastforce
        next
          assume "\<not>(\<exists>n. lset (ldropn n P) \<subseteq> VV p** )"
          show ?thesis sorry
        qed
      next
        assume "v0 \<notin> S - W"
        with `v0 \<in> S` have "v0 \<in> W" by blast
        with `P $ 0 = v0` `\<not>lnull P` show "lset P \<inter> W \<noteq> {}"
          by (metis disjoint_iff_not_equal lnth_0 lset_intros(1) not_lnull_conv)
      qed
    }
    ultimately have "attractor_strategy_on p \<sigma> v0 S W"
      unfolding attractor_strategy_on_def strategy_attracts_to_def
      using \<sigma>_valid by blast
  }
  thus ?thesis by blast
qed
*)

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
        using valid_path_ltl maximal_tail path_conforms_with_strategy_ltl by auto

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
      using valid_path_ltl maximal_tail path_conforms_with_strategy_ltl by auto
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

  show "strategy_avoids p \<sigma> (V - A) A" proof (cases)
    assume "V - A = {}"
    show ?thesis by (simp add: `V - A = {}`)
  next
    assume "V - A \<noteq> {}"
    show ?thesis proof (unfold strategy_avoids_def; intro allI impI; elim conjE)
      fix P n i
      assume "\<not>lnull P" "valid_path P" "path_conforms_with_strategy p P \<sigma>" "P $ 0 \<in> V - A"

      thus "lset P \<inter> A = {}" proof (induct P)
        case adm
        show ?case proof (rule ccpo.admissibleI)
          fix X assume
            X: "Complete_Partial_Order.chain path_prefix X"
               "\<forall>P \<in> X. \<not>lnull P \<longrightarrow> valid_path P \<longrightarrow> path_conforms_with_strategy p P \<sigma> \<longrightarrow> P $ 0 \<in> V - A \<longrightarrow> lset P \<inter> A = {}"
          {
            assume lSupX: "valid_path (lSup X)" "path_conforms_with_strategy p (lSup X) \<sigma>" "lSup X $ 0 \<in> V - A"
            have "lset (lSup X) \<inter> A = {}" proof (rule ccontr)
              assume "lset (lSup X) \<inter> A \<noteq> {}"
              then obtain P where P: "P \<in> X" "lset P \<inter> A \<noteq> {}" using X(1) lset_lSup by blast
              have *: "lprefix P (lSup X)" by (simp add: P(1) X(1) llist.lub_upper)
              from P(2) have "\<not>lnull P" using lset_eq_empty by fastforce
              moreover with * lSupX(3) have "P $ 0 \<in> V - A" using lnth_lprefix by force
              moreover from * lSupX(1) have "valid_path P" using valid_path_prefix by blast
              moreover from * lSupX(2) have "path_conforms_with_strategy p P \<sigma>" using path_conforms_with_strategy_prefix by blast
              ultimately show False using X(2) P by blast
            qed
          }
          thus "\<not>lnull (lSup X) \<longrightarrow> valid_path (lSup X) \<longrightarrow> path_conforms_with_strategy p (lSup X) \<sigma> \<longrightarrow> lSup X $ 0 \<in> V - A \<longrightarrow> lset (lSup X) \<inter> A = {}" by blast
        qed
      next
        case LNil thus ?case by simp
      next
        case (LCons v P)
        have "lnull P \<Longrightarrow> lset P \<inter> A = {}" by (simp add: lset_lnull)
        moreover from LCons(2) LCons.prems(2) LCons.prems(3)
          have "\<not>lnull P \<Longrightarrow> P $ 0 \<in> V - A \<Longrightarrow> lset P \<inter> A = {}"
          using valid_path_ltl maximal_tail path_conforms_with_strategy_ltl by force
        moreover {
          assume "\<not>lnull P" "P $ 0 \<notin> V - A"
          then obtain P' w where w: "P = LCons w P'" by (meson not_lnull_conv)
          have "\<not>deadend v" using LCons.prems(2) edges_are_in_V valid_path_edges' w by blast
          have "v \<in> V - A" using LCons.prems(4) by auto
          from `\<not>lnull P` `P $ 0 \<notin> V - A` LCons.prems(2) w
            have "w \<in> A"
            by (metis DiffI llist.set_intros(1) lnth_0 not_lnull_conv rev_subsetD valid_path_in_V valid_path_ltl')
          have False proof (cases)
            assume "v \<in> VV p"
            with w LCons.prems(3)
              have "path_conforms_with_strategy p (LCons v (LCons w P')) \<sigma>" by blast
            with `v \<in> VV p`
              have "\<sigma> v = w"
              using path_conforms_with_strategy_start by blast
            from `v \<in> VV p` `\<not>deadend v` `v \<in> V - A`
              have "\<sigma>' v \<notin> A"
              using \<sigma>'_correct(1) by blast
            with \<sigma>_def `\<sigma> v = w` `v \<in> V - A` `w \<in> A` show False by auto
          next
            assume "v \<notin> VV p"
            with `v \<in> V - A`
              have "v \<in> VV p**" by auto
            moreover from `w \<in> A` LCons.prems(2) w
              have "\<exists>w. v\<rightarrow>w \<and> w \<in> A" using valid_path_edges' by blast
            ultimately
              have "v \<in> directly_attracted p** A"
              using `\<not>deadend v` `v \<in> V - A` unfolding directly_attracted_def by auto
            with `v \<in> V - A` assms show False unfolding A_def using attractor_unfolding by fastforce
          qed
        }
        ultimately show "lset (LCons v P) \<inter> A = {}" using LCons.prems(4) by auto
      qed
    qed
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
