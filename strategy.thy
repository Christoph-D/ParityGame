theory strategy
imports
  Main
  parity_game
begin

type_synonym 'a Strategy = "'a \<Rightarrow> 'a option"

context ParityGame begin
definition strategy_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_on p \<sigma> W \<equiv> \<forall>v \<in> W \<inter> VV p. \<not>deadend v \<longrightarrow> (\<exists>w. \<sigma> v = Some w)"
definition strategy_only_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_only_on p \<sigma> W \<equiv> \<forall>v. (v \<in> W \<inter> VV p \<and> \<not>deadend v \<longrightarrow> (\<exists>w. \<sigma> v = Some w)) \<and> (v \<notin> W \<inter> VV p \<longrightarrow> \<sigma> v = None)"

definition path_conforms_with_strategy :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy p P \<sigma> \<equiv> \<forall>i w. enat i < llength P \<and> P $ i \<in> VV p \<and> \<sigma> (P $ i) = Some w \<longrightarrow> enat (Suc i) < llength P \<and> P $ Suc i = w"
definition path_conforms_with_strategy_up_to :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> nat \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy_up_to p P \<sigma> n \<equiv> \<forall>i w. enat i < llength P \<and> i < n \<and> P $ i \<in> VV p \<and> \<sigma> (P $ i) = Some w \<longrightarrow> enat (Suc i) < llength P \<and> P $ Suc i = w"

(* "Conform to \<sigma> as long as possible." *)
definition path_conforms_with_strategy_maximally :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy_maximally p P \<sigma> \<equiv> (path_conforms_with_strategy p P \<sigma>
      \<or> (\<exists>n. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat (Suc n) = llength P \<and> P $ n \<in> VV p \<and> \<sigma> (P $ n) = None))
    \<and> (\<forall>i. enat i < llength P \<and> \<not>deadend (P $ i) \<and> (P $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (P $ i) = Some w)) \<longrightarrow> enat (Suc i) < llength P)"

definition valid_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "valid_strategy p \<sigma> \<equiv> \<forall>v w. \<sigma> v = Some w \<longrightarrow> v \<in> VV p \<and> v\<rightarrow>w"
definition valid_strategy_from :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  "valid_strategy_from p \<sigma> v0 \<equiv> (\<forall>v w. \<sigma> v = Some w \<longrightarrow> v \<in> VV p \<and> v\<rightarrow>w)
    \<and> (\<forall>P n. enat n < llength P \<and> valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P $ 0 = v0 \<and> P $ n \<in> VV p \<and> \<not>deadend (P $ n)
        \<longrightarrow> (\<exists>w. \<sigma> (P $ n) = Some w))"

definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v \<equiv> \<forall>P. \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v \<longrightarrow> winning_path p P"

definition strategy_attracts_from_to :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_from_to p \<sigma> A W \<equiv> (\<forall>P.
      \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 \<in> A
    \<longrightarrow> lset P \<inter> W \<noteq> {})"

definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv> (\<forall>P n.
      \<not>lnull P \<and> valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P $ 0 \<in> A
    \<longrightarrow> (\<forall>i \<le> n. enat i < llength P \<longrightarrow> P $ i \<notin> W))"

definition strategy_less_eq :: "'a Strategy \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy_less_eq \<sigma> \<sigma>' \<equiv> \<forall>v w. \<sigma> v = Some w \<longrightarrow> \<sigma> v = \<sigma>' v"
abbreviation "strategy_less \<equiv> \<lambda>\<sigma> \<sigma>'. strategy_less_eq \<sigma> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>'"

lemma path_conforms_with_strategy_approximations:
  assumes "\<And>n. path_conforms_with_strategy_up_to p P \<sigma> n"
  shows "path_conforms_with_strategy p P \<sigma>"
proof (subst path_conforms_with_strategy_def, clarify)
  fix i v w assume "enat i < llength P" "P $ i \<in> VV p" "\<sigma> (P $ i) = Some w"
  thus "enat (Suc i) < llength P \<and> P $ Suc i = w" using assms[of "Suc i"] path_conforms_with_strategy_up_to_def by blast
qed

lemma path_conforms_with_strategy_approximations2: "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy_up_to p P \<sigma> n"
  and path_conforms_with_strategy_less_eq: "path_conforms_with_strategy_up_to p P \<sigma> n \<Longrightarrow> m \<le> n \<Longrightarrow> path_conforms_with_strategy_up_to p P \<sigma> m"
  by simp_all

lemma path_conforms_up_to_VVpstar:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> n" "P $ n \<notin> VV p"
  shows "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)" using assms less_Suc_eq by auto

lemma path_conforms_empty:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> n" "\<not>enat n < llength P"
  shows "path_conforms_with_strategy_up_to p P \<sigma> m"
proof (unfold path_conforms_with_strategy_up_to_def; clarify)
  fix i w assume i: "enat i < llength P" "P $ i \<in> VV p" "\<sigma> (P $ i) = Some w"
  from i(1) have "enat i < llength P" using dual_order.strict_trans enat_ord_simps(2) by blast
  from this assms(2) have "i < n" by (meson dual_order.strict_trans1 enat_ord_simps(2) le_less_linear)
  thus "enat (Suc i) < llength P \<and> P $ Suc i = w" using i assms(1) path_conforms_with_strategy_up_to_def by blast
qed

abbreviation path_prefix :: "'a Path \<Rightarrow> 'a Path \<Rightarrow> bool" where "path_prefix \<equiv> lprefix"

lemma path_prefix_length: "\<lbrakk> path_prefix P P'; i < llength P \<rbrakk> \<Longrightarrow> i < llength P'" by (metis dual_order.strict_trans lstrict_prefix_def lstrict_prefix_llength_less)
lemma path_prefix_included: "\<lbrakk> path_prefix P P'; enat i < llength P \<rbrakk> \<Longrightarrow> P $ i = P' $ i" using lprefix_lnthD by blast
lemma path_prefix_infinite: "\<lbrakk> path_prefix P P'; \<not>lfinite P \<rbrakk> \<Longrightarrow> P $ i = P' $ i" by (simp add: not_lfinite_lprefix_conv_eq)
lemma path_prefix_valid:
  assumes "valid_path P'" "path_prefix P P'"
  shows "valid_path P"
proof (subst valid_path_equiv, intro conjI)
  show "lset P \<subseteq> V" by (meson assms(1) assms(2) dual_order.trans lprefix_lsetD valid_path_in_V)
  show "\<forall>i v w. enat (Suc i) < llength P \<and> P $ i = v \<and> P $ Suc i = w \<longrightarrow> v \<rightarrow> w" proof (clarify)
    fix i v w assume *: "enat (Suc i) < llength P"
    hence "enat (Suc i) < llength P'" using assms(2) path_prefix_length by blast
    thus "P $ i \<rightarrow> (P $ Suc i)" using "*" assms(1) assms(2) dual_order.strict_trans path_prefix_included valid_path_edges by fastforce
  qed
qed

lemma path_conforms_with_strategy_maximally_empty [simp]: "path_conforms_with_strategy_maximally p LNil \<sigma>" by simp

lemma path_conforms_with_strategy_maximally_start:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and "P $ 0 = v0" "v0 \<in> VV p" "\<sigma> v0 = Some w"
    and "\<not>lnull P"
  shows "enat (Suc 0) < llength P \<and> \<sigma> v0 = Some (P $ Suc 0)"
proof-
  have *: "P $ 0 \<in> VV p \<and> \<sigma> (P $ 0) = Some w" by (simp add: assms(2) assms(3) assms(4))
  { assume "path_conforms_with_strategy p P \<sigma>"
    moreover have "enat 0 < llength P" using `\<not>lnull P` zero_enat_def by auto
    ultimately have "enat (Suc 0) < llength P \<and> P $ Suc 0 = w" using * path_conforms_with_strategy_def by blast
    hence ?thesis using assms(4) by blast
  }
  moreover
  { assume "\<exists>n v. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat (Suc n) = llength P \<and> P $ n = v \<and> v \<in> VV p \<and> \<sigma> v = None"
    then obtain n v where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "enat (Suc n) = llength P" "P $ n = v" "v \<in> VV p" "\<sigma> v = None" by blast
    have ?thesis proof (cases)
      assume "n = 0"
      thus ?thesis using assms(2) assms(4) n_def(2) n_def(3) n_def(5) by auto
    next
      assume "n \<noteq> 0"
      hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" using n_def(1) by simp
      hence "enat (Suc 0) < llength P \<and> P $ Suc 0 = w" unfolding path_conforms_with_strategy_up_to_def using * `\<not>lnull P` zero_enat_def by auto
      thus ?thesis using assms(4) by blast
    qed
  }
  ultimately show ?thesis using assms(1) path_conforms_with_strategy_maximally_def by blast
qed

lemma path_conforms_with_strategy_maximally_start_VVpstar:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and P: "P $ 0 \<in> VV p**" "\<not>deadend (P $ 0)" "\<not>lnull P"
  shows "enat (Suc 0) < llength P"
proof-
  have "P $ 0 \<notin> VV p \<and> enat 0 < llength P" using P(1) P(3) zero_enat_def by auto
  thus ?thesis using path_conforms_with_strategy_maximally_def assms(1) P(2) by metis
qed

lemma maximal_path_conforms_maximally:
  assumes P_conforms: "path_conforms_with_strategy p P \<sigma>"
    and P_maximal: "maximal_path P"
  shows "path_conforms_with_strategy_maximally p P \<sigma>"
proof-
  { fix i assume "enat i < llength P" "\<not>deadend (P $ i)"
    with P_maximal have "enat (Suc i) < llength P" using maximal_path_impl1 by blast
  }
  with P_conforms show ?thesis unfolding path_conforms_with_strategy_maximally_def by blast
qed

lemma valid_strategy_none_on_VVpstar: "valid_strategy p \<sigma> \<Longrightarrow> v \<notin> VV p \<Longrightarrow> \<sigma> v = None" by (metis not_None_eq valid_strategy_def)
lemma valid_strategy_none_on_VVpstar2: "valid_strategy p \<sigma> \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<sigma> v = None" by (metis DiffD2 Player.distinct(1) valid_strategy_none_on_VVpstar)
lemma valid_strategy_none_on_deadends: "valid_strategy p \<sigma> \<Longrightarrow> deadend v \<Longrightarrow> \<sigma> v = None" by (meson edges_are_in_V not_Some_eq valid_strategy_def)
lemma valid_empty_strategy: "valid_strategy p (\<lambda>_. None)" using valid_strategy_def by simp

lemma valid_strategy_updates:
  assumes "valid_strategy p \<sigma>" "v0 \<rightarrow> w0" "v0 \<in> VV p"
  shows "valid_strategy p (\<sigma>(v0 \<mapsto> w0))"
proof-
  let ?\<sigma> = "\<sigma>(v0 \<mapsto> w0)"
  { fix v w assume *: "?\<sigma> v = Some w"
    hence "v \<in> VV p \<and> v \<rightarrow> w" using assms valid_strategy_def by (cases "v0 = v"; auto)
  }
  thus ?thesis using valid_strategy_def by blast
qed

lemma strategy_subset [intro]: "\<lbrakk> W' \<subseteq> W; strategy_on p \<sigma> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'"
  using strategy_on_def by (simp add: strategy_on_def subset_iff)
lemma strategy_on_empty [simp]: "strategy_on p \<sigma> {}"
  by (simp add: strategy_on_def)
lemma strategy_only_on_empty_set_exists: "\<exists>\<sigma>. valid_strategy p \<sigma> \<and> strategy_only_on p \<sigma> {}"
  by (rule exI [of _ "\<lambda>_.None"]; simp add: valid_strategy_def strategy_only_on_def)
lemma strategy_only_on_on [intro]: "strategy_only_on p \<sigma> W \<Longrightarrow> strategy_on p \<sigma> W"
  by (simp add: strategy_on_def strategy_only_on_def)
lemma strategy_only_on_updates:
  assumes "strategy_only_on p \<sigma> W" "v0 \<in> VV p"
  shows "strategy_only_on p (\<sigma>(v0 \<mapsto> w0)) (W \<union> {v0})"
proof-
  { fix v assume v: "v \<in> (W \<union> {v0}) \<inter> VV p" "\<not>deadend v"
    have "\<exists>w. (\<sigma>(v0 \<mapsto> w0)) v = Some w" proof (cases)
      assume "v = v0" thus ?thesis by simp
    next
      assume "v \<noteq> v0"
      hence "v \<in> W \<inter> VV p" using v(1) by blast
      hence "\<exists>w. \<sigma> v = Some w" using v(2) assms(1) strategy_only_on_def by blast
      thus ?thesis using `v \<noteq> v0` by simp
    qed
  }
  moreover {
    fix v assume v: "v \<notin> (W \<union> {v0}) \<inter> VV p"
    hence *: "v \<noteq> v0" using assms(2) by blast
    have "\<sigma> v = None" using assms(1) strategy_only_on_def v by blast
    hence "(\<sigma>(v0 \<mapsto> w0)) v = None" using * by simp
  }
  ultimately show ?thesis using strategy_only_on_def by presburger
qed

lemma strategy_only_on_case_rule [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<in> VV p - W \<rbrakk> \<Longrightarrow> strategy_only_on p (\<sigma>(v \<mapsto> w)) (insert v W)" using strategy_only_on_updates by auto
lemma strategy_only_on_on_subset [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; W' \<subseteq> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'" by (simp add: strategy_only_on_on strategy_subset)
lemma strategy_only_on_elements [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<notin> W \<rbrakk> \<Longrightarrow> \<sigma> v = None" using strategy_only_on_def by auto
lemma strategy_only_on_case_rule2 [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<notin> VV p \<rbrakk> \<Longrightarrow> strategy_only_on p \<sigma> (insert v W)" using strategy_only_on_def by (simp add: strategy_only_on_def)
lemma valid_strategy_in_V:
  "\<lbrakk> valid_strategy p \<sigma>; v \<in> VV p; \<sigma> v = Some w \<rbrakk> \<Longrightarrow> w \<in> V" using assms valid_edge_set valid_strategy_def by auto
lemma valid_strategy_from_is_valid_strategy [intro]:
  "valid_strategy_from p \<sigma> v0 \<Longrightarrow> valid_strategy p \<sigma>" using valid_strategy_def valid_strategy_from_def by simp

lemma path_conforms_up_to_deadends:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> n" "valid_path P" "valid_strategy p \<sigma>"
    and "enat n < llength P" "deadend (P $ n)"
  shows "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)"
proof-
  { fix i w assume i: "enat i < llength P" "i < Suc n" "P $ i \<in> VV p" and w: "\<sigma> (P $ i) = Some w"
    have "enat (Suc n) = llength P" by (simp add: assms(2) assms(4) assms(5) valid_path_ends_on_deadend)
    have "P $ Suc i = w \<and> enat (Suc i) < llength P" proof (cases)
      assume "i < n"
      hence "P $ Suc i = w" using assms(1) i(1) i(3) w path_conforms_with_strategy_up_to_def by blast
      thus ?thesis by (metis Suc_mono `enat (Suc n) = llength P` `i < n` enat_ord_simps(2))
    next
      assume "\<not>i < n"
      hence "i = n" using i(2) less_antisym by blast
      have "\<sigma> (P $ n) = None" using assms(3) assms(5) valid_strategy_none_on_deadends by blast
      thus ?thesis using w `i = n` by simp
    qed
  }
  thus ?thesis by simp
qed

lemma one_step_path_exists:
  assumes "v0 \<in> V" "valid_strategy p \<sigma>"
  shows "\<exists>P. valid_path P \<and> lfinite P \<and> path_conforms_with_strategy_up_to p P \<sigma> (Suc 0) \<and> \<not>lnull P \<and> P $ 0 = v0"
proof (cases "\<sigma> v0 = None"; rule exI; intro conjI)
  case True
  def [simp]: P \<equiv> "LCons v0 LNil"
  show "lfinite P" "\<not>lnull P" "P $ 0 = v0" by simp_all
  show "valid_path P" by (simp add: assms(1) valid_path_base')
  show "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" using True by simp
next
  case False
  hence w0: "the (\<sigma> v0) \<in> V" by (metis assms(2) option.exhaust_sel valid_strategy_in_V valid_strategy_none_on_VVpstar)
  def [simp]: P \<equiv> "LCons v0 (LCons (the (\<sigma> v0)) LNil)"
  have "llength P = eSuc (eSuc 0)" by simp
  hence *: "llength P = enat (Suc (Suc 0))" by (simp add: eSuc_enat zero_enat_def)
  show "lfinite P" "\<not>lnull P" "P $ 0 = v0" by simp_all
  show "valid_path P" proof (intro valid_path_impl2, simp add: w0 assms(1); clarify)
    fix i assume i: "enat (Suc i) < llength P"
    hence "i = 0" using i by (subst (asm) "*") simp
    moreover have "v0 \<in> VV p \<and> v0\<rightarrow>(the (\<sigma> v0))" using assms(2) valid_strategy_def False by auto
    ultimately show "P $ i \<rightarrow> (P $ Suc i)" using w0 by fastforce
  qed
  show "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" unfolding path_conforms_with_strategy_up_to_def using "*" by auto
qed

lemma valid_strategy_from_starts_correctly:
  assumes "valid_strategy_from p \<sigma> v0" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<exists>w. \<sigma> v0 = Some w"
proof -
  obtain P where P_def: "valid_path P" "lfinite P" "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" "\<not>lnull P" "P $ 0 = v0"
    using one_step_path_exists assms by blast
  moreover have "path_conforms_with_strategy_up_to p P \<sigma> 0" using P_def(2) by simp
  moreover have "P $ 0 \<in> VV p" by (simp add: assms(2) P_def(5))
  moreover have "\<not>deadend (P $ 0)" using P_def(5) assms(3) by blast
  moreover have "enat 0 < llength P" using P_def(4) zero_enat_def by auto
  ultimately have "\<exists>w. \<sigma> (P $ 0) = Some w" using assms(1)
    apply (unfold valid_strategy_from_def)
    apply (drule conjunct2)
    by blast
  thus ?thesis using P_def(5) by blast
qed

lemma infinite_path_tail_conforms [intro]:
  assumes "path_conforms_with_strategy p P \<sigma>"
  shows "path_conforms_with_strategy p (ltl P) \<sigma>"
proof (unfold path_conforms_with_strategy_def, intro allI impI, elim conjE, case_tac "lnull P", simp)
  fix i w assume i: "enat i < llength (ltl P)" "ltl P $ i \<in> VV p" "\<sigma> (ltl P $ i) = Some w"
  assume "\<not>lnull P"
  hence "ltl P $ i = P $ Suc i" by (simp add: lnth_ltl)
  with i(2) i(3) have "P $ Suc i \<in> VV p \<and> \<sigma> (P $ Suc i) = Some w" by simp
  moreover from i(1) have "enat (Suc i) < llength P" using enat_ltl_Suc by blast
  ultimately have "enat (Suc (Suc i)) < llength P \<and> P $ Suc (Suc i) = w" using assms(1) path_conforms_with_strategy_def by blast
  with `\<not>lnull P` show "enat (Suc i) < llength (ltl P) \<and> ltl P $ Suc i = w" using enat_Suc_ltl lnth_ltl by blast
qed

lemma path_conforms_with_strategy_up_to_tail:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)"
  shows "path_conforms_with_strategy_up_to p (ltl P) \<sigma> n"
proof (unfold path_conforms_with_strategy_up_to_def; intro allI impI; elim conjE, case_tac "lnull P", simp)
  let ?P = "ltl P"
  fix i w assume i: "enat i < llength ?P" "i < n" "?P $ i \<in> VV p" "\<sigma> (?P $ i) = Some w"
  assume "\<not>lnull P"
  from i(1) have "enat (Suc i) < llength P" by (metis ldrop_eSuc_ltl leD leI lnull_ldropn)
  moreover from i(2) have "Suc i < Suc n" by simp
  moreover from `\<not>lnull P` i(3) have "P $ Suc i \<in> VV p" using lnth_ltl by force
  moreover from `\<not>lnull P` i(4) have "\<sigma> (P $ Suc i) = Some w" using lnth_ltl by fastforce
  ultimately have "enat (Suc (Suc i)) < llength P \<and> P $ Suc (Suc i) = w" using assms(1) path_conforms_with_strategy_up_to_def by blast
  thus "enat (Suc i) < llength ?P \<and> ?P $ Suc i = w" by (simp add: `\<not>lnull P` enat_Suc_ltl lnth_ltl)
qed

lemma infinite_path_tail_head:
  assumes "\<not>lnull P" "P $ 0 \<in> VV p" "\<sigma> (P $ 0) = Some w" "path_conforms_with_strategy p P \<sigma>"
  shows "enat (Suc 0) < llength P \<and> P $ Suc 0 = w"
proof-
  have "enat 0 < llength P" using assms(1) zero_enat_def by auto
  thus ?thesis using assms unfolding path_conforms_with_strategy_def by blast
qed

lemma path_conforms_with_strategy_maximally_tail:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
  shows "path_conforms_with_strategy_maximally p (ltl P) \<sigma>"
proof (case_tac "lnull P", simp)
  assume "\<not>lnull P"
  let ?P = "ltl P"

  (* Helper lemma to prove the second conjunct of path_conforms_with_strategy_maximally. *)
  { fix i assume i: "enat i < llength (ltl P)" "\<not>deadend (ltl P $ i)" "ltl P $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (ltl P $ i) = Some w)"
    have "enat (Suc i) < llength P" proof-
      have "enat i < epred (llength P)" using i(1) by (simp add: epred_llength)
      hence "eSuc (enat i) < llength P" by (metis epred_eSuc epred_le_epredI leD leI)
      thus ?thesis by (simp add: eSuc_enat)
    qed
    moreover have "\<not>deadend (P $ Suc i)" using `\<not>lnull P` i(2) lnth_ltl by fastforce
    moreover have "P $ Suc i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (P $ Suc i) = Some w)" using `\<not>lnull P` i(3) lnth_ltl by force
    ultimately have "enat (Suc i) < llength (ltl P)" using assms path_conforms_with_strategy_maximally_def enat_Suc_ltl by blast
  } note * = this

  let ?A = "path_conforms_with_strategy p P \<sigma>"
  let ?B = "\<exists>n v. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat (Suc n) = llength P \<and> P $ n = v \<and> P $ n \<in> VV p \<and> \<sigma> v = None"
  show ?thesis proof (cases)
    assume ?A
    hence "path_conforms_with_strategy p ?P \<sigma>" using infinite_path_tail_conforms
      by (meson `\<not>lnull P` path_conforms_with_strategy_approximations path_conforms_with_strategy_approximations2 path_conforms_with_strategy_up_to_tail)
    thus ?thesis using * path_conforms_with_strategy_maximally_def by blast
  next
    assume "\<not>?A"
    hence "?B" using assms path_conforms_with_strategy_maximally_def by metis
    then obtain n v where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "enat (Suc n) = llength P" "P $ n = v" "v \<in> VV p" "\<sigma> v = None" by blast
    show ?thesis proof (cases)
      assume "n = 0"
      hence "eSuc 0 = llength P" using n_def(2) by (simp add: eSuc_enat zero_enat_def)
      hence "P = LCons v LNil" by (metis `n = 0` eSuc_inject llength_LCons llength_eq_0 lnth_0 lnull_def n_def(3) not_lnull_conv)
      thus ?thesis by simp
    next
      assume "n \<noteq> 0"
      then obtain m where "Suc m = n" by (metis nat.exhaust)
      hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc m) \<and> enat (Suc (Suc m)) = llength P \<and> P $ Suc m = v \<and> v \<in> VV p \<and> \<sigma> v = None"
        using n_def by metis
      moreover with `\<not>lnull P` have "path_conforms_with_strategy_up_to p ?P \<sigma> m" using path_conforms_with_strategy_up_to_tail by blast
      ultimately have "\<exists>n v. path_conforms_with_strategy_up_to p ?P \<sigma> n \<and> enat (Suc n) = llength ?P \<and> ?P $ n = v \<and> v \<in> VV p \<and> \<sigma> v = None"
        using `\<not>lnull P` by (metis (no_types, lifting) co.enat.sel(2) eSuc_enat epred_llength lnth_ltl)
      thus ?thesis using * path_conforms_with_strategy_maximally_def by blast
    qed
  qed
qed

(* strategy_less_eq *)

lemma strategy_less_eq_equiv: "\<lbrakk> \<And>v. \<sigma> v \<noteq> None \<Longrightarrow> \<sigma>' v = \<sigma> v \<rbrakk> \<Longrightarrow> strategy_less_eq \<sigma> \<sigma>'"
  by (simp add: strategy_less_eq_def)

lemma strategy_less_eq_not_none: "\<lbrakk> strategy_less_eq \<sigma> \<sigma>'; \<sigma> v \<noteq> None \<rbrakk> \<Longrightarrow> \<sigma>' v \<noteq> None"
  using strategy_less_eq_def by auto

lemma strategy_less_eq_updates: "\<sigma> v = None \<Longrightarrow> strategy_less_eq \<sigma> (\<sigma>(v \<mapsto> w))"
  by (metis fun_upd_other strategy_less_eq_equiv)

lemma strategy_on_is_monotone:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_on p \<sigma> W"
  shows "strategy_on p \<sigma>' W"
proof-
  { fix v assume "v \<in> W \<inter> VV p" "\<not>deadend v"
    hence "\<exists>w. \<sigma> v = Some w" using assms(2) strategy_on_def by blast
    hence "\<exists>w. \<sigma>' v = Some w" using assms(1) by (metis strategy_less_eq_def)
  }
  thus ?thesis by (meson strategy_on_def)
qed

lemma strategy_less_eq_tran:
  "\<lbrakk> strategy_less_eq \<sigma> \<sigma>'; strategy_less_eq \<sigma>' \<sigma>'' \<rbrakk> \<Longrightarrow> strategy_less_eq \<sigma> \<sigma>''"
  unfolding strategy_less_eq_def by auto

lemma strategy_less_eq_refl [simp]: "strategy_less_eq \<sigma> \<sigma>"
  by (simp add: option.case_eq_if strategy_less_eq_def)

lemma strategy_less_eq_antisymm:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_less_eq \<sigma>' \<sigma>"
  shows "\<sigma> = \<sigma>'"
proof (rule ccontr)
  assume "\<sigma> \<noteq> \<sigma>'"
  then obtain v where "\<sigma> v \<noteq> \<sigma>' v" by blast
  thus False by (metis assms option.collapse strategy_less_eq_def)
qed

lemma strategy_preorder: "class.preorder strategy_less_eq strategy_less"
  by (unfold_locales) (blast intro: strategy_less_eq_antisymm strategy_less_eq_refl strategy_less_eq_tran)+

lemma strategy_less_eq_least [simp]: "strategy_only_on p \<sigma> {} \<Longrightarrow> strategy_less_eq \<sigma> \<sigma>'"
  by (simp add: strategy_less_eq_def strategy_only_on_elements)

lemma strategy_less_eq_extensible:
  assumes "W \<subseteq> W'" "strategy_on p \<sigma> W" "valid_strategy p \<sigma>"
  shows "\<exists>\<sigma>'. valid_strategy p \<sigma>' \<and> strategy_less_eq \<sigma> \<sigma>' \<and> strategy_on p \<sigma>' W'"
proof-
  def [simp]: \<sigma>' \<equiv> "\<lambda>v. if \<sigma> v \<noteq> None then \<sigma> v else (if v \<in> VV p \<and> \<not>deadend v then Some (SOME w. v\<rightarrow>w) else None)"
  have "strategy_less_eq \<sigma> \<sigma>'" proof-
    have "\<And>v w. \<sigma> v = Some w \<Longrightarrow> \<sigma> v = \<sigma>' v" unfolding \<sigma>'_def by simp
    thus ?thesis using strategy_less_eq_def by blast
  qed
  moreover have "strategy_on p \<sigma>' W'" proof (unfold strategy_on_def; rule; rule)
    fix v assume v: "v \<in> W' \<inter> VV p" "\<not>deadend v"
    show "\<exists>w. \<sigma>' v = Some w" proof (cases)
      assume assm: "\<sigma> v = None"
      have "v \<in> VV p" using v(1) by blast
      hence "\<sigma>' v = Some (SOME w. v\<rightarrow>w)" unfolding \<sigma>'_def using assm v(2) by presburger
      thus "\<exists>w. \<sigma>' v = Some w" by blast
    next
      assume *: "\<sigma> v \<noteq> None"
      hence **: "\<exists>w. \<sigma> v = Some w" by blast
      have "\<sigma> v = \<sigma>' v" unfolding \<sigma>'_def by (simp add: "*")
      thus ?thesis using ** by presburger
    qed
  qed
  moreover have "valid_strategy p \<sigma>'" proof (unfold valid_strategy_def, clarify)
    fix v w assume v_def: "\<sigma>' v = Some w"
    show "v \<in> VV p \<and> v \<rightarrow> w" proof (cases "\<sigma> v = None")
      case True
      have "v \<in> VV p" by (metis \<sigma>'_def True option.distinct(1) v_def)
      have "\<sigma>' v = Some (SOME w. v\<rightarrow>w)" using True v_def by (metis \<sigma>'_def option.distinct(1))
      hence *: "w = (SOME w. v\<rightarrow>w)" by (metis option.sel v_def)
      have "\<not>deadend v" using v_def `\<sigma> v = None` by (metis \<sigma>'_def option.distinct(1))
      hence "\<exists>w. v\<rightarrow>w" by auto
      thus ?thesis using * `v \<in> VV p` by (metis (mono_tags, lifting) someI)
    next
      case False
      then obtain w' where w'_def: "\<sigma> v = Some w'" by blast
      have "v \<in> VV p \<and> v \<rightarrow> w'" using assms(3) valid_strategy_def by (metis w'_def)
      moreover have "w = w'" by (metis False w'_def option.inject v_def \<sigma>'_def)
      ultimately show ?thesis by blast
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma strategy_only_on_extensible:
  assumes "valid_strategy p \<sigma>" "strategy_only_on p \<sigma> W'" "W' \<subseteq> W"
  shows "\<exists>\<sigma>'. valid_strategy p \<sigma>' \<and> strategy_less_eq \<sigma> \<sigma>' \<and> strategy_only_on p \<sigma>' W"
proof-
  let ?\<sigma>' = "\<lambda>v. if \<sigma> v \<noteq> None then \<sigma> v else if v \<in> W \<inter> VV p \<and> \<not>deadend v then Some (SOME w. v\<rightarrow>w) else None"
  have "valid_strategy p ?\<sigma>'" proof (unfold valid_strategy_def, intro allI impI)
    fix v w assume v: "?\<sigma>' v = Some w"
    thus "v \<in> VV p \<and> v\<rightarrow>w" proof (cases "\<sigma> v \<noteq> None")
      case True
      hence "\<sigma> v = ?\<sigma>' v" by simp
      thus "v \<in> VV p \<and> v\<rightarrow>w" using assms(1) v valid_strategy_def by (metis (no_types, lifting))
    next
      case False
      with v have *: "v \<in> W \<inter> VV p \<and> \<not>deadend v" by (metis option.distinct(2))
      hence "\<exists>w. v\<rightarrow>w" by blast
      hence "v\<rightarrow>(SOME w. v\<rightarrow>w)" by (meson someI_ex)
      hence "v\<rightarrow>the (Some (SOME w. v\<rightarrow>w))" by auto
      moreover have "v \<in> VV p" using * by simp
      ultimately show ?thesis using False v by (metis option.distinct(1) option.sel)
    qed
  qed
  moreover have "strategy_only_on p ?\<sigma>' W" proof (unfold strategy_only_on_def, intro allI conjI)
    fix v
    show "v \<in> W \<inter> VV p \<and> \<not>deadend v \<longrightarrow> (\<exists>w. ?\<sigma>' v = Some w)" (is ?A) by (metis option.collapse)
    show "v \<notin> W \<inter> VV p \<longrightarrow> ?\<sigma>' v = None" (is ?B) proof (clarify)
      fix v assume assm: "v \<notin> W \<inter> VV p"
      hence "v \<notin> W' \<inter> VV p" using assms(3) by blast
      hence "\<sigma> v = None" using assms(2) strategy_only_on_def by blast
      thus "?\<sigma>' v = None" using assm by auto
    qed
  qed
  moreover have "strategy_less_eq \<sigma> ?\<sigma>'" using strategy_less_eq_equiv by presburger
  ultimately show ?thesis using strategy_only_on_def by blast
qed

lemma path_conforms_preserved_under_extension:
  assumes "path_conforms_with_strategy p P \<sigma>'" "strategy_less_eq \<sigma> \<sigma>'"
  shows "path_conforms_with_strategy p P \<sigma>"
proof (unfold path_conforms_with_strategy_def, intro allI impI, elim conjE)
  fix i w assume i: "enat i < llength P" "P $ i \<in> VV p" "\<sigma> (P $ i) = Some w"
  hence "\<sigma>' (P $ i) = Some w" using assms(2) strategy_less_eq_def by auto
  with i(1) i(2) assms(1) show "enat (Suc i) < llength P \<and> P $ Suc i = w" unfolding path_conforms_with_strategy_def by blast
qed

(* winning_strategy *)

lemma winning_strategy_preserved_under_extension:
  assumes "winning_strategy p \<sigma> v0" "valid_strategy_from p \<sigma> v0" "strategy_less_eq \<sigma> \<sigma>'"
  shows "winning_strategy p \<sigma>' v0"
  using assms path_conforms_preserved_under_extension winning_strategy_def by blast

(* strategy_attracts_from_to *)

lemma strategy_attracts_from_to_trivial [simp]: "strategy_attracts_from_to p \<sigma> W W"
  by (metis disjoint_iff_not_equal lnth_0 lset_intros(1) not_lnull_conv strategy_attracts_from_to_def)
lemma strategy_attracts_from_to_empty [simp]: "strategy_attracts_from_to p \<sigma> {} W"
  by (simp add: strategy_attracts_from_to_def)

lemma strategy_attracts_from_to_extends:
  assumes "strategy_attracts_from_to p \<sigma> A W" "strategy_less_eq \<sigma> \<sigma>'"
  shows "strategy_attracts_from_to p \<sigma>' A W"
proof (unfold strategy_attracts_from_to_def, intro allI impI, elim conjE)
  fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>'" "P $ 0 \<in> A"
  from assms(2) P(4) have "path_conforms_with_strategy p P \<sigma>" using path_conforms_preserved_under_extension by blast
  with P(1) P(2) P(3) P(5) assms(1) show "lset P \<inter> W \<noteq> {}" using strategy_attracts_from_to_def by blast
qed

(* strategy_avoids *)

lemma strategy_avoids_trivial [simp]: "strategy_avoids p \<sigma> {} W"
  by (meson empty_iff strategy_avoids_def)

lemma strategy_avoids_directly:
  assumes "strategy_avoids p \<sigma> A W" "v0 \<in> A" "v0 \<in> VV p" "\<sigma> v0 = Some w0" "valid_strategy p \<sigma>"
  shows "w0 \<notin> W"
proof (rule ccontr, simp)
  assume assm: "w0 \<in> W"
  obtain P where P: "valid_path P" "lfinite P" "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" "\<not>lnull P" "P $ 0 = v0" using one_step_path_exists assms by blast
  have "v0 \<in> A" using P(4) assms(2) by simp
  hence "\<And>i v. i \<le> Suc 0 \<and> enat i < llength P \<longrightarrow> P $ i \<notin> W" using assms(1) strategy_avoids_def P by blast
  hence "\<And>v. enat (Suc 0) < llength P \<longrightarrow> P $ Suc 0 \<notin> W" by blast
  moreover have "v0 \<in> VV p" by (simp add: P(4) assms(3))
  ultimately show False
    using P(3) P(4) P(5) assm assms(4)
    by (metis (no_types, lifting) lessI llength_eq_0 neq_iff not_iless0 path_conforms_with_strategy_up_to_def zero_enat_def)
qed

lemma strategy_avoids_strongly:
  assumes "strategy_avoids p \<sigma> A W"
    and "path_conforms_with_strategy p P \<sigma>"
    and "enat n < llength P" "valid_path P" "P $ 0 \<in> A"
  shows "P $ n \<notin> W"
proof-
  from assms(3) have "\<not>lnull P" by auto
  with assms show ?thesis using strategy_avoids_def path_conforms_with_strategy_approximations2 by blast
qed

lemma valid_strategy_is_valid_strategy_from:
  assumes \<sigma>_valid: "valid_strategy p \<sigma>"
    and \<sigma>_only_on: "strategy_on p \<sigma> A"
    and \<sigma>_avoids: "strategy_avoids p \<sigma> A (V - A)"
    and v0_def: "v0 \<in> A"
  shows "valid_strategy_from p \<sigma> v0"
proof (unfold valid_strategy_from_def; intro conjI)
  show "\<forall>v w. \<sigma> v = Some w \<longrightarrow> v \<in> VV p \<and> v\<rightarrow>w" using \<sigma>_valid valid_strategy_def by blast
  show "\<forall>P n. enat n < llength P \<and> valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P $ 0 = v0 \<and> P $ n \<in> VV p \<and> \<not> deadend (P $ n) \<longrightarrow> (\<exists>w. \<sigma> (P $ n) = Some w)"
  proof (intro allI impI; elim conjE)
    fix P n
    assume n_valid: "enat n < llength P"
      and P_valid: "valid_path P"
      and P_conforms_up_to_n: "path_conforms_with_strategy_up_to p P \<sigma> n"
      and P_valid_start: "P $ 0 = v0"
      and P_Suc_n_in_VV_p: "P $ n \<in> VV p"
      and P_Suc_n_no_deadend: "\<not>deadend (P $ n)"
    have "\<not>lnull P" using n_valid by auto
    hence "P $ n \<notin> V - A" using P_conforms_up_to_n \<sigma>_avoids by (simp add: P_valid_start v0_def strategy_avoids_def P_valid n_valid)
    hence "P $ n \<in> A \<inter> VV p" using P_Suc_n_in_VV_p by blast
    thus "\<exists>w. \<sigma> (P $ n) = Some w" using \<sigma>_only_on P_Suc_n_no_deadend strategy_on_def by blast
  qed
qed

lemma valid_strategy_is_valid_strategy_from_V:
  "\<lbrakk> valid_strategy p \<sigma>; strategy_on p \<sigma> V; v0 \<in> V \<rbrakk> \<Longrightarrow> valid_strategy_from p \<sigma> v0"
  by (metis Diff_cancel empty_iff strategy_avoids_def valid_strategy_is_valid_strategy_from)

(* temporarily commented out
primrec greedy_conforming_path :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a option" where
  "greedy_conforming_path p \<sigma> v0 0 = Some v0"
  | "greedy_conforming_path p \<sigma> v0 (Suc n) = (
    if greedy_conforming_path p \<sigma> v0 n = None
    then None
    else if (the (greedy_conforming_path p \<sigma> v0 n)) \<in> VV p
      then \<sigma> (the (greedy_conforming_path p \<sigma> v0 n))
      else if deadend (the (greedy_conforming_path p \<sigma> v0 n))
        then None
        else Some (SOME w. w \<in> V \<and> (the (greedy_conforming_path p \<sigma> v0 n))\<rightarrow>w))"

theorem strategy_conforming_path_exists:
  fixes p \<sigma>
  assumes v0_def: "v0 \<in> V" and \<sigma>_dom: "strategy_on p \<sigma> V" and \<sigma>_valid: "valid_strategy_from p \<sigma> v0"
  shows "\<exists>P. \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0"
  proof (intro exI conjI)
    (* Recursively construct a path starting from v0. *)
    def P \<equiv> "greedy_conforming_path p \<sigma> v0"
    (* We need a simplification rule on P (not on greedy_conforming_path) for the proofs below. *)
    have P_simp [simp]: "\<And>n. P (Suc n) = (
      if P n = None
      then None
      else if (the (P n)) \<in> VV p
        then \<sigma> (the (P n))
        else if deadend (the (P n)) then None else Some (SOME w. w \<in> V \<and> (the (P n))\<rightarrow>w))"
        apply (subst P_def)+ by simp
    (* have P_simp2 [simp]: "\<And>n. P n = None \<Longrightarrow> P (Suc n) = None" by simp *)
    have P_simp3: "\<And>n v. P n = Some v \<Longrightarrow> P (Suc n) =
      (if v \<in> VV p
        then \<sigma> v
        else if deadend v then None else Some (SOME w. w \<in> V \<and> v\<rightarrow>w))"
       proof-
        fix n v assume assm: "P n = Some v"
        have *: "the (P n) = v" using assm by (metis option.sel)
        have "P n \<noteq> None" using assm by blast
        thus "P (Suc n) = (if v \<in> VV p then \<sigma> v else if deadend v then None else Some (SOME w. w \<in> V \<and> v \<rightarrow> w))"
          apply (subst P_simp) apply (subst "*")+ by presburger
      qed

    show P_valid_start: "P 0 = Some v0" unfolding P_def using v0_def by auto

    (* The key lemma.  Show simultaneously that
      1) the path is in V and
      2) there is an edge between every two consecutive entries. *)
    have edges_exist: "\<And>i v w. P i = Some v \<Longrightarrow> v \<in> V \<and> (P (Suc i) = Some w \<longrightarrow> v\<rightarrow>w)" proof-
      have *:
        "\<And>i v w. \<lbrakk> P i = Some v; v \<in> V; P (Suc i) = Some w \<rbrakk> \<Longrightarrow> w \<in> V \<and> v\<rightarrow>w" proof-
        fix i v w
        assume P_i: "P i = Some v" "v \<in> V" and P_Suc_i: "P (Suc i) = Some w"
        have no_deadend: "\<not>deadend v" proof (cases rule: VV_cases[of "v" p])
          show "v \<in> V" using P_i(2) .
        next
          assume P_i_in_VVp: "v \<in> VV p"
          hence "\<sigma> v = P (Suc i)" using P_i(1) P_simp3 by presburger
          then obtain w where "\<sigma> v = Some w" using P_Suc_i by auto
          hence "v\<rightarrow>w" using \<sigma>_valid P_i_in_VVp valid_strategy_from_def by blast
          thus ?thesis using valid_edge_set by auto
        next
          assume "v \<in> VV p**"
          hence "v \<notin> VV p" by auto
          thus ?thesis by (metis (no_types, hide_lams) P_Suc_i P_i(1) P_simp option.distinct(1) option.sel)
        qed
        show "w \<in> V \<and> v\<rightarrow>w" proof(cases)
          assume P_i_in_VVp: "v \<in> VV p"
          hence *: "\<sigma> v = P (Suc i)" using P_simp P_i(1) by presburger
          hence "\<sigma> v \<noteq> None" using P_Suc_i by auto
          hence "v\<rightarrow>the (\<sigma> v)" using \<sigma>_valid P_i_in_VVp valid_strategy_from_def by blast
          hence "v\<rightarrow>w" using * by auto
          moreover hence "the (P (Suc i)) \<in> V" using valid_edge_set by blast
          ultimately show ?thesis using valid_edge_set by auto
        next
          assume P_i_not_in_VVp: "v \<notin> VV p"
          hence P_Suc_i_simp1: "P (Suc i) = (if deadend (the (P i)) then None else Some (SOME w. w \<in> V \<and> (the (P i))\<rightarrow>w))" by (simp add: P_i(1))
          hence "P (Suc i) = Some (SOME w. w \<in> V \<and> (the (P i))\<rightarrow>w)" using no_deadend by auto
          hence "the (P (Suc i)) = (SOME w. w \<in> V \<and> (the (P i))\<rightarrow>w)" by (metis (no_types, lifting) option.sel)
          moreover have "\<exists>w. w \<in> V \<and> the (P i)\<rightarrow>w" by (metis P_Suc_i_simp1 option.discI w_def)
          ultimately show ?thesis by (metis (no_types, lifting) someI_ex)
        qed
      qed
      fix i show "P i \<noteq> None \<Longrightarrow> the (P i) \<in> V \<and> (P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i)))" proof (induct i)
        case 0 thus ?case using P_valid_start v0_def * by blast
      next
        case (Suc i) thus ?case using * by (meson DiffD1 P_simp)
      qed
    qed

    show P_conforms: "path_conforms_with_strategy p P \<sigma>" proof (unfold path_conforms_with_strategy_def; intro allI impI; elim conjE)
      fix i assume i_def: "P i \<noteq> None" "the (P i) \<in> VV p"
      show "\<sigma> (the (P i)) = P (Suc i)" by (simp add: i_def)
    qed

    show P_valid: "valid_path P" proof (unfold valid_path_def; intro conjI)
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

    show "maximal_path P" proof (unfold maximal_path_def; intro allI impI; elim conjE)
      fix i assume P_i: "P i \<noteq> None" and P_i_no_deadend: "\<not>deadend (the (P i))"
      show "P (Suc i) \<noteq> None" proof (cases)
        assume P_i_VV_p: "the (P i) \<in> VV p"
        hence "\<sigma> (the (P i)) \<noteq> None" using P_i_no_deadend strategy_on_def \<sigma>_dom by blast
        moreover have "P (Suc i) = \<sigma> (the (P i))" by (simp add: P_i P_i_VV_p)
        ultimately show "P (Suc i) \<noteq> None" by simp
      next
        assume "the (P i) \<notin> VV p"
        hence "P (Suc i) = Some (SOME w. w \<in> V \<and> (the (P i))\<rightarrow>w)" using P_i P_i_no_deadend P_simp by presburger
        thus "P (Suc i) \<noteq> None" by auto
      qed
    qed
  qed
*)

lemma paths_can_be_restricted:
  assumes \<sigma>'_valid: "valid_strategy p \<sigma>"
    and \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma>' \<sigma>"
    and P_valid: "valid_path P"
    and P_notNull: "\<not>lnull P"
    and P_conforms: "path_conforms_with_strategy_maximally p P \<sigma>"
  shows "\<exists>P'. \<not>lnull P' \<and> path_prefix P' P \<and> path_conforms_with_strategy_maximally p P' \<sigma>'"
proof-
  def [simp]: n_end \<equiv> "\<lambda>n. enat n < llength P \<and> P $ n \<in> VV p \<and> \<sigma>' (P $ n) = None"
  show ?thesis proof (cases)
    assume "\<exists>n. n_end n"
    then obtain n where n: "n_end n" "\<And>i. i < n \<Longrightarrow> \<not>n_end i" using obtain_min by blast
    def [simp]: P' \<equiv> "ltake (eSuc (enat n)) P"
    have P'_len: "llength P' = eSuc (enat n)" proof-
      have "llength P' = min (eSuc (enat n)) (llength P)" by simp
      moreover from n(1) have "eSuc (enat n) \<le> llength P" by (simp add: ileI1)
      ultimately show ?thesis by linarith
    qed
    have "\<not>lnull P'" by (simp add: P_notNull)
    moreover have P'_prefix_P: "path_prefix P' P" by simp
    moreover have "path_conforms_with_strategy_maximally p P' \<sigma>'" proof-
      {
        fix i assume i: "enat i < llength P'" "P' $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma>' (P' $ i) = Some w)"
        with n(1) P'_prefix_P have "i \<noteq> n" by (metis n_end_def option.distinct(1) path_prefix_included)
        with i(1) P'_len have "enat (Suc i) < llength P'" by auto
      }
      moreover have "\<exists>n. path_conforms_with_strategy_up_to p P' \<sigma>' n \<and> enat (Suc n) = llength P' \<and> P' $ n \<in> VV p \<and> \<sigma>' (P' $ n) = None" proof (intro exI conjI)
        show "path_conforms_with_strategy_up_to p P' \<sigma>' n" proof (unfold path_conforms_with_strategy_up_to_def, intro allI impI, elim conjE)
          fix i w assume i: "enat i < llength P'" "i < n" "P' $ i \<in> VV p" "\<sigma>' (P' $ i) = Some w"
          from i(4) \<sigma>_less_eq_\<sigma>' have "\<sigma> (P' $ i) = Some w" using strategy_less_eq_def by auto
          with i(1) P'_prefix_P have "\<sigma> (P $ i) = Some w" using path_prefix_included by fastforce
          moreover have "path_conforms_with_strategy_up_to p P \<sigma> (Suc i)" proof (cases "path_conforms_with_strategy p P \<sigma>")
            case True
            thus ?thesis using path_conforms_with_strategy_approximations2 by blast
          next
            case False
            then obtain m where m: "path_conforms_with_strategy_up_to p P \<sigma> m" "enat (Suc m) = llength P" "P $ m \<in> VV p" "\<sigma> (P $ m) = None"
              using P_conforms path_conforms_with_strategy_maximally_def by blast
            from m(4) \<sigma>_less_eq_\<sigma>' have "\<sigma>' (P $ m) = None" using strategy_less_eq_not_none by blast
            with m(2) m(3) have "n_end m" using n_end_def by (metis (full_types, hide_lams) enat_ord_simps(2) lessI)
            with n(2) have "n \<le> m" using le_less_linear by blast
            with `i < n` have "Suc i \<le> m" by presburger
            with m(1) show ?thesis using path_conforms_with_strategy_less_eq by blast
          qed
          moreover from i(1) P'_prefix_P have "enat i < llength P" using path_prefix_length by blast
          moreover have "i < Suc i" by simp
          moreover from i(1) i(3) P'_prefix_P have "P $ i \<in> VV p" by (metis lprefix_lnthD)
          ultimately have "enat (Suc i) < llength P \<and> P $ Suc i = w" using path_conforms_with_strategy_up_to_def by blast
          hence "P' $ Suc i = w" by (simp add: eSuc_enat i(2) lnth_ltake)
          with P'_len `i < n` show "enat (Suc i) < llength P' \<and> P' $ Suc i = w" by auto
        qed
        show "enat (Suc n) = llength P'" using P'_len eSuc_enat by auto
        have "P' $ n = P $ n" using n(1) n_end_def by (simp add: path_prefix_included)
        thus "P' $ n \<in> VV p" "\<sigma>' (P' $ n) = None" using n(1) n_end_def by auto
      qed
      ultimately show ?thesis using path_conforms_with_strategy_maximally_def by blast
    qed
    ultimately show ?thesis by blast
  next
    assume no_n_end: "\<not>(\<exists>n. n_end n)"
    have "path_conforms_with_strategy p P \<sigma>'" proof-
      {
        fix i w assume i: "enat i < llength P" "P $ i \<in> VV p" "\<sigma>' (P $ i) = Some w"
        from i(3) \<sigma>_less_eq_\<sigma>' have "\<sigma> (P $ i) = Some w"
          using strategy_less_eq_def by auto
        moreover from no_n_end \<sigma>_less_eq_\<sigma>' P_conforms
          have "path_conforms_with_strategy p P \<sigma>"
          by (metis n_end_def path_conforms_empty path_conforms_with_strategy_approximations path_conforms_with_strategy_maximally_def strategy_less_eq_not_none)
        ultimately have "enat (Suc i) < llength P \<and> P $ Suc i = w" using i(1) i(2) path_conforms_with_strategy_def by blast
      }
      thus ?thesis using path_conforms_with_strategy_def by blast
    qed
    moreover {
      fix i assume i: "enat i < llength P" "\<not>deadend (P $ i)" "P $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma>' (P $ i) = Some w)"
      from i(3) have "P $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (P $ i) = Some w)" using \<sigma>_less_eq_\<sigma>' strategy_less_eq_def by force
      with i(1) i(2) have "enat (Suc i) < llength P" using P_conforms path_conforms_with_strategy_maximally_def by blast
    }
    ultimately have "path_conforms_with_strategy_maximally p P \<sigma>'" using path_conforms_with_strategy_maximally_def by blast
    thus ?thesis using P_notNull by blast
  qed
qed

end -- "context ParityGame"

end
