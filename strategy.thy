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

(*definition restrict_path :: "'a Path \<Rightarrow> 'a set \<Rightarrow> 'a Path" (infixl "\<restriction>\<^sub>P" 80) where
  "restrict_path P W \<equiv> \<lambda>i. if the (P i) \<in> W then P i else None"
definition restrict_strategy :: "'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a Strategy" (infixl "\<restriction>\<^sub>S" 80) where
  "restrict_strategy \<sigma> W \<equiv> \<lambda>v. if v \<in> W \<and> the (\<sigma> v) \<in> W then \<sigma> v else None"

lemma restricted_strategy_invariant [simp]:
  assumes "v \<in> W" "the (\<sigma> v) \<in> W"
  shows "(\<sigma> \<restriction>\<^sub>S W) v = \<sigma> v"
  by (simp add: assms restrict_strategy_def)

lemma restricted_path_invariant [simp]:
  assumes "the (P i) \<in> W"
  shows "(P \<restriction>\<^sub>P W) i = P i"
  by (simp add: assms restrict_path_def)

lemma restricted_path_dom [simp]:
  assumes "i \<in> path_dom (P \<restriction>\<^sub>P W)"
  shows "i \<in> path_dom P"
  by (metis (mono_tags, lifting) assms mem_Collect_eq restrict_path_def)
*)

(* True iff \<sigma> is defined on all non-deadend nodes of the given player. *)
definition positional_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "positional_strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"

definition path_conforms_with_strategy :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy p P \<sigma> \<equiv> \<forall>i w. enat i < llength P \<and> P $ i \<in> VV p \<and> \<sigma> (P $ i) = Some w \<longrightarrow> enat (Suc i) < llength P \<and> P $ Suc i = w"
definition path_conforms_with_strategy_up_to :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> nat \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy_up_to p P \<sigma> n \<equiv> \<forall>i w. enat i < llength P \<and> i < n \<and> P $ i \<in> VV p \<and> \<sigma> (P $ i) = Some w \<longrightarrow> enat (Suc i) < llength P \<and> P $ Suc i = w"
lemma path_conforms_with_strategy_approximations:
  assumes "\<And>n. path_conforms_with_strategy_up_to p P \<sigma> n"
  shows "path_conforms_with_strategy p P \<sigma>"
proof (subst path_conforms_with_strategy_def, clarify)
  fix i v w assume "enat i < llength P" "P $ i \<in> VV p" "\<sigma> (P $ i) = Some w"
  thus "enat (Suc i) < llength P \<and> P $ Suc i = w" using assms[of "Suc i"] path_conforms_with_strategy_up_to_def by blast
qed
lemma path_conforms_with_strategy_approximations2:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy_up_to p P \<sigma> n" by simp
lemma path_conforms_with_strategy_less_eq:
  "path_conforms_with_strategy_up_to p P \<sigma> n \<Longrightarrow> m \<le> n \<Longrightarrow> path_conforms_with_strategy_up_to p P \<sigma> m" by simp
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

-- "Conform to \<sigma> as long as possible."
definition path_conforms_with_strategy_maximally :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy_maximally p P \<sigma> \<equiv> (path_conforms_with_strategy p P \<sigma>
      \<or> (\<exists>n. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat n < llength P \<and> P $ n \<in> VV p \<and> \<sigma> (P $ n) = None))
    \<and> (\<forall>i. enat i < llength P \<and> \<not>deadend (P $ i) \<and> (P $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (P $ i) = Some w)) \<longrightarrow> enat (Suc i) < llength P)"

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

lemma path_conforms_with_strategy_maximally_start:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and "P $ 0 = v0" "v0 \<in> VV p" "\<sigma> v0 = Some w"
    and P_notNull: "\<not>lnull P"
  shows "enat (Suc 0) < llength P \<and> \<sigma> v0 = Some (P $ Suc 0)"
  proof-
    have *: "P $ 0 \<in> VV p \<and> \<sigma> (P $ 0) = Some w" by (simp add: assms(2) assms(3) assms(4))
    { assume "path_conforms_with_strategy p P \<sigma>"
      moreover have "enat 0 < llength P" using P_notNull zero_enat_def by auto
      ultimately have "enat (Suc 0) < llength P \<and> P $ Suc 0 = w" using * path_conforms_with_strategy_def by blast
      hence ?thesis using assms(4) by blast
    }
    moreover
    { assume "\<exists>n v. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat n < llength P \<and> P $ n = v \<and> v \<in> VV p \<and> \<sigma> v = None"
      then obtain n v where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "enat n < llength P" "P $ n = v" "v \<in> VV p" "\<sigma> v = None" by blast
      have ?thesis proof (cases)
        assume "n = 0"
        thus ?thesis using assms(2) assms(4) n_def(2) n_def(3) n_def(5) by auto
      next
        assume "n \<noteq> 0"
        hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" using n_def(1) by simp
        hence "enat (Suc 0) < llength P \<and> P $ Suc 0 = w" unfolding path_conforms_with_strategy_up_to_def using * P_notNull zero_enat_def by auto
        thus ?thesis using assms(4) by blast
      qed
    }
    ultimately show ?thesis using assms(1) path_conforms_with_strategy_maximally_def by blast
  qed

lemma path_conforms_with_strategy_maximally_start_VVpstar:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and v: "P $ 0 \<in> VV p**" "\<not>deadend (P $ 0)" "\<not>lnull P"
  shows "enat (Suc 0) < llength P"
  proof-
    have "P $ 0 \<notin> VV p" using v(1) by auto
    moreover have "enat 0 < llength P" using v(3) zero_enat_def by auto
    ultimately show ?thesis using path_conforms_with_strategy_maximally_def assms(1) v(2) by metis
  qed

definition valid_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "valid_strategy p \<sigma> \<equiv> \<forall>v w. \<sigma> v = Some w \<longrightarrow> v \<in> VV p \<and> v\<rightarrow>w"
definition valid_strategy_from :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  "valid_strategy_from p \<sigma> v0 \<equiv> (\<forall>v w. \<sigma> v = Some w \<longrightarrow> v \<in> VV p \<and> v\<rightarrow>w)
    \<and> (\<forall>P n. enat n < llength P \<and> valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P $ n \<in> VV p \<and> \<not>deadend (P $ n)
        \<longrightarrow> (\<exists>w. \<sigma> (P $ n) = Some w))"

lemma valid_strategy_none_on_VVpstar: "valid_strategy p \<sigma> \<Longrightarrow> v \<notin> VV p \<Longrightarrow> \<sigma> v = None" by (metis not_None_eq valid_strategy_def)
lemma valid_strategy_none_on_VVpstar2: "valid_strategy p \<sigma> \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<sigma> v = None" by (metis DiffD2 Player.distinct(1) valid_strategy_none_on_VVpstar)
lemma valid_strategy_none_on_deadends: "valid_strategy p \<sigma> \<Longrightarrow> deadend v \<Longrightarrow> \<sigma> v = None" by (meson edges_are_in_V not_Some_eq valid_strategy_def)
lemma valid_empty_strategy: "valid_strategy p (\<lambda>_. None)" using valid_strategy_def by simp

lemma valid_strategy_updates:
  assumes "valid_strategy p \<sigma>" "v0 \<rightarrow> w0" "v0 \<in> VV p"
  shows "valid_strategy p (\<sigma>(v0 \<mapsto> w0))"
  proof-
    let ?\<sigma> = "\<sigma>(v0 \<mapsto> w0)"
    {
      fix v w assume *: "?\<sigma> v = Some w"
      hence "v \<in> VV p \<and> v \<rightarrow> w" using assms valid_strategy_def by (cases "v0 = v"; auto)
    }
    thus ?thesis using valid_strategy_def by blast
  qed

lemma strategy_subset [intro]:
  "\<lbrakk> W' \<subseteq> W; strategy_on p \<sigma> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'" using strategy_on_def by (simp add: strategy_on_def subset_iff)
lemma strategy_on_empty_set [simp]:
  "strategy_on p \<sigma> {}" by (simp add: strategy_on_def)
lemma strategy_only_on_empty_set_exists:
  "\<exists>\<sigma>. valid_strategy p \<sigma> \<and> strategy_only_on p \<sigma> {}"
  by (rule exI [of _ "\<lambda>_.None"]; simp add: valid_strategy_def strategy_only_on_def)
lemma strategy_only_on_on [intro]:
  "strategy_only_on p \<sigma> W \<Longrightarrow> strategy_on p \<sigma> W" by (simp add: strategy_on_def strategy_only_on_def)
lemma strategy_only_on_updates:
  assumes "strategy_only_on p \<sigma> W" "v0 \<in> VV p"
  shows "strategy_only_on p (\<sigma>(v0 \<mapsto> w0)) (W \<union> {v0})" proof-
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
  assumes "\<not>lfinite P" "path_conforms_with_strategy p P \<sigma>"
  shows "path_conforms_with_strategy p (ltl P) \<sigma>"
proof (unfold path_conforms_with_strategy_def, intro allI impI, elim conjE)
  fix i w assume i: "enat i < llength (ltl P)" "ltl P $ i \<in> VV p" "\<sigma> (ltl P $ i) = Some w"
  have *: "ltl P $ i = P $ Suc i" using assms(1) by (simp add: ltl_inf)
  from "*" have "P $ Suc i \<in> VV p" using i(2) by simp
  moreover from "*" have "\<sigma> (P $ Suc i) = Some w" using i(3) by simp
  moreover have "enat (Suc (Suc i)) < llength P" by (simp add: assms(1) not_lfinite_llength)
  ultimately have "enat (Suc (Suc i)) < llength P \<and> P $ Suc (Suc i) = w" using assms(2) path_conforms_with_strategy_def by (metis Suc_ile_eq order.strict_implies_order)
  thus "enat (Suc i) < llength (ltl P) \<and> ltl P $ Suc i = w" using assms(1) ltl_inf by (metis enat_ord_code(4) lfinite_ltl llength_eq_infty_conv_lfinite)
qed

lemma path_tail_conforms_suc:
  assumes "\<not>lnull P" "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)"
  shows "path_conforms_with_strategy_up_to p (ltl P) \<sigma> n"
proof-
  let ?P = "ltl P"
  { fix i w assume i: "enat i < llength ?P" "i < n" "?P $ i \<in> VV p" "\<sigma> (?P $ i) = Some w"
    have "enat (Suc i) < llength P" by (metis i(1) ldrop_eSuc_ltl leD leI lnull_ldropn)
    moreover have "Suc i < Suc n" using i(2) by simp
    moreover have "P $ Suc i \<in> VV p" using assms(1) i(3) lnth_ltl by force
    moreover have "\<sigma> (P $ Suc i) = Some w" using assms(1) i(4) lnth_ltl by fastforce
    ultimately have "enat (Suc (Suc i)) < llength P \<and> P $ Suc (Suc i) = w" using assms(2) path_conforms_with_strategy_up_to_def by blast
    hence "enat (Suc i) < llength ?P \<and> ?P $ Suc i = w" by (simp add: assms(1) enat_Suc_ltl lnth_ltl)
  }
  thus ?thesis unfolding path_conforms_with_strategy_up_to_def by blast
qed

lemma infinite_path_tail_head [simp]:
  assumes "\<not>lnull P" "P $ 0 \<in> VV p" "\<sigma> (P $ 0) = Some w" "path_conforms_with_strategy p P \<sigma>"
  shows "enat (Suc 0) < llength P \<and> P $ Suc 0 = w"
proof-
  have "enat 0 < llength P" using assms(1) zero_enat_def by auto
  thus ?thesis using assms unfolding path_conforms_with_strategy_def by blast
qed

lemma path_conforms_with_strategy_maximally_tail:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and "\<not>lnull P" "P $ 0 = v0" "\<sigma> v0 = Some w0"
  shows "path_conforms_with_strategy_maximally p (ltl P) \<sigma>"
proof-
  let ?P = "ltl P"

  (* Helper lemma to prove the second conjunct of path_conforms_with_strategy_maximally. *)
  { fix i assume i: "enat i < llength (ltl P)" "\<not>deadend (ltl P $ i)" "ltl P $ i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (ltl P $ i) = Some w)"
    have "enat (Suc i) < llength P" proof-
      have "enat i < epred (llength P)" using i(1) by (simp add: epred_llength)
      hence "eSuc (enat i) < llength P" by (metis epred_eSuc epred_le_epredI leD leI)
      thus ?thesis by (simp add: eSuc_enat)
    qed
    moreover have "\<not>deadend (P $ Suc i)" using assms(2) i(2) lnth_ltl by fastforce
    moreover have "P $ Suc i \<in> VV p \<longrightarrow> (\<exists>w. \<sigma> (P $ Suc i) = Some w)" using assms(2) i(3) lnth_ltl by force
    ultimately have "enat (Suc i) < llength (ltl P)" using assms(1) path_conforms_with_strategy_maximally_def enat_Suc_ltl by blast
  } note * = this

  let ?A = "path_conforms_with_strategy p P \<sigma>"
  let ?B = "\<exists>n v. path_conforms_with_strategy_up_to p P \<sigma> n \<and> enat n < llength P \<and> P $ n = v \<and> P $ n \<in> VV p \<and> \<sigma> v = None"
  show ?thesis proof (cases)
    assume ?A
    hence "path_conforms_with_strategy p ?P \<sigma>" using infinite_path_tail_conforms
      by (meson assms(2) path_conforms_with_strategy_approximations path_conforms_with_strategy_approximations2 path_tail_conforms_suc)
    thus ?thesis using * path_conforms_with_strategy_maximally_def by blast
  next
    assume "\<not>?A"
    hence "?B" using assms(1) path_conforms_with_strategy_maximally_def by metis
    then obtain n v where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "enat n < llength P" "P $ n = v" "v \<in> VV p" "\<sigma> v = None" by blast
    have "\<sigma> v0 \<noteq> None" using assms(4) by simp
    hence "n \<noteq> 0" by (metis assms(3) n_def(3) n_def(5))
    then obtain m where "Suc m = n" by (metis nat.exhaust)
    hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc m) \<and> enat (Suc m) < llength P \<and> P $ Suc m = v \<and> v \<in> VV p \<and> \<sigma> v = None"
      using n_def by metis
    moreover hence "path_conforms_with_strategy_up_to p ?P \<sigma> m" using path_tail_conforms_suc assms(2) by blast
    ultimately have "\<exists>n v. path_conforms_with_strategy_up_to p ?P \<sigma> n \<and> enat n < llength ?P \<and> ?P $ n = v \<and> v \<in> VV p \<and> \<sigma> v = None"
      using assms(2) enat_Suc_ltl lnth_ltl by blast
    thus ?thesis using * path_conforms_with_strategy_maximally_def by blast
  qed
qed

(*
lemma path_conforms_with_strategy_maximally:
  assumes P_conforms: "path_conforms_with_strategy_maximally p P (\<sigma>(v \<mapsto> w))"
    and P: "P 0 = Some v" and v: "v \<in> VV p" "v\<rightarrow>w" and \<sigma>: "\<sigma> v = None"
  shows "\<exists>P'. path_conforms_with_strategy_maximally p P' \<sigma>
    \<and> P (Suc 0) = P' 0
    \<and> ((\<exists>n. P' n = Some v \<and> (\<forall>i \<le> n. P' i = P (Suc i))) \<or> (\<forall>i. P' i = P (Suc i)))"
  proof (cases "\<exists>n > 0. P n = Some v")
    case True
    def good \<equiv> "\<lambda>n. n > 0 \<and> P n = Some v"
    have "\<exists>n. good n" using good_def True by blast
    then obtain n where *: "good n \<and> (\<forall>m < n. \<not>good m)" by (metis (full_types) ex_least_nat_le gr_implies_not0)
    have 1: "n > 0" using * good_def by blast
    have 2: "P n = Some v" using * good_def by blast
    let ?P' = "\<lambda>i. if i \<le> n then P (Suc i) else None"
    show ?thesis sorry
  next
    case False
    hence no_v: "\<forall>n > 0. P n \<noteq> Some v" by blast
    let ?P' = "path_tail P"
    have "path_conforms_with_strategy_maximally p ?P' \<sigma>" proof (cases "path_conforms_with_strategy p P (\<sigma>(v \<mapsto> w))")
      case True
      hence "path_conforms_with_strategy p ?P' \<sigma>" proof-
        { fix i assume "?P' i \<noteq> None" "the (?P' i) \<in> VV p"
          hence "P (Suc i) \<noteq> None \<and> the (P (Suc i)) \<in> VV p" by blast
          moreover hence "(\<sigma>(v \<mapsto> w))(the (P (Suc i))) = P (Suc (Suc i))" using True path_conforms_with_strategy_def by blast
          moreover have "P (Suc i) \<noteq> Some v" using no_v by blast
          ultimately have "\<sigma> (the (?P' i)) = ?P' (Suc i)" by (metis fun_upd_other option.collapse)
        }
        thus ?thesis using path_conforms_with_strategy_def by blast
      qed
      thus ?thesis using path_conforms_with_strategy_maximally_def by blast
    next
      case False
      def good \<equiv> "\<lambda>n. path_conforms_with_strategy_up_to p P (\<sigma>(v \<mapsto> w)) n \<and> P n \<noteq> None \<and> (\<sigma>(v \<mapsto> w)) (the (P n)) = None"
      have "\<exists>n. good n" using good_def path_conforms_with_strategy_maximally_def P_conforms False by blast
      then obtain n where *: "good n \<and> (\<forall>m < n. \<not>good m)" by (metis (full_types) ex_least_nat_le gr_implies_not0)
      have 1: "path_conforms_with_strategy_up_to p P (\<sigma>(v \<mapsto> w)) n" using * good_def by blast
      have 2: "P n \<noteq> None" using * good_def by blast
      have 3: "(\<sigma>(v \<mapsto> w))(the (P n)) = None" using * good_def by blast
      have "n \<noteq> 0" by (metis "3" P fun_upd_apply option.distinct(1) option.sel)
      then obtain m where m_def: "n = Suc m" using nat.exhaust by auto
      have "path_conforms_with_strategy_up_to p ?P' \<sigma> m" proof-
        { fix i assume "i < m" and P: "?P' i \<noteq> None" "the (?P' i) \<in> VV p"
          have "the (?P' i) \<noteq> v" by (metis P(1) no_v option.collapse zero_less_Suc)
          moreover have "(\<sigma>(v \<mapsto> w)) (the (?P' i)) = ?P' (Suc i)"
            using 1 path_conforms_with_strategy_up_to_def by (metis P(1) P(2) Suc_mono `i < m` m_def)
          ultimately have "\<sigma> (the (?P' i)) = ?P' (Suc i)" by simp
        }
        thus ?thesis using path_conforms_with_strategy_up_to_def by blast
      qed
      moreover have "?P' m \<noteq> None" using 2 m_def by blast
      moreover have "\<sigma> (the (?P' m)) = None" using 3 m_def by (metis fun_upd_def option.distinct(2))
      ultimately have "\<exists>n. path_conforms_with_strategy_up_to p ?P' \<sigma> n \<and> ?P' n \<noteq> None \<and> \<sigma> (the (?P' n)) = None" by blast
      thus ?thesis using path_conforms_with_strategy_maximally_def by blast
    qed
    moreover have "P (Suc 0) = ?P' 0" by simp
    moreover have "\<forall>i. ?P' i = P (Suc i)" by blast
    ultimately show ?thesis by blast
  qed
*)

definition strategy_less_eq :: "'a Strategy \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy_less_eq \<sigma> \<sigma>' \<equiv> \<forall>v w. \<sigma> v = Some w \<longrightarrow> \<sigma> v = \<sigma>' v"
abbreviation "strategy_less \<equiv> \<lambda>\<sigma> \<sigma>'. strategy_less_eq \<sigma> \<sigma>' \<and> \<sigma> \<noteq> \<sigma>'"

lemma strategy_less_eq_not_none:
  assumes "\<And>v. \<sigma> v \<noteq> None \<Longrightarrow> \<sigma>' v = \<sigma> v"
  shows "strategy_less_eq \<sigma> \<sigma>'"
  by (simp add: assms strategy_less_eq_def)

lemma strategy_less_eq_not_none2:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "\<sigma> v \<noteq> None"
  shows "\<sigma>' v \<noteq> None"
  proof-
    have "\<exists>w. \<sigma> v = Some w" using assms(2) by blast
    hence "\<sigma> v = \<sigma>' v" using assms(1) strategy_less_eq_def by blast
    thus ?thesis using assms(2) by presburger
  qed

lemma strategy_less_eq_updates:
  assumes "\<sigma> v = None"
  shows "strategy_less_eq \<sigma> (\<sigma>(v \<mapsto> w))"
  by (metis assms fun_upd_other option.distinct(1) strategy_less_eq_def)
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
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_less_eq \<sigma>' \<sigma>''"
  shows "strategy_less_eq \<sigma> \<sigma>''" by (unfold strategy_less_eq_def; metis assms strategy_less_eq_def)
lemma strategy_less_eq_refl [simp]:
  "strategy_less_eq \<sigma> \<sigma>" by (simp add: option.case_eq_if strategy_less_eq_def)

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

lemma strategy_less_eq_least [simp]:
  "strategy_only_on p \<sigma> {} \<Longrightarrow> strategy_less_eq \<sigma> \<sigma>'" by (simp add: strategy_less_eq_def strategy_only_on_elements)
lemma strategy_less_eq_extensible:
  assumes "W \<subseteq> W'" "strategy_on p \<sigma> W" "valid_strategy p \<sigma>"
  shows "\<exists>\<sigma>'. valid_strategy p \<sigma>' \<and> strategy_less_eq \<sigma> \<sigma>' \<and> strategy_on p \<sigma>' W'" proof-
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
    moreover have "valid_strategy p \<sigma>'" proof-
      {
        fix v w assume v_def: "\<sigma>' v = Some w"
        have "v \<in> VV p \<and> v \<rightarrow> w" proof (cases)
          assume assm: "\<sigma> v = None"
          have "v \<in> VV p" by (metis \<sigma>'_def assm option.distinct(1) v_def)
          have "\<sigma>' v = Some (SOME w. v\<rightarrow>w)" using assm v_def by (metis \<sigma>'_def option.distinct(1))
          hence *: "w = (SOME w. v\<rightarrow>w)" by (metis option.sel v_def)
          have "\<not>deadend v" using v_def `\<sigma> v = None` by (metis \<sigma>'_def option.distinct(1))
          hence "\<exists>w. v\<rightarrow>w" by auto
          thus ?thesis using * `v \<in> VV p` by (metis (mono_tags, lifting) someI)
        next
          assume assm: "\<sigma> v \<noteq> None"
          then obtain w' where w'_def: "\<sigma> v = Some w'" by blast
          have "v \<in> VV p \<and> v \<rightarrow> w'" using assms(3) valid_strategy_def by (metis w'_def)
          moreover have "w = w'" by (metis assm w'_def option.inject v_def \<sigma>'_def)
          ultimately show ?thesis by blast
        qed
      }
      thus ?thesis using valid_strategy_def by blast
    qed
    ultimately show ?thesis by blast
  qed
lemma strategy_only_on_extensible:
  assumes "valid_strategy p \<sigma>" "strategy_only_on p \<sigma> W'" "W' \<subseteq> W"
  shows "\<exists>\<sigma>'. valid_strategy p \<sigma>' \<and> strategy_less_eq \<sigma> \<sigma>' \<and> strategy_only_on p \<sigma>' W" proof-
    let ?\<sigma>' = "\<lambda>v. if \<sigma> v \<noteq> None then \<sigma> v else if v \<in> W \<inter> VV p \<and> \<not>deadend v then Some (SOME w. v\<rightarrow>w) else None"
    have "valid_strategy p ?\<sigma>'" proof-
      { fix v w assume v: "?\<sigma>' v = Some w"
        hence "v \<in> VV p \<and> v\<rightarrow>w" proof (cases "\<sigma> v \<noteq> None")
          case True
          have "\<sigma> v = ?\<sigma>' v" by (simp add: True)
          thus "v \<in> VV p \<and> v\<rightarrow>w" using assms(1) v valid_strategy_def by (metis (no_types, lifting))
        next
          case False
          hence *: "v \<in> W \<inter> VV p \<and> \<not>deadend v" using v by (metis option.distinct(2))
          hence "\<exists>w. v\<rightarrow>w" by blast
          hence "v\<rightarrow>(SOME w. v\<rightarrow>w)" by (meson someI_ex)
          hence "v\<rightarrow>the (Some (SOME w. v\<rightarrow>w))" by auto
          moreover have "v \<in> VV p" using * by simp
          ultimately show ?thesis using False v by (metis option.distinct(1) option.sel)
        qed
      }
      thus ?thesis using valid_strategy_def by blast
    qed
    moreover have "strategy_only_on p ?\<sigma>' W" proof (unfold strategy_only_on_def; intro allI)
      fix v
      have "v \<in> W \<inter> VV p \<and> \<not>deadend v \<longrightarrow> (\<exists>w. ?\<sigma>' v = Some w)" (is ?A) by (metis option.collapse)
      moreover have "v \<notin> W \<inter> VV p \<longrightarrow> ?\<sigma>' v = None" (is ?B) proof (clarify)
        fix v assume assm: "v \<notin> W \<inter> VV p"
        hence "v \<notin> W' \<inter> VV p" using assms(3) by blast
        hence "\<sigma> v = None" using assms(2) strategy_only_on_def by blast
        thus "?\<sigma>' v = None" using assm by auto
      qed
      ultimately show "?A \<and> ?B" by blast
    qed
    moreover have "strategy_less_eq \<sigma> ?\<sigma>'" using strategy_less_eq_not_none by presburger
    ultimately show ?thesis using strategy_only_on_def by blast
  qed

(*
lemma restricted_strategy_paths:
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

lemma restricted_strategy_paths_inv:
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

(*

definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v \<equiv> \<forall>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) = v \<longrightarrow> winning_path p P"

definition strategy_attracts_from_to :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_from_to p \<sigma> A W \<equiv> (\<forall>P.
      valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) \<in> A
    \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))"
lemma strategy_attracts_from_to_trivial [simp]:
  "strategy_attracts_from_to p \<sigma> W W" by (meson strategy_attracts_from_to_def valid_paths_are_nonempty)
definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv> (\<forall>P n v0.
      valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P 0 = Some v0 \<and> v0 \<in> A
    \<longrightarrow> (\<forall>i v. i \<le> n \<and> P i = Some v \<longrightarrow> v \<notin> W))"
lemma strategy_avoids_trivial [simp]:
  "strategy_avoids p \<sigma> {} W" by (meson empty_iff strategy_avoids_def)
lemma strategy_avoids_directly:
  assumes "strategy_avoids p \<sigma> A W" "v0 \<in> A" "v0 \<in> VV p" "\<sigma> v0 = Some w0" "valid_strategy p \<sigma>"
  shows "w0 \<notin> W"
  proof (rule ccontr; simp)
    assume assm: "w0 \<in> W"
    obtain P where P: "valid_path P" "finite_path P" "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" "P 0 = Some v0" using one_step_path_exists assms by blast
    have "v0 \<in> A" using P(4) assms(2) by simp
    hence "\<And>i v. i \<le> Suc 0 \<and> P i = Some v \<longrightarrow> v \<notin> W" using assms(1) strategy_avoids_def P by blast
    hence "\<And>v. P (Suc 0) = Some v \<longrightarrow> v \<notin> W" by blast
    moreover have "v0 \<in> VV p" by (simp add: P(4) assms(3))
    ultimately show False
      by (metis P(3) P(4) assm assms(4) lessI path_conforms_with_strategy_up_to_def)
  qed
lemma strategy_avoids_strongly:
  assumes "strategy_avoids p \<sigma> A W"
    and P_conforms: "path_conforms_with_strategy p P \<sigma>"
    and "valid_path P" "P 0 = Some v0" "v0 \<in> A" "P n = Some v"
  shows "v \<notin> W"
  proof-
    have "path_conforms_with_strategy_up_to p P \<sigma> n" using P_conforms path_conforms_with_strategy_approximations2 by blast
    hence "\<forall>i v. i \<le> n \<and> P i = Some v \<longrightarrow> v \<notin> W" using assms strategy_avoids_def by blast
    thus ?thesis using Suc_n_not_le_n assms(6) linear by blast
  qed

lemma path_conforms_preserved_under_extension:
  assumes \<sigma>_valid: "valid_strategy_from p \<sigma> v0"
    and \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> \<sigma>'"
    and P_valid: "valid_path P"
    and P_conforms: "path_conforms_with_strategy p P \<sigma>'"
    and P_valid_start: "P 0 = Some v0"
  shows "path_conforms_with_strategy p P \<sigma>"
  proof (unfold path_conforms_with_strategy_def; intro allI impI; elim conjE)
    fix i v
    assume P: "P i = Some v" "v \<in> VV p"
    show "\<sigma> v = P (Suc i)" proof (cases)
      assume deadend: "deadend v"
      hence "P (Suc i) = None" by (meson P_valid P(1) valid_path_ends_on_deadend)
      moreover have "\<sigma> v = None" proof (rule ccontr)
        assume "\<sigma> v \<noteq> None"
        then obtain w where "\<sigma> v = Some w" by blast
        hence "v\<rightarrow>w" using valid_strategy_from_def \<sigma>_valid P(2) by blast
        thus False using deadend using valid_edge_set by auto
      qed
      ultimately show ?thesis by simp
    next
      assume no_deadend: "\<not>deadend v"
      hence \<sigma>'_next: "\<sigma>' v = P (Suc i)" using P_conforms P path_conforms_with_strategy_def by blast
      {
        fix n
        have "path_conforms_with_strategy_up_to p P \<sigma> n" proof (induct n)
          case 0 thus ?case unfolding path_conforms_with_strategy_up_to_def by blast
        next
          case (Suc n)
          show ?case proof (cases)
            assume "P n = None" thus ?thesis using path_conforms_empty by (meson P_valid Suc.hyps le_eq_less_or_eq lessI)
          next
            assume "P n \<noteq> None"
            then obtain v where v_def: "P n = Some v" by blast
            show "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)" proof (cases)
              assume assm: "v \<in> VV p \<and> \<not>deadend v"
              hence "\<sigma> v \<noteq> None" using v_def \<sigma>_valid P_valid P_conforms P_valid_start valid_strategy_from_def Suc.hyps by blast
              hence "\<sigma> v = \<sigma>' v" using \<sigma>_less_eq_\<sigma>' using strategy_less_eq_def by blast
              moreover have "\<sigma>' v = P (Suc n)" using v_def P_conforms assm path_conforms_with_strategy_def by blast
              ultimately have *: "\<sigma> v = P (Suc n)" by simp
              show ?thesis proof (unfold path_conforms_with_strategy_up_to_def; intro allI impI)
                fix i v' assume i_def: "i < Suc n \<and> P i = Some v' \<and> v' \<in> VV p"
                show "\<sigma> v' = P (Suc i)" proof (cases)
                  assume "i < n"
                  hence "P i = Some v' \<Longrightarrow> v' \<in> VV p \<Longrightarrow> \<sigma> v' = P (Suc i)" using Suc.hyps path_conforms_with_strategy_up_to_def by blast
                  thus ?thesis using i_def by blast
                next
                  assume "\<not>i < n"
                  hence "i = n" using i_def by auto
                  thus ?thesis using * by (metis i_def option.sel v_def)
                qed
              qed
            next
              assume "\<not>(v \<in> VV p \<and> \<not>deadend v)"
              moreover { assume "v \<notin> VV p" hence ?thesis using Suc.hyps path_conforms_up_to_VVpstar v_def by blast }
              moreover { assume "deadend v" hence ?thesis using P_valid Suc.hyps \<sigma>_valid path_conforms_up_to_deadends v_def by blast }
              ultimately show ?thesis by blast
            qed
          qed
        qed
      }
      hence "path_conforms_with_strategy p P \<sigma>" using path_conforms_with_strategy_approximations by blast
      thus ?thesis using P(1) P(2) path_conforms_with_strategy_def by blast
    qed
  qed

lemma winning_strategy_preserved_under_extension:
  assumes \<sigma>_valid: "valid_strategy_from p \<sigma> v0"
    and \<sigma>_winning: "winning_strategy p \<sigma> v0"
    and \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> \<sigma>'"
  shows "winning_strategy p \<sigma>' v0"
  using assms path_conforms_preserved_under_extension winning_strategy_def valid_paths_are_nonempty
  by (metis option.collapse)

lemma valid_strategy_is_valid_strategy_from:
  assumes \<sigma>_valid: "valid_strategy p \<sigma>"
    and \<sigma>_only_on: "strategy_on p \<sigma> A"
    and \<sigma>_avoids: "strategy_avoids p \<sigma> A (V - A)"
    and v0_def: "v0 \<in> A"
  shows "valid_strategy_from p \<sigma> v0"
  proof (unfold valid_strategy_from_def; intro conjI)
    show "\<forall>v w. \<sigma> v = Some w \<longrightarrow> v \<in> VV p \<and> v\<rightarrow>w" using \<sigma>_valid valid_strategy_def by blast
    show "\<forall>P n v. valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> P 0 = Some v0 \<and> P n = Some v \<and> v \<in> VV p \<and> \<not>deadend v \<longrightarrow> (\<exists>w. \<sigma> v = Some w)"
      proof (intro allI impI; elim conjE)
      fix P n v
      assume P_valid: "valid_path P"
        and P_conforms_up_to_n: "path_conforms_with_strategy_up_to p P \<sigma> n"
        and P_valid_start: "P 0 = Some v0"
        and P_Suc_n_not_None: "P n = Some v"
        and P_Suc_n_in_VV_p: "v \<in> VV p"
        and P_Suc_n_no_deadend: "\<not>deadend v"
      have *: "\<And>i v. i < n \<Longrightarrow> P i = Some v \<Longrightarrow> v \<in> VV p \<Longrightarrow> \<sigma> v = P (Suc i)" using path_conforms_with_strategy_up_to_def P_conforms_up_to_n by blast
      have P_n_not_None: "P n \<noteq> None" using P_Suc_n_not_None P_valid valid_path_is_contiguous_suc by blast
      have "\<forall>i v. i \<le> n \<and> P i = Some v \<longrightarrow> v \<notin> (V - A)" using \<sigma>_avoids strategy_avoids_def P_valid P_conforms_up_to_n P_valid_start v0_def by metis
      hence "v \<notin> (V - A)" using P_Suc_n_not_None by blast
      hence "v \<in> A" using P_Suc_n_in_VV_p by blast
      hence "v \<in> A \<inter> VV p" using P_Suc_n_in_VV_p by blast
      thus "\<exists>w. \<sigma> v = Some w" using \<sigma>_only_on P_Suc_n_no_deadend strategy_on_def by blast
    qed
  qed
lemma valid_strategy_is_valid_strategy_from_V:
  assumes \<sigma>_valid: "valid_strategy p \<sigma>"
    and \<sigma>_on: "strategy_on p \<sigma> V"
    and v0_def: "v0 \<in> V"
  shows "valid_strategy_from p \<sigma> v0"
  by (metis Diff_cancel \<sigma>_on \<sigma>_valid empty_iff strategy_avoids_def v0_def valid_strategy_is_valid_strategy_from)

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
  shows "\<exists>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P 0 = Some v0"
  sorry
(* temporarily commented out
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

*)

lemma paths_can_be_restricted:
  assumes \<sigma>'_valid: "valid_strategy p \<sigma>"
    and \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma>' \<sigma>"
    and P_valid: "valid_path P"
    and P_conforms: "path_conforms_with_strategy_maximally p P \<sigma>"
  shows "\<exists>P'. \<not>lnull P' \<and> path_prefix P' P \<and> path_conforms_with_strategy_maximally p P' \<sigma>'"
  sorry

end -- "context ParityGame"

end
