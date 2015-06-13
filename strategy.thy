theory strategy
imports
  Main
  parity_game
begin

type_synonym 'a Strategy = "'a \<Rightarrow> 'a option"

context ParityGame begin

definition strategy_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_on p \<sigma> W \<equiv> \<forall>v \<in> W \<inter> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None"
definition strategy_only_on :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_only_on p \<sigma> W \<equiv> (\<forall>v \<in> W \<inter> VV p. \<not>deadend v \<longrightarrow> \<sigma> v \<noteq> None) \<and> (\<forall>v. v \<notin> W \<inter> VV p \<longrightarrow> \<sigma> v = None)"

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
  [simp]: "path_conforms_with_strategy p P \<sigma> \<equiv> (\<forall>i. P i \<noteq> None \<and> the (P i) \<in> VV p \<longrightarrow> \<sigma> (the (P i)) = P (Suc i))"
definition path_conforms_with_strategy_up_to :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> nat \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy_up_to p P \<sigma> n \<equiv> (\<forall>i < n. P i \<noteq> None \<and> the (P i) \<in> VV p \<longrightarrow> \<sigma> (the (P i)) = P (Suc i))"
lemma path_conforms_with_strategy_approximations:
  "(\<And>n. path_conforms_with_strategy_up_to p P \<sigma> n) \<Longrightarrow> path_conforms_with_strategy p P \<sigma>" by fastforce
lemma path_conforms_with_strategy_approximations2:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy_up_to p P \<sigma> n" by simp
lemma path_conforms_with_strategy_less_eq:
  "path_conforms_with_strategy_up_to p P \<sigma> n \<Longrightarrow> m \<le> n \<Longrightarrow> path_conforms_with_strategy_up_to p P \<sigma> m" by fastforce
lemma path_conforms_up_to_VVpstar:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> n" "the (P n) \<notin> VV p"
  shows "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)" using assms less_Suc_eq by auto

-- "Conform to \<sigma> as long as possible."
definition path_conforms_with_strategy_maximally :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  [simp]: "path_conforms_with_strategy_maximally p P \<sigma> \<equiv> path_conforms_with_strategy p P \<sigma>
    \<or> (\<exists>n. path_conforms_with_strategy_up_to p P \<sigma> n \<and> P n \<noteq> None \<and> \<sigma> (the (P n)) = None)"

lemma path_conforms_with_strategy_maximally_start:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and "P 0 \<noteq> None" "the (P 0) \<in> VV p" "\<sigma> (the (P 0)) \<noteq> None"
  shows "\<sigma> (the (P 0)) = P (Suc 0)"
  proof-
    { assume "path_conforms_with_strategy p P \<sigma>"
      hence ?thesis using assms(2) assms(3) path_conforms_with_strategy_def by blast
    }
    moreover
    { assume "\<exists>n. path_conforms_with_strategy_up_to p P \<sigma> n \<and> P n \<noteq> None \<and> \<sigma> (the (P n)) = None"
      then obtain n where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "P n \<noteq> None" "\<sigma> (the (P n)) = None" by blast
      have ?thesis proof (cases)
        assume "n = 0"
        thus ?thesis using assms(4) n_def(3) by blast
      next
        assume "n \<noteq> 0"
        hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" using n_def(1) by simp
        thus ?thesis using assms(2) assms(3) path_conforms_with_strategy_up_to_def by blast
      qed
    }
    ultimately show ?thesis using assms(1) path_conforms_with_strategy_maximally_def by blast
  qed

definition valid_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "valid_strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<sigma> v \<noteq> None \<longrightarrow> v\<rightarrow>the (\<sigma> v)"
definition valid_strategy_from :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  "valid_strategy_from p \<sigma> v0 \<equiv> (\<forall>v \<in> VV p. \<sigma> v \<noteq> None \<longrightarrow> v\<rightarrow>the (\<sigma> v))
    \<and> (\<forall>P n. valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> the (P 0) = v0
        \<and> P n \<noteq> None \<and> the (P n) \<in> VV p \<and> \<not>deadend (the (P n))
        \<longrightarrow> \<sigma> (the (P n)) \<noteq> None)"

lemma valid_strategy_updates:
  assumes "valid_strategy p \<sigma>" "v \<rightarrow> w"
  shows "valid_strategy p (\<sigma>(v \<mapsto> w))"
  proof-
    {
      fix u assume "u \<in> VV p" "(\<sigma>(v \<mapsto> w)) u \<noteq> None"
      hence "valid_strategy p (\<sigma>(v \<mapsto> w))" apply (cases "v = u") using assms valid_strategy_def by auto
    }
    thus ?thesis using valid_strategy_def by blast
  qed

lemma strategy_subset [intro]:
  "\<lbrakk> W' \<subseteq> W; strategy_on p \<sigma> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'" using strategy_on_def by auto
lemma strategy_on_empty_set [simp]:
  "strategy_on p \<sigma> {}" by (simp add: strategy_on_def)
lemma strategy_only_on_empty_set_exists:
  "\<exists>\<sigma>. valid_strategy p \<sigma> \<and> strategy_only_on p \<sigma> {}"
  by (rule exI [of _ "\<lambda>_.None"]; simp add: valid_strategy_def strategy_only_on_def)
lemma strategy_only_on_on [intro]:
  "strategy_only_on p \<sigma> W \<Longrightarrow> strategy_on p \<sigma> W" by (simp add: strategy_on_def strategy_only_on_def)
lemma strategy_only_on_on_subset [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; W' \<subseteq> W \<rbrakk> \<Longrightarrow> strategy_on p \<sigma> W'" by (simp add: strategy_only_on_on strategy_subset)
lemma strategy_only_on_elements [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<notin> W \<rbrakk> \<Longrightarrow> \<sigma> v = None" using strategy_only_on_def by auto
lemma strategy_only_on_case_rule [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<in> VV p - W; v\<rightarrow>w \<rbrakk> \<Longrightarrow> strategy_only_on p (\<sigma>(v \<mapsto> w)) (insert v W)" using strategy_only_on_def by auto
lemma strategy_only_on_case_rule2 [intro]:
  "\<lbrakk> strategy_only_on p \<sigma> W; v \<notin> VV p \<rbrakk> \<Longrightarrow> strategy_only_on p \<sigma> (insert v W)" using strategy_only_on_def by auto
lemma valid_strategy_in_V:
  "\<lbrakk> valid_strategy p \<sigma>; v \<in> VV p; \<sigma> v \<noteq> None \<rbrakk> \<Longrightarrow> the (\<sigma> v) \<in> V" using assms valid_edge_set valid_strategy_def by auto
lemma valid_strategy_from_is_valid_strategy [intro]:
  "valid_strategy_from p \<sigma> v0 \<Longrightarrow> valid_strategy p \<sigma>" using valid_strategy_def valid_strategy_from_def by simp

lemma path_conforms_up_to_deadends:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> n" "valid_path P" "valid_strategy p \<sigma>" "deadend (the (P n))"
  shows "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)" proof-
    {
      assume VVp: "the (P n) \<in> VV p"
      have "\<forall>v \<in> VV p. \<sigma> v \<noteq> None \<longrightarrow> v\<rightarrow>the (\<sigma> v)" using assms(3) valid_strategy_def by blast
      hence "\<sigma> (the (P n)) \<noteq> None \<longrightarrow> the (P n)\<rightarrow>the (\<sigma> (the (P n)))" using VVp by blast
      hence "\<sigma> (the (P n)) = None" using assms(4) using valid_edge_set by auto
      { assume "P n \<noteq> None" "the (P n) \<in> VV p"
        hence "\<sigma> (the (P n)) = P (Suc n)" by (metis `\<sigma> (the (P n)) = None` assms(2) assms(4) valid_path_def)
      }
      hence ?thesis using assms(1) by (simp add: less_Suc_eq)
    }
    moreover { assume "the (P n) \<notin> VV p" hence ?thesis using assms(1) path_conforms_up_to_VVpstar by blast }
    ultimately show ?thesis by blast
  qed

lemma one_step_path_exists:
  assumes "v0 \<in> V" "valid_strategy p \<sigma>"
  shows "\<exists>P. valid_path P \<and> finite_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> (Suc 0) \<and> the (P 0) = v0"
  proof (rule exI; intro conjI)
    def P \<equiv> "\<lambda>i :: nat. if i = 0 then Some v0 else (if i = 1 \<and> v0\<rightarrow>the (\<sigma> v0) then \<sigma> v0 else None)"
    show "finite_path P" unfolding P_def finite_path_def by (metis One_nat_def Suc_lessI less_imp_Suc_add less_numeral_extra(4) nat.distinct(1) not_gr0 option.distinct(1))
    show "valid_path P" proof (unfold valid_path_def; intro conjI)
      show "P 0 \<noteq> None" by (simp add: P_def)
      show "infinite_path P \<or> finite_path P" using `finite_path P` by blast
      show "\<forall>i. P i \<noteq> None \<longrightarrow> the (P i) \<in> V" using P_def assms valid_edge_set by auto
      show "\<forall>i. P i \<noteq> None \<and> P (Suc i) \<noteq> None \<longrightarrow> the (P i) \<rightarrow> the (P (Suc i))" by (simp add: P_def)
    qed
    show "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" using P_def assms(2) valid_strategy_def by auto
    show "the (P 0) = v0" using P_def by simp
  qed
lemma valid_strategy_from_starts_correctly:
  assumes "valid_strategy_from p \<sigma> v0" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 \<noteq> None"
  proof -
    obtain P where P_def: "valid_path P" "the (P 0) = v0"
      using one_step_path_exists assms by blast
    moreover have "path_conforms_with_strategy_up_to p P \<sigma> 0" using P_def(2) by simp
    moreover have "P 0 \<noteq> None" using P_def(1) valid_path_def by blast
    moreover have "the (P 0) \<in> VV p" by (simp add: P_def(2) assms(2))
    moreover have "\<not>deadend (the (P 0))" using P_def(2) assms(3) by blast
    ultimately have "\<sigma> (the (P 0)) \<noteq> None" using valid_strategy_from_def assms(1) by blast
    thus ?thesis using P_def(2) by blast
  qed

lemma infinite_path_tail_conforms [intro]:
  assumes "path_conforms_with_strategy p P \<sigma>"
  shows "path_conforms_with_strategy p (path_tail P) \<sigma>"
  using assms path_conforms_with_strategy_def by auto

lemma path_tail_conforms_suc:
  assumes "path_conforms_with_strategy_up_to p P \<sigma> (Suc n)"
  shows "path_conforms_with_strategy_up_to p (path_tail P) \<sigma> n"
  using assms by auto

lemma infinite_path_tail_head [simp]:
  assumes "P 0 = Some v" "v \<in> VV p" "\<sigma> v = Some w" "path_conforms_with_strategy p P \<sigma>"
  shows "Some w = P 1"
  using assms by auto

lemma path_conforms_with_strategy_maximally_tail:
  assumes "path_conforms_with_strategy_maximally p P \<sigma>"
    and "P 0 \<noteq> None" "the (P 0) \<in> VV p" "\<sigma> (the (P 0)) \<noteq> None"
  shows "path_conforms_with_strategy_maximally p (path_tail P) \<sigma>"
  proof-
    { assume "path_conforms_with_strategy p P \<sigma>"
      hence "path_conforms_with_strategy p (path_tail P) \<sigma>" using infinite_path_tail_conforms by blast
      hence ?thesis using path_conforms_with_strategy_maximally_def by blast
    }
    moreover
    { assume "\<exists>n. path_conforms_with_strategy_up_to p P \<sigma> n \<and> P n \<noteq> None \<and> \<sigma> (the (P n)) = None"
      then obtain n where n_def: "path_conforms_with_strategy_up_to p P \<sigma> n" "P n \<noteq> None" "\<sigma> (the (P n)) = None" by blast
      have "n \<noteq> 0" by (metis assms(4) n_def(3))
      then obtain m where "Suc m = n" by (metis nat.exhaust)
      hence "path_conforms_with_strategy_up_to p P \<sigma> (Suc m) \<and> P (Suc m) \<noteq> None \<and> \<sigma> (the (P (Suc m))) = None"
        using n_def by metis
      moreover hence "path_conforms_with_strategy_up_to p (path_tail P) \<sigma> m" using path_tail_conforms_suc by blast
      ultimately have "\<exists>n. path_conforms_with_strategy_up_to p (path_tail P) \<sigma> n \<and> (path_tail P) n \<noteq> None \<and> \<sigma> (the ((path_tail P) n)) = None"
        by blast
    }
    ultimately show ?thesis using assms(1) path_conforms_with_strategy_maximally_def by blast
  qed

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

definition strategy_less_eq :: "'a Strategy \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy_less_eq \<sigma> \<sigma>' \<equiv> \<forall>v. \<sigma> v \<noteq> None \<longrightarrow> \<sigma> v = \<sigma>' v"

lemma strategy_less_eq_updates:
  assumes "\<sigma> v = None"
  shows "strategy_less_eq \<sigma> (\<sigma>(v \<mapsto> w))"
  by (simp add: assms option.case_eq_if strategy_less_eq_def)
lemma strategy_on_is_monotone:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_on p \<sigma> W"
  shows "strategy_on p \<sigma>' W"
  proof-
    { fix v assume "v \<in> W \<inter> VV p" "\<not>deadend v"
      hence "\<sigma> v \<noteq> None" using assms(2) strategy_on_def by blast
      hence "\<sigma>' v \<noteq> None" using assms(1) by (simp add: strategy_less_eq_def option.case_eq_if)
    }
    thus ?thesis by (simp add: strategy_on_def)
  qed
lemma strategy_less_eq_tran:
  assumes "strategy_less_eq \<sigma> \<sigma>'" "strategy_less_eq \<sigma>' \<sigma>''"
  shows "strategy_less_eq \<sigma> \<sigma>''" by (unfold strategy_less_eq_def; metis assms strategy_less_eq_def)
lemma strategy_less_eq_refl [simp]:
  "strategy_less_eq \<sigma> \<sigma>" by (simp add: option.case_eq_if strategy_less_eq_def)
lemma strategy_less_eq_least [simp]:
  "strategy_only_on p \<sigma> {} \<Longrightarrow> strategy_less_eq \<sigma> \<sigma>'" by (simp add: strategy_less_eq_def strategy_only_on_elements)
lemma strategy_less_eq_extensible:
  assumes "W \<subseteq> W'" "strategy_on p \<sigma> W" "valid_strategy p \<sigma>"
  shows "\<exists>\<sigma>'. valid_strategy p \<sigma>' \<and> strategy_less_eq \<sigma> \<sigma>' \<and> strategy_on p \<sigma>' W'" proof-
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
    moreover have "valid_strategy p ?\<sigma>'" proof-
      {
        fix v assume v_def: "v \<in> VV p" "?\<sigma>' v \<noteq> None"
        have "v \<rightarrow> the (?\<sigma>' v)" proof (cases)
          assume "\<sigma> v = None"
          hence "?\<sigma>' v = Some (SOME w. v\<rightarrow>w)" using v_def(2) by presburger
          hence *: "the (?\<sigma>' v) = (SOME w. v\<rightarrow>w)" by (rule option_the_simp)
          have "\<not>deadend v" using v_def(2) `\<sigma> v = None` by presburger
          hence "\<exists>w. v\<rightarrow>w" by auto
          thus ?thesis using * by (metis (mono_tags, lifting) someI)
        next
          assume "\<sigma> v \<noteq> None"
          moreover hence "v \<rightarrow> the (\<sigma> v)" using assms(3) `v \<in> VV p` valid_strategy_def by blast
          ultimately show ?thesis by simp
        qed
      }
      thus ?thesis using valid_strategy_def by blast
    qed
    ultimately show ?thesis by auto
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

definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v \<equiv> \<forall>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) = v \<longrightarrow> winning_path p P"

definition strategy_attracts_from_to :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_from_to p \<sigma> A W \<equiv> (\<forall>P.
      valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) \<in> A
    \<longrightarrow> (\<exists>i. P i \<noteq> None \<and> the (P i) \<in> W))"
lemma strategy_attracts_from_to_trivial [simp]:
  "strategy_attracts_from_to p \<sigma> W W" by (meson strategy_attracts_from_to_def valid_paths_are_nonempty)
definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv> (\<forall>P n.
      valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> the (P 0) \<in> A
    \<longrightarrow> (\<forall>i \<le> n. P i \<noteq> None \<longrightarrow> the (P i) \<notin> W))"
lemma strategy_avoids_trivial [simp]:
  "strategy_avoids p \<sigma> {} W" by (meson empty_iff strategy_avoids_def)
lemma strategy_avoids_directly:
  assumes "strategy_avoids p \<sigma> A W" "v0 \<in> A" "v0 \<in> VV p" "\<sigma> v0 \<noteq> None" "valid_strategy p \<sigma>"
  shows "the (\<sigma> v0) \<notin> W"
  proof (rule ccontr; simp)
    assume assm: "the (\<sigma> v0) \<in> W"
    obtain P where P: "valid_path P" "finite_path P" "path_conforms_with_strategy_up_to p P \<sigma> (Suc 0)" "the (P 0) = v0" using one_step_path_exists assms by blast
    have "the (P 0) \<in> A" using P(4) assms(2) by simp
    hence "\<forall>i \<le> Suc 0. P i \<noteq> None \<longrightarrow> the (P i) \<notin> W" using assms(1) strategy_avoids_def P by blast
    hence "P (Suc 0) \<noteq> None \<longrightarrow> the (P (Suc 0)) \<notin> W" by blast
    moreover have "\<sigma> (the (P 0)) \<noteq> None" by (simp add: P(4) assms(4))
    moreover have "the (P 0) \<in> VV p" by (simp add: P(4) assms(3))
    ultimately show False
      by (metis P(1) P(3) P(4) assm lessI path_conforms_with_strategy_up_to_def valid_paths_are_nonempty)
  qed
lemma strategy_avoids_strongly:
  assumes "strategy_avoids p \<sigma> A W"
    and P_conforms: "path_conforms_with_strategy p P \<sigma>"
    and "valid_path P" "the (P 0) \<in> A" "P n \<noteq> None"
  shows "the (P n) \<notin> W"
  proof-
    have "path_conforms_with_strategy_up_to p P \<sigma> n" using P_conforms path_conforms_with_strategy_approximations2 by blast
    hence "\<forall>i \<le> n. P i \<noteq> None \<longrightarrow> the (P i) \<notin> W" using assms strategy_avoids_def by blast
    thus ?thesis using Suc_n_not_le_n assms(5) linear by blast
  qed

lemma path_conforms_preserved_under_extension:
  assumes \<sigma>_valid: "valid_strategy_from p \<sigma> v0"
    and \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> \<sigma>'"
    and P_valid: "valid_path P"
    and P_conforms: "path_conforms_with_strategy p P \<sigma>'"
    and P_valid_start: "the (P 0) = v0"
  shows "path_conforms_with_strategy p P \<sigma>"
  proof (unfold path_conforms_with_strategy_def; intro allI impI; elim conjE)
    fix i
    assume P: "P i \<noteq> None" "the (P i) \<in> VV p"
    show "\<sigma> (the (P i)) = P (Suc i)" proof (cases)
      assume deadend: "deadend (the (P i))"
      hence "P (Suc i) = None" using P_valid valid_path_is_contiguous_suc valid_path_def by meson
      moreover have "\<sigma> (the (P i)) = None" proof (rule ccontr)
        assume "\<sigma> (the (P i)) \<noteq> None"
        hence "the (P i)\<rightarrow>the (\<sigma> (the (P i)))" using valid_strategy_from_def \<sigma>_valid P(2) by blast
        thus False using deadend using valid_edge_set by auto
      qed
      ultimately show ?thesis by simp
    next
      assume no_deadend: "\<not>deadend (the (P i))"
      hence \<sigma>'_next: "\<sigma>' (the (P i)) = P (Suc i)" using P_conforms P path_conforms_with_strategy_def by blast
      {
        fix n
        have "path_conforms_with_strategy_up_to p P \<sigma> n" proof (induct n)
          case 0 thus ?case unfolding path_conforms_with_strategy_up_to_def by blast
        next
          case (Suc n)
          show ?case proof (cases)
            assume assm: "P n \<noteq> None \<and> the (P n) \<in> VV p \<and> \<not>deadend (the (P n))"
            hence "\<sigma> (the (P n)) \<noteq> None" using \<sigma>_valid P_valid P_conforms P_valid_start valid_strategy_from_def Suc.hyps by blast
            hence "\<sigma> (the (P n)) = \<sigma>' (the (P n))" using \<sigma>_less_eq_\<sigma>' using strategy_less_eq_def by blast
            moreover have "\<sigma>' (the (P n)) = P (Suc n)" using P_conforms assm path_conforms_with_strategy_def by blast
            ultimately have *: "\<sigma> (the (P n)) = P (Suc n)" by simp
            thus ?thesis proof (unfold path_conforms_with_strategy_up_to_def; intro allI impI)
              fix i assume i_def: "i < Suc n" "P i \<noteq> None \<and> the (P i) \<in> VV p"
              show "\<sigma> (the (P i)) = P (Suc i)" proof (cases)
                assume "i < n"
                hence "P i \<noteq> None \<Longrightarrow> the (P i) \<in> VV p \<Longrightarrow> \<sigma> (the (P i)) = P (Suc i)" using Suc.hyps path_conforms_with_strategy_up_to_def by blast
                thus ?thesis using i_def(2) by blast
              next
                assume "\<not>i < n"
                hence "i = n" using i_def(1) by auto
                thus ?thesis using * by blast
              qed
            qed
          next
            assume "\<not>(P n \<noteq> None \<and> the (P n) \<in> VV p \<and> \<not>deadend (the (P n)))"
            moreover { assume "P n = None" hence ?thesis by (metis Suc.hyps less_antisym path_conforms_with_strategy_up_to_def) }
            moreover { assume "the (P  n) \<notin> VV p" hence ?thesis using Suc.hyps path_conforms_up_to_VVpstar by blast }
            moreover { assume "deadend (the (P n))" hence ?thesis using P_valid Suc.hyps \<sigma>_valid path_conforms_up_to_deadends by blast }
            ultimately show ?thesis by blast
          qed
        qed
      }
      hence "path_conforms_with_strategy p P \<sigma>" using path_conforms_with_strategy_approximations by blast

      hence "\<sigma> (the (P i)) = \<sigma>' (the (P i))" using strategy_less_eq_def \<sigma>_less_eq_\<sigma>' by (metis (mono_tags, hide_lams) P(1) P(2) \<sigma>'_next path_conforms_with_strategy_def)
      thus ?thesis by (simp add: \<sigma>'_next)
    qed
  qed

lemma winning_strategy_preserved_under_extension:
  assumes \<sigma>_valid: "valid_strategy_from p \<sigma> v0"
    and \<sigma>_winning: "winning_strategy p \<sigma> v0"
    and \<sigma>_less_eq_\<sigma>': "strategy_less_eq \<sigma> \<sigma>'"
  shows "winning_strategy p \<sigma>' v0"
  using assms path_conforms_preserved_under_extension winning_strategy_def by blast

lemma valid_strategy_is_valid_strategy_from:
  assumes \<sigma>_valid: "valid_strategy p \<sigma>"
    and \<sigma>_only_on: "strategy_on p \<sigma> A"
    and \<sigma>_avoids: "strategy_avoids p \<sigma> A (V - A)"
    and v0_def: "v0 \<in> A"
  shows "valid_strategy_from p \<sigma> v0"
  proof (unfold valid_strategy_from_def; intro conjI)
    show "\<forall>v\<in>VV p. \<sigma> v \<noteq> None \<longrightarrow> v \<rightarrow> the (\<sigma> v)" using \<sigma>_valid valid_strategy_def by blast
    show "\<forall>P n. valid_path P \<and> path_conforms_with_strategy_up_to p P \<sigma> n \<and> the (P 0) = v0
      \<and> P n \<noteq> None \<and> the (P n) \<in> VV p \<and> \<not>deadend (the (P n)) \<longrightarrow> \<sigma> (the (P n)) \<noteq> None"
      proof (intro allI impI; elim conjE)
      fix P n
      assume P_valid: "valid_path P"
        and P_conforms_up_to_n: "path_conforms_with_strategy_up_to p P \<sigma> n"
        and P_valid_start: "the (P 0) = v0"
        and P_Suc_n_not_None: "P n \<noteq> None"
        and P_Suc_n_in_VV_p: "the (P n) \<in> VV p"
        and P_Suc_n_no_deadend: "\<not>deadend (the (P n))"
      have *: "\<And>i. i < n \<Longrightarrow> P i \<noteq> None \<Longrightarrow> the (P i) \<in> VV p \<Longrightarrow> \<sigma> (the (P i)) = P (Suc i)" using path_conforms_with_strategy_up_to_def P_conforms_up_to_n by metis
      have P_n_not_None: "P n \<noteq> None" using P_Suc_n_not_None P_valid valid_path_is_contiguous_suc by blast
      have "\<forall>i \<le> n. P i \<noteq> None \<longrightarrow> the (P i) \<notin> (V - A)" using \<sigma>_avoids strategy_avoids_def P_valid P_conforms_up_to_n P_valid_start v0_def by metis
      hence "the (P n) \<notin> (V - A)" using P_Suc_n_not_None by blast
      hence "the (P n) \<in> A" using P_Suc_n_in_VV_p by blast
      hence "the (P n) \<in> A \<inter> VV p" using P_Suc_n_in_VV_p by blast
      thus "\<sigma> (the (P n)) \<noteq> None" using \<sigma>_only_on P_Suc_n_no_deadend strategy_on_def by blast
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
  shows "\<exists>P. valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> the (P 0) = v0"
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

    show P_valid_start: "the (P 0) = v0" unfolding P_def using v0_def by auto

    (* The key lemma.  Show simultaneously that
      1) the path is in V and
      2) there is an edge between every two consecutive entries. *)
    have edges_exist: "\<And>i. P i \<noteq> None \<Longrightarrow> the (P i) \<in> V \<and> (P (Suc i) \<noteq> None \<longrightarrow> the (P i)\<rightarrow>the (P (Suc i)))" proof-
      have *:
        "\<And>i. \<lbrakk> P i \<noteq> None; the (P i) \<in> V; P (Suc i) \<noteq> None \<rbrakk> \<Longrightarrow> the (P (Suc i)) \<in> V \<and> the (P i)\<rightarrow>the (P (Suc i))" proof-
        fix i
        assume P_i: "P i \<noteq> None" "the (P i) \<in> V" and P_Suc_i: "P (Suc i) \<noteq> None"
        have no_deadend: "\<not>deadend (the (P i))" proof-
          show "\<not>deadend (the (P i))" proof (cases rule: VV_cases[of "the (P i)" p])
            show "the (P i) \<in> V" using P_i(2) .
          next
            assume P_i_in_VVp: "the (P i) \<in> VV p"
            hence "\<sigma> (the (P i)) = P (Suc i)" using P_simp P_i(1) by presburger
            hence "\<sigma> (the (P i)) \<noteq> None" using P_Suc_i by auto
            hence "the (P i)\<rightarrow>the (\<sigma> (the (P i)))" using \<sigma>_valid P_i_in_VVp valid_strategy_from_def by blast
            thus ?thesis using valid_edge_set by auto
          next
            assume "the (P i) \<in> VV p**"
            thus ?thesis by (meson P_simp VV_equivalence P_i(2) P_Suc_i)
          qed
        qed
        obtain w where w_def: "P (Suc i) = Some w" using P_Suc_i by blast
        show "the (P (Suc i)) \<in> V \<and> the (P i)\<rightarrow>the (P (Suc i))" proof(cases)
          assume P_i_in_VVp: "the (P i) \<in> VV p"
          hence *: "\<sigma> (the (P i)) = P (Suc i)" using P_simp P_i(1) by presburger
          hence "\<sigma> (the (P i)) \<noteq> None" using P_Suc_i by auto
          hence "the (P i)\<rightarrow>the (\<sigma> (the (P i)))" using \<sigma>_valid P_i_in_VVp valid_strategy_from_def by blast
          hence "the (P i)\<rightarrow>the (P (Suc i))" using * by auto
          moreover hence "the (P (Suc i)) \<in> V" using valid_edge_set by blast
          ultimately show ?thesis using valid_edge_set by auto
        next
          assume P_i_not_in_VVp: "the (P i) \<notin> VV p"
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

end -- "context ParityGame"

end
