theory strategy
imports
  Main
  parity_game
begin

type_synonym 'a Strategy = "'a \<Rightarrow> 'a"

context ParityGame begin

definition strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> v\<rightarrow>\<sigma> v"

coinductive path_conforms_with_strategy :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
path_conforms_LNil:  "path_conforms_with_strategy p LNil \<sigma>"
| path_conforms_LCons_LNil: "path_conforms_with_strategy p (LCons v LNil) \<sigma>"
| path_conforms_VVp: "\<lbrakk> v \<in> VV p; w = \<sigma> v; path_conforms_with_strategy p (LCons w Ps) \<sigma> \<rbrakk> \<Longrightarrow> path_conforms_with_strategy p (LCons v (LCons w Ps)) \<sigma>"
| path_conforms_VVpstar: "\<lbrakk> v \<notin> VV p; path_conforms_with_strategy p Ps \<sigma> \<rbrakk> \<Longrightarrow> path_conforms_with_strategy p (LCons v Ps) \<sigma>"

definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  [simp]: "winning_strategy p \<sigma> v0 \<equiv> \<forall>P. \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0 \<longrightarrow> winning_path p P"

definition strategy_attracts :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts p \<sigma> A W \<equiv> \<forall>P.
      \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 \<in> A
    \<longrightarrow> (\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A)"

definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> v0 W \<equiv> (\<forall>P.
      \<not>lnull P \<and> valid_path P \<and> maximal_path P \<and> path_conforms_with_strategy p P \<sigma> \<and> P $ 0 = v0
    \<longrightarrow> lset P \<inter> W = {})"

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

(*
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
qed *)

(*
lemma valid_strategy_none_on_VVpstar: "valid_strategy p \<sigma> \<Longrightarrow> v \<notin> VV p \<Longrightarrow> \<sigma> v = None" by (metis not_None_eq valid_strategy_def)
lemma valid_strategy_none_on_VVpstar2: "valid_strategy p \<sigma> \<Longrightarrow> v \<in> VV p** \<Longrightarrow> \<sigma> v = None" by (metis DiffD2 Player.distinct(1) valid_strategy_none_on_VVpstar)
lemma valid_strategy_none_on_deadends: "valid_strategy p \<sigma> \<Longrightarrow> deadend v \<Longrightarrow> \<sigma> v = None" by (meson edges_are_in_V not_Some_eq valid_strategy_def)
lemma valid_empty_strategy: "valid_strategy p (\<lambda>_. None)" using valid_strategy_def by simp
*)

(* An arbitrary strategy.  Useful to define other strategies. *)
definition "\<sigma>_arbitrary \<equiv> \<lambda>v. SOME w. v\<rightarrow>w"

lemma valid_arbitrary_strategy: "strategy p \<sigma>_arbitrary" proof-
  { fix v assume "\<not>deadend v"
    hence "\<not>deadend v \<Longrightarrow> v \<rightarrow> \<sigma>_arbitrary v" unfolding \<sigma>_arbitrary_def using someI_ex[of "\<lambda>w. v\<rightarrow>w"] by blast
  }
  thus ?thesis unfolding strategy_def by blast
qed

lemma valid_strategy_updates: "\<lbrakk> strategy p \<sigma>; v0\<rightarrow>w0 \<rbrakk> \<Longrightarrow> strategy p (\<sigma>(v0 := w0))"
  unfolding strategy_def by auto

lemma valid_strategy_in_V: "\<lbrakk> strategy p \<sigma>; v \<in> VV p; \<not>deadend v \<rbrakk> \<Longrightarrow> \<sigma> v \<in> V"
  unfolding strategy_def using valid_edge_set by auto

lemma one_step_path_exists:
  assumes "v0 \<in> V"
  shows "\<exists>P. valid_path P \<and> lfinite P \<and> path_conforms_with_strategy p P \<sigma> \<and> \<not>lnull P \<and> P $ 0 = v0"
  by (meson assms lfinite_code(1) lfinite_code(2) llist.disc(2) lnth_0 path_conforms_with_strategy.intros(2) valid_path_base')

lemma path_conforms_with_strategy_ltl [intro]:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ltl P) \<sigma>"
  by (drule path_conforms_with_strategy.cases) (simp_all add: path_conforms_with_strategy.intros(1))

lemma path_conforms_with_strategy_irrelevant:
  assumes "path_conforms_with_strategy p P \<sigma>" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P (\<sigma>(v := w))"
  using assms apply (coinduction arbitrary: P) by (drule path_conforms_with_strategy.cases) auto

lemma path_conforms_with_strategy_irrelevant':
  assumes "path_conforms_with_strategy p P (\<sigma>(v := w))" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P \<sigma>"
  by (metis assms fun_upd_triv fun_upd_upd path_conforms_with_strategy_irrelevant)

(* strategy_attracts_from_to *)

lemma strategy_attracts_irrelevant:
  assumes "strategy_attracts p \<sigma> A W" "v \<notin> A" "strategy p \<sigma>"
  shows "strategy_attracts p (\<sigma>(v := w)) A W" proof-
  { fix P assume P: "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P (\<sigma>(v := w))" "P $ 0 \<in> A"
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A" proof (cases)
      assume "v \<in> lset P"
      then obtain n where n: "enat n < llength P" "P $ n = v" by (meson in_lset_conv_lnth)
      (* obtain the minimal n, etc. *)
      show ?thesis sorry
    next
      assume "v \<notin> lset P"
      with P(4) have "path_conforms_with_strategy p P \<sigma>" using path_conforms_with_strategy_irrelevant' by blast
      with P(1) P(2) P(3) P(5) assms(1) show ?thesis unfolding strategy_attracts_def by blast
    qed
  }
  thus ?thesis unfolding strategy_attracts_def by blast
qed

lemma strategy_attracts_from_to_trivial [simp]: "strategy_attracts p \<sigma> W W"
  unfolding strategy_attracts_def using lnull_0_llength zero_enat_def by fastforce

lemma strategy_attracts_from_to_empty [simp]: "strategy_attracts p \<sigma> {} W"
  by (simp add: strategy_attracts_def)

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
