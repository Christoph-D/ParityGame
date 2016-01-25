(* Introduces the concept of avoiding strategies. *)
theory Strategy_Avoids
imports
  Main
  AttractorStrategy
begin

context ParityGame begin

(* All \<sigma>-paths starting from A never visit W.
   That is, "\<exists>\<sigma>. strategy_avoids p \<sigma> A (V - A)" means that A is a p-trap. *)
definition strategy_avoids :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_avoids p \<sigma> A W \<equiv>
    (\<forall>P v0. v0 \<in> A \<and> vmc_path G P v0 p \<sigma> \<longrightarrow> lset P \<inter> W = {})"

lemma strategy_avoids_trivial [simp]: "strategy_avoids p \<sigma> {} W"
  unfolding strategy_avoids_def by simp

(* If A is the p-attractor of a set W, then p** has a strategy on V - A avoiding A.
   Note that this theorem is not required to prove positional_strategy_exists. *)
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

  show "strategy p \<sigma>"
    unfolding \<sigma>_def using \<sigma>'_correct(2) valid_strategy_updates_set valid_arbitrary_strategy by blast

  show "strategy_avoids p \<sigma> (V - A) A" proof (cases "V - A = {}")
    case False
    {
      fix P v v0 assume v0: "v0 \<in> V - A" "vmc_path G P v0 p \<sigma>"
      then interpret vmc_path G P v0 p \<sigma> by blast
      have "v \<in> lset P \<Longrightarrow> v \<in> V - A" proof (insert v0, induct arbitrary: v0 rule: llist_set_induct)
        case (find P v0)
        interpret vmc_path G P v0 p \<sigma> using find.prems(2) .
        show ?case using P_v0 find.prems(1) by blast
      next
        case (step P v v0)
        interpret vmc_path G P v0 p \<sigma> using step.prems(2) .
        show ?case proof (cases "lnull (ltl P)")
          case True
          thus "v \<in> V - A" using lset_lnull step.hyps(2) by blast
        next
          case False
          then interpret vmc_path_no_deadend G P v0 p \<sigma> using P_no_deadend_v0 by unfold_locales
          have "w0 \<notin> A" proof (cases)
            assume "v0 \<in> VV p"
            moreover hence "\<sigma>' v0 \<notin> A" using \<sigma>'_correct(1) step.prems(1) v0_edge_w0 w0_V by blast
            ultimately show "w0 \<notin> A" using \<sigma>_def step.prems(1) v0_conforms by auto
          next
            assume "v0 \<notin> VV p"
            { assume "w0 \<in> A"
              have "v0 \<in> VV p**" using `v0 \<notin> VV p` `v0 \<in> V - A` by blast
              moreover have "v0 \<notin> VV p****" using `v0 \<notin> VV p` other_other_player[of p] by metis
              moreover have "\<exists>w. v0\<rightarrow>w \<and> w \<in> A" using `w0 \<in> A` using v0_edge_w0 by blast
              ultimately have "v0 \<in> directly_attracted p** A"
                unfolding directly_attracted_def
                using `\<not>deadend v0` `v0 \<in> V - A`
                by blast
              hence False
                unfolding A_def using `v0 \<in> V - A` assms attractor_unfolding[of "p**" W] by blast
            }
            thus "w0 \<notin> A" by blast
          qed
          thus "v \<in> V - A" using w0_V w0_def vmc_path_ltl w0_def step.hyps(3) by simp
        qed
      qed
    }
    thus ?thesis unfolding strategy_avoids_def by blast
  qed (simp del: Diff_eq_empty_iff)
qed

end -- "context ParityGame"

end
