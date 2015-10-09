(* Some lemmas that might be useful one day, but are irrelevant for positional determinacy. *)
theory Bonus_Lemmas
imports
  Main
  strategy
begin

(* A valid conforming path can always be extended to a valid maximal conforming path. *)
lemma (in ParityGame) vc_path_to_vmc_path:
  assumes \<sigma>: "strategy p \<sigma>"
    and P: "\<not>lnull P" "valid_path P" "path_conforms_with_strategy p P \<sigma>"
  shows "\<exists>P'. lprefix P P' \<and> vmc_path G P' (lhd P') p \<sigma>"
proof (cases)
  assume "lfinite P \<and> \<not>deadend (llast P)"
  hence "lfinite P" "\<not>deadend (llast P)" by simp_all
  def v \<equiv> "if llast P \<in> VV p then \<sigma> (llast P) else \<sigma>_arbitrary (llast P)"
  have paths_connect: "llast P \<rightarrow> v" unfolding v_def apply (cases "llast P \<in> VV p")
    using `\<not>deadend (llast P)` \<sigma> valid_arbitrary_strategy[of "p**"] strategy_def by auto
  hence "llast P \<in> V" "v \<in> V" using edges_are_in_V by blast+
  def P' \<equiv> "lappend P (greedy_conforming_path p \<sigma> \<sigma>_arbitrary v)"
    (is "lappend _ ?B")
  have "llast P \<in> VV p \<Longrightarrow> \<sigma> (llast P) = lhd ?B" using v_def by simp
  hence "path_conforms_with_strategy p P' \<sigma>"
    unfolding P'_def
    using \<sigma> `v \<in> V` path_conforms_with_strategy_lappend[OF `lfinite P` `\<not>lnull P` P(3)]
    by simp
  moreover have "maximal_path P'" unfolding P'_def using maximal_path_lappend \<sigma> `v \<in> V` by simp
  moreover have "valid_path P'" unfolding P'_def
    using valid_path_lappend[OF `lfinite P` P(2)] \<sigma> `v \<in> V` `lfinite P` paths_connect by simp
  ultimately have "vmc_path G P' (lhd P') p \<sigma>" using P'_def by unfold_locales simp_all
  thus ?thesis using lprefix_lappend[of P ?B] P'_def by blast
next
  assume "\<not>(lfinite P \<and> \<not>deadend (llast P))"
  hence "maximal_path P" using maximal_ends_on_deadend' P(2) infinite_path_is_maximal by blast
  hence "vmc_path G P (lhd P) p \<sigma>" using P by unfold_locales simp_all
  thus ?thesis by blast
qed

lemma (in vmc_path) path_conforms_with_strategy_update_path:
  assumes \<sigma>: "strategy p \<sigma>" and \<sigma>': "strategy p \<sigma>'"
    (* P is influenced by changing \<sigma> to \<sigma>'. *)
    and v: "v \<in> lset P" "v \<in> VV p" "\<not>deadend v" "\<sigma> v \<noteq> \<sigma>' v"
  shows "\<exists>P' n.
    vmc_path G P' v0 p \<sigma>'
    \<and> enat (Suc n) < llength P' \<and> enat (Suc n) < llength P
    \<and> ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P
    \<and> P $ n \<in> VV p \<and> \<not>deadend (P $ n)
    \<and> \<sigma> (P $ n) \<noteq> \<sigma>' (P $ n)"
proof-
  (* Determine the first index where P fails to follow \<sigma>'. *)
  def fail \<equiv> "\<lambda>P n. enat (Suc n) < llength P \<and> P $ n \<in> VV p \<and> \<not>deadend (P $ n) \<and> \<sigma>' (P $ n) \<noteq> P $ Suc n"
  hence "\<exists>n. fail P n" proof-
    from v(1) obtain n where n: "enat n < llength P" "P $ n = v" by (meson in_lset_conv_lnth)
    with v(3) P_maximal
      have "enat (Suc n) < llength P" using maximal_path_impl1 by blast
    moreover from n(2) v(2)
      have "P $ n \<in> VV p" by simp
    moreover with P_conforms `enat (Suc n) < llength P` n(2) v(4)
      have "\<sigma>' (P $ n) \<noteq> P $ Suc n" using vmc_path_conforms by auto
    ultimately show ?thesis unfolding fail_def using n(2) v(3) by blast
  qed
  then obtain n where "fail P n" and n_min: "\<And>m. m < n \<Longrightarrow> \<not>fail P m"
    using ex_least_nat_le[of "\<lambda>n. fail P n"] by blast
  hence n: "enat (Suc n) < llength P" "P $ n \<in> VV p" "\<not>deadend (P $ n)" "\<sigma>' (P $ n) \<noteq> P $ Suc n"
    unfolding fail_def by blast+
  def P' \<equiv> "lappend (ltake (enat (Suc n)) P) (greedy_conforming_path p \<sigma>' \<sigma>_arbitrary (\<sigma>' (P $ n)))"
    (is "lappend ?A ?B")
  have "\<sigma>' (P $ n) \<in> V" using \<sigma>' n(2,3) valid_strategy_in_V by blast
  then interpret PB: vmc_path G ?B "\<sigma>' (P $ n)" p \<sigma>'
    by unfold_locales (simp_all add: \<sigma>')

  have "llength ?A = enat (Suc n)" using llength_ltake' n(1) by blast

  from n(2) n(3) \<sigma>' have "\<sigma>' (P $ n) \<in> V" using valid_strategy_in_V by blast

  have "llast ?A = P $ n" proof-
    have "llast ?A = ?A $ n" using `llength ?A = enat (Suc n)` unfolding llast_def by simp
    moreover have "enat n < llength ?A" using `llength ?A = enat (Suc n)` by simp
    ultimately show ?thesis using lnth_lappend1[of n ?A ?B] by (simp add: lnth_ltake)
  qed

  have "\<sigma> (P $ n) \<noteq> \<sigma>' (P $ n)" using n(1,2,4) vmc_path_conforms by auto
  moreover have "enat (Suc n) < llength P'"
    unfolding P'_def using `llength ?A = enat (Suc n)` by simp
  moreover have "ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P"
    unfolding P'_def using `llength ?A = enat (Suc n)`
    by (metis P'_def `enat (Suc n) < llength P'` llength_ltake
              lprefix_lappendD lprefix_llength_eq_imp_eq ltake_is_lprefix min.strict_order_iff)
  moreover have "vmc_path G P' v0 p \<sigma>'" proof (unfold_locales)
    show "lhd P' = v0" unfolding P'_def using P_v0
      by (metis P'_def PB.P_not_null P_0 `ltake (enat (Suc n)) P' = ltake (enat (Suc n)) P`
                enat_ord_simps(2) lappend.disc_iff(2) lhd_conv_lnth ltake_lnth zero_less_Suc)
    show "\<not>lnull P'" unfolding P'_def by simp
    show "valid_path P'" proof-
      have "llast ?A \<rightarrow> lhd ?B" proof-
        have "lhd ?B = \<sigma>' (P $ n)" by simp
        moreover from n(2) n(3) \<sigma>'
          have "P $ n \<rightarrow> \<sigma>' (P $ n)" using strategy_def by blast
        ultimately show ?thesis using `llast ?A = P $ n` by simp
      qed
      thus ?thesis unfolding P'_def using PB.P_valid valid_path_lappend[of ?A ?B] by auto
    qed
    show "maximal_path P'" proof-
      have "\<not>lnull ?B" by simp
      moreover from \<sigma>' `\<sigma>' (P $ n) \<in> V`
        have "maximal_path ?B"
          using greedy_conforming_path_properties(4)[of "\<sigma>' (P $ n)" p \<sigma>' \<sigma>_arbitrary] 
                valid_arbitrary_strategy
          by blast
      ultimately show ?thesis unfolding P'_def using maximal_path_lappend by blast
    qed

    show "path_conforms_with_strategy p P' \<sigma>'" proof-
      have "lfinite ?A" "\<not>lnull ?B" by simp_all
      moreover have "\<not>lnull ?A" by (simp add: enat_0_iff(1))
      moreover have "llast ?A \<in> VV p" by (simp add: `llast ?A = P $ n` n(2))
      moreover have "\<sigma>' (llast ?A) = lhd ?B" using `llast ?A = P $ n` by simp
      moreover have "path_conforms_with_strategy p ?A \<sigma>'" proof-
        have *: "vmc_path G P v0 p \<sigma>" by unfold_locales
        have "lprefix ?A P" by simp
        moreover from * n n_min
          have "path_conforms_with_strategy p ?A \<sigma>'"
        proof (induct n arbitrary: P v0)
          case 0
          then interpret P: vmc_path G P v0 p \<sigma> by blast
          have "ltake (enat (Suc 0)) P = LCons (lhd P) LNil"
            by (simp add: lappend_lnull1 ltake_Suc_conv_snoc_lnth zero_enat_def)
          thus ?case by (simp add: path_conforms_LCons_LNil)
        next
          case (Suc n P v0)
          interpret vmc_path_no_deadend G P v0 p \<sigma>
            using Suc.prems(2) vmc_path.vmc_path_llength_no_deadend[OF Suc.prems(1)] by blast
          have "enat (Suc n) < llength (ltl P)" using enat_Suc_ltl Suc.prems(2) by blast
          moreover have "ltl P $ n \<in> VV p" using P_lnth_Suc Suc.prems(3) by auto
          moreover have "\<not>deadend (ltl P $ n)" using P_lnth_Suc Suc.prems(4) by auto
          moreover have "\<sigma>' (ltl P $ n) \<noteq> ltl P $ Suc n" using P_lnth_Suc Suc.prems(5) by auto
          moreover have "\<And>m. m < n \<Longrightarrow> \<not>fail (ltl P) m" proof-
            fix m assume "m < n"
            hence "\<not>fail P (Suc m)" by (simp add: Suc.prems(6))
            hence *: "\<lbrakk> enat (Suc (Suc m)) < llength P;
                P $ Suc m \<in> VV p;
                \<not>deadend (P $ Suc m) \<rbrakk> \<Longrightarrow>
                \<sigma>' (P $ Suc m) = P $ Suc (Suc m)"
              unfolding fail_def by blast
            {
              assume **: "enat (Suc m) < llength (ltl P)"
                "ltl P $ m \<in> VV p"
                "\<not>deadend (ltl P $ m)"
              have A: "ltl P $ m = P $ Suc m" by (simp add: Suc.prems(2) lnth_ltl)
              from **(1) have "enat (Suc (Suc m)) < llength P" using enat_ltl_Suc by blast
              moreover from **(2) have "P $ Suc m \<in> VV p" by (simp add: A)
              moreover from **(3) have "\<not>deadend (P $ Suc m)" by (simp add: A)
              ultimately have "\<sigma>' (P $ Suc m) = P $ Suc (Suc m)" using * by blast
              hence "\<sigma>' (ltl P $ m) = ltl P $ Suc m" by (simp add: A Suc.prems(2) lnth_ltl)
            }
            thus "\<not>fail (ltl P) m" unfolding fail_def by blast
          qed
          ultimately have *: "path_conforms_with_strategy p (ltake (enat (Suc n)) (ltl P)) \<sigma>'"
            using Suc.hyps[OF vmc_path_ltl] by blast
          have "path_conforms_with_strategy p (LCons (lhd P) (ltake (enat (Suc n)) (ltl P))) \<sigma>'"
          proof (cases)
            assume "lhd P \<in> VV p"
            hence "lhd (ltl P) = \<sigma> (lhd P)" by (simp add: v0_conforms w0_def)
            have "\<not>deadend (lhd P)" using P_v0 v0_edge_w0 w0_V by blast
            moreover have "enat (Suc 0) < llength P" by (simp add: enat_ltl_Suc lnull_0_llength)
            moreover have "\<not>fail P 0" by (simp add: Suc.prems(6))
            ultimately have "\<sigma>' (P $ 0) = P $ Suc 0" unfolding fail_def by (metis P_0 P_v0 `lhd P \<in> VV p`)
            with `lhd (ltl P) = \<sigma> (lhd P)`
              have "\<sigma>' (P $ 0) = \<sigma> (P $ 0)" by (simp add: P_lnth_Suc Ptl_0)
            with `lhd (ltl P) = \<sigma> (lhd P)`
              have 1: "lhd (ltl P) = \<sigma>' (lhd P)" by (simp add: Suc.prems(2) lhd_conv_lnth)
            obtain w Ps where w: "ltake (enat (Suc n)) (ltl P) = LCons w Ps"
              by (metis `\<not>lnull (ltl P)` enat_ord_simps(2) lessI less_irrefl lhd_LCons_ltl
                        lnull_ltake min_enat_simps(2) min_less_iff_conj)
            moreover from w have "path_conforms_with_strategy p (LCons w Ps) \<sigma>'" using * by simp
            moreover from w 1 have "w = \<sigma>' (lhd P)"
              by (metis `\<not>lnull (ltl P)` enat_ord_simps(2) lnth_0 lnth_0_conv_lhd lnth_ltake zero_less_Suc)
            ultimately show ?thesis
              using path_conforms_VVp[of "lhd P" p w \<sigma>' Ps] `lhd P \<in> VV p` by force
          next
            assume "lhd P \<notin> VV p"
            thus ?thesis by (simp add: * path_conforms_VVpstar)
          qed
          moreover have "LCons (lhd P) (ltake (enat (Suc n)) (ltl P)) = ltake (eSuc (enat (Suc n))) P"
            by (metis P_LCons P_v0 ltake_eSuc_LCons)
          ultimately show "path_conforms_with_strategy p (ltake (enat (Suc (Suc n))) P) \<sigma>'"
            by (simp add: eSuc_enat)
        qed
        ultimately show ?thesis using path_conforms_with_strategy_prefix by blast
      qed
      moreover from \<sigma>' `\<sigma>' (P $ n) \<in> V`
        have "path_conforms_with_strategy p ?B \<sigma>'"
          using greedy_conforming_path_properties(5)[of "\<sigma>' (P $ n)" p \<sigma>' \<sigma>_arbitrary]
                valid_arbitrary_strategy
          by blast
      ultimately show ?thesis unfolding P'_def using path_conforms_with_strategy_lappend by blast
    qed
  qed
  ultimately show ?thesis using n(1,2,3) by blast
qed

end
