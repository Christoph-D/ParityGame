theory positional_strategy
imports
  Main
  attractor_strategy
begin

context ParityGame begin

lemma positional_strategy_induction_step:
  assumes "v \<in> V"
    and no_deadends: "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
    and IH: "\<And>(G :: ('a, 'b) ParityGame_scheme) v.
      \<lbrakk> card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>) < card (\<omega> ` V); v \<in> V\<^bsub>G\<^esub>; ParityGame G; \<And>v. v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<not>Digraph.deadend G v  \<rbrakk>
        \<Longrightarrow> \<exists>p \<sigma>. ParityGame.strategy G p \<sigma> \<and> ParityGame.winning_strategy G p \<sigma> v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
proof-
  {
    def min_prio \<equiv> "Min (\<omega> ` V)"
    fix p assume p: "winning_priority p min_prio"
    def W0 \<equiv> "{ v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }"
    def W1 \<equiv> "{ v \<in> V. \<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v }"
    def U \<equiv> "V - W1"
    def K \<equiv> "U \<inter> (\<omega> -` {min_prio})"
    def V' \<equiv> "U - attractor p K"

    def [simp]: G' \<equiv> "subgame V'"
    interpret G': ParityGame G' using subgame_ParityGame by simp

    have "V' \<subseteq> V" unfolding U_def V'_def by blast
    hence [simp]: "V\<^bsub>G'\<^esub> = V'" unfolding G'_def by simp

    have "V\<^bsub>G'\<^esub> \<subseteq> V" "E\<^bsub>G'\<^esub> \<subseteq> E" "\<omega>\<^bsub>G'\<^esub> = \<omega>" unfolding G'_def by (simp_all add: subgame_\<omega>)
    have "G'.VV p = V' \<inter> VV p" unfolding G'_def using subgame_VV by simp

    have V_decomp: "V = attractor p K \<union> V' \<union> W1" proof-
      have "V - W1 \<subseteq> attractor p K \<union> V'" unfolding V'_def U_def by auto
      hence "V \<subseteq> attractor p K \<union> V' \<union> W1" by blast
      moreover have "attractor p K \<subseteq> V" by (metis Diff_subset K_def U_def attractor_is_bounded_by_V inf_le1 subset_trans)
      ultimately show ?thesis unfolding W1_def using `V' \<subseteq> V` by blast
    qed

    obtain \<sigma>W1 where \<sigma>W1: "strategy p** \<sigma>W1" "\<And>v. v \<in> W1 \<Longrightarrow> winning_strategy p** \<sigma>W1 v"
      using merge_winning_strategies[of W1 "p**"] W1_def by fastforce

    have G'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>G'.deadend v" proof-
      fix v assume v: "v \<in> V\<^bsub>G'\<^esub>"
      {
        assume "G'.deadend v"
        hence not_in_V': "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<notin> V'" proof-
          fix w assume "v\<rightarrow>w"
          { assume "w \<in> V'"
            hence "w \<in> V\<^bsub>G'\<^esub>" using `V\<^bsub>G'\<^esub> = V'` by blast
            moreover hence "v \<rightarrow>\<^bsub>G'\<^esub> w" unfolding G'_def using `V' \<subseteq> V` `v \<in> V\<^bsub>G'\<^esub>` `v\<rightarrow>w` by simp
            ultimately have False using `G'.deadend v` by blast
          }
          thus "w \<notin> V'" by blast
        qed
        have "v \<in> V" using `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> \<subseteq> V` by blast
        have "v \<in> V'" using `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> = V'` by blast
        hence "v \<notin> W1" unfolding V'_def U_def by blast
        have "\<not>deadend v" using no_deadends v `V\<^bsub>G'\<^esub> \<subseteq> V` by blast
        moreover {
          assume "v \<in> VV p"
          {
            fix w assume "v\<rightarrow>w"
            {
              assume "w \<in> attractor p K"
              hence "v \<in> attractor p K" using `v \<in> VV p` `v\<rightarrow>w` attractor_set_VVp by blast
              hence False using `v \<in> V'` V'_def by blast
            }
            hence "w \<notin> attractor p K" by blast
            hence "w \<in> W1" using not_in_V' V_decomp `v\<rightarrow>w` by blast
          }
          (* All successors of v point to W1, so v \<in> W1 *)
          hence "winning_strategy p** \<sigma>W1 v" using strategy_extends_backwards_VVp[of v p \<sigma>W1] \<sigma>W1 `v \<in> VV p` by blast
          hence False using W1_def \<sigma>W1(1) `v \<in> VV p` `v \<notin> W1` by blast
        }
        moreover {
          assume "v \<notin> VV p"
          hence "v \<in> VV p**" using `\<not>deadend v` by blast
          {
            fix w assume "v\<rightarrow>w"
            {
              assume "w \<in> W1"
              let ?\<sigma>W1 = "\<sigma>W1(v := w)"
              have "strategy p** ?\<sigma>W1" by (simp add: \<sigma>W1(1) `v\<rightarrow>w` valid_strategy_updates)
              moreover have "winning_strategy p** ?\<sigma>W1 v" proof-
                have "\<not>(\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v)" using `v \<notin> W1` `v \<in> V` W1_def by auto
                moreover have "winning_strategy p** \<sigma>W1 w" using `w \<in> W1` \<sigma>W1(2) by blast
                ultimately have "winning_strategy p** ?\<sigma>W1 w" using winning_strategy_updates[of "p**" \<sigma>W1 w v w] \<sigma>W1 `v\<rightarrow>w` by blast
                thus ?thesis using strategy_extends_backwards_VVpstar[of v p ?\<sigma>W1 w] `v \<in> VV p**` `v\<rightarrow>w` `strategy p** ?\<sigma>W1` by auto
              qed
              ultimately have "v \<in> W1" using W1_def \<sigma>W1(1) `v \<in> VV p**` by blast
              hence False using `v \<in> V'` V'_def U_def by blast
            }
            hence "w \<notin> W1" by blast
            hence "w \<in> attractor p K" using not_in_V' V_decomp `v\<rightarrow>w` by blast
          }
          (* All successors of v point to attractor p K, so v \<in> attractor p K *)
          hence "v \<in> attractor p K" using `v \<in> VV p**` attractor_set_VVpstar `\<not>deadend v` by blast
          hence False using `v \<in> V'` V'_def by blast
        }
        ultimately have False by blast
      }
      thus "\<not>Digraph.deadend G' v" by blast
    qed

    {
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"

      (* Apply the induction hypothesis to get the winning regions of G'. *)
      have G'_winning_regions: "\<exists>p \<sigma>. G'.strategy p \<sigma> \<and> G'.winning_strategy p \<sigma> v" proof-
        have "card (\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>) < card (\<omega> ` V)" proof-
          { assume "min_prio \<in> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>"
            then obtain v where v: "v \<in> V\<^bsub>G'\<^esub>" "\<omega>\<^bsub>G'\<^esub> v = min_prio" by blast
            hence "v \<in> \<omega> -` {min_prio}" using `\<omega>\<^bsub>G'\<^esub> = \<omega>` by simp
            hence False using V'_def K_def attractor_set_base `V\<^bsub>G'\<^esub> = V'` v(1)
              by (metis DiffD1 DiffD2 IntI contra_subsetD)
          }
          hence "min_prio \<notin> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>" by blast
          moreover have "min_prio \<in> \<omega> ` V"
            unfolding min_prio_def using priorities_finite Min_in assms(1) by blast
          moreover have "\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub> \<subseteq> \<omega> ` V" unfolding G'_def by simp
          ultimately show ?thesis by (metis priorities_finite psubsetI psubset_card_mono)
        qed
        thus ?thesis using IH[of G'] `v \<in> V\<^bsub>G'\<^esub>` G'_no_deadends G'.ParityGame by blast
      qed

      (* It turns out the winning region of player p** is empty. *)
      have "\<exists>\<sigma>. G'.strategy p \<sigma> \<and> G'.winning_strategy p \<sigma> v" proof (rule ccontr)
        assume "\<not>?thesis"
        moreover obtain p' \<sigma> where p': "G'.strategy p' \<sigma>" "G'.winning_strategy p' \<sigma> v"
          using G'_winning_regions by blast
        ultimately have "p' \<noteq> p" by blast
        hence "p' = p**" by (cases p; cases p') auto
        with p' have \<sigma>: "G'.strategy p** \<sigma>" "G'.winning_strategy p** \<sigma> v" by simp_all

        have "\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v" proof (rule exI, rule conjI)
          def \<sigma>' \<equiv> "override_on (override_on \<sigma>_arbitrary \<sigma>W1 W1) \<sigma> V'"
          show "strategy p** \<sigma>'" proof-
            {
              fix v assume v: "v \<in> VV p**" "\<not>deadend v"
              have "v \<rightarrow> \<sigma>' v" proof (cases)
                assume "v \<in> V'"
                hence "v \<in> G'.VV p**" using subgame_VV[of "p**"] `v \<in> VV p**` G'_def by fastforce
                moreover have "\<not>G'.deadend v" using G'_no_deadends `v \<in> V'` `V\<^bsub>G'\<^esub> = V'` by blast
                ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma> v" using \<sigma>(1) G'.strategy_def[of "p**" \<sigma>] by blast
                moreover have "\<sigma> v = \<sigma>' v" unfolding \<sigma>'_def using `v \<in> V'` by simp
                ultimately show ?thesis using `E\<^bsub>G'\<^esub> \<subseteq> E` G'_def by fastforce
              next
                assume "v \<notin> V'"
                thus ?thesis unfolding \<sigma>'_def using v valid_arbitrary_strategy \<sigma>W1(1)
                  unfolding strategy_def by (metis (no_types, lifting) override_on_def)
              qed
            }
            thus ?thesis unfolding strategy_def by blast
          qed
          show "winning_strategy p** \<sigma>' v"
          proof (unfold winning_strategy_def, intro allI impI, rule ccontr)
            fix P assume "vmc_path G P v p** \<sigma>'"
            then interpret vmc_path G P v "p**" \<sigma>' .
            assume "\<not>winning_path p** P"
            (* First we show that P stays in V', because if it stays in V', then it conforms to \<sigma>,
            so it must be winning for p**. *)
            have "lset P \<subseteq> V'" proof (rule ccontr)
              (* Assume P does not stay in V'. *)
              assume "\<not>lset P \<subseteq> V'"
              (* Then there exists a minimal n where it leaves V', which cannot be 0. *)
              hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> V'" by (simp add: lset_subset)
              then obtain n where n: "enat n < llength P" "P $ n \<notin> V'"
                "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> V')"
                using ex_least_nat_le[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> V'"] by blast
              have n_min: "\<And>i. i < n \<Longrightarrow> P $ i \<in> V'"
                using n(1) n(3) dual_order.strict_trans enat_ord_simps(2) by blast
              have "n \<noteq> 0" using n(2) `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> = V'` by (metis P_0)
              then obtain n' where n': "Suc n' = n" using not0_implies_Suc by blast
              hence "P $ n' \<in> V'" using n_min by blast
              have "P $ n' \<in> VV p" proof (rule ccontr)
                (* Assume that P leaves V' from a p** node x. P conforms to \<sigma> on V'.  On p** nodes
                \<sigma> always chooses a successor in V', so x cannot be a p** node. *)
                assume "P $ n' \<notin> VV p"
                hence "P $ n' \<in> VV p**" using `P $ n' \<in> V'` `V' \<subseteq> V` by auto
                hence "\<sigma>' (P $ n') = P $ Suc n'" using n' n(1) vmc_path_conforms by blast
                hence *: "\<sigma> (P $ n') = P $ Suc n'" using \<sigma>'_def `P $ n' \<in> V'` by auto
                have "\<not>G'.deadend (P $ n')"
                  using `P $ n' \<in> V'` G'_no_deadends `V\<^bsub>G'\<^esub> = V'` by blast
                moreover have "P $ n' \<in> G'.VV p**"
                  using `P $ n' \<in> VV p**` `P $ n' \<in> V'` subgame_VV[of "p**" V'] G'_def by fastforce
                ultimately have "P $ n' \<rightarrow>\<^bsub>G'\<^esub> \<sigma> (P $ n')"
                  using \<sigma>(1)[unfolded G'.strategy_def] `P $ n' \<in> VV p**` by blast
                hence "P $ n' \<rightarrow>\<^bsub>G'\<^esub> P $ n" using * n' by simp
                hence "P $ n \<in> V'" using `V\<^bsub>G'\<^esub> = V'` by blast
                thus False using n(2) by blast
              qed
              show False proof (cases)
                (* P leaves V' to enter W1.  This is fatal for player p. *)
                assume "P $ n \<in> W1"
                def P' \<equiv> "ldropn n P"
                (* P' is winning in W1 because \<sigma>' is \<sigma>W1 on W1. *)
                interpret vmc_path G P' "P $ n" "p**" \<sigma>'
                  unfolding P'_def using n(1) vmc_path_ldropn by auto
                have "path_conforms_with_strategy p** P' \<sigma>W1" proof-
                  { fix v assume "v \<in> V" "\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v"
                    hence "v \<in> W1" unfolding W1_def by blast
                    hence "\<sigma>W1 v = \<sigma>' v" by (simp add: U_def V'_def \<sigma>'_def)
                  }
                  hence "lset P' \<subseteq> W1"
                    using W1_def paths_stay_in_winning_region \<sigma>W1 `P $ n \<in> W1` vmc_path
                    by blast
                  moreover have "\<And>v. v \<in> W1 \<Longrightarrow> \<sigma>' v = \<sigma>W1 v" by (simp add: U_def V'_def \<sigma>'_def)
                  moreover have "path_conforms_with_strategy p** P' \<sigma>'" unfolding P'_def by simp
                  ultimately show ?thesis
                    by (metis path_conforms_with_strategy_irrelevant_updates subsetCE)
                qed
                then interpret vmc_path G P' "P $ n" "p**" \<sigma>W1 using conforms_to_another_strategy by blast
                have "winning_path p** P'"
                  using \<sigma>W1(2) `P $ n \<in> W1` vmc_path winning_strategy_def by blast
                hence "winning_path p** P"
                  unfolding P'_def using winning_path_drop_add[OF `valid_path P`] n(1) by blast
                thus False using `\<not>winning_path p** P` by blast
              next
                (* P leaves V' to enter attractor p K.  Then P $ n' must already be in the
                attractor because there is an edge, which is a contradiction to P $ n' \<in> V'. *)
                assume "P $ n \<notin> W1"
                hence "P $ n \<in> attractor p K"
                  using V_decomp n(2) P_valid n(1) valid_path_finite_in_V' by blast
                moreover have "P $ n' \<rightarrow> P $ n" using P_valid n' n(1) valid_path_impl1 by blast
                ultimately have "P $ n' \<in> attractor p K" using `P $ n' \<in> VV p` attractor_set_VVp by blast
                thus False using `P $ n' \<in> V'` V'_def by blast
              qed
            qed (* lset P \<subseteq> V' *)
            hence "G'.valid_path P" using subgame_valid_path by simp
            moreover have "G'.maximal_path P"
              using `lset P \<subseteq> V'` subgame_maximal_path `V' \<subseteq> V` by simp
            moreover have "G'.path_conforms_with_strategy p** P \<sigma>" proof-
              have "G'.path_conforms_with_strategy p** P \<sigma>'"
                using subgame_path_conforms_with_strategy `V' \<subseteq> V` `lset P \<subseteq> V'`
                by simp
              moreover have "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma>' v = \<sigma> v" using `lset P \<subseteq> V'` \<sigma>'_def by auto
              ultimately show ?thesis
                using G'.path_conforms_with_strategy_irrelevant_updates by blast
            qed
            ultimately have "G'.winning_path p** P"
              using \<sigma>(2) G'.winning_strategy_def G'.valid_maximal_conforming_path_0 P_0 P_not_null
              by blast
            moreover have "G'.VV p**** \<subseteq> VV p****"
              using subgame_VV_subset G'_def by blast
            ultimately show False
              using G'.winning_path_supergame[of "p**"] `\<omega>\<^bsub>G'\<^esub> = \<omega>` `\<not>winning_path p** P` ParityGame
              by blast
          qed
        qed
        moreover have "v \<in> V" using `V\<^bsub>G'\<^esub> \<subseteq> V` `v \<in> V\<^bsub>G'\<^esub>` by blast
        ultimately have "v \<in> W1" unfolding W1_def by blast
        thus False using `v \<in> V\<^bsub>G'\<^esub>` using U_def V'_def `V\<^bsub>G'\<^esub> = V'` `v \<in> V\<^bsub>G'\<^esub>` by blast
      qed
    } note recursion = this

    obtain \<sigma>1
      where \<sigma>1: "strategy p \<sigma>1"
                "strategy_attracts p \<sigma>1 (attractor p K) K"
      using attractor_has_strategy[of K p] K_def U_def by auto
    obtain \<sigma>2
      where \<sigma>2: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> G'.strategy p \<sigma>2"
                "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> G'.winning_strategy p \<sigma>2 v"
      using G'.merge_winning_strategies[of "V\<^bsub>G'\<^esub>"] recursion by blast

    def choose \<equiv> "\<lambda>v. SOME w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)"
    def \<sigma> \<equiv> "override_on (override_on choose \<sigma>2 V') \<sigma>1 (attractor p K - K)"

    have "attractor p K \<inter> W1 = {}" proof (rule ccontr)
      assume "attractor p K \<inter> W1 \<noteq> {}"
      then obtain v where v: "v \<in> attractor p K" "v \<in> W1" by blast
      hence "v \<in> V" using W1_def by blast
      obtain P where "vmc2_path G P v p \<sigma>1 \<sigma>W1"
        using strategy_conforming_path_exists \<sigma>W1(1) \<sigma>1(1) `v \<in> V` by blast
      then interpret vmc2_path G P v p \<sigma>1 \<sigma>W1 .
      have "strategy_attracts_via p \<sigma>1 v (attractor p K) K" using v(1) \<sigma>1(2) strategy_attracts_def by blast
      hence "lset P \<inter> K \<noteq> {}" using strategy_attracts_viaE visits_via_visits by blast
      hence "\<not>lset P \<subseteq> W1" unfolding K_def U_def by blast
      thus False unfolding W1_def using comp.paths_stay_in_winning_region \<sigma>W1 v(2) by auto
    qed

    have \<sigma>_\<sigma>1 [simp]: "\<And>v. v \<in> attractor p K - K \<Longrightarrow> \<sigma> v = \<sigma>1 v" unfolding \<sigma>_def by simp
    have \<sigma>_\<sigma>2 [simp]: "\<And>v. v \<in> V' \<Longrightarrow> \<sigma> v = \<sigma>2 v" unfolding \<sigma>_def V'_def by auto
    have \<sigma>_K [simp]: "\<And>v. v \<in> K \<union> W1 \<Longrightarrow> \<sigma> v = choose v" proof-
      fix v assume "v \<in> K \<union> W1"
      moreover hence "v \<notin> V'" unfolding V'_def U_def using attractor_set_base by auto
      ultimately show "\<sigma> v = choose v" unfolding \<sigma>_def U_def using `attractor p K \<inter> W1 = {}`
        by (metis (mono_tags, lifting) Diff_iff IntI UnE override_on_def override_on_emptyset)
    qed

    { fix v assume v: "v \<in> VV p"
      hence "\<not>deadend v" using no_deadends by blast
      have "\<exists>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)" proof (cases)
        assume "v \<in> W1"
        thus ?thesis using no_deadends `\<not>deadend v` by blast
      next
        assume "v \<notin> W1"
        show ?thesis proof (rule ccontr)
          assume "\<not>(\<exists>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1))"
          hence "\<And>w. v\<rightarrow>w \<Longrightarrow> winning_strategy p** \<sigma>W1 w" using \<sigma>W1(2) by blast
          hence "winning_strategy p** \<sigma>W1 v" using strategy_extends_backwards_VVp \<sigma>W1(1) `v \<in> VV p` by blast
          hence "v \<in> W1" unfolding W1_def using \<sigma>W1(1) `\<not>deadend v` by blast
          thus False using `v \<notin> W1` by blast
        qed
      qed
      hence "v\<rightarrow>choose v" "v \<in> W1 \<or> choose v \<notin> W1" unfolding choose_def
        using someI_ex[of "\<lambda>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)"] by blast+
    } note choose_works = this

    have "strategy p \<sigma>" proof-
      { fix v assume v: "v \<in> VV p" "\<not>deadend v"
        hence "v \<in> attractor p K - K \<Longrightarrow> v\<rightarrow>\<sigma> v" using \<sigma>_\<sigma>1 \<sigma>1(1) v unfolding strategy_def by auto
        moreover have "v \<in> V' \<Longrightarrow> v\<rightarrow>\<sigma> v" proof-
          assume "v \<in> V'"
          moreover have "v \<in> V\<^bsub>G'\<^esub>" using `v \<in> V'` `V\<^bsub>G'\<^esub> = V'` by blast
          moreover have "v \<in> G'.VV p" using `G'.VV p = V' \<inter> VV p` `v \<in> V'` `v \<in> VV p` by blast
          moreover have "\<not>Digraph.deadend G' v" using G'_no_deadends `v \<in> V\<^bsub>G'\<^esub>` by blast
          ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma>2 v" using \<sigma>2(1) G'.strategy_def[of p \<sigma>2] by blast
          with `v \<in> V'` show "v\<rightarrow>\<sigma> v" using `E\<^bsub>G'\<^esub> \<subseteq> E` \<sigma>_\<sigma>2 by (metis subsetCE)
        qed
        moreover have "v \<in> K \<union> W1 \<Longrightarrow> v\<rightarrow>\<sigma> v" using choose_works(1) v by auto
        moreover have "v \<in> V" using `v \<in> VV p` by blast
        ultimately have "v\<rightarrow>\<sigma> v" using V_decomp by blast
      }
      thus ?thesis unfolding strategy_def by blast
    qed

    have \<sigma>_attracts: "strategy_attracts p \<sigma> (attractor p K) K" proof-
      have "strategy_attracts p (override_on \<sigma> \<sigma>1 (attractor p K - K)) (attractor p K) K"
        using strategy_attracts_irrelevant_override \<sigma>1 `strategy p \<sigma>` by blast
      moreover have "\<sigma> = override_on \<sigma> \<sigma>1 (attractor p K - K)" by (rule ext) (simp add: override_on_def)
      ultimately show ?thesis by simp
    qed

    (* Show that \<sigma> is a winning strategy on V - W1. *)
    have "\<forall>v \<in> V - W1. winning_strategy p \<sigma> v" proof-
      {
        fix v P assume P: "v \<in> V - W1" "vmc_path G P v p \<sigma>"
        interpret vmc_path G P v p \<sigma> using P(2) .
        have "\<not>lfinite P"
          using no_deadends lfinite_lset maximal_ends_on_deadend[of P] P_maximal P_not_null lset_P_V
          by blast
        have "lset P \<subseteq> V - W1" proof
          fix v' assume "v' \<in> lset P"
          thus "v' \<in> V - W1" using P proof (induct arbitrary: v rule: llist_set_induct)
            case (find P')
            interpret vmc_path G P' v p \<sigma> using find.prems(2) .
            show ?case using P_v0 find.prems(1) by blast
          next
            case (step P' v')
            interpret vmc_path G P' v p \<sigma> using step.prems(2) .
            interpret vmc_path_no_deadend G P' v p \<sigma>
              by (rule vmc_path_lnull_ltl_no_deadend) (metis DiffE Diff_empty lset_eq_empty step.hyps(2))
            have "w0 \<in> V - W1" proof (rule ccontr)
              assume "w0 \<notin> V - W1"
              hence "w0 \<in> W1" by simp
              show False proof (cases)
                assume "v \<in> VV p"
                hence "\<sigma> v = w0" using v0_conforms by blast
                hence "v \<notin> K" using choose_works(2)[OF `v \<in> VV p`] `v \<in> V - W1` `w0 \<in> W1` by auto
                moreover have "v \<notin> attractor p K - K" proof
                  assume *: "v \<in> attractor p K - K"
                  hence "visits_via P' (attractor p K) K"
                    using \<sigma>_attracts strategy_attractsE by blast
                  then obtain n where
                    n: "enat n < llength P' \<and> P' $ n \<in> K \<and> lset (ltake (enat n) P') \<subseteq> attractor p K"
                       "\<And>i. i < n \<Longrightarrow>
                        \<not>(enat i < llength P' \<and> P' $ i \<in> K \<and> lset (ltake (enat i) P') \<subseteq> attractor p K)"
                    using ex_least_nat_le[of
                      "\<lambda>n. enat n < llength P' \<and> P' $ n \<in> K \<and> lset (ltake (enat n) P') \<subseteq> attractor p K"]
                    unfolding visits_via_def by blast
                  hence n_min: "\<And>i. i < n \<Longrightarrow> P' $ i \<notin> K" proof-
                    fix i assume "i < n"
                    moreover hence "enat i < llength P'"
                      using n(1) dual_order.strict_trans enat_ord_simps(2) by blast
                    moreover have "lset (ltake (enat i) P') \<subseteq> lset (ltake (enat n) P')"
                      using `i < n` lprefix_lset' by simp
                    ultimately show "P' $ i \<notin> K" using n by blast
                  qed
                  have "v \<notin> K" using * by blast
                  hence "n \<noteq> 0" using n(1) by (metis P_0)
                  have "w0 \<notin> K" using `w0 \<in> W1` K_def U_def by blast
                  hence "Suc 0 \<noteq> n" using n(1) P_Suc_0 by auto
                  hence "Suc (Suc 0) \<le> n" using `n \<noteq> 0` by presburger
                  hence "lset (ltake (enat (Suc (Suc 0))) P') \<subseteq> attractor p K"
                    using n by (meson enat_ord_simps(1) lprefix_lset' subset_trans)
                  hence "lset (ltake (eSuc (eSuc 0)) P') \<subseteq> attractor p K"
                    by (simp add: eSuc_enat zero_enat_def)
                  hence "ltake (eSuc (eSuc 0)) P' $ Suc 0 \<in> attractor p K"
                    by (metis Ptl_not_null enat_ltl_Suc i0_less llength_eq_0 lset_lnth
                              ltake.disc(2) ltake_ltl zero_enat_def zero_ne_eSuc)
                  hence "w0 \<in> attractor p K" using P_Suc_0
                    by (metis P_not_null Ptl_not_null lnth_0_conv_lhd lnth_ltl ltake.disc(2)
                              ltake.simps(3) ltake_ltl zero_ne_eSuc)
                  thus False using `w0 \<in> W1` `attractor p K \<inter> W1 = {}` by blast
                qed
                moreover have "v \<notin> V'" proof
                  assume "v \<in> V'"
                  have "\<sigma>2 v \<in> V\<^bsub>G'\<^esub>" proof (rule G'.valid_strategy_in_V[of p \<sigma>2 v])
                    have "v \<in> V\<^bsub>G'\<^esub>" using `V\<^bsub>G'\<^esub> = V'` `v \<in> V'` by simp
                    thus "\<not>G'.deadend v" using G'_no_deadends by blast
                    show "G'.strategy p \<sigma>2" using \<sigma>2(1) `v \<in> V\<^bsub>G'\<^esub>` by blast
                    show "v \<in> G'.VV p" using `v \<in> VV p` `G'.VV p = V' \<inter> VV p` `v \<in> V'` by simp
                  qed
                  hence "w0 \<in> V\<^bsub>G'\<^esub>" using `v \<in> V'` `\<sigma> v = w0` by simp
                  thus False using `V\<^bsub>G'\<^esub> = V'` `w0 \<in> W1` V'_def U_def by blast
                qed
                ultimately show False using `v \<in> V - W1` V_decomp by blast
              next
                assume "v \<notin> VV p"
                hence "v \<in> VV p**" using step.prems(1) by blast
                let ?\<sigma> = "\<sigma>W1(v := w0)"
                have "winning_strategy p** \<sigma>W1 w0" using `w0 \<in> W1` \<sigma>W1(2) by blast
                moreover have "\<not>(\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v)"
                  using `v \<in> V - W1` W1_def by blast
                ultimately have "winning_strategy p** ?\<sigma> w0"
                  using winning_strategy_updates[of "p**" \<sigma>W1 w0 v w0] \<sigma>W1(1) `v\<rightarrow>w0` by blast
                moreover have "strategy p** ?\<sigma>" using `v\<rightarrow>w0` \<sigma>W1(1) valid_strategy_updates by blast
                ultimately have "winning_strategy p** ?\<sigma> v"
                  using strategy_extends_backwards_VVpstar[of v p ?\<sigma> w0] `v \<in> VV p**` `v\<rightarrow>w0` by auto
                hence "v \<in> W1" unfolding W1_def using `strategy p** ?\<sigma>` `v \<in> V - W1` by blast
                thus False using `v \<in> V - W1` by blast
              qed
            qed
            thus "v' \<in> V - W1" using step.hyps(3) vmc_path_ltl by blast
          qed
        qed
        hence "lset P \<subseteq> attractor p K \<union> V'" using V_decomp by blast
        (* Every \<sigma>-conforming path starting in V - W1 is winning.  We distinguish two cases:
           1. P eventually stays in V'.  Then P is winning because \<sigma>2 is winning.
           2. P visits K infinitely often.  Then P is winning because of the priority of K.
        *)
        have "winning_path p P" proof (cases)
          assume "\<exists>n. lset (ldropn n P) \<subseteq> V'"
          (* P eventually stays in V'. *)
          then obtain n where n: "lset (ldropn n P) \<subseteq> V'" by blast
          def P' \<equiv> "ldropn n P"
          have "\<not>lnull P'" using P'_def `\<not>lfinite P` infinite_no_deadend lfinite_ldropn by blast
          moreover have "lset P' \<subseteq> V'" using P'_def n by simp
          ultimately have "lhd P' \<in> V'" by auto
          hence "V' \<inter> V \<noteq> {}" using `V' \<subseteq> V` by auto
          interpret vmc_path G' P' "lhd P'" p \<sigma>2 proof
            show "\<not>lnull P'" using `\<not>lnull P'` .
            show "G'.valid_path P'" proof-
              have "valid_path P'" unfolding P'_def by simp
              thus ?thesis using subgame_valid_path `lset P' \<subseteq> V'` `V' \<inter> V \<noteq> {}` G'_def by blast
            qed
            show "G'.maximal_path P'" proof-
              have "maximal_path P'" unfolding P'_def by simp
              thus ?thesis
                using subgame_maximal_path `lset P' \<subseteq> V'` `V' \<inter> V \<noteq> {}` `V' \<subseteq> V` G'_def by blast
            qed
            show "G'.path_conforms_with_strategy p P' \<sigma>2" proof-
              have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def by simp
              hence "path_conforms_with_strategy p P' \<sigma>2"
                using path_conforms_with_strategy_irrelevant_updates `lset P' \<subseteq> V'` \<sigma>_\<sigma>2 by blast
              thus ?thesis
                using subgame_path_conforms_with_strategy `lset P' \<subseteq> V'` `V' \<inter> V \<noteq> {}` `V' \<subseteq> V` G'_def
                by blast
            qed
          qed simp
          have "P' $ 0 = lhd P'" using `\<not>lnull P'` lnth_0_conv_lhd by blast
          moreover have "G'.winning_strategy p \<sigma>2 (lhd P')"
            using `lset P' \<subseteq> V'` `\<not>lnull P'` \<sigma>2(2)[of "lhd P'"] `V\<^bsub>G'\<^esub> = V'` llist.set_sel(1)
            by blast
          ultimately have "G'.winning_path p P'" using G'.winning_strategy_def vmc_path by blast
          moreover have "G'.VV p** \<subseteq> VV p**" unfolding G'_def using subgame_VV by simp
          ultimately have "winning_path p P'"
            using G'.winning_path_supergame[of p P' G] `\<omega>\<^bsub>G'\<^esub> = \<omega>` ParityGame by blast
          thus ?thesis
            using P'_def infinite_small_llength[OF `\<not>lfinite P`]
                  winning_path_drop_add[of P p n] `valid_path P`
            by blast
        next
          assume "\<not>(\<exists>n. lset (ldropn n P) \<subseteq> V')"
          (* P visits K infinitely often. *)
          hence *: "\<And>n. \<not>lset (ldropn n P) \<subseteq> V'" by blast
          have *: "\<And>n. \<exists>k \<ge> n. P $ k \<notin> V'" proof-
            fix n
            obtain k where k: "ldropn n P $ k \<notin> V'" using * by (metis path_set_at subsetI)
            hence "P $ k + n \<notin> V'" using lnth_ldropn[of n k P] infinite_small_llength `\<not>lfinite P` by metis
            thus "\<exists>k \<ge> n. P $ k \<notin> V'" using le_add2 by blast
          qed
          have "\<And>n. \<exists>k \<ge> n. P $ k \<in> attractor p K" proof-
            fix n obtain k where "k \<ge> n" "P $ k \<notin> V'" using * by blast
            thus "\<exists>k \<ge> n. P $ k \<in> attractor p K" using `\<not>lfinite P` `lset P \<subseteq> V - W1`
              by (metis DiffI U_def V'_def llist_set_nth)
          qed
          moreover have "\<And>k. P $ k \<in> attractor p K \<Longrightarrow> \<exists>n \<ge> k. P $ n \<in> K" proof-
            fix k
            interpret vmc_path G "ldropn k P" "P $ k" p \<sigma>
              using vmc_path_ldropn[OF infinite_small_llength[OF `\<not>lfinite P`]] by blast
            assume "P $ k \<in> attractor p K"
            then obtain n where "ldropn k P $ n \<in> K"
              by (meson G'.visits_via_def \<sigma>_attracts strategy_attractsE)
            hence "P $ n + k \<in> K" using lnth_ldropn infinite_small_llength[OF `\<not>lfinite P`] by simp
            thus "\<exists>n \<ge> k. P $ n \<in> K" using le_add2 by blast
          qed
          ultimately have *: "\<And>n. \<exists>k \<ge> n. P $ k \<in> K" by (meson dual_order.trans)
          hence *: "\<And>n. lset (ldropn n P) \<inter> K \<noteq> {}" proof-
            fix n
            obtain k where k: "k \<ge> n" "P $ k \<in> K" using * by blast
            have "ldropn n P $ k - n = P $ (k - n) + n"
              using k(1) lnth_ldropn[of n "k - n" P] infinite_small_llength `\<not>lfinite P` by blast
            hence "ldropn n P $ k - n \<in> K" using k by simp
            thus "lset (ldropn n P) \<inter> K \<noteq> {}"
              by (meson `\<not>lfinite P` disjoint_iff_not_equal lfinite_ldropn llist_nth_set)
          qed
          {
            fix n
            obtain v where v: "v \<in> lset (ldropn n P)" "v \<in> K" using * by blast
            have "\<omega> v = min_prio" using K_def v(2) by blast
            hence "min_prio \<in> lset (ldropn n (lmap \<omega> P))" using v(1) by auto
          }
          hence "min_prio \<in> path_inf_priorities P" unfolding path_inf_priorities_def by blast
          moreover {
            fix a assume "a \<in> path_inf_priorities P"
            hence "a \<in> lset (ldropn 0 (lmap \<omega> P))" unfolding path_inf_priorities_def by blast
            hence "a \<in> \<omega> ` lset P" by simp
            then obtain v where "v \<in> lset P" "\<omega> v = a" by blast
            hence "min_prio \<le> a"
              unfolding min_prio_def using `lset P \<subseteq> V` priorities_finite Min_le by blast
          }
          ultimately show ?thesis unfolding winning_path_def
            using `winning_priority p min_prio` `\<not>lfinite P` by blast
        qed
      }
      thus ?thesis unfolding winning_strategy_def by blast
    qed
    hence "\<forall>v \<in> V. \<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" using W1_def `strategy p \<sigma>` by blast
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" using `v \<in> V` by simp
  }
  moreover have "\<exists>p. winning_priority p (Min (\<omega> ` V))" by auto
  ultimately show ?thesis by blast
qed

theorem positional_strategy_exists_without_deadends:
  assumes "v \<in> V" "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  using assms ParityGame
  by (induct "card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>)" arbitrary: G v rule: nat_less_induct)
     (rule ParityGame.positional_strategy_induction_step, simp_all)

(* Prove a stronger version of the previous theorem: Allow deadends.
   This is the main theorem. *)
theorem positional_strategy_exists:
  assumes "v0 \<in> V"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0"
proof-
  let ?deadends = "\<lambda>p. {v \<in> VV p. deadend v}"
  have deadends_in_V: "\<And>p. ?deadends p \<subseteq> V" by auto
  { fix p
    def A \<equiv> "attractor p (?deadends p**)"
    assume v_in_attractor: "v0 \<in> attractor p (?deadends p**)"
    then obtain \<sigma> where \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> A (?deadends p**)"
      using attractor_has_strategy[of "?deadends p**" "p"] A_def deadends_in_V by blast

    have "A \<subseteq> V" using A_def using attractor_is_bounded_by_V deadends_in_V by blast
    hence "A - ?deadends p** \<subseteq> V" by auto

    have "winning_strategy p \<sigma> v0" proof (unfold winning_strategy_def, intro allI impI)
      fix P assume P: "vmc_path G P v0 p \<sigma>"
      then interpret vmc_path G P v0 p \<sigma> .
      from \<sigma>(2) v_in_attractor
        obtain i where i_def: "enat i < llength P" "P $ i \<in> ?deadends p**" "lset (ltake (enat i) P) \<subseteq> A"
        using A_def strategy_attractsE[unfolded visits_via_def] by blast
      have *: "enat (Suc i) = llength P" using P_ends_on_deadend i_def(1) i_def(2) by auto
      have "llast P \<in> VV p**" proof-
        have "eSuc (enat i) = llength P" by (simp add: * eSuc_enat)
        moreover have "P $ i \<in> VV p**" using i_def by blast
        ultimately show ?thesis by (metis llast_conv_lnth)
      qed
      thus "winning_path p P"
        using winning_path_def llength_eq_enat_lfiniteD[of P "Suc i"] * by simp
    qed
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0" using \<sigma> by blast
  } note lemma_path_to_deadend = this
  def A \<equiv> "\<lambda>p. attractor p (?deadends p**)"
  def V' \<equiv> "V - A Even - A Odd"
  hence "V' \<subseteq> V" by blast
  show ?thesis proof (cases)
    assume "v0 \<in> V'"
    hence "V' \<inter> V \<noteq> {}" using `v0 \<in> V` by blast
    def G' \<equiv> "subgame V'"
    have "ParityGame G'" using `V' \<inter> V \<noteq> {}` unfolding G'_def using subgame_ParityGame by blast
    then interpret G': ParityGame G' .
    have "V\<^bsub>G'\<^esub> = V'" unfolding G'_def using `V' \<subseteq> V` by simp
    hence "v0 \<in> V\<^bsub>G'\<^esub>" using `v0 \<in> V'` by simp
    moreover have V'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>G'.deadend v" proof
      fix v assume "v \<in> V\<^bsub>G'\<^esub>" "G'.deadend v"
      hence "v \<in> V'" "v \<in> V" unfolding G'_def subgame_def by simp_all
      show False proof (cases)
        assume "deadend v"
        { fix p assume "v \<in> VV p**"
          hence "v \<in> attractor p (?deadends p**)" using `deadend v`
            using attractor_set_base[of "?deadends p**" p] by blast
          hence False using `v \<in> V'` unfolding V'_def A_def by (cases p) simp_all
        }
        thus False using `v \<in> V` by auto
      next
        assume "\<not>deadend v"
        hence "\<exists>w. v\<rightarrow>w" by auto
        have all_in_attractor:
          "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> attractor Even (?deadends Even**) \<or> w \<in> attractor Odd (?deadends Odd**)"
        proof (rule ccontr)
          fix w
          assume "v\<rightarrow>w"
             and "\<not>(w \<in> attractor Even (?deadends Even**) \<or> w \<in> attractor Odd (?deadends Odd**))"
          hence "w \<in> V'" unfolding V'_def using A_def by blast
          hence "w \<in> V\<^bsub>G'\<^esub>" unfolding G'_def subgame_def using `v\<rightarrow>w` by auto
          hence "v \<rightarrow>\<^bsub>G'\<^esub> w" using `v\<rightarrow>w` `v \<in> V\<^bsub>G'\<^esub>` unfolding G'_def subgame_def by auto
          thus False using `G'.deadend v` using `w \<in> V\<^bsub>G'\<^esub>` by blast
        qed
        { fix p assume "v \<in> VV p"
          { assume "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p (?deadends p**)"
            hence "v \<in> attractor p (?deadends p**)" using `v \<in> VV p` attractor_set_VVp by blast
            hence False using `v \<in> V'` unfolding V'_def A_def by (cases p) blast+
          }
          hence "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> attractor p** (?deadends p****)"
            using all_in_attractor by (cases p) auto
          hence "v \<in> attractor p** (?deadends p****)"
            using `\<not>deadend v` `v \<in> VV p` attractor_set_VVpstar by auto
          hence False using `v \<in> V'` unfolding V'_def A_def by (cases p) auto
        }
        thus False using `v \<in> V` by auto
      qed
    qed
    ultimately obtain p \<sigma> where \<sigma>: "G'.strategy p \<sigma>" "G'.winning_strategy p \<sigma> v0"
      using G'.positional_strategy_exists_without_deadends by blast

    have V'_no_deadends': "\<And>v. v \<in> V' \<Longrightarrow> \<not>deadend v" proof
      fix v assume "v \<in> V'" "deadend v"
      obtain p where "v \<in> VV p****" using `v \<in> V'` `V' \<subseteq> V` by blast
      hence "v \<in> A p**"
        unfolding A_def using `deadend v` attractor_set_base[of "?deadends p****" "p**"] by blast
      thus False using `v \<in> V'` unfolding V'_def by (cases p) auto
    qed

    obtain \<sigma>_attr
      where \<sigma>_attr: "strategy p \<sigma>_attr" "strategy_attracts p \<sigma>_attr (A p) (?deadends p**)"
      using attractor_has_strategy[OF `?deadends p** \<subseteq> V`] A_def by blast
    def \<sigma>' \<equiv> "override_on \<sigma> \<sigma>_attr (A Even \<union> A Odd)"
    have \<sigma>'_is_\<sigma>_on_V': "\<And>v. v \<in> V' \<Longrightarrow> \<sigma>' v = \<sigma> v"
      unfolding V'_def \<sigma>'_def A_def by (cases p) simp_all
    have "strategy p \<sigma>'" proof-
      { fix v assume v: "v \<in> VV p" "\<not>deadend v"
        have "v\<rightarrow>\<sigma>' v" proof (cases)
          assume "v \<in> V'"
          hence "v \<in> V\<^bsub>G'\<^esub>" unfolding G'_def subgame_def using `V' \<subseteq> V` by auto
          hence "v \<in> G'.VV p" unfolding G'_def subgame_def using `v \<in> VV p` by auto
          moreover have "\<not>G'.deadend v" using V'_no_deadends `v \<in> V\<^bsub>G'\<^esub>` by blast
          ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma> v" using \<sigma>(1)[unfolded G'.strategy_def] by blast
          hence "v \<rightarrow> \<sigma> v" unfolding G'_def subgame_def by auto
          thus ?thesis using \<sigma>'_is_\<sigma>_on_V' `v \<in> V'` by simp
        next
          assume "v \<notin> V'"
          hence "\<sigma>' v = \<sigma>_attr v"
            unfolding \<sigma>'_def V'_def A_def by (cases p) (insert v(2), auto)
          thus ?thesis using v \<sigma>_attr(1)[unfolded strategy_def] by auto
        qed
      }
      thus ?thesis unfolding strategy_def by blast
    qed
    moreover have "winning_strategy p \<sigma>' v0" proof-
      { fix P assume "vmc_path G P v0 p \<sigma>'"
        then interpret vmc_path G P v0 p \<sigma>' .
        interpret vmc_path_no_deadend G P v0 p \<sigma>'
          using V'_no_deadends' `v0 \<in> V'` by unfold_locales
        assume contra: "\<not>winning_path p P"
        have contra': "winning_path p** P"
          by (simp add: contra paths_are_winning_for_exactly_one_player)

        have "lset P \<inter> A p = {}" proof (rule ccontr)
          assume "lset P \<inter> A p \<noteq> {}"
          have "strategy_attracts p (override_on \<sigma>' \<sigma>_attr (A p - ?deadends p**))
                                    (A p)
                                    (?deadends p**)"
            using strategy_attracts_irrelevant_override[OF \<sigma>_attr(2) \<sigma>_attr(1) `strategy p \<sigma>'`]
            by blast
          moreover have "override_on \<sigma>' \<sigma>_attr (A p - ?deadends p**) = \<sigma>'"
            by (rule ext, unfold \<sigma>'_def, cases p) (simp_all add: override_on_def)
          ultimately have "strategy_attracts p \<sigma>' (A p) (?deadends p**)" by simp
          hence "lset P \<inter> ?deadends p** \<noteq> {}"
            using `lset P \<inter> A p \<noteq> {}` attracted_path[OF `?deadends p** \<subseteq> V`] by simp
          then obtain n where n: "enat n < llength P" "P $ n \<in> VV p**" "deadend (P $ n)"
            using lset_intersect_lnth[of P "?deadends p**"] by blast
          have *: "llength P = enat (Suc n)" using n(1) n(3) P_ends_on_deadend by simp
          have "lfinite P" using llength_eq_enat_lfiniteD[OF *] by simp
          moreover have "llast P \<in> VV p**" using n(2) * llast_def[of P] by simp
          ultimately show False using contra winning_path_def P_not_null by blast
        qed

        moreover have "lset P \<inter> A p** = {}" proof-
          { fix v assume "v \<in> lset P"
            hence "v \<notin> A p**" using vmc_path `v0 \<in> V'` `lset P \<inter> A p = {}`
            proof (induct arbitrary: v0 rule: llist_set_induct)
              case (find P v0)
              interpret vmc_path G P v0 p \<sigma>' using find.prems(1) .
              show ?case using V'_def find.prems(2) by auto
            next
              case (step P v v0)
              interpret P: vmc_path G P v0 p \<sigma>' using step.prems(1) .
              have "\<not>deadend v0" using V'_no_deadends' `v0 \<in> V'` by blast
              then interpret P: vmc_path_no_deadend G P v0 p \<sigma>' by unfold_locales
              have "P.w0 \<in> V'" proof-
                have "P.w0 \<notin> A p" using step.prems(3) P.w0_lset_P by blast
                moreover have "P.w0 \<notin> A p**" proof
                  assume "P.w0 \<in> A p**"
                  moreover have "v0 \<in> VV p**" proof (rule ccontr)
                    assume "v0 \<notin> VV p**"
                    hence "v0 \<in> VV p" by simp
                    hence "v0 \<in> G'.VV p" unfolding G'_def using subgame_VV `v0 \<in> V'` by blast
                    moreover have "v0 \<in> V\<^bsub>G'\<^esub>" using `V\<^bsub>G'\<^esub> = V'` `v0 \<in> V'` by simp
                    moreover hence "\<not>G'.deadend v0" using V'_no_deadends by blast
                    ultimately have "\<sigma> v0 \<in> V\<^bsub>G'\<^esub>" using \<sigma>(1)[unfolded G'.strategy_def] by blast
                    hence "\<sigma>' v0 \<in> V'" by (simp add: \<sigma>'_is_\<sigma>_on_V' step.prems(2) `V\<^bsub>G'\<^esub> = V'`)
                    moreover have "\<sigma>' v0 = P.w0" using `v0 \<in> VV p` P.v0_conforms by blast
                    ultimately have "P.w0 \<in> V'" by simp
                    thus False using `P.w0 \<in> A p**` unfolding V'_def by (cases p) auto
                  qed
                  ultimately have "v0 \<in> A p**"
                    using A_def `v0\<rightarrow>P.w0` attractor_outside by blast
                  thus False using `v0 \<in> V'` unfolding V'_def by (cases p) auto
                qed
                ultimately show "P.w0 \<in> V'" unfolding V'_def using A_def by (cases p) auto
              qed
              moreover have "lset (ltl P) \<inter> A p = {}" using in_lset_ltlD step.prems(3) by fastforce
              ultimately show "v \<notin> A p**" using step.hyps(3)[OF P.vmc_path_ltl] by blast
            qed
          }
          thus ?thesis by blast
        qed

        ultimately have "lset P \<subseteq> V'"
          unfolding V'_def using lset_P_V by (cases p) (simp_all add: Diff_Int_distrib le_iff_inf)
        then interpret vmc_path G' P v0 p \<sigma>'
          unfolding G'_def using subgame_path_vmc_path[OF `V' \<subseteq> V`] by blast
        have "G'.path_conforms_with_strategy p P \<sigma>" proof-
          have "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma>' v = \<sigma> v"
            using \<sigma>'_is_\<sigma>_on_V' `V\<^bsub>G'\<^esub> = V'` lset_P_V by blast
          thus "G'.path_conforms_with_strategy p P \<sigma>"
            using P_conforms G'.path_conforms_with_strategy_irrelevant_updates by blast
        qed
        then interpret vmc_path G' P v0 p \<sigma> using conforms_to_another_strategy by blast
        have *: "G'.winning_path p P" using \<sigma>(2)[unfolded G'.winning_strategy_def] vmc_path by blast
        have False using `\<not>winning_path p P`
          using G'.winning_path_supergame[OF * ParityGame, unfolded G'_def]
                subgame_VV_subset[of "p**" V'] subgame_\<omega>[of V']
          by blast
      }
      thus ?thesis unfolding winning_strategy_def by blast
    qed
    ultimately show ?thesis by blast
  next
    assume "v0 \<notin> V'"
    then obtain p where "v0 \<in> attractor p (?deadends p**)"
      unfolding V'_def A_def using `v0 \<in> V` by blast
    thus ?thesis using lemma_path_to_deadend[of p] by blast
  qed
qed

end -- "context ParityGame"

end
