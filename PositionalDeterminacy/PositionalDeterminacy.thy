section {* Positional determinacy of parity games *}

theory PositionalDeterminacy
imports
  Main
  AttractorStrategy
begin

context ParityGame begin

text {* Removing the attractor sets of deadends leaves a subgame without deadends. *}

lemma subgame_without_deadends:
  assumes V'_def: "V' = V - attractor p (deadends p**) - attractor p** (deadends p****)"
    (is "V' = V - ?A - ?B")
    and v: "v \<in> V\<^bsub>subgame V'\<^esub>"
  shows "\<not>Digraph.deadend (subgame V') v"
proof (cases)
  assume "deadend v"
  have v: "v \<in> V - ?A - ?B" using v unfolding V'_def subgame_def by simp
  { fix p' assume "v \<in> VV p'**"
    hence "v \<in> attractor p' (deadends p'**)"
      using `deadend v` attractor_set_base[of "deadends p'**" p']
      unfolding deadends_def by blast
    hence False using v by (cases p'; cases p) auto
  }
  thus ?thesis using v by blast
next
  assume "\<not>deadend v"
  have v: "v \<in> V - ?A - ?B" using v unfolding V'_def subgame_def by simp
  def G' \<equiv> "subgame V'"
  interpret G': ParityGame G' unfolding G'_def using subgame_ParityGame .
  show ?thesis proof
    assume "Digraph.deadend (subgame V') v"
    hence "G'.deadend v" unfolding G'_def .
    have all_in_attractor: "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> ?A \<or> w \<in> ?B" proof (rule ccontr)
      fix w
      assume "v\<rightarrow>w" "\<not>(w \<in> ?A \<or> w \<in> ?B)"
      hence "w \<in> V'" unfolding V'_def by blast
      hence "w \<in> V\<^bsub>G'\<^esub>" unfolding G'_def subgame_def using `v\<rightarrow>w` by auto
      hence "v \<rightarrow>\<^bsub>G'\<^esub> w" using `v\<rightarrow>w` assms(2) unfolding G'_def subgame_def by auto
      thus False using `G'.deadend v` using `w \<in> V\<^bsub>G'\<^esub>` by blast
    qed
    { fix p' assume "v \<in> VV p'"
      { assume "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor p' (deadends p'**)"
        hence "v \<in> attractor p' (deadends p'**)" using `v \<in> VV p'` attractor_set_VVp by blast
        hence False using v by (cases p'; cases p) auto
      }
      hence "\<And>w. v\<rightarrow>w \<Longrightarrow> w \<in> attractor p'** (deadends p'****)"
        using all_in_attractor by (cases p'; cases p) auto
      hence "v \<in> attractor p'** (deadends p'****)"
        using `\<not>deadend v` `v \<in> VV p'` attractor_set_VVpstar by auto
      hence False using v by (cases p'; cases p) auto
    }
    thus False using v by blast
  qed
qed

lemma (in vmc_path) vmc_path_lset_closed_subset:
  assumes VVp: "\<And>v. \<lbrakk> v \<in> S; \<not>deadend v; v \<in> VV p \<rbrakk> \<Longrightarrow> \<sigma> v \<in> S \<union> T"
    and VVpstar: "\<And>v w. \<lbrakk> v \<in> S; \<not>deadend v; v \<in> VV p** ; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<in> S \<union> T"
    and v0: "v0 \<in> S"
    and "lset P \<inter> T = {}"
  shows "lset P \<subseteq> S"
proof
  fix v assume "v \<in> lset P"
  thus "v \<in> S" using vmc_path assms(3,4)
  proof (induct arbitrary: v0 rule: llist_set_induct)
    case (find P)
    interpret vmc_path G P v0 p \<sigma> using find.prems(1) .
    show ?case by (simp add: find.prems(2))
  next
    case (step P v v0)
    interpret vmc_path G P v0 p \<sigma> using step.prems(1) .
    have "\<not>lnull (ltl P)" using step.hyps(2) by (metis emptyE lset_eq_empty)
    then interpret vmc_path_no_deadend G P v0 p \<sigma> using vmc_path_lnull_ltl_no_deadend by blast
    have "w0 \<in> S \<union> T" proof (cases)
      assume "v0 \<in> VV p"
      hence "\<sigma> v0 \<in> S \<union> T" using assms(1) step.prems(2) v0_no_deadend by blast
      thus "w0 \<in> S \<union> T" using v0_conforms `v0 \<in> VV p` by simp
    next
      assume "v0 \<notin> VV p"
      thus "w0 \<in> S \<union> T" using `v0\<rightarrow>w0` assms(2) step.prems(2) v0_no_deadend by auto
    qed
    hence "w0 \<in> S" using step.prems(3) w0_lset_P by blast
    moreover have "lset (ltl P) \<inter> T = {}" using step.prems(3)
      by (meson disjoint_eq_subset_Compl lset_ltl subset_trans)
    ultimately show "v \<in> S" using step.hyps(3)[of w0] by simp
  qed
qed

subsection {* Induction step *}

text {*
  The proof of positional determinacy is by induction over the size of the finite set
  @{term "\<omega> ` V"}, the set of priorities.  The following lemma is the induction step.

  For now, we assume there are no deadends in the graph.  Later we will get rid of this assumption.
*}

lemma positional_strategy_induction_step:
  assumes "v \<in> V"
    and no_deadends: "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
    and IH: "\<And>(G :: ('a, 'b) ParityGame_scheme) v.
      \<lbrakk> card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>) < card (\<omega> ` V); v \<in> V\<^bsub>G\<^esub>;
        ParityGame G;
        \<And>v. v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<not>Digraph.deadend G v  \<rbrakk>
      \<Longrightarrow> \<exists>p \<sigma>. ParityGame.strategy G p \<sigma> \<and> ParityGame.winning_strategy G p \<sigma> v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
proof-
  {
    text {* First, we determine the minimum priority and the player who likes it. *}
    def min_prio \<equiv> "Min (\<omega> ` V)"
    fix p assume p: "winning_priority p min_prio"
    text {* Then we define the tentative winning region of player @{term "p**"}.
      The rest of the proof is to show that this is the complete winning region.
    *}
    def W1 \<equiv> "winning_region p**"
    text {* For this, we define several more sets of nodes.
      First, @{text U} is the tentative winning region of player @{term p}.
    *}
    def U \<equiv> "V - W1"
    def K \<equiv> "U \<inter> (\<omega> -` {min_prio})"
    def V' \<equiv> "U - attractor p K"

    def [simp]: G' \<equiv> "subgame V'"
    interpret G': ParityGame G' using subgame_ParityGame by simp

    have U_equiv: "\<And>v. v \<in> V \<Longrightarrow> v \<in> U \<longleftrightarrow> v \<notin> winning_region p**"
      unfolding U_def W1_def by blast

    have "V' \<subseteq> V" unfolding U_def V'_def by blast
    hence [simp]: "V\<^bsub>G'\<^esub> = V'" unfolding G'_def by simp

    have "V\<^bsub>G'\<^esub> \<subseteq> V" "E\<^bsub>G'\<^esub> \<subseteq> E" "\<omega>\<^bsub>G'\<^esub> = \<omega>" unfolding G'_def by (simp_all add: subgame_\<omega>)
    have "G'.VV p = V' \<inter> VV p" unfolding G'_def using subgame_VV by simp

    have V_decomp: "V = attractor p K \<union> V' \<union> W1" proof-
      have "V \<subseteq> attractor p K \<union> V' \<union> W1"
        unfolding V'_def U_def by blast
      moreover have "attractor p K \<subseteq> V"
        using attractor_is_bounded_by_V[of K] unfolding K_def U_def by blast
      ultimately show ?thesis
        unfolding W1_def winning_region_def using `V' \<subseteq> V` by blast
    qed

    have G'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>G'.deadend v" proof-
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"
      hence *: "v \<in> U - attractor p K" using `V\<^bsub>G'\<^esub> = V'` V'_def by blast
      moreover hence "\<exists>w \<in> U. v\<rightarrow>w"
        using removing_winning_region_induces_no_deadends[of v "p**"] no_deadends U_equiv U_def
        by blast
      moreover have "\<And>w. \<lbrakk> v \<in> VV p**; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<in> U"
        using * U_equiv winning_region_extends_VVp by blast
      ultimately have "\<exists>w \<in> V'. v\<rightarrow>w"
        using U_equiv winning_region_extends_VVp removing_attractor_induces_no_deadends V'_def
        by blast
      thus "\<not>G'.deadend v" using `v \<in> V\<^bsub>G'\<^esub>` `V' \<subseteq> V` by simp
    qed

    text {*
      By definition of @{term W1}, we obtain a winning strategy on @{term W1} for player @{term "p**"}.
    *}
    obtain \<sigma>W1 where \<sigma>W1:
      "strategy p** \<sigma>W1" "\<And>v. v \<in> W1 \<Longrightarrow> winning_strategy p** \<sigma>W1 v"
      unfolding W1_def using merge_winning_strategies by blast

    {
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"

      text {* Apply the induction hypothesis to get the winning strategy for @{term v} in @{term G'}. *}
      have G'_winning_strategy: "\<exists>p \<sigma>. G'.strategy p \<sigma> \<and> G'.winning_strategy p \<sigma> v" proof-
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

      text {*
        It turns out the winning region of player @{term "p**"} is empty, so we have a strategy
        for player @{term p}.
      *}
      have "v \<in> G'.winning_region p" proof (rule ccontr)
        assume "\<not>?thesis"
        moreover obtain p' \<sigma> where p': "G'.strategy p' \<sigma>" "G'.winning_strategy p' \<sigma> v"
          using G'_winning_strategy by blast
        ultimately have "p' \<noteq> p" using `v \<in> V\<^bsub>G'\<^esub>` unfolding G'.winning_region_def by blast
        hence "p' = p**" by (cases p; cases p') auto
        with p' have \<sigma>: "G'.strategy p** \<sigma>" "G'.winning_strategy p** \<sigma> v" by simp_all

        have "v \<in> winning_region p**" proof (rule winning_regionI)
          show "v \<in> V" using `v \<in> V\<^bsub>G'\<^esub>` `V\<^bsub>G'\<^esub> \<subseteq> V` by blast
          def \<sigma>' \<equiv> "override_on (override_on \<sigma>_arbitrary \<sigma>W1 W1) \<sigma> V'"
          thus "strategy p** \<sigma>'"
            using valid_strategy_updates_set_strong valid_arbitrary_strategy \<sigma>W1(1)
                  valid_strategy_supergame \<sigma>(1) G'_no_deadends `V\<^bsub>G'\<^esub> = V'`
            unfolding G'_def by blast
          show "winning_strategy p** \<sigma>' v"
          proof (rule winning_strategyI, rule ccontr)
            fix P assume "vmc_path G P v p** \<sigma>'"
            then interpret vmc_path G P v "p**" \<sigma>' .
            assume "\<not>winning_path p** P"
            text {*
              First we show that @{term P} stays in @{term V'}, because if it stays in @{term V'},
              then it conforms to @{term \<sigma>}, so it must be winning for @{term "p**"}. *}

            have "lset P \<subseteq> V'" proof (rule vmc_path_lset_closed_subset)
              fix v assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p**"
              hence "v \<in> ParityGame.VV (subgame V') p**" by auto
              moreover have "\<not>G'.deadend v" using G'_no_deadends `V\<^bsub>G'\<^esub> = V'` `v \<in> V'` by blast
              ultimately have "\<sigma> v \<in> V'"
                using subgame_strategy_stays_in_subgame p'(1) `p' = p**`
                unfolding G'_def by blast
              thus "\<sigma>' v \<in> V' \<union> W1" unfolding \<sigma>'_def using `v \<in> V'` by simp
            next
              fix v w assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p****" "v\<rightarrow>w"
              show "w \<in> V' \<union> W1" proof (rule ccontr)
                assume "w \<notin> V' \<union> W1"
                hence "w \<in> attractor p K" using V_decomp `v\<rightarrow>w` by blast
                hence "v \<in> attractor p K" using `v \<in> VV p****` attractor_set_VVp `v\<rightarrow>w` by auto
                thus False using `v \<in> V'` V'_def by blast
              qed
            next
              show "lset P \<inter> W1 = {}" proof (rule ccontr)
                assume "lset P \<inter> W1 \<noteq> {}"
                then obtain n where n: "enat n < llength P" "P $ n \<in> W1"
                  by (meson lset_intersect_lnth)
                def P' \<equiv> "ldropn n P"
                then interpret P': vmc_path G P' "P $ n" "p**" \<sigma>'
                  unfolding P'_def using vmc_path_ldropn n(1) by blast
                have "winning_strategy p** \<sigma>W1 (P $ n)" using \<sigma>W1(2) n(2) by blast
                moreover have *: "\<And>v. v \<in> W1 \<Longrightarrow> \<sigma>W1 v = \<sigma>' v" unfolding \<sigma>'_def V'_def U_def by simp
                ultimately have "lset P' \<subseteq> W1"
                  using P'.paths_stay_in_winning_region[OF \<sigma>W1(1)]
                  unfolding W1_def
                  by blast
                hence "\<And>v. v \<in> lset P' \<Longrightarrow> \<sigma>' v = \<sigma>W1 v" using * by auto
                hence "path_conforms_with_strategy p** P' \<sigma>W1"
                  using path_conforms_with_strategy_irrelevant_updates P'.P_conforms
                  by blast
                then interpret P': vmc_path G P' "P $ n" "p**" \<sigma>W1
                  using P'.conforms_to_another_strategy by blast
                have "winning_path p** P'"
                  using \<sigma>W1(2) n(2) P'.vmc_path winning_strategy_def by blast
                thus False unfolding P'_def
                  using winning_path_drop_add n(1) P_valid `\<not>winning_path p** P`
                  by blast
              qed
            next
              show "v \<in> V'" using `V\<^bsub>G'\<^esub> = V'` `v \<in> V\<^bsub>G'\<^esub>` by blast
            qed
            text {* This concludes the proof of @{term "lset P \<subseteq> V'"}. *}
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
            moreover have "G'.VV p**** \<subseteq> VV p****" using subgame_VV_subset G'_def by blast
            ultimately show False
              using G'.winning_path_supergame[of "p**"] `\<omega>\<^bsub>G'\<^esub> = \<omega>` `\<not>winning_path p** P` ParityGame
              by blast
          qed
        qed
        moreover have "v \<in> V" using `V\<^bsub>G'\<^esub> \<subseteq> V` `v \<in> V\<^bsub>G'\<^esub>` by blast
        ultimately have "v \<in> W1" unfolding W1_def winning_region_def by blast
        thus False using `v \<in> V\<^bsub>G'\<^esub>` using U_def V'_def `V\<^bsub>G'\<^esub> = V'` `v \<in> V\<^bsub>G'\<^esub>` by blast
      qed
    } note recursion = this

    text {*
      We compose a winning strategy for player @{term p} on @{term "V - W1"} out of three pieces.
    *}

    text {*
      First, if we happen to land in the attractor region of @{term K}, we follow the attractor
      strategy.  This is good because the priority of the vertices in @{term K} is good for
      player @{term p}, so he likes to go there. *}
    obtain \<sigma>1
      where \<sigma>1: "strategy p \<sigma>1"
                "strategy_attracts p \<sigma>1 (attractor p K) K"
      using attractor_has_strategy[of K p] K_def U_def by auto

    text {* Next, on @{term G'} we follow the winning strategy whose existence we proved earlier. *}
    have "G'.winning_region p = V\<^bsub>G'\<^esub>" using recursion unfolding G'.winning_region_def by blast
    then obtain \<sigma>2
      where \<sigma>2: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> G'.strategy p \<sigma>2"
                "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> G'.winning_strategy p \<sigma>2 v"
      using G'.merge_winning_strategies by blast

    text {*
      As a last option we choose an arbitrary successor but avoid entering @{term W1}.
      In particular, this defines the strategy on the set @{term K}. *}
    def choose \<equiv> "\<lambda>v. SOME w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)"

    text {* Compose the three pieces. *}
    def \<sigma> \<equiv> "override_on (override_on choose \<sigma>2 V') \<sigma>1 (attractor p K - K)"

    have "attractor p K \<inter> W1 = {}" proof (rule ccontr)
      assume "attractor p K \<inter> W1 \<noteq> {}"
      then obtain v where v: "v \<in> attractor p K" "v \<in> W1" by blast
      hence "v \<in> V" using W1_def winning_region_def by blast
      obtain P where "vmc2_path G P v p \<sigma>1 \<sigma>W1"
        using strategy_conforming_path_exists \<sigma>W1(1) \<sigma>1(1) `v \<in> V` by blast
      then interpret vmc2_path G P v p \<sigma>1 \<sigma>W1 .
      have "strategy_attracts_via p \<sigma>1 v (attractor p K) K" using v(1) \<sigma>1(2) strategy_attracts_def by blast
      hence "lset P \<inter> K \<noteq> {}" using strategy_attracts_viaE visits_via_visits by blast
      hence "\<not>lset P \<subseteq> W1" unfolding K_def U_def by blast
      thus False unfolding W1_def using comp.paths_stay_in_winning_region \<sigma>W1 v(2) by auto
    qed

    text {* On specific sets, @{term \<sigma>} behaves like one of the three pieces. *}
    have \<sigma>_\<sigma>1 [simp]: "\<And>v. v \<in> attractor p K - K \<Longrightarrow> \<sigma> v = \<sigma>1 v" unfolding \<sigma>_def by simp
    have \<sigma>_\<sigma>2 [simp]: "\<And>v. v \<in> V' \<Longrightarrow> \<sigma> v = \<sigma>2 v" unfolding \<sigma>_def V'_def by auto
    have \<sigma>_K [simp]: "\<And>v. v \<in> K \<union> W1 \<Longrightarrow> \<sigma> v = choose v" proof-
      fix v assume "v \<in> K \<union> W1"
      moreover hence "v \<notin> V'" unfolding V'_def U_def using attractor_set_base by auto
      ultimately show "\<sigma> v = choose v" unfolding \<sigma>_def U_def using `attractor p K \<inter> W1 = {}`
        by (metis (mono_tags, lifting) Diff_iff IntI UnE override_on_def override_on_emptyset)
    qed

    text {* Show that @{term choose} succeeds in avoiding entering @{term W1}. *}
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
          hence "winning_strategy p** \<sigma>W1 v"
            using strategy_extends_backwards_VVpstar \<sigma>W1(1) `v \<in> VV p` by simp
          hence "v \<in> W1" unfolding W1_def winning_region_def using \<sigma>W1(1) `\<not>deadend v` by blast
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

    text {* Show that @{term \<sigma>} is a winning strategy on @{term "V - W1"}. *}
    have "\<forall>v \<in> V - W1. winning_strategy p \<sigma> v" proof-
      {
        fix v P assume P: "v \<in> V - W1" "vmc_path G P v p \<sigma>"
        interpret vmc_path G P v p \<sigma> using P(2) .

        have "lset P \<subseteq> V - W1" proof (rule vmc_path_lset_closed_subset)
          fix v assume "v \<in> V - W1" "\<not>deadend v" "v \<in> VV p"
          show "\<sigma> v \<in> V - W1 \<union> {}" proof (rule ccontr)
            assume "\<not>?thesis"
            hence "\<sigma> v \<in> W1"
              using `strategy p \<sigma>` `\<not>deadend v` `v \<in> VV p`
              unfolding strategy_def by blast
            hence "v \<notin> K" using choose_works(2)[OF `v \<in> VV p`] `v \<in> V - W1` by auto
            moreover have "v \<notin> attractor p K - K" proof
              assume "v \<in> attractor p K - K"
              hence "\<sigma> v \<in> attractor p K"
                using attracted_strategy_step `strategy p \<sigma>` \<sigma>_attracts `\<not>deadend v` `v \<in> VV p`
                      attractor_set_base
                by blast
              thus False using `\<sigma> v \<in> W1` `attractor p K \<inter> W1 = {}` by blast
            qed
            moreover have "v \<notin> V'" proof
              assume "v \<in> V'"
              have "\<sigma>2 v \<in> V\<^bsub>G'\<^esub>" proof (rule G'.valid_strategy_in_V[of p \<sigma>2 v])
                have "v \<in> V\<^bsub>G'\<^esub>" using `V\<^bsub>G'\<^esub> = V'` `v \<in> V'` by simp
                thus "\<not>G'.deadend v" using G'_no_deadends by blast
                show "G'.strategy p \<sigma>2" using \<sigma>2(1) `v \<in> V\<^bsub>G'\<^esub>` by blast
                show "v \<in> G'.VV p" using `v \<in> VV p` `G'.VV p = V' \<inter> VV p` `v \<in> V'` by simp
              qed
              hence "\<sigma> v \<in> V\<^bsub>G'\<^esub>" using `v \<in> V'` by simp
              thus False using `V\<^bsub>G'\<^esub> = V'` `\<sigma> v \<in> W1` V'_def U_def by blast
            qed
            ultimately show False using `v \<in> V - W1` V_decomp by blast
          qed
        next
          fix v w assume "v \<in> V - W1" "\<not>deadend v" "v \<in> VV p**" "v\<rightarrow>w"
          show "w \<in> V - W1 \<union> {}" proof (rule ccontr)
            assume "\<not>?thesis"
            hence "w \<in> W1" using `v\<rightarrow>w` by blast
            let ?\<sigma> = "\<sigma>W1(v := w)"
            have "winning_strategy p** \<sigma>W1 w" using `w \<in> W1` \<sigma>W1(2) by blast
            moreover have "\<not>(\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v)"
              using `v \<in> V - W1` unfolding W1_def winning_region_def by blast
            ultimately have "winning_strategy p** ?\<sigma> w"
              using winning_strategy_updates[of "p**" \<sigma>W1 w v w] \<sigma>W1(1) `v\<rightarrow>w`
              unfolding winning_region_def by blast
            moreover have "strategy p** ?\<sigma>" using `v\<rightarrow>w` \<sigma>W1(1) valid_strategy_updates by blast
            ultimately have "winning_strategy p** ?\<sigma> v"
              using strategy_extends_backwards_VVp[of v "p**" ?\<sigma> w]
                    `v \<in> VV p**` `v\<rightarrow>w`
              by auto
            hence "v \<in> W1" unfolding W1_def winning_region_def
              using `strategy p** ?\<sigma>` `v \<in> V - W1` by blast
            thus False using `v \<in> V - W1` by blast
          qed
        qed (insert P(1), simp_all)
        text {* This concludes the proof of @{term "lset P \<subseteq> V - W1"}. *}
        hence "lset P \<subseteq> attractor p K \<union> V'" using V_decomp by blast

        have "\<not>lfinite P"
          using no_deadends lfinite_lset maximal_ends_on_deadend[of P] P_maximal P_not_null lset_P_V
          by blast

        text {*
          Every @{term \<sigma>}-conforming path starting in @{term "V - W1"} is winning.
          We distinguish two cases:
          \begin{enumerate}
            \item @{term P} eventually stays in @{term V'}.
              Then @{term P} is winning because @{term \<sigma>2} is winning.
            \item @{term P} visits @{term K} infinitely often.
              Then @{term P} is winning because of the priority of the vertices in @{term K}.
          \end{enumerate}
        *}
        have "winning_path p P" proof (cases)
          assume "\<exists>n. lset (ldropn n P) \<subseteq> V'"
          text {* The first case: @{term P} eventually stays in @{term V'}. *}
          then obtain n where n: "lset (ldropn n P) \<subseteq> V'" by blast
          def P' \<equiv> "ldropn n P"
          hence "lset P' \<subseteq> V'" using n by blast
          interpret vmc_path G' P' "lhd P'" p \<sigma>2 proof
            show "\<not>lnull P'" unfolding P'_def
              using `\<not>lfinite P` lfinite_ldropn lnull_imp_lfinite by blast
            show "G'.valid_path P'" proof-
              have "valid_path P'" unfolding P'_def by simp
              thus ?thesis using subgame_valid_path `lset P' \<subseteq> V'` G'_def by blast
            qed
            show "G'.maximal_path P'" proof-
              have "maximal_path P'" unfolding P'_def by simp
              thus ?thesis using subgame_maximal_path `lset P' \<subseteq> V'` `V' \<subseteq> V` G'_def by blast
            qed
            show "G'.path_conforms_with_strategy p P' \<sigma>2" proof-
              have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def by simp
              hence "path_conforms_with_strategy p P' \<sigma>2"
                using path_conforms_with_strategy_irrelevant_updates `lset P' \<subseteq> V'` \<sigma>_\<sigma>2
                by blast
              thus ?thesis
                using subgame_path_conforms_with_strategy `lset P' \<subseteq> V'` `V' \<subseteq> V` G'_def
                by blast
            qed
          qed simp
          have "G'.winning_strategy p \<sigma>2 (lhd P')"
            using `lset P' \<subseteq> V'` `\<not>lnull P'` \<sigma>2(2)[of "lhd P'"] `V\<^bsub>G'\<^esub> = V'` llist.set_sel(1)
            by blast
          hence "G'.winning_path p P'" using G'.winning_strategy_def vmc_path by blast
          moreover have "G'.VV p** \<subseteq> VV p**" unfolding G'_def using subgame_VV by simp
          ultimately have "winning_path p P'"
            using G'.winning_path_supergame[of p P' G] `\<omega>\<^bsub>G'\<^esub> = \<omega>` ParityGame by blast
          thus ?thesis
            unfolding P'_def
            using infinite_small_llength[OF `\<not>lfinite P`]
                  winning_path_drop_add[of P p n] `valid_path P`
            by blast
        next
          assume "\<not>(\<exists>n. lset (ldropn n P) \<subseteq> V')"
          text {* The second case: @{term P} visits @{term K} infinitely often. *}
          hence *: "\<And>n. \<not>lset (ldropn n P) \<subseteq> V'" by blast
          have *: "\<And>n. \<exists>k \<ge> n. P $ k \<notin> V'" proof-
            fix n
            obtain k where k: "ldropn n P $ k \<notin> V'" using * by (metis lset_lnth subsetI)
            hence "P $ k + n \<notin> V'"
              using lnth_ldropn[of n k P] infinite_small_llength `\<not>lfinite P` by metis
            thus "\<exists>k \<ge> n. P $ k \<notin> V'" using le_add2 by blast
          qed
          have "\<And>n. \<exists>k \<ge> n. P $ k \<in> attractor p K" proof-
            fix n obtain k where "k \<ge> n" "P $ k \<notin> V'" using * by blast
            thus "\<exists>k \<ge> n. P $ k \<in> attractor p K" using `\<not>lfinite P` `lset P \<subseteq> V - W1`
              by (metis DiffI U_def V'_def lset_nth_member_inf)
          qed
          moreover have "\<And>k. P $ k \<in> attractor p K \<Longrightarrow> \<exists>n \<ge> k. P $ n \<in> K" proof-
            fix k
            interpret vmc_path G "ldropn k P" "P $ k" p \<sigma>
              using vmc_path_ldropn infinite_small_llength `\<not>lfinite P` by blast
            assume "P $ k \<in> attractor p K"
            then obtain n where "ldropn k P $ n \<in> K"
              using \<sigma>_attracts strategy_attractsE
              unfolding G'.visits_via_def
              by blast
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
            moreover have "enat (k - n) < llength (ldropn n P)"
              using `\<not>lfinite P` lfinite_ldropn by blast
            ultimately show "lset (ldropn n P) \<inter> K \<noteq> {}"
              using in_lset_conv_lnth[of "ldropn n P $ k - n"] by blast
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
    hence "\<forall>v \<in> V. \<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
      unfolding W1_def winning_region_def using `strategy p \<sigma>` by blast
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" using `v \<in> V` by simp
  }
  moreover have "\<exists>p. winning_priority p (Min (\<omega> ` V))" by auto
  ultimately show ?thesis by blast
qed


subsection {* Positional determinacy without deadends *}

theorem positional_strategy_exists_without_deadends:
  assumes "v \<in> V" "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  using assms ParityGame
  by (induct "card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>)" arbitrary: G v rule: nat_less_induct)
     (rule ParityGame.positional_strategy_induction_step, simp_all)


subsection {* Positional determinacy *}

text {*
  Prove a stronger version of the previous theorem: Allow deadends.
  This is the main theorem.
*}
theorem positional_strategy_exists:
  assumes "v0 \<in> V"
  shows "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0"
proof-
  { fix p
    def A \<equiv> "attractor p (deadends p**)"
    assume v0_in_attractor: "v0 \<in> attractor p (deadends p**)"
    then obtain \<sigma> where \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> A (deadends p**)"
      using attractor_has_strategy[of "deadends p**" "p"] A_def deadends_in_V by blast

    have "A \<subseteq> V" using A_def using attractor_is_bounded_by_V deadends_in_V by blast
    hence "A - deadends p** \<subseteq> V" by auto

    have "winning_strategy p \<sigma> v0" proof (unfold winning_strategy_def, intro allI impI)
      fix P assume "vmc_path G P v0 p \<sigma>"
      then interpret vmc_path G P v0 p \<sigma> .
      show "winning_path p P"
        using visits_deadend[of "p**"] \<sigma>(2) strategy_attracts_lset v0_in_attractor
        unfolding A_def by simp
    qed
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0" using \<sigma> by blast
  } note lemma_path_to_deadend = this
  def A \<equiv> "\<lambda>p. attractor p (deadends p**)"
  text {* Remove the attractor sets of the sets of deadends. *}
  def V' \<equiv> "V - A Even - A Odd"
  hence "V' \<subseteq> V" by blast
  show ?thesis proof (cases)
    assume "v0 \<in> V'"
    def G' \<equiv> "subgame V'"
    interpret G': ParityGame G' unfolding G'_def using subgame_ParityGame .
    have "V\<^bsub>G'\<^esub> = V'" unfolding G'_def using `V' \<subseteq> V` by simp
    hence "v0 \<in> V\<^bsub>G'\<^esub>" using `v0 \<in> V'` by simp
    moreover have V'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>G'.deadend v" proof-
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"
      moreover have "V' = V - A Even - A Even**" using V'_def by simp
      ultimately show "\<not>G'.deadend v"
        using subgame_without_deadends `v \<in> V\<^bsub>G'\<^esub>` unfolding A_def G'_def by blast
    qed
    ultimately obtain p \<sigma> where \<sigma>: "G'.strategy p \<sigma>" "G'.winning_strategy p \<sigma> v0"
      using G'.positional_strategy_exists_without_deadends by blast

    have V'_no_deadends': "\<And>v. v \<in> V' \<Longrightarrow> \<not>deadend v" proof-
      fix v assume "v \<in> V'"
      hence "\<not>G'.deadend v" using V'_no_deadends `V' \<subseteq> V` unfolding G'_def by auto
      thus "\<not>deadend v" unfolding G'_def using `V' \<subseteq> V` by auto
    qed

    obtain \<sigma>_attr
      where \<sigma>_attr: "strategy p \<sigma>_attr" "strategy_attracts p \<sigma>_attr (A p) (deadends p**)"
      using attractor_has_strategy[OF deadends_in_V] A_def by blast
    def \<sigma>' \<equiv> "override_on \<sigma> \<sigma>_attr (A Even \<union> A Odd)"
    have \<sigma>'_is_\<sigma>_on_V': "\<And>v. v \<in> V' \<Longrightarrow> \<sigma>' v = \<sigma> v"
      unfolding V'_def \<sigma>'_def A_def by (cases p) simp_all

    have "strategy p \<sigma>'" proof-
      have "\<sigma>' = override_on \<sigma>_attr \<sigma> (UNIV - A Even - A Odd)"
        unfolding \<sigma>'_def override_on_def by (rule ext) simp
      moreover have "strategy p (override_on \<sigma>_attr \<sigma> V')"
        using valid_strategy_supergame \<sigma>_attr(1) \<sigma>(1) V'_no_deadends `V\<^bsub>G'\<^esub> = V'`
        unfolding G'_def by blast
      ultimately show ?thesis by (simp add: valid_strategy_only_in_V V'_def override_on_def)
    qed
    moreover have "winning_strategy p \<sigma>' v0" proof (rule winning_strategyI, rule ccontr)
      fix P assume "vmc_path G P v0 p \<sigma>'"
      then interpret vmc_path G P v0 p \<sigma>' .
      interpret vmc_path_no_deadend G P v0 p \<sigma>'
        using V'_no_deadends' `v0 \<in> V'` by unfold_locales
      assume contra: "\<not>winning_path p P"

      have "lset P \<subseteq> V'" proof (rule vmc_path_lset_closed_subset)
        fix v assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p"
        hence "v \<in> G'.VV p" unfolding G'_def by (simp add: `v \<in> V'`)
        moreover have "\<not>G'.deadend v" using V'_no_deadends `v \<in> V'` `V\<^bsub>G'\<^esub> = V'` by blast
        moreover have "G'.strategy p \<sigma>'"
          using G'.valid_strategy_only_in_V \<sigma>'_def \<sigma>'_is_\<sigma>_on_V' \<sigma>(1) `V\<^bsub>G'\<^esub> = V'` by auto
        ultimately show "\<sigma>' v \<in> V' \<union> A p" using subgame_strategy_stays_in_subgame
          unfolding G'_def by blast
      next
        fix v w assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p**" "v\<rightarrow>w"
        have "w \<notin> A p**" proof
          assume "w \<in> A p**"
          hence "v \<in> A p**" unfolding A_def
            using `v \<in> VV p**` `v\<rightarrow>w` attractor_set_VVp by blast
          thus False using `v \<in> V'` unfolding V'_def by (cases p) auto
        qed
        thus "w \<in> V' \<union> A p" unfolding V'_def using `v\<rightarrow>w` by (cases p) auto
      next
        show "lset P \<inter> A p = {}" proof (rule ccontr)
          assume "lset P \<inter> A p \<noteq> {}"
          have "strategy_attracts p (override_on \<sigma>' \<sigma>_attr (A p - deadends p**))
                                    (A p)
                                    (deadends p**)"
            using strategy_attracts_irrelevant_override[OF \<sigma>_attr(2) \<sigma>_attr(1) `strategy p \<sigma>'`]
            by blast
          moreover have "override_on \<sigma>' \<sigma>_attr (A p - deadends p**) = \<sigma>'"
            by (rule ext, unfold \<sigma>'_def, cases p) (simp_all add: override_on_def)
          ultimately have "strategy_attracts p \<sigma>' (A p) (deadends p**)" by simp
          hence "lset P \<inter> deadends p** \<noteq> {}"
            using `lset P \<inter> A p \<noteq> {}` attracted_path[OF deadends_in_V] by simp
          thus False using contra visits_deadend[of "p**"] by simp
        qed
      qed (insert `v0 \<in> V'`)

      then interpret vmc_path G' P v0 p \<sigma>'
        unfolding G'_def using subgame_path_vmc_path[OF `V' \<subseteq> V`] by blast
      have "G'.path_conforms_with_strategy p P \<sigma>" proof-
        have "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma>' v = \<sigma> v"
          using \<sigma>'_is_\<sigma>_on_V' `V\<^bsub>G'\<^esub> = V'` lset_P_V by blast
        thus "G'.path_conforms_with_strategy p P \<sigma>"
          using P_conforms G'.path_conforms_with_strategy_irrelevant_updates by blast
      qed
      then interpret vmc_path G' P v0 p \<sigma> using conforms_to_another_strategy by blast
      have "G'.winning_path p P"
        using \<sigma>(2)[unfolded G'.winning_strategy_def] vmc_path by blast
      from `\<not>winning_path p P`
           G'.winning_path_supergame[OF this ParityGame, unfolded G'_def]
           subgame_VV_subset[of "p**" V']
           subgame_\<omega>[of V']
        show False by blast
    qed
    ultimately show ?thesis by blast
  next
    assume "v0 \<notin> V'"
    then obtain p where "v0 \<in> attractor p (deadends p**)"
      unfolding V'_def A_def using `v0 \<in> V` by blast
    thus ?thesis using lemma_path_to_deadend by blast
  qed
qed

end -- "context ParityGame"

end
