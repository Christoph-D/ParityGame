(* Theorems about how to get a uniform strategy given strategies for each node. *)
theory merge_strategies
imports
  Main
  attractor Winning_Strategy Well_Ordered_Strategy
begin

context ParityGame begin

lemma merge_attractor_strategies:
  assumes "S \<subseteq> V"
    and strategies_ex: "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
proof-
  def good \<equiv> "\<lambda>v. { \<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W }"
  let ?G = "{\<sigma>. \<exists>v \<in> S - W. \<sigma> \<in> good v}"
  obtain r where r: "well_order_on ?G r" using well_order_on by blast

  interpret WellOrderedStrategies G "S - W" p good r proof
    show "S - W \<subseteq> V" using `S \<subseteq> V` by blast
  next
    show "\<And>v. v \<in> S - W \<Longrightarrow> \<exists>\<sigma>. \<sigma> \<in> good v" unfolding good_def using strategies_ex by blast
  next
    show "\<And>v \<sigma>. \<sigma> \<in> good v \<Longrightarrow> strategy p \<sigma>" unfolding good_def by blast
  next
    fix v w \<sigma> assume v: "v \<in> S - W" "v\<rightarrow>w" "v \<in> VV p \<Longrightarrow> \<sigma> v = w" "\<sigma> \<in> good v"
    hence \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v S W" unfolding good_def by simp_all
    hence "strategy_attracts_via p \<sigma> w S W" using strategy_attracts_via_successor v by blast
    thus "\<sigma> \<in> good w" unfolding good_def using \<sigma>(1) by blast
  qed (insert r)

  have S_W_no_deadends: "\<And>v. v \<in> S - W \<Longrightarrow> \<not>deadend v"
    using strategy_attracts_via_no_deadends[of _ S W] strategies_ex
    by (metis (no_types) Diff_iff S_V rev_subsetD)

  {
    fix v0 assume "v0 \<in> S"
    fix P assume "vmc_path G P v0 p well_ordered_strategy"
    then interpret vmc_path G P v0 p well_ordered_strategy .
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> S" proof (rule ccontr)
      assume "\<not>?thesis"
      hence contra: "\<And>n. enat n < llength P \<Longrightarrow> P $ n \<in> W \<Longrightarrow> \<not>lset (ltake (enat n) P) \<subseteq> S" by blast
      have "lset P \<subseteq> S - W" proof (rule ccontr)
        assume "\<not>lset P \<subseteq> S - W"
        hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> S - W" by (meson lset_subset)
        then obtain n where n:
          "enat n < llength P" "P $ n \<notin> S - W"
          "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> S - W)"
          using ex_least_nat_le[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> S - W"] by blast
        from n(1) n(3) have "\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W" using dual_order.strict_trans enat_ord_simps(2) by blast
        hence "lset (ltake (enat n) P) \<subseteq> S - W" using lset_ltake by blast
        hence "P $ n \<notin> W" using contra n(1) by blast
        moreover have "P $ n \<notin> V - S - W" proof
          assume "P $ n \<in> V - S - W"
          hence "n \<noteq> 0" using `v0 \<in> S` n(2) by force
          then obtain n' where n': "Suc n' = n" using not0_implies_Suc by blast
          hence "P $ n' \<in> S - W" using `\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W` by blast
          def [simp]: P' \<equiv> "ldropn n' P"
          def [simp]: \<sigma>' \<equiv> "choose (P $ n')"
          hence \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' (P $ n') S W"
            using `P $ n' \<in> S - W` choose_good good_def \<sigma>'_def by blast+
          have "enat n' < llength P" using n(1) n' using dual_order.strict_trans enat_ord_simps(2) by blast
          show False proof (cases)
            assume "P $ n' \<in> VV p"
            hence "well_ordered_strategy (P $ n') \<in> S \<union> W"
              using \<sigma>'(1) \<sigma>'(2) `P $ n' \<in> S - W` assms(1) assms(2)
                strategy_attracts_VVp S_W_no_deadends well_ordered_strategy_def by auto
            moreover have "well_ordered_strategy (P $ n') = P $ n" proof-
              have "enat (Suc n') < llength P" using n' n(1) by simp
              hence "well_ordered_strategy (P $ n') = P $ Suc n'"
                using P_conforms P_valid `P $ n' \<in> VV p` path_conforms_with_strategy_conforms by blast
              thus ?thesis using n' by simp
            qed
            ultimately show False using `P $ n \<in> V - S - W` by auto
          next
            assume "P $ n' \<notin> VV p"
            hence "\<not>(P $ n')\<rightarrow>(P $ n)" using strategy_attracts_VVpstar
              \<sigma>'(1) \<sigma>'(2) `P $ n \<in> V - S - W` `P $ n' \<in> S - W` assms(1) assms(2) by blast
            hence "\<not>(P $ n')\<rightarrow>(P $ Suc n')" using n' by simp
            moreover have "enat (Suc n') < llength P" using n' n(1) by simp
            ultimately show False using P_valid `enat n' < llength P` valid_path_impl1 by blast
          qed
        qed
        moreover have "P $ n \<in> V" using n(1) P_valid valid_path_finite_in_V' by blast
        ultimately show False using n(2) by blast
      qed
      have "\<not>lfinite P" proof
        assume "lfinite P"
        hence "deadend (llast P)" using P_maximal `\<not>lnull P` maximal_ends_on_deadend by blast
        moreover have "llast P \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lnull P` `lfinite P` lfinite_lset by blast
        ultimately show False using S_W_no_deadends by blast
      qed

      obtain n where n: "path_conforms_with_strategy p (ldropn n P) (path_strategies P $ n)"
        using path_eventually_conforms_to_\<sigma>_map_n[OF `\<not>lfinite P` `lset P \<subseteq> S - W` P_valid P_conforms]
          by blast
      def [simp]: \<sigma>' \<equiv> "path_strategies P $ n"
      def [simp]: P' \<equiv> "ldropn n P"
      interpret vmc_path G P' "lhd P'" p \<sigma>' proof
        show "\<not>lnull P'" unfolding P'_def using `\<not>lfinite P` infinite_no_deadend lfinite_ldropn by blast
      qed (simp_all add: n)
      have "strategy p \<sigma>'" unfolding \<sigma>'_def
        using path_strategies_strategy `lset P \<subseteq> S - W` `\<not>lfinite P` infinite_small_llength
        by blast
      moreover have "strategy_attracts_via p \<sigma>' (lhd P') S W" proof-
        have "P $ n \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lfinite P` llist_set_nth by blast
        hence "\<sigma>' \<in> good (P $ n)"
          using path_strategies_good \<sigma>'_def `\<not>lfinite P` `lset P \<subseteq> S - W` by blast
        hence "strategy_attracts_via p \<sigma>' (P $ n) S W" unfolding good_def by blast
        thus ?thesis unfolding P'_def using P_0 by (simp add: `\<not>lfinite P` infinite_small_llength)
      qed
      ultimately obtain m where m: "enat m < llength P'" "P' $ m \<in> W"
        using strategy_attracts_viaE by blast
      moreover from `lset P \<subseteq> S - W` have "lset P' \<subseteq> S - W" using lset_ldropn_subset by fastforce
      ultimately show False by (meson Diff_iff lset_lnth)
    qed
  }
  thus ?thesis using strategy_attractsI[of S] well_ordered_strategy_valid by auto
qed

lemma merge_winning_strategies:
  assumes "S \<subseteq> V" and strategies_ex: "\<And>v. v \<in> V \<Longrightarrow> v \<in> S \<longleftrightarrow> (\<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v)"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> (\<forall>v \<in> S. winning_strategy p \<sigma> v)"
proof-
  def good \<equiv> "\<lambda>v. { \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }"
  let ?G = "{\<sigma>. \<exists>v \<in> S. \<sigma> \<in> good v}"
  obtain r where r: "well_order_on ?G r" using well_order_on by blast

  have no_VVp_deadends: "\<And>v. \<lbrakk> v \<in> S; v \<in> VV p \<rbrakk> \<Longrightarrow> \<not>deadend v"
    using no_winning_strategy_on_deadends strategies_ex by blast

  interpret WellOrderedStrategies G S p good r proof
    show "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. \<sigma> \<in> good v" unfolding good_def using strategies_ex `S \<subseteq> V` by blast
  next
    show "\<And>v \<sigma>. \<sigma> \<in> good v \<Longrightarrow> strategy p \<sigma>" unfolding good_def by blast
  next
    fix v w \<sigma> assume v: "v \<in> S" "v\<rightarrow>w" "v \<in> VV p \<Longrightarrow> \<sigma> v = w" "\<sigma> \<in> good v"
    hence \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v" unfolding good_def by simp_all
    hence "winning_strategy p \<sigma> w" proof (cases)
      assume "v \<in> VV p"
      moreover hence "\<sigma> v = w" using v(3) by blast
      moreover have "\<not>deadend v" using no_VVp_deadends `v \<in> VV p` `v \<in> S` by blast
      ultimately show ?thesis using strategy_extends_VVp \<sigma> by blast
    next
      assume "v \<notin> VV p"
      thus ?thesis using strategy_extends_VVpstar \<sigma> `v\<rightarrow>w` by blast
    qed
    thus "\<sigma> \<in> good w" unfolding good_def using \<sigma>(1) by blast
  qed (insert `S \<subseteq> V` r)

  have S_closed: "\<And>v w \<sigma>. \<lbrakk> v \<in> S; v\<rightarrow>w; v \<in> VV p \<Longrightarrow> \<sigma> v = w; \<sigma> \<in> good v \<rbrakk> \<Longrightarrow> w \<in> S" proof-
    fix v w \<sigma> assume "v \<in> S" "v\<rightarrow>w" "v \<in> VV p \<Longrightarrow> \<sigma> v = w" "\<sigma> \<in> good v"
    hence "\<sigma> \<in> good w" using strategies_continue by blast
    thus "w \<in> S" using strategies_continue good_def strategies_ex `v\<rightarrow>w` by blast
  qed

  {
    fix v0 assume "v0 \<in> S"
    fix P assume P: "vmc_path G P v0 p well_ordered_strategy"
    then interpret vmc_path G P v0 p well_ordered_strategy .
    have "winning_path p P" proof (rule ccontr)
      assume contra: "\<not>winning_path p P"
      hence "winning_path p** P" using paths_are_winning_for_exactly_one_player P_valid by blast
      have "lset P \<subseteq> S" proof
        fix v assume "v \<in> lset P"
        thus "v \<in> S" using `v0 \<in> S` P `winning_path p** P` proof (induct arbitrary: v0 rule: llist_set_induct)
          case (find P)
          then interpret vmc_path G P v0 p well_ordered_strategy by blast
          show ?case by (simp add: find.prems(1))
        next
          case (step P v)
          then interpret vmc_path G P v0 p well_ordered_strategy by blast
          show ?case proof (cases)
            assume "lnull (ltl P)"
            hence "P = LCons v LNil" by (metis llist.disc(2) lset_cases step.hyps(2))
            thus ?thesis using step.prems(1) P_LCons by blast
          next
            assume "\<not>lnull (ltl P)"
            then interpret vmc_path_no_deadend G P v0 p well_ordered_strategy
              using vmc_path_lnull_ltl_no_deadend by blast
            { assume "v0 \<in> VV p"
              hence "well_ordered_strategy v0 = w0" using v0_conforms by blast
              hence "choose v0 v0 = w0" by (simp add: v0_conforms step.prems(1) well_ordered_strategy_def)
            }
            hence "w0 \<in> S" using S_closed `v0\<rightarrow>w0` choose_good step.prems(1) by blast
            moreover have "vmc_path G (ltl P) w0 p well_ordered_strategy" using vmc_path_ltl by blast
            moreover have "winning_path p** (ltl P)"
              using `\<not>lnull P` `\<not>lnull (ltl P)` winning_path_ltl step.prems(3) by blast
            ultimately show "v \<in> S" using step.hyps(3) `\<not>lnull (ltl P)` by blast
          qed
        qed
      qed
      have "\<not>lfinite P" proof
        assume "lfinite P"
        hence "deadend (llast P)" using P_maximal `\<not>lnull P` maximal_ends_on_deadend by blast
        moreover have "llast P \<in> S" using `lset P \<subseteq> S` `\<not>lnull P` `lfinite P` lfinite_lset by blast
        moreover have "llast P \<in> VV p" using `winning_path p** P` `lfinite P` `\<not>lnull P`
          unfolding winning_path_def by simp
        ultimately show False using no_VVp_deadends by blast
      qed

      obtain n where n: "path_conforms_with_strategy p (ldropn n P) (path_strategies P $ n)"
        using path_eventually_conforms_to_\<sigma>_map_n[OF `\<not>lfinite P` `lset P \<subseteq> S` P_valid P_conforms]
          by blast
      def [simp]: \<sigma>' \<equiv> "path_strategies P $ n"
      def [simp]: P' \<equiv> "ldropn n P"
      interpret P': vmc_path G P' "lhd P'" p \<sigma>' proof
        show "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
      qed (simp_all add: n)
      have "strategy p \<sigma>'" unfolding \<sigma>'_def
        using path_strategies_strategy `lset P \<subseteq> S` `\<not>lfinite P` by blast
      moreover have "winning_strategy p \<sigma>' (lhd P')" proof-
        have "P $ n \<in> S" using `lset P \<subseteq> S` `\<not>lfinite P` llist_set_nth by blast
        hence "\<sigma>' \<in> good (P $ n)"
          using path_strategies_good choose_good \<sigma>'_def `\<not>lfinite P` `lset P \<subseteq> S` by blast
        hence "winning_strategy p \<sigma>' (P $ n)" unfolding good_def by blast
        thus ?thesis
          unfolding P'_def using P_0 `\<not>lfinite P` by (simp add: infinite_small_llength lhd_ldropn)
      qed
      ultimately have "winning_path p P'" unfolding winning_strategy_def using P'.vmc_path by blast
      moreover have "\<not>lfinite P'" using `\<not>lfinite P` P'_def by simp
      ultimately show False
        using contra winning_path_drop_add[OF P_valid] by auto
    qed
  }
  thus ?thesis unfolding winning_strategy_def using well_ordered_strategy_valid by auto
qed

end -- "context ParityGame"

end
