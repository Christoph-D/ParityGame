(* Theorems about how to get a uniform strategy given strategies for each node. *)
theory merge_strategies
imports
  Main
  parity_game strategy attractor
begin

context ParityGame begin

lemma merge_attractor_strategies:
  assumes "S \<subseteq> V" and strategies_ex: "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
proof-
  let ?good = "\<lambda>v. { \<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W }"
  def G \<equiv> "{ \<sigma>. \<exists>v \<in> S. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W }"
  obtain r where r: "well_order_on G r" using well_order_on by blast
  hence wf: "wf (r - Id)" using well_order_on_def by blast

  def [simp]: choose' \<equiv> "\<lambda>v \<sigma>. \<sigma> \<in> ?good v \<and> (\<forall>\<sigma>'. (\<sigma>', \<sigma>) \<in> r - Id \<longrightarrow> \<sigma>' \<notin> ?good v)"
  def [simp]: choose \<equiv> "\<lambda>v. THE \<sigma>. choose' v \<sigma>"
  def \<sigma> \<equiv> "override_on \<sigma>_arbitrary (\<lambda>v. choose v v) (S - W)"

  { fix v assume "v \<in> S"
    hence "\<exists>\<sigma>. \<sigma> \<in> ?good v" using strategies_ex by blast
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

  have \<sigma>_valid: "strategy p \<sigma>" proof-
    {
      fix v assume *: "v \<in> S" "v \<in> VV p" "\<not>deadend v"
      from `v \<in> S` have "strategy p (choose v)" using choose_works choose'_def by blast
      with * have "v\<rightarrow>(\<lambda>v. choose v v) v" using strategy_def by blast
    }
    thus ?thesis using valid_strategy_updates_set \<sigma>_def by force
  qed

  have S_W_no_deadends: "\<And>v. v \<in> S - W \<Longrightarrow> \<not>deadend v" proof (rule ccontr, subst (asm) not_not)
    fix v assume "v \<in> S - W" "deadend v"
    def [simp]: P \<equiv> "LCons v LNil"
    obtain \<sigma>' where \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' v S W" using `v \<in> S - W` strategies_ex by auto
    moreover have "\<not>lnull P \<and> P $ 0 = v" by simp
    moreover have "valid_path P" using `v \<in> S - W` `S \<subseteq> V` valid_path_base' by auto
    moreover have "maximal_path P" using `deadend v` by (simp add: maximal_path.intros(2))
    moreover have "path_conforms_with_strategy p P \<sigma>'" by (simp add: path_conforms_LCons_LNil)
    ultimately have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> S"
      using \<sigma>'(2) unfolding strategy_attracts_via_def by blast
    moreover have "llength P = eSuc 0" by simp
    ultimately have "P $ 0 \<in> W" by (simp add: enat_0_iff(1))
    with `v \<in> S - W` show False by auto
  qed

  {
    fix v0 assume "v0 \<in> S"
    fix P assume "\<not>lnull P"
      and P_valid: "valid_path P"
      and P_maximal: "maximal_path P"
      and P_conforms: "path_conforms_with_strategy p P \<sigma>"
      and P_valid_start: "P $ 0 = v0"
    have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> S" proof (rule ccontr)
      assume "\<not>?thesis"
      hence contra: "\<And>n. enat n < llength P \<Longrightarrow> P $ n \<in> W \<Longrightarrow> \<not>lset (ltake (enat n) P) \<subseteq> S" by blast
      have "lset P \<subseteq> S - W" proof (rule ccontr)
        assume "\<not>lset P \<subseteq> S - W"
        hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> S - W" by (meson lset_subset)
        then obtain n where n: "enat n < llength P" "P $ n \<notin> S - W" "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> S - W)"
          using obtain_min[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> S - W"] by metis
        from n(1) n(3) have "\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W" using dual_order.strict_trans enat_ord_simps(2) by blast
        hence "lset (ltake (enat n) P) \<subseteq> S - W" using lset_ltake by blast
        hence "P $ n \<notin> W" using contra n(1) by blast
        moreover have "P $ n \<notin> V - S - W" proof (rule ccontr, subst (asm) not_not)
          assume "P $ n \<in> V - S - W"
          hence "n \<noteq> 0" using P_valid_start `v0 \<in> S` n(2) by force
          then obtain n' where n': "Suc n' = n" by (metis nat.exhaust)
          hence "P $ n' \<in> S - W" using `\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W` by blast
          def [simp]: P' \<equiv> "ldropn n' P"
          def [simp]: \<sigma>' \<equiv> "choose (P $ n')"
          hence \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' (P $ n') S W"
            using `P $ n' \<in> S - W` choose_works unfolding choose'_def by blast+
          have "enat n' < llength P" using n(1) n' using dual_order.strict_trans enat_ord_simps(2) by blast
          show False proof (cases)
            assume "P $ n' \<in> VV p"
            hence "\<sigma> (P $ n') \<in> S \<union> W" using \<sigma>'(1) \<sigma>'(2) \<sigma>_def `P $ n' \<in> S - W` assms(1) assms(2) strategy_attracts_VVp S_W_no_deadends by auto
            moreover have "\<sigma> (P $ n') = P $ n" proof-
              have "enat (Suc n') < llength P" using n' n(1) by simp
              hence "\<sigma> (P $ n') = P $ Suc n'" using P_conforms P_valid `P $ n' \<in> VV p` path_conforms_with_strategy_conforms by blast
              thus ?thesis using n' by simp
            qed
            ultimately show False using `P $ n \<in> V - S - W` by auto
          next
            assume "P $ n' \<notin> VV p"
            hence "\<not>(P $ n')\<rightarrow>(P $ n)" using strategy_attracts_VVpstar \<sigma>'(1) \<sigma>'(2) `P $ n \<in> V - S - W` `P $ n' \<in> S - W` assms(1) assms(2) by blast
            hence "\<not>(P $ n')\<rightarrow>(P $ Suc n')" using n' by simp
            moreover have "enat (Suc n') < llength P" using n' n(1) by simp
            ultimately show False using P_valid `enat n' < llength P` valid_path_impl1 by blast
          qed
        qed
        moreover have "P $ n \<in> V" using n(1) P_valid valid_path_finite_in_V' by blast
        ultimately show False using n(2) by blast
      qed
      have "\<not>lfinite P" proof (rule ccontr, subst (asm) not_not)
        assume "lfinite P"
        hence "deadend (llast P)" using P_maximal `\<not>lnull P` maximal_ends_on_deadend by blast
        moreover have "llast P \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lnull P` `lfinite P` lfinite_lset by blast
        ultimately show False using S_W_no_deadends by blast
      qed
      have P_no_deadends: "\<And>n. \<not>deadend (P $ n)"
        using `\<not>lfinite P` S_W_no_deadends `lset P \<subseteq> S - W` llist_nth_set by fastforce
      show False proof (cases "\<exists>n. lset (ldropn n P) \<subseteq> VV p**")
        case True
        then obtain n where n: "lset (ldropn n P) \<subseteq> VV p**" by blast
        def [simp]: P' \<equiv> "ldropn n P"
        have "lset P' \<subseteq> S - W" using `lset P \<subseteq> S - W` P'_def lset_ldropn_subset by force
        moreover have "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
        ultimately have "P' $ 0 \<in> S" by (metis Diff_subset P'_def `\<not>lfinite P` lfinite_ldropn llist_set_nth subset_trans)
        then obtain \<sigma>' where \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' (P' $ 0) S W" using strategies_ex by blast
        moreover have "valid_path P'" using P_valid by (simp add: valid_path_drop)
        moreover have "maximal_path P'" using P_maximal by (simp add: maximal_drop)
        moreover have "path_conforms_with_strategy p P' \<sigma>'" using n path_conforms_with_strategy_VVpstar by simp
        ultimately obtain m where m: "enat m < llength P'" "P' $ m \<in> W" "lset (ltake (enat m) P') \<subseteq> S"
          unfolding strategy_attracts_via_def using `\<not>lnull P'` by blast
        thus False by (meson Diff_iff `lset P' \<subseteq> S - W` lset_lnth)
      next
        case False
        have always_again_in_VVp: "\<And>n. \<exists>m. n \<le> m \<and> P $ m \<in> VV p" proof-
          fix n
          have "\<not>lset (ldropn n P) \<subseteq> VV p**" using False by blast
          then obtain m where m: "ldropn n P $ m \<notin> VV p**" using lset_subset[of "ldropn n P" "VV p**"] by blast
          hence "ldropn n P $ m \<in> VV p" using P_valid VV_cases `\<not>lfinite P` lfinite_ldropn valid_path_drop valid_path_in_V' by blast
          hence "P $ m + n \<in> VV p" using lnth_ldropn `\<not>lfinite P` by (simp add: infinite_small_llength)
          thus "\<exists>m. n \<le> m \<and> P $ m \<in> VV p" using le_add2 by blast
        qed
        def [simp]: \<sigma>_map \<equiv> "\<lambda>n. choose (P $ n)"
        have "\<And>n. P $ n \<in> S" using `lset P \<subseteq> S - W` `\<not>lfinite P` llist_set_nth by blast
        {
          fix n
          let ?v = "P $ n"
          have "choose' ?v (\<sigma>_map n)" using choose_works[of ?v] `\<And>n. P $ n \<in> S` unfolding \<sigma>_map_def by blast
          hence "strategy p (\<sigma>_map n) \<and> strategy_attracts_via p (\<sigma>_map n) ?v S W" unfolding choose'_def by blast
        } note \<sigma>_map_choose' = this
        hence \<sigma>_map_in_G: "\<And>n. \<sigma>_map n \<in> G" unfolding G_def using `\<And>n. P $ n \<in> S` by blast
        have \<sigma>_map_monotone: "\<And>n m. n < m \<Longrightarrow> (\<sigma>_map m, \<sigma>_map n) \<in> r" proof-
          {
            fix n
            have "(\<sigma>_map (Suc n), \<sigma>_map n) \<in> r" proof-
              have "strategy p (\<sigma>_map n)" using \<sigma>_map_choose' by blast
              moreover have *: "P $ n \<in> VV p \<Longrightarrow> \<sigma>_map n (P $ n) = P $ Suc n" proof-
                assume "P $ n \<in> VV p"
                hence "\<sigma> (P $ n) = P $ Suc n" using P_conforms P_valid path_conforms_with_strategy_conforms infinite_small_llength `\<not>lfinite P` by fastforce
                moreover have "\<sigma> (P $ n) = \<sigma>_map n (P $ n)" proof-
                  have "P $ n \<in> S - W" using `\<not>lfinite P` `lset P \<subseteq> S - W` llist_set_nth by blast
                  thus ?thesis by (simp add: \<sigma>_def)
                qed
                ultimately show "\<sigma>_map n (P $ n) = P $ Suc n" by simp
              qed
              moreover have "P $ n \<in> S - W" using `\<not>lfinite P` `lset P \<subseteq> S - W` llist_set_nth by blast
              moreover have "P $ n \<rightarrow> P $ Suc n" using P_valid `\<not>lfinite P` infinite_small_llength valid_path_edges by blast
              moreover have "strategy_attracts_via p (\<sigma>_map n) (P $ n) S W" using \<sigma>_map_choose' by blast
              ultimately have "strategy_attracts_via p (\<sigma>_map n) (P $ Suc n) S W" using strategy_attracts_via_successor[of p "\<sigma>_map n" "P $ n" S W "P $ Suc n"] \<sigma>_def `strategy p (\<sigma>_map n)` by force
              hence "\<sigma>_map n \<in> ?good (P $ Suc n)" using `strategy p (\<sigma>_map n)` by blast
              hence *: "(\<sigma>_map n, choose (P $ Suc n)) \<notin> r - Id" using `\<And>n. P $ n \<in> S` choose'_def choose_works by blast
              have "(choose (P $ Suc n), \<sigma>_map n) \<in> r" proof (cases)
                assume "\<sigma>_map n = choose (P $ Suc n)"
                moreover have "refl_on G r" using r unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by blast
                ultimately show ?thesis using \<sigma>_map_in_G refl_onD by fastforce
              next
                assume "\<sigma>_map n \<noteq> choose (P $ Suc n)"
                moreover with * have "(\<sigma>_map n, choose (P $ Suc n)) \<notin> r" by blast
                moreover have "total_on G r" using r unfolding well_order_on_def linear_order_on_def by blast
                ultimately show ?thesis by (metis \<sigma>_map_def \<sigma>_map_in_G total_on_def)
              qed
              thus ?thesis unfolding \<sigma>_map_def by blast
            qed
          } note case_Suc' = this
          {
            fix n m assume "(\<sigma>_map m, \<sigma>_map n) \<in> r"
            moreover have "(\<sigma>_map (Suc m), \<sigma>_map m) \<in> r" using case_Suc' by blast
            moreover have "trans r" using r unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by blast
            ultimately have "(\<sigma>_map (Suc m), \<sigma>_map n) \<in> r" by (meson transE)
          } note case_Suc = this

          fix n m :: nat assume "n < m"
          thus "(\<sigma>_map m, \<sigma>_map n) \<in> r" proof (induct "m - n" arbitrary: n m)
            case 0 thus ?case by simp
          next
            case (Suc d)
            show ?case proof (cases)
              assume "d = 0"
              thus ?thesis using case_Suc' by (metis Suc.hyps(2) Suc.prems Suc_diff_Suc Suc_inject Suc_leI diff_is_0_eq diffs0_imp_equal)
            next
              assume "d \<noteq> 0"
              have "m \<noteq> 0" using Suc.hyps(2) by linarith
              then obtain m' where m': "Suc m' = m" by (metis nat.exhaust)
              hence "d = m' - n" using Suc.hyps(2) by linarith
              hence "(\<sigma>_map m', \<sigma>_map n) \<in> r" using Suc.hyps(1) `d \<noteq> 0` zero_less_diff by blast
              thus ?thesis using m' case_Suc by blast
            qed
          qed
        qed
        def [simp]: \<sigma>_set \<equiv> "\<sigma>_map ` UNIV"
        have "\<exists>\<sigma>. \<sigma> \<in> \<sigma>_set" using \<sigma>_set_def by blast
        then obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> \<sigma>_set" "\<And>\<tau>. (\<tau>, \<sigma>') \<in> r - Id \<Longrightarrow> \<tau> \<notin> \<sigma>_set" using wfE_min[of "r - Id" _ \<sigma>_set] wf by blast
        then obtain n where n: "\<sigma>_map n = \<sigma>'" by auto
        have \<sigma>_map_constant: "\<And>m. n \<le> m \<Longrightarrow> \<sigma>_map n = \<sigma>_map m" proof-
          fix m assume "n \<le> m"
          show "\<sigma>_map n = \<sigma>_map m" proof (rule ccontr)
            assume *: "\<sigma>_map n \<noteq> \<sigma>_map m"
            with `n \<le> m` have "n < m" using le_imp_less_or_eq by blast
            with \<sigma>_map_monotone have "(\<sigma>_map m, \<sigma>_map n) \<in> r" by blast
            with * have "(\<sigma>_map m, \<sigma>_map n) \<in> r - Id" by simp
            with \<sigma>'(2) n have "\<sigma>_map m \<notin> \<sigma>_set" by blast
            thus False unfolding \<sigma>_set_def by blast
          qed
        qed
        def [simp]: P' \<equiv> "ldropn n P"
        have "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
        moreover have "valid_path P'" using P_valid by (simp add: valid_path_drop)
        moreover have "maximal_path P'" using P_maximal by (simp add: maximal_drop)
        moreover have "path_conforms_with_strategy p P' \<sigma>'" proof-
          have "\<And>v. v \<in> lset P' \<Longrightarrow> \<sigma> v = \<sigma>' v" proof-
            fix v assume "v \<in> lset P'"
            hence "v \<in> S - W" using `lset P \<subseteq> S - W` by (metis P'_def contra_subsetD in_lset_ldropnD)
            from `v \<in> lset P'` obtain m where m: "enat m < llength P'" "P' $ m = v" by (meson in_lset_conv_lnth)
            hence "P $ m + n = P' $ m" unfolding P'_def by (simp add: `\<not>lfinite P` infinite_small_llength)
            moreover have "\<sigma> v = choose v v" unfolding \<sigma>_def using `v \<in> S - W` by auto
            ultimately have "\<sigma> v = \<sigma>_map (m + n) v" unfolding \<sigma>_map_def using m(2) by auto
            thus "\<sigma> v = \<sigma>' v" using n \<sigma>_map_constant[of "m + n"] by simp
          qed
          moreover have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def by (simp add: P_conforms path_conforms_with_strategy_drop)
          ultimately show ?thesis using path_conforms_with_strategy_irrelevant_updates by blast
        qed
        moreover have "strategy p \<sigma>'" unfolding \<sigma>_set_def using \<sigma>'(1) G_def \<sigma>_map_in_G by auto
        moreover have "strategy_attracts_via p \<sigma>' (P' $ 0) S W" proof-
          have "P $ n \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lfinite P` llist_set_nth by blast
          hence "choose' (P $ n) (choose (P $ n))" using choose_works by blast
          hence "strategy_attracts_via p \<sigma>' (P $ n) S W" unfolding choose'_def using n \<sigma>_map_def by blast
          moreover have "P $ n = P' $ 0" unfolding P'_def by (simp add: `\<not>lfinite P` infinite_small_llength)
          ultimately show ?thesis by simp
        qed
        ultimately obtain m where m: "enat m < llength P'" "P' $ m \<in> W"
          unfolding strategy_attracts_via_def using `\<not>lnull P'` by blast
        moreover from `lset P \<subseteq> S - W` have "lset P' \<subseteq> S - W" using lset_ldropn_subset by fastforce
        ultimately show False by (meson Diff_iff lset_lnth)
      qed
    qed
  }
  hence "strategy_attracts p \<sigma> S W" using strategy_attracts_def strategy_attracts_via_def by auto
  thus ?thesis using \<sigma>_valid by auto
qed

lemma merge_winning_strategies:
  assumes "S \<subseteq> V" "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> (\<forall>v \<in> S. winning_strategy p \<sigma> v)"
proof-
  show ?thesis sorry
qed

end -- "context ParityGame"

end
