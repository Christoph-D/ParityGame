(* Theorems about how to get a uniform strategy given strategies for each node. *)
theory merge_strategies
imports
  Main
  parity_game strategy attractor
begin

locale WellOrderedStrategies = ParityGame +
  fixes S :: "'a set"
    and p :: Player
    and good :: "'a \<Rightarrow> 'a Strategy set" (* The set of good strategies on a node v *)
    and r :: "('a Strategy \<times> 'a Strategy) set"
  assumes S_V: "S \<subseteq> V"
    (* r is a wellorder on the set of all strategies which are good somewhere. *)
    and r_wo: "well_order_on {\<sigma>. \<exists>v \<in> S. \<sigma> \<in> good v} r"
    (* Every node has a good strategy. *)
    and good_ex: "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. \<sigma> \<in> good v"
    (* good strategies are well-formed strategies. *)
    and good_strategies: "\<And>v \<sigma>. \<sigma> \<in> good v \<Longrightarrow> strategy p \<sigma>"
    (* A good strategy on v is also good on possible successors of v. *)
    and strategies_continue: "\<And>v w \<sigma>. \<lbrakk> v \<in> S; v\<rightarrow>w; v \<in> VV p \<Longrightarrow> \<sigma> v = w; \<sigma> \<in> good v \<rbrakk> \<Longrightarrow> \<sigma> \<in> good w"
begin

(* The set of all strategies which are good somewhere. *)
abbreviation "Strategies \<equiv> {\<sigma>. \<exists>v \<in> S. \<sigma> \<in> good v}"

definition minimal_good_strategy where
  "minimal_good_strategy v \<sigma> \<equiv> \<sigma> \<in> good v \<and> (\<forall>\<sigma>'. (\<sigma>', \<sigma>) \<in> r - Id \<longrightarrow> \<sigma>' \<notin> good v)"

(* Among the good strategies on v, choose the minimum. *)
definition choose where
  "choose v \<equiv> THE \<sigma>. minimal_good_strategy v \<sigma>"

(* Define a strategy which uses the minimum strategy on all nodes of S.
   Of course, we need to prove that this is a well-formed strategy. *)
definition well_ordered_strategy where
  "well_ordered_strategy \<equiv> override_on \<sigma>_arbitrary (\<lambda>v. choose v v) S"

(* Show some simple properties of the binary relation r on the set Strategies. *)
lemma r_refl [simp]: "refl_on Strategies r"
  using r_wo unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by blast
lemma r_total [simp]: "total_on Strategies r"
  using r_wo unfolding well_order_on_def linear_order_on_def by blast
lemma r_trans [simp]: "trans r"
  using r_wo unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def by blast
lemma r_wf [simp]: "wf (r - Id)"
  using well_order_on_def r_wo by blast

(* Choose always chooses a minimal good strategy on S. *)
lemma choose_works:
  assumes "v \<in> S"
  shows "minimal_good_strategy v (choose v)"
proof-
  have wf: "wf (r - Id)" using well_order_on_def r_wo by blast
  obtain \<sigma> where \<sigma>1: "minimal_good_strategy v \<sigma>"
    unfolding minimal_good_strategy_def by (meson good_ex[OF `v \<in> S`] wf wf_eq_minimal)
  hence \<sigma>: "\<sigma> \<in> good v" "\<And>\<sigma>'. (\<sigma>', \<sigma>) \<in> r - Id \<Longrightarrow> \<sigma>' \<notin> good v"
    unfolding minimal_good_strategy_def by auto
  { fix \<sigma>' assume "minimal_good_strategy v \<sigma>'"
    hence \<sigma>': "\<sigma>' \<in> good v" "\<And>\<sigma>. (\<sigma>, \<sigma>') \<in> r - Id \<Longrightarrow> \<sigma> \<notin> good v"
      unfolding minimal_good_strategy_def by auto
    have "(\<sigma>, \<sigma>') \<notin> r - Id" using \<sigma>(1) \<sigma>'(2) by blast
    moreover have "(\<sigma>', \<sigma>) \<notin> r - Id" using \<sigma>(2) \<sigma>'(1) by auto
    moreover have "\<sigma> \<in> Strategies" using \<sigma>(1) `v \<in> S` by auto
    moreover have "\<sigma>' \<in> Strategies" using \<sigma>'(1) `v \<in> S` by auto
    ultimately have "\<sigma>' = \<sigma>"
      using r_wo Linear_order_in_diff_Id well_order_on_Field well_order_on_def by fastforce
  }
  with \<sigma>1 have "\<exists>!\<sigma>. minimal_good_strategy v \<sigma>" by blast
  thus ?thesis using theI'[of "minimal_good_strategy v", folded choose_def] by blast
qed

corollary
  assumes "v \<in> S"
  shows choose_good: "choose v \<in> good v"
    and choose_minimal: "\<And>\<sigma>'. (\<sigma>', choose v) \<in> r - Id \<Longrightarrow> \<sigma>' \<notin> good v"
    and choose_strategy: "strategy p (choose v)"
  using choose_works[OF assms, unfolded minimal_good_strategy_def] good_strategies by blast+

corollary choose_in_Strategies: "v \<in> S \<Longrightarrow> choose v \<in> Strategies" using assms choose_good by blast

lemma well_ordered_strategy_valid: "strategy p well_ordered_strategy"
proof-
  {
    fix v assume "v \<in> S" "v \<in> VV p" "\<not>deadend v"
    moreover have "strategy p (choose v)"
      using choose_works[OF `v \<in> S`, unfolded minimal_good_strategy_def, THEN conjunct1] good_strategies
      by blast
    ultimately have "v\<rightarrow>(\<lambda>v. choose v v) v" using strategy_def by blast
  }
  thus ?thesis unfolding well_ordered_strategy_def using valid_strategy_updates_set by force
qed

(* Maps a path to its strategies. *)
definition \<sigma>_map where "\<sigma>_map P \<equiv> \<lambda>n. choose (P $ n)"

lemma \<sigma>_map_in_Strategies:
  assumes "lset P \<subseteq> S" "enat n < llength P"
  shows "\<sigma>_map P n \<in> Strategies"
  using \<sigma>_map_def assms choose_in_Strategies lset_lnth by fastforce

lemma \<sigma>_map_good:
  assumes "lset P \<subseteq> S" "enat n < llength P"
  shows "\<sigma>_map P n \<in> good (P $ n)"
  by (simp add: \<sigma>_map_def assms choose_good lset_lnth)

lemma \<sigma>_map_strategy:
  assumes "lset P \<subseteq> S" "enat n < llength P"
  shows "strategy p (\<sigma>_map P n)"
  using \<sigma>_map_good assms good_strategies by blast


lemma \<sigma>_map_monotone_Suc:
  assumes P: "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
    "enat (Suc n) < llength P"
  shows "(\<sigma>_map P (Suc n), \<sigma>_map P n) \<in> r"
proof-
  def P' \<equiv> "ldropn n P"
  hence "enat (Suc 0) < llength P'" using P(4)
    by (metis enat_ltl_Suc ldrop_eSuc_ltl ldropn_Suc_conv_ldropn llist.disc(2) lnull_0_llength ltl_ldropn)
  then obtain v w Ps where vw: "P' = LCons v (LCons w Ps)" by (metis ldropn_0 ldropn_Suc_conv_ldropn ldropn_lnull lnull_0_llength)
  moreover have "lset P' \<subseteq> S" using P(1) P'_def lset_ldropn_subset by fastforce
  ultimately have "v \<in> S" "w \<in> S" by auto
  moreover have "v\<rightarrow>w" using valid_path_edges'[of v w Ps, folded vw] valid_path_drop[OF P(2)] P'_def by blast
  moreover have "choose v \<in> good v" using choose_good `v \<in> S` by blast
  moreover have "v \<in> VV p \<Longrightarrow> choose v v = w" proof-
    assume "v \<in> VV p"
    moreover have "path_conforms_with_strategy p P' well_ordered_strategy"
      unfolding P'_def using path_conforms_with_strategy_drop P(3) by blast
    ultimately have "well_ordered_strategy v = w" using vw path_conforms_with_strategy_start by blast
    thus "choose v v = w" unfolding well_ordered_strategy_def using `v \<in> S` by auto
  qed
  ultimately have "choose v \<in> good w" using strategies_continue by blast
  hence *: "(choose v, choose w) \<notin> r - Id" using choose_minimal `w \<in> S` by blast

  have "(choose w, choose v) \<in> r" proof (cases)
    assume "choose v = choose w"
    thus ?thesis using r_refl refl_onD choose_in_Strategies[OF `v \<in> S`] by fastforce
  next
    assume "choose v \<noteq> choose w"
    thus ?thesis using * r_total choose_in_Strategies[OF `v \<in> S`] choose_in_Strategies[OF `w \<in> S`]
      by (metis (lifting) Linear_order_in_diff_Id r_wo well_order_on_Field well_order_on_def)
  qed
  hence "(\<sigma>_map P' (Suc 0), \<sigma>_map P' 0) \<in> r" unfolding \<sigma>_map_def using vw by simp
  thus ?thesis by (metis P'_def \<sigma>_map_def assms(4) ldropn_Suc_conv_ldropn ldropn_eq_LConsD lnth_0 lnth_Suc_LCons vw)
qed

lemma \<sigma>_map_monotone:
  assumes P: "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
    "n < m" "enat m < llength P"
  shows "(\<sigma>_map P m, \<sigma>_map P n) \<in> r"
using assms proof (induct "m - n" arbitrary: n m, simp)
  case (Suc d)
  show ?case proof (cases)
    assume "d = 0"
    thus ?thesis using \<sigma>_map_monotone_Suc[OF P(1) P(2) P(3)]
      by (metis (no_types) Suc.hyps(2) Suc.prems(4) Suc.prems(5) Suc_diff_Suc Suc_inject Suc_leI diff_is_0_eq diffs0_imp_equal)
  next
    assume "d \<noteq> 0"
    have "m \<noteq> 0" using Suc.hyps(2) by linarith
    then obtain m' where m': "Suc m' = m" by (metis nat.exhaust)
    hence "d = m' - n" using Suc.hyps(2) by presburger
    moreover hence "n < m'" using `d \<noteq> 0` by presburger 
    ultimately have "(\<sigma>_map P m', \<sigma>_map P n) \<in> r"
      using Suc.hyps(1)[of m' n, OF _ P(1) P(2) P(3)] Suc.prems(5) dual_order.strict_trans enat_ord_simps(2) m'
      by blast
    thus ?thesis
      using m' \<sigma>_map_monotone_Suc[OF P(1) P(2) P(3)] by (metis (no_types) Suc.prems(5) r_trans trans_def)
  qed
qed

lemma \<sigma>_map_eventually_constant:
  assumes "\<not>lfinite P" "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
  shows "\<exists>n. \<forall>m \<ge> n. \<sigma>_map P n = \<sigma>_map P m"
proof-
  def \<sigma>_set \<equiv> "\<sigma>_map P ` UNIV"
  have "\<exists>\<sigma>. \<sigma> \<in> \<sigma>_set" using \<sigma>_set_def by blast
  then obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> \<sigma>_set" "\<And>\<tau>. (\<tau>, \<sigma>') \<in> r - Id \<Longrightarrow> \<tau> \<notin> \<sigma>_set"
    using wfE_min[of "r - Id" _ \<sigma>_set] by auto
  then obtain n where n: "\<sigma>_map P n = \<sigma>'" using \<sigma>_set_def by auto
  {
    fix m assume "n \<le> m"
    have "\<sigma>_map P n = \<sigma>_map P m" proof (rule ccontr)
      assume *: "\<sigma>_map P n \<noteq> \<sigma>_map P m"
      with `n \<le> m` have "n < m" using le_imp_less_or_eq by blast
      with \<sigma>_map_monotone have "(\<sigma>_map P m, \<sigma>_map P n) \<in> r" using assms by (simp add: infinite_small_llength)
      with * have "(\<sigma>_map P m, \<sigma>_map P n) \<in> r - Id" by simp
      with \<sigma>'(2) n have "\<sigma>_map P m \<notin> \<sigma>_set" by blast
      thus False unfolding \<sigma>_set_def by blast
    qed
  }
  thus ?thesis by blast
qed

lemma path_eventually_conforms_to_\<sigma>_map_n:
  assumes "\<not>lfinite P" "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
  shows "\<exists>n. path_conforms_with_strategy p (ldropn n P) (\<sigma>_map P n)"
proof-
  obtain n where n: "\<And>m. n \<le> m \<Longrightarrow> \<sigma>_map P n = \<sigma>_map P m" using \<sigma>_map_eventually_constant assms by blast
  let ?\<sigma> = well_ordered_strategy
  def P' \<equiv> "ldropn n P"
  { fix v assume "v \<in> lset P'"
    hence "v \<in> S" using `lset P \<subseteq> S` P'_def in_lset_ldropnD by fastforce
    from `v \<in> lset P'` obtain m where m: "enat m < llength P'" "P' $ m = v" by (meson in_lset_conv_lnth)
    hence "P $ m + n = P' $ m" unfolding P'_def by (simp add: `\<not>lfinite P` infinite_small_llength)
    moreover have "?\<sigma> v = choose v v" unfolding well_ordered_strategy_def using `v \<in> S` by auto
    ultimately have "?\<sigma> v = \<sigma>_map P (m + n) v" unfolding \<sigma>_map_def using m(2) by auto
    hence "?\<sigma> v = \<sigma>_map P n v" using n[of "m + n"] by simp
  }
  moreover have "path_conforms_with_strategy p P' well_ordered_strategy"
    unfolding P'_def by (simp add: assms(4) path_conforms_with_strategy_drop)
  ultimately show ?thesis
    using path_conforms_with_strategy_irrelevant_updates P'_def by blast
qed

end -- "WellOrderedStrategies"

context ParityGame begin

lemma no_winning_strategy_on_deadends:
  assumes "v \<in> VV p" "deadend v" "strategy p \<sigma>"
  shows "\<not>winning_strategy p \<sigma> v"
proof-
  obtain P where "vmc_path G P v p \<sigma>" using strategy_conforming_path_exists_single assms by blast
  then interpret vmc_path G P v p \<sigma> .
  have "lnull (ltl P)" using `deadend v` using P_LCons lnull_def valid_path_cons_simp by fastforce
  hence "P = LCons v LNil" by (metis P_LCons lnull_def)
  hence "\<not>winning_path p P" unfolding winning_path_def using `v \<in> VV p` by auto
  thus ?thesis using winning_strategy_def by fastforce
qed

(* An attractor set S - W of W cannot contain deadends because from deadends one cannot attract to W. *)
lemma attractor_no_deadends:
  assumes "S \<subseteq> V" "v \<in> S - W" "strategy_attracts_via p \<sigma> v S W"
  shows "\<not>deadend v"
proof
  assume "deadend v"
  def [simp]: P \<equiv> "LCons v LNil"
  interpret vmc_path G P v p \<sigma> proof
    show "valid_path P" using `v \<in> S - W` `S \<subseteq> V` valid_path_base' by auto
    show "maximal_path P" using `deadend v` by (simp add: maximal_path.intros(2))
    show "path_conforms_with_strategy p P \<sigma>" by (simp add: path_conforms_LCons_LNil)
  qed simp_all
  have "\<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> S"
    using assms(3) strategy_attracts_viaE by blast
  moreover have "llength P = eSuc 0" by simp
  ultimately have "P $ 0 \<in> W" by (simp add: enat_0_iff(1))
  with `v \<in> S - W` show False by auto
qed

lemma merge_attractor_strategies:
  assumes "S \<subseteq> V" and strategies_ex: "\<And>v. v \<in> S \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
proof-
  def good \<equiv> "\<lambda>v. { \<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v S W }"
  let ?G = "{\<sigma>. \<exists>v \<in> S - W. \<sigma> \<in> good v}"
  obtain r where r: "well_order_on ?G r" using well_order_on by blast

  interpret WellOrderedStrategies G "S - W" p good r proof
    show "S - W \<subseteq> V" using `S \<subseteq> V` by blast
  next
    show "well_order_on ?G r" using r .
  next
    show "\<And>v. v \<in> S - W \<Longrightarrow> \<exists>\<sigma>. \<sigma> \<in> good v" unfolding good_def using strategies_ex by blast
  next
    show "\<And>v \<sigma>. \<sigma> \<in> good v \<Longrightarrow> strategy p \<sigma>" unfolding good_def by blast
  next
    fix v w \<sigma> assume v: "v \<in> S - W" "v\<rightarrow>w" "v \<in> VV p \<Longrightarrow> \<sigma> v = w" "\<sigma> \<in> good v"
    hence \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v S W" unfolding good_def by simp_all
    hence "strategy_attracts_via p \<sigma> w S W" using strategy_attracts_via_successor v by blast
    thus "\<sigma> \<in> good w" unfolding good_def using \<sigma>(1) by blast
  qed

  def [simp]: \<sigma> \<equiv> "well_ordered_strategy"

  have S_W_no_deadends: "\<And>v. v \<in> S - W \<Longrightarrow> \<not>deadend v"
    using attractor_no_deadends[OF `S \<subseteq> V`] strategies_ex by (meson Diff_iff)

  {
    fix v0 assume "v0 \<in> S"
    fix P assume "vmc_path G P v0 p \<sigma>"
    then interpret vmc_path G P v0 p \<sigma> .
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
          then obtain n' where n': "Suc n' = n" by (metis nat.exhaust)
          hence "P $ n' \<in> S - W" using `\<And>i. i < n \<Longrightarrow> P $ i \<in> S - W` by blast
          def [simp]: P' \<equiv> "ldropn n' P"
          def [simp]: \<sigma>' \<equiv> "choose (P $ n')"
          hence \<sigma>': "strategy p \<sigma>'" "strategy_attracts_via p \<sigma>' (P $ n') S W"
            using `P $ n' \<in> S - W` choose_good good_def \<sigma>'_def by blast+
          have "enat n' < llength P" using n(1) n' using dual_order.strict_trans enat_ord_simps(2) by blast
          show False proof (cases)
            assume "P $ n' \<in> VV p"
            hence "\<sigma> (P $ n') \<in> S \<union> W"
              using \<sigma>'(1) \<sigma>'(2) \<sigma>_def `P $ n' \<in> S - W` assms(1) assms(2)
                strategy_attracts_VVp S_W_no_deadends well_ordered_strategy_def by auto
            moreover have "\<sigma> (P $ n') = P $ n" proof-
              have "enat (Suc n') < llength P" using n' n(1) by simp
              hence "\<sigma> (P $ n') = P $ Suc n'"
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

      obtain n where n: "path_conforms_with_strategy p (ldropn n P) (\<sigma>_map P n)"
        using path_eventually_conforms_to_\<sigma>_map_n[OF `\<not>lfinite P` `lset P \<subseteq> S - W` P_valid P_conforms[unfolded \<sigma>_def]]
          by blast
      def [simp]: \<sigma>' \<equiv> "\<sigma>_map P n"
      def [simp]: P' \<equiv> "ldropn n P"
      interpret vmc_path G P' "lhd P'" p \<sigma>' proof
        show "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
        show "valid_path P'" using P_valid by (simp add: valid_path_drop)
        show "maximal_path P'" using P_maximal by (simp add: maximal_drop)
        show "path_conforms_with_strategy p P' \<sigma>'" using n by simp
      qed simp
      have "strategy p \<sigma>'" unfolding \<sigma>'_def
        using \<sigma>_map_strategy `lset P \<subseteq> S - W` `\<not>lfinite P` infinite_small_llength by blast
      moreover have "strategy_attracts_via p \<sigma>' (lhd P') S W" proof-
        have "P $ n \<in> S - W" using `lset P \<subseteq> S - W` `\<not>lfinite P` llist_set_nth by blast
        hence "\<sigma>' \<in> good (P $ n)" using \<sigma>_map_good by (simp add: \<sigma>_map_def choose_good)
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
    show "S \<subseteq> V" using `S \<subseteq> V` .
  next
    show "well_order_on ?G r" using r .
  next
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
  qed

  have S_closed: "\<And>v w \<sigma>. \<lbrakk> v \<in> S; v\<rightarrow>w; v \<in> VV p \<Longrightarrow> \<sigma> v = w; \<sigma> \<in> good v \<rbrakk> \<Longrightarrow> w \<in> S" proof-
    fix v w \<sigma> assume "v \<in> S" "v\<rightarrow>w" "v \<in> VV p \<Longrightarrow> \<sigma> v = w" "\<sigma> \<in> good v"
    hence "\<sigma> \<in> good w" using strategies_continue by blast
    thus "w \<in> S" using strategies_continue good_def strategies_ex `v\<rightarrow>w` by blast
  qed

  def [simp]: \<sigma> \<equiv> "well_ordered_strategy"
  {
    fix v0 assume "v0 \<in> S"
    fix P assume P: "vmc_path G P v0 p \<sigma>"
    then interpret vmc_path G P v0 p \<sigma> .
    have "winning_path p P" proof (rule ccontr)
      assume contra: "\<not>winning_path p P"
      hence "winning_path p** P" using paths_are_winning_for_exactly_one_player P_valid by blast
      have "lset P \<subseteq> S" proof
        fix v assume "v \<in> lset P"
        thus "v \<in> S" using `v0 \<in> S` P `winning_path p** P` proof (induct arbitrary: v0 rule: llist_set_induct)
          case (find P)
          then interpret vmc_path G P v0 p \<sigma> by blast
          show ?case by (simp add: find.prems(1))
        next
          case (step P v)
          then interpret vmc_path G P v0 p \<sigma> by blast
          show ?case proof (cases)
            assume "lnull (ltl P)"
            hence "P = LCons v LNil" by (metis llist.disc(2) lset_cases step.hyps(2))
            thus ?thesis using step.prems(1) P_LCons by blast
          next
            assume "\<not>lnull (ltl P)"
            then interpret vmc_path_no_deadend G P v0 p \<sigma> using vmc_path_lnull_ltl_no_deadend by blast
            { assume "v0 \<in> VV p"
              hence "\<sigma> v0 = w0" using v0_conforms by blast
              hence "choose v0 v0 = w0" by (simp add: v0_conforms step.prems(1) well_ordered_strategy_def)
            }
            hence "w0 \<in> S" using S_closed `v0\<rightarrow>w0` choose_good step.prems(1) by blast
            moreover have "vmc_path G (ltl P) w0 p \<sigma>" using vmc_path_ltl by blast
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
        moreover have "llast P \<in> VV p" using `winning_path p** P` `lfinite P` `\<not>lnull P` unfolding winning_path_def by simp
        ultimately show False using no_VVp_deadends by blast
      qed

      obtain n where n: "path_conforms_with_strategy p (ldropn n P) (\<sigma>_map P n)"
        using path_eventually_conforms_to_\<sigma>_map_n[OF `\<not>lfinite P` `lset P \<subseteq> S` P_valid P_conforms[unfolded \<sigma>_def]]
          by blast
      def [simp]: \<sigma>' \<equiv> "\<sigma>_map P n"
      def [simp]: P' \<equiv> "ldropn n P"
      interpret P': vmc_path G P' "lhd P'" p \<sigma>' proof
        show "\<not>lnull P'" using `\<not>lfinite P` using P'_def infinite_no_deadend lfinite_ldropn by blast
        show "valid_path P'" using P_valid by (simp add: valid_path_drop)
        show "maximal_path P'" using P_maximal by (simp add: maximal_drop)
        show "path_conforms_with_strategy p P' \<sigma>'" using n by simp
      qed simp
      have "strategy p \<sigma>'" unfolding \<sigma>'_def
        using \<sigma>_map_strategy `lset P \<subseteq> S` `\<not>lfinite P` by blast
      moreover have "winning_strategy p \<sigma>' (lhd P')" proof-
        have "P $ n \<in> S" using `lset P \<subseteq> S` `\<not>lfinite P` llist_set_nth by blast
        hence "\<sigma>' \<in> good (P $ n)" using \<sigma>_map_good by (simp add: \<sigma>_map_def choose_good)
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
