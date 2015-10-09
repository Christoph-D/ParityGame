theory Well_Ordered_Strategy
imports
  Main
  strategy
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
definition "path_strategies \<equiv> lmap choose"

lemma path_strategies_in_Strategies:
  assumes "lset P \<subseteq> S"
  shows "lset (path_strategies P) \<subseteq> Strategies"
  using path_strategies_def assms choose_in_Strategies by auto

lemma path_strategies_good:
  assumes "lset P \<subseteq> S" "enat n < llength P"
  shows "path_strategies P $ n \<in> good (P $ n)"
  by (simp add: path_strategies_def assms choose_good lset_lnth)

lemma path_strategies_strategy:
  assumes "lset P \<subseteq> S" "enat n < llength P"
  shows "strategy p (path_strategies P $ n)"
  using path_strategies_good assms good_strategies by blast


lemma path_strategies_monotone_Suc:
  assumes P: "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
    "enat (Suc n) < llength P"
  shows "(path_strategies P $ Suc n, path_strategies P $ n) \<in> r"
proof-
  def P' \<equiv> "ldropn n P"
  hence "enat (Suc 0) < llength P'" using P(4)
    by (metis enat_ltl_Suc ldrop_eSuc_ltl ldropn_Suc_conv_ldropn llist.disc(2) lnull_0_llength ltl_ldropn)
  then obtain v w Ps where vw: "P' = LCons v (LCons w Ps)"
    by (metis ldropn_0 ldropn_Suc_conv_ldropn ldropn_lnull lnull_0_llength)
  moreover have "lset P' \<subseteq> S" unfolding P'_def using P(1) lset_ldropn_subset[of n P] by blast
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
  hence "(path_strategies P' $ Suc 0, path_strategies P' $ 0) \<in> r"
    unfolding path_strategies_def using vw by simp
  thus ?thesis unfolding path_strategies_def P'_def
    using lnth_lmap_ldropn[OF Suc_llength[OF P(4)], of choose]
          lnth_lmap_ldropn_Suc[OF P(4), of choose]
    by simp
qed

lemma path_strategies_monotone:
  assumes P: "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
    "n < m" "enat m < llength P"
  shows "(path_strategies P $ m, path_strategies P $ n) \<in> r"
using assms proof (induct "m - n" arbitrary: n m, simp)
  case (Suc d)
  show ?case proof (cases)
    assume "d = 0"
    thus ?thesis using path_strategies_monotone_Suc[OF P(1,2,3)]
      by (metis (no_types) Suc.hyps(2) Suc.prems(4,5) Suc_diff_Suc Suc_inject Suc_leI diff_is_0_eq diffs0_imp_equal)
  next
    assume "d \<noteq> 0"
    have "m \<noteq> 0" using Suc.hyps(2) by linarith
    then obtain m' where m': "Suc m' = m" using not0_implies_Suc by blast
    hence "d = m' - n" using Suc.hyps(2) by presburger
    moreover hence "n < m'" using `d \<noteq> 0` by presburger 
    ultimately have "(path_strategies P $ m', path_strategies P $ n) \<in> r"
      using Suc.hyps(1)[of m' n, OF _ P(1,2,3)] Suc.prems(5) dual_order.strict_trans enat_ord_simps(2) m'
      by blast
    thus ?thesis
      using m' path_strategies_monotone_Suc[OF P(1,2,3)] by (metis (no_types) Suc.prems(5) r_trans trans_def)
  qed
qed

lemma path_strategies_eventually_constant:
  assumes "\<not>lfinite P" "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
  shows "\<exists>n. \<forall>m \<ge> n. path_strategies P $ n = path_strategies P $ m"
proof-
  def \<sigma>_set \<equiv> "lset (path_strategies P)"
  have "\<exists>\<sigma>. \<sigma> \<in> \<sigma>_set" unfolding \<sigma>_set_def path_strategies_def
    by (metis assms(1) image_eqI llist.set_map llist_nth_set)
  then obtain \<sigma>' where \<sigma>': "\<sigma>' \<in> \<sigma>_set" "\<And>\<tau>. (\<tau>, \<sigma>') \<in> r - Id \<Longrightarrow> \<tau> \<notin> \<sigma>_set"
    using wfE_min[of "r - Id" _ \<sigma>_set] by auto
  obtain n where n: "path_strategies P $ n = \<sigma>'"
    using \<sigma>'(1) path_set_at[of \<sigma>'] unfolding \<sigma>_set_def by blast
  {
    fix m assume "n \<le> m"
    have "path_strategies P $ n = path_strategies P $ m" proof (rule ccontr)
      assume *: "path_strategies P $ n \<noteq> path_strategies P $ m"
      with `n \<le> m` have "n < m" using le_imp_less_or_eq by blast
      with path_strategies_monotone have "(path_strategies P $ m, path_strategies P $ n) \<in> r"
        using assms by (simp add: infinite_small_llength)
      with * have "(path_strategies P $ m, path_strategies P $ n) \<in> r - Id" by simp
      with \<sigma>'(2) n have "path_strategies P $ m \<notin> \<sigma>_set" by blast
      thus False unfolding \<sigma>_set_def
        by (metis (mono_tags, lifting) assms(1) lfinite_lmap llist_nth_set path_strategies_def)
    qed
  }
  thus ?thesis by blast
qed

lemma path_eventually_conforms_to_\<sigma>_map_n:
  assumes "\<not>lfinite P" "lset P \<subseteq> S" "valid_path P" "path_conforms_with_strategy p P well_ordered_strategy"
  shows "\<exists>n. path_conforms_with_strategy p (ldropn n P) (path_strategies P $ n)"
proof-
  obtain n where n: "\<And>m. n \<le> m \<Longrightarrow> path_strategies P $ n = path_strategies P $ m"
    using path_strategies_eventually_constant assms by blast
  let ?\<sigma> = well_ordered_strategy
  def P' \<equiv> "ldropn n P"
  { fix v assume "v \<in> lset P'"
    hence "v \<in> S" using `lset P \<subseteq> S` P'_def in_lset_ldropnD by fastforce
    from `v \<in> lset P'` obtain m where m: "enat m < llength P'" "P' $ m = v" by (meson in_lset_conv_lnth)
    hence "P $ m + n = v" unfolding P'_def by (simp add: `\<not>lfinite P` infinite_small_llength)
    moreover have "?\<sigma> v = choose v v" unfolding well_ordered_strategy_def using `v \<in> S` by auto
    ultimately have "?\<sigma> v = (path_strategies P $ m + n) v"
      unfolding path_strategies_def using infinite_small_llength[OF assms(1)] by simp
    hence "?\<sigma> v = (path_strategies P $ n) v" using n[of "m + n"] by simp
  }
  moreover have "path_conforms_with_strategy p P' well_ordered_strategy"
    unfolding P'_def by (simp add: assms(4) path_conforms_with_strategy_drop)
  ultimately show ?thesis
    using path_conforms_with_strategy_irrelevant_updates P'_def by blast
qed

end -- "WellOrderedStrategies"

end
