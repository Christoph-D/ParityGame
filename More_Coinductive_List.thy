theory More_Coinductive_List
imports
  Main
  "Coinductive/Coinductive_List"
begin

lemma llist_set_nth: "\<lbrakk> \<not>lfinite x; lset x \<subseteq> X \<rbrakk> \<Longrightarrow> lnth x i \<in> X"
  by (metis contra_subsetD inf_llist_lnth lset_inf_llist rangeI)
lemma enat_Suc_ltl: assumes "enat (Suc i) < llength xs" shows "enat i < llength (ltl xs)" proof-
  from assms have "eSuc (enat i) < llength xs" by (simp add: eSuc_enat)
  hence "enat i < epred (llength xs)" using eSuc_le_iff ileI1 by fastforce
  thus ?thesis by (simp add: epred_llength)
qed
lemma enat_ltl_Suc: "enat i < llength (ltl xs) \<Longrightarrow> enat (Suc i) < llength xs"
  by (metis assms eSuc_enat ldrop_ltl leD leI lnull_ldrop)
lemma lset_intersect_lnth: "lset xs \<inter> A \<noteq> {} \<Longrightarrow> \<exists>i. enat i < llength xs \<and> lnth xs i \<in> A"
  by (metis assms disjoint_iff_not_equal in_lset_conv_lnth)
lemma infinite_small_llength [intro]: "\<not>lfinite xs \<Longrightarrow> enat i < llength xs"
  using enat_iless lfinite_conv_llength_enat neq_iff by blast
lemma lnull_0_llength: "\<not>lnull xs \<Longrightarrow> enat 0 < llength xs"
  using zero_enat_def by auto
lemma ltake_lnth: "ltake n xs = ltake n ys \<Longrightarrow> enat m < n \<Longrightarrow> lnth xs m = lnth ys m"
  by (metis lnth_ltake)
lemma enat_0_lt_Suc [simp]: "0 < enat (Suc n)"
  by (simp add: enat_0_iff(1))
lemma lprefix_lset' [simp]: "n \<le> m \<Longrightarrow> lset (ltake n xs) \<subseteq> lset (ltake m xs)"
  by (simp add: lprefix_lsetD)
lemma lset_lnth: "lset xs \<subseteq> A \<Longrightarrow> enat n < llength xs \<Longrightarrow> lnth xs n \<in> A"
  by (meson contra_subsetD in_lset_conv_lnth)
lemma lset_ltake_Suc: "lset (ltake n xs) \<subseteq> A \<Longrightarrow> lset (ltake (eSuc n) (LCons x xs)) \<subseteq> insert x A"
  by auto
lemma lset_ltake_Suc':
  assumes "\<not>lnull xs" "lnth xs 0 = x" "lset (ltake (enat n) (ltl xs)) \<subseteq> A"
  shows "lset (ltake (enat (Suc n)) xs) \<subseteq> insert x A"
proof-
  from assms(3) have "lset (ltake (eSuc (enat n)) (LCons x (ltl xs))) \<subseteq> insert x A"
    using lset_ltake_Suc[of "enat n" "ltl xs" A x] by blast
  moreover from assms have "LCons x (ltl xs) = xs" by (metis lnth_0 ltl_simps(2) not_lnull_conv)
  ultimately show ?thesis by (simp add: eSuc_enat)
qed
lemma lnth_lprefix: "\<not>lnull xs \<Longrightarrow> lprefix xs ys \<Longrightarrow> lnth xs 0 = lnth ys 0"
  by (simp add: lnth_0_conv_lhd lprefix_lhdD lprefix_not_lnullD)
lemma lfinite_lset: "lfinite xs \<Longrightarrow> \<not>lnull xs \<Longrightarrow> llast xs \<in> lset xs"
proof (induct rule: lfinite_induct, simp)
  case (LCons xs)
  show ?case proof (cases "lnull (ltl xs)")
    case True
    thus ?thesis by (metis LCons.prems lhd_LCons_ltl llast_LCons llist.set_sel(1))
  next
    case False
    hence "llast (ltl xs) \<in> lset (ltl xs)" using LCons.hyps(3) by blast
    hence "llast (ltl xs) \<in> lset xs" by (simp add: in_lset_ltlD)
    thus ?thesis by (metis False LCons.prems lhd_LCons_ltl llast_LCons2)
  qed
qed
lemma ltl_ldrop: "(\<And>xs. P xs \<Longrightarrow> P (ltl xs)) \<Longrightarrow> P xs \<Longrightarrow> P (ldropn n xs)"
  unfolding ldropn_def by (induct n) simp_all
lemma lset_subset: "\<not>(lset xs \<subseteq> A) \<Longrightarrow> \<exists>n. enat n < llength xs \<and> lnth xs n \<notin> A"
  by (metis in_lset_conv_lnth subsetI)

lemma lset_ltake: "(\<And>i. i < n \<Longrightarrow> lnth xs i \<in> A) \<Longrightarrow> lset (ltake (enat n) xs) \<subseteq> A"
proof (induct n arbitrary: xs)
  case 0
  have "ltake (enat 0) xs = LNil" by (simp add: zero_enat_def)
  thus ?case by simp
next
  case (Suc n)
  show ?case proof (cases "xs = LNil", simp)
    assume "xs \<noteq> LNil"
    then obtain x xs' where xs: "xs = LCons x xs'" by (meson neq_LNil_conv)
    have "\<And>i. i < n \<Longrightarrow> lnth xs' i \<in> A" proof-
      fix i assume "i < n"
      hence "Suc i < Suc n" by simp
      hence "lnth xs (Suc i) \<in> A" using Suc.prems by presburger
      thus "lnth xs' i \<in> A" using xs by simp
    qed
    hence "lset (ltake (enat n) xs') \<subseteq> A" using Suc.hyps by blast
    moreover have "ltake (enat (Suc n)) xs = LCons x (ltake (enat n) xs')"
      using xs ltake_eSuc_LCons[of _ x xs'] by (metis (no_types) eSuc_enat)
    moreover have "x \<in> A" using Suc.prems xs by force
    ultimately show ?thesis by simp
  qed
qed

lemma llength_ltake': "enat n < llength xs \<Longrightarrow> llength (ltake (enat n) xs) = enat n"
  by (metis assms llength_ltake min.strict_order_iff)
lemma llast_ltake:
  assumes "enat (Suc n) < llength xs"
  shows "llast (ltake (enat (Suc n)) xs) = lnth xs n" (is "llast ?A = _")
  unfolding llast_def using llength_ltake'[OF assms] by (auto simp add: lnth_ltake)

lemma infinite_no_deadend: "\<not>lfinite xs \<Longrightarrow> \<not>lnull xs" by auto
lemma ltl_inf: "\<not>lfinite xs \<Longrightarrow> lnth xs (Suc i) = lnth (ltl xs) i"
  by (simp add: infinite_no_deadend lnth_ltl)
lemma path_set_at: "v \<in> lset xs \<Longrightarrow> \<exists>n. lnth xs n = v"
  by (induct rule: llist.set_induct, meson lnth_0, meson lnth_Suc_LCons)
lemma lfinite_drop: "lfinite xs \<Longrightarrow> \<exists>n. ldrop n xs = LNil" by auto
lemma lfinite_drop_set: "lfinite xs \<Longrightarrow> \<exists>n. v \<notin> lset (ldrop n xs)"
  by (metis ldrop_inf lmember_code(1) lset_lmember)
lemma in_set_ldropn: "x \<in> lset (ldropn (Suc n) xs) \<Longrightarrow> x \<in> lset (ldropn n xs)"
  by (simp add: in_lset_ltlD ldrop_eSuc_ltl ltl_ldropn)

lemma lset_ltake_ltl: "lset (ltake (enat n) (ltl xs)) \<subseteq> lset (ltake (enat (Suc n)) xs)"
proof (cases)
  assume "\<not>lnull xs"
  then obtain v0 where "xs = LCons v0 (ltl xs)" by (metis lhd_LCons_ltl)
  hence "ltake (eSuc (enat n)) xs = LCons v0 (ltake (enat n) (ltl xs))"
    by (metis assms ltake_eSuc_LCons)
  hence "lset (ltake (enat (Suc n)) xs) = lset (LCons v0 (ltake (enat n) (ltl xs)))"
    by (simp add: eSuc_enat)
  thus ?thesis using lset_LCons[of v0 "ltake (enat n) (ltl xs)"] by blast
qed (simp add: lnull_def)

lemma lprefix_llength: "\<lbrakk> lprefix P P'; i < llength P \<rbrakk> \<Longrightarrow> i < llength P'"
  using less_le_trans lprefix_llength_le by blast

notation lnth (infix "$" 61)

end