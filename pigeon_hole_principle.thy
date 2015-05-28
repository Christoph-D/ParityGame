theory pigeon_hole_principle
imports
  Main
begin

(*
  The infinite/finite pigeon hole principle.  Given a surjective function f: nat \<Rightarrow> X into a
  finite set X, there exists an element x \<in> X such that there are infinitely many i with f(i) = x.
*)
lemma pigeon_hole_principle_weak:
  fixes X :: "'a set"
    and f :: "nat \<Rightarrow> 'a"
  assumes "finite X"
    and codom_f_is_X: "\<forall>i. f(i) \<in> X"
    and f_is_surjective: "\<forall>x \<in> X. \<exists>i. f(i) = x"
  shows "\<exists>x \<in> X. \<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x))"
  proof -
  from `finite X` have
    "\<lbrakk> \<forall>i. f(i) \<in> X; \<forall>x \<in> X. \<exists>i. f(i) = x \<rbrakk> \<Longrightarrow> (\<exists>x \<in> X. \<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)))"
  proof (induct X arbitrary: f rule: finite_induct)
    case empty then show ?case by auto
  next
    case (insert a Y)
    show "\<exists>x \<in> insert a Y. \<forall>i. f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)"
    proof cases
      assume "Y = {}" then show ?case using insert by blast
    next
      assume "Y \<noteq> {}" then obtain z where "z \<in> Y" by blast
      show ?case
      proof cases
        (* If $f$ hits the element $a$ infinitely often, we are done. *)
        assume "\<forall>i. f(i) = a \<longrightarrow> (\<exists>j > i. f(j) = a)"
        then show ?case by blast
      next
        (* $f$ hits the element $a$ only finitely often. *)
        assume a_is_no_good: "\<not>(\<forall>i. f(i) = a \<longrightarrow> (\<exists>j > i. f(j) = a))"
        (* We define a function g with codomain Y so that we can use the induction hypothesis. *)
        def g \<equiv> "\<lambda>i. (if f(i) = a then z else f(i))"
        have codom_g_is_Y: "\<And>i. g(i) \<in> Y"
        proof -
          fix i show "g(i) \<in> Y"
          proof cases
            assume "f(i) = a"
            then show ?thesis using g_def `z \<in> Y` by auto
          next
            assume "f(i) \<noteq> a"
            then have "g(i) = f(i)" using g_def by simp
            moreover have "f(i) \<in> Y" using `f(i) \<noteq> a` insert by auto
            ultimately show ?thesis by auto
          qed
        qed
        have precond2: "\<And>x. x \<in> Y \<Longrightarrow> \<exists>i. g(i) = x"
        proof -
          fix x assume "x \<in> Y"
          then have "x \<in> insert a Y" by auto
          then obtain i where "f(i) = x" using insert by auto
          then have "g(i) = x" using `x \<in> Y` g_def insert by auto
          then show "\<exists>i. g(i) = x" by auto
        qed
        obtain x where x_def: "x \<in> Y \<and> (\<forall>i. g(i) = x \<longrightarrow> (\<exists>j > i. g(j) = x))" using codom_g_is_Y insert.hyps(3) by blast
        have "\<forall>i. f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)" by (metis (full_types) a_is_no_good dual_order.strict_trans g_def insert.hyps(2) nat_neq_iff x_def)
        then show ?case using x_def by blast
      qed
    qed
  qed
  then show ?thesis using codom_f_is_X by fastforce
qed

theorem pigeon_hole_principle:
  fixes X :: "'a set" and f :: "nat \<Rightarrow> 'a"
  assumes "finite X" and codom_f_is_X: "\<forall>i. f(i) \<in> X"
  shows "\<exists>x \<in> X. (\<exists>i. f(i) = x) \<and> (\<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)))"
  proof -
    def Y \<equiv> "{x \<in> X. \<exists>i. f(i) = x}"
    then have "finite Y" using `finite X` finite_subset by auto
    have codom_f_is_Y: "\<forall>i. f(i) \<in> Y" using Y_def codom_f_is_X by blast
    have f_surjective: "\<forall>x \<in> Y. \<exists>i. f(i) = x" using Y_def by blast
    then have "\<exists>x \<in> Y. (\<exists>i. f(i) = x) \<and> (\<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)))"
      by (simp add: pigeon_hole_principle_weak `finite Y` codom_f_is_Y)
    then show ?thesis using codom_f_is_X by blast
  qed

end
