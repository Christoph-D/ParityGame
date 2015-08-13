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
using assms proof (induct X arbitrary: f rule: finite_induct)
  case empty then show ?case by auto
next
  case (insert a Y)
  show "\<exists>x \<in> insert a Y. \<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x))"
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
      then have codom_g_is_Y: "\<And>i. g(i) \<in> Y"
        using `z \<in> Y` insert.prems(1) by auto
      (* Now we can define an element x \<in> Y that f hits infinitely often. *)
      then obtain x where x_def: "x \<in> Y \<and> (\<forall>i. g(i) = x \<longrightarrow> (\<exists>j > i. g(j) = x))"
        using insert.hyps(3) by blast
      have "\<forall>i. f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)"
        by (metis (full_types) a_is_no_good dual_order.strict_trans g_def insert.hyps(2) nat_neq_iff x_def)
      then show ?case using x_def by blast
    qed
  qed
qed

(* The same as above without the requirement that f is surjective. *)
theorem pigeon_hole_principle:
  fixes X :: "'a set"
    and f :: "nat \<Rightarrow> 'a"
  assumes "finite X"
    and codom_f_is_X: "\<forall>i. f(i) \<in> X"
  shows "\<exists>x \<in> X. (\<exists>i. f(i) = x) \<and> (\<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)))"
proof-
  def Y \<equiv> "range f \<inter> X" (* Intersecting with X simplifies the proof. *)
  then have "finite Y" by (simp add: `finite X`)
  have codom_f_is_Y: "\<forall>i. f(i) \<in> Y" by (simp add: Y_def codom_f_is_X)
  have f_surjective: "\<forall>x \<in> Y. \<exists>i. f(i) = x" using Y_def by blast
  then have "\<exists>x \<in> Y. (\<exists>i. f(i) = x) \<and> (\<forall>i. (f(i) = x \<longrightarrow> (\<exists>j > i. f(j) = x)))"
    by (simp add: pigeon_hole_principle_weak `finite Y` codom_f_is_Y)
  then show ?thesis using codom_f_is_X by blast
qed

end
