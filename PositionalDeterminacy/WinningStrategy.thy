section {* Winning strategies *}

theory WinningStrategy
imports
  Main
  Strategy
begin

context ParityGame begin

text {*
  Here we define winning strategies.

  A strategy is winning for player @{term p} from @{term v0} if every maximal @{term \<sigma>}-path
  starting in @{term v0} is winning.
*}
definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  "winning_strategy p \<sigma> v0 \<equiv> \<forall>P. vmc_path G P v0 p \<sigma> \<longrightarrow> winning_path p P"

lemma winning_strategyI:
  assumes "\<And>P. vmc_path G P v0 p \<sigma> \<Longrightarrow> winning_path p P"
  shows "winning_strategy p \<sigma> v0"
  unfolding winning_strategy_def using assms by blast

lemma (in vmc_path) paths_hits_winning_strategy_is_winning:
  assumes \<sigma>: "winning_strategy p \<sigma> v"
    and v: "v \<in> lset P"
  shows "winning_path p P"
proof-
  obtain n where n: "enat n < llength P" "P $ n = v" using v by (meson in_lset_conv_lnth)
  interpret P': vmc_path G "ldropn n P" v p \<sigma> using n vmc_path_ldropn by blast
  have "winning_path p (ldropn n P)" using \<sigma> by (simp add: winning_strategy_def)
  thus ?thesis using winning_path_drop_add P_valid n(1) by blast
qed

subsection {* Deadends *}

lemma no_winning_strategy_on_deadends:
  assumes "v \<in> VV p" "deadend v" "strategy p \<sigma>"
  shows "\<not>winning_strategy p \<sigma> v"
proof-
  obtain P where "vmc_path G P v p \<sigma>" using strategy_conforming_path_exists_single assms by blast
  then interpret vmc_path G P v p \<sigma> .
  have "P = LCons v LNil" using P_deadend_v0_LCons `deadend v` by blast
  hence "\<not>winning_path p P" unfolding winning_path_def using `v \<in> VV p` by auto
  thus ?thesis using winning_strategy_def by fastforce
qed

lemma winning_strategy_on_deadends:
  assumes "v \<in> VV p" "deadend v" "strategy p \<sigma>"
  shows "winning_strategy p** \<sigma> v"
proof (rule winning_strategyI)
  fix P assume "vmc_path G P v p** \<sigma>"
  then interpret vmc_path G P v "p**" \<sigma> .
  have "P = LCons v LNil" using P_deadend_v0_LCons `deadend v` by blast
  thus "winning_path p** P" unfolding winning_path_def
    using `v \<in> VV p` P_valid paths_are_winning_for_one_player by auto
qed

subsection {* Extension theorems *}

lemma strategy_extends_VVp:
  assumes v0: "v0 \<in> VV p" "\<not>deadend v0"
  and \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
  shows "winning_strategy p \<sigma> (\<sigma> v0)"
proof (rule winning_strategyI)
  fix P assume "vmc_path G P (\<sigma> v0) p \<sigma>"
  then interpret vmc_path G P "\<sigma> v0" p \<sigma> .
  have "v0\<rightarrow>\<sigma> v0" using v0 \<sigma>(1) strategy_def by blast
  hence "winning_path p (LCons v0 P)"
    using \<sigma>(2) extension_valid_maximal_conforming winning_strategy_def by blast
  thus "winning_path p P" using winning_path_ltl[of p "LCons v0 P"] by simp
qed

lemma strategy_extends_VVpstar:
  assumes v0: "v0 \<in> VV p**" "v0\<rightarrow>w0"
  and \<sigma>: "winning_strategy p \<sigma> v0"
  shows "winning_strategy p \<sigma> w0"
proof (rule winning_strategyI)
  fix P assume "vmc_path G P w0 p \<sigma>"
  then interpret vmc_path G P w0 p \<sigma> .
  have "winning_path p (LCons v0 P)"
    using extension_valid_maximal_conforming VV_impl1 \<sigma> v0 winning_strategy_def
    by auto
  thus "winning_path p P" using winning_path_ltl[of p "LCons v0 P"] by auto
qed

lemma strategy_extends_backwards_VVpstar:
  assumes v0: "v0 \<in> VV p**"
    and \<sigma>: "strategy p \<sigma>" "\<And>w. v0\<rightarrow>w \<Longrightarrow> winning_strategy p \<sigma> w"
  shows "winning_strategy p \<sigma> v0"
proof (rule winning_strategyI)
  fix P assume "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> .
  show "winning_path p P" proof (cases)
    assume "deadend v0"
    thus ?thesis using P_deadend_v0_LCons winning_path_def v0 by auto
  next
    assume "\<not>deadend v0"
    then interpret vmc_path_no_deadend G P v0 p \<sigma> by unfold_locales
    interpret ltlP: vmc_path G "ltl P" w0 p \<sigma> using vmc_path_ltl .
    have "winning_path p (ltl P)"
      using \<sigma>(2) v0_edge_w0 vmc_path_ltl winning_strategy_def by blast
    thus "winning_path p P"
      using winning_path_LCons by (metis P_LCons' ltlP.P_LCons ltlP.P_not_null)
  qed
qed

lemma strategy_extends_backwards_VVp:
  assumes v0: "v0 \<in> VV p" "\<sigma> v0 = w" "v0\<rightarrow>w"
    and \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> w"
  shows "winning_strategy p \<sigma> v0"
proof (rule winning_strategyI)
  fix P assume "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> .
  have "\<not>deadend v0" using `v0\<rightarrow>w` by blast
  then interpret vmc_path_no_deadend G P v0 p \<sigma> by unfold_locales
  have "winning_path p (ltl P)"
    using \<sigma>(2)[unfolded winning_strategy_def] v0(1,2) v0_conforms vmc_path_ltl by presburger
  thus "winning_path p P" using winning_path_LCons by (metis P_LCons Ptl_not_null)
qed

subsection {* Winning regions *}

definition "winning_region p \<equiv> { v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }"

lemma winning_regionI:
  assumes "v \<in> V" "strategy p \<sigma>" "winning_strategy p \<sigma> v"
  shows "v \<in> winning_region p"
  using assms unfolding winning_region_def by blast

lemma (in vmc_path) paths_stay_in_winning_region:
  assumes \<sigma>': "strategy p \<sigma>'" "winning_strategy p \<sigma>' v0"
    and \<sigma>: "\<And>v. v \<in> winning_region p \<Longrightarrow> \<sigma>' v = \<sigma> v"
  shows "lset P \<subseteq> winning_region p"
proof
  fix x assume "x \<in> lset P"
  thus "x \<in> winning_region p" using assms vmc_path
  proof (induct arbitrary: v0 rule: llist_set_induct)
    case (find P v0)
    interpret vmc_path G P v0 p \<sigma> using find.prems(4) .
    show ?case using P_v0 \<sigma>'(1) find.prems(2) v0_V unfolding winning_region_def by blast
  next
    case (step P x v0)
    interpret vmc_path G P v0 p \<sigma> using step.prems(4) .
    show ?case proof (cases)
      assume "lnull (ltl P)"
      thus ?thesis using P_lnull_ltl_LCons step.hyps(2) by auto
    next
      assume "\<not>lnull (ltl P)"
      then interpret vmc_path_no_deadend G P v0 p \<sigma> using P_no_deadend_v0 by unfold_locales
      have "winning_strategy p \<sigma>' w0" proof (cases)
        assume "v0 \<in> VV p"
        hence "winning_strategy p \<sigma>' (\<sigma>' v0)"
          using strategy_extends_VVp local.step(4) step.prems(2) v0_no_deadend by blast
        moreover have "\<sigma> v0 = w0" using v0_conforms `v0 \<in> VV p` by blast
        moreover have "\<sigma>' v0 = \<sigma> v0"
          using \<sigma> assms(1) step.prems(2) v0_V unfolding winning_region_def by blast
        ultimately show ?thesis by simp
      next
        assume "v0 \<notin> VV p"
        thus ?thesis using v0_V strategy_extends_VVpstar step(4) step.prems(2) by simp
      qed
      thus ?thesis using step.hyps(3) step(4) \<sigma> vmc_path_ltl by blast
    qed
  qed
qed


subsection {* Updates *}

lemma winning_region_in_V [simp]: "winning_region p \<subseteq> V" unfolding winning_region_def by blast

lemma winning_strategy_updates:
  assumes \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
    and v: "v \<notin> winning_region p" "v\<rightarrow>w"
  shows "winning_strategy p (\<sigma>(v := w)) v0"
proof (rule winning_strategyI)
  fix P assume "vmc_path G P v0 p (\<sigma>(v := w))"
  then interpret vmc_path G P v0 p "\<sigma>(v := w)" .
  have "\<And>v'. v' \<in> winning_region p \<Longrightarrow> \<sigma> v' = (\<sigma>(v := w)) v'" using v by auto
  hence "v \<notin> lset P" using v paths_stay_in_winning_region \<sigma> unfolding winning_region_def by blast
  hence "path_conforms_with_strategy p P \<sigma>"
    using P_conforms path_conforms_with_strategy_irrelevant' by blast
  thus "winning_path p P" using conforms_to_another_strategy \<sigma>(2) winning_strategy_def by blast
qed

end -- "context ParityGame"

end
