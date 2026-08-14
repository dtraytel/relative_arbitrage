section \<open>Auxiliary results behind the statement\<close>

text \<open>Not part of the document: the individual clauses, the two class
  inclusions, and the assembled theorem in terms of the internal value
  function.  The statement theory restates the last of these for the paper's
  own value function.\<close>

theory Statement_Auxiliary
  imports
    "Relative_Arbitrage.Value_Function_Uniqueness"
    "Relative_Arbitrage.Exit_Class_Infinite"
    "Relative_Arbitrage.Exit_Class_Marginals"
begin

theorem paper_value_function_agrees:
  fixes K :: "(real^'n::finite) set"
  assumes "closed K" and "0 \<le> L"
  shows "iexit_val k L K x = xval k L K x"
  using assms by (rule iexit_val_eq_xval)

theorem paper_class_marginal:
  fixes P :: "('n::finite pairpath) measure"
  assumes "P \<in> iexit_class k L x" and "0 \<le> L"
  shows "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t)) \<in> xclass k L x"
  using assms by (rule iexit_class_marginal_in_xclass)

theorem paper_class_lift:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes "Q \<in> xclass k L x" and "0 \<le> L"
  shows "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * L) w t)) \<in> iexit_class k L x"
  using assms by (rule xclass_lift_in_iexit_class)

theorem convex_sets_are_expandable:
  fixes K :: "(real^'n::finite) set"
  assumes "convex K" and "compact K" and "interior K \<noteq> {}"
  shows "expandable K"
  by (rule convex_expandable[OF assms(2,1,3)])

theorem clause_0_finite:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
    and "K \<subseteq> cball 0 rK"
  shows "iexit_val k L K x
      \<le> ennreal ((rK * rK - x \<bullet> x) / real (CARD('n) - k))"
  by (rule iexit_val_le_ball_bound
        [OF assms(1,2) compact_imp_closed[OF assms(3)] assms(4)])

theorem clause_0_not_infinite:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
  shows "iexit_val k L K x \<noteq> \<top>"
  by (rule iexit_val_neq_top[OF assms])

theorem clause_1_upper_semicontinuous:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
    and "enn2real (iexit_val k L K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (iexit_val k L K y) < c"
  by (rule iexit_val_real_usc[OF assms])

theorem clause_2_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (iexit_val k L K z))"
  by (rule iexit_val_visc_subsol[OF assms])

theorem clause_2_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "1 \<le> k" and "compact K"
  shows "visc_supersol_env k L K (interior K)
      (lsc_envK K (\<lambda>u. enn2real (iexit_val k L K u)))"
  by (rule iexit_val_supersol_lsc_K[OF assms])

theorem clause_3_boundary_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "compact K"
  shows "visc_subsol_env k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (iexit_val k L K x)})
      (\<lambda>z. enn2real (iexit_val k L K z))"
  by (rule iexit_val_subsol_bc[OF assms])

theorem clause_3_boundary_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes "k < CARD('n)" and "1 \<le> L" and "1 \<le> k" and "compact K"
  shows "visc_supersol_env k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (iexit_val k L K z)))"
  by (rule iexit_val_supersol_bc_K[OF assms])

theorem clause_4_uniqueness:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes "k < CARD('n)" and "1 \<le> L" and "1 \<le> k"
    and "compact K" and "K \<noteq> {}" and "expandable K"
    and "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
           \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and "visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and "visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
           (lsc_envK K u)"
    and "x \<in> K"
  shows "u x = enn2real (iexit_val k L K x)"
  by (rule iexit_val_uniqueness_K[OF assms])

theorem theorem_1_1_iexit:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
  defines "v \<equiv> (\<lambda>z. enn2real (iexit_val k L K z))"
  shows "(\<exists>B. \<forall>y. \<bar>v y\<bar> \<le> B)
         \<comment> \<open>clause (0): finiteness.  Read through \<^const>\<open>enn2real\<close>, so this also
             says the value is finite; \<open>iexit_val\<close> itself is an \<^typ>\<open>ennreal\<close>
             and on a ball is bounded by the closed form of Example 3.1.\<close>
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
         \<comment> \<open>clause (1): upper semicontinuity.\<close>
       \<and> visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
         \<comment> \<open>clause (2), subsolution half, together with clause (3) for the
             subsolution: the touching set is the interior together with the
             boundary points where \<open>v\<close> is positive.\<close>
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0})
           (lsc_envK K v)
         \<comment> \<open>clause (2), supersolution half, with clause (3) for the
             supersolution.  Note the asymmetry Definition 3.1 itself has: the
             subsolution property is asked of \<open>v\<close>, the supersolution property of
             its lower envelope.  The paper's standing \<open>1 \<le> L\<close> is assumed; \<open>L = 1\<close>
             is not excluded, though Case 1 of Section 3 does not reach it as
             written --- it perturbs eigenvalues into the empty interval \<open>(1,L)\<close>
             --- and an exact-rotation covariance field is used instead.\<close>
       \<and> (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x))
         \<comment> \<open>clause (4): uniqueness.  The competitor is quantified over inside
             the statement, so the whole of Theorem 1.1 is one formula.  Every
             hypothesis on it is about \<open>K\<close> alone --- semicontinuity and
             boundedness are demanded only at and between points of \<open>K\<close>, and the
             envelope is the paper's \<^const>\<open>lsc_envK\<close>.  Continuity is not
             assumed, and is not part of Theorem 1.1; boundedness is, sitting in
             Definition 3.1.\<close>"
proof -
  have bnd: "\<exists>B. \<forall>y. \<bar>v y\<bar> \<le> B"
  proof -
    obtain rK :: real where r0: "0 \<le> rK" and KB: "K \<subseteq> cball 0 rK"
      using compact_cball_bound[OF cK] by blast
    show ?thesis
      unfolding v_def
      by (intro exI[of _ "rK * rK / real (CARD('n) - k)"] allI)
         (rule iexit_val_real_bounded[OF kn L1 cK KB r0])
  qed
  have usc: "\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c)"
    unfolding v_def
    by (intro allI impI clause_1_upper_semicontinuous[OF kn L1 cK])
  have sub: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def
    by (rule visc_subsol_env_imp_env2
          [OF clause_3_boundary_subsolution[OF kn L1 cK]])
  have sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
    unfolding v_def
    by (rule visc_supersol_env_imp_env2
          [OF clause_3_boundary_supersolution[OF kn L1 k1 cK]])
  have uniq: "\<forall>x\<in>K. u x = v x"
    if "\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c)"
      and "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd"
      and "visc_subsol_env2 k L K
             (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
      and "visc_supersol_env2 k L K
             (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
             (lsc_envK K u)"
    for u :: "real^'n \<Rightarrow> real" and Bd
    unfolding v_def
    using that
    by (intro ballI clause_4_uniqueness[OF kn L1 k1 cK neK expK]) blast+
  from bnd usc sub sup uniq show ?thesis by blast
qed

theorem example_3_1_iexit:
  fixes r :: real and x :: "real^'n::finite"
  assumes "1 \<le> k" and "k < CARD('n)" and "1 \<le> L" and "0 < r"
  shows "enn2real (iexit_val k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  by (rule example_3_1_uncapped[OF assms])

end
