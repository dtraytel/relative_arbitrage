section \<open>Theorem 1.1, assembled\<close>

(*<*)
theory Theorem_1_1
  imports
    Exit_Class_Marginals Value_Function_Uniqueness
begin
(*>*)

text \<open>The last theory of the session.  It states the five clauses of Theorem 1.1
  of \<^cite>\<open>LaiShkolnikovSoner\<close> for the paper's own objects --- the value
  function \<^const>\<open>xval\<close> of Eq. (1.6) over the class \<^const>\<open>xclass\<close> of
  Eq. (1.7) --- with the paper's hypotheses: existence (clauses (0)--(3)) for
  every compact \<open>K\<close>, uniqueness (clause (4)) under the additional
  expandability hypothesis.  The statement session restates the conjunction.\<close>

text \<open>The paper's value function of Eq. (1.6), over the paper's class of Eq. (1.7), is
  the internal \<^const>\<open>iexit_val\<close> on every closed \<open>K\<close>.  Everything below is
  stated for \<^const>\<open>xval\<close> itself.\<close>

lemma xval_eq_iexit_val:
  fixes K :: "(real^'n::finite) set"
  assumes "closed K" and "1 \<le> L"
  shows "xval k L K = iexit_val k L K"
  using iexit_val_eq_xval[OF assms(1)] assms(2) by (intro ext) simp

subsection \<open>The five clauses\<close>

text \<open>Clauses (0)--(3) hold for every compact \<open>K\<close>; only clause (4) needs the
  expandability hypothesis, as in the paper.\<close>

theorem xval_bounded:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
  shows "\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B"
proof -
  obtain rK :: real where KB: "K \<subseteq> cball 0 rK"
    using compact_cball_bound[OF cK] by blast
  show ?thesis
  proof (intro exI[of _ "rK * rK / real (CARD('n) - k)"] allI)
    fix y
    have "iexit_val k L K y \<le> ennreal ((rK * rK - y \<bullet> y) / real (CARD('n) - k))"
      unfolding iexit_val_eq_icovariation_val
      by (rule icovariation_val_le_ball_bound[OF closed_sconstraint sconstraint_convex
          mat_1_rate_in_sconstraint[OF L1] sconstraint_trace_bounds[OF kn order_trans[OF zero_le_one L1]]
          compact_imp_closed[OF cK] KB])
    also have "\<dots> \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (intro ennreal_leI divide_right_mono) auto
    finally show "xval k L K y \<le> ennreal (rK * rK / real (CARD('n) - k))"
      by (simp add: xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1])
  qed
qed

theorem xval_usc:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
    and lt: "enn2real (xval k L K z) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (xval k L K y) < c"
proof -
  have nk: "0 < real (CARD('n) - k)" using kn by simp
  have lt': "enn2real (icovariation_val (sconstraint k L) K z) < c"
    using lt by (simp add: xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1] iexit_val_eq_icovariation_val)
  have "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (icovariation_val (sconstraint k L) K y) < c"
    by (rule icovariation_val_real_usc[OF closed_sconstraint sconstraint_convex mat_1_rate_in_sconstraint[OF L1]
        sconstraint_bounds[OF order_trans[OF zero_le_one L1]] nk sconstraint_trace_ge[OF kn] cK lt'])
  then show ?thesis
    by (simp add: xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1] iexit_val_eq_icovariation_val)
qed

theorem xval_subsolution:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and cK: "compact K"
  shows "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < enn2real (xval k L K x)})
      (\<lambda>z. enn2real (xval k L K z))"
  unfolding xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1]
  by (rule visc_subsol_env_imp_env2[OF iexit_val_subsol_bc[OF kn L1 cK]])

theorem xval_supersolution:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  shows "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K.
         lsc_envK K (\<lambda>z. enn2real (xval k L K z)) x < 0})
      (lsc_envK K (\<lambda>z. enn2real (xval k L K z)))"
  unfolding xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1]
  by (rule visc_supersol_env_imp_env2[OF iexit_val_supersol_bc_K[OF kn L1 k1 cK]])

theorem xval_unique:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and cK: "compact K" and expK: "expandable K"
    and usc: "\<And>c z. z \<in> K \<Longrightarrow> u z < c \<Longrightarrow>
           \<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c"
    and bd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sup: "visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
           (lsc_envK K u)"
    and x: "x \<in> K"
  shows "u x = enn2real (xval k L K x)"
proof -
  have neK: "K \<noteq> {}" using x by blast
  show ?thesis
    unfolding xval_eq_iexit_val[OF compact_imp_closed[OF cK] L1]
    by (rule iexit_val_uniqueness_K[OF kn L1 k1 cK neK expK usc bd sub sup x])
qed

subsection \<open>Theorem 1.1 as one formula\<close>

theorem theorem_1_1_assembled:
  fixes K :: "(real^'n::finite) set"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L" and k1: "1 \<le> k" and cK: "compact K"
  defines "v \<equiv> (\<lambda>z. enn2real (xval k L K z))"
  shows "(\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B)
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
       \<and> visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
       \<and> visc_supersol_env2 k L K
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)
       \<and> (expandable K \<longrightarrow>
          (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_env2 k L K
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x)))"
proof (intro conjI impI allI ballI)
  show "\<exists>B :: real. \<forall>y. xval k L K y \<le> ennreal B"
    by (rule xval_bounded[OF kn L1 cK])
next
  fix c z assume "v z < c"
  then show "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c"
    unfolding v_def by (rule xval_usc[OF kn L1 cK])
next
  show "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < v x}) v"
    unfolding v_def by (rule xval_subsolution[OF kn L1 cK])
next
  show "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)"
    unfolding v_def by (rule xval_supersolution[OF kn L1 k1 cK])
next
  fix u :: "real^'n \<Rightarrow> real" and Bd x
  assume expK: "expandable K"
    and usc: "\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c)"
    and bd: "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd"
    and sub: "visc_subsol_env2 k L K (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
    and x: "x \<in> K"
  show "u x = v x"
    unfolding v_def
    by (rule xval_unique[OF kn L1 k1 cK expK _ _ sub sup x])
       (use usc bd in blast)+
qed

subsection \<open>Theorem 1.1 for an abstract constraint set\<close>

text \<open>The same five clauses for the value function \<^const>\<open>xcovariation_val\<close> of
  any set \<open>S\<close> of covariation rates with the structure the proof reads: closed,
  convex, bounded by \<open>B\<close>, of positive semidefinite matrices with diagonal bound
  \<open>D\<close> and trace at least \<open>\<theta> > 0\<close>, invariant under orthogonal conjugation, and
  containing the sphere-tangential rates \<open>I - u u\<^sup>T\<close>; the operator is
  \<^const>\<open>covariation_op\<close> \<open>S\<close>, with envelopes \<^const>\<open>covariation_op_lsc\<close> and
  \<^const>\<open>covariation_op_usc\<close>.  At \<open>S = sconstraint k L\<close> these are the
  paper's objects (\<open>xval_eq_xcovariation_val\<close>, \<open>ell_op_lsc_eq_covariation_op_lsc\<close>,
  \<open>ell_op_usc_eq_covariation_op_usc\<close>).\<close>

theorem covariation_theorem_1_1:
  fixes K :: "(real^'n::finite) set" and S :: "(real^'n^'n) set"
  assumes B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S" and Spsd: "\<And>a. a \<in> S \<Longrightarrow> psd a"
    and rot: "\<And>R b. orthogonal_matrix R \<Longrightarrow> b \<in> S \<Longrightarrow> R ** b ** transpose R \<in> S"
    and tan1: "\<And>u :: real^'n. norm u \<le> 1 \<Longrightarrow>
      tanpU (mat 1) u ** transpose (tanpU (mat 1) u) \<in> S"
    and n2: "2 \<le> CARD('n)"
    and th0: "0 < \<theta>" and th: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> \<theta> \<le> trace a"
    and cK: "compact K"
  defines "v \<equiv> (\<lambda>z. enn2real (xcovariation_val S K z))"
  shows "(\<exists>Bv :: real. \<forall>y. xcovariation_val S K y \<le> ennreal Bv)
       \<and> (\<forall>c z. v z < c \<longrightarrow> (\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> v y < c))
       \<and> visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
           (interior K \<union> {x \<in> K - interior K. 0 < v x}) v
       \<and> visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
           (interior K \<union> {x \<in> K - interior K. lsc_envK K v x < 0}) (lsc_envK K v)
       \<and> (expandable K \<longrightarrow>
          (\<forall>u :: real^'n \<Rightarrow> real. \<forall>Bd.
            (\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow>
               (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c))
            \<longrightarrow> (\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd)
            \<longrightarrow> visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
                 (interior K \<union> {x \<in> K - interior K. 0 < u x}) u
            \<longrightarrow> visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
                 (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0})
                 (lsc_envK K u)
            \<longrightarrow> (\<forall>x\<in>K. u x = v x)))"
proof -
  have Kc: "closed K" by (rule compact_imp_closed[OF cK])
  have SST: "tanpU (mat 1) 0 ** transpose (tanpU (mat 1) (0 :: real^'n)) \<in> S"
    by (rule tan1) simp
  have Dent: "\<bar>a $ i $ j\<bar> \<le> B" if a: "a \<in> S" for a :: "real^'n^'n" and i j
  proof -
    have "\<bar>a $ i $ j\<bar> \<le> norm (a $ i)" by (rule component_le_norm_cart)
    also have "\<dots> \<le> norm a" by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> B" by (rule B[OF a])
    finally show ?thesis .
  qed
  have eq: "icovariation_val S K x = xcovariation_val S K x" for x
    by (rule icovariation_val_eq_xcovariation_val[OF Sc Sv Spsd B0 Dent Kc])
  have v: "v = (\<lambda>z. enn2real (icovariation_val S K z))"
    unfolding v_def eq ..
  show ?thesis
    unfolding v eq[symmetric]
  proof (intro conjI impI allI ballI)
    obtain rK :: real where KB: "K \<subseteq> cball 0 rK"
      using compact_cball_bound[OF cK] by blast
    show "\<exists>Bv :: real. \<forall>y. icovariation_val S K y \<le> ennreal Bv"
    proof (intro exI[of _ "rK * rK / \<theta>"] allI)
      fix y
      have "icovariation_val S K y \<le> ennreal ((rK * rK - y \<bullet> y) / \<theta>)"
        by (rule icovariation_val_le_ball_bound[OF Sc Sv SST B0 B th0 th Kc KB])
      also have "\<dots> \<le> ennreal (rK * rK / \<theta>)"
        using th0 by (intro ennreal_leI divide_right_mono) auto
      finally show "icovariation_val S K y \<le> ennreal (rK * rK / \<theta>)" .
    qed
  next
    fix c z assume lt: "enn2real (icovariation_val S K z) < c"
    show "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> enn2real (icovariation_val S K y) < c"
      by (rule icovariation_val_real_usc[OF Sc Sv SST B0 B D0 D th0 th cK lt])
  next
    have "visc_subsol_gen test_fun_at (\<lambda>_. principal K) (covariation_op S)
        (interior K \<union> {x \<in> K - interior K. 0 < enn2real (icovariation_val S K x)})
        (\<lambda>z. enn2real (icovariation_val S K z))"
      by (rule icovariation_val_subsol_bc[OF B0 B D0 D Sc Sv SST Spsd th0 th cK])
    then have "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op S)
        (interior K \<union> {x \<in> K - interior K. 0 < enn2real (icovariation_val S K x)})
        (\<lambda>z. enn2real (icovariation_val S K z))"
      by (rule visc_subsol_gen_test_mono) (rule test_fun_C2_imp_test_fun_at)
    then show "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
        (interior K \<union> {x \<in> K - interior K. 0 < enn2real (icovariation_val S K x)})
        (\<lambda>z. enn2real (icovariation_val S K z))"
      by (rule visc_subsol_gen_mono) (rule covariation_op_lsc_le)
  next
    have "visc_supersol_gen test_fun_at (\<lambda>_. principal K) (covariation_op_usc S)
        (interior K \<union> {x \<in> K - interior K.
           lsc_envK K (\<lambda>z. enn2real (icovariation_val S K z)) x < 0})
        (lsc_envK K (\<lambda>z. enn2real (icovariation_val S K z)))"
      by (rule icovariation_val_supersol_bc_K[OF B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th cK])
    then show "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
        (interior K \<union> {x \<in> K - interior K.
           lsc_envK K (\<lambda>z. enn2real (icovariation_val S K z)) x < 0})
        (lsc_envK K (\<lambda>z. enn2real (icovariation_val S K z)))"
      by (rule visc_supersol_gen_test_mono) (rule test_fun_C2_imp_test_fun_at)
  next
    fix u :: "real^'n \<Rightarrow> real" and Bd x
    assume expK: "expandable K"
      and usc: "\<forall>c z. z \<in> K \<longrightarrow> u z < c \<longrightarrow> (\<exists>e>0. \<forall>y\<in>K. dist z y < e \<longrightarrow> u y < c)"
      and bd: "\<forall>y\<in>K. \<bar>u y\<bar> \<le> Bd"
      and sub: "visc_subsol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_lsc S)
        (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
      and sup: "visc_supersol_gen test_fun_C2 (\<lambda>_. principal K) (covariation_op_usc S)
        (interior K \<union> {x \<in> K - interior K. lsc_envK K u x < 0}) (lsc_envK K u)"
      and x: "x \<in> K"
    have neK: "K \<noteq> {}" using x by blast
    show "u x = enn2real (icovariation_val S K x)"
      by (rule icovariation_val_uniqueness_K[OF B0 B D0 D Sc Sv Spsd rot tan1 n2 th0 th
            cK neK expK _ _ sub sup x])
        (use usc bd in blast)+
  qed
qed

subsection \<open>Example 3.1\<close>

theorem example_3_1_xval:
  fixes r :: real and x :: "real^'n::finite"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L" and r0: "0 < r"
  shows "enn2real (xval k L (cball 0 r) x)
      = max ((r * r - x \<bullet> x) / real (CARD('n) - k)) 0"
  unfolding xval_eq_iexit_val[OF closed_cball L1]
  by (rule example_3_1_uncapped[OF k1 kn L1 r0])

(*<*)
end
(*>*)
