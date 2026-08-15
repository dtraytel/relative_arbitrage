section \<open>Theorem 4.2(a) via the Crandall-Ishii jet machinery\<close>

(*<*)
theory Comparison_Principle
  imports "Alexandrov_Sup_Convolution.Sup_Convolution" Operator_Envelope_Continuity
begin

(*>*)
text \<open>@{theory Alexandrov_Sup_Convolution.Sup_Convolution} develops the jet machinery
  independently of this development, directly over \<open>HOL-Analysis.Analysis\<close>.  This
  theory combines it with @{theory Relative_Arbitrage.Operator_Envelope_Continuity}
  to package the derivative facts into \<open>test_fun_at\<close> and discharge
  \<open>max_principle_boundary\<close>.\<close>

subsection \<open>A jet gives a test function\<close>

text \<open>For a symmetric \<open>H\<close> the quadratic
  \<open>\<phi> z = p \<cdot> (z - x) + ((z - x) \<cdot> (H *v (z - x)))/2\<close>
  with gradient field \<open>g z = p + H *v (z - x)\<close> is a test function at \<open>x\<close> in
  the sense of \<open>test_fun_at\<close>.\<close>

lemma jet_test_fun_at:
  fixes H :: "real^'n::finite^'n" and p x :: "real^'n"
  assumes symH: "transpose H = H"
  shows "test_fun_at (\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
      (\<lambda>z. p + H *v (z - x)) H x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose H = H" by (rule symH)
next
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
        has_derivative (\<lambda>h. (p + H *v (y - x)) \<bullet> h)) (at y)"
  proof (rule exI[of _ 1], intro conjI ballI)
    show "(0::real) < 1" by simp
    fix y :: "real^'n" assume "y \<in> ball x 1"
    show "((\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
        has_derivative (\<lambda>h. (p + H *v (y - x)) \<bullet> h)) (at y)"
      by (rule quadratic_test_derivative[OF symH])
  qed
next
  show "((\<lambda>z. p + H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at x)"
    by (rule quadratic_test_grad_derivative)
qed

text \<open>The form used downstream has the jet matrix arrive as an abstract
  symmetric bounded linear map, as produced throughout
  @{theory Alexandrov_Sup_Convolution.Sup_Convolution}.\<close>

subsection \<open>The jet interface to Definition 3.1(b)\<close>

text \<open>\<open>visc_supersol_env_imp_jet\<close> derives, from Definition 3.1(b), a quadratic
  test function that touches \<open>w\<close> from below on a ball, with the operator
  inequality read off over the upper envelope \<open>F\<^sup>*\<close>; boundedness of the
  quadratic on the compact \<open>K\<close> is proved, not assumed.  Its hypothesis is
  \<open>visc_supersol_env2\<close>, over the paper's own \<open>C\<^sup>2\<close> test functions ---
  the quadratic it builds is a polynomial, so nothing wider is ever needed.\<close>

lemma quad_bdd_above_on_bounded:
  fixes p yh :: "real^'n::finite" and M :: "real^'n^'n"
    and K :: "(real^'n) set"
  assumes Kb: "bounded K"
  obtains B where "\<And>z. z \<in> K \<Longrightarrow>
    p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2 \<le> B"
proof -
  obtain R where R: "\<And>z. z \<in> K \<Longrightarrow> norm z \<le> R"
    using Kb unfolding bounded_iff by blast
  define D where "D = R + norm yh"
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define N where "N = onorm ((*v) M)"
  have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
  have main: "p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2
      \<le> norm p * D + D * (N * D) / 2" if zK: "z \<in> K" for z
  proof -
    have nz: "norm z \<le> R" by (rule R[OF zK])
    have nzy: "norm (z - yh) \<le> D"
    proof -
      have "norm (z - yh) \<le> norm z + norm yh" by (rule norm_triangle_ineq4)
      then show ?thesis unfolding D_def using nz by linarith
    qed
    have D0: "0 \<le> D" using nzy by (meson norm_ge_zero order_trans)
    have t1: "p \<bullet> (z - yh) \<le> norm p * D"
    proof -
      have "p \<bullet> (z - yh) \<le> norm p * norm (z - yh)"
        by (rule norm_cauchy_schwarz)
      moreover have "norm p * norm (z - yh) \<le> norm p * D"
        by (rule mult_left_mono[OF nzy norm_ge_zero])
      ultimately show ?thesis by linarith
    qed
    have t2: "(z - yh) \<bullet> (M *v (z - yh)) \<le> D * (N * D)"
    proof -
      have a: "(z - yh) \<bullet> (M *v (z - yh))
          \<le> norm (z - yh) * norm (M *v (z - yh))"
        by (rule norm_cauchy_schwarz)
      have b: "norm (M *v (z - yh)) \<le> N * norm (z - yh)"
        unfolding N_def by (rule onorm[OF bl])
      have c: "N * norm (z - yh) \<le> N * D"
        by (rule mult_left_mono[OF nzy N0])
      have d: "norm (z - yh) * norm (M *v (z - yh))
          \<le> norm (z - yh) * (N * D)"
      proof (rule mult_left_mono)
        show "norm (M *v (z - yh)) \<le> N * D" using b c by linarith
        show "0 \<le> norm (z - yh)" by simp
      qed
      have e: "norm (z - yh) * (N * D) \<le> D * (N * D)"
        by (rule mult_right_mono[OF nzy]) (use N0 D0 in simp)
      show ?thesis using a d e by linarith
    qed
    show ?thesis using t1 t2 by linarith
  qed
  show ?thesis by (rule that) (use main in blast)
qed

section \<open>Definition 3.1 with genuine \<open>C\<^sup>2\<close> test functions\<close>

text \<open>\<^const>\<open>test_fun_at\<close> asks only that \<open>\<phi>\<close> be differentiable near \<open>x\<close> with
  gradient field \<open>g\<close>, and that \<open>g\<close> be differentiable at \<open>x\<close>; away from \<open>x\<close> it
  constrains \<open>\<phi>\<close> not at all.  Definition 3.1 quantifies over \<open>\<phi> \<in> C\<^sup>2(\<real>\<^sup>n)\<close>,
  a strictly smaller class.  For the assertions that the value function is a
  sub- or supersolution the larger class is the stronger statement, so nothing
  is lost there; but the uniqueness clause \<^emph>\<open>assumes\<close> the property of a
  competitor, and there the larger class would make the hypothesis stronger
  than the paper's and the theorem correspondingly weaker.  So the class is
  spelled out here: a gradient field defined everywhere, together with a
  \<^emph>\<open>continuous\<close> symmetric Hessian field.\<close>

definition test_fun_C2 ::
  "(real^'n::finite \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool"
  where
  "test_fun_C2 \<phi> g H x \<longleftrightarrow>
     (\<exists>G. (\<forall>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)) \<and>
          (\<forall>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)) \<and>
          (\<forall>y. transpose (G y) = G y) \<and>
          continuous_on UNIV G \<and> G x = H)"

lemma test_fun_C2_imp_test_fun_at:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real"
  assumes "test_fun_C2 \<phi> g H x"
  shows "test_fun_at \<phi> g H x"
proof -
  obtain G where G: "\<And>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    "\<And>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)"
    "\<And>y. transpose (G y) = G y" "G x = H"
    using assms unfolding test_fun_C2_def by blast
  show ?thesis
    unfolding test_fun_at_def
  proof (intro conjI)
    show "transpose H = H" using G(3)[of x] G(4) by simp
    show "\<exists>e>0. \<forall>y \<in> ball x e. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
      by (intro exI[of _ 1] conjI ballI) (auto simp: G(1))
    show "(g has_derivative (\<lambda>h. H *v h)) (at x)" using G(2)[of x] G(4) by simp
  qed
qed

text \<open>The affine gradient field of a quadratic has the same derivative at every
  point, not just at the base point, which is what a Hessian \<^emph>\<open>field\<close> needs.\<close>

lemma quadratic_grad_derivative_at:
  fixes H :: "real^'n::finite^'n" and p x y :: "real^'n"
  shows "((\<lambda>z. p + H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at y)"
proof -
  have blH: "bounded_linear ((*v) H)" by (rule matrix_vector_mul_bounded_linear)
  have shift: "((\<lambda>z::real^'n. z - x) has_derivative (\<lambda>h. h)) (at y)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>z. H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at y)"
    using bounded_linear.has_derivative[OF blH shift] by simp
  then show ?thesis by (auto intro!: derivative_eq_intros)
qed

text \<open>The three functions the comparison proof ever hands to the paper's
  hypothesis: the quadratic 2-jet, a constant, and a quartic shift of either.\<close>

lemma jet_test_fun_C2:
  fixes H :: "real^'n::finite^'n" and p x :: "real^'n"
  assumes symH: "transpose H = H"
  shows "test_fun_C2 (\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
      (\<lambda>z. p + H *v (z - x)) H x"
  unfolding test_fun_C2_def
proof (intro exI[of _ "\<lambda>_. H"] conjI allI)
  fix y :: "real^'n"
  show "((\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (H *v (z - x)))/2)
      has_derivative (\<lambda>h. (p + H *v (y - x)) \<bullet> h)) (at y)"
    by (rule quadratic_test_derivative[OF symH])
next
  fix y :: "real^'n"
  show "((\<lambda>z. p + H *v (z - x)) has_derivative (\<lambda>h. H *v h)) (at y)"
    by (rule quadratic_grad_derivative_at)
qed (use symH in \<open>auto intro: continuous_on_const\<close>)

lemma test_fun_C2_const:
  fixes x :: "real^'n::finite" and C :: real
  shows "test_fun_C2 (\<lambda>y. C) (\<lambda>y. 0) 0 x"
  unfolding test_fun_C2_def
proof (intro exI[of _ "\<lambda>_. 0"] conjI allI)
  fix y :: "real^'n"
  have z1: "(\<lambda>h. (0 :: real^'n) \<bullet> h) = (\<lambda>h :: real^'n. 0)" by simp
  show "((\<lambda>y. C) has_derivative (\<lambda>h. (0 :: real^'n) \<bullet> h)) (at y)"
    unfolding z1 by (rule has_derivative_const)
next
  fix y :: "real^'n"
  have z2: "(\<lambda>h. (0 :: real^'n^'n) *v h) = (\<lambda>h :: real^'n. 0)"
    by (simp add: matrix_vector_mult_def vec_eq_iff fun_eq_iff)
  show "((\<lambda>y :: real^'n. 0 :: real^'n) has_derivative
      (\<lambda>h. (0 :: real^'n^'n) *v h)) (at y)"
    unfolding z2 by (rule has_derivative_const)
qed (auto simp: transpose_def vec_eq_iff)

lemma test_fun_C2_add_const:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and c :: real
  assumes tf: "test_fun_C2 \<phi> g H x"
  shows "test_fun_C2 (\<lambda>z. c + \<phi> z) g H x"
proof -
  obtain G where G: "\<And>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    "\<And>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)"
    "\<And>y. transpose (G y) = G y" "continuous_on UNIV G" "G x = H"
    using tf unfolding test_fun_C2_def by blast
  have "((\<lambda>z. c + \<phi> z) has_derivative (\<lambda>h. g y \<bullet> h)) (at y)" for y
    using G(1)[of y] by (auto intro!: derivative_eq_intros)
  then show ?thesis
    unfolding test_fun_C2_def using G(2,3,4,5) by blast
qed

lemma op_matvec: "outer_prod u u *v h = (u \<bullet> h) *\<^sub>R (u :: real^'n::finite)"
  by (simp add: outer_prod_def matrix_vector_mult_def vec_eq_iff inner_vec_def
      sum_distrib_left mult.assoc mult.commute mult.left_commute)

lemma op_transpose: "transpose (outer_prod u u) = outer_prod (u :: real^'n::finite) u"
  by (simp add: outer_prod_def transpose_def vec_eq_iff mult.commute)

lemma op_continuous:
  "continuous_on UNIV (\<lambda>y :: real^'n::finite. outer_prod (y - x) (y - x))"
  unfolding outer_prod_def
  by (intro continuous_on_vec_lambda continuous_intros)

text \<open>The Hessian field of the quartic \<open>C|z-x|\<^sup>4\<close>, which is what
  \<^const>\<open>test_fun_at\<close> never had to record.\<close>

lemma quartic_grad_derivative:
  fixes x y :: "real^'n::finite" and C :: real
  shows "((\<lambda>z. (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) has_derivative
      (\<lambda>h. ((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h)) (at y)"
proof -
  have d: "((\<lambda>z. (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) has_derivative
      (\<lambda>h. (4 * C * (2 * ((y - x) \<bullet> h))) *\<^sub>R (y - x)
           + (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h)) (at y)"
    by (auto intro!: derivative_eq_intros simp: inner_commute)
  have eq: "(\<lambda>h. (4 * C * (2 * ((y - x) \<bullet> h))) *\<^sub>R (y - x)
           + (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h)
      = (\<lambda>h. ((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h)"
  proof (rule ext)
    fix h :: "real^'n"
    have "((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h
        = (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (mat 1 *v h)
          + (8 * C) *\<^sub>R (outer_prod (y - x) (y - x) *v h)"
      by (simp add: matrix_vector_mult_add_rdistrib
          scaleR_matrix_vector_assoc[symmetric])
    also have "\<dots> = (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h
          + (8 * C) *\<^sub>R (((y - x) \<bullet> h) *\<^sub>R (y - x))"
      by (simp add: op_matvec)
    finally show "(4 * C * (2 * ((y - x) \<bullet> h))) *\<^sub>R (y - x)
           + (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R h
        = ((4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
            + (8 * C) *\<^sub>R outer_prod (y - x) (y - x)) *v h"
      by simp
  qed
  show ?thesis using d unfolding eq .
qed

lemma test_fun_C2_quartic_shift:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and C :: real
  assumes tf: "test_fun_C2 \<phi> g H x"
  shows "test_fun_C2 (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)
      (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) H x"
proof -
  obtain G where G: "\<And>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    "\<And>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)"
    "\<And>y. transpose (G y) = G y" "continuous_on UNIV G" "G x = H"
    using tf unfolding test_fun_C2_def by blast
  define Q where "Q = (\<lambda>y :: real^'n. (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R mat 1
      + (8 * C) *\<^sub>R outer_prod (y - x) (y - x))"
  have Qsym: "transpose (Q y) = Q y" for y
    unfolding Q_def
    by (simp add: transpose_add transpose_scalar op_transpose)
  have Qx: "Q x = 0"
    unfolding Q_def by (simp add: outer_prod_def vec_eq_iff)
  have Qcont: "continuous_on UNIV Q"
    unfolding Q_def by (intro continuous_intros op_continuous)
  show ?thesis
    unfolding test_fun_C2_def
  proof (intro exI[of _ "\<lambda>y. G y - Q y"] conjI allI)
    fix y :: "real^'n"
    have d2: "((\<lambda>z :: real^'n. C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))) (at y)"
      by (auto intro!: derivative_eq_intros simp: inner_commute)
    have d3: "((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. g y \<bullet> h
          - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))) (at y)"
      by (rule has_derivative_diff[OF G(1) d2])
    have d4: "(\<lambda>h. g y \<bullet> h
          - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))
        = (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)"
      by (rule ext) (simp only: quartic_coeff_assoc inner_scaleR_diff_eq)
    show "((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)) (at y)"
      using d3 unfolding d4 .
  next
    fix y :: "real^'n"
    have e1: "((\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))
        has_derivative (\<lambda>h. G y *v h - Q y *v h)) (at y)"
      unfolding Q_def
      by (rule has_derivative_diff[OF G(2) quartic_grad_derivative])
    have e2: "(\<lambda>h. G y *v h - Q y *v h) = (\<lambda>h. (G y - Q y) *v h)"
      by (rule ext) (simp add: matrix_vector_mult_diff_rdistrib)
    show "((\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))
        has_derivative (\<lambda>h. (G y - Q y) *v h)) (at y)"
      using e1 unfolding e2 .
  next
    fix y :: "real^'n"
    have "transpose (G y - Q y) = transpose (G y) - transpose (Q y)"
      by (simp add: transpose_def vec_eq_iff)
    also have "\<dots> = G y - Q y" by (simp add: G(3) Qsym)
    finally show "transpose (G y - Q y) = G y - Q y" .
  next
    show "continuous_on UNIV (\<lambda>y. G y - Q y)"
      by (intro continuous_intros G(4) Qcont)
  next
    show "G x - Q x = H" by (simp add: Qx G(5))
  qed
qed

text \<open>Definition 3.1 itself, now with the paper's own test-function class.\<close>

definition visc_subsol_env2 ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_env2 k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_C2 \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        ell_op_lsc k L (g x) H \<le> 1)"

definition visc_supersol_env2 ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_env2 k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_C2 \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

text \<open>Fewer test functions means a weaker condition, so everything proved in the
  \<^const>\<open>test_fun_at\<close> form still delivers Definition 3.1 as the paper states it.\<close>

section \<open>\<open>F\<close> reads only the symmetric part of \<open>M\<close>\<close>

text \<open>Definition 3.1 takes the envelopes of \<open>F\<close> over \<open>\<real>\<^sup>n \<times> \<S>\<^sup>n\<close>, the paper's
  symmetric matrices, whereas \<^const>\<open>ell_op_lsc\<close> and \<^const>\<open>ell_op_usc\<close> take them
  over \<open>\<real>\<^sup>n \<times> \<real>\<^sup>n\<^sup>\<times>\<^sup>n\<close>.  Nothing changes: the feasible matrices are psd, hence
  symmetric, so \<open>F\<close> factors through \<open>M \<mapsto> (M + M\<^sup>T)/2\<close>, and that map is a
  contraction fixing \<open>\<S>\<^sup>n\<close> --- so every ball around a symmetric \<open>M\<close> realises the
  same set of values as its symmetric part does.\<close>

lemma trace_transpose_eq:
  fixes N :: "real^'n::finite^'n"
  shows "trace (transpose N) = trace N"
  by (simp add: trace_def transpose_def)

text \<open>\<open>trace_mul_comm\<close> is \<open>trace_matrix_commute\<close> from
  @{theory Relative_Arbitrage.Operator_Envelopes}.\<close>

lemma trace_mult_sym_right:
  fixes M a :: "real^'n::finite^'n"
  assumes sa: "transpose a = a"
  shows "trace (M ** a) = trace (transpose M ** a)"
proof -
  have e1: "trace (transpose M ** a) = trace (a ** transpose M)"
    by (rule trace_matrix_commute)
  have e2: "a ** transpose M = transpose (M ** a)"
    by (simp add: matrix_transpose_mul sa)
  have e3: "trace (transpose (M ** a)) = trace (M ** a)"
    by (rule trace_transpose_eq)
  show ?thesis using e1 e2 e3 by simp
qed

lemma trace_add_eq:
  fixes A B :: "real^'n::finite^'n"
  shows "trace (A + B) = trace A + trace B"
  by (simp add: trace_def sum.distrib)

text \<open>\<open>matrix_mult_scaleR_left\<close> is \<open>scaleR_matrix_mult\<close> from
  @{theory Relative_Arbitrage.Curvature_Operator}.\<close>

lemma matrix_mult_add_left:
  fixes A B C :: "real^'n::finite^'n"
  shows "(A + B) ** C = A ** C + B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib algebra_simps)

definition sym_part :: "real^'n::finite^'n \<Rightarrow> real^'n^'n" where
  "sym_part M = (1/2) *\<^sub>R (M + transpose M)"

lemma sym_part_sym: "transpose (sym_part M) = sym_part (M :: real^'n::finite^'n)"
  by (simp add: sym_part_def transpose_def vec_eq_iff add.commute)

lemma sym_part_id: "transpose M = M \<Longrightarrow> sym_part (M :: real^'n::finite^'n) = M"
  by (simp add: sym_part_def scaleR_add_right vec_eq_iff)

lemma sym_part_diff:
  fixes A B :: "real^'n::finite^'n"
  shows "sym_part (A - B) = sym_part A - sym_part B"
  by (simp add: sym_part_def transpose_def vec_eq_iff algebra_simps)

theorem ell_op_sym_part:
  fixes M :: "real^'n::finite^'n"
  shows "ell_op k L p M = ell_op k L p (sym_part M)"
proof -
  have obj: "- trace (sym_part M ** a) / 2 = - trace (M ** a) / 2"
    if aF: "a \<in> feasible k L p" for a
  proof -
    have sa: "transpose a = a"
      using aF unfolding feasible_def psd_def by blast
    have "trace (sym_part M ** a) = (1/2) * trace ((M + transpose M) ** a)"
      unfolding sym_part_def by (simp add: scaleR_matrix_mult trace_scaleR)
    also have "\<dots> = (1/2) * (trace (M ** a) + trace (transpose M ** a))"
      by (simp add: matrix_mult_add_left trace_add_eq)
    also have "\<dots> = trace (M ** a)"
      using trace_mult_sym_right[OF sa, of M] by simp
    finally show ?thesis by simp
  qed
  have "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p
      = (\<lambda>a. - trace (sym_part M ** a) / 2) ` feasible k L p"
    using obj by (intro image_cong refl) simp
  then show ?thesis unfolding ell_op_def by simp
qed

lemma norm_transpose_eq:
  fixes P :: "real^'n::finite^'n"
  shows "norm (transpose P) = norm P"
proof -
  have "inner (transpose P) (transpose P) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. P$j$i * P$j$i)"
    by (simp add: inner_vec_def transpose_def)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. P$j$i * P$j$i)" by (rule sum.swap)
  also have "\<dots> = inner P P" by (simp add: inner_vec_def)
  finally show ?thesis by (simp add: norm_eq_sqrt_inner)
qed

lemma norm_sym_part_le:
  fixes P :: "real^'n::finite^'n"
  shows "norm (sym_part P) \<le> norm P"
proof -
  have "norm (sym_part P) = (1/2) * norm (P + transpose P)"
    unfolding sym_part_def by simp
  also have "\<dots> \<le> (1/2) * (norm P + norm (transpose P))"
    by (intro mult_left_mono norm_triangle_ineq) simp
  also have "\<dots> = norm P" by (simp add: norm_transpose_eq)
  finally show ?thesis .
qed

lemma ell_op_pair_sym_part:
  fixes M' :: "real^'n::finite^'n"
  shows "ell_op_pair k L (p', sym_part M') = ell_op_pair k L (p', M')"
  unfolding ell_op_pair_def by (simp add: ell_op_sym_part[symmetric])

lemma ell_op_image_sym:
  fixes M :: "real^'n::finite^'n"
  assumes symM: "transpose M = M" and e: "0 < e"
  shows "ell_op_pair k L ` ball (p, M) e
       = ell_op_pair k L ` {w \<in> ball (p, M) e. transpose (snd w) = snd w}"
proof
  show "ell_op_pair k L ` {w \<in> ball (p, M) e. transpose (snd w) = snd w}
      \<subseteq> ell_op_pair k L ` ball (p, M) e" by blast
next
  show "ell_op_pair k L ` ball (p, M) e
      \<subseteq> ell_op_pair k L ` {w \<in> ball (p, M) e. transpose (snd w) = snd w}"
  proof
    fix v assume "v \<in> ell_op_pair k L ` ball (p, M) e"
    then obtain w where w: "w \<in> ball (p, M) e" and v: "v = ell_op_pair k L w"
      by blast
    obtain p' M' where wpm: "w = (p', M')" by (cases w)
    have d: "dist (sym_part M') M \<le> dist M' M"
    proof -
      have "sym_part M' - M = sym_part (M' - M)"
        using sym_part_diff[of M' M] sym_part_id[OF symM] by simp
      then have "norm (sym_part M' - M) = norm (sym_part (M' - M))" by simp
      also have "\<dots> \<le> norm (M' - M)" by (rule norm_sym_part_le)
      finally show ?thesis by (simp add: dist_norm)
    qed
    have "dist (p', sym_part M') (p, M)
        = sqrt ((dist p' p)\<^sup>2 + (dist (sym_part M') M)\<^sup>2)"
      by (simp add: dist_Pair_Pair)
    also have "\<dots> \<le> sqrt ((dist p' p)\<^sup>2 + (dist M' M)\<^sup>2)"
      using d by (intro real_sqrt_le_mono add_left_mono power_mono) auto
    also have "\<dots> = dist w (p, M)" unfolding wpm by (simp add: dist_Pair_Pair)
    finally have dw: "dist (p', sym_part M') (p, M) \<le> dist w (p, M)" .
    have "dist w (p, M) < e" using w by (simp add: dist_commute)
    with dw have inb: "(p', sym_part M') \<in> ball (p, M) e"
      by (simp add: dist_commute)
    have "v = ell_op_pair k L (p', sym_part M')"
      unfolding v wpm by (rule ell_op_pair_sym_part[symmetric])
    moreover have "(p', sym_part M')
        \<in> {w \<in> ball (p, M) e. transpose (snd w) = snd w}"
      using inb by (simp add: sym_part_sym)
    ultimately show "v \<in> ell_op_pair k L
        ` {w \<in> ball (p, M) e. transpose (snd w) = snd w}" by blast
  qed
qed

theorem ell_op_lsc_eq_over_sym:
  fixes M :: "real^'n::finite^'n"
  assumes symM: "transpose M = M"
  shows "ell_op_lsc k L p M
       = (SUP e \<in> {0<..}. INF w \<in> {w \<in> ball (p, M) e. transpose (snd w) = snd w}.
            ell_op_pair k L w)"
  unfolding ell_op_lsc_def
proof (rule SUP_cong[OF refl])
  fix e :: real assume "e \<in> {0<..}"
  then have e: "0 < e" by simp
  show "(INF w \<in> ball (p, M) e. ell_op_pair k L w)
      = (INF w \<in> {w \<in> ball (p, M) e. transpose (snd w) = snd w}.
           ell_op_pair k L w)"
    by (rule arg_cong[where f = Inf]) (rule ell_op_image_sym[OF symM e])
qed

theorem ell_op_usc_eq_over_sym:
  fixes M :: "real^'n::finite^'n"
  assumes symM: "transpose M = M"
  shows "ell_op_usc k L p M
       = (INF e \<in> {0<..}. SUP w \<in> {w \<in> ball (p, M) e. transpose (snd w) = snd w}.
            ell_op_pair k L w)"
  unfolding ell_op_usc_def
proof (rule INF_cong[OF refl])
  fix e :: real assume "e \<in> {0<..}"
  then have e: "0 < e" by simp
  show "(SUP w \<in> ball (p, M) e. ell_op_pair k L w)
      = (SUP w \<in> {w \<in> ball (p, M) e. transpose (snd w) = snd w}.
           ell_op_pair k L w)"
    by (rule arg_cong[where f = Sup]) (rule ell_op_image_sym[OF symM e])
qed

lemma visc_subsol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "visc_subsol_env2 k L K \<Omega> f1"
  shows "visc_subsol_env2 k L K \<Omega> f2"
  unfolding visc_subsol_env2_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_C2 \<phi> g H x"
    and gl: "\<forall>y\<in>K. f2 y - \<phi> y \<le> f2 x - \<phi> x"
  have xK: "x \<in> K" using x OK by blast
  have "\<forall>y\<in>K. f1 y - \<phi> y \<le> f1 x - \<phi> x"
    using gl eq xK by (metis (no_types, lifting))
  then show "ell_op_lsc k L (g x) H \<le> 1"
    using h x tf unfolding visc_subsol_env2_def by blast
qed

lemma visc_supersol_env2_cong:
  fixes f1 f2 :: "real^'n::finite \<Rightarrow> real"
  assumes OK: "\<Omega> \<subseteq> K" and eq: "\<And>y. y \<in> K \<Longrightarrow> f1 y = f2 y"
    and h: "visc_supersol_env2 k L K \<Omega> f1"
  shows "visc_supersol_env2 k L K \<Omega> f2"
  unfolding visc_supersol_env2_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_C2 \<phi> g H x"
    and gl: "\<forall>y\<in>K. f2 x - \<phi> x \<le> f2 y - \<phi> y"
  have xK: "x \<in> K" using x OK by blast
  have "\<forall>y\<in>K. f1 x - \<phi> x \<le> f1 y - \<phi> y"
    using gl eq xK by (metis (no_types, lifting))
  then show "1 \<le> ell_op_usc k L (g x) H"
    using h x tf unfolding visc_supersol_env2_def by blast
qed

lemma visc_subsol_env2_mono:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_subsol_env2 k L K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_subsol_env2 k L K \<Omega>' u"
  using assms unfolding visc_subsol_env2_def by blast

lemma visc_supersol_env2_mono:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_supersol_env2 k L K \<Omega> u" and "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_supersol_env2 k L K \<Omega>' u"
  using assms unfolding visc_supersol_env2_def by blast

lemma visc_subsol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_subsol_env k L K \<Omega> u"
  shows "visc_subsol_env2 k L K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding visc_subsol_env_def visc_subsol_env2_def by blast

lemma visc_supersol_env_imp_env2:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes "visc_supersol_env k L K \<Omega> u"
  shows "visc_supersol_env2 k L K \<Omega> u"
  using assms test_fun_C2_imp_test_fun_at
  unfolding visc_supersol_env_def visc_supersol_env2_def by blast

text \<open>The two places where the paper-facing hypothesis is actually consumed:
  a local touching is deepened by a quartic into a global one over \<open>K\<close>.  The
  \<open>C\<^sup>2\<close> versions are the originals with @{thm [source] test_fun_C2_quartic_shift}
  in place of @{thm [source] test_fun_at_quartic_shift}; the quartic shift of a
  \<open>C\<^sup>2\<close> function is again \<open>C\<^sup>2\<close>, so nothing else moves.\<close>

theorem visc_supersol_env2_local:
  fixes K :: "(real^'n::finite) set" and w \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assumes sup: "visc_supersol_env2 k L K \<Omega> w"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_C2 \<phi> g H x"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> \<phi> y \<le> B\<phi>"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
  shows "1 \<le> ell_op_usc k L (g x) H"
proof -
  have r40: "0 < r ^ 4" using r0 by simp
  define C where "C = max 0 ((w x - \<phi> x - Bw + B\<phi>) / r ^ 4)"
  have C0: "0 \<le> C" unfolding C_def by simp
  have Cbig: "w x - \<phi> x - Bw + B\<phi> \<le> C * r ^ 4"
  proof -
    have "(w x - \<phi> x - Bw + B\<phi>) / r ^ 4 \<le> C" unfolding C_def by simp
    then have "(w x - \<phi> x - Bw + B\<phi>) / r ^ 4 * r ^ 4 \<le> C * r ^ 4"
      by (rule mult_right_mono) (use r40 in linarith)
    then show ?thesis using r40 by simp
  qed
  define \<psi> where "\<psi> = (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)"
  define gg where
    "gg = (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))"
  have tf': "test_fun_C2 \<psi> gg H x"
    unfolding \<psi>_def gg_def by (rule test_fun_C2_quartic_shift[OF tf])
  have ggx: "gg x = g x" unfolding gg_def by simp
  have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
  have glob: "w x - \<psi> x \<le> w y - \<psi> y" if yK: "y \<in> K" for y
  proof (cases "y \<in> ball x r")
    case True
    have nn: "0 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_nonneg_nonneg[OF C0]) simp
    show ?thesis using lm[OF True] nn unfolding \<psi>_def psix[unfolded \<psi>_def]
      by simp
  next
    case False
    then have dxy: "r \<le> dist x y" by simp
    have sq: "r\<^sup>2 \<le> (y - x) \<bullet> (y - x)"
    proof -
      have "r \<le> norm (y - x)"
        using dxy by (simp add: dist_norm norm_minus_commute)
      then have "r\<^sup>2 \<le> (norm (y - x))\<^sup>2" using r0 by (intro power_mono) auto
      then show ?thesis by (simp add: dot_square_norm)
    qed
    have q4: "r ^ 4 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
    proof -
      have "(r\<^sup>2)\<^sup>2 \<le> ((y - x) \<bullet> (y - x))\<^sup>2" using sq by (intro power_mono) auto
      then show ?thesis by (simp add: power_even_eq)
    qed
    have cq: "C * r ^ 4 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_left_mono[OF q4 C0])
    have lo: "Bw \<le> w y" by (rule wlo[OF yK])
    have hi: "\<phi> y \<le> B\<phi>" by (rule phi[OF yK])
    show ?thesis unfolding \<psi>_def using Cbig cq lo hi by simp
  qed
  have "1 \<le> ell_op_usc k L (gg x) H"
    using sup[unfolded visc_supersol_env2_def] x\<Omega> tf' glob by blast
  then show ?thesis unfolding ggx .
qed

theorem visc_subsol_env2_local:
  fixes K :: "(real^'n::finite) set" and u \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assumes sub: "visc_subsol_env2 k L K \<Omega> u"
    and x\<Omega>: "x \<in> \<Omega>"
    and tf: "test_fun_C2 \<phi> g H x"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and phi: "\<And>y. y \<in> K \<Longrightarrow> B\<phi> \<le> \<phi> y"
    and r0: "0 < r"
    and lm: "\<And>y. y \<in> ball x r \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
  shows "ell_op_lsc k L (g x) H \<le> 1"
proof -
  have r40: "0 < r ^ 4" using r0 by simp
  define C where "C = max 0 ((Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4)"
  have C0: "0 \<le> C" unfolding C_def by simp
  have Cbig: "Bu - B\<phi> - (u x - \<phi> x) \<le> C * r ^ 4"
  proof -
    have "(Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4 \<le> C" unfolding C_def by simp
    then have "(Bu - B\<phi> - (u x - \<phi> x)) / r ^ 4 * r ^ 4 \<le> C * r ^ 4"
      by (rule mult_right_mono) (use r40 in linarith)
    then show ?thesis using r40 by simp
  qed
  define \<psi> where "\<psi> = (\<lambda>z. \<phi> z - (- C) * ((z - x) \<bullet> (z - x))\<^sup>2)"
  define gg where
    "gg = (\<lambda>z. g z - (4 * (- C) * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))"
  have tf': "test_fun_C2 \<psi> gg H x"
    unfolding \<psi>_def gg_def by (rule test_fun_C2_quartic_shift[OF tf])
  have ggx: "gg x = g x" unfolding gg_def by simp
  have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
  have glob: "u y - \<psi> y \<le> u x - \<psi> x" if yK: "y \<in> K" for y
  proof (cases "y \<in> ball x r")
    case True
    have nn: "0 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_nonneg_nonneg[OF C0]) simp
    show ?thesis using lm[OF True] nn unfolding \<psi>_def psix[unfolded \<psi>_def]
      by simp
  next
    case False
    then have dxy: "r \<le> dist x y" by simp
    have sq: "r\<^sup>2 \<le> (y - x) \<bullet> (y - x)"
    proof -
      have "r \<le> norm (y - x)"
        using dxy by (simp add: dist_norm norm_minus_commute)
      then have "r\<^sup>2 \<le> (norm (y - x))\<^sup>2" using r0 by (intro power_mono) auto
      then show ?thesis by (simp add: dot_square_norm)
    qed
    have q4: "r ^ 4 \<le> ((y - x) \<bullet> (y - x))\<^sup>2"
    proof -
      have "(r\<^sup>2)\<^sup>2 \<le> ((y - x) \<bullet> (y - x))\<^sup>2" using sq by (intro power_mono) auto
      then show ?thesis by (simp add: power_even_eq)
    qed
    have cq: "C * r ^ 4 \<le> C * ((y - x) \<bullet> (y - x))\<^sup>2"
      by (rule mult_left_mono[OF q4 C0])
    have hi: "u y \<le> Bu" by (rule uhi[OF yK])
    have lo: "B\<phi> \<le> \<phi> y" by (rule phi[OF yK])
    show ?thesis unfolding \<psi>_def using Cbig cq hi lo by simp
  qed
  have "ell_op_lsc k L (gg x) H \<le> 1"
    using sub[unfolded visc_subsol_env2_def] x\<Omega> tf' glob by blast
  then show ?thesis unfolding ggx .
qed

definition supersol_jet ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "supersol_jet k L \<Omega> w \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

theorem visc_supersol_env_imp_jet:
  fixes K :: "(real^'n::finite) set" and w :: "real^'n \<Rightarrow> real"
  assumes sup: "visc_supersol_env2 k L K \<Omega> w"
    and Kb: "bounded K"
    and wlo: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
  shows "supersol_jet k L \<Omega> w"
  unfolding supersol_jet_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  obtain e0 where e00: "0 < e0"
    and lme: "\<And>y. y \<in> ball x e0 \<Longrightarrow> w x - \<phi> x \<le> w y - \<phi> y"
    using lm by blast
  have step: "1 \<le> ell_op_usc k L (g x) (H - \<delta> *\<^sub>R mat 1)"
    if d: "0 < \<delta>" for \<delta>
  proof -
    have symM: "transpose (H - \<delta> *\<^sub>R mat 1) = H - \<delta> *\<^sub>R mat 1"
      by (rule transpose_shift_diff[OF symH])
    obtain r where r0: "0 < r"
      and mino: "\<And>z. z \<in> ball x r \<Longrightarrow>
        \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    proof (rule test_fun_quadratic_minorates[OF tf d])
      fix rr :: real
      assume a1: "0 < rr" and a2: "\<And>z. z \<in> ball x rr \<Longrightarrow>
        \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
      show thesis by (rule that[OF a1 a2])
    qed
    define \<psi> where "\<psi> = (\<lambda>z. \<phi> x + (g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2))"
    define gg where "gg = (\<lambda>z. g x + (H - \<delta> *\<^sub>R mat 1) *v (z - x))"
    have tfp: "test_fun_C2 \<psi> gg (H - \<delta> *\<^sub>R mat 1) x"
      unfolding \<psi>_def gg_def
      by (rule test_fun_C2_add_const[OF jet_test_fun_C2[OF symM]])
    have ggx: "gg x = g x" unfolding gg_def by simp
    have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
    obtain B where B: "\<And>z. z \<in> K \<Longrightarrow>
      g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> B"
    proof (rule quad_bdd_above_on_bounded[OF Kb,
            where p = "g x" and yh = x and M = "H - \<delta> *\<^sub>R mat 1"])
      fix BB :: real
      assume "\<And>z. z \<in> K \<Longrightarrow>
        g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> BB"
      then show thesis by (rule that)
    qed
    have Bp: "\<And>z. z \<in> K \<Longrightarrow> \<psi> z \<le> \<phi> x + B"
      unfolding \<psi>_def using B by simp
    have r0': "0 < min r e0" using r0 e00 by simp
    have lm': "w x - \<psi> x \<le> w y - \<psi> y" if y: "y \<in> ball x (min r e0)" for y
    proof -
      have y1: "y \<in> ball x r" using y by simp
      have y2: "y \<in> ball x e0" using y by simp
      have "\<psi> y \<le> \<phi> y" unfolding \<psi>_def using mino[OF y1] by simp
      then show ?thesis using lme[OF y2] unfolding psix by simp
    qed
    have "1 \<le> ell_op_usc k L (gg x) (H - \<delta> *\<^sub>R mat 1)"
      by (rule visc_supersol_env2_local[OF sup x tfp wlo Bp r0' lm'])
    then show ?thesis unfolding ggx .
  qed
  define es where "es = (\<lambda>j :: nat. 1 / real (Suc j))"
  have es0: "0 < es j" for j unfolding es_def by simp
  have ge: "1 \<le> ell_op_usc k L (g x) (H - es j *\<^sub>R mat 1)" for j
    by (rule step[OF es0])
  have lim: "(\<lambda>j. (g x, H - es j *\<^sub>R mat 1)) \<longlonglongrightarrow> (g x, H)"
  proof -
    have "es \<longlonglongrightarrow> 0" unfolding es_def
      using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
    then have "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0 *\<^sub>R mat 1"
      by (rule tendsto_scaleR[OF _ tendsto_const])
    then have z: "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0" by simp
    have "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H - 0"
      by (rule tendsto_diff[OF tendsto_const z])
    then have m: "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H" by simp
    show ?thesis by (rule tendsto_Pair[OF tendsto_const m])
  qed
  show "1 \<le> ell_op_usc k L (g x) H"
    by (rule ell_op_usc_ge_one_limit[OF ge lim])
qed

lemma quad_bdd_below_on_bounded:
  fixes p yh :: "real^'n::finite" and M :: "real^'n^'n"
    and K :: "(real^'n) set"
  assumes Kb: "bounded K"
  obtains B where "\<And>z. z \<in> K \<Longrightarrow>
    B \<le> p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2"
proof -
  obtain B0 where B0: "\<And>z. z \<in> K \<Longrightarrow>
    (- p) \<bullet> (z - yh) + ((z - yh) \<bullet> ((- M) *v (z - yh))) / 2 \<le> B0"
  proof (rule quad_bdd_above_on_bounded[OF Kb,
          where p = "- p" and yh = yh and M = "- M"])
    fix BB :: real
    assume "\<And>z. z \<in> K \<Longrightarrow>
      (- p) \<bullet> (z - yh) + ((z - yh) \<bullet> ((- M) *v (z - yh))) / 2 \<le> BB"
    then show thesis by (rule that)
  qed
  have main: "- B0 \<le> p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2"
    if zK: "z \<in> K" for z
  proof -
    have mv: "(- M) *v (z - yh) = - (M *v (z - yh))"
    proof -
      have "(- M :: real^'n^'n) *v (z - yh) = (0 - M) *v (z - yh)" by simp
      also have "\<dots> = 0 *v (z - yh) - M *v (z - yh)"
        by (rule matrix_vector_mult_diff_rdistrib)
      also have "\<dots> = - (M *v (z - yh))" by simp
      finally show ?thesis .
    qed
    have "(- p) \<bullet> (z - yh) + ((z - yh) \<bullet> ((- M) *v (z - yh))) / 2
        = - (p \<bullet> (z - yh) + ((z - yh) \<bullet> (M *v (z - yh))) / 2)"
      unfolding mv by simp
    then show ?thesis using B0[OF zK] by linarith
  qed
  show ?thesis by (rule that) (use main in blast)
qed

text \<open>The subsolution counterpart of \<open>visc_supersol_env_imp_jet\<close> lands on the
  envelope-free notion, since \<open>F\<^sub>* = F\<close> everywhere (@{thm [source]
  ell_op_lsc_at_zero} at \<open>p = 0\<close>, @{thm [source] ell_op_lsc_off_zero}
  elsewhere); only the touching needs upgrading from global on \<open>K\<close> to local,
  via @{thm [source] visc_subsol_env_local}.\<close>

theorem visc_subsol_env_imp_visc_subsol:
  fixes K :: "(real^'n::finite) set" and u :: "real^'n \<Rightarrow> real"
  assumes sub: "visc_subsol_env2 k L K \<Omega> u"
    and Kb: "bounded K"
    and uhi: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
  shows "visc_subsol k L \<Omega> u"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  obtain e0 where e00: "0 < e0"
    and lme: "\<And>y. y \<in> ball x e0 \<Longrightarrow> u y - \<phi> y \<le> u x - \<phi> x"
    using lm by blast
  have step: "ell_op k L (g x) (H + \<delta> *\<^sub>R mat 1) \<le> 1" if d: "0 < \<delta>" for \<delta>
  proof -
    have symM: "transpose (H + \<delta> *\<^sub>R mat 1) = H + \<delta> *\<^sub>R mat 1"
      by (rule transpose_shift_add[OF symH])
    obtain r where r0: "0 < r"
      and majo: "\<And>z. z \<in> ball x r \<Longrightarrow>
        \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof (rule test_fun_quadratic_dominates[OF tf d])
      fix rr :: real
      assume a1: "0 < rr" and a2: "\<And>z. z \<in> ball x rr \<Longrightarrow>
        \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      show thesis by (rule that[OF a1 a2])
    qed
    define \<psi> where "\<psi> = (\<lambda>z. \<phi> x + (g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2))"
    define gg where "gg = (\<lambda>z. g x + (H + \<delta> *\<^sub>R mat 1) *v (z - x))"
    have tfp: "test_fun_C2 \<psi> gg (H + \<delta> *\<^sub>R mat 1) x"
      unfolding \<psi>_def gg_def
      by (rule test_fun_C2_add_const[OF jet_test_fun_C2[OF symM]])
    have ggx: "gg x = g x" unfolding gg_def by simp
    have psix: "\<psi> x = \<phi> x" unfolding \<psi>_def by simp
    obtain B where B: "\<And>z. z \<in> K \<Longrightarrow>
      B \<le> g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof (rule quad_bdd_below_on_bounded[OF Kb,
            where p = "g x" and yh = x and M = "H + \<delta> *\<^sub>R mat 1"])
      fix BB :: real
      assume "\<And>z. z \<in> K \<Longrightarrow>
        BB \<le> g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      then show thesis by (rule that)
    qed
    have Bp: "\<And>z. z \<in> K \<Longrightarrow> \<phi> x + B \<le> \<psi> z"
      unfolding \<psi>_def using B by simp
    have r0': "0 < min r e0" using r0 e00 by simp
    have lm': "u y - \<psi> y \<le> u x - \<psi> x" if y: "y \<in> ball x (min r e0)" for y
    proof -
      have y1: "y \<in> ball x r" using y by simp
      have y2: "y \<in> ball x e0" using y by simp
      have "\<phi> y \<le> \<psi> y" unfolding \<psi>_def using majo[OF y1] by simp
      then show ?thesis using lme[OF y2] unfolding psix by simp
    qed
    have lsc: "ell_op_lsc k L (gg x) (H + \<delta> *\<^sub>R mat 1) \<le> 1"
      by (rule visc_subsol_env2_local[OF sub x tfp uhi Bp r0' lm'])
    show ?thesis
    proof (cases "g x = 0")
      case True
      have "ell_op_lsc k L (0 :: real^'n) (H + \<delta> *\<^sub>R mat 1)
          = ereal (ell_op k L (0 :: real^'n) (H + \<delta> *\<^sub>R mat 1))"
        by (rule ell_op_lsc_at_zero[OF kk(1) kk(2) LL])
      then show ?thesis using lsc unfolding ggx True by simp
    next
      case False
      have "ell_op_lsc k L (g x) (H + \<delta> *\<^sub>R mat 1)
          = ereal (ell_op k L (g x) (H + \<delta> *\<^sub>R mat 1))"
        by (rule ell_op_lsc_off_zero[OF symM False LL kk(1) kk(2)])
      then show ?thesis using lsc unfolding ggx by simp
    qed
  qed
  show "ell_op k L (g x) H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0: "0 < e"
    have A0: "0 < real CARD('n) * L / 2" using LL by simp
    define \<delta> where "\<delta> = e / (real CARD('n) * L / 2)"
    have d0: "0 < \<delta>" unfolding \<delta>_def using e0 A0 by simp
    have ne: "feasible k L (g x) \<noteq> ({} :: (real^'n^'n) set)"
      by (rule feasible_nonempty[OF kk(1) kk(2) LL])
    have gap: "ell_op k L (g x) H
        \<le> ell_op k L (g x) (H + \<delta> *\<^sub>R mat 1) + mgap L H (H + \<delta> *\<^sub>R mat 1)"
      by (rule ell_op_M_gap[OF ne])
    have mg: "mgap L H (H + \<delta> *\<^sub>R mat 1) = \<delta> * real CARD('n) * L / 2"
      by (rule mgap_shift_id(1)[OF less_imp_le[OF d0]])
    have L0: "L \<noteq> 0" using LL by linarith
    have eq: "\<delta> * real CARD('n) * L / 2 = e"
      unfolding \<delta>_def using A0 L0 by (simp add: field_simps)
    have mg': "mgap L H (H + \<delta> *\<^sub>R mat 1) = e" using mg eq by simp
    show "ell_op k L (g x) H \<le> 1 + e"
      using gap step[OF d0] mg' by linarith
  qed
qed

lemma jet_test_fun_at_abstract:
  fixes X :: "(real^'n::finite) \<Rightarrow> (real^'n)" and p x :: "real^'n"
  assumes lin: "linear X" and sym: "\<And>v w. v \<bullet> X w = w \<bullet> X v"
  shows "test_fun_at
      (\<lambda>z. p \<bullet> (z - x) + ((z - x) \<bullet> (matrix X *v (z - x)))/2)
      (\<lambda>z. p + matrix X *v (z - x)) (matrix X) x"
  by (rule jet_test_fun_at[OF matrix_of_symmetric[OF lin sym]])

subsection \<open>The closing step of Theorem 4.2\<close>

text \<open>At the test point the gradient field of the jet test function is just
  \<open>p\<close>, which is what \<open>visc_subsol\<close> and \<open>supersol_jet\<close> feed to \<open>ell_op\<close>.\<close>

text \<open>The subsolution gives \<open>F(p, X) \<le> 1\<close>, the supersolution \<open>1 \<le> F(p, Y)\<close>,
  and the theorem on sums gives \<open>X \<preceq> Y\<close>, so degenerate ellipticity
  (\<open>ell_op_elliptic_le\<close>) sandwiches both values at \<open>1\<close>. Since \<open>F = 1\<close>
  carries no zeroth-order term, closing the argument needs a strict
  inequality, obtained by perturbing the subsolution.\<close>

lemma ell_op_strict_contradiction:
  fixes X Y :: "real^'n::finite^'n"
  assumes psd: "psd (Y - X)"
    and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    and sub: "ell_op k L p X < 1" and sup: "1 \<le> ell_op k L p Y"
  shows False
proof -
  have "ell_op k L p Y \<le> ell_op k L p X"
    by (rule ell_op_elliptic_le[OF psd ne])
  thus False using sub sup by linarith
qed

subsection \<open>Where the strictness comes from\<close>

text \<open>\<open>F(p, M) = Inf {- tr(M a)/2 | a feasible}\<close> has no zeroth-order term, so
  a subsolution cannot be made strict by subtracting a constant. But \<open>F\<close> is
  positively homogeneous in \<open>M\<close>, and the feasible set depends on \<open>p\<close> only
  through \<open>a *v p = 0\<close>: scaling a subsolution by \<open>\<theta> \<in> (0,1)\<close> sends
  \<open>(p, X)\<close> to \<open>(\<theta> p, \<theta> X)\<close> and \<open>F(p,X) \<le> 1\<close> to the strict
  \<open>F(\<theta> p, \<theta> X) \<le> \<theta> < 1\<close>.\<close>

lemma feasible_scaleR_p:
  fixes p :: "real^'n::finite"
  assumes t: "\<theta> \<noteq> 0"
  shows "feasible k L (\<theta> *\<^sub>R p) = feasible k L p"
proof -
  have iff: "(a *v (\<theta> *\<^sub>R p) = 0) = (a *v p = 0)" for a :: "real^'n^'n"
  proof -
    have "a *v (\<theta> *\<^sub>R p) = \<theta> *\<^sub>R (a *v p)"
      by (simp add: scaleR_matrix_vector_assoc[symmetric]
          matrix_scaleR_vector_ac)
    thus ?thesis using t by simp
  qed
  show ?thesis unfolding feasible_def using iff by auto
qed

text \<open>Scaling a conditionally-complete infimum by a positive constant:
  \<open>cInf_mult_pos\<close> lives in @{theory Relative_Arbitrage.Operator_Envelopes}.\<close>

text \<open>Positive homogeneity of \<open>F\<close> in the matrix argument: with
  \<open>feasible_scaleR_p\<close>, this is the strict-perturbation mechanism, scaling
  a subsolution's jet to \<open>(\<theta> p, \<theta> X)\<close> and its value to
  \<open>\<theta> F(p,X) \<le> \<theta> < 1\<close>.\<close>

lemma ell_op_scaleR_matrix:
  fixes M :: "real^'n::finite^'n"
  assumes t: "0 < \<theta>" and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
  shows "ell_op k L p (\<theta> *\<^sub>R M) = \<theta> * ell_op k L p M"
proof -
  have pt: "- trace ((\<theta> *\<^sub>R M) ** a) / 2 = \<theta> * (- trace (M ** a) / 2)"
    for a :: "real^'n^'n"
  proof -
    have "(\<theta> *\<^sub>R M) ** a = \<theta> *\<^sub>R (M ** a)"
      by (rule scaleR_matrix_mult)
    thus ?thesis by (simp add: trace_scaleR_matrix)
  qed
  have img: "(\<lambda>a. - trace ((\<theta> *\<^sub>R M) ** a) / 2) ` feasible k L p
      = (\<lambda>x. \<theta> * x) ` ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
    unfolding image_image using pt by simp
  show ?thesis
    unfolding ell_op_def img
    by (rule cInf_mult_pos[OF t _ ell_op_bdd_below]) (use ne in simp)
qed

lemma ell_op_scaleR_p:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes t: "\<theta> \<noteq> 0"
  shows "ell_op k L (\<theta> *\<^sub>R p) M = ell_op k L p M"
  unfolding ell_op_def feasible_scaleR_p[OF t] ..

text \<open>Scaling a subsolution by \<open>\<theta> \<in> (0,1)\<close> makes its operator inequality
  strict, since \<open>F\<close> has no zeroth-order term. With
  \<open>ell_op_strict_contradiction\<close>, a scaled subsolution and an unscaled
  supersolution sharing a jet pair \<open>X \<preceq> Y\<close> are inconsistent -- the
  contradiction underlying Theorem 4.2(a).\<close>

subsection \<open>Scaling a subsolution\<close>

text \<open>A test function scales, so a subsolution scaled by \<open>\<theta> \<in> (0,1)\<close>
  satisfies the strict operator inequality at each of its test points.\<close>

lemma test_fun_at_scaleR:
  fixes H :: "real^'n::finite^'n"
  assumes tf: "test_fun_at \<phi> g H x" and c: "0 < c"
  shows "test_fun_at (\<lambda>z. c * \<phi> z) (\<lambda>z. c *\<^sub>R g z) (c *\<^sub>R H) x"
  unfolding test_fun_at_def
proof (intro conjI)
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  show "transpose (c *\<^sub>R H) = c *\<^sub>R H"
    unfolding transpose_scaleR symH ..
next
  obtain e where e: "0 < e"
    and d: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. c * \<phi> z) has_derivative (\<lambda>h. (c *\<^sub>R g y) \<bullet> h)) (at y)"
  proof (rule exI[of _ e], intro conjI ballI)
    show "0 < e" by (rule e)
    fix y assume y: "y \<in> ball x e"
    have "((\<lambda>z. c *\<^sub>R \<phi> z) has_derivative (\<lambda>h. c *\<^sub>R (g y \<bullet> h))) (at y)"
      by (rule has_derivative_scaleR_right[OF d[OF y]])
    moreover have "(\<lambda>h. c *\<^sub>R (g y \<bullet> h)) = (\<lambda>h. (c *\<^sub>R g y) \<bullet> h)"
      by (rule ext) simp
    ultimately show "((\<lambda>z. c * \<phi> z) has_derivative (\<lambda>h. (c *\<^sub>R g y) \<bullet> h)) (at y)"
      by simp
  qed
next
  have dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast
  have "((\<lambda>z. c *\<^sub>R g z) has_derivative (\<lambda>h. c *\<^sub>R (H *v h))) (at x)"
    by (rule has_derivative_scaleR_right[OF dg])
  moreover have "(\<lambda>h. c *\<^sub>R (H *v h)) = (\<lambda>h. (c *\<^sub>R H) *v h)"
    by (rule ext) (simp add: scaleR_matrix_vector_assoc)
  ultimately show "((\<lambda>z. c *\<^sub>R g z) has_derivative (\<lambda>h. (c *\<^sub>R H) *v h)) (at x)"
    by simp
qed

theorem visc_subsol_scaled_strict:
  fixes u :: "real^'n::finite \<Rightarrow> real" and H :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>" "\<theta> < 1"
    and x: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and ne: "feasible k L (g x) \<noteq> ({} :: (real^'n^'n) set)"
    and maxloc: "\<exists>e>0. \<forall>y \<in> ball x e. \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
  shows "ell_op k L (g x) H < 1"
proof -
  define c where "c = 1/\<theta>"
  have c0: "0 < c" unfolding c_def using t(1) by simp
  have cn: "c \<noteq> 0" using c0 by simp
  have tfc: "test_fun_at (\<lambda>z. c * \<phi> z) (\<lambda>z. c *\<^sub>R g z) (c *\<^sub>R H) x"
    by (rule test_fun_at_scaleR[OF tf c0])
  obtain e where e: "0 < e"
    and m: "\<And>y. y \<in> ball x e \<Longrightarrow> \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
    using maxloc by blast
  have mc: "\<exists>e>0. \<forall>y \<in> ball x e. u y - c * \<phi> y \<le> u x - c * \<phi> x"
  proof (rule exI[of _ e], intro conjI ballI)
    show "0 < e" by (rule e)
    fix y assume y: "y \<in> ball x e"
    have "(\<theta> * u y - \<phi> y) * c \<le> (\<theta> * u x - \<phi> x) * c"
      using m[OF y] c0 by (intro mult_right_mono) auto
    thus "u y - c * \<phi> y \<le> u x - c * \<phi> x"
      unfolding c_def using t(1) by (simp add: field_simps)
  qed
  have "ell_op k L ((\<lambda>z. c *\<^sub>R g z) x) (c *\<^sub>R H) \<le> 1"
    using sub x tfc mc unfolding visc_subsol_def by blast
  hence step: "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) \<le> 1" by simp
  have "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) = ell_op k L (g x) (c *\<^sub>R H)"
    by (rule ell_op_scaleR_p[OF cn])
  also have "\<dots> = c * ell_op k L (g x) H"
    by (rule ell_op_scaleR_matrix[OF c0 ne])
  finally have "c * ell_op k L (g x) H \<le> 1" using step by simp
  hence "ell_op k L (g x) H \<le> \<theta>"
    unfolding c_def using t(1) by (simp add: field_simps)
  thus ?thesis using t(2) by linarith
qed

subsection \<open>Freezing one variable in the doubled maximum\<close>

text \<open>Freezing one variable at the joint maximiser gives the two conditions
  the doubling argument needs: freezing \<open>y = yh\<close> makes \<open>xh\<close> a maximiser of
  \<open>u\<close> against \<open>x \<mapsto> (\<alpha>/2) \<parallel>x - yh\<parallel>\<^sup>2\<close>, and freezing \<open>x = xh\<close> makes \<open>yh\<close> a
  minimiser of \<open>w\<close> against \<open>y \<mapsto> - (\<alpha>/2) \<parallel>xh - y\<parallel>\<^sup>2\<close>. This converts the
  two-variable maximum into the one-variable data \<open>visc_subsol\<close> and
  \<open>supersol_jet\<close> consume.\<close>

lemma doubling_partial_max_fst:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes jmax: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and yh: "yh \<in> S" and x: "x \<in> S"
  shows "u x - (\<alpha>/2) * (norm (x - yh))\<^sup>2
      \<le> u xh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
  using jmax[OF x yh] by simp

lemma doubling_partial_min_snd:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes jmax: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> S" and y: "y \<in> S"
  shows "w yh - (- ((\<alpha>/2) * (norm (xh - yh))\<^sup>2))
      \<le> w y - (- ((\<alpha>/2) * (norm (xh - y))\<^sup>2))"
  using jmax[OF xh y] by simp

text \<open>The two frozen penalties are smooth quadratics with the same gradient
  \<open>\<alpha> *\<^sub>R (xh - yh)\<close> at their respective points, and Hessians
  \<open>\<alpha> *\<^sub>R mat 1\<close> and \<open>- \<alpha> *\<^sub>R mat 1\<close>. The common gradient lets the two
  viscosity inequalities be compared at a common \<open>p\<close>; the wrongly-ordered
  Hessians are why the theorem on sums is needed to replace them by an
  ordered pair \<open>X \<preceq> Y\<close>.\<close>

text \<open>The same gradient at the other frozen point, letting the subsolution
  and supersolution inequalities be evaluated at a common vector
  \<open>p = \<alpha> *\<^sub>R (xh - yh)\<close>.\<close>

text \<open>The two Hessians, \<open>\<alpha> I\<close> and \<open>- \<alpha> I\<close>, are ordered the wrong way, the
  obstruction the theorem on sums removes.\<close>

text \<open>Packaging both frozen penalties as test functions supplies, with
  \<open>doubling_partial_max_fst\<close> and \<open>doubling_partial_min_snd\<close>, exactly the
  hypotheses \<open>visc_subsol\<close> and \<open>supersol_jet\<close> require, so the doubled
  maximum feeds into the two viscosity inequalities.\<close>

subsection \<open>What naive doubling delivers\<close>

text \<open>Feeding the two frozen test functions into the two viscosity
  definitions gives the two operator inequalities at the common vector
  \<open>p = \<alpha> *\<^sub>R (xh - yh)\<close>, with Hessians \<open>\<alpha> I\<close> and \<open>- \<alpha> I\<close>.\<close>

text \<open>Degenerate ellipticity would close the argument if the Hessians were
  ordered \<open>X \<preceq> Y\<close>, i.e. \<open>psd ((- \<alpha>) *\<^sub>R mat 1 - \<alpha> *\<^sub>R mat 1)\<close>; for
  \<open>\<alpha> > 0\<close> that matrix is \<open>(- 2 * \<alpha>) *\<^sub>R mat 1\<close>, negative definite. So the
  two inequalities arrive with Hessians ordered the wrong way, and replacing
  \<open>(\<alpha> I, - \<alpha> I)\<close> by an ordered pair \<open>X \<preceq> Y\<close> is the theorem on sums' role.\<close>

subsection \<open>From the abstract matrix inequality to \<open>psd\<close>\<close>

text \<open>\<open>sums_matrix_inequality\<close> gives \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close> for bounded linear
  \<open>X\<close>, \<open>Y\<close>, while \<open>ell_op_elliptic_le\<close> wants \<open>psd (N - M)\<close> for matrices.
  Since \<open>psd\<close> is symmetry plus \<open>0 \<le> x \<cdot> (a *v x)\<close>, the two are the same
  statement once represented by \<open>matrix\<close>.\<close>

lemma matrix_diff_vec:
  fixes X Y :: "(real^'n::finite) \<Rightarrow> (real^'n)"
  assumes lX: "linear X" and lY: "linear Y"
  shows "(matrix Y - matrix X) *v v = Y v - X v"
proof -
  have "(matrix Y - matrix X) *v v = matrix Y *v v - matrix X *v v"
    by (simp add: matrix_vector_mult_diff_rdistrib)
  thus ?thesis
    unfolding matrix_vec_apply[OF lX] matrix_vec_apply[OF lY] .
qed

theorem psd_of_abstract_le:
  fixes X Y :: "(real^'n::finite) \<Rightarrow> (real^'n)"
  assumes lX: "linear X" and lY: "linear Y"
    and symX: "\<And>v w. v \<bullet> X w = w \<bullet> X v"
    and symY: "\<And>v w. v \<bullet> Y w = w \<bullet> Y v"
    and le: "\<And>v. v \<bullet> X v \<le> v \<bullet> Y v"
  shows "psd (matrix Y - matrix X)"
  unfolding psd_def
proof (intro conjI allI)
  have sX: "transpose (matrix X) = matrix X"
    by (rule matrix_of_symmetric[OF lX symX])
  have sY: "transpose (matrix Y) = matrix Y"
    by (rule matrix_of_symmetric[OF lY symY])
  have td: "transpose (matrix Y - matrix X)
      = transpose (matrix Y) - transpose (matrix X)"
    by (simp add: transpose_def vec_eq_iff)
  show "transpose (matrix Y - matrix X) = matrix Y - matrix X"
    unfolding td sX sY ..
next
  fix v :: "real^'n"
  have "v \<bullet> ((matrix Y - matrix X) *v v) = v \<bullet> (Y v - X v)"
    unfolding matrix_diff_vec[OF lX lY] ..
  also have "\<dots> = v \<bullet> Y v - v \<bullet> X v" by (simp add: inner_diff_right)
  finally show "0 \<le> v \<bullet> ((matrix Y - matrix X) *v v)"
    using le[of v] by simp
qed

subsection \<open>The closing chain of Theorem 4.2(a)\<close>

text \<open>A scaled subsolution and a supersolution touching an ordered jet pair
  at a common \<open>p\<close> are inconsistent: scaling supplies strictness
  (\<open>visc_subsol_scaled_strict\<close>), the ordering supplies \<open>psd\<close>
  (\<open>psd_of_abstract_le\<close>), and degenerate ellipticity closes
  (\<open>ell_op_strict_contradiction\<close>). This is Theorem 4.2(a) modulo the
  hypotheses \<open>ord\<close>, \<open>subtest\<close> and \<open>suptest\<close>, supplied by the
  Rademacher/Alexandrov/Jensen/theorem-on-sums development in
  @{theory Alexandrov_Sup_Convolution.Sup_Convolution}.\<close>

theorem comparison_contradiction:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "(real^'n) \<Rightarrow> (real^'n)"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and xh: "xh \<in> \<Omega>" and yh: "yh \<in> \<Omega>"
    and lX: "linear X" and lY: "linear Y"
    and symX: "\<And>v z. v \<bullet> X z = z \<bullet> X v"
    and symY: "\<And>v z. v \<bullet> Y z = z \<bullet> Y v"
    and ord: "\<And>v. v \<bullet> X v \<le> v \<bullet> Y v"
    and ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L" and pnz: "p \<noteq> 0"
    and subtest: "\<exists>e>0. \<forall>z \<in> ball xh e.
        \<theta> * u z - (p \<bullet> (z - xh) + ((z - xh) \<bullet> (matrix X *v (z - xh)))/2)
        \<le> \<theta> * u xh
        - (p \<bullet> (xh - xh) + ((xh - xh) \<bullet> (matrix X *v (xh - xh)))/2)"
    and suptest: "\<exists>e>0. \<forall>z \<in> ball yh e.
        w yh - (p \<bullet> (yh - yh) + ((yh - yh) \<bullet> (matrix Y *v (yh - yh)))/2)
        \<le> w z - (p \<bullet> (z - yh) + ((z - yh) \<bullet> (matrix Y *v (z - yh)))/2)"
  shows False
proof -
  have tfX: "test_fun_at
      (\<lambda>z. p \<bullet> (z - xh) + ((z - xh) \<bullet> (matrix X *v (z - xh)))/2)
      (\<lambda>z. p + matrix X *v (z - xh)) (matrix X) xh"
    by (rule jet_test_fun_at_abstract[OF lX symX])
  have gX: "(\<lambda>z. p + matrix X *v (z - xh)) xh = p" by simp
  have neX: "feasible k L ((\<lambda>z. p + matrix X *v (z - xh)) xh)
      \<noteq> ({} :: (real^'n^'n) set)"
    unfolding gX by (rule ne)
  have strict: "ell_op k L ((\<lambda>z. p + matrix X *v (z - xh)) xh) (matrix X) < 1"
    by (rule visc_subsol_scaled_strict[OF sub t(1) t(2) xh tfX neX subtest])
  hence strictp: "ell_op k L p (matrix X) < 1" unfolding gX .
  have tfY: "test_fun_at
      (\<lambda>z. p \<bullet> (z - yh) + ((z - yh) \<bullet> (matrix Y *v (z - yh)))/2)
      (\<lambda>z. p + matrix Y *v (z - yh)) (matrix Y) yh"
    by (rule jet_test_fun_at_abstract[OF lY symY])
  have gY: "(\<lambda>z. p + matrix Y *v (z - yh)) yh = p" by simp
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + matrix Y *v (z - yh)) yh) (matrix Y)"
    using sup yh tfY suptest unfolding supersol_jet_def by blast
  hence "1 \<le> ell_op_usc k L p (matrix Y)" unfolding gY .
  hence supp: "1 \<le> ell_op k L p (matrix Y)"
    unfolding ell_op_usc_eq_at_nonzero[OF kk(1) kk(2) LL pnz] by simp
  have psdXY: "psd (matrix Y - matrix X)"
    by (rule psd_of_abstract_le[OF lX lY symX symY ord])
  show False
    by (rule ell_op_strict_contradiction[OF psdXY ne strictp supp])
qed

subsection \<open>The envelope route for removing the jet correction\<close>

text \<open>\<open>superjet_local_max\<close> introduces a strictly convex correction
  \<open>(\<delta>/2) * norm k\<^sup>2\<close>, so the matrix reaching the operator is \<open>X + \<delta> I\<close>
  rather than \<open>X\<close>. Removing \<open>\<delta>\<close> passes to closed second-order jets via the
  envelopes: the two envelope inequalities sandwich the sharp one, and
  \<open>visc_subsol_imp_env\<close> / \<open>visc_supersol_imp_env\<close> (@{theory Relative_Arbitrage.Operator_Envelopes}) show the
  envelope-free notions already imply the envelope ones on an open
  \<open>\<Omega> \<subseteq> K\<close>.\<close>

text \<open>The two envelope-form hypotheses in the shape the doubling produces:
  on an open \<open>\<Omega>\<close> inside \<open>K\<close>, a subsolution and supersolution in the
  envelope-free sense are also envelope sub/supersolutions, letting the
  doubling argument run where the \<open>\<delta> \<rightarrow> 0\<close> passage is legitimate.\<close>

lemma ball_prod_shift_snd:
  fixes p :: "real^'n::finite" and M N :: "real^'n^'n"
  assumes "w \<in> ball (p, M) e"
  shows "w + (0, N - M) \<in> ball (p, N) e"
proof -
  have eq: "(w + (0, N - M)) - (p, N) = w - (p, M)"
    by (simp add: prod_eq_iff)
  have "dist (w + (0, N - M)) (p, N) = dist w (p, M)"
    unfolding dist_norm eq ..
  moreover have "dist w (p, M) < e"
    using assms by (simp add: dist_commute)
  ultimately show ?thesis
    by (simp add: dist_commute)
qed

lemma ell_op_pair_shift_snd_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_pair k L (w + (0, N - M)) \<le> ell_op_pair k L w"
proof -
  have ne: "feasible k L (fst w) \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have psd': "psd ((snd w + (N - M)) - snd w)"
    using psd by simp
  have "ell_op k L (fst w) (snd w + (N - M)) \<le> ell_op k L (fst w) (snd w)"
    by (rule ell_op_elliptic_le[OF psd' ne])
  then show ?thesis
    by (simp add: ell_op_pair_def)
qed

theorem ell_op_lsc_elliptic_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_lsc k L p N \<le> ell_op_lsc k L p M"
  unfolding ell_op_lsc_def
proof (rule SUP_mono)
  fix e :: real
  assume e: "e \<in> {0<..}"
  have "(INF w \<in> ball ((p :: real^'n), N) e. ell_op_pair k L w)
      \<le> (INF w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
  proof (rule INF_mono)
    fix w :: "(real^'n) \<times> (real^'n^'n)"
    assume w: "w \<in> ball ((p :: real^'n), M) e"
    have "w + (0, N - M) \<in> ball ((p :: real^'n), N) e"
      by (rule ball_prod_shift_snd[OF w])
    moreover have "ell_op_pair k L (w + (0, N - M)) \<le> ell_op_pair k L w"
      by (rule ell_op_pair_shift_snd_le[OF psd k(1) k(2) L])
    ultimately show "\<exists>v \<in> ball ((p :: real^'n), N) e.
        ell_op_pair k L v \<le> ell_op_pair k L w"
      by blast
  qed
  with e show "\<exists>e' \<in> {0<..}. (INF w \<in> ball ((p :: real^'n), N) e. ell_op_pair k L w)
      \<le> (INF w \<in> ball ((p :: real^'n), M) e'. ell_op_pair k L w)"
    by blast
qed

text \<open>And the same for the upper envelope, by the dual argument: the same
  translation carries \<open>ball (p, M) e\<close> onto \<open>ball (p, N) e\<close>, and the
  integrand decreases along it, so the suprema compare and then the infima
  over the radius do.\<close>

theorem ell_op_usc_envelope_elliptic_le:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_usc k L p N \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_mono)
  fix e :: real
  assume e: "e \<in> {0<..}"
  have "(SUP w \<in> ball ((p :: real^'n), N) e. ell_op_pair k L w)
      \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
  proof (rule SUP_mono)
    fix v :: "(real^'n) \<times> (real^'n^'n)"
    assume v: "v \<in> ball ((p :: real^'n), N) e"
    have vm: "v - (0, N - M) \<in> ball ((p :: real^'n), M) e"
    proof -
      have eq: "(v - (0, N - M)) - (p, M) = v - (p, N)"
        by (simp add: prod_eq_iff)
      have "dist (v - (0, N - M)) (p, M) = dist v (p, N)"
        unfolding dist_norm eq ..
      moreover have "dist v (p, N) < e"
        using v by (simp add: dist_commute)
      ultimately show ?thesis
        by (simp add: dist_commute)
    qed
    have "ell_op_pair k L v \<le> ell_op_pair k L (v - (0, N - M))"
    proof -
      have "ell_op_pair k L ((v - (0, N - M)) + (0, N - M))
          \<le> ell_op_pair k L (v - (0, N - M))"
        by (rule ell_op_pair_shift_snd_le[OF psd k(1) k(2) L])
      then show ?thesis by simp
    qed
    with vm show "\<exists>u \<in> ball ((p :: real^'n), M) e.
        ell_op_pair k L v \<le> ell_op_pair k L u"
      by blast
  qed
  with e show "\<exists>e' \<in> {0<..}. (SUP w \<in> ball ((p :: real^'n), N) e'. ell_op_pair k L w)
      \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
    by blast
qed

subsection \<open>The envelope-form contradiction\<close>

text \<open>Ellipticity of the envelopes alone gives \<open>F\<^sup>*(p, Y) \<le> F\<^sup>*(p, X)\<close>, but
  combined with \<open>F\<^sub>*(p, X) < 1\<close> this is consistent wherever the two
  envelopes separate at \<open>(p, X)\<close>, i.e. wherever \<open>F\<close> is discontinuous. The
  mixed-envelope inequalities close only where the envelopes coincide with
  \<open>F\<close>, which by Lemma 3.1's last clause is everywhere off the origin
  (\<open>ell_op_lsc_off_zero\<close>, \<open>ell_op_usc_off_zero\<close>), reducing the envelope
  contradiction to the envelope-free one.\<close>

theorem ell_op_env_strict_contradiction:
  fixes X Y :: "real^'n::finite^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and p: "p \<noteq> 0" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and sub: "ell_op_lsc k L p X < 1" and sup: "1 \<le> ell_op_usc k L p Y"
  shows False
proof -
  have ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have eX: "ell_op_lsc k L p X = ereal (ell_op k L p X)"
    by (rule ell_op_lsc_off_zero[OF symX p L k(1) k(2)])
  have eY: "ell_op_usc k L p Y = ereal (ell_op k L p Y)"
    by (rule ell_op_usc_off_zero[OF symY p L k(1) k(2)])
  have subr: "ell_op k L p X < 1"
    using sub unfolding eX by (simp add: one_ereal_def)
  have supr: "1 \<le> ell_op k L p Y"
    using sup unfolding eY by (simp add: one_ereal_def)
  show False
    by (rule ell_op_strict_contradiction[OF psd ne subr supr])
qed

text \<open>The same for the non-strict sandwich, the form in which the envelope
  inequalities first arrive from the doubling.\<close>

text \<open>At \<open>p = 0\<close> the two envelopes disagree: \<open>ell_op_lsc_at_zero\<close> gives
  \<open>F\<^sub>*(0, M) = F(0, M)\<close>, while \<open>eq36\<close> gives \<open>F\<^sup>*(0, M) = eq36_rhs k L M\<close>,
  whose index range omits the eigenvalue \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close> of Eq. (3.5). So
  \<open>1 \<le> F\<^sup>*(0, Y)\<close> is strictly weaker than \<open>1 \<le> F(0, Y)\<close>, and envelope
  ellipticity cannot close the gap -- the degeneracy Lemma 3.1 isolates, and
  why the doubling needs the shared gradient to be nonzero.\<close>

subsection \<open>The dichotomy the side condition forces on the doubling\<close>

text \<open>In the doubling, the shared gradient at the maximising pair
  \<open>(x', y')\<close> of \<open>\<Phi>(x,y) = u x - w y - (\<alpha>/2) \<bar>x - y\<bar>\<^sup>2\<close> is
  \<open>p = \<alpha> (x' - y')\<close>, so \<open>p \<noteq> 0\<close> means the maximising pair is off the
  diagonal. For \<open>\<alpha> \<noteq> 0\<close> the gradient vanishes precisely on the diagonal.\<close>

text \<open>If the maximising pair is on the diagonal, the doubling degenerates:
  its common point maximises \<open>u - w\<close> over \<open>K\<close> itself, by comparing \<open>\<Phi>\<close>
  against the diagonal, where the penalty vanishes on both sides. So either
  the maximising pair is off the diagonal and \<open>ell_op_env_strict_contradiction\<close>
  applies, or \<open>u - w\<close> attains its maximum over \<open>K\<close> at the common point.\<close>

lemma doubling_diagonal_max:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and diag: "xh = yh" and xh: "xh \<in> K"
    and x: "x \<in> K"
  shows "u x - w x \<le> u xh - w xh"
proof -
  have "u x - w x - (\<alpha>/2) * (norm (x - x))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule mx[OF x x])
  then show ?thesis
    using diag by simp
qed

text \<open>Conversely, if \<open>u - w\<close> does not attain its maximum over \<open>K\<close> at the
  common point, the maximising pair cannot be on the diagonal, so the
  gradient is nonzero and the envelope contradiction applies.\<close>

lemma doubling_off_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and x: "x \<in> K"
    and gt: "u xh - w xh < u x - w x"
  shows "xh \<noteq> yh"
proof
  assume "xh = yh"
  from doubling_diagonal_max[OF mx this xh x] have "u x - w x \<le> u xh - w xh" .
  with gt show False by linarith
qed

corollary doubling_grad_nonzero:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and x: "x \<in> K"
    and gt: "u xh - w xh < u x - w x"
    and a: "\<alpha> \<noteq> 0"
  shows "\<alpha> *\<^sub>R (xh - yh) \<noteq> 0"
  using doubling_off_diagonal[OF mx xh x gt] a by simp

subsection \<open>The penalty estimate\<close>

text \<open>Every Crandall-Ishii comparison argument needs the penalty term at the
  maximising pair to be bounded, hence to vanish as \<open>\<alpha> \<rightarrow> \<infinity>\<close>, forcing
  \<open>x'\<close> and \<open>y'\<close> together and driving the doubled maximum to the maximum of
  \<open>u - w\<close>. The proof compares \<open>\<Phi>\<close> at the maximiser against \<open>\<Phi>\<close> at a
  diagonal point \<open>(z,z)\<close>, where the penalty vanishes, bounding the penalty
  at the maximiser by the gap between \<open>u(z) - w(z)\<close> and an upper bound for
  \<open>u x - w y\<close> on \<open>K \<times> K\<close>.\<close>

lemma doubling_penalty_bound:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C"
  shows "(\<alpha>/2) * (norm (xh - yh))\<^sup>2 \<le> C - (u z - w z)"
proof -
  have "u z - w z - (\<alpha>/2) * (norm (z - z))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule mx[OF z z])
  then have "u z - w z \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by simp
  with bnd show ?thesis by linarith
qed

text \<open>In the form actually used: for \<open>\<alpha> > 0\<close> the squared distance between
  the two components of the maximiser is \<open>O(1/\<alpha>)\<close>, with an explicit
  constant, driving \<open>x' - y' \<rightarrow> 0\<close>.\<close>

corollary doubling_dist_bound:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C" and a: "0 < \<alpha>"
  shows "(norm (xh - yh))\<^sup>2 \<le> 2 * (C - (u z - w z)) / \<alpha>"
proof -
  have "(\<alpha>/2) * (norm (xh - yh))\<^sup>2 \<le> C - (u z - w z)"
    by (rule doubling_penalty_bound[OF mx xh yh z bnd])
  then have "\<alpha> * (norm (xh - yh))\<^sup>2 \<le> 2 * (C - (u z - w z))"
    by simp
  then show ?thesis
    using a by (simp add: field_simps)
qed

text \<open>Since the penalty is bounded, the doubled maximum is at least the
  maximum of \<open>u - w\<close> along the diagonal; with \<open>doubling_diagonal_max\<close> this
  says the doubling can only improve on the diagonal value.\<close>

lemma doubling_ge_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and z: "z \<in> K"
  shows "u z - w z
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
proof -
  have "u z - w z - (\<alpha>/2) * (norm (z - z))\<^sup>2
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule mx[OF z z])
  then show ?thesis by simp
qed

subsection \<open>The dichotomy for a general penalty\<close>

text \<open>These four lemmas use the penalty only through \<open>Pn 0 = 0\<close>: each proof
  instantiates the maximiser inequality at a diagonal point, where the
  penalty is \<open>Pn (z - z) = Pn 0\<close> (\<open>soft_pen_zero\<close> for \<open>soft_pen\<close>).
  \<open>doubling_off_diagonal_gen\<close> puts the maximising pair off the diagonal
  whenever \<open>u - w\<close> beats its value at the common point, making
  \<open>soft_grad_nonzero\<close> applicable and supplying the positive lower bound
  \<open>c\<close>.\<close>

lemma doubling_diagonal_max_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
    and P0: "Pn 0 = 0"
    and diag: "xh = yh" and xh: "xh \<in> K"
    and x: "x \<in> K"
  shows "u x - w x \<le> u xh - w xh"
proof -
  have base: "u x - w x - Pn (x - x) \<le> u xh - w yh - Pn (xh - yh)"
    by (rule mx[OF x x])
  have e1: "x - x = (0 :: real^'n)" by simp
  have e2: "xh - yh = (0 :: real^'n)" using diag by simp
  from base have "u x - w x - Pn 0 \<le> u xh - w yh - Pn 0"
    unfolding e1 e2 .
  then have "u x - w x \<le> u xh - w yh" unfolding P0 by simp
  then show ?thesis using diag by simp
qed

lemma doubling_off_diagonal_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
    and P0: "Pn 0 = 0"
    and xh: "xh \<in> K" and x: "x \<in> K"
    and gt: "u xh - w xh < u x - w x"
  shows "xh \<noteq> yh"
proof
  assume e: "xh = yh"
  from doubling_diagonal_max_gen[OF mx P0 e xh x]
  have "u x - w x \<le> u xh - w xh" .
  with gt show False by linarith
qed

lemma doubling_penalty_bound_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
    and P0: "Pn 0 = 0"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C"
  shows "Pn (xh - yh) \<le> C - (u z - w z)"
proof -
  have base: "u z - w z - Pn (z - z) \<le> u xh - w yh - Pn (xh - yh)"
    by (rule mx[OF z z])
  have e: "z - z = (0 :: real^'n)" by simp
  from base have "u z - w z - Pn 0 \<le> u xh - w yh - Pn (xh - yh)"
    unfolding e .
  then have "u z - w z \<le> u xh - w yh - Pn (xh - yh)" unfolding P0 by simp
  with bnd show ?thesis by linarith
qed

subsection \<open>Monotonicity of the doubled maximum in the penalty parameter\<close>

text \<open>The other ingredient of the \<open>\<alpha> \<rightarrow> \<infinity>\<close> passage: the doubled maximum is
  antimonotone in \<open>\<alpha>\<close>, since a larger penalty can only decrease the
  supremum, the maximiser for larger \<open>\<alpha>\<close> being an admissible competitor for
  smaller \<open>\<alpha>\<close>. With \<open>doubling_ge_diagonal\<close>, this pins the family between
  two \<open>\<alpha>\<close>-independent bounds, so the limit exists without a compactness
  argument.\<close>

subsection \<open>The components of the maximiser merge, with no subsequences\<close>

text \<open>Because \<open>doubling_dist_bound\<close> comes with an explicit constant,
  \<open>x'\<^sub>\<alpha> - y'\<^sub>\<alpha> \<rightarrow> 0\<close> is a sandwich between \<open>0\<close> and \<open>2D/\<alpha>\<close>, needing
  neither compactness of \<open>K\<close> nor a subsequence.\<close>

subsection \<open>The diagonal branch \<open>p = 0\<close>\<close>

text \<open>The dichotomy leaves the diagonal branch \<open>p = 0\<close>. Since \<open>eq36\<close>
  identifies \<open>F\<^sup>*(0, M)\<close> with \<open>eq36_rhs k L M\<close>, ellipticity of \<open>F\<^sup>*\<close>
  transfers to \<open>eq36_rhs\<close>, a statement about the eigenvalue expression of
  Eq. (3.6).\<close>

theorem eq36_rhs_antitone:
  fixes M N :: "real^'n::finite^'n"
  assumes psd: "psd (N - M)"
    and symM: "transpose M = M" and symN: "transpose N = N"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "eq36_rhs k L N \<le> eq36_rhs k L M"
proof -
  have "ereal (eq36_rhs k L N) = ell_op_usc k L (0 :: real^'n) N"
    by (rule eq36[OF symN L k(1) k(2), symmetric])
  also have "\<dots> \<le> ell_op_usc k L (0 :: real^'n) M"
    by (rule ell_op_usc_envelope_elliptic_le[OF psd k(1) k(2) L])
  also have "\<dots> = ereal (eq36_rhs k L M)"
    by (rule eq36[OF symM L k(1) k(2)])
  finally show ?thesis by simp
qed

text \<open>The gap between the two envelopes at the origin,
  \<open>eq36_rhs k L M - F(0, M)\<close>, is nonnegative: \<open>ell_op_le_eq36\<close> specialised
  to \<open>p = 0\<close>, combined with \<open>ell_op_lsc_at_zero\<close>.\<close>

text \<open>At \<open>p = 0\<close>, \<open>F\<^sub>*(0,X) = F(0,X)\<close> and \<open>F\<^sup>*(0,Y) = eq36_rhs k L Y\<close>, with
  \<open>eq36_rhs\<close> antitone; the supersolution gives \<open>1 \<le> eq36_rhs k L X\<close> and
  the subsolution \<open>F(0,X) < 1\<close>. These are consistent because
  \<open>F(0,X) \<le> eq36_rhs k L X\<close> with room to spare, so the envelope gap at
  \<open>p = 0\<close> does not vanish in general.\<close>

subsection \<open>The diagonal branch closes without further hypotheses\<close>

text \<open>The \<open>p = 0\<close> branch closes without the envelopes, whose gap
  \<open>F(0,M) < F\<^sup>*(0,M) = eq36_rhs k L M\<close> is real, since the constraint
  \<open>a p = 0\<close> of \<open>feasible\<close> drops a dimension as \<open>p \<rightarrow> 0\<close>.
  \<open>subsol_shifted_bound\<close> and \<open>supersol_shifted_bound\<close> instead bound
  \<open>ell_op\<close> itself at the shifted matrices, and \<open>ell_op_M_gap\<close> bounds its
  change under a shift by \<open>\<delta> I\<close> by \<open>\<delta>\<sqdot>n\<sqdot>L/2 \<rightarrow> 0\<close>, giving
  \<open>1 \<le> F(p,Y) \<le> F(p,X) \<le> \<theta> < 1\<close> without reference to \<open>p\<close>. The
  off-diagonal condition is not needed.\<close>

lemma small_multiple_exists:
  fixes C g :: real
  assumes C: "0 < C" and g: "0 < g"
  shows "\<exists>\<delta>. 0 < \<delta> \<and> \<delta> < 1 \<and> \<delta> * C < g"
proof -
  define d where "d = min (1/2) (g/(2*C))"
  have h1: "0 < g/(2*C)" using C g by simp
  have d0: "0 < d" unfolding d_def using h1 by simp
  have d1: "d < 1" unfolding d_def by simp
  have "d * C \<le> (g/(2*C)) * C"
    unfolding d_def
    by (rule mult_right_mono[OF min.cobounded2 less_imp_le[OF C]])
  also have "(g/(2*C)) * C = g/2" using C by simp
  also have "g/2 < g" using g by simp
  finally have "d * C < g" .
  with d0 d1 show ?thesis by blast
qed

lemma shift_limit_absurd:
  fixes a b m tt bnd :: real
  assumes le1: "bnd \<le> a" and step: "a \<le> b + m" and meq: "m = tt"
    and small: "tt < bnd - b"
  shows False
  using assms by linarith

lemma shift_limit_absurd2:
  fixes a cc m tt th :: real
  assumes step: "a \<le> cc + m" and cle: "cc \<le> th" and meq: "m = tt"
    and small: "tt < a - th"
  shows False
  using assms by linarith

theorem strict_contradiction_of_shifts_any_p:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and t: "\<theta> < 1"
    and subs: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < 1 \<Longrightarrow> ell_op k L p (X + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    and sups: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < 1 \<Longrightarrow> 1 \<le> ell_op k L p (Y - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have ne: "feasible k L p \<noteq> ({} :: (real^'n^'n) set)"
    by (rule feasible_nonempty[OF k(1) k(2) L])
  have C0: "0 < real CARD('n) * L / 2" using k L by simp
  have cY: "1 \<le> ell_op k L p Y"
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L p Y"
    then have g: "0 < 1 - ell_op k L p Y" by linarith
    obtain \<delta> where d0: "0 < \<delta>" and d1: "\<delta> < 1"
      and dlt: "\<delta> * (real CARD('n) * L / 2) < 1 - ell_op k L p Y"
      using small_multiple_exists[OF C0 g] by blast
    have dN: "\<delta> * real CARD('n) * L / 2 < 1 - ell_op k L p Y"
    proof -
      have e1: "\<delta> * real CARD('n) * L / 2 = \<delta> * (real CARD('n) * L / 2)"
        by simp
      show ?thesis unfolding e1 by (rule dlt)
    qed
    show False
      by (rule shift_limit_absurd
          [OF sups[OF d0 d1] ell_op_M_gap[OF ne]
             mgap_shift_id(2)[OF less_imp_le[OF d0]] dN])
  qed
  have cX: "ell_op k L p X \<le> \<theta>"
  proof (rule ccontr)
    assume "\<not> ell_op k L p X \<le> \<theta>"
    then have g: "0 < ell_op k L p X - \<theta>" by linarith
    obtain \<delta> where d0: "0 < \<delta>" and d1: "\<delta> < 1"
      and dlt: "\<delta> * (real CARD('n) * L / 2) < ell_op k L p X - \<theta>"
      using small_multiple_exists[OF C0 g] by blast
    have dN: "\<delta> * real CARD('n) * L / 2 < ell_op k L p X - \<theta>"
    proof -
      have e1: "\<delta> * real CARD('n) * L / 2 = \<delta> * (real CARD('n) * L / 2)"
        by simp
      show ?thesis unfolding e1 by (rule dlt)
    qed
    show False
      by (rule shift_limit_absurd2
          [OF ell_op_M_gap[OF ne] subs[OF d0 d1]
             mgap_shift_id(1)[OF less_imp_le[OF d0]] dN])
  qed
  have ell: "ell_op k L p Y \<le> ell_op k L p X"
    by (rule ell_op_elliptic_le[OF psd ne])
  from cY cX ell t show False by linarith
qed

subsection \<open>Existence of the maximising pair\<close>

text \<open>Every doubling lemma above takes the maximising property of
  \<open>(x', y')\<close> as a hypothesis; on a compact \<open>K\<close> with continuous \<open>u\<close> and
  \<open>w\<close> it follows from attainment of a supremum by a continuous function on
  the compact product \<open>K \<times> K\<close>.\<close>

theorem doubling_maximiser_exists:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
proof -
  have cp: "compact (K \<times> K)"
    by (rule compact_Times[OF cK cK])
  have nep: "K \<times> K \<noteq> {}"
    using neK by blast
  have cfst: "continuous_on (K \<times> K) (\<lambda>z. u (fst z))"
    by (rule continuous_on_compose2[OF cu continuous_on_fst[OF continuous_on_id]])
       auto
  have csnd: "continuous_on (K \<times> K) (\<lambda>z. w (snd z))"
    by (rule continuous_on_compose2[OF cw continuous_on_snd[OF continuous_on_id]])
       auto
  have cpen: "continuous_on (K \<times> K)
      (\<lambda>z. (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)"
    by (intro continuous_intros)
  have cont: "continuous_on (K \<times> K)
      (\<lambda>z. u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)"
    using cfst csnd cpen by (intro continuous_intros)
  obtain z where z: "z \<in> K \<times> K"
    and mx: "\<forall>v \<in> K \<times> K.
        u (fst v) - w (snd v) - (\<alpha>/2) * (norm (fst v - snd v))\<^sup>2
          \<le> u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
    using continuous_attains_sup[OF cp nep cont] by blast
  have zf: "fst z \<in> K" and zs: "snd z \<in> K"
    using z by auto
  have "\<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
  proof (intro ballI)
    fix x y assume "x \<in> K" "y \<in> K"
    then have "(x, y) \<in> K \<times> K" by simp
    from mx[rule_format, OF this] show
      "u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> u (fst z) - w (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
      by simp
  qed
  with zf zs show ?thesis by blast
qed

text \<open>The same for a general penalty: the penalty enters the existence proof
  only through the continuity of \<open>cpen\<close>, so the general version takes that
  as a hypothesis; the rest is \<open>compact_Times\<close> plus
  \<open>continuous_attains_sup\<close>.\<close>

theorem doubling_maximiser_exists_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and cPn: "continuous_on UNIV Pn"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - Pn (x - y) \<le> u xh - w yh - Pn (xh - yh)"
proof -
  have cp: "compact (K \<times> K)"
    by (rule compact_Times[OF cK cK])
  have nep: "K \<times> K \<noteq> {}"
    using neK by blast
  have cfst: "continuous_on (K \<times> K) (\<lambda>z. u (fst z))"
    by (rule continuous_on_compose2[OF cu continuous_on_fst[OF continuous_on_id]])
       auto
  have csnd: "continuous_on (K \<times> K) (\<lambda>z. w (snd z))"
    by (rule continuous_on_compose2[OF cw continuous_on_snd[OF continuous_on_id]])
       auto
  have cdiff: "continuous_on (K \<times> K) (\<lambda>z. fst z - snd z)"
    by (intro continuous_intros)
  have cpen: "continuous_on (K \<times> K) (\<lambda>z. Pn (fst z - snd z))"
    by (rule continuous_on_compose2[OF cPn cdiff subset_UNIV])
  have cont: "continuous_on (K \<times> K)
      (\<lambda>z. u (fst z) - w (snd z) - Pn (fst z - snd z))"
    using cfst csnd cpen by (intro continuous_intros)
  obtain z where z: "z \<in> K \<times> K"
    and mx: "\<forall>v \<in> K \<times> K.
        u (fst v) - w (snd v) - Pn (fst v - snd v)
          \<le> u (fst z) - w (snd z) - Pn (fst z - snd z)"
    using continuous_attains_sup[OF cp nep cont] by blast
  have zf: "fst z \<in> K" and zs: "snd z \<in> K"
    using z by auto
  have "\<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - Pn (x - y)
        \<le> u (fst z) - w (snd z) - Pn (fst z - snd z)"
  proof (intro ballI)
    fix x y assume "x \<in> K" "y \<in> K"
    then have "(x, y) \<in> K \<times> K" by simp
    from mx[rule_format, OF this] show
      "u x - w y - Pn (x - y)
        \<le> u (fst z) - w (snd z) - Pn (fst z - snd z)"
      by simp
  qed
  with zf zs show ?thesis by blast
qed

text \<open>The packaged form: on a compact \<open>K\<close> the doubling produces a
  maximising pair together with the penalty bound and the diagonal lower
  bound already proved for it.\<close>

subsection \<open>Discharging the remaining bare hypothesis of the penalty estimate\<close>

text \<open>\<open>doubling_penalty_bound\<close> and \<open>doubling_dist_bound\<close> carry a bare
  hypothesis \<open>u x' - w y' \<le> C\<close>; on a compact \<open>K\<close> with continuous data it
  comes from the same attainment argument as the maximiser itself.\<close>

lemma doubling_upper_bound_exists:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>C. \<forall>x\<in>K. \<forall>y\<in>K. u x - w y \<le> C"
proof -
  have cp: "compact (K \<times> K)"
    by (rule compact_Times[OF cK cK])
  have nep: "K \<times> K \<noteq> {}"
    using neK by blast
  have cfst: "continuous_on (K \<times> K) (\<lambda>z. u (fst z))"
    by (rule continuous_on_compose2[OF cu continuous_on_fst[OF continuous_on_id]])
       auto
  have csnd: "continuous_on (K \<times> K) (\<lambda>z. w (snd z))"
    by (rule continuous_on_compose2[OF cw continuous_on_snd[OF continuous_on_id]])
       auto
  have cont: "continuous_on (K \<times> K) (\<lambda>z. u (fst z) - w (snd z))"
    using cfst csnd by (intro continuous_intros)
  obtain z where z: "z \<in> K \<times> K"
    and mx: "\<forall>v \<in> K \<times> K. u (fst v) - w (snd v) \<le> u (fst z) - w (snd z)"
    using continuous_attains_sup[OF cp nep cont] by blast
  have "\<forall>x\<in>K. \<forall>y\<in>K. u x - w y \<le> u (fst z) - w (snd z)"
  proof (intro ballI)
    fix x y assume "x \<in> K" "y \<in> K"
    then have "(x, y) \<in> K \<times> K" by simp
    from mx[rule_format, OF this]
    show "u x - w y \<le> u (fst z) - w (snd z)" by simp
  qed
  then show ?thesis by blast
qed

text \<open>Combining the two attainment results with the penalty estimate: on a
  compact \<open>K\<close> with continuous data the doubling produces a maximising pair
  whose penalty is bounded by an \<open>\<alpha>\<close>-independent constant, and whose two
  components are within \<open>O(1/\<surd>\<alpha>)\<close> of each other.\<close>

subsection \<open>Producing the local-max hypotheses of \<open>comparison_contradiction\<close>\<close>

text \<open>\<open>comparison_contradiction\<close> takes \<open>subtest\<close> and \<open>suptest\<close> -- local
  max/min statements for the jet test function -- as hypotheses; these are
  exactly what \<open>superjet_local_max\<close> yields from an Alexandrov jet once the
  test matrix is corrected by \<open>\<delta> I\<close>, since the \<open>(\<delta>/2)\<bar>k\<bar>\<^sup>2\<close> slack it
  leaves is precisely the extra quadratic form contributed by \<open>\<delta> I\<close>.\<close>

lemma quad_form_shift_identity:
  fixes A :: "real^'n::finite^'n" and k :: "real^'n"
  shows "k \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) + \<delta> * (norm k)\<^sup>2"
proof -
  have "(A + \<delta> *\<^sub>R mat 1) *v k = A *v k + \<delta> *\<^sub>R k"
    by (simp add: matrix_vector_mult_add_rdistrib
        scaleR_matrix_vector_assoc[symmetric])
  then have "k \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) + k \<bullet> (\<delta> *\<^sub>R k)"
    by (simp add: inner_add_right)
  then show ?thesis
    by (simp add: dot_square_norm)
qed

text \<open>The bridge itself: an Alexandrov jet of \<open>v\<close> at \<open>xh\<close> with data
  \<open>(p, A)\<close> gives, for every \<open>\<delta> > 0\<close>, the local-max statement for the jet
  test function built from \<open>(p, A + \<delta> I)\<close>, the \<open>subtest\<close> hypothesis
  \<open>comparison_contradiction\<close> requires.\<close>

theorem jet_imp_local_max_test:
  fixes v :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes lim: "((\<lambda>k. (v (xh + k) - v xh - p \<bullet> k - (k \<bullet> (A *v k))/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>z \<in> ball xh e.
      v z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> v xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
proof -
  obtain e where e: "0 < e"
    and b: "\<And>k. norm k < e \<Longrightarrow>
        v (xh + k) - (p \<bullet> k + (k \<bullet> (A *v k))/2 + (\<delta>/2) * (norm k)\<^sup>2) \<le> v xh"
    using superjet_local_max[OF lim d] by blast
  have "\<forall>z \<in> ball xh e.
      v z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> v xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
  proof
    fix z assume z: "z \<in> ball xh e"
    have nk: "norm (z - xh) < e"
      using z by (simp add: dist_norm norm_minus_commute)
    have xz: "xh + (z - xh) = z" by simp
    from b[OF nk] have
      "v z - (p \<bullet> (z - xh) + ((z - xh) \<bullet> (A *v (z - xh)))/2
          + (\<delta>/2) * (norm (z - xh))\<^sup>2) \<le> v xh"
      unfolding xz .
    moreover have
      "(z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh))
        = (z - xh) \<bullet> (A *v (z - xh)) + \<delta> * (norm (z - xh))\<^sup>2"
      by (rule quad_form_shift_identity)
    ultimately show
      "v z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> v xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((A + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
      by (simp add: add_divide_distrib)
  qed
  with e show ?thesis by blast
qed

lemma matrix_vector_neg_left:
  fixes B :: "real^'n::finite^'n"
  shows "(- B) *v x = - (B *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

lemma quad_form_shift_identity_neg:
  fixes A :: "real^'n::finite^'n" and k :: "real^'n"
  shows "k \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) - \<delta> * (norm k)\<^sup>2"
proof -
  have "(A - \<delta> *\<^sub>R mat 1) *v k = A *v k - \<delta> *\<^sub>R k"
    by (simp add: matrix_vector_mult_diff_rdistrib
        scaleR_matrix_vector_assoc[symmetric])
  then have "k \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v k) = k \<bullet> (A *v k) - k \<bullet> (\<delta> *\<^sub>R k)"
    by (simp add: inner_diff_right)
  then show ?thesis
    by (simp add: dot_square_norm)
qed

text \<open>The mirror image for the supersolution side: a subjet of \<open>v\<close> at \<open>yh\<close>
  gives the local-min statement, with correction \<open>- \<delta> I\<close>, following from
  the same theorem applied to \<open>-v\<close>, whose jet data is \<open>(-p, -A)\<close>.\<close>

subsection \<open>The jet hypothesis only ever needs one side\<close>

text \<open>\<open>superjet_local_max\<close> (@{theory Alexandrov_Sup_Convolution.Sup_Convolution}) only uses one side of its
  \<open>tendsto\<close> hypothesis; the diagonal branch of Theorem 4.2(a) supplies only
  an upper bound on the increment of \<open>B = supconv (-w) \<epsilon>\<close>. This
  subsection restates the chain with a one-sided hypothesis;
  \<open>onesided_of_tendsto\<close> shows it is a genuine weakening. The quantifier
  over the threshold \<open>c\<close> is necessary: in \<open>supersol_no_vanishing_jet\<close> the
  bound is produced inside the proof by \<open>small_multiple_exists\<close>, after the
  hypothesis is fixed.\<close>

lemma superjet_local_max_onesided:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F kk in at 0.
      (u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2) / (norm kk)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>kk. norm kk < e \<longrightarrow>
      u (xh + kk) - (p \<bullet> kk + (kk \<bullet> X kk)/2 + (\<delta>/2) * (norm kk)\<^sup>2) \<le> u xh"
proof -
  have d2: "0 < \<delta>/2" using d by simp
  from ub[OF d2] obtain e where e: "0 < e"
    and b: "\<And>kk. kk \<noteq> 0 \<Longrightarrow> dist kk 0 < e
      \<Longrightarrow> (u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2) / (norm kk)\<^sup>2 < \<delta>/2"
    unfolding eventually_at by blast
  have main: "u (xh + kk) - (p \<bullet> kk + (kk \<bullet> X kk)/2 + (\<delta>/2) * (norm kk)\<^sup>2)
      \<le> u xh" if nk: "norm kk < e" for kk
  proof (cases "kk = 0")
    case True
    show ?thesis unfolding True by simp
  next
    case False
    have nn: "0 < (norm kk)\<^sup>2" using False by simp
    have dk: "dist kk 0 < e" using nk by (simp add: dist_norm)
    have "(u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2) / (norm kk)\<^sup>2 < \<delta>/2"
      by (rule b[OF False dk])
    hence "u (xh + kk) - u xh - p \<bullet> kk - (kk \<bullet> X kk)/2 < (\<delta>/2) * (norm kk)\<^sup>2"
      using nn by (simp add: field_simps)
    thus ?thesis by simp
  qed
  show ?thesis using e main by blast
qed

text \<open>If the increment of \<open>B\<close> at \<open>p\<close> is eventually dominated by some \<open>D\<close>
  that is \<open>o(|h|^2)\<close>, it satisfies the one-sided hypothesis -- exactly what
  a diagonal maximiser supplies, with \<open>D\<close> the penalty; domination holds only
  eventually since the maximiser inequality needs \<open>p + h\<close> to stay in \<open>K\<close>.\<close>

lemma onesided_of_tendsto_gen:
  fixes D :: "'a::euclidean_space \<Rightarrow> real"
  assumes lim: "((\<lambda>hh. D hh / (norm hh)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and c: "0 < c"
  shows "\<forall>\<^sub>F hh in at 0. D hh / (norm hh)\<^sup>2 < c"
proof -
  have step: "q < c" if "dist q 0 < c" for q :: real
    using that by (simp add: dist_real_def abs_less_iff)
  have T: "\<forall>\<^sub>F hh in at 0. dist (D hh / (norm hh)\<^sup>2) 0 < c"
    by (rule tendstoD[OF lim c])
  show ?thesis by (rule eventually_mono[OF T]) (rule step)
qed

lemma onesided_of_dominated:
  fixes B D :: "'a::euclidean_space \<Rightarrow> real"
  assumes dom: "\<forall>\<^sub>F hh in at 0. B (p + hh) - B p \<le> D hh"
    and lim: "((\<lambda>hh. D hh / (norm hh)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and c: "0 < c"
  shows "\<forall>\<^sub>F hh in at 0. (B (p + hh) - B p) / (norm hh)\<^sup>2 < c"
proof -
  have T: "\<forall>\<^sub>F hh in at 0. D hh / (norm hh)\<^sup>2 < c"
    by (rule onesided_of_tendsto_gen[OF lim c])
  from eventually_conj[OF dom T] show ?thesis
  proof (rule eventually_mono)
    fix hh :: 'a
    assume A: "B (p + hh) - B p \<le> D hh \<and> D hh / (norm hh)\<^sup>2 < c"
    have le: "B (p + hh) - B p \<le> D hh" using A by simp
    have "(B (p + hh) - B p) / (norm hh)\<^sup>2 \<le> D hh / (norm hh)\<^sup>2"
      by (rule divide_right_mono[OF le]) simp
    then show "(B (p + hh) - B p) / (norm hh)\<^sup>2 < c" using A by linarith
  qed
qed

theorem jet_imp_local_min_test_onesided:
  fixes v :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F kk in at 0.
      ((- v) (yh + kk) - (- v) yh - (- p) \<bullet> kk
        - (kk \<bullet> ((- A) *v kk))/2) / (norm kk)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
proof -
  obtain e where e: "0 < e"
    and b: "\<And>kk. norm kk < e \<Longrightarrow>
        (- v) (yh + kk) - ((- p) \<bullet> kk + (kk \<bullet> ((- A) *v kk))/2
          + (\<delta>/2) * (norm kk)\<^sup>2) \<le> (- v) yh"
    using superjet_local_max_onesided[OF ub d] by blast
  have "\<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
  proof
    fix z assume z: "z \<in> ball yh e"
    have nk: "norm (z - yh) < e"
      using z by (simp add: dist_norm norm_minus_commute)
    have yz: "yh + (z - yh) = z" by simp
    have negq: "(z - yh) \<bullet> ((- A) *v (z - yh))
        = - ((z - yh) \<bullet> (A *v (z - yh)))"
      by (simp add: matrix_vector_neg_left)
    from b[OF nk] have h:
      "- v z - (- (p \<bullet> (z - yh))
          + ((z - yh) \<bullet> ((- A) *v (z - yh)))/2
          + (\<delta>/2) * (norm (z - yh))\<^sup>2) \<le> - v yh"
      unfolding yz by simp
    have q: "(z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh))
        = (z - yh) \<bullet> (A *v (z - yh)) - \<delta> * (norm (z - yh))\<^sup>2"
      by (rule quad_form_shift_identity_neg)
    from h show
      "v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
      unfolding q negq by (simp add: field_simps)
  qed
  with e show ?thesis by blast
qed

theorem jet_imp_local_min_test:
  fixes v :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes lim: "((\<lambda>k. ((- v) (yh + k) - (- v) yh - (- p) \<bullet> k
      - (k \<bullet> ((- A) *v k))/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "\<exists>e>0. \<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
proof -
  obtain e where e: "0 < e"
    and b: "\<And>k. norm k < e \<Longrightarrow>
        (- v) (yh + k) - ((- p) \<bullet> k + (k \<bullet> ((- A) *v k))/2
          + (\<delta>/2) * (norm k)\<^sup>2) \<le> (- v) yh"
    using superjet_local_max[OF lim d] by blast
  have "\<forall>z \<in> ball yh e.
      v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
  proof
    fix z assume z: "z \<in> ball yh e"
    have nk: "norm (z - yh) < e"
      using z by (simp add: dist_norm norm_minus_commute)
    have yz: "yh + (z - yh) = z" by simp
    have negq: "(z - yh) \<bullet> ((- A) *v (z - yh))
        = - ((z - yh) \<bullet> (A *v (z - yh)))"
      by (simp add: matrix_vector_neg_left)
    from b[OF nk] have h:
      "- v z - (- (p \<bullet> (z - yh))
          + ((z - yh) \<bullet> ((- A) *v (z - yh)))/2
          + (\<delta>/2) * (norm (z - yh))\<^sup>2) \<le> - v yh"
      unfolding yz by simp
    have q: "(z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh))
        = (z - yh) \<bullet> (A *v (z - yh)) - \<delta> * (norm (z - yh))\<^sup>2"
      by (rule quad_form_shift_identity_neg)
    from h show
      "v yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> v z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((A - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
      unfolding q negq by (simp add: field_simps)
  qed
  with e show ?thesis by blast
qed

subsection \<open>Removing the jet correction\<close>

text \<open>The \<open>\<delta>\<close> from \<open>jet_imp_local_max_test\<close> cannot cancel against
  \<open>X \<preceq> Y\<close>: correcting to \<open>X + \<delta> I\<close>, \<open>Y - \<delta> I\<close> would need
  \<open>Y - X \<succeq> 2\<delta> I\<close>, but the theorem on sums gives only \<open>Y - X \<succeq> 0\<close>, so
  \<open>\<delta>\<close> is removed by a limit instead. Degenerate ellipticity gives
  \<open>F(p, M + \<delta> I) \<le> F(p, M)\<close>, and since \<open>F\<^sub>*\<close> is the limit over points near
  \<open>(p, M)\<close>, \<open>F(p, M + \<delta> I) \<le> 1\<close> for all \<open>\<delta>\<close> already gives
  \<open>F\<^sub>*(p, M) \<le> 1\<close>.\<close>

text \<open>The mirror statement for the upper envelope, needed by the
  supersolution side: a lower bound at the shifted matrices \<open>M - \<delta> I\<close>
  transfers to \<open>F\<^sup>*\<close> at \<open>M\<close>, for the dual reason.\<close>

subsection \<open>Making the strictness survive the limit\<close>

text \<open>The two shift theorems above are stated with bound \<open>1\<close>, enough for the
  sandwich but not the contradiction: passing to the limit turns
  \<open>F(p, X + \<delta> I) < 1\<close> into \<open>F\<^sub>*(p, X) \<le> 1\<close>, losing strictness. The fix:
  the strictness from \<open>\<theta>\<close>-scaling is uniform,
  \<open>F(\<theta> p, \<theta> X) = \<theta> F(p, X) \<le> \<theta>\<close> with \<open>\<theta> < 1\<close> independent of \<open>\<delta>\<close>, and a
  uniform bound survives the limit, so the shift theorems are restated with
  an arbitrary bound \<open>c\<close> in place of \<open>1\<close>.\<close>

theorem ell_op_lsc_le_of_shifts:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> ell_op k L p (M + \<delta> *\<^sub>R mat 1) \<le> c"
    and D: "0 < D"
  shows "ell_op_lsc k L p M \<le> ereal c"
  unfolding ell_op_lsc_def
proof (rule SUP_least)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e"
  proof -
    have dle: "d \<le> e/(2*(N+1))"
      unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e"
    proof -
      have "e * N < e * (2*(N+1))"
        using e0 N0 by simp
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have dp: "dist ((p, M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
      = d * N"
  proof -
    have "dist ((p, M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
        = sqrt ((dist p p)\<^sup>2 + (dist (M + d *\<^sub>R mat 1) M)\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (M + d *\<^sub>R mat 1) M"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have mem: "((p, M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      \<in> ball (p, M) e"
    using dp small by (simp add: dist_commute)
  have "(INF w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)
      \<le> ell_op_pair k L (p, M + d *\<^sub>R mat 1)"
    by (rule INF_lower[OF mem])
  also have "\<dots> \<le> ereal c"
    using b[OF d0 dD] by (simp add: ell_op_pair_def)
  finally show "(INF w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)
      \<le> ereal c" .
qed

theorem ell_op_usc_ge_of_shifts:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> c \<le> ell_op k L p (M - \<delta> *\<^sub>R mat 1)"
    and D: "0 < D"
  shows "ereal c \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e"
  proof -
    have dle: "d \<le> e/(2*(N+1))"
      unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e"
    proof -
      have "e * N < e * (2*(N+1))"
        using e0 N0 by simp
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have dp: "dist ((p, M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
      = d * N"
  proof -
    have "dist ((p, M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) (p, M)
        = sqrt ((dist p p)\<^sup>2 + (dist (M - d *\<^sub>R mat 1) M)\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (M - d *\<^sub>R mat 1) M"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have mem: "((p, M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      \<in> ball (p, M) e"
    using dp small by (simp add: dist_commute)
  have "ereal c \<le> ell_op_pair k L (p, M - d *\<^sub>R mat 1)"
    using b[OF d0 dD] by (simp add: ell_op_pair_def)
  also have "\<dots> \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)"
    by (rule SUP_upper[OF mem])
  finally show "ereal c
      \<le> (SUP w \<in> ball ((p :: real^'n), M) e. ell_op_pair k L w)" .
qed

text \<open>The closing chain of Theorem 4.2(a) in \<open>\<delta>\<close>-corrected form: a uniform
  strict bound \<open>c < 1\<close> on the subsolution side at every \<open>X + \<delta> I\<close>, the
  supersolution bound at every \<open>Y - \<delta> I\<close>, the ordering \<open>X \<preceq> Y\<close> from the
  theorem on sums, and \<open>p \<noteq> 0\<close> from \<open>doubling_grad_nonzero\<close>. No \<open>\<delta>\<close>
  survives in the conclusion.\<close>

theorem env_strict_contradiction_of_shifts:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and p: "p \<noteq> 0" and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and D: "0 < D" and c1: "c < 1"
    and subs: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D
        \<Longrightarrow> ell_op k L p (X + \<delta> *\<^sub>R mat 1) \<le> c"
    and sups: "\<And>\<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D
        \<Longrightarrow> 1 \<le> ell_op k L p (Y - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have lsc: "ell_op_lsc k L p X \<le> ereal c"
    by (rule ell_op_lsc_le_of_shifts[OF subs D])
  have c1e: "ereal c < 1"
    using c1 by (simp add: one_ereal_def)
  have sub: "ell_op_lsc k L p X < 1"
    using lsc c1e by (rule le_less_trans)
  have sup: "1 \<le> ell_op_usc k L p Y"
    using ell_op_usc_ge_of_shifts[OF sups D] by (simp add: one_ereal_def)
  show False
    by (rule ell_op_env_strict_contradiction[OF psd symX symY p k(1) k(2) L
          sub sup])
qed

subsection \<open>The uniform strict bound, and the shifted families\<close>

text \<open>\<open>visc_subsol_scaled_strict\<close> concludes \<open>F < 1\<close>, but its proof actually
  gives the stronger \<open>F \<le> \<theta>\<close>; this is the same argument stopped one step
  earlier, giving the bound that survives the \<open>\<delta> \<rightarrow> 0\<close> limit.\<close>

theorem visc_subsol_scaled_uniform:
  fixes u :: "real^'n::finite \<Rightarrow> real" and H :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>"
    and x: "x \<in> \<Omega>"
    and tf: "test_fun_at \<phi> g H x"
    and ne: "feasible k L (g x) \<noteq> ({} :: (real^'n^'n) set)"
    and maxloc: "\<exists>e>0. \<forall>y \<in> ball x e. \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
  shows "ell_op k L (g x) H \<le> \<theta>"
proof -
  define c where "c = 1/\<theta>"
  have c0: "0 < c" unfolding c_def using t by simp
  have cn: "c \<noteq> 0" using c0 by simp
  have tfc: "test_fun_at (\<lambda>z. c * \<phi> z) (\<lambda>z. c *\<^sub>R g z) (c *\<^sub>R H) x"
    by (rule test_fun_at_scaleR[OF tf c0])
  obtain e where e: "0 < e"
    and m: "\<And>y. y \<in> ball x e \<Longrightarrow> \<theta> * u y - \<phi> y \<le> \<theta> * u x - \<phi> x"
    using maxloc by blast
  have mc: "\<exists>e>0. \<forall>y \<in> ball x e. u y - c * \<phi> y \<le> u x - c * \<phi> x"
  proof (rule exI[of _ e], intro conjI ballI)
    show "0 < e" by (rule e)
    fix y assume y: "y \<in> ball x e"
    have "(\<theta> * u y - \<phi> y) * c \<le> (\<theta> * u x - \<phi> x) * c"
      using m[OF y] c0 by (intro mult_right_mono) auto
    thus "u y - c * \<phi> y \<le> u x - c * \<phi> x"
      unfolding c_def using t by (simp add: field_simps)
  qed
  have "ell_op k L ((\<lambda>z. c *\<^sub>R g z) x) (c *\<^sub>R H) \<le> 1"
    using sub x tfc mc unfolding visc_subsol_def by blast
  hence step: "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) \<le> 1" by simp
  have "ell_op k L (c *\<^sub>R g x) (c *\<^sub>R H) = ell_op k L (g x) (c *\<^sub>R H)"
    by (rule ell_op_scaleR_p[OF cn])
  also have "\<dots> = c * ell_op k L (g x) H"
    by (rule ell_op_scaleR_matrix[OF c0 ne])
  finally have "c * ell_op k L (g x) H \<le> 1" using step by simp
  thus ?thesis
    unfolding c_def using t by (simp add: field_simps)
qed

text \<open>Symmetry of the corrected matrices, needed by the jet test function:
  transposition is additive entrywise, so both directions of the correction
  preserve symmetry.\<close>

text \<open>The two producers: an Alexandrov jet of \<open>\<theta> u\<close> at \<open>x'\<close> with data
  \<open>(p, X)\<close> gives, for every \<open>\<delta> > 0\<close>, the uniform bound
  \<open>F(p, X + \<delta> I) \<le> \<theta>\<close>; dually on the supersolution side. These are the
  two families \<open>env_strict_contradiction_of_shifts\<close> consumes.\<close>

theorem subsol_shifted_bound:
  fixes u :: "real^'n::finite \<Rightarrow> real" and Xm :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>"
    and xh: "xh \<in> \<Omega>"
    and Xs: "transpose Xm = Xm"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and jet: "((\<lambda>h. (\<theta> * u (xh + h) - \<theta> * u xh - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
proof -
  have sym: "transpose (Xm + \<delta> *\<^sub>R mat 1) = Xm + \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_add[OF Xs])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - xh)
        + ((z - xh) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      (\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) (Xm + \<delta> *\<^sub>R mat 1) xh"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) xh = p"
    by simp
  have ne: "feasible k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) xh)
      \<noteq> ({} :: (real^'n^'n) set)"
    unfolding g by (rule feasible_nonempty[OF k(1) k(2) L])
  have maxloc: "\<exists>e>0. \<forall>z \<in> ball xh e.
      \<theta> * u z - (p \<bullet> (z - xh)
          + ((z - xh) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)))/2)
      \<le> \<theta> * u xh - (p \<bullet> (xh - xh)
          + ((xh - xh) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (xh - xh)))/2)"
    by (rule jet_imp_local_max_test[OF jet d])
  have "ell_op k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - xh)) xh)
      (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    by (rule visc_subsol_scaled_uniform[OF sub t xh tf ne maxloc])
  thus ?thesis unfolding g .
qed

theorem supersol_shifted_bound_onesided:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        ((- w) (yh + hh) - (- w) yh - (- p) \<bullet> hh
          - (hh \<bullet> ((- Ym) *v hh))/2) / (norm hh)\<^sup>2 < c"
    and d: "0 < \<delta>"
  shows "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have sym: "transpose (Ym - \<delta> *\<^sub>R mat 1) = Ym - \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_diff[OF Ys])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - yh)
        + ((z - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)
      (\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) (Ym - \<delta> *\<^sub>R mat 1) yh"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh = p"
    by simp
  have minloc: "\<exists>e>0. \<forall>z \<in> ball yh e.
      w yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> w z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
    by (rule jet_imp_local_min_test_onesided[OF ub d])
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup yh tf minloc unfolding supersol_jet_def by blast
  thus ?thesis unfolding g .
qed

theorem supersol_shifted_bound:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and jet: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- p) \<bullet> h
        - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have sym: "transpose (Ym - \<delta> *\<^sub>R mat 1) = Ym - \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_diff[OF Ys])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - yh)
        + ((z - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)
      (\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) (Ym - \<delta> *\<^sub>R mat 1) yh"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh = p"
    by simp
  have minloc: "\<exists>e>0. \<forall>z \<in> ball yh e.
      w yh - (p \<bullet> (yh - yh)
          + ((yh - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (yh - yh)))/2)
      \<le> w z - (p \<bullet> (z - yh)
          + ((z - yh) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)))/2)"
    by (rule jet_imp_local_min_test[OF jet d])
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - yh)) yh)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup yh tf minloc unfolding supersol_jet_def by blast
  thus ?thesis unfolding g .
qed

corollary supersol_shifted_bound_ne:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w" and yh: "yh \<in> \<Omega>"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Ys: "transpose Ym = Ym"
    and jet: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- p) \<bullet> h
        - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>" and p0: "p \<noteq> 0"
  shows "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound[OF sup yh Ys jet d])
  then show ?thesis
    unfolding ell_op_usc_eq_at_nonzero[OF kk(1) kk(2) LL p0] by simp
qed

subsection \<open>The quartic penalty and its exact second-order expansion\<close>

text \<open>Writing \<open>s = d \<bullet> d\<close> and \<open>t = 2(d \<bullet> h) + h \<bullet> h\<close>, the exact expansion
  \<open>P(d+h) - P(d) = (\<beta>/4)((s+t)\<^sup>2 - s\<^sup>2) = (\<beta>/4)(2st + t\<^sup>2)\<close> gives gradient
  \<open>\<nabla>P(d) = \<beta>(d \<bullet> d) d\<close> and Hessian quadratic form
  \<open>h \<mapsto> \<beta>(d \<bullet> d)(h \<bullet> h) + 2\<beta>(d \<bullet> h)\<^sup>2\<close>, matrix
  \<open>\<beta>((d \<bullet> d) I + 2 d d\<^sup>T)\<close>, with remainder \<open>o(\<parallel>h\<parallel>\<^sup>2)\<close>. Both vanish only at
  \<open>d = 0\<close>, giving the supersolution a \<open>(0,0)\<close> jet on the diagonal and hence
  the contradiction of \<open>supersol_no_vanishing_jet\<close>.\<close>

definition quartic_pen :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real" where
  "quartic_pen \<beta> d = (\<beta>/4) * (d \<bullet> d)\<^sup>2"

text \<open>The jet itself, in the shape the slice lemmas consume: gradient
  \<open>\<beta>(d \<bullet> d) d\<close>, quadratic form \<open>h \<mapsto> \<beta>(d \<bullet> d)(h \<bullet> h) + 2\<beta>(d \<bullet> h)\<^sup>2\<close>.
  Exact, holding at every \<open>d\<close> with no smallness hypothesis.\<close>

text \<open>At \<open>d = 0\<close> both gradient and quadratic form vanish, so the quartic
  penalty has second-order jet \<open>(0, 0)\<close> there; feeding this to
  \<open>supersol_no_vanishing_jet\<close> gives the paper's \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.\<close>

subsection \<open>The doubled penalty's jet, for an arbitrary penalty\<close>

text \<open>Below \<open>sums_matrix_inequality\<close> the \<open>psd\<close> chain is abstract in the two
  block maps; \<open>sums_matrix_inequality\<close> itself uses an exact identity for
  the quadratic penalty, which for general \<open>P\<close> is only asymptotic, and this
  lemma supplies it. Writing \<open>e k = fst k - snd k\<close>, the doubled penalty
  \<open>z \<mapsto> P (fst z - snd z)\<close> has gradient \<open>(G, -G)\<close> and Hessian
  \<open>k \<mapsto> (Z (e k), -Z (e k))\<close> at \<open>z'\<close>, with numerator collapsing to
  \<open>R (e k)\<close>. Although \<open>e\<close> is not injective near \<open>0\<close>, the limit survives
  because \<open>e\<close> is 2-Lipschitz and kills only the diagonal, where \<open>R 0 = 0\<close>.\<close>

lemma matrix_vector_mult_diff_gen:
  fixes Z :: "real^'n::finite^'n"
  shows "Z *v (u - v) = Z *v u - Z *v v"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_subtractf algebra_simps)

lemma doubled_penalty_jet:
  fixes P :: "real^'n::finite \<Rightarrow> real" and Z :: "real^'n^'n" and G :: "real^'n"
    and zh :: "(real^'n) \<times> (real^'n)"
  assumes Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
      - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>k. (P (fst (zh + k) - snd (zh + k)) - P (fst zh - snd zh)
      - ((G, - G) :: (real^'n) \<times> (real^'n)) \<bullet> k
      - (k \<bullet> ((Z *v (fst k - snd k), Z *v (snd k - fst k))
            :: (real^'n) \<times> (real^'n)))/2) / (norm k)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)"
proof -
  define R where "R = (\<lambda>h::real^'n. P ((fst zh - snd zh) + h)
      - P (fst zh - snd zh) - G \<bullet> h - (h \<bullet> (Z *v h))/2)"
  have Rlim: "((\<lambda>h. R h / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding R_def by (rule Pjet)
  have R0: "R 0 = 0" unfolding R_def by simp
  have num: "P (fst (zh + k) - snd (zh + k)) - P (fst zh - snd zh)
      - ((G, - G) :: (real^'n) \<times> (real^'n)) \<bullet> k
      - (k \<bullet> ((Z *v (fst k - snd k), Z *v (snd k - fst k))
            :: (real^'n) \<times> (real^'n)))/2
    = R (fst k - snd k)" for k
  proof -
    have mvd: "Z *v (snd k - fst k) = - (Z *v (fst k - snd k))"
      by (simp add: matrix_vector_mult_diff_gen)
    have e: "fst (zh + k) - snd (zh + k)
        = (fst zh - snd zh) + (fst k - snd k)"
      by simp
    show ?thesis
      unfolding R_def e mvd
      by (simp add: inner_prod_def
          algebra_simps)
  qed
  have main: "((\<lambda>k::(real^'n)\<times>(real^'n). R (fst k - snd k) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
  proof (rule tendstoI)
    fix e :: real assume e: "0 < e"
    then have e4: "0 < e/4" by simp
    have evR: "\<forall>\<^sub>F h in at (0::real^'n). dist (R h / (norm h)\<^sup>2) 0 < e/4"
      by (rule tendstoD[OF Rlim e4])
    obtain \<delta> where d0: "0 < \<delta>"
      and dd: "\<And>h::real^'n. h \<noteq> 0 \<Longrightarrow> dist h 0 < \<delta>
          \<Longrightarrow> dist (R h / (norm h)\<^sup>2) 0 < e/4"
      using evR unfolding eventually_at by blast
    show "\<forall>\<^sub>F k in at (0::(real^'n)\<times>(real^'n)).
        dist (R (fst k - snd k) / (norm k)\<^sup>2) 0 < e"
      unfolding eventually_at
    proof (intro exI[of _ "\<delta>/2"] conjI)
      show "0 < \<delta>/2" using d0 by simp
      show "\<forall>k\<in>UNIV. k \<noteq> (0::(real^'n)\<times>(real^'n)) \<and> dist k 0 < \<delta>/2
          \<longrightarrow> dist (R (fst k - snd k) / (norm k)\<^sup>2) 0 < e"
      proof (intro ballI impI)
        fix k :: "(real^'n)\<times>(real^'n)"
        assume k: "k \<noteq> 0 \<and> dist k 0 < \<delta>/2"
        have knz: "k \<noteq> 0" using k by simp
        have kd: "norm k < \<delta>/2" using k by (simp add: dist_norm)
        have kpos: "0 < norm k" using knz by simp
        have ksq: "0 < (norm k)\<^sup>2" using kpos by simp
        show "dist (R (fst k - snd k) / (norm k)\<^sup>2) 0 < e"
        proof (cases "fst k - snd k = 0")
          case True
          then show ?thesis using R0 e by simp
        next
          case False
          have nf: "norm (fst k) \<le> norm k"
            using norm_fst_le[of "fst k" "snd k"] by simp
          have ns: "norm (snd k) \<le> norm k"
            using norm_snd_le[where x = "fst k" and y = "snd k"] by simp
          have nh: "norm (fst k - snd k) \<le> 2 * norm k"
          proof -
            have "norm (fst k - snd k) \<le> norm (fst k) + norm (snd k)"
              by (rule norm_triangle_ineq4)
            then show ?thesis using nf ns by linarith
          qed
          have hd: "dist (fst k - snd k) 0 < \<delta>"
            using nh kd by (simp add: dist_norm)
          have step: "dist (R (fst k - snd k) / (norm (fst k - snd k))\<^sup>2) 0
              < e/4"
            by (rule dd[OF False hd])
          have hpos: "0 < (norm (fst k - snd k))\<^sup>2" using False by simp
          have absR: "\<bar>R (fst k - snd k)\<bar>
              < (e/4) * (norm (fst k - snd k))\<^sup>2"
          proof -
            have "\<bar>R (fst k - snd k)\<bar> / (norm (fst k - snd k))\<^sup>2 < e/4"
              using step by (simp add: dist_real_def)
            then show ?thesis using hpos by (simp add: pos_divide_less_eq)
          qed
          have sq4: "(norm (fst k - snd k))\<^sup>2 \<le> 4 * (norm k)\<^sup>2"
          proof -
            have "(norm (fst k - snd k))\<^sup>2 \<le> (2 * norm k)\<^sup>2"
              by (rule power_mono[OF nh]) simp
            then show ?thesis by (simp add: power2_eq_square)
          qed
          have lt: "\<bar>R (fst k - snd k)\<bar> < e * (norm k)\<^sup>2"
          proof -
            have "(e/4) * (norm (fst k - snd k))\<^sup>2
                \<le> (e/4) * (4 * (norm k)\<^sup>2)"
              by (rule mult_left_mono[OF sq4]) (use e in linarith)
            then show ?thesis using absR by simp
          qed
          show ?thesis
            using lt ksq by (simp add: dist_real_def pos_divide_less_eq)
        qed
      qed
    qed
  qed
  show ?thesis unfolding num by (rule main)
qed

subsection \<open>Semiconvexity of the doubled functional, for a general penalty\<close>

text \<open>The Jensen/Alexandrov layer needs global semiconvexity of
  \<open>a(x) + b(y) - P(x - y)\<close>, i.e. \<open>P\<close> semiconcave (Hessian bounded above); a
  quadratic gets this for free, a globally quartic penalty does not, since
  its Hessian grows like \<open>\<beta>\<parallel>d\<parallel>\<^sup>2\<close>. For \<open>P\<close> semiconcave with constant
  \<open>\<kappa>\<close>, the identity
  \<open>-P(x-y) + \<kappa>\<parallel>z\<parallel>\<^sup>2 = [(\<kappa>/2)\<parallel>x-y\<parallel>\<^sup>2 - P(x-y)] + (\<kappa>/2)\<parallel>x+y\<parallel>\<^sup>2\<close> writes the
  functional as a sum of two convex pieces, composed with
  \<open>z \<mapsto> fst z - snd z\<close> and \<open>z \<mapsto> fst z + snd z\<close> respectively. For quadratic
  \<open>P\<close> the first bracket vanishes identically, collapsing to
  \<open>semiconvex_penalty\<close>.\<close>

lemma convex_on_prod_diff:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes g: "convex_on UNIV g"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a. g (fst z - snd z))"
proof (rule convex_onI)
  fix t :: real and x y :: "'a \<times> 'a"
  assume t: "0 < t" "t < 1"
  have L: "fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) - snd ((1 - t) *\<^sub>R x + t *\<^sub>R y)
      = (1 - t) *\<^sub>R (fst x - snd x) + t *\<^sub>R (fst y - snd y)"
    by (simp add: algebra_simps)
  show "g (fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) - snd ((1 - t) *\<^sub>R x + t *\<^sub>R y))
      \<le> (1 - t) * g (fst x - snd x) + t * g (fst y - snd y)"
    unfolding L
    by (rule convex_onD[OF g]) (use t in auto)
qed simp

lemma convex_on_prod_add:
  fixes g :: "'a::euclidean_space \<Rightarrow> real"
  assumes g: "convex_on UNIV g"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a. g (fst z + snd z))"
proof (rule convex_onI)
  fix t :: real and x y :: "'a \<times> 'a"
  assume t: "0 < t" "t < 1"
  have L: "fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) + snd ((1 - t) *\<^sub>R x + t *\<^sub>R y)
      = (1 - t) *\<^sub>R (fst x + snd x) + t *\<^sub>R (fst y + snd y)"
    by (simp add: algebra_simps)
  show "g (fst ((1 - t) *\<^sub>R x + t *\<^sub>R y) + snd ((1 - t) *\<^sub>R x + t *\<^sub>R y))
      \<le> (1 - t) * g (fst x + snd x) + t * g (fst y + snd y)"
    unfolding L
    by (rule convex_onD[OF g]) (use t in auto)
qed simp

theorem semiconvex_penalty_gen:
  fixes P :: "'a::euclidean_space \<Rightarrow> real"
  assumes k: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - P d)"
  shows "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      - P (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2)"
proof -
  have eq: "(\<lambda>z::'a \<times> 'a. - P (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a \<times> 'a.
          ((\<kappa>/2) * (norm (fst z - snd z))\<^sup>2 - P (fst z - snd z))
          + (\<kappa>/2) * (norm (fst z + snd z))\<^sup>2)"
  proof (rule ext)
    fix z :: "'a \<times> 'a"
    have d: "(norm (fst z - snd z))\<^sup>2
        = (norm (fst z))\<^sup>2 - 2*(fst z \<bullet> snd z) + (norm (snd z))\<^sup>2"
      by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
          inner_commute)
    have s: "(norm (fst z + snd z))\<^sup>2
        = (norm (fst z))\<^sup>2 + 2*(fst z \<bullet> snd z) + (norm (snd z))\<^sup>2"
      by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
          inner_commute)
    show "- P (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2
        = ((\<kappa>/2) * (norm (fst z - snd z))\<^sup>2 - P (fst z - snd z))
          + (\<kappa>/2) * (norm (fst z + snd z))\<^sup>2"
      unfolding norm_prod_sq d s by (simp add: algebra_simps)
  qed
  have c1: "convex_on UNIV (\<lambda>z::'a \<times> 'a.
      (\<kappa>/2) * (norm (fst z - snd z))\<^sup>2 - P (fst z - snd z))"
    by (rule convex_on_prod_diff[OF sc])
  have cn: "convex_on UNIV (\<lambda>x::'a. (\<kappa>/2) * (norm x)\<^sup>2)"
  proof -
    have k2: "0 \<le> \<kappa>/2" using k by simp
    have "convex_on UNIV (\<lambda>x::'a. (norm x)\<^sup>2)"
      by (rule convex_on_norm_sq[OF convex_UNIV])
    then show ?thesis by (rule convex_on_cmul[OF k2])
  qed
  have c2: "convex_on UNIV (\<lambda>z::'a \<times> 'a. (\<kappa>/2) * (norm (fst z + snd z))\<^sup>2)"
    by (rule convex_on_prod_add[OF cn])
  show ?thesis unfolding eq by (rule convex_on_add[OF c1 c2])
qed

subsection \<open>A concrete penalty: semiconcave, with a vanishing 2-jet at the origin\<close>

text \<open>\<open>semiconvex_penalty_gen\<close> reduces the question to exhibiting one
  penalty that is semiconcave with an explicit constant and has vanishing
  gradient and Hessian at \<open>0\<close>. The pure quartic fails semiconcavity;
  \<open>P(d) = (\<kappa>/2)\<parallel>d\<parallel>\<^sup>2 - \<kappa>(\<surd>(\<parallel>d\<parallel>\<^sup>2 + 1) - 1)\<close> has both properties.
  Semiconcavity is free since
  \<open>(\<kappa>/2)\<parallel>d\<parallel>\<^sup>2 - P(d) = \<kappa>(\<surd>(\<parallel>d\<parallel>\<^sup>2 + 1) - 1) = \<kappa>(\<parallel>(d, 1)\<parallel> - 1)\<close>, a norm
  composed with an affine map. The 2-jet at \<open>0\<close> vanishes because
  \<open>\<surd>(s+1) - 1 = s/(\<surd>(s+1)+1)\<close>, so \<open>P(h)/\<parallel>h\<parallel>\<^sup>2 \<rightarrow> 0\<close>: near \<open>0\<close> the penalty
  is \<open>\<approx> (\<kappa>/8)\<parallel>d\<parallel>\<^sup>4\<close>, while far out it grows quadratically.\<close>

definition soft_pen :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real" where
  "soft_pen \<kappa> d = (\<kappa>/2) * (norm d)\<^sup>2 - \<kappa> * (sqrt ((norm d)\<^sup>2 + 1) - 1)"

lemma convex_on_norm_lift:
  fixes dummy :: "'a::real_normed_vector"
  shows "convex_on UNIV (\<lambda>d::'a. norm ((d, 1) :: 'a \<times> real))"
proof (rule convex_onI)
  fix t :: real and x y :: 'a
  assume t: "0 < t" "t < 1"
  have L: "(((1 - t) *\<^sub>R x + t *\<^sub>R y, 1) :: 'a \<times> real)
      = (1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real) + t *\<^sub>R ((y, 1) :: 'a \<times> real)"
    by simp
  have n1: "norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real))
      = (1 - t) * norm ((x, 1) :: 'a \<times> real)"
  proof -
    have "norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real))
        = \<bar>1 - t\<bar> * norm ((x, 1) :: 'a \<times> real)"
      by (rule norm_scaleR)
    moreover have "\<bar>1 - t\<bar> = 1 - t" using t by simp
    ultimately show ?thesis by simp
  qed
  have n2: "norm (t *\<^sub>R ((y, 1) :: 'a \<times> real))
      = t * norm ((y, 1) :: 'a \<times> real)"
  proof -
    have "norm (t *\<^sub>R ((y, 1) :: 'a \<times> real))
        = \<bar>t\<bar> * norm ((y, 1) :: 'a \<times> real)"
      by (rule norm_scaleR)
    moreover have "\<bar>t\<bar> = t" using t by simp
    ultimately show ?thesis by simp
  qed
  have "norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real) + t *\<^sub>R ((y, 1) :: 'a \<times> real))
      \<le> norm ((1 - t) *\<^sub>R ((x, 1) :: 'a \<times> real))
        + norm (t *\<^sub>R ((y, 1) :: 'a \<times> real))"
    by (rule norm_triangle_ineq)
  also have "\<dots> = (1 - t) * norm ((x, 1) :: 'a \<times> real)
        + t * norm ((y, 1) :: 'a \<times> real)"
    unfolding n1 n2 ..
  finally show "norm (((1 - t) *\<^sub>R x + t *\<^sub>R y, 1) :: 'a \<times> real)
      \<le> (1 - t) * norm ((x, 1) :: 'a \<times> real)
        + t * norm ((y, 1) :: 'a \<times> real)"
    unfolding L .
qed simp

lemma soft_pen_gap:
  fixes d :: "real^'n::finite"
  shows "(\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d
      = \<kappa> * norm ((d, 1) :: (real^'n) \<times> real) - \<kappa>"
proof -
  have n: "norm ((d, 1) :: (real^'n) \<times> real) = sqrt ((norm d)\<^sup>2 + 1)"
    by (simp add: norm_Pair)
  show ?thesis unfolding soft_pen_def n by (simp add: algebra_simps)
qed

theorem soft_pen_semiconcave:
  fixes \<kappa> :: real
  assumes k: "0 \<le> \<kappa>"
  shows "convex_on UNIV (\<lambda>d::real^'n::finite. (\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d)"
proof -
  have e: "(\<lambda>d::real^'n. (\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d)
      = (\<lambda>d::real^'n. \<kappa> * norm ((d, 1) :: (real^'n) \<times> real) + (- \<kappa>))"
  proof (rule ext)
    fix d :: "real^'n"
    show "(\<kappa>/2) * (norm d)\<^sup>2 - soft_pen \<kappa> d
        = \<kappa> * norm ((d, 1) :: (real^'n) \<times> real) + (- \<kappa>)"
      using soft_pen_gap[of \<kappa> d] by simp
  qed
  have c1: "convex_on UNIV (\<lambda>d::real^'n. norm ((d, 1) :: (real^'n) \<times> real))"
    by (rule convex_on_norm_lift)
  have c2: "convex_on UNIV (\<lambda>d::real^'n. \<kappa> * norm ((d, 1) :: (real^'n) \<times> real))"
    by (rule convex_on_cmul[OF k c1])
  have c3: "convex_on UNIV (\<lambda>d::real^'n. - \<kappa>)"
    by (simp add: convex_on_const)
  show ?thesis unfolding e by (rule convex_on_add[OF c2 c3])
qed

lemma div_mul_div_cancel_aux:
  fixes k s r :: real
  assumes s: "s \<noteq> 0"
  shows "k * (s / r) / s = k / r"
  using s by (simp add: field_simps)

lemma soft_pen_quotient:
  fixes h :: "real^'n::finite"
  assumes h: "h \<noteq> 0"
  shows "soft_pen \<kappa> h / (norm h)\<^sup>2
      = \<kappa>/2 - \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1)"
proof -
  have s0: "0 < (norm h)\<^sup>2" using h by simp
  have r: "0 < sqrt ((norm h)\<^sup>2 + 1) + 1"
  proof -
    have "0 \<le> sqrt ((norm h)\<^sup>2 + 1)" by simp
    then show ?thesis by linarith
  qed
  have sq: "sqrt ((norm h)\<^sup>2 + 1) * sqrt ((norm h)\<^sup>2 + 1) = (norm h)\<^sup>2 + 1"
    using s0 by simp
  have id: "sqrt ((norm h)\<^sup>2 + 1) - 1
      = (norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1)"
  proof -
    have "(sqrt ((norm h)\<^sup>2 + 1) - 1) * (sqrt ((norm h)\<^sup>2 + 1) + 1)
        = (norm h)\<^sup>2"
      using sq by (simp add: algebra_simps)
    then show ?thesis using r by (simp add: field_simps)
  qed
  have "soft_pen \<kappa> h / (norm h)\<^sup>2
      = ((\<kappa>/2) * (norm h)\<^sup>2
          - \<kappa> * ((norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1))) / (norm h)\<^sup>2"
    unfolding soft_pen_def id ..
  also have "\<dots> = ((\<kappa>/2) * (norm h)\<^sup>2) / (norm h)\<^sup>2
      - (\<kappa> * ((norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1))) / (norm h)\<^sup>2"
    by (rule diff_divide_distrib)
  also have "((\<kappa>/2) * (norm h)\<^sup>2) / (norm h)\<^sup>2 = \<kappa>/2"
    using s0 by simp
  also have "(\<kappa> * ((norm h)\<^sup>2 / (sqrt ((norm h)\<^sup>2 + 1) + 1))) / (norm h)\<^sup>2
      = \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1)"
    by (rule div_mul_div_cancel_aux) (use s0 in linarith)
  finally show ?thesis .
qed

theorem soft_pen_vanishing_jet_at_zero:
  fixes \<kappa> :: real
  shows "((\<lambda>h::real^'n::finite. (soft_pen \<kappa> (0 + h) - soft_pen \<kappa> 0)
      / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have z: "soft_pen \<kappa> 0 = 0" by (simp add: soft_pen_def)
  have nz0: "\<forall>\<^sub>F h in at (0::real^'n). h \<noteq> 0"
    by (simp add: eventually_at_filter)
  have ev: "\<forall>\<^sub>F h in at (0::real^'n).
      \<kappa>/2 - \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1)
        = (soft_pen \<kappa> (0 + h) - soft_pen \<kappa> 0) / (norm h)\<^sup>2"
    using nz0
  proof eventually_elim
    case (elim h)
    then show ?case unfolding z using soft_pen_quotient[OF elim] by simp
  qed
  have lim: "((\<lambda>h::real^'n. \<kappa>/2 - \<kappa> / (sqrt ((norm h)\<^sup>2 + 1) + 1))
      \<longlongrightarrow> \<kappa>/2 - \<kappa> / (sqrt ((norm (0::real^'n))\<^sup>2 + 1) + 1)) (at 0)"
    by (intro tendsto_intros) simp
  have val: "\<kappa>/2 - \<kappa> / (sqrt ((norm (0::real^'n))\<^sup>2 + 1) + 1) = 0"
    by simp
  show ?thesis
    by (rule Lim_transform_eventually[OF lim[unfolded val] ev])
qed

subsection \<open>Second-order expansion of the square root\<close>

text \<open>\<open>soft_pen\<close>'s jet at a general \<open>d\<close> needs an exact, not asymptotic,
  expansion. Writing \<open>S = \<surd>(u+\<Delta>)\<close> and \<open>R = \<surd>u\<close>, the conjugate identity
  gives \<open>S - R = \<Delta>/(S+R)\<close>, and identically
  \<open>S - R - \<Delta>/(2R) = -\<Delta>\<^sup>2/(2R(S+R)\<^sup>2)\<close>. So the second-order remainder is a
  quotient, and \<open>o(\<Delta>\<^sup>2)\<close> is just continuity of
  \<open>\<Delta> \<mapsto> 1/(2R(S+R)\<^sup>2)\<close> at \<open>\<Delta> = 0\<close>, where it equals \<open>1/(8R\<^sup>3)\<close>, the
  Taylor coefficient.\<close>

lemma sqrt_diff_exact:
  fixes u D :: real
  assumes uD: "0 \<le> u + D" and u: "0 \<le> u"
    and pos: "0 < sqrt (u + D) + sqrt u"
  shows "sqrt (u + D) - sqrt u = D / (sqrt (u + D) + sqrt u)"
proof -
  have s1: "sqrt (u + D) * sqrt (u + D) = u + D" using uD by simp
  have s2: "sqrt u * sqrt u = u" using u by simp
  have prod: "(sqrt (u + D) - sqrt u) * (sqrt (u + D) + sqrt u) = D"
    using s1 s2 by (simp add: algebra_simps)
  show ?thesis
    using pos prod by (simp add: nonzero_eq_divide_eq)
qed

text \<open>The same identity without the quotient, holding for every \<open>\<Delta>\<close>
  including \<open>0\<close>. The algebraic heart: \<open>(S+R)\<^sup>2 - \<Delta> = 2R(S+R)\<close>, whence
  \<open>\<Delta>/(2R) - \<Delta>\<^sup>2/(2R(S+R)\<^sup>2) = \<Delta>/(S+R) = S - R\<close>.\<close>

lemma sqrt_rhs_aux:
  fixes D R T :: real
  assumes R: "R \<noteq> 0" and T: "T \<noteq> 0" and key: "T\<^sup>2 - D = 2 * R * T"
  shows "D / (2 * R) - D\<^sup>2 / (2 * R * T\<^sup>2) = D / T"
proof -
  have n: "D * T\<^sup>2 - D\<^sup>2 = D * (2 * R * T)"
  proof -
    have "D * T\<^sup>2 - D\<^sup>2 = D * (T\<^sup>2 - D)"
      by (simp add: algebra_simps power2_eq_square)
    also have "\<dots> = D * (2 * R * T)" unfolding key ..
    finally show ?thesis .
  qed
  have "D / (2 * R) - D\<^sup>2 / (2 * R * T\<^sup>2) = (D * T\<^sup>2 - D\<^sup>2) / (2 * R * T\<^sup>2)"
    using R T by (simp add: field_simps)
  also have "\<dots> = (D * (2 * R * T)) / (2 * R * T\<^sup>2)" unfolding n ..
  also have "\<dots> = D / T"
    using R T by (simp add: power2_eq_square field_simps)
  finally show ?thesis .
qed

theorem sqrt_second_order_exact:
  fixes u D :: real
  assumes u: "0 < u" and uD: "0 \<le> u + D"
  shows "sqrt (u + D) - sqrt u
      = D / (2 * sqrt u)
        - D\<^sup>2 / (2 * sqrt u * (sqrt (u + D) + sqrt u)\<^sup>2)"
proof -
  have R: "0 < sqrt u" using u by simp
  have S: "0 \<le> sqrt (u + D)" using uD by simp
  have SR: "0 < sqrt (u + D) + sqrt u" using R S by linarith
  have s1: "sqrt (u + D) * sqrt (u + D) = u + D" using uD by simp
  have s2: "sqrt u * sqrt u = u" using u by simp
  have key: "(sqrt (u + D) + sqrt u)\<^sup>2 - D
      = 2 * sqrt u * (sqrt (u + D) + sqrt u)"
    using s1 s2 by (simp add: power2_eq_square algebra_simps)
  have e: "sqrt (u + D) - sqrt u = D / (sqrt (u + D) + sqrt u)"
    by (rule sqrt_diff_exact) (use uD u SR in linarith)+
  have rhs: "D / (2 * sqrt u)
        - D\<^sup>2 / (2 * sqrt u * (sqrt (u + D) + sqrt u)\<^sup>2)
      = D / (sqrt (u + D) + sqrt u)"
    by (rule sqrt_rhs_aux) (use R SR key in auto)
  show ?thesis unfolding e rhs ..
qed

text \<open>\<open>soft_pen\<close>'s increment expands exactly: the quadratic part expands
  exactly, and the square-root part follows from \<open>sqrt_second_order_exact\<close>
  at \<open>u = \<parallel>d\<parallel>\<^sup>2 + 1\<close>, \<open>\<Delta> = 2(d \<bullet> h) + h \<bullet> h\<close>. The gradient is
  \<open>\<kappa>(1 - 1/R) d\<close> and the Hessian form is
  \<open>\<kappa>(1 - 1/R)(h \<bullet> h) + \<kappa>(d \<bullet> h)\<^sup>2/R\<^sup>3\<close>, both vanishing at \<open>d = 0\<close> where
  \<open>R = 1\<close>.\<close>

theorem soft_pen_expand:
  fixes d h :: "real^'n::finite"
  shows "soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      = (\<kappa>/2) * (2*(d \<bullet> h) + (h \<bullet> h))
        - \<kappa> * ((2*(d \<bullet> h) + (h \<bullet> h)) / (2 * sqrt ((norm d)\<^sup>2 + 1))
            - (2*(d \<bullet> h) + (h \<bullet> h))\<^sup>2
              / (2 * sqrt ((norm d)\<^sup>2 + 1)
                  * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
                     + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))"
proof -
  have u: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have D: "(norm (d + h))\<^sup>2 = (norm d)\<^sup>2 + (2*(d \<bullet> h) + (h \<bullet> h))"
    by (simp add: power2_norm_eq_inner
        inner_commute algebra_simps)
  have uD: "0 \<le> ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))"
  proof -
    have e: "((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))
        = (norm (d + h))\<^sup>2 + 1"
      using D by simp
    show ?thesis unfolding e
      by (rule add_nonneg_nonneg[OF zero_le_power2 zero_le_one])
  qed
  have ex: "sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        - sqrt ((norm d)\<^sup>2 + 1)
      = (2*(d \<bullet> h) + (h \<bullet> h)) / (2 * sqrt ((norm d)\<^sup>2 + 1))
        - (2*(d \<bullet> h) + (h \<bullet> h))\<^sup>2
          / (2 * sqrt ((norm d)\<^sup>2 + 1)
              * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
                 + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)"
    by (rule sqrt_second_order_exact[OF u uD])
  have split: "soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      = (\<kappa>/2) * (2*(d \<bullet> h) + (h \<bullet> h))
        - \<kappa> * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
               - sqrt ((norm d)\<^sup>2 + 1))"
    unfolding soft_pen_def using D by (simp add: algebra_simps)
  show ?thesis unfolding split ex ..
qed

text \<open>Collecting the expansion into gradient + Hessian + remainder: with
  \<open>a = d \<bullet> h\<close>, \<open>b = h \<bullet> h\<close>, \<open>\<Delta> = 2a + b\<close> and \<open>R = \<surd>(\<parallel>d\<parallel>\<^sup>2+1)\<close>,
  \<open>(\<kappa>/2)\<Delta> - \<kappa>\<Delta>/(2R) = \<kappa>(1 - 1/R) a + (\<kappa>/2)(1 - 1/R) b\<close>, an identity
  giving the gradient and half the Hessian term exactly; the remainder is
  the two quotient terms.\<close>

lemma soft_pen_rem_aux:
  fixes k R a b W :: real
  assumes R: "R \<noteq> 0"
  shows "(k/2) * (2*a + b) - k * ((2*a + b) / (2*R) - W)
        - k * (1 - 1/R) * a
        - (k * (1 - 1/R) * b + k * a\<^sup>2 / R^3) / 2
      = k * W - k * a\<^sup>2 / (2 * R^3)"
  using R by (simp add: field_simps)

theorem soft_pen_rem:
  fixes d h :: "real^'n::finite"
  shows "soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
        - \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)
        - (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
            + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) / 2
      = \<kappa> * ((2*(d \<bullet> h) + (h \<bullet> h))\<^sup>2
              / (2 * sqrt ((norm d)\<^sup>2 + 1)
                  * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
                     + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
        - \<kappa> * (d \<bullet> h)\<^sup>2 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)"
proof -
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have R: "sqrt ((norm d)\<^sup>2 + 1) \<noteq> 0" using up by simp
  show ?thesis
    unfolding soft_pen_expand
    by (rule soft_pen_rem_aux[OF R])
qed

text \<open>One input to the remainder limit: \<open>(d \<bullet> h)\<^sup>2/\<parallel>h\<parallel>\<^sup>2\<close> is bounded,
  uniformly in \<open>h\<close>, by \<open>\<parallel>d\<parallel>\<^sup>2\<close> (Cauchy-Schwarz squared), enabling
  \<open>Lim_null_comparison\<close>.\<close>

lemma inner_sq_over_norm_sq_le:
  fixes d h :: "real^'n::finite"
  shows "(d \<bullet> h)\<^sup>2 \<le> (norm d)\<^sup>2 * (norm h)\<^sup>2"
proof -
  have cs: "\<bar>d \<bullet> h\<bar> \<le> norm d * norm h"
    by (rule Cauchy_Schwarz_ineq2)
  have "(\<bar>d \<bullet> h\<bar>)\<^sup>2 \<le> (norm d * norm h)\<^sup>2"
    by (rule power_mono[OF cs]) simp
  then show ?thesis
    by (simp add: power_mult_distrib)
qed

corollary inner_sq_quotient_bounded:
  fixes d h :: "real^'n::finite"
  assumes h: "h \<noteq> 0"
  shows "(d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2 \<le> (norm d)\<^sup>2"
proof -
  have b: "0 < (norm h)\<^sup>2" using h by simp
  show ?thesis
    using inner_sq_over_norm_sq_le[of d h] b
    by (simp add: pos_divide_le_eq)
qed

text \<open>The other input: the denominator \<open>T h = \<surd>(u + \<Delta> h) + R\<close> tends to
  \<open>2R\<close> as \<open>h \<rightarrow> 0\<close>, so \<open>2/(R T\<^sup>2) - 1/(2R\<^sup>3)\<close> vanishes, since
  \<open>R(2R)\<^sup>2 = 4R\<^sup>3\<close>.\<close>

lemma soft_pen_T_tendsto:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1))
      \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
proof -
  have "((\<lambda>h::real^'n. ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
      \<longlongrightarrow> ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> (0::real^'n)) + ((0::real^'n) \<bullet> 0)))
      (at 0)"
    by (intro tendsto_intros)
  then have a: "((\<lambda>h::real^'n. ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
      \<longlongrightarrow> (norm d)\<^sup>2 + 1) (at 0)"
    by simp
  have b: "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))))
      \<longlongrightarrow> sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule tendsto_real_sqrt[OF a])
  have "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1))
      \<longlongrightarrow> sqrt ((norm d)\<^sup>2 + 1) + sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule tendsto_add[OF b tendsto_const])
  then show ?thesis by simp
qed

text \<open>The bracket itself vanishes: \<open>T h \<rightarrow> 2R\<close> gives \<open>R T h\<^sup>2 \<rightarrow> 4R\<^sup>3\<close>, so
  \<open>2/(R T h\<^sup>2) \<rightarrow> 1/(2R\<^sup>3)\<close>, the constant subtracted.\<close>

lemma soft_pen_bracket_tendsto:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. 2 / (sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
        - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)) \<longlongrightarrow> 0) (at 0)"
proof -
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" using up by simp
  have Tl: "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1)) \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule soft_pen_T_tendsto)
  have Dl: "((\<lambda>h::real^'n. sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      \<longlongrightarrow> sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2) (at 0)"
    by (intro tendsto_intros Tl)
  have dnz: "sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2 \<noteq> 0"
    using Rp by (simp add: power2_eq_square)
  have Ql: "((\<lambda>h::real^'n. 2 / (sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
      \<longlongrightarrow> 2 / (sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)) (at 0)"
    by (rule tendsto_divide[OF tendsto_const Dl dnz])
  have val: "2 / (sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      = 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)"
  proof -
    have e: "sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2
        = 4 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3"
      by (simp add: power2_eq_square power3_eq_cube)
    show ?thesis unfolding e using Rp by (simp add: field_simps)
  qed
  have "((\<lambda>h::real^'n. 2 / (sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3))
      \<longlongrightarrow> 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)
        - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)) (at 0)"
    by (rule tendsto_diff[OF Ql[unfolded val] tendsto_const])
  then show ?thesis by simp
qed

text \<open>The second summand of the remainder quotient: numerator \<open>\<rightarrow> 0\<close> over
  denominator \<open>\<rightarrow> 8R\<^sup>3 \<noteq> 0\<close>.\<close>

lemma soft_pen_second_summand_tendsto:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))
      / (2 * sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
proof -
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" using up by simp
  have Nl: "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))) \<longlongrightarrow> 0) (at 0)"
  proof -
    have "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h)))
        \<longlongrightarrow> \<kappa> * (4*(d \<bullet> (0::real^'n)) + ((0::real^'n) \<bullet> 0))) (at 0)"
      by (intro tendsto_intros)
    then show ?thesis by simp
  qed
  have Tl: "((\<lambda>h::real^'n. sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
        + sqrt ((norm d)\<^sup>2 + 1)) \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1)) (at 0)"
    by (rule soft_pen_T_tendsto)
  have Dl: "((\<lambda>h::real^'n. 2 * sqrt ((norm d)\<^sup>2 + 1)
        * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
           + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      \<longlongrightarrow> 2 * sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2) (at 0)"
    by (intro tendsto_intros Tl)
  have dnz: "2 * sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2 \<noteq> 0"
    using Rp by (simp add: power2_eq_square)
  have "((\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))
      / (2 * sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
      \<longlongrightarrow> 0 / (2 * sqrt ((norm d)\<^sup>2 + 1) * (2 * sqrt ((norm d)\<^sup>2 + 1))\<^sup>2))
      (at 0)"
    by (rule tendsto_divide[OF Nl Dl dnz])
  then show ?thesis by simp
qed

text \<open>The remainder quotient splits into a bounded factor times a vanishing
  bracket, plus a vanishing summand, via \<open>\<Delta>\<^sup>2 = 4a\<^sup>2 + 4ab + b\<^sup>2\<close>:
  \<open>4a\<^sup>2\<close> carries the bounded factor, and \<open>(4ab + b\<^sup>2)/b\<close> is the second
  summand.\<close>

lemma rem_split_aux:
  fixes k R T a b :: real
  assumes R: "R \<noteq> 0" and T: "T \<noteq> 0" and b: "b \<noteq> 0"
  shows "(k * ((2*a + b)\<^sup>2 / (2 * R * T\<^sup>2)) - k * a\<^sup>2 / (2 * R^3)) / b
      = (a\<^sup>2 / b) * (k * (2/(R*T\<^sup>2) - 1/(2*R^3)))
        + k * (4*a + b) / (2*R*T\<^sup>2)"
  using R T b
  by (simp add: field_simps power2_eq_square power3_eq_cube)

text \<open>The jet assembles the analysis above via \<open>soft_pen_rem\<close> and
  \<open>rem_split_aux\<close>, killing the first summand by \<open>Lim_null_comparison\<close> and
  adding the second. Stated with the Hessian as a quadratic form;
  converting it to the matrix \<open>\<kappa>(1 - 1/R) I + (\<kappa>/R\<^sup>3) d d\<^sup>T\<close> is a separate
  step.\<close>

theorem soft_pen_jet_form:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. (soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      - \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)
      - (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
          + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) / 2) / (norm h)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)"
proof -
  let ?R = "sqrt ((norm d)\<^sup>2 + 1)"
  let ?T = "\<lambda>h::real^'n.
      sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))) + sqrt ((norm d)\<^sup>2 + 1)"
  let ?Br = "\<lambda>h::real^'n.
      2 / (sqrt ((norm d)\<^sup>2 + 1)
            * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
               + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)
      - 1 / (2 * (sqrt ((norm d)\<^sup>2 + 1)) ^ 3)"
  let ?Sc = "\<lambda>h::real^'n. \<kappa> * (4*(d \<bullet> h) + (h \<bullet> h))
      / (2 * sqrt ((norm d)\<^sup>2 + 1)
          * (sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))
             + sqrt ((norm d)\<^sup>2 + 1))\<^sup>2)"
  have up: "0 < (norm d)\<^sup>2 + 1"
    by (rule add_nonneg_pos[OF zero_le_power2 zero_less_one])
  have Rp: "0 < ?R" using up by simp
  have Rnz: "?R \<noteq> 0" using Rp by linarith
  have uDh: "0 \<le> ((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h))" for h :: "real^'n"
  proof -
    have D: "(norm (d + h))\<^sup>2 = (norm d)\<^sup>2 + (2*(d \<bullet> h) + (h \<bullet> h))"
      by (simp add: power2_norm_eq_inner
          inner_commute algebra_simps)
    have e: "((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)) = (norm (d + h))\<^sup>2 + 1"
      using D by simp
    show ?thesis unfolding e
      by (rule add_nonneg_nonneg[OF zero_le_power2 zero_le_one])
  qed
  have Tnz: "?T h \<noteq> 0" for h :: "real^'n"
  proof -
    have "0 \<le> sqrt (((norm d)\<^sup>2 + 1) + (2*(d \<bullet> h) + (h \<bullet> h)))"
      using uDh[of h] by simp
    then show ?thesis using Rp by linarith
  qed
  have nz0: "\<forall>\<^sub>F h in at (0::real^'n). h \<noteq> 0"
    by (simp add: eventually_at_filter)
  have gl: "((\<lambda>h::real^'n. (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>) \<longlongrightarrow> 0) (at 0)"
  proof -
    have "((\<lambda>h::real^'n. \<kappa> * ?Br h) \<longlongrightarrow> \<kappa> * 0) (at 0)"
      by (rule tendsto_mult[OF tendsto_const soft_pen_bracket_tendsto])
    then have "((\<lambda>h::real^'n. \<bar>\<kappa> * ?Br h\<bar>) \<longlongrightarrow> \<bar>\<kappa> * 0\<bar>) (at 0)"
      by (rule tendsto_rabs)
    then have "((\<lambda>h::real^'n. (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>)
        \<longlongrightarrow> (norm d)\<^sup>2 * \<bar>\<kappa> * 0\<bar>) (at 0)"
      by (rule tendsto_mult[OF tendsto_const])
    then show ?thesis by simp
  qed
  have cmp: "\<forall>\<^sub>F h in at (0::real^'n).
      norm (((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h))
        \<le> (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>"
    using nz0
  proof eventually_elim
    case (elim h)
    have nn: "0 \<le> (d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2" by simp
    have bd: "(d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2 \<le> (norm d)\<^sup>2"
      by (rule inner_sq_quotient_bounded[OF elim])
    have "norm (((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h))
        = ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * \<bar>\<kappa> * ?Br h\<bar>"
      using nn by (simp add: abs_mult)
    also have "\<dots> \<le> (norm d)\<^sup>2 * \<bar>\<kappa> * ?Br h\<bar>"
      by (rule mult_right_mono[OF bd]) simp
    finally show ?case .
  qed
  have first: "((\<lambda>h::real^'n. ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h))
      \<longlongrightarrow> 0) (at 0)"
    by (rule Lim_null_comparison[OF cmp gl])
  have second: "((\<lambda>h::real^'n. ?Sc h) \<longlongrightarrow> 0) (at 0)"
    by (rule soft_pen_second_summand_tendsto)
  have sum0: "((\<lambda>h::real^'n.
      ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h) + ?Sc h) \<longlongrightarrow> 0) (at 0)"
    using tendsto_add[OF first second] by simp
  have ev: "\<forall>\<^sub>F h in at (0::real^'n).
      ((d \<bullet> h)\<^sup>2 / (norm h)\<^sup>2) * (\<kappa> * ?Br h) + ?Sc h
      = (soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
          - \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)
          - (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
              + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) / 2)
        / (norm h)\<^sup>2"
    using nz0
  proof eventually_elim
    case (elim h)
    then have bnz: "h \<bullet> h \<noteq> 0" by simp
    have nb: "(norm h)\<^sup>2 = h \<bullet> h" by (simp add: power2_norm_eq_inner)
    show ?case
      unfolding soft_pen_rem nb
      by (rule rem_split_aux[symmetric, OF Rnz Tnz bnz])
  qed
  show ?thesis by (rule Lim_transform_eventually[OF sum0 ev])
qed

subsection \<open>The soft penalty's Hessian as a matrix\<close>

text \<open>The chain consumes \<open>h \<bullet> (Z *v h)\<close> as a matrix,
  \<open>Z = \<kappa>(1 - 1/R) I + (\<kappa>/R\<^sup>3) d d\<^sup>T\<close>; symmetry, needed by the general
  \<open>psd\<close> chain but not by the quadratic case where \<open>Z = \<alpha> I\<close> is symmetric
  for free, is an entrywise computation.\<close>

text \<open>\<open>outer_prod\<close> lives in @{theory Relative_Arbitrage.Curvature_Operator}.\<close>

definition soft_hess :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real^'n^'n" where
  "soft_hess \<kappa> d = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R mat 1
      + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) *\<^sub>R outer_prod d d"

lemma soft_hess_entry:
  fixes d :: "real^'n::finite"
  shows "soft_hess \<kappa> d $ i $ j
      = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) * (if i = j then 1 else 0)
        + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) * (d $ i * d $ j)"
  by (simp add: soft_hess_def mat_def outer_prod_def)

lemma soft_hess_sym:
  fixes d :: "real^'n::finite"
  shows "transpose (soft_hess \<kappa> d) = soft_hess \<kappa> d"
proof -
  have "transpose (soft_hess \<kappa> d) $ i $ j = soft_hess \<kappa> d $ i $ j" for i j
  proof -
    have "transpose (soft_hess \<kappa> d) $ i $ j = soft_hess \<kappa> d $ j $ i"
      by (simp add: transpose_def)
    also have "\<dots> = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)))
            * (if j = i then 1 else 0)
          + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) * (d $ j * d $ i)"
      by (rule soft_hess_entry)
    also have "\<dots> = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)))
            * (if i = j then 1 else 0)
          + (\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3) * (d $ i * d $ j)"
      by (simp add: mult.commute eq_commute)
    also have "\<dots> = soft_hess \<kappa> d $ i $ j"
      by (rule soft_hess_entry[symmetric])
    finally show ?thesis .
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

lemma soft_hess_quadform:
  fixes d h :: "real^'n::finite"
  shows "h \<bullet> (soft_hess \<kappa> d *v h)
      = \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (h \<bullet> h)
        + \<kappa> * (d \<bullet> h)\<^sup>2 / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3"
proof -
  let ?A = "\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
  let ?B = "\<kappa> / (sqrt ((norm d)\<^sup>2 + 1)) ^ 3"
  have s1: "(\<Sum>j\<in>UNIV. ?A * (h $ i * ((if i = j then 1 else 0) * h $ j)))
      = ?A * (h $ i * h $ i)" for i
  proof -
    have "(\<Sum>j\<in>UNIV. ?A * (h $ i * ((if i = j then 1 else 0) * h $ j)))
        = (\<Sum>j\<in>UNIV. if j = i then ?A * (h $ i * h $ j) else 0)"
      by (rule sum.cong) auto
    also have "\<dots> = ?A * (h $ i * h $ i)" by simp
    finally show ?thesis .
  qed
  have "h \<bullet> (soft_hess \<kappa> d *v h)
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. h $ i * (soft_hess \<kappa> d $ i $ j * h $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
        ?A * (h $ i * ((if i = j then 1 else 0) * h $ j))
      + ?B * ((h $ i * d $ i) * (d $ j * h $ j)))"
    by (simp add: soft_hess_entry algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV.
          ?A * (h $ i * ((if i = j then 1 else 0) * h $ j)))
      + (\<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j))))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>i\<in>UNIV. ?A * (h $ i * h $ i))
      + (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j)))"
    by (simp add: s1 sum.distrib)
  also have "(\<Sum>i\<in>UNIV. ?A * (h $ i * h $ i)) = ?A * (h \<bullet> h)"
    by (simp add: inner_vec_def sum_distrib_left)
  also have "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j)))
      = ?B * ((\<Sum>i\<in>UNIV. h $ i * d $ i) * (\<Sum>j\<in>UNIV. d $ j * h $ j))"
  proof -
    have a: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. ?B * ((h $ i * d $ i) * (d $ j * h $ j)))
        = ?B * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (h $ i * d $ i) * (d $ j * h $ j))"
      by (simp add: sum_distrib_left)
    have b: "(\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (h $ i * d $ i) * (d $ j * h $ j))
        = (\<Sum>i\<in>UNIV. h $ i * d $ i) * (\<Sum>j\<in>UNIV. d $ j * h $ j)"
      by (rule sum_product[symmetric])
    show ?thesis unfolding a b ..
  qed
  also have "(\<Sum>i\<in>UNIV. h $ i * d $ i) = d \<bullet> h"
    by (simp add: inner_vec_def mult.commute)
  also have "(\<Sum>j\<in>UNIV. d $ j * h $ j) = d \<bullet> h"
    by (simp add: inner_vec_def)
  finally show ?thesis
    by (simp add: power2_eq_square)
qed

subsection \<open>The gradient field of \<open>soft_pen\<close>, and the two uniform bounds\<close>

text \<open>\<open>soft_pen_jet_form\<close> writes the Hessian as a quadratic expression,
  matched to \<open>soft_hess\<close> by \<open>soft_hess_quadform\<close>, with the gradient
  packaged as \<open>soft_grad\<close>. Writing \<open>R = \<surd>(\<parallel>d\<parallel>\<^sup>2+1) \<ge> 1\<close>: the first
  summand lies in \<open>[0, \<kappa>\<parallel>z\<parallel>\<^sup>2]\<close>, and Cauchy-Schwarz bounds the second by
  \<open>\<kappa>\<parallel>z\<parallel>\<^sup>2\<close>, so the quadratic form is bounded by \<open>2\<kappa>\<parallel>z\<parallel>\<^sup>2\<close>, uniformly in
  \<open>d\<close>.\<close>

definition soft_grad :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real^'n" where
  "soft_grad \<kappa> d = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R d"

lemma soft_grad_inner:
  fixes d h :: "real^'n::finite"
  shows "soft_grad \<kappa> d \<bullet> h = \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * (d \<bullet> h)"
  unfolding soft_grad_def by simp

theorem soft_pen_jet_field:
  fixes d :: "real^'n::finite"
  shows "((\<lambda>h::real^'n. (soft_pen \<kappa> (d + h) - soft_pen \<kappa> d
      - soft_grad \<kappa> d \<bullet> h - (h \<bullet> (soft_hess \<kappa> d *v h))/2) / (norm h)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)"
  using soft_pen_jet_form[where \<kappa> = \<kappa> and d = d]
  unfolding soft_grad_inner soft_hess_quadform .

lemma sqrt_norm_sq_add_one_ge_one:
  fixes d :: "real^'n::finite"
  shows "1 \<le> sqrt ((norm d)\<^sup>2 + 1)"
proof -
  have "(1::real) = sqrt 1" by simp
  also have "sqrt (1::real) \<le> sqrt ((norm d)\<^sup>2 + 1)"
    by (rule real_sqrt_le_mono) simp
  finally show ?thesis .
qed

lemma soft_hess_quadform_bounds:
  fixes d z :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "0 \<le> z \<bullet> (soft_hess \<kappa> d *v z)"
    and "z \<bullet> (soft_hess \<kappa> d *v z) \<le> (2*\<kappa>) * (norm z)\<^sup>2"
proof -
  let ?R = "sqrt ((norm d)\<^sup>2 + 1)"
  have R1: "1 \<le> ?R" by (rule sqrt_norm_sq_add_one_ge_one)
  have Rp: "0 < ?R" using R1 by linarith
  have inv: "0 < 1 / ?R" using Rp by simp
  have invle: "1 / ?R \<le> 1" using R1 Rp by (simp add: divide_le_eq_1)
  have A0: "0 \<le> \<kappa> * (1 - 1 / ?R)"
    by (rule mult_nonneg_nonneg[OF k]) (use invle in linarith)
  have A1: "\<kappa> * (1 - 1 / ?R) \<le> \<kappa>"
    using mult_left_mono[OF _ k, of "1 - 1/?R" 1] inv by simp
  have zz: "z \<bullet> z = (norm z)\<^sup>2" by (simp add: power2_norm_eq_inner)
  have nz: "0 \<le> (norm z)\<^sup>2" by simp
  \<comment> \<open>the first summand\<close>
  have f0: "0 \<le> \<kappa> * (1 - 1 / ?R) * (z \<bullet> z)"
    unfolding zz by (rule mult_nonneg_nonneg[OF A0 nz])
  have f1: "\<kappa> * (1 - 1 / ?R) * (z \<bullet> z) \<le> \<kappa> * (norm z)\<^sup>2"
    unfolding zz by (rule mult_right_mono[OF A1 nz])
  \<comment> \<open>the second summand: Cauchy-Schwarz, then @{term "(norm d)\<^sup>2 \<le> ?R\<^sup>2"}\<close>
  have Rne: "?R \<noteq> 0" using Rp by linarith
  have R2: "?R * ?R = (norm d)\<^sup>2 + 1"
    using real_sqrt_pow2[of "(norm d)\<^sup>2 + 1"] by (simp add: power2_eq_square)
  have cs: "(d \<bullet> z)\<^sup>2 \<le> (norm d)\<^sup>2 * (norm z)\<^sup>2"
  proof -
    have "(d \<bullet> z)\<^sup>2 = \<bar>d \<bullet> z\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> (norm d * norm z)\<^sup>2"
      by (rule power_mono[OF Cauchy_Schwarz_ineq2[of d z]]) simp
    also have "\<dots> = (norm d)\<^sup>2 * (norm z)\<^sup>2" by (simp add: power_mult_distrib)
    finally show ?thesis .
  qed
  have dR: "(norm d)\<^sup>2 \<le> ?R * ?R" unfolding R2 by simp
  have cs2: "(d \<bullet> z)\<^sup>2 \<le> (?R * ?R) * (norm z)\<^sup>2"
    using cs mult_right_mono[OF dR nz] by linarith
  have cube: "?R ^ 3 = ?R * ?R * ?R" by (simp add: power3_eq_cube)
  have cubep: "0 < ?R ^ 3" using Rp by simp
  have s0: "0 \<le> \<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3"
    by (rule divide_nonneg_pos[OF mult_nonneg_nonneg[OF k] cubep]) simp
  have cancel: "a * (b * b * c) / (b * b * b) = a * c / b"
    if "b \<noteq> 0" for a b c :: real
    using that by (simp add: field_simps)
  have s1: "\<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3 \<le> \<kappa> * (norm z)\<^sup>2"
  proof -
    have "\<kappa> * (d \<bullet> z)\<^sup>2 \<le> \<kappa> * ((?R * ?R) * (norm z)\<^sup>2)"
      by (rule mult_left_mono[OF cs2 k])
    then have "\<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3 \<le> (\<kappa> * ((?R * ?R) * (norm z)\<^sup>2)) / ?R ^ 3"
      by (rule divide_right_mono) (use cubep in linarith)
    also have "(\<kappa> * ((?R * ?R) * (norm z)\<^sup>2)) / ?R ^ 3 = (\<kappa> * (norm z)\<^sup>2) / ?R"
      unfolding cube by (rule cancel[OF Rne])
    also have "(\<kappa> * (norm z)\<^sup>2) / ?R \<le> \<kappa> * (norm z)\<^sup>2"
    proof -
      have nn: "0 \<le> \<kappa> * (norm z)\<^sup>2" by (rule mult_nonneg_nonneg[OF k nz])
      have "\<kappa> * (norm z)\<^sup>2 * 1 \<le> \<kappa> * (norm z)\<^sup>2 * ?R"
        by (rule mult_left_mono[OF R1 nn])
      then show ?thesis using Rp by (simp add: divide_le_eq)
    qed
    finally show ?thesis .
  qed
  have expand: "z \<bullet> (soft_hess \<kappa> d *v z)
      = \<kappa> * (1 - 1 / ?R) * (z \<bullet> z) + \<kappa> * (d \<bullet> z)\<^sup>2 / ?R ^ 3"
    by (rule soft_hess_quadform)
  show "0 \<le> z \<bullet> (soft_hess \<kappa> d *v z)" unfolding expand using f0 s0 by linarith
  show "z \<bullet> (soft_hess \<kappa> d *v z) \<le> (2*\<kappa>) * (norm z)\<^sup>2"
    unfolding expand using f1 s1 by linarith
qed

lemma soft_hess_bound:
  fixes d z :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "\<bar>z \<bullet> (soft_hess \<kappa> d *v z)\<bar> \<le> (2*\<kappa>) * (norm z)\<^sup>2"
  using soft_hess_quadform_bounds[OF k, of z d] by linarith

subsection \<open>\<open>soft_grad\<close> is Lipschitz, at a non-sharp elementary constant\<close>

text \<open>The gradient field of \<open>soft_pen \<kappa>\<close> is Lipschitz at an elementary,
  non-sharp constant, obtained algebraically without the mean value
  inequality or a bound on the operator norm of \<open>soft_hess\<close>. Writing
  \<open>R d = \<surd>(\<parallel>d\<parallel>\<^sup>2+1) \<ge> 1\<close>, \<open>R\<close> is 1-Lipschitz:
  \<open>(R x - R y)(R x + R y) = \<parallel>x\<parallel>\<^sup>2 - \<parallel>y\<parallel>\<^sup>2\<close> together with
  \<open>|\<parallel>x\<parallel> - \<parallel>y\<parallel>| \<le> \<parallel>x-y\<parallel>\<close> gives the bound after cancelling the positive
  factor \<open>Rx+Ry\<close>.\<close>

lemma norm_le_soft_R:
  fixes x :: "real^'n::finite"
  shows "norm x \<le> sqrt ((norm x)\<^sup>2 + 1)"
proof -
  have "norm x = sqrt ((norm x)\<^sup>2)" by simp
  also have "\<dots> \<le> sqrt ((norm x)\<^sup>2 + 1)" by (rule real_sqrt_le_mono) simp
  finally show ?thesis .
qed

lemma abs_norm_diff_le:
  fixes x y :: "'a::real_normed_vector"
  shows "\<bar>norm x - norm y\<bar> \<le> norm (x - y)"
proof -
  have a: "norm x - norm y \<le> norm (x - y)" by (rule norm_triangle_ineq2)
  have b: "norm y - norm x \<le> norm (y - x)" by (rule norm_triangle_ineq2)
  have c: "norm (y - x) = norm (x - y)" by (rule norm_minus_commute)
  show ?thesis using a b unfolding c by linarith
qed

lemma soft_R_lipschitz:
  fixes x y :: "real^'n::finite"
  shows "\<bar>sqrt ((norm x)\<^sup>2 + 1) - sqrt ((norm y)\<^sup>2 + 1)\<bar> \<le> norm (x - y)"
proof -
  let ?s = "sqrt ((norm x)\<^sup>2 + 1)"
  let ?t = "sqrt ((norm y)\<^sup>2 + 1)"
  have s1: "1 \<le> ?s" by (rule sqrt_norm_sq_add_one_ge_one)
  have t1: "1 \<le> ?t" by (rule sqrt_norm_sq_add_one_ge_one)
  have sum_pos: "0 < ?s + ?t" using s1 t1 by linarith
  have ssq: "?s * ?s = (norm x)\<^sup>2 + 1"
    using real_sqrt_pow2[of "(norm x)\<^sup>2 + 1"] by (simp add: power2_eq_square)
  have tsq: "?t * ?t = (norm y)\<^sup>2 + 1"
    using real_sqrt_pow2[of "(norm y)\<^sup>2 + 1"] by (simp add: power2_eq_square)
  \<comment> \<open>the difference of squares, both ways round\<close>
  have diffsq: "(?s - ?t) * (?s + ?t) = (norm x - norm y) * (norm x + norm y)"
  proof -
    have "(?s - ?t) * (?s + ?t) = ?s * ?s - ?t * ?t"
      by (simp add: algebra_simps)
    also have "\<dots> = (norm x)\<^sup>2 - (norm y)\<^sup>2" unfolding ssq tsq by simp
    also have "\<dots> = (norm x - norm y) * (norm x + norm y)"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have absprod: "\<bar>?s - ?t\<bar> * (?s + ?t)
      = \<bar>norm x - norm y\<bar> * (norm x + norm y)"
  proof -
    have nn: "0 \<le> ?s + ?t" using sum_pos by linarith
    have nn2: "0 \<le> norm x + norm y" by simp
    have "\<bar>?s - ?t\<bar> * (?s + ?t) = \<bar>(?s - ?t) * (?s + ?t)\<bar>"
      using nn by (simp add: abs_mult)
    also have "\<dots> = \<bar>(norm x - norm y) * (norm x + norm y)\<bar>"
      unfolding diffsq ..
    also have "\<dots> = \<bar>norm x - norm y\<bar> * (norm x + norm y)"
      using nn2 by (simp add: abs_mult)
    finally show ?thesis .
  qed
  \<comment> \<open>and now the two elementary bounds\<close>
  have b1: "\<bar>norm x - norm y\<bar> \<le> norm (x - y)" by (rule abs_norm_diff_le)
  have b2: "norm x + norm y \<le> ?s + ?t"
    using norm_le_soft_R[of x] norm_le_soft_R[of y] by linarith
  have chain: "\<bar>?s - ?t\<bar> * (?s + ?t) \<le> norm (x - y) * (?s + ?t)"
  proof -
    have "\<bar>norm x - norm y\<bar> * (norm x + norm y)
        \<le> norm (x - y) * (norm x + norm y)"
      by (rule mult_right_mono[OF b1]) simp
    also have "\<dots> \<le> norm (x - y) * (?s + ?t)"
      by (rule mult_left_mono[OF b2]) simp
    finally show ?thesis unfolding absprod .
  qed
  show ?thesis by (rule mult_right_le_imp_le[OF chain sum_pos])
qed

text \<open>The shrink map \<open>d \<mapsto> d / R d\<close> is 2-Lipschitz: with \<open>s = R x\<close>,
  \<open>t = R y\<close>, clearing denominators gives
  \<open>st(x/s - y/t) = t(x-y) + (t-s)y\<close>, and the \<open>R\<close>-Lipschitz bound with
  \<open>\<parallel>y\<parallel> \<le> t\<close>, \<open>s \<ge> 1\<close> yields the non-sharp constant 2. Since
  \<open>soft_grad \<kappa> d = \<kappa> d - \<kappa>(shrink d)\<close>, \<open>soft_grad \<kappa>\<close> is \<open>3\<kappa>\<close>-Lipschitz.\<close>

definition soft_shrink :: "real^'n::finite \<Rightarrow> real^'n" where
  "soft_shrink d = (1 / sqrt ((norm d)\<^sup>2 + 1)) *\<^sub>R d"

lemma soft_grad_split:
  fixes d :: "real^'n::finite"
  shows "soft_grad \<kappa> d = \<kappa> *\<^sub>R d - \<kappa> *\<^sub>R soft_shrink d"
proof -
  have "soft_grad \<kappa> d = (\<kappa> - \<kappa> * (1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R d"
    unfolding soft_grad_def by (simp add: algebra_simps)
  also have "\<dots> = \<kappa> *\<^sub>R d - (\<kappa> * (1 / sqrt ((norm d)\<^sup>2 + 1))) *\<^sub>R d"
    by (rule scaleR_left_diff_distrib)
  also have "\<dots> = \<kappa> *\<^sub>R d - \<kappa> *\<^sub>R ((1 / sqrt ((norm d)\<^sup>2 + 1)) *\<^sub>R d)"
    by simp
  finally show ?thesis unfolding soft_shrink_def .
qed

lemma soft_shrink_lipschitz:
  fixes x y :: "real^'n::finite"
  shows "norm (soft_shrink x - soft_shrink y) \<le> 2 * norm (x - y)"
proof -
  let ?s = "sqrt ((norm x)\<^sup>2 + 1)"
  let ?t = "sqrt ((norm y)\<^sup>2 + 1)"
  let ?D = "norm (soft_shrink x - soft_shrink y)"
  have s1: "1 \<le> ?s" by (rule sqrt_norm_sq_add_one_ge_one)
  have t1: "1 \<le> ?t" by (rule sqrt_norm_sq_add_one_ge_one)
  have sp: "0 < ?s" using s1 by linarith
  have tp: "0 < ?t" using t1 by linarith
  have stp: "0 < ?s * ?t" using sp tp by (rule mult_pos_pos)
  \<comment> \<open>clear the denominators\<close>
  have key: "(?s * ?t) *\<^sub>R (soft_shrink x - soft_shrink y) = ?t *\<^sub>R x - ?s *\<^sub>R y"
  proof -
    have "(?s * ?t) *\<^sub>R ((1/?s) *\<^sub>R x - (1/?t) *\<^sub>R y)
        = (?s * ?t) *\<^sub>R ((1/?s) *\<^sub>R x) - (?s * ?t) *\<^sub>R ((1/?t) *\<^sub>R y)"
      by (rule scaleR_right_diff_distrib)
    also have "\<dots> = ((?s * ?t) * (1/?s)) *\<^sub>R x - ((?s * ?t) * (1/?t)) *\<^sub>R y"
      by simp
    also have "\<dots> = ?t *\<^sub>R x - ?s *\<^sub>R y" using sp tp by simp
    finally show ?thesis unfolding soft_shrink_def .
  qed
  have decomp: "?t *\<^sub>R x - ?s *\<^sub>R y = ?t *\<^sub>R (x - y) + (?t - ?s) *\<^sub>R y"
    by (simp add:
          algebra_simps)
  \<comment> \<open>the triangle estimate\<close>
  have tri: "norm (?t *\<^sub>R (x - y) + (?t - ?s) *\<^sub>R y)
      \<le> norm (?t *\<^sub>R (x - y)) + norm ((?t - ?s) *\<^sub>R y)"
    by (rule norm_triangle_ineq)
  have e1: "norm (?t *\<^sub>R (x - y)) = ?t * norm (x - y)" using tp by simp
  have e2: "norm ((?t - ?s) *\<^sub>R y) = \<bar>?t - ?s\<bar> * norm y" by simp
  have absb: "\<bar>?t - ?s\<bar> \<le> norm (x - y)"
  proof -
    have "\<bar>?s - ?t\<bar> \<le> norm (x - y)" by (rule soft_R_lipschitz)
    then show ?thesis by (simp add: abs_minus_commute)
  qed
  have ny: "norm y \<le> ?t" by (rule norm_le_soft_R)
  have prod: "\<bar>?t - ?s\<bar> * norm y \<le> ?t * norm (x - y)"
  proof -
    have "\<bar>?t - ?s\<bar> * norm y \<le> norm (x - y) * norm y"
      by (rule mult_right_mono[OF absb]) simp
    also have "\<dots> \<le> norm (x - y) * ?t" by (rule mult_left_mono[OF ny]) simp
    also have "norm (x - y) * ?t = ?t * norm (x - y)" by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have bound: "norm (?t *\<^sub>R x - ?s *\<^sub>R y) \<le> 2 * (?t * norm (x - y))"
    unfolding decomp using tri e1 e2 prod by linarith
  \<comment> \<open>and cancel\<close>
  have step: "(?s * ?t) * ?D \<le> 2 * (?t * norm (x - y))"
  proof -
    have "(?s * ?t) * ?D = norm ((?s * ?t) *\<^sub>R (soft_shrink x - soft_shrink y))"
      using stp by simp
    also have "\<dots> = norm (?t *\<^sub>R x - ?s *\<^sub>R y)" unfolding key ..
    also have "\<dots> \<le> 2 * (?t * norm (x - y))" by (rule bound)
    finally show ?thesis .
  qed
  have r1: "(?s * ?t) * ?D = ?t * (?s * ?D)" by (simp add: mult_ac)
  have r2: "2 * (?t * norm (x - y)) = ?t * (2 * norm (x - y))"
    by (simp add: mult_ac)
  have cancel: "?t * (?s * ?D) \<le> ?t * (2 * norm (x - y))"
    using step unfolding r1 r2 .
  have sN: "?s * ?D \<le> 2 * norm (x - y)"
    by (rule mult_left_le_imp_le[OF cancel tp])
  have grow: "?D \<le> ?s * ?D"
  proof -
    have "1 * ?D \<le> ?s * ?D" by (rule mult_right_mono[OF s1]) simp
    then show ?thesis by simp
  qed
  show ?thesis using grow sN by linarith
qed

theorem soft_grad_lipschitz:
  fixes x y :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "norm (soft_grad \<kappa> x - soft_grad \<kappa> y) \<le> (3*\<kappa>) * norm (x - y)"
proof -
  let ?S = "soft_shrink x - soft_shrink y"
  have split: "soft_grad \<kappa> x - soft_grad \<kappa> y = \<kappa> *\<^sub>R (x - y) - \<kappa> *\<^sub>R ?S"
    unfolding soft_grad_split
    by (simp add: algebra_simps)
  have tri: "norm (\<kappa> *\<^sub>R (x - y) - \<kappa> *\<^sub>R ?S)
      \<le> norm (\<kappa> *\<^sub>R (x - y)) + norm (\<kappa> *\<^sub>R ?S)"
    by (rule norm_triangle_ineq4)
  have e1: "norm (\<kappa> *\<^sub>R (x - y)) = \<kappa> * norm (x - y)" using k by simp
  have e2: "norm (\<kappa> *\<^sub>R ?S) = \<kappa> * norm ?S" using k by simp
  have sh: "\<kappa> * norm ?S \<le> \<kappa> * (2 * norm (x - y))"
    by (rule mult_left_mono[OF soft_shrink_lipschitz k])
  have exp: "(3*\<kappa>) * norm (x - y) = \<kappa> * norm (x - y) + \<kappa> * (2 * norm (x - y))"
    by (simp add: algebra_simps)
  show ?thesis unfolding split exp using tri e1 e2 sh by linarith
qed

subsection \<open>The diagonal dichotomy for \<open>soft_pen\<close>\<close>

text \<open>At \<open>d = 0\<close> the gradient and Hessian of \<open>soft_pen\<close> both vanish, so a
  diagonal configuration would give the supersolution's test function a
  vanishing jet \<open>(0,0)\<close>, forbidden by \<open>supersol_no_vanishing_jet\<close>. Off
  the diagonal, for \<open>\<kappa> > 0\<close> the gradient is nonzero since \<open>R d > 1\<close> for
  \<open>d \<noteq> 0\<close>, making \<open>\<kappa>(1 - 1/R d)\<close> strictly positive, the positive lower
  bound \<open>c\<close> needed elsewhere.\<close>

lemma soft_R_gt_one:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0"
  shows "1 < sqrt ((norm d)\<^sup>2 + 1)"
proof -
  have "0 < norm d" using d by simp
  then have "0 < (norm d)\<^sup>2" by simp
  then have "(1::real) < (norm d)\<^sup>2 + 1" by linarith
  then have "sqrt (1::real) < sqrt ((norm d)\<^sup>2 + 1)" by (rule real_sqrt_less_mono)
  then show ?thesis by simp
qed

lemma soft_grad_coeff_pos:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and k: "0 < \<kappa>"
  shows "0 < \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
proof -
  have R: "1 < sqrt ((norm d)\<^sup>2 + 1)" by (rule soft_R_gt_one[OF d])
  then have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have "1 / sqrt ((norm d)\<^sup>2 + 1) < 1" using R Rp by (simp add: divide_less_eq)
  then have pos: "0 < 1 - 1 / sqrt ((norm d)\<^sup>2 + 1)" by linarith
  show ?thesis by (rule mult_pos_pos[OF k pos])
qed

lemma soft_grad_nonzero:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and k: "0 < \<kappa>"
  shows "soft_grad \<kappa> d \<noteq> 0"
proof -
  have c: "0 < \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
    by (rule soft_grad_coeff_pos[OF d k])
  then have cne: "\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) \<noteq> 0" by linarith
  show ?thesis
    unfolding soft_grad_def using cne d by simp
qed

lemma soft_grad_norm_pos:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and k: "0 < \<kappa>"
  shows "0 < norm (soft_grad \<kappa> d)"
  using soft_grad_nonzero[OF d k] by simp

text \<open>Taking \<open>c\<close> to be the actual gradient norm at the maximiser cancels
  \<open>\<kappa>\<close> from \<open>(3\<kappa>)(2\<rho>) < \<parallel>soft_grad \<kappa> d\<parallel>\<close>, reducing to
  \<open>6\<rho> < (1 - 1/R d) \<parallel>d\<parallel>\<close>. Since every other constraint on \<open>\<rho>\<close> in the
  chain is an upper bound, such a \<open>\<rho>\<close> always exists.\<close>

lemma soft_grad_norm_eq:
  fixes d :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "norm (soft_grad \<kappa> d)
      = (\<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))) * norm d"
proof -
  have R1: "1 \<le> sqrt ((norm d)\<^sup>2 + 1)" by (rule sqrt_norm_sq_add_one_ge_one)
  then have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have "1 / sqrt ((norm d)\<^sup>2 + 1) \<le> 1" using R1 Rp by (simp add: divide_le_eq_1)
  then have nn: "0 \<le> \<kappa> * (1 - 1 / sqrt ((norm d)\<^sup>2 + 1))"
    by (intro mult_nonneg_nonneg[OF k]) linarith
  show ?thesis unfolding soft_grad_def using nn by simp
qed

lemma soft_rsmall_of_rho:
  fixes d :: "real^'n::finite"
  assumes k: "0 < \<kappa>"
    and small: "6 * \<rho> < (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d"
  shows "(3*\<kappa>) * (2*\<rho>) < norm (soft_grad \<kappa> d)"
proof -
  have knn: "0 \<le> \<kappa>" using k by linarith
  have eq: "norm (soft_grad \<kappa> d)
      = \<kappa> * ((1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d)"
    unfolding soft_grad_norm_eq[OF knn] by (simp add: mult_ac)
  have "\<kappa> * (6 * \<rho>) < \<kappa> * ((1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d)"
    by (rule mult_strict_left_mono[OF small k])
  moreover have "(3*\<kappa>) * (2*\<rho>) = \<kappa> * (6 * \<rho>)" by (simp add: mult_ac)
  ultimately show ?thesis unfolding eq by linarith
qed

lemma exists_small_rho_aux:
  fixes B G :: real
  assumes B: "0 < B" and G: "0 < G"
  shows "\<exists>\<rho>. 0 < \<rho> \<and> \<rho> < B \<and> 6 * \<rho> < G"
proof -
  have h1: "0 < B/2" by (rule divide_pos_pos[OF B]) simp
  have h2: "0 < G/12" by (rule divide_pos_pos[OF G]) simp
  have eB: "B = B/2 + B/2" by simp
  have eG: "G = 12 * (G/12)" by simp
  have le1: "min (B/2) (G/12) \<le> B/2" by simp
  have le2: "min (B/2) (G/12) \<le> G/12" by simp
  have p1: "0 < min (B/2) (G/12)" using h1 h2 by simp
  have p2: "min (B/2) (G/12) < B" using le1 h1 eB by linarith
  have p3: "6 * min (B/2) (G/12) < G"
  proof -
    have "6 * min (B/2) (G/12) \<le> 6 * (G/12)"
      by (rule mult_left_mono[OF le2]) simp
    then show ?thesis using h2 eG by linarith
  qed
  show ?thesis using p1 p2 p3 by blast
qed

lemma soft_gap_pos:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0"
  shows "0 < (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d"
proof -
  have R: "1 < sqrt ((norm d)\<^sup>2 + 1)" by (rule soft_R_gt_one[OF d])
  then have Rp: "0 < sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have "1 / sqrt ((norm d)\<^sup>2 + 1) < 1" using R Rp by (simp add: divide_less_eq)
  then have cpos: "0 < 1 - 1 / sqrt ((norm d)\<^sup>2 + 1)" by linarith
  have dpos: "0 < norm d" using d by simp
  show ?thesis by (rule mult_pos_pos[OF cpos dpos])
qed

lemma soft_rho_exists:
  fixes d :: "real^'n::finite"
  assumes d: "d \<noteq> 0" and B: "0 < B"
  shows "\<exists>\<rho>. 0 < \<rho> \<and> \<rho> < B
      \<and> 6 * \<rho> < (1 - 1 / sqrt ((norm d)\<^sup>2 + 1)) * norm d"
  by (rule exists_small_rho_aux[OF B soft_gap_pos[OF d]])

subsection \<open>Jensen's semiconvexity input, for a general penalty\<close>

text \<open>\<open>doubled_functional_semiconvex\<close> transcribed for a general penalty
  \<open>Pn\<close>, replacing the quadratic-specific semiconvexity step by the
  hypothesis \<open>sc\<close>; the doubled constant becomes \<open>1/\<epsilon> + 1/\<epsilon> + 2\<kappa>\<close>,
  matching the quadratic case at \<open>\<kappa> = \<alpha>\<close>.\<close>

theorem doubled_functional_semiconvex_gen:
  fixes u v :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bv: "\<And>y. v y \<le> Bv"
    and e: "0 < \<epsilon>" and k: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - Pn d)"
  shows "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z) - Pn (fst z - snd z))
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa>)/2) * (norm z)\<^sup>2)"
proof -
  have ce: "0 \<le> 1/\<epsilon>" using e by simp
  have A: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      supconv u \<epsilon> (fst z) + ((1/\<epsilon>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_of_fst[OF supconv_semiconvex'[OF Bu e] ce])
  have B: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      supconv v \<epsilon> (snd z) + ((1/\<epsilon>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_of_snd[OF supconv_semiconvex'[OF Bv e] ce])
  have AB: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z))
      + ((1/\<epsilon> + 1/\<epsilon>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_add[OF A B])
  have C: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      - Pn (fst z - snd z) + ((2*\<kappa>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_penalty_gen[OF k sc])
  have ABC: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)) + - Pn (fst z - snd z))
      + (((1/\<epsilon> + 1/\<epsilon>) + 2*\<kappa>)/2) * (norm z)\<^sup>2)"
    by (rule semiconvex_add[OF AB C])
  have eq: "(\<lambda>z::(real^'n) \<times> (real^'n).
        ((supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z)) + - Pn (fst z - snd z))
        + (((1/\<epsilon> + 1/\<epsilon>) + 2*\<kappa>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::(real^'n) \<times> (real^'n).
        (supconv u \<epsilon> (fst z) + supconv v \<epsilon> (snd z) - Pn (fst z - snd z))
        + ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa>)/2) * (norm z)\<^sup>2)"
    by (rule ext) simp
  show ?thesis using ABC unfolding eq .
qed

text \<open>Jensen's lemma for the general doubled functional, as
  \<open>doubled_supconv_jet_exists\<close> with \<open>(\<alpha>/2)\<parallel>fst y - snd y\<parallel>\<^sup>2\<close> replaced by
  \<open>Pn (fst y - snd y)\<close> and the semiconvexity constant by
  \<open>1/\<epsilon> + 1/\<epsilon> + 2\<kappa>\<close>.\<close>

text \<open>Subtracting \<open>\<delta>\<parallel>z - \<xi>\<parallel>\<^sup>2\<close> and adding back \<open>\<delta>\<parallel>z\<parallel>\<^sup>2\<close> leaves an affine
  term \<open>\<delta>(2 z \<bullet> \<xi> - \<parallel>\<xi>\<parallel>\<^sup>2)\<close>, so a semiconvex \<open>\<Psi>\<close> stays semiconvex after
  this shift, with its constant raised by \<open>2\<delta>\<close>; the argument is
  independent of the penalty.\<close>

lemma semiconvex_shift_perturb:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes cvx: "convex_on UNIV (\<lambda>z. \<Psi> z + (C/2) * (norm z)\<^sup>2)"
    and dnn: "0 \<le> \<delta>"
  shows "convex_on UNIV (\<lambda>z. (\<Psi> z - \<delta> * (norm (z - \<xi>))\<^sup>2)
      + ((C + 2*\<delta>)/2) * (norm z)\<^sup>2)"
proof -
  have sq: "(norm (z - \<xi>))\<^sup>2 = (norm z)\<^sup>2 - 2 * (z \<bullet> \<xi>) + (norm \<xi>)\<^sup>2"
    for z :: 'a
    by (simp add: power2_norm_eq_inner inner_diff_left inner_diff_right
        inner_commute)
  have e: "(\<lambda>z::'a. (\<Psi> z - \<delta> * (norm (z - \<xi>))\<^sup>2)
        + ((C + 2*\<delta>)/2) * (norm z)\<^sup>2)
      = (\<lambda>z::'a. (\<Psi> z + (C/2) * (norm z)\<^sup>2)
        + \<delta> * (2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))"
  proof (rule ext)
    fix z :: 'a
    show "(\<Psi> z - \<delta> * (norm (z - \<xi>))\<^sup>2) + ((C + 2*\<delta>)/2) * (norm z)\<^sup>2
        = (\<Psi> z + (C/2) * (norm z)\<^sup>2) + \<delta> * (2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2)"
      unfolding sq by (simp add: algebra_simps)
  qed
  have aff: "convex_on UNIV (\<lambda>z::'a. \<delta> * (2 * (z \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))"
  proof (rule convex_onI)
    fix t :: real and x y :: 'a
    assume "0 < t" "t < 1"
    show "\<delta> * (2 * (((1 - t) *\<^sub>R x + t *\<^sub>R y) \<bullet> \<xi>) - (norm \<xi>)\<^sup>2)
        \<le> (1 - t) * (\<delta> * (2 * (x \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))
          + t * (\<delta> * (2 * (y \<bullet> \<xi>) - (norm \<xi>)\<^sup>2))"
      by (simp add: algebra_simps)
  qed simp
  show ?thesis unfolding e by (rule convex_on_add[OF cvx aff])
qed

text \<open>Jensen's lemma for the shifted general functional, the strict-gap
  version: the shifted functional \<open>\<Phi> - \<delta>\<parallel>z - \<xi>\<^sub>0\<parallel>\<^sup>2\<close>, with \<open>\<Phi>\<close> the
  general doubled functional, is semiconvex with constant raised by
  \<open>2\<delta>\<close> by \<open>semiconvex_shift_perturb\<close>.\<close>

theorem doubled_supconv_jet_exists_shifted_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. w y \<le> Bw"
    and e: "0 < \<epsilon>" and k: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - Pn d)"
    and dnn: "0 \<le> \<delta>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi>
        \<Longrightarrow> (supconv u \<epsilon> (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
              + (supconv w \<epsilon> (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
              - Pn (fst y - snd y) \<le> m"
    and d: "0 < dd"
    and small: "2 * dd * r
        < ((supconv u \<epsilon> (fst \<xi>) - \<delta> * (norm (fst \<xi> - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd \<xi>) - \<delta> * (norm (snd \<xi> - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst \<xi> - snd \<xi>)) - m"
  shows "\<exists>zh p q W. dist zh \<xi> < \<rho> \<and> norm p \<le> dd
      \<and> (\<forall>y \<in> cball \<xi> r.
          ((supconv u \<epsilon> (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst y - snd y)) + p \<bullet> y
          \<le> ((supconv u \<epsilon> (fst zh) - \<delta> * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd zh) - \<delta> * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst zh - snd zh)) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>kk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*\<delta>) * (norm kk)\<^sup>2) \<le> kk \<bullet> W kk)
      \<and> ((\<lambda>kk. (((supconv u \<epsilon> (fst (zh + kk))
                - \<delta> * (norm (fst (zh + kk) - fst \<xi>\<^sub>0))\<^sup>2)
              + (supconv w \<epsilon> (snd (zh + kk))
                - \<delta> * (norm (snd (zh + kk) - snd \<xi>\<^sub>0))\<^sup>2)
              - Pn (fst (zh + kk) - snd (zh + kk)))
            - ((supconv u \<epsilon> (fst zh) - \<delta> * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
              + (supconv w \<epsilon> (snd zh) - \<delta> * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
              - Pn (fst zh - snd zh))
            - q \<bullet> kk - (kk \<bullet> W kk)/2) / (norm kk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have split: "(supconv u \<epsilon> (fst z) - \<delta> * (norm (fst z - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv w \<epsilon> (snd z) - \<delta> * (norm (snd z - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst z - snd z)
      = (supconv u \<epsilon> (fst z) + supconv w \<epsilon> (snd z) - Pn (fst z - snd z))
        - \<delta> * (norm (z - \<xi>\<^sub>0))\<^sup>2"
    for z :: "(real^'n) \<times> (real^'n)"
  proof -
    have nsplit: "(norm (z - \<xi>\<^sub>0))\<^sup>2
        = (norm (fst z - fst \<xi>\<^sub>0))\<^sup>2 + (norm (snd z - snd \<xi>\<^sub>0))\<^sup>2"
    proof -
      have "(norm (z - \<xi>\<^sub>0))\<^sup>2
          = (norm (fst (z - \<xi>\<^sub>0)))\<^sup>2 + (norm (snd (z - \<xi>\<^sub>0)))\<^sup>2"
        by (rule norm_prod_sq)
      then show ?thesis by simp
    qed
    show ?thesis unfolding nsplit by (simp add: algebra_simps)
  qed
  have base: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      (supconv u \<epsilon> (fst z) + supconv w \<epsilon> (snd z) - Pn (fst z - snd z))
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa>)/2) * (norm z)\<^sup>2)"
    by (rule doubled_functional_semiconvex_gen[OF Bu Bw e k sc])
  have cvx: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      ((supconv u \<epsilon> (fst z) - \<delta> * (norm (fst z - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv w \<epsilon> (snd z) - \<delta> * (norm (snd z - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst z - snd z))
      + (((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa>) + 2*\<delta>)/2) * (norm z)\<^sup>2)"
    unfolding split
    by (rule semiconvex_shift_perturb[OF base dnn])
  have c: "0 < 1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*\<delta>"
  proof -
    have "0 < 1/\<epsilon>" using e by simp
    then show ?thesis using k dnn by linarith
  qed
  show ?thesis
    by (rule semiconvex_jensen_alexandrov_point[OF cvx c rho(1) rho(2)
          bnd d small])
qed

text \<open>The annulus bound Jensen's strict-gap version needs: a plain
  maximiser of \<open>\<Phi>\<close> over \<open>cball \<xi>\<^sub>0 r\<close> gives no strict gap, but
  subtracting \<open>\<delta>\<parallel>z - \<xi>\<^sub>0\<parallel>\<^sup>2\<close> costs at least \<open>\<delta>\<rho>\<^sup>2\<close> on the annulus
  \<open>\<rho> \<le> \<parallel>y - \<xi>\<^sub>0\<parallel>\<close>, while the centre value \<open>\<Phi>(\<xi>\<^sub>0)\<close> is exact.\<close>

lemma shifted_annulus_bound_split_gen:
  fixes A B :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        A (fst y) + B (snd y) - Pn (fst y - snd y)
        \<le> A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and dnn: "0 \<le> \<delta>" and rho: "0 < \<rho>"
    and y: "y \<in> cball \<xi>\<^sub>0 r" and ann: "\<rho> \<le> dist y \<xi>\<^sub>0"
  shows "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)
      \<le> (A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)) - \<delta> * \<rho>\<^sup>2"
proof -
  have nsplit: "(norm (y - \<xi>\<^sub>0))\<^sup>2
      = (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2 + (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2"
  proof -
    have "(norm (y - \<xi>\<^sub>0))\<^sup>2
        = (norm (fst (y - \<xi>\<^sub>0)))\<^sup>2 + (norm (snd (y - \<xi>\<^sub>0)))\<^sup>2"
      by (rule norm_prod_sq)
    then show ?thesis by simp
  qed
  have dn: "norm (y - \<xi>\<^sub>0) = dist y \<xi>\<^sub>0" by (simp add: dist_norm)
  have sq: "\<rho>\<^sup>2 \<le> (norm (y - \<xi>\<^sub>0))\<^sup>2"
    unfolding dn by (rule power_mono[OF ann]) (use rho in linarith)
  have pen: "\<delta> * \<rho>\<^sup>2 \<le> \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    by (rule mult_left_mono[OF sq dnn])
  have mx: "A (fst y) + B (snd y) - Pn (fst y - snd y)
      \<le> A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    by (rule mxK[OF y])
  have e: "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)
      = (A (fst y) + B (snd y) - Pn (fst y - snd y))
        - \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    unfolding nsplit by (simp add: algebra_simps)
  show ?thesis unfolding e using mx pen by linarith
qed

text \<open>The matrix inequality for a general penalty adds the penalty's jet to
  \<open>expPsi\<close> rather than substituting a fixed quadratic identity; the
  block-diagonal identity and the vanishing of the penalty form on the
  diagonal rely only on \<open>P(x - y)\<close> being constant along \<open>(v,v)\<close>, true
  for any \<open>P\<close>.\<close>

lemma matrix_vector_mult_scaleR_gen:
  fixes Z :: "real^'n::finite^'n"
  shows "Z *v (s *\<^sub>R u) = s *\<^sub>R (Z *v u)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_distrib_left
      algebra_simps)

theorem sums_matrix_inequality_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
    and v: "v \<noteq> 0"
  shows "v \<bullet> (fst (W (v, 0)) + Z *v v)
       + v \<bullet> (snd (W (0, v)) + Z *v v) \<le> 0"
proof -
  define Pop where "Pop = (\<lambda>k::(real^'n) \<times> (real^'n).
      ((Z *v (fst k - snd k), Z *v (snd k - fst k)) :: (real^'n) \<times> (real^'n)))"
  define WP where "WP = (\<lambda>k::(real^'n) \<times> (real^'n). W k + Pop k)"
  define g0 where "g0 = ((G, - G) :: (real^'n) \<times> (real^'n))"
  have scPop: "Pop (s *\<^sub>R u) = s *\<^sub>R Pop u" for s :: real and u
    unfolding Pop_def
    by (simp add: scaleR_diff_right[symmetric] matrix_vector_mult_scaleR_gen)
  have scWP: "WP (s *\<^sub>R u) = s *\<^sub>R WP u" for s :: real and u
    unfolding WP_def scW scPop by (simp add: scaleR_add_right)
  have penlim: "((\<lambda>k. (Pn (fst (zh + k) - snd (zh + k))
        - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2) / (norm k)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    unfolding g0_def Pop_def by (rule doubled_penalty_jet[OF Pjet])
  have rem: "((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2)
      + (Pn (fst (zh + k) - snd (zh + k))
        - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2)
      = (a (fst (zh + k)) + b (snd (zh + k)))
        - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2" for k
  proof -
    have iWP: "k \<bullet> WP k = k \<bullet> W k + k \<bullet> Pop k"
      unfolding WP_def by (simp add: inner_add_right)
    have iq: "(q + g0) \<bullet> k = q \<bullet> k + g0 \<bullet> k"
      by (simp add: inner_add_left)
    show ?thesis unfolding iWP iq by simp argo
  qed
  have expTheta: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k)))
      - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  proof -
    have s: "((\<lambda>k. (((a (fst (zh + k)) + b (snd (zh + k))
            - Pn (fst (zh + k) - snd (zh + k)))
          - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
          - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2)
        + ((Pn (fst (zh + k) - snd (zh + k))
          - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2) / (norm k)\<^sup>2))
        \<longlongrightarrow> 0) (at 0)"
      using tendsto_add[OF expPsi penlim] by simp
    have e: "(((a (fst (zh + k)) + b (snd (zh + k))
            - Pn (fst (zh + k) - snd (zh + k)))
          - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
          - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2)
        + ((Pn (fst (zh + k) - snd (zh + k))
          - Pn (fst zh - snd zh) - g0 \<bullet> k - (k \<bullet> Pop k)/2) / (norm k)\<^sup>2)
      = ((a (fst (zh + k)) + b (snd (zh + k)))
        - (a (fst zh) + b (snd zh)) - (q + g0) \<bullet> k - (k \<bullet> WP k)/2)
        / (norm k)\<^sup>2" for k
      using rem[of k] by (simp add: add_divide_distrib[symmetric])
    show ?thesis using s unfolding e .
  qed
  have blk: "(v, v) \<bullet> WP (v, v)
      = v \<bullet> fst (WP (v, 0)) + v \<bullet> snd (WP (0, v))"
    by (rule product_form_block_diagonal[OF expTheta scWP v v])
  have pdiag: "(v, v) \<bullet> Pop (v, v) = 0"
    unfolding Pop_def by (simp add: inner_prod_def)
  have "(v, v) \<bullet> WP (v, v) = (v, v) \<bullet> W (v, v) + (v, v) \<bullet> Pop (v, v)"
    unfolding WP_def by (simp add: inner_add_right)
  hence "(v, v) \<bullet> WP (v, v) = (v, v) \<bullet> W (v, v)"
    unfolding pdiag by simp
  moreover have "(v, v) \<bullet> W (v, v) \<le> 0" by (rule neg)
  ultimately have "v \<bullet> fst (WP (v, 0)) + v \<bullet> snd (WP (0, v)) \<le> 0"
    unfolding blk[symmetric] by simp
  thus ?thesis unfolding WP_def Pop_def by simp
qed

text \<open>The ordering in \<open>\<le>\<close> form, then with the negativity hypothesis
  discharged at the interior maximum, both with \<open>\<alpha> *\<^sub>R v\<close> replaced by
  \<open>Z *v v\<close> and the penalty's jet \<open>Pjet\<close> threaded through.\<close>

theorem sums_gives_ordering_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
  shows "v \<bullet> (fst (W (v, 0)) + Z *v v)
       \<le> v \<bullet> (- (snd (W (0, v)) + Z *v v))"
proof (cases "v = 0")
  case True
  then show ?thesis by simp
next
  case False
  have h: "v \<bullet> (fst (W (v, 0)) + Z *v v)
      + v \<bullet> (snd (W (0, v)) + Z *v v) \<le> 0"
    by (rule sums_matrix_inequality_gen[OF expPsi Pjet scW neg False])
  have neg_eq: "v \<bullet> (- (snd (W (0, v)) + Z *v v))
      = - (v \<bullet> (snd (W (0, v)) + Z *v v))"
    by (rule inner_minus_right)
  show ?thesis
    unfolding neg_eq using h by linarith
qed

theorem sums_ordering_at_interior_max_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes blW: "bounded_linear W"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k))
        \<le> a (fst zh) + b (snd zh) - Pn (fst zh - snd zh)"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> (fst (W (v, 0)) + Z *v v)
       \<le> v \<bullet> (- (snd (W (0, v)) + Z *v v))"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z::(real^'n) \<times> (real^'n).
      a (fst z) + b (snd z) - Pn (fst z - snd z))"
  have mxP: "\<Psi> (zh + k) \<le> \<Psi> zh" if "norm k < d" for k
    unfolding \<Psi>_def by (rule mx[OF that])
  have expP: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding \<Psi>_def by (rule expPsi)
  have neg: "k \<bullet> W k \<le> 0" for k
    using second_order_interior_max[OF blW dpos mxP expP] by blast
  have scW: "W (s *\<^sub>R u) = s *\<^sub>R W u" for s :: real and u
    using blW by (simp add: linear_simps)
  show ?thesis
    by (rule sums_gives_ordering_gen[OF expPsi Pjet scW neg])
qed

text \<open>Block linearity and symmetry with \<open>Z *v v\<close> in place of
  \<open>\<alpha> *\<^sub>R v\<close>, proved directly rather than through the penalty-specific
  \<open>linear_slice_fst\<close> / \<open>sym_slice_fst\<close>; symmetry needs \<open>Z\<close> symmetric,
  which holds for the quartic penalty's Hessian
  \<open>\<beta>((d \<bullet> d) I + 2 d d\<^sup>T)\<close>.\<close>

lemma inner_matrix_sym:
  fixes Z :: "real^'n::finite^'n"
  assumes s: "transpose Z = Z"
  shows "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"
proof -
  have zij: "Z $ i $ j = Z $ j $ i" for i j
  proof -
    have "Z $ i $ j = (transpose Z) $ i $ j" using s by simp
    also have "\<dots> = Z $ j $ i" by (simp add: transpose_def)
    finally show ?thesis .
  qed
  have "v \<bullet> (Z *v z) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. v $ i * (Z $ i $ j * z $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. v $ i * (Z $ i $ j * z $ j))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. z $ j * (Z $ j $ i * v $ i))"
    by (simp add: zij mult.commute mult.left_commute)
  also have "\<dots> = z \<bullet> (Z *v v)"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  finally show ?thesis .
qed

lemma linear_block_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. fst (W (v, 0)) + Z *v v)"
proof -
  have lW: "linear W"
    using blW by (simp add: linear_conv_bounded_linear)
  have l1: "linear (\<lambda>v::real^'n. fst (W (v, 0)))"
  proof (rule linearI)
    fix x y :: "real^'n"
    have "W (x + y, 0) = W (((x, 0) :: (real^'n) \<times> (real^'n)) + (y, 0))"
      by simp
    also have "\<dots> = W (x, 0) + W (y, 0)" by (rule linear_add[OF lW])
    finally show "fst (W (x + y, 0)) = fst (W (x, 0)) + fst (W (y, 0))"
      by simp
  next
    fix c :: real and x :: "real^'n"
    have "W (c *\<^sub>R x, 0) = W (c *\<^sub>R ((x, 0) :: (real^'n) \<times> (real^'n)))"
      by simp
    also have "\<dots> = c *\<^sub>R W (x, 0)" by (rule linear_cmul[OF lW])
    finally show "fst (W (c *\<^sub>R x, 0)) = c *\<^sub>R fst (W (x, 0))"
      by simp
  qed
  have l2: "linear (\<lambda>v::real^'n. Z *v v)"
    by (rule matrix_vector_mul_linear)
  show ?thesis by (rule linear_compose_add[OF l1 l2])
qed

lemma linear_block_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. - (snd (W (0, v)) + Z *v v))"
proof -
  have lW: "linear W"
    using blW by (simp add: linear_conv_bounded_linear)
  have l1: "linear (\<lambda>v::real^'n. snd (W (0, v)))"
  proof (rule linearI)
    fix x y :: "real^'n"
    have "W (0, x + y) = W (((0, x) :: (real^'n) \<times> (real^'n)) + (0, y))"
      by simp
    also have "\<dots> = W (0, x) + W (0, y)" by (rule linear_add[OF lW])
    finally show "snd (W (0, x + y)) = snd (W (0, x)) + snd (W (0, y))"
      by simp
  next
    fix c :: real and x :: "real^'n"
    have "W (0, c *\<^sub>R x) = W (c *\<^sub>R ((0, x) :: (real^'n) \<times> (real^'n)))"
      by simp
    also have "\<dots> = c *\<^sub>R W (0, x)" by (rule linear_cmul[OF lW])
    finally show "snd (W (0, c *\<^sub>R x)) = c *\<^sub>R snd (W (0, x))"
      by simp
  qed
  have l2: "linear (\<lambda>v::real^'n. Z *v v)"
    by (rule matrix_vector_mul_linear)
  have l3: "linear (\<lambda>v::real^'n. snd (W (0, v)) + Z *v v)"
    by (rule linear_compose_add[OF l1 l2])
  show ?thesis by (rule linear_compose_neg[OF l3])
qed

lemma sym_block_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "v \<bullet> (fst (W (z, 0)) + Z *v z)
       = z \<bullet> (fst (W (v, 0)) + Z *v v)"
proof -
  have w1: "v \<bullet> fst (W (z, 0)) = ((v, 0) :: (real^'n) \<times> (real^'n)) \<bullet> W (z, 0)"
    by (simp add: inner_prod_def)
  have w2: "z \<bullet> fst (W (v, 0)) = ((z, 0) :: (real^'n) \<times> (real^'n)) \<bullet> W (v, 0)"
    by (simp add: inner_prod_def)
  have wsym: "v \<bullet> fst (W (z, 0)) = z \<bullet> fst (W (v, 0))"
    unfolding w1 w2 by (rule symW)
  have zsym: "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"
    by (rule inner_matrix_sym[OF symZ])
  show ?thesis
    using wsym zsym by (simp add: inner_add_right)
qed

lemma sym_block_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "v \<bullet> (- (snd (W (0, z)) + Z *v z))
       = z \<bullet> (- (snd (W (0, v)) + Z *v v))"
proof -
  have w1: "v \<bullet> snd (W (0, z)) = ((0, v) :: (real^'n) \<times> (real^'n)) \<bullet> W (0, z)"
    by (simp add: inner_prod_def)
  have w2: "z \<bullet> snd (W (0, v)) = ((0, z) :: (real^'n) \<times> (real^'n)) \<bullet> W (0, v)"
    by (simp add: inner_prod_def)
  have wsym: "v \<bullet> snd (W (0, z)) = z \<bullet> snd (W (0, v))"
    unfolding w1 w2 by (rule symW)
  have zsym: "v \<bullet> (Z *v z) = z \<bullet> (Z *v v)"
    by (rule inner_matrix_sym[OF symZ])
  have l: "v \<bullet> (- (snd (W (0, z)) + Z *v z))
      = - (v \<bullet> snd (W (0, z))) - (v \<bullet> (Z *v z))"
    by (simp add: inner_add_right inner_diff_right)
  have r: "z \<bullet> (- (snd (W (0, v)) + Z *v v))
      = - (z \<bullet> snd (W (0, v))) - (z \<bullet> (Z *v v))"
    by (simp add: inner_add_right inner_diff_right)
  show ?thesis unfolding l r using wsym zsym by simp
qed

corollary sums_psd_at_interior_max_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k))
        \<le> a (fst zh) + b (snd zh) - Pn (fst zh - snd zh)"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - Pn (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "psd (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))
            - matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))"
  by (rule psd_of_abstract_le
      [OF linear_block_fst_gen[OF blW] linear_block_snd_gen[OF blW]
         sym_block_fst_gen[OF symW symZ] sym_block_snd_gen[OF symW symZ]
         sums_ordering_at_interior_max_gen[OF blW dpos mx expPsi Pjet]])

subsection \<open>A supersolution has no vanishing second-order jet\<close>

text \<open>A supersolution is never tested at a vanishing second-order jet
  \<open>(0, 0)\<close>, since the supersolution property would then read
  \<open>1 \<le> F\<^sup>*(0, 0) = 0\<close>. This rules out the diagonal case of the paper's
  quartic penalty in \<open>x - y\<close>: at a diagonal maximiser its gradient and
  Hessian in \<open>y\<close> vanish, giving exactly \<open>(0, 0)\<close>; off the diagonal the
  common gradient is the penalty's, automatically nonzero. Since
  \<open>F(p, 0) = 0\<close> for every \<open>p\<close> (the feasible set is nonempty and
  \<open>-trace(0 a)/2 = 0\<close> for every \<open>a\<close>), the \<open>\<delta>\<close>-removal argument of
  \<open>strict_contradiction_of_shifts_any_p\<close> gives the contradiction:
  \<open>1 \<le> F(0, -\<delta>I) \<le> F(0,0) + \<delta>nL/2\<close> fails for small \<open>\<delta>\<close>.\<close>

text \<open>As \<open>supersol_no_vanishing_jet\<close>, but with the one-sided jet
  hypothesis the diagonal branch of Theorem 4.2(a) actually supplies: a
  maximiser inequality bounds the increment from above only.\<close>

theorem supersol_no_vanishing_jet_onesided:
  fixes w :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        ((- w) (yh + hh) - (- w) yh) / (norm hh)\<^sup>2 < c"
  shows False
proof -
  obtain \<delta> :: real where d0: "0 < \<delta>"
    and ltone: "\<And>q :: real^'n.
      ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
  proof (rule ell_op_usc_small_shift_lt_one[OF k(1) k(2) L])
    fix dd :: real
    assume a1: "0 < dd" and a2: "dd < 1"
      and a3: "\<And>q :: real^'n.
        ell_op_usc k L q ((0::real^'n^'n) - dd *\<^sub>R mat 1) < 1"
    show thesis by (rule that[OF a1 a3])
  qed
  have Ys: "transpose (0::real^'n^'n) = 0"
    by (simp add: transpose_def vec_eq_iff)
  have ub0: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
      ((- w) (yh + hh) - (- w) yh - (- (0::real^'n)) \<bullet> hh
        - (hh \<bullet> ((- (0::real^'n^'n)) *v hh))/2) / (norm hh)\<^sup>2 < c"
    using ub by simp
  have one: "1 \<le> ell_op_usc k L (0::real^'n)
      ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound_onesided[OF sup yh Ys ub0 d0])
  show False using one ltone[of "0::real^'n"] by simp

qed

theorem supersol_no_vanishing_jet:
  fixes w :: "real^'n::finite \<Rightarrow> real"
  assumes sup: "supersol_jet k L \<Omega> w"
    and yh: "yh \<in> \<Omega>"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and jet: "((\<lambda>h. ((- w) (yh + h) - (- w) yh) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  obtain \<delta> :: real where d0: "0 < \<delta>"
    and ltone: "\<And>q :: real^'n.
      ell_op_usc k L q ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1) < 1"
  proof (rule ell_op_usc_small_shift_lt_one[OF k(1) k(2) L])
    fix dd :: real
    assume a1: "0 < dd" and a2: "dd < 1"
      and a3: "\<And>q :: real^'n.
        ell_op_usc k L q ((0::real^'n^'n) - dd *\<^sub>R mat 1) < 1"
    show thesis by (rule that[OF a1 a3])
  qed
  have Ys: "transpose (0::real^'n^'n) = 0"
    by (simp add: transpose_def vec_eq_iff)
  have jet0: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- (0::real^'n)) \<bullet> h
      - (h \<bullet> ((- (0::real^'n^'n)) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using jet by simp
  have one: "1 \<le> ell_op_usc k L (0::real^'n)
      ((0::real^'n^'n) - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound[OF sup yh Ys jet0 d0])
  show False using one ltone[of "0::real^'n"] by simp

qed

subsection \<open>Theorem 4.2(a): the closing chain from jets\<close>

text \<open>Theorem 4.2(a) from second-order jets for \<open>\<theta> u\<close> at \<open>xh\<close> and for
  \<open>-w\<close> at \<open>yh\<close> with a common gradient \<open>p\<close>, the ordering
  \<open>psd (Ym - Xm)\<close>, symmetry of both matrices, and the off-diagonal
  condition \<open>p \<noteq> 0\<close>. The shift correction \<open>\<delta>\<close> used to reach genuine
  local extrema is removed by the lower and upper envelopes and does not
  appear in the statement.\<close>

theorem comparison_env_from_jets:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Xm Ym :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and xh: "xh \<in> \<Omega>" and yh: "yh \<in> \<Omega>"
    and Xs: "transpose Xm = Xm" and Ys: "transpose Ym = Ym"
    and psd: "psd (Ym - Xm)"
    and p: "p \<noteq> 0"
    and k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and jetu: "((\<lambda>h. (\<theta> * u (xh + h) - \<theta> * u xh - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "((\<lambda>h. ((- w) (yh + h) - (- w) yh - (- p) \<bullet> h
        - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  have subs: "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule subsol_shifted_bound[OF sub t(1) xh Xs k(1) k(2) L jetu that(1)])
  have sups: "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule supersol_shifted_bound_ne[OF sup yh k(1) k(2) L Ys jetw
          that(1) p])
  show False
    by (rule env_strict_contradiction_of_shifts[OF psd Xs Ys p k(1) k(2) L
          zero_less_one t(2) subs sups])
qed

text \<open>The same conclusion with the off-diagonal condition \<open>p \<noteq> 0\<close>
  replaced, via \<open>doubling_grad_nonzero\<close>, by the statement that \<open>xh\<close>
  fails to maximise \<open>u - w\<close> over \<open>K\<close>.\<close>

subsection \<open>Wiring the theorem on sums to the ordering hypothesis\<close>

text \<open>\<open>comparison_env_from_jets\<close> consumes \<open>psd (Ym - Xm)\<close>. The theorem
  on sums (\<open>sums_matrix_inequality\<close>, @{theory Alexandrov_Sup_Convolution.Sup_Convolution}) delivers the
  ordering between the two diagonal blocks. Writing
  \<open>X v = fst (W (v,0)) + \<alpha> v\<close> and
  \<open>Y v = - (snd (W (0,v)) + \<alpha> v)\<close> (negated since the supersolution
  enters the doubled functional as \<open>-w\<close>), this reads
  \<open>v \<cdot> X v \<le> v \<cdot> Y v\<close>; the \<open>+ \<alpha> v\<close> term in each block is the penalty's
  second derivative restricted to that block.\<close>

theorem sums_gives_ordering:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and scW: "\<And>s u. W (s *\<^sub>R u) = s *\<^sub>R W u"
    and neg: "\<And>k. k \<bullet> W k \<le> 0"
  shows "v \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)
       \<le> v \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof (cases "v = 0")
  case True
  then show ?thesis by simp
next
  case False
  have raw: "v \<bullet> fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
       + v \<bullet> snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0)) \<le> 0"
    by (rule sums_matrix_inequality[OF expPsi scW neg False])
  have e1: "fst (W (v, 0) + \<alpha> *\<^sub>R (v - 0, 0 - v))
      = fst (W (v, 0)) + \<alpha> *\<^sub>R v"
    by simp
  have e2: "snd (W (0, v) + \<alpha> *\<^sub>R (0 - v, v - 0))
      = snd (W (0, v)) + \<alpha> *\<^sub>R v"
    by simp
  from raw have h: "v \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)
       + v \<bullet> (snd (W (0, v)) + \<alpha> *\<^sub>R v) \<le> 0"
    unfolding e1 e2 .
  have neg_eq: "v \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))
      = - (v \<bullet> (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule inner_minus_right)
  show ?thesis
    unfolding neg_eq using h by linarith
qed

text \<open>With linearity and symmetry of the two blocks, supplied by the
  Alexandrov jet's bounded linear and symmetric Hessian, the ordering
  becomes the \<open>psd\<close> hypothesis \<open>comparison_env_from_jets\<close> wants.\<close>

subsection \<open>Discharging the negativity hypothesis at the doubled maximum\<close>

text \<open>The hypothesis \<open>k \<cdot> W k \<le> 0\<close> of \<open>sums_gives_ordering\<close> is what
  \<open>second_order_interior_max\<close> gives at an interior maximum, which the
  doubled functional has by construction; the ordering then depends only
  on the maximum property and the jet.\<close>

theorem sums_ordering_at_interior_max:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)
       \<le> v \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z::(real^'n) \<times> (real^'n).
      a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)"
  have mxP: "\<Psi> (zh + k) \<le> \<Psi> zh" if "norm k < d" for k
    unfolding \<Psi>_def by (rule mx[OF that])
  have expP: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
      / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding \<Psi>_def by (rule expPsi)
  have neg: "k \<bullet> W k \<le> 0" for k
    using second_order_interior_max[OF blW dpos mxP expP] by blast
  have scW: "W (s *\<^sub>R u) = s *\<^sub>R W u" for s :: real and u
    using blW by (simp add: linear_simps)
  show ?thesis
    by (rule sums_gives_ordering[OF expPsi scW neg])
qed

text \<open>The same conclusion in \<open>psd\<close> form, consumed by
  \<open>comparison_env_from_jets\<close>, depending only on the maximum property of
  the doubled functional, its Alexandrov jet, and the linearity and
  symmetry of the two diagonal blocks.\<close>

corollary sums_psd_at_interior_max:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and lX: "linear (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    and lY: "linear (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    and symX: "\<And>v z. v \<bullet> (fst (W (z, 0)) + \<alpha> *\<^sub>R z)
        = z \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    and symY: "\<And>v z. v \<bullet> (- (snd (W (0, z)) + \<alpha> *\<^sub>R z))
        = z \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
  shows "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
            - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
  by (rule psd_of_abstract_le[OF lX lY symX symY
        sums_ordering_at_interior_max[OF blW dpos mx expPsi]])

subsection \<open>Instantiating at the doubled sup-convolutions\<close>

text \<open>The doubled functional built from the sup-convolutions of \<open>u\<close> and
  \<open>w\<close> is semiconvex (\<open>doubled_functional_semiconvex\<close>) with constant
  \<open>1/\<epsilon> + 1/\<epsilon> + 2\<alpha>\<close>, one \<open>1/\<epsilon>\<close> from each sup-convolution and \<open>2\<alpha>\<close>
  from the penalty; positive as soon as \<open>\<epsilon> > 0\<close>, so Jensen's lemma
  applies and produces a point carrying a genuine Alexandrov jet.\<close>

lemma doubled_semiconvexity_constant_pos:
  fixes \<epsilon> \<alpha> :: real
  assumes e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
  shows "0 < 1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>"
proof -
  have inv: "0 < inverse \<epsilon>"
    by (rule positive_imp_inverse_positive[OF e])
  have "0 < 1/\<epsilon>"
    using inv by (simp add: inverse_eq_divide)
  then show ?thesis using a by linarith
qed

theorem doubled_supconv_jet_exists:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. w y \<le> Bw"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi>
        \<Longrightarrow> supconv u \<epsilon> (fst y) + supconv w \<epsilon> (snd y)
              - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2 \<le> m"
    and d: "0 < dd"
    and small: "2 * dd * r
        < (supconv u \<epsilon> (fst \<xi>) + supconv w \<epsilon> (snd \<xi>)
            - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2) - m"
  shows "\<exists>zh p q W. dist zh \<xi> < \<rho> \<and> norm p \<le> dd
      \<and> (\<forall>y \<in> cball \<xi> r.
          (supconv u \<epsilon> (fst y) + supconv w \<epsilon> (snd y)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
          \<le> (supconv u \<epsilon> (fst zh) + supconv w \<epsilon> (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>k. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) * (norm k)\<^sup>2) \<le> k \<bullet> W k)
      \<and> ((\<lambda>k. ((supconv u \<epsilon> (fst (zh + k)) + supconv w \<epsilon> (snd (zh + k))
              - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
            - (supconv u \<epsilon> (fst zh) + supconv w \<epsilon> (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
            - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have cvx: "convex_on UNIV (\<lambda>z::(real^'n) \<times> (real^'n).
      (supconv u \<epsilon> (fst z) + supconv w \<epsilon> (snd z)
        - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>)/2) * (norm z)\<^sup>2)"
    by (rule doubled_functional_semiconvex[OF Bu Bw e a])
  have c: "0 < 1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>"
    by (rule doubled_semiconvexity_constant_pos[OF e a])
  show ?thesis
    by (rule semiconvex_jensen_alexandrov_point[OF cvx c rho(1) rho(2)
          bnd d small])
qed

text \<open>The shifted version of Jensen's lemma for the doubled sup-convolution
  functional, giving the strict inequality Jensen needs: subtracting
  \<open>\<delta>\<parallel>z - \<xi>\<^sub>0\<parallel>\<^sup>2\<close> turns a plain maximiser \<open>\<xi>\<^sub>0\<close> into a strict one, with
  gap \<open>\<delta>\<rho>\<^sup>2\<close> on the annulus. By \<open>norm_sq_prod_split\<close> the perturbation
  splits across the two blocks, so the perturbed functional keeps the
  doubled form \<open>a (fst z) + b (snd z) - penalty\<close>.\<close>

lemma norm_sq_prod_split:
  fixes z c :: "('a::euclidean_space) \<times> 'a"
  shows "(norm (z - c))\<^sup>2
       = (norm (fst z - fst c))\<^sup>2 + (norm (snd z - snd c))\<^sup>2"
  by (simp add: power2_norm_eq_inner inner_prod_def)

theorem doubled_supconv_jet_exists_shifted:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. w y \<le> Bw"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>" and dnn: "0 \<le> \<delta>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi>
        \<Longrightarrow> (supconv u \<epsilon> (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
              + (supconv w \<epsilon> (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
              - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2 \<le> m"
    and d: "0 < dd"
    and small: "2 * dd * r
        < ((supconv u \<epsilon> (fst \<xi>) - \<delta> * (norm (fst \<xi> - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd \<xi>) - \<delta> * (norm (snd \<xi> - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2) - m"
  shows "\<exists>zh p q W. dist zh \<xi> < \<rho> \<and> norm p \<le> dd
      \<and> (\<forall>y \<in> cball \<xi> r.
          ((supconv u \<epsilon> (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
          \<le> ((supconv u \<epsilon> (fst zh) - \<delta> * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd zh) - \<delta> * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>k. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*\<delta>) * (norm k)\<^sup>2) \<le> k \<bullet> W k)
      \<and> ((\<lambda>k. (((supconv u \<epsilon> (fst (zh + k)) - \<delta> * (norm (fst (zh + k) - fst \<xi>\<^sub>0))\<^sup>2)
              + (supconv w \<epsilon> (snd (zh + k)) - \<delta> * (norm (snd (zh + k) - snd \<xi>\<^sub>0))\<^sup>2)
              - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
            - ((supconv u \<epsilon> (fst zh) - \<delta> * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
              + (supconv w \<epsilon> (snd zh) - \<delta> * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
            - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have split: "(supconv u \<epsilon> (fst z) - \<delta> * (norm (fst z - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv w \<epsilon> (snd z) - \<delta> * (norm (snd z - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2
      = (supconv u \<epsilon> (fst z) + supconv w \<epsilon> (snd z)
          - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
        - \<delta> * (norm (z - \<xi>\<^sub>0))\<^sup>2"
    for z
    by (simp add: norm_sq_prod_split algebra_simps)
  have cvx: "convex_on UNIV (\<lambda>z.
      ((supconv u \<epsilon> (fst z) - \<delta> * (norm (fst z - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv w \<epsilon> (snd z) - \<delta> * (norm (snd z - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2)
      + ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*\<delta>)/2) * (norm z)\<^sup>2)"
    unfolding split
    by (rule doubled_functional_semiconvex_shifted[OF Bu Bw e a])
  have c: "0 < 1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*\<delta>"
    using doubled_semiconvexity_constant_pos[OF e a] dnn by linarith
  show ?thesis
    by (rule semiconvex_jensen_alexandrov_point[OF cvx c rho(1) rho(2)
          bnd d small])
qed

text \<open>Subtracting \<open>\<delta>\<parallel>y - \<xi>\<^sub>0\<parallel>\<^sup>2\<close> costs at least \<open>\<delta>\<rho>\<^sup>2\<close> outside the
  \<open>\<rho>\<close>-ball and nothing at the centre, turning a plain maximiser of
  \<open>\<Phi>\<close> into a strict one; stated abstractly in \<open>\<Phi>\<close> since nothing about
  the doubling is used.\<close>

lemma shifted_annulus_bound:
  fixes \<Phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow> \<Phi> y \<le> \<Phi> \<xi>\<^sub>0"
    and dpos: "0 \<le> \<delta>" and rho: "0 < \<rho>"
    and y: "y \<in> cball \<xi>\<^sub>0 r" and ann: "\<rho> \<le> dist y \<xi>\<^sub>0"
  shows "\<Phi> y - \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2 \<le> \<Phi> \<xi>\<^sub>0 - \<delta> * \<rho>\<^sup>2"
proof -
  have dn: "dist y \<xi>\<^sub>0 = norm (y - \<xi>\<^sub>0)"
    by (simp add: dist_norm)
  have "\<rho>\<^sup>2 \<le> (norm (y - \<xi>\<^sub>0))\<^sup>2"
    using ann rho unfolding dn by (simp add: power_mono)
  then have "\<delta> * \<rho>\<^sup>2 \<le> \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    by (rule mult_left_mono[OF _ dpos])
  moreover have "\<Phi> y \<le> \<Phi> \<xi>\<^sub>0" by (rule mx[OF y])
  ultimately show ?thesis by linarith
qed

text \<open>With \<open>m = \<Phi> \<xi>\<^sub>0 - \<delta>\<rho>\<^sup>2\<close>, the smallness condition
  \<open>doubled_supconv_jet_exists_shifted\<close> needs reduces to
  \<open>2 dd r < \<delta>\<rho>\<^sup>2\<close>, a condition on \<open>dd, r, \<delta>, \<rho>\<close> alone, so \<open>dd\<close> can
  always be chosen after \<open>\<delta>\<close> and \<open>\<rho>\<close>.\<close>

lemma shifted_jensen_smallness:
  fixes \<Phi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes r: "0 < r" and dpos: "0 < \<delta>" and rho: "0 < \<rho>"
    and ddlt: "dd < (\<delta> * \<rho>\<^sup>2) / (2*r)"
  shows "2 * dd * r
      < (\<Phi> \<xi>\<^sub>0 - \<delta> * (norm (\<xi>\<^sub>0 - \<xi>\<^sub>0))\<^sup>2) - (\<Phi> \<xi>\<^sub>0 - \<delta> * \<rho>\<^sup>2)"
proof -
  have r2: "0 < 2*r" using r by simp
  have "dd * (2*r) < ((\<delta> * \<rho>\<^sup>2) / (2*r)) * (2*r)"
    by (rule mult_strict_right_mono[OF ddlt r2])
  also have "((\<delta> * \<rho>\<^sup>2) / (2*r)) * (2*r) = \<delta> * \<rho>\<^sup>2"
    using r2 by simp
  finally have "dd * (2*r) < \<delta> * \<rho>\<^sup>2" .
  then have "2 * dd * r < \<delta> * \<rho>\<^sup>2"
    by (simp add: algebra_simps)
  then show ?thesis by simp
qed

text \<open>A doubling maximiser is naturally stated for the unsplit functional
  \<open>A (fst y) + B (snd y) - penalty\<close>, whereas
  \<open>doubled_supconv_jet_exists_shifted\<close> wants its annulus bound with the
  two per-block quadratics written out; \<open>norm_sq_prod_split\<close> reconciles
  the two forms, and the centre value is unchanged since both quadratics
  vanish at \<open>\<xi>\<^sub>0\<close>.\<close>

lemma shifted_annulus_bound_split:
  fixes A B :: "real^'n::finite \<Rightarrow> real"
  assumes mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        A (fst y) + B (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
        \<le> A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0) - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2"
    and dpos: "0 \<le> \<delta>" and rho: "0 < \<rho>"
    and y: "y \<in> cball \<xi>\<^sub>0 r" and ann: "\<rho> \<le> dist y \<xi>\<^sub>0"
  shows "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
      \<le> (A (fst \<xi>\<^sub>0) + B (snd \<xi>\<^sub>0)
            - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2) - \<delta> * \<rho>\<^sup>2"
proof -
  have sp: "(A (fst y) - \<delta> * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (B (snd y) - \<delta> * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
      = (A (fst y) + B (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2)
        - \<delta> * (norm (y - \<xi>\<^sub>0))\<^sup>2"
    by (simp add: norm_sq_prod_split algebra_simps)
  show ?thesis
    unfolding sp
    by (rule shifted_annulus_bound
        [where \<Phi> = "\<lambda>z. A (fst z) + B (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
           and \<xi>\<^sub>0 = \<xi>\<^sub>0 and r = r and \<delta> = \<delta> and \<rho> = \<rho>,
         OF mxK dpos rho y ann])
qed

text \<open>The slice lemmas applied to the perturbed functional give jets of
  \<open>f - \<delta>\<parallel>\<cdot> - c\<parallel>\<^sup>2\<close>; since a quadratic has an exact expansion, this
  transfers a jet of \<open>f\<close> exactly, leaving the remainder unchanged and
  shifting the gradient and Hessian by \<open>2\<delta>(x' - c)\<close> and \<open>2\<delta> I\<close>. The
  gradient shift, bounded by \<open>2\<delta>\<rho>\<close>, does not vanish for fixed \<open>\<delta>\<close>.\<close>

subsection \<open>The antisymmetric linear tilt of the doubling\<close>

text \<open>An antisymmetric linear tilt of the doubling does not bound the
  common gradient \<open>q = \<alpha>(x'-y') + \<eta> e\<close> away from zero: comparing the
  tilted functional at the maximiser against the diagonal shows the
  penalty bound acquires an \<open>\<eta>\<parallel>x'-y'\<parallel>\<close> term, degrading by exactly what
  the tilt gains.\<close>

text \<open>The jet transfer for a linear shift: a jet of \<open>f - c \<bullet> \<cdot>\<close> is a jet
  of \<open>f\<close> with the gradient moved by \<open>c\<close> and the Hessian untouched, by
  direct rewriting since the shift is affine.\<close>

lemma jet_transfer_quadratic:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes lim: "((\<lambda>h. ((f (xh + h) - \<delta> * (norm (xh + h - c))\<^sup>2)
        - (f xh - \<delta> * (norm (xh - c))\<^sup>2)
        - p \<bullet> h - (h \<bullet> X h)/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (f (xh + h) - f xh
        - (p + (2*\<delta>) *\<^sub>R (xh - c)) \<bullet> h
        - (h \<bullet> (X h + (2*\<delta>) *\<^sub>R h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have eq: "(f (xh + h) - f xh
        - (p + (2*\<delta>) *\<^sub>R (xh - c)) \<bullet> h
        - (h \<bullet> (X h + (2*\<delta>) *\<^sub>R h))/2) / (norm h)\<^sup>2
      = ((f (xh + h) - \<delta> * (norm (xh + h - c))\<^sup>2)
        - (f xh - \<delta> * (norm (xh - c))\<^sup>2)
        - p \<bullet> h - (h \<bullet> X h)/2) / (norm h)\<^sup>2" for h
  proof -
    have re: "xh + h - c = (xh - c) + h" by simp
    have sq: "(norm (xh + h - c))\<^sup>2
        = (norm (xh - c))\<^sup>2 + 2 * ((xh - c) \<bullet> h) + (norm h)\<^sup>2"
      unfolding re
      by (simp add: power2_norm_eq_inner
          inner_commute algebra_simps)
    have ip: "(p + (2*\<delta>) *\<^sub>R (xh - c)) \<bullet> h = p \<bullet> h + 2*\<delta>*((xh - c) \<bullet> h)"
      by (simp add: inner_add_left)
    have hh: "h \<bullet> (X h + (2*\<delta>) *\<^sub>R h) = h \<bullet> X h + 2*\<delta>*(norm h)\<^sup>2"
      by (simp add: inner_add_right power2_norm_eq_inner)
    show ?thesis
      unfolding sq ip hh by (simp add: algebra_simps)
  qed
  show ?thesis
    unfolding eq by (rule lim)
qed

text \<open>This delivers precisely the input of \<open>sums_psd_at_interior_max\<close>: a
  point \<open>z'\<close>, a symmetric bounded-linear \<open>W\<close>, and the second-order
  expansion of the doubled functional at \<open>z'\<close>. With
  \<open>supconv_dominates_shift\<close>, transferring the jet back to \<open>u\<close> and
  \<open>w\<close>, and \<open>comparison_env_from_jets\<close>, this completes the chain of
  Theorem 4.2(a). Jensen's lemma returns a global maximum of the tilted
  functional \<open>\<Psi> + p \<cdot> \<cdot>\<close> over \<open>cball \<xi> r\<close>, with \<open>norm p \<le> dd\<close>;
  converting it to the interior-max form needed only requires restricting
  to a ball inside \<open>cball \<xi> r\<close> around \<open>z'\<close>, permitted since
  \<open>dist z' \<xi> < \<rho> < r\<close>.\<close>

subsection \<open>From Jensen's tilted global maximum to an interior maximum\<close>

text \<open>Jensen's lemma returns a global maximum of the tilted functional
  \<open>\<Psi> + p \<cdot> \<cdot>\<close> over \<open>cball \<xi> r\<close>, whereas \<open>sums_ordering_at_interior_max\<close>
  wants a plain interior maximum on a ball. The tilt is harmless: it
  splits as \<open>fst p \<cdot> fst z + snd p \<cdot> snd z\<close> and absorbs into the two
  summands \<open>a\<close> and \<open>b\<close>, leaving the doubled block structure intact, so
  the global maximum restricts to an interior maximum on a ball of radius
  \<open>r - dist z' \<xi> > 0\<close> around \<open>z'\<close>.\<close>

lemma tilt_absorb:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
  shows "(a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + p \<bullet> z
       = (a (fst z) + fst p \<bullet> fst z) + (b (snd z) + snd p \<bullet> snd z)
         - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
  by (cases p, cases z) simp

lemma global_max_imp_interior_max:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<Psi> y \<le> \<Psi> zh"
    and kk: "norm k < r - dist zh \<xi>"
  shows "\<Psi> (zh + k) \<le> \<Psi> zh"
proof -
  have "dist (zh + k) \<xi> \<le> dist (zh + k) zh + dist zh \<xi>"
    by (rule dist_triangle)
  moreover have "dist (zh + k) zh = norm k"
    by (simp add: dist_norm)
  ultimately have "dist (zh + k) \<xi> \<le> norm k + dist zh \<xi>"
    by simp
  with kk have "dist (zh + k) \<xi> < r"
    by linarith
  then have "zh + k \<in> cball \<xi> r"
    by (simp add: dist_commute)
  then show ?thesis
    by (rule mx)
qed

lemma interior_radius_pos:
  fixes zh \<xi> :: "'a::euclidean_space"
  assumes "dist zh \<xi> < r"
  shows "0 < r - dist zh \<xi>"
  using assms by linarith

text \<open>Jensen's output becomes exactly the interior-maximum hypothesis of
  \<open>sums_ordering_at_interior_max\<close>, with the tilt absorbed into the two
  summands.\<close>

theorem doubled_tilted_interior_max:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh"
    and kk: "norm k < r - dist zh \<xi>"
  shows "(a (fst (zh + k)) + fst p \<bullet> fst (zh + k))
         + (b (snd (zh + k)) + snd p \<bullet> snd (zh + k))
         - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
       \<le> (a (fst zh) + fst p \<bullet> fst zh) + (b (snd zh) + snd p \<bullet> snd zh)
         - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
proof -
  define \<Psi> where "\<Psi> = (\<lambda>z::(real^'n) \<times> (real^'n).
      (a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + p \<bullet> z)"
  have mxP: "\<Psi> y \<le> \<Psi> zh" if "y \<in> cball \<xi> r" for y
    unfolding \<Psi>_def by (rule mx[OF that])
  have "\<Psi> (zh + k) \<le> \<Psi> zh"
    by (rule global_max_imp_interior_max
        [where \<Psi> = \<Psi> and \<xi> = \<xi> and r = r and zh = zh and k = k,
         OF mxP kk])
  then show ?thesis
    unfolding \<Psi>_def tilt_absorb .
qed

subsection \<open>The block hypotheses come from the jet itself\<close>

text \<open>The linearity and symmetry of the two diagonal blocks that
  \<open>sums_psd_at_interior_max\<close> needs follow from the Alexandrov jet's
  \<open>bounded_linear W\<close> and \<open>u \<cdot> W u' = u' \<cdot> W u\<close>, via
  \<open>linear_slice_fst\<close> / \<open>linear_slice_snd\<close> / \<open>sym_slice_fst\<close> /
  \<open>sym_slice_snd\<close> (@{theory Alexandrov_Sup_Convolution.Sup_Convolution}).\<close>

lemma linear_of_bounded_linear_prod:
  fixes W :: "'a::euclidean_space \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes blW: "bounded_linear W"
  shows "linear W"
proof (rule linearI)
  fix x y show "W (x + y) = W x + W y"
    using blW by (simp add: linear_simps)
next
  fix c x show "W (c *\<^sub>R x) = c *\<^sub>R W x"
    using blW by (simp add: linear_simps)
qed

lemma linear_block_fst:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
proof -
  have lW: "linear W"
    by (rule linear_of_bounded_linear_prod[OF blW])
  have "linear (\<lambda>z. fst (W (z, 0) + \<alpha> *\<^sub>R (z - 0, 0 - z)))"
    by (rule linear_slice_fst[OF lW])
  then show ?thesis by simp
qed

lemma linear_block_snd:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
  shows "linear (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof -
  have lW: "linear W"
    by (rule linear_of_bounded_linear_prod[OF blW])
  have "linear (\<lambda>z. - snd (W (0, z) + \<alpha> *\<^sub>R (0 - z, z - 0)))"
    by (rule linear_slice_snd[OF lW])
  then show ?thesis by simp
qed

lemma sym_block_fst:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "v \<bullet> (fst (W (z, 0)) + \<alpha> *\<^sub>R z)
       = z \<bullet> (fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
proof -
  have "v \<bullet> (\<lambda>y. fst (W (y, 0) + \<alpha> *\<^sub>R (y - 0, 0 - y))) z
      = z \<bullet> (\<lambda>y. fst (W (y, 0) + \<alpha> *\<^sub>R (y - 0, 0 - y))) v"
    by (rule sym_slice_fst[OF symW])
  then show ?thesis by simp
qed

lemma sym_block_snd:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "v \<bullet> (- (snd (W (0, z)) + \<alpha> *\<^sub>R z))
       = z \<bullet> (- (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
proof -
  have "v \<bullet> (\<lambda>y. - snd (W (0, y) + \<alpha> *\<^sub>R (0 - y, y - 0))) z
      = z \<bullet> (\<lambda>y. - snd (W (0, y) + \<alpha> *\<^sub>R (0 - y, y - 0))) v"
    by (rule sym_slice_snd[OF symW])
  then show ?thesis by simp
qed

text \<open>With those block properties, the \<open>psd\<close> ordering needs nothing beyond
  the jet and the maximum property.\<close>

theorem sums_psd_from_jet:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
            - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
proof -
  have lX: "linear (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    by (rule linear_block_fst[OF blW])
  have lY: "linear (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule linear_block_snd[OF blW])
  show ?thesis
    by (rule sums_psd_at_interior_max[OF blW dpos mx expPsi lX lY
          sym_block_fst[OF symW] sym_block_snd[OF symW]])
qed

subsection \<open>Transferring the jet back from the sup-convolution to \<open>u\<close>\<close>

text \<open>The viscosity hypotheses concern \<open>u\<close> and \<open>w\<close>, not the
  sup-convolutions. \<open>supconv_dominates_shift\<close> (@{theory Alexandrov_Sup_Convolution.Sup_Convolution})
  bridges them: if the sup-convolution at \<open>x\<close> is attained at \<open>y\<^sub>s\<close>,
  increments of \<open>u\<close> at \<open>y\<^sub>s\<close> are dominated by increments of
  \<open>supconv u \<epsilon>\<close> at \<open>x\<close> with the same increment vector \<open>k\<close>. A local
  quadratic upper bound for the sup-convolution thus transfers verbatim
  to \<open>u\<close> at the attaining point, with the same jet data \<open>(p, A)\<close>.\<close>

theorem supconv_bound_transfer:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and loc: "supconv u \<epsilon> (x + k) - supconv u \<epsilon> x \<le> c"
  shows "u (ys + k) - u ys \<le> c"
proof -
  have "u (ys + k) - u ys \<le> supconv u \<epsilon> (x + k) - supconv u \<epsilon> x"
    by (rule supconv_dominates_shift[OF B e opt])
  with loc show ?thesis by linarith
qed

text \<open>A quadratic local upper bound for \<open>supconv u \<epsilon>\<close> at \<open>x\<close> becomes the
  same bound for \<open>u\<close> at \<open>y\<^sub>s\<close>, the hypothesis \<open>jet_imp_local_max_test\<close>
  produces and \<open>subsol_shifted_bound\<close> consumes, now stated for \<open>u\<close>
  itself.\<close>

theorem supconv_local_max_transfer:
  fixes u :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and lm: "\<And>h. norm h < d \<Longrightarrow>
        supconv u \<epsilon> (x + h) - (p \<bullet> h + (h \<bullet> (A *v h))/2) \<le> supconv u \<epsilon> x"
    and k: "norm k < d"
  shows "u (ys + k) - (p \<bullet> k + (k \<bullet> (A *v k))/2) \<le> u ys"
proof -
  have "supconv u \<epsilon> (x + k) - supconv u \<epsilon> x \<le> p \<bullet> k + (k \<bullet> (A *v k))/2"
    using lm[OF k] by linarith
  then have "u (ys + k) - u ys \<le> p \<bullet> k + (k \<bullet> (A *v k))/2"
    by (rule supconv_bound_transfer[OF B e opt])
  then show ?thesis by linarith
qed

text \<open>The ball form used by \<open>visc_subsol\<close> and \<open>supersol_jet\<close>: the local
  statement about \<open>supconv u \<epsilon>\<close> near \<open>x\<close> becomes a local statement about
  \<open>u\<close> near \<open>y\<^sub>s\<close>, on a ball of the same radius.\<close>

corollary supconv_local_max_transfer_ball:
  fixes u :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n^'n"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and dpos: "0 < d"
    and lm: "\<And>h. norm h < d \<Longrightarrow>
        supconv u \<epsilon> (x + h) - (p \<bullet> h + (h \<bullet> (A *v h))/2) \<le> supconv u \<epsilon> x"
  shows "\<exists>e>0. \<forall>z \<in> ball ys e.
      u z - (p \<bullet> (z - ys) + ((z - ys) \<bullet> (A *v (z - ys)))/2)
      \<le> u ys - (p \<bullet> (ys - ys) + ((ys - ys) \<bullet> (A *v (ys - ys)))/2)"
proof -
  have "\<forall>z \<in> ball ys d.
      u z - (p \<bullet> (z - ys) + ((z - ys) \<bullet> (A *v (z - ys)))/2)
      \<le> u ys - (p \<bullet> (ys - ys) + ((ys - ys) \<bullet> (A *v (ys - ys)))/2)"
  proof
    fix z assume z: "z \<in> ball ys d"
    have nk: "norm (z - ys) < d"
      using z by (simp add: dist_norm norm_minus_commute)
    have yz: "ys + (z - ys) = z" by simp
    from supconv_local_max_transfer[OF B e opt lm nk]
    have "u z - (p \<bullet> (z - ys) + ((z - ys) \<bullet> (A *v (z - ys)))/2) \<le> u ys"
      unfolding yz .
    then show "u z - (p \<bullet> (z - ys) + ((z - ys) \<bullet> (A *v (z - ys)))/2)
        \<le> u ys - (p \<bullet> (ys - ys) + ((ys - ys) \<bullet> (A *v (ys - ys)))/2)"
      by simp
  qed
  with dpos show ?thesis by blast
qed

subsection \<open>Descending the one-sided bound to the attainment point\<close>

text \<open>\<open>supconv_local_max_transfer_ball\<close> descends a local max for a fixed
  quadratic; the \<open>o(|h|^2)\<close> version needed here applies it once per
  threshold \<open>c\<close>: the one-sided bound at threshold \<open>c/2\<close> is a local max
  for \<open>c *\<^sub>R mat 1\<close> with zero gradient, and descent yields the one-sided
  bound at threshold \<open>c\<close> for \<open>u\<close> at \<open>ys\<close>. Quantifying over \<open>c\<close> makes the
  Hessian effectively zero without a vanishing second-order jet directly.\<close>

lemma supconv_onesided_descent:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and ub: "\<And>c. 0 < c \<Longrightarrow> \<forall>\<^sub>F hh in at 0.
        (supconv u \<epsilon> (x + hh) - supconv u \<epsilon> x) / (norm hh)\<^sup>2 < c"
    and c: "0 < c"
  shows "\<forall>\<^sub>F hh in at 0. (u (ys + hh) - u ys) / (norm hh)\<^sup>2 < c"
proof -
  have chalf: "0 < c/2" using c by simp
  have chlt: "c/2 < c" using c by simp
  from ub[OF chalf] obtain d where dpos: "0 < d"
    and b: "\<And>hh. hh \<noteq> 0 \<Longrightarrow> dist hh 0 < d \<Longrightarrow>
      (supconv u \<epsilon> (x + hh) - supconv u \<epsilon> x) / (norm hh)\<^sup>2 < c/2"
    unfolding eventually_at by blast
  have quad: "hh \<bullet> ((c *\<^sub>R mat 1) *v hh) = c * (norm hh)\<^sup>2" for hh :: "real^'n"
    by (simp add: scaleR_matrix_vector_assoc[symmetric] power2_norm_eq_inner)
  \<comment> \<open>the one-sided bound IS a local max for the quadratic \<open>c *\<^sub>R mat 1\<close>\<close>
  have lm: "supconv u \<epsilon> (x + h)
      - ((0::real^'n) \<bullet> h + (h \<bullet> ((c *\<^sub>R mat 1) *v h))/2) \<le> supconv u \<epsilon> x"
    if nh: "norm h < d" for h
  proof (cases "h = 0")
    case True
    show ?thesis unfolding True by simp
  next
    case False
    have nn: "0 < (norm h)\<^sup>2" using False by simp
    have dh: "dist h 0 < d" using nh by (simp add: dist_norm)
    have "(supconv u \<epsilon> (x + h) - supconv u \<epsilon> x) / (norm h)\<^sup>2 < c/2"
      by (rule b[OF False dh])
    then have lt: "supconv u \<epsilon> (x + h) - supconv u \<epsilon> x < (c/2) * (norm h)\<^sup>2"
      using nn by (simp add: field_simps)
    show ?thesis unfolding quad using lt by simp
  qed
  obtain ee where eepos: "0 < ee"
    and ballb: "\<And>z. z \<in> ball ys ee \<Longrightarrow>
      u z - ((0::real^'n) \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((c *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> u ys - ((0::real^'n) \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((c *\<^sub>R mat 1) *v (ys - ys)))/2)"
    using supconv_local_max_transfer_ball[OF B e opt dpos lm] by blast
  have main: "(u (ys + hh) - u ys) / (norm hh)\<^sup>2 < c"
    if h0: "hh \<noteq> 0" and hd: "dist hh 0 < ee" for hh
  proof -
    have nn: "0 < (norm hh)\<^sup>2" using h0 by simp
    have zb: "ys + hh \<in> ball ys ee" using hd by (simp add: dist_norm)
    have zz: "(ys + hh) - ys = hh" by simp
    from ballb[OF zb]
    have h1: "u (ys + hh) - (hh \<bullet> ((c *\<^sub>R mat 1) *v hh))/2 \<le> u ys"
      unfolding zz by simp
    have h2: "u (ys + hh) - u ys \<le> (c * (norm hh)\<^sup>2)/2"
      using h1 unfolding quad by linarith
    have "(u (ys + hh) - u ys) / (norm hh)\<^sup>2
        \<le> ((c * (norm hh)\<^sup>2)/2) / (norm hh)\<^sup>2"
      by (rule divide_right_mono[OF h2]) simp
    also have "((c * (norm hh)\<^sup>2)/2) / (norm hh)\<^sup>2 = c/2"
      using nn by (simp add: field_simps)
    finally show ?thesis using chlt by linarith
  qed
  show ?thesis unfolding eventually_at using eepos main by blast
qed

subsection \<open>Symmetry of the two block matrices\<close>

text \<open>The symmetry \<open>transpose Xm = Xm\<close> and \<open>transpose Ym = Ym\<close> needed by
  \<open>comparison_env_from_jets\<close> follows from the jet: \<open>matrix_of_symmetric\<close>
  (@{theory Alexandrov_Sup_Convolution.Sup_Convolution}) converts an abstract symmetric linear map into a
  symmetric matrix, fed by the block lemmas above.\<close>

lemma transpose_matrix_block_fst:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "transpose (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
       = matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
  by (rule matrix_of_symmetric[OF linear_block_fst[OF blW]
        sym_block_fst[OF symW]])

lemma transpose_matrix_block_snd:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
  shows "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
       = matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
  by (rule matrix_of_symmetric[OF linear_block_snd[OF blW]
        sym_block_snd[OF symW]])

text \<open>The jet alone yields all three matrix hypotheses of
  \<open>comparison_env_from_jets\<close>: both block matrices are symmetric, and
  they are ordered.\<close>

theorem block_matrices_from_jet:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow>
        a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>k. ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "transpose (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
           = matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    and "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
           = matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    and "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
            - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
proof -
  show "transpose (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      = matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    by (rule transpose_matrix_block_fst[OF blW symW])
  show "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      = matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule transpose_matrix_block_snd[OF blW symW])
  show "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
    by (rule sums_psd_from_jet[OF blW symW dpos mx expPsi])
qed

subsection \<open>The gradient alignment\<close>

text \<open>\<open>comparison_env_from_jets\<close> needs the jets of \<open>\<theta> u\<close> at \<open>x'\<close> and of
  \<open>-w\<close> at \<open>y'\<close> to share a common gradient \<open>p\<close> (with sign \<open>p\<close>, \<open>-p\<close>).
  Since the penalty \<open>-(\<alpha>/2)\<bar>x - y\<bar>\<^sup>2\<close> contributes \<open>\<minusplus>\<alpha>(x - y)\<close> to the
  two blocks, this holds exactly when the doubled gradient
  \<open>q\<^sub>1 + q\<^sub>2 = 0\<close>, which is automatic since \<open>q = 0\<close> at an interior
  maximum (\<open>second_order_interior_max\<close>). This gives the common gradient
  \<open>p = \<alpha>(x' - y')\<close>, whose nonvanishing \<open>doubling_grad_nonzero\<close>
  establishes.\<close>

theorem gradient_vanishes_at_interior_max:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes blW: "bounded_linear W" and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow> \<Psi> (zh + k) \<le> \<Psi> zh"
    and expPsi: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
        / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = 0"
proof -
  have "q \<bullet> q = 0"
    using second_order_interior_max[OF blW dpos mx expPsi] by blast
  then show ?thesis
    by simp
qed

text \<open>Consequently the jet at the doubled maximum has no first-order term
  at all.\<close>

text \<open>With \<open>q = 0\<close>, the first block's gradient is \<open>\<alpha>(x' - y')\<close> and the
  second block's is its negative, so a single \<open>p\<close> serves both jets, as
  \<open>comparison_env_from_jets\<close> requires.\<close>

subsection \<open>Theorem 4.2(a), end to end\<close>

text \<open>Every matrix hypothesis is derived from the Alexandrov data of the
  doubled functional, with shared gradient \<open>\<alpha>(x' - y')\<close> on both sides.
  What remains as hypotheses: the two viscosity properties, the scaling
  parameter, the interior maximum of the doubled functional with its
  jet, the off-diagonal condition, and the two jets of \<open>\<theta> u\<close> and
  \<open>-w\<close> at the two component points.\<close>

theorem comparison_env_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and a b :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and xhO: "xh \<in> \<Omega>" and yhO: "yh \<in> \<Omega>"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and blW: "bounded_linear W"
    and symW: "\<And>z z'. z \<bullet> W z' = z' \<bullet> W z"
    and dpos: "0 < dd"
    and mx: "\<And>hk. norm hk < dd \<Longrightarrow>
        a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and nz: "\<alpha> *\<^sub>R (xh - yh) \<noteq> 0"
    and jetu: "((\<lambda>h. (\<theta> * u (xh + h) - \<theta> * u xh
        - (\<alpha> *\<^sub>R (xh - yh)) \<bullet> h
        - (h \<bullet> (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "((\<lambda>h. ((- w) (yh + h) - (- w) yh
        - (- (\<alpha> *\<^sub>R (xh - yh))) \<bullet> h
        - (h \<bullet> ((- matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  have symX: "transpose (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      = matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v)"
    by (rule block_matrices_from_jet(1)[OF blW symW dpos mx expPsi])
  have symY: "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      = matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule block_matrices_from_jet(2)[OF blW symW dpos mx expPsi])
  have psdXY: "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
    by (rule block_matrices_from_jet(3)[OF blW symW dpos mx expPsi])
  show False
    by (rule comparison_env_from_jets[OF sub sup t(1) t(2) xhO yhO symX symY
          psdXY nz kk(1) kk(2) LL jetu jetw])
qed

text \<open>The same, with the off-diagonal condition traded for the statement
  that \<open>x'\<close> fails to maximise \<open>u - w\<close> over \<open>K\<close>; by the gradient
  alignment this is the same condition as \<open>p \<noteq> 0\<close>.\<close>

subsection \<open>Deriving the component jets from the doubled jet\<close>

text \<open>The two component jets \<open>comparison_env_complete\<close> takes as
  hypotheses come from the doubled jet by restricting to the two
  coordinate slices. Moving the first argument by \<open>h\<close> and holding the
  second fixed changes \<open>(\<alpha>/2)\<bar>x - y\<bar>\<^sup>2\<close> by a linear term
  \<open>\<alpha>(x - y) \<cdot> h\<close> plus a quadratic term \<open>(\<alpha>/2)\<bar>h\<bar>\<^sup>2\<close>, exactly, since
  the penalty's Taylor expansion is exact -- the source of both the
  \<open>\<alpha>(x' - y')\<close> in the gradient and the \<open>+ \<alpha> v\<close> in the Hessian block.\<close>

lemma penalty_difference_identity:
  fixes x y h :: "real^'n::finite"
  shows "(\<alpha>/2) * (norm (x + h - y))\<^sup>2 - (\<alpha>/2) * (norm (x - y))\<^sup>2
       = \<alpha> * ((x - y) \<bullet> h) + (\<alpha>/2) * (norm h)\<^sup>2"
proof -
  have "(norm (x + h - y))\<^sup>2 = (norm ((x - y) + h))\<^sup>2"
    by (simp add: algebra_simps)
  also have "\<dots> = (norm (x - y))\<^sup>2 + 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2"
    by (simp add: power2_norm_eq_inner
        inner_commute algebra_simps)
  finally show ?thesis
    by (simp add: field_simps)
qed

text \<open>The slice embedding is a legitimate change of filter: as \<open>h\<close> tends
  to \<open>0\<close> in \<open>real^'n\<close> avoiding \<open>0\<close>, the pair \<open>(h, 0)\<close> tends to \<open>0\<close> in
  the product avoiding \<open>0\<close>, letting a limit statement about the doubled
  functional be evaluated along the slice.\<close>

lemma filterlim_slice_fst:
  "filterlim (\<lambda>h::real^'n::finite. (h, 0::real^'n)) (at 0) (at 0)"
proof (rule filterlim_atI)
  show "((\<lambda>h::real^'n. (h, 0::real^'n)) \<longlongrightarrow> 0) (at 0)"
    by (simp add: zero_prod_def tendsto_Pair)
next
  show "\<forall>\<^sub>F h in at (0 :: real^'n). (h, 0::real^'n) \<noteq> 0"
    by (simp add: eventually_at_filter zero_prod_def)
qed

lemma filterlim_slice_snd:
  "filterlim (\<lambda>h::real^'n::finite. (0::real^'n, h)) (at 0) (at 0)"
proof (rule filterlim_atI)
  show "((\<lambda>h::real^'n. (0::real^'n, h)) \<longlongrightarrow> 0) (at 0)"
    by (simp add: zero_prod_def tendsto_Pair)
next
  show "\<forall>\<^sub>F h in at (0 :: real^'n). (0::real^'n, h) \<noteq> 0"
    by (simp add: eventually_at_filter zero_prod_def)
qed

text \<open>The norm of a slice vector is the norm of its nonzero component,
  which keeps the quotient in the jet transfer unchanged.\<close>

text \<open>The doubled jet restricts to the first slice: the \<open>b\<close> terms cancel
  since the second argument does not move, the penalty contributes
  \<open>\<alpha>(x' - y') \<cdot> h\<close> to the gradient and \<open>\<alpha> h\<close> to the Hessian, and
  \<open>W\<close> contributes its first diagonal block, exactly the block \<open>X\<close> of
  the theorem on sums.\<close>

lemma doubled_slice_numerator_fst:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  shows "((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
        - (\<alpha>/2) * (norm (fst (zh + (h, 0)) - snd (zh + (h, 0))))\<^sup>2)
      - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
      - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2)
    = a (fst zh + h) - a (fst zh)
      - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
      - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2"
proof -
  have p: "(\<alpha>/2) * (norm (fst zh + h - snd zh))\<^sup>2
      - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      = \<alpha> * ((fst zh - snd zh) \<bullet> h) + (\<alpha>/2) * (norm h)\<^sup>2"
    by (rule penalty_difference_identity)
  show ?thesis
    using p by (simp add: inner_prod_def inner_commute
        power2_norm_eq_inner algebra_simps)
qed

theorem doubled_jet_slice_fst:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have comp: "((\<lambda>h. ((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - (\<alpha>/2) * (norm (fst (zh + (h, 0)) - snd (zh + (h, 0))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_fst]
    by (simp add: o_def)
  have eq: "((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - (\<alpha>/2) * (norm (fst (zh + (h, 0)) - snd (zh + (h, 0))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2
      = (a (fst zh + h) - a (fst zh)
        - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2" for h
    unfolding doubled_slice_numerator_fst
    by (simp add: norm_Pair)
  from comp[unfolded eq] show ?thesis .
qed

text \<open>The same restriction for an arbitrary penalty \<open>P\<close> given by its jet: a
  general \<open>P\<close> has a remainder rather than an exact identity, so the two
  limits are added via \<open>tendsto_add\<close>, since \<open>P(d+h) - P(d)\<close> cancels
  between them (\<open>d = x' - y'\<close>). The resulting jet has gradient
  \<open>fst q + G\<close> and Hessian \<open>fst (W (h,0)) + Z h\<close>, the quadratic
  statement with \<open>\<alpha>(x' - y')\<close> replaced by \<open>G\<close> and \<open>\<alpha> h\<close> by \<open>Z h\<close>.\<close>

theorem doubled_jet_slice_fst_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have comp: "((\<lambda>h. ((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_fst]
    by (simp add: o_def)
  have sum0: "((\<lambda>h. (((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      + ((P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
    using tendsto_add[OF comp Pjet] by simp
  have eq: "(((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
          - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2) / (norm ((h, 0)))\<^sup>2)
      + ((P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)
    = (a (fst zh + h) - a (fst zh)
        - (fst q + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2" for h
  proof -
    have np: "norm ((h, 0) :: (real^'n) \<times> (real^'n)) = norm h"
      by (simp add: norm_Pair)
    have num: "((a (fst (zh + (h, 0))) + b (snd (zh + (h, 0)))
            - P (fst (zh + (h, 0)) - snd (zh + (h, 0))))
          - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
          - q \<bullet> (h, 0) - ((h, 0) \<bullet> W (h, 0))/2)
        + (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
            - G \<bullet> h - (h \<bullet> (Z *v h))/2)
      = a (fst zh + h) - a (fst zh)
          - (fst q + G) \<bullet> h
          - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2"
      by (simp add: inner_prod_def
          algebra_simps)
    show ?thesis
      unfolding np
      using num by (simp add: add_divide_distrib[symmetric])
  qed
  from sum0[unfolded eq] show ?thesis .
qed

text \<open>The mirror image on the second slice: the penalty now moves the
  second argument, so its linear contribution changes sign, giving the
  gradient of \<open>b\<close> at \<open>y'\<close> as \<open>q\<^sub>2 - \<alpha>(x' - y')\<close>, while the quadratic
  contribution \<open>\<alpha> h\<close> to the Hessian keeps the same sign in both slices
  -- this asymmetry is what makes the two jets share \<open>p\<close> and \<open>-p\<close> while
  both blocks carry \<open>+ \<alpha> v\<close>.\<close>

lemma penalty_difference_identity_snd:
  fixes x y h :: "real^'n::finite"
  shows "(\<alpha>/2) * (norm (x - (y + h)))\<^sup>2 - (\<alpha>/2) * (norm (x - y))\<^sup>2
       = - (\<alpha> * ((x - y) \<bullet> h)) + (\<alpha>/2) * (norm h)\<^sup>2"
proof -
  have e1: "(norm (x - (y + h)))\<^sup>2
      = (norm (x - y))\<^sup>2 - 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2"
  proof -
    have "(norm (x - (y + h)))\<^sup>2 = (norm ((x - y) - h))\<^sup>2"
      by (simp add: algebra_simps)
    also have "\<dots> = (norm (x - y))\<^sup>2 - 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2"
      by (simp add: power2_norm_eq_inner
          inner_commute algebra_simps)
    finally show ?thesis .
  qed
  have e2: "(\<alpha>/2) * (norm (x - (y + h)))\<^sup>2
      = (\<alpha>/2) * ((norm (x - y))\<^sup>2 - 2 * ((x - y) \<bullet> h) + (norm h)\<^sup>2)"
    using e1 by simp
  show ?thesis
    using e2 by (simp add: algebra_simps)
qed

lemma doubled_slice_numerator_snd:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  shows "((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
        - (\<alpha>/2) * (norm (fst (zh + (0, h)) - snd (zh + (0, h))))\<^sup>2)
      - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
      - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2)
    = b (snd zh + h) - b (snd zh)
      - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
      - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2"
proof -
  have p: "(\<alpha>/2) * (norm (fst zh - (snd zh + h)))\<^sup>2
      - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      = - (\<alpha> * ((fst zh - snd zh) \<bullet> h)) + (\<alpha>/2) * (norm h)\<^sup>2"
    by (rule penalty_difference_identity_snd)
  show ?thesis
    using p by (simp add: inner_prod_def inner_commute
        power2_norm_eq_inner algebra_simps)
qed

theorem doubled_jet_slice_snd:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have comp: "((\<lambda>h. ((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - (\<alpha>/2) * (norm (fst (zh + (0, h)) - snd (zh + (0, h))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_snd]
    by (simp add: o_def)
  have eq: "((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - (\<alpha>/2) * (norm (fst (zh + (0, h)) - snd (zh + (0, h))))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2
      = (b (snd zh + h) - b (snd zh)
        - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2" for h
    unfolding doubled_slice_numerator_snd
    by (simp add: norm_Pair)
  from comp[unfolded eq] show ?thesis .
qed

text \<open>The mirror slice for a general penalty: the second slice moves \<open>y\<close>,
  so the penalty is evaluated at \<open>d - h\<close>, and the jet hypothesis is
  transported along \<open>h \<mapsto> -h\<close>, a filter isomorphism of \<open>at 0\<close>
  (\<open>negfilt\<close>); the sign flips in \<open>(-h) \<bullet> (Z (-h))\<close> cancel, so the
  transported remainder is the same \<open>o(\<parallel>h\<parallel>\<^sup>2)\<close> with \<open>G \<bullet> h\<close> flipped,
  exactly why the two slice gradients come out as negatives.\<close>

theorem doubled_jet_slice_snd_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - G) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have mv: "Z *v (- h) = - (Z *v h)" for h :: "real^'n"
    by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)
  have negfilt: "filterlim (\<lambda>h::real^'n. - h) (at 0) (at 0)"
  proof (rule filterlim_atI)
    have "((\<lambda>h::real^'n. - h) \<longlongrightarrow> - 0) (at 0)"
      by (intro tendsto_intros)
    then show "((\<lambda>h::real^'n. - h) \<longlongrightarrow> 0) (at 0)" by simp
    show "\<forall>\<^sub>F h in at (0::real^'n). - h \<noteq> 0"
      by (simp add: eventually_at_filter)
  qed
  have Pneg0: "((\<lambda>h. (P ((fst zh - snd zh) + - h) - P (fst zh - snd zh)
      - G \<bullet> (- h) - ((- h) \<bullet> (Z *v (- h)))/2) / (norm (- h))\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF Pjet negfilt] by (simp add: o_def)
  have Pneg: "((\<lambda>h. (P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
      + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  proof -
    have e: "(P ((fst zh - snd zh) + - h) - P (fst zh - snd zh)
          - G \<bullet> (- h) - ((- h) \<bullet> (Z *v (- h)))/2) / (norm (- h))\<^sup>2
        = (P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
          + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2" for h
      by (simp add: mv algebra_simps)
    show ?thesis using Pneg0 unfolding e .
  qed
  have comp: "((\<lambda>h. ((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - P (fst (zh + (0, h)) - snd (zh + (0, h))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using filterlim_compose[OF expPsi filterlim_slice_snd]
    by (simp add: o_def)
  have sum0: "((\<lambda>h. (((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - P (fst (zh + (0, h)) - snd (zh + (0, h))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      + ((P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
        + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
    using tendsto_add[OF comp Pneg] by simp
  have eq: "(((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
          - P (fst (zh + (0, h)) - snd (zh + (0, h))))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2) / (norm ((0, h)))\<^sup>2)
      + ((P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
        + G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2)
    = (b (snd zh + h) - b (snd zh)
        - (snd q - G) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2" for h
  proof -
    have np: "norm ((0, h) :: (real^'n) \<times> (real^'n)) = norm h"
      by (simp add: norm_Pair)
    have num: "((a (fst (zh + (0, h))) + b (snd (zh + (0, h)))
            - P (fst (zh + (0, h)) - snd (zh + (0, h))))
          - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
          - q \<bullet> (0, h) - ((0, h) \<bullet> W (0, h))/2)
        + (P (fst zh - (snd zh + h)) - P (fst zh - snd zh)
            + G \<bullet> h - (h \<bullet> (Z *v h))/2)
      = b (snd zh + h) - b (snd zh)
          - (snd q - G) \<bullet> h
          - (h \<bullet> (snd (W (0, h)) + Z *v h))/2"
      by (simp add: inner_prod_def
          algebra_simps)
    show ?thesis
      unfolding np
      using num by (simp add: add_divide_distrib[symmetric])
  qed
  from sum0[unfolded eq] show ?thesis .
qed

text \<open>With \<open>q = 0\<close> at the doubled maximum
  (\<open>gradient_vanishes_at_interior_max\<close>) the two gradients become
  \<open>\<alpha>(x' - y')\<close> and \<open>-\<alpha>(x' - y')\<close>, the shared \<open>p\<close> and \<open>-p\<close> that
  \<open>comparison_env_complete\<close> requires.\<close>

corollary doubled_jet_slices_at_max:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W" and dpos: "0 < dd"
    and mx: "\<And>hk. norm hk < dd \<Longrightarrow>
        a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2
        \<le> a (fst zh) + b (snd zh)
          - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (\<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (\<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have q0: "q = 0"
    by (rule gradient_vanishes_at_interior_max[where \<Psi> = "\<lambda>z.
          a (fst z) + b (snd z) - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
          and zh = zh and q = q and W = W and d = dd,
        OF blW dpos mx expPsi])
  show "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (\<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using doubled_jet_slice_fst[OF expPsi] unfolding q0 by simp
  show "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (\<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using doubled_jet_slice_snd[OF expPsi] unfolding q0 by simp
qed

subsection \<open>Matching the block Hessians against their matrices\<close>

text \<open>The slice jets carry their Hessians as functions
  \<open>h \<mapsto> fst (W (h,0)) + \<alpha> h\<close> and \<open>h \<mapsto> snd (W (0,h)) + \<alpha> h\<close>, while the
  viscosity machinery wants matrices. \<open>matrix_works\<close> bridges them, but
  is stated for \<open>Vector_Spaces.linear\<close>, so real-vector-space \<open>linear\<close>
  must be routed through \<open>linear_matrix_vector_mul_eq\<close> first.\<close>

text \<open>\<open>matrix_apply_eq\<close> is \<open>matrix_vec_apply\<close> from
  @{theory Alexandrov_Sup_Convolution.Sup_Convolution}.\<close>

lemma block_fst_matrix_apply:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
  shows "matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v) *v h
       = fst (W (h, 0)) + \<alpha> *\<^sub>R h"
  by (rule matrix_vec_apply[OF linear_block_fst[OF blW]])

lemma block_snd_matrix_apply:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
  shows "(- matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))) *v h
       = snd (W (0, h)) + \<alpha> *\<^sub>R h"
proof -
  have l: "linear (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))"
    by (rule linear_block_snd[OF blW])
  have "(- matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))) *v h
      = - (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)) *v h)"
    by (rule matrix_vector_neg_left)
  also have "\<dots> = - (- (snd (W (0, h)) + \<alpha> *\<^sub>R h))"
    using matrix_vec_apply[OF l] by simp
  finally show ?thesis by simp
qed

subsection \<open>Theorem 4.2(a) from the doubled jet alone\<close>

text \<open>The component jets are no longer hypotheses: they are produced from
  the doubled jet by \<open>doubled_jet_slices_at_max\<close> and matched to their
  matrices by the lemmas above. What remains assumed is the doubled data
  itself -- an interior maximum of
  \<open>\<theta> u(x) - w(y) - (\<alpha>/2)\<bar>x - y\<bar>\<^sup>2\<close> at \<open>z' = (x', y')\<close> with its
  Alexandrov jet -- plus the two viscosity properties and the
  off-diagonal condition.\<close>

subsection \<open>The subsolution bound straight from a sup-convolution jet\<close>

text \<open>The comparison argument's doubled functional is built from the
  sup-convolutions of \<open>u\<close> and \<open>w\<close>, since those are what is semiconvex
  and what Jensen's lemma applies to; the jet produced at the doubled
  maximum is thus a jet of \<open>supconv (\<theta> u) \<epsilon>\<close>, not of \<open>\<theta> u\<close>. This
  theorem closes that gap: the \<open>\<delta>\<close>-corrected quadratic bound for the
  sup-convolution at \<open>x\<close> transfers, by \<open>supconv_local_max_transfer_ball\<close>,
  to the same bound for \<open>\<theta> u\<close> at the attaining point \<open>y\<^sub>s\<close> -- same
  \<open>p\<close>, same matrix -- where the viscosity property applies, with
  \<open>y\<^sub>s\<close> now the point that must lie in \<open>\<Omega>\<close>.\<close>

theorem subsol_shifted_bound_supconv:
  fixes u :: "real^'n::finite \<Rightarrow> real" and Xm :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u"
    and t: "0 < \<theta>"
    and ysO: "ys \<in> \<Omega>"
    and Xs: "transpose Xm = Xm"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
        = \<theta> * u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
proof -
  have sym: "transpose (Xm + \<delta> *\<^sub>R mat 1) = Xm + \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_add[OF Xs])
  obtain r where r: "0 < r"
    and b: "\<And>h. norm h < r \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
          - (p \<bullet> h + (h \<bullet> (Xm *v h))/2 + (\<delta>/2) * (norm h)\<^sup>2)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> x"
    using superjet_local_max[OF jet d] by blast
  have lm: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (x + h)
        - (p \<bullet> h + (h \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v h))/2)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> x" if "norm h < r" for h
  proof -
    have q: "h \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v h)
        = h \<bullet> (Xm *v h) + \<delta> * (norm h)\<^sup>2"
      by (rule quad_form_shift_identity)
    from b[OF that] show ?thesis
      unfolding q by (simp add: add_divide_distrib)
  qed
  have maxloc: "\<exists>e>0. \<forall>z \<in> ball ys e.
      \<theta> * u z - (p \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> \<theta> * u ys - (p \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)"
    by (rule supconv_local_max_transfer_ball[OF Bu e opt r lm])
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - ys)
        + ((z - ys) \<bullet> ((Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      (\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) (Xm + \<delta> *\<^sub>R mat 1) ys"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys = p"
    by simp
  have ne: "feasible k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      \<noteq> ({} :: (real^'n^'n) set)"
    unfolding g by (rule feasible_nonempty[OF kk(1) kk(2) LL])
  have "ell_op k L ((\<lambda>z. p + (Xm + \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    by (rule visc_subsol_scaled_uniform[OF sub t ysO tf ne maxloc])
  thus ?thesis unfolding g .
qed

text \<open>The supersolution mirror: the sup-convolution is taken of \<open>-w\<close>, the
  summand the doubled functional carries, and the transferred bound
  becomes a local minimum statement for \<open>w\<close> after negation. The
  correction runs the other way, \<open>Ym - \<delta> I\<close>, as with
  \<open>jet_imp_local_min_test\<close>.\<close>

lemma neg_shift_matrix_apply:
  fixes B :: "real^'n::finite^'n"
  shows "((- B) + \<delta> *\<^sub>R mat 1) *v h = - ((B - \<delta> *\<^sub>R mat 1) *v h)"
proof -
  have e: "(- B) + \<delta> *\<^sub>R mat 1 = - (B - \<delta> *\<^sub>R mat 1)"
    by simp
  show ?thesis
    unfolding e by (rule matrix_vector_neg_left)
qed

theorem supersol_shifted_bound_supconv:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w"
    and ysO: "ys \<in> \<Omega>"
    and Ys: "transpose Ym = Ym"
    and Bw: "\<And>y. (- w) y \<le> Bw" and e: "0 < \<epsilon>"
    and opt: "supconv (- w) \<epsilon> x = (- w) ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (- w) \<epsilon> (x + h) - supconv (- w) \<epsilon> x
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>"
  shows "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have sym: "transpose (Ym - \<delta> *\<^sub>R mat 1) = Ym - \<delta> *\<^sub>R mat 1"
    by (rule transpose_shift_diff[OF Ys])
  obtain r where r: "0 < r"
    and b: "\<And>h. norm h < r \<Longrightarrow>
        supconv (- w) \<epsilon> (x + h)
          - ((- p) \<bullet> h + (h \<bullet> ((- Ym) *v h))/2 + (\<delta>/2) * (norm h)\<^sup>2)
        \<le> supconv (- w) \<epsilon> x"
    using superjet_local_max[OF jet d] by blast
  have lm: "supconv (- w) \<epsilon> (x + h)
        - ((- p) \<bullet> h + (h \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v h))/2)
      \<le> supconv (- w) \<epsilon> x" if "norm h < r" for h
  proof -
    have q: "h \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v h)
        = h \<bullet> ((- Ym) *v h) + \<delta> * (norm h)\<^sup>2"
      by (rule quad_form_shift_identity)
    from b[OF that] show ?thesis
      unfolding q by (simp add: add_divide_distrib)
  qed
  have tr: "\<exists>e>0. \<forall>z \<in> ball ys e.
      (- w) z - ((- p) \<bullet> (z - ys)
          + ((z - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> (- w) ys - ((- p) \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)"
    by (rule supconv_local_max_transfer_ball[OF Bw e opt r lm])
  obtain s where s: "0 < s"
    and m: "\<And>z. z \<in> ball ys s \<Longrightarrow>
      (- w) z - ((- p) \<bullet> (z - ys)
          + ((z - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      \<le> (- w) ys - ((- p) \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> (((- Ym) + \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)"
    using tr by blast
  have minloc: "\<exists>e>0. \<forall>z \<in> ball ys e.
      w ys - (p \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)
      \<le> w z - (p \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)"
  proof (rule exI[of _ s], intro conjI ballI)
    show "0 < s" by (rule s)
    fix z assume z: "z \<in> ball ys s"
    from m[OF z] show
      "w ys - (p \<bullet> (ys - ys)
          + ((ys - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (ys - ys)))/2)
      \<le> w z - (p \<bullet> (z - ys)
          + ((z - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)"
      unfolding neg_shift_matrix_apply
      by simp
  qed
  have tf: "test_fun_at
      (\<lambda>z. p \<bullet> (z - ys)
        + ((z - ys) \<bullet> ((Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)))/2)
      (\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) (Ym - \<delta> *\<^sub>R mat 1) ys"
    by (rule jet_test_fun_at[OF sym])
  have g: "(\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) ys = p"
    by simp
  have "1 \<le> ell_op_usc k L ((\<lambda>z. p + (Ym - \<delta> *\<^sub>R mat 1) *v (z - ys)) ys)
      (Ym - \<delta> *\<^sub>R mat 1)"
    using sup ysO tf minloc unfolding supersol_jet_def by blast
  thus ?thesis unfolding g .
qed

corollary supersol_shifted_bound_supconv_ne:
  fixes w :: "real^'n::finite \<Rightarrow> real" and Ym :: "real^'n^'n"
  assumes sup: "supersol_jet k L \<Omega> w" and ysO: "ys \<in> \<Omega>"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Ys: "transpose Ym = Ym"
    and Bw: "\<And>y. (- w) y \<le> Bw" and e: "0 < \<epsilon>"
    and opt: "supconv (- w) \<epsilon> x = (- w) ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    and jet: "((\<lambda>h. (supconv (- w) \<epsilon> (x + h) - supconv (- w) \<epsilon> x
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and d: "0 < \<delta>" and p0: "p \<noteq> 0"
  shows "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
proof -
  have "1 \<le> ell_op_usc k L p (Ym - \<delta> *\<^sub>R mat 1)"
    by (rule supersol_shifted_bound_supconv[OF sup ysO Ys Bw e opt jet d])
  then show ?thesis
    unfolding ell_op_usc_eq_at_nonzero[OF kk(1) kk(2) LL p0] by simp
qed

subsection \<open>Theorem 4.2(a) from sup-convolution jets\<close>

text \<open>The closing chain in the form the comparison argument reaches: both
  bounds come from jets of the sup-convolutions, which the doubled
  functional carries, and the two attaining points \<open>y\<^sub>s\<^sup>u\<close> and
  \<open>y\<^sub>s\<^sup>w\<close> are where the viscosity properties are applied. The uniform
  bound \<open>\<theta> < 1\<close> on the subsolution side survives the \<open>\<delta> \<rightarrow> 0\<close>
  limit and yields the strict envelope inequality; the off-diagonal
  condition \<open>p \<noteq> 0\<close> identifies the two envelopes with \<open>F\<close> itself. No
  \<open>\<delta>\<close> appears in the conclusion.\<close>

theorem comparison_supconv_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Xm Ym :: "real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and ysuO: "ysu \<in> \<Omega>" and yswO: "ysw \<in> \<Omega>"
    and Xs: "transpose Xm = Xm" and Ys: "transpose Ym = Ym"
    and psd: "psd (Ym - Xm)"
    and pnz: "p \<noteq> 0"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
    and optu: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> xu
        = \<theta> * u ysu - (dist xu ysu)\<^sup>2 / (2*\<epsilon>)"
    and optw: "supconv (- w) \<epsilon> xw = (- w) ysw - (dist xw ysw)\<^sup>2 / (2*\<epsilon>)"
    and jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> xu - p \<bullet> h
        - (h \<bullet> (Xm *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (xw + h) - supconv (- w) \<epsilon> xw
        - (- p) \<bullet> h - (h \<bullet> ((- Ym) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
  shows False
proof -
  have subs: "ell_op k L p (Xm + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule subsol_shifted_bound_supconv[OF sub t(1) ysuO Xs kk(1) kk(2) LL
          Bu e optu jetu that(1)])
  have sups: "1 \<le> ell_op k L p (Ym - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for \<delta>
    by (rule supersol_shifted_bound_supconv_ne[OF sup yswO kk(1) kk(2) LL
          Ys Bw e optw jetw that(1) pnz])
  show False
    by (rule env_strict_contradiction_of_shifts[OF psd Xs Ys pnz kk(1) kk(2) LL
          zero_less_one t(2) subs sups])
qed

subsection \<open>Theorem 4.2(a) from the doubled sup-convolution jet alone\<close>

text \<open>The full composition: the two component jets are no longer
  hypotheses but the two coordinate slices of the doubled jet, produced
  by \<open>doubled_jet_slices_at_max\<close> with \<open>a\<close> and \<open>b\<close> instantiated at the
  two sup-convolutions, and matched to their matrices by the block
  lemmas; the three matrix hypotheses come from
  \<open>block_matrices_from_jet\<close>. What remains assumed is the two viscosity
  properties, the scaling parameter \<open>\<theta>\<close>, an interior maximum of the
  doubled sup-convolution functional with its Alexandrov jet, the
  off-diagonal condition, and that each sup-convolution is attained at a
  point of \<open>\<Omega>\<close>.\<close>

subsection \<open>Absorbing Jensen's tilt: the general nearby-point form\<close>

text \<open>The tilt perturbs the gradient as well as the matrix, unlike the
  earlier shift theorems, which move only the matrix by \<open>\<delta> I\<close>; Jensen's
  tilt moves the gradient by an amount \<open>\<le> dd\<close> that is at our disposal
  but not zero. The right statement is the general one: a bound holding
  at points arbitrarily close to \<open>(p, M)\<close>, however produced, passes to
  the lower envelope -- exactly the content of \<open>F\<^sub>*\<close>, subsuming both
  the \<open>\<delta> I\<close> shifts and the tilt, with the nearby point allowed to
  depend on the radius so that \<open>dd\<close> can be chosen after it.\<close>

theorem ell_op_lsc_le_of_nearby:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
      dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e
      \<and> ell_op k L p' M' \<le> c"
  shows "ell_op_lsc k L p M \<le> ereal c"
  unfolding ell_op_lsc_def
proof (rule SUP_least)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  obtain p' M' where d: "dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e"
    and bd: "ell_op k L p' M' \<le> c"
    using b[OF e0] by blast
  have mem: "((p', M') :: (real^'n) \<times> (real^'n^'n)) \<in> ball (p, M) e"
    using d by (simp add: dist_commute)
  have "(INF v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)
      \<le> ell_op_pair k L (p', M')"
    by (rule INF_lower[OF mem])
  also have "\<dots> \<le> ereal c"
    using bd by (simp add: ell_op_pair_def)
  finally show "(INF v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)
      \<le> ereal c" .
qed

theorem ell_op_usc_ge_of_nearby:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes b: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
      dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e
      \<and> c \<le> ell_op k L p' M'"
  shows "ereal c \<le> ell_op_usc k L p M"
  unfolding ell_op_usc_def
proof (rule INF_greatest)
  fix e :: real
  assume "e \<in> {0<..}"
  then have e0: "0 < e" by simp
  obtain p' M' where d: "dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, M) < e"
    and bd: "c \<le> ell_op k L p' M'"
    using b[OF e0] by blast
  have mem: "((p', M') :: (real^'n) \<times> (real^'n^'n)) \<in> ball (p, M) e"
    using d by (simp add: dist_commute)
  have "ereal c \<le> ell_op_pair k L (p', M')"
    using bd by (simp add: ell_op_pair_def)
  also have "\<dots> \<le> (SUP v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)"
    by (rule SUP_upper[OF mem])
  finally show "ereal c
      \<le> (SUP v \<in> ball ((p :: real^'n), M) e. ell_op_pair k L v)" .
qed

text \<open>The closing contradiction in that generality: compare
  \<open>env_strict_contradiction_of_shifts\<close>, whose hypotheses no longer name
  the \<open>\<delta> I\<close> shifts, only that suitable bounds hold arbitrarily near
  \<open>(p, X)\<close> and \<open>(p, Y)\<close> -- the form the tilt-absorption argument needs,
  since there the nearby points are produced by re-running Jensen with a
  smaller \<open>dd\<close> rather than by a fixed algebraic shift.\<close>

theorem env_strict_contradiction_of_nearby:
  fixes X Y :: "real^'n::finite^'n" and p :: "real^'n"
  assumes psd: "psd (Y - X)"
    and symX: "transpose X = X" and symY: "transpose Y = Y"
    and pnz: "p \<noteq> 0" and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and c1: "c < 1"
    and subs: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
        dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X) < e
        \<and> ell_op k L p' M' \<le> c"
    and sups: "\<And>e. 0 < e \<Longrightarrow> \<exists>p' M'.
        dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y) < e
        \<and> 1 \<le> ell_op k L p' M'"
  shows False
proof -
  have lsc: "ell_op_lsc k L p X \<le> ereal c"
    by (rule ell_op_lsc_le_of_nearby[OF subs])
  have c1e: "ereal c < 1"
    using c1 by (simp add: one_ereal_def)
  have sub: "ell_op_lsc k L p X < 1"
    using lsc c1e by (rule le_less_trans)
  have sup: "1 \<le> ell_op_usc k L p Y"
    using ell_op_usc_ge_of_nearby[OF sups] by (simp add: one_ereal_def)
  show False
    by (rule ell_op_env_strict_contradiction[OF psd symX symY pnz kk(1) kk(2)
          LL sub sup])
qed

subsection \<open>The quantitative input the tilt argument needs\<close>

text \<open>The nearby-point hypothesis is discharged once the perturbed data
  approaches \<open>(p, M)\<close> at a controlled rate in the tilt parameter; this
  lemma isolates and discharges exactly that, reducing the remaining
  work to one estimate: the maximiser and its jet move at most linearly
  in \<open>dd\<close>. No convergence of the jets themselves is needed, only
  \<open>dist ((P dd, Mf dd)) (p, M) \<le> \<kappa> dd\<close> for arbitrary \<open>\<kappa>\<close>, since the
  radius is chosen after it.\<close>

text \<open>Theorem 4.2(a) reduces to one quantitative hypothesis per side: the
  perturbed gradient/matrix pair at tilt \<open>dd\<close> lies within \<open>\<kappa> dd\<close> of the
  limiting pair; the envelopes, strictness, ordering and off-diagonal
  condition are already established.\<close>

subsection \<open>A tilt that needs no limit at all\<close>

text \<open>A second way to absorb Jensen's tilt, which removes the limit rather than
  controlling it: at an interior maximum of the tilted functional, the
  untilted jet has gradient exactly \<open>-p\<close>, since the tilt contributes
  \<open>p \<bullet> k\<close> to every increment.\<close>

theorem gradient_is_minus_tilt:
  fixes \<Psi> :: "'a::euclidean_space \<Rightarrow> real"
  assumes blW: "bounded_linear W" and dpos: "0 < d"
    and mx: "\<And>k. norm k < d \<Longrightarrow> \<Psi> (zh + k) + p \<bullet> (zh + k) \<le> \<Psi> zh + p \<bullet> zh"
    and expPsi: "((\<lambda>k. (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2)
        / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = - p"
proof -
  have mxT: "(\<lambda>z. \<Psi> z + p \<bullet> z) (zh + k) \<le> (\<lambda>z. \<Psi> z + p \<bullet> z) zh"
    if "norm k < d" for k
    using mx[OF that] by simp
  have expT: "((\<lambda>k. ((\<lambda>z. \<Psi> z + p \<bullet> z) (zh + k) - (\<lambda>z. \<Psi> z + p \<bullet> z) zh
        - (q + p) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  proof -
    have eq: "((\<lambda>z. \<Psi> z + p \<bullet> z) (zh + k) - (\<lambda>z. \<Psi> z + p \<bullet> z) zh
        - (q + p) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2
      = (\<Psi> (zh + k) - \<Psi> zh - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2" for k
      by (simp add: algebra_simps)
    show ?thesis
      unfolding eq by (rule expPsi)
  qed
  have "q + p = 0"
    by (rule gradient_vanishes_at_interior_max
        [where \<Psi> = "\<lambda>z. \<Psi> z + p \<bullet> z" and zh = zh and q = "q + p"
           and W = W and d = d,
         OF blW dpos mxT expT])
  then show ?thesis
    by (simp add: eq_neg_iff_add_eq_0)
qed

text \<open>If the tilt is antisymmetric, \<open>p = (p\<^sub>0,-p\<^sub>0)\<close>, the two block gradients
  are exact negatives of each other, giving the alignment
  \<open>comparison_supconv_complete\<close> needs with no limit and no rate estimate on
  the tilt.  This route needs Jensen's lemma to deliver such an
  antisymmetric tilt.\<close>

subsection \<open>The Hessians at the doubled maximum are two-sidedly bounded\<close>

text \<open>Route (i) needs the perturbed Hessians bounded as the tilt shrinks.
  \<open>convex_alexandrov\<close> (@{theory Alexandrov_Sup_Convolution.Sup_Convolution}) supplies a Hessian \<open>B\<close> with
  \<open>0 \<le> k \<bullet> Bk\<close>; combined with \<open>k \<bullet> Wk \<le> 0\<close> from
  \<open>second_order_interior_max\<close>, this pins the Hessian \<open>W = B - cI\<close> at a
  maximum of a semiconvex function between \<open>-c\<close> and \<open>0\<close>.
  \<open>semiconvex_alexandrov_bounded\<close> carries this two-sided bound, and
  \<open>norm_matrix_le_of_form_bound\<close> turns it into a matrix-norm bound.\<close>

lemma hessian_lower_bound_of_psd:
  fixes B :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes psd: "\<And>v. 0 \<le> v \<bullet> B v"
  shows "- (c * (norm k)\<^sup>2) \<le> k \<bullet> (B k - c *\<^sub>R k)"
proof -
  have "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"
    by (simp add: inner_diff_right power2_norm_eq_inner)
  moreover have "0 \<le> k \<bullet> B k"
    by (rule psd)
  ultimately show ?thesis
    by linarith
qed

theorem semiconvex_hessian_two_sided:
  fixes B W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes psd: "\<And>v. 0 \<le> v \<bullet> B v"
    and neg: "\<And>v. v \<bullet> W v \<le> 0"
    and Wdef: "\<And>v. W v = B v - c *\<^sub>R v"
  shows "- (c * (norm k)\<^sup>2) \<le> k \<bullet> W k" and "k \<bullet> W k \<le> 0"
proof -
  show "- (c * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    unfolding Wdef by (rule hessian_lower_bound_of_psd[OF psd])
  show "k \<bullet> W k \<le> 0"
    by (rule neg)
qed

text \<open>The quadratic form of \<open>W\<close> is bounded in absolute value by \<open>c\<parallel>k\<parallel>\<^sup>2\<close>,
  uniformly over the family and independent of the tilt.\<close>

corollary semiconvex_hessian_abs_bound:
  fixes B W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes psd: "\<And>v. 0 \<le> v \<bullet> B v"
    and neg: "\<And>v. v \<bullet> W v \<le> 0"
    and Wdef: "\<And>v. W v = B v - c *\<^sub>R v"
    and c0: "0 \<le> c"
  shows "\<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
proof -
  have lo: "- (c * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    by (rule semiconvex_hessian_two_sided(1)[OF psd neg Wdef])
  have hi: "k \<bullet> W k \<le> 0"
    by (rule neg)
  have "0 \<le> c * (norm k)\<^sup>2"
    by (rule mult_nonneg_nonneg[OF c0]) simp
  with lo hi show ?thesis
    by (intro abs_leI) linarith+
qed

subsection \<open>From the quadratic-form bound to a genuine operator bound\<close>

text \<open>The diagonal bound \<open>k \<bullet> Wk\<close> does not by itself bound the operator;
  polarisation recovers the off-diagonal entries by pure algebra, and the
  parallelogram law turns the result into a bound uniform over the unit
  sphere, with no spectral theory.\<close>

lemma polarization_symmetric:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
  shows "4 * (u \<bullet> W v) = (u + v) \<bullet> W (u + v) - (u - v) \<bullet> W (u - v)"
proof -
  have a: "W (u + v) = W u + W v"
    using lin unfolding linear_iff by blast
  have b: "W (u - v) = W u - W v"
    using lin by (simp add: linear_diff)
  have e1: "(u + v) \<bullet> W (u + v) = u \<bullet> W u + u \<bullet> W v + (v \<bullet> W u + v \<bullet> W v)"
    unfolding a by (simp add: inner_add_left inner_add_right)
  have e2: "(u - v) \<bullet> W (u - v) = u \<bullet> W u - u \<bullet> W v - (v \<bullet> W u - v \<bullet> W v)"
    unfolding b by (simp add: inner_diff_left inner_diff_right)
  have s: "v \<bullet> W u = u \<bullet> W v"
    by (rule sym)
  show ?thesis
    unfolding e1 e2 s by simp
qed

lemma parallelogram_norm:
  fixes u v :: "'a::euclidean_space"
  shows "(norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2
       = 2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2"
  by (simp add: power2_norm_eq_inner
      inner_commute algebra_simps)

theorem symmetric_form_bound:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
  shows "\<bar>u \<bullet> W v\<bar> \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
proof -
  have pol: "4 * (u \<bullet> W v) = (u + v) \<bullet> W (u + v) - (u - v) \<bullet> W (u - v)"
    by (rule polarization_symmetric[OF lin sym])
  have b1: "\<bar>(u + v) \<bullet> W (u + v)\<bar> \<le> c * (norm (u + v))\<^sup>2"
    by (rule bnd)
  have b2: "\<bar>(u - v) \<bullet> W (u - v)\<bar> \<le> c * (norm (u - v))\<^sup>2"
    by (rule bnd)
  have b1a: "- (c * (norm (u + v))\<^sup>2) \<le> (u + v) \<bullet> W (u + v)"
    using b1 by (simp add: abs_le_iff)
  have b1b: "(u + v) \<bullet> W (u + v) \<le> c * (norm (u + v))\<^sup>2"
    using b1 by (simp add: abs_le_iff)
  have b2a: "- (c * (norm (u - v))\<^sup>2) \<le> (u - v) \<bullet> W (u - v)"
    using b2 by (simp add: abs_le_iff)
  have b2b: "(u - v) \<bullet> W (u - v) \<le> c * (norm (u - v))\<^sup>2"
    using b2 by (simp add: abs_le_iff)
  have par: "(norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2
      = 2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2"
    by (rule parallelogram_norm)
  have e: "c * (norm (u + v))\<^sup>2 + c * (norm (u - v))\<^sup>2
      = 2 * (c * ((norm u)\<^sup>2 + (norm v)\<^sup>2))"
  proof -
    have "c * (norm (u + v))\<^sup>2 + c * (norm (u - v))\<^sup>2
        = c * ((norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2)"
      by (simp add: algebra_simps)
    also have "\<dots> = c * (2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2)"
      unfolding par ..
    also have "\<dots> = 2 * (c * ((norm u)\<^sup>2 + (norm v)\<^sup>2))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro abs_leI)
    show "u \<bullet> W v \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
      using pol b1b b2a e by linarith
    show "- (u \<bullet> W v) \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
      using pol b1a b2b e by linarith
  qed
qed

text \<open>On the unit sphere the bound is simply \<open>c\<close>: the Hessians at the doubled
  maxima are bounded entrywise by the semiconvexity constant, uniformly in
  the tilt, giving the boundedness a Bolzano-Weierstrass argument needs.\<close>

corollary symmetric_form_bound_unit:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
    and nu: "norm u = 1" and nv: "norm v = 1"
  shows "\<bar>u \<bullet> W v\<bar> \<le> c"
proof -
  have "\<bar>u \<bullet> W v\<bar> \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
    by (rule symmetric_form_bound[OF lin sym bnd])
  then show ?thesis
    unfolding nu nv by simp
qed

subsection \<open>Boundedness to a limit point, and limit point to nearby points\<close>

text \<open>With the operator bound, Bolzano-Weierstrass applies directly: the
  perturbed data live in a ball of a finite-dimensional space, and
  \<open>cball\<close> is (sequentially) compact.  Stated for an arbitrary euclidean
  space, this covers the pair \<open>(gradient, Hessian)\<close> at once, since a
  product of euclidean spaces is euclidean.\<close>

theorem bounded_seq_limit_point:
  fixes Z :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes bnd: "\<And>i. norm (Z i) \<le> B"
  shows "\<exists>Z0 r. strict_mono r \<and> (\<lambda>i. Z (r i)) \<longlonglongrightarrow> Z0"
proof -
  have mem: "Z i \<in> cball (0::'a) B" for i
    using bnd[of i] by simp
  have sc: "seq_compact (cball (0::'a) B)"
    by (rule compact_imp_seq_compact[OF compact_cball])
  obtain Z0 r where sm: "strict_mono r" and lim: "(Z \<circ> r) \<longlonglongrightarrow> Z0"
    using sc mem unfolding seq_compact_def by blast
  show ?thesis
  proof (intro exI conjI)
    show "strict_mono r" by (rule sm)
    show "(\<lambda>i. Z (r i)) \<longlonglongrightarrow> Z0"
      using lim by (simp add: o_def)
  qed
qed

text \<open>If a property holds along a sequence converging to \<open>Z\<^sub>0\<close>, it holds at
  points arbitrarily close to \<open>Z\<^sub>0\<close> - the hypothesis shape of
  \<open>ell_op_lsc_le_of_nearby\<close> and \<open>ell_op_usc_ge_of_nearby\<close>.  Stated for an
  arbitrary predicate, so it serves both the subsolution and supersolution
  side.\<close>

theorem nearby_of_convergent:
  fixes Z :: "nat \<Rightarrow> 'a::metric_space"
  assumes conv: "Z \<longlonglongrightarrow> Z0" and P: "\<And>i. P (Z i)" and e0: "0 < e"
  shows "\<exists>z. dist z Z0 < e \<and> P z"
proof -
  from conv[unfolded lim_sequentially] e0
  obtain N where N: "\<And>i. N \<le> i \<Longrightarrow> dist (Z i) Z0 < e"
    by blast
  have d: "dist (Z N) Z0 < e"
    using N[of N] by simp
  have p: "P (Z N)"
    by (rule P)
  from d p show ?thesis by blast
qed

text \<open>A bounded family on which the operator bound holds yields the
  nearby-point hypothesis at a produced limit point.  The closing argument
  still needs, at that limit, the ordering \<open>X \<preceq> Y\<close>, symmetry of both
  matrices, and \<open>p \<noteq> 0\<close>.  Symmetry and the ordering are closed conditions
  and pass to the limit automatically; \<open>p \<noteq> 0\<close> is not closed and needs a
  positive lower bound along the family.\<close>

subsection \<open>A positive lower bound on the shared gradient\<close>

text \<open>\<open>p \<noteq> 0\<close> needs a positive lower bound on \<open>\<parallel>p\<parallel>\<close> along the family, not
  merely nonvanishing at each member.  If \<open>x̂\<close> misses the maximum of
  \<open>u - w\<close> by at least \<open>\<gamma>\<close>, comparing \<open>\<Phi>\<close> at \<open>(x̂,ŷ)\<close> against the diagonal
  point gives \<open>\<gamma> + (\<alpha>/2)\<parallel>x̂-ŷ\<parallel>\<^sup>2 \<le> w x̂ - w ŷ\<close>, so the value gap forces a
  position gap via a modulus of continuity for \<open>w\<close>; for Lipschitz \<open>w\<close> the
  bound is \<open>\<gamma>/L\<^sub>w\<close>, independent of \<open>\<alpha>\<close>.\<close>

theorem doubling_grad_lower_bound:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and zK: "z \<in> K" and xK: "xh \<in> K" and yK: "yh \<in> K"
    and a: "0 \<le> \<alpha>"
    and gap: "u xh - w xh + \<gamma> \<le> u z - w z"
    and lip: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> \<bar>w p - w q\<bar> \<le> Lw * norm (p - q)"
    and Lw: "0 < Lw"
  shows "\<gamma> / Lw \<le> norm (xh - yh)"
proof -
  have diag: "u z - w z
      \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule doubling_ge_diagonal[where u = u and w = w and K = K, OF mx zK])
  have sq: "0 \<le> (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    using a by simp
  have gw: "\<gamma> \<le> w xh - w yh"
    using diag gap sq by linarith
  have "\<bar>w xh - w yh\<bar> \<le> Lw * norm (xh - yh)"
    by (rule lip[OF xK yK])
  then have "\<gamma> \<le> Lw * norm (xh - yh)"
    using gw by linarith
  then show ?thesis
    using Lw by (simp add: field_simps)
qed

text \<open>The shared gradient \<open>p = \<alpha>(x̂-ŷ)\<close> has norm at least \<open>\<alpha>\<gamma>/L\<^sub>w\<close>, a bound
  holding fixed along the family, which is what lets \<open>p \<noteq> 0\<close> survive the
  limit.\<close>

corollary doubling_grad_norm_lower_bound:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - (\<alpha>/2) * (norm (x - y))\<^sup>2
          \<le> u xh - w yh - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and zK: "z \<in> K" and xK: "xh \<in> K" and yK: "yh \<in> K"
    and a: "0 < \<alpha>"
    and gap: "u xh - w xh + \<gamma> \<le> u z - w z"
    and lip: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> \<bar>w p - w q\<bar> \<le> Lw * norm (p - q)"
    and Lw: "0 < Lw"
  shows "\<alpha> * (\<gamma> / Lw) \<le> norm (\<alpha> *\<^sub>R (xh - yh))"
proof -
  have base: "\<gamma> / Lw \<le> norm (xh - yh)"
    by (rule doubling_grad_lower_bound[where u = u and w = w and K = K
          and z = z, OF mx zK xK yK less_imp_le[OF a] gap lip Lw])
  have step: "\<alpha> * (\<gamma> / Lw) \<le> \<alpha> * norm (xh - yh)"
    by (rule mult_left_mono[OF base less_imp_le[OF a]])
  have nrm: "norm (\<alpha> *\<^sub>R (xh - yh)) = \<alpha> * norm (xh - yh)"
  proof -
    have ab: "\<bar>\<alpha>\<bar> = \<alpha>"
      by (rule abs_of_pos[OF a])
    have "norm (\<alpha> *\<^sub>R (xh - yh)) = \<bar>\<alpha>\<bar> * norm (xh - yh)"
      by (rule norm_scaleR)
    then show ?thesis unfolding ab .
  qed
  show ?thesis unfolding nrm by (rule step)
qed

text \<open>The same bound for the doubling run on sup-convolutions:
  \<open>supconv_lipschitz\<close> gives the modulus of continuity with the same
  constant, and \<open>doubled_value_gap_supconv\<close> gives the value gap with
  explicit loss \<open>\<epsilon>(L\<^sub>u\<^sup>2+L\<^sub>w\<^sup>2)/2\<close>.  The doubled functional is
  \<open>A(x)+B(y)-\<close>penalty with \<open>B = supconv(-w)\<epsilon>\<close>, so \<open>w\<close> is instantiated at
  \<open>-B\<close>, and the Lipschitz hypothesis transfers since negation preserves
  \<open>\<bar>\<cdot>\<bar>\<close>.\<close>

corollary doubling_grad_lower_bound_supconv:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
          - (\<alpha>/2) * (norm (x - y))\<^sup>2
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    and zK: "z \<in> K" and xK: "xh \<in> K" and yK: "yh \<in> K"
    and a: "0 < \<alpha>" and e: "0 < \<epsilon>"
    and Bw: "\<And>y. (- w) y \<le> Bw"
    and lipw: "\<And>p q. \<bar>(- w) p - (- w) q\<bar> \<le> Lw * norm (p - q)"
    and Lwpos: "0 < Lw"
    and gap: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> xh + \<gamma>
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> z + supconv (- w) \<epsilon> z"
  shows "\<alpha> * (\<gamma> / Lw) \<le> norm (\<alpha> *\<^sub>R (xh - yh))"
proof -
  have lipB: "\<bar>(- supconv (- w) \<epsilon> p) - (- supconv (- w) \<epsilon> q)\<bar>
      \<le> Lw * norm (p - q)" for p q
  proof -
    have "\<bar>supconv (- w) \<epsilon> p - supconv (- w) \<epsilon> q\<bar> \<le> Lw * norm (p - q)"
      by (rule supconv_lipschitz[OF Bw e lipw])
    then show ?thesis by simp
  qed
  show ?thesis
    by (rule doubling_grad_norm_lower_bound
        [where u = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>"
           and w = "\<lambda>y. - supconv (- w) \<epsilon> y"
           and K = K and \<alpha> = \<alpha> and xh = xh and yh = yh and z = z
           and \<gamma> = \<gamma> and Lw = Lw])
       (use mx zK xK yK a gap lipB Lwpos in simp_all)
qed

text \<open>Continuity of the two sup-convolutions is free: \<open>supconv_continuous\<close>
  needs only an upper bound and \<open>\<epsilon> > 0\<close>, giving continuity on all of
  \<open>UNIV\<close> with no regularity of \<open>u\<close> or \<open>w\<close> beyond boundedness.\<close>

corollary doubling_maximiser_supconv:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
        - (\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
proof -
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu e] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw e] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  have "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y)
        - (\<alpha>/2) * (norm (x - y))\<^sup>2
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh - (- supconv (- w) \<epsilon> yh)
        - (\<alpha>/2) * (norm (xh - yh))\<^sup>2"
    by (rule doubling_maximiser_exists[OF cK neK cA cB])
  then show ?thesis by simp
qed

text \<open>Theorem 4.2(a)'s proof runs the comparison on \<open>\<theta>u\<close> with \<open>\<theta> < 1\<close>, making
  the operator inequality strict for \<open>ell_op_env_strict_contradiction\<close>.
  The interior/boundary gap for \<open>u-w\<close> survives this scaling explicitly:
  \<open>\<theta>u-w\<close> differs from \<open>u-w\<close> by at most \<open>(1-\<theta>)B\<close>, so a gap \<open>M-m\<close> survives
  whenever \<open>2(1-\<theta>)B < M-m\<close>.\<close>

lemma theta_gap_preserved:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes bd: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
    and t: "\<theta> \<le> 1"
    and gap: "(1 - \<theta>) * (2*B) < M - m"
    and xK: "xs \<in> K" and xval: "M \<le> u xs - w xs"
    and SK: "S \<subseteq> K"
    and bdry: "\<And>y. y \<in> S \<Longrightarrow> u y - w y \<le> m"
    and y: "y \<in> S"
  shows "\<theta> * u y - w y < \<theta> * u xs - w xs"
proof -
  have yK: "y \<in> K" using y SK by blast
  have t0: "0 \<le> 1 - \<theta>" using t by simp
  have uy: "\<bar>u y\<bar> \<le> B" by (rule bd[OF yK])
  have ux: "\<bar>u xs\<bar> \<le> B" by (rule bd[OF xK])
  have ly: "(1 - \<theta>) * (- B) \<le> (1 - \<theta>) * u y"
    by (rule mult_left_mono[OF _ t0]) (use uy in linarith)
  have lx: "(1 - \<theta>) * u xs \<le> (1 - \<theta>) * B"
    by (rule mult_left_mono[OF _ t0]) (use ux in linarith)  have ey: "\<theta> * u y - w y = (u y - w y) - (1 - \<theta>) * u y"
    by (simp add: algebra_simps)
  have ex: "\<theta> * u xs - w xs = (u xs - w xs) - (1 - \<theta>) * u xs"
    by (simp add: algebra_simps)
  have my: "u y - w y \<le> m" by (rule bdry[OF y])
  have dexp: "(1 - \<theta>) * (2*B) = (1 - \<theta>) * B + (1 - \<theta>) * B"
    by (simp add: algebra_simps)
  have neg: "(1 - \<theta>) * (- B) = - ((1 - \<theta>) * B)"
    by (simp add: algebra_simps)
  from ly lx my xval gap show ?thesis
    unfolding ey ex using dexp neg by linarith
qed

subsection \<open>Symmetry and the ordering pass to the limit\<close>subsection \<open>Symmetry and the ordering pass to the limit\<close>

text \<open>Symmetry and positive semidefiniteness are closed conditions and so
  survive the passage to a limit point, proved entrywise via
  \<open>tendsto_vec_nth\<close>: convergence in \<open>real^'n^'n\<close> is convergence of every
  entry.\<close>

lemma tendsto_entry:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0"
  shows "(\<lambda>i. A i $ j $ k) \<longlonglongrightarrow> A0 $ j $ k"
  by (rule tendsto_vec_nth[OF tendsto_vec_nth[OF conv]])

lemma transpose_limit:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0" and sym: "\<And>i. transpose (A i) = A i"
  shows "transpose A0 = A0"
proof -
  have eq: "A0 $ j $ k = A0 $ k $ j" for j k
  proof -
    have f: "(\<lambda>i. A i $ j $ k) = (\<lambda>i. A i $ k $ j)"
    proof (rule ext)
      fix i
      have "A i $ j $ k = (transpose (A i)) $ k $ j"
        by (simp add: transpose_def)
      also have "\<dots> = A i $ k $ j"
        using sym by simp
      finally show "A i $ j $ k = A i $ k $ j" .
    qed
    have "(\<lambda>i. A i $ j $ k) \<longlonglongrightarrow> A0 $ k $ j"
      unfolding f by (rule tendsto_entry[OF conv])
    from tendsto_entry[OF conv] this show ?thesis
      by (rule LIMSEQ_unique)
  qed
  show ?thesis
    by (simp add: vec_eq_iff transpose_def eq)
qed

lemma tendsto_quadratic_form:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0"
  shows "(\<lambda>i. x \<bullet> (A i *v x)) \<longlonglongrightarrow> x \<bullet> (A0 *v x)"
proof -
  have e: "y \<bullet> (B *v y) = (\<Sum>j\<in>UNIV. y $ j * (\<Sum>k\<in>UNIV. B $ j $ k * y $ k))"
    for B :: "real^'n^'n" and y :: "real^'n"
    by (simp add: inner_vec_def matrix_vector_mult_def)
  show ?thesis
    unfolding e
    by (intro tendsto_sum tendsto_mult tendsto_const tendsto_entry[OF conv])
qed

theorem psd_limit:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0" and p: "\<And>i. psd (A i)"
  shows "psd A0"
proof -
  have sym: "transpose (A i) = A i" for i
    using p[of i] unfolding psd_def by simp
  have nn: "0 \<le> x \<bullet> (A i *v x)" for i and x :: "real^'n"
    using p[of i] unfolding psd_def by simp
  have s0: "transpose A0 = A0"
    by (rule transpose_limit[OF conv sym])
  have q0: "0 \<le> x \<bullet> (A0 *v x)" for x :: "real^'n"
  proof -
    have "(\<lambda>i. x \<bullet> (A i *v x)) \<longlonglongrightarrow> x \<bullet> (A0 *v x)"
      by (rule tendsto_quadratic_form[OF conv])
    then show ?thesis
      by (rule LIMSEQ_le_const) (use nn in blast)
  qed
  show ?thesis
    unfolding psd_def using s0 q0 by blast
qed

text \<open>\<open>psd (Y-X)\<close> is preserved when both sequences converge, since subtraction
  is continuous and \<open>psd\<close> is a closed condition.\<close>

corollary psd_diff_limit:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and p: "\<And>i. psd (Y i - X i)"
  shows "psd (Y0 - X0)"
proof -
  have "(\<lambda>i. Y i - X i) \<longlonglongrightarrow> Y0 - X0"
    by (rule tendsto_diff[OF cY cX])
  from psd_limit[OF this p] show ?thesis .
qed

subsection \<open>The asymptotic ordering\<close>

text \<open>Perturbing the doubled functional by \<open>-\<delta>\<parallel>z-\<xi>\<^sub>0\<parallel>\<^sup>2\<close> shifts \<open>X\<close> to
  \<open>X+2\<delta>I\<close> and \<open>Y\<close> to \<open>Y-2\<delta>I\<close>, so \<open>(Y-X)-4\<delta>I\<close> need not be psd even when
  \<open>Y-X\<close> is: the per-index ordering is lost.  What survives is the
  ordering in the limit, since \<open>psd\<close> is closed and the defect \<open>4\<delta>\<close>
  vanishes; the right hypothesis for a shifted family is
  \<open>psd(Y\<^sub>i-X\<^sub>i+c\<^sub>iI)\<close> with \<open>c\<^sub>i \<rightarrow> 0\<close>.\<close>

corollary psd_diff_limit_shifted:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and cs :: "nat \<Rightarrow> real"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cs0: "cs \<longlonglongrightarrow> 0"
    and p: "\<And>i. psd (Y i - X i + (cs i) *\<^sub>R mat 1)"
  shows "psd (Y0 - X0)"
proof -
  have s0: "(\<lambda>i. (cs i) *\<^sub>R (mat 1 :: real^'n^'n))
      \<longlonglongrightarrow> (0::real) *\<^sub>R (mat 1 :: real^'n^'n)"
    by (rule tendsto_scaleR[OF cs0 tendsto_const])
  have "(\<lambda>i. Y i - X i + (cs i) *\<^sub>R mat 1)
      \<longlonglongrightarrow> (Y0 - X0) + (0::real) *\<^sub>R (mat 1 :: real^'n^'n)"
    by (rule tendsto_add[OF tendsto_diff[OF cY cX] s0])
  then have "(\<lambda>i. Y i - X i + (cs i) *\<^sub>R mat 1) \<longlonglongrightarrow> Y0 - X0"
    by simp
  from psd_limit[OF this p] show ?thesis .
qed

subsection \<open>Route (i), threaded\<close>

text \<open>Everything is supplied as sequences of perturbed data, produced by
  re-running Jensen with a shrinking tilt, together with their limits.
  Symmetry and the ordering are needed only along the sequence
  (\<open>transpose_limit\<close>, \<open>psd_diff_limit\<close>); only \<open>p \<noteq> 0\<close> is required at the
  limit itself, supplied by \<open>doubling_grad_norm_lower_bound\<close>.  The two
  gradient sequences must converge to the same \<open>p\<close> - the gradient
  alignment.\<close>

theorem env_strict_contradiction_of_limits:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and psdi: "\<And>i. psd (Y i - X i)"
    and pnz: "p \<noteq> 0"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and c1: "c < 1"
    and bndu: "\<And>i. ell_op k L (Pu i) (X i) \<le> c"
    and bndw: "\<And>i. 1 \<le> ell_op k L (Pw i) (Y i)"
  shows False
proof -
  have sX0: "transpose X0 = X0"
    by (rule transpose_limit[OF cX symX])
  have sY0: "transpose Y0 = Y0"
    by (rule transpose_limit[OF cY symY])
  have p0: "psd (Y0 - X0)"
    by (rule psd_diff_limit[OF cX cY psdi])
  have subs: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X0) < e
      \<and> ell_op k L p' M' \<le> c" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pu i, X i)) \<longlonglongrightarrow> ((p, X0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPu cX])
    have P: "ell_op k L (fst ((Pu i, X i) :: (real^'n) \<times> (real^'n^'n)))
        (snd ((Pu i, X i) :: (real^'n) \<times> (real^'n^'n))) \<le> c" for i
      using bndu[of i] by simp
    obtain z where dz: "dist z ((p, X0) :: (real^'n) \<times> (real^'n^'n)) < e"
      and pz: "ell_op k L (fst z) (snd z) \<le> c"
      using nearby_of_convergent
        [where P = "\<lambda>z. ell_op k L (fst z) (snd z) \<le> c", OF cZ P e0]
      by blast
    have zc: "(fst z, snd z) = z" by simp
    from dz pz show ?thesis
      by (intro exI[of _ "fst z"] exI[of _ "snd z"]) (simp add: zc)
  qed
  have sups: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y0) < e
      \<and> 1 \<le> ell_op k L p' M'" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pw i, Y i)) \<longlonglongrightarrow> ((p, Y0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPw cY])
    have P: "1 \<le> ell_op k L (fst ((Pw i, Y i) :: (real^'n) \<times> (real^'n^'n)))
        (snd ((Pw i, Y i) :: (real^'n) \<times> (real^'n^'n)))" for i
      using bndw[of i] by simp
    obtain z where dz: "dist z ((p, Y0) :: (real^'n) \<times> (real^'n^'n)) < e"
      and pz: "1 \<le> ell_op k L (fst z) (snd z)"
      using nearby_of_convergent
        [where P = "\<lambda>z. 1 \<le> ell_op k L (fst z) (snd z)", OF cZ P e0]
      by blast
    have zc: "(fst z, snd z) = z" by simp
    from dz pz show ?thesis
      by (intro exI[of _ "fst z"] exI[of _ "snd z"]) (simp add: zc)
  qed
  show False
    by (rule env_strict_contradiction_of_nearby[OF p0 sX0 sY0 pnz kk(1) kk(2)
          LL c1 subs sups])
qed

subsection \<open>The gradient alignment along the family\<close>

text \<open>The last hypothesis of \<open>env_strict_contradiction_of_limits\<close> - that the
  two gradient sequences share a limit - follows from the tilts shrinking
  to zero: with tilt \<open>p\<^sub>i\<close> the untilted jet has gradient \<open>-p\<^sub>i\<close>, so the two
  block gradients differ by \<open>fst p\<^sub>i + snd p\<^sub>i\<close> alone, independent of the
  maximiser.\<close>

lemma tendsto_of_norm_bound:
  fixes Z :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes b: "\<And>i. norm (Z i) \<le> D i" and D: "D \<longlonglongrightarrow> 0"
  shows "Z \<longlonglongrightarrow> 0"
proof (rule Lim_null_comparison[OF _ D])
  show "\<forall>\<^sub>F i in sequentially. norm (Z i) \<le> D i"
    using b by simp
qed

theorem gradient_sequences_align:
  fixes Pt :: "nat \<Rightarrow> (real^'n::finite) \<times> (real^'n)" and G :: "nat \<Rightarrow> real^'n"
  assumes tilt: "Pt \<longlonglongrightarrow> 0" and gconv: "G \<longlonglongrightarrow> g"
  shows "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    and "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
proof -
  have f0: "(\<lambda>i. fst (Pt i)) \<longlonglongrightarrow> 0"
    using tendsto_fst[OF tilt] by (simp add: zero_prod_def)
  have s0: "(\<lambda>i. snd (Pt i)) \<longlonglongrightarrow> 0"
    using tendsto_snd[OF tilt] by (simp add: zero_prod_def)
  show "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    using tendsto_add[OF tendsto_minus[OF f0] gconv] by simp
  show "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
    using tendsto_add[OF s0 gconv] by simp
qed

text \<open>The doubling supplies tilts bounded by a sequence \<open>dd\<^sub>i \<rightarrow> 0\<close>, exactly
  what re-running Jensen with a shrinking tilt parameter gives.\<close>

corollary gradient_sequences_align_of_bound:
  fixes Pt :: "nat \<Rightarrow> (real^'n::finite) \<times> (real^'n)" and G :: "nat \<Rightarrow> real^'n"
  assumes b: "\<And>i. norm (Pt i) \<le> dd i" and dd: "dd \<longlonglongrightarrow> 0"
    and gconv: "G \<longlonglongrightarrow> g"
  shows "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    and "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
proof -
  have t0: "Pt \<longlonglongrightarrow> 0"
    by (rule tendsto_of_norm_bound[OF b dd])
  show "(\<lambda>i. - fst (Pt i) + G i) \<longlonglongrightarrow> g"
    by (rule gradient_sequences_align(1)[OF t0 gconv])
  show "(\<lambda>i. snd (Pt i) + G i) \<longlonglongrightarrow> g"
    by (rule gradient_sequences_align(2)[OF t0 gconv])
qed

subsection \<open>The diagonal step: two limits at once\<close>

text \<open>\<open>env_strict_contradiction_of_limits\<close> wants the operator bound at
  \<open>X\<^sub>i\<close>, but \<open>subsol_shifted_bound_supconv\<close> only delivers it at the
  corrected matrix \<open>X\<^sub>i+\<delta>I\<close>, so the two limits \<open>i \<rightarrow> \<infinity>\<close> and \<open>\<delta> \<rightarrow> 0\<close>
  must be taken together via the nearby-point formulation.  The predicate
  is taken curried, as \<open>Q p' M'\<close> rather than \<open>P (p', M')\<close>, so that \<open>OF\<close>
  unifies against the unreduced projections.\<close>

theorem nearby_of_convergent_shifted:
  fixes Pz :: "nat \<Rightarrow> real^'n::finite" and Mz :: "nat \<Rightarrow> real^'n^'n"
  assumes conv: "(\<lambda>i. (Pz i, Mz i)) \<longlonglongrightarrow> Z0"
    and Q: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> Q (Pz i) (Mz i + \<delta> *\<^sub>R mat 1)"
    and D: "0 < D" and e0: "0 < e"
  shows "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) Z0 < e
      \<and> Q p' M'"
proof -
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e/2"
  proof -
    have dle: "d \<le> e/(2*(N+1))" unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e/2"
    proof -
      have expand: "(e/2) * (2*(N+1)) = e * N + e"
        by (simp add: algebra_simps)
      have "e * N < (e/2) * (2*(N+1))"
        unfolding expand using e0 by linarith
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have e2: "0 < e/2" using e0 by simp
  from conv[unfolded lim_sequentially] e2
  obtain M where M: "\<And>i. M \<le> i \<Longrightarrow> dist ((Pz i, Mz i)) Z0 < e/2"
    by blast
  have dz: "dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0 < e/2"
    using M[of M] by simp
  have shift: "dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      (Pz M, Mz M) = d * N"
  proof -
    have "dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        = sqrt ((dist (Pz M) (Pz M))\<^sup>2
            + (dist (Mz M + d *\<^sub>R mat 1) (Mz M))\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (Mz M + d *\<^sub>R mat 1) (Mz M)"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have tri: "dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) Z0
      \<le> dist ((Pz M, Mz M + d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        + dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0"
    by (rule dist_triangle)
  have near: "dist ((Pz M, Mz M + d *\<^sub>R mat 1)
      :: (real^'n) \<times> (real^'n^'n)) Z0 < e"
    using tri shift small dz by linarith
  have q: "Q (Pz M) (Mz M + d *\<^sub>R mat 1)"
    by (rule Q[OF d0 dD])
  from near q show ?thesis by blast
qed

text \<open>The mirrored version for the supersolution side: the correction runs the
  other way, \<open>Y\<^sub>i-\<delta>I\<close>, but the estimate is identical since the shift has
  the same norm.\<close>

theorem nearby_of_convergent_shifted_neg:
  fixes Pz :: "nat \<Rightarrow> real^'n::finite" and Mz :: "nat \<Rightarrow> real^'n^'n"
  assumes conv: "(\<lambda>i. (Pz i, Mz i)) \<longlonglongrightarrow> Z0"
    and Q: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow> Q (Pz i) (Mz i - \<delta> *\<^sub>R mat 1)"
    and D: "0 < D" and e0: "0 < e"
  shows "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) Z0 < e
      \<and> Q p' M'"
proof -
  define N where "N = norm (mat 1 :: real^'n^'n)"
  have N0: "0 \<le> N" unfolding N_def by simp
  define d where "d = min (D/2) (e/(2*(N+1)))"
  have d0: "0 < d" unfolding d_def using D e0 N0 by simp
  have dD: "d < D" unfolding d_def using D by simp
  have small: "d * N < e/2"
  proof -
    have dle: "d \<le> e/(2*(N+1))" unfolding d_def by simp
    have "d * N \<le> (e/(2*(N+1))) * N"
      by (rule mult_right_mono[OF dle N0])
    also have "(e/(2*(N+1))) * N = e * N / (2*(N+1))"
      by simp
    also have "\<dots> < e/2"
    proof -
      have expand: "(e/2) * (2*(N+1)) = e * N + e"
        by (simp add: algebra_simps)
      have "e * N < (e/2) * (2*(N+1))"
        unfolding expand using e0 by linarith
      moreover have "0 < 2*(N+1)"
        using N0 by simp
      ultimately show ?thesis
        by (simp add: divide_less_eq)
    qed
    finally show ?thesis .
  qed
  have e2: "0 < e/2" using e0 by simp
  from conv[unfolded lim_sequentially] e2
  obtain M where M: "\<And>i. M \<le> i \<Longrightarrow> dist ((Pz i, Mz i)) Z0 < e/2"
    by blast
  have dz: "dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0 < e/2"
    using M[of M] by simp
  have shift: "dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
      (Pz M, Mz M) = d * N"
  proof -
    have "dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        = sqrt ((dist (Pz M) (Pz M))\<^sup>2
            + (dist (Mz M - d *\<^sub>R mat 1) (Mz M))\<^sup>2)"
      by (rule dist_Pair_Pair)
    also have "\<dots> = dist (Mz M - d *\<^sub>R mat 1) (Mz M)"
      by simp
    also have "\<dots> = norm (d *\<^sub>R (mat 1 :: real^'n^'n))"
      by (simp add: dist_norm)
    also have "\<dots> = d * N"
      unfolding N_def using d0 by simp
    finally show ?thesis .
  qed
  have tri: "dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n)) Z0
      \<le> dist ((Pz M, Mz M - d *\<^sub>R mat 1) :: (real^'n) \<times> (real^'n^'n))
          (Pz M, Mz M)
        + dist ((Pz M, Mz M) :: (real^'n) \<times> (real^'n^'n)) Z0"
    by (rule dist_triangle)
  have near: "dist ((Pz M, Mz M - d *\<^sub>R mat 1)
      :: (real^'n) \<times> (real^'n^'n)) Z0 < e"
    using tri shift small dz by linarith
  have q: "Q (Pz M) (Mz M - d *\<^sub>R mat 1)"
    by (rule Q[OF d0 dD])
  from near q show ?thesis by blast
qed

text \<open>The contradiction with both limits taken together: bounds at the
  \<open>\<delta>\<close>-corrected matrices along a sequence of tilts is exactly what the
  doubling reaches.\<close>

theorem env_strict_contradiction_of_shifted_limits:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and p0: "psd (Y0 - X0)"
    and pnz: "p \<noteq> 0"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and c1: "c < 1" and D: "0 < D"
    and bndu: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow>
        ell_op k L (Pu i) (X i + \<delta> *\<^sub>R mat 1) \<le> c"
    and bndw: "\<And>i \<delta>. 0 < \<delta> \<Longrightarrow> \<delta> < D \<Longrightarrow>
        1 \<le> ell_op k L (Pw i) (Y i - \<delta> *\<^sub>R mat 1)"
  shows False
proof -
  have sX0: "transpose X0 = X0"
    by (rule transpose_limit[OF cX symX])
  have sY0: "transpose Y0 = Y0"
    by (rule transpose_limit[OF cY symY])
  note p0
  have subs: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, X0) < e
      \<and> ell_op k L p' M' \<le> c" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pu i, X i)) \<longlonglongrightarrow> ((p, X0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPu cX])
    show ?thesis
      by (rule nearby_of_convergent_shifted
          [where Q = "\<lambda>p' M'. ell_op k L p' M' \<le> c", OF cZ bndu D e0])
  qed
  have sups: "\<exists>p' M'. dist ((p', M') :: (real^'n) \<times> (real^'n^'n)) (p, Y0) < e
      \<and> 1 \<le> ell_op k L p' M'" if e0: "0 < e" for e
  proof -
    have cZ: "(\<lambda>i. (Pw i, Y i)) \<longlonglongrightarrow> ((p, Y0) :: (real^'n) \<times> (real^'n^'n))"
      by (rule tendsto_Pair[OF cPw cY])
    show ?thesis
      by (rule nearby_of_convergent_shifted_neg
          [where Q = "\<lambda>p' M'. 1 \<le> ell_op k L p' M'", OF cZ bndw D e0])
  qed
  show False
    by (rule env_strict_contradiction_of_nearby[OF p0 sX0 sY0 pnz kk(1) kk(2)
          LL c1 subs sups])
qed

subsection \<open>Theorem 4.2(a) from a sequence of sup-convolution jets\<close>

text \<open>Each index \<open>i\<close> of the Jensen application supplies a maximiser, its jet,
  and the sup-convolution attainment point.  The per-index operator bounds
  come from \<open>subsol_shifted_bound_supconv\<close> and
  \<open>supersol_shifted_bound_supconv\<close>, and
  \<open>env_strict_contradiction_of_shifted_limits\<close> takes both limits, with no
  rate and no relation assumed between \<open>i\<close> and \<open>\<delta>\<close>.\<close>

theorem comparison_supconv_sequence_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "nat \<Rightarrow> real^'n^'n" and Pu Pw :: "nat \<Rightarrow> real^'n"
    and xu xw ysu ysw :: "nat \<Rightarrow> real^'n"
  assumes sub: "visc_subsol k L \<Omega>\<^sub>u u" and sup: "supersol_jet k L \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and ysuO: "\<And>i. ysu i \<in> \<Omega>\<^sub>u" and yswO: "\<And>i. ysw i \<in> \<Omega>\<^sub>w"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and p0: "psd (Y0 - X0)"
    and optu: "\<And>i. supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i)
        = \<theta> * u (ysu i) - (dist (xu i) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    and optw: "\<And>i. supconv (- w) \<epsilon> (xw i)
        = (- w) (ysw i) - (dist (xw i) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    and jetu: "\<And>i. ((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i) - Pu i \<bullet> h
        - (h \<bullet> (X i *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "\<And>i. ((\<lambda>h. (supconv (- w) \<epsilon> (xw i + h) - supconv (- w) \<epsilon> (xw i)
        - (- Pw i) \<bullet> h - (h \<bullet> ((- Y i) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cPu: "Pu \<longlonglongrightarrow> p" and cPw: "Pw \<longlonglongrightarrow> p"
    and pnz: "p \<noteq> 0"
  shows False
proof -
  have bndu: "ell_op k L (Pu i) (X i + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule subsol_shifted_bound_supconv
        [OF sub t(1) ysuO symX kk(1) kk(2) LL Bu e optu jetu that(1)])
  \<comment> \<open>The supersolution bound is over \<open>F\<^sup>*\<close>, and \<open>F\<^sup>* = F\<close> only away from
      \<open>0\<close>; the gradient FAMILY need not avoid \<open>0\<close>, but its LIMIT does, so it
      avoids \<open>0\<close> eventually.  Shifting every family past that index costs
      nothing --- all hypotheses are either indexwise or convergences.\<close>
  have np: "0 < norm p" using pnz by simp
  obtain N where N: "\<And>i. N \<le> i \<Longrightarrow> norm p / 2 < norm (Pw i)"
  proof -
    have cn: "(\<lambda>i. norm (Pw i)) \<longlonglongrightarrow> norm p"
      by (rule tendsto_norm[OF cPw])
    have "norm p / 2 < norm p" using np by simp
    then have "\<forall>\<^sub>F i in sequentially. norm p / 2 < norm (Pw i)"
      using cn by (rule order_tendstoD(1)[rotated])
    then obtain N0 where N0: "\<forall>n\<ge>N0. norm p / 2 < norm (Pw n)"
      unfolding eventually_sequentially by blast
    show thesis by (rule that[of N0]) (use N0 in blast)
  qed
  have pwnz: "Pw (i + N) \<noteq> 0" for i
  proof -
    have "norm p / 2 < norm (Pw (i + N))" by (rule N) simp
    then show ?thesis using np by auto
  qed
  have bndw: "1 \<le> ell_op k L (Pw (i + N)) (Y (i + N) - \<delta> *\<^sub>R mat 1)"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule supersol_shifted_bound_supconv_ne
        [OF sup yswO kk(1) kk(2) LL symY Bw e optw jetw that(1) pwnz])
  have bndu': "ell_op k L (Pu (i + N)) (X (i + N) + \<delta> *\<^sub>R mat 1) \<le> \<theta>"
    if "0 < \<delta>" "\<delta> < 1" for i \<delta>
    by (rule bndu[OF that(1) that(2)])
  show False
    by (rule env_strict_contradiction_of_shifted_limits
        [OF LIMSEQ_ignore_initial_segment[OF cX]
           LIMSEQ_ignore_initial_segment[OF cY]
           LIMSEQ_ignore_initial_segment[OF cPu]
           LIMSEQ_ignore_initial_segment[OF cPw]
           symX symY p0
           pnz kk(1) kk(2) LL t(2)
           zero_less_one bndu' bndw])
qed

subsection \<open>The shrinking tilt is always available\<close>

text \<open>\<open>comparison_supconv_sequence_complete\<close> consumes a sequence of Jensen
  applications with tilts shrinking to zero.  Jensen's smallness condition
  \<open>2 dd r < \<Phi>(\<xi>)-m\<close> holds for every sufficiently small tilt once the
  centre beats the boundary value at all, so an admissible sequence
  converging to zero always exists.\<close>

lemma jensen_tilt_threshold_pos:
  fixes r m Psixi :: real
  assumes gap: "m < Psixi" and r: "0 < r"
  shows "0 < (Psixi - m) / (2*r)"
  using gap r by simp

lemma jensen_tilt_small_enough:
  fixes r m Psixi dd :: real
  assumes r: "0 < r"
    and dlt: "dd < (Psixi - m) / (2*r)"
  shows "2 * dd * r < Psixi - m"
proof -
  have r2: "0 < 2*r" using r by simp
  have "dd * (2*r) < ((Psixi - m) / (2*r)) * (2*r)"
    by (rule mult_strict_right_mono[OF dlt r2])
  also have "((Psixi - m) / (2*r)) * (2*r) = Psixi - m"
    using r2 by simp
  finally have "dd * (2*r) < Psixi - m" .
  then show ?thesis
    by (simp add: algebra_simps)
qed

text \<open>An explicit admissible sequence, not canonical, giving the family
  construction a concrete witness rather than a bare existence claim.\<close>

lemma tilt_sequence_pos:
  fixes D :: real
  assumes D: "0 < D"
  shows "0 < D / (2 + real i)"
  using D by simp

lemma tilt_sequence_lt:
  fixes D :: real
  assumes D: "0 < D"
  shows "D / (2 + real i) < D"
proof -
  have den: "(1::real) < 2 + real i" by simp
  have "D / (2 + real i) < D / 1"
    by (rule divide_strict_left_mono[OF den D]) simp
  then show ?thesis by simp
qed

lemma tilt_sequence_tendsto:
  fixes D :: real
  shows "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
proof -
  have F: "filterlim (\<lambda>i. 2 + real i) at_top sequentially"
    by (rule filterlim_tendsto_add_at_top[OF tendsto_const
          filterlim_real_sequentially])
  show ?thesis
    by (rule tendsto_divide_0[OF tendsto_const
          filterlim_at_top_imp_at_infinity[OF F]])
qed

theorem tilt_sequence_admissible:
  fixes D :: real
  assumes D: "0 < D"
  shows "\<And>i. 0 < D / (2 + real i)"
    and "\<And>i. D / (2 + real i) < D"
    and "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
proof -
  show "0 < D / (2 + real i)" for i
    by (rule tilt_sequence_pos[OF D])
  show "D / (2 + real i) < D" for i
    by (rule tilt_sequence_lt[OF D])
  show "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
    by (rule tilt_sequence_tendsto)
qed

subsection \<open>Replacing the Lipschitz modulus by compactness\<close>

text \<open>\<open>doubling_grad_lower_bound\<close> converts a value gap in \<open>w\<close> into a position
  gap via a Lipschitz modulus, more than continuity on compact \<open>K\<close>
  supplies.  Continuity plus compactness suffices instead: pairs in
  \<open>K \<times> K\<close> realising a fixed gap \<open>\<gamma> > 0\<close> stay bounded away from the
  diagonal, since a sequence with \<open>\<parallel>p\<^sub>n-q\<^sub>n\<parallel> \<rightarrow> 0\<close> would force \<open>\<gamma> \<le> 0\<close>
  by continuity at the common limit.  The resulting separation depends on
  \<open>\<gamma>\<close>, \<open>K\<close> and \<open>v\<close> but not \<open>\<alpha>\<close>.\<close>

lemma positive_separation_of_value_gap:
  fixes v :: "'a::real_normed_vector \<Rightarrow> real"
  assumes cK: "compact K" and cv: "continuous_on K v" and g: "0 < \<gamma>"
  shows "\<exists>d>0. \<forall>p\<in>K. \<forall>q\<in>K. \<gamma> \<le> v p - v q \<longrightarrow> d \<le> norm (p - q)"
proof (rule ccontr)
  assume "\<not> (\<exists>d>0. \<forall>p\<in>K. \<forall>q\<in>K. \<gamma> \<le> v p - v q \<longrightarrow> d \<le> norm (p - q))"
  then have H: "\<And>d. 0 < d \<Longrightarrow> \<exists>p\<in>K. \<exists>q\<in>K. \<gamma> \<le> v p - v q \<and> norm (p - q) < d"
    by force
  have ex: "\<forall>n::nat. \<exists>z. fst z \<in> K \<and> snd z \<in> K
      \<and> \<gamma> \<le> v (fst z) - v (snd z) \<and> norm (fst z - snd z) < 1/(2 + real n)"
  proof
    fix n :: nat
    have pos: "0 < 1/(2 + real n)" by simp
    obtain p q where "p \<in> K" "q \<in> K" "\<gamma> \<le> v p - v q"
        "norm (p - q) < 1/(2 + real n)"
      using H[OF pos] by blast
    then show "\<exists>z. fst z \<in> K \<and> snd z \<in> K
        \<and> \<gamma> \<le> v (fst z) - v (snd z) \<and> norm (fst z - snd z) < 1/(2 + real n)"
      by (intro exI[of _ "(p, q)"]) simp
  qed
  have exZ: "\<exists>Z. \<forall>n. fst (Z n) \<in> K \<and> snd (Z n) \<in> K
      \<and> \<gamma> \<le> v (fst (Z n)) - v (snd (Z n))
      \<and> norm (fst (Z n) - snd (Z n)) < 1/(2 + real n)"
    using ex by (rule choice)
  then obtain Z where Z: "\<forall>n. fst (Z n) \<in> K \<and> snd (Z n) \<in> K
      \<and> \<gamma> \<le> v (fst (Z n)) - v (snd (Z n))
      \<and> norm (fst (Z n) - snd (Z n)) < 1/(2 + real n)"
    by blast
  have pK: "fst (Z n) \<in> K" for n using Z by blast
  have qK: "snd (Z n) \<in> K" for n using Z by blast
  have gapn: "\<gamma> \<le> v (fst (Z n)) - v (snd (Z n))" for n using Z by blast
  have small: "norm (fst (Z n) - snd (Z n)) \<le> 1/(2 + real n)" for n
  proof -
    have "norm (fst (Z n) - snd (Z n)) < 1/(2 + real n)" using Z by blast
    then show ?thesis by linarith
  qed
  have diff0: "(\<lambda>n. fst (Z n) - snd (Z n)) \<longlonglongrightarrow> 0"
    by (rule tendsto_of_norm_bound[OF small tilt_sequence_tendsto])
  have allp: "\<forall>n. fst (Z n) \<in> K" using pK by blast
  obtain l r where lK: "l \<in> K" and sm: "strict_mono r"
    and lim: "((\<lambda>n. fst (Z n)) \<circ> r) \<longlonglongrightarrow> l"
    by (rule seq_compactE[OF compact_imp_seq_compact[OF cK] allp])
  have limp: "(\<lambda>n. fst (Z (r n))) \<longlonglongrightarrow> l" using lim by (simp add: o_def)
  have limq: "(\<lambda>n. snd (Z (r n))) \<longlonglongrightarrow> l"
  proof -
    have "((\<lambda>n. fst (Z n) - snd (Z n)) \<circ> r) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_subseq_LIMSEQ[OF diff0 sm])
    then have d0: "(\<lambda>n. fst (Z (r n)) - snd (Z (r n))) \<longlonglongrightarrow> 0"
      by (simp add: o_def)
    have "(\<lambda>n. fst (Z (r n)) - (fst (Z (r n)) - snd (Z (r n)))) \<longlonglongrightarrow> l - 0"
      by (rule tendsto_diff[OF limp d0])
    then show ?thesis by simp
  qed
  have seqc: "\<And>x a. a \<in> K \<Longrightarrow> (\<forall>n. x n \<in> K) \<Longrightarrow> x \<longlonglongrightarrow> a \<Longrightarrow> (v \<circ> x) \<longlonglongrightarrow> v a"
    using cv unfolding continuous_on_sequentially by blast
  have cvp: "(\<lambda>n. v (fst (Z (r n)))) \<longlonglongrightarrow> v l"
  proof -
    have "(v \<circ> (\<lambda>n. fst (Z (r n)))) \<longlonglongrightarrow> v l"
      by (rule seqc[OF lK _ limp]) (use pK in blast)
    then show ?thesis by (simp add: o_def)
  qed
  have cvq: "(\<lambda>n. v (snd (Z (r n)))) \<longlonglongrightarrow> v l"
  proof -
    have "(v \<circ> (\<lambda>n. snd (Z (r n)))) \<longlonglongrightarrow> v l"
      by (rule seqc[OF lK _ limq]) (use qK in blast)
    then show ?thesis by (simp add: o_def)
  qed
  have "\<gamma> \<le> v l - v l"
  proof (rule tendsto_lowerbound[OF tendsto_diff[OF cvp cvq]])
    show "\<forall>\<^sub>F n in sequentially. \<gamma> \<le> v (fst (Z (r n))) - v (snd (Z (r n)))"
      using gapn by simp
  qed simp
  then show False using g by simp
qed

text \<open>Two consequences: \<open>doubling_grad_lower_bound\<close> with the Lipschitz
  hypothesis replaced by an abstract separation, and the same for the
  shared gradient's norm - the separation plays exactly the role the
  Lipschitz constant did.\<close>

text \<open>For the doubling run on sup-convolutions, the separation is required of
  \<open>supconv(-w)\<epsilon>\<close> itself, supplied by \<open>positive_separation_of_value_gap\<close>
  from compactness of \<open>K\<close> and \<open>supconv_continuous\<close> alone - no Lipschitz
  constant enters.  The sign bookkeeping is as in
  \<open>doubling_grad_lower_bound_supconv\<close>, with \<open>w\<close> instantiated at \<open>-B\<close>.\<close>

text \<open>The parameter choice for the shifted family: the perturbation \<open>\<delta>\<^sub>i\<close> and
  Jensen's tilt \<open>dd\<^sub>i\<close> must satisfy \<open>shifted_jensen_smallness\<close>'s
  \<open>dd\<^sub>i < \<delta>\<^sub>i\<rho>\<^sup>2/(2r)\<close>; taking \<open>\<delta>\<^sub>i=D\<^sub>0/(2+i)\<close> and \<open>dd\<^sub>i=\<delta>\<^sub>i\<rho>\<^sup>2/(4r)\<close>
  satisfies it with room to spare, and both sequences vanish.\<close>

lemma shifted_family_parameters:
  fixes D\<^sub>0 \<rho> r :: real
  assumes D0: "0 < D\<^sub>0" and rho: "0 < \<rho>" and r: "0 < r"
  shows "0 < D\<^sub>0/(2 + real i)"
    and "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)"
    and "D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
        < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (2*r)"
    and "(\<lambda>i. D\<^sub>0/(2 + real i)) \<longlonglongrightarrow> 0"
    and "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) \<longlonglongrightarrow> 0"
proof -
  show d1: "0 < D\<^sub>0/(2 + real i)"
    by (rule tilt_sequence_pos[OF D0])
  have rs: "0 < \<rho>\<^sup>2" using rho by simp
  have dr: "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2"
    by (rule mult_pos_pos[OF d1 rs])
  have r4: "0 < 4*r" using r by simp
  show "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)"
    by (rule divide_pos_pos[OF dr r4])
  show "D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (2*r)"
    by (rule divide_strict_left_mono[OF _ dr]) (use r in auto)
  show t0: "(\<lambda>i. D\<^sub>0/(2 + real i)) \<longlonglongrightarrow> 0"
    by (rule tilt_sequence_tendsto)
  have "(\<lambda>i. D\<^sub>0/(2 + real i) * (\<rho>\<^sup>2 / (4*r))) \<longlonglongrightarrow> 0 * (\<rho>\<^sup>2 / (4*r))"
    by (rule tendsto_mult[OF t0 tendsto_const])
  then show "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) \<longlonglongrightarrow> 0"
    by simp
qed

subsection \<open>The sup-convolution is attained\<close>

text \<open>\<open>comparison_supconv_sequence_complete\<close> takes attainment of each
  sup-convolution as a hypothesis - the points \<open>y\<^sub>s\<close> where
  \<open>supconv u \<epsilon> x = u y\<^sub>s - dist(x,y\<^sub>s)\<^sup>2/(2\<epsilon>)\<close>.  For continuous \<open>u\<close>
  bounded above they exist by coercivity: beyond an explicit radius
  \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))+1\<close> the penalty already beats the value at \<open>x\<close>,
  so the supremum over the whole space equals the supremum over one
  compact ball, attained by continuity.\<close>

theorem supconv_attained_ball:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
  shows "\<exists>ys. dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"proof -
  define M where "M = max 0 (2*\<epsilon>*(Bu - u x))"
  have M0: "0 \<le> M" unfolding M_def by simp
  have s0: "0 \<le> sqrt M" using M0 by simp
  define R where "R = sqrt M + 1"
  have R0: "0 < R" unfolding R_def using s0 by linarith
  have Rsq: "2*\<epsilon>*(Bu - u x) < R\<^sup>2"
  proof -
    have sq: "(sqrt M)\<^sup>2 = M" using M0 by simp
    have exp: "R\<^sup>2 = (sqrt M)\<^sup>2 + 2 * sqrt M + 1"
      unfolding R_def by (simp add: power2_eq_square algebra_simps)
    have "M \<le> R\<^sup>2"
      unfolding exp sq using s0 by linarith
    moreover have "2*\<epsilon>*(Bu - u x) \<le> M"
      unfolding M_def by simp
    moreover have "M < R\<^sup>2"
      unfolding exp sq using s0 by linarith
    ultimately show ?thesis by linarith
  qed
  have cpt: "compact (cball x R)" by (rule compact_cball)
  have ne: "cball x R \<noteq> {}" using R0 by auto
  have cont: "continuous_on (cball x R) (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
    by (intro continuous_intros continuous_on_subset[OF cu subset_UNIV])
       (use e in auto)
  obtain ys where ysin: "ys \<in> cball x R"
    and ysmax: "\<forall>y \<in> cball x R.
        u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using continuous_attains_sup[OF cpt ne cont] by blast
  have xin: "x \<in> cball x R" using R0 by simp
  have key: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)" for y
  proof (cases "dist x y \<le> R")
    case True
    then have "y \<in> cball x R" by (simp add: dist_commute)
    with ysmax show ?thesis by blast
  next
    case False
    then have gt: "R < dist x y" by simp
    have lt: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) < u x"
    proof -
      have "R\<^sup>2 < (dist x y)\<^sup>2"
        by (rule power_strict_mono[OF gt less_imp_le[OF R0]]) simp
      then have big: "2*\<epsilon>*(Bu - u x) < (dist x y)\<^sup>2"
        using Rsq by linarith
      have c0: "0 < 2*\<epsilon>" using e by simp
      have "(Bu - u x) * (2*\<epsilon>) < (dist x y)\<^sup>2"
        using big by (simp add: algebra_simps)
      then have "Bu - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
        using c0 by (simp add: pos_less_divide_eq)
      then show ?thesis using B[of y] by linarith
    qed
    have xval: "u x = u x - (dist x x)\<^sup>2 / (2*\<epsilon>)" by simp
    have "u x - (dist x x)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      using ysmax xin by blast
    with lt xval show ?thesis by linarith
  qed
  have "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  proof (rule antisym)
    show "supconv u \<epsilon> x \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      unfolding supconv_def by (rule cSUP_least) (auto simp: key)
    show "u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>) \<le> supconv u \<epsilon> x"
      unfolding supconv_def
      by (intro cSUP_upper supconv_bdd_above[OF B e]) simp
  qed
  moreover have "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    using ysin unfolding R_def M_def by (simp add: dist_commute)
  ultimately show ?thesis by blast
qed

corollary supconv_attained:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
  shows "\<exists>ys. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  using supconv_attained_ball[OF B e cu] by blast

text \<open>As a family: along any sequence of base points the attaining points can
  be chosen simultaneously by countable choice, with no uniformity in
  \<open>i\<close> needed.\<close>

text \<open>The attaining point lies in an explicit ball of radius
  \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))+1\<close> around the base point, an \<open>O(\<surd>\<epsilon>)\<close> bound
  that makes the \<open>y\<^sub>s \<in> \<Omega>\<close> hypothesis of the comparison theorems
  dischargeable rather than assumed.  Stated as a separate corollary so
  existing consumers of \<open>supconv_attained\<close> are untouched.\<close>

corollary supconv_attained_in:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and sub: "cball x (sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1) \<subseteq> \<Omega>"
  shows "\<exists>ys \<in> \<Omega>. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where d: "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_ball[OF B e cu] by blast
  have "ys \<in> cball x (sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1)"
    using d by (simp add: dist_commute)
  with sub have "ys \<in> \<Omega>" by blast
  with v show ?thesis by blast
qed

text \<open>The family form: along any sequence of base points, the attaining points
  can be chosen inside \<open>\<Omega>\<close> simultaneously, provided each base point's
  ball is.\<close>

corollary supconv_attained_family_in:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and xs :: "nat \<Rightarrow> 'a"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and sub: "\<And>i. cball (xs i)
        (sqrt (max 0 (2*\<epsilon>*(Bu - u (xs i)))) + 1) \<subseteq> \<Omega>"
  shows "\<exists>ys. \<forall>i. ys i \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u (ys i) - (dist (xs i) (ys i))\<^sup>2 / (2*\<epsilon>)"
proof -
  have "\<forall>i. \<exists>y. y \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u y - (dist (xs i) y)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_in[OF B e cu sub] by blast
  then show ?thesis by (rule choice)
qed

subsection \<open>The attainment radius as a parameter\<close>

text \<open>The \<open>+1\<close> in \<open>supconv_attained_ball\<close> is an artifact of a strict
  inequality in its proof; with it, \<open>cball x R \<subseteq> \<Omega>\<close> asks \<open>\<Omega>\<close> for a ball
  of radius one, which no bounded \<open>\<Omega>\<close> of small diameter has.  Any radius
  exceeding \<open>\<surd>(max 0 (2\<epsilon>(B\<^sub>u-u x)))\<close> serves as well, separating the
  hypothesis into a geometric condition on \<open>R\<close> and a smallness condition
  on \<open>\<epsilon>\<close>, discharged separately at the top level.\<close>

theorem supconv_attained_ball_rad:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
  shows "\<exists>ys. dist x ys \<le> R
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  define M where "M = max 0 (2*\<epsilon>*(Bu - u x))"
  have M0: "0 \<le> M" unfolding M_def by simp
  have s0: "0 \<le> sqrt M" using M0 by simp
  have sR: "sqrt M < R" using R unfolding M_def .
  have R0: "0 < R" using s0 sR by linarith
  have Rsq: "2*\<epsilon>*(Bu - u x) < R\<^sup>2"
  proof -
    have sq: "(sqrt M)\<^sup>2 = M" using M0 by simp
    have "(sqrt M)\<^sup>2 < R\<^sup>2"
      by (rule power_strict_mono[OF sR s0]) simp
    then have "M < R\<^sup>2" unfolding sq .
    moreover have "2*\<epsilon>*(Bu - u x) \<le> M" unfolding M_def by simp
    ultimately show ?thesis by linarith
  qed
  have cpt: "compact (cball x R)" by (rule compact_cball)
  have ne: "cball x R \<noteq> {}" using R0 by auto
  have cont: "continuous_on (cball x R) (\<lambda>y. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
    by (intro continuous_intros continuous_on_subset[OF cu subset_UNIV])
       (use e in auto)
  obtain ys where ysin: "ys \<in> cball x R"
    and ysmax: "\<forall>y \<in> cball x R.
        u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using continuous_attains_sup[OF cpt ne cont] by blast
  have xin: "x \<in> cball x R" using R0 by simp
  have key: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)" for y
  proof (cases "dist x y \<le> R")
    case True
    then have "y \<in> cball x R" by (simp add: dist_commute)
    with ysmax show ?thesis by blast
  next
    case False
    then have gt: "R < dist x y" by simp
    have lt: "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) < u x"
    proof -
      have "R\<^sup>2 < (dist x y)\<^sup>2"
        by (rule power_strict_mono[OF gt less_imp_le[OF R0]]) simp
      then have big: "2*\<epsilon>*(Bu - u x) < (dist x y)\<^sup>2"
        using Rsq by linarith
      have c0: "0 < 2*\<epsilon>" using e by simp
      have "(Bu - u x) * (2*\<epsilon>) < (dist x y)\<^sup>2"
        using big by (simp add: algebra_simps)
      then have "Bu - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
        using c0 by (simp add: pos_less_divide_eq)
      then show ?thesis using B[of y] by linarith
    qed
    have xval: "u x = u x - (dist x x)\<^sup>2 / (2*\<epsilon>)" by simp
    have "u x - (dist x x)\<^sup>2 / (2*\<epsilon>) \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      using ysmax xin by blast
    with lt xval show ?thesis by linarith
  qed
  have "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
  proof (rule antisym)
    show "supconv u \<epsilon> x \<le> u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
      unfolding supconv_def by (rule cSUP_least) (auto simp: key)
    show "u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>) \<le> supconv u \<epsilon> x"
      unfolding supconv_def
      by (intro cSUP_upper supconv_bdd_above[OF B e]) simp
  qed
  moreover have "dist x ys \<le> R"
    using ysin by (simp add: dist_commute)
  ultimately show ?thesis by blast
qed

corollary supconv_attained_in_rad:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
    and sub: "cball x R \<subseteq> \<Omega>"
  shows "\<exists>ys \<in> \<Omega>. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where d: "dist x ys \<le> R"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_ball_rad[OF B e cu R] by blast
  have "ys \<in> cball x R"
    using d by (simp add: dist_commute)
  with sub have "ys \<in> \<Omega>" by blast
  with v show ?thesis by blast
qed

corollary supconv_attained_family_in_rad:
  fixes u :: "'a::euclidean_space \<Rightarrow> real" and xs :: "nat \<Rightarrow> 'a"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "\<And>i. sqrt (max 0 (2*\<epsilon>*(Bu - u (xs i)))) < R"
    and sub: "\<And>i. cball (xs i) R \<subseteq> \<Omega>"
  shows "\<exists>ys. \<forall>i. ys i \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u (ys i) - (dist (xs i) (ys i))\<^sup>2 / (2*\<epsilon>)"
proof -
  have "\<forall>i. \<exists>y. y \<in> \<Omega>
      \<and> supconv u \<epsilon> (xs i) = u y - (dist (xs i) y)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_in_rad[OF B e cu R sub] by blast
  then show ?thesis by (rule choice)
qed

text \<open>Every attainment point, not just the one \<open>supconv_attained_ball\<close>
  produces, lies inside that radius: if \<open>z\<close> attains then
  \<open>u z - dist\<^sup>2/(2\<epsilon>) \<ge> u x\<close> gives \<open>dist\<^sup>2 \<le> 2\<epsilon>(B\<^sub>u-u x)\<close>.  The universal
  form is needed where membership of the attainment point in \<open>\<Omega>\<close> comes
  from a gate on \<open>u\<close> rather than from a ball.\<close>

lemma supconv_attain_radius:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and opt: "supconv u \<epsilon> x = u z - (dist x z)\<^sup>2 / (2*\<epsilon>)"
  shows "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))"
proof -
  have ge: "u x \<le> supconv u \<epsilon> x" by (rule supconv_ge[OF B e])
  have "u x \<le> u z - (dist x z)\<^sup>2 / (2*\<epsilon>)" using ge unfolding opt .
  then have "(dist x z)\<^sup>2 / (2*\<epsilon>) \<le> u z - u x" by linarith
  moreover have "u z - u x \<le> Bu - u x" using B[of z] by linarith
  ultimately have "(dist x z)\<^sup>2 / (2*\<epsilon>) \<le> Bu - u x" by linarith
  then have sq: "(dist x z)\<^sup>2 \<le> 2*\<epsilon>*(Bu - u x)"
    using e by (simp add: pos_divide_le_eq mult.commute)
  then have sq': "(dist x z)\<^sup>2 \<le> max 0 (2*\<epsilon>*(Bu - u x))" by simp
  have "dist x z = sqrt ((dist x z)\<^sup>2)" by simp
  also have "\<dots> \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))"
    using sq' by (rule real_sqrt_le_mono)
  finally show ?thesis .
qed

subsection \<open>The sup-convolution converges to its function, with a rate\<close>

text \<open>Locating the doubling maximiser needs \<open>supconv u \<epsilon>\<close> close to \<open>u\<close>, not
  merely above it: \<open>supconv_ge\<close> gives \<open>u \<le> supconv u \<epsilon>\<close>, and
  \<open>supconv_attained_ball_rad\<close> bounds the attainment radius.  With a
  global two-sided bound \<open>B\<^sub>l \<le> u \<le> B\<^sub>u\<close> that radius is \<open>O(\<surd>\<epsilon>)\<close>
  uniformly in \<open>x\<close>, so with a modulus of continuity for \<open>u\<close>,
  \<open>supconv u \<epsilon> \<le> u + \<sigma>\<close> for every sufficiently small \<open>\<epsilon>\<close>, with no
  Lipschitz constant needed.\<close>

text \<open>\<open>supconv_uniform_upper\<close> is false for merely usc data; what usc data
  gives instead, matching the classical Crandall--Ishii argument, is a
  local upper bound with no continuity and no attainment: if \<open>u \<le> M\<close> on
  \<open>cball x R\<close> and the penalty already beats the global range outside it,
  then \<open>supconv u \<epsilon> x \<le> M\<close>.  \<open>supconv_le_of_local_bound\<close> gets the same
  conclusion via attainment, needing \<open>continuous_on UNIV u\<close>.\<close>

lemma supconv_le_of_local_bound_usc:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>" and R0: "0 \<le> R"
    and gap: "2*\<epsilon>*(Bu - M) < R\<^sup>2"
    and loc: "\<And>y. dist x y \<le> R \<Longrightarrow> u y \<le> M"
  shows "supconv u \<epsilon> x \<le> M"
  unfolding supconv_def
proof (rule cSUP_least)
  show "(UNIV :: 'a set) \<noteq> {}" by simp
  fix y :: 'a
  show "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> M"
  proof (cases "dist x y \<le> R")
    case True
    have "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)" using e by simp
    then show ?thesis using loc[OF True] by linarith
  next
    case False
    then have Rlt: "R < dist x y" by linarith
    have "R\<^sup>2 \<le> (dist x y)\<^sup>2" using R0 Rlt by (intro power_mono) simp_all
    then have "2*\<epsilon>*(Bu - M) < (dist x y)\<^sup>2" using gap by linarith
    then have "Bu - M < (dist x y)\<^sup>2 / (2*\<epsilon>)"
      using e by (simp add: pos_less_divide_eq mult.commute)
    then show ?thesis using B[of y] by linarith
  qed
qed

text \<open>Along any sequence of base points converging to \<open>x\<^sub>0\<close> with
  \<open>\<epsilon>\<^sub>j \<rightarrow> 0\<close>, the sup-convolutions are eventually below any strict upper
  bound for \<open>u\<close> at \<open>x\<^sub>0\<close>: the attainment radius \<open>\<surd>(2\<epsilon>\<^sub>j(B\<^sub>u-B\<^sub>l))\<close> shrinks
  into the neighbourhood where usc gives \<open>u < c\<close>.\<close>

subsection \<open>Shrinking the domain, and extending \<open>u\<close> off \<open>K\<close>\<close>

text \<open>All three viscosity predicates quantify over \<open>x \<in> \<Omega>\<close>, so each is
  antitone in \<open>\<Omega>\<close>: this restricts the \<open>u\<close>-side from Definition 3.1's
  gated set to \<open>{u>0}\<close>, and the \<open>w\<close>-side from \<open>interior K'\<close> to a small
  neighbourhood of the maximiser.\<close>

lemma visc_subsol_mono_dom:
  assumes s: "visc_subsol k L \<Omega> u" and sub: "\<Omega>' \<subseteq> \<Omega>"
  shows "visc_subsol k L \<Omega>' u"
  using s sub unfolding visc_subsol_def by blast

text \<open>\<open>visc_subsol_env k L K \<Omega> u\<close> reads \<open>u\<close> only on \<open>K\<close>, insensitive to its
  values off \<open>K\<close>, which is what makes the extension below legitimate:
  Definition 3.1(a) transfers to the extended function for free.\<close>

lemma visc_subsol_env_agrees:
  fixes K :: "(real^'n::finite) set"
  assumes sub: "visc_subsol_env2 k L K \<Omega> u" and OK: "\<Omega> \<subseteq> K"
    and eq: "\<And>y. y \<in> K \<Longrightarrow> u' y = u y"
  shows "visc_subsol_env2 k L K \<Omega> u'"
  unfolding visc_subsol_env2_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_C2 \<phi> g H x"
    and gl: "\<forall>y\<in>K. u' y - \<phi> y \<le> u' x - \<phi> x"
  have xK: "x \<in> K" using x OK by blast
  have gl': "\<forall>y\<in>K. u y - \<phi> y \<le> u x - \<phi> x"
  proof
    fix y assume y: "y \<in> K"
    have "u y - \<phi> y = u' y - \<phi> y" using eq[OF y] by simp
    also have "\<dots> \<le> u' x - \<phi> x" using gl y by blast
    also have "\<dots> = u x - \<phi> x" using eq[OF xK] by simp
    finally show "u y - \<phi> y \<le> u x - \<phi> x" .
  qed
  show "ell_op_lsc k L (g x) H \<le> 1"
    using sub x tf gl' unfolding visc_subsol_env2_def by blast
qed

text \<open>Extending an usc \<open>u\<close> off a closed \<open>K\<close> by a constant at or below its
  minimum on \<open>K\<close> keeps it usc; @{thm [source] usc_extension_bounded} in
  @{theory Relative_Arbitrage.Operator_Envelopes} does the \<open>-B\<close> case, needed as negative as required so the
  doubled functional cannot be maximised off \<open>K\<close>.\<close>

lemma usc_extend_const_below:
  fixes u :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes cl: "closed K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lo: "\<And>y. y \<in> K \<Longrightarrow> Bl \<le> u y" and CB: "C \<le> Bl"
    and lt: "(if z \<in> K then u z else C) < c"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> (if y \<in> K then u y else C) < c"
proof (cases "z \<in> K")
  case True
  then have uz: "u z < c" using lt by simp
  have Cc: "C < c" using CB lo[OF True] uz by linarith
  obtain e where e0: "0 < e" and h: "\<And>y. dist z y < e \<Longrightarrow> u y < c"
    using uscu[OF uz] by blast
  show ?thesis
  proof (rule exI[of _ e], intro conjI allI impI e0)
    fix y assume "dist z y < e"
    then show "(if y \<in> K then u y else C) < c" using h Cc by simp
  qed
next
  case False
  then have Cc: "C < c" using lt by simp
  have opn: "open (- K)" using cl by (rule open_Compl)
  have zin: "z \<in> - K" using False by simp
  obtain e where e0: "0 < e" and bl: "ball z e \<subseteq> - K"
    using opn zin unfolding open_contains_ball by blast
  show ?thesis
  proof (rule exI[of _ e], intro conjI allI impI e0)
    fix y assume dy: "dist z y < e"
    then have "y \<in> ball z e" by (simp add: dist_commute)
    then have "y \<notin> K" using bl by blast
    then show "(if y \<in> K then u y else C) < c" using Cc by simp
  qed
qed

text \<open>Far from \<open>K\<close> the extended function's sup-convolution returns to the
  constant, since the whole competing ball misses \<open>K\<close>: this confines the
  doubling maximiser to a bounded neighbourhood of \<open>K\<close> without boundary
  avoidance on the \<open>x\<close>-side.\<close>

lemma supconv_extend_far_le:
  fixes u :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes B: "\<And>y. \<theta> * (if y \<in> K then u y else C) \<le> Bu" and e: "0 < \<epsilon>"
    and d0: "0 \<le> d" and gap: "2*\<epsilon>*(Bu - \<theta>*C) < d\<^sup>2"
    and far: "\<And>b. b \<in> K \<Longrightarrow> d < dist x b"
  shows "supconv (\<lambda>y. \<theta> * (if y \<in> K then u y else C)) \<epsilon> x \<le> \<theta>*C"
proof (rule supconv_le_of_local_bound_usc[OF B e d0 gap])
  fix y assume dy: "dist x y \<le> d"
  have "y \<notin> K"
  proof
    assume "y \<in> K"
    from far[OF this] show False using dy by linarith
  qed
  then show "\<theta> * (if y \<in> K then u y else C) \<le> \<theta>*C" by simp
qed
text \<open>The Crandall--Ishii core needs \<open>continuous_on UNIV\<close> only to attain the
  sup-convolution's supremum, more than necessary: the competitor
  \<open>y \<mapsto> u y - dist\<^sup>2/(2\<epsilon>)\<close> is usc as soon as \<open>u\<close> is, bounded above, and
  below its value at \<open>x\<close> outside an explicit ball, so \<open>usc_attains_sup_gen\<close>
  on that compact ball gives a global maximiser - letting the chain run on
  usc/lsc data directly.\<close>

lemma supconv_attained_usc_ball:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  obtains ys where "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
    and "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  define R where "R = sqrt (max 0 (2*\<epsilon>*(Bu - u x))) + 1"
  have R1: "1 \<le> R" unfolding R_def by simp
  have R0: "0 < R" using R1 by linarith
  define g where "g = (\<lambda>y :: real^'n. u y - (dist x y)\<^sup>2 / (2*\<epsilon>))"
  have ene: "2*\<epsilon> \<noteq> 0" using e by simp
  have pc: "isCont (\<lambda>y :: real^'n. - ((dist x y)\<^sup>2 / (2*\<epsilon>))) z" for z
    by (intro continuous_intros) (use ene in simp_all)
  have p2: "\<exists>d>0. \<forall>y. dist zz y < d \<longrightarrow> - ((dist x y)\<^sup>2 / (2*\<epsilon>)) < cc"
    if "- ((dist x zz)\<^sup>2 / (2*\<epsilon>)) < cc" for cc and zz :: "real^'n"
    by (rule usc_eps_of_continuous[OF pc that])
  have gusc: "\<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> g y < c" if lt: "g z < c"
    for c and z :: "real^'n"
  proof -
    have lt': "u z + (- ((dist x z)\<^sup>2 / (2*\<epsilon>))) < c"
      using lt unfolding g_def by simp
    from usc_eps_add[OF uscu p2 lt'] obtain d where d0: "0 < d"
      and h: "\<forall>y. dist z y < d \<longrightarrow> u y + (- ((dist x y)\<^sup>2 / (2*\<epsilon>))) < c"
      by blast
    show ?thesis
    proof (rule exI[of _ d], intro conjI allI impI d0)
      fix y assume "dist z y < d"
      then show "g y < c" using h unfolding g_def by simp
    qed
  qed
  have gB: "g y \<le> Bu" for y
  proof -
    have "0 \<le> (dist x y)\<^sup>2 / (2*\<epsilon>)" using e by simp
    then show ?thesis unfolding g_def using B[of y] by linarith
  qed
  have neS: "cball x R \<noteq> {}" using R0 by auto
  obtain ys where ysS: "ys \<in> cball x R"
    and mxb: "\<And>y. y \<in> cball x R \<Longrightarrow> g y \<le> g ys"
    using usc_attains_sup_gen[OF gusc _ compact_cball neS, of Bu] gB by blast
  have xS: "x \<in> cball x R" using R0 by simp
  have glob: "g y \<le> g ys" for y
  proof (cases "dist x y \<le> R")
    case True
    then have "y \<in> cball x R" by (simp add: dist_commute)
    then show ?thesis by (rule mxb)
  next
    case False
    then have dR: "R < dist x y" by linarith
    have s0: "0 \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))" by simp
    have "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < dist x y"
      using dR unfolding R_def by linarith
    then have "(sqrt (max 0 (2*\<epsilon>*(Bu - u x))))\<^sup>2 < (dist x y)\<^sup>2"
      using s0 by (intro power_strict_mono) simp_all
    then have Rsq: "max 0 (2*\<epsilon>*(Bu - u x)) < (dist x y)\<^sup>2" by simp
    then have "2*\<epsilon>*(Bu - u x) < (dist x y)\<^sup>2" by simp
    then have "Bu - u x < (dist x y)\<^sup>2 / (2*\<epsilon>)"
      using e by (simp add: pos_less_divide_eq mult.commute)
    then have "g y < u x" unfolding g_def using B[of y] by linarith
    moreover have "u x = g x" unfolding g_def by simp
    moreover have "g x \<le> g ys" by (rule mxb[OF xS])
    ultimately show ?thesis by linarith
  qed
  have bdd: "bdd_above (range (\<lambda>y :: real^'n. u y - (dist x y)\<^sup>2 / (2*\<epsilon>)))"
    by (rule supconv_bdd_above[OF B e])
  have le: "supconv u \<epsilon> x \<le> g ys"
    unfolding supconv_def
  proof (rule cSUP_least)
    show "(UNIV :: (real^'n) set) \<noteq> {}" by simp
    fix y :: "real^'n"
    show "u y - (dist x y)\<^sup>2 / (2*\<epsilon>) \<le> g ys"
      using glob[of y] unfolding g_def by simp
  qed
  have ge: "g ys \<le> supconv u \<epsilon> x"
    unfolding supconv_def g_def by (rule cSUP_upper[OF UNIV_I bdd])
  have eq: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using le ge unfolding g_def by linarith
  have dR: "dist x ys \<le> R" using ysS by (simp add: dist_commute)
  show ?thesis by (rule that[of ys]) (use dR eq in \<open>simp_all add: R_def\<close>)
qed

lemma supconv_attained_usc_ball_rad:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
  shows "\<exists>ys. dist x ys \<le> R
      \<and> supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball[OF B e uscu] by blast
  have "dist x ys \<le> sqrt (max 0 (2*\<epsilon>*(Bu - u x)))"
    by (rule supconv_attain_radius[OF B e v])
  then have "dist x ys \<le> R" using R by linarith
  with v show ?thesis by blast
qed

corollary supconv_attained_usc_in_rad:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
    and sub: "cball x R \<subseteq> \<Omega>"
  shows "\<exists>ys \<in> \<Omega>. supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
proof -
  obtain ys where d: "dist x ys \<le> R"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball_rad[OF B e uscu R] by blast
  have "ys \<in> cball x R" using d by (simp add: dist_commute)
  with sub have "ys \<in> \<Omega>" by blast
  with v show ?thesis by blast
qed

corollary supconv_attained_usc_family:
  fixes u :: "real^'n::finite \<Rightarrow> real" and xs :: "nat \<Rightarrow> real^'n"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> u y < c"
  shows "\<exists>ys. \<forall>i. supconv u \<epsilon> (xs i)
      = u (ys i) - (dist (xs i) (ys i))\<^sup>2 / (2*\<epsilon>)"
proof -
  have "\<forall>i. \<exists>y. supconv u \<epsilon> (xs i) = u y - (dist (xs i) y)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_ball[OF B e uscu] by blast
  then show ?thesis by (rule choice)
qed

text \<open>The two-domain localised maximiser replaces
  \<open>doubling_localised_maximiser_soft\<close> with the \<open>x\<close>-side boundary avoidance
  gone: maximise the doubled sup-convolved functional over the compact
  \<open>Q \<times> K'\<close>; if the \<open>x\<close>-side sup-convolution is below \<open>\<beta>\<close> off \<open>Q\<close> and a
  witness beats \<open>\<beta>+B\<^sub>w\<close>, the maximiser maximises over all of
  \<open>UNIV \<times> K'\<close>, leaving only the \<open>y\<close>-coordinate constrained - which
  \<open>K \<subseteq> K'\<^sup>\<circ>\<close> gives room for.  This is why Theorem 4.2(b) runs on two
  domains.\<close>

lemma doubled_maximiser_over_UNIV_snd:
  fixes A Bfun Pn :: "real^'n::finite \<Rightarrow> real" and K' Q :: "(real^'n) set"
  assumes cQ: "compact Q" and cK': "compact K'"
    and cA: "continuous_on UNIV A" and cB: "continuous_on UNIV Bfun"
    and cP: "continuous_on UNIV Pn"
    and zQ: "z \<in> Q" and zK': "z \<in> K'"
    and Bw: "\<And>y. Bfun y \<le> Bw"
    and Pnn: "\<And>d. 0 \<le> Pn d"
    and out: "\<And>x. x \<notin> Q \<Longrightarrow> A x \<le> \<beta>"
    and gapv: "\<beta> + Bw < A z + Bfun z - Pn (z - z)"
  obtains xh yh where "xh \<in> Q" and "yh \<in> K'"
    and "\<And>x y. y \<in> K' \<Longrightarrow>
        A x + Bfun y - Pn (x - y) \<le> A xh + Bfun yh - Pn (xh - yh)"
proof -
  define S where "S = Q \<times> K'"
  define F where "F = (\<lambda>p :: (real^'n) \<times> (real^'n).
      A (fst p) + Bfun (snd p) - Pn (fst p - snd p))"
  have cS: "compact S" unfolding S_def by (rule compact_Times[OF cQ cK'])
  have zS: "(z, z) \<in> S" unfolding S_def using zQ zK' by simp
  have neS: "S \<noteq> {}" using zS by blast
  have cF: "continuous_on S F"
    unfolding F_def
    by (intro continuous_intros
        continuous_on_compose2[OF cA continuous_on_fst[OF continuous_on_id]]
        continuous_on_compose2[OF cB continuous_on_snd[OF continuous_on_id]]
        continuous_on_compose2[OF cP])
      auto
  obtain \<xi> where xiS: "\<xi> \<in> S" and mxS: "\<And>p. p \<in> S \<Longrightarrow> F p \<le> F \<xi>"
    using continuous_attains_sup[OF cS neS cF] by blast
  have xhQ: "fst \<xi> \<in> Q" and yhK: "snd \<xi> \<in> K'"
    using xiS unfolding S_def by auto
  have base: "A z + Bfun z - Pn (z - z) \<le> F \<xi>"
    using mxS[OF zS] unfolding F_def by simp
  have all: "A x + Bfun y - Pn (x - y)
      \<le> A (fst \<xi>) + Bfun (snd \<xi>) - Pn (fst \<xi> - snd \<xi>)" if y: "y \<in> K'" for x y
  proof (cases "x \<in> Q")
    case True
    then have "(x, y) \<in> S" unfolding S_def using y by simp
    from mxS[OF this] show ?thesis unfolding F_def by simp
  next
    case False
    have "A x + Bfun y - Pn (x - y) \<le> \<beta> + Bw"
      using out[OF False] Bw[of y] Pnn[of "x - y"] by linarith
    also have "\<dots> < A z + Bfun z - Pn (z - z)" by (rule gapv)
    also have "\<dots> \<le> F \<xi>" by (rule base)
    finally show ?thesis unfolding F_def by simp
  qed
  show ?thesis by (rule that[OF xhQ yhK]) (use all in blast)
qed

text \<open>Maximality over \<open>UNIV \<times> K'\<close> restricts to the ball the Crandall--Ishii
  core wants as soon as the \<open>y\<close>-coordinate has room; the \<open>x\<close>-coordinate is
  unconstrained.\<close>

lemma mxK_of_UNIV_snd:
  fixes A Bfun Pn :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. y \<in> K' \<Longrightarrow>
      A x + Bfun y - Pn (x - y)
      \<le> A (fst \<xi>\<^sub>0) + Bfun (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and ball: "cball (snd \<xi>\<^sub>0) r \<subseteq> K'"
    and p: "p \<in> cball \<xi>\<^sub>0 r"
  shows "A (fst p) + Bfun (snd p) - Pn (fst p - snd p)
      \<le> A (fst \<xi>\<^sub>0) + Bfun (snd \<xi>\<^sub>0) - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
proof -
  have "dist (snd p) (snd \<xi>\<^sub>0) \<le> dist p \<xi>\<^sub>0" by (rule dist_snd_le)
  also have "\<dots> \<le> r" using p by (simp add: dist_commute)
  finally have "snd p \<in> cball (snd \<xi>\<^sub>0) r" by (simp add: dist_commute)
  then have "snd p \<in> K'" using ball by blast
  from mx[OF this] show ?thesis .
qed
text \<open>The other half of the two-domain interface: the core reads the
  subsolution property at the attainment point of \<open>supconv(\<theta>u)\<epsilon>\<close> over the
  \<open>\<rho>\<close>-ball around \<open>x\<^sup>h\<close>, and Definition 3.1's gate puts that point in
  \<open>{u>0}\<close> whenever the sup-convolution is positive there, since the
  attained value adds a nonnegative penalty.  Positivity on the whole
  ball, not just at \<open>x\<^sup>h\<close>, is free since \<open>\<rho>\<close> is a free parameter
  preserved by shrinking.\<close>

lemma cont_pos_near:
  fixes A :: "real^'n::finite \<Rightarrow> real"
  assumes cA: "continuous_on UNIV A" and pos: "0 < A p"
  obtains \<rho> where "0 < \<rho>" and "\<And>x. dist x p \<le> \<rho> \<Longrightarrow> 0 < A x"
proof -
  have ic: "isCont A p"
    using cA by (simp add: continuous_on_eq_continuous_at)
  obtain d where d0: "0 < d"
    and h: "\<And>x. dist x p < d \<Longrightarrow> dist (A x) (A p) < A p"
    using ic[unfolded continuous_at_eps_delta] pos by blast
  show ?thesis
  proof (rule that[of "d/2"])
    show "0 < d/2" using d0 by simp
    fix x assume "dist x p \<le> d/2"
    then have "dist x p < d" using d0 by linarith
    from h[OF this] have "\<bar>A x - A p\<bar> < A p" by (simp add: dist_real_def)
    then show "0 < A x" by linarith
  qed
qed

lemma attain_gate_of_positive:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes t0: "0 < \<theta>" and e: "0 < \<epsilon>"
    and pos: "0 < supconv (\<lambda>y. \<theta> * u y) \<epsilon> x"
    and opt: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)"
  shows "0 < u z"
proof -
  have s0: "0 < \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)" using pos unfolding opt .
  have "0 \<le> (dist x z)\<^sup>2 / (2*\<epsilon>)" using e by simp
  with s0 have "0 < \<theta> * u z" by linarith
  then show ?thesis using t0 by (simp add: zero_less_mult_iff)
qed

text \<open>On a \<open>\<rho>\<close>-ball where the sup-convolution stays positive, every attainment
  point lies in the gated set - the core's \<open>atu\<close> hypothesis.\<close>

lemma atu_of_positive_ball:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes t0: "0 < \<theta>" and e: "0 < \<epsilon>"
    and posb: "\<And>x. dist x p \<le> \<rho> \<Longrightarrow> 0 < supconv (\<lambda>y. \<theta> * u y) \<epsilon> x"
    and dx: "dist x p \<le> \<rho>"
    and opt: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)"
  shows "z \<in> {q. 0 < u q}"
  using attain_gate_of_positive[OF t0 e posb[OF dx] opt] by simp

lemma supconv_le_of_local_bound:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and e: "0 < \<epsilon>"
    and cu: "continuous_on UNIV u"
    and R: "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < R"
    and loc: "\<And>y. dist x y \<le> R \<Longrightarrow> u y \<le> M"
  shows "supconv u \<epsilon> x \<le> M"
proof -
  obtain ys where d: "dist x ys \<le> R"
    and v: "supconv u \<epsilon> x = u ys - (dist x ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_ball_rad[OF B e cu R] by blast
  have nn: "0 \<le> (dist x ys)\<^sup>2 / (2*\<epsilon>)" using e by simp
  have "supconv u \<epsilon> x \<le> u ys" unfolding v using nn by linarith
  also have "u ys \<le> M" by (rule loc[OF d])
  finally show ?thesis .
qed

lemma supconv_radius_uniform:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes lo: "\<And>y. Bl \<le> u y" and e: "0 < \<epsilon>" and h: "0 < \<eta>"
    and small: "2*\<epsilon>*(Bu - Bl) < \<eta>\<^sup>2"
  shows "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < \<eta>"
proof -
  have mono: "2*\<epsilon>*(Bu - u x) \<le> 2*\<epsilon>*(Bu - Bl)"
    by (rule mult_left_mono) (use lo[of x] e in linarith)+
  have hpos: "0 < \<eta>\<^sup>2" using h by simp
  have mx: "max 0 (2*\<epsilon>*(Bu - u x)) < \<eta>\<^sup>2"
  proof (cases "0 \<le> 2*\<epsilon>*(Bu - u x)")
    case True
    then have "max 0 (2*\<epsilon>*(Bu - u x)) = 2*\<epsilon>*(Bu - u x)" by simp
    then show ?thesis using mono small by linarith
  next
    case False
    then have "max 0 (2*\<epsilon>*(Bu - u x)) = 0" by simp
    then show ?thesis using hpos by linarith
  qed
  have "sqrt (max 0 (2*\<epsilon>*(Bu - u x))) < sqrt (\<eta>\<^sup>2)"
    by (rule real_sqrt_less_mono[OF mx])
  moreover have "sqrt (\<eta>\<^sup>2) = \<eta>" using h by simp
  ultimately show ?thesis by simp
qed

theorem supconv_sandwich:
  fixes u :: "'a::euclidean_space \<Rightarrow> real"
  assumes B: "\<And>y. u y \<le> Bu" and lo: "\<And>y. Bl \<le> u y"
    and e: "0 < \<epsilon>" and cu: "continuous_on UNIV u"
    and h: "0 < \<eta>" and small: "2*\<epsilon>*(Bu - Bl) < \<eta>\<^sup>2"
    and loc: "\<And>y. dist x y \<le> \<eta> \<Longrightarrow> u y \<le> u x + \<sigma>"
  shows "u x \<le> supconv u \<epsilon> x"
    and "supconv u \<epsilon> x \<le> u x + \<sigma>"
proof -
  show "u x \<le> supconv u \<epsilon> x" by (rule supconv_ge[OF B e])
  show "supconv u \<epsilon> x \<le> u x + \<sigma>"
    by (rule supconv_le_of_local_bound
        [where Bu = Bu and R = \<eta> and M = "u x + \<sigma>",
         OF B e cu supconv_radius_uniform[OF lo e h small] loc])
qed

subsection \<open>Locating the doubling maximiser away from the boundary\<close>

text \<open>This step makes \<open>interior K\<close>, not \<open>K\<close>, the domain where the viscosity
  properties are used.  The needed geometric data at the doubling
  maximiser \<open>(x̂,ŷ)\<close> - \<open>cball \<xi>\<^sub>0 r \<subseteq> K \<times> K\<close> and
  \<open>cball x R\<^sub>u \<subseteq> interior K\<close> - follows by
  \<open>cball_subset_interior_of_far_from_boundary\<close> from \<open>x̂\<close> and \<open>ŷ\<close> lying more
  than \<open>\<kappa>\<close> from \<open>K - interior K\<close>, which the interior/boundary gap of
  \<open>\<theta>u-w\<close> forces via \<open>m + 2\<sigma> + \<tau> + \<tau>' < M\<close>, each small quantity
  controlled by a free parameter (\<open>\<sigma>\<close> by \<open>\<epsilon>\<close>, \<open>\<tau>\<close> by \<open>\<alpha>\<close>, \<open>\<tau>'\<close> by
  \<open>\<kappa>\<close>).  Stated for abstract \<open>f\<close>, \<open>g\<close> and moduli, so the sup-convolutions
  and \<open>\<theta>\<close>-scaling stay invisible.\<close>

lemma uniform_modulus_on_compact:
  fixes v :: "'a::heine_borel \<Rightarrow> real"
  assumes cC: "compact C" and cv: "continuous_on C v" and s: "0 < \<sigma>"
  shows "\<exists>\<eta>>0. \<forall>p\<in>C. \<forall>q\<in>C. dist p q \<le> \<eta> \<longrightarrow> v q \<le> v p + \<sigma>"
proof -
  have uc: "uniformly_continuous_on C v"
    by (rule compact_uniformly_continuous[OF cv cC])
  obtain d where d0: "0 < d"
    and dd: "\<And>x x'. x \<in> C \<Longrightarrow> x' \<in> C \<Longrightarrow> dist x' x < d \<Longrightarrow> dist (v x') (v x) < \<sigma>"
    by (rule uniformly_continuous_onE[OF uc s]) blast
  have main: "\<forall>p\<in>C. \<forall>q\<in>C. dist p q \<le> d/2 \<longrightarrow> v q \<le> v p + \<sigma>"
  proof (intro ballI impI)
    fix p q assume p: "p \<in> C" and q: "q \<in> C" and dpq: "dist p q \<le> d/2"
    have "dist q p < d" using dpq d0 by (simp add: dist_commute)
    then have "dist (v q) (v p) < \<sigma>" by (rule dd[OF p q])
    then show "v q \<le> v p + \<sigma>" by (simp add: dist_real_def)
  qed
  have "0 < d/2" using d0 by simp
  then show ?thesis using main by blast
qed

theorem doubling_maximiser_far_from_boundary:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes xK: "xh \<in> K" and yK: "yh \<in> K"
    and val: "M \<le> f z + g z"
    and tr: "f z + g z \<le> f xh + g yh + 2*\<sigma>"
    and near: "dist xh yh \<le> \<beta>"
    and modg: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<beta> \<Longrightarrow> g q \<le> g p + \<tau>"
    and bdry: "\<And>c. c \<in> K - interior K \<Longrightarrow> f c + g c \<le> m"
    and modF: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<kappa>
        \<Longrightarrow> f p + g p \<le> f q + g q + \<tau>'"
    and gap: "m + 2*\<sigma> + \<tau> + \<tau>' < M"
    and b: "b \<in> K - interior K"
  shows "\<kappa> < dist xh b"
proof (rule ccontr)
  assume "\<not> \<kappa> < dist xh b"
  then have d: "dist xh b \<le> \<kappa>" by linarith
  have bK: "b \<in> K" using b by simp
  have g1: "g yh \<le> g xh + \<tau>" by (rule modg[OF xK yK near])
  have s1: "M \<le> f xh + g yh + 2*\<sigma>" using val tr by linarith
  have s2: "M \<le> f xh + g xh + \<tau> + 2*\<sigma>" using s1 g1 by linarith
  have s3: "f xh + g xh \<le> f b + g b + \<tau>'" by (rule modF[OF xK bK d])
  have s4: "f b + g b \<le> m" by (rule bdry[OF b])
  from s2 s3 s4 gap show False by linarith
qed

subsection \<open>The two penalty-carrying localisation helpers, generalised\<close>

text \<open>Of the eleven lemmas in the localisation layer, only two mention the
  penalty, and neither uses anything quadratic about it:
  \<open>doubling_maximiser_value_transfer\<close> uses only \<open>Pn 0 = 0\<close>, and
  \<open>norm_lt_of_penalty_bound\<close> uses only coercivity, phrased as "the
  penalty exceeds \<open>C\<close> outside radius \<open>\<beta>\<close>".
  \<open>doubling_maximiser_far_from_boundary\<close> itself is penalty-free,
  consuming the penalty only through the abstracted \<open>tr\<close> and \<open>near\<close>.\<close>

lemma doubling_maximiser_value_transfer_gen:
  fixes A Bf f g :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + Bf y - Pn (x - y) \<le> A xh + Bf yh - Pn (xh - yh)"
    and zK: "z \<in> K"
    and P0: "Pn 0 = 0"
    and lowA: "f z \<le> A z" and lowB: "g z \<le> Bf z"
    and upA: "A xh \<le> f xh + \<sigma>" and upB: "Bf yh \<le> g yh + \<sigma>"
  shows "f z + g z + Pn (xh - yh) \<le> f xh + g yh + 2*\<sigma>"
proof -
  have diag: "A z + Bf z - Pn (z - z) \<le> A xh + Bf yh - Pn (xh - yh)"
    by (rule mx[OF zK zK])
  have zz: "z - z = (0 :: real^'n)" by simp
  have "A z + Bf z \<le> A xh + Bf yh - Pn (xh - yh)"
    using diag unfolding zz P0 by simp
  then show ?thesis using lowA lowB upA upB by linarith
qed

lemma norm_lt_of_penalty_bound_gen:
  fixes d :: "'a::real_normed_vector" and Pn :: "'a \<Rightarrow> real" and C \<beta> :: real
  assumes p: "Pn d \<le> C"
    and coer: "\<And>x. \<beta> \<le> norm x \<Longrightarrow> C < Pn x"
  shows "norm d < \<beta>"
proof (rule ccontr)
  assume "\<not> norm d < \<beta>"
  then have "\<beta> \<le> norm d" by linarith
  then have "C < Pn d" by (rule coer)
  then show False using p by argo
qed

subsection \<open>\<open>soft_pen\<close> vanishes on the diagonal and is coercive\<close>

text \<open>Both facts reduce to the radial profile
  \<open>h s = \<kappa>(s/2-(sqrt(s+1)-1))\<close> at \<open>s = norm d\<^sup>2\<close>: \<open>h 0 = 0\<close> is immediate,
  and monotonicity follows the difference-of-squares trick of
  \<open>soft_R_lipschitz\<close>.\<close>

lemma soft_pen_zero: "soft_pen \<kappa> (0 :: real^'n::finite) = 0"
  unfolding soft_pen_def by simp

lemma sqrt_shift_diff_bound:
  fixes s t :: real
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "2 * (sqrt (t + 1) - sqrt (s + 1)) \<le> t - s"
proof -
  have tnn: "0 \<le> t" using s st by linarith
  have a1: "1 \<le> sqrt (t + 1)"
  proof -
    have "(1::real) = sqrt 1" by simp
    also have "sqrt (1::real) \<le> sqrt (t + 1)" by (rule real_sqrt_le_mono) (use tnn in linarith)
    finally show ?thesis .
  qed
  have b1: "1 \<le> sqrt (s + 1)"
  proof -
    have "(1::real) = sqrt 1" by simp
    also have "sqrt (1::real) \<le> sqrt (s + 1)" by (rule real_sqrt_le_mono) (use s in linarith)
    finally show ?thesis .
  qed
  have ab: "sqrt (s + 1) \<le> sqrt (t + 1)" by (rule real_sqrt_le_mono) (use st in linarith)
  have sq: "sqrt (t + 1) * sqrt (t + 1) - sqrt (s + 1) * sqrt (s + 1) = t - s"
  proof -
    have et: "sqrt (t + 1) * sqrt (t + 1) = t + 1"
      using real_sqrt_pow2[of "t + 1"] tnn by (simp add: power2_eq_square)
    have es: "sqrt (s + 1) * sqrt (s + 1) = s + 1"
      using real_sqrt_pow2[of "s + 1"] s by (simp add: power2_eq_square)
    show ?thesis unfolding et es by simp
  qed
  have fact: "(sqrt (t + 1) - sqrt (s + 1)) * (sqrt (t + 1) + sqrt (s + 1))
      = t - s"
  proof -
    have "(sqrt (t + 1) - sqrt (s + 1)) * (sqrt (t + 1) + sqrt (s + 1))
        = sqrt (t + 1) * sqrt (t + 1) - sqrt (s + 1) * sqrt (s + 1)"
      by (simp add: algebra_simps)
    also have "\<dots> = t - s" by (rule sq)
    finally show ?thesis .
  qed
  have dnn: "0 \<le> sqrt (t + 1) - sqrt (s + 1)" using ab by linarith
  have sum2: "2 \<le> sqrt (t + 1) + sqrt (s + 1)" using a1 b1 by linarith
  have "(sqrt (t + 1) - sqrt (s + 1)) * 2
      \<le> (sqrt (t + 1) - sqrt (s + 1)) * (sqrt (t + 1) + sqrt (s + 1))"
    by (rule mult_left_mono[OF sum2 dnn])
  then show ?thesis unfolding fact by (simp add: mult_ac)
qed

text \<open>The bound variables are \<open>a\<close> and \<open>b\<close>, not \<open>s\<close> and \<open>t\<close>: with a variable
  named \<open>s\<close>, \<open>(\<kappa>/2)*s\<close> lexes as the Cartesian scalar-vector product
  token and fails to type-check.\<close>

lemma soft_pen_radial_mono:
  fixes a b :: real
  assumes k: "0 \<le> \<kappa>" and a0: "0 \<le> a" and ab: "a \<le> b"
  shows "(\<kappa>/2) * a - \<kappa> * (sqrt (a + 1) - 1)
      \<le> (\<kappa>/2) * b - \<kappa> * (sqrt (b + 1) - 1)"
proof -
  have base: "2 * (sqrt (b + 1) - sqrt (a + 1)) \<le> b - a"
    by (rule sqrt_shift_diff_bound[OF a0 ab])
  have scaled: "\<kappa> * (2 * (sqrt (b + 1) - sqrt (a + 1))) \<le> \<kappa> * (b - a)"
    by (rule mult_left_mono[OF base k])
  have l: "\<kappa> * (2 * (sqrt (b + 1) - sqrt (a + 1)))
      = 2 * (\<kappa> * (sqrt (b + 1) - sqrt (a + 1)))" by (simp add: mult_ac)
  have rr: "\<kappa> * (b - a) = 2 * ((\<kappa>/2) * (b - a))" by simp
  have half: "\<kappa> * (sqrt (b + 1) - sqrt (a + 1)) \<le> (\<kappa>/2) * (b - a)"
    using scaled unfolding l rr by linarith
  have e1: "\<kappa> * (sqrt (b + 1) - sqrt (a + 1))
      = \<kappa> * (sqrt (b + 1) - 1) - \<kappa> * (sqrt (a + 1) - 1)"
    by (simp add: algebra_simps)
  have e2: "(\<kappa>/2) * (b - a) = (\<kappa>/2) * b - (\<kappa>/2) * a"
    by (rule right_diff_distrib)
  show ?thesis using half unfolding e1 e2 by linarith
qed

lemma soft_pen_mono_norm:
  fixes x y :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>" and le: "norm x \<le> norm y"
  shows "soft_pen \<kappa> x \<le> soft_pen \<kappa> y"
proof -
  have s: "0 \<le> (norm x)\<^sup>2" by simp
  have st: "(norm x)\<^sup>2 \<le> (norm y)\<^sup>2" by (rule power_mono[OF le]) simp
  show ?thesis
    unfolding soft_pen_def by (rule soft_pen_radial_mono[OF k s st])
qed

lemma soft_pen_nonneg:
  fixes d :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>"
  shows "0 \<le> soft_pen \<kappa> d"
proof -
  have "norm (0 :: real^'n) \<le> norm d" by simp
  then have "soft_pen \<kappa> (0 :: real^'n) \<le> soft_pen \<kappa> d"
    by (rule soft_pen_mono_norm[OF k])
  then show ?thesis unfolding soft_pen_zero .
qed

lemma soft_pen_little_o:
  "((\<lambda>h::real^'n::finite. soft_pen \<kappa> h / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  using soft_pen_vanishing_jet_at_zero[where \<kappa> = \<kappa>]
  unfolding soft_pen_zero by simp

text \<open>A diagonal maximiser's increment bound is exactly the one-sided
  hypothesis \<open>supersol_no_vanishing_jet_onesided\<close> consumes.\<close>

lemma diagonal_increment_onesided:
  fixes B :: "real^'n::finite \<Rightarrow> real"
  assumes dom: "\<forall>\<^sub>F hh in at 0. B (p + hh) - B p \<le> soft_pen \<kappa> hh"
    and c: "0 < c"
  shows "\<forall>\<^sub>F hh in at 0. (B (p + hh) - B p) / (norm hh)\<^sup>2 < c"
  by (rule onesided_of_dominated[OF dom soft_pen_little_o c])

lemma soft_pen_neg:
  fixes d :: "real^'n::finite"
  shows "soft_pen \<kappa> (- d) = soft_pen \<kappa> d"
  unfolding soft_pen_def by simp

text \<open>A diagonal maximiser bounds the increment of each component above by
  the penalty only; the maximiser inequality is one-sided and says
  nothing below.\<close>

lemma diagonal_max_increments:
  fixes A B :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + B y - Pn (x - y) \<le> A p + B p - Pn (p - p)"
    and P0: "Pn 0 = 0"
    and pK: "p \<in> K"
  shows "\<And>y. y \<in> K \<Longrightarrow> B y - B p \<le> Pn (p - y)"
    and "\<And>x. x \<in> K \<Longrightarrow> A x - A p \<le> Pn (x - p)"
proof -
  have e: "p - p = (0 :: real^'n)" by simp
  show "B y - B p \<le> Pn (p - y)" if y: "y \<in> K" for y
  proof -
    have "A p + B y - Pn (p - y) \<le> A p + B p - Pn 0"
      using mx[OF pK y] unfolding e .
    then show ?thesis unfolding P0 by simp
  qed
  show "A x - A p \<le> Pn (x - p)" if x: "x \<in> K" for x
  proof -
    have "A x + B p - Pn (x - p) \<le> A p + B p - Pn 0"
      using mx[OF x pK] unfolding e .
    then show ?thesis unfolding P0 by simp
  qed
qed

lemma diagonal_max_increment_soft:
  fixes A B :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + B y - soft_pen \<kappa> (x - y) \<le> A p + B p - soft_pen \<kappa> (p - p)"
    and pK: "p \<in> K" and hK: "p + h \<in> K"
  shows "B (p + h) - B p \<le> soft_pen \<kappa> h"
proof -
  have base: "B (p + h) - B p \<le> soft_pen \<kappa> (p - (p + h))"
    by (rule diagonal_max_increments(1)[OF mx soft_pen_zero pK hK])
  have e: "p - (p + h) = - h" by simp
  have "B (p + h) - B p \<le> soft_pen \<kappa> (- h)" using base unfolding e .
  then show ?thesis unfolding soft_pen_neg .
qed

lemma gap_split_aux:
  fixes G :: real
  assumes G: "0 < G"
  shows "\<exists>\<sigma> \<tau> \<tau>'. 0 < \<sigma> \<and> 0 < \<tau> \<and> 0 < \<tau>' \<and> 2*\<sigma> + \<tau> + \<tau>' < G"
proof -
  have p: "0 < G/8" using G by simp
  have e: "G = 8*(G/8)" by simp
  have "2*(G/8) + (G/8) + (G/8) < G" using p e by linarith
  with p show ?thesis by blast
qed

subsection \<open>Coercivity of \<open>soft_pen\<close>: recovering the norm bound\<close>

text \<open>The quadratic penalty bounds \<open>norm(x̂-ŷ)\<close> by dividing
  \<open>(\<alpha>/2)\<parallel>d\<parallel>\<^sup>2 \<le> C\<^sub>0\<close> through by \<open>\<alpha>\<close>; for a general penalty this needs
  coercivity instead (\<open>norm_lt_of_penalty_bound_gen\<close>).  \<open>soft_pen\<close> is
  linear in \<open>\<kappa>\<close>, so at fixed radius \<open>\<beta>\<close> its value eventually beats any
  fixed \<open>C\<^sub>0\<close> as \<open>\<kappa> \<rightarrow> \<infinity>\<close>, parallel to the \<open>\<alpha> \<rightarrow> \<infinity>\<close> mechanism for
  the quadratic case.\<close>

lemma sqrt_lt_half_plus_one:
  fixes c :: real
  assumes c: "0 < c"
  shows "sqrt (2*c + 1) < c + 1"
proof -
  have p: "0 < c + 1" using c by linarith
  have sq: "2*c + 1 < (c + 1)\<^sup>2"
  proof -
    have e: "(c + 1)\<^sup>2 = c\<^sup>2 + 2*c + 1"
      by (simp add: power2_eq_square algebra_simps)
    have "0 < c\<^sup>2" using c by simp
    then show ?thesis unfolding e by linarith
  qed
  have "sqrt (2*c + 1) < sqrt ((c + 1)\<^sup>2)" by (rule real_sqrt_less_mono[OF sq])
  also have "sqrt ((c + 1)\<^sup>2) = c + 1" using p by simp
  finally show ?thesis .
qed

lemma radial_profile_pos:
  fixes a :: real
  assumes k: "0 < \<kappa>" and a: "0 < a"
  shows "0 < (\<kappa>/2) * a - \<kappa> * (sqrt (a + 1) - 1)"
proof -
  define c where "c = a/2"
  have cpos: "0 < c" unfolding c_def using a by simp
  have ac: "a = 2*c" unfolding c_def by simp
  have lt: "sqrt (2*c + 1) < c + 1" by (rule sqrt_lt_half_plus_one[OF cpos])
  have gap: "0 < (c + 1) - sqrt (2*c + 1)" using lt by linarith
  have h1: "(\<kappa>/2) * (2*c) = \<kappa> * c" by simp
  have e: "(\<kappa>/2) * a - \<kappa> * (sqrt (a + 1) - 1)
      = \<kappa> * ((c + 1) - sqrt (2*c + 1))"
    unfolding ac h1 by (simp add: algebra_simps)
  show ?thesis unfolding e by (rule mult_pos_pos[OF k gap])
qed

lemma soft_pen_ge_radial:
  fixes x :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>" and bnn: "0 \<le> \<beta>" and b: "\<beta> \<le> norm x"
  shows "(\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1) \<le> soft_pen \<kappa> x"
proof -
  have a0: "0 \<le> \<beta>\<^sup>2" by simp
  have ab: "\<beta>\<^sup>2 \<le> (norm x)\<^sup>2" by (rule power_mono[OF b bnn])
  show ?thesis
    unfolding soft_pen_def by (rule soft_pen_radial_mono[OF k a0 ab])
qed

text \<open>The packaged coercivity, in the shape \<open>norm_lt_of_penalty_bound_gen\<close>
  consumes: hypothesis \<open>big\<close> says \<open>\<kappa>\<close> is large enough that the penalty at
  radius \<open>\<beta>\<close> exceeds \<open>C\<^sub>0\<close>, and such \<open>\<kappa>\<close> always exists since the radial
  profile is strictly positive and linear in \<open>\<kappa>\<close> (\<open>soft_pen_kappa_exists\<close>).\<close>

lemma soft_pen_coercive_outside:
  fixes x :: "real^'n::finite"
  assumes k: "0 \<le> \<kappa>" and bnn: "0 \<le> \<beta>"
    and big: "C\<^sub>0 < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    and b: "\<beta> \<le> norm x"
  shows "C\<^sub>0 < soft_pen \<kappa> x"
  using big soft_pen_ge_radial[OF k bnn b] by linarith

lemma soft_pen_kappa_exists:
  fixes \<beta> C\<^sub>0 :: real
  assumes b: "0 < \<beta>"
  shows "\<exists>\<kappa>. 0 < \<kappa> \<and> C\<^sub>0 < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
proof -
  define P where "P = (1/2) * \<beta>\<^sup>2 - 1 * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
  have bsq: "0 < \<beta>\<^sup>2" using b by simp
  have Ppos: "0 < P" unfolding P_def by (rule radial_profile_pos[OF _ bsq]) simp
  have Pne: "P \<noteq> 0" using Ppos by linarith
  \<comment> \<open>generic in the scalar, so simp never sees the quotient defining it\<close>
  have scale: "kk * P = (kk/2) * \<beta>\<^sup>2 - kk * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    for kk :: real
    unfolding P_def by (simp add: algebra_simps)
  define \<kappa> where "\<kappa> = (max 0 C\<^sub>0 + 1) / P"
  have numpos: "0 < max 0 C\<^sub>0 + 1" by simp
  have kpos: "0 < \<kappa>" unfolding \<kappa>_def by (rule divide_pos_pos[OF numpos Ppos])
  have prod: "\<kappa> * P = max 0 C\<^sub>0 + 1" unfolding \<kappa>_def using Pne by simp
  have "C\<^sub>0 < max 0 C\<^sub>0 + 1" by simp
  then have lt: "C\<^sub>0 < \<kappa> * P" using prod by linarith
  have final: "C\<^sub>0 < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    using lt unfolding scale[of \<kappa>] .
  from kpos final show ?thesis by blast
qed
text \<open>The \<open>y\<close>-side of the two-domain interface: at the maximiser the penalty
  is bounded by the range, so a large enough \<open>\<kappa>\<^sub>P\<close> pins \<open>y^h\<close> to \<open>x^h\<close>;
  \<open>x^h\<close> is near \<open>K\<close>, and \<open>two_domain_gap\<close> keeps \<open>K\<close> a positive distance
  from \<open>\<partial>K'\<close>.  Composing the three gives the \<open>fary\<close> hypothesis, needed
  only on the \<open>y\<close>-side.\<close>

lemma pin_of_penalty_bound:
  fixes A Bfun :: "real^'n::finite \<Rightarrow> real" and xh yh :: "real^'n"
  assumes k: "0 \<le> \<kappa>\<^sub>P" and bnn: "0 \<le> \<beta>"
    and Aub: "\<And>x. A x \<le> Bu" and Bnp: "\<And>y. Bfun y \<le> 0"
    and Mnn: "0 \<le> M"
    and mx: "M \<le> A xh + Bfun yh - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and big: "Bu < (\<kappa>\<^sub>P/2)*\<beta>\<^sup>2 - \<kappa>\<^sub>P*(sqrt (\<beta>\<^sup>2 + 1) - 1)"
  shows "norm (xh - yh) < \<beta>"
proof (rule ccontr)
  assume "\<not> norm (xh - yh) < \<beta>"
  then have b: "\<beta> \<le> norm (xh - yh)" by linarith
  have lo: "Bu < soft_pen \<kappa>\<^sub>P (xh - yh)"
    by (rule soft_pen_coercive_outside[OF k bnn big b])
  have hi: "soft_pen \<kappa>\<^sub>P (xh - yh) \<le> Bu"
    using mx Aub[of xh] Bnp[of yh] Mnn by linarith
  from lo hi show False by linarith
qed

lemma fary_of_pin:
  fixes K K' :: "(real^'n::finite) set" and xh yh q b :: "real^'n"
  assumes gap: "\<And>x c. x \<in> K \<Longrightarrow> c \<in> K' - interior K' \<Longrightarrow> d < dist x c"
    and qK: "q \<in> K" and xQ: "dist xh q \<le> dQ"
    and pin: "norm (xh - yh) < \<beta>"
    and fit: "\<beta> + dQ + \<kappa> \<le> d"
    and bK: "b \<in> K' - interior K'"
  shows "\<kappa> < dist yh b"
proof -
  have g: "d < dist q b" by (rule gap[OF qK bK])
  have t1: "dist q b \<le> dist q yh + dist yh b" by (rule dist_triangle)
  have t2: "dist q yh \<le> dist q xh + dist xh yh" by (rule dist_triangle)
  have e1: "dist xh yh = norm (xh - yh)" by (simp add: dist_norm)
  have e2: "dist q xh = dist xh q" by (rule dist_commute)
  have "dist q yh < dQ + \<beta>" using t2 pin xQ unfolding e1 e2 by linarith
  then show ?thesis using g t1 fit by linarith
qed

text \<open>Continuity of \<open>soft_pen\<close> is the single hypothesis
  \<open>doubling_maximiser_exists_gen\<close> needs about the penalty.  \<open>sqrt\<close> is
  total in Isabelle, so no positivity side condition is needed.\<close>

lemma soft_pen_continuous:
  "continuous_on UNIV (soft_pen \<kappa> :: real^'n::finite \<Rightarrow> real)"
  unfolding soft_pen_def by (intro continuous_intros)

theorem doubling_maximiser_exists_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      u x - w y - soft_pen \<kappa> (x - y)
        \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)"
  by (rule doubling_maximiser_exists_gen[OF cK neK cu cw soft_pen_continuous])

text \<open>The sup-convolution form matches the \<open>mxKK\<close> hypothesis of
  \<open>comparison_from_localised_maximiser_soft\<close>, a transcription of
  \<open>doubling_maximiser_supconv\<close> with continuity of the two sup-convolutions
  free from \<open>supconv_continuous\<close>.\<close>

corollary doubling_maximiser_supconv_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
  shows "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa> (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - soft_pen \<kappa> (xh - yh)"
proof -
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu e] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw e] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  have "\<exists>xh\<in>K. \<exists>yh\<in>K. \<forall>x\<in>K. \<forall>y\<in>K.
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y) - soft_pen \<kappa> (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh - (- supconv (- w) \<epsilon> yh)
        - soft_pen \<kappa> (xh - yh)"
    by (rule doubling_maximiser_exists_soft[OF cK neK cA cB])
  then show ?thesis by simp
qed

subsection \<open>The \<open>\<kappa> \<rightarrow> \<infinity>\<close> step for \<open>soft_pen\<close>: the maximiser closes up\<close>

text \<open>The \<open>soft_pen\<close> analogue of \<open>doubling_dist_bound\<close>: the penalty at radius
  \<open>\<beta>\<close> grows linearly in \<open>\<kappa>\<close> and eventually exceeds the fixed \<open>C\<^sub>0\<close>,
  forcing the maximiser inside radius \<open>\<beta>\<close>.  The quantifier order matters:
  \<open>\<beta>\<close> is given first, \<open>\<kappa>\<close> chosen afterwards, so the statement produces
  \<open>\<kappa>\<close> and the maximiser together.\<close>

lemma doubling_near_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes mx: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        u x - w y - soft_pen \<kappa> (x - y)
          \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)"
    and k: "0 \<le> \<kappa>"
    and xh: "xh \<in> K" and yh: "yh \<in> K" and z: "z \<in> K"
    and bnd: "u xh - w yh \<le> C"
    and bnn: "0 \<le> \<beta>"
    and big: "C - (u z - w z) < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
  shows "dist xh yh < \<beta>"
proof -
  have pb: "soft_pen \<kappa> (xh - yh) \<le> C - (u z - w z)"
    by (rule doubling_penalty_bound_gen[OF mx soft_pen_zero xh yh z bnd])
  have coer: "C - (u z - w z) < soft_pen \<kappa> x" if "\<beta> \<le> norm x"
    for x :: "real^'n"
    by (rule soft_pen_coercive_outside[OF k bnn big that])
  \<comment> \<open>pin every argument: \<open>?Pn ?d\<close> is higher-order and admits several unifiers\<close>
  have "norm (xh - yh) < \<beta>"
    by (rule norm_lt_of_penalty_bound_gen
        [where Pn = "soft_pen \<kappa>" and d = "xh - yh"
           and C = "C - (u z - w z)" and \<beta> = \<beta>,
         OF pb coer])
  then show ?thesis by (simp add: dist_norm)
qed

theorem doubling_close_maximiser_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and z: "z \<in> K"
    and bnd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> u x - w y \<le> C"
    and bpos: "0 < \<beta>"
  shows "\<exists>\<kappa>. 0 < \<kappa> \<and> (\<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K. u x - w y - soft_pen \<kappa> (x - y)
          \<le> u xh - w yh - soft_pen \<kappa> (xh - yh))
      \<and> dist xh yh < \<beta>)"
proof -
  obtain \<kappa> where kpos: "0 < \<kappa>"
    and big: "C - (u z - w z)
        < (\<kappa>/2) * \<beta>\<^sup>2 - \<kappa> * (sqrt (\<beta>\<^sup>2 + 1) - 1)"
    using soft_pen_kappa_exists[OF bpos] by blast
  have knn: "0 \<le> \<kappa>" using kpos by linarith
  have bnn: "0 \<le> \<beta>" using bpos by linarith
  obtain xh yh where xh: "xh \<in> K" and yh: "yh \<in> K"
    and mx: "\<forall>x\<in>K. \<forall>y\<in>K. u x - w y - soft_pen \<kappa> (x - y)
        \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)"
    using doubling_maximiser_exists_soft[OF cK neK cu cw, where \<kappa> = \<kappa>] by blast
  have mxa: "u x - w y - soft_pen \<kappa> (x - y)
      \<le> u xh - w yh - soft_pen \<kappa> (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mx that by blast
  have near: "dist xh yh < \<beta>"
    by (rule doubling_near_soft
        [OF mxa knn xh yh z bnd[OF xh yh] bnn big])
  show ?thesis using kpos xh yh mx near by blast
qed

text \<open>The \<open>\<kappa> \<rightarrow> \<infinity>\<close> step in the sup-convolution shape the assembly consumes,
  with the same sign flip as \<open>doubling_maximiser_supconv_soft\<close>:
  instantiate at \<open>u := supconv(\<theta>u)\<epsilon>\<close> and \<open>w := \<lambda>y. -supconv(-w)\<epsilon> y\<close>.\<close>

theorem doubling_close_maximiser_supconv_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and e: "0 < \<epsilon>"
    and z: "z \<in> K"
    and bnd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y \<le> C"
    and bpos: "0 < \<beta>"
  shows "\<exists>\<kappa>. 0 < \<kappa> \<and> (\<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K.
         supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa> (x - y)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
           - soft_pen \<kappa> (xh - yh))
      \<and> dist xh yh < \<beta>)"
proof -
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu e] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw e] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  have bnd': "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y) \<le> C"
    if "x \<in> K" "y \<in> K" for x y
    using bnd[OF that] by simp
  have "\<exists>\<kappa>. 0 < \<kappa> \<and> (\<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K.
         supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (- supconv (- w) \<epsilon> y) - soft_pen \<kappa> (x - y)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh - (- supconv (- w) \<epsilon> yh)
           - soft_pen \<kappa> (xh - yh))
      \<and> dist xh yh < \<beta>)"
    by (rule doubling_close_maximiser_soft
        [where u = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>"
           and w = "\<lambda>y. - supconv (- w) \<epsilon> y" and K = K and z = z and C = C
           and \<beta> = \<beta>,
         OF cK neK cA cB z bnd' bpos])
  then show ?thesis by simp
qed

subsection \<open>The \<open>\<epsilon> \<rightarrow> 0\<close> step: the sup-convolution is uniformly close on \<open>K\<close>\<close>

text \<open>\<open>supconv_sandwich\<close> needs a local modulus valid on a ball sticking out
  of \<open>K\<close>, but the doubling maximiser's location is unknown, so the bound
  must be uniform over \<open>K\<close>.  The fix runs \<open>uniform_modulus_on_compact\<close>
  on \<open>cball 0 R\<close> containing the 1-neighbourhood of \<open>K\<close>, capping the
  modulus radius at 1 - which relies on the earlier reduction to
  globally continuous, globally bounded data.\<close>

lemma exists_eps_aux:
  fixes H D :: real
  assumes H: "0 < H" and D: "0 \<le> D"
  shows "\<exists>\<epsilon>. 0 < \<epsilon> \<and> 2*\<epsilon>*D < H"
proof -
  have dp: "0 < 2*(D+1)" using D by simp
  define e where "e = H/(2*(D+1))"
  have epos: "0 < e" unfolding e_def by (rule divide_pos_pos[OF H dp])
  have ne: "2*(D+1) \<noteq> 0" using dp by linarith
  have key: "2*e*(D+1) = H"
  proof -
    have "2*e*(D+1) = (H/(2*(D+1))) * (2*(D+1))"
      unfolding e_def by (simp add: mult_ac)
    also have "\<dots> = H" using ne by simp
    finally show ?thesis .
  qed
  have expd: "2*e*(D+1) = 2*e*D + 2*e" by (simp add: algebra_simps)
  have "2*e*D < H" using key expd epos by linarith
  with epos show ?thesis by blast
qed

lemma eps_mono_aux:
  fixes \<epsilon> \<epsilon>\<^sub>0 D H :: real
  assumes ep: "0 < \<epsilon>" and le: "\<epsilon> \<le> \<epsilon>\<^sub>0"
    and lt: "2*\<epsilon>\<^sub>0*(max 0 D) < H"
  shows "2*\<epsilon>*D < H"
proof -
  have Dnn: "0 \<le> max 0 D" by simp
  have dle: "D \<le> max 0 D" by simp
  have e2: "0 \<le> 2*\<epsilon>" using ep by linarith
  have s1: "2*\<epsilon>*D \<le> 2*\<epsilon>*(max 0 D)" by (rule mult_left_mono[OF dle e2])
  have le2: "2*\<epsilon> \<le> 2*\<epsilon>\<^sub>0" using le by linarith
  have s2: "2*\<epsilon>*(max 0 D) \<le> 2*\<epsilon>\<^sub>0*(max 0 D)"
    by (rule mult_right_mono[OF le2 Dnn])
  from s1 s2 lt show ?thesis by linarith
qed

lemma supconv_uniform_upper:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K"
    and B: "\<And>y. u y \<le> Bu" and lo: "\<And>y. Bl \<le> u y"
    and cu: "continuous_on UNIV u"
    and s: "0 < \<sigma>"
  shows "\<exists>\<epsilon>\<^sub>0. 0 < \<epsilon>\<^sub>0 \<and> (\<forall>\<epsilon>. 0 < \<epsilon> \<longrightarrow> \<epsilon> \<le> \<epsilon>\<^sub>0
      \<longrightarrow> (\<forall>x\<in>K. supconv u \<epsilon> x \<le> u x + \<sigma>))"
proof -
  have bK: "bounded K" by (rule compact_imp_bounded[OF cK])
  then obtain R\<^sub>0 where R0: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> R\<^sub>0"
    using bounded_iff by blast
  define R where "R = max 0 R\<^sub>0 + 1"
  have R1: "1 \<le> R" unfolding R_def by simp
  have KR: "norm x \<le> R - 1" if "x \<in> K" for x
    using R0[OF that] unfolding R_def by simp
  have cb: "compact (cball (0::real^'n) R)" by (rule compact_cball)
  have cuR: "continuous_on (cball (0::real^'n) R) u"
    by (rule continuous_on_subset[OF cu subset_UNIV])
  obtain \<eta> where hpos: "0 < \<eta>"
    and modu: "\<And>p q. p \<in> cball (0::real^'n) R \<Longrightarrow> q \<in> cball (0::real^'n) R
        \<Longrightarrow> dist p q \<le> \<eta> \<Longrightarrow> u q \<le> u p + \<sigma>"
    using uniform_modulus_on_compact[OF cb cuR s] by blast
  define h where "h = min \<eta> 1"
  have hp: "0 < h" unfolding h_def using hpos by simp
  have hle1: "h \<le> 1" unfolding h_def by simp
  have hlem: "h \<le> \<eta>" unfolding h_def by simp
  have Dnn: "0 \<le> max 0 (Bu - Bl)" by simp
  have hsq: "0 < h\<^sup>2" using hp by simp
  obtain \<epsilon>\<^sub>0 where e0pos: "0 < \<epsilon>\<^sub>0"
    and esm: "2*\<epsilon>\<^sub>0*(max 0 (Bu - Bl)) < h\<^sup>2"
    using exists_eps_aux[OF hsq Dnn] by blast
  \<comment> \<open>the bound survives shrinking \<open>\<epsilon>\<close>, which is what lets the assembly pick ONE
      \<open>\<epsilon>\<close> serving both sup-convolutions\<close>
  have esm2: "2*\<epsilon>*(Bu - Bl) < h\<^sup>2" if ep: "0 < \<epsilon>" and ele: "\<epsilon> \<le> \<epsilon>\<^sub>0" for \<epsilon>
  proof -
    have le: "Bu - Bl \<le> max 0 (Bu - Bl)" by simp
    have e2: "0 \<le> 2*\<epsilon>" using ep by linarith
    have step1: "2*\<epsilon>*(Bu - Bl) \<le> 2*\<epsilon>*(max 0 (Bu - Bl))"
      by (rule mult_left_mono[OF le e2])
    have le2: "2*\<epsilon> \<le> 2*\<epsilon>\<^sub>0" using ele by linarith
    have step2: "2*\<epsilon>*(max 0 (Bu - Bl)) \<le> 2*\<epsilon>\<^sub>0*(max 0 (Bu - Bl))"
      by (rule mult_right_mono[OF le2 Dnn])
    from step1 step2 esm show ?thesis by linarith
  qed
  have main: "supconv u \<epsilon> x \<le> u x + \<sigma>"
    if ep: "0 < \<epsilon>" and ele: "\<epsilon> \<le> \<epsilon>\<^sub>0" and x: "x \<in> K" for \<epsilon> x
  proof -
    have nx: "norm x \<le> R - 1" by (rule KR[OF x])
    have xR: "x \<in> cball (0::real^'n) R"
      using nx R1 by (simp add: dist_norm)
    have loc: "u y \<le> u x + \<sigma>" if d: "dist x y \<le> h" for y
    proof -
      have tri: "dist 0 y \<le> dist 0 x + dist x y" by (rule dist_triangle)
      have d0y: "dist (0::real^'n) y = norm y" by simp
      have d0x: "dist (0::real^'n) x = norm x" by simp
      have "norm y \<le> norm x + h" using tri d hle1 unfolding d0y d0x by linarith
      then have "norm y \<le> R" using nx hle1 by linarith
      then have yR: "y \<in> cball (0::real^'n) R" by (simp add: dist_norm)
      have dh: "dist x y \<le> \<eta>" using d hlem by linarith
      show ?thesis by (rule modu[OF xR yR dh])
    qed
    show ?thesis
      by (rule supconv_sandwich(2)[OF B lo ep cu hp esm2[OF ep ele] loc])
  qed
  show ?thesis using e0pos main by blast
qed

subsection \<open>Threading the parameters: the localised maximiser for \<open>soft_pen\<close>\<close>

text \<open>Threading the five smallness steps, in order (the maximiser depends on
  \<open>\<kappa>\<^sub>P\<close>, which must be fixed before it, and \<open>\<beta>\<close> before \<open>\<kappa>\<^sub>P\<close>):

    \<open>G = M - m > 0\<close>, split as \<open>\<sigma> = \<tau> = \<tau>' = G/8\<close>
    \<open>\<tau>\<close>  fixes \<open>\<beta>\<^sub>0\<close>   (modulus of \<open>g\<close> on \<open>K\<close>)
    \<open>\<tau>'\<close> fixes \<open>\<kappa>\<^sub>0\<close>   (modulus of \<open>f + g\<close> on \<open>K\<close>)
    \<open>\<kappa>\<^sub>g = \<kappa>\<^sub>0/2\<close>, \<open>\<beta> = min \<beta>\<^sub>0 (\<kappa>\<^sub>0/2)\<close>
    \<open>\<sigma>\<close>  fixes \<open>\<epsilon>\<close>, and \<open>\<beta>\<close> fixes \<open>\<kappa>\<^sub>P\<close> and the maximiser

  The bound for \<open>ŷ\<close> comes free from the one for \<open>x̂\<close> via the triangle
  inequality, avoiding a second modulus for \<open>f\<close>.\<close>

theorem doubling_localised_maximiser_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and zK: "z \<in> K"
    and Mval: "M \<le> \<theta> * u z - w z"
    and bdry: "\<And>c. c \<in> K - interior K \<Longrightarrow> \<theta> * u c - w c \<le> m"
    and gapMm: "m < M"
  shows "\<exists>\<epsilon>>0. \<exists>\<kappa>\<^sub>g>0. \<exists>\<kappa>\<^sub>P>0. \<exists>xh\<in>K. \<exists>yh\<in>K.
      (\<forall>x\<in>K. \<forall>y\<in>K.
         supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
           - soft_pen \<kappa>\<^sub>P (xh - yh))
    \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b)
    \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b)
    \<and> 2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2
    \<and> 2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
proof -
  \<comment> \<open>1. split the gap\<close>
  have Gpos: "0 < M - m" using gapMm by linarith
  obtain \<sigma> \<tau> \<tau>' where spos: "0 < \<sigma>" and tpos: "0 < \<tau>" and t'pos: "0 < \<tau>'"
    and gsum: "2*\<sigma> + \<tau> + \<tau>' < M - m"
    using gap_split_aux[OF Gpos] by blast
  \<comment> \<open>2. the modulus of \<open>g = -w\<close>, at scale \<open>\<tau>\<close>\<close>
  have cwK: "continuous_on K (- w)"
    by (rule continuous_on_subset[OF cw subset_UNIV])
  obtain \<beta>\<^sub>0 where b0pos: "0 < \<beta>\<^sub>0"
    and modg0: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<beta>\<^sub>0 \<Longrightarrow> (- w) q \<le> (- w) p + \<tau>"
    using uniform_modulus_on_compact[OF cK cwK tpos] by blast
  \<comment> \<open>3. the modulus of \<open>f + g\<close>, at scale \<open>\<tau>'\<close>\<close>
  have cFK: "continuous_on K (\<lambda>y. \<theta> * u y + (- w) y)"
    by (intro continuous_intros
        continuous_on_subset[OF cu subset_UNIV]
        continuous_on_subset[OF cw subset_UNIV])
  obtain \<kappa>\<^sub>0 where k0pos: "0 < \<kappa>\<^sub>0"
    and modF0: "\<And>p q. p \<in> K \<Longrightarrow> q \<in> K \<Longrightarrow> dist p q \<le> \<kappa>\<^sub>0
        \<Longrightarrow> (\<lambda>y. \<theta> * u y + (- w) y) q \<le> (\<lambda>y. \<theta> * u y + (- w) y) p + \<tau>'"
    using uniform_modulus_on_compact[OF cK cFK t'pos] by blast
  \<comment> \<open>4. the two radii\<close>
  define \<kappa>\<^sub>g where "\<kappa>\<^sub>g = \<kappa>\<^sub>0/2"
  define \<beta> where "\<beta> = min \<beta>\<^sub>0 (\<kappa>\<^sub>0/2)"
  have kgpos: "0 < \<kappa>\<^sub>g" unfolding \<kappa>\<^sub>g_def using k0pos by simp
  have bpos: "0 < \<beta>" unfolding \<beta>_def using b0pos k0pos by simp
  have bleb0: "\<beta> \<le> \<beta>\<^sub>0" unfolding \<beta>_def by simp
  have fit: "\<kappa>\<^sub>g + \<beta> \<le> \<kappa>\<^sub>0"
    unfolding \<kappa>\<^sub>g_def \<beta>_def using k0pos by simp
  \<comment> \<open>5. one \<open>\<epsilon>\<close> for BOTH sup-convolutions\<close>
  obtain \<epsilon>u where eupos: "0 < \<epsilon>u"
    and upu: "\<And>e x. 0 < e \<Longrightarrow> e \<le> \<epsilon>u \<Longrightarrow> x \<in> K
        \<Longrightarrow> supconv (\<lambda>y. \<theta> * u y) e x \<le> \<theta> * u x + \<sigma>"
    using supconv_uniform_upper[OF cK Bu lou cu spos] by blast
  obtain \<epsilon>w where ewpos: "0 < \<epsilon>w"
    and upw: "\<And>e x. 0 < e \<Longrightarrow> e \<le> \<epsilon>w \<Longrightarrow> x \<in> K
        \<Longrightarrow> supconv (- w) e x \<le> (- w) x + \<sigma>"
    using supconv_uniform_upper[OF cK Bw low cw spos] by blast
  \<comment> \<open>\<open>\<epsilon>\<close> must ALSO be small enough that the sup-convolution attainment radii
      \<open>R\<^sub>u\<close>, \<open>R\<^sub>w\<close> fit inside \<open>\<kappa>\<^sub>g\<close> --- a constraint that comes from downstream,
      from \<open>smallu\<close>/\<open>fitu\<close> in \<open>comparison_from_localised_maximiser_soft\<close>, and is
      invisible from the boundary argument alone.  It is consistent because
      \<open>\<kappa>\<^sub>g\<close> is fixed at step 4, BEFORE \<open>\<epsilon>\<close> is chosen at step 5.\<close>
  have hq: "0 < (\<kappa>\<^sub>g/4)\<^sup>2" using kgpos by simp
  have DunN: "0 \<le> max 0 (Bu - Blu)" by simp
  have DwnN: "0 \<le> max 0 (Bw - Blw)" by simp
  obtain \<epsilon>A where eApos: "0 < \<epsilon>A"
    and eAlt: "2*\<epsilon>A*(max 0 (Bu - Blu)) < (\<kappa>\<^sub>g/4)\<^sup>2"
    using exists_eps_aux[OF hq DunN] by blast
  obtain \<epsilon>B where eBpos: "0 < \<epsilon>B"
    and eBlt: "2*\<epsilon>B*(max 0 (Bw - Blw)) < (\<kappa>\<^sub>g/4)\<^sup>2"
    using exists_eps_aux[OF hq DwnN] by blast
  define \<epsilon> where "\<epsilon> = min (min \<epsilon>u \<epsilon>w) (min \<epsilon>A \<epsilon>B)"
  have epos: "0 < \<epsilon>" unfolding \<epsilon>_def using eupos ewpos eApos eBpos by simp
  have eleu: "\<epsilon> \<le> \<epsilon>u" unfolding \<epsilon>_def by simp
  have elew: "\<epsilon> \<le> \<epsilon>w" unfolding \<epsilon>_def by simp
  have eleA: "\<epsilon> \<le> \<epsilon>A" unfolding \<epsilon>_def by simp
  have eleB: "\<epsilon> \<le> \<epsilon>B" unfolding \<epsilon>_def by simp
  have smallu: "2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2"
    by (rule eps_mono_aux[OF epos eleA eAlt])
  have smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    by (rule eps_mono_aux[OF epos eleB eBlt])
  \<comment> \<open>6. an upper bound for the doubled functional on \<open>K \<times> K\<close>\<close>
  have cA: "continuous_on K (supconv (\<lambda>y. \<theta> * u y) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bu epos] subset_UNIV])
  have cB0: "continuous_on K (supconv (- w) \<epsilon>)"
    by (rule continuous_on_subset[OF supconv_continuous[OF Bw epos] subset_UNIV])
  have cB: "continuous_on K (\<lambda>y. - supconv (- w) \<epsilon> y)"
    by (intro continuous_intros cB0)
  obtain C where Cbnd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> x - (\<lambda>y. - supconv (- w) \<epsilon> y) y \<le> C"
    using doubling_upper_bound_exists[OF cK neK cA cB] by blast
  have Cbnd': "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y \<le> C"
    if "x \<in> K" "y \<in> K" for x y
    using Cbnd[OF that] by simp
  \<comment> \<open>7. \<open>\<beta>\<close> fixes \<open>\<kappa>\<^sub>P\<close> and with it the maximiser\<close>
  obtain \<kappa>\<^sub>P xh yh where kPpos: "0 < \<kappa>\<^sub>P" and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxb: "\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and near: "dist xh yh < \<beta>"
    using doubling_close_maximiser_supconv_soft
      [OF cK neK Bu Bw epos zK Cbnd' bpos] by blast
  have mx: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - soft_pen \<kappa>\<^sub>P (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mxb that by blast
  \<comment> \<open>8. transfer the value to the ORIGINAL functions\<close>
  have kPnn: "0 \<le> \<kappa>\<^sub>P" using kPpos by linarith
  have vt: "\<theta> * u z + (- w) z + soft_pen \<kappa>\<^sub>P (xh - yh)
      \<le> \<theta> * u xh + (- w) yh + 2*\<sigma>"
    by (rule doubling_maximiser_value_transfer_gen
        [where A = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and Bf = "supconv (- w) \<epsilon>"
           and f = "\<lambda>y. \<theta> * u y" and g = "- w" and Pn = "soft_pen \<kappa>\<^sub>P"
           and K = K and xh = xh and yh = yh and z = z and \<sigma> = \<sigma>,
         OF mx zK soft_pen_zero
            supconv_ge[OF Bu epos] supconv_ge[OF Bw epos]
            upu[OF epos eleu xhK] upw[OF epos elew yhK]])
  have pnn: "0 \<le> soft_pen \<kappa>\<^sub>P (xh - yh)" by (rule soft_pen_nonneg[OF kPnn])
  have tr: "\<theta> * u z + (- w) z \<le> \<theta> * u xh + (- w) yh + 2*\<sigma>"
    using vt pnn by linarith
  \<comment> \<open>9. the boundary theorem, at radius \<open>\<kappa>\<^sub>g + \<beta>\<close>\<close>
  have valM: "M \<le> \<theta> * u z + (- w) z" using Mval by simp
  have nearle: "dist xh yh \<le> \<beta>" using near by linarith
  have modg: "(- w) q \<le> (- w) p + \<tau>" if "p \<in> K" "q \<in> K" "dist p q \<le> \<beta>" for p q
    using modg0[OF that(1) that(2)] that(3) bleb0 by linarith
  have bdry': "\<theta> * u c + (- w) c \<le> m" if "c \<in> K - interior K" for c
    using bdry[OF that] by simp
  have modF: "\<theta> * u p + (- w) p \<le> \<theta> * u q + (- w) q + \<tau>'"
    if "p \<in> K" "q \<in> K" "dist p q \<le> \<kappa>\<^sub>g + \<beta>" for p q
  proof -
    have "dist q p \<le> \<kappa>\<^sub>0" using that(3) fit by (simp add: dist_commute)
    from modF0[OF that(2) that(1) this] show ?thesis by simp
  qed
  have gap: "m + 2*\<sigma> + \<tau> + \<tau>' < M" using gsum by linarith
  have farx: "\<kappa>\<^sub>g + \<beta> < dist xh b" if b: "b \<in> K - interior K" for b
    by (rule doubling_maximiser_far_from_boundary
        [where f = "\<lambda>y. \<theta> * u y" and g = "- w" and K = K and xh = xh
           and yh = yh and M = M and z = z and \<sigma> = \<sigma> and \<beta> = \<beta>
           and \<tau> = \<tau> and m = m and \<kappa> = "\<kappa>\<^sub>g + \<beta>" and \<tau>' = \<tau>',
         OF xhK yhK valM tr nearle modg bdry' modF gap b])
  \<comment> \<open>10. and the mirror bound for \<open>ŷ\<close>, for free\<close>
  have fary: "\<kappa>\<^sub>g < dist yh b" if b: "b \<in> K - interior K" for b
  proof -
    have tri: "dist xh b \<le> dist xh yh + dist yh b" by (rule dist_triangle)
    have "\<kappa>\<^sub>g + \<beta> < dist xh b" by (rule farx[OF b])
    then show ?thesis using tri near by linarith
  qed
  \<comment> \<open>explicit introductions: a single \<open>blast\<close> over this nested existential
      searches instead of just building the witness, and PIDE flags it as
      possibly nonterminating\<close>
  have f1: "\<kappa>\<^sub>g < dist xh b" if b: "b \<in> K - interior K" for b
    using farx[OF b] bpos by linarith
  have F1: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b"
  proof
    fix b assume "b \<in> K - interior K"
    then show "\<kappa>\<^sub>g < dist xh b" by (rule f1)
  qed
  have F2: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b"
  proof
    fix b assume "b \<in> K - interior K"
    then show "\<kappa>\<^sub>g < dist yh b" by (rule fary)
  qed
  have inner: "(\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh))
      \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b)
      \<and> (\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b)
      \<and> 2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2
      \<and> 2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    by (intro conjI mxb F1 F2 smallu smallw)
  show ?thesis
    by (rule exI[of _ \<epsilon>], rule conjI[OF epos],
        rule exI[of _ \<kappa>\<^sub>g], rule conjI[OF kgpos],
        rule exI[of _ \<kappa>\<^sub>P], rule conjI[OF kPpos],
        rule bexI[OF _ xhK], rule bexI[OF _ yhK], rule inner)
qed

subsection \<open>Skolemising a four-component existential over an index\<close>

text \<open>\<open>doubled_supconv_jet_exists\<close> produces four objects at once - the
  maximiser, the tilt, the gradient and the Hessian - so plain \<open>choice\<close>
  does not apply directly; this is the general skolemisation form,
  reusable wherever a construction is run at each index and collected
  into sequences.\<close>

lemma choice4:
  assumes "\<And>i. \<exists>a b c d. P i a b c d"
  shows "\<exists>A B C D. \<forall>i. P i (A i) (B i) (C i) (D i)"
  using assms by metis

text \<open>The shifted analogue: run Jensen at the perturbation \<open>\<delta>\<^sub>i\<close> and tilt
  \<open>dd\<^sub>i\<close> of \<open>shifted_family_parameters\<close>, and skolemise.  Both hypotheses
  Jensen needs are automatic, from \<open>shifted_annulus_bound_split\<close> and the
  smallness condition \<open>2 dd\<^sub>i r < \<delta>\<^sub>i\<rho>\<^sup>2\<close>; only the maximiser property
  over \<open>cball \<xi>\<^sub>0 r\<close> is assumed.\<close>

theorem shifted_jensen_family:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. w y \<le> Bw"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and D0: "0 < D\<^sub>0"
    and mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        supconv u \<epsilon> (fst y) + supconv w \<epsilon> (snd y)
          - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
        \<le> supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
          - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2"
  shows "\<exists>zh p q W. \<forall>i.
      dist (zh i) \<xi>\<^sub>0 < \<rho>
      \<and> norm (p i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv u \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p i \<bullet> y
          \<le> ((supconv u \<epsilon> (fst (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh i) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zh i) - snd (zh i)))\<^sup>2) + p i \<bullet> (zh i))
      \<and> bounded_linear (W i) \<and> (\<forall>v z. v \<bullet> W i z = z \<bullet> W i v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> W i hk)
      \<and> ((\<lambda>hk. (((supconv u \<epsilon> (fst (zh i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zh i + hk) - snd (zh i + hk)))\<^sup>2)
          - ((supconv u \<epsilon> (fst (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh i) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zh i) - snd (zh i)))\<^sup>2)
          - q i \<bullet> hk - (hk \<bullet> W i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have r0: "0 < r" using rho by simp
  have dpos: "0 < D\<^sub>0/(2 + real i)" for i
    by (rule shifted_family_parameters(1)[OF D0 rho(1) r0])
  have dnn: "0 \<le> D\<^sub>0/(2 + real i)" for i
    using dpos[of i] by linarith
  have ddpos: "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)" for i
    by (rule shifted_family_parameters(2)[OF D0 rho(1) r0])
  have ddlt: "D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (2*r)" for i
    by (rule shifted_family_parameters(3)[OF D0 rho(1) r0])
  have bnd: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow> \<rho> \<le> dist y \<xi>\<^sub>0 \<Longrightarrow>
      (supconv u \<epsilon> (fst y) - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv w \<epsilon> (snd y)
            - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
      \<le> (supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
          - (D\<^sub>0/(2 + real i)) * \<rho>\<^sup>2" for i
    by (rule shifted_annulus_bound_split[OF mxK dnn rho(1)])
  have gen: "2 * (Y / (4*r)) * r = Y / 2" for Y :: real
    using r0 by (simp add: field_simps)
  have halfgen: "Y / 2 < Y" if "0 < Y" for Y :: real
    using that by simp
  have small: "2 * (D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) * r
      < ((supconv u \<epsilon> (fst \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (fst \<xi>\<^sub>0 - fst \<xi>\<^sub>0))\<^sup>2)
          + (supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (snd \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
          - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
        - ((supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
              - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
            - (D\<^sub>0/(2 + real i)) * \<rho>\<^sup>2)" for i
  proof -
    have pos: "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2"
      by (rule mult_pos_pos[OF dpos]) (use rho(1) in simp)
    have lhs: "2 * (D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) * r
        = D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / 2"
      by (rule gen)
    have rhs: "((supconv u \<epsilon> (fst \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (fst \<xi>\<^sub>0 - fst \<xi>\<^sub>0))\<^sup>2)
          + (supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (snd \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
          - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
        - ((supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
              - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
            - (D\<^sub>0/(2 + real i)) * \<rho>\<^sup>2)
      = D\<^sub>0/(2 + real i) * \<rho>\<^sup>2"
      by simp
    show ?thesis
      unfolding lhs rhs by (rule halfgen[OF pos])
  qed  define P where "P = (\<lambda>i zh p q W.
      dist zh \<xi>\<^sub>0 < \<rho>
      \<and> norm p \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv u \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
          \<le> ((supconv u \<epsilon> (fst zh)
              - (D\<^sub>0/(2 + real i)) * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd zh)
              - (D\<^sub>0/(2 + real i)) * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> W hk)
      \<and> ((\<lambda>hk. (((supconv u \<epsilon> (fst (zh + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
          - ((supconv u \<epsilon> (fst zh)
              - (D\<^sub>0/(2 + real i)) * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd zh)
              - (D\<^sub>0/(2 + real i)) * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
          - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0))"
  have H: "\<exists>zh p q W. P i zh p q W" for i
    unfolding P_def
    by (rule doubled_supconv_jet_exists_shifted
        [OF Bu Bw e a dnn rho(1) rho(2) bnd ddpos small])
  obtain zf pf qf Wf where famP: "\<forall>i. P i (zf i) (pf i) (qf i) (Wf i)"
    using choice4[where P = P, OF H] by blast
  show ?thesis
    using famP[unfolded P_def] by blast
qed

text \<open>The shifted Jensen family for a general penalty: run the shifted
  construction at tilts \<open>\<delta>\<^sub>i = D\<^sub>0/(2+i)\<close> and skolemise with \<open>choice4\<close>, a
  transcription of \<open>shifted_jensen_family\<close> now that every lemma it calls
  has a general form.\<close>

theorem shifted_jensen_family_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
  assumes Bu: "\<And>y. u y \<le> Bu" and Bw: "\<And>y. w y \<le> Bw"
    and e: "0 < \<epsilon>" and k: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - Pn d)"
    and rho: "0 < \<rho>" "\<rho> < r"
    and D0: "0 < D\<^sub>0"
    and mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        supconv u \<epsilon> (fst y) + supconv w \<epsilon> (snd y) - Pn (fst y - snd y)
        \<le> supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
  shows "\<exists>zh p q W. \<forall>i.
      dist (zh i) \<xi>\<^sub>0 < \<rho>
      \<and> norm (p i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv u \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst y - snd y)) + p i \<bullet> y
          \<le> ((supconv u \<epsilon> (fst (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh i) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zh i) - snd (zh i))) + p i \<bullet> (zh i))
      \<and> bounded_linear (W i) \<and> (\<forall>v z. v \<bullet> W i z = z \<bullet> W i v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> W i hk)
      \<and> ((\<lambda>hk. (((supconv u \<epsilon> (fst (zh i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zh i + hk) - snd (zh i + hk)))
          - ((supconv u \<epsilon> (fst (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh i) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zh i) - snd (zh i)))
          - q i \<bullet> hk - (hk \<bullet> W i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
proof -
  have r0: "0 < r" using rho by simp
  have dpos: "0 < D\<^sub>0/(2 + real i)" for i
    by (rule shifted_family_parameters(1)[OF D0 rho(1) r0])
  have dnn: "0 \<le> D\<^sub>0/(2 + real i)" for i using dpos[of i] by linarith
  have ddpos: "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)" for i
    by (rule shifted_family_parameters(2)[OF D0 rho(1) r0])
  have bnd: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow> \<rho> \<le> dist y \<xi>\<^sub>0 \<Longrightarrow>
      (supconv u \<epsilon> (fst y) - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv w \<epsilon> (snd y)
            - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)
      \<le> (supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))
          - (D\<^sub>0/(2 + real i)) * \<rho>\<^sup>2" for i
    by (rule shifted_annulus_bound_split_gen
        [where \<delta> = "D\<^sub>0/(2 + real i)" and A = "supconv u \<epsilon>"
           and B = "supconv w \<epsilon>" and Pn = Pn and \<xi>\<^sub>0 = \<xi>\<^sub>0 and r = r,
         OF mxK dnn rho(1)])
  have gen: "2 * (Y / (4*r)) * r = Y / 2" for Y :: real
    using r0 by (simp add: field_simps)
  have halfgen: "Y / 2 < Y" if "0 < Y" for Y :: real
    using that by simp
  have small: "2 * (D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) * r
      < ((supconv u \<epsilon> (fst \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (fst \<xi>\<^sub>0 - fst \<xi>\<^sub>0))\<^sup>2)
          + (supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (snd \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
          - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))
        - ((supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
              - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))
            - (D\<^sub>0/(2 + real i)) * \<rho>\<^sup>2)" for i
  proof -
    have pos: "0 < D\<^sub>0/(2 + real i) * \<rho>\<^sup>2"
      by (rule mult_pos_pos[OF dpos]) (use rho(1) in simp)
    have lhs: "2 * (D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)) * r
        = (D\<^sub>0/(2 + real i) * \<rho>\<^sup>2) / 2"
      by (rule gen)
    have rhs: "((supconv u \<epsilon> (fst \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (fst \<xi>\<^sub>0 - fst \<xi>\<^sub>0))\<^sup>2)
          + (supconv w \<epsilon> (snd \<xi>\<^sub>0)
            - (D\<^sub>0/(2 + real i)) * (norm (snd \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2)
          - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))
        - ((supconv u \<epsilon> (fst \<xi>\<^sub>0) + supconv w \<epsilon> (snd \<xi>\<^sub>0)
              - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))
            - (D\<^sub>0/(2 + real i)) * \<rho>\<^sup>2)
      = D\<^sub>0/(2 + real i) * \<rho>\<^sup>2"
      by simp
    show ?thesis
      unfolding lhs rhs by (rule halfgen[OF pos])
  qed
  define P where "P = (\<lambda>i zh p q W.
      dist zh \<xi>\<^sub>0 < \<rho>
      \<and> norm p \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv u \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst y - snd y)) + p \<bullet> y
          \<le> ((supconv u \<epsilon> (fst zh)
              - (D\<^sub>0/(2 + real i)) * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd zh)
              - (D\<^sub>0/(2 + real i)) * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst zh - snd zh)) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> W hk)
      \<and> ((\<lambda>hk. (((supconv u \<epsilon> (fst (zh + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zh + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd (zh + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zh + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zh + hk) - snd (zh + hk)))
          - ((supconv u \<epsilon> (fst zh)
              - (D\<^sub>0/(2 + real i)) * (norm (fst zh - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv w \<epsilon> (snd zh)
              - (D\<^sub>0/(2 + real i)) * (norm (snd zh - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst zh - snd zh))
          - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0))"
  have H: "\<exists>zh p q W. P i zh p q W" for i
    unfolding P_def
    by (rule doubled_supconv_jet_exists_shifted_gen
        [OF Bu Bw e k sc dnn rho(1) rho(2) bnd ddpos small])
  obtain zf pf qf Wf where famP: "\<forall>i. P i (zf i) (pf i) (qf i) (Wf i)"
    using choice4[where P = P, OF H] by blast
  show ?thesis
    using famP[unfolded P_def] by blast
qed
subsection \<open>The family construction, abstracted over the produced predicate\<close>

text \<open>Stated abstractly over the produced predicate \<open>Q\<close> rather than
  transcribing \<open>doubled_supconv_jet_exists\<close>'s fifteen-line jet conclusion
  directly.  Read \<open>Q dd zh p q W\<close> as "running the construction at tilt
  \<open>dd\<close> yields maximiser \<open>zh\<close>, tilt vector \<open>p\<close>, gradient \<open>q\<close> and Hessian
  \<open>W\<close>".  The hypothesis is \<open>doubled_supconv_jet_exists\<close> with its
  \<open>dd\<close>-dependent side conditions discharged by \<open>jensen_tilt_small_enough\<close>;
  the conclusion is the indexed family
  \<open>comparison_supconv_sequence_complete\<close> consumes.\<close>

text \<open>With \<open>tilt_sequence_admissible\<close> this gives families indexed by \<open>i\<close>
  whose tilts converge to zero, which \<open>gradient_sequences_align_of_bound\<close>
  needs to align the two gradients and close the alignment hypothesis of
  \<open>env_strict_contradiction_of_shifted_limits\<close>.\<close>

section \<open>From a bounded family to the contradiction\<close>

text \<open>\<open>comparison_supconv_sequence_complete\<close> asks for four convergent
  sequences and \<open>p \<noteq> 0\<close> at the limit, but the doubling produces only
  bounds - on the Hessians, the penalty gradients, and the tilts.  Three
  facts close the gap: simultaneous extraction is free, since a finite
  tuple of euclidean spaces is euclidean and one application of
  \<open>bounded_seq_limit_point\<close> extracts a subsequence along which every
  component converges; the per-index hypotheses survive subsequencing
  since they are universally quantified; and the two gradient sequences
  share a limit by \<open>gradient_sequences_align_of_bound\<close> (they differ only
  by the shrinking tilt), while \<open>p \<noteq> 0\<close> survives as the uniform lower
  bound \<open>c \<le> \<parallel>G\<^sub>i\<parallel>\<close> from \<open>doubling_grad_norm_lower_bound\<close>.\<close>

subsection \<open>The quadratic-form bound becomes a norm bound\<close>

text \<open>\<open>symmetric_form_bound_unit\<close> gives the entrywise bound
  \<open>\<bar>u \<bullet> Wv\<bar> \<le> c\<close>; \<open>norm_le_l1\<close> closes the gap to
  \<open>\<parallel>matrix W\<parallel> \<le> B\<close> with no spectral theory, since the operator norm is
  at most the sum of absolute coordinates.\<close>

lemma norm_le_card_Basis_bound:
  fixes M :: "'a::euclidean_space"
  assumes b: "\<And>e. e \<in> Basis \<Longrightarrow> \<bar>M \<bullet> e\<bar> \<le> c"
  shows "norm M \<le> real (card (Basis :: 'a set)) * c"
proof -
  have "norm M \<le> (\<Sum>e\<in>(Basis :: 'a set). \<bar>M \<bullet> e\<bar>)"
    by (rule norm_le_l1)
  also have "\<dots> \<le> (\<Sum>e\<in>(Basis :: 'a set). c)"
    by (rule sum_mono) (rule b)
  also have "\<dots> = real (card (Basis :: 'a set)) * c"
    by simp
  finally show ?thesis .
qed

lemma matrix_Basis_cases:
  fixes e :: "real^'n::finite^'n"
  assumes "e \<in> Basis"
  shows "\<exists>i j. e = axis i (axis j 1)"
proof -
  from assms obtain i u where eu: "e = axis i u"
    and uB: "u \<in> (Basis :: (real^'n) set)"
    unfolding Basis_vec_def by blast
  from uB obtain j v where uv: "u = axis j v"
    and vB: "v \<in> (Basis :: real set)"
    unfolding Basis_vec_def by blast
  from vB have "v = 1" by simp
  with eu uv show ?thesis by blast
qed

lemma inner_matrix_axis:
  fixes W :: "real^'n::finite \<Rightarrow> real^'n"
  assumes lin: "linear W"
  shows "matrix W \<bullet> axis i (axis j 1) = (axis i 1 :: real^'n) \<bullet> W (axis j 1)"
proof -
  have "matrix W \<bullet> axis i (axis j 1) = matrix W $ i $ j"
    by (simp add: inner_axis)
  also have "\<dots> = (W (axis j 1)) $ i"
    by (simp add: matrix_def)
  also have "\<dots> = (axis i 1 :: real^'n) \<bullet> W (axis j 1)"
    by (simp add: inner_axis')
  finally show ?thesis .
qed

theorem norm_matrix_le_of_form_bound:
  fixes W :: "real^'n::finite \<Rightarrow> real^'n"
  assumes lin: "linear W" and sym: "\<And>v z. v \<bullet> W z = z \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
  shows "norm (matrix W) \<le> real (card (Basis :: (real^'n^'n) set)) * c"
proof (rule norm_le_card_Basis_bound)
  fix e :: "real^'n^'n"
  assume "e \<in> Basis"
  then obtain i j where e: "e = axis i (axis j 1)"
    using matrix_Basis_cases by blast
  have nu: "norm (axis i (1::real) :: real^'n) = 1"
    by (rule norm_axis_1)
  have nv: "norm (axis j (1::real) :: real^'n) = 1"
    by (rule norm_axis_1)
  have "\<bar>(axis i 1 :: real^'n) \<bullet> W (axis j 1)\<bar> \<le> c"
    by (rule symmetric_form_bound_unit[OF lin sym bnd nu nv])
  then show "\<bar>matrix W \<bullet> e\<bar> \<le> c"
    unfolding e inner_matrix_axis[OF lin] .
qed

text \<open>From the jet to \<open>\<parallel>X\<^sub>i\<parallel> \<le> BX\<close>: testing the product-space Hessian
  \<open>W\<close> against \<open>(k,0)\<close> and \<open>(0,k)\<close> bounds the two block maps, with block
  constant \<open>C+\<bar>\<alpha>\<bar>\<close>.  No sign hypothesis on \<open>C\<close> is needed:
  \<open>-C\<parallel>k\<parallel>\<^sup>2 \<le> k \<bullet> Wk \<le> 0\<close> already forces \<open>0 \<le> C\<parallel>k\<parallel>\<^sup>2\<close>.\<close>

lemma hessian_abs_bound_of_two_sided:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lo: "\<And>k. - (C * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    and hi: "\<And>k. k \<bullet> W k \<le> 0"
  shows "\<bar>k \<bullet> W k\<bar> \<le> C * (norm k)\<^sup>2"
proof -
  have l: "- (C * (norm k)\<^sup>2) \<le> k \<bullet> W k" by (rule lo)
  have h: "k \<bullet> W k \<le> 0" by (rule hi)
  from l h have nn: "0 \<le> C * (norm k)\<^sup>2" by linarith
  from l h nn show ?thesis by (intro abs_leI) linarith+
qed

lemma block_form_bound_fst:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (fst (W (k, 0)) + \<alpha> *\<^sub>R k)\<bar> \<le> (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((k, 0) :: (real^'n) \<times> (real^'n)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> fst (W (k, 0))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(k, 0)"] by (simp add: inner_prod_def n0)
  have eqsum: "k \<bullet> (fst (W (k, 0)) + \<alpha> *\<^sub>R k)
      = k \<bullet> fst (W (k, 0)) + \<alpha> * (norm k)\<^sup>2"
    by (simp add: inner_add_right power2_norm_eq_inner)
  have aa: "\<bar>\<alpha> * (norm k)\<^sup>2\<bar> = \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    by (simp add: abs_mult)
  have "\<bar>k \<bullet> (fst (W (k, 0)) + \<alpha> *\<^sub>R k)\<bar>
      \<le> \<bar>k \<bullet> fst (W (k, 0))\<bar> + \<bar>\<alpha> * (norm k)\<^sup>2\<bar>"
    unfolding eqsum by (rule abs_triangle_ineq)
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    using b1 aa by linarith
  also have "\<dots> = (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma block_form_bound_snd:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (- (snd (W (0, k)) + \<alpha> *\<^sub>R k))\<bar> \<le> (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((0, k) :: (real^'n) \<times> (real^'n)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> snd (W (0, k))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(0, k)"] by (simp add: inner_prod_def n0)
  have eqsum: "k \<bullet> (- (snd (W (0, k)) + \<alpha> *\<^sub>R k))
      = - (k \<bullet> snd (W (0, k)) + \<alpha> * (norm k)\<^sup>2)"
    by (simp add: inner_diff_right inner_add_right
        power2_norm_eq_inner)
  have aa: "\<bar>\<alpha> * (norm k)\<^sup>2\<bar> = \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    by (simp add: abs_mult)
  have "\<bar>k \<bullet> (- (snd (W (0, k)) + \<alpha> *\<^sub>R k))\<bar>
      \<le> \<bar>k \<bullet> snd (W (0, k))\<bar> + \<bar>\<alpha> * (norm k)\<^sup>2\<bar>"
    unfolding eqsum by (simp add: abs_triangle_ineq)
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + \<bar>\<alpha>\<bar> * (norm k)\<^sup>2"
    using b1 aa by linarith
  also have "\<dots> = (C + \<bar>\<alpha>\<bar>) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem norm_block_matrices_bounded:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W" and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and lo: "\<And>k. - (C * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    and hi: "\<And>k. k \<bullet> W k \<le> 0"
  shows "norm (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
    and "norm (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
proof -
  have bnd: "\<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2" for z
    by (rule hessian_abs_bound_of_two_sided[OF lo hi])
  show "norm (matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_fst[OF blW] sym_block_fst[OF symW]
           block_form_bound_fst[OF bnd]])
  show "norm (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + \<bar>\<alpha>\<bar>)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_snd[OF blW] sym_block_snd[OF symW]
           block_form_bound_snd[OF bnd]])
qed

text \<open>For a general penalty, \<open>onorm_le_matrix_component_sum\<close> bounds
  \<open>onorm ((*v) Z)\<close> by the entry sum, and Cauchy-Schwarz gives the
  quadratic form bound, replacing the quadratic version's \<open>\<bar>\<alpha>\<bar>\<close>.  The
  block bounds take the constant abstractly (\<open>KZ\<close>), so a sharper bound -
  e.g. the quartic's Hessian \<open>\<beta>((d \<bullet> d)I+2dd\<^sup>T)\<close> has norm
  \<open>O(\<beta>\<parallel>d\<parallel>\<^sup>2)\<close> - can be supplied instead.\<close>

lemma block_form_bound_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
    and bZ: "\<And>z. \<bar>z \<bullet> (Z *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (fst (W (k, 0)) + Z *v k)\<bar> \<le> (C + KZ) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((k, 0) :: (real^'n) \<times> (real^'n)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> fst (W (k, 0))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(k, 0)"] by (simp add: inner_prod_def n0)
  have b2: "\<bar>k \<bullet> (Z *v k)\<bar> \<le> KZ * (norm k)\<^sup>2" by (rule bZ)
  have "\<bar>k \<bullet> (fst (W (k, 0)) + Z *v k)\<bar>
      \<le> \<bar>k \<bullet> fst (W (k, 0))\<bar> + \<bar>k \<bullet> (Z *v k)\<bar>"
    by (simp add: inner_add_right abs_triangle_ineq)
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + KZ * (norm k)\<^sup>2"
    using b1 b2 by linarith
  also have "\<dots> = (C + KZ) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma block_form_bound_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes bnd: "\<And>z. \<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2"
    and bZ: "\<And>z. \<bar>z \<bullet> (Z *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
  shows "\<bar>k \<bullet> (- (snd (W (0, k)) + Z *v k))\<bar> \<le> (C + KZ) * (norm k)\<^sup>2"
proof -
  have n0: "norm ((0, k) :: (real^'n) \<times> (real^'n)) = norm k"
    by (simp add: norm_Pair)
  have b1: "\<bar>k \<bullet> snd (W (0, k))\<bar> \<le> C * (norm k)\<^sup>2"
    using bnd[of "(0, k)"] by (simp add: inner_prod_def n0)
  have b2: "\<bar>k \<bullet> (Z *v k)\<bar> \<le> KZ * (norm k)\<^sup>2" by (rule bZ)
  have e: "k \<bullet> (- (snd (W (0, k)) + Z *v k))
      = - (k \<bullet> snd (W (0, k))) - (k \<bullet> (Z *v k))"
    by (simp add: inner_add_right inner_diff_right)
  have "\<bar>k \<bullet> (- (snd (W (0, k)) + Z *v k))\<bar>
      \<le> \<bar>k \<bullet> snd (W (0, k))\<bar> + \<bar>k \<bullet> (Z *v k)\<bar>"
    unfolding e by simp
  also have "\<dots> \<le> C * (norm k)\<^sup>2 + KZ * (norm k)\<^sup>2"
    using b1 b2 by linarith
  also have "\<dots> = (C + KZ) * (norm k)\<^sup>2"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem norm_block_matrices_bounded_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W" and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
    and lo: "\<And>k. - (C * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    and hi: "\<And>k. k \<bullet> W k \<le> 0"
    and bZ: "\<And>z. \<bar>z \<bullet> (Z *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
  shows "norm (matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
    and "norm (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
proof -
  have bnd: "\<bar>z \<bullet> W z\<bar> \<le> C * (norm z)\<^sup>2" for z
    by (rule hessian_abs_bound_of_two_sided[OF lo hi])
  show "norm (matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_fst_gen[OF blW] sym_block_fst_gen[OF symW symZ]
           block_form_bound_fst_gen[OF bnd bZ]])
  show "norm (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * (C + KZ)"
    by (rule norm_matrix_le_of_form_bound
        [OF linear_block_snd_gen[OF blW] sym_block_snd_gen[OF symW symZ]
           block_form_bound_snd_gen[OF bnd bZ]])
qed

text \<open>The \<open>\<delta>\<close>-perturbation shifts both Hessians by the same \<open>2\<delta>I\<close>, so the
  ordering is untouched (the shifts cancel, \<open>psd_shifted_diff\<close>), symmetry
  is preserved since \<open>\<delta>I\<close> is symmetric, and the norm bound degrades by
  \<open>\<bar>2\<delta>\<bar>\<parallel>I\<parallel>\<close>, a constant vanishing with \<open>\<delta>\<^sub>i\<close>.\<close>

text \<open>\<open>transpose_scaleR\<close> and \<open>transpose_add\<close> live in
  @{theory Relative_Arbitrage.Constraint_Set_Convexity}.\<close>

lemma transpose_shifted_block:
  fixes M :: "real^'n::finite^'n"
  assumes s: "transpose M = M"
  shows "transpose (M + c *\<^sub>R mat 1) = M + c *\<^sub>R mat 1"
proof -
  have "transpose (M + c *\<^sub>R mat 1)
      = transpose M + transpose (c *\<^sub>R (mat 1 :: real^'n^'n))"
    by (rule transpose_add)
  also have "transpose (c *\<^sub>R (mat 1 :: real^'n^'n))
      = c *\<^sub>R transpose (mat 1 :: real^'n^'n)"
    by (rule transpose_scaleR)
  also have "transpose (mat 1 :: real^'n^'n) = mat 1"
    by (rule transpose_mat)
  finally show ?thesis using s by simp
qed

lemma psd_shifted_diff:
  fixes X Y :: "real^'n::finite^'n"
  assumes p: "psd (Y - X)"
  shows "psd ((Y + c *\<^sub>R mat 1) - (X + c *\<^sub>R mat 1))"
proof -
  have "(Y + c *\<^sub>R mat 1) - (X + c *\<^sub>R mat 1) = Y - X"
    by simp
  then show ?thesis using p by simp
qed

text \<open>The bridge between the jets' operator-form Hessian
  \<open>\<lambda>v. f v + c *\<^sub>R v\<close> and the matrix form the family theorem wants:
  taking the matrix of the shifted operator adds \<open>cI\<close>.  Every shifted
  fact then reduces to its unshifted counterpart plus
  \<open>transpose_shifted_block\<close>, \<open>psd_shifted_diff\<close> and \<open>norm_shifted_block\<close>.\<close>

lemma matrix_shift_apply:
  fixes M :: "real^'n::finite^'n"
  shows "(M + c *\<^sub>R mat 1) *v h = M *v h + c *\<^sub>R h"
proof -
  have "((M + c *\<^sub>R mat 1) *v h) $ i = (M *v h + c *\<^sub>R h) $ i" for i
  proof -
    have "((M + c *\<^sub>R mat 1) *v h) $ i
        = (\<Sum>j\<in>UNIV. (M $ i $ j + c * (if i = j then 1 else 0)) * h $ j)"
      by (simp add: matrix_vector_mult_def mat_def)
    also have "\<dots> = (\<Sum>j\<in>UNIV. M $ i $ j * h $ j)
        + (\<Sum>j\<in>UNIV. c * (if i = j then 1 else 0) * h $ j)"
      by (simp add: algebra_simps sum.distrib)
    also have "(\<Sum>j\<in>UNIV. c * (if i = j then 1 else 0) * h $ j)
        = (\<Sum>j\<in>UNIV. if j = i then c * h $ j else 0)"
      by (rule sum.cong) auto
    also have "(\<Sum>j\<in>UNIV. if j = i then c * h $ j else 0) = c * h $ i"
      by simp    finally show ?thesis
      by (simp add: matrix_vector_mult_def)
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

lemma norm_shifted_block:
  fixes M :: "real^'n::finite^'n"
  shows "norm (M + c *\<^sub>R mat 1)
      \<le> norm M + \<bar>c\<bar> * norm (mat 1 :: real^'n^'n)"
proof -
  have "norm (M + c *\<^sub>R mat 1) \<le> norm M + norm (c *\<^sub>R (mat 1 :: real^'n^'n))"
    by (rule norm_triangle_ineq)
  moreover have "norm (c *\<^sub>R (mat 1 :: real^'n^'n))
      = \<bar>c\<bar> * norm (mat 1 :: real^'n^'n)"
    by simp
  ultimately show ?thesis by linarith
qed

text \<open>Shifting \<open>Y\<close> down by \<open>cI\<close> and \<open>X\<close> up by \<open>cI\<close> costs the difference
  exactly \<open>2cI\<close>, recovering \<open>Y-X\<close> on cancellation; this is the equation
  behind the asymptotic \<open>psdi\<close> hypothesis, with defect
  \<open>cs\<^sub>i=2c\<^sub>i \<rightarrow> 0\<close>.\<close>

lemma shift_cancel_matrix:
  fixes X Y :: "real^'n::finite^'n"
  shows "(Y - c *\<^sub>R mat 1) - (X + c *\<^sub>R mat 1) + (2*c) *\<^sub>R mat 1 = Y - X"
  by (simp add: vec_eq_iff mat_def axis_def algebra_simps)

text \<open>The lower bound \<open>c \<le> \<parallel>G\<^sub>i\<parallel>\<close> is given by
  \<open>doubling_grad_norm_lower_bound\<close> at the doubling maximiser (the centre
  \<open>\<xi>\<close> of Jensen's ball); a triangle inequality moves it to Jensen's point
  at cost \<open>2\<bar>\<alpha>\<bar>\<rho>\<close>, uniformly in the index, so \<open>\<rho> < c/(4\<bar>\<alpha>\<bar>)\<close> keeps
  half of it.  The cost is left explicit since \<open>\<rho>\<close> is also constrained
  from the boundary side.\<close>

lemma penalty_gradient_nearby_bound:
  fixes zh \<xi> :: "(real^'n::finite) \<times> (real^'n)"
  assumes c: "c \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))"
    and d: "dist zh \<xi> \<le> \<rho>"
  shows "c - 2 * \<bar>\<alpha>\<bar> * \<rho> \<le> norm (\<alpha> *\<^sub>R (fst zh - snd zh))"
proof -
  have f: "norm (fst \<xi> - fst zh) \<le> \<rho>"
  proof -
    have "norm (fst \<xi> - fst zh) = dist (fst \<xi>) (fst zh)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist \<xi> zh" by (rule dist_fst_le)
    also have "\<dots> = dist zh \<xi>" by (rule dist_commute)
    finally show ?thesis using d by linarith
  qed
  have s: "norm (snd \<xi> - snd zh) \<le> \<rho>"
  proof -
    have "norm (snd \<xi> - snd zh) = dist (snd \<xi>) (snd zh)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist \<xi> zh" by (rule dist_snd_le)
    also have "\<dots> = dist zh \<xi>" by (rule dist_commute)
    finally show ?thesis using d by linarith
  qed  have eq: "\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>) - \<alpha> *\<^sub>R (fst zh - snd zh)
      = \<alpha> *\<^sub>R ((fst \<xi> - fst zh) - (snd \<xi> - snd zh))"
    by (simp add: algebra_simps)
  have "norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) - norm (\<alpha> *\<^sub>R (fst zh - snd zh))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>) - \<alpha> *\<^sub>R (fst zh - snd zh))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> = \<bar>\<alpha>\<bar> * norm ((fst \<xi> - fst zh) - (snd \<xi> - snd zh))"
    unfolding eq by simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (norm (fst \<xi> - fst zh) + norm (snd \<xi> - snd zh))"
    by (intro mult_left_mono norm_triangle_ineq4) simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)"
    using f s by (intro mult_left_mono) auto
  finally have "norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))
      - norm (\<alpha> *\<^sub>R (fst zh - snd zh)) \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)" .
  moreover have "\<bar>\<alpha>\<bar> * (2 * \<rho>) = 2 * \<bar>\<alpha>\<bar> * \<rho>" by simp
  ultimately show ?thesis using c by linarith
qed

text \<open>The value gap transfers to the sup-convolutions with an explicit loss:
  \<open>supconv_le_of_lipschitz\<close> sandwiches each sup-convolution between its
  function and that function plus \<open>\<epsilon>L\<^sup>2/2\<close>, so a gap \<open>\<gamma>\<close> for
  \<open>\<theta>u,w\<close> becomes \<open>\<gamma>-\<epsilon>(L\<^sub>u\<^sup>2+L\<^sub>w\<^sup>2)/2\<close> for the sup-convolutions,
  positive for every sufficiently small \<open>\<epsilon>\<close>.\<close>

theorem doubled_value_gap_supconv:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes e: "0 < \<epsilon>"
    and lipu: "\<And>p q. \<bar>\<theta> * u p - \<theta> * u q\<bar> \<le> Lu * norm (p - q)"
    and lipw: "\<And>p q. \<bar>(- w) p - (- w) q\<bar> \<le> Lw * norm (p - q)"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and gap: "\<theta> * u xh + (- w) xh + \<gamma> \<le> \<theta> * u z + (- w) z"
  shows "supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> xh
           + (\<gamma> - \<epsilon> * (Lu\<^sup>2 + Lw\<^sup>2) / 2)
         \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> z + supconv (- w) \<epsilon> z"
proof -
  have au: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh \<le> \<theta> * u xh + \<epsilon> * Lu\<^sup>2 / 2"
    by (rule supconv_le_of_lipschitz[OF e lipu])
  have aw: "supconv (- w) \<epsilon> xh \<le> (- w) xh + \<epsilon> * Lw\<^sup>2 / 2"
    by (rule supconv_le_of_lipschitz[OF e lipw])
  have gu: "\<theta> * u z \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> z"
    by (rule supconv_ge[OF Bu e])
  have gw: "(- w) z \<le> supconv (- w) \<epsilon> z"
    by (rule supconv_ge[OF Bw e])
  have dexp: "\<epsilon> * (Lu\<^sup>2 + Lw\<^sup>2) / 2 = \<epsilon> * Lu\<^sup>2 / 2 + \<epsilon> * Lw\<^sup>2 / 2"
    by (simp add: algebra_simps)
  from au aw gu gw gap dexp show ?thesis by linarith
qed

subsection \<open>The per-index data from one Jensen application\<close>

text \<open>\<open>doubled_supconv_jet_exists\<close> returns, at each tilt, a maximiser of the
  tilted functional together with an Alexandrov jet of the untilted one;
  this reads off the two component jets.  The tilt costs nothing to
  absorb: at an interior maximum of the tilted functional the untilted
  jet has gradient exactly \<open>-p\<close> (\<open>gradient_is_minus_tilt\<close>), so the two
  block gradients are \<open>-fst p+\<alpha>(x̂-ŷ)\<close> and \<open>-(snd p+\<alpha>(x̂-ŷ))\<close>, matching
  \<open>Pu\<close> and \<open>-Pw\<close> of \<open>comparison_supconv_bounded_family\<close> with common
  penalty gradient \<open>G = \<alpha>(x̂-ŷ)\<close>.\<close>

theorem tilted_doubled_jet_slices:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = - pt"
    and "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  show qm: "q = - pt"
    by (rule gradient_is_minus_tilt
        [where \<Psi> = "\<lambda>z. a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2"
           and d = "r - dist zh \<xi>" and zh = zh and p = pt and q = q and W = W,
         OF blW dpos mxT expPsi])
  have s1: "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_fst[OF expPsi])
  have s2: "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_snd[OF expPsi])
  have eqf: "(- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh))
      = fst q + \<alpha> *\<^sub>R (fst zh - snd zh)"
    using qm by simp
  have eqs: "(- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh)))
      = snd q - \<alpha> *\<^sub>R (fst zh - snd zh)"
    using qm by simp
  show "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + \<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s1 unfolding eqf .
  show "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + \<alpha> *\<^sub>R (fst zh - snd zh))) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s2 unfolding eqs .
qed

text \<open>The same for a general penalty: \<open>global_max_imp_interior_max\<close> and
  \<open>gradient_is_minus_tilt\<close> are already abstract in \<open>\<Psi>\<close>, so the
  conclusion is the quadratic one with \<open>\<alpha>(x̂-ŷ)\<close> replaced by \<open>G\<close> and
  \<open>\<alpha> h\<close> by \<open>Zh\<close>, carrying the penalty's jet \<open>(G,Z)\<close> along.\<close>

theorem tilted_doubled_jet_slices_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - P (fst y - snd y)) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "q = - pt"
    and "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + G)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z) - P (fst z - snd z)) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  show qm: "q = - pt"
    by (rule gradient_is_minus_tilt
        [where \<Psi> = "\<lambda>z. a (fst z) + b (snd z) - P (fst z - snd z)"
           and d = "r - dist zh \<xi>" and zh = zh and p = pt and q = q and W = W,
         OF blW dpos mxT expPsi])
  have s1: "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (fst q + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_fst_gen[OF expPsi Pjet])
  have s2: "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (snd q - G) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    by (rule doubled_jet_slice_snd_gen[OF expPsi Pjet])
  have eqf: "(- fst pt + G) = fst q + G"
    using qm by simp
  have eqs: "(- (snd pt + G)) = snd q - G"
    using qm by simp
  show "((\<lambda>h. (a (fst zh + h) - a (fst zh)
        - (- fst pt + G) \<bullet> h
        - (h \<bullet> (fst (W (h, 0)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s1 unfolding eqf .
  show "((\<lambda>h. (b (snd zh + h) - b (snd zh)
        - (- (snd pt + G)) \<bullet> h
        - (h \<bullet> (snd (W (0, h)) + Z *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    using s2 unfolding eqs .
qed

text \<open>For the shifted functional, running the slice lemmas on
  \<open>a-\<delta>\<parallel>\<cdot>-fst \<xi>\<^sub>0\<parallel>\<^sup>2\<close> and \<open>b-\<delta>\<parallel>\<cdot>-snd \<xi>\<^sub>0\<parallel>\<^sup>2\<close> then
  \<open>jet_transfer_quadratic\<close> shifts the two block gradients by
  \<open>2\<delta>(x̂-fst \<xi>\<^sub>0)\<close> and \<open>2\<delta>(y̅-snd \<xi>\<^sub>0)\<close>, and the Hessians by \<open>2\<delta>I\<close> -
  both \<open>O(\<delta>)\<close>, vanishing along \<open>\<delta>\<^sub>i \<rightarrow> 0\<close> as the alignment hypothesis
  needs.\<close>

text \<open>\<open>second_order_interior_max\<close> reads \<open>v \<bullet> Wv \<le> 0\<close> off the tilted
  interior maximum with no extra hypothesis; paired with the lower bound
  \<open>-c\<parallel>v\<parallel>\<^sup>2 \<le> v \<bullet> Wv\<close> from semiconvexity, this is the two-sided bound
  \<open>semiconvex_hessian_abs_bound\<close> wants, and through
  \<open>norm_matrix_le_of_form_bound\<close> gives the \<open>\<parallel>X\<^sub>i\<parallel> \<le> BX\<close> hypothesis of
  \<open>comparison_supconv_bounded_family\<close>.  \<open>semiconvex_jensen_alexandrov_point\<close>
  and \<open>doubled_supconv_jet_exists\<close> carry both halves of this bound, so
  \<open>norm_block_matrices_bounded\<close> closes the chain.\<close>
text \<open>The Hessian bound for a general penalty needs no jet of \<open>P\<close> at all,
  since \<open>second_order_interior_max\<close> concerns the full functional's
  Hessian \<open>W\<close>; a pure transcription.\<close>

theorem tilted_doubled_hessian_nonpositive_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and P :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - P (fst y - snd y)) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - P (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> W v \<le> 0"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z) - P (fst z - snd z)) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  have eq: "(((a (fst (zh + k)) + b (snd (zh + k))
          - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2
      = ((a (fst (zh + k)) + b (snd (zh + k))
          - P (fst (zh + k) - snd (zh + k)))
        - (a (fst zh) + b (snd zh) - P (fst zh - snd zh))
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2" for k
    by (simp add: algebra_simps)
  have expT: "((\<lambda>k. (((a (fst (zh + k)) + b (snd (zh + k))
          - P (fst (zh + k) - snd (zh + k))) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh) - P (fst zh - snd zh)) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule expPsi)
  have "(q + pt) \<bullet> v = 0 \<and> v \<bullet> W v \<le> 0"
    by (rule second_order_interior_max
        [where f = "\<lambda>z. (a (fst z) + b (snd z) - P (fst z - snd z)) + pt \<bullet> z"
           and x = zh and q = "q + pt" and X = W and \<delta> = "r - dist zh \<xi>",
         OF blW dpos mxT expT])
  then show ?thesis by simp
qed

theorem tilted_doubled_hessian_nonpositive:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "v \<bullet> W v \<le> 0"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxT: "(a (fst (zh + k)) + b (snd (zh + k))
        - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k)
      \<le> (a (fst zh) + b (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    if kk: "norm k < r - dist zh \<xi>" for k
    by (rule global_max_imp_interior_max
        [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + pt \<bullet> z"
           and \<xi> = \<xi> and r = r and zh = zh and k = k, OF mx kk])
  have eq: "(((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2
      = ((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2" for k
    by (simp add: algebra_simps)
  have expT: "((\<lambda>k. (((a (fst (zh + k)) + b (snd (zh + k))
          - (\<alpha>/2) * (norm (fst (zh + k) - snd (zh + k)))\<^sup>2) + pt \<bullet> (zh + k))
        - ((a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh)
        - (q + pt) \<bullet> k - (k \<bullet> W k)/2) / (norm k)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule expPsi)
  have "(q + pt) \<bullet> v = 0 \<and> v \<bullet> W v \<le> 0"
    by (rule second_order_interior_max
        [where f = "\<lambda>z. (a (fst z) + b (snd z)
              - (\<alpha>/2) * (norm (fst z - snd z))\<^sup>2) + pt \<bullet> z"
           and x = zh and q = "q + pt" and X = W and \<delta> = "r - dist zh \<xi>",
         OF blW dpos mxT expT])
  then show ?thesis by simp
qed

text \<open>For the ordering, the tilt must be absorbed into the two summands:
  \<open>sums_psd_from_jet\<close> wants a plain (untilted) doubled maximum, supplied
  by \<open>doubled_tilted_interior_max\<close> for \<open>a+fst p \<bullet> \<cdot>\<close> and
  \<open>b+snd p \<bullet> \<cdot>\<close>.  (Unlike the gradients, where \<open>gradient_is_minus_tilt\<close>
  avoids absorption, the psd ordering needs it.)\<close>

theorem tilted_doubled_psd_ordering:
  fixes a b :: "real^'n::finite \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
  assumes blW: "bounded_linear W"
    and symW: "\<And>uu uu'. uu \<bullet> W uu' = uu' \<bullet> W uu"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "psd (matrix (\<lambda>v. - (snd (W (0, v)) + \<alpha> *\<^sub>R v))
            - matrix (\<lambda>v. fst (W (v, 0)) + \<alpha> *\<^sub>R v))"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxAB: "(a (fst (zh + hk)) + fst pt \<bullet> fst (zh + hk))
        + (b (snd (zh + hk)) + snd pt \<bullet> snd (zh + hk))
        - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2
      \<le> (a (fst zh) + fst pt \<bullet> fst zh) + (b (snd zh) + snd pt \<bullet> snd zh)
        - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2"
    if kk: "norm hk < r - dist zh \<xi>" for hk
    by (rule doubled_tilted_interior_max
        [where a = a and b = b and \<alpha> = \<alpha> and p = pt and \<xi> = \<xi> and r = r
           and zh = zh and k = hk, OF mx kk])
  have eq: "(((a (fst (zh + hk)) + fst pt \<bullet> fst (zh + hk))
          + (b (snd (zh + hk)) + snd pt \<bullet> snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - ((a (fst zh) + fst pt \<bullet> fst zh) + (b (snd zh) + snd pt \<bullet> snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - (q + pt) \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2
      = ((a (fst (zh + hk)) + b (snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - (a (fst zh) + b (snd zh) - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2" for hk
    by (simp add: inner_prod_def algebra_simps)
  have expAB: "((\<lambda>hk. (((a (fst (zh + hk)) + fst pt \<bullet> fst (zh + hk))
          + (b (snd (zh + hk)) + snd pt \<bullet> snd (zh + hk))
          - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
        - ((a (fst zh) + fst pt \<bullet> fst zh) + (b (snd zh) + snd pt \<bullet> snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
        - (q + pt) \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule expPsi)
  show ?thesis
    by (rule sums_psd_from_jet
        [where a = "\<lambda>x. a x + fst pt \<bullet> x" and b = "\<lambda>y. b y + snd pt \<bullet> y"
           and d = "r - dist zh \<xi>" and zh = zh and q = "q + pt" and W = W,
         OF blW symW dpos mxAB expAB])
qed

text \<open>The psd ordering for a general penalty absorbs the tilt into the two
  summands inline, since \<open>sums_psd_at_interior_max_gen\<close> wants an untilted
  maximum.  It needs the extra hypothesis \<open>transpose Z = Z\<close>, unlike the
  quadratic case where \<open>Z = \<alpha>I\<close> is symmetric for free; it holds for the
  quartic's Hessian \<open>\<beta>((d \<bullet> d)I+2dd\<^sup>T)\<close>.\<close>

theorem tilted_doubled_psd_ordering_gen:
  fixes a b :: "real^'n::finite \<Rightarrow> real" and Pn :: "real^'n \<Rightarrow> real"
    and W :: "(real^'n) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and zh \<xi> pt q :: "(real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n" and G :: "real^'n"
  assumes blW: "bounded_linear W"
    and symW: "\<And>uu uu'. uu \<bullet> W uu' = uu' \<bullet> W uu"
    and symZ: "transpose Z = Z"
    and rz: "dist zh \<xi> < r"
    and mx: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
        (a (fst y) + b (snd y) - Pn (fst y - snd y)) + pt \<bullet> y
        \<le> (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh)) + pt \<bullet> zh"
    and expPsi: "((\<lambda>hk. ((a (fst (zh + hk)) + b (snd (zh + hk))
          - Pn (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and Pjet: "((\<lambda>h. (Pn ((fst zh - snd zh) + h) - Pn (fst zh - snd zh)
        - G \<bullet> h - (h \<bullet> (Z *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
  shows "psd (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))
            - matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))"
proof -
  have dpos: "0 < r - dist zh \<xi>"
    by (rule interior_radius_pos[OF rz])
  have mxAB: "(a (fst (zh + hk)) + fst pt \<bullet> fst (zh + hk))
        + (b (snd (zh + hk)) + snd pt \<bullet> snd (zh + hk))
        - Pn (fst (zh + hk) - snd (zh + hk))
      \<le> (a (fst zh) + fst pt \<bullet> fst zh) + (b (snd zh) + snd pt \<bullet> snd zh)
        - Pn (fst zh - snd zh)"
    if kk: "norm hk < r - dist zh \<xi>" for hk
  proof -
    have g: "(a (fst (zh + hk)) + b (snd (zh + hk))
          - Pn (fst (zh + hk) - snd (zh + hk))) + pt \<bullet> (zh + hk)
        \<le> (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh)) + pt \<bullet> zh"
      by (rule global_max_imp_interior_max
          [where \<Psi> = "\<lambda>z. (a (fst z) + b (snd z) - Pn (fst z - snd z))
                + pt \<bullet> z"
             and \<xi> = \<xi> and r = r and zh = zh and k = hk, OF mx kk])
    show ?thesis using g by (simp add: inner_prod_def algebra_simps)
  qed
  have eq: "(((a (fst (zh + hk)) + fst pt \<bullet> fst (zh + hk))
          + (b (snd (zh + hk)) + snd pt \<bullet> snd (zh + hk))
          - Pn (fst (zh + hk) - snd (zh + hk)))
        - ((a (fst zh) + fst pt \<bullet> fst zh) + (b (snd zh) + snd pt \<bullet> snd zh)
            - Pn (fst zh - snd zh))
        - (q + pt) \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2
      = ((a (fst (zh + hk)) + b (snd (zh + hk))
          - Pn (fst (zh + hk) - snd (zh + hk)))
        - (a (fst zh) + b (snd zh) - Pn (fst zh - snd zh))
        - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2" for hk
    by (simp add: inner_prod_def algebra_simps)
  have expAB: "((\<lambda>hk. (((a (fst (zh + hk)) + fst pt \<bullet> fst (zh + hk))
          + (b (snd (zh + hk)) + snd pt \<bullet> snd (zh + hk))
          - Pn (fst (zh + hk) - snd (zh + hk)))
        - ((a (fst zh) + fst pt \<bullet> fst zh) + (b (snd zh) + snd pt \<bullet> snd zh)
            - Pn (fst zh - snd zh))
        - (q + pt) \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    unfolding eq by (rule expPsi)
  show ?thesis
    by (rule sums_psd_at_interior_max_gen
        [where a = "\<lambda>x. a x + fst pt \<bullet> x" and b = "\<lambda>y. b y + snd pt \<bullet> y"
           and Pn = Pn and d = "r - dist zh \<xi>" and zh = zh and q = "q + pt"
           and W = W and Z = Z and G = G,
         OF blW symW symZ dpos mxAB expAB Pjet])
qed

subsection \<open>Bundling: one subsequence for the whole family\<close>

lemma norm_Pair_le:
  fixes a :: "'a::real_normed_vector" and b :: "'b::real_normed_vector"
  shows "norm ((a, b) :: 'a \<times> 'b) \<le> norm a + norm b"
proof -
  have eq: "((a, b) :: 'a \<times> 'b) = (a, 0) + (0, b)" by simp
  have "norm ((a, b) :: 'a \<times> 'b)
      \<le> norm ((a, 0) :: 'a \<times> 'b) + norm ((0, b) :: 'a \<times> 'b)"
    unfolding eq by (rule norm_triangle_ineq)
  then show ?thesis by (simp add: norm_Pair)
qed

theorem bounded_seq_limit_point_triple:
  fixes A :: "nat \<Rightarrow> 'a::euclidean_space" and B :: "nat \<Rightarrow> 'b::euclidean_space"
    and C :: "nat \<Rightarrow> 'c::euclidean_space"
  assumes bA: "\<And>i. norm (A i) \<le> Ba" and bB: "\<And>i. norm (B i) \<le> Bb"
    and bC: "\<And>i. norm (C i) \<le> Bc"
  shows "\<exists>A0 B0 C0 rr. strict_mono rr \<and> (\<lambda>i. A (rr i)) \<longlonglongrightarrow> A0
      \<and> (\<lambda>i. B (rr i)) \<longlonglongrightarrow> B0 \<and> (\<lambda>i. C (rr i)) \<longlonglongrightarrow> C0"
proof -
  have bnd: "norm ((A i, B i, C i) :: 'a \<times> 'b \<times> 'c) \<le> Ba + Bb + Bc" for i
  proof -
    have "norm ((A i, B i, C i) :: 'a \<times> 'b \<times> 'c)
        \<le> norm (A i) + norm ((B i, C i) :: 'b \<times> 'c)"
      by (rule norm_Pair_le)
    moreover have "norm ((B i, C i) :: 'b \<times> 'c) \<le> norm (B i) + norm (C i)"
      by (rule norm_Pair_le)
    ultimately show ?thesis
      using bA[of i] bB[of i] bC[of i] by linarith
  qed
  obtain Z0 rr where sm: "strict_mono rr"
    and lim: "(\<lambda>i. ((A (rr i), B (rr i), C (rr i)) :: 'a \<times> 'b \<times> 'c)) \<longlonglongrightarrow> Z0"
    using bounded_seq_limit_point
      [where Z = "\<lambda>i. ((A i, B i, C i) :: 'a \<times> 'b \<times> 'c)", OF bnd]
    by blast
  show ?thesis
  proof (intro exI conjI)
    show "strict_mono rr" by (rule sm)
    show "(\<lambda>i. A (rr i)) \<longlonglongrightarrow> fst Z0"
      using tendsto_fst[OF lim] by simp
    show "(\<lambda>i. B (rr i)) \<longlonglongrightarrow> fst (snd Z0)"
      using tendsto_fst[OF tendsto_snd[OF lim]] by simp
    show "(\<lambda>i. C (rr i)) \<longlonglongrightarrow> snd (snd Z0)"
      using tendsto_snd[OF tendsto_snd[OF lim]] by simp
  qed
qed

subsection \<open>The contradiction from bounds alone\<close>

text \<open>The replacement for \<open>comparison_supconv_sequence_complete\<close>: every
  convergence hypothesis becomes a bound, \<open>p \<noteq> 0\<close> becomes the uniform
  lower bound \<open>c \<le> \<parallel>G\<^sub>i\<parallel>\<close>, and the two gradient sequences are defined
  from the tilts and penalty gradients, \<open>Pu\<^sub>i=-fst p\<^sub>i+G\<^sub>i\<close> and
  \<open>Pw\<^sub>i=snd p\<^sub>i+G\<^sub>i\<close>, matching how the doubling produces them.\<close>

theorem comparison_supconv_bounded_family:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and X Y :: "nat \<Rightarrow> real^'n^'n" and Pu Pw G :: "nat \<Rightarrow> real^'n"
    and xu xw ysu ysw :: "nat \<Rightarrow> real^'n"
  assumes sub: "visc_subsol k L \<Omega>\<^sub>u u" and sup: "supersol_jet k L \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and ysuO: "\<And>i. ysu i \<in> \<Omega>\<^sub>u" and yswO: "\<And>i. ysw i \<in> \<Omega>\<^sub>w"
    and symX: "\<And>i. transpose (X i) = X i"
    and symY: "\<And>i. transpose (Y i) = Y i"
    and psdi: "\<And>i. psd (Y i - X i + (cs i) *\<^sub>R mat 1)"
    and cs0: "cs \<longlonglongrightarrow> 0"
    and optu: "\<And>i. supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i)
        = \<theta> * u (ysu i) - (dist (xu i) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    and optw: "\<And>i. supconv (- w) \<epsilon> (xw i)
        = (- w) (ysw i) - (dist (xw i) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    and jetu: "\<And>i. ((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu i) - Pu i \<bullet> h
        - (h \<bullet> (X i *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and jetw: "\<And>i. ((\<lambda>h. (supconv (- w) \<epsilon> (xw i + h) - supconv (- w) \<epsilon> (xw i)
        - (- Pw i) \<bullet> h - (h \<bullet> ((- Y i) *v h))/2) / (norm h)\<^sup>2)
      \<longlongrightarrow> 0) (at 0)"
    and bX: "\<And>i. norm (X i) \<le> BX" and bY: "\<And>i. norm (Y i) \<le> BY"
    and bG: "\<And>i. norm (G i) \<le> BG"
    and au: "(\<lambda>i. Pu i - G i) \<longlonglongrightarrow> 0"
    and aw: "(\<lambda>i. Pw i - G i) \<longlonglongrightarrow> 0"
    and glb: "\<And>i. c \<le> norm (G i)" and cpos: "0 < c"
  shows False
proof -
  obtain g X0 Y0 rr where sm: "strict_mono rr"
    and cG: "(\<lambda>i. G (rr i)) \<longlonglongrightarrow> g"
    and cX: "(\<lambda>i. X (rr i)) \<longlonglongrightarrow> X0"
    and cY: "(\<lambda>i. Y (rr i)) \<longlonglongrightarrow> Y0"
    using bounded_seq_limit_point_triple
      [where A = G and B = X and C = Y and Ba = BG and Bb = BX and Bc = BY,
       OF bG bX bY]
    by blast
  have aur: "(\<lambda>i. Pu (rr i) - G (rr i)) \<longlonglongrightarrow> 0"
    using LIMSEQ_subseq_LIMSEQ[OF au sm] by (simp add: o_def)
  have awr: "(\<lambda>i. Pw (rr i) - G (rr i)) \<longlonglongrightarrow> 0"
    using LIMSEQ_subseq_LIMSEQ[OF aw sm] by (simp add: o_def)
  have cPu: "(\<lambda>i. Pu (rr i)) \<longlonglongrightarrow> g"
    using tendsto_add[OF aur cG] by simp
  have cPw: "(\<lambda>i. Pw (rr i)) \<longlonglongrightarrow> g"
    using tendsto_add[OF awr cG] by simp  have cnorm: "(\<lambda>i. norm (G (rr i))) \<longlonglongrightarrow> norm g"
    by (rule tendsto_norm[OF cG])
  have cg: "c \<le> norm g"
  proof (rule tendsto_lowerbound[OF cnorm])
    show "\<forall>\<^sub>F i in sequentially. c \<le> norm (G (rr i))"
      using glb by simp
  qed simp
  have pnz: "g \<noteq> 0"
    using cg cpos by auto
  have ysuOr: "ysu (rr i) \<in> \<Omega>\<^sub>u" for i by (rule ysuO)
  have yswOr: "ysw (rr i) \<in> \<Omega>\<^sub>w" for i by (rule yswO)
  have symXr: "transpose (X (rr i)) = X (rr i)" for i by (rule symX)
  have symYr: "transpose (Y (rr i)) = Y (rr i)" for i by (rule symY)
  have psdir: "psd (Y (rr i) - X (rr i) + (cs (rr i)) *\<^sub>R mat 1)" for i
    by (rule psdi)
  have csr: "(\<lambda>i. cs (rr i)) \<longlonglongrightarrow> 0"
    using LIMSEQ_subseq_LIMSEQ[OF cs0 sm] by (simp add: o_def)
  have p0: "psd (Y0 - X0)"
    by (rule psd_diff_limit_shifted[OF cX cY csr psdir])
  have optur: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu (rr i))
      = \<theta> * u (ysu (rr i)) - (dist (xu (rr i)) (ysu (rr i)))\<^sup>2 / (2*\<epsilon>)" for i
    by (rule optu)
  have optwr: "supconv (- w) \<epsilon> (xw (rr i))
      = (- w) (ysw (rr i)) - (dist (xw (rr i)) (ysw (rr i)))\<^sup>2 / (2*\<epsilon>)" for i
    by (rule optw)
  have jetur: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu (rr i) + h)
      - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (xu (rr i)) - Pu (rr i) \<bullet> h
      - (h \<bullet> (X (rr i) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    by (rule jetu)
  have jetwr: "((\<lambda>h. (supconv (- w) \<epsilon> (xw (rr i) + h)
      - supconv (- w) \<epsilon> (xw (rr i))
      - (- Pw (rr i)) \<bullet> h - (h \<bullet> ((- Y (rr i)) *v h))/2) / (norm h)\<^sup>2)
    \<longlongrightarrow> 0) (at 0)" for i
    by (rule jetw)
  show False
    by (rule comparison_supconv_sequence_complete
        [OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw ysuOr yswOr
           symXr symYr p0 optur optwr jetur jetwr cX cY cPu cPw pnz])
qed

section \<open>The instantiation: Theorem 4.2(a) from the doubling data alone\<close>

text \<open>The assembly's hypotheses are all data of the comparison argument - the
  two viscosity properties, the scaling \<open>\<theta>\<close>, the sup-convolution
  parameter \<open>\<epsilon>\<close>, the penalty weight \<open>\<alpha>\<close>, and Jensen's geometric data
  \<open>(\<xi>,r,\<rho>,m)\<close> - plus two smallness conditions relating them; the jets,
  Hessians and gradients are all produced.  \<open>subu\<close>/\<open>subw\<close> require the
  sup-convolutions' attaining balls in \<open>\<Omega>\<close>, a genuine smallness condition
  on \<open>\<epsilon>\<close> via the explicit \<open>O(\<surd>\<epsilon>)\<close> radius of \<open>supconv_attained_ball\<close>;
  \<open>rsmall\<close> requires \<open>\<rho>\<close> small compared with \<open>c/(2\<bar>\<alpha>\<bar>)\<close> so the gradient
  lower bound survives the move to Jensen's maximiser.\<close>

lemma penalty_gradient_nearby_upper:
  fixes zh \<xi> :: "(real^'n::finite) \<times> (real^'n)"
  assumes d: "dist zh \<xi> \<le> \<rho>"
  shows "norm (\<alpha> *\<^sub>R (fst zh - snd zh))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) + 2 * \<bar>\<alpha>\<bar> * \<rho>"
proof -
  have f: "norm (fst zh - fst \<xi>) \<le> \<rho>"
  proof -
    have "norm (fst zh - fst \<xi>) = dist (fst zh) (fst \<xi>)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist zh \<xi>" by (rule dist_fst_le)
    finally show ?thesis using d by linarith
  qed
  have s: "norm (snd zh - snd \<xi>) \<le> \<rho>"
  proof -
    have "norm (snd zh - snd \<xi>) = dist (snd zh) (snd \<xi>)"
      by (simp add: dist_norm)
    also have "\<dots> \<le> dist zh \<xi>" by (rule dist_snd_le)
    finally show ?thesis using d by linarith
  qed
  have eq: "\<alpha> *\<^sub>R (fst zh - snd zh) - \<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)
      = \<alpha> *\<^sub>R ((fst zh - fst \<xi>) - (snd zh - snd \<xi>))"
    by (simp add: algebra_simps)
  have "norm (\<alpha> *\<^sub>R (fst zh - snd zh)) - norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))
      \<le> norm (\<alpha> *\<^sub>R (fst zh - snd zh) - \<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> = \<bar>\<alpha>\<bar> * norm ((fst zh - fst \<xi>) - (snd zh - snd \<xi>))"
    unfolding eq by simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (norm (fst zh - fst \<xi>) + norm (snd zh - snd \<xi>))"
    by (intro mult_left_mono norm_triangle_ineq4) simp
  also have "\<dots> \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)"
    using f s by (intro mult_left_mono) auto
  finally have "norm (\<alpha> *\<^sub>R (fst zh - snd zh))
      - norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) \<le> \<bar>\<alpha>\<bar> * (2 * \<rho>)" .
  moreover have "\<bar>\<alpha>\<bar> * (2 * \<rho>) = 2 * \<bar>\<alpha>\<bar> * \<rho>" by simp
  ultimately show ?thesis by linarith
qed

theorem comparison_supconv_doubling_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi> :: "(real^'n) \<times> (real^'n)"
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and bnd: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow> \<rho> \<le> dist y \<xi>
        \<Longrightarrow> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
              - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2 \<le> m"
    and gapm: "m < supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
              - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2"
    and subu: "\<And>x. dist x (fst \<xi>) \<le> \<rho> \<Longrightarrow>
        cball x (sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x))) + 1) \<subseteq> \<Omega>"
    and subw: "\<And>x. dist x (snd \<xi>) \<le> \<rho> \<Longrightarrow>
        cball x (sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x))) + 1) \<subseteq> \<Omega>"
    and glb: "c \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>))"
    and rsmall: "2 * \<bar>\<alpha>\<bar> * \<rho> < c"
  shows False
proof -
  have r0: "0 < r" using rho by simp
  define D where "D = (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
              - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2 - m) / (2*r)"
  have D0: "0 < D"
    unfolding D_def by (rule jensen_tilt_threshold_pos[OF gapm r0])
  have ddpos: "0 < D / (2 + real i)" for i
    by (rule tilt_sequence_pos[OF D0])
  have ddlt: "D / (2 + real i) < D" for i
    by (rule tilt_sequence_lt[OF D0])
  have dd0: "(\<lambda>i. D / (2 + real i)) \<longlonglongrightarrow> 0"
    by (rule tilt_sequence_tendsto)
  have ddlt': "D / (2 + real i)
      < (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
          - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2 - m) / (2*r)" for i
    using ddlt[of i] by (simp only: D_def)
  have small: "2 * (D / (2 + real i)) * r
      < (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>) + supconv (- w) \<epsilon> (snd \<xi>)
          - (\<alpha>/2) * (norm (fst \<xi> - snd \<xi>))\<^sup>2) - m" for i
    by (rule jensen_tilt_small_enough[OF r0 ddlt'])
  define P where "P = (\<lambda>i zh p q W.
      dist zh \<xi> < \<rho> \<and> norm p \<le> D / (2 + real i)
      \<and> (\<forall>y \<in> cball \<xi> r.
          (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + p \<bullet> y
          \<le> (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst zh) + supconv (- w) \<epsilon> (snd zh)
            - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2) + p \<bullet> zh)
      \<and> bounded_linear W \<and> (\<forall>v z. v \<bullet> W z = z \<bullet> W v)
      \<and> (\<forall>k. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) * (norm k)\<^sup>2) \<le> k \<bullet> W k)
      \<and> ((\<lambda>hk. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zh + hk))
              + supconv (- w) \<epsilon> (snd (zh + hk))
              - (\<alpha>/2) * (norm (fst (zh + hk) - snd (zh + hk)))\<^sup>2)
            - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst zh) + supconv (- w) \<epsilon> (snd zh)
              - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2)
            - q \<bullet> hk - (hk \<bullet> W hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0))"
  have H: "\<exists>zh p q W. P i zh p q W" for i
    unfolding P_def
    by (rule doubled_supconv_jet_exists
        [OF Bu Bw e a rho(1) rho(2) bnd ddpos small])
  obtain zf pf qf Wf where famP: "\<forall>i. P i (zf i) (pf i) (qf i) (Wf i)"
    using choice4[where P = P, OF H] by blast
  note fam = famP[unfolded P_def]
  have dz: "dist (zf i) \<xi> < \<rho>" for i using fam by blast  have dzle: "dist (zf i) \<xi> \<le> \<rho>" for i using dz[of i] by linarith
  have dzr: "dist (zf i) \<xi> < r" for i using dz[of i] rho(2) by linarith
  have np: "norm (pf i) \<le> D / (2 + real i)" for i using fam by blast
  have mxf: "\<And>y. y \<in> cball \<xi> r \<Longrightarrow>
      (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pf i \<bullet> y
      \<le> (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i)) + supconv (- w) \<epsilon> (snd (zf i))
        - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2) + pf i \<bullet> (zf i)" for i
    using fam by blast
  have blW: "bounded_linear (Wf i)" for i using fam by blast
  have symW: "\<And>v z. v \<bullet> Wf i z = z \<bullet> Wf i v" for i using fam by blast
  have loW: "\<And>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) * (norm hk)\<^sup>2) \<le> hk \<bullet> Wf i hk" for i
    using fam by blast
  have expf: "((\<lambda>hk. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
            + supconv (- w) \<epsilon> (snd (zf i + hk))
            - (\<alpha>/2) * (norm (fst (zf i + hk) - snd (zf i + hk)))\<^sup>2)
          - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              + supconv (- w) \<epsilon> (snd (zf i))
            - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2)
          - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using fam by blast
  have hiW: "\<And>v. v \<bullet> Wf i v \<le> 0" for i
    by (rule tilted_doubled_hessian_nonpositive
        [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
  have psdi: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))" for i
    by (rule tilted_doubled_psd_ordering
        [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW symW dzr mxf expf])
  have psdi0: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
          + (0::real) *\<^sub>R mat 1)" for i
    using psdi[of i] by simp
  have cszero: "(\<lambda>_::nat. 0::real) \<longlonglongrightarrow> 0"
    by simp
  have symX: "transpose (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))
      = matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)" for i
    by (rule transpose_matrix_block_fst[OF blW symW])
  have symY: "transpose (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
      = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))" for i
    by (rule transpose_matrix_block_snd[OF blW symW])
  have bX: "norm (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set)) * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) + \<bar>\<alpha>\<bar>)"
    for i
    by (rule norm_block_matrices_bounded(1)[OF blW symW loW hiW])
  have bY: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set)) * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha>) + \<bar>\<alpha>\<bar>)"
    for i
    by (rule norm_block_matrices_bounded(2)[OF blW symW loW hiW])
  have jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<bullet> h
        - (h \<bullet> (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using tilted_doubled_jet_slices(2)
      [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
         and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
         and q = "qf i" and W = "Wf i",
       OF blW dzr mxf expf]
    unfolding block_fst_matrix_apply[OF blW] .
  have jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
        - supconv (- w) \<epsilon> (snd (zf i))
        - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))) \<bullet> h
        - (h \<bullet> ((- matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using tilted_doubled_jet_slices(3)
      [where a = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and b = "supconv (- w) \<epsilon>"
         and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi> and r = r and pt = "pf i"
         and q = "qf i" and W = "Wf i",
       OF blW dzr mxf expf]
    unfolding block_snd_matrix_apply[OF blW] .
  have dfst: "dist (fst (zf i)) (fst \<xi>) \<le> \<rho>" for i
    using dist_fst_le[of "zf i" \<xi>] dzle[of i] by linarith
  have dsnd: "dist (snd (zf i)) (snd \<xi>) \<le> \<rho>" for i
    using dist_snd_le[of "zf i" \<xi>] dzle[of i] by linarith
  obtain ysu where ysu: "\<forall>i. ysu i \<in> \<Omega>
      \<and> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu i) - (dist (fst (zf i)) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in
      [where u = "\<lambda>y. \<theta> * u y" and xs = "\<lambda>i. fst (zf i)" and \<Omega> = \<Omega>
         and Bu = Bu and \<epsilon> = \<epsilon>,
       OF Bu e cu subu[OF dfst]]
    by blast
  obtain ysw where ysw: "\<forall>i. ysw i \<in> \<Omega>
      \<and> supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw i) - (dist (snd (zf i)) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in
      [where u = "- w" and xs = "\<lambda>i. snd (zf i)" and \<Omega> = \<Omega>
         and Bu = Bw and \<epsilon> = \<epsilon>,
       OF Bw e cw subw[OF dsnd]]
    by blast
  have bG: "norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi> - snd \<xi>)) + 2 * \<bar>\<alpha>\<bar> * \<rho>" for i
    by (rule penalty_gradient_nearby_upper[OF dzle])
  have gG: "c - 2 * \<bar>\<alpha>\<bar> * \<rho> \<le> norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))" for i
    by (rule penalty_gradient_nearby_bound[OF glb dzle])
  have cG: "0 < c - 2 * \<bar>\<alpha>\<bar> * \<rho>" using rsmall by linarith
  have pt0: "pf \<longlonglongrightarrow> 0"
    by (rule tendsto_of_norm_bound[OF np dd0])
  have au: "(\<lambda>i. (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
    using tendsto_minus[OF tendsto_fst[OF pt0]] by (simp add: zero_prod_def)
  have aw: "(\<lambda>i. (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
    using tendsto_snd[OF pt0] by (simp add: zero_prod_def)
  show False
    by (rule comparison_supconv_bounded_family
        [where u = u and w = w and \<Omega>\<^sub>u = \<Omega> and \<Omega>\<^sub>w = \<Omega>
           and \<theta> = \<theta> and \<epsilon> = \<epsilon>
           and X = "\<lambda>i. matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)"
           and Y = "\<lambda>i. matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))"
           and G = "\<lambda>i. \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and Pu = "\<lambda>i. - fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and Pw = "\<lambda>i. snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and xu = "\<lambda>i. fst (zf i)" and xw = "\<lambda>i. snd (zf i)"
           and ysu = ysu and ysw = ysw
           and cs = "\<lambda>_. 0"
           and c = "c - 2 * \<bar>\<alpha>\<bar> * \<rho>",
         OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw])
       (use ysu ysw symX symY psdi0 cszero jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

subsection \<open>Assembly 1 complete: the contradiction from the maximiser alone\<close>

text \<open>The completion: from a plain maximiser of the doubled sup-convolution
  functional at \<open>\<xi>\<^sub>0\<close> - no strict gap - plus the gradient lower bound
  there and the attainment balls, this derives \<open>False\<close>.  The strict gap
  is manufactured by the \<open>-\<delta>\<^sub>i\<parallel>z-\<xi>\<^sub>0\<parallel>\<^sup>2\<close> perturbation with
  \<open>\<delta>\<^sub>i=D\<^sub>0/(2+i) \<rightarrow> 0\<close> (\<open>shifted_jensen_family\<close>).  The three \<open>O(\<delta>\<^sub>i)\<close>
  costs - gradient shift \<open>2\<delta>\<^sub>i(\<cdot>-\<xi>\<^sub>0)\<close>, Hessian shift \<open>\<plusminus>2\<delta>\<^sub>iI\<close> with
  ordering defect \<open>4\<delta>\<^sub>i\<close>, and Hessian norm shift \<open>2D\<^sub>0\<parallel>I\<parallel>\<close> - land
  exactly where the generalised interfaces expect them.\<close>

theorem comparison_supconv_maximiser_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
  assumes sub: "visc_subsol k L \<Omega> u" and sup: "supersol_jet k L \<Omega> w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and a: "0 \<le> \<alpha>"
    and rho: "0 < \<rho>" "\<rho> < r"
    and D0: "0 < D\<^sub>0"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
          - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - (\<alpha>/2) * (norm (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))\<^sup>2"
    and radu: "\<And>x. dist x (fst \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x))) < R\<^sub>u"
    and radw: "\<And>x. dist x (snd \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x))) < R\<^sub>w"
    and subu: "\<And>x. dist x (fst \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow> cball x R\<^sub>u \<subseteq> \<Omega>"
    and subw: "\<And>x. dist x (snd \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow> cball x R\<^sub>w \<subseteq> \<Omega>"
    and glb: "c \<le> norm (\<alpha> *\<^sub>R (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "2 * \<bar>\<alpha>\<bar> * \<rho> < c"
  shows False
proof -
  have r0: "0 < r" using rho by simp
  obtain zf pf qf Wf where fam: "\<forall>i.
      dist (zf i) \<xi>\<^sub>0 < \<rho>
      \<and> norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pf i \<bullet> y
          \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2) + pf i \<bullet> (zf i))
      \<and> bounded_linear (Wf i) \<and> (\<forall>v z. v \<bullet> Wf i z = z \<bullet> Wf i v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> Wf i hk)
      \<and> ((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zf i + hk) - snd (zf i + hk)))\<^sup>2)
          - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2)
          - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using shifted_jensen_family[OF Bu Bw e a rho(1) rho(2) D0 mxK] by blast
  have dz: "dist (zf i) \<xi>\<^sub>0 < \<rho>" for i using fam by blast
  have dzle: "dist (zf i) \<xi>\<^sub>0 \<le> \<rho>" for i using dz[of i] by linarith
  have dzr: "dist (zf i) \<xi>\<^sub>0 < r" for i using dz[of i] rho(2) by linarith
  have np: "norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)" for i
    using fam by blast
  have mxf: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
      ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
          - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd y)
          - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst y - snd y))\<^sup>2) + pf i \<bullet> y
      \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2) + pf i \<bullet> (zf i)" for i
    using fam by blast
  have blW: "bounded_linear (Wf i)" for i using fam by blast
  have symW: "\<And>v z. v \<bullet> Wf i z = z \<bullet> Wf i v" for i using fam by blast
  have loW: "\<And>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
      \<le> hk \<bullet> Wf i hk" for i
    using fam by blast
  have expf: "((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst (zf i + hk) - snd (zf i + hk)))\<^sup>2)
      - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (\<alpha>/2) * (norm (fst (zf i) - snd (zf i)))\<^sup>2)
      - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using fam by blast
  have dpos: "0 < D\<^sub>0/(2 + real i)" for i by (rule tilt_sequence_pos[OF D0])
  have dlt: "D\<^sub>0/(2 + real i) < D\<^sub>0" for i by (rule tilt_sequence_lt[OF D0])
  have dfst: "dist (fst (zf i)) (fst \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_fst_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have dsnd: "dist (snd (zf i)) (snd \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_snd_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have hiW: "\<And>v. v \<bullet> Wf i v \<le> 0" for i
    by (rule tilted_doubled_hessian_nonpositive
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
  have psdU: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))" for i
    by (rule tilted_doubled_psd_ordering
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW symW dzr mxf expf])
  have psdS: "psd ((matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        - (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
            + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        + (2*(2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1)" for i
    using psdU[of i] unfolding shift_cancel_matrix .
  have cs0: "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 2*(2*(0::real))"
      by (intro tendsto_mult tendsto_const tilt_sequence_tendsto)
    then show ?thesis by simp
  qed
  have jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
           + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
        - (h \<bullet> ((matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
                + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceA: "((\<lambda>h. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) + h - fst \<xi>\<^sub>0))\<^sup>2)
        - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<bullet> h
        - (h \<bullet> (fst (Wf i (h, 0)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices(2)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
    have transA: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (fst (Wf i (h, 0)) + \<alpha> *\<^sub>R h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "fst \<xi>\<^sub>0" and xh = "fst (zf i)"
             and p = "- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
             and X = "\<lambda>h. fst (Wf i (h, 0)) + \<alpha> *\<^sub>R h",
           OF sliceA])
    show ?thesis
      using transA
      unfolding matrix_shift_apply block_fst_matrix_apply[OF blW] .
  qed
  have jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
        - supconv (- w) \<epsilon> (snd (zf i))
        - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))) \<bullet> h
        - (h \<bullet> ((- (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
                - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceB: "((\<lambda>h. ((supconv (- w) \<epsilon> (snd (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) + h - snd \<xi>\<^sub>0))\<^sup>2)
        - (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))) \<bullet> h
        - (h \<bullet> (snd (Wf i (0, h)) + \<alpha> *\<^sub>R h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices(3)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and \<alpha> = \<alpha> and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
    have transB: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
          - supconv (- w) \<epsilon> (snd (zf i))
          - (- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (snd (Wf i (0, h)) + \<alpha> *\<^sub>R h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (- w) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "snd \<xi>\<^sub>0" and xh = "snd (zf i)"
             and p = "- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))"
             and X = "\<lambda>h. snd (Wf i (0, h)) + \<alpha> *\<^sub>R h",
           OF sliceB])
    have negPw: "- (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = - (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have negY: "- (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        = (- matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
          + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      using transB
      unfolding negPw negY matrix_shift_apply block_snd_matrix_apply[OF blW] .
  qed
  have symXs: "transpose (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
    by (rule transpose_shifted_block
        [OF transpose_matrix_block_fst[OF blW symW]])
  have symYs: "transpose (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      unfolding eqm
      by (rule transpose_shifted_block
          [OF transpose_matrix_block_snd[OF blW symW]])
  qed
  have bXun: "norm (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>)" for i
    by (rule norm_block_matrices_bounded(1)[OF blW symW loW hiW])
  have bYun: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v)))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>)" for i
    by (rule norm_block_matrices_bounded(2)[OF blW symW loW hiW])
  have Cuni: "real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>)
      \<le> real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>)" for i
  proof -
    have "(1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*(D\<^sub>0/(2 + real i))) + \<bar>\<alpha>\<bar>
        \<le> (1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>"
      using dlt[of i] by linarith
    then show ?thesis by (rule mult_left_mono) simp
  qed
  have habs: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)
      \<le> 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have e1: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> = 2*(D\<^sub>0/(2 + real i))"
      using D0 by simp
    have e2: "2*(D\<^sub>0/(2 + real i)) \<le> 2*D\<^sub>0"
      using dlt[of i] by linarith
    show ?thesis
      unfolding e1 by (rule mult_right_mono[OF e2]) simp
  qed
  have bX: "norm (matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
    using norm_shifted_block
        [where M = "matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)"
           and c = "2*(D\<^sub>0/(2 + real i))"]
      bXun[of i] Cuni[of i] habs[of i]
    by linarith
  have bY: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<alpha> + 2*D\<^sub>0) + \<bar>\<alpha>\<bar>)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    have h2: "\<bar>- (2*(D\<^sub>0/(2 + real i)))\<bar> * norm (mat 1 :: real^'n^'n)
        = \<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)"
      by simp
    show ?thesis
      unfolding eqm
      using norm_shifted_block
          [where M = "matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))"
             and c = "- (2*(D\<^sub>0/(2 + real i)))"]
        h2 bYun[of i] Cuni[of i] habs[of i]
      by linarith
  qed
  obtain ysu where ysu: "\<forall>i. ysu i \<in> \<Omega>
      \<and> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu i) - (dist (fst (zf i)) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in_rad
      [where u = "\<lambda>y. \<theta> * u y" and xs = "\<lambda>i. fst (zf i)" and \<Omega> = \<Omega>
         and Bu = Bu and \<epsilon> = \<epsilon> and R = R\<^sub>u,
       OF Bu e cu radu[OF dfst] subu[OF dfst]]
    by blast
  obtain ysw where ysw: "\<forall>i. ysw i \<in> \<Omega>
      \<and> supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw i) - (dist (snd (zf i)) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_family_in_rad
      [where u = "- w" and xs = "\<lambda>i. snd (zf i)" and \<Omega> = \<Omega>
         and Bu = Bw and \<epsilon> = \<epsilon> and R = R\<^sub>w,
       OF Bw e cw radw[OF dsnd] subw[OF dsnd]]
    by blast
  have nfst: "norm (fst (pf i)) \<le> norm (pf i)" for i
    using norm_fst_le[of "fst (pf i)" "snd (pf i)"] by simp
  have nsnd: "norm (snd (pf i)) \<le> norm (pf i)" for i
    using norm_snd_le[where x = "fst (pf i)" and y = "snd (pf i)"] by simp
  have nshiftA: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (fst (zf i)) (fst \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dfst p2])
    finally show ?thesis .
  qed
  have nshiftB: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (snd (zf i)) (snd \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dsnd p2])
    finally show ?thesis .
  qed
  have Elim: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)
      + 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
  proof -
    have l1: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)) \<longlonglongrightarrow> 0"
      by (rule shifted_family_parameters(5)[OF D0 rho(1) r0])
    have l2: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
    proof -
      have h: "(\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i))) \<longlonglongrightarrow> (2*\<rho>) * 0"
        by (rule tendsto_mult[OF tendsto_const tilt_sequence_tendsto])
      have eq: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>)
          = (\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i)))"
        by (rule ext) (simp add: mult_ac)
      show ?thesis unfolding eq using h by simp
    qed
    from tendsto_add[OF l1 l2] show ?thesis by simp
  qed
  have au: "(\<lambda>i. (- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        = (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0) - fst (pf i)"
      by simp
    have tri: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)
          - fst (pf i))
        \<le> norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
          + norm (fst (pf i))"
      by (rule norm_triangle_ineq4)
    show "norm ((- fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftA[of i] nfst[of i] np[of i] by linarith
  qed
  have aw: "(\<lambda>i. (snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
        = snd (pf i) - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have tri: "norm (snd (pf i)
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        \<le> norm (snd (pf i))
          + norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))"
      by (rule norm_triangle_ineq4)
    show "norm ((snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - \<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftB[of i] nsnd[of i] np[of i] by linarith
  qed
  have bG: "norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))
      \<le> norm (\<alpha> *\<^sub>R (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)) + 2 * \<bar>\<alpha>\<bar> * \<rho>" for i
    by (rule penalty_gradient_nearby_upper[OF dzle])
  have gG: "c - 2 * \<bar>\<alpha>\<bar> * \<rho> \<le> norm (\<alpha> *\<^sub>R (fst (zf i) - snd (zf i)))" for i
    by (rule penalty_gradient_nearby_bound[OF glb dzle])
  have cG: "0 < c - 2 * \<bar>\<alpha>\<bar> * \<rho>" using rsmall by linarith
  show False
    by (rule comparison_supconv_bounded_family
        [where u = u and w = w and \<Omega>\<^sub>u = \<Omega> and \<Omega>\<^sub>w = \<Omega>
           and \<theta> = \<theta> and \<epsilon> = \<epsilon>
           and X = "\<lambda>i. matrix (\<lambda>v. fst (Wf i (v, 0)) + \<alpha> *\<^sub>R v)
              + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and Y = "\<lambda>i. matrix (\<lambda>v. - (snd (Wf i (0, v)) + \<alpha> *\<^sub>R v))
              - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and G = "\<lambda>i. \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))"
           and Pu = "\<lambda>i. - fst (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
              + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)"
           and Pw = "\<lambda>i. snd (pf i) + \<alpha> *\<^sub>R (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
           and xu = "\<lambda>i. fst (zf i)" and xw = "\<lambda>i. snd (zf i)"
           and ysu = ysu and ysw = ysw
           and cs = "\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))"
           and c = "c - 2 * \<bar>\<alpha>\<bar> * \<rho>",
         OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw])
       (use ysu ysw symXs symYs psdS cs0 jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

text \<open>The four block-matrix helpers under a general Hessian block \<open>Z\<close>: each
  is the corresponding lemma with \<open>\<alpha> *\<^sub>R v\<close> replaced by \<open>Z *v v\<close>, the
  symmetry pair additionally needing \<open>Z\<close> symmetric.\<close>

lemma block_fst_matrix_apply_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "matrix (\<lambda>v. fst (W (v, 0)) + Z *v v) *v h
       = fst (W (h, 0)) + Z *v h"
  by (rule matrix_vec_apply[OF linear_block_fst_gen[OF blW]])

lemma block_snd_matrix_apply_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
  shows "(- matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))) *v h
       = snd (W (0, h)) + Z *v h"
proof -
  have l: "linear (\<lambda>v. - (snd (W (0, v)) + Z *v v))"
    by (rule linear_block_snd_gen[OF blW])
  have "(- matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))) *v h
      = - (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)) *v h)"
    by (rule matrix_vector_neg_left)
  also have "\<dots> = - (- (snd (W (0, h)) + Z *v h))"
    using matrix_vec_apply[OF l] by simp
  finally show ?thesis by simp
qed

lemma transpose_matrix_block_fst_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "transpose (matrix (\<lambda>v. fst (W (v, 0)) + Z *v v))
       = matrix (\<lambda>v. fst (W (v, 0)) + Z *v v)"
  by (rule matrix_of_symmetric[OF linear_block_fst_gen[OF blW]
        sym_block_fst_gen[OF symW symZ]])

lemma transpose_matrix_block_snd_gen:
  fixes W :: "(real^'n::finite) \<times> (real^'n) \<Rightarrow> (real^'n) \<times> (real^'n)"
    and Z :: "real^'n^'n"
  assumes blW: "bounded_linear W"
    and symW: "\<And>u u'. u \<bullet> W u' = u' \<bullet> W u"
    and symZ: "transpose Z = Z"
  shows "transpose (matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v)))
       = matrix (\<lambda>v. - (snd (W (0, v)) + Z *v v))"
  by (rule matrix_of_symmetric[OF linear_block_snd_gen[OF blW]
        sym_block_snd_gen[OF symW symZ]])

text \<open>Two locality facts about the penalty gradient for a general penalty:
  the quadratic penalty's gradient \<open>\<alpha> *\<^sub>R d\<close> is \<open>\<bar>\<alpha>\<bar>\<close>-Lipschitz; in
  general a Lipschitz bound \<open>KG\<close> on the gradient field \<open>Gf\<close> is assumed
  instead, with the displacement \<open>d\<close> moving by at most \<open>2\<rho>\<close> as in the
  quadratic case.\<close>

lemma diff_displacement_bound:
  fixes zh \<xi> :: "(real^'n::finite) \<times> (real^'n)"
  assumes d: "dist zh \<xi> \<le> \<rho>"
  shows "norm ((fst zh - snd zh) - (fst \<xi> - snd \<xi>)) \<le> 2*\<rho>"
proof -
  have e: "(fst zh - snd zh) - (fst \<xi> - snd \<xi>)
      = (fst zh - fst \<xi>) - (snd zh - snd \<xi>)" by simp
  have "norm ((fst zh - fst \<xi>) - (snd zh - snd \<xi>))
      \<le> norm (fst zh - fst \<xi>) + norm (snd zh - snd \<xi>)"
    by (rule norm_triangle_ineq4)
  moreover have "norm (fst zh - fst \<xi>) \<le> \<rho>"
    using dist_fst_le[of zh \<xi>] d by (simp add: dist_norm)
  moreover have "norm (snd zh - snd \<xi>) \<le> \<rho>"
    using dist_snd_le[of zh \<xi>] d by (simp add: dist_norm)
  ultimately show ?thesis unfolding e by linarith
qed

lemma penalty_gradient_nearby_upper_gen:
  fixes zh \<xi> :: "(real^'n::finite) \<times> (real^'n)" and Gf :: "real^'n \<Rightarrow> real^'n"
  assumes d: "dist zh \<xi> \<le> \<rho>"
    and lip: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KG: "0 \<le> KG"
  shows "norm (Gf (fst zh - snd zh)) \<le> norm (Gf (fst \<xi> - snd \<xi>)) + KG * (2*\<rho>)"
proof -
  have "norm (Gf (fst zh - snd zh)) - norm (Gf (fst \<xi> - snd \<xi>))
      \<le> norm (Gf (fst zh - snd zh) - Gf (fst \<xi> - snd \<xi>))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> \<le> KG * norm ((fst zh - snd zh) - (fst \<xi> - snd \<xi>))"
    by (rule lip)
  also have "\<dots> \<le> KG * (2*\<rho>)"
    by (rule mult_left_mono[OF diff_displacement_bound[OF d] KG])
  finally show ?thesis by linarith
qed

lemma penalty_gradient_nearby_bound_gen:
  fixes zh \<xi> :: "(real^'n::finite) \<times> (real^'n)" and Gf :: "real^'n \<Rightarrow> real^'n"
  assumes c: "c \<le> norm (Gf (fst \<xi> - snd \<xi>))"
    and d: "dist zh \<xi> \<le> \<rho>"
    and lip: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KG: "0 \<le> KG"
  shows "c - KG * (2*\<rho>) \<le> norm (Gf (fst zh - snd zh))"
proof -
  have "norm (Gf (fst \<xi> - snd \<xi>)) - norm (Gf (fst zh - snd zh))
      \<le> norm (Gf (fst \<xi> - snd \<xi>) - Gf (fst zh - snd zh))"
    by (rule norm_triangle_ineq2)
  also have "\<dots> \<le> KG * norm ((fst \<xi> - snd \<xi>) - (fst zh - snd zh))"
    by (rule lip)
  also have "norm ((fst \<xi> - snd \<xi>) - (fst zh - snd zh))
      = norm ((fst zh - snd zh) - (fst \<xi> - snd \<xi>))"
    by (rule norm_minus_commute)
  finally have "norm (Gf (fst \<xi> - snd \<xi>)) - norm (Gf (fst zh - snd zh))
      \<le> KG * (2*\<rho>)"
    using mult_left_mono[OF diff_displacement_bound[OF d] KG] by linarith
  then show ?thesis using c by linarith
qed

text \<open>\<open>comparison_supconv_maximiser_complete\<close> generalised: the quadratic
  penalty \<open>(\<alpha>/2)(norm d)\<^sup>2\<close> becomes an arbitrary \<open>Pn\<close> that is
  \<open>\<kappa>\<close>-semiconcave with gradient field \<open>Gf\<close> and Hessian field \<open>Zf\<close>,
  evaluated at the displacement \<open>d\<close> of the \<open>i\<close>-th maximiser.  Jensen's
  tilt is genuinely quadratic and not part of the penalty, so
  \<open>jet_transfer_quadratic\<close> still applies; the consumer
  \<open>comparison_supconv_bounded_family\<close> is penalty-agnostic and reused
  verbatim.\<close>

theorem comparison_supconv_maximiser_complete_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
    and Pn :: "real^'n \<Rightarrow> real"
    and Gf :: "real^'n \<Rightarrow> real^'n" and Zf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes sub: "visc_subsol k L \<Omega>\<^sub>u u" and sup: "supersol_jet k L \<Omega>\<^sub>w w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and kap: "0 \<le> \<kappa>"
    and sc: "convex_on UNIV (\<lambda>d. (\<kappa>/2) * (norm d)\<^sup>2 - Pn d)"
    and Pjet: "\<And>d. ((\<lambda>h. (Pn (d + h) - Pn d - Gf d \<bullet> h
          - (h \<bullet> (Zf d *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and symZ: "\<And>d. transpose (Zf d) = Zf d"
    and bZ: "\<And>d z. \<bar>z \<bullet> (Zf d *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
    and lipG: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KGnn: "0 \<le> KG"
    and rho: "0 < \<rho>" "\<rho> < r"
    and D0: "0 < D\<^sub>0"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and mxK: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y) + supconv (- w) \<epsilon> (snd y)
          - Pn (fst y - snd y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and atu: "\<And>x z. dist x (fst \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)
        \<Longrightarrow> z \<in> \<Omega>\<^sub>u"
    and atw: "\<And>x z. dist x (snd \<xi>\<^sub>0) \<le> \<rho> \<Longrightarrow>
        supconv (- w) \<epsilon> x = (- w) z - (dist x z)\<^sup>2 / (2*\<epsilon>)
        \<Longrightarrow> z \<in> \<Omega>\<^sub>w"
    and glb: "c \<le> norm (Gf (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "KG * (2*\<rho>) < c"
  shows False
proof -
  have r0: "0 < r" using rho by simp
  obtain zf pf qf Wf where fam: "\<forall>i.
      dist (zf i) \<xi>\<^sub>0 < \<rho>
      \<and> norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)
      \<and> (\<forall>y \<in> cball \<xi>\<^sub>0 r.
          ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
              - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd y)
              - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst y - snd y)) + pf i \<bullet> y
          \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zf i) - snd (zf i))) + pf i \<bullet> (zf i))
      \<and> bounded_linear (Wf i) \<and> (\<forall>v z. v \<bullet> Wf i z = z \<bullet> Wf i v)
      \<and> (\<forall>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
            \<le> hk \<bullet> Wf i hk)
      \<and> ((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i + hk))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zf i + hk) - snd (zf i + hk)))
          - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
            + (supconv (- w) \<epsilon> (snd (zf i))
              - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
            - Pn (fst (zf i) - snd (zf i)))
          - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    using shifted_jensen_family_gen[OF Bu Bw e kap sc rho(1) rho(2) D0 mxK]
    by blast
  have dz: "dist (zf i) \<xi>\<^sub>0 < \<rho>" for i using fam by blast
  have dzle: "dist (zf i) \<xi>\<^sub>0 \<le> \<rho>" for i using dz[of i] by linarith
  have dzr: "dist (zf i) \<xi>\<^sub>0 < r" for i using dz[of i] rho(2) by linarith
  have np: "norm (pf i) \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2 / (4*r)" for i
    using fam by blast
  have mxf: "\<And>y. y \<in> cball \<xi>\<^sub>0 r \<Longrightarrow>
      ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst y)
          - (D\<^sub>0/(2 + real i)) * (norm (fst y - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd y)
          - (D\<^sub>0/(2 + real i)) * (norm (snd y - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst y - snd y)) + pf i \<bullet> y
      \<le> ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst (zf i) - snd (zf i))) + pf i \<bullet> (zf i)" for i
    using fam by blast
  have blW: "bounded_linear (Wf i)" for i using fam by blast
  have symW: "\<And>v z. v \<bullet> Wf i z = z \<bullet> Wf i v" for i using fam by blast
  have loW: "\<And>hk. - ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) * (norm hk)\<^sup>2)
      \<le> hk \<bullet> Wf i hk" for i
    using fam by blast
  have expf: "((\<lambda>hk. (((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i + hk) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i + hk))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i + hk) - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst (zf i + hk) - snd (zf i + hk)))
      - ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        + (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - Pn (fst (zf i) - snd (zf i)))
      - qf i \<bullet> hk - (hk \<bullet> Wf i hk)/2) / (norm hk)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
    using fam by blast
  have dpos: "0 < D\<^sub>0/(2 + real i)" for i by (rule tilt_sequence_pos[OF D0])
  have dlt: "D\<^sub>0/(2 + real i) < D\<^sub>0" for i by (rule tilt_sequence_lt[OF D0])
  have dfst: "dist (fst (zf i)) (fst \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_fst_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have dsnd: "dist (snd (zf i)) (snd \<xi>\<^sub>0) \<le> \<rho>" for i
    using dist_snd_le[of "zf i" \<xi>\<^sub>0] dzle[of i] by linarith
  have hiW: "\<And>v. v \<bullet> Wf i v \<le> 0" for i
    by (rule tilted_doubled_hessian_nonpositive_gen
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and P = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i",
         OF blW dzr mxf expf])
  have psdU: "psd (matrix (\<lambda>v. - (snd (Wf i (0, v))
            + Zf (fst (zf i) - snd (zf i)) *v v))
          - matrix (\<lambda>v. fst (Wf i (v, 0))
            + Zf (fst (zf i) - snd (zf i)) *v v))" for i
    by (rule tilted_doubled_psd_ordering_gen
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and Pn = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i"
           and Z = "Zf (fst (zf i) - snd (zf i))"
           and G = "Gf (fst (zf i) - snd (zf i))",
         OF blW symW symZ dzr mxf expf Pjet])
  have psdS: "psd ((matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        - (matrix (\<lambda>v. fst (Wf i (v, 0))
              + Zf (fst (zf i) - snd (zf i)) *v v)
            + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        + (2*(2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1)" for i
    using psdU[of i] unfolding shift_cancel_matrix .
  have cs0: "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))) \<longlonglongrightarrow> 2*(2*(0::real))"
      by (intro tendsto_mult tendsto_const tilt_sequence_tendsto)
    then show ?thesis by simp
  qed
  have jetu: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
        - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        - (- fst (pf i) + Gf (fst (zf i) - snd (zf i))
           + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
        - (h \<bullet> ((matrix (\<lambda>v. fst (Wf i (v, 0))
                    + Zf (fst (zf i) - snd (zf i)) *v v)
                + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceA: "((\<lambda>h. ((supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) + h - fst \<xi>\<^sub>0))\<^sup>2)
        - (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (fst (zf i) - fst \<xi>\<^sub>0))\<^sup>2)
        - (- fst (pf i) + Gf (fst (zf i) - snd (zf i))) \<bullet> h
        - (h \<bullet> (fst (Wf i (h, 0))
              + Zf (fst (zf i) - snd (zf i)) *v h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices_gen(2)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and P = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i"
           and Z = "Zf (fst (zf i) - snd (zf i))"
           and G = "Gf (fst (zf i) - snd (zf i))",
         OF blW dzr mxf expf Pjet])
    have transA: "((\<lambda>h. (supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i) + h)
          - supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
          - (- fst (pf i) + Gf (fst (zf i) - snd (zf i))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (fst (Wf i (h, 0)) + Zf (fst (zf i) - snd (zf i)) *v h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "fst \<xi>\<^sub>0" and xh = "fst (zf i)"
             and p = "- fst (pf i) + Gf (fst (zf i) - snd (zf i))"
             and X = "\<lambda>h. fst (Wf i (h, 0))
                + Zf (fst (zf i) - snd (zf i)) *v h",
           OF sliceA])
    show ?thesis
      using transA
      unfolding matrix_shift_apply block_fst_matrix_apply_gen[OF blW] .
  qed
  have jetw: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
        - supconv (- w) \<epsilon> (snd (zf i))
        - (- (snd (pf i) + Gf (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))) \<bullet> h
        - (h \<bullet> ((- (matrix (\<lambda>v. - (snd (Wf i (0, v))
                      + Zf (fst (zf i) - snd (zf i)) *v v))
                - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)) *v h))/2)
        / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)" for i
  proof -
    have sliceB: "((\<lambda>h. ((supconv (- w) \<epsilon> (snd (zf i) + h)
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) + h - snd \<xi>\<^sub>0))\<^sup>2)
        - (supconv (- w) \<epsilon> (snd (zf i))
          - (D\<^sub>0/(2 + real i)) * (norm (snd (zf i) - snd \<xi>\<^sub>0))\<^sup>2)
        - (- (snd (pf i) + Gf (fst (zf i) - snd (zf i)))) \<bullet> h
        - (h \<bullet> (snd (Wf i (0, h))
              + Zf (fst (zf i) - snd (zf i)) *v h))/2) / (norm h)\<^sup>2)
        \<longlongrightarrow> 0) (at 0)"
      by (rule tilted_doubled_jet_slices_gen(3)
        [where a = "\<lambda>x. supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - fst \<xi>\<^sub>0))\<^sup>2"
           and b = "\<lambda>x. supconv (- w) \<epsilon> x
              - (D\<^sub>0/(2 + real i)) * (norm (x - snd \<xi>\<^sub>0))\<^sup>2"
           and P = Pn and zh = "zf i" and \<xi> = \<xi>\<^sub>0 and r = r and pt = "pf i"
           and q = "qf i" and W = "Wf i"
           and Z = "Zf (fst (zf i) - snd (zf i))"
           and G = "Gf (fst (zf i) - snd (zf i))",
         OF blW dzr mxf expf Pjet])
    have transB: "((\<lambda>h. (supconv (- w) \<epsilon> (snd (zf i) + h)
          - supconv (- w) \<epsilon> (snd (zf i))
          - (- (snd (pf i) + Gf (fst (zf i) - snd (zf i)))
             + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)) \<bullet> h
          - (h \<bullet> (snd (Wf i (0, h)) + Zf (fst (zf i) - snd (zf i)) *v h
                  + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R h))/2)
          / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
      by (rule jet_transfer_quadratic
          [where f = "supconv (- w) \<epsilon>" and \<delta> = "D\<^sub>0/(2 + real i)"
             and c = "snd \<xi>\<^sub>0" and xh = "snd (zf i)"
             and p = "- (snd (pf i) + Gf (fst (zf i) - snd (zf i)))"
             and X = "\<lambda>h. snd (Wf i (0, h))
                + Zf (fst (zf i) - snd (zf i)) *v h",
           OF sliceB])
    have negPw: "- (snd (pf i) + Gf (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = - (snd (pf i) + Gf (fst (zf i) - snd (zf i)))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have negY: "- (matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
        = (- matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v)))
          + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      using transB
      unfolding negPw negY matrix_shift_apply
        block_snd_matrix_apply_gen[OF blW] .
  qed
  have symXs: "transpose (matrix (\<lambda>v. fst (Wf i (v, 0))
          + Zf (fst (zf i) - snd (zf i)) *v v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. fst (Wf i (v, 0)) + Zf (fst (zf i) - snd (zf i)) *v v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
    by (rule transpose_shifted_block
        [OF transpose_matrix_block_fst_gen[OF blW symW symZ]])
  have symYs: "transpose (matrix (\<lambda>v. - (snd (Wf i (0, v))
            + Zf (fst (zf i) - snd (zf i)) *v v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      = matrix (\<lambda>v. - (snd (Wf i (0, v))
            + Zf (fst (zf i) - snd (zf i)) *v v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    show ?thesis
      unfolding eqm
      by (rule transpose_shifted_block
          [OF transpose_matrix_block_snd_gen[OF blW symW symZ]])
  qed
  have bXun: "norm (matrix (\<lambda>v. fst (Wf i (v, 0))
        + Zf (fst (zf i) - snd (zf i)) *v v))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ)" for i
    by (rule norm_block_matrices_bounded_gen(1)[OF blW symW symZ loW hiW bZ])
  have bYun: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v))
        + Zf (fst (zf i) - snd (zf i)) *v v)))
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ)" for i
    by (rule norm_block_matrices_bounded_gen(2)[OF blW symW symZ loW hiW bZ])
  have Cuni: "real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ)
      \<le> real (card (Basis :: (real^'n^'n) set))
        * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ)" for i
  proof -
    have "(1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*(D\<^sub>0/(2 + real i))) + KZ
        \<le> (1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ"
      using dlt[of i] by linarith
    then show ?thesis by (rule mult_left_mono) simp
  qed
  have habs: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)
      \<le> 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have e1: "\<bar>2*(D\<^sub>0/(2 + real i))\<bar> = 2*(D\<^sub>0/(2 + real i))"
      using D0 by simp
    have e2: "2*(D\<^sub>0/(2 + real i)) \<le> 2*D\<^sub>0"
      using dlt[of i] by linarith
    show ?thesis
      unfolding e1 by (rule mult_right_mono[OF e2]) simp
  qed
  have bX: "norm (matrix (\<lambda>v. fst (Wf i (v, 0))
          + Zf (fst (zf i) - snd (zf i)) *v v)
        + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
    using norm_shifted_block
        [where M = "matrix (\<lambda>v. fst (Wf i (v, 0))
            + Zf (fst (zf i) - snd (zf i)) *v v)"
           and c = "2*(D\<^sub>0/(2 + real i))"]
      bXun[of i] Cuni[of i] habs[of i]
    by linarith
  have bY: "norm (matrix (\<lambda>v. - (snd (Wf i (0, v))
          + Zf (fst (zf i) - snd (zf i)) *v v))
        - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1)
      \<le> real (card (Basis :: (real^'n^'n) set))
          * ((1/\<epsilon> + 1/\<epsilon> + 2*\<kappa> + 2*D\<^sub>0) + KZ)
        + 2*D\<^sub>0 * norm (mat 1 :: real^'n^'n)" for i
  proof -
    have eqm: "matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1
        = matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))
          + (- (2*(D\<^sub>0/(2 + real i)))) *\<^sub>R mat 1"
      by simp
    have h2: "\<bar>- (2*(D\<^sub>0/(2 + real i)))\<bar> * norm (mat 1 :: real^'n^'n)
        = \<bar>2*(D\<^sub>0/(2 + real i))\<bar> * norm (mat 1 :: real^'n^'n)"
      by simp
    show ?thesis
      unfolding eqm
      using norm_shifted_block
          [where M = "matrix (\<lambda>v. - (snd (Wf i (0, v))
              + Zf (fst (zf i) - snd (zf i)) *v v))"
             and c = "- (2*(D\<^sub>0/(2 + real i)))"]
        h2 bYun[of i] Cuni[of i] habs[of i]
      by linarith
  qed
  obtain ysu0 where ysu0: "\<And>i. supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu0 i) - (dist (fst (zf i)) (ysu0 i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_family
      [where u = "\<lambda>y. \<theta> * u y" and xs = "\<lambda>i. fst (zf i)"
         and Bu = Bu and \<epsilon> = \<epsilon>, OF Bu e uu]
    by blast
  define ysu where "ysu = ysu0"
  have ysu: "\<forall>i. ysu i \<in> \<Omega>\<^sub>u
      \<and> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (zf i))
        = \<theta> * u (ysu i) - (dist (fst (zf i)) (ysu i))\<^sup>2 / (2*\<epsilon>)"
    unfolding ysu_def using ysu0 atu[OF dfst] by blast
  obtain ysw0 where ysw0: "\<And>i. supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw0 i) - (dist (snd (zf i)) (ysw0 i))\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_family
      [where u = "- w" and xs = "\<lambda>i. snd (zf i)"
         and Bu = Bw and \<epsilon> = \<epsilon>, OF Bw e uw]
    by blast
  define ysw where "ysw = ysw0"
  have ysw: "\<forall>i. ysw i \<in> \<Omega>\<^sub>w
      \<and> supconv (- w) \<epsilon> (snd (zf i))
        = (- w) (ysw i) - (dist (snd (zf i)) (ysw i))\<^sup>2 / (2*\<epsilon>)"
    unfolding ysw_def using ysw0 atw[OF dsnd] by blast
  have nfst: "norm (fst (pf i)) \<le> norm (pf i)" for i
    using norm_fst_le[of "fst (pf i)" "snd (pf i)"] by simp
  have nsnd: "norm (snd (pf i)) \<le> norm (pf i)" for i
    using norm_snd_le[where x = "fst (pf i)" and y = "snd (pf i)"] by simp
  have nshiftA: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (fst (zf i)) (fst \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dfst p2])
    finally show ?thesis .
  qed
  have nshiftB: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>" for i
  proof -
    have p2: "0 \<le> 2*(D\<^sub>0/(2 + real i))" using dpos[of i] by linarith
    have "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        = 2*(D\<^sub>0/(2 + real i)) * dist (snd (zf i)) (snd \<xi>\<^sub>0)"
      using p2 D0 by (simp add: dist_norm)
    also have "\<dots> \<le> 2*(D\<^sub>0/(2 + real i)) * \<rho>"
      by (rule mult_left_mono[OF dsnd p2])
    finally show ?thesis .
  qed
  have Elim: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)
      + 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
  proof -
    have l1: "(\<lambda>i. D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r)) \<longlonglongrightarrow> 0"
      by (rule shifted_family_parameters(5)[OF D0 rho(1) r0])
    have l2: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>) \<longlonglongrightarrow> 0"
    proof -
      have h: "(\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i))) \<longlonglongrightarrow> (2*\<rho>) * 0"
        by (rule tendsto_mult[OF tendsto_const tilt_sequence_tendsto])
      have eq: "(\<lambda>i. 2*(D\<^sub>0/(2 + real i))*\<rho>)
          = (\<lambda>i. (2*\<rho>) * (D\<^sub>0/(2 + real i)))"
        by (rule ext) (simp add: mult_ac)
      show ?thesis unfolding eq using h by simp
    qed
    from tendsto_add[OF l1 l2] show ?thesis by simp
  qed
  have au: "(\<lambda>i. (- fst (pf i) + Gf (fst (zf i) - snd (zf i))
        + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
      - Gf (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(- fst (pf i) + Gf (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i))
        = (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0) - fst (pf i)"
      by simp
    have tri: "norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)
          - fst (pf i))
        \<le> norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
          + norm (fst (pf i))"
      by (rule norm_triangle_ineq4)
    show "norm ((- fst (pf i) + Gf (fst (zf i) - snd (zf i))
          + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftA[of i] nfst[of i] np[of i] by linarith
  qed
  have aw: "(\<lambda>i. (snd (pf i) + Gf (fst (zf i) - snd (zf i))
        - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
      - Gf (fst (zf i) - snd (zf i))) \<longlonglongrightarrow> 0"
  proof (rule tendsto_of_norm_bound[OF _ Elim])
    fix i
    have eq0: "(snd (pf i) + Gf (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i))
        = snd (pf i) - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
      by simp
    have tri: "norm (snd (pf i)
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        \<le> norm (snd (pf i))
          + norm ((2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))"
      by (rule norm_triangle_ineq4)
    show "norm ((snd (pf i) + Gf (fst (zf i) - snd (zf i))
          - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0))
        - Gf (fst (zf i) - snd (zf i)))
        \<le> D\<^sub>0/(2 + real i) * \<rho>\<^sup>2/(4*r) + 2*(D\<^sub>0/(2 + real i))*\<rho>"
      unfolding eq0
      using tri nshiftB[of i] nsnd[of i] np[of i] by linarith
  qed
  have bG: "norm (Gf (fst (zf i) - snd (zf i)))
      \<le> norm (Gf (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)) + KG * (2*\<rho>)" for i
    by (rule penalty_gradient_nearby_upper_gen[OF dzle lipG KGnn])
  have gG: "c - KG * (2*\<rho>) \<le> norm (Gf (fst (zf i) - snd (zf i)))" for i
    by (rule penalty_gradient_nearby_bound_gen[OF glb dzle lipG KGnn])
  have cG: "0 < c - KG * (2*\<rho>)" using rsmall by linarith
  show False
    by (rule comparison_supconv_bounded_family
        [where u = u and w = w and \<Omega>\<^sub>u = \<Omega>\<^sub>u and \<Omega>\<^sub>w = \<Omega>\<^sub>w
           and \<theta> = \<theta> and \<epsilon> = \<epsilon>
           and X = "\<lambda>i. matrix (\<lambda>v. fst (Wf i (v, 0))
                + Zf (fst (zf i) - snd (zf i)) *v v)
              + (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and Y = "\<lambda>i. matrix (\<lambda>v. - (snd (Wf i (0, v))
                + Zf (fst (zf i) - snd (zf i)) *v v))
              - (2*(D\<^sub>0/(2 + real i))) *\<^sub>R mat 1"
           and G = "\<lambda>i. Gf (fst (zf i) - snd (zf i))"
           and Pu = "\<lambda>i. - fst (pf i) + Gf (fst (zf i) - snd (zf i))
              + (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (fst (zf i) - fst \<xi>\<^sub>0)"
           and Pw = "\<lambda>i. snd (pf i) + Gf (fst (zf i) - snd (zf i))
              - (2 * (D\<^sub>0/(2 + real i))) *\<^sub>R (snd (zf i) - snd \<xi>\<^sub>0)"
           and xu = "\<lambda>i. fst (zf i)" and xw = "\<lambda>i. snd (zf i)"
           and ysu = ysu and ysw = ysw
           and cs = "\<lambda>i. 2*(2*(D\<^sub>0/(2 + real i)))"
           and c = "c - KG * (2*\<rho>)",
         OF sub sup t(1) t(2) kk(1) kk(2) LL e Bu Bw])
       (use ysu ysw symXs symYs psdS cs0 jetu jetw au aw bX bY bG gG cG
        in blast)+
qed

section \<open>The \<open>max_principle_boundary\<close> interface needs continuity: the raw version is refutable\<close>

text \<open>\<open>max_principle_boundary k L K\<close> (@{theory Relative_Arbitrage.Operator_Envelope_Continuity}) as originally
  stated, quantifying over all \<open>u\<close>, \<open>w\<close> satisfying \<open>visc_subsol\<close>/
  \<open>supersol_jet\<close> on \<open>interior K\<close> with no semicontinuity or boundedness,
  is false: those local conditions say nothing about the boundary values
  of \<open>u\<close> and \<open>w\<close>, which can be moved to destroy any boundary maximum of
  \<open>u - w\<close> (\<open>visc_supersol_cong_on\<close>, \<open>max_principle_boundary_counterexample\<close>).
  The paper's Theorem 4.2(a) needs \<open>u\<close> upper semicontinuous and \<open>w\<close>
  lower semicontinuous on \<open>K\<close>, which is also what makes \<open>u-w\<close> attain a
  maximum on compact \<open>K\<close> at all.\<close>

lemma visc_subsol_cong_on:
  fixes u u' :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_subsol k L \<Omega> u" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> u' y = u y"
  shows "visc_subsol k L \<Omega> u'"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and loc: "\<exists>e>0. \<forall>y \<in> ball x e. u' y - \<phi> y \<le> u' x - \<phi> x"
  from loc obtain e where e0: "0 < e"
    and le: "\<And>y. y \<in> ball x e \<Longrightarrow> u' y - \<phi> y \<le> u' x - \<phi> x" by blast
  from op x obtain d where d0: "0 < d" and dsub: "ball x d \<subseteq> \<Omega>"
    using open_contains_ball by blast
  have loc': "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  proof (intro exI[of _ "min e d"] conjI ballI)
    show "0 < min e d" using e0 d0 by simp
    fix y assume y: "y \<in> ball x (min e d)"
    then have ye: "y \<in> ball x e" and yd: "y \<in> ball x d" by auto
    have "u y - \<phi> y = u' y - \<phi> y" using eq[OF subsetD[OF dsub yd]] by simp
    also have "\<dots> \<le> u' x - \<phi> x" by (rule le[OF ye])
    also have "\<dots> = u x - \<phi> x" using eq[OF x] by simp
    finally show "u y - \<phi> y \<le> u x - \<phi> x" .
  qed
  from s x tf loc' show "ell_op k L (g x) H \<le> 1"
    unfolding visc_subsol_def by blast
qed

lemma visc_supersol_cong_on:
  fixes w w' :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_supersol k L \<Omega> w" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> w' y = w y"
  shows "visc_supersol k L \<Omega> w'"
  unfolding visc_supersol_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and loc: "\<exists>e>0. \<forall>y \<in> ball x e. w' x - \<phi> x \<le> w' y - \<phi> y"
  from loc obtain e where e0: "0 < e"
    and le: "\<And>y. y \<in> ball x e \<Longrightarrow> w' x - \<phi> x \<le> w' y - \<phi> y" by blast
  from op x obtain d where d0: "0 < d" and dsub: "ball x d \<subseteq> \<Omega>"
    using open_contains_ball by blast
  have loc': "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  proof (intro exI[of _ "min e d"] conjI ballI)
    show "0 < min e d" using e0 d0 by simp
    fix y assume y: "y \<in> ball x (min e d)"
    then have ye: "y \<in> ball x e" and yd: "y \<in> ball x d" by auto
    have "w x - \<phi> x = w' x - \<phi> x" using eq[OF x] by simp
    also have "\<dots> \<le> w' y - \<phi> y" by (rule le[OF ye])
    also have "\<dots> = w y - \<phi> y" using eq[OF subsetD[OF dsub yd]] by simp
    finally show "w x - \<phi> x \<le> w y - \<phi> y" .
  qed
  from s x tf loc' show "1 \<le> ell_op k L (g x) H"
    unfolding visc_supersol_def by blast
qed

lemma supersol_jet_cong_on:
  fixes w w' :: "real^'n::finite \<Rightarrow> real"
  assumes s: "supersol_jet k L \<Omega> w" and op: "open \<Omega>"
    and eq: "\<And>y. y \<in> \<Omega> \<Longrightarrow> w' y = w y"
  shows "supersol_jet k L \<Omega> w'"
  unfolding supersol_jet_def
proof (intro ballI allI impI)
  fix x \<phi> g H
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and loc: "\<exists>e>0. \<forall>y \<in> ball x e. w' x - \<phi> x \<le> w' y - \<phi> y"
  from loc obtain e where e0: "0 < e"
    and le: "\<And>y. y \<in> ball x e \<Longrightarrow> w' x - \<phi> x \<le> w' y - \<phi> y" by blast
  from op x obtain d where d0: "0 < d" and dsub: "ball x d \<subseteq> \<Omega>"
    using open_contains_ball by blast
  have loc': "\<exists>e>0. \<forall>y \<in> ball x e. w x - \<phi> x \<le> w y - \<phi> y"
  proof (intro exI[of _ "min e d"] conjI ballI)
    show "0 < min e d" using e0 d0 by simp
    fix y assume y: "y \<in> ball x (min e d)"
    then have ye: "y \<in> ball x e" and yd: "y \<in> ball x d" by auto
    have "w x - \<phi> x = w' x - \<phi> x" using eq[OF x] by simp
    also have "\<dots> \<le> w' y - \<phi> y" by (rule le[OF ye])
    also have "\<dots> = w y - \<phi> y" using eq[OF subsetD[OF dsub yd]] by simp
    finally show "w x - \<phi> x \<le> w y - \<phi> y" .
  qed
  from s x tf loc' show "1 \<le> ell_op_usc k L (g x) H"
    unfolding supersol_jet_def by blast
qed

text \<open>The refutation: given any sub/supersolution pair and nonempty interior,
  the supersolution's boundary values can be raised uniformly enough to
  make every boundary point lose to a fixed interior point, independent
  of the operator, dimension or geometry of \<open>K\<close>.\<close>

theorem max_principle_boundary_counterexample:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "visc_supersol k L (interior K) w"
    and ne: "interior K \<noteq> {}"
  shows "\<not> max_principle_boundary_raw k L K"
proof
  assume mp: "max_principle_boundary_raw k L K"
  from ne obtain y0 where y0: "y0 \<in> interior K" by blast
  define w' where "w' = (\<lambda>y. if y \<in> interior K then w y
      else u y - (u y0 - w y0) + 1)"
  have sup': "visc_supersol k L (interior K) w'"
    by (rule visc_supersol_cong_on[OF sup open_interior]) (simp add: w'_def)
  obtain x where x: "x \<in> K - interior K"
    and mx: "\<And>y. y \<in> K \<Longrightarrow> u y - w' y \<le> u x - w' x"
    using mp sub sup' unfolding max_principle_boundary_raw_def by blast
  have xb: "x \<notin> interior K" using x by simp
  have vx: "u x - w' x = (u y0 - w y0) - 1"
    unfolding w'_def using xb by simp
  have vy: "u y0 - w' y0 = u y0 - w y0"
    unfolding w'_def using y0 by simp
  have "y0 \<in> K" using y0 interior_subset by blast
  from mx[OF this] vx vy show False by simp
qed

text \<open>The repair lives in @{theory Relative_Arbitrage.Operator_Envelope_Continuity}: the corrected
  \<open>max_principle_boundary\<close> carries \<open>continuous_on K u\<close> and
  \<open>continuous_on K w\<close>, \<open>max_principle_boundary_attains\<close> records that
  \<open>u-w\<close> then attains its maximum on compact \<open>K\<close>, and \<open>max_principle_le\<close>,
  \<open>comparison_from_max_principle\<close>, \<open>uniqueness_from_max_principle\<close>
  thread the two continuity hypotheses through.  Everything downstream -
  4.2(b), Theorem 4.3, Proposition 4.1 - is unchanged except for carrying
  this continuity.\<close>

section \<open>Reduction to globally bounded, globally continuous data\<close>

text \<open>The chain above needs \<open>u\<close> and \<open>w\<close> global, bounded and continuous on all
  of \<open>real^'n\<close>, since the sup-convolution is a supremum over the whole
  space; the corrected \<open>max_principle_boundary\<close> supplies only
  \<open>continuous_on K\<close>.  Tietze's extension theorem gives a global
  continuous representative with the same sup-norm bound, and the
  viscosity properties are unaffected since \<open>visc_subsol\<close> is a local
  condition at points of the open \<open>interior K\<close> - the same locality that
  made the raw interface refutable now works in reverse.\<close>

lemma continuous_extension_bounded:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "closed K" and cu: "continuous_on K u"
    and B0: "0 \<le> B" and B: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
  shows "\<exists>v. continuous_on UNIV v \<and> (\<forall>y\<in>K. v y = u y) \<and> (\<forall>y. \<bar>v y\<bar> \<le> B)"
proof -
  have cl: "closedin (top_of_set UNIV) K"
    using cK by (simp add: closedin_closed_eq)
  have nB: "\<And>x. x \<in> K \<Longrightarrow> norm (u x) \<le> B" using B by simp
  show ?thesis
  proof (rule Tietze[OF cu cl B0 nB])
    fix g :: "real^'n \<Rightarrow> real"
    assume cg: "continuous_on UNIV g"
      and geq: "\<And>x. x \<in> K \<Longrightarrow> g x = u x"
      and gB: "\<And>x. x \<in> UNIV \<Longrightarrow> norm (g x) \<le> B"
    have "\<forall>y. \<bar>g y\<bar> \<le> B" using gB by simp
    then show "\<exists>v. continuous_on UNIV v \<and> (\<forall>y\<in>K. v y = u y)
        \<and> (\<forall>y. \<bar>v y\<bar> \<le> B)"
      using cg geq by blast
  qed
qed

lemma visc_subsol_extend:
  fixes u v :: "real^'n::finite \<Rightarrow> real"
  assumes s: "visc_subsol k L (interior K) u"
    and eq: "\<And>y. y \<in> K \<Longrightarrow> v y = u y"
  shows "visc_subsol k L (interior K) v"
proof (rule visc_subsol_cong_on[OF s open_interior])
  fix y assume "y \<in> interior K"
  then have "y \<in> K" using interior_subset by blast
  then show "v y = u y" by (rule eq)
qed

lemma supersol_jet_extend:
  fixes w v :: "real^'n::finite \<Rightarrow> real"
  assumes s: "supersol_jet k L (interior K) w"
    and eq: "\<And>y. y \<in> K \<Longrightarrow> v y = w y"
  shows "supersol_jet k L (interior K) v"
proof (rule supersol_jet_cong_on[OF s open_interior])
  fix y assume "y \<in> interior K"
  then have "y \<in> K" using interior_subset by blast
  then show "v y = w y" by (rule eq)
qed

text \<open>Packaged: from a compact \<open>K\<close> and a function continuous on it comes a
  global representative, bounded by the sup-norm on \<open>K\<close>, continuous,
  agreeing on \<open>K\<close>, and carrying the viscosity property unchanged.\<close>

lemma bounded_on_compact:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes cK: "compact K" and cu: "continuous_on K u"
  shows "\<exists>B\<ge>0. \<forall>y\<in>K. \<bar>u y\<bar> \<le> B"
proof (cases "K = {}")
  case True
  then show ?thesis by (intro exI[of _ 0]) simp
next
  case False
  have c: "continuous_on K (\<lambda>y. \<bar>u y\<bar>)"
    by (intro continuous_intros cu)
  obtain x where xK: "x \<in> K" and mx: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> \<bar>u x\<bar>"
    using continuous_attains_sup[OF cK False c] by blast
  have "0 \<le> \<bar>u x\<bar>" by simp
  then show ?thesis using mx by blast
qed

subsection \<open>Distance to the boundary controls the balls\<close>

text \<open>The assembly's ball hypotheses - \<open>cball \<xi>\<^sub>0 r \<subseteq> K \<times> K\<close> for Jensen,
  \<open>cball x R\<^sub>u \<subseteq> interior K\<close> for attainment - are instances of one
  geometric fact: a point of closed \<open>K\<close> further than \<open>\<kappa>\<close> from every
  point of \<open>K - interior K\<close> has its whole \<open>\<kappa>\<close>-ball inside
  \<open>interior K\<close>, since a segment leaving \<open>K\<close> must cross
  \<open>frontier K = K - interior K\<close>.\<close>

lemma cball_subset_interior_of_far_from_boundary:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "closed K" and xK: "x \<in> K"
    and k0: "0 \<le> \<kappa>"
    and far: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist x b"
  shows "cball x \<kappa> \<subseteq> interior K"
proof
  fix y assume y: "y \<in> cball x \<kappa>"
  then have dxy: "dist x y \<le> \<kappa>" by simp
  have fr: "frontier K = K - interior K"
    using cK by (simp add: frontier_def)
  have yK: "y \<in> K"
  proof (rule ccontr)
    assume ny: "y \<notin> K"
    have conn: "connected (closed_segment x y)" by simp
    have m1: "closed_segment x y \<inter> K \<noteq> {}"
      using xK ends_in_segment(1)[of x y] by blast
    have m2: "closed_segment x y - K \<noteq> {}"
      using ny ends_in_segment(2)[of x y] by blast
    obtain b where b: "b \<in> closed_segment x y" and bf: "b \<in> frontier K"
      using connected_Int_frontier[OF conn m1 m2] by blast
    have "norm (b - x) \<le> norm (y - x)" by (rule segment_bound1[OF b])
    then have "dist x b \<le> dist x y"
      by (simp add: dist_norm norm_minus_commute)
    then have "dist x b \<le> \<kappa>" using dxy by linarith
    moreover have "\<kappa> < dist x b" using far bf fr by blast
    ultimately show False by linarith
  qed
  show "y \<in> interior K"
  proof (rule ccontr)
    assume "y \<notin> interior K"
    with yK have "y \<in> K - interior K" by simp
    then have "\<kappa> < dist x y" by (rule far)
    with dxy show False by linarith
  qed
qed

lemma cball_prod_subset_of_far_from_boundary:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "closed K" and xK: "x \<in> K" and yK: "y \<in> K"
    and k0: "0 \<le> \<kappa>"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist x b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist y b"
    and z: "dist z (x, y) \<le> \<kappa>"
  shows "fst z \<in> K \<and> snd z \<in> K"
proof -
  have d1: "dist (fst z) x \<le> \<kappa>"
    using dist_fst_le[of z "(x, y)"] z by simp
  have d2: "dist (snd z) y \<le> \<kappa>"
    using dist_snd_le[of z "(x, y)"] z by simp
  have s1: "cball x \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF cK xK k0 farx])
  have s2: "cball y \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF cK yK k0 fary])
  have "fst z \<in> cball x \<kappa>" using d1 by (simp add: dist_commute)
  then have "fst z \<in> interior K" using s1 by blast
  moreover have "snd z \<in> cball y \<kappa>" using d2 by (simp add: dist_commute)
  then have "snd z \<in> interior K" using s2 by blast
  ultimately show ?thesis using interior_subset by blast
qed

subsection \<open>From a localised maximiser straight to the contradiction\<close>

text \<open>The bridge between the localisation and the assembly: given the
  doubling maximiser \<open>\<xi>\<^sub>0\<close> over \<open>K \<times> K\<close> with both components further
  than \<open>\<kappa>\<close> from \<open>K - interior K\<close>, every geometric hypothesis of
  \<open>comparison_supconv_maximiser_complete\<close> is derivable via
  \<open>cball_subset_interior_of_far_from_boundary\<close> and
  \<open>supconv_radius_uniform\<close>.  The remaining quantitative inputs are the
  inequalities \<open>r \<le> \<kappa>\<close>, \<open>\<rho>+R\<^sub>u \<le> \<kappa>\<close>, \<open>\<rho>+R\<^sub>w \<le> \<kappa>\<close>, \<open>2\<bar>\<alpha>\<bar>\<rho> < c\<close> and two
  smallness conditions on \<open>\<epsilon>\<close>.\<close>

text \<open>Under a general penalty every geometric derivation is untouched, since
  the penalty only carries along unchanged from \<open>mxKK\<close> to \<open>mxK\<close>; only
  the gradient conditions \<open>glb\<close> and \<open>rsmall\<close> refer to it, through \<open>Gf\<close>
  and its Lipschitz constant \<open>KG\<close>.\<close>

theorem comparison_from_localised_maximiser_gen:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and K :: "(real^'n) set"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
    and Pn :: "real^'n \<Rightarrow> real"
    and Gf :: "real^'n \<Rightarrow> real^'n" and Zf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and kap: "0 \<le> \<kappa>\<^sub>P"
    and scP: "convex_on UNIV (\<lambda>d. (\<kappa>\<^sub>P/2) * (norm d)\<^sup>2 - Pn d)"
    and Pjet: "\<And>d. ((\<lambda>h. (Pn (d + h) - Pn d - Gf d \<bullet> h
          - (h \<bullet> (Zf d *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    and symZ: "\<And>d. transpose (Zf d) = Zf d"
    and bZ: "\<And>d z. \<bar>z \<bullet> (Zf d *v z)\<bar> \<le> KZ * (norm z)\<^sup>2"
    and lipG: "\<And>d d'. norm (Gf d - Gf d') \<le> KG * norm (d - d')"
    and KGnn: "0 \<le> KG"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - Pn (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and xK: "fst \<xi>\<^sub>0 \<in> K" and yK: "snd \<xi>\<^sub>0 \<in> K"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (fst \<xi>\<^sub>0) b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (snd \<xi>\<^sub>0) b"
    and rho: "0 < \<rho>" "\<rho> < r" and rk: "r \<le> \<kappa>"
    and Rup: "0 < R\<^sub>u" and Rwp: "0 < R\<^sub>w"
    and smallu: "2*\<epsilon>*(Bu - Blu) < R\<^sub>u\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < R\<^sub>w\<^sup>2"
    and fitu: "\<rho> + R\<^sub>u \<le> \<kappa>" and fitw: "\<rho> + R\<^sub>w \<le> \<kappa>"
    and D0: "0 < D\<^sub>0"
    and glb: "c \<le> norm (Gf (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "KG * (2*\<rho>) < c"
  shows False
proof -
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  have k0: "0 \<le> \<kappa>" using rho rk by linarith
  have coll: "(fst \<xi>\<^sub>0, snd \<xi>\<^sub>0) = \<xi>\<^sub>0" by simp
  have insx: "cball (fst \<xi>\<^sub>0) \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK xK k0 farx])
  have insy: "cball (snd \<xi>\<^sub>0) \<kappa> \<subseteq> interior K"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK yK k0 fary])
  have mxK: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst z) + supconv (- w) \<epsilon> (snd z)
        - Pn (fst z - snd z)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
        - Pn (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    if z: "z \<in> cball \<xi>\<^sub>0 r" for z
  proof -
    have dz: "dist z (fst \<xi>\<^sub>0, snd \<xi>\<^sub>0) \<le> \<kappa>"
      unfolding coll using z rk by (simp add: dist_commute)
    have "fst z \<in> K \<and> snd z \<in> K"
      by (rule cball_prod_subset_of_far_from_boundary
          [OF clK xK yK k0 farx fary dz])
    then show ?thesis using mxKK by blast
  qed
  have radu: "sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x))) < R\<^sub>u" for x
    by (rule supconv_radius_uniform[OF lou e Rup smallu])
  have radw: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x))) < R\<^sub>w" for x
    by (rule supconv_radius_uniform[OF low e Rwp smallw])
  have subu: "cball x R\<^sub>u \<subseteq> interior K" if d: "dist x (fst \<xi>\<^sub>0) \<le> \<rho>" for x
  proof -
    have "cball x R\<^sub>u \<subseteq> cball (fst \<xi>\<^sub>0) \<kappa>"
    proof
      fix y assume "y \<in> cball x R\<^sub>u"
      then have dy: "dist x y \<le> R\<^sub>u" by simp
      have "dist (fst \<xi>\<^sub>0) y \<le> dist (fst \<xi>\<^sub>0) x + dist x y"
        by (rule dist_triangle)
      also have "\<dots> \<le> \<rho> + R\<^sub>u"
        using d dy by (simp add: dist_commute)
      finally show "y \<in> cball (fst \<xi>\<^sub>0) \<kappa>" using fitu by simp
    qed
    then show ?thesis using insx by blast
  qed
  have subw: "cball x R\<^sub>w \<subseteq> interior K" if d: "dist x (snd \<xi>\<^sub>0) \<le> \<rho>" for x
  proof -
    have "cball x R\<^sub>w \<subseteq> cball (snd \<xi>\<^sub>0) \<kappa>"
    proof
      fix y assume "y \<in> cball x R\<^sub>w"
      then have dy: "dist x y \<le> R\<^sub>w" by simp
      have "dist (snd \<xi>\<^sub>0) y \<le> dist (snd \<xi>\<^sub>0) x + dist x y"
        by (rule dist_triangle)
      also have "\<dots> \<le> \<rho> + R\<^sub>w"
        using d dy by (simp add: dist_commute)
      finally show "y \<in> cball (snd \<xi>\<^sub>0) \<kappa>" using fitw by simp
    qed
    then show ?thesis using insy by blast
  qed
  have icu: "isCont (\<lambda>y. \<theta> * u y) z" for z
    using cu[unfolded continuous_on_eq_continuous_at[OF open_UNIV]] by blast
  have icw: "isCont (- w) z" for z
    using cw[unfolded continuous_on_eq_continuous_at[OF open_UNIV]] by blast
  have uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
      \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    by (rule usc_eps_of_continuous[OF icu])
  have uw: "\<And>c z. (- w) z < c \<Longrightarrow>
      \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    by (rule usc_eps_of_continuous[OF icw])
  have atu: "z \<in> interior K"
    if d: "dist x (fst \<xi>\<^sub>0) \<le> \<rho>"
      and o: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x
          = \<theta> * u z - (dist x z)\<^sup>2 / (2*\<epsilon>)" for x z
  proof -
    have "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bu - \<theta> * u x)))"
      by (rule supconv_attain_radius[OF Bu e o])
    also have "\<dots> < R\<^sub>u" by (rule radu)
    finally have "z \<in> cball x R\<^sub>u" by (simp add: dist_commute)
    then show ?thesis using subu[OF d] by blast
  qed
  have atw: "z \<in> interior K"
    if d: "dist x (snd \<xi>\<^sub>0) \<le> \<rho>"
      and o: "supconv (- w) \<epsilon> x = (- w) z - (dist x z)\<^sup>2 / (2*\<epsilon>)" for x z
  proof -
    have "dist x z \<le> sqrt (max 0 (2*\<epsilon>*(Bw - (- w) x)))"
      by (rule supconv_attain_radius[OF Bw e o])
    also have "\<dots> < R\<^sub>w" by (rule radw)
    finally have "z \<in> cball x R\<^sub>w" by (simp add: dist_commute)
    then show ?thesis using subw[OF d] by blast
  qed
  show False
    by (rule comparison_supconv_maximiser_complete_gen
        [where u = u and w = w and \<xi>\<^sub>0 = \<xi>\<^sub>0 and D\<^sub>0 = D\<^sub>0
           and \<Omega>\<^sub>u = "interior K" and \<Omega>\<^sub>w = "interior K"
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa> = \<kappa>\<^sub>P and \<rho> = \<rho> and r = r
           and Pn = Pn and Gf = Gf and Zf = Zf and KZ = KZ and KG = KG
           and Bu = Bu and Bw = Bw and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL e kap scP Pjet symZ bZ lipG
            KGnn rho(1) rho(2) D0 Bu Bw uu uw])
       (use mxK atu atw glb rsmall in blast)+
qed

subsection \<open>The chain at the concrete penalty \<open>soft_pen\<close>\<close>

text \<open>Every abstract hypothesis of the \<open>_gen\<close> chain is discharged at
  \<open>Pn = soft_pen \<kappa>\<close>:

    \<open>sc\<close>    by \<open>soft_pen_semiconcave\<close>
    \<open>Pjet\<close>  by \<open>soft_pen_jet_field\<close>   (gradient field \<open>soft_grad \<kappa>\<close>,
                                      Hessian field \<open>soft_hess \<kappa>\<close>)
    \<open>symZ\<close>  by \<open>soft_hess_sym\<close>
    \<open>bZ\<close>    by \<open>soft_hess_bound\<close>       with \<open>KZ = 2\<kappa>\<close>
    \<open>lipG\<close>  by \<open>soft_grad_lipschitz\<close>   with \<open>KG = 3\<kappa>\<close>

  so the theorem below mentions no penalty data beyond \<open>\<kappa>\<close> itself;
  \<open>KZ\<close> and \<open>KG\<close> are free parameters, not sharp constants.\<close>

theorem comparison_from_localised_maximiser_soft:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
    and K :: "(real^'n) set"
    and \<xi>\<^sub>0 :: "(real^'n) \<times> (real^'n)"
    and D\<^sub>0 :: real
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and e: "0 < \<epsilon>" and kap: "0 \<le> \<kappa>\<^sub>P"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst \<xi>\<^sub>0) + supconv (- w) \<epsilon> (snd \<xi>\<^sub>0)
          - soft_pen \<kappa>\<^sub>P (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0)"
    and xK: "fst \<xi>\<^sub>0 \<in> K" and yK: "snd \<xi>\<^sub>0 \<in> K"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (fst \<xi>\<^sub>0) b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa> < dist (snd \<xi>\<^sub>0) b"
    and rho: "0 < \<rho>" "\<rho> < r" and rk: "r \<le> \<kappa>"
    and Rup: "0 < R\<^sub>u" and Rwp: "0 < R\<^sub>w"
    and smallu: "2*\<epsilon>*(Bu - Blu) < R\<^sub>u\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < R\<^sub>w\<^sup>2"
    and fitu: "\<rho> + R\<^sub>u \<le> \<kappa>" and fitw: "\<rho> + R\<^sub>w \<le> \<kappa>"
    and D0: "0 < D\<^sub>0"
    and glb: "c \<le> norm (soft_grad \<kappa>\<^sub>P (fst \<xi>\<^sub>0 - snd \<xi>\<^sub>0))"
    and rsmall: "(3*\<kappa>\<^sub>P) * (2*\<rho>) < c"
  shows False
proof -
  have KGnn: "0 \<le> 3*\<kappa>\<^sub>P" using kap by linarith
  show False
    by (rule comparison_from_localised_maximiser_gen
        [where u = u and w = w and K = K and \<xi>\<^sub>0 = \<xi>\<^sub>0 and D\<^sub>0 = D\<^sub>0
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = \<kappa>\<^sub>P and \<rho> = \<rho> and r = r and \<kappa> = \<kappa>
           and Pn = "soft_pen \<kappa>\<^sub>P" and Gf = "soft_grad \<kappa>\<^sub>P"
           and Zf = "soft_hess \<kappa>\<^sub>P" and KZ = "2*\<kappa>\<^sub>P" and KG = "3*\<kappa>\<^sub>P"
           and Bu = Bu and Bw = Bw and Blu = Blu and Blw = Blw
           and R\<^sub>u = R\<^sub>u and R\<^sub>w = R\<^sub>w and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL e kap
            soft_pen_semiconcave[OF kap] soft_pen_jet_field soft_hess_sym
            soft_hess_bound[OF kap] soft_grad_lipschitz[OF kap] KGnn cK
            Bu Bw lou low cu cw])
       (use mxKK xK yK farx fary rho rk Rup Rwp smallu smallw fitu fitw
            D0 glb rsmall in blast)+
qed

subsection \<open>Branch (A): the off-diagonal case closes\<close>

text \<open>Given the localised maximiser off the diagonal, the remaining
  parameters of \<open>comparison_from_localised_maximiser_soft\<close> are
  determined:

    \<open>R\<^sub>u = R\<^sub>w = \<kappa>\<^sub>g/4\<close>, \<open>r = \<kappa>\<^sub>g\<close>, \<open>\<rho> < 3\<kappa>\<^sub>g/4\<close> small enough that
    \<open>6\<rho> < (1 - 1/R d) norm d\<close> (\<open>soft_rho_exists\<close>),
    \<open>c = norm (soft_grad \<kappa>\<^sub>P d)\<close> (positive by \<open>soft_grad_norm_pos\<close>),
    \<open>D\<^sub>0 = 1\<close>

  \<open>rsmall\<close> is \<open>soft_rsmall_of_rho\<close>, and \<open>glb\<close> holds by reflexivity
  since \<open>c\<close> is the gradient norm; \<open>\<kappa>\<^sub>P\<close> cancels in \<open>rsmall\<close>.\<close>

theorem comparison_soft_off_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and epos: "0 < \<epsilon>" and kgpos: "0 < \<kappa>\<^sub>g" and kPpos: "0 < \<kappa>\<^sub>P"
    and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and farx: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa>\<^sub>g < dist xh b"
    and fary: "\<And>b. b \<in> K - interior K \<Longrightarrow> \<kappa>\<^sub>g < dist yh b"
    and smallu: "2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and off: "xh \<noteq> yh"
  shows False
proof -
  have kPnn: "0 \<le> \<kappa>\<^sub>P" using kPpos by linarith
  have dne: "xh - yh \<noteq> 0" using off by simp
  \<comment> \<open>the positive gradient lower bound\<close>
  define c where "c = norm (soft_grad \<kappa>\<^sub>P (xh - yh))"
  have cpos: "0 < c" unfolding c_def by (rule soft_grad_norm_pos[OF dne kPpos])
  \<comment> \<open>the radii\<close>
  define R\<^sub>u where "R\<^sub>u = \<kappa>\<^sub>g/4"
  have Rupos: "0 < R\<^sub>u" unfolding R\<^sub>u_def using kgpos by simp
  have Bpos: "0 < 3*\<kappa>\<^sub>g/4" using kgpos by simp
  obtain \<rho> where rpos: "0 < \<rho>" and rlt: "\<rho> < 3*\<kappa>\<^sub>g/4"
    and rgrad: "6 * \<rho> < (1 - 1 / sqrt ((norm (xh - yh))\<^sup>2 + 1)) * norm (xh - yh)"
    using soft_rho_exists[OF dne Bpos] by blast
  have rltk: "\<rho> < \<kappa>\<^sub>g" using rlt kgpos by simp
  have fitu: "\<rho> + R\<^sub>u \<le> \<kappa>\<^sub>g" unfolding R\<^sub>u_def using rlt by simp
  have rsmall: "(3*\<kappa>\<^sub>P) * (2*\<rho>) < c"
    unfolding c_def by (rule soft_rsmall_of_rho[OF kPpos rgrad])
  have glb: "c \<le> norm (soft_grad \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh)))"
    unfolding c_def by simp
  \<comment> \<open>the maximiser hypothesis in the paired form\<close>
  have mxp: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
        - soft_pen \<kappa>\<^sub>P (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh))
        + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh))"
    if "x \<in> K" "y \<in> K" for x y
    using mxKK[OF that] by simp
  have xKp: "fst (xh, yh) \<in> K" using xhK by simp
  have yKp: "snd (xh, yh) \<in> K" using yhK by simp
  have farxp: "\<kappa>\<^sub>g < dist (fst (xh, yh)) b" if "b \<in> K - interior K" for b
    using farx[OF that] by simp
  have faryp: "\<kappa>\<^sub>g < dist (snd (xh, yh)) b" if "b \<in> K - interior K" for b
    using fary[OF that] by simp
  have smu: "2*\<epsilon>*(Bu - Blu) < R\<^sub>u\<^sup>2" unfolding R\<^sub>u_def by (rule smallu)
  have smw: "2*\<epsilon>*(Bw - Blw) < R\<^sub>u\<^sup>2" unfolding R\<^sub>u_def by (rule smallw)
  have D0: "(0::real) < 1" by simp
  show False
    by (rule comparison_from_localised_maximiser_soft
        [where u = u and w = w and K = K and \<xi>\<^sub>0 = "(xh, yh)" and D\<^sub>0 = 1
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = \<kappa>\<^sub>P and \<kappa> = \<kappa>\<^sub>g and \<rho> = \<rho> and r = \<kappa>\<^sub>g
           and Bu = Bu and Bw = Bw and Blu = Blu and Blw = Blw
           and R\<^sub>u = R\<^sub>u and R\<^sub>w = R\<^sub>u and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL epos kPnn cK Bu Bw lou low cu cw])
       (use mxp xKp yKp farxp faryp rpos rltk order.refl Rupos
            smu smw fitu D0 glb rsmall in blast)+
qed

subsection \<open>Branch (A) in the two-domain setting\<close>

text \<open>The same branch with the \<open>x\<close>-side boundary avoidance replaced by
  \<open>posb\<close> - the sup-convolution is positive on a \<open>\<rho>\<^sub>u\<close>-ball around
  \<open>x^h\<close>, supplied by Definition 3.1's gate with no geometry needed.  The
  \<open>y\<close>-side keeps its ball, paid for by \<open>K \<subseteq> K'\<^sup>\<circ>\<close>; the maximality
  hypothesis \<open>mxU\<close> ranges over \<open>UNIV \<times> K'\<close>, from
  \<open>doubled_maximiser_over_UNIV_snd\<close>.\<close>

theorem comparison_2dom_off_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K' :: "(real^'n) set"
  assumes sub: "visc_subsol k L {q. 0 < u q} u"
    and sup: "supersol_jet k L (interior K') w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and low: "\<And>y. Blw \<le> (- w) y"
    and uu: "\<And>c z. \<theta> * u z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> \<theta> * u y < c"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and epos: "0 < \<epsilon>" and kgpos: "0 < \<kappa>\<^sub>g" and kPpos: "0 < \<kappa>\<^sub>P"
    and clK': "closed K'" and yhK': "yh \<in> K'"
    and mxU: "\<And>a q. q \<in> K' \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> a + supconv (- w) \<epsilon> q - soft_pen \<kappa>\<^sub>P (a - q)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and fary: "\<And>b. b \<in> K' - interior K' \<Longrightarrow> \<kappa>\<^sub>g < dist yh b"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and rupos: "0 < \<rho>\<^sub>u"
    and posb: "\<And>a. dist a xh \<le> \<rho>\<^sub>u \<Longrightarrow> 0 < supconv (\<lambda>y. \<theta> * u y) \<epsilon> a"
    and off: "xh \<noteq> yh"
  shows False
proof -
  have kPnn: "0 \<le> \<kappa>\<^sub>P" using kPpos by linarith
  have kgnn: "0 \<le> \<kappa>\<^sub>g" using kgpos by linarith
  have dne: "xh - yh \<noteq> 0" using off by simp
  define c where "c = norm (soft_grad \<kappa>\<^sub>P (xh - yh))"
  have cpos: "0 < c" unfolding c_def by (rule soft_grad_norm_pos[OF dne kPpos])
  define R\<^sub>w where "R\<^sub>w = \<kappa>\<^sub>g/4"
  have Rwpos: "0 < R\<^sub>w" unfolding R\<^sub>w_def using kgpos by simp
  have smallw': "2*\<epsilon>*(Bw - Blw) < R\<^sub>w\<^sup>2"
    unfolding R\<^sub>w_def by (rule smallw)
  have Bpos: "0 < min (3*\<kappa>\<^sub>g/4) \<rho>\<^sub>u" using kgpos rupos by simp
  obtain \<rho> where rpos: "0 < \<rho>" and rlt: "\<rho> < min (3*\<kappa>\<^sub>g/4) \<rho>\<^sub>u"
    and rgrad: "6 * \<rho>
        < (1 - 1 / sqrt ((norm (xh - yh))\<^sup>2 + 1)) * norm (xh - yh)"
    using soft_rho_exists[OF dne Bpos] by blast
  have rlt1: "\<rho> < 3*\<kappa>\<^sub>g/4" using rlt by simp
  have rltu: "\<rho> \<le> \<rho>\<^sub>u" using rlt by simp
  have rltk: "\<rho> < \<kappa>\<^sub>g" using rlt1 kgpos by simp
  have fitw: "\<rho> + R\<^sub>w \<le> \<kappa>\<^sub>g" unfolding R\<^sub>w_def using rlt1 by simp
  have rsmall: "(3*\<kappa>\<^sub>P) * (2*\<rho>) < c"
    unfolding c_def by (rule soft_rsmall_of_rho[OF kPpos rgrad])
  have glb: "c \<le> norm (soft_grad \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh)))"
    unfolding c_def by simp
  have insy: "cball yh \<kappa>\<^sub>g \<subseteq> interior K'"
    by (rule cball_subset_interior_of_far_from_boundary[OF clK' yhK' kgnn fary])
  have ballK': "cball (snd (xh, yh)) \<kappa>\<^sub>g \<subseteq> K'"
    using insy interior_subset by auto
  have mx': "\<And>a q. q \<in> K' \<Longrightarrow>
      supconv (\<lambda>y. \<theta> * u y) \<epsilon> a + supconv (- w) \<epsilon> q - soft_pen \<kappa>\<^sub>P (a - q)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh))
        + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh))"
    using mxU by simp
  have mxK: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst p) + supconv (- w) \<epsilon> (snd p)
        - soft_pen \<kappa>\<^sub>P (fst p - snd p)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> (fst (xh, yh))
        + supconv (- w) \<epsilon> (snd (xh, yh))
        - soft_pen \<kappa>\<^sub>P (fst (xh, yh) - snd (xh, yh))"
    if p: "p \<in> cball (xh, yh) \<kappa>\<^sub>g" for p
    by (rule mxK_of_UNIV_snd
        [where A = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>" and Bfun = "supconv (- w) \<epsilon>"
           and Pn = "soft_pen \<kappa>\<^sub>P" and K' = K' and \<xi>\<^sub>0 = "(xh, yh)"
           and r = \<kappa>\<^sub>g and p = p,
         OF mx' ballK' p])
  have atw: "z \<in> interior K'"
    if d: "dist a (snd (xh, yh)) \<le> \<rho>"
      and o: "supconv (- w) \<epsilon> a = (- w) z - (dist a z)\<^sup>2 / (2*\<epsilon>)" for a z
  proof -
    have d1: "dist a z \<le> sqrt (max 0 (2*\<epsilon>*(Bw - (- w) a)))"
      by (rule supconv_attain_radius[OF Bw epos o])
    have d2: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) a))) < R\<^sub>w"
      by (rule supconv_radius_uniform[OF low epos Rwpos smallw'])
    have dz: "dist a z \<le> R\<^sub>w" using d1 d2 by linarith
    have "dist yh z \<le> dist yh a + dist a z" by (rule dist_triangle)
    also have "\<dots> \<le> \<rho> + R\<^sub>w" using d dz by (simp add: dist_commute)
    finally have "z \<in> cball yh \<kappa>\<^sub>g" using fitw by simp
    then show ?thesis using insy by blast
  qed
  have atu: "z \<in> {q. 0 < u q}"
    if d: "dist a (fst (xh, yh)) \<le> \<rho>"
      and o: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> a = \<theta> * u z - (dist a z)\<^sup>2 / (2*\<epsilon>)"
    for a z
  proof -
    have du: "dist a xh \<le> \<rho>\<^sub>u" using d rltu by simp
    show ?thesis by (rule atu_of_positive_ball[OF t(1) epos posb du o])
  qed
  have D0: "(0::real) < 1" by simp
  have KGnn: "0 \<le> 3*\<kappa>\<^sub>P" using kPnn by linarith
  show False
    by (rule comparison_supconv_maximiser_complete_gen
        [where u = u and w = w and \<xi>\<^sub>0 = "(xh, yh)" and D\<^sub>0 = 1
           and \<Omega>\<^sub>u = "{q. 0 < u q}" and \<Omega>\<^sub>w = "interior K'"
           and \<theta> = \<theta> and \<epsilon> = \<epsilon> and \<kappa> = \<kappa>\<^sub>P and \<rho> = \<rho> and r = \<kappa>\<^sub>g
           and Pn = "soft_pen \<kappa>\<^sub>P" and Gf = "soft_grad \<kappa>\<^sub>P"
           and Zf = "soft_hess \<kappa>\<^sub>P" and KZ = "2*\<kappa>\<^sub>P" and KG = "3*\<kappa>\<^sub>P"
           and Bu = Bu and Bw = Bw and c = c,
         OF sub sup t(1) t(2) kk(1) kk(2) LL epos kPnn
            soft_pen_semiconcave[OF kPnn] soft_pen_jet_field soft_hess_sym
            soft_hess_bound[OF kPnn] soft_grad_lipschitz[OF kPnn] KGnn
            rpos rltk D0 Bu Bw uu uw])
       (use mxK atu atw glb rsmall in blast)+
qed

subsection \<open>Branch (B): the diagonal case closes too\<close>

text \<open>The four steps chained: at a diagonal maximiser (interior, by the
  localisation), the maximiser inequality bounds the increment of
  \<open>B = supconv(-w)\<epsilon>\<close> above by the penalty, which is \<open>o(\<bar>h\<bar>^2)\<close>; that
  descends to \<open>-w\<close> at the attainment point, and a supersolution cannot
  have such a flat point.  This uses no property of the subsolution
  side, so the diagonal case is a genuinely different argument from the
  off-diagonal one.\<close>

theorem comparison_soft_diagonal:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and A :: "real^'n \<Rightarrow> real"
  assumes sup: "supersol_jet k L (interior K) w"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and Bw: "\<And>y. (- w) y \<le> Bw"
    and uw: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
    and epos: "0 < \<epsilon>"
    and pK: "p \<in> K" and pint: "p \<in> interior K"
    and mxKK: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        A x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> A p + supconv (- w) \<epsilon> p - soft_pen \<kappa>\<^sub>P (p - p)"
    and rad: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) p))) < R\<^sub>w"
    and subw: "cball p R\<^sub>w \<subseteq> interior K"
  shows False
proof -
  \<comment> \<open>the attainment point, and it is interior\<close>
  obtain ys where ysO: "ys \<in> interior K"
    and opt: "supconv (- w) \<epsilon> p = (- w) ys - (dist p ys)\<^sup>2 / (2*\<epsilon>)"
    using supconv_attained_usc_in_rad[OF Bw epos uw rad subw] by blast
  \<comment> \<open>\<open>p\<close> is interior, so \<open>p + hh\<close> stays in \<open>K\<close> for small \<open>hh\<close>\<close>
  \<comment> \<open>\<open>mem_interior\<close> already delivers the ball inside \<open>K\<close> itself, so no
      subset-transitivity step is needed --- routing it through
      \<open>interior_subset\<close> instead made \<open>blast\<close> search for seconds and PIDE flag it\<close>
  obtain r\<^sub>0 where r0: "0 < r\<^sub>0" and rb: "ball p r\<^sub>0 \<subseteq> K"
    using pint unfolding mem_interior by blast
  have nb: "p + hh \<in> K" if "hh \<noteq> 0" and "dist hh 0 < r\<^sub>0" for hh
  proof -
    have "dist (p + hh) p < r\<^sub>0" using that by (simp add: dist_norm)
    then have "p + hh \<in> ball p r\<^sub>0" by (simp add: dist_commute)
    then show ?thesis using rb by blast
  qed
  have nbhd: "\<forall>\<^sub>F hh in at 0. p + hh \<in> K"
    unfolding eventually_at using r0 nb by blast
  \<comment> \<open>step 1: the increment bound\<close>
  have dom: "\<forall>\<^sub>F hh in at 0.
      supconv (- w) \<epsilon> (p + hh) - supconv (- w) \<epsilon> p \<le> soft_pen \<kappa>\<^sub>P hh"
  proof (rule eventually_mono[OF nbhd])
    fix hh :: "real^'n"
    assume hK: "p + hh \<in> K"
    show "supconv (- w) \<epsilon> (p + hh) - supconv (- w) \<epsilon> p \<le> soft_pen \<kappa>\<^sub>P hh"
      by (rule diagonal_max_increment_soft[OF mxKK pK hK])
  qed
  \<comment> \<open>step 2: it is the one-sided hypothesis\<close>
  have ub: "\<forall>\<^sub>F hh in at 0.
      (supconv (- w) \<epsilon> (p + hh) - supconv (- w) \<epsilon> p) / (norm hh)\<^sup>2 < c"
    if c: "0 < c" for c
    by (rule diagonal_increment_onesided[OF dom c])
  \<comment> \<open>step 3: descend to the attainment point\<close>
  have ubw: "\<forall>\<^sub>F hh in at 0. ((- w) (ys + hh) - (- w) ys) / (norm hh)\<^sup>2 < c"
    if c: "0 < c" for c
    by (rule supconv_onesided_descent[OF Bw epos opt ub c])
  \<comment> \<open>step 4: a supersolution has no such flat point\<close>
  show False
    by (rule supersol_no_vanishing_jet_onesided
        [OF sup ysO kk(1) kk(2) LL ubw])
qed

subsection \<open>A nonempty compact set has a nonempty frontier\<close>

text \<open>\<open>max_principle_boundary\<close> asserts a maximiser in \<open>K - interior K\<close>,
  which is inhabited for compact nonempty \<open>K\<close>: otherwise
  \<open>K = interior K\<close> is clopen in the connected whole space, and
  \<open>K \<noteq> UNIV\<close> since \<open>K\<close> is bounded.  With \<open>K = {}\<close> the predicate is
  unprovable, since the hypotheses hold vacuously but the conclusion
  asserts membership in the empty set; \<open>K \<noteq> {}\<close> is a genuine side
  condition.\<close>

lemma compact_frontier_nonempty:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K" and ne: "K \<noteq> {}"
    and dim: "0 < CARD('n)"
  shows "K - interior K \<noteq> {}"
proof -
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  have fr: "frontier K = K - interior K"
    using clK by (simp add: frontier_def)
  have unb: "\<not> bounded (UNIV :: (real^'n) set)"
  proof -
    have "\<exists>x :: 'n. True" using dim by (simp add: card_gt_0_iff ex_in_conv)
    then show ?thesis by simp
  qed
  have nU: "K \<noteq> UNIV"
  proof
    assume "K = UNIV"
    then have "bounded (UNIV :: (real^'n) set)"
      using compact_imp_bounded[OF cK] by simp
    with unb show False by blast
  qed
  have "frontier K \<noteq> {}" using ne nU by (simp add: frontier_eq_empty)
  then show ?thesis unfolding fr .
qed

subsection \<open>The two branches combined\<close>

text \<open>\<open>doubling_localised_maximiser_soft\<close> produces the maximiser; branch
  (A) closes it off the diagonal, branch (B) on it.  Branch (B)'s
  geometric hypotheses follow from the localisation:

    \<open>xh \<in> interior K\<close> - \<open>farx\<close> gives \<open>\<kappa>\<^sub>g < dist xh b\<close> for every
      boundary \<open>b\<close>, ruling out \<open>xh\<close> itself being one.
    \<open>cball xh R\<^sub>w \<subseteq> interior K\<close> - from
      \<open>cball_subset_interior_of_far_from_boundary\<close> at radius \<open>\<kappa>\<^sub>g\<close>.
    the attainment radius bound - from \<open>supconv_radius_uniform\<close>.\<close>

theorem comparison_soft_complete:
  fixes u w :: "real^'n::finite \<Rightarrow> real"
  assumes sub: "visc_subsol k L (interior K) u"
    and sup: "supersol_jet k L (interior K) w"
    and t: "0 < \<theta>" "\<theta> < 1"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}"
    and Bu: "\<And>y. \<theta> * u y \<le> Bu" and Bw: "\<And>y. (- w) y \<le> Bw"
    and lou: "\<And>y. Blu \<le> \<theta> * u y" and low: "\<And>y. Blw \<le> (- w) y"
    and cu: "continuous_on UNIV (\<lambda>y. \<theta> * u y)"
    and cw: "continuous_on UNIV (- w)"
    and zK: "z \<in> K"
    and Mval: "M \<le> \<theta> * u z - w z"
    and bdry: "\<And>c. c \<in> K - interior K \<Longrightarrow> \<theta> * u c - w c \<le> m"
    and gapMm: "m < M"
  shows False
proof -
  obtain \<epsilon> \<kappa>\<^sub>g \<kappa>\<^sub>P xh yh where
        epos: "0 < \<epsilon>" and kgpos: "0 < \<kappa>\<^sub>g" and kPpos: "0 < \<kappa>\<^sub>P"
    and xhK: "xh \<in> K" and yhK: "yh \<in> K"
    and mxb: "\<forall>x\<in>K. \<forall>y\<in>K.
        supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
          - soft_pen \<kappa>\<^sub>P (xh - yh)"
    and farx: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist xh b"
    and fary: "\<forall>b \<in> K - interior K. \<kappa>\<^sub>g < dist yh b"
    and smallu: "2*\<epsilon>*(Bu - Blu) < (\<kappa>\<^sub>g/4)\<^sup>2"
    and smallw: "2*\<epsilon>*(Bw - Blw) < (\<kappa>\<^sub>g/4)\<^sup>2"
    using doubling_localised_maximiser_soft
      [OF cK neK Bu Bw lou low cu cw zK Mval bdry gapMm] by blast
  have mx: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
        - soft_pen \<kappa>\<^sub>P (x - y)
      \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> yh
        - soft_pen \<kappa>\<^sub>P (xh - yh)" if "x \<in> K" "y \<in> K" for x y
    using mxb that by blast
  have farxa: "\<kappa>\<^sub>g < dist xh b" if "b \<in> K - interior K" for b
    using farx that by blast
  have farya: "\<kappa>\<^sub>g < dist yh b" if "b \<in> K - interior K" for b
    using fary that by blast
  show False
  proof (cases "xh = yh")
    case False
    show False
      by (rule comparison_soft_off_diagonal
          [OF sub sup t(1) t(2) kk(1) kk(2) LL cK Bu Bw lou low cu cw
              epos kgpos kPpos xhK yhK mx farxa farya smallu smallw False])
  next
    case True
    \<comment> \<open>\<open>xh\<close> is interior: a boundary point would give \<open>\<kappa>\<^sub>g < dist xh xh = 0\<close>\<close>
    have pint: "xh \<in> interior K"
    proof (rule ccontr)
      assume "xh \<notin> interior K"
      with xhK have "xh \<in> K - interior K" by simp
      from farxa[OF this] show False using kgpos by simp
    qed
    have clK: "closed K" by (rule compact_imp_closed[OF cK])
    have kgnn: "0 \<le> \<kappa>\<^sub>g" using kgpos by linarith
    have insx: "cball xh \<kappa>\<^sub>g \<subseteq> interior K"
      by (rule cball_subset_interior_of_far_from_boundary
          [OF clK xhK kgnn farxa])
    have Rwpos: "0 < \<kappa>\<^sub>g/4" using kgpos by simp
    have shrink: "cball xh (\<kappa>\<^sub>g/4) \<subseteq> cball xh \<kappa>\<^sub>g"
    proof
      fix y assume "y \<in> cball xh (\<kappa>\<^sub>g/4)"
      then have d1: "dist xh y \<le> \<kappa>\<^sub>g/4" by simp
      have d2: "\<kappa>\<^sub>g/4 \<le> \<kappa>\<^sub>g" using kgpos by simp
      show "y \<in> cball xh \<kappa>\<^sub>g" using d1 d2 by simp
    qed
    have subw: "cball xh (\<kappa>\<^sub>g/4) \<subseteq> interior K" using shrink insx by blast
    have rad: "sqrt (max 0 (2*\<epsilon>*(Bw - (- w) xh))) < \<kappa>\<^sub>g/4"
      by (rule supconv_radius_uniform[OF low epos Rwpos smallw])
    have icwd: "isCont (- w) z" for z
      using cw[unfolded continuous_on_eq_continuous_at[OF open_UNIV]] by blast
    have uwd: "\<And>c z. (- w) z < c \<Longrightarrow>
        \<exists>d>0. \<forall>y. dist z y < d \<longrightarrow> (- w) y < c"
      by (rule usc_eps_of_continuous[OF icwd])
    have mxd: "supconv (\<lambda>y. \<theta> * u y) \<epsilon> x + supconv (- w) \<epsilon> y
          - soft_pen \<kappa>\<^sub>P (x - y)
        \<le> supconv (\<lambda>y. \<theta> * u y) \<epsilon> xh + supconv (- w) \<epsilon> xh
          - soft_pen \<kappa>\<^sub>P (xh - xh)" if "x \<in> K" "y \<in> K" for x y
      using mx[OF that] unfolding True[symmetric] .
    show False
      by (rule comparison_soft_diagonal
          [where w = w and K = K and A = "supconv (\<lambda>y. \<theta> * u y) \<epsilon>"
             and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = \<kappa>\<^sub>P and p = xh and R\<^sub>w = "\<kappa>\<^sub>g/4" and Bw = Bw,
           OF sup kk(1) kk(2) LL Bw uwd epos xhK pint mxd rad subw])
  qed
qed

section \<open>Theorem 4.2(a): \<open>max_principle_boundary\<close>\<close>

text \<open>\<open>comparison_soft_complete\<close> needs globally bounded, globally
  continuous data; the gap from the predicate's \<open>continuous_on K\<close> is
  closed by \<open>continuous_extension_bounded\<close> with \<open>visc_subsol_extend\<close>/
  \<open>supersol_jet_extend\<close>, which work because the viscosity conditions
  are local and \<open>interior K\<close> is open.  \<open>K \<noteq> {}\<close> is a genuine side
  condition (\<open>compact_frontier_nonempty\<close>).\<close>

lemma theta_exists_aux:
  fixes B G :: real
  assumes B: "0 \<le> B" and G: "0 < G"
  shows "\<exists>\<theta>. 0 < \<theta> \<and> \<theta> < 1 \<and> (1-\<theta>)*(2*B) < G"
proof -
  obtain t where tpos: "0 < t" and tlt: "2*t*B < G"
    using exists_eps_aux[OF G B] by blast
  define t' where "t' = min t (1/2)"
  have t'pos: "0 < t'" unfolding t'_def using tpos by simp
  have t'le: "t' \<le> t" unfolding t'_def by simp
  have t'half: "t' \<le> 1/2" unfolding t'_def by simp
  have le2: "2*t' \<le> 2*t" using t'le by linarith
  have "2*t'*B \<le> 2*t*B" by (rule mult_right_mono[OF le2 B])
  then have lt: "2*t'*B < G" using tlt by linarith
  have eq: "(1 - (1 - t'))*(2*B) = 2*t'*B" by (simp add: algebra_simps)
  have th1: "0 < 1 - t'" using t'half by linarith
  have th2: "1 - t' < 1" using t'pos by linarith
  have final: "(1 - (1 - t'))*(2*B) < G" unfolding eq by (rule lt)
  show ?thesis by (rule exI[of _ "1 - t'"]) (intro conjI th1 th2 final)
qed

theorem max_principle_boundary_holds:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
  shows "max_principle_boundary k L K"
proof -
  have dim: "0 < CARD('n)" using kk by simp
  have clK: "closed K" by (rule compact_imp_closed[OF cK])
  show ?thesis
    unfolding max_principle_boundary_def
  proof (intro allI impI)
    fix u w :: "real^'n \<Rightarrow> real"
    assume subE: "visc_subsol_env k L K (interior K) u"
      and supE: "visc_supersol_env k L K (interior K) w"
      and cu: "continuous_on K u" and cw: "continuous_on K w"
    \<comment> \<open>Definition 3.1(b) yields the jet form once and for all\<close>
    have Kb: "bounded K" by (rule compact_imp_bounded[OF cK])
    obtain Bw where Bw: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    proof -
      have "bounded (w ` K)"
        by (rule compact_imp_bounded[OF compact_continuous_image[OF cw cK]])
      then obtain a where a: "\<forall>z \<in> w ` K. norm z \<le> a"
        unfolding bounded_iff by blast
      have "- a \<le> w y" if y: "y \<in> K" for y
      proof -
        have "norm (w y) \<le> a" using a y by blast
        then have "\<bar>w y\<bar> \<le> a" by simp
        then have "- (w y) \<le> a" by (simp add: abs_le_iff)
        then show ?thesis by linarith
      qed
      then show thesis by (rule that)
    qed
    have sup: "supersol_jet k L (interior K) w"
      by (rule visc_supersol_env_imp_jet
            [OF visc_supersol_env_imp_env2[OF supE] Kb Bw])
    obtain Bu where Bu: "\<And>y. y \<in> K \<Longrightarrow> u y \<le> Bu"
    proof -
      have "bounded (u ` K)"
        by (rule compact_imp_bounded[OF compact_continuous_image[OF cu cK]])
      then obtain a where a: "\<forall>z \<in> u ` K. norm z \<le> a"
        unfolding bounded_iff by blast
      have "u y \<le> a" if y: "y \<in> K" for y
      proof -
        have "norm (u y) \<le> a" using a y by blast
        then have "\<bar>u y\<bar> \<le> a" by simp
        then show ?thesis by (simp add: abs_le_iff)
      qed
      then show thesis by (rule that)
    qed
    have sub: "visc_subsol k L (interior K) u"
      by (rule visc_subsol_env_imp_visc_subsol
            [OF visc_subsol_env_imp_env2[OF subE] Kb Bu kk(1) kk(2) LL])
    show "\<exists>x \<in> K - interior K. \<forall>y \<in> K. u y - w y \<le> u x - w x"
    proof (rule ccontr)
      assume nb: "\<not> (\<exists>x \<in> K - interior K. \<forall>y \<in> K. u y - w y \<le> u x - w x)"
      \<comment> \<open>the global maximiser\<close>
      obtain xs where xsK: "xs \<in> K"
        and xsmax: "\<And>y. y \<in> K \<Longrightarrow> u y - w y \<le> u xs - w xs"
        using max_principle_boundary_attains[OF cK neK cu cw] by blast
      \<comment> \<open>the boundary is compact and nonempty\<close>
      have clS: "closed (K - interior K)"
        by (intro closed_Diff clK open_interior)
      have bS: "bounded (K - interior K)"
        by (rule bounded_subset[OF compact_imp_bounded[OF cK]]) blast
      have cpS: "compact (K - interior K)"
        using bS clS by (simp add: compact_eq_bounded_closed)
      have neS: "K - interior K \<noteq> {}"
        by (rule compact_frontier_nonempty[OF cK neK dim])
      have cS: "continuous_on (K - interior K) (\<lambda>y. u y - w y)"
        by (intro continuous_intros
            continuous_on_subset[OF cu Diff_subset]
            continuous_on_subset[OF cw Diff_subset])
      obtain xb where xbS: "xb \<in> K - interior K"
        and xbmax: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y - w y \<le> u xb - w xb"
        using continuous_attains_sup[OF cpS neS cS] by blast
      \<comment> \<open>the boundary maximum is STRICTLY below the global one\<close>
      have gap: "u xb - w xb < u xs - w xs"
      proof -
        from nb obtain y where yK: "y \<in> K"
          and ygt: "\<not> (u y - w y \<le> u xb - w xb)"
          using xbS by blast
        have "u xb - w xb < u y - w y" using ygt by linarith
        also have "u y - w y \<le> u xs - w xs" by (rule xsmax[OF yK])
        finally show ?thesis .
      qed
      \<comment> \<open>globally bounded, globally continuous replacements\<close>
      obtain Bu where Bu0: "0 \<le> Bu" and BuK: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> Bu"
        using bounded_on_compact[OF cK cu] by blast
      obtain Bw where Bw0: "0 \<le> Bw" and BwK: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> Bw"
        using bounded_on_compact[OF cK cw] by blast
      define B where "B = max Bu Bw"
      have B0: "0 \<le> B" unfolding B_def using Bu0 by simp
      have BuB: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B"
        unfolding B_def using BuK by (simp add: le_max_iff_disj)
      have BwB: "\<And>y. y \<in> K \<Longrightarrow> \<bar>w y\<bar> \<le> B"
        unfolding B_def using BwK by (simp add: le_max_iff_disj)
      obtain u' where cu': "continuous_on UNIV u'"
        and equ: "\<And>y. y \<in> K \<Longrightarrow> u' y = u y" and bu': "\<And>y. \<bar>u' y\<bar> \<le> B"
        using continuous_extension_bounded[OF clK cu B0 BuB] by blast
      obtain w' where cw': "continuous_on UNIV w'"
        and eqw: "\<And>y. y \<in> K \<Longrightarrow> w' y = w y" and bw': "\<And>y. \<bar>w' y\<bar> \<le> B"
        using continuous_extension_bounded[OF clK cw B0 BwB] by blast
      have sub': "visc_subsol k L (interior K) u'"
        by (rule visc_subsol_extend[OF sub equ])
      have sup': "supersol_jet k L (interior K) w'"
        by (rule supersol_jet_extend[OF sup eqw])
      \<comment> \<open>the \<open>\<theta>\<close>-scaling preserves the gap\<close>
      have Gpos: "0 < (u xs - w xs) - (u xb - w xb)" using gap by linarith
      obtain \<theta> where tpos: "0 < \<theta>" and tlt1: "\<theta> < 1"
        and tgap: "(1-\<theta>)*(2*B) < (u xs - w xs) - (u xb - w xb)"
        using theta_exists_aux[OF B0 Gpos] by blast
      have absu: "\<And>y. y \<in> K \<Longrightarrow> \<bar>u y\<bar> \<le> B" by (rule BuB)
      have strict: "\<theta> * u y - w y < \<theta> * u xs - w xs"
        if y: "y \<in> K - interior K" for y
        by (rule theta_gap_preserved
            [where u = u and w = w and K = K and B = B and \<theta> = \<theta>
               and M = "u xs - w xs" and m = "u xb - w xb"
               and xs = xs and S = "K - interior K" and y = y,
             OF absu less_imp_le[OF tlt1] tgap xsK order.refl
                Diff_subset xbmax y])
      \<comment> \<open>a uniform boundary bound for the scaled pair\<close>
      have cS2: "continuous_on (K - interior K) (\<lambda>y. \<theta> * u y - w y)"
        by (intro continuous_intros
            continuous_on_subset[OF cu Diff_subset]
            continuous_on_subset[OF cw Diff_subset])
      obtain xc where xcS: "xc \<in> K - interior K"
        and xcmax: "\<And>y. y \<in> K - interior K \<Longrightarrow>
            \<theta> * u y - w y \<le> \<theta> * u xc - w xc"
        using continuous_attains_sup[OF cpS neS cS2] by blast
      define mm where "mm = \<theta> * u xc - w xc"
      define MM where "MM = \<theta> * u xs - w xs"
      have mlt: "mm < MM" unfolding mm_def MM_def by (rule strict[OF xcS])
      \<comment> \<open>transfer everything to the extended data and close\<close>
      have bdry': "\<theta> * u' c - w' c \<le> mm" if c: "c \<in> K - interior K" for c
      proof -
        have cK': "c \<in> K" using c by simp
        have "\<theta> * u' c - w' c = \<theta> * u c - w c"
          unfolding equ[OF cK'] eqw[OF cK'] ..
        also have "\<dots> \<le> mm" unfolding mm_def by (rule xcmax[OF c])
        finally show ?thesis .
      qed
      have Mval': "MM \<le> \<theta> * u' xs - w' xs"
        unfolding MM_def equ[OF xsK] eqw[OF xsK] by simp
      have upu: "\<theta> * u' y \<le> \<theta> * B" for y
        by (rule mult_left_mono) (use bu'[of y] tpos in linarith)+
      have lou: "- (\<theta> * B) \<le> \<theta> * u' y" for y
      proof -
        have "\<theta> * (- B) \<le> \<theta> * u' y"
          by (rule mult_left_mono) (use bu'[of y] tpos in linarith)+
        then show ?thesis by simp
      qed
      have upw: "(- w') y \<le> B" for y using bw'[of y] by simp
      have low: "- B \<le> (- w') y" for y using bw'[of y] by simp
      have cuu: "continuous_on UNIV (\<lambda>y. \<theta> * u' y)"
        by (intro continuous_intros cu')
      \<comment> \<open>\<open>continuous_intros\<close> does not see through the FUNCTION-level negation
          \<open>- w'\<close>; unfold it to a lambda first\<close>
      have cww: "continuous_on UNIV (- w')"
      proof -
        have e: "(- w') = (\<lambda>y. - w' y)" by (rule ext) simp
        show ?thesis unfolding e by (intro continuous_intros cw')
      qed
      show False
        by (rule comparison_soft_complete
            [where u = u' and w = w' and K = K and \<theta> = \<theta>
               and Bu = "\<theta> * B" and Bw = B and Blu = "- (\<theta> * B)" and Blw = "- B"
               and z = xs and M = MM and m = mm,
             OF sub' sup' tpos tlt1 kk(1) kk(2) LL cK neK upu upw lou low
                cuu cww xsK Mval' bdry' mlt])
    qed
  qed
qed

section \<open>Uniqueness on a general compact set\<close>

text \<open>The first consequence of Theorem 4.2(a): two continuous viscosity
  solutions on compact \<open>K\<close> agreeing on \<open>K - interior K\<close> agree everywhere
  on \<open>K\<close>.  Both directions swap the roles of sub- and supersolution,
  putting the maximum of \<open>u - w\<close> on the boundary where it vanishes.
  This generalises the third clause of \<open>theorem_1_1_ball_fragment\<close>,
  previously available only for \<open>K = cball 0 r\<close> via the explicit
  Example 3.1 formula \<open>ball_v\<close>.\<close>

text \<open>The comparison principle proper, with ordered boundary data: a
  subsolution below a supersolution on the boundary stays below it
  throughout \<open>K\<close>.\<close>

theorem viscosity_uniqueness_compact:
  fixes K :: "(real^'n::finite) set" and u w :: "real^'n \<Rightarrow> real"
  assumes cK: "compact K" and neK: "K \<noteq> {}"
    and kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cu: "continuous_on K u" and cw: "continuous_on K w"
    and subu: "visc_subsol_env k L K (interior K) u"
    and supu: "visc_supersol_env k L K (interior K) u"
    and subw: "visc_subsol_env k L K (interior K) w"
    and supw: "visc_supersol_env k L K (interior K) w"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y = w y"
    and x: "x \<in> K"
  shows "u x = w x"
proof -
  have mpb: "max_principle_boundary k L K"
    by (rule max_principle_boundary_holds[OF cK neK kk(1) kk(2) LL])
  \<comment> \<open>\<open>u - w\<close> peaks on the boundary, where it vanishes\<close>
  have le: "u x \<le> w x"
  proof -
    obtain b where bB: "b \<in> K - interior K"
      and bmax: "\<And>y. y \<in> K \<Longrightarrow> u y - w y \<le> u b - w b"
      using mpb subu supw cu cw unfolding max_principle_boundary_def by blast
    have "u b - w b = 0" using bd[OF bB] by simp
    then have "u x - w x \<le> 0" using bmax[OF x] by linarith
    then show ?thesis by linarith
  qed
  \<comment> \<open>and the same with the roles swapped\<close>
  have ge: "w x \<le> u x"
  proof -
    obtain b where bB: "b \<in> K - interior K"
      and bmax: "\<And>y. y \<in> K \<Longrightarrow> w y - u y \<le> w b - u b"
      using mpb subw supu cw cu unfolding max_principle_boundary_def by blast
    have "w b - u b = 0" using bd[OF bB] by simp
    then have "w x - u x \<le> 0" using bmax[OF x] by linarith
    then show ?thesis by linarith
  qed
  from le ge show ?thesis by simp
qed

section \<open>Map of the Theorem 4.2(a) chain\<close>

text \<open>This theory is long enough that the order of the argument is not
  visible from the section headings; the chain in dependency order:

  1. The operator and its envelopes: \<open>ell_op_lsc_elliptic_le\<close>,
  \<open>ell_op_env_strict_contradiction\<close> give degenerate ellipticity for both
  envelopes and the closing contradiction off the origin;
  \<open>eq36_rhs_antitone\<close> handles \<open>p = 0\<close>.

  2. The doubling: \<open>doubling_maximiser_exists\<close>, \<open>doubling_dist_bound\<close>,
  \<open>doubling_grad_lower_bound\<close> give the maximising pair, the \<open>O(1/\<alpha>)\<close>
  penalty estimate, and a positive lower bound on the shared gradient.

  3. Doubled jet to component jets to operator bounds:
  \<open>doubled_supconv_jet_exists\<close>, \<open>doubled_jet_slices_at_max\<close>,
  \<open>jet_imp_local_max_test\<close>, \<open>visc_subsol_scaled_uniform\<close>.

  4. Removing corrections, and compactness:
  \<open>ell_op_lsc_le_of_nearby\<close> passes a bound at nearby points to the
  envelope, subsuming both the \<open>\<delta> I\<close> shift and Jensen's tilt;
  \<open>symmetric_form_bound\<close> and \<open>bounded_seq_limit_point\<close> turn
  quadratic-form bounds into a limiting matrix pair without the spectral
  theorem.

  5. Assembly from bounds rather than limits:
  \<open>comparison_supconv_bounded_family\<close>, \<open>tilted_doubled_psd_ordering\<close>.

  6. The instantiation: \<open>comparison_supconv_doubling_complete\<close> runs
  Jensen at shrinking tilts and discharges the geometric data, closing
  \<open>max_principle_boundary\<close>, which requires continuity of \<open>u\<close> and \<open>w\<close> on
  \<open>K\<close>.\<close>

section \<open>Boundary nonnegativity and the \<open>T\<^sub>\<iota>\<close> hypothesis\<close>

subsection \<open>A supersolution with the zero boundary condition is nonnegative\<close>

text \<open>Definition 3.1's boundary clause for the supersolution is active
  exactly where \<open>u\<^sub>* < 0\<close>: at a global minimum the constant test function
  touches from below, giving \<open>1 \<le> F^*(0,0) = 0\<close>, the paper's
  diagonal-case contradiction.  Stated with \<open>w\<close> itself lsc, as
  Proposition 4.1 feeds it.\<close>

theorem supersol_bc_nonneg:
  fixes w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}"
    and lscw: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bw: "\<And>y. y \<in> K \<Longrightarrow> Bw \<le> w y"
    and sup: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. w x < 0}) w"
  shows "\<And>x. x \<in> K \<Longrightarrow> 0 \<le> w x"
proof -
  fix x0 assume x0K: "x0 \<in> K"
  show "0 \<le> w x0"
  proof (rule ccontr)
    assume neg: "\<not> 0 \<le> w x0"
    obtain z where zK: "z \<in> K" and zmin: "\<And>y. y \<in> K \<Longrightarrow> w z \<le> w y"
      using lsc_attains_inf_ex[OF lscw Bw cK neK] by blast
    have wz0: "w z < 0" using zmin[OF x0K] neg by linarith
    have zO: "z \<in> interior K \<union> {x \<in> K - interior K. w x < 0}"
      using zK wz0 by (cases "z \<in> interior K") auto
    have tf: "test_fun_C2 (\<lambda>y. w z) (\<lambda>y. 0) 0 z" by (rule test_fun_C2_const)
    have touch: "\<forall>y\<in>K. w z - w z \<le> w y - w z" using zmin by simp
    have "1 \<le> ell_op_usc k L ((\<lambda>y. 0 :: real^'n) z) (0 :: real^'n^'n)"
      using sup[unfolded visc_supersol_env2_def] zO tf touch by blast
    then have one: "(1 :: ereal) \<le> ell_op_usc k L (0 :: real^'n) (0 :: real^'n^'n)"
      by simp
    have "ell_op_usc k L (0 :: real^'n) (0 :: real^'n^'n) < 1"
      by (rule ell_op_usc_zero_zero_lt_one[OF kk(1) kk(2) LL])
    then show False using one by simp
  qed
qed

subsection \<open>The \<open>T\<^sub>\<iota>\<close> hypothesis and its convex instance\<close>

text \<open>The paper's hypothesis on \<open>K\<close> for the uniqueness clause of Theorem 1.1:
  a family \<open>T\<^sub>\<iota>\<close> of rotation-dilation-translations, \<open>\<iota> \<in> (1,2]\<close>, with
  \<open>K \<subseteq> (T\<^sub>\<iota> \` K)^\<circ>\<close> and \<open>T\<^sub>\<iota> \<rightarrow> id\<close>, phrased as an \<open>\<epsilon>\<close>-statement with
  the inverse map written out so no invertibility side condition is
  carried.\<close>

definition expandable :: "(real^'n::finite) set \<Rightarrow> bool" where
  "expandable K \<longleftrightarrow>
     (\<forall>e > 0. \<exists>R b c. orthogonal_matrix R \<and> 1 < c \<and> c < 1 + e
        \<and> K \<subseteq> interior ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
        \<and> (\<forall>x \<in> K. dist ((1/c) *\<^sub>R (transpose R *v (x - b))) x \<le> e))"

theorem convex_expandable:
  fixes K :: "(real^'n::finite) set"
  assumes cK: "compact K" and cvx: "convex K" and iK: "interior K \<noteq> {}"
  shows "expandable K"
  unfolding expandable_def
proof (intro allI impI)
  fix e :: real assume e0: "0 < e"
  obtain x0 where x0: "x0 \<in> interior K" using iK by blast
  have neK: "K \<noteq> {}" using x0 interior_subset by blast
  then obtain y0 where y0K: "y0 \<in> K" by blast
  obtain a where a: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> a"
    using compact_imp_bounded[OF cK] unfolding bounded_iff by blast
  define D where "D = a + norm x0"
  have D0: "0 \<le> D"
    unfolding D_def using a[OF y0K] norm_ge_zero[of y0] norm_ge_zero[of x0]
    by linarith
  have Db: "norm (x - x0) \<le> D" if xK: "x \<in> K" for x
  proof -
    have "norm (x - x0) \<le> norm x + norm x0" by (rule norm_triangle_ineq4)
    also have "\<dots> \<le> a + norm x0" using a[OF xK] by simp
    finally show ?thesis unfolding D_def .
  qed

  text \<open>The dilation factor is \<open>e/(2(D+1))\<close> rather than \<open>e/(D+1)\<close>, so
  \<open>c < 1+e\<close> is strict even when \<open>D = 0\<close>.\<close>
  define A where "A = e / (2 * (D + 1))"
  have D1: "0 < D + 1" using D0 by linarith
  have A0: "0 < A" unfolding A_def using e0 D1 by simp
  have D1ne: "D + 1 \<noteq> 0" using D1 by simp
  have AD1: "A * (D + 1) = e / 2" unfolding A_def using D1ne by (simp add: field_simps)
  have Ae2: "A \<le> e / 2"
  proof -
    have "A * 1 \<le> A * (D + 1)" using A0 D0 by (simp add: mult_left_mono)
    then show ?thesis using AD1 by simp
  qed
  have ADe: "A * D \<le> e / 2"
  proof -
    have "A * D \<le> A * (D + 1)" using A0 by (simp add: mult_left_mono)
    then show ?thesis using AD1 by simp
  qed
  define c where "c = 1 + A"
  have c1: "1 < c" unfolding c_def using A0 by simp
  have cne: "c \<noteq> 0" using c1 by simp
  have c0: "0 < c" using c1 by simp
  have ce: "c < 1 + e" unfolding c_def using Ae2 e0 by linarith

  define T where "T = (\<lambda>x :: real^'n. c *\<^sub>R (mat 1 *v x) + (1 - c) *\<^sub>R x0)"
  have Teq: "T x = x0 + c *\<^sub>R (x - x0)" for x
    unfolding T_def by (simp add: algebra_simps)

  text \<open>\<open>T\<close> is an affine homeomorphism, so it maps the interior into the
    interior of the image.\<close>
  have Timg: "T ` S = (\<lambda>z. (x0 - c *\<^sub>R x0) + z) ` ((\<lambda>z. c *\<^sub>R z) ` S)"
    for S :: "(real^'n) set"
    unfolding image_image by (rule image_cong[OF refl]) (simp add: Teq algebra_simps)
  have opT: "open (T ` interior K)"
    unfolding Timg by (rule open_translation, rule open_scaling[OF cne open_interior])
  have Tint: "T ` interior K \<subseteq> interior (T ` K)"
    by (rule interior_maximal[OF image_mono[OF interior_subset] opT])

  have sub: "K \<subseteq> interior (T ` K)"
  proof
    fix x assume xK: "x \<in> K"
    define y where "y = x0 + (1/c) *\<^sub>R (x - x0)"
    have yint: "y \<in> interior K"
      unfolding y_def
      using mem_interior_closure_convex_shrink[OF cvx x0, of x "1 - 1/c"]
        xK c1 closure_subset
      by (auto simp: algebra_simps)
    have Ty: "T y = x"
      unfolding Teq y_def using cne by (simp add: algebra_simps)
    show "x \<in> interior (T ` K)" using Tint yint Ty by force
  qed

  have inv: "\<forall>x \<in> K. dist ((1/c) *\<^sub>R (transpose (mat 1) *v
      (x - (1 - c) *\<^sub>R x0))) x \<le> e"
  proof
    fix x assume xK: "x \<in> K"
    have mv: "transpose (mat 1 :: real^'n^'n) *v (x - (1 - c) *\<^sub>R x0)
        = x - (1 - c) *\<^sub>R x0"
      by simp
    have step1: "(1/c) *\<^sub>R (x - (1 - c) *\<^sub>R x0) - x = ((1/c) - 1) *\<^sub>R (x - x0)"
    proof -
      have sc: "(1/c) * (1 - c) = 1/c - 1" using cne by (simp add: field_simps)
      have "(1/c) *\<^sub>R (x - (1 - c) *\<^sub>R x0) - x
          = (1/c) *\<^sub>R x - ((1/c) * (1 - c)) *\<^sub>R x0 - x"
        by (simp add: scaleR_diff_right)
      also have "\<dots> = (1/c) *\<^sub>R x - (1/c - 1) *\<^sub>R x0 - x" unfolding sc by (rule refl)
      also have "\<dots> = ((1/c) - 1) *\<^sub>R (x - x0)"
        by (simp add: scaleR_diff_right scaleR_left_diff_distrib)
      finally show ?thesis .
    qed
    have cinv1: "1/c \<le> 1" using c1 by simp
    have shrink: "1 - 1/c \<le> A"
    proof -
      have d1: "0 \<le> c - 1" using c1 by linarith
      have "(c - 1) * 1 \<le> (c - 1) * c" using c1 d1 by (simp add: mult_left_mono)
      then have "c - 1 \<le> (c - 1) * c" by simp
      then have "(c - 1)/c \<le> c - 1" using c0 by (simp add: divide_le_eq)
      moreover have "1 - 1/c = (c - 1)/c" using cne by (simp add: field_simps)
      ultimately show ?thesis unfolding c_def by simp
    qed
    have "dist ((1/c) *\<^sub>R (transpose (mat 1 :: real^'n^'n) *v
        (x - (1 - c) *\<^sub>R x0))) x = norm (((1/c) - 1) *\<^sub>R (x - x0))"
      unfolding dist_norm mv step1 by (rule refl)
    also have "\<dots> = (1 - 1/c) * norm (x - x0)"
      using cinv1 by (simp add: abs_if)
    also have "\<dots> \<le> A * norm (x - x0)"
      by (rule mult_right_mono[OF shrink]) simp
    also have "\<dots> \<le> A * D" using A0 Db[OF xK] by (simp add: mult_left_mono)
    also have "\<dots> \<le> e / 2" by (rule ADe)
    also have "\<dots> \<le> e" using e0 by linarith
    finally show "dist ((1/c) *\<^sub>R (transpose (mat 1 :: real^'n^'n) *v
        (x - (1 - c) *\<^sub>R x0))) x \<le> e" .
  qed

  show "\<exists>R b c. orthogonal_matrix R \<and> 1 < c \<and> c < 1 + e
      \<and> K \<subseteq> interior ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
      \<and> (\<forall>x \<in> K. dist ((1/c) *\<^sub>R (transpose R *v (x - b))) x \<le> e)"
    by (rule exI[of _ "mat 1"], rule exI[of _ "(1 - c) *\<^sub>R x0"],
        rule exI[of _ c])
      (use c1 ce sub inv orthogonal_matrix_id T_def in auto)
qed

subsection \<open>Test functions compose with invertible affine maps\<close>

text \<open>\<open>matvec_add_right'\<close> is \<open>matvec_add_right\<close> from
  @{theory Relative_Arbitrage.Curvature_Operator}.\<close>

text \<open>\<open>matvec_scaleR_right'\<close> is \<open>matvec_scaleR_right\<close> from
  @{theory Relative_Arbitrage.Operator_Envelopes}.\<close>

lemma affine_linear:
  fixes R :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
proof -
  have "linear (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
    by (simp add: linear_iff matvec_add_right matvec_scaleR_right
        scaleR_right_distrib)
  then show ?thesis by (simp add: linear_conv_bounded_linear)
qed

lemma affine_has_derivative:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  shows "((\<lambda>z. c *\<^sub>R (R *v z) + b) has_derivative (\<lambda>h. c *\<^sub>R (R *v h))) (at y)"
proof -
  have lin: "((\<lambda>z :: real^'n. c *\<^sub>R (R *v z)) has_derivative
      (\<lambda>h. c *\<^sub>R (R *v h))) (at y)"
    by (rule bounded_linear.has_derivative[OF affine_linear has_derivative_ident])
  have "((\<lambda>z. c *\<^sub>R (R *v z) + b) has_derivative
      (\<lambda>h. c *\<^sub>R (R *v h) + 0)) (at y)"
    by (rule has_derivative_add[OF lin has_derivative_const])
  then show ?thesis by simp
qed

text \<open>The chain rule through \<open>A z = c \<cdot> Rz + b\<close>: the gradient picks up a
  factor \<open>c\<close> and a transpose, the Hessian a factor \<open>c^2\<close> and a
  conjugation - precisely what the invariances of \<open>F\<close> (display (4.4))
  undo.\<close>

theorem test_fun_at_affine:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and R :: "real^'n^'n" and b x :: "real^'n"
  assumes tf: "test_fun_at \<phi> g H (c *\<^sub>R (R *v x) + b)"
    and orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "test_fun_at (\<lambda>z. \<phi> (c *\<^sub>R (R *v z) + b))
      (\<lambda>z. c *\<^sub>R (transpose R *v g (c *\<^sub>R (R *v z) + b)))
      ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) x"
proof -
  define A :: "real^'n \<Rightarrow> real^'n" where "A = (\<lambda>z. c *\<^sub>R (R *v z) + b)"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have dA: "(A has_derivative (\<lambda>h. c *\<^sub>R (R *v h))) (at y)" for y
    unfolding A_def by (rule affine_has_derivative)
  have distA: "dist (A x) (A y) = c * dist x y" for y
  proof -
    have "A x - A y = c *\<^sub>R (R *v (x - y))"
      unfolding A_def by (simp add: matvec_diff_right scaleR_right_diff_distrib)
    then show ?thesis
      unfolding dist_norm using c0
      by (simp add: norm_orthogonal_matrix_vector[OF orth])
  qed
  obtain e where e0: "0 < e"
    and d: "\<And>y. y \<in> ball (A x) e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def A_def by blast
  have dg: "(g has_derivative (\<lambda>h. H *v h)) (at (A x))"
    using tf unfolding test_fun_at_def A_def by blast

  show ?thesis
    unfolding test_fun_at_def
  proof (intro conjI)
    show "transpose ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R))
        = (c\<^sup>2) *\<^sub>R (transpose R ** H ** R)"
    proof -
      have "transpose (transpose R ** H ** R)
          = transpose R ** transpose H ** transpose (transpose R)"
        by (simp add: matrix_transpose_mul matrix_mul_assoc)
      also have "\<dots> = transpose R ** H ** R" unfolding symH by simp
      finally show ?thesis by (simp add: transpose_scaleR)
    qed
  next
    have main: "((\<lambda>z. \<phi> (A z)) has_derivative
        (\<lambda>h. (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h)) (at y)"
      if yb: "dist x y < e / c" for y
    proof -
      have "dist (A x) (A y) = c * dist x y" by (rule distA)
      also have "\<dots> < c * (e / c)" by (rule mult_strict_left_mono[OF yb c0])
      also have "\<dots> = e" using c0 by simp
      finally have Ay: "A y \<in> ball (A x) e" by simp
      have chain: "((\<lambda>z. \<phi> (A z)) has_derivative
          (\<lambda>h. g (A y) \<bullet> (c *\<^sub>R (R *v h)))) (at y)"
        by (rule has_derivative_compose[OF dA d[OF Ay]])
      have req: "(\<lambda>h. g (A y) \<bullet> (c *\<^sub>R (R *v h)))
          = (\<lambda>h :: real^'n. (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h)"
      proof (rule ext)
        fix h :: "real^'n"
        have "g (A y) \<bullet> (c *\<^sub>R (R *v h)) = c * (g (A y) \<bullet> (R *v h))"
          by (rule inner_scaleR_right)
        also have "g (A y) \<bullet> (R *v h) = (transpose R *v g (A y)) \<bullet> h"
          by (rule inner_transpose_matrix)
        also have "c * ((transpose R *v g (A y)) \<bullet> h)
            = (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h"
          by (rule inner_scaleR_left[symmetric])
        finally show "g (A y) \<bullet> (c *\<^sub>R (R *v h))
            = (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h" .
      qed
      show ?thesis using chain unfolding req .
    qed
    show "\<exists>e>0. \<forall>y \<in> ball x e.
        ((\<lambda>z. \<phi> (c *\<^sub>R (R *v z) + b)) has_derivative
          (\<lambda>h. (c *\<^sub>R (transpose R *v g (c *\<^sub>R (R *v y) + b))) \<bullet> h)) (at y)"
    proof (intro exI[of _ "e / c"] conjI ballI)
      show "0 < e / c" using e0 c0 by simp
    next
      fix y assume "y \<in> ball x (e / c)"
      then have dy: "dist x y < e / c" by simp
      show "((\<lambda>z. \<phi> (c *\<^sub>R (R *v z) + b)) has_derivative
          (\<lambda>h. (c *\<^sub>R (transpose R *v g (c *\<^sub>R (R *v y) + b))) \<bullet> h)) (at y)"
        using main[OF dy] unfolding A_def .
    qed
  next
    have chain: "((\<lambda>z. g (A z)) has_derivative
        (\<lambda>h. H *v (c *\<^sub>R (R *v h)))) (at x)"
      by (rule has_derivative_compose[OF dA dg])
    have blinT: "bounded_linear (\<lambda>q :: real^'n. c *\<^sub>R (transpose R *v q))"
      by (rule affine_linear)
    have D: "((\<lambda>z. c *\<^sub>R (transpose R *v g (A z))) has_derivative
        (\<lambda>h. c *\<^sub>R (transpose R *v (H *v (c *\<^sub>R (R *v h)))))) (at x)"
      by (rule bounded_linear.has_derivative[OF blinT chain])
    have step: "c *\<^sub>R (transpose R *v (H *v (c *\<^sub>R (R *v h))))
        = ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) *v h" for h :: "real^'n"
    proof -
      have e1: "H *v (c *\<^sub>R (R *v h)) = c *\<^sub>R (H *v (R *v h))"
        by (rule matvec_scaleR_right)
      have e2: "transpose R *v (c *\<^sub>R (H *v (R *v h)))
          = c *\<^sub>R (transpose R *v (H *v (R *v h)))"
        by (rule matvec_scaleR_right)
      have e3: "transpose R *v (H *v (R *v h)) = (transpose R ** H ** R) *v h"
        by (metis matrix_vector_mul_assoc)
      have e4: "((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) *v h
          = (c\<^sup>2) *\<^sub>R ((transpose R ** H ** R) *v h)"
        by (simp add: matrix_vector_mult_def vec_eq_iff sum_distrib_left
            mult.assoc)
      have "c *\<^sub>R (transpose R *v (H *v (c *\<^sub>R (R *v h))))
          = c *\<^sub>R (c *\<^sub>R ((transpose R ** H ** R) *v h))"
        by (simp only: e1 e2 e3)
      also have "\<dots> = (c\<^sup>2) *\<^sub>R ((transpose R ** H ** R) *v h)"
        by (simp add: power2_eq_square)
      finally show ?thesis by (simp only: e4)
    qed
    have req: "(\<lambda>h :: real^'n. c *\<^sub>R (transpose R *v (H *v (c *\<^sub>R (R *v h)))))
        = (\<lambda>h. ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) *v h)"
      by (rule ext) (rule step)
    show "((\<lambda>z. c *\<^sub>R (transpose R *v g (c *\<^sub>R (R *v z) + b))) has_derivative
        (\<lambda>h. ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) *v h)) (at x)"
      using D unfolding req A_def .
  qed
qed

subsection \<open>The transformed supersolution --- Theorem 4.3's engine\<close>

text \<open>The paper's display (4.4) run backwards: the factors
  \<open>test_fun_at_affine\<close> introduces are exactly what \<open>ell_op_usc_scale\<close>
  and \<open>ell_op_usc_conj_rot\<close> remove.  The Hessian factor \<open>c^2\<close> cancels
  against the \<open>c^2\<close> in \<open>w'\<close> before the operator is applied, so no
  scaling invariance is needed for the Hessian argument.\<close>

text \<open>The \<open>C\<^sup>2\<close> counterparts of @{thm [source] test_fun_at_scaleR} and
  @{thm [source] test_fun_at_affine}.  Precomposing with \<open>z \<mapsto> c\<cdot>(R z) + b\<close>
  conjugates the Hessian field, \<open>G \<mapsto> c\<^sup>2 \<cdot> R\<^sup>T G(A \<cdot>) R\<close>, which stays symmetric
  and stays continuous --- the latter because conjugation is a linear map of
  matrices, hence bounded in finite dimension.\<close>

lemma test_fun_C2_scaleR:
  fixes H :: "real^'n::finite^'n"
  assumes tf: "test_fun_C2 \<phi> g H x" and c: "0 < c"
  shows "test_fun_C2 (\<lambda>z. c * \<phi> z) (\<lambda>z. c *\<^sub>R g z) (c *\<^sub>R H) x"
proof -
  obtain G where G: "\<And>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    "\<And>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)"
    "\<And>y. transpose (G y) = G y" "continuous_on UNIV G" "G x = H"
    using tf unfolding test_fun_C2_def by blast
  show ?thesis
    unfolding test_fun_C2_def
  proof (intro exI[of _ "\<lambda>y. c *\<^sub>R G y"] conjI allI)
    fix y :: "real^'n"
    have "((\<lambda>z. c * \<phi> z) has_derivative (\<lambda>h. c * (g y \<bullet> h))) (at y)"
      using G(1)[of y] by (auto intro!: derivative_eq_intros)
    then show "((\<lambda>z. c * \<phi> z) has_derivative (\<lambda>h. (c *\<^sub>R g y) \<bullet> h)) (at y)"
      by simp
  next
    fix y :: "real^'n"
    have "((\<lambda>z. c *\<^sub>R g z) has_derivative (\<lambda>h. c *\<^sub>R (G y *v h))) (at y)"
      using G(2)[of y] by (auto intro!: derivative_eq_intros)
    then show "((\<lambda>z. c *\<^sub>R g z) has_derivative (\<lambda>h. (c *\<^sub>R G y) *v h)) (at y)"
      by (simp add: scaleR_matrix_vector_assoc)
  next
    fix y :: "real^'n"
    show "transpose (c *\<^sub>R G y) = c *\<^sub>R G y"
      by (simp add: transpose_scaleR G(3))
  next
    show "continuous_on UNIV (\<lambda>y. c *\<^sub>R G y)"
      by (intro continuous_intros G(4))
  next
    show "c *\<^sub>R G x = c *\<^sub>R H" by (simp add: G(5))
  qed
qed

lemma conj_mat_continuous:
  fixes R :: "real^'n::finite^'n"
  assumes "continuous_on UNIV M"
  shows "continuous_on UNIV (\<lambda>y. transpose R ** M y ** R)"
proof -
  have lin: "linear (\<lambda>N :: real^'n^'n. transpose R ** N ** R)"
    unfolding linear_iff
    by (auto simp: matrix_matrix_mult_def vec_eq_iff sum.distrib
        sum_distrib_left sum_distrib_right algebra_simps)
  have bl: "bounded_linear (\<lambda>N :: real^'n^'n. transpose R ** N ** R)"
    using lin by (simp add: linear_conv_bounded_linear)
  show ?thesis by (rule bounded_linear.continuous_on[OF bl assms])
qed

theorem test_fun_C2_affine:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and R :: "real^'n^'n" and b x :: "real^'n"
  assumes tf: "test_fun_C2 \<phi> g H (c *\<^sub>R (R *v x) + b)"
    and orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "test_fun_C2 (\<lambda>z. \<phi> (c *\<^sub>R (R *v z) + b))
      (\<lambda>z. c *\<^sub>R (transpose R *v g (c *\<^sub>R (R *v z) + b)))
      ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) x"
proof -
  define A :: "real^'n \<Rightarrow> real^'n" where "A = (\<lambda>z. c *\<^sub>R (R *v z) + b)"
  obtain G where G: "\<And>y. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    "\<And>y. (g has_derivative (\<lambda>h. G y *v h)) (at y)"
    "\<And>y. transpose (G y) = G y" "continuous_on UNIV G" "G (A x) = H"
    using tf unfolding test_fun_C2_def A_def by blast
  have dA: "(A has_derivative (\<lambda>h. c *\<^sub>R (R *v h))) (at y)" for y
    unfolding A_def by (rule affine_has_derivative)
  have Acont: "continuous_on UNIV A"
    unfolding A_def by (intro continuous_intros)
  have GA: "continuous_on UNIV (\<lambda>y. G (A y))"
    by (rule continuous_on_compose2[OF G(4) Acont]) simp
  have main: "test_fun_C2 (\<lambda>z. \<phi> (A z))
      (\<lambda>z. c *\<^sub>R (transpose R *v g (A z)))
      ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) x"
    unfolding test_fun_C2_def
  proof (intro exI[of _ "\<lambda>y. (c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R)"] conjI allI)
    fix y :: "real^'n"
    have comp: "((\<lambda>z. \<phi> (A z)) has_derivative
        (\<lambda>h. g (A y) \<bullet> (c *\<^sub>R (R *v h)))) (at y)"
      by (rule has_derivative_compose[OF dA G(1)])
    have eq: "(\<lambda>h. g (A y) \<bullet> (c *\<^sub>R (R *v h)))
        = (\<lambda>h :: real^'n. (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h)"
    proof (rule ext)
      fix h :: "real^'n"
      have "g (A y) \<bullet> (c *\<^sub>R (R *v h)) = c * (g (A y) \<bullet> (R *v h))"
        by (rule inner_scaleR_right)
      also have "g (A y) \<bullet> (R *v h) = (transpose R *v g (A y)) \<bullet> h"
        by (rule inner_transpose_matrix)
      also have "c * ((transpose R *v g (A y)) \<bullet> h)
          = (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h"
        by (rule inner_scaleR_left[symmetric])
      finally show "g (A y) \<bullet> (c *\<^sub>R (R *v h))
          = (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h" .
    qed
    show "((\<lambda>z. \<phi> (A z)) has_derivative
        (\<lambda>h. (c *\<^sub>R (transpose R *v g (A y))) \<bullet> h)) (at y)"
      using comp unfolding eq .
  next
    fix y :: "real^'n"
    have dgA: "((\<lambda>z. g (A z)) has_derivative
        (\<lambda>h. G (A y) *v (c *\<^sub>R (R *v h)))) (at y)"
      by (rule has_derivative_compose[OF dA G(2)])
    have blT: "bounded_linear ((*v) (transpose R :: real^'n^'n))"
      by (rule matrix_vector_mul_bounded_linear)
    have d1: "((\<lambda>z. transpose R *v g (A z)) has_derivative
        (\<lambda>h. transpose R *v (G (A y) *v (c *\<^sub>R (R *v h))))) (at y)"
      by (rule bounded_linear.has_derivative[OF blT dgA])
    have d2: "((\<lambda>z. c *\<^sub>R (transpose R *v g (A z))) has_derivative
        (\<lambda>h. c *\<^sub>R (transpose R *v (G (A y) *v (c *\<^sub>R (R *v h)))))) (at y)"
      using d1 by (auto intro!: derivative_eq_intros)
    have eq2: "(\<lambda>h. c *\<^sub>R (transpose R *v (G (A y) *v (c *\<^sub>R (R *v h)))))
        = (\<lambda>h. ((c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R)) *v h)"
    proof (rule ext)
      fix h :: "real^'n"
      have "c *\<^sub>R (transpose R *v (G (A y) *v (c *\<^sub>R (R *v h))))
          = c *\<^sub>R (transpose R *v (c *\<^sub>R (G (A y) *v (R *v h))))"
        by (simp add: matvec_scaleR_right)
      also have "\<dots> = (c * c) *\<^sub>R (transpose R *v (G (A y) *v (R *v h)))"
        by (simp add: matvec_scaleR_right)
      also have "\<dots> = (c * c) *\<^sub>R ((transpose R ** G (A y) ** R) *v h)"
        by (simp add: matrix_vector_mul_assoc matrix_mul_assoc)
      also have "\<dots> = ((c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R)) *v h"
        by (simp add: power2_eq_square scaleR_matrix_vector_assoc)
      finally show "c *\<^sub>R (transpose R *v (G (A y) *v (c *\<^sub>R (R *v h))))
          = ((c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R)) *v h" .
    qed
    show "((\<lambda>z. c *\<^sub>R (transpose R *v g (A z))) has_derivative
        (\<lambda>h. ((c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R)) *v h)) (at y)"
      using d2 unfolding eq2 .
  next
    fix y :: "real^'n"
    have "transpose (transpose R ** G (A y) ** R)
        = transpose R ** transpose (G (A y)) ** transpose (transpose R)"
      by (simp add: matrix_transpose_mul matrix_mul_assoc)
    also have "\<dots> = transpose R ** G (A y) ** R" using G(3) by simp
    finally show "transpose ((c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R))
        = (c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R)"
      by (simp add: transpose_scaleR)
  next
    show "continuous_on UNIV (\<lambda>y. (c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R))"
      using conj_mat_continuous[OF GA] by (intro continuous_intros)
  next
    show "(c\<^sup>2) *\<^sub>R (transpose R ** G (A x) ** R)
        = (c\<^sup>2) *\<^sub>R (transpose R ** H ** R)" by (simp add: G(5))
  qed
  show ?thesis using main unfolding A_def .
qed

theorem visc_supersol_env_affine:
  fixes w :: "real^'n::finite \<Rightarrow> real" and K \<Omega> :: "(real^'n) set"
    and R :: "real^'n^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
    and sup: "visc_supersol_env2 k L K \<Omega> w"
  shows "visc_supersol_env2 k L ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
      ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` \<Omega>)
      (\<lambda>X. c\<^sup>2 * w ((1/c) *\<^sub>R (transpose R *v (X - b))))"
  unfolding visc_supersol_env2_def
proof (intro ballI allI impI)
  define T :: "real^'n \<Rightarrow> real^'n" where "T = (\<lambda>x. c *\<^sub>R (R *v x) + b)"
  define w' :: "real^'n \<Rightarrow> real"
    where "w' = (\<lambda>X. c\<^sup>2 * w ((1/c) *\<^sub>R (transpose R *v (X - b))))"
  have cne: "c \<noteq> 0" using c0 by simp
  have Tinv: "(1/c) *\<^sub>R (transpose R *v (T z - b)) = z" for z
  proof -
    have "T z - b = c *\<^sub>R (R *v z)" unfolding T_def by simp
    then have "transpose R *v (T z - b) = c *\<^sub>R (transpose R *v (R *v z))"
      by (simp add: matvec_scaleR_right)
    also have "transpose R *v (R *v z) = z"
      using orth unfolding orthogonal_matrix_def
      by (metis matrix_vector_mul_assoc matrix_vector_mul_lid)
    finally show ?thesis using cne by simp
  qed
  have wT: "w' (T z) = c\<^sup>2 * w z" for z unfolding w'_def Tinv by (rule refl)
  have c2: "0 < c\<^sup>2" using c0 by simp

  fix X assume XO: "X \<in> T ` \<Omega>"
  fix \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume tf: "test_fun_C2 \<phi> g H X"
  assume touch: "\<forall>Y \<in> T ` K. w' X - \<phi> X \<le> w' Y - \<phi> Y"
  from XO obtain x0 where x0: "x0 \<in> \<Omega>" and Xx: "X = T x0" by auto

  text \<open>Pull the test function back through \<open>T\<close> and divide by \<open>c\<^sup>2\<close>.\<close>
  have tfA: "test_fun_C2 (\<lambda>z. \<phi> (T z))
      (\<lambda>z. c *\<^sub>R (transpose R *v g (T z))) ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R)) x0"
    unfolding T_def
    using test_fun_C2_affine[OF tf[unfolded Xx T_def] orth c0] .
  have tfB: "test_fun_C2 (\<lambda>z. (1 / c\<^sup>2) * \<phi> (T z))
      (\<lambda>z. (1 / c\<^sup>2) *\<^sub>R (c *\<^sub>R (transpose R *v g (T z))))
      ((1 / c\<^sup>2) *\<^sub>R ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R))) x0"
    by (rule test_fun_C2_scaleR[OF tfA]) (use c2 in simp)
  have gsimp: "(\<lambda>z. (1 / c\<^sup>2) *\<^sub>R (c *\<^sub>R (transpose R *v g (T z))))
      = (\<lambda>z. (1/c) *\<^sub>R (transpose R *v g (T z)))"
    using cne by (simp add: power2_eq_square)
  have Hsimp: "(1 / c\<^sup>2) *\<^sub>R ((c\<^sup>2) *\<^sub>R (transpose R ** H ** R))
      = transpose R ** H ** R" using c2 by simp
  have tfC: "test_fun_C2 (\<lambda>z. (1 / c\<^sup>2) * \<phi> (T z))
      (\<lambda>z. (1/c) *\<^sub>R (transpose R *v g (T z))) (transpose R ** H ** R) x0"
    using tfB unfolding gsimp Hsimp .

  text \<open>The touching descends because \<open>c\<^sup>2 > 0\<close>.\<close>
  have touch': "\<forall>y \<in> K. w x0 - (1 / c\<^sup>2) * \<phi> (T x0)
      \<le> w y - (1 / c\<^sup>2) * \<phi> (T y)"
  proof
    fix y assume yK: "y \<in> K"
    then have "T y \<in> T ` K" by blast
    then have "w' (T x0) - \<phi> (T x0) \<le> w' (T y) - \<phi> (T y)"
      using touch unfolding Xx by blast
    then have le: "c\<^sup>2 * w x0 - \<phi> (T x0) \<le> c\<^sup>2 * w y - \<phi> (T y)" unfolding wT .
    have dc: "(1 / c\<^sup>2) * c\<^sup>2 = 1" using c2 by simp
    have "(1 / c\<^sup>2) * (c\<^sup>2 * w x0 - \<phi> (T x0))
        \<le> (1 / c\<^sup>2) * (c\<^sup>2 * w y - \<phi> (T y))"
      by (rule mult_left_mono[OF le]) (use c2 in simp)
    then show "w x0 - (1 / c\<^sup>2) * \<phi> (T x0) \<le> w y - (1 / c\<^sup>2) * \<phi> (T y)"
      using dc by (simp add: algebra_simps)
  qed

  have one: "1 \<le> ell_op_usc k L ((1/c) *\<^sub>R (transpose R *v g (T x0)))
      (transpose R ** H ** R)"
    using sup[unfolded visc_supersol_env2_def] x0 tfC touch' by blast

  text \<open>Now undo both factors with the invariances of \<open>F\<close>.\<close>
  have orthT: "orthogonal_matrix (transpose R)"
    using orth unfolding orthogonal_matrix_def by auto
  have "ell_op_usc k L ((1/c) *\<^sub>R (transpose R *v g X)) (transpose R ** H ** R)
      = ell_op_usc k L (transpose R *v g X) (transpose R ** H ** R)"
    by (rule ell_op_usc_scale) (use c0 in simp)
  also have "\<dots> = ell_op_usc k L (g X) H"
  proof -
    have "ell_op_usc k L (transpose R *v g X)
        (transpose R ** H ** transpose (transpose R)) = ell_op_usc k L (g X) H"
      by (rule ell_op_usc_conj_rot[OF orthT])
    then show ?thesis by simp
  qed
  finally show "1 \<le> ell_op_usc k L (g X) H" using one unfolding Xx by simp
qed

section \<open>Two-domain comparison, Theorem 4.3, Proposition 4.1\<close>

subsection \<open>The two-domain maximum principle: Theorem 4.2(b)\<close>

text \<open>Theorem 4.2(b): the two-domain comparison principle.  For \<open>u\<close> usc
  bounded on \<open>K\<close>, \<open>w\<close> lsc bounded on \<open>K' \<supseteq> K\<close> with
  \<open>K \<subseteq> interior K'\<close>, a subsolution/supersolution pair with \<open>u \<le> 0\<close> on
  \<open>\<partial>K\<close> and \<open>w \<ge> 0\<close> on \<open>K'\<close> satisfies \<open>u \<le> w\<close> on \<open>K\<close>.  The proof
  penalises with a quartic over the product,
  \<open>\<Phi>\<^sup>\<epsilon>(x,y) = \<kappa> u x - w y - \<epsilon>\<^sup>-\<^sup>1\<bar>x-y\<bar>\<^sup>4\<close>, \<open>\<kappa> \<in> (0,1)\<close>, and splits on
  where the maximiser converges as \<open>\<epsilon> \<rightarrow> 0\<close>: on the diagonal,
  Definition 3.1(b) gives \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>; in the interior of \<open>K\<close>,
  Crandall--Ishii and continuity of \<open>F\<close> off \<open>p = 0\<close> force \<open>\<kappa> \<ge> 1\<close>; on
  the boundary, the sign conditions on \<open>u\<close>, \<open>w\<close> force \<open>\<Phi>\<^sup>\<epsilon> \<le> 0\<close>,
  and \<open>\<kappa> \<up> 1\<close> gives the conclusion.  The two-domain setting makes the
  supersolution side's ball requirement free, since
  \<open>K \<subseteq> interior K'\<close> gives every point of \<open>K\<close> a neighbourhood inside
  \<open>K'\<close>.\<close>

subsection \<open>The gate fact, verified\<close>

text \<open>Definition 3.1(a)'s gate is open at every maximiser of the doubled
  functional, boundary or not, with no case-split on the sign of \<open>u\<close>.
  Stated for an arbitrary nonnegative penalty, so it applies to the
  paper's quartic and to \<open>soft_pen\<close> alike.\<close>

text \<open>The gate is inherited by the sup-convolution's attainment point: the
  Jensen step reads the subsolution property at that point, not at
  \<open>x^h\<close>, and it lies in Definition 3.1's gated \<open>\<Omega>\<close> since the attained
  value is \<open>\<ge> \<theta>u x^h > 0\<close>.\<close>

subsection \<open>The two-domain doubled maximiser\<close>

text \<open>Existence of the maximiser of \<open>\<theta>u(x)-w(y)-pen(x-y)\<close> over \<open>K \<times> K'\<close>
  for usc \<open>u\<close> and lsc \<open>w\<close>, needing no continuity: the objective is usc
  on the compact product, by the \<open>\<epsilon>\<close>-form calculus in @{theory Relative_Arbitrage.Operator_Envelopes} and
  \<open>usc_attains_sup_gen\<close>, stated there for an arbitrary metric space so
  it applies to the product.\<close>

text \<open>The \<open>y\<close>-side avoidance is free in the two-domain setting: \<open>K\<close> sits a
  positive distance inside \<open>K'\<close>, so once the penalty pins \<open>y^h\<close> near
  \<open>K\<close> it is interior to \<open>K'\<close>.  The \<open>x\<close>-side needs no analogue, since the
  gate lemmas put \<open>x^h\<close> in \<open>\<Omega>\<close> wherever it lands.\<close>

lemma two_domain_gap:
  fixes K K' :: "(real^'n::finite) set"
  assumes cK: "compact K" and cK': "compact K'" and sub: "K \<subseteq> interior K'"
  obtains d where "0 < d"
    and "\<And>x b. x \<in> K \<Longrightarrow> b \<in> K' - interior K' \<Longrightarrow> d < dist x b"
proof -
  have clB: "closed (K' - interior K')"
    by (intro closed_Diff compact_imp_closed[OF cK'] open_interior)
  have disj: "K \<inter> (K' - interior K') = {}" using sub by blast
  obtain d where d0: "0 < d"
    and dd: "\<And>x b. x \<in> K \<Longrightarrow> b \<in> K' - interior K' \<Longrightarrow> d \<le> dist x b"
    using separate_compact_closed[OF cK clB disj] by blast
  show ?thesis
  proof (rule that[of "d/2"])
    show "0 < d/2" using d0 by simp
    fix x b assume "x \<in> K" and "b \<in> K' - interior K'"
    from dd[OF this] show "d/2 < dist x b" using d0 by linarith
  qed
qed

theorem comparison_two_domain:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K K' :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}" and cK': "compact K'"
    and KK': "K \<subseteq> interior K'"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supw: "visc_supersol_env2 k L K' (interior K') w"
    and w0: "\<And>y. y \<in> K' \<Longrightarrow> 0 \<le> w y"
    and x: "x \<in> K"
  shows "u x \<le> w x"
proof (rule ccontr)
  assume "\<not> u x \<le> w x"
  then have fail: "w x < u x" by linarith
  have B0: "0 \<le> B" using Bu[of x] by linarith
  have uup: "u y \<le> B" for y using abs_le_D1[OF Bu[of y]] .
  have ulo: "- B \<le> u y" for y using abs_le_D2[OF Bu[of y]] by linarith
  have wupB: "w y \<le> B" for y using abs_le_D1[OF Bw[of y]] .
  have wloB: "- B \<le> w y" for y using abs_le_D2[OF Bw[of y]] by linarith
  have xK': "x \<in> K'" using x KK' interior_subset by blast
  have wx0: "0 \<le> w x" by (rule w0[OF xK'])
  have ux0: "0 < u x" using wx0 fail by linarith
  \<comment> \<open>abstract the quotient: \<open>linarith\<close> and \<open>simp\<close> handle an ATOM over \<open>2\<close>,
      not a compound\<close>
  define rr where "rr = w x / u x"
  have r0: "0 \<le> rr" unfolding rr_def
    using wx0 ux0 by (simp add: zero_le_divide_iff)
  have r1: "rr < 1" unfolding rr_def
    using fail ux0 by (simp add: divide_less_eq)
  define \<theta> where "\<theta> = (rr + 1) / 2"
  have t0: "0 < \<theta>" unfolding \<theta>_def using r0 by simp
  have t1: "\<theta> < 1" unfolding \<theta>_def using r1 by simp
  have rt: "rr < \<theta>" unfolding \<theta>_def using r1 by simp
  have "w x / u x < \<theta>" using rt unfolding rr_def .
  then have "w x < \<theta> * u x"
    using ux0 by (simp add: divide_less_eq mult.commute)
  then have Mp: "0 < \<theta> * u x - w x" by linarith
  define M where "M = \<theta> * u x - w x"
  have M0: "0 < M" unfolding M_def by (rule Mp)

  \<comment> \<open>1.  the \<open>w\<close>-side replacement: clipping at \<open>0\<close> costs nothing on \<open>K'\<close>,
      where \<open>w \<ge> 0\<close> already, and buys \<open>supconv (-w\<sim>) \<epsilon> \<le> 0\<close> --- which is what
      both the gate and the pinning need\<close>
  define wt where "wt = (\<lambda>y. max (w y) 0)"
  have wtnn: "0 \<le> wt y" for y unfolding wt_def by simp
  have wteq: "wt y = w y" if "y \<in> K'" for y
    unfolding wt_def using w0[OF that] by simp
  have wtB: "\<bar>wt y\<bar> \<le> B" for y
    unfolding wt_def using wupB[of y] wloB[of y] B0 by simp
  have negwt: "(- wt) y \<le> 0" for y using wtnn[of y] by simp
  have lowt: "- B \<le> (- wt) y" for y using wtB[of y] by simp
  have wlo: "\<And>y. y \<in> K' \<Longrightarrow> - B \<le> w y" using wloB by blast
  have supj0: "supersol_jet k L (interior K') w"
    by (rule visc_supersol_env_imp_jet
        [OF supw compact_imp_bounded[OF cK'] wlo])
  have supj: "supersol_jet k L (interior K') wt"
  proof (rule supersol_jet_cong_on[OF supj0 open_interior])
    fix y assume "y \<in> interior K'"
    then have "y \<in> K'" using interior_subset by blast
    then show "wt y = w y" by (rule wteq)
  qed
  have uwt: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> (- wt) y < c"
    if lt: "(- wt) z < c" for c z
  proof (cases "0 < c")
    case True
    show ?thesis
    proof (rule exI[of _ 1], intro conjI allI impI)
      show "(0::real) < 1" by simp
      fix y assume "dist z y < 1"
      show "(- wt) y < c" using True negwt[of y] by linarith
    qed
  next
    case False
    then have c0: "c \<le> 0" by linarith
    have "- max (w z) 0 < c" using lt unfolding wt_def by simp
    then have "0 < max (w z) 0" using c0 by linarith
    then have "max (w z) 0 = w z" by simp
    then have "- c < w z" using \<open>- max (w z) 0 < c\<close> by linarith
    from lscw[OF this] obtain e where e0: "0 < e"
      and h: "\<forall>y. dist z y < e \<longrightarrow> - c < w y" by blast
    show ?thesis
    proof (rule exI[of _ e], intro conjI allI impI e0)
      fix y assume "dist z y < e"
      then have "- c < w y" using h by blast
      then have "- w y < c" by linarith
      moreover have "(- wt) y \<le> - w y" unfolding wt_def by simp
      ultimately show "(- wt) y < c" by linarith
    qed
  qed

  \<comment> \<open>2.  the \<open>u\<close>-side extension: below the minimum, so the doubled functional
      cannot be maximised off \<open>K\<close>, and Definition 3.1(a) is untouched\<close>
  define C where "C = - B - 1"
  have Cneg: "C < 0" unfolding C_def using B0 by simp
  have CleB: "C \<le> - B" unfolding C_def by simp
  define ut where "ut = (\<lambda>y. if y \<in> K then u y else C)"
  have utK: "ut y = u y" if "y \<in> K" for y unfolding ut_def using that by simp
  have loK: "\<And>y. y \<in> K \<Longrightarrow> - B \<le> u y" using ulo by blast
  have utB: "ut y \<le> B" for y
  proof (cases "y \<in> K")
    case True
    then show ?thesis unfolding ut_def using uup[of y] by simp
  next
    case False
    then show ?thesis unfolding ut_def C_def using B0 by simp
  qed
  have BuA: "\<theta> * ut y \<le> B" for y
  proof (cases "0 \<le> ut y")
    case True
    have "\<theta> * ut y \<le> 1 * ut y"
      using True t1 by (intro mult_right_mono) simp_all
    then show ?thesis using utB[of y] by simp
  next
    case False
    have "\<theta> * ut y \<le> 0" using False t0 by (simp add: mult_nonneg_nonpos)
    then show ?thesis using B0 by linarith
  qed
  have uscut: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> ut y < c" if lt: "ut z < c" for c z
  proof -
    have lt': "(if z \<in> K then u z else C) < c" using lt unfolding ut_def .
    have "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> (if y \<in> K then u y else C) < c"
      by (rule usc_extend_const_below
          [OF compact_imp_closed[OF cK] uscu loK CleB lt'])
    then show ?thesis unfolding ut_def .
  qed
  have uut: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> \<theta> * ut y < c"
    if "\<theta> * ut z < c" for c z
    by (rule usc_eps_scale[OF uscut t0 that])
  have OmK: "interior K \<union> {q \<in> K - interior K. 0 < u q} \<subseteq> K"
    using interior_subset by blast
  have subenv: "visc_subsol_env2 k L K
      (interior K \<union> {q \<in> K - interior K. 0 < u q}) ut"
    by (rule visc_subsol_env_agrees[OF subu OmK]) (simp add: ut_def)
  have subloc: "visc_subsol k L
      (interior K \<union> {q \<in> K - interior K. 0 < u q}) ut"
    by (rule visc_subsol_env_imp_visc_subsol
        [OF subenv compact_imp_bounded[OF cK] _
            kk(1) kk(2) LL, where Bu = B])
      (use utB in simp)
  have gateK: "{q. 0 < ut q}
      \<subseteq> interior K \<union> {q \<in> K - interior K. 0 < u q}"
  proof
    fix q assume "q \<in> {q. 0 < ut q}"
    then have p: "0 < ut q" by simp
    have qK: "q \<in> K"
    proof (rule ccontr)
      assume "q \<notin> K"
      then have "ut q = C" unfolding ut_def by simp
      then show False using p Cneg by linarith
    qed
    then have pu: "0 < u q" using p unfolding ut_def by simp
    show "q \<in> interior K \<union> {q \<in> K - interior K. 0 < u q}"
      using qK pu by (cases "q \<in> interior K") auto
  qed
  have subgate: "visc_subsol k L {q. 0 < ut q} ut"
    by (rule visc_subsol_mono_dom[OF subloc gateK])

  \<comment> \<open>3.  the geometry: one gap, split three ways\<close>
  obtain dg where dg0: "0 < dg"
    and gap: "\<And>a b. a \<in> K \<Longrightarrow> b \<in> K' - interior K' \<Longrightarrow> dg < dist a b"
    using two_domain_gap[OF cK cK' KK'] by blast
  define kg where "kg = dg/8"
  define dQ where "dQ = dg/8"
  define bet where "bet = dg/8"
  have kg0: "0 < kg" unfolding kg_def using dg0 by simp
  have kgnn: "0 \<le> kg" using kg0 by linarith
  have dQ0: "0 < dQ" unfolding dQ_def using dg0 by simp
  have dQnn: "0 \<le> dQ" using dQ0 by linarith
  have bet0: "0 < bet" unfolding bet_def using dg0 by simp
  have betnn: "0 \<le> bet" using bet0 by linarith
  have fit: "bet + dQ + kg \<le> dg"
    unfolding bet_def dQ_def kg_def using dg0 by simp

  \<comment> \<open>4.  the confinement region\<close>
  define Q where "Q = {b + h |b h. b \<in> K \<and> h \<in> cball (0::real^'n) dQ}"
  have cQ: "compact Q" unfolding Q_def
    by (rule compact_sums[OF cK compact_cball])
  have xQ: "x \<in> Q"
  proof -
    have "(0::real^'n) \<in> cball 0 dQ" using dQnn by simp
    then have "x + 0 \<in> Q" unfolding Q_def using x by blast
    then show ?thesis by simp
  qed
  have Qnear: "\<exists>b\<in>K. dist q b \<le> dQ" if "q \<in> Q" for q
  proof -
    from that obtain b h where qeq: "q = b + h" and bK: "b \<in> K"
      and hb: "h \<in> cball (0::real^'n) dQ" unfolding Q_def by blast
    have "dist q b = norm h" unfolding qeq by (simp add: dist_norm)
    also have "\<dots> \<le> dQ" using hb by simp
    finally show ?thesis using bK by blast
  qed
  have Qfar: "dQ < dist q b" if qQ: "q \<notin> Q" and bK: "b \<in> K" for q b
  proof (rule ccontr)
    assume "\<not> dQ < dist q b"
    then have "dist q b \<le> dQ" by linarith
    then have "q - b \<in> cball (0::real^'n) dQ"
      by (simp add: dist_norm norm_minus_commute)
    moreover have "q = b + (q - b)" by simp
    ultimately have "q \<in> Q" unfolding Q_def using bK by blast
    then show False using qQ by blast
  qed

  \<comment> \<open>5.  \<open>\<epsilon>\<close> small: the far-field bound and the \<open>w\<close>-side radius\<close>
  define D where "D = max (B - \<theta>*C) B"
  define H where "H = min (dQ\<^sup>2) ((kg/4)\<^sup>2)"
  have Dnn: "0 \<le> D" unfolding D_def using B0 by simp
  have H0: "0 < H" unfolding H_def using dQ0 kg0 by simp
  obtain \<epsilon> where e0: "0 < \<epsilon>" and esm: "2*\<epsilon>*D < H"
    using exists_eps_aux[OF H0 Dnn] by blast
  have esm1: "2*\<epsilon>*(B - \<theta>*C) < dQ\<^sup>2"
  proof -
    have "2*\<epsilon>*(B - \<theta>*C) \<le> 2*\<epsilon>*D"
      unfolding D_def using e0 by (intro mult_left_mono) simp_all
    also have "\<dots> < H" by (rule esm)
    also have "H \<le> dQ\<^sup>2" unfolding H_def by simp
    finally show ?thesis .
  qed
  have esm2: "2*\<epsilon>*(0 - (- B)) < (kg/4)\<^sup>2"
  proof -
    have "2*\<epsilon>*(0 - (- B)) \<le> 2*\<epsilon>*D"
      unfolding D_def using e0 by (intro mult_left_mono) simp_all
    also have "\<dots> < H" by (rule esm)
    also have "H \<le> (kg/4)\<^sup>2" unfolding H_def by simp
    finally show ?thesis .
  qed

  \<comment> \<open>6.  \<open>\<kappa>\<^sub>P\<close> large: the pinning\<close>
  obtain kP where kP0: "0 < kP"
    and kPbig: "B < (kP/2)*bet\<^sup>2 - kP*(sqrt (bet\<^sup>2 + 1) - 1)"
    using soft_pen_kappa_exists[OF bet0, of B] by blast
  have kPnn: "0 \<le> kP" using kP0 by linarith

  \<comment> \<open>7.  the doubled maximiser over \<open>UNIV \<times> K'\<close>\<close>
  define A where "A = supconv (\<lambda>y. \<theta> * ut y) \<epsilon>"
  define Bf where "Bf = supconv (- wt) \<epsilon>"
  have cA: "continuous_on UNIV A"
    unfolding A_def by (rule supconv_continuous[OF BuA e0])
  have cB: "continuous_on UNIV Bf"
    unfolding Bf_def by (rule supconv_continuous[OF negwt e0])
  have Ale: "A y \<le> B" for y unfolding A_def by (rule supconv_le[OF BuA e0])
  have Bfle: "Bf y \<le> 0" for y unfolding Bf_def by (rule supconv_le[OF negwt e0])
  have out: "A q \<le> \<theta>*C" if qQ: "q \<notin> Q" for q
  proof -
    have far: "\<And>b. b \<in> K \<Longrightarrow> dQ < dist q b" using Qfar[OF qQ] by blast
    have Bu': "\<And>y. \<theta> * (if y \<in> K then u y else C) \<le> B"
      using BuA unfolding ut_def by simp
    show ?thesis
      unfolding A_def ut_def
      by (rule supconv_extend_far_le[OF Bu' e0 dQnn esm1 far])
  qed
  have base: "M \<le> A x + Bf x - soft_pen kP (x - x)"
  proof -
    have a1: "\<theta> * ut x \<le> A x" unfolding A_def by (rule supconv_ge[OF BuA e0])
    have a2: "(- wt) x \<le> Bf x" unfolding Bf_def by (rule supconv_ge[OF negwt e0])
    have a3: "\<theta> * ut x = \<theta> * u x" using utK[OF x] by simp
    have a4: "(- wt) x = - w x" using wteq[OF xK'] by simp
    have a5: "soft_pen kP (x - x) = 0" by (simp add: soft_pen_zero)
    show ?thesis unfolding M_def a5 using a1 a2 a3 a4 by linarith
  qed
  have gapv: "\<theta>*C + 0 < A x + Bf x - soft_pen kP (x - x)"
  proof -
    have "\<theta>*C < 0" using t0 Cneg by (simp add: mult_pos_neg)
    then show ?thesis using base M0 by linarith
  qed
  obtain xh yh where xhQ: "xh \<in> Q" and yhK': "yh \<in> K'"
    and mxU: "\<And>a q. q \<in> K' \<Longrightarrow>
        A a + Bf q - soft_pen kP (a - q)
        \<le> A xh + Bf yh - soft_pen kP (xh - yh)"
    using doubled_maximiser_over_UNIV_snd
      [OF cQ cK' cA cB soft_pen_continuous xQ xK' Bfle
          soft_pen_nonneg[OF kPnn] out gapv]
    by blast
  have Mmax: "M \<le> A xh + Bf yh - soft_pen kP (xh - yh)"
    using base mxU[OF xK', of x] by linarith

  \<comment> \<open>8.  the gate at the maximiser, and the pinning\<close>
  have Axh: "0 < A xh"
    using Mmax Bfle[of yh] soft_pen_nonneg[OF kPnn, of "xh - yh"] M0 by linarith
  obtain ru where ru0: "0 < ru" and posb: "\<And>a. dist a xh \<le> ru \<Longrightarrow> 0 < A a"
    using cont_pos_near[OF cA Axh] by blast
  have M0': "0 \<le> M" using M0 by linarith
  have pin: "norm (xh - yh) < bet"
    by (rule pin_of_penalty_bound
        [where A = A and Bfun = Bf and xh = xh and yh = yh
           and \<kappa>\<^sub>P = kP and \<beta> = bet and Bu = B and M = M,
         OF kPnn betnn Ale Bfle M0' Mmax kPbig])
  obtain q where qK: "q \<in> K" and dq: "dist xh q \<le> dQ"
    using Qnear[OF xhQ] by blast
  have fary: "kg < dist yh b" if bK: "b \<in> K' - interior K' " for b
    by (rule fary_of_pin[OF gap qK dq pin fit bK])
  have insy: "cball yh kg \<subseteq> interior K'"
    by (rule cball_subset_interior_of_far_from_boundary
        [OF compact_imp_closed[OF cK'] yhK' kgnn fary])
  have mxU': "\<And>a q. q \<in> K' \<Longrightarrow>
      supconv (\<lambda>y. \<theta> * ut y) \<epsilon> a + supconv (- wt) \<epsilon> q - soft_pen kP (a - q)
      \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> yh
        - soft_pen kP (xh - yh)"
    using mxU unfolding A_def Bf_def .
  have posb': "\<And>a. dist a xh \<le> ru \<Longrightarrow> 0 < supconv (\<lambda>y. \<theta> * ut y) \<epsilon> a"
    using posb unfolding A_def .

  \<comment> \<open>9.  the two branches\<close>
  show False
  proof (cases "xh = yh")
    case False
    show False
      by (rule comparison_2dom_off_diagonal
          [where u = ut and w = wt and K' = K' and \<theta> = \<theta> and \<epsilon> = \<epsilon>
             and Bu = B and Bw = 0 and Blw = "- B" and \<kappa>\<^sub>g = kg
             and \<kappa>\<^sub>P = kP and xh = xh and yh = yh and \<rho>\<^sub>u = ru,
           OF subgate supj t0 t1 kk(1) kk(2) LL BuA negwt lowt uut uwt
              e0 kg0 kP0 compact_imp_closed[OF cK'] yhK' mxU' fary
              esm2 ru0 posb' False])
  next
    case True
    have xhK'2: "xh \<in> K'" using yhK' True by simp
    have pint: "xh \<in> interior K'"
      using insy True kgnn by auto
    have subwd: "cball xh (kg/4) \<subseteq> interior K'"
    proof -
      have "cball xh (kg/4) \<subseteq> cball yh kg"
        using True kg0 by (simp add: cball_subset_cball_iff)
      then show ?thesis using insy by blast
    qed
    have radd: "sqrt (max 0 (2*\<epsilon>*(0 - (- wt) xh))) < kg/4"
      by (rule supconv_radius_uniform[OF lowt e0 _ esm2]) (use kg0 in simp)
    have mxd: "\<And>a q. a \<in> K' \<Longrightarrow> q \<in> K' \<Longrightarrow>
        supconv (\<lambda>y. \<theta> * ut y) \<epsilon> a + supconv (- wt) \<epsilon> q
          - soft_pen kP (a - q)
        \<le> supconv (\<lambda>y. \<theta> * ut y) \<epsilon> xh + supconv (- wt) \<epsilon> xh
          - soft_pen kP (xh - xh)"
      using mxU' unfolding True[symmetric] by blast
    show False
      by (rule comparison_soft_diagonal
          [where w = wt and K = K' and A = "supconv (\<lambda>y. \<theta> * ut y) \<epsilon>"
             and \<epsilon> = \<epsilon> and \<kappa>\<^sub>P = kP and p = xh and R\<^sub>w = "kg/4" and Bw = 0,
           OF supj kk(1) kk(2) LL negwt uwt e0 xhK'2 pint mxd radd subwd])
  qed
qed

subsection \<open>Theorem 4.3, on top of the two-domain principle\<close>

text \<open>Two small facts about the inverse of the dilation, used to transfer
  lower semicontinuity and the bound to the transformed supersolution.\<close>

lemma affine_inv_dist:
  fixes R :: "real^'n::finite^'n" and b :: "real^'n"
  assumes orth: "orthogonal_matrix R" and c0: "0 < c"
  shows "dist ((1/c) *\<^sub>R (transpose R *v (X - b)))
             ((1/c) *\<^sub>R (transpose R *v (Y - b))) = (1/c) * dist X Y"
proof -
  have orthT: "orthogonal_matrix (transpose R)"
    using orth unfolding orthogonal_matrix_def by auto
  have e1: "transpose R *v (X - b) - transpose R *v (Y - b)
      = transpose R *v (X - Y)"
  proof -
    have "transpose R *v (X - b) - transpose R *v (Y - b)
        = transpose R *v ((X - b) - (Y - b))"
      by (rule matvec_diff_right[symmetric])
    also have "(X - b) - (Y - b) = X - Y" by simp
    finally show ?thesis .
  qed
  have d: "(1/c) *\<^sub>R (transpose R *v (X - b)) - (1/c) *\<^sub>R (transpose R *v (Y - b))
      = (1/c) *\<^sub>R (transpose R *v (X - Y))"
  proof -
    have "(1/c) *\<^sub>R (transpose R *v (X - b)) - (1/c) *\<^sub>R (transpose R *v (Y - b))
        = (1/c) *\<^sub>R (transpose R *v (X - b) - transpose R *v (Y - b))"
      by (rule scaleR_right_diff_distrib[symmetric])
    also have "\<dots> = (1/c) *\<^sub>R (transpose R *v (X - Y))" unfolding e1 by (rule refl)
    finally show ?thesis .
  qed
  have nn: "norm (transpose R *v (X - Y)) = norm (X - Y)"
    by (rule norm_orthogonal_matrix_vector[OF orthT])
  have "dist ((1/c) *\<^sub>R (transpose R *v (X - b)))
      ((1/c) *\<^sub>R (transpose R *v (Y - b)))
      = norm ((1/c) *\<^sub>R (transpose R *v (X - Y)))"
    unfolding dist_norm d by (rule refl)
  also have "\<dots> = \<bar>1/c\<bar> * norm (transpose R *v (X - Y))" by (rule norm_scaleR)
  also have "\<dots> = (1/c) * norm (X - Y)" unfolding nn using c0 by simp
  finally show ?thesis unfolding dist_norm .
qed

text \<open>The paper's Theorem 4.3, in the form Proposition 4.1 consumes: for usc
  bounded \<open>u\<close> and lsc bounded \<open>w\<close> both satisfying Definition 3.1's
  boundary condition on an expandable \<open>K\<close>, \<open>u \<le> w^*\<close> on \<open>K\<close>.  The
  \<open>\<iota> \<down> 1\<close> limit is taken along \<open>e\<^sub>j = 1/Suc j\<close>.\<close>

theorem comparison_expandable:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and lscw: "\<And>c z. c < w z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < w y"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supw: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. w x < 0}) w"
    and x: "x \<in> K"
  shows "u x \<le> usc_env w x"
proof -
  have wB: "w y \<le> B" for y using Bw[of y] by (simp add: abs_le_iff)
  have wlb: "- B \<le> w y" for y using Bw[of y] by (simp add: abs_le_iff)
  have w0K: "\<And>y. y \<in> K \<Longrightarrow> 0 \<le> w y"
  proof -
    have lb: "\<And>y. y \<in> K \<Longrightarrow> - B \<le> w y" using wlb by blast
    show "\<And>y. y \<in> K \<Longrightarrow> 0 \<le> w y"
      by (rule supersol_bc_nonneg[OF kk(1) kk(2) LL cK neK lscw lb supw])
  qed

  text \<open>One dilation step: \<open>u x \<le> c\<^sup>2 \<cdot> w z\<close> with \<open>z\<close> within \<open>e\<close> of \<open>x\<close>.\<close>
  have step: "\<exists>z c. dist z x \<le> e \<and> 1 < c \<and> c < 1 + e
      \<and> u x \<le> c\<^sup>2 * w z" if e0: "0 < e" for e
  proof -
    obtain R b c where orth: "orthogonal_matrix R" and c1: "1 < c"
      and ce: "c < 1 + e"
      and Ksub: "K \<subseteq> interior ((\<lambda>z. c *\<^sub>R (R *v z) + b) ` K)"
      and Tclose: "\<forall>z \<in> K. dist ((1/c) *\<^sub>R (transpose R *v (z - b))) z \<le> e"
      using expK unfolding expandable_def using e0 by blast
    define T where "T = (\<lambda>z :: real^'n. c *\<^sub>R (R *v z) + b)"
    define S where "S = (\<lambda>Y :: real^'n. (1/c) *\<^sub>R (transpose R *v (Y - b)))"
    define w' where "w' = (\<lambda>Y. c\<^sup>2 * w (S Y))"
    have c0: "0 < c" using c1 by linarith
    have c2: "0 < c\<^sup>2" using c0 by simp
    have ST: "S (T z) = z" for z unfolding S_def T_def by (rule affine_inv_left[OF orth c0])
    have TS: "T (S Y) = Y" for Y unfolding S_def T_def by (rule affine_inv_right[OF orth c0])

    text \<open>\<open>T ` K\<close> is compact and contains \<open>K\<close> in its interior.\<close>
    have contT: "continuous_on UNIV T"
    proof -
      have "continuous_on UNIV (\<lambda>z :: real^'n. c *\<^sub>R (R *v z))"
        by (rule bounded_linear.continuous_on[OF affine_linear continuous_on_id])
      then show ?thesis unfolding T_def by (intro continuous_intros)
    qed
    have cTK: "compact (T ` K)"
      by (rule compact_continuous_image[OF continuous_on_subset[OF contT subset_UNIV] cK])
    have KTK: "K \<subseteq> interior (T ` K)" using Ksub unfolding T_def .

    text \<open>The transformed supersolution, on the full interior of \<open>T ` K\<close>.\<close>
    have supa: "visc_supersol_env2 k L (T ` K)
        (T ` (interior K \<union> {x \<in> K - interior K. w x < 0})) w'"
      unfolding T_def w'_def S_def
      by (rule visc_supersol_env_affine[OF orth c0 supw])
    have intTK: "interior (T ` K) = T ` interior K"
      unfolding T_def by (rule affine_interior_image[OF orth c0])
    have supw': "visc_supersol_env2 k L (T ` K) (interior (T ` K)) w'"
      by (rule visc_supersol_env2_mono[OF supa]) (use intTK in blast)

    text \<open>Lower semicontinuity, bound and nonnegativity of \<open>w'\<close>.\<close>
    have lscw': "\<exists>ee>0. \<forall>Y. dist Z Y < ee \<longrightarrow> d < w' Y" if lt: "d < w' Z" for d Z
    proof -
      have "d / c\<^sup>2 < w (S Z)" using lt c2 unfolding w'_def by (simp add: field_simps)
      then obtain ee where ee0: "0 < ee"
        and eey: "\<forall>y. dist (S Z) y < ee \<longrightarrow> d / c\<^sup>2 < w y" using lscw by blast
      have "d < w' Y" if dY: "dist Z Y < c * ee" for Y
      proof -
        have "dist (S Z) (S Y) = (1/c) * dist Z Y"
          unfolding S_def by (rule affine_inv_dist[OF orth c0])
        also have "\<dots> < (1/c) * (c * ee)"
          by (rule mult_strict_left_mono[OF dY]) (use c0 in simp)
        also have "\<dots> = ee" using c0 by simp
        finally have "d / c\<^sup>2 < w (S Y)" using eey by blast
        then show ?thesis unfolding w'_def using c2 by (simp add: field_simps)
      qed
      then show ?thesis using ee0 c0 by (intro exI[of _ "c * ee"]) auto
    qed
    have Bw': "\<bar>w' Y\<bar> \<le> c\<^sup>2 * B" for Y
    proof -
      have "\<bar>w' Y\<bar> = c\<^sup>2 * \<bar>w (S Y)\<bar>" unfolding w'_def using c2 by (simp add: abs_mult)
      also have "\<dots> \<le> c\<^sup>2 * B" using Bw[of "S Y"] c2 by (simp add: mult_left_mono)
      finally show ?thesis .
    qed
    have w'0: "0 \<le> w' Y" if Y: "Y \<in> T ` K" for Y
    proof -
      from Y obtain z where zK: "z \<in> K" and Yz: "Y = T z" by auto
      have "S Y = z" unfolding Yz by (rule ST)
      then show ?thesis unfolding w'_def using w0K[OF zK] c2 by simp
    qed
    have BuB: "\<bar>u y\<bar> \<le> c\<^sup>2 * B" for y
    proof -
      have B0: "0 \<le> B" using Bu[of x] by simp
      have c2ge: "1 \<le> c\<^sup>2"
      proof -
        have "1 * 1 \<le> c * c" using c1 by (intro mult_mono) auto
        then show ?thesis by (simp add: power2_eq_square)
      qed
      have "\<bar>u y\<bar> \<le> B" by (rule Bu)
      also have "B = 1 * B" by simp
      also have "\<dots> \<le> c\<^sup>2 * B" by (rule mult_right_mono[OF c2ge B0])
      finally show ?thesis .
    qed

    text \<open>Apply the two-domain comparison on \<open>(K, T ` K)\<close>.\<close>
    have "u x \<le> w' x"
      by (rule comparison_two_domain
          [OF kk LL cK neK cTK KTK uscu lscw' BuB Bw' subu supw' w'0 x])
    then have uxw: "u x \<le> c\<^sup>2 * w (S x)" unfolding w'_def .
    have dSx: "dist (S x) x \<le> e" unfolding S_def using Tclose x by blast
    show ?thesis
      by (rule exI[of _ "S x"], rule exI[of _ c]) (use dSx c1 ce uxw in blast)
  qed

  text \<open>Let \<open>e \<down> 0\<close> and read off the upper envelope.\<close>
  have main: "d \<le> usc_env w x" if d: "d < u x" for d
  proof -
    have "\<forall>j. \<exists>p. dist (fst p) x \<le> 1 / real (Suc j) \<and> 1 < snd p
        \<and> snd p < 1 + 1 / real (Suc j) \<and> u x \<le> (snd p)\<^sup>2 * w (fst p)"
    proof
      fix j :: nat
      have "0 < 1 / real (Suc j)" by simp
      from step[OF this] obtain z cc where
        "dist z x \<le> 1 / real (Suc j)" "1 < cc" "cc < 1 + 1 / real (Suc j)"
        "u x \<le> cc\<^sup>2 * w z" by blast
      then show "\<exists>p. dist (fst p) x \<le> 1 / real (Suc j) \<and> 1 < snd p
          \<and> snd p < 1 + 1 / real (Suc j) \<and> u x \<le> (snd p)\<^sup>2 * w (fst p)"
        by (intro exI[of _ "(z, cc)"]) simp
    qed
    then obtain p where
      pd: "\<And>j. dist (fst (p j)) x \<le> 1 / real (Suc j)"
      and pc1: "\<And>j. 1 < snd (p j)"
      and pce: "\<And>j. snd (p j) < 1 + 1 / real (Suc j)"
      and pux: "\<And>j. u x \<le> (snd (p j))\<^sup>2 * w (fst (p j))" by metis
    define zs where "zs = (\<lambda>j. fst (p j))"
    define cs where "cs = (\<lambda>j. snd (p j))"
    have nul: "(\<lambda>j. 1 / real (Suc j)) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_Suc[OF lim_1_over_n])
    have lim: "zs \<longlonglongrightarrow> x"
    proof (rule metric_LIMSEQ_I)
      fix r :: real assume r0: "0 < r"
      obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> \<bar>1 / real (Suc j) - 0\<bar> < r"
        using nul r0 unfolding lim_sequentially by (metis dist_real_def)
      show "\<exists>N. \<forall>j\<ge>N. dist (zs j) x < r"
      proof (intro exI[of _ N] allI impI)
        fix j assume "N \<le> j"
        have "dist (zs j) x \<le> 1 / real (Suc j)" unfolding zs_def by (rule pd)
        also have "\<dots> < r" using N[OF \<open>N \<le> j\<close>] by simp
        finally show "dist (zs j) x < r" .
      qed
    qed
    have cslim: "cs \<longlonglongrightarrow> 1"
    proof (rule metric_LIMSEQ_I)
      fix r :: real assume r0: "0 < r"
      obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> \<bar>1 / real (Suc j) - 0\<bar> < r"
        using nul r0 unfolding lim_sequentially by (metis dist_real_def)
      show "\<exists>N. \<forall>j\<ge>N. dist (cs j) 1 < r"
      proof (intro exI[of _ N] allI impI)
        fix j assume "N \<le> j"
        have "1 < cs j" unfolding cs_def by (rule pc1)
        moreover have "cs j < 1 + 1 / real (Suc j)" unfolding cs_def by (rule pce)
        moreover have "1 / real (Suc j) < r" using N[OF \<open>N \<le> j\<close>] by simp
        ultimately show "dist (cs j) 1 < r" by (simp add: dist_real_def)
      qed
    qed
    have sqlim: "(\<lambda>j. u x / (cs j)\<^sup>2) \<longlonglongrightarrow> u x"
    proof -
      have "(\<lambda>j. (cs j)\<^sup>2) \<longlonglongrightarrow> 1\<^sup>2" by (intro tendsto_intros cslim)
      then have sq: "(\<lambda>j. (cs j)\<^sup>2) \<longlonglongrightarrow> 1" by simp
      have "(\<lambda>j. u x / (cs j)\<^sup>2) \<longlonglongrightarrow> u x / 1"
        by (rule tendsto_divide[OF tendsto_const sq]) simp
      then show ?thesis by simp
    qed
    obtain N where N: "\<And>j. N \<le> j \<Longrightarrow> d < u x / (cs j)\<^sup>2"
      using order_tendstoD(1)[OF sqlim d] unfolding eventually_sequentially by blast
    have lo: "d \<le> w (zs (j + N))" for j
    proof -
      have cN: "1 < cs (j + N)" unfolding cs_def by (rule pc1)
      then have cN2: "0 < (cs (j + N))\<^sup>2" by simp
      have "d < u x / (cs (j + N))\<^sup>2" by (rule N) simp
      then have d1: "d * (cs (j + N))\<^sup>2 < u x"
        using cN2 by (simp add: divide_le_eq pos_less_divide_eq)
      have d2: "u x \<le> (cs (j + N))\<^sup>2 * w (zs (j + N))"
        unfolding cs_def zs_def by (rule pux)
      have "d * (cs (j + N))\<^sup>2 < w (zs (j + N)) * (cs (j + N))\<^sup>2"
        using d1 d2 by (simp add: mult.commute)
      then have "d < w (zs (j + N))"
        by (rule mult_right_less_imp_less[OF _ less_imp_le[OF cN2]])
      then show ?thesis by linarith
    qed
    have lim': "(\<lambda>j. zs (j + N)) \<longlonglongrightarrow> x"
      using lim by (rule LIMSEQ_ignore_initial_segment)
    show ?thesis
      by (rule usc_env_limsup_bound
          [where u = w and zs = "\<lambda>j. zs (j + N)" and x = x and c = d and B = B,
           OF wB lim' lo])
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> u x \<le> usc_env w x"
    then have lt: "usc_env w x < u x" by simp
    obtain d where d1: "usc_env w x < d" and d2: "d < u x"
      using lt dense by blast
    have "d \<le> usc_env w x" by (rule main[OF d2])
    then show False using d1 by linarith
  qed
qed

subsection \<open>Proposition 4.1: uniqueness among bounded usc solutions\<close>

text \<open>The paper's Proposition 4.1: both functions are assumed usc and
  bounded globally; a caller with data only on \<open>K\<close> extends first with
  \<open>usc_extension_bounded\<close>, which changes nothing on \<open>K\<close> and preserves
  both viscosity properties.\<close>

theorem uniqueness_expandable:
  fixes u w :: "real^'n::finite \<Rightarrow> real" and K :: "(real^'n) set"
  assumes kk: "1 \<le> k" "k < CARD('n)" and LL: "1 \<le> L"
    and cK: "compact K" and neK: "K \<noteq> {}" and expK: "expandable K"
    and uscu: "\<And>c z. u z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> u y < c"
    and uscw: "\<And>c z. w z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> w y < c"
    and Bu: "\<And>y. \<bar>u y\<bar> \<le> B" and Bw: "\<And>y. \<bar>w y\<bar> \<le> B"
    and subu: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < u x}) u"
    and supu: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env u x < 0}) (lsc_env u)"
    and subw: "visc_subsol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. 0 < w x}) w"
    and supw: "visc_supersol_env2 k L K
      (interior K \<union> {x \<in> K - interior K. lsc_env w x < 0}) (lsc_env w)"
    and x: "x \<in> K"
  shows "u x = w x"
proof -
  text \<open>One direction, stated once and applied twice with the roles swapped.\<close>
  have half: "a x \<le> bb x"
    if usca: "\<And>c z. a z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a y < c"
      and uscb: "\<And>c z. bb z < c \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> bb y < c"
      and Ba: "\<And>y. \<bar>a y\<bar> \<le> B" and Bb: "\<And>y. \<bar>bb y\<bar> \<le> B"
      and suba: "visc_subsol_env2 k L K
        (interior K \<union> {x \<in> K - interior K. 0 < a x}) a"
      and supb: "visc_supersol_env2 k L K
        (interior K \<union> {x \<in> K - interior K. lsc_env bb x < 0}) (lsc_env bb)"
    for a bb :: "real^'n \<Rightarrow> real"
  proof -
    have bl: "- B \<le> bb y" for y using Bb[of y] by (simp add: abs_le_iff)
    have bu: "bb y \<le> B" for y using Bb[of y] by (simp add: abs_le_iff)
    have lsclow: "- B \<le> lsc_env bb y" for y by (rule lsc_env_ge[OF bl])
    have lscself: "lsc_env bb y \<le> bb y" for y by (rule lsc_env_le_self[OF bl])
    have lscB: "\<bar>lsc_env bb y\<bar> \<le> B" for y
    proof -
      have "lsc_env bb y \<le> B" using lscself[of y] bu[of y] by linarith
      then show ?thesis using lsclow[of y] by (simp add: abs_le_iff)
    qed
    have lscl: "\<And>c z. c < lsc_env bb z \<Longrightarrow>
        \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < lsc_env bb y"
      by (rule lsc_env_lsc[OF bl])
    have "a x \<le> usc_env (lsc_env bb) x"
      by (rule comparison_expandable
          [OF kk LL cK neK expK usca lscl Ba lscB suba supb x])
    also have "\<dots> \<le> usc_env bb x"
      by (rule usc_env_mono[OF lscself bu])
    also have "\<dots> = bb x" by (rule usc_env_eq_self[OF bu uscb])
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule antisym)
    show "u x \<le> w x" by (rule half[OF uscu uscw Bu Bw subu supw])
    show "w x \<le> u x" by (rule half[OF uscw uscu Bw Bu subw supu])
  qed
qed

(*<*)
end
(*>*)
