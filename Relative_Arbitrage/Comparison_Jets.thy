section \<open>The jet interface to Definition 3.1\<close>

(*<*)
theory Comparison_Jets
  imports "Second_Order_Viscosity_Analysis.Soft_Penalty" Operator_Envelope_Continuity
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Second_Order_Viscosity_Analysis.Doubling_Of_Variables"
    "Semicontinuous_Analysis.Semicontinuity"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
begin

(*>*)

text \<open>\<open>Theorem_On_Sums\<close> and the theories below it develop the jet
  machinery independently of this development, directly over
  \<open>HOL-Analysis.Analysis\<close>.  This theory combines it with
  @{theory Relative_Arbitrage.Operator_Envelope_Continuity} to package the
  derivative facts into \<open>test_fun_at\<close>, and states Definition 3.1 with the
  paper's own \<open>C\<^sup>2\<close> test functions.\<close>

text \<open>\<open>Theorem_On_Sums\<close> and the theories below it develop the jet
  machinery independently of this development, directly over
  \<open>HOL-Analysis.Analysis\<close>.  This theory combines it with
  @{theory Relative_Arbitrage.Operator_Envelope_Continuity} to package the
  derivative facts into \<open>test_fun_at\<close>, and states Definition 3.1 with the
  paper's own \<open>C\<^sup>2\<close> test functions.\<close>

text \<open>@{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums} and the theories
  below it develop the jet machinery
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
  @{theory Second_Order_Viscosity_Analysis.Theorem_On_Sums}.\<close>

subsection \<open>The jet interface to Definition 3.1(b)\<close>

text \<open>\<open>quad_bdd_above_on_bounded\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

section \<open>Definition 3.1 with genuine \<open>C\<^sup>2\<close> test functions\<close>

text \<open>\<open>test_fun_C2\<close> lives in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>

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

text \<open>\<open>quadratic_grad_derivative_at\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>

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

text \<open>\<open>visc_subsol_env2\<close>, \<open>visc_supersol_env2\<close> live in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>

text \<open>Fewer test functions means a weaker condition, so everything proved in the
  \<^const>\<open>test_fun_at\<close> form still delivers Definition 3.1 as the paper states it.\<close>


(*<*)
end
(*>*)
