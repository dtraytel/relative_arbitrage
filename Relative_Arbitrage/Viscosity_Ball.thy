section \<open>Example 3.1 as a smooth viscosity solution\<close>

(*<*)
theory Viscosity_Ball
  imports Viscosity_Definitions
begin

(*>*)

text \<open>
  The explicit radial solution on the ball verifies both viscosity
  inequalities.  These sat in @{theory Relative_Arbitrage.Curvature_Operator}
  next to \<open>ball_v\<close> itself; they are the only thing there that reads the
  viscosity predicates, so they follow those predicates out.
\<close>

theorem ball_v_viscosity_subsol:
  fixes r :: real and k :: nat and L :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  shows "visc_subsol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume xO: "x \<in> ball 0 r"
    and tf: "test_fun_at \<phi> g H x"
    and lmax: "\<exists>e>0. \<forall>y \<in> ball x e. ball_v r k y - \<phi> y \<le> ball_v r k x - \<phi> x"
  define c where "c = real (CARD('n) - k)"
  have c_pos: "0 < c"
    using k by (simp add: c_def)
  from xO have xball: "x \<in> ball 0 r" .
  from tf have symH: "transpose H = H"
    and hessH: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    by (auto simp: test_fun_at_def)
  from tf obtain e1 where e1: "0 < e1"
    "\<And>y. y \<in> ball x e1 \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    by (auto simp: test_fun_at_def)
  from lmax obtain e2 where e2: "0 < e2"
    "\<And>y. y \<in> ball x e2 \<Longrightarrow> ball_v r k y - \<phi> y \<le> ball_v r k x - \<phi> x"
    by auto
  obtain e3 where e3: "0 < e3" "ball x e3 \<subseteq> ball 0 r"
    using openE[OF open_ball xball] by blast
  define e where "e = min e1 (min e2 e3)"
  have e_pos: "0 < e"
    using e1(1) e2(1) e3(1) by (simp add: e_def)
  have e_sub1: "ball x e \<subseteq> ball x e1"
    and e_sub2: "ball x e \<subseteq> ball x e2"
    and e_sub3: "ball x e \<subseteq> ball 0 r"
    using e3(2) by (auto simp: e_def)
  define q where "q = (\<lambda>y :: real^'n. (r\<^sup>2 - y \<bullet> y) / c)"
  define \<psi> where "\<psi> = (\<lambda>y. \<phi> y - q y)"
  define g\<psi> where "g\<psi> = (\<lambda>y. g y + (2 / c) *\<^sub>R y)"
  have \<psi>_deriv: "(\<psi> has_derivative (\<lambda>h. g\<psi> y \<bullet> h)) (at y)"
    if y: "y \<in> ball x e" for y
  proof -
    have "(\<psi> has_derivative
        (\<lambda>h. g y \<bullet> h - (- (2 / c) *\<^sub>R y) \<bullet> h)) (at y)"
      unfolding \<psi>_def q_def
      by (intro derivative_intros e1(2) e_sub1[THEN subsetD] y
          quadratic_gradient c_pos)
    moreover have "(\<lambda>h. g y \<bullet> h - (- (2 / c) *\<^sub>R y) \<bullet> h)
        = (\<lambda>h. g\<psi> y \<bullet> h)"
      by (simp add: fun_eq_iff g\<psi>_def inner_add_left)
    ultimately show ?thesis
      by simp
  qed
  have \<psi>_hess: "(g\<psi> has_derivative
      (\<lambda>h. (H + (2 / c) *\<^sub>R mat 1) *v h)) (at x)"
  proof -
    have "(g\<psi> has_derivative (\<lambda>h. H *v h + (2 / c) *\<^sub>R h)) (at x)"
      unfolding g\<psi>_def
      by (intro derivative_intros hessH)
    moreover have "(\<lambda>h :: real^'n. H *v h + (2 / c) *\<^sub>R h)
        = (\<lambda>h. (H + (2 / c) *\<^sub>R mat 1) *v h)"
      by (simp add: fun_eq_iff matrix_vector_mult_add_rdistrib
          scaleR_matrix_vector)
    ultimately show ?thesis
      by simp
  qed
  have \<psi>_min: "\<psi> x \<le> \<psi> y" if y: "y \<in> ball x e" for y
  proof -
    have "ball_v r k y - \<phi> y \<le> ball_v r k x - \<phi> x"
      using e2(2) e_sub2 y by auto
    moreover have "ball_v r k y = q y"
      using ball_v_eq_quadratic e_sub3 y by (fastforce simp: q_def c_def)
    moreover have "ball_v r k x = q x"
      using ball_v_eq_quadratic[OF xball] by (simp add: q_def c_def)
    ultimately show ?thesis
      by (simp add: \<psi>_def)
  qed
  have x_mem: "x \<in> ball x e"
    using e_pos by simp
  have ev_min: "eventually (\<lambda>y. \<psi> x \<le> \<psi> y) (at x)"
    using \<psi>_min e_pos
    by (auto simp: eventually_at dist_commute intro!: exI[of _ e])
  have g\<psi>x0: "g\<psi> x = 0"
    by (rule local_min_gradient_zero[OF \<psi>_deriv[OF x_mem] ev_min])
  then have gx: "g x = - ((2 / c) *\<^sub>R x)"
    unfolding g\<psi>_def add_eq_0_iff2 .
  have quadform: "0 \<le> h \<bullet> ((H + (2 / c) *\<^sub>R mat 1) *v h)" for h
    by (rule local_min_hessian_psd[OF e_pos \<psi>_deriv \<psi>_hess \<psi>_min])
  have symH': "H $ i $ j = H $ j $ i" for i j
    using symH by (metis transpose_def vec_lambda_beta)
  have symQ: "transpose (H + (2 / c) *\<^sub>R mat 1) = H + (2 / c) *\<^sub>R mat 1"
    by (simp add: transpose_def vec_eq_iff mat_def symH')
  have Qpsd: "psd (H + (2 / c) *\<^sub>R mat 1)"
    using symQ quadform by (simp add: psd_def)
  have "psd (H - (- (2 / real (CARD('n) - k)) *\<^sub>R mat 1))"
    using Qpsd by (simp add: c_def)
  from ell_op_le_one_of_psd_diff[OF k L this]
  show "ell_op k L (g x) H \<le> 1" .
qed

theorem ball_v_viscosity_supersol:
  fixes r :: real and k :: nat and L :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  shows "visc_supersol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
  unfolding visc_supersol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
  assume xO: "x \<in> ball 0 r"
    and tf: "test_fun_at \<phi> g H x"
    and lmin: "\<exists>e>0. \<forall>y \<in> ball x e. ball_v r k x - \<phi> x \<le> ball_v r k y - \<phi> y"
  define c where "c = real (CARD('n) - k)"
  have c_pos: "0 < c"
    using k by (simp add: c_def)
  from xO have xball: "x \<in> ball 0 r" .
  from tf have symH: "transpose H = H"
    and hessH: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    by (auto simp: test_fun_at_def)
  from tf obtain e1 where e1: "0 < e1"
    "\<And>y. y \<in> ball x e1 \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    by (auto simp: test_fun_at_def)
  from lmin obtain e2 where e2: "0 < e2"
    "\<And>y. y \<in> ball x e2 \<Longrightarrow> ball_v r k x - \<phi> x \<le> ball_v r k y - \<phi> y"
    by auto
  obtain e3 where e3: "0 < e3" "ball x e3 \<subseteq> ball 0 r"
    using openE[OF open_ball xball] by blast
  define e where "e = min e1 (min e2 e3)"
  have e_pos: "0 < e"
    using e1(1) e2(1) e3(1) by (simp add: e_def)
  have e_sub1: "ball x e \<subseteq> ball x e1"
    and e_sub2: "ball x e \<subseteq> ball x e2"
    and e_sub3: "ball x e \<subseteq> ball 0 r"
    using e3(2) by (auto simp: e_def)
  define q where "q = (\<lambda>y :: real^'n. (r\<^sup>2 - y \<bullet> y) / c)"
  define \<psi> where "\<psi> = (\<lambda>y. q y - \<phi> y)"
  define g\<psi> where "g\<psi> = (\<lambda>y. - (2 / c) *\<^sub>R y - g y)"
  have \<psi>_deriv: "(\<psi> has_derivative (\<lambda>h. g\<psi> y \<bullet> h)) (at y)"
    if y: "y \<in> ball x e" for y
  proof -
    have "(\<psi> has_derivative
        (\<lambda>h. (- (2 / c) *\<^sub>R y) \<bullet> h - g y \<bullet> h)) (at y)"
      unfolding \<psi>_def q_def
      by (intro derivative_intros e1(2) e_sub1[THEN subsetD] y
          quadratic_gradient c_pos)
    moreover have "(\<lambda>h. (- (2 / c) *\<^sub>R y) \<bullet> h - g y \<bullet> h)
        = (\<lambda>h. g\<psi> y \<bullet> h)"
      by (simp add: fun_eq_iff g\<psi>_def inner_diff_left)
    ultimately show ?thesis
      by simp
  qed
  have \<psi>_hess: "(g\<psi> has_derivative
      (\<lambda>h. ((- (2 / c) *\<^sub>R mat 1) - H) *v h)) (at x)"
  proof -
    have "(g\<psi> has_derivative (\<lambda>h. - (2 / c) *\<^sub>R h - H *v h)) (at x)"
      unfolding g\<psi>_def
      by (intro derivative_intros hessH)
    moreover have "(\<lambda>h :: real^'n. - (2 / c) *\<^sub>R h - H *v h)
        = (\<lambda>h. ((- (2 / c) *\<^sub>R mat 1) - H) *v h)"
      by (simp add: fun_eq_iff matrix_vector_mult_diff_rdistrib
          neg_matrix_vector scaleR_matrix_vector)
    ultimately show ?thesis
      by simp
  qed
  have \<psi>_min: "\<psi> x \<le> \<psi> y" if y: "y \<in> ball x e" for y
  proof -
    have "ball_v r k x - \<phi> x \<le> ball_v r k y - \<phi> y"
      using e2(2) e_sub2 y by auto
    moreover have "ball_v r k y = q y"
      using ball_v_eq_quadratic e_sub3 y by (fastforce simp: q_def c_def)
    moreover have "ball_v r k x = q x"
      using ball_v_eq_quadratic[OF xball] by (simp add: q_def c_def)
    ultimately show ?thesis
      by (simp add: \<psi>_def)
  qed
  have x_mem: "x \<in> ball x e"
    using e_pos by simp
  have ev_min: "eventually (\<lambda>y. \<psi> x \<le> \<psi> y) (at x)"
    using \<psi>_min e_pos
    by (auto simp: eventually_at dist_commute intro!: exI[of _ e])
  have g\<psi>x0: "g\<psi> x = 0"
    by (rule local_min_gradient_zero[OF \<psi>_deriv[OF x_mem] ev_min])
  then have gx: "g x = - ((2 / c) *\<^sub>R x)"
    unfolding g\<psi>_def by (simp add: algebra_simps)
  have quadform: "0 \<le> h \<bullet> (((- (2 / c) *\<^sub>R mat 1) - H) *v h)" for h
    by (rule local_min_hessian_psd[OF e_pos \<psi>_deriv \<psi>_hess \<psi>_min])
  have symH': "H $ i $ j = H $ j $ i" for i j
    using symH by (metis axis1_inner inner_matrix_sym matrix_vector_axis_one)
  have symQ: "transpose ((- (2 / c) *\<^sub>R mat 1) - H)
      = (- (2 / c) *\<^sub>R mat 1) - H"
    by (simp add: transpose_def vec_eq_iff mat_def symH')
  have Qpsd: "psd ((- (2 / c) *\<^sub>R mat 1) - H)"
    using symQ quadform by (simp add: psd_def)
  have "psd ((- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) - H)"
    using Qpsd by (simp add: c_def)
  from ell_op_ge_one_of_psd_diff[OF k L this]
  show "1 \<le> ell_op k L (g x) H" .
qed

text \<open>
  The PDE part of Theorem 1.1 for Example 3.1: on the punctured open ball,
  the explicit function \<open>v\<close> of Eq. (3.9) is a viscosity solution of
  \<open>F(Dv, D\<^sup>2v) = 1\<close>, and it vanishes on the boundary \<open>|x| = r\<close>.
\<close>

theorem ball_v_solves_pde_viscosity:
  fixes r :: real and k :: nat and L :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  shows "visc_sol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
    and "\<And>x :: real^'n. norm x = r \<Longrightarrow> ball_v r k x = 0"
proof -
  show "visc_sol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
    using ball_v_viscosity_subsol[OF assms] ball_v_viscosity_supersol[OF assms]
    by (simp add: visc_sol_def)
  show "\<And>x :: real^'n. norm x = r \<Longrightarrow> ball_v r k x = 0"
    by (rule ball_v_boundary)
qed


(*<*)
end
(*>*)
