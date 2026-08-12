(*
  Title:   Relative_Arbitrage_Comparison.thy
  Content: Uniqueness of the ball solution of Eq. (3.9) WITHOUT the
           Crandall--Ishii comparison principle.

  Relative_Arbitrage_Uniqueness derives uniqueness from the locale
  comparison_principle, i.e. from the comparison principle for two
  arbitrary viscosity solutions -- that is the Crandall--Ishii theorem,
  which needs sup-convolutions and Jensen's lemma.

  For the paper's statement (Theorem 1.1, uniqueness, for Example 3.1)
  none of that is required: one of the two functions being compared is
  the EXPLICIT SMOOTH solution v of Eq. (3.9), so it can serve directly
  as a test function.  Since the operator F is positively homogeneous in
  the Hessian and invariant under scaling of the gradient, the scaled
  function (1+e)v is a STRICT supersolution and (1-e)v a STRICT
  subsolution, which turns the touching argument into a contradiction
  without any doubling of variables.

  Result: ball_v_unique_solution_smooth -- the explicit v is the unique
  continuous viscosity solution with its boundary data, proved from
  first principles.
*)

theory Relative_Arbitrage_Comparison
  imports Relative_Arbitrage_Uniqueness
begin

section \<open>Continuity of the ball value function\<close>

lemma continuous_on_ball_v:
  "continuous_on S (ball_v r k :: real^'n::finite \<Rightarrow> real)"
proof (cases "real (CARD('n) - k) = 0")
  case True
  then have "(ball_v r k :: real^'n \<Rightarrow> real) = (\<lambda>_. 0)"
    by (simp add: ball_v_def fun_eq_iff)
  then show ?thesis by simp
next
  case False
  show ?thesis
    unfolding ball_v_def using False by (intro continuous_intros) auto
qed

section \<open>The scaled ball function as a test function\<close>

text \<open>Gradient and Hessian of \<open>c * v\<close> inside the ball.  The scalar
  \<open>b = c * (-2/(n-k))\<close> is carried as a variable so that no normalisation
  can split it apart.\<close>

lemma ball_v_scaled_test_fun:
  fixes x :: "real^'n::finite"
  assumes x: "norm x < r" and k: "k < CARD('n)" and c: "0 < c"
    and b: "b = c * (- (2 / real (CARD('n) - k)))"
  shows "test_fun_at (\<lambda>y. c * ball_v r k y) (\<lambda>y. b *\<^sub>R y)
     (b *\<^sub>R mat 1) x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose (b *\<^sub>R (mat 1 :: real^'n^'n)) = b *\<^sub>R mat 1"
    by (simp add: transpose_scaleR)
next
  have e_pos: "0 < r - norm x"
    using x by simp
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>y. c * ball_v r k y) has_derivative (\<lambda>h. (b *\<^sub>R y) \<bullet> h)) (at y)"
  proof (intro exI[of _ "r - norm x"] conjI e_pos ballI)
    fix y :: "real^'n" assume y: "y \<in> ball x (r - norm x)"
    have "norm y \<le> norm (y - x) + norm x"
      using norm_triangle_sub[of y x] by simp
    also have "\<dots> < (r - norm x) + norm x"
      using y by (simp add: dist_norm norm_minus_commute)
    finally have ny: "norm y < r" by simp
    have base: "((ball_v r k) has_derivative
        (\<lambda>h. (- (2 / real (CARD('n) - k)) *\<^sub>R y) \<bullet> h)) (at y)"
      by (rule ball_v_gradient[OF ny k])
    have "((\<lambda>y. c *\<^sub>R ball_v r k y) has_derivative
        (\<lambda>h. c *\<^sub>R ((- (2 / real (CARD('n) - k)) *\<^sub>R y) \<bullet> h))) (at y)"
      using base by (rule has_derivative_scaleR_right)
    then show "((\<lambda>y. c * ball_v r k y) has_derivative
        (\<lambda>h. (b *\<^sub>R y) \<bullet> h)) (at y)"
      by (simp add: b mult.assoc)
  qed
next
  have lin: "((\<lambda>y :: real^'n. b *\<^sub>R y) has_derivative
      (\<lambda>h. b *\<^sub>R h)) (at x)"
    by (intro derivative_eq_intros) auto
  have mv: "(b *\<^sub>R (mat 1 :: real^'n^'n)) *v h = b *\<^sub>R h" for h
    by (simp add: scaleR_matrix_vector_assoc[symmetric])
  show "((\<lambda>y :: real^'n. b *\<^sub>R y) has_derivative
      (\<lambda>h. (b *\<^sub>R mat 1) *v h)) (at x)"
    using lin by (simp add: mv)
qed

text \<open>Positive homogeneity of \<open>F\<close>: scaling the gradient does not change
  the feasible set, and scaling the Hessian scales the infimum, so the
  scaled ball function solves \<open>F = c\<close> instead of \<open>F = 1\<close>.\<close>

lemma ell_op_ball_scaled:
  fixes x :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and c: "0 < c"
    and b: "b = c * (- (2 / real (CARD('n) - k)))"
  shows "ell_op k L (b *\<^sub>R x) (b *\<^sub>R mat 1) = c"
proof -
  define d where "d = - (2 / real (CARD('n) - k))"
  have b_eq: "b = c * d"
    using b by (simp add: d_def)
  have ne: "feasible k L (d *\<^sub>R x) \<noteq> ({} :: (real^'n^'n) set)"
    by (intro feasible_nonempty k L)
  have "ell_op k L (b *\<^sub>R x) (b *\<^sub>R (mat 1 :: real^'n^'n))
      = ell_op k L (c *\<^sub>R (d *\<^sub>R x)) (c *\<^sub>R (d *\<^sub>R mat 1))"
    unfolding b_eq by simp
  also have "\<dots> = ell_op k L (d *\<^sub>R x) (c *\<^sub>R (d *\<^sub>R mat 1))"
    using c by (intro ell_op_scale_p) simp
  also have "\<dots> = c * ell_op k L (d *\<^sub>R x) (d *\<^sub>R mat 1)"
    by (intro ell_op_dilation c ne)
  also have "ell_op k L (d *\<^sub>R x) (d *\<^sub>R (mat 1 :: real^'n^'n)) = 1"
    unfolding d_def by (intro ell_op_eval k L)
  finally show ?thesis by simp
qed

section \<open>The punctured ball is dense in the closed ball\<close>

text \<open>Needed to identify the parabolic boundary \<open>closure \<Omega> - \<Omega>\<close> of
  \<open>\<Omega> = ball 0 r - {0}\<close> with the sphere together with the origin.\<close>

lemma closure_ball_minus_zero:
  fixes r :: real
  assumes r: "0 < r"
  shows "closure (ball (0::real^'n::finite) r - {0}) = cball 0 r"
proof
  show "closure (ball (0::real^'n) r - {0}) \<subseteq> cball 0 r"
    using closure_mono[of "ball (0::real^'n) r - {0}" "ball 0 r"] r by simp
next
  have sub: "ball (0::real^'n) r \<subseteq> closure (ball 0 r - {0})"
  proof
    fix y :: "real^'n" assume y: "y \<in> ball 0 r"
    show "y \<in> closure (ball 0 r - {0})"
    proof (cases "y = 0")
      case False
      with y show ?thesis
        using closure_subset[of "ball (0::real^'n) r - {0}"] by auto
    next
      case True
      have "\<forall>e>0. \<exists>z \<in> ball (0::real^'n) r - {0}. dist z y < e"
      proof (intro allI impI)
        fix e :: real assume e: "0 < e"
        define t where "t = min e r / 2"
        have t_pos: "0 < t" and t_lt: "t < r" and t_lt_e: "t < e"
          using e r by (auto simp: t_def)
        define z where "z = t *\<^sub>R axis (undefined :: 'n) (1::real)"
        have nz: "norm (z :: real^'n) = t"
          using t_pos by (simp add: z_def)
        have z_ne: "z \<noteq> (0 :: real^'n)"
          using nz t_pos by auto
        have "z \<in> ball (0::real^'n) r - {0}"
          using nz t_lt z_ne by (simp add: dist_norm)
        moreover have "dist z y < e"
          using nz t_lt_e by (simp add: True dist_norm)
        ultimately show "\<exists>z \<in> ball (0::real^'n) r - {0}. dist z y < e"
          by blast
      qed
      then show ?thesis
        by (simp add: closure_approachable)
    qed
  qed
  have "cball (0::real^'n) r = closure (ball 0 r)"
    using r by simp
  also have "closure (ball (0::real^'n) r) \<subseteq> closure (ball 0 r - {0})"
    by (rule closure_minimal[OF sub closed_closure])
  finally show "cball (0::real^'n) r \<subseteq> closure (ball 0 r - {0})" .
qed

section \<open>Comparison with the explicit smooth solution\<close>

lemma ball_v_pos:
  fixes x :: "real^'n::finite"
  assumes x: "norm x < r" and k: "k < CARD('n)"
  shows "0 < ball_v r k x"
proof -
  have "(norm x)\<^sup>2 < r\<^sup>2"
    using x by (intro power_strict_mono) simp_all
  then have "x \<bullet> x < r\<^sup>2"
    by (simp add: dot_square_norm)
  moreover have "0 < real (CARD('n) - k)"
    using k by simp
  ultimately show ?thesis
    by (simp add: ball_v_def)
qed

lemma norm_less_of_ball:
  fixes z :: "real^'n::finite"
  assumes z: "norm z < r" and y: "y \<in> ball z (r - norm z)"
  shows "norm y < r"
proof -
  have "norm y \<le> norm (y - z) + norm z"
    using norm_triangle_sub[of y z] by simp
  also have "\<dots> < (r - norm z) + norm z"
    using y by (simp add: dist_norm norm_minus_commute)
  finally show ?thesis by simp
qed

text \<open>Every viscosity subsolution which is dominated by \<open>v\<close> on the
  boundary is dominated by \<open>v\<close> everywhere.  The proof compares \<open>u\<close> with
  the STRICT supersolution \<open>c * v\<close>, \<open>c > 1\<close>: at an interior maximum of
  \<open>u - c * v\<close> the smooth function \<open>c * v\<close> is an admissible test function,
  so the subsolution property forces \<open>c = ell_op \<dots> \<le> 1\<close>.  No doubling of
  variables and hence no Crandall--Ishii lemma is needed.\<close>

theorem visc_subsol_le_ball_v:
  fixes r :: real and u :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cont: "continuous_on (cball 0 r) u"
    and sub: "visc_subsol k L (ball (0::real^'n) r) u"
    and bd: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
              \<Longrightarrow> u y \<le> ball_v r k y"
    and x: "x \<in> ball (0::real^'n) r"
  shows "u x \<le> ball_v r k x"
proof (rule field_le_epsilon)
  fix d :: real assume d: "0 < d"
  have xr: "norm x < r"
    using x by simp
  have vx: "0 < ball_v r k x"
    by (rule ball_v_pos[OF xr k(2)])
  define c where "c = 1 + d / ball_v r k x"
  have c1: "1 < c"
    using d vx by (simp add: c_def)
  then have cpos: "0 < c" by simp
  define \<psi> where "\<psi> = (\<lambda>y :: real^'n. u y - c * ball_v r k y)"
  have cont\<psi>: "continuous_on (cball (0::real^'n) r) \<psi>"
    unfolding \<psi>_def
    by (intro continuous_intros cont continuous_on_ball_v)
  have "cball (0::real^'n) r \<noteq> {}"
    using r by auto
  from continuous_attains_sup[OF compact_cball this cont\<psi>]
  obtain z :: "real^'n" where z: "z \<in> cball 0 r"
    and zmax: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> \<psi> y \<le> \<psi> z"
    by blast
  have zle: "\<psi> z \<le> 0"
  proof (cases "z \<in> ball (0::real^'n) r")
    case True
    then have zr: "norm z < r" by auto
    define b where "b = c * (- (2 / real (CARD('n) - k)))"
    have tf: "test_fun_at (\<lambda>y. c * ball_v r k y) (\<lambda>y. b *\<^sub>R y)
        (b *\<^sub>R mat 1) z"
      by (rule ball_v_scaled_test_fun[OF zr k(2) cpos b_def])
    have loc: "\<exists>e>0. \<forall>y \<in> ball z e.
        u y - c * ball_v r k y \<le> u z - c * ball_v r k z"
    proof (intro exI[of _ "r - norm z"] conjI ballI)
      show "0 < r - norm z" using zr by simp
    next
      fix y :: "real^'n" assume y: "y \<in> ball z (r - norm z)"
      have "norm y < r"
        by (rule norm_less_of_ball[OF zr y])
      then have "y \<in> cball (0::real^'n) r" by simp
      from zmax[OF this] show
        "u y - c * ball_v r k y \<le> u z - c * ball_v r k z"
        by (simp add: \<psi>_def)
    qed
    have "ell_op k L ((\<lambda>y. b *\<^sub>R y) z) (b *\<^sub>R mat 1) \<le> 1"
      using sub True tf loc unfolding visc_subsol_def by blast
    then have "ell_op k L (b *\<^sub>R z) (b *\<^sub>R (mat 1 :: real^'n^'n)) \<le> 1"
      by simp
    also have "ell_op k L (b *\<^sub>R z) (b *\<^sub>R (mat 1 :: real^'n^'n)) = c"
      by (rule ell_op_ball_scaled[OF k L cpos b_def])
    finally have "c \<le> 1" .
    with c1 show ?thesis by linarith
  next
    case False
    have "u z \<le> ball_v r k z"
      by (rule bd[OF z False])
    moreover have "ball_v r k z \<le> c * ball_v r k z"
      using mult_right_mono[of 1 c "ball_v r k z"] c1 ball_v_nonneg[of r k z]
      by simp
    ultimately show ?thesis
      by (simp add: \<psi>_def)
  qed
  have "u x - c * ball_v r k x = \<psi> x"
    by (simp add: \<psi>_def)
  also have "\<psi> x \<le> \<psi> z"
    using x by (intro zmax) auto
  also note zle
  finally have "u x \<le> c * ball_v r k x" by simp
  also have "c * ball_v r k x = ball_v r k x + d"
    using vx by (simp add: c_def field_simps)
  finally show "u x \<le> ball_v r k x + d" .
qed

text \<open>Dually, \<open>v\<close> is dominated by every viscosity supersolution, comparing
  with the STRICT subsolution \<open>c * v\<close>, \<open>0 < c < 1\<close>.\<close>

theorem ball_v_le_visc_supersol:
  fixes r :: real and u :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cont: "continuous_on (cball 0 r) u"
    and sup: "visc_supersol k L (ball (0::real^'n) r) u"
    and bd: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
              \<Longrightarrow> ball_v r k y \<le> u y"
    and x: "x \<in> ball (0::real^'n) r"
  shows "ball_v r k x \<le> u x"
proof (rule field_le_epsilon)
  fix d :: real assume d: "0 < d"
  have xr: "norm x < r"
    using x by simp
  have vx: "0 < ball_v r k x"
    by (rule ball_v_pos[OF xr k(2)])
  define e where "e = min d (ball_v r k x / 2)"
  have e_pos: "0 < e" and e_le: "e \<le> d" and e_lt: "e < ball_v r k x"
    using d vx by (auto simp: e_def)
  define c where "c = 1 - e / ball_v r k x"
  have c1: "c < 1"
    using e_pos vx by (simp add: c_def)
  have cpos: "0 < c"
    using e_lt vx by (simp add: c_def)
  define \<psi> where "\<psi> = (\<lambda>y :: real^'n. u y - c * ball_v r k y)"
  have cont\<psi>: "continuous_on (cball (0::real^'n) r) \<psi>"
    unfolding \<psi>_def
    by (intro continuous_intros cont continuous_on_ball_v)
  have "cball (0::real^'n) r \<noteq> {}"
    using r by auto
  from continuous_attains_inf[OF compact_cball this cont\<psi>]
  obtain z :: "real^'n" where z: "z \<in> cball 0 r"
    and zmin: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> \<psi> z \<le> \<psi> y"
    by blast
  have zge: "0 \<le> \<psi> z"
  proof (cases "z \<in> ball (0::real^'n) r")
    case True
    then have zr: "norm z < r" by auto
    define b where "b = c * (- (2 / real (CARD('n) - k)))"
    have tf: "test_fun_at (\<lambda>y. c * ball_v r k y) (\<lambda>y. b *\<^sub>R y)
        (b *\<^sub>R mat 1) z"
      by (rule ball_v_scaled_test_fun[OF zr k(2) cpos b_def])
    have loc: "\<exists>e>0. \<forall>y \<in> ball z e.
        u z - c * ball_v r k z \<le> u y - c * ball_v r k y"
    proof (intro exI[of _ "r - norm z"] conjI ballI)
      show "0 < r - norm z" using zr by simp
    next
      fix y :: "real^'n" assume y: "y \<in> ball z (r - norm z)"
      have "norm y < r"
        by (rule norm_less_of_ball[OF zr y])
      then have "y \<in> cball (0::real^'n) r" by simp
      from zmin[OF this] show
        "u z - c * ball_v r k z \<le> u y - c * ball_v r k y"
        by (simp add: \<psi>_def)
    qed
    have "1 \<le> ell_op k L ((\<lambda>y. b *\<^sub>R y) z) (b *\<^sub>R mat 1)"
      using sup True tf loc unfolding visc_supersol_def by blast
    then have "1 \<le> ell_op k L (b *\<^sub>R z) (b *\<^sub>R (mat 1 :: real^'n^'n))"
      by simp
    also have "ell_op k L (b *\<^sub>R z) (b *\<^sub>R (mat 1 :: real^'n^'n)) = c"
      by (rule ell_op_ball_scaled[OF k L cpos b_def])
    finally have "1 \<le> c" .
    with c1 show ?thesis by linarith
  next
    case False
    have "ball_v r k z \<le> u z"
      by (rule bd[OF z False])
    moreover have "c * ball_v r k z \<le> ball_v r k z"
      using c1 ball_v_nonneg[of r k z] by (simp add: mult_le_cancel_right2)
    ultimately show ?thesis
      by (simp add: \<psi>_def)
  qed
  have "c * ball_v r k x = ball_v r k x - e"
    using vx by (simp add: c_def field_simps)
  moreover have "\<psi> z \<le> \<psi> x"
    using x by (intro zmin) auto
  ultimately have "ball_v r k x - e \<le> u x"
    using zge by (simp add: \<psi>_def)
  then show "ball_v r k x \<le> u x + d"
    using e_le by simp
qed

section \<open>Uniqueness without the Crandall--Ishii comparison principle\<close>

text \<open>Theorem 1.1 (uniqueness) for Example 3.1, with no axiomatic input:
  the explicit function of Eq. (3.9) is the unique continuous viscosity
  solution of \<open>F(\<nabla>u, \<nabla>\<^sup>2 u) = 1\<close> on the whole open ball --- the interior
  \<open>K\<^sup>\<circ>\<close> of Definition 3.1 --- with its own boundary data on the sphere.\<close>

theorem ball_v_unique_solution_smooth:
  fixes r :: real and u :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cont: "continuous_on (cball 0 r) u"
    and u: "visc_sol k L (ball (0::real^'n) r) u"
    and bd: "\<And>y :: real^'n. y \<in> closure (ball 0 r) - ball 0 r
              \<Longrightarrow> u y = ball_v r k y"
  shows "\<And>x :: real^'n. x \<in> ball 0 r \<Longrightarrow> u x = ball_v r k x"
proof -
  fix x :: "real^'n" assume x: "x \<in> ball 0 r"
  have bd': "u y = ball_v r k y"
    if that: "y \<in> cball (0::real^'n) r" "y \<notin> ball 0 r" for y :: "real^'n"
  proof -
    have "y \<in> closure (ball (0::real^'n) r)"
      unfolding closure_ball[OF r] by (rule that(1))
    with that(2) show ?thesis
      by (intro bd) simp
  qed
  have le: "u x \<le> ball_v r k x"
    using u by (intro visc_subsol_le_ball_v[OF k L r cont _ _ x])
      (auto simp: visc_sol_def bd')
  have ge: "ball_v r k x \<le> u x"
    using u by (intro ball_v_le_visc_supersol[OF k L r cont _ _ x])
      (auto simp: visc_sol_def bd')
  from le ge show "u x = ball_v r k x" by simp
qed

text \<open>On the whole closed ball -- interior points by the theorem above,
  boundary points by hypothesis.\<close>

corollary ball_v_unique_on_cball:
  fixes r :: real and u :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cont: "continuous_on (cball 0 r) u"
    and u: "visc_sol k L (ball (0::real^'n) r) u"
    and bd: "\<And>y :: real^'n. y \<in> closure (ball 0 r) - ball 0 r
              \<Longrightarrow> u y = ball_v r k y"
    and x: "x \<in> cball (0::real^'n) r"
  shows "u x = ball_v r k x"
proof (cases "x \<in> ball (0::real^'n) r")
  case True
  show ?thesis
    by (rule ball_v_unique_solution_smooth[OF k L r cont u bd True])
next
  case False
  have "x \<in> closure (ball (0::real^'n) r)"
    unfolding closure_ball[OF r] by (rule x)
  with False show ?thesis
    by (intro bd) simp
qed

text \<open>The hypotheses are satisfiable: the explicit function itself is a
  continuous viscosity solution with those boundary values.  Hence the pair
  of results is an existence-and-uniqueness statement, with no axioms.\<close>

corollary ball_v_visc_sol_exists:
  fixes r :: real
  assumes k: "1 \<le> k" "k < CARD('n::finite)" and L: "1 \<le> L"
  shows "continuous_on (cball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
    and "visc_sol k L (ball 0 r) (ball_v r k :: real^'n \<Rightarrow> real)"
  by (rule continuous_on_ball_v, rule ball_v_solves_pde_viscosity(1)[OF k L])

section \<open>Section 4 for the ball, with no Crandall--Ishii input\<close>

text \<open>Theorem 4.3 of the paper (comparison) and Proposition 4.1 (uniqueness) are
  proved there for a general compact \<open>K\<close>, via Theorem 4.2(a), whose proof doubles
  the variables and invokes the Crandall--Ishii theorem on sums -- cited in the
  paper as [CI90] and NOT available in this development (see
  \<open>max_principle_boundary\<close> in Lemma_3_1_Envelopes.thy for where that gap is
  isolated).

  For \<open>K\<close> a closed ball, however, the whole of Section 4's conclusion is
  available UNCONDITIONALLY, because the explicit solution \<open>ball_v\<close> of Eq. (3.9)
  can be interposed: a subsolution lies below it and a supersolution above it,
  each by comparison with a strictly scaled copy of \<open>ball_v\<close> used as a test
  function.  No doubling of variables occurs anywhere.

  This is exactly the case Theorem 1.1 needs for Example 3.1.\<close>

theorem comparison_ball:
  fixes r :: real and u w :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cu: "continuous_on (cball 0 r) u"
    and cw: "continuous_on (cball 0 r) w"
    and sub: "visc_subsol k L (ball (0::real^'n) r) u"
    and sup: "visc_supersol k L (ball (0::real^'n) r) w"
    and bdu: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
                \<Longrightarrow> u y \<le> ball_v r k y"
    and bdw: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
                \<Longrightarrow> ball_v r k y \<le> w y"
    and x: "x \<in> ball (0::real^'n) r"
  shows "u x \<le> w x"
proof -
  have "u x \<le> ball_v r k x"
    by (rule visc_subsol_le_ball_v[OF k L r cu sub bdu x])
  also have "\<dots> \<le> w x"
    by (rule ball_v_le_visc_supersol[OF k L r cw sup bdw x])
  finally show ?thesis .
qed

text \<open>Boundary data given as an ORDERED pair on the sphere, which is the form
  Theorem 4.3 is stated in: \<open>u \<le> w\<close> on the sphere suffices, provided the common
  value is that of \<open>ball_v\<close>.  Stated separately because it is the shape the
  assembly of Theorem 1.1 will want.\<close>

corollary comparison_ball_zero_boundary:
  fixes r :: real and u w :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cu: "continuous_on (cball 0 r) u"
    and cw: "continuous_on (cball 0 r) w"
    and sub: "visc_subsol k L (ball (0::real^'n) r) u"
    and sup: "visc_supersol k L (ball (0::real^'n) r) w"
    and bd: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
               \<Longrightarrow> u y \<le> ball_v r k y \<and> ball_v r k y \<le> w y"
    and x: "x \<in> ball (0::real^'n) r"
  shows "u x \<le> w x"
proof -
  have bdu: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
      \<Longrightarrow> u y \<le> ball_v r k y"
    using bd by blast
  have bdw: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
      \<Longrightarrow> ball_v r k y \<le> w y"
    using bd by blast
  show ?thesis
    by (rule comparison_ball[OF k L r cu cw sub sup bdu bdw x])
qed

text \<open>Proposition 4.1 for the ball: two viscosity solutions agreeing with
  \<open>ball_v\<close> on the sphere agree everywhere.  Both directions of
  \<open>comparison_ball\<close>.\<close>

corollary uniqueness_ball:
  fixes r :: real and u w :: "real^'n::finite \<Rightarrow> real"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and r: "0 < r"
    and cu: "continuous_on (cball 0 r) u"
    and cw: "continuous_on (cball 0 r) w"
    and u: "visc_sol k L (ball (0::real^'n) r) u"
    and w: "visc_sol k L (ball (0::real^'n) r) w"
    and bdu: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
                \<Longrightarrow> u y = ball_v r k y"
    and bdw: "\<And>y :: real^'n. y \<in> cball 0 r \<Longrightarrow> y \<notin> ball 0 r
                \<Longrightarrow> w y = ball_v r k y"
    and x: "x \<in> ball (0::real^'n) r"
  shows "u x = w x"
proof -
  have su: "visc_subsol k L (ball (0::real^'n) r) u"
    and pu: "visc_supersol k L (ball (0::real^'n) r) u"
    using u by (auto simp: visc_sol_def)
  have sw: "visc_subsol k L (ball (0::real^'n) r) w"
    and pw: "visc_supersol k L (ball (0::real^'n) r) w"
    using w by (auto simp: visc_sol_def)
  have le1: "u x \<le> w x"
    by (rule comparison_ball[OF k L r cu cw su pw _ _ x]) (simp_all add: bdu bdw)
  have le2: "w x \<le> u x"
    by (rule comparison_ball[OF k L r cw cu sw pu _ _ x]) (simp_all add: bdu bdw)
  from le1 le2 show ?thesis
    by simp
qed

section \<open>Theorem 4.2(a) when one function is smooth: no Crandall--Ishii\<close>

text \<open>The mechanism of the ball argument, abstracted.  Theorem 4.2(a) of the
  paper needs the Crandall--Ishii theorem on sums because BOTH \<open>u\<close> and \<open>w\<close> are
  merely semicontinuous, so neither can serve as a test function for the other.
  If, however, one of them is a SMOOTH STRICT supersolution, the maximum
  principle is elementary: at an interior maximum of \<open>u - \<psi>\<close> the smooth \<open>\<psi>\<close> IS an
  admissible test function, so the subsolution property forces
  \<open>F(\<nabla>\<psi>, \<nabla>\<^sup>2\<psi>) \<le> 1\<close> there, contradicting strictness.  Hence the maximum sits on
  the boundary.

  This is the general form of what \<open>visc_subsol_le_ball_v\<close> does with
  \<open>\<psi> = c \<cdot> ball_v\<close>, \<open>c > 1\<close>.  It applies on ANY compact \<open>K\<close> for which a smooth
  strict supersolution is available, and needs nothing from Section 4's harder
  half.  The gradient field is \<open>g\<close> and the Hessian field \<open>Hf\<close>, matching the shape
  of \<open>test_fun_at\<close>.\<close>

theorem visc_subsol_le_smooth_strict:
  fixes u \<psi> :: "real^'n::finite \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and Hf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes cpt: "compact K" and Kne: "K \<noteq> {}"
    and cu: "continuous_on K u" and cpsi: "continuous_on K \<psi>"
    and sub: "visc_subsol k L (interior K) u"
    and test: "\<And>z. z \<in> interior K \<Longrightarrow> test_fun_at \<psi> g (Hf z) z"
    and strict: "\<And>z. z \<in> interior K \<Longrightarrow> 1 < ell_op k L (g z) (Hf z)"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> u y \<le> \<psi> y"
    and x: "x \<in> K"
  shows "u x \<le> \<psi> x"
proof -
  define \<Phi> where "\<Phi> = (\<lambda>y. u y - \<psi> y)"
  have cont\<Phi>: "continuous_on K \<Phi>"
    unfolding \<Phi>_def using cu cpsi by (intro continuous_intros)
  obtain z where z: "z \<in> K" and zmax: "\<And>y. y \<in> K \<Longrightarrow> \<Phi> y \<le> \<Phi> z"
    using continuous_attains_sup[OF cpt Kne cont\<Phi>] by blast
  text \<open>The maximum cannot be interior: there \<open>\<psi>\<close> is a legitimate test function.\<close>
  have zbd: "z \<in> K - interior K"
  proof (rule ccontr)
    assume "z \<notin> K - interior K"
    then have zi: "z \<in> interior K"
      using z by blast
    obtain e where e: "0 < e" and eball: "ball z e \<subseteq> K"
      using zi unfolding mem_interior by blast
    have loc: "\<exists>e>0. \<forall>y \<in> ball z e. u y - \<psi> y \<le> u z - \<psi> z"
    proof (intro exI[of _ e] conjI e ballI)
      fix y assume "y \<in> ball z e"
      then have "y \<in> K" using eball by blast
      then show "u y - \<psi> y \<le> u z - \<psi> z"
        using zmax unfolding \<Phi>_def by simp
    qed
    have "ell_op k L (g z) (Hf z) \<le> 1"
      using sub zi test[OF zi] loc unfolding visc_subsol_def by blast
    moreover have "1 < ell_op k L (g z) (Hf z)"
      by (rule strict[OF zi])
    ultimately show False
      by simp
  qed
  have "\<Phi> z \<le> 0"
    unfolding \<Phi>_def using bd[OF zbd] by simp
  then have "\<Phi> x \<le> 0"
    using zmax[OF x] by simp
  then show ?thesis
    unfolding \<Phi>_def by simp
qed

text \<open>The dual statement, for a smooth STRICT subsolution below a
  supersolution.\<close>

theorem smooth_strict_le_visc_supersol:
  fixes w \<psi> :: "real^'n::finite \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and Hf :: "real^'n \<Rightarrow> real^'n^'n"
  assumes cpt: "compact K" and Kne: "K \<noteq> {}"
    and cw: "continuous_on K w" and cpsi: "continuous_on K \<psi>"
    and sup: "visc_supersol k L (interior K) w"
    and test: "\<And>z. z \<in> interior K \<Longrightarrow> test_fun_at \<psi> g (Hf z) z"
    and strict: "\<And>z. z \<in> interior K \<Longrightarrow> ell_op k L (g z) (Hf z) < 1"
    and bd: "\<And>y. y \<in> K - interior K \<Longrightarrow> \<psi> y \<le> w y"
    and x: "x \<in> K"
  shows "\<psi> x \<le> w x"
proof -
  define \<Phi> where "\<Phi> = (\<lambda>y. w y - \<psi> y)"
  have cont\<Phi>: "continuous_on K \<Phi>"
    unfolding \<Phi>_def using cw cpsi by (intro continuous_intros)
  obtain z where z: "z \<in> K" and zmin: "\<And>y. y \<in> K \<Longrightarrow> \<Phi> z \<le> \<Phi> y"
    using continuous_attains_inf[OF cpt Kne cont\<Phi>] by blast
  have zbd: "z \<in> K - interior K"
  proof (rule ccontr)
    assume "z \<notin> K - interior K"
    then have zi: "z \<in> interior K"
      using z by blast
    obtain e where e: "0 < e" and eball: "ball z e \<subseteq> K"
      using zi unfolding mem_interior by blast
    have loc: "\<exists>e>0. \<forall>y \<in> ball z e. w z - \<psi> z \<le> w y - \<psi> y"
    proof (intro exI[of _ e] conjI e ballI)
      fix y assume "y \<in> ball z e"
      then have "y \<in> K" using eball by blast
      then show "w z - \<psi> z \<le> w y - \<psi> y"
        using zmin unfolding \<Phi>_def by simp
    qed
    have "1 \<le> ell_op k L (g z) (Hf z)"
      using sup zi test[OF zi] loc unfolding visc_supersol_def by blast
    moreover have "ell_op k L (g z) (Hf z) < 1"
      by (rule strict[OF zi])
    ultimately show False
      by simp
  qed
  have "0 \<le> \<Phi> z"
    unfolding \<Phi>_def using bd[OF zbd] by simp
  then have "0 \<le> \<Phi> x"
    using zmin[OF x] by simp
  then show ?thesis
    unfolding \<Phi>_def by simp
qed

section \<open>Towards Section 2: the feasible set is entrywise bounded\<close>

text \<open>Lemma 2.2 of the paper assumes the set \<open>S\<close> of admissible covariances is
  BOUNDED.  For the paper's \<open>S\<close> that is a purely linear-algebraic fact, provable
  here without any probability: \<open>psd a\<close> bounds the diagonal below by \<open>0\<close> and
  \<open>eigen_ub a L\<close> bounds it above by \<open>L\<close>, testing the quadratic form at the
  coordinate vectors.\<close>

lemma inner_axis_one:
  fixes y :: "real^'n::finite"
  shows "axis i (1 :: real) \<bullet> y = y $ i"
  by (simp add: inner_axis')

lemma matrix_vector_axis_one:
  fixes a :: "real^'n::finite^'n"
  shows "(a *v axis i (1 :: real)) $ l = a $ l $ i"
proof -
  have "(a *v axis i (1 :: real)) $ l
      = (\<Sum>j\<in>UNIV. a $ l $ j * (if j = i then 1 else 0))"
    unfolding matrix_vector_mult_def axis_def by simp
  also have "\<dots> = (\<Sum>j\<in>UNIV. if j = i then a $ l $ j else 0)"
    by (intro sum.cong refl) simp
  also have "\<dots> = a $ l $ i"
    by simp
  finally show ?thesis .
qed

lemma feasible_diag_bound:
  fixes a :: "real^'n::finite^'n"
  assumes af: "a \<in> feasible k L p"
  shows "0 \<le> a $ i $ i" and "a $ i $ i \<le> L"
proof -
  have psda: "0 \<le> x \<bullet> (a *v x)" for x
    using af by (simp add: feasible_def psd_def)
  have ub: "x \<bullet> (a *v x) \<le> L * (x \<bullet> x)" for x
    using af by (simp add: feasible_def eigen_ub_def)
  have q: "axis i (1 :: real) \<bullet> (a *v axis i (1 :: real)) = a $ i $ i"
    by (simp add: inner_axis_one matrix_vector_axis_one)
  have nn: "axis i (1 :: real) \<bullet> axis i (1 :: real) = 1"
    unfolding inner_axis_one by (simp add: axis_def)
  show "0 \<le> a $ i $ i"
    using psda[of "axis i 1"] q by simp
  have "a $ i $ i \<le> L * (axis i (1 :: real) \<bullet> axis i (1 :: real))"
    using ub[of "axis i 1"] q by simp
  then show "a $ i $ i \<le> L"
    unfolding nn by simp
qed

text \<open>Hence the trace is bounded on the feasible set, which is the quantitative
  form Lemma 2.2's hypothesis is used in.\<close>

corollary feasible_trace_bound:
  fixes a :: "real^'n::finite^'n"
  assumes af: "a \<in> feasible k L p"
  shows "0 \<le> trace a" and "trace a \<le> real CARD('n) * L"
proof -
  show "0 \<le> trace a"
    unfolding trace_def
    by (intro sum_nonneg ballI) (rule feasible_diag_bound(1)[OF af])
  have "trace a \<le> (\<Sum>i\<in>(UNIV :: 'n set). L)"
    unfolding trace_def
    by (intro sum_mono) (rule feasible_diag_bound(2)[OF af])
  also have "\<dots> = real CARD('n) * L"
    by simp
  finally show "trace a \<le> real CARD('n) * L" .
qed


text \<open>The off-diagonal entries are bounded too.  Testing the psd quadratic form
  at \<open>axis i 1 \<plusminus> axis j 1\<close> gives \<open>a\<^sub>i\<^sub>i + a\<^sub>j\<^sub>j \<plusminus> 2 a\<^sub>i\<^sub>j \<ge> 0\<close>, i.e.
  \<open>2 \<bar>a\<^sub>i\<^sub>j\<bar> \<le> a\<^sub>i\<^sub>i + a\<^sub>j\<^sub>j \<le> 2 L\<close>.  (For \<open>i = j\<close> the same bound is the diagonal
  one.)\<close>

lemma quadform_axis_pair:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "(axis i (1::real) + axis j 1) \<bullet> (a *v (axis i (1::real) + axis j 1))
       = a $ i $ i + a $ j $ j + 2 * a $ i $ j"
proof -
  have aji: "a $ j $ i = a $ i $ j"
    by (metis sym transpose_def vec_lambda_beta)
  have mv: "(a *v (axis i (1::real) + axis j 1))
      = (a *v axis i (1::real)) + (a *v axis j 1)"
    by (simp add: matrix_vector_right_distrib)
  have "(axis i (1::real) + axis j 1) \<bullet> (a *v (axis i (1::real) + axis j 1))
      = (a *v axis i (1::real)) $ i + (a *v axis j (1::real)) $ i
        + ((a *v axis i (1::real)) $ j + (a *v axis j (1::real)) $ j)"
    unfolding mv by (simp add: inner_add_left inner_axis_one)
  also have "\<dots> = a $ i $ i + a $ i $ j + (a $ j $ i + a $ j $ j)"
    by (simp add: matrix_vector_axis_one)
  also have "\<dots> = a $ i $ i + a $ j $ j + 2 * a $ i $ j"
    unfolding aji by simp
  finally show ?thesis .
qed

lemma matrix_vector_mult_vec_diff:
  fixes a :: "real^'n::finite^'n"
  shows "a *v (x - y) = a *v x - a *v y"
  by (simp add: matrix_vector_mult_def vec_eq_iff right_diff_distrib sum_subtractf)

lemma quadform_axis_pair_minus:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "(axis i (1::real) - axis j 1) \<bullet> (a *v (axis i (1::real) - axis j 1))
       = a $ i $ i + a $ j $ j - 2 * a $ i $ j"
proof -
  have aji: "a $ j $ i = a $ i $ j"
    by (metis sym transpose_def vec_lambda_beta)
  have mv: "(a *v (axis i (1::real) - axis j 1))
      = (a *v axis i (1::real)) - (a *v axis j 1)"
    by (rule matrix_vector_mult_vec_diff)
  have "(axis i (1::real) - axis j 1) \<bullet> (a *v (axis i (1::real) - axis j 1))
      = (a *v axis i (1::real)) $ i - (a *v axis j (1::real)) $ i
        - ((a *v axis i (1::real)) $ j - (a *v axis j (1::real)) $ j)"
    unfolding mv by (simp add: inner_diff_left inner_axis_one)
  also have "\<dots> = a $ i $ i - a $ i $ j - (a $ j $ i - a $ j $ j)"
    by (simp add: matrix_vector_axis_one)
  also have "\<dots> = a $ i $ i + a $ j $ j - 2 * a $ i $ j"
    unfolding aji by simp
  finally show ?thesis .
qed

lemma feasible_offdiag_abs_le:
  fixes a :: "real^'n::finite^'n"
  assumes af: "a \<in> feasible k L p"
  shows "\<bar>a $ i $ j\<bar> \<le> L"
proof -
  have sym: "transpose a = a"
    using af by (simp add: feasible_def psd_def)
  have psda: "0 \<le> x \<bullet> (a *v x)" for x
    using af by (simp add: feasible_def psd_def)
  have dii: "a $ i $ i \<le> L" and djj: "a $ j $ j \<le> L"
    by (rule feasible_diag_bound(2)[OF af])+
  have plus: "0 \<le> a $ i $ i + a $ j $ j + 2 * a $ i $ j"
    using psda[of "axis i 1 + axis j 1"]
    unfolding quadform_axis_pair[OF sym] .
  have minus: "0 \<le> a $ i $ i + a $ j $ j - 2 * a $ i $ j"
    using psda[of "axis i 1 - axis j 1"]
    unfolding quadform_axis_pair_minus[OF sym] .
  have "2 * \<bar>a $ i $ j\<bar> \<le> a $ i $ i + a $ j $ j"
    using plus minus by (simp add: abs_le_iff)
  also have "\<dots> \<le> 2 * L"
    using dii djj by simp
  finally show ?thesis
    by simp
qed

text \<open>Hence Lemma 2.2's hypothesis: the feasible set is BOUNDED.  Combined with
  the Frobenius entry bound this is the quantitative statement the compactness
  argument of Section 2 consumes.\<close>

theorem feasible_bounded:
  fixes p :: "real^'n::finite"
  assumes L: "0 \<le> L"
  shows "bounded (feasible k L p :: (real^'n^'n) set)"
proof (rule boundedI)
  fix a :: "real^'n^'n"
  assume af: "a \<in> feasible k L p"
  have entry: "\<bar>a $ i $ j\<bar> \<le> L" for i j
    by (rule feasible_offdiag_abs_le[OF af])
  have sq: "a \<bullet> a \<le> (real CARD('n) * L)^2"
  proof -
    have "a \<bullet> a = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). a $ i $ j * a $ i $ j)"
      unfolding inner_vec_def by simp
    also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). L * L)"
    proof (intro sum_mono)
      fix i j :: 'n
      have "a $ i $ j * a $ i $ j = \<bar>a $ i $ j\<bar> * \<bar>a $ i $ j\<bar>"
        by (simp add: abs_mult[symmetric])
      also have "\<dots> \<le> L * L"
        using entry[of i j] by (intro mult_mono) auto
      finally show "a $ i $ j * a $ i $ j \<le> L * L" .
    qed
    also have "\<dots> = (real CARD('n) * L)^2"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have "norm a = sqrt (a \<bullet> a)"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> \<le> sqrt ((real CARD('n) * L)^2)"
    using sq by (rule real_sqrt_le_mono)
  also have "\<dots> = real CARD('n) * L"
    using L by simp
  finally show "norm a \<le> real CARD('n) * L" .
qed

end
