section \<open>Two-domain comparison: Theorem 4.2(b), Theorem 4.3, Proposition 4.1\<close>

(*<*)
theory Comparison_Two_Domain
  imports Comparison_Principle
begin

(*>*)

text \<open>
  What the one-domain maximum principle is for: the boundary-nonnegativity
  argument and the \<open>T\<^sub>\<iota>\<close> hypothesis it needs, the two-domain
  principle, and the two uniqueness statements built on them.
\<close>

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

text \<open>\<open>expandable\<close> lives in @{theory Relative_Arbitrage.Viscosity_Definitions}.\<close>


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
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

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

text \<open>\<open>two_domain_gap\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


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
