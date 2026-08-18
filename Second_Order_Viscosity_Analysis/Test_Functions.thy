section \<open>Test functions and their two-jets\<close>

(*<*)
theory Test_Functions
  imports Soft_Penalty
begin

(*>*)

text \<open>
  The class of functions a viscosity solution is tested against.
  \<open>test_fun_at \<phi> g H x\<close> asks that \<open>\<phi>\<close> be differentiable near \<open>x\<close> with
  gradient field \<open>g\<close>, and that \<open>g\<close> be differentiable at \<open>x\<close> with derivative
  \<open>H\<close>; away from \<open>x\<close> it constrains \<open>\<phi>\<close> not at all.  \<open>test_fun_C2\<close> is the
  smaller class the classical definition quantifies over: a gradient field
  defined everywhere, with a continuous symmetric Hessian field.

  Which class one takes matters in both directions -- the larger class makes
  an assertion that a function IS a solution stronger, and an assumption that
  a competitor is one weaker -- so both are here, with the bridge between
  them and the closure properties (constants, scaling, affine change of
  variable, quadratic and quartic test functions) that any comparison
  argument needs.  None of it mentions an operator.

  \<open>expandable\<close> is the geometric side condition of the same circle of ideas:
  a compact set that can be pushed strictly inside its own image by a
  rotation-dilation-translation arbitrarily close to the identity.  Convex
  bodies with nonempty interior are expandable.
\<close>

text \<open>
  Every notion of viscosity sub- and supersolution the development uses, and
  the test-function predicates they quantify over.  They were spread over
  five theories, each defined where it was first needed; the implications
  between them stay where their proofs' machinery is, but the definitions
  are collected here so that the five variants can be read against each
  other.

  The envelope operators \<open>ell_op_lsc\<close> and \<open>ell_op_usc\<close> come along because
  three of the predicates are stated through them, and their definitions
  need nothing beyond \<open>ell_op\<close>.  Their calculus is in
  \<open>Operator_Envelopes\<close>.
\<close>

definition test_fun_at ::
  "(real^'n \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool"
  where
  "test_fun_at \<phi> g H x \<longleftrightarrow>
     transpose H = H \<and>
     (\<exists>e>0. \<forall>y \<in> ball x e. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)) \<and>
     (g has_derivative (\<lambda>h. H *v h)) (at x)"

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

text \<open>The paper's hypothesis on \<open>K\<close> for the uniqueness clause of Theorem 1.1:
  a family \<open>T\<^sub>\<iota>\<close> of rotation-dilation-translations, \<open>\<iota> \<in> (1,2]\<close>, with
  \<open>K \<subseteq> (T\<^sub>\<iota> \` K)^\<circ>\<close> and \<open>T\<^sub>\<iota> \<rightarrow> id\<close>, phrased as an \<open>\<epsilon>\<close>-statement with
  the inverse map written out so no invertibility side condition is
  carried.\<close>

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

lemma test_fun_at_scaleR:
  fixes H :: "real^'n::finite^'n"
  assumes tf: "test_fun_at \<phi> g H x" and c: "0 < c"
  shows "test_fun_at (\<lambda>z. c * \<phi> z) (\<lambda>z. c *\<^sub>R g z) (c *\<^sub>R H) x"
  unfolding test_fun_at_def
proof (intro conjI)
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  show "transpose (c *\<^sub>R H) = c *\<^sub>R H"
    unfolding transpose_scalar symH ..
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
      by (simp add: transpose_scalar G(3))
  next
    show "continuous_on UNIV (\<lambda>y. c *\<^sub>R G y)"
      by (intro continuous_intros G(4))
  next
    show "c *\<^sub>R G x = c *\<^sub>R H" by (simp add: G(5))
  qed
qed

text \<open>\<open>conj_mat_continuous\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

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
      finally show ?thesis by (simp add: transpose_scalar)
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
      by (simp add: transpose_scalar)
  next
    show "continuous_on UNIV (\<lambda>y. (c\<^sup>2) *\<^sub>R (transpose R ** G (A y) ** R))"
      using conj_mat_continuous[OF GA] by (intro continuous_intros)
  next
    show "(c\<^sup>2) *\<^sub>R (transpose R ** G (A x) ** R)
        = (c\<^sup>2) *\<^sub>R (transpose R ** H ** R)" by (simp add: G(5))
  qed
  show ?thesis using main unfolding A_def .
qed

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

text \<open>\<open>test_fun_C2\<close> lives in \<open>Viscosity_Definitions\<close>.\<close>

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

text \<open>\<open>visc_subsol_env2\<close>, \<open>visc_supersol_env2\<close> live in \<open>Viscosity_Definitions\<close>.\<close>

text \<open>Fewer test functions means a weaker condition, so everything proved in the
  \<^const>\<open>test_fun_at\<close> form still delivers Definition 3.1 as the paper states it.\<close>


(*<*)

lemma test_fun_at_quartic_shift:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and C :: real
  assumes tf: "test_fun_at \<phi> g H x"
  shows "test_fun_at (\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2)
      (\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) H x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose H = H" using tf unfolding test_fun_at_def by blast
next
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have main: "((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
      (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)) (at y)"
    if y: "y \<in> ball x e" for y
  proof -
    have d1: "(\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)" by (rule dphi[OF y])
    have d2: "((\<lambda>z :: real^'n. C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))) (at y)"
      by (auto intro!: derivative_eq_intros simp: inner_commute)
    have d3: "((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. g y \<bullet> h
          - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))) (at y)"
      by (rule has_derivative_diff[OF d1 d2])
    have d4: "(\<lambda>h. g y \<bullet> h
          - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h))))
        = (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)"
    proof (rule ext)
      fix h :: "real^'n"
      show "g y \<bullet> h - C * (2 * ((y - x) \<bullet> (y - x)) * (2 * ((y - x) \<bullet> h)))
          = (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h"
        unfolding quartic_coeff_assoc by (rule inner_scaleR_diff_eq)
    qed
    show ?thesis using d3 unfolding d4 .
  qed
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. \<phi> z - C * ((z - x) \<bullet> (z - x))\<^sup>2) has_derivative
        (\<lambda>h. (g y - (4 * C * ((y - x) \<bullet> (y - x))) *\<^sub>R (y - x)) \<bullet> h)) (at y)"
    using e0 main by blast
next
  have dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast
  have dq: "((\<lambda>z :: real^'n. (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))
      has_derivative (\<lambda>h. 0)) (at x)"
    by (auto intro!: derivative_eq_intros)
  have "((\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x)) has_derivative
      (\<lambda>h. H *v h - 0)) (at x)"
    by (rule has_derivative_diff[OF dg dq])
  then show "((\<lambda>z. g z - (4 * C * ((z - x) \<bullet> (z - x))) *\<^sub>R (z - x))
      has_derivative (\<lambda>h. H *v h)) (at x)" by simp
qed

lemma test_fun_at_quadratic:
  fixes M :: "real^'n::finite^'n" and p x :: "real^'n" and c :: real
  assumes sym: "transpose M = M"
  shows "test_fun_at (\<lambda>z. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
      (\<lambda>z. p + M *v z) M x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose M = M" by (rule sym)
next
  have bl: "bounded_linear (\<lambda>z :: real^'n. M *v z)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have dM: "((\<lambda>z :: real^'n. M *v z) has_derivative (\<lambda>h. M *v h)) (at y)"
    for y :: "real^'n"
    by (rule bounded_linear.has_derivative[OF bl has_derivative_ident])
  have d: "((\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
      has_derivative (\<lambda>h. (p + M *v y) \<bullet> h)) (at y)" for y :: "real^'n"
  proof -
    have "((\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
        has_derivative (\<lambda>h. p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2))
        (at y)"
      by (auto intro!: derivative_eq_intros dM)
    moreover have "(\<lambda>h :: real^'n. p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2)
        = (\<lambda>h. (p + M *v y) \<bullet> h)"
    proof (rule ext)
      fix h :: "real^'n"
      have "y \<bullet> (M *v h) = (transpose M *v y) \<bullet> h"
        by (rule inner_transpose_matrix)
      then have "y \<bullet> (M *v h) = (M *v y) \<bullet> h" using sym by simp
      then show "p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2
          = (p + M *v y) \<bullet> h"
        by (simp add: inner_commute inner_add_right)
    qed
    ultimately show ?thesis by simp
  qed
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2) has_derivative
        (\<lambda>h. (p + M *v y) \<bullet> h)) (at y)"
    using d by (intro exI[of _ 1]) auto
next
  have bl: "bounded_linear (\<lambda>z :: real^'n. M *v z)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  show "((\<lambda>z. p + M *v z) has_derivative (\<lambda>h. M *v h)) (at x)"
    using bounded_linear.has_derivative[OF bl has_derivative_ident]
    by (auto intro!: derivative_eq_intros)
qed

section \<open>The ball exit time along a continuous path\<close>

text \<open>Three pathwise facts about \<open>pball_exit\<close>, all consumed by an
  Ito-side supplier and none needing a law: they are statements about a
  single continuous path.

  The first is attainment.  With \<open>K\<close> open the target \<open>-K\<close> is closed, so
  along a continuous path the infimum defining \<open>pexit\<close> is a minimum
  whenever it is below the horizon: the path really is outside \<open>K\<close> at the
  exit time.  This is the single fact that fails for a general
  discontinuous function, and every other clause below is a consequence
  of it.\<close>

lemma test_fun_at_shifted_quadratic:
  fixes M :: "real^'n::finite^'n" and x \<eta> y :: "real^'n" and b :: real
  assumes sym: "transpose M = M"
  shows "test_fun_at (\<lambda>z. b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. M *v (z - x) + \<eta>) M y"
proof -
  define p where "p = \<eta> - M *v x"
  define cc where "cc = b + (x \<bullet> (M *v x)) / 2 - \<eta> \<bullet> x"
  have f_eq: "(\<lambda>z. b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      = (\<lambda>z. cc + p \<bullet> z + (z \<bullet> (M *v z)) / 2)"
  proof (rule ext)
    fix z :: "real^'n"
    have m1: "M *v (z - x) = M *v z - M *v x"
      by (simp add: matrix_vector_mult_diff_distrib)
    have s1: "x \<bullet> (M *v z) = z \<bullet> (M *v x)"
    proof -
      have "x \<bullet> (M *v z) = (transpose M *v x) \<bullet> z"
        by (rule inner_transpose_matrix)
      also have "\<dots> = (M *v x) \<bullet> z" using sym by simp
      finally show ?thesis by (simp add: inner_commute)
    qed
    have s2: "(M *v x) \<bullet> z = z \<bullet> (M *v x)" by (rule inner_commute)
    have e: "(z - x) \<bullet> (M *v (z - x))
        = z \<bullet> (M *v z) - 2 * (z \<bullet> (M *v x)) + x \<bullet> (M *v x)"
      unfolding m1 using s1
      by (simp add: inner_diff_left inner_diff_right)
    have pz: "p \<bullet> z = \<eta> \<bullet> z - z \<bullet> (M *v x)"
      unfolding p_def by (simp add: inner_diff_left s2)
    have ez: "\<eta> \<bullet> (z - x) = \<eta> \<bullet> z - \<eta> \<bullet> x"
      by (simp add: inner_diff_right)
    show "b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x)
        = cc + p \<bullet> z + (z \<bullet> (M *v z)) / 2"
      unfolding e cc_def pz ez by (simp add: field_simps)
  qed
  have g_eq: "(\<lambda>z :: real^'n. M *v (z - x) + \<eta>) = (\<lambda>z. p + M *v z)"
    by (rule ext) (simp add: p_def algebra_simps)
  show ?thesis
    unfolding f_eq g_eq by (rule test_fun_at_quadratic[OF sym])
qed

text \<open>The heart of Case 2.  Given a strict quadratic separation on a
  closed ball --- which is what \<open>test_fun_strict_minorate_zero_grad\<close>
  delivers once the gradient vanishes --- a tilt by \<open>\<eta>\<close> has a minimiser
  \<open>y\<close>, and that minimiser is within \<open>\<bar>\<eta>\<bar>/c\<close> of the centre.  For
  \<open>\<bar>\<eta>\<bar> < c\<rho>\<close> that puts \<open>y\<close> strictly inside the ball, so the minimality
  is a genuine local touching at \<open>y\<close> --- exactly the hypothesis the
  localised Case 1 consumes.

  No properties of \<open>W\<close> are used beyond lower semicontinuity: the lower
  bound needed for the infimum comes from the separation itself, since
  \<open>W \<ge> W x + Q + c\<bar>z - x\<bar>\<^sup>2\<close> already forces \<open>W - Q - \<langle>\<eta>, \<cdot> - x\<rangle> \<ge> W x - \<bar>\<eta>\<bar>\<rho>\<close>
  on the ball.\<close>

lemma test_fun_quadratic_minorates:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<delta> :: real
  assumes tf: "test_fun_at \<phi> g H x" and d0: "0 < \<delta>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
proof -
  have dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
      norm (g y - g x - (H *v (y - x))) \<le> e * norm (y - x)"
    using dg unfolding has_derivative_at_alt by blast
  moreover have "0 < \<delta> / 2" using d0 by simp
  ultimately obtain d where dd: "0 < d"
    and bnd: "\<And>y. norm (y - x) < d \<Longrightarrow>
        norm (g y - g x - (H *v (y - x))) \<le> (\<delta> / 2) * norm (y - x)"
    by blast
  define r where "r = min e d"
  have r0: "0 < r" using e0 dd by (simp add: r_def)
  have main: "\<phi> x + g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    if z: "z \<in> ball x r" for z
  proof -
    define v where "v = z - x"
    have nv: "norm v < r"
      using z by (simp add: v_def dist_norm norm_minus_commute)
    define A where "A = g x \<bullet> v"
    define B where "B = v \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v v)"
    define f where "f t = (\<phi> x + t * A + t\<^sup>2 * B / 2) - \<phi> (x + t *\<^sub>R v)" for t
    have f0: "f 0 = 0" by (simp add: f_def)
    have deriv: "\<exists>y. (f has_field_derivative y) (at t) \<and> y \<le> 0"
      if t: "0 \<le> t" "t \<le> 1" for t
    proof -
      have ntv: "norm (t *\<^sub>R v) \<le> norm v"
        using t by (simp add: mult_left_le_one_le)
      have mem: "x + t *\<^sub>R v \<in> ball x e"
        using ntv nv by (simp add: dist_norm r_def)
      have d1: "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_field_derivative
          g (x + t *\<^sub>R v) \<bullet> v) (at t)"
      proof -
        have i1: "((\<lambda>t :: real. x + t *\<^sub>R v) has_derivative (\<lambda>h. h *\<^sub>R v)) (at t)"
          by (auto intro!: derivative_eq_intros)
        have i2: "(\<phi> has_derivative (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> h)) (at (x + t *\<^sub>R v))"
          by (rule dphi[OF mem])
        have "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_derivative
            (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> (h *\<^sub>R v))) (at t)"
          using diff_chain_at[OF i1 i2] by (simp add: o_def)
        then show ?thesis
          by (rule has_derivative_imp_has_field_derivative)
            (simp add: ac_simps)
      qed
      have d2: "((\<lambda>t. \<phi> x + t * A + t\<^sup>2 * B / 2) has_field_derivative
          A + t * B) (at t)"
        by (auto intro!: derivative_eq_intros)
      have df: "(f has_field_derivative
          ((A + t * B) - g (x + t *\<^sub>R v) \<bullet> v)) (at t)"
        unfolding f_def by (rule DERIV_diff[OF d2 d1])
      have expand: "(A + t * B) - g (x + t *\<^sub>R v) \<bullet> v
          = - ((g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v)
            - t * (\<delta> * (v \<bullet> v))"
      proof -
        have m1: "(H - \<delta> *\<^sub>R mat 1) *v v = H *v v - \<delta> *\<^sub>R v"
          by (simp add: matrix_vector_mult_diff_rdistrib scaleR_matrix_vector
              )
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_commute
              algebra_simps)
      qed
      have small: "- ((g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v)
          \<le> (\<delta> / 2) * (t * norm v) * norm v"
      proof -
        have "norm (t *\<^sub>R v) < d"
          using ntv nv by (simp add: r_def)
        moreover have "(x + t *\<^sub>R v) - x = t *\<^sub>R v" by simp
        ultimately have nb: "norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            \<le> (\<delta> / 2) * norm (t *\<^sub>R v)"
          using bnd[of "x + t *\<^sub>R v"] by simp
        have "- ((g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v)
            = (- (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))) \<bullet> v"
          by (metis inner_minus_left)
        also have "\<dots> \<le> norm (- (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))))
            * norm v"
          by (rule norm_cauchy_schwarz)
        also have "\<dots> = norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            * norm v"
          by (metis norm_minus_cancel)
        also have "\<dots> \<le> ((\<delta> / 2) * norm (t *\<^sub>R v)) * norm v"
          by (rule mult_right_mono[OF nb norm_ge_zero])
        also have "\<dots> = (\<delta> / 2) * (t * norm v) * norm v"
          using t by simp
        finally show ?thesis .
      qed
      have vv: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have "(A + t * B) - g (x + t *\<^sub>R v) \<bullet> v
          \<le> (\<delta> / 2) * (t * norm v) * norm v - t * (\<delta> * (norm v * norm v))"
        unfolding expand vv by (rule diff_right_mono[OF small])
      also have "\<dots> = - (\<delta> / 2) * t * (norm v * norm v)"
        by (simp add: field_simps)
      also have "\<dots> \<le> 0"
        using d0 t by simp
      finally show ?thesis using df by blast
    qed
    have "f 1 \<le> f 0"
      by (rule DERIV_nonpos_imp_nonincreasing[of 0 1 f])
        (use deriv in auto)
    then have "\<phi> x + 1 * A + 1\<^sup>2 * B / 2 \<le> \<phi> (x + 1 *\<^sub>R v)"
      using f0 by (simp add: f_def)
    then show ?thesis by (simp add: v_def A_def B_def)
  qed
  show ?thesis by (rule that[OF r0 main])
qed

text \<open>\<open>quartic_coeff_assoc\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>


text \<open>\<open>transpose_shift_add\<close>, \<open>transpose_shift_diff\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

lemma test_fun_quadratic_dominates:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<delta> :: real
  assumes tf: "test_fun_at \<phi> g H x" and d0: "0 < \<delta>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> z \<le> \<phi> x + g x \<bullet> (z - x) + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
proof -
  have symH: "transpose H = H"
    and dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast+
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
      norm (g y - g x - (H *v (y - x))) \<le> e * norm (y - x)"
    using dg unfolding has_derivative_at_alt by blast
  moreover have "0 < \<delta> / 2" using d0 by simp
  ultimately obtain d where dd: "0 < d"
    and bnd: "\<And>y. norm (y - x) < d \<Longrightarrow>
        norm (g y - g x - (H *v (y - x))) \<le> (\<delta> / 2) * norm (y - x)"
    by blast
  define r where "r = min e d"
  have r0: "0 < r" using e0 dd by (simp add: r_def)
  have main: "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    if z: "z \<in> ball x r" for z
  proof -
    define v where "v = z - x"
    have nv: "norm v < r"
      using z by (simp add: v_def dist_norm norm_minus_commute)
    define A where "A = g x \<bullet> v"
    define B where "B = v \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v v)"
    define f where "f t = \<phi> (x + t *\<^sub>R v) - (\<phi> x + t * A + t\<^sup>2 * B / 2)" for t
    have f0: "f 0 = 0" by (simp add: f_def)
    have deriv: "\<exists>y. (f has_field_derivative y) (at t) \<and> y \<le> 0"
      if t: "0 \<le> t" "t \<le> 1" for t
    proof -
      have ntv: "norm (t *\<^sub>R v) \<le> norm v"
        using t by (simp add: mult_left_le_one_le)
      have mem: "x + t *\<^sub>R v \<in> ball x e"
        using ntv nv by (simp add: dist_norm r_def)
      have d1: "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_field_derivative
          g (x + t *\<^sub>R v) \<bullet> v) (at t)"
      proof -
        have i1: "((\<lambda>t :: real. x + t *\<^sub>R v) has_derivative (\<lambda>h. h *\<^sub>R v)) (at t)"
          by (auto intro!: derivative_eq_intros)
        have i2: "(\<phi> has_derivative (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> h)) (at (x + t *\<^sub>R v))"
          by (rule dphi[OF mem])
        have "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_derivative
            (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> (h *\<^sub>R v))) (at t)"
          using diff_chain_at[OF i1 i2] by (simp add: o_def)
        then show ?thesis
          by (rule has_derivative_imp_has_field_derivative)
            (simp add: ac_simps)
      qed
      have d2: "((\<lambda>t. \<phi> x + t * A + t\<^sup>2 * B / 2) has_field_derivative
          A + t * B) (at t)"
        by (auto intro!: derivative_eq_intros)
      have df: "(f has_field_derivative
          (g (x + t *\<^sub>R v) \<bullet> v - (A + t * B))) (at t)"
        unfolding f_def by (rule DERIV_diff[OF d1 d2])
      have expand: "g (x + t *\<^sub>R v) \<bullet> v - (A + t * B)
          = (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v - t * (\<delta> * (v \<bullet> v))"
      proof -
        have m1: "(H + \<delta> *\<^sub>R mat 1) *v v = H *v v + \<delta> *\<^sub>R v"
          by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector
              )
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_commute
              algebra_simps)
      qed
      have small: "(g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v
          \<le> (\<delta> / 2) * (t * norm v) * norm v"
      proof -
        have "norm (t *\<^sub>R v) < d"
          using ntv nv by (simp add: r_def)
        moreover have "(x + t *\<^sub>R v) - x = t *\<^sub>R v" by simp
        ultimately have nb: "norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            \<le> (\<delta> / 2) * norm (t *\<^sub>R v)"
          using bnd[of "x + t *\<^sub>R v"] by simp
        have "(g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v
            \<le> norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) * norm v"
          by (rule norm_cauchy_schwarz)
        also have "\<dots> \<le> ((\<delta> / 2) * norm (t *\<^sub>R v)) * norm v"
          by (rule mult_right_mono[OF nb norm_ge_zero])
        also have "\<dots> = (\<delta> / 2) * (t * norm v) * norm v"
          using t by simp
        finally show ?thesis .
      qed
      have vv: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have "g (x + t *\<^sub>R v) \<bullet> v - (A + t * B)
          \<le> (\<delta> / 2) * (t * norm v) * norm v - t * (\<delta> * (norm v * norm v))"
        unfolding expand vv by (rule diff_right_mono[OF small])
      also have "\<dots> = - (\<delta> / 2) * t * (norm v * norm v)"
        by (simp add: field_simps)
      also have "\<dots> \<le> 0"
        using d0 t by simp
      finally show ?thesis using df by blast
    qed
    have "f 1 \<le> f 0"
      by (rule DERIV_nonpos_imp_nonincreasing[of 0 1 f])
        (use deriv in auto)
    then have "\<phi> (x + 1 *\<^sub>R v) \<le> \<phi> x + 1 * A + 1\<^sup>2 * B / 2"
      using f0 by (simp add: f_def)
    then show ?thesis by (simp add: v_def A_def B_def)
  qed
  show ?thesis by (rule that[OF r0 main])
qed

text \<open>The mirror for subsolutions: adding a quartic deepens a local
  maximum and, for a large enough coefficient, makes it global over \<open>K\<close>,
  reusing @{thm [source] test_fun_at_quartic_shift} with a negative
  coefficient.\<close>

lemma test_fun_strict_minorant_zero_grad:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<epsilon> :: real
  assumes tf: "test_fun_at \<phi> g H x" and g0: "g x = 0" and e0: "0 < \<epsilon>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z"
proof -
  have he: "0 < \<epsilon> / 2" using e0 by simp
  obtain r where r0: "0 < r"
    and min2: "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    by (rule test_fun_quadratic_minorates[OF tf he]) blast
  have key: "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
      + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z" if zr: "z \<in> ball x r" for z
  proof -
    have e1: "(H - \<epsilon> *\<^sub>R mat 1) *v (z - x) = H *v (z - x) - \<epsilon> *\<^sub>R (z - x)"
      by (simp add: matrix_vector_mult_diff_rdistrib
          scaleR_matrix_vector)
    have e2: "(H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x)
        = H *v (z - x) - (\<epsilon>/2) *\<^sub>R (z - x)"
      by (simp add: matrix_vector_mult_diff_rdistrib
          scaleR_matrix_vector)
    have i1: "(z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))
        = (z - x) \<bullet> (H *v (z - x)) - \<epsilon> * ((z - x) \<bullet> (z - x))"
      unfolding e1 by (simp add: inner_diff_right)
    have i2: "(z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))
        = (z - x) \<bullet> (H *v (z - x)) - (\<epsilon>/2) * ((z - x) \<bullet> (z - x))"
      unfolding e2 by (simp add: inner_diff_right)
    have "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      = \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))) / 2"
      unfolding i1 i2 g0 by (simp add: field_simps)
    also have "\<dots> \<le> \<phi> z" by (rule min2[OF zr])
    finally show ?thesis .
  qed
  show ?thesis by (rule that[OF r0]) (use key in blast)
qed

text \<open>\<open>tilted_minimiser_close\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>The tilted test function of Case 2 is the quadratic
  \<open>b + \<onehalf>(z - x)\<^sup>T M (z - x) + \<langle>\<eta>, z - x\<rangle>\<close>, centred at the touching point
  \<open>x\<close> but examined at a nearby point \<open>y\<close>.  Recentring it into the normal
  form \<open>c + \<langle>p, z\<rangle> + \<onehalf>z\<^sup>T M z\<close> uses only symmetry of \<open>M\<close>, which
  \<open>test_fun_at\<close> supplies as part of its own definition.\<close>

lemma touching_grad_lt_horizon_gen:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and W :: "real^'n \<Rightarrow> real"
  assumes xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and rho0: "0 < \<rho>"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      W x - \<phi> x \<le> W y - \<phi> y"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> W y \<le> T"
    and gx0: "g x \<noteq> 0"
  shows "W x < T"
proof -
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  define h where "h = (\<lambda>s. \<phi> (x + s *\<^sub>R g x))"
  have hd: "(h has_field_derivative (g x \<bullet> g x)) (at 0)"
  proof -
    have i1: "((\<lambda>s :: real. x + s *\<^sub>R g x)
        has_derivative (\<lambda>u. u *\<^sub>R g x)) (at 0)"
      by (auto intro!: derivative_eq_intros)
    have mem0: "x + (0::real) *\<^sub>R g x \<in> ball x e" using e0 by simp
    have i2: "(\<phi> has_derivative (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> u))
        (at (x + (0::real) *\<^sub>R g x))"
      by (rule dphi[OF mem0])
    have "((\<lambda>s. \<phi> (x + s *\<^sub>R g x)) has_derivative
        (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> (u *\<^sub>R g x))) (at 0)"
      using diff_chain_at[OF i1 i2] by (simp add: o_def)
    then show ?thesis unfolding h_def
      by (rule has_derivative_imp_has_field_derivative)
        (simp add: ac_simps)
  qed
  have gg0: "0 < g x \<bullet> g x"
    using gx0 by simp
  have "((\<lambda>s. (h s - h 0) / (s - 0)) \<longlongrightarrow> g x \<bullet> g x) (at 0)"
    using hd by (simp add: has_field_derivative_iff)
  then have "\<forall>\<^sub>F s in at (0::real). 0 < (h s - h 0) / (s - 0)"
    by (rule order_tendstoD(1)[OF _ gg0])
  then obtain d where d0: "0 < d"
    and hpos: "\<And>s :: real. s \<noteq> 0 \<Longrightarrow> \<bar>s\<bar> < d \<Longrightarrow> 0 < (h s - h 0) / s"
    unfolding eventually_at by (auto simp: dist_real_def)
  define ng where "ng = norm (g x) + 1"
  have ng0: "0 < ng" unfolding ng_def
    using norm_ge_zero[of "g x"] by linarith
  define s where
    "s = min (min d (e / ng)) (min (eK / ng) (\<rho> / ng)) / 2"
  have s0: "0 < s"
    unfolding s_def using d0 e0 eK0 ng0 rho0 by simp
  have sd: "s < d" unfolding s_def using d0 e0 eK0 ng0 rho0 by auto
  have se: "s * ng < e"
  proof -
    have "s \<le> (e / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> e / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using e0 by linarith
  qed
  have sK: "s * ng < eK"
  proof -
    have "s \<le> (eK / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> eK / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using eK0 by linarith
  qed
  have sR: "s * ng < \<rho>"
  proof -
    have "s \<le> (\<rho> / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> \<rho> / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using rho0 by linarith
  qed
  have sg_lt: "s * norm (g x) < min e (min eK \<rho>)"
  proof -
    have "s * norm (g x) \<le> s * ng"
      unfolding ng_def using s0 by (intro mult_left_mono) auto
    then show ?thesis using se sK sR by simp
  qed
  define z where "z = x + s *\<^sub>R g x"
  have dz: "dist x z = s * norm (g x)"
    unfolding z_def dist_norm using s0 by simp
  have zK: "z \<in> K"
  proof -
    have "z \<in> ball x eK" using dz sg_lt by simp
    then show ?thesis using eKK by blast
  qed
  have zR: "dist x z < \<rho>" using dz sg_lt by simp
  have hgt: "\<phi> x < \<phi> z"
  proof -
    have "0 < (h s - h 0) / s" using hpos[of s] s0 sd by simp
    then have "0 < h s - h 0" using s0 by (simp add: zero_less_divide_iff)
    then show ?thesis unfolding h_def z_def by simp
  qed
  have "W x \<le> W z - (\<phi> z - \<phi> x)" using tmin[OF zK zR] by simp
  also have "\<dots> < W z" using hgt by simp
  also have "\<dots> \<le> T" by (rule bnd[OF zK])
  finally show ?thesis .
qed

definition expandable :: "(real^'n::finite) set \<Rightarrow> bool" where
  "expandable K \<longleftrightarrow>
     (\<forall>e > 0. \<exists>R b c. orthogonal_matrix R \<and> 1 < c \<and> c < 1 + e
        \<and> K \<subseteq> interior ((\<lambda>x. c *\<^sub>R (R *v x) + b) ` K)
        \<and> (\<forall>x \<in> K. dist ((1/c) *\<^sub>R (transpose R *v (x - b))) x \<le> e))"

text \<open>The envelopes are taken in the pair \<open>(p, M)\<close> jointly, as in the
  paper, so \<open>F\<close> is first packaged as a function on the product metric
  space, with values in \<open>ereal\<close> so that the suprema and infima below are
  unconditionally defined.\<close>

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

text \<open>\<open>affine_linear\<close>, \<open>affine_has_derivative\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>The chain rule through \<open>A z = c \<cdot> Rz + b\<close>: the gradient picks up a
  factor \<open>c\<close> and a transpose, the Hessian a factor \<open>c^2\<close> and a
  conjugation - precisely what the invariances of \<open>F\<close> (display (4.4))
  undo.\<close>

(*<*)
end
(*>*)
