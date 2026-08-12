(*
  Title:   Relative_Arbitrage_PDE.thy
  Content: Formalization of the deterministic core of

             J.-H. Lai, M. Shkolnikov, H. M. Soner:
             "Relative arbitrage problem under eigenvalue lower bounds"
             arXiv:2512.17702

  Scope: The paper characterizes time horizons for relative arbitrage via the
  fully nonlinear elliptic PDE  F(Dv, D^2 v) = 1  on a compact set K, where
  (Eq. 1.9)

    F(p, M) = inf { -1/2 tr(M a) :  a psd,  a p = 0,
                                    lambda_(n-k)(a) >= 1,  lambda_(1)(a) <= L }

  (lambda_(m) = m-th largest eigenvalue).  We formalize:

    * the constraint set of Eq. 1.9, with the spectral conditions expressed
      through their Courant-Fischer variational characterizations
      (lambda_(m)(a) >= 1  iff  some m-dimensional subspace S has
       Rayleigh quotient >= 1 on S;  lambda_(1)(a) <= L  iff the Rayleigh
       quotient is <= L everywhere), which avoids developing the spectral
      theorem while remaining equivalent for symmetric matrices;
    * the operator F;
    * the trace lower bound  tr(a) >= n - k  for feasible a (the Ky Fan /
      Courant-Fischer argument underlying the lower bound in Example 3.1);
    * feasibility: rank-(n-k) orthogonal projections orthogonal to p are
      admissible and attain the bound;
    * Example 3.1 (Eq. 3.9): on the ball B_r(0) the function
        v(x) = max (r^2 - |x|^2) 0 / (n - k)
      satisfies F(grad v(x), Hess v(x)) = 1 for every x in the open ball
      (including the centre, where the gradient vanishes and the constraint
      a p = 0 of Eq. 1.9 becomes vacuous),
      with v = 0 on the boundary; we also verify grad and Hess by
      differentiation;
    * the spectral theorem for real symmetric matrices (variational proof),
      nonnegativity of traces of products of psd matrices, and the
      degenerate ellipticity of F;
    * viscosity sub-/supersolutions of F(Du, D^2u) = 1 in the standard
      Crandall-Ishii-Lions test-function formulation (no AFP entry covers
      viscosity solutions), together with first- and second-order
      conditions at interior minima, and the theorem that v is a viscosity
      solution on the whole open ball -- the interior of K in Definition
      3.1 -- with zero boundary values: the
      solvability part of Theorem 1.1 for Example 3.1.

  The probabilistic side (Definition 1.1, the class of sufficiently
  volatile markets in martingale-problem form, and the exit-time bound of
  Example 3.1) is formalized in the companion theory
  Relative_Arbitrage_Stochastic.  Not formalized (out of reach of current
  Isabelle/HOL libraries): Ito calculus and stochastic integration, the
  optimal-martingale construction (Eq. 3.11), the comparison/uniqueness
  part of Theorem 1.1, and Lemma 3.1 (semicontinuous envelopes).
*)

theory Relative_Arbitrage_PDE
  imports "HOL-Analysis.Analysis"
begin

unbundle inner_syntax

section \<open>Linear-algebra preliminaries\<close>

subsection \<open>Outer products\<close>

definition outer_prod :: "real^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "outer_prod u v = (\<chi> i j. u $ i * v $ j)"

lemma outer_prod_mv [simp]: "outer_prod u v *v x = (v \<bullet> x) *\<^sub>R u"
  unfolding outer_prod_def matrix_vector_mult_def inner_vec_def
  by (simp add: vec_eq_iff sum_distrib_left ac_simps)

lemma transpose_outer_prod [simp]: "transpose (outer_prod u v) = outer_prod v u"
  by (simp add: outer_prod_def transpose_def vec_eq_iff)

lemma trace_outer_prod [simp]: "trace (outer_prod u v) = u \<bullet> v"
  by (simp add: outer_prod_def trace_def inner_vec_def)

lemma mult_outer_prod: "A ** outer_prod u v = outer_prod (A *v u) v"
  unfolding outer_prod_def matrix_matrix_mult_def matrix_vector_mult_def
  by (simp add: vec_eq_iff sum_distrib_left sum_distrib_right ac_simps)

subsection \<open>Sums of matrices\<close>

lemma trace_matrix_sum: "trace (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. trace (f x))"
proof -
  have "trace (\<Sum>x\<in>S. f x) = (\<Sum>i\<in>UNIV. \<Sum>x\<in>S. f x $ i $ i)"
    by (simp add: trace_def)
  also have "\<dots> = (\<Sum>x\<in>S. \<Sum>i\<in>UNIV. f x $ i $ i)"
    by (rule sum.swap)
  finally show ?thesis
    by (simp add: trace_def)
qed

lemma transpose_matrix_sum: "transpose (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. transpose (f x))"
  by (simp add: transpose_def vec_eq_iff)

lemma matrix_vector_mult_sum: "(\<Sum>x\<in>S. f x) *v y = (\<Sum>x\<in>S. f x *v y)"
proof -
  have "((\<Sum>x\<in>S. f x) *v y) $ i = (\<Sum>x\<in>S. f x *v y) $ i" for i
  proof -
    have "((\<Sum>x\<in>S. f x) *v y) $ i = (\<Sum>j\<in>UNIV. \<Sum>x\<in>S. f x $ i $ j * y $ j)"
      by (simp add: matrix_vector_mult_def sum_distrib_right)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>j\<in>UNIV. f x $ i $ j * y $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_vector_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma matrix_mult_sum_right: "A ** (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. A ** f x)"
proof -
  have "(A ** (\<Sum>x\<in>S. f x)) $ i $ j = (\<Sum>x\<in>S. A ** f x) $ i $ j" for i j
  proof -
    have "(A ** (\<Sum>x\<in>S. f x)) $ i $ j = (\<Sum>k\<in>UNIV. \<Sum>x\<in>S. A $ i $ k * f x $ k $ j)"
      by (simp add: matrix_matrix_mult_def sum_distrib_left)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>k\<in>UNIV. A $ i $ k * f x $ k $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_matrix_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma scaleR_matrix_mult:
  fixes A :: "real^'m^'n" and B :: "real^'p^'m"
  shows "(r *\<^sub>R A) ** B = r *\<^sub>R (A ** B)"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_distrib_left ac_simps)

lemma trace_scaleR: "trace (r *\<^sub>R A) = r * trace A"
  by (simp add: trace_def sum_distrib_left)

lemma scaleR_matrix_vector:
  fixes A :: "real^'m^'n"
  shows "(r *\<^sub>R A) *v x = r *\<^sub>R (A *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_distrib_left ac_simps)

lemma neg_matrix_vector:
  fixes A :: "real^'m^'n"
  shows "(- A) *v x = - (A *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)

subsection \<open>Orthonormal families\<close>

definition onormal :: "(real^'n) set \<Rightarrow> bool" where
  "onormal B \<longleftrightarrow> finite B \<and> pairwise orthogonal B \<and> (\<forall>u\<in>B. norm u = 1)"

lemma onormal_inner_self [simp]: "onormal B \<Longrightarrow> u \<in> B \<Longrightarrow> u \<bullet> u = 1"
  by (metis onormal_def norm_eq_1)

lemma onormal_inner_distinct: "onormal B \<Longrightarrow> u \<in> B \<Longrightarrow> v \<in> B \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<bullet> v = 0"
  by (auto simp: onormal_def pairwise_def orthogonal_def)

lemma onormal_inner_sums:
  assumes B: "onormal B"
  shows "(\<Sum>u\<in>B. f u *\<^sub>R u) \<bullet> (\<Sum>v\<in>B. g v *\<^sub>R v) = (\<Sum>u\<in>B. f u * g u)"
proof -
  have "(\<Sum>u\<in>B. f u *\<^sub>R u) \<bullet> (\<Sum>v\<in>B. g v *\<^sub>R v)
      = (\<Sum>v\<in>B. \<Sum>u\<in>B. f u * g v * (u \<bullet> v))"
    by (simp add: inner_sum_left inner_sum_right sum_distrib_left ac_simps)
  also have "\<dots> = (\<Sum>u\<in>B. \<Sum>v\<in>B. f u * g v * (u \<bullet> v))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>u\<in>B. \<Sum>v\<in>B. if v = u then f u * g u else 0)"
    by (intro sum.cong refl)
      (use B in \<open>auto dest: onormal_inner_distinct\<close>)
  also have "\<dots> = (\<Sum>u\<in>B. f u * g u)"
    using B by (simp add: onormal_def)
  finally show ?thesis .
qed

lemma onormal_expand:
  assumes B: "onormal B" and x: "x \<in> span B"
  shows "(\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u) = x"
proof -
  from x B obtain c where c: "x = (\<Sum>v\<in>B. c v *\<^sub>R v)"
    by (auto simp: span_finite onormal_def)
  have "u \<bullet> x = c u" if u: "u \<in> B" for u
  proof -
    have "u \<bullet> x = (\<Sum>v\<in>B. c v * (u \<bullet> v))"
      by (simp add: c inner_sum_right ac_simps)
    also have "\<dots> = (\<Sum>v\<in>B. if v = u then c u else 0)"
      by (intro sum.cong refl)
        (use B u in \<open>auto dest: onormal_inner_distinct simp: ac_simps\<close>)
    also have "\<dots> = c u"
      using B u by (simp add: onormal_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: c cong: sum.cong)
qed

lemma onormal_bessel:
  assumes B: "onormal B"
  shows "(\<Sum>u\<in>B. (u \<bullet> x)\<^sup>2) \<le> x \<bullet> x"
proof -
  define s where "s = (\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u)"
  have ss: "s \<bullet> s = (\<Sum>u\<in>B. (u \<bullet> x)\<^sup>2)"
    by (simp add: s_def onormal_inner_sums[OF B] power2_eq_square)
  have xs: "x \<bullet> s = (\<Sum>u\<in>B. (u \<bullet> x)\<^sup>2)"
    by (simp add: s_def inner_sum_right power2_eq_square inner_commute)
  have "0 \<le> (x - s) \<bullet> (x - s)"
    by simp
  also have "(x - s) \<bullet> (x - s) = x \<bullet> x - 2 * (x \<bullet> s) + s \<bullet> s"
    by (simp add: inner_diff_left inner_diff_right inner_commute)
  finally show ?thesis
    using ss xs by simp
qed

subsection \<open>Completeness relation and traces in orthonormal bases\<close>

lemma onormal_complete:
  assumes B: "onormal B" and U: "span B = UNIV"
  shows "(\<Sum>u\<in>B. outer_prod u u) = mat 1"
proof -
  have "(\<Sum>u\<in>B. outer_prod u u) *v x = mat 1 *v x" for x
  proof -
    have "(\<Sum>u\<in>B. outer_prod u u) *v x = (\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u)"
      by (simp add: matrix_vector_mult_sum)
    also have "\<dots> = x"
      by (rule onormal_expand[OF B]) (simp add: U)
    finally show ?thesis
      by simp
  qed
  then show ?thesis
    by (auto simp: matrix_eq)
qed

lemma trace_onormal_basis:
  assumes B: "onormal B" and U: "span B = UNIV"
  shows "trace A = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
proof -
  have "trace A = trace (A ** (\<Sum>u\<in>B. outer_prod u u))"
    by (simp add: onormal_complete[OF B U])
  also have "\<dots> = (\<Sum>u\<in>B. trace (A ** outer_prod u u))"
    by (simp add: matrix_mult_sum_right trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
    by (simp add: mult_outer_prod inner_commute)
  finally show ?thesis .
qed

subsection \<open>Extension of orthonormal families to orthonormal bases\<close>

lemma onormal_extension:
  assumes B: "onormal B"
  obtains C where "onormal C" "B \<subseteq> C" "span C = UNIV"
proof -
  have orthB: "pairwise orthogonal B"
    using B by (simp add: onormal_def)
  obtain U where U: "pairwise orthogonal (B \<union> U)"
    "span (B \<union> U) = span (B \<union> Basis)"
    using orthogonal_extension[OF orthB, where T = Basis] by blast
  define C where "C = (\<lambda>u. u /\<^sub>R norm u) ` ((B \<union> U) - {0})"
  have C_norm: "norm u = 1" if "u \<in> C" for u
    using that
    by (auto simp: C_def sgn_div_norm[symmetric] norm_sgn split: if_splits)
  have C_orth: "pairwise orthogonal C"
  proof (rule pairwiseI)
    fix x y assume "x \<in> C" "y \<in> C" "x \<noteq> y"
    then obtain u v where uv: "u \<in> (B \<union> U) - {0}" "v \<in> (B \<union> U) - {0}"
      "x = u /\<^sub>R norm u" "y = v /\<^sub>R norm v"
      by (auto simp: C_def)
    with \<open>x \<noteq> y\<close> have "u \<noteq> v" by auto
    with U(1) uv have "orthogonal u v"
      by (auto simp: pairwise_def)
    then show "orthogonal x y"
      by (simp add: uv orthogonal_def)
  qed
  have C_fin: "finite C"
    using C_orth C_norm
    by (intro pairwise_orthogonal_imp_finite) auto
  have BC: "B \<subseteq> C"
  proof
    fix b assume b: "b \<in> B"
    with B have "norm b = 1"
      by (simp add: onormal_def)
    with b show "b \<in> C"
      by (force simp: C_def intro: rev_image_eqI)
  qed
  have C_sub: "C \<subseteq> span (B \<union> U)"
  proof
    fix y assume "y \<in> C"
    then obtain u where u: "u \<in> (B \<union> U) - {0}" "y = u /\<^sub>R norm u"
      by (auto simp: C_def)
    then show "y \<in> span (B \<union> U)"
      by (metis DiffD1 span_base span_scale)
  qed
  have sub_C: "B \<union> U \<subseteq> span C"
  proof
    fix u assume u: "u \<in> B \<union> U"
    show "u \<in> span C"
    proof (cases "u = 0")
      case True
      then show ?thesis
        by (simp add: span_zero)
    next
      case False
      with u have "u /\<^sub>R norm u \<in> C"
        by (auto simp: C_def)
      then have "norm u *\<^sub>R (u /\<^sub>R norm u) \<in> span C"
        by (intro span_scale span_base)
      with False show ?thesis
        by simp
    qed
  qed
  have "span C = span (B \<union> U)"
    using C_sub sub_C by (simp add: span_eq)
  also have "\<dots> = span (B \<union> Basis)"
    by (fact U(2))
  also have "\<dots> = UNIV"
  proof -
    have "(UNIV :: (real^'n) set) = span Basis"
      by simp
    also have "\<dots> \<subseteq> span (B \<union> Basis)"
      by (intro span_mono) auto
    finally show ?thesis
      by auto
  qed
  finally have C_span: "span C = UNIV" .
  show thesis
    by (rule that[of C]) (use C_fin C_orth C_norm BC C_span in \<open>auto simp: onormal_def\<close>)
qed

subsection \<open>The trace lower bound (Courant--Fischer/Ky Fan argument)\<close>

lemma trace_ge_dim:
  fixes a :: "real^'n^'n"
  assumes psd: "\<And>x. 0 \<le> x \<bullet> (a *v x)"
    and S: "subspace S"
    and ray: "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
  shows "real (dim S) \<le> trace a"
proof -
  obtain B where B: "B \<subseteq> S" "pairwise orthogonal B" "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
    "independent B" "card B = dim S" "span B = S"
    using orthonormal_basis_subspace[OF S] by metis
  have onB: "onormal B"
    using B by (auto simp: onormal_def intro: pairwise_orthogonal_imp_finite)
  obtain C where C: "onormal C" "B \<subseteq> C" "span C = UNIV"
    using onormal_extension[OF onB] by blast
  have "real (dim S) = (\<Sum>u\<in>B. u \<bullet> u)"
    using B(5) onB by (simp add: onormal_def)
  also have "\<dots> \<le> (\<Sum>u\<in>B. u \<bullet> (a *v u))"
    by (intro sum_mono ray) (use B(1) in auto)
  also have "\<dots> \<le> (\<Sum>u\<in>C. u \<bullet> (a *v u))"
    using C by (intro sum_mono2 psd) (auto simp: onormal_def)
  also have "\<dots> = trace a"
    by (simp add: trace_onormal_basis[OF C(1,3)])
  finally show ?thesis .
qed

section \<open>The constraint set and the elliptic operator of Eq. (1.9)\<close>

text \<open>
  Positive semidefinite symmetric matrices; the spectral constraints of
  Eq. (1.9) are expressed via their Courant--Fischer variational
  characterizations, which for symmetric matrices are equivalent to
  \<open>\<lambda>\<^sub>(\<^sub>m\<^sub>)(a) \<ge> 1\<close> and \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(a) \<le> L\<close>, respectively.
\<close>

definition psd :: "real^'n^'n \<Rightarrow> bool" where
  "psd a \<longleftrightarrow> transpose a = a \<and> (\<forall>x. 0 \<le> x \<bullet> (a *v x))"

definition eigen_lb :: "real^'n^'n \<Rightarrow> nat \<Rightarrow> bool" where
  "eigen_lb a m \<longleftrightarrow> (\<exists>S. subspace S \<and> m \<le> dim S \<and> (\<forall>x\<in>S. x \<bullet> x \<le> x \<bullet> (a *v x)))"

definition eigen_ub :: "real^'n^'n \<Rightarrow> real \<Rightarrow> bool" where
  "eigen_ub a L \<longleftrightarrow> (\<forall>x. x \<bullet> (a *v x) \<le> L * (x \<bullet> x))"

text \<open>The feasible set of Eq. (1.9), for gradient \<open>p\<close>: \<close>

definition feasible :: "nat \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> (real^'n^'n) set" where
  "feasible k L p =
     {a. psd a \<and> a *v p = 0 \<and> eigen_lb a (CARD('n) - k) \<and> eigen_ub a L}"

text \<open>The fully nonlinear operator \<open>F(p, M)\<close> of Eq. (1.9): \<close>

definition ell_op :: "nat \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n^'n \<Rightarrow> real" where
  "ell_op k L p M = Inf ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"

subsection \<open>Feasibility: projections onto \<open>(n-k)\<close>-dimensional subspaces of \<open>p\<^sup>\<bottom>\<close>\<close>

lemma feasible_witness:
  fixes p :: "real^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  obtains a where "a \<in> feasible k L p" "trace a = real (CARD('n) - k)"
proof -
  define H where "H = {y :: real^'n. p \<bullet> y = 0}"
  have subH: "subspace H"
    by (simp add: H_def subspace_hyperplane)
  text \<open>For \<open>p = 0\<close> the \<open>hyperplane\<close> is all of \<open>\<real>\<^sup>n\<close>, so the dimension bound
    holds without the nondegeneracy assumption; only the inequality is used.\<close>
  have dimH: "CARD('n) - 1 \<le> dim H"
  proof (cases "p = 0")
    case True
    then have "H = UNIV"
      by (simp add: H_def)
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by (simp add: H_def dim_hyperplane)
  qed
  obtain B where B: "B \<subseteq> H" "pairwise orthogonal B" "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
    "independent B" "card B = dim H" "span B = H"
    using orthonormal_basis_subspace[OF subH] by metis
  have "CARD('n) - k \<le> card B"
  proof -
    have "CARD('n) - k \<le> CARD('n) - 1"
      using k(1) by (rule diff_le_mono2)
    also have "CARD('n) - 1 \<le> dim H"
      by (rule dimH)
    also have "dim H = card B"
      by (rule B(5)[symmetric])
    finally show ?thesis .
  qed
  then obtain T where T: "T \<subseteq> B" "card T = CARD('n) - k" "finite T"
    by (rule obtain_subset_with_card_n)
  have onT: "onormal T"
    using T B by (auto simp: onormal_def elim: pairwise_subset)
  define a where "a = (\<Sum>u\<in>T. outer_prod u u)"
  have amv: "a *v x = (\<Sum>u\<in>T. (u \<bullet> x) *\<^sub>R u)" for x
    by (simp add: a_def matrix_vector_mult_sum)
  have quad: "x \<bullet> (a *v x) = (\<Sum>u\<in>T. (u \<bullet> x)\<^sup>2)" for x
    by (simp add: amv inner_sum_right power2_eq_square inner_commute)
  have psd_a: "psd a"
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose a = a"
      by (simp add: a_def transpose_matrix_sum)
  next
    show "0 \<le> x \<bullet> (a *v x)" for x
      by (simp add: quad sum_nonneg)
  qed
  have ap: "a *v p = 0"
  proof -
    have "u \<bullet> p = 0" if "u \<in> T" for u
      using that T(1) B(1) by (auto simp: H_def inner_commute)
    then show ?thesis
      by (simp add: amv)
  qed
  have lb_a: "eigen_lb a (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ "span T"] conjI ballI)
    show "subspace (span T)" by (rule subspace_span)
    have "independent T"
      using onT by (intro pairwise_orthogonal_independent) (auto simp: onormal_def)
    then have "dim (span T) = card T"
      by (simp add: dim_eq_card_independent)
    then show "CARD('n) - k \<le> dim (span T)"
      by (simp add: T(2))
    fix x assume x: "x \<in> span T"
    have "x \<bullet> x = (\<Sum>u\<in>T. (u \<bullet> x) *\<^sub>R u) \<bullet> (\<Sum>u\<in>T. (u \<bullet> x) *\<^sub>R u)"
      by (simp add: onormal_expand[OF onT x])
    also have "\<dots> = (\<Sum>u\<in>T. (u \<bullet> x)\<^sup>2)"
      by (simp add: onormal_inner_sums[OF onT] power2_eq_square)
    finally show "x \<bullet> x \<le> x \<bullet> (a *v x)"
      by (simp add: quad)
  qed
  have ub_a: "eigen_ub a L"
    unfolding eigen_ub_def
  proof (intro allI)
    fix x :: "real^'n"
    have "x \<bullet> (a *v x) \<le> x \<bullet> x"
      by (simp add: quad onormal_bessel[OF onT])
    also have "\<dots> \<le> L * (x \<bullet> x)"
      using L by (simp add: mult_right_mono
          [of 1 L "x \<bullet> x", simplified])
    finally show "x \<bullet> (a *v x) \<le> L * (x \<bullet> x)" .
  qed
  have tr_a: "trace a = real (CARD('n) - k)"
    using onT by (simp add: a_def trace_matrix_sum T(2))
  show thesis
    by (rule that[of a])
      (use psd_a ap lb_a ub_a tr_a in \<open>auto simp: feasible_def\<close>)
qed

subsection \<open>Main theorem: verification of Example 3.1 (Eq. 3.9)\<close>

text \<open>
  For the ball \<open>K = cball 0 r\<close> the candidate value function is
  \<open>v x = max (r\<^sup>2 - \<bar>x\<bar>\<^sup>2) 0 / (n - k)\<close>, whose gradient at \<open>x\<close> is
  \<open>- (2/(n-k)) *\<^sub>R x\<close> and whose Hessian is the constant matrix
  \<open>- (2/(n-k)) *\<^sub>R mat 1\<close>.  We show \<open>F(\<nabla>v x, \<nabla>\<^sup>2 v x) = 1\<close> for all
  interior points \<open>x \<noteq> 0\<close>.
\<close>

lemma neg_half_trace_ball_op:
  fixes a :: "real^'n^'n"
  assumes c_pos: "0 < c"
  shows "- trace ((- (2 / c) *\<^sub>R mat 1) ** a) / 2 = trace a / c"
proof -
  have "((- (2 / c) *\<^sub>R mat 1) ** a) $ i $ i = - (2 / c) * a $ i $ i" for i
    by (simp add: matrix_matrix_mult_def mat_def if_distrib if_distribR
        cong: if_cong)
  then have "trace ((- (2 / c) *\<^sub>R mat 1) ** a) = - ((2 / c) * trace a)"
    by (simp add: trace_def sum_distrib_left sum_negf)
  then show ?thesis
    using c_pos by (simp add: field_simps)
qed

lemma feasible_trace_lb:
  fixes a :: "real^'n^'n"
  assumes a: "a \<in> feasible k L p"
  shows "real (CARD('n) - k) \<le> trace a"
proof -
  from a obtain S where S: "subspace S" "CARD('n) - k \<le> dim S"
    "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
    by (auto simp: feasible_def eigen_lb_def)
  have "real (CARD('n) - k) \<le> real (dim S)"
    using S(2) by simp
  also have "\<dots> \<le> trace a"
    using a S by (intro trace_ge_dim) (auto simp: feasible_def psd_def)
  finally show ?thesis .
qed

lemma feasible_value_ge_one:
  fixes a :: "real^'n^'n"
  assumes k: "k < CARD('n)" and a: "a \<in> feasible k L p"
  shows "1 \<le> - trace ((- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) ** a) / 2"
proof -
  have c_pos: "0 < real (CARD('n) - k)"
    using k by simp
  from feasible_trace_lb[OF a] c_pos have "1 \<le> trace a / real (CARD('n) - k)"
    by (simp add: pos_le_divide_eq)
  then show ?thesis
    unfolding neg_half_trace_ball_op[OF c_pos] .
qed

theorem ell_op_eval:
  fixes p :: "real^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op k L p (- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) = 1"
proof -
  define c where "c = real (CARD('n) - k)"
  have c_pos: "0 < c"
    using k by (simp add: c_def)
  obtain a0 where a0: "a0 \<in> feasible k L p" "trace a0 = c"
    unfolding c_def using k L by (rule feasible_witness)
  have a0_val: "- trace ((- (2 / c) *\<^sub>R mat 1) ** a0) / 2 = 1"
    unfolding neg_half_trace_ball_op[OF c_pos] using c_pos by (simp add: a0(2))
  have "ell_op k L p (- (2 / c) *\<^sub>R mat 1) = 1"
    unfolding ell_op_def
    by (rule cInf_eq_minimum)
      (use a0 a0_val feasible_value_ge_one[OF k(2)] c_def in \<open>force+\<close>)
  then show ?thesis
    by (simp add: c_def)
qed

subsection \<open>The candidate value function and its derivatives\<close>

definition ball_v :: "real \<Rightarrow> nat \<Rightarrow> real^'n \<Rightarrow> real" where
  "ball_v r k x = max (r\<^sup>2 - x \<bullet> x) 0 / real (CARD('n) - k)"

lemma ball_v_nonneg: "0 \<le> ball_v r k x"
  by (simp add: ball_v_def)

lemma ball_v_boundary: "norm x = r \<Longrightarrow> ball_v r k x = 0"
  by (simp add: ball_v_def dot_square_norm)

lemma ball_v_gradient:
  fixes x :: "real^'n"
  assumes x: "norm x < r" and k: "k < CARD('n)"
  shows "((ball_v r k) has_derivative
           (\<lambda>h. (- (2 / real (CARD('n) - k)) *\<^sub>R x) \<bullet> h)) (at x)"
proof -
  define c where "c = real (CARD('n) - k)"
  have c_pos: "0 < c"
    using k by (simp add: c_def)
  have inner_deriv: "((\<lambda>y. (r\<^sup>2 - y \<bullet> y) / c) has_derivative
      (\<lambda>h. (- (2 / c) *\<^sub>R x) \<bullet> h)) (at x)"
    using c_pos
    by (auto intro!: derivative_eq_intros
        simp: inner_commute divide_simps algebra_simps)
  have eq: "(r\<^sup>2 - y \<bullet> y) / c = ball_v r k y" if "y \<in> ball (0::real^'n) r" for y
  proof -
    have "norm y < r"
      using that by simp
    then have "(norm y)\<^sup>2 < r\<^sup>2"
      by (intro power_strict_mono) simp_all
    then have "y \<bullet> y < r\<^sup>2"
      by (simp add: dot_square_norm)
    then show ?thesis
      by (simp add: ball_v_def c_def max_def)
  qed
  show ?thesis
    unfolding c_def[symmetric]
  proof (rule has_derivative_transform_within_open)
    show "((\<lambda>y. (r\<^sup>2 - y \<bullet> y) / c) has_derivative
        (\<lambda>h. (- (2 / c) *\<^sub>R x) \<bullet> h)) (at x)"
      by (fact inner_deriv)
    show "open (ball (0::real^'n) r)"
      by simp
    show "x \<in> ball (0::real^'n) r"
      using x by (simp add: dist_norm)
    show "\<And>y. y \<in> ball (0::real^'n) r \<Longrightarrow> (r\<^sup>2 - y \<bullet> y) / c = ball_v r k y"
      by (rule eq)
  qed
qed

lemma ball_v_hessian:
  fixes x :: "real^'n"
  shows "((\<lambda>x :: real^'n. - (2 / real (CARD('n) - k)) *\<^sub>R x) has_derivative
           (\<lambda>h. (- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) *v h)) (at x)"
proof -
  have "((\<lambda>x :: real^'n. - (2 / real (CARD('n) - k)) *\<^sub>R x) has_derivative
      (\<lambda>h. - (2 / real (CARD('n) - k)) *\<^sub>R h)) (at x)"
    by (auto intro!: derivative_eq_intros)
  moreover have "(\<lambda>h :: real^'n. - (2 / real (CARD('n) - k)) *\<^sub>R h)
      = (\<lambda>h. (- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) *v h)"
    by (simp add: fun_eq_iff neg_matrix_vector scaleR_matrix_vector)
  ultimately show ?thesis
    by simp
qed

text \<open>
  Example 3.1: at every interior point of the ball --- including the centre,
  where the gradient vanishes --- the gradient and Hessian of \<open>v\<close> satisfy the
  PDE \<open>F(\<nabla>v, \<nabla>\<^sup>2 v) = 1\<close> of Theorem 1.1.  At \<open>p = 0\<close> the constraint \<open>a p = 0\<close>
  of Eq. (1.9) is vacuous, so the feasible set is larger, but the value of the
  infimum is unchanged: the trace bound \<open>tr a \<ge> n - k\<close> holds for every
  feasible \<open>a\<close> and is attained by a rank-\<open>(n-k)\<close> projection, which is feasible
  for \<open>p = 0\<close> as well.
\<close>

corollary ball_solves_pde:
  fixes x :: "real^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op k L (- (2 / real (CARD('n) - k)) *\<^sub>R x)
                    (- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) = 1"
  by (rule ell_op_eval[OF k L])

section \<open>The spectral theorem for real symmetric matrices\<close>

text \<open>
  Needed for the degenerate ellipticity of \<open>F\<close> (monotonicity in the Hessian
  argument w.r.t. the Loewner order), which in turn is the key structural
  property behind the viscosity-solution formulation of Theorem 1.1.  We prove
  the spectral theorem by the variational argument (Rayleigh-quotient
  maximization on invariant subspaces); no derivatives are needed.
\<close>

lemma inner_transpose_matrix:
  fixes A :: "real^'m^'n" and x :: "real^'n" and y :: "real^'m"
  shows "x \<bullet> (A *v y) = (transpose A *v x) \<bullet> y"
proof -
  have "x \<bullet> (A *v y) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. x $ i * (A $ i $ j * y $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. x $ i * (A $ i $ j * y $ j))"
    by (rule sum.swap)
  also have "\<dots> = (transpose A *v x) \<bullet> y"
    by (simp add: inner_vec_def matrix_vector_mult_def transpose_def
        sum_distrib_left sum_distrib_right ac_simps)
  finally show ?thesis .
qed

lemma sym_inner_swap:
  fixes a :: "real^'n^'n"
  assumes "transpose a = a"
  shows "x \<bullet> (a *v y) = y \<bullet> (a *v x)"
proof -
  have "x \<bullet> (a *v y) = (transpose a *v x) \<bullet> y"
    by (rule inner_transpose_matrix)
  also have "\<dots> = (a *v x) \<bullet> y"
    by (simp add: assms)
  also have "\<dots> = y \<bullet> (a *v x)"
    by (rule inner_commute)
  finally show ?thesis .
qed

text \<open>A linear coefficient dominated by a quadratic must vanish:\<close>

lemma linear_coeff_zero:
  fixes c1 c2 :: real
  assumes le: "\<And>t :: real. c1 * t + c2 * t\<^sup>2 \<le> 0"
  shows "c1 = 0"
proof (rule ccontr)
  assume c1: "c1 \<noteq> 0"
  define e where "e = \<bar>c1\<bar> / (2 * \<bar>c2\<bar> + 2)"
  have denom_pos: "0 < 2 * \<bar>c2\<bar> + 2"
    by simp
  have e_pos: "0 < e"
    using c1 denom_pos by (simp add: e_def)
  have key: "(2 * \<bar>c2\<bar> + 2) * e = \<bar>c1\<bar>"
    using denom_pos by (simp add: e_def)
  define t where "t = (if 0 < c1 then e else - e)"
  have c1t: "c1 * t = \<bar>c1\<bar> * e"
    using c1 by (auto simp: t_def abs_if)
  have t2: "t\<^sup>2 = e\<^sup>2"
    by (auto simp: t_def)
  have c2bound: "- (\<bar>c2\<bar> * e\<^sup>2) \<le> c2 * t\<^sup>2"
  proof -
    have "- \<bar>c2\<bar> \<le> c2"
      by simp
    then have "- \<bar>c2\<bar> * e\<^sup>2 \<le> c2 * e\<^sup>2"
      by (rule mult_right_mono) simp
    then show ?thesis
      by (simp add: t2)
  qed
  have eb: "\<bar>c2\<bar> * e \<le> \<bar>c1\<bar> / 2"
  proof -
    have "2 * (\<bar>c2\<bar> * e) \<le> (2 * \<bar>c2\<bar> + 2) * e"
      using e_pos by (simp add: algebra_simps)
    with key show ?thesis
      by simp
  qed
  have e2: "\<bar>c2\<bar> * e\<^sup>2 \<le> (\<bar>c1\<bar> / 2) * e"
  proof -
    have "\<bar>c2\<bar> * e\<^sup>2 = (\<bar>c2\<bar> * e) * e"
      by (simp add: power2_eq_square ac_simps)
    also have "\<dots> \<le> (\<bar>c1\<bar> / 2) * e"
      using eb e_pos by (intro mult_right_mono) auto
    finally show ?thesis .
  qed
  have lower: "\<bar>c1\<bar> * e - (\<bar>c1\<bar> / 2) * e \<le> c1 * t + c2 * t\<^sup>2"
    using c1t c2bound e2 by linarith
  have "\<bar>c1\<bar> * e - (\<bar>c1\<bar> / 2) * e = (\<bar>c1\<bar> / 2) * e"
    by (simp add: algebra_simps)
  moreover have "0 < (\<bar>c1\<bar> / 2) * e"
    using c1 e_pos by (intro mult_pos_pos) auto
  ultimately show False
    using le[of t] lower by linarith
qed

subsection \<open>Rayleigh-quotient maximizers are eigenvectors\<close>

lemma rayleigh_maximizer:
  fixes a :: "real^'n^'n"
  assumes S: "subspace S" and ne: "S \<noteq> {0}"
  obtains u where "u \<in> S" "norm u = 1"
    "\<And>v. v \<in> S \<Longrightarrow> norm v = 1 \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
proof -
  define K where "K = S \<inter> sphere 0 1"
  have cptK: "compact K"
    unfolding K_def
    by (metis closed_subspace[OF S] compact_sphere compact_Int_closed
        inf_commute)
  have Kne: "K \<noteq> {}"
  proof -
    obtain z where z: "z \<in> S" "z \<noteq> 0"
      using ne subspace_0[OF S] by blast
    have "z /\<^sub>R norm z \<in> S"
      using z(1) S by (simp add: subspace_scale)
    moreover have "norm (z /\<^sub>R norm z) = 1"
      using z(2) by (simp add: sgn_div_norm[symmetric] norm_sgn)
    ultimately show ?thesis
      by (auto simp: K_def)
  qed
  have cont: "continuous_on K (\<lambda>x. x \<bullet> (a *v x))"
    by (intro continuous_intros linear_continuous_on)
      (simp add: linear_linear[symmetric])
  obtain u where u: "u \<in> K" "\<And>v. v \<in> K \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using continuous_attains_sup[OF cptK Kne cont] by blast
  show thesis
    by (rule that[of u]) (use u in \<open>auto simp: K_def\<close>)
qed

lemma rayleigh_maximizer_eigenvector:
  fixes a :: "real^'n^'n"
  assumes sym: "transpose a = a"
    and S: "subspace S"
    and inv: "\<And>x. x \<in> S \<Longrightarrow> a *v x \<in> S"
    and u: "u \<in> S" "norm u = 1"
    and max: "\<And>v. v \<in> S \<Longrightarrow> norm v = 1 \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
  shows "a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
proof -
  define l where "l = u \<bullet> (a *v u)"
  have uu: "u \<bullet> u = 1"
    using u(2) by (simp add: norm_eq_1)
  have orth_zero: "v \<bullet> (a *v u) = 0"
    if v: "v \<in> S" "u \<bullet> v = 0" "norm v = 1" for v
  proof -
    have vv: "v \<bullet> v = 1"
      using v(3) by (simp add: norm_eq_1)
    have quad: "(u + t *\<^sub>R v) \<bullet> (a *v (u + t *\<^sub>R v))
        = l + 2 * t * (v \<bullet> (a *v u)) + t\<^sup>2 * (v \<bullet> (a *v v))" for t
    proof -
      have "a *v (u + t *\<^sub>R v) = a *v u + t *\<^sub>R (a *v v)"
        by (simp add: matrix_vector_right_distrib matrix_vector_mult_scaleR)
      then have "(u + t *\<^sub>R v) \<bullet> (a *v (u + t *\<^sub>R v))
          = u \<bullet> (a *v u) + t * (u \<bullet> (a *v v)) + t * (v \<bullet> (a *v u))
            + t * t * (v \<bullet> (a *v v))"
        by (simp add: algebra_simps)
      also have "u \<bullet> (a *v v) = v \<bullet> (a *v u)"
        by (rule sym_inner_swap[OF sym])
      finally show ?thesis
        by (simp add: l_def power2_eq_square algebra_simps)
    qed
    have normsq: "(u + t *\<^sub>R v) \<bullet> (u + t *\<^sub>R v) = 1 + t\<^sup>2" for t
      using uu vv v(2)
      by (simp add: inner_commute
          power2_eq_square algebra_simps)
    have ineq: "(u + t *\<^sub>R v) \<bullet> (a *v (u + t *\<^sub>R v)) \<le> l * (1 + t\<^sup>2)" for t
    proof -
      define w where "w = u + t *\<^sub>R v"
      have wS: "w \<in> S"
        using u(1) v(1) S by (simp add: w_def subspace_add subspace_scale)
      have wnz: "w \<noteq> 0"
      proof
        assume "w = 0"
        then have "(u + t *\<^sub>R v) \<bullet> (u + t *\<^sub>R v) = 0"
          by (simp add: w_def)
        with normsq[of t] have "1 + t\<^sup>2 = 0"
          by simp
        then show False
          using zero_le_power2[of t] by linarith
      qed
      have wnorm: "(norm w)\<^sup>2 = 1 + t\<^sup>2"
        using normsq[of t] by (simp add: w_def dot_square_norm[symmetric])
      have wpos: "0 < norm w"
        using wnz by simp
      have unit: "norm (w /\<^sub>R norm w) = 1"
        using wnz by (simp add: sgn_div_norm[symmetric] norm_sgn)
      have memS: "w /\<^sub>R norm w \<in> S"
        using wS S by (simp add: subspace_scale)
      have "(w /\<^sub>R norm w) \<bullet> (a *v (w /\<^sub>R norm w)) \<le> l"
        unfolding l_def by (rule max[OF memS unit])
      then have "(inverse (norm w))\<^sup>2 * (w \<bullet> (a *v w)) \<le> l"
        by (simp add: power2_eq_square algebra_simps)
      then have "w \<bullet> (a *v w) \<le> l * (norm w)\<^sup>2"
        using wpos
        by (simp add: power2_eq_square field_simps)
      then show ?thesis
        by (simp add: w_def wnorm[symmetric])
    qed
    have "2 * (v \<bullet> (a *v u)) * t + (v \<bullet> (a *v v) - l) * t\<^sup>2 \<le> 0" for t
      using quad[of t] ineq[of t] by (simp add: algebra_simps)
    from linear_coeff_zero[OF this] show ?thesis
      by simp
  qed
  define w where "w = a *v u - l *\<^sub>R u"
  have wS: "w \<in> S"
    using inv[OF u(1)] u(1) S by (simp add: w_def subspace_diff subspace_scale)
  have uw: "u \<bullet> w = 0"
    by (simp add: w_def inner_diff_right l_def uu)
  have "w = 0"
  proof (rule ccontr)
    assume wnz: "w \<noteq> 0"
    have memS: "w /\<^sub>R norm w \<in> S"
      using wS S by (simp add: subspace_scale)
    have unit: "norm (w /\<^sub>R norm w) = 1"
      using wnz by (simp add: sgn_div_norm[symmetric] norm_sgn)
    have orth: "u \<bullet> (w /\<^sub>R norm w) = 0"
      using uw by simp
    from orth_zero[OF memS orth unit]
    have "(w /\<^sub>R norm w) \<bullet> (a *v u) = 0" .
    then have "w \<bullet> (a *v u) = 0"
      using wnz by simp
    then have au_w: "(a *v u) \<bullet> w = 0"
      by (simp add: inner_commute)
    have "w \<bullet> w = (a *v u) \<bullet> w - (l *\<^sub>R u) \<bullet> w"
      by (subst (1) w_def) (rule inner_diff_left)
    also have "\<dots> = 0"
      using au_w uw by simp
    finally have "w \<bullet> w = 0" .
    with wnz show False
      by simp
  qed
  then show ?thesis
    by (simp add: w_def l_def)
qed

subsection \<open>Orthonormal eigenbases of invariant subspaces\<close>

lemma invariant_subspace_eigenbasis_ex:
  fixes a :: "real^'n^'n"
  assumes sym: "transpose a = a"
  shows "subspace S \<Longrightarrow> (\<forall>x\<in>S. a *v x \<in> S) \<Longrightarrow>
    \<exists>B. onormal B \<and> B \<subseteq> S \<and> span B = S \<and>
        (\<forall>u\<in>B. a *v u = (u \<bullet> (a *v u)) *\<^sub>R u)"
proof (induction "dim S" arbitrary: S rule: less_induct)
  case (less S)
  show ?case
  proof (cases "S = {0}")
    case True
    then show ?thesis
      by (intro exI[of _ "{}"]) (auto simp: onormal_def pairwise_def)
  next
    case False
    obtain u where u: "u \<in> S" "norm u = 1"
      and umax: "\<And>v. v \<in> S \<Longrightarrow> norm v = 1 \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
      using rayleigh_maximizer[OF less.prems(1) False] by metis
    have uu: "u \<bullet> u = 1"
      using u(2) by (simp add: norm_eq_1)
    have eig_u: "a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
      by (rule rayleigh_maximizer_eigenvector[OF sym less.prems(1) _ u umax])
        (use less.prems(2) in blast)
    define S' where "S' = {x \<in> S. u \<bullet> x = 0}"
    have S'_eq: "S' = S \<inter> {x. u \<bullet> x = 0}"
      by (auto simp: S'_def)
    have subS': "subspace S'"
      unfolding S'_eq
      by (intro subspace_inter less.prems(1) subspace_hyperplane)
    have invS': "\<forall>x\<in>S'. a *v x \<in> S'"
    proof
      fix x assume "x \<in> S'"
      then have xS: "x \<in> S" and xu: "u \<bullet> x = 0"
        by (auto simp: S'_def)
      have "a *v x \<in> S"
        using less.prems(2) xS by blast
      moreover have "u \<bullet> (a *v x) = 0"
      proof -
        have "u \<bullet> (a *v x) = x \<bullet> (a *v u)"
          by (rule sym_inner_swap[OF sym])
        also have "\<dots> = (u \<bullet> (a *v u)) * (x \<bullet> u)"
          by (subst (1) eig_u) simp
        also have "\<dots> = 0"
          using xu by (simp add: inner_commute)
        finally show ?thesis .
      qed
      ultimately show "a *v x \<in> S'"
        by (simp add: S'_def)
    qed
    have uS': "u \<notin> S'"
      using uu by (auto simp: S'_def)
    have dimlt: "dim S' < dim S"
    proof -
      have sub: "S' \<subseteq> S"
        by (auto simp: S'_def)
      then have le: "dim S' \<le> dim S"
        by (rule dim_subset)
      have "S' \<noteq> S"
        using uS' u(1) by auto
      then have "dim S' \<noteq> dim S"
        using subS' less.prems(1) sub
        by (metis subspace_dim_equal order_refl)
      with le show ?thesis
        by simp
    qed
    from less.hyps[OF dimlt subS' invS'] obtain B' where
      B': "onormal B'" "B' \<subseteq> S'" "span B' = S'"
        "\<forall>w\<in>B'. a *v w = (w \<bullet> (a *v w)) *\<^sub>R w"
      by blast
    define B where "B = insert u B'"
    have BS: "B \<subseteq> S"
      using u(1) B'(2) by (auto simp: B_def S'_def)
    have onB: "onormal B"
    proof -
      have "orthogonal u b" if "b \<in> B'" for b
        using B'(2) that by (auto simp: S'_def orthogonal_def)
      then show ?thesis
        using B'(1) u(2)
        by (auto simp: onormal_def B_def pairwise_insert orthogonal_commute)
    qed
    have spanB: "span B = S"
    proof -
      have "span B \<subseteq> S"
        using BS less.prems(1) by (simp add: span_minimal)
      moreover have "S \<subseteq> span B"
      proof
        fix x assume xS: "x \<in> S"
        have "u \<bullet> (x - (u \<bullet> x) *\<^sub>R u) = 0"
          by (simp add: inner_diff_right uu)
        moreover have "x - (u \<bullet> x) *\<^sub>R u \<in> S"
          using xS u(1) less.prems(1)
          by (simp add: subspace_diff subspace_scale)
        ultimately have "x - (u \<bullet> x) *\<^sub>R u \<in> span B'"
          by (simp add: B'(3) S'_def)
        then show "x \<in> span B"
          unfolding B_def
          by (metis span_breakdown_eq)
      qed
      ultimately show ?thesis
        by blast
    qed
    have eigB: "\<forall>w\<in>B. a *v w = (w \<bullet> (a *v w)) *\<^sub>R w"
      using B'(4) eig_u by (auto simp: B_def)
    show ?thesis
      using onB BS spanB eigB by blast
  qed
qed

theorem symmetric_eigenbasis:
  fixes a :: "real^'n^'n"
  assumes "transpose a = a"
  obtains B where "onormal B" "span B = UNIV"
    "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  using invariant_subspace_eigenbasis_ex[OF assms subspace_UNIV] by auto

subsection \<open>Positive semidefinite matrices and degenerate ellipticity\<close>

lemma trace_mult_psd_nonneg:
  fixes a b :: "real^'n^'n"
  assumes a: "psd a" and b: "psd b"
  shows "0 \<le> trace (a ** b)"
proof -
  from a have syma: "transpose a = a" and posa: "\<And>x. 0 \<le> x \<bullet> (a *v x)"
    by (auto simp: psd_def)
  from b have posb: "\<And>x. 0 \<le> x \<bullet> (b *v x)"
    by (auto simp: psd_def)
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF syma] by metis
  have "trace (a ** b) = (\<Sum>u\<in>B. u \<bullet> ((a ** b) *v u))"
    by (rule trace_onormal_basis[OF B])
  moreover have "u \<bullet> ((a ** b) *v u)
      = (u \<bullet> (a *v u)) * (u \<bullet> (b *v u))" if uB: "u \<in> B" for u
  proof -
    have "u \<bullet> ((a ** b) *v u) = u \<bullet> (a *v (b *v u))"
      by (simp add: matrix_vector_mul_assoc)
    also have "\<dots> = (b *v u) \<bullet> (a *v u)"
      by (rule sym_inner_swap[OF syma])
    also have "\<dots> = (b *v u) \<bullet> ((u \<bullet> (a *v u)) *\<^sub>R u)"
      by (subst (1) eig[OF uB]) simp
    also have "\<dots> = (u \<bullet> (a *v u)) * (u \<bullet> (b *v u))"
      by (simp add: inner_commute)
    finally show ?thesis .
  qed
  moreover have "0 \<le> (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (b *v u)))"
    by (intro sum_nonneg mult_nonneg_nonneg posa posb)
  ultimately show ?thesis
    by simp
qed

lemma matrix_add_rdistrib: "(A + B) ** C = A ** C + B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum.distrib
      algebra_simps)

text \<open>
  Degenerate ellipticity of the operator \<open>F\<close> of Eq. (1.9): increasing the
  Hessian argument in the Loewner order decreases every value in the defining
  infimum.
\<close>

lemma ell_op_pointwise_elliptic:
  fixes M Q a :: "real^'n^'n"
  assumes Q: "psd Q" and a: "a \<in> feasible k L p"
  shows "- trace ((M + Q) ** a) / 2 \<le> - trace (M ** a) / 2"
proof -
  have "trace ((M + Q) ** a) = trace (M ** a) + trace (Q ** a)"
    by (simp add: matrix_add_rdistrib trace_add)
  moreover have "0 \<le> trace (Q ** a)"
    using Q a by (intro trace_mult_psd_nonneg) (auto simp: feasible_def)
  ultimately show ?thesis
    by simp
qed

section \<open>Viscosity solutions of \<open>F(Du, D\<^sup>2u) = 1\<close> (Theorem 1.1, PDE side)\<close>

text \<open>
  The AFP contains no viscosity-solution theory, so we formalize the standard
  Crandall--Ishii--Lions test-function definitions for the equation
  \<open>F(Du, D\<^sup>2u) = 1\<close> directly.  A test function at \<open>x\<close> is represented by its
  gradient field \<open>g\<close> on a neighbourhood of \<open>x\<close> and its (symmetric) Hessian
  matrix \<open>H\<close> at \<open>x\<close>.
\<close>

subsection \<open>Bounds on the feasible set\<close>

lemma feasible_entry_bound:
  fixes a :: "real^'n^'n"
  assumes a: "a \<in> feasible k L p"
  shows "\<bar>a $ i $ j\<bar> \<le> L"
proof -
  from a have sym: "transpose a = a" and pos: "\<And>x. 0 \<le> x \<bullet> (a *v x)"
    and ub: "\<And>x. x \<bullet> (a *v x) \<le> L * (x \<bullet> x)"
    by (auto simp: feasible_def psd_def eigen_ub_def)
  have av_axis: "(a *v axis m 1) $ l = a $ l $ m" for l m
    by (simp add: matrix_vector_mult_def axis_def if_distrib if_distribR
        cong: if_cong)
  have quad_entry: "(axis l 1) \<bullet> (a *v axis m 1) = a $ l $ m" for l m
    by (simp add: inner_axis' av_axis)
  have expand: "(y + z) \<bullet> (a *v (y + z))
      = y \<bullet> (a *v y) + 2 * (y \<bullet> (a *v z)) + z \<bullet> (a *v z)" for y z
    by (simp add:
        sym_inner_swap[OF sym] algebra_simps)
  have expand2: "(y - z) \<bullet> (a *v (y - z))
      = y \<bullet> (a *v y) - 2 * (y \<bullet> (a *v z)) + z \<bullet> (a *v z)" for y z
    by (simp add:
        sym_inner_swap[OF sym] algebra_simps)
  show ?thesis
  proof (cases "i = j")
    case True
    have "0 \<le> a $ i $ i"
      using pos[of "axis i 1"] by (simp add: quad_entry)
    moreover have "a $ i $ i \<le> L"
      using ub[of "axis i 1"] by (simp add: quad_entry inner_axis_axis)
    ultimately show ?thesis
      using True by simp
  next
    case False
    have nn: "(axis i 1 :: real^'n) \<bullet> axis j 1 = 0"
      using False by (simp add: inner_axis_axis)
    have nsq: "(axis i 1 + axis j 1) \<bullet> ((axis i 1 :: real^'n) + axis j 1) = 2"
      "(axis i 1 - axis j 1) \<bullet> ((axis i 1 :: real^'n) - axis j 1) = 2"
      using False
      by (auto simp: inner_add_left inner_add_right inner_diff_left
          inner_diff_right inner_axis_axis)
    have plus0: "0 \<le> a $ i $ i + 2 * a $ i $ j + a $ j $ j"
      using pos[of "axis i 1 + axis j 1"] by (simp add: expand quad_entry)
    have plusL: "a $ i $ i + 2 * a $ i $ j + a $ j $ j \<le> 2 * L"
      using ub[of "axis i 1 + axis j 1"] by (simp add: expand quad_entry nsq)
    have minus0: "0 \<le> a $ i $ i - 2 * a $ i $ j + a $ j $ j"
      using pos[of "axis i 1 - axis j 1"] by (simp add: expand2 quad_entry)
    have minusL: "a $ i $ i - 2 * a $ i $ j + a $ j $ j \<le> 2 * L"
      using ub[of "axis i 1 - axis j 1"] by (simp add: expand2 quad_entry nsq)
    have dii: "0 \<le> a $ i $ i" and djj: "0 \<le> a $ j $ j"
      using pos[of "axis i 1"] pos[of "axis j 1"] by (simp_all add: quad_entry)
    show ?thesis
      using plus0 plusL minus0 minusL dii djj by linarith
  qed
qed

lemma ell_op_bdd_below:
  fixes M :: "real^'n^'n"
  shows "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
proof (rule bdd_belowI[of _ "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * L) / 2"])
  fix v assume "v \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  then obtain a where a: "a \<in> feasible k L p" and v: "v = - trace (M ** a) / 2"
    by auto
  have tr: "trace (M ** a) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * a $ j $ i)"
    by (simp add: trace_def matrix_matrix_mult_def)
  have "trace (M ** a) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j * a $ j $ i\<bar>)"
    unfolding tr by (intro sum_mono order_trans[OF _ sum_abs]) auto
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * L)"
    by (intro sum_mono)
      (simp add: abs_mult mult_left_mono feasible_entry_bound[OF a])
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * L"
    by (simp add: sum_distrib_right)
  finally show "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * L) / 2 \<le> v"
    by (simp add: v)
qed

lemma feasible_nonempty:
  fixes p :: "real^'n"
  assumes "1 \<le> k" "k < CARD('n)" "1 \<le> L"
  shows "feasible k L p \<noteq> {}"
  using feasible_witness[OF assms] by blast

subsection \<open>Perturbation bounds for the operator\<close>

lemma ell_op_le_one_of_psd_diff:
  fixes p :: "real^'n" and H :: "real^'n^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and Q: "psd (H - (- (2 / real (CARD('n) - k)) *\<^sub>R mat 1))"
  shows "ell_op k L p H \<le> 1"
proof -
  define c where "c = real (CARD('n) - k)"
  have c_pos: "0 < c"
    using k by (simp add: c_def)
  obtain a0 where a0: "a0 \<in> feasible k L p" "trace a0 = c"
    unfolding c_def using k L by (rule feasible_witness)
  have Qc: "psd (H - (- (2 / c) *\<^sub>R mat 1))"
    using Q by (simp add: c_def)
  have "- trace ((- (2 / c) *\<^sub>R mat 1 + (H - (- (2 / c) *\<^sub>R mat 1))) ** a0) / 2
      \<le> - trace ((- (2 / c) *\<^sub>R mat 1) ** a0) / 2"
    by (rule ell_op_pointwise_elliptic[OF Qc a0(1)])
  moreover have "- (2 / c) *\<^sub>R mat 1 + (H - (- (2 / c) *\<^sub>R mat 1)) = H"
    by simp
  ultimately have le1: "- trace (H ** a0) / 2 \<le> - trace ((- (2 / c) *\<^sub>R mat 1) ** a0) / 2"
    by simp
  have "- trace ((- (2 / c) *\<^sub>R mat 1) ** a0) / 2 = 1"
    unfolding neg_half_trace_ball_op[OF c_pos] using c_pos by (simp add: a0(2))
  with le1 have le1': "- trace (H ** a0) / 2 \<le> 1"
    by simp
  have "ell_op k L p H \<le> - trace (H ** a0) / 2"
    unfolding ell_op_def
    by (intro cInf_lower imageI a0(1) ell_op_bdd_below)
  with le1' show ?thesis
    by simp
qed

lemma ell_op_ge_one_of_psd_diff:
  fixes p :: "real^'n" and H :: "real^'n^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and Q: "psd ((- (2 / real (CARD('n) - k)) *\<^sub>R mat 1) - H)"
  shows "1 \<le> ell_op k L p H"
proof -
  define c where "c = real (CARD('n) - k)"
  have c_pos: "0 < c"
    using k by (simp add: c_def)
  have Qc: "psd ((- (2 / c) *\<^sub>R mat 1) - H)"
    using Q by (simp add: c_def)
  have per: "1 \<le> - trace (H ** a) / 2" if a: "a \<in> feasible k L p" for a
  proof -
    have "- trace ((H + ((- (2 / c) *\<^sub>R mat 1) - H)) ** a) / 2
        \<le> - trace (H ** a) / 2"
      by (rule ell_op_pointwise_elliptic[OF Qc a])
    moreover have "H + ((- (2 / c) *\<^sub>R mat 1) - H) = - (2 / c) *\<^sub>R mat 1"
      by simp
    ultimately have "- trace ((- (2 / c) *\<^sub>R mat 1) ** a) / 2 \<le> - trace (H ** a) / 2"
      by simp
    moreover have "1 \<le> - trace ((- (2 / c) *\<^sub>R mat 1) ** a) / 2"
      using feasible_value_ge_one[OF k(2) a] by (simp add: c_def)
    ultimately show ?thesis
      by simp
  qed
  show ?thesis
    unfolding ell_op_def
    by (intro cInf_greatest)
      (use feasible_nonempty[OF k L] per in auto)
qed

subsection \<open>Test functions and viscosity sub-/supersolutions\<close>

definition test_fun_at ::
  "(real^'n \<Rightarrow> real) \<Rightarrow> (real^'n \<Rightarrow> real^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> bool"
  where
  "test_fun_at \<phi> g H x \<longleftrightarrow>
     transpose H = H \<and>
     (\<exists>e>0. \<forall>y \<in> ball x e. (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)) \<and>
     (g has_derivative (\<lambda>h. H *v h)) (at x)"

definition visc_subsol ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol k L \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        ell_op k L (g x) H \<le> 1)"

definition visc_supersol ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol k L \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op k L (g x) H)"

definition visc_sol ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_sol k L \<Omega> u \<longleftrightarrow> visc_subsol k L \<Omega> u \<and> visc_supersol k L \<Omega> u"

subsection \<open>First- and second-order conditions at interior minima\<close>

lemma local_min_gradient_zero:
  fixes \<psi> :: "real^'n \<Rightarrow> real"
  assumes deriv: "(\<psi> has_derivative (\<lambda>h. g \<bullet> h)) (at x)"
    and min: "eventually (\<lambda>y. \<psi> x \<le> \<psi> y) (at x)"
  shows "g = 0"
proof -
  have "(\<lambda>h. g \<bullet> h) = (\<lambda>h. 0)"
    by (rule has_derivative_local_min[OF deriv min])
  then have "g \<bullet> g = 0"
    using fun_cong[of "(\<lambda>h. g \<bullet> h)" "(\<lambda>h. 0)" g] by simp
  then show ?thesis
    by simp
qed

lemma local_min_hessian_psd:
  fixes \<psi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes e_pos: "0 < e"
    and deriv: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<psi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    and hess: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    and min: "\<And>y. y \<in> ball x e \<Longrightarrow> \<psi> x \<le> \<psi> y"
  shows "0 \<le> h \<bullet> (H *v h)"
proof (cases "h = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  have x_mem: "x \<in> ball x e"
    using e_pos by simp
  have ev_min: "eventually (\<lambda>y. \<psi> x \<le> \<psi> y) (at x)"
    using min e_pos
    by (auto simp: eventually_at dist_commute intro!: exI[of _ e])
  have gx0: "g x = 0"
    by (rule local_min_gradient_zero[OF deriv[OF x_mem] ev_min])
  define A where "A = h \<bullet> (H *v h)"
  define nh where "nh = norm h"
  have nh_pos: "0 < nh"
    using False by (simp add: nh_def)
  define d where "d = e / nh"
  have d_pos: "0 < d"
    using e_pos nh_pos by (simp add: d_def)
  have mem: "x + t *\<^sub>R h \<in> ball x e" if "\<bar>t\<bar> < d" for t
  proof -
    have "dist x (x + t *\<^sub>R h) = \<bar>t\<bar> * nh"
      by (simp add: dist_norm nh_def)
    also have "\<dots> < d * nh"
      using that nh_pos by (simp add: mult_strict_right_mono)
    also have "\<dots> = e"
      using nh_pos by (simp add: d_def)
    finally show ?thesis
      by simp
  qed
  have f_deriv: "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_real_derivative
      (g (x + t *\<^sub>R h) \<bullet> h)) (at t)"
    if t: "\<bar>t\<bar> < d" for t
  proof -
    have 1: "((\<lambda>s. x + s *\<^sub>R h) has_derivative (\<lambda>s. s *\<^sub>R h)) (at t)"
      by (auto intro!: derivative_eq_intros)
    have 2: "(\<psi> has_derivative (\<lambda>h'. g (x + t *\<^sub>R h) \<bullet> h')) (at (x + t *\<^sub>R h))"
      by (rule deriv[OF mem[OF t]])
    have "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative
        (\<lambda>s. g (x + t *\<^sub>R h) \<bullet> (s *\<^sub>R h))) (at t)"
      using diff_chain_at[OF 1 2] by (simp add: o_def)
    then have "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative
        (\<lambda>s. s * (g (x + t *\<^sub>R h) \<bullet> h))) (at t)"
      by (simp add: mult_ac)
    then show ?thesis
      unfolding has_field_derivative_def
      by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff mult_ac)
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> 0 \<le> h \<bullet> (H *v h)"
    then have A_neg: "A < 0"
      by (simp add: A_def)
    have flim: "filterlim (\<lambda>t :: real. x + t *\<^sub>R h) (at x) (at 0)"
    proof -
      have "((\<lambda>t :: real. x + t *\<^sub>R h) \<longlongrightarrow> x) (at 0)"
        by (auto intro!: tendsto_eq_intros)
      moreover have "eventually (\<lambda>t :: real. x + t *\<^sub>R h \<noteq> x) (at 0)"
        using False by (auto simp: eventually_at_filter)
      ultimately show ?thesis
        by (simp add: filterlim_at)
    qed
    have hd: "((\<lambda>y. (1 / norm (y - x)) *\<^sub>R (g y - (g x + H *v (y - x)))) \<longlongrightarrow> 0) (at x)"
      using hess unfolding has_derivative_at2 by blast
    have comp: "((\<lambda>t. (1 / norm ((x + t *\<^sub>R h) - x)) *\<^sub>R
        (g (x + t *\<^sub>R h) - (g x + H *v ((x + t *\<^sub>R h) - x)))) \<longlongrightarrow> 0) (at 0)"
      by (rule filterlim_compose[OF hd flim])
    then have comp2: "((\<lambda>t. (1 / (\<bar>t\<bar> * nh)) *\<^sub>R
        (g (x + t *\<^sub>R h) - t *\<^sub>R (H *v h))) \<longlongrightarrow> 0) (at 0)"
      by (simp add: gx0 matrix_vector_mult_scaleR nh_def)
    have inner_lim: "((\<lambda>t. ((1 / (\<bar>t\<bar> * nh)) *\<^sub>R
        (g (x + t *\<^sub>R h) - t *\<^sub>R (H *v h))) \<bullet> h) \<longlongrightarrow> 0) (at 0)"
      using tendsto_inner[OF comp2 tendsto_const] by simp
    define E where
      "E = (\<lambda>t. ((1 / (\<bar>t\<bar> * nh)) *\<^sub>R (g (x + t *\<^sub>R h) - t *\<^sub>R (H *v h))) \<bullet> h)"
    have E_lim: "(E \<longlongrightarrow> 0) (at 0)"
      using inner_lim unfolding E_def .
    have E_val: "g (x + t *\<^sub>R h) \<bullet> h = t * A + (\<bar>t\<bar> * nh) * E t"
      if "t \<noteq> 0" for t
    proof -
      have nz: "\<bar>t\<bar> * nh \<noteq> 0"
        using that nh_pos by simp
      have "E t = (g (x + t *\<^sub>R h) \<bullet> h - t * A) / (\<bar>t\<bar> * nh)"
        by (simp add: E_def A_def inner_diff_left inner_diff_right
            inner_commute)
      with nz show ?thesis
        by (simp add: field_simps)
    qed
    define eps where "eps = - A / (2 * nh)"
    have eps_pos: "0 < eps"
      using A_neg nh_pos by (simp add: eps_def divide_neg_pos)
    have "eventually (\<lambda>t. \<bar>E t\<bar> < eps) (at 0)"
      using tendstoD[OF E_lim eps_pos] by (simp add: dist_real_def)
    then obtain dd where dd_pos: "0 < dd"
      and dd: "\<And>t. t \<noteq> 0 \<Longrightarrow> \<bar>t\<bar> < dd \<Longrightarrow> \<bar>E t\<bar> < eps"
      by (auto simp: eventually_at dist_real_def)
    define t0 where "t0 = min d dd / 2"
    have t0_pos: "0 < t0"
      using d_pos dd_pos by (simp add: t0_def)
    have t0d: "t0 < d" and t0dd: "t0 < dd"
      using d_pos dd_pos by (auto simp: t0_def)
    have fneg: "g (x + s *\<^sub>R h) \<bullet> h < 0" if s: "0 < s" "s \<le> t0" for s
    proof -
      have s_ne: "s \<noteq> 0" and s_dd: "\<bar>s\<bar> < dd"
        using s t0dd by auto
      have Es: "\<bar>E s\<bar> < eps"
        by (rule dd[OF s_ne s_dd])
      have gsh: "g (x + s *\<^sub>R h) \<bullet> h = s * A + (s * nh) * E s"
        using E_val[OF s_ne] s(1) by (simp add: abs_of_pos)
      have snh_pos: "0 < s * nh"
        using s(1) nh_pos by simp
      have "(s * nh) * E s < (s * nh) * eps"
        using Es snh_pos by (intro mult_strict_left_mono) auto
      moreover have "(s * nh) * eps = s * (- A / 2)"
        using nh_pos by (simp add: eps_def)
      ultimately have "g (x + s *\<^sub>R h) \<bullet> h < s * A + s * (- A / 2)"
        unfolding gsh by linarith
      also have "\<dots> = s * (A / 2)"
        by (simp add: algebra_simps)
      also have "\<dots> < 0"
        using s(1) A_neg by (intro mult_pos_neg) auto
      finally show ?thesis .
    qed
    have cont: "continuous_on {0..t0} (\<lambda>s. \<psi> (x + s *\<^sub>R h))"
    proof -
      have "isCont (\<lambda>s. \<psi> (x + s *\<^sub>R h)) s" if "s \<in> {0..t0}" for s
      proof -
        have "\<bar>s\<bar> < d"
          using that t0d by auto
        from f_deriv[OF this] show ?thesis
          by (rule DERIV_isCont)
      qed
      then show ?thesis
        by (auto intro: continuous_at_imp_continuous_on)
    qed
    obtain \<xi> where xi: "0 < \<xi>" "\<xi> < t0"
      and mvt_eq: "\<psi> (x + t0 *\<^sub>R h) - \<psi> (x + 0 *\<^sub>R h)
        = (g (x + \<xi> *\<^sub>R h) \<bullet> h) * (t0 - 0)"
    proof -
      have derf: "((\<lambda>s. \<psi> (x + s *\<^sub>R h)) has_derivative
          (\<lambda>y. y * (g (x + s *\<^sub>R h) \<bullet> h))) (at s)"
        if "0 < s" "s < t0" for s
      proof -
        have "\<bar>s\<bar> < d"
          using that t0d by auto
        from f_deriv[OF this, unfolded has_field_derivative_def]
        show ?thesis
          by (rule has_derivative_eq_rhs) (simp add: fun_eq_iff mult_ac)
      qed
      from mvt[OF t0_pos cont derf] obtain \<xi>
        where "0 < \<xi>" "\<xi> < t0"
          "\<psi> (x + t0 *\<^sub>R h) - \<psi> (x + 0 *\<^sub>R h)
            = (t0 - 0) * (g (x + \<xi> *\<^sub>R h) \<bullet> h)"
        by blast
      then show thesis
        by (intro that[of \<xi>]) (auto simp: algebra_simps)
    qed
    have "\<psi> (x + 0 *\<^sub>R h) \<le> \<psi> (x + t0 *\<^sub>R h)"
      using min[OF mem[of t0]] t0d t0_pos by simp
    with mvt_eq have "0 \<le> (g (x + \<xi> *\<^sub>R h) \<bullet> h) * t0"
      by simp
    with t0_pos have "0 \<le> g (x + \<xi> *\<^sub>R h) \<bullet> h"
      by (simp add: zero_le_mult_iff)
    with fneg[of \<xi>] xi show False
      by simp
  qed
qed

subsection \<open>The explicit solution of Example 3.1 is a viscosity solution\<close>

lemma ball_v_eq_quadratic:
  fixes y :: "real^'n"
  assumes "y \<in> ball 0 r"
  shows "ball_v r k y = (r\<^sup>2 - y \<bullet> y) / real (CARD('n) - k)"
proof -
  have "norm y < r"
    using assms by (simp add: dist_norm)
  then have "(norm y)\<^sup>2 < r\<^sup>2"
    by (intro power_strict_mono) simp_all
  then have "y \<bullet> y < r\<^sup>2"
    by (simp add: dot_square_norm)
  then show ?thesis
    by (simp add: ball_v_def max_def)
qed

lemma quadratic_gradient:
  fixes y :: "real^'n"
  assumes c_pos: "0 < (c::real)"
  shows "((\<lambda>y :: real^'n. (r\<^sup>2 - y \<bullet> y) / c) has_derivative
      (\<lambda>h. (- (2 / c) *\<^sub>R y) \<bullet> h)) (at y)"
  using c_pos
  by (auto intro!: derivative_eq_intros
      simp: inner_commute divide_simps algebra_simps)

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
    using symH by (metis transpose_def vec_lambda_beta)
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

end
