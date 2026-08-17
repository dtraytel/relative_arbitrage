
(*<*)
theory Curvature_Operator
  imports "Symmetric_Matrix_Spectra.Symmetric_Spectral"
begin

(*>*)

text \<open>
  Formalizes the deterministic core of J.-H. Lai, M. Shkolnikov and
  H. M. Soner, Relative arbitrage problem under eigenvalue lower bounds
  (\<^cite>\<open>LaiShkolnikovSoner\<close>): the operator \<open>F\<close> of Eq. (1.9),

    \<open>F(p, M) = Inf {- trace (M ** a) / 2 | a. psd a \<and> a *v p = 0
       \<and> eigen_lb a (n - k) \<and> eigen_ub a L}\<close>,

  with the spectral conditions expressed through their Courant-Fischer
  variational characterizations \<open>eigen_lb\<close> and \<open>eigen_ub\<close> rather than
  ordered eigenvalues. It proves the trace lower bound
  \<open>trace a \<ge> n - k\<close> for feasible \<open>a\<close> and its attainment by
  rank-\<open>(n - k)\<close> orthogonal projections, the fact behind Example 3.1,
  together with the spectral theorem for real symmetric matrices and the
  degenerate ellipticity of \<open>F\<close>. It also gives viscosity sub- and
  supersolutions of \<open>F(Du, D\<^sup>2u) = 1\<close> in the Crandall-Ishii-Lions
  test-function formulation, and shows that the explicit solution of
  Example 3.1 (Eq. 3.9) is a viscosity solution on the open ball with
  zero boundary values.\<close>
unbundle inner_syntax

section \<open>The constraint set and the elliptic operator of Eq. (1.9)\<close>

text \<open>
  Positive semidefinite symmetric matrices; the spectral constraints of
  Eq. (1.9) are expressed via their Courant--Fischer variational
  characterizations, which for symmetric matrices are equivalent to
  \<open>\<lambda>\<^sub>(\<^sub>m\<^sub>)(a) \<ge> 1\<close> and \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(a) \<le> L\<close>, respectively.
\<close>

text \<open>\<open>psd\<close> lives in @{theory Symmetric_Matrix_Spectra.Symmetric_Spectral}.\<close>

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
  \<open>- (2/(n-k)) *\<^sub>R mat 1\<close>.  Then \<open>F(\<nabla>v x, \<nabla>\<^sup>2 v x) = 1\<close> for all
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
    by (auto intro!: derivative_eq_intros simp: inner_commute divide_simps)
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

text \<open>
  Example 3.1: at every interior point of the ball --- including the centre,
  where the gradient vanishes --- the gradient and Hessian of \<open>v\<close> satisfy the
  PDE \<open>F(\<nabla>v, \<nabla>\<^sup>2 v) = 1\<close> of Theorem 1.1.  At \<open>p = 0\<close> the constraint \<open>a p = 0\<close>
  of Eq. (1.9) is vacuous, so the feasible set is larger, but the value of the
  infimum is unchanged: the trace bound \<open>tr a \<ge> n - k\<close> holds for every
  feasible \<open>a\<close> and is attained by a rank-\<open>(n-k)\<close> projection, which is feasible
  for \<open>p = 0\<close> as well.
\<close>

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
  The standard Crandall--Ishii--Lions test-function definitions for the
  equation \<open>F(Du, D\<^sup>2u) = 1\<close>.  A test function at \<open>x\<close> is represented by its
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

text \<open>\<open>test_fun_at\<close>, \<open>visc_subsol\<close>, \<open>visc_supersol\<close>, \<open>visc_sol\<close> live in \<open>Viscosity_Definitions\<close>.\<close>


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
  by (auto intro!: derivative_eq_intros simp: inner_commute divide_simps)

text \<open>\<open>ball_v_viscosity_subsol\<close>, \<open>ball_v_viscosity_supersol\<close>, \<open>ball_v_solves_pde_viscosity\<close> live in \<open>Viscosity_Ball\<close>.\<close>


(*<*)
end
(*>*)
