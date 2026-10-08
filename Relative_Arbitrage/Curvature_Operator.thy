
(*<*)
theory Curvature_Operator
  imports "Symmetric_Matrix_Spectra.Symmetric_Spectral"
    "Symmetric_Matrix_Spectra.Matrix_Algebra"
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

text \<open>\<open>F\<close> reads only the symmetric part of \<open>M\<close>: every feasible \<open>a\<close> is symmetric,
  and \<open>tr(M\<^sup>T a) = tr(M a)\<close> for symmetric \<open>a\<close>.  This is what lets the envelopes
  \<open>F\<^sub>*\<close>, \<open>F\<^sup>*\<close> be taken over all matrices rather than over \<open>\<bbbS>\<^sup>n\<close>.\<close>

theorem ell_op_sym_part:
  fixes M :: "real^'n::finite^'n"
  shows "ell_op k L p M = ell_op k L p ((1/2) *\<^sub>R (M + transpose M))"
proof -
  have "- trace (M ** a) / 2 = - trace (((1/2) *\<^sub>R (M + transpose M)) ** a) / 2"
    if "a \<in> feasible k L p" for a
  proof -
    have sym: "transpose a = a" using that by (simp add: feasible_def psd_def)
    show ?thesis
      by (simp add: scaleR_matrix_mult matrix_add_rdistrib trace_add trace_scaleR
            trace_transpose_mult_sym[OF sym])
  qed
  then show ?thesis unfolding ell_op_def by (intro arg_cong[where f = Inf] image_cong) auto
qed

text \<open>The upper eigenvalue bound bounds every diagonal entry.\<close>

lemma eigen_ub_diag:
  fixes a :: "real^'m::finite^'m"
  assumes "eigen_ub a L"
  shows "a $ l $ l \<le> L"
proof -
  have ax: "axis l 1 \<bullet> (axis l 1 :: real^'m) = 1"
    by (simp add: inner_vec_def axis_def if_distrib cong: if_cong)
  show ?thesis
    using assms diag_entry_quadform[where a = a and l = l] ax
    by (auto simp: eigen_ub_def dest: spec[of _ "axis l 1"])
qed

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

text \<open>\<open>neg_half_trace_ball_op\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The candidate value function and its derivatives\<close>

definition ball_v :: "real \<Rightarrow> nat \<Rightarrow> real^'n \<Rightarrow> real" where
  "ball_v r k x = max (r\<^sup>2 - x \<bullet> x) 0 / real (CARD('n) - k)"

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

subsection \<open>Test functions and viscosity sub-/supersolutions\<close>

text \<open>\<open>test_fun_at\<close>, \<open>visc_subsol\<close>, \<open>visc_supersol\<close>, \<open>visc_sol\<close> live in \<open>Viscosity_Definitions\<close>.\<close>


subsection \<open>First- and second-order conditions at interior minima\<close>

text \<open>\<open>local_min_gradient_zero\<close>, \<open>local_min_hessian_psd\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


(*<*)
end
(*>*)
