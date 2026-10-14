
(*<*)
theory Operator_Formula
  imports
    Curvature_Operator Operator_Continuity
begin

(*>*)

text \<open>
  Formalizes the eigenvalue comparison used in the proof of Lemma 3.1 of
  \<^cite>\<open>LaiShkolnikovSoner\<close>, the Poincare separation inequality

    \<open>lambda\<^sub>i(M\<^sub>p) \<ge> lambda\<^bsub>i+1\<^esub>(M)\<close>,   \<open>i = 1, ..., n - 1\<close>,

  together with the Rayleigh bounds it rests on. Two consequences are
  used: for Eq. (3.5), that the eigenvalue \<open>M\<^sub>p\<close> carries in the
  \<open>p\<close>-direction, \<open>min (lambda\<^sub>n(M), 0)\<close>, is the smallest of the
  spectrum of \<open>M\<^sub>p\<close>, which needs only the weak Rayleigh bound; and for
  Eq. (3.6), the limit as \<open>p\<^sup>m \<rightarrow> 0\<close> along \<open>p\<^sup>m = q\<^sub>1 / m\<close>, where the
  index shift comes from the full separation inequality.\<close>
section \<open>Elementary matrix algebra, continued\<close>

text \<open>\<open>matrix_mul_diff_right\<close> and \<open>matrix_mul_diff_left\<close> live in
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

section \<open>The full Ky Fan sum is the trace\<close>

text \<open>\<open>kyfan CARD('n)\<close> takes the whole spectrum, so it equals the trace, by
  evaluating \<open>kyfan\<close> on the eigenbasis via the completeness relation.\<close>

section \<open>The Rayleigh bounds\<close>

text \<open>A unit vector gives a rank-one projection, and its orthogonal
  complement a projection of trace \<open>n-1\<close>.\<close>

section \<open>\<open>M\<^sub>p\<close> on the hyperplane \<open>p\<^sup>\<bottom>\<close>\<close>

text \<open>On \<open>p\<^sup>\<bottom>\<close> the projection \<open>I - pp'/|p|\<^sup>2\<close> acts as the identity, so
  \<open>M\<^sub>p\<close> has exactly the Rayleigh quotients of \<open>M\<close> there, and its
  \<open>p\<close>-direction eigenvalue \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close> is the smallest of its
  spectrum, as needed for Eq. (3.5).  The first fact is
  @{thm [source] perp_proj_fixes_perp} in
  @{theory Symmetric_Matrix_Spectra.Orthogonal_Projections}.\<close>

lemma Mp_apply_perp:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0" and y: "p \<bullet> y = 0"
  shows "Mp p M *v y = (mat 1 - rank1proj p) *v (M *v y)"
proof -
  define Q where "Q = (mat 1 - rank1proj p :: real^'n^'n)"
  define c where "c = min (eigval CARD('n) M) 0"
  have Qy: "Q *v y = y"
    unfolding Q_def by (rule perp_proj_fixes_perp[OF y])
  have MpQ: "Mp p M = Q ** M ** Q + c *\<^sub>R rank1proj p"
    unfolding Mp_def Q_def c_def using p by simp
  have "Mp p M *v y = (Q ** M ** Q) *v y + (c *\<^sub>R rank1proj p) *v y"
    unfolding MpQ by (rule matrix_vector_mult_add_rdistrib)
  also have "\<dots> = Q *v (M *v (Q *v y)) + c *\<^sub>R (rank1proj p *v y)"
    by (simp add: matrix_vector_mul_assoc matrix_mul_assoc
        scaleR_matrix_vector_assoc[symmetric])
  also have "\<dots> = Q *v (M *v y)"
    by (simp add: Qy rank1proj_annihilates_perp[OF y])
  finally show ?thesis
    unfolding Q_def .
qed

lemma Mp_quadform_perp:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0" and y: "p \<bullet> y = 0"
  shows "y \<bullet> (Mp p M *v y) = y \<bullet> (M *v y)"
proof -
  have symQ: "transpose (mat 1 - rank1proj p :: real^'n^'n) = mat 1 - rank1proj p"
    by (rule symmetric_perp_proj)
  have "y \<bullet> (Mp p M *v y) = y \<bullet> ((mat 1 - rank1proj p) *v (M *v y))"
    by (simp add: Mp_apply_perp[OF p y])
  also have "\<dots> = (M *v y) \<bullet> ((mat 1 - rank1proj p) *v y)"
    by (rule sym_inner_swap[OF symQ])
  also have "\<dots> = (M *v y) \<bullet> y"
    by (simp add: perp_proj_fixes_perp[OF y])
  also have "\<dots> = y \<bullet> (M *v y)"
    by (simp add: inner_commute)
  finally show ?thesis .
qed

text \<open>Hence every Rayleigh quotient of \<open>M\<^sub>p\<close> on \<open>p\<^sup>\<bottom>\<close> dominates the
  \<open>p\<close>-direction eigenvalue.  This is the one-sided comparison the paper needs.\<close>

theorem Mp_perp_quadform_ge:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
    and y: "p \<bullet> y = 0" and ny: "norm y = 1"
  shows "min (eigval CARD('n) M) 0 \<le> y \<bullet> (Mp p M *v y)"
proof -
  have "min (eigval CARD('n) M) 0 \<le> eigval CARD('n) M"
    by (rule min.cobounded1)
  also have "\<dots> \<le> y \<bullet> (M *v y)"
    by (rule eigval_min_le_quadform[OF sym ny])
  also have "\<dots> = y \<bullet> (Mp p M *v y)"
    by (rule Mp_quadform_perp[OF p y, symmetric])
  finally show ?thesis .
qed

section \<open>An orthonormal eigenbasis of \<open>M\<^sub>p\<close> containing \<open>p/|p|\<close>\<close>

text \<open>The unit vector \<open>p/|p|\<close> is an eigenvector of \<open>M\<^sub>p\<close> with eigenvalue
  \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close>, so the symmetric \<open>M\<^sub>p\<close> has an orthonormal eigenbasis
  containing it, the rest lying in \<open>p\<^sup>\<bottom>\<close>.\<close>

lemma Mp_apply_unit_p:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0"
  shows "Mp p M *v (p /\<^sub>R norm p) = min (eigval CARD('n) M) 0 *\<^sub>R (p /\<^sub>R norm p)"
  using Mp_apply_p[OF p, of M] by (simp add: matrix_vector_mult_scaleR mult.commute)

lemma Mp_quadform_unit_p:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0"
  shows "(p /\<^sub>R norm p) \<bullet> (Mp p M *v (p /\<^sub>R norm p)) = min (eigval CARD('n) M) 0"
proof -
  define q where "q = p /\<^sub>R norm p"
  have "norm q = 1" unfolding q_def using p by simp
  then have qq: "q \<bullet> q = 1" by (simp add: dot_square_norm)
  show ?thesis using Mp_apply_unit_p[OF p, of M] unfolding q_def[symmetric] by (simp add: qq)
qed

theorem Mp_eigenbasis_adapted:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
  shows "\<exists>B. onormal B \<and> span B = UNIV
      \<and> (\<forall>u\<in>B. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u)
      \<and> p /\<^sub>R norm p \<in> B
      \<and> (\<forall>u \<in> B - {p /\<^sub>R norm p}. p \<bullet> u = 0)"
proof -
  have nq: "norm (p /\<^sub>R norm p) = 1"
    using p by simp
  have eigq: "Mp p M *v (p /\<^sub>R norm p)
      = ((p /\<^sub>R norm p) \<bullet> (Mp p M *v (p /\<^sub>R norm p))) *\<^sub>R (p /\<^sub>R norm p)"
    unfolding Mp_quadform_unit_p[OF p] by (rule Mp_apply_unit_p[OF p])
  show ?thesis
    using eigenbasis_containing_eigenvector[OF transpose_Mp[OF sym] nq eigq] p by auto
qed

section \<open>The Courant-Fischer min-max lower bound\<close>

text \<open>The general Courant-Fischer lower bound, @{thm [source] eigval_ge_of_subspace},
  lives in @{theory Symmetric_Matrix_Spectra.Poincare_Separation}.  Its \<open>c = 1\<close>
  form is what \<open>eigen_lb\<close> delivers.\<close>

corollary eigval_ge_of_eigen_lb:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and lb: "eigen_lb a m"
    and m: "0 < m" "m \<le> CARD('n)"
  shows "1 \<le> eigval m a"
proof -
  obtain S where S: "subspace S" "m \<le> dim S"
    and quad: "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
    using lb by (auto simp: eigen_lb_def)
  have quad': "1 * (x \<bullet> x) \<le> x \<bullet> (a *v x)" if "x \<in> S" for x
    using quad[OF that] by simp
  show ?thesis
    by (rule eigval_ge_of_subspace[OF sym S(1) S(2) quad' m(1) m(2)])
qed

section \<open>The clipped trace bound\<close>

text \<open>With the Courant-Fischer bound in hand, the clipped weights sum to at
  least \<open>m\<close> over an eigenbasis of \<open>a\<close>: the top-\<open>m\<close> threshold set has
  eigenvalues \<open>\<ge> eigval m a \<ge> 1\<close>, each clipped to \<open>1\<close>, and the rest
  contribute \<open>\<ge> 0\<close> by positive semidefiniteness.\<close>

lemma sum_min_eigval_ge:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and psd: "\<And>x. 0 \<le> x \<bullet> (a *v x)"
    and lb: "eigen_lb a m" and m: "0 < m" "m \<le> CARD('n)"
    and V: "onormal V" "span V = UNIV"
    and eig: "\<And>v. v \<in> V \<Longrightarrow> a *v v = (v \<bullet> (a *v v)) *\<^sub>R v"
  shows "real m \<le> (\<Sum>v\<in>V. min (v \<bullet> (a *v v)) 1)"
proof -
  obtain T w where T: "T \<subseteq> V" "card T = m"
    and "\<And>u v. u \<in> T \<Longrightarrow> v \<in> V - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and "w \<in> T" and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    and eigw: "eigval m a = w \<bullet> (a *v w)"
    using eigval_threshold_witness[OF V sym eig m] by blast
  have one: "1 \<le> eigval m a"
    by (rule eigval_ge_of_eigen_lb[OF sym lb m])
  have inT: "min (v \<bullet> (a *v v)) 1 = 1" if v: "v \<in> T" for v
    using one wmin[OF v] unfolding eigw by simp
  have "real m = (\<Sum>v\<in>T. min (v \<bullet> (a *v v)) 1)"
    using inT T(2) by simp
  also have "\<dots> \<le> (\<Sum>v\<in>V. min (v \<bullet> (a *v v)) 1)"
    using onormal_finite[OF V(1)] T(1) psd by (intro sum_mono2) auto
  finally show ?thesis .
qed

text \<open>The bound transfers from an eigenbasis of \<open>a\<close> to an arbitrary
  orthonormal basis, as Eq. (3.5) needs for the adapted eigenbasis of
  \<open>M\<^sub>p\<close>.  The clipped matrix \<open>c\<close> is dominated by both \<open>a\<close> and the identity,
  with basis-independent trace.\<close>

theorem sum_min_weights_ge:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and psd: "\<And>x. 0 \<le> x \<bullet> (a *v x)"
    and lb: "eigen_lb a m" and m: "0 < m" "m \<le> CARD('n)"
    and B: "onormal B" "span B = UNIV"
  shows "real m \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
proof -
  obtain V where V: "onormal V" "span V = UNIV"
    and finV: "finite V"
    and eig: "\<And>v. v \<in> V \<Longrightarrow> a *v v = (v \<bullet> (a *v v)) *\<^sub>R v"
    using symmetric_eigendecomposition[OF sym] by metis
  define lam where "lam = (\<lambda>v :: real^'n. v \<bullet> (a *v v))"
  define c where "c = (\<Sum>v\<in>V. min (lam v) 1 *\<^sub>R outer_prod v v)"
  have adecomp: "a = (\<Sum>v\<in>V. lam v *\<^sub>R outer_prod v v)"
    unfolding lam_def by (rule spectral_decomposition[OF V eig])
  have onecomp: "(mat 1 :: real^'n^'n) = (\<Sum>v\<in>V. 1 *\<^sub>R outer_prod v v)"
    using onormal_complete[OF V] by simp
  text \<open>\<open>c \<preceq> a\<close> and \<open>c \<preceq> I\<close>.\<close>
  have cle_a: "u \<bullet> (c *v u) \<le> u \<bullet> (a *v u)" for u
    unfolding c_def
    by (rule quadform_weighted_outer_mono[OF V(1) adecomp refl]) simp
  have cle_1: "u \<bullet> (c *v u) \<le> u \<bullet> u" for u
  proof -
    have "u \<bullet> (c *v u) \<le> u \<bullet> (mat 1 *v u)"
      unfolding c_def
      by (rule quadform_weighted_outer_mono[OF V(1) onecomp refl]) simp
    then show ?thesis
      by simp
  qed
  have cle: "u \<bullet> (c *v u) \<le> min (u \<bullet> (a *v u)) 1" if u: "u \<in> B" for u
  proof -
    have nu: "norm u = 1"
      using u B(1) by (simp add: onormal_def)
    then have uu: "u \<bullet> u = 1"
      by (simp add: dot_square_norm)
    show ?thesis
      using cle_a[of u] cle_1[of u] uu by simp
  qed
  text \<open>The trace of \<open>c\<close> is at least \<open>m\<close>, and is basis-independent.\<close>
  have trc: "trace c = (\<Sum>v\<in>V. min (lam v) 1)"
    unfolding c_def by (rule trace_weighted_outer_sum[OF V(1)])
  have mtr: "real m \<le> trace c"
    unfolding trc lam_def
    by (rule sum_min_eigval_ge[OF sym psd lb m V eig])
  have "real m \<le> (\<Sum>u\<in>B. u \<bullet> (c *v u))"
    using mtr trace_onormal_basis[OF B, of c] by simp
  also have "\<dots> \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
    using cle by (intro sum_mono) simp
  finally show ?thesis .
qed

section \<open>The box program\<close>

text \<open>The combinatorial heart of Eq. (3.5), stated without matrices.  Splitting
  \<open>lam u = max (lam u) 0 + min (lam u) 0\<close>, the positive part is bounded by
  \<open>t \<le> 1\<close> and the negative part by \<open>sum_weighted_le_top_subset\<close>, whose "top
  subset" is the \<open>m\<close> least negative directions.\<close>

text \<open>\<open>sum_weighted_le_top_subset\<close> needs weights summing to \<open>m\<close> exactly,
  while the clipped-weight bound only gives \<open>\<ge> m\<close>.  Scaling down by
  \<open>real m / (\<Sum>t)\<close> repairs this without hurting the negative part, since
  \<open>min (lam u) 0 \<le> 0\<close>.\<close>

section \<open>The upper bound of Eq. (3.5) in bracket form\<close>

text \<open>For a symmetric \<open>N\<close> with eigenbasis \<open>B\<close>, and weights coming from any
  \<open>a\<close> satisfying the feasible-set constraints, the objective is bounded by
  \<open>bracket m L N\<close>: this is @{thm [source] bracket_upper_bound} in
  @{theory Symmetric_Matrix_Spectra.Ky_Fan}.\<close>

text \<open>Applied to \<open>N = M\<^sub>p\<close> and a feasible \<open>a\<close>: this is the upper-bound half of
  Eq. (3.5) for the actual trace pairing.  \<open>trace_Mp\<close> replaces \<open>M\<close> by \<open>M\<^sub>p\<close>,
  \<open>trace_mult_eigen_weights\<close> expands against the adapted eigenbasis,
  \<open>sum_min_weights_ge\<close> supplies the clipped-weight bound from \<open>eigen_lb\<close>, and
  \<open>bracket_upper_bound\<close> finishes.\<close>

theorem trace_le_bracket_feasible:
  fixes M a :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
    and af: "a \<in> feasible k L p" and L: "1 \<le> L"
    and k: "k < CARD('n)"
  shows "trace (M ** a) \<le> bracket (CARD('n) - k) L (Mp p M)"
proof -
  define m where "m = CARD('n) - k"
  have m0: "0 < m"
    unfolding m_def using k by simp
  have mn: "m \<le> CARD('n)"
    unfolding m_def by simp
  have syma: "transpose a = a"
    using af by (simp add: feasible_def psd_def)
  have psda: "0 \<le> x \<bullet> (a *v x)" for x
    using af by (simp add: feasible_def psd_def)
  have ap: "a *v p = 0"
    using af by (simp add: feasible_def)
  have lba: "eigen_lb a m"
    unfolding m_def using af by (simp add: feasible_def)
  have symMp: "transpose (Mp p M) = Mp p M"
    by (rule transpose_Mp[OF sym])
  obtain B where B: "onormal B" "span B = UNIV"
    and eigB: "\<forall>u\<in>B. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u"
    using Mp_eigenbasis_adapted[OF sym p] by blast
  have eigB': "Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u" if "u \<in> B" for u
    using eigB that by blast
  have w0: "0 \<le> u \<bullet> (a *v u)" for u
    by (rule psda)
  have wL: "u \<bullet> (a *v u) \<le> L" if u: "u \<in> B" for u
  proof -
    have "norm u = 1"
      using u B(1) by (simp add: onormal_def)
    then have uu: "u \<bullet> u = 1"
      by (simp add: dot_square_norm)
    have "u \<bullet> (a *v u) \<le> L * (u \<bullet> u)"
      using af by (simp add: feasible_def eigen_ub_def)
    then show ?thesis
      using uu by simp
  qed
  have wsum: "real m \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
    by (rule sum_min_weights_ge[OF syma psda lba m0 mn B])
  have "trace (M ** a) = trace (Mp p M ** a)"
    by (rule trace_Mp[OF syma ap, symmetric])
  also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (Mp p M *v u)) * (u \<bullet> (a *v u)))"
    by (rule trace_mult_eigen_weights[OF B symMp eigB'])
  also have "\<dots> \<le> bracket m L (Mp p M)"
    by (rule bracket_upper_bound[OF symMp B eigB' mn L w0 wL wsum])
  finally show ?thesis
    unfolding m_def .
qed

text \<open>Read back through the definition of \<open>ell_op\<close> as an infimum: this is one
  of the two inequalities of Eq. (3.5).\<close>

corollary ell_op_ge_half_bracket:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "- (1/2) * bracket (CARD('n) - k) L (Mp p M) \<le> ell_op k L p M"
  unfolding ell_op_def
proof (rule cInf_greatest)
  show "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p \<noteq> {}"
    using feasible_witness[OF k L] by blast
next
  fix x
  assume "x \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
  then obtain a :: "real^'n^'n" where a: "a \<in> feasible k L p"
    and x: "x = - trace (M ** a) / 2"
    by blast
  have "trace (M ** a) \<le> bracket (CARD('n) - k) L (Mp p M)"
    by (rule trace_le_bracket_feasible[OF sym p a L k(2)])
  then show "- (1/2) * bracket (CARD('n) - k) L (Mp p M) \<le> x"
    unfolding x by simp
qed

section \<open>The objective of Eq. (3.5) in the adapted eigenbasis\<close>

text \<open>The paper justifies Eq. (3.5) by observing \<open>tr(Ma) = tr(M\<^sub>p a)\<close> for
  \<open>a \<succeq> 0\<close> with \<open>ap = 0\<close>, and writing symmetric \<open>M\<^sub>p\<close> as a linear
  combination of outer products (\<open>trace_Mp\<close> in @{theory Relative_Arbitrage_Equation.Operator_Continuity} gives the
  first fact).  This section carries out the expansion and its weight
  constraints.\<close>

section \<open>Feasibility of weighted outer-product sums\<close>

text \<open>For the reverse inequality of Eq. (3.5) a feasible \<open>a\<close> attaining the
  bracket must be exhibited, of the form
  \<open>a = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)\<close> for an orthonormal basis \<open>B\<close>.  This
  section checks each clause of \<open>feasible\<close> for such a sum; the
  annihilation clause is @{thm [source] weighted_outer_sum_annihilates} in
  @{theory Symmetric_Matrix_Spectra.Outer_Products}.\<close>

text \<open>The upper eigenvalue bound: all weights below \<open>L\<close> gives \<open>eigen_ub \<dots> L\<close>,
  by Parseval.\<close>

lemma eigen_ub_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" "span B = UNIV"
    and cL: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> L"
  shows "eigen_ub (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) L"
  unfolding eigen_ub_def
proof
  fix x :: "real^'n"
  have "(\<Sum>u\<in>B. c u * (u \<bullet> x)^2) \<le> (\<Sum>u\<in>B. L * (u \<bullet> x)^2)"
    using cL by (intro sum_mono mult_right_mono) auto
  then show "x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x) \<le> L * (x \<bullet> x)"
    by (simp add: quadform_weighted_outer_sum_eq[OF onormal_finite[OF B(1)]]
        parseval_onormal[OF B] flip: sum_distrib_left)
qed

text \<open>The lower eigenvalue bound: a subset of the basis on which the weights are
  at least \<open>1\<close> spans a subspace witnessing \<open>eigen_lb\<close>, of dimension its
  cardinality, by Parseval on that span.\<close>

lemma eigen_lb_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" "span B = UNIV"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u"
    and S: "S \<subseteq> B" and cS: "\<And>u. u \<in> S \<Longrightarrow> 1 \<le> c u"
    and m: "m \<le> card S"
  shows "eigen_lb (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) m"
  unfolding eigen_lb_def
proof (intro exI[of _ "span S"] conjI ballI)
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have onS: "onormal S"
    by (rule onormal_subset[OF B(1) S])
  show "subspace (span S)"
    by (rule subspace_span)
  show "m \<le> dim (span S)"
    using m onormal_card_dim_span[OF onS] by simp
  fix x assume x: "x \<in> span S"
  have "x \<bullet> x = (\<Sum>u\<in>S. (u \<bullet> x)^2)"
    by (rule onormal_span_parseval[OF onS x, symmetric])
  also have "\<dots> \<le> (\<Sum>u\<in>S. c u * (u \<bullet> x)^2)"
  proof (rule sum_mono)
    fix u assume "u \<in> S"
    then show "(u \<bullet> x)^2 \<le> c u * (u \<bullet> x)^2"
      using mult_right_mono[OF cS[OF \<open>u \<in> S\<close>], of "(u \<bullet> x)^2"] by simp
  qed
  also have "\<dots> \<le> (\<Sum>u\<in>B. c u * (u \<bullet> x)^2)"
    using c0 by (intro sum_mono2[OF finB S]) auto
  also have "\<dots> = x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x)"
    by (rule quadform_weighted_outer_sum_eq[OF finB, symmetric])
  finally show "x \<bullet> x \<le> x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x)" .
qed

section \<open>The reverse inequality of Eq. (3.5): the attaining witness\<close>

text \<open>The optimum of the linear program is attained at the \<open>a\<close> that puts
  weight \<open>L\<close> on every positive eigendirection of \<open>M\<^sub>p\<close> and weight \<open>1\<close> on a
  top-\<open>m\<close> threshold set inside \<open>p\<^sup>\<bottom>\<close>, possible since
  \<open>m \<le> CARD('n) - 1\<close> and the \<open>p\<close>-eigenvalue is minimal.\<close>

theorem bracket_attained:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "\<exists>a. a \<in> feasible k L p
      \<and> trace (M ** a) = bracket (CARD('n) - k) L (Mp p M)"
proof -
  define m where "m = CARD('n) - k"
  define q where "q = p /\<^sub>R norm p"
  define N where "N = Mp p M"
  have symN: "transpose N = N"
    unfolding N_def by (rule transpose_Mp[OF sym])
  obtain B where B: "onormal B" "span B = UNIV"
    and eigB: "\<forall>u\<in>B. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u"
    and qB: "q \<in> B" and restperp: "\<forall>u \<in> B - {q}. p \<bullet> u = 0"
    using Mp_eigenbasis_adapted[OF sym p] unfolding q_def by blast
  have eigB': "N *v u = (u \<bullet> (N *v u)) *\<^sub>R u" if "u \<in> B" for u
    unfolding N_def using eigB that by blast
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (N *v u))"
  text \<open>The \<open>p\<close>-eigenvalue is nonpositive and minimal.\<close>
  have lamq: "lam q = min (eigval CARD('n) M) 0"
    unfolding lam_def q_def N_def by (rule Mp_quadform_unit_p[OF p])
  have lamq_le0: "lam q \<le> 0"
    unfolding lamq by simp
  have lamq_min: "lam q \<le> lam u" if u: "u \<in> B - {q}" for u
  proof -
    have nu: "norm u = 1"
      using u B(1) by (simp add: onormal_def)
    have pu: "p \<bullet> u = 0"
      using u restperp by blast
    have lu: "lam u = u \<bullet> (Mp p M *v u)"
      unfolding lam_def N_def by (rule refl)
    have "min (eigval CARD('n) M) 0 \<le> u \<bullet> (Mp p M *v u)"
      by (rule Mp_perp_quadform_ge[OF sym p pu nu])
    then show ?thesis
      unfolding lamq lu .
  qed
  text \<open>Pick the top-\<open>m\<close> threshold set inside \<open>B - {q}\<close>.\<close>
  have finB': "finite (B - {q})"
    using finB by simp
  have cardB': "card (B - {q}) = CARD('n) - 1"
    using qB finB cardB by (simp add: card_Diff_singleton)
  have mB': "m \<le> card (B - {q})"
    unfolding m_def cardB' using k(1) by simp
  obtain T0 where T0: "T0 \<subseteq> B - {q}" "card T0 = m"
    and thresh': "\<And>u v. u \<in> T0 \<Longrightarrow> v \<in> (B - {q}) - T0 \<Longrightarrow> lam v \<le> lam u"
    using exists_top_subset[where f = lam, OF finB' mB'] by metis
  have T0B: "T0 \<subseteq> B"
    using T0(1) by blast
  have qnotT0: "q \<notin> T0"
    using T0(1) by blast
  text \<open>\<open>T\<^sub>0\<close> is a threshold set of the whole basis, the \<open>p\<close>-direction being
    minimal.\<close>
  have thresh: "lam v \<le> lam u" if u: "u \<in> T0" and v: "v \<in> B - T0" for u v
  proof (cases "v = q")
    case True
    have "u \<in> B - {q}"
      using u T0(1) by blast
    then show ?thesis
      unfolding True by (rule lamq_min)
  next
    case False
    then have "v \<in> (B - {q}) - T0"
      using v by blast
    then show ?thesis
      by (rule thresh'[OF u])
  qed
  text \<open>The weights.\<close>
  define c where "c = (\<lambda>u :: real^'n. if 0 < lam u then L else if u \<in> T0 then 1 else 0)"
  define a where "a = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
  have c0: "0 \<le> c u" for u
    unfolding c_def using L by simp
  have cL: "c u \<le> L" for u
    unfolding c_def using L by simp
  have cT0: "1 \<le> c u" if "u \<in> T0" for u
    unfolding c_def using that L by simp
  have cq: "c q = 0"
    unfolding c_def using lamq_le0 qnotT0 by simp
  text \<open>Feasibility.\<close>
  have psda: "psd a"
    unfolding a_def by (rule psd_weighted_outer_sum[OF B(1)]) (rule c0)
  have ap: "a *v p = 0"
    unfolding a_def
  proof (rule weighted_outer_sum_annihilates[OF finB])
    fix u assume u: "u \<in> B"
    show "c u = 0 \<or> p \<bullet> u = 0"
    proof (cases "u = q")
      case True
      then show ?thesis using cq by simp
    next
      case False
      then have "u \<in> B - {q}" using u by blast
      then show ?thesis using restperp by blast
    qed
  qed
  have uba: "eigen_ub a L"
    unfolding a_def by (rule eigen_ub_weighted_outer_sum[OF B]) (rule cL)
  have mcard: "m \<le> card T0"
    using T0(2) by simp
  have lba: "eigen_lb a m"
    unfolding a_def
  proof (rule eigen_lb_weighted_outer_sum[OF B(1) B(2) _ T0B _ mcard])
    show "0 \<le> c u" if "u \<in> B" for u
      by (rule c0)
    show "1 \<le> c u" if "u \<in> T0" for u
      by (rule cT0[OF that])
  qed
  have feas: "a \<in> feasible k L p"
    unfolding feasible_def m_def[symmetric]
    using psda ap lba uba by simp
  text \<open>The value: the weights were chosen so that the objective is exactly the
    bracket.\<close>
  have pointwise: "lam u * c u
      = L * max (lam u) 0 + (if u \<in> T0 then min (lam u) 0 else 0)" for u
    unfolding c_def by (simp add: min_def max_def)
  have restrict: "(\<Sum>u\<in>B. if u \<in> T0 then min (lam u) 0 else 0)
      = (\<Sum>u\<in>T0. min (lam u) 0)"
  proof -
    have "(\<Sum>u\<in>B. if u \<in> T0 then min (lam u) 0 else 0)
        = (\<Sum>u\<in>T0. if u \<in> T0 then min (lam u) 0 else 0)"
      by (rule sum.mono_neutral_right[OF finB T0B]) auto
    also have "\<dots> = (\<Sum>u\<in>T0. min (lam u) 0)"
      by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  have poseq: "(\<Sum>u\<in>B. max (lam u) 0) = possum CARD('n) N"
    unfolding lam_def
    by (rule possum_full_eq_sum_basis[OF B symN eigB', symmetric])
  have negeq: "(\<Sum>u\<in>T0. min (lam u) 0) = kyfan m N - possum m N"
    unfolding lam_def
    by (rule kyfan_minus_possum_threshold[OF B symN eigB' T0B T0(2)
          thresh[unfolded lam_def], symmetric])
  have "trace (M ** a) = trace (N ** a)"
    unfolding N_def
    using psda by (intro trace_Mp[symmetric] ap) (simp add: psd_def)
  also have "\<dots> = (\<Sum>u\<in>B. lam u * c u)"
  proof -
    have "trace (N ** a) = (\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u)))"
      unfolding a_def by (rule trace_mult_eigen_weights[OF B symN eigB'])
    also have "\<dots> = (\<Sum>u\<in>B. lam u * c u)"
    proof (intro sum.cong refl)
      fix u assume u: "u \<in> B"
      have "u \<bullet> (a *v u) = c u"
        unfolding a_def by (rule quadform_weighted_outer_sum[OF B(1) u])
      then show "(u \<bullet> (N *v u)) * (u \<bullet> (a *v u)) = lam u * c u"
        unfolding lam_def by simp
    qed
    finally show ?thesis .
  qed
  also have "\<dots> = L * (\<Sum>u\<in>B. max (lam u) 0)
      + (\<Sum>u\<in>B. if u \<in> T0 then min (lam u) 0 else 0)"
    unfolding pointwise by (simp add: sum.distrib sum_distrib_left)
  also have "\<dots> = L * possum CARD('n) N + (kyfan m N - possum m N)"
    unfolding poseq restrict negeq by (rule refl)
  also have "\<dots> = bracket m L N"
    by (simp add: bracket_def)
  finally have val: "trace (M ** a) = bracket m L N" .
  show ?thesis
    unfolding m_def[symmetric] N_def[symmetric]
    by (rule exI[of _ a]) (intro conjI feas val)
qed

corollary ell_op_le_half_bracket:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L p M \<le> - (1/2) * bracket (CARD('n) - k) L (Mp p M)"
proof -
  obtain a :: "real^'n^'n" where a: "a \<in> feasible k L p"
    and val: "trace (M ** a) = bracket (CARD('n) - k) L (Mp p M)"
    using bracket_attained[OF sym p L k(1) k(2)] by blast
  have "ell_op k L p M \<le> - trace (M ** a) / 2"
    by (rule ell_op_le_witness[OF a])
  also have "\<dots> = - (1/2) * bracket (CARD('n) - k) L (Mp p M)"
    unfolding val by simp
  finally show ?thesis .
qed

section \<open>Eq. (3.5)\<close>

text \<open>The two inequalities together.  This is Eq. (3.5) of the paper:

    \<open>F(p, M) = -\<onehalf> \<Sum>\<^sub>i\<^sub>=\<^sub>1\<^sup>n\<^sup>-\<^sup>k [L \<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) 1{\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p)>0} + \<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) 1{\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p)\<le>0}]
                   - \<onehalf> \<Sum>\<^sub>i\<^sub>=\<^sub>n\<^sub>-\<^sub>k\<^sub>+\<^sub>1\<^sup>n L \<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) 1{\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p)>0}\<close>

  in the equivalent closed form \<open>-\<onehalf> bracket (n-k) L M\<^sub>p\<close>, where
  \<open>bracket m L a = L * possum n a + (kyfan m a - possum m a)\<close>; the two agree by
  \<open>bracket_eq_sum\<close> (@{theory Symmetric_Matrix_Spectra.Ky_Fan}), which rewrites \<open>possum\<close> and
  \<open>kyfan - possum\<close> as the sums of positive and of nonpositive ordered
  eigenvalues respectively.\<close>

theorem ell_op_eq_half_bracket:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L p M = - (1/2) * bracket (CARD('n) - k) L (Mp p M)"
  using ell_op_ge_half_bracket[OF sym p L k(1) k(2)]
    ell_op_le_half_bracket[OF sym p L k(1) k(2)]
  by simp

text \<open>And in the paper's displayed form, as sums over the ordered
  eigenvalues.\<close>

section \<open>Scale invariance: the paper's sequence is constant\<close>

text \<open>\<open>rank1proj\<close> depends only on the line through \<open>p\<close>
  (@{thm [source] rank1proj_scaleR} in
  @{theory Symmetric_Matrix_Spectra.Orthogonal_Projections}), so \<open>M\<^sub>p\<close> does too.
  Hence the paper's sequence \<open>(q\<^sub>1/m, M)\<close> for the lower bound of Eq. (3.6)
  is constant in \<open>m\<close>: \<open>M\<^sub>q\<^sub>1\<^sub>/\<^sub>m = M\<^sub>q\<^sub>1\<close>, so only \<open>p\<^sup>m \<longrightarrow> 0\<close> matters.\<close>

text \<open>\<open>F\<close> is constant along the paper's sequence: the feasible set sees only
  the direction of \<open>p\<close>.\<close>

corollary ell_op_scaleR_dir:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and c: "0 < c" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
proof -
  have "feasible k L (c *\<^sub>R p) = feasible k L p"
    using c by (auto simp: feasible_def matrix_vector_mult_scaleR)
  then show ?thesis unfolding ell_op_def by simp
qed

section \<open>The spectrum of \<open>M\<^sub>q\<close> when \<open>q\<close> is an eigenvector of \<open>M\<close>\<close>

text \<open>This is the computation behind Eq. (3.6).  If \<open>q\<close> is a unit eigenvector
  of \<open>M\<close>, any eigenbasis of \<open>M\<close> containing \<open>q\<close> is also an eigenbasis of
  \<open>M\<^sub>q\<close>: off \<open>q\<close> the eigenvalues agree, while \<open>M\<^sub>q\<close> carries
  \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close> at \<open>q\<close>.  Taking \<open>q = q\<^sub>1\<close> the top eigenvector deletes
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close> from the spectrum and replaces it at the bottom, the index
  shift of Eq. (3.6).\<close>

lemma Mp_eig_on_perp:
  fixes M :: "real^'n::finite^'n"
  assumes q: "q \<noteq> 0" and u: "q \<bullet> u = 0"
    and eigu: "M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
  shows "Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
proof -
  define mu where "mu = u \<bullet> (M *v u)"
  have eigu': "M *v u = mu *\<^sub>R u"
    unfolding mu_def by (rule eigu)
  have "Mp q M *v u = (mat 1 - rank1proj q) *v (M *v u)"
    by (rule Mp_apply_perp[OF q u])
  also have "\<dots> = (mat 1 - rank1proj q) *v (mu *\<^sub>R u)"
    unfolding eigu' by (rule refl)
  also have "\<dots> = mu *\<^sub>R ((mat 1 - rank1proj q) *v u)"
    by (simp add: matrix_scaleR_vector_ac scaleR_matrix_vector_assoc)
  also have "\<dots> = mu *\<^sub>R u"
    by (simp add: perp_proj_fixes_perp[OF u])
  finally show ?thesis
    unfolding mu_def .
qed

theorem Mp_eigenbasis_of_M_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and q: "norm q = 1"
    and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
  shows "\<exists>B. onormal B \<and> span B = UNIV \<and> q \<in> B
      \<and> (\<forall>u \<in> B - {q}. q \<bullet> u = 0)
      \<and> (\<forall>u \<in> B - {q}. M *v u = (u \<bullet> (M *v u)) *\<^sub>R u)
      \<and> (\<forall>u \<in> B - {q}. Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u)
      \<and> Mp q M *v q = min (eigval CARD('n) M) 0 *\<^sub>R q"
proof -
  have qne: "q \<noteq> 0"
    using q by auto
  obtain B where B: "onormal B" "span B = UNIV" and qB: "q \<in> B"
    and eigB: "\<forall>u\<in>B. M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    and restperp: "\<forall>u \<in> B - {q}. q \<bullet> u = 0"
    using eigenbasis_containing_eigenvector[OF sym q eigq] by blast
  have MpB: "\<forall>u \<in> B - {q}. Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
  proof (intro ballI)
    fix u assume u: "u \<in> B - {q}"
    have qu: "q \<bullet> u = 0"
      using u restperp by blast
    have eigu: "M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
      using u eigB by blast
    show "Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
      by (rule Mp_eig_on_perp[OF qne qu eigu])
  qed
  have Mpq: "Mp q M *v q = min (eigval CARD('n) M) 0 *\<^sub>R q"
    by (rule Mp_apply_p[OF qne])
  have MB: "\<forall>u \<in> B - {q}. M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    using eigB by blast
  show ?thesis
    by (rule exI[of _ B]) (intro conjI B(1) B(2) qB restperp MB MpB Mpq)
qed

section \<open>The index shift of Eq. (3.6)\<close>

text \<open>A unit eigenvector attaining \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)\<close> exists: take the top-\<open>1\<close> threshold
  set of an eigenbasis.  This is the \<open>q\<^sub>1\<close> of the paper's sequence
  \<open>(q\<^sub>1/m, M)\<close>.\<close>

theorem kyfan_Mp_top_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and q: "norm q = 1"
    and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
    and top: "q \<bullet> (M *v q) = eigval 1 M"
    and j: "j \<le> CARD('n) - 1"
  shows "kyfan j (Mp q M) = kyfan (Suc j) M - eigval 1 M"
proof -
  have qne: "q \<noteq> 0"
    using q by auto
  have symMp: "transpose (Mp q M) = Mp q M"
    by (rule transpose_Mp[OF sym])
  obtain B where B: "onormal B" "span B = UNIV" and qB: "q \<in> B"
    and restperp: "\<forall>u \<in> B - {q}. q \<bullet> u = 0"
    and eigM: "\<forall>u \<in> B - {q}. M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    and eigMp: "\<forall>u \<in> B - {q}. Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    and Mpq: "Mp q M *v q = min (eigval CARD('n) M) 0 *\<^sub>R q"
    using Mp_eigenbasis_of_M_eigenvector[OF sym q eigq] by blast
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have qq: "q \<bullet> q = 1"
    using q by (simp add: dot_square_norm)
  text \<open>@{theory Symmetric_Matrix_Spectra.Ky_Fan}: \<open>M\<^sub>q\<close> agrees with \<open>M\<close> off \<open>q\<close> and carries
    \<open>min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close> at \<open>q\<close>.\<close>
  define lamM where "lamM = (\<lambda>u :: real^'n. u \<bullet> (M *v u))"
  define lamP where "lamP = (\<lambda>u :: real^'n. u \<bullet> (Mp q M *v u))"
  have eigMp': "Mp q M *v u = (u \<bullet> (Mp q M *v u)) *\<^sub>R u" if u: "u \<in> B" for u
  proof (cases "u = q")
    case True
    have "q \<bullet> (Mp q M *v q) = min (eigval CARD('n) M) 0"
      unfolding Mpq using qq by simp
    then show ?thesis
      unfolding True using Mpq by simp
  next
    case False
    then have "u \<in> B - {q}" using u by blast
    then have e: "Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u" using eigMp by blast
    moreover from e have "u \<bullet> (Mp q M *v u) = (u \<bullet> (M *v u)) * (u \<bullet> u)"
      by simp
    moreover have "u \<bullet> u = 1"
      using u B(1) by (simp add: onormal_def dot_square_norm)
    ultimately show ?thesis by simp
  qed
  have lamPq: "lamP q = min (eigval CARD('n) M) 0"
    unfolding lamP_def Mpq using qq by simp
  have lamP_eq: "lamP u = lamM u" if u: "u \<in> B - {q}" for u
  proof -
    have e: "Mp q M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
      using u eigMp by blast
    have "u \<bullet> u = 1"
      using u B(1) by (simp add: onormal_def dot_square_norm)
    then show ?thesis
      unfolding lamP_def lamM_def using e by simp
  qed
  text \<open>\<open>q\<close> is minimal for \<open>M\<^sub>q\<close> and maximal for \<open>M\<close>.\<close>
  have lamP_min: "lamP q \<le> lamP u" if u: "u \<in> B - {q}" for u
  proof -
    have nu: "norm u = 1"
      using u B(1) by (simp add: onormal_def)
    have qu: "q \<bullet> u = 0"
      using u restperp by blast
    have lu: "lamP u = u \<bullet> (Mp q M *v u)"
      unfolding lamP_def by (rule refl)
    have "min (eigval CARD('n) M) 0 \<le> u \<bullet> (Mp q M *v u)"
      by (rule Mp_perp_quadform_ge[OF sym qne qu nu])
    then show ?thesis
      unfolding lamPq lu .
  qed
  have lamM_max: "lamM u \<le> lamM q" if u: "u \<in> B" for u
  proof -
    have nu: "norm u = 1"
      using u B(1) by (simp add: onormal_def)
    have "u \<bullet> (M *v u) \<le> eigval 1 M"
      by (rule quadform_le_eigval_1[OF sym nu])
    then show ?thesis
      unfolding lamM_def using top by simp
  qed
  text \<open>Choose a top-\<open>j\<close> threshold set inside \<open>B - {q}\<close>.\<close>
  have finB': "finite (B - {q})"
    using finB by simp
  have cardB': "card (B - {q}) = CARD('n) - 1"
    using qB finB cardB by (simp add: card_Diff_singleton)
  have jB': "j \<le> card (B - {q})"
    using j cardB' by simp
  obtain T where T: "T \<subseteq> B - {q}" "card T = j"
    and thresh': "\<And>u v. u \<in> T \<Longrightarrow> v \<in> (B - {q}) - T \<Longrightarrow> lamM v \<le> lamM u"
    using exists_top_subset[where f = lamM, OF finB' jB'] by metis
  have TB: "T \<subseteq> B"
    using T(1) by blast
  have qnotT: "q \<notin> T"
    using T(1) by blast
  have finT: "finite T"
    using TB finB by (rule finite_subset)
  text \<open>\<open>T\<close> is a threshold set for \<open>M\<^sub>q\<close> on all of \<open>B\<close>, since \<open>q\<close> is minimal.\<close>
  have threshP: "lamP v \<le> lamP u" if u: "u \<in> T" and v: "v \<in> B - T" for u v
  proof (cases "v = q")
    case True
    have "u \<in> B - {q}" using u T(1) by blast
    then show ?thesis unfolding True by (rule lamP_min)
  next
    case False
    then have vBq: "v \<in> (B - {q}) - T" using v by blast
    have "lamM v \<le> lamM u" by (rule thresh'[OF u vBq])
    moreover have "lamP v = lamM v" using vBq by (intro lamP_eq) blast
    moreover have "lamP u = lamM u" using u T(1) by (intro lamP_eq) blast
    ultimately show ?thesis by simp
  qed
  text \<open>\<open>insert q T\<close> is a threshold set for \<open>M\<close>, since \<open>q\<close> is maximal.\<close>
  have threshM: "lamM v \<le> lamM u"
    if u: "u \<in> insert q T" and v: "v \<in> B - insert q T" for u v
  proof (cases "u = q")
    case True
    show ?thesis unfolding True using v by (intro lamM_max) blast
  next
    case False
    then have uT: "u \<in> T" using u by simp
    have "v \<in> (B - {q}) - T" using v by blast
    then show ?thesis by (rule thresh'[OF uT])
  qed
  have cardqT: "card (insert q T) = Suc j"
    using qnotT finT T(2) by simp
  have qTB: "insert q T \<subseteq> B"
    using qB TB by blast
  text \<open>Evaluate both Ky Fan sums on their threshold sets.\<close>
  have kP: "kyfan j (Mp q M) = (\<Sum>u\<in>T. lamP u)"
    unfolding lamP_def
    by (rule kyfan_threshold[OF B symMp eigMp' TB T(2) threshP[unfolded lamP_def]])
  have kM: "kyfan (Suc j) M = (\<Sum>u\<in>insert q T. lamM u)"
    unfolding lamM_def
    by (rule kyfan_threshold[OF B sym _ qTB cardqT threshM[unfolded lamM_def]])
      (use eigM eigq in blast)
  have "kyfan (Suc j) M = lamM q + (\<Sum>u\<in>T. lamM u)"
    unfolding kM using qnotT finT by simp
  also have "\<dots> = eigval 1 M + (\<Sum>u\<in>T. lamP u)"
  proof -
    have "lamM q = eigval 1 M"
      unfolding lamM_def by (rule top)
    moreover have "(\<Sum>u\<in>T. lamM u) = (\<Sum>u\<in>T. lamP u)"
      using T(1) by (intro sum.cong refl) (metis lamP_eq subsetD)
    ultimately show ?thesis by simp
  qed
  finally have "kyfan (Suc j) M = eigval 1 M + kyfan j (Mp q M)"
    unfolding kP by simp
  then show ?thesis by simp
qed

text \<open>Hence the ordered eigenvalues themselves shift: \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>q\<^sub>1) = \<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close>
  for \<open>i = 1, \<dots>, n-1\<close>.  The paper only needs the inequality (Poincare
  separation); with \<open>q\<^sub>1\<close> an eigenvector it is an equality, which is why
  evaluating at \<open>(q\<^sub>1/m, M)\<close> gives the matching bound.\<close>

corollary eigval_Mp_top_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and q: "norm q = 1"
    and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
    and top: "q \<bullet> (M *v q) = eigval 1 M"
    and i: "1 \<le> i" "i \<le> CARD('n) - 1"
  shows "eigval i (Mp q M) = eigval (Suc i) M"
proof -
  have i1: "i - 1 \<le> CARD('n) - 1"
    using i(2) by simp
  have si: "Suc (i - 1) = i"
    using i(1) by simp
  have a: "kyfan i (Mp q M) = kyfan (Suc i) M - eigval 1 M"
    by (rule kyfan_Mp_top_eigenvector[OF sym q eigq top i(2)])
  have b: "kyfan (i - 1) (Mp q M) = kyfan i M - eigval 1 M"
    using kyfan_Mp_top_eigenvector[OF sym q eigq top i1] si by simp
  have "eigval i (Mp q M) = kyfan i (Mp q M) - kyfan (i - 1) (Mp q M)"
    unfolding eigval_def by (rule refl)
  also have "\<dots> = kyfan (Suc i) M - kyfan i M"
    unfolding a b by simp
  also have "\<dots> = eigval (Suc i) M"
    unfolding eigval_def by simp
  finally show ?thesis .
qed

text \<open>The smallest eigenvalue of \<open>M\<^sub>q\<close> is nonpositive, because \<open>M\<^sub>q\<close> carries
  \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0) \<le> 0\<close> in the \<open>q\<close>-direction.  That is all Eq. (3.6) needs of
  it: the last eigenvalue contributes nothing to the positive part.\<close>

lemma eigval_Mp_last_nonpos:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and q: "norm q = 1"
  shows "eigval CARD('n) (Mp q M) \<le> 0"
proof -
  have qne: "q \<noteq> 0"
    using q by auto
  have symMp: "transpose (Mp q M) = Mp q M"
    by (rule transpose_Mp[OF sym])
  have "eigval CARD('n) (Mp q M) \<le> q \<bullet> (Mp q M *v q)"
    by (rule eigval_min_le_quadform[OF symMp q])
  also have "\<dots> = min (eigval CARD('n) M) 0"
  proof -
    have "q /\<^sub>R norm q = q"
      using q by simp
    then show ?thesis
      using Mp_quadform_unit_p[OF qne] by simp
  qed
  also have "\<dots> \<le> 0"
    by simp
  finally show ?thesis .
qed

text \<open>Putting the shift and sign together: the bracket of \<open>M\<^sub>q\<^sub>1\<close> is the
  bracket of \<open>M\<close> with every index moved up by one, the positive part
  running \<open>i = 2, \<dots>, n\<close> and the negative part \<open>i = 2, \<dots>, n-k+1\<close>: the right
  hand side of Eq. (3.6).\<close>

theorem bracket_Mp_top_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and q: "norm q = 1"
    and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
    and top: "q \<bullet> (M *v q) = eigval 1 M"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "bracket (CARD('n) - k) L (Mp q M)
       = L * (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
         + (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)"
proof -
  have symMp: "transpose (Mp q M) = Mp q M"
    by (rule transpose_Mp[OF sym])
  obtain n' where n': "CARD('n) = Suc n'"
    using not0_implies_Suc[of "CARD('n)"] by auto
  have shift: "eigval i (Mp q M) = eigval (Suc i) M" if "1 \<le> i" "i \<le> n'" for i
    by (rule eigval_Mp_top_eigenvector[OF sym q eigq top that(1)]) (use that n' in simp)
  have last: "max (eigval (Suc n') (Mp q M)) 0 = 0"
    using eigval_Mp_last_nonpos[OF sym q] n' by simp
  have pos: "(\<Sum>i\<in>{1..CARD('n)}. max (eigval i (Mp q M)) 0)
      = (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)"
  proof -
    have "(\<Sum>i\<in>{1..Suc n'}. max (eigval i (Mp q M)) 0)
        = (\<Sum>i\<in>{1..n'}. max (eigval i (Mp q M)) 0)"
      using last by (simp add: atLeastAtMostSuc_conv)
    also have "\<dots> = (\<Sum>i\<in>{1..n'}. max (eigval (Suc i) M) 0)"
      by (intro sum.cong refl) (simp add: shift)
    also have "\<dots> = (\<Sum>i\<in>{2..Suc n'}. max (eigval i M) 0)"
      by (rule sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc]) auto
    finally show ?thesis
      unfolding n' .
  qed
  have neg: "(\<Sum>i\<in>{1..CARD('n) - k}. min (eigval i (Mp q M)) 0)
      = (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)"
  proof -
    have "(\<Sum>i\<in>{1..CARD('n) - k}. min (eigval i (Mp q M)) 0)
        = (\<Sum>i\<in>{1..CARD('n) - k}. min (eigval (Suc i) M) 0)"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {1..CARD('n) - k}"
      then have "1 \<le> i" "i \<le> n'"
        using k n' by auto
      then show "min (eigval i (Mp q M)) 0 = min (eigval (Suc i) M) 0"
        by (simp add: shift)
    qed
    also have "\<dots> = (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)"
      by (rule sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc]) auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding bracket_eq_sum[OF symMp diff_le_self] pos neg ..
qed

text \<open>The value of \<open>F\<close> along the paper's sequence \<open>(q\<^sub>1/m, M)\<close>: by scale
  invariance it is constant in \<open>m\<close> and equals the right hand side of
  Eq. (3.6), giving the lower bound for \<open>F\<^sup>*(0, M)\<close> since \<open>q\<^sub>1/m \<longrightarrow> 0\<close>.\<close>

corollary ell_op_at_top_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and q: "norm q = 1"
    and eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
    and top: "q \<bullet> (M *v q) = eigval 1 M"
    and L: "1 \<le> L" and k: "1 \<le> k" "k < CARD('n)"
    and c: "0 < c"
  shows "ell_op k L (c *\<^sub>R q) M
       = - (1/2) * (L * (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
           + (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0))"
proof -
  have qne: "q \<noteq> 0"
    using q by auto
  have "ell_op k L (c *\<^sub>R q) M = ell_op k L q M"
    by (rule ell_op_scaleR_dir[OF sym c qne L k(1) k(2)])
  also have "\<dots> = - (1/2) * bracket (CARD('n) - k) L (Mp q M)"
    by (rule ell_op_eq_half_bracket[OF sym qne L k(1) k(2)])
  also have "\<dots> = - (1/2) * (L * (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
      + (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0))"
    by (simp add: bracket_Mp_top_eigenvector[OF sym q eigq top k(1) k(2)])
  finally show ?thesis .
qed

section \<open>General Poincare separation\<close>

text \<open>The paper's inequality \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>)(M\<^sub>p) \<ge> \<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close> for arbitrary
  \<open>p \<noteq> 0\<close>, by a dimension count: the span \<open>S\<close> of the top \<open>i+1\<close>
  eigenvectors of \<open>M\<close> and the hyperplane \<open>p\<^sup>\<bottom>\<close> have dimensions \<open>i+1\<close> and
  \<open>n-1\<close>, so their intersection has dimension \<open>\<ge> i\<close>, where the Rayleigh
  quotients of \<open>M\<^sub>p\<close> and \<open>M\<close> agree.\<close>

theorem poincare_separation:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
    and i: "1 \<le> i" "i < CARD('n)"
  shows "eigval (Suc i) M \<le> eigval i (Mp p M)"
proof -
  have symMp: "transpose (Mp p M) = Mp p M"
    by (rule transpose_Mp[OF sym])
  obtain B where B: "onormal B" "span B = UNIV"
    and finB: "finite B" and cardB: "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    using symmetric_eigendecomposition[OF sym] by metis
  have siB: "Suc i \<le> card B"
    using i(2) cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = Suc i"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T
        \<Longrightarrow> v \<bullet> (M *v v) \<le> u \<bullet> (M *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (M *v u)", OF finB siB]
    by metis
  have onT: "onormal T"
    by (rule onormal_subset[OF B(1) T(1)])
  define S where "S = span T"
  define W where "W = {y :: real^'n. p \<bullet> y = 0}"
  have subS: "subspace S"
    unfolding S_def by (rule subspace_span)
  have subW: "subspace W"
    unfolding W_def by (simp add: subspace_hyperplane)
  have dimS: "dim S = Suc i"
    unfolding S_def using onormal_card_dim_span[OF onT] T(2) by simp
  have dimW: "dim W = CARD('n) - 1"
    unfolding W_def using p by (simp add: dim_hyperplane)
  text \<open>The dimension count.\<close>
  have dimSW: "i \<le> dim (S \<inter> W)"
  proof -
    have "dim S + dim W \<le> dim (S \<inter> W) + CARD('n)"
      by (rule dim_inter_ge[OF subS subW])
    then have "Suc i + (CARD('n) - 1) \<le> dim (S \<inter> W) + CARD('n)"
      unfolding dimS dimW by simp
    then show ?thesis
      using i(2) by simp
  qed
  have subSW: "subspace (S \<inter> W)"
    using subS subW by (auto simp: subspace_def)
  text \<open>On \<open>S \<inter> W\<close> the Rayleigh quotient of \<open>M\<^sub>p\<close> is that of \<open>M\<close>, and is at
    least \<open>\<lambda>\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>)(M)\<close>.\<close>
  have quad: "eigval (Suc i) M * (x \<bullet> x) \<le> x \<bullet> (Mp p M *v x)"
    if x: "x \<in> S \<inter> W" for x
  proof -
    have xS: "x \<in> span T"
      using x unfolding S_def by blast
    have xW: "p \<bullet> x = 0"
      using x unfolding W_def by blast
    have si0: "0 < Suc i"
      by simp
    have "eigval (Suc i) M * (x \<bullet> x) \<le> x \<bullet> (M *v x)"
      by (rule quadform_ge_on_span_threshold[OF B sym eig T(1) T(2) si0 thresh xS])
    also have "\<dots> = x \<bullet> (Mp p M *v x)"
      by (rule Mp_quadform_perp[OF p xW, symmetric])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule eigval_ge_of_subspace[OF symMp subSW dimSW quad])
      (use i in auto)
qed

text \<open>Uniformly in \<open>p\<close>, including \<open>p = 0\<close> where \<open>M\<^sub>0 = M\<close> and the shift is just
  the monotonicity of the ordered eigenvalues.\<close>

lemma eigval_Mp_ge_shift:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and i: "1 \<le> i" "i < CARD('n)"
  shows "eigval (Suc i) M \<le> eigval i (Mp p M)"
proof (cases "p = 0")
  case True
  have "Suc i \<le> CARD('n)"
    using i(2) by simp
  then show ?thesis
    unfolding True using eigval_antimono[OF sym i(1)] by simp
next
  case False
  then show ?thesis
    by (rule poincare_separation[OF sym _ i(1) i(2)])
qed

text \<open>Hence the bracket of \<open>M\<^sub>p\<close> always dominates the shifted bracket of \<open>M\<close>,
  which, since \<open>F = -\<onehalf> bracket\<close>, is the upper bound \<open>F(p, M) \<le> eq36_rhs\<close>
  needed for Eq. (3.6).\<close>

theorem bracket_ge_shifted:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "L * (\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
         + (\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)
       \<le> bracket (CARD('n) - k) L (Mp p M)"
proof -
  define N where "N = Mp p M"
  have symN: "transpose N = N"
    unfolding N_def by (rule transpose_Mp[OF sym])
  obtain n' where n': "CARD('n) = Suc n'"
    using not0_implies_Suc[of "CARD('n)"] by auto
  have shift: "eigval (Suc i) M \<le> eigval i N" if "1 \<le> i" "i \<le> n'" for i
    unfolding N_def by (rule eigval_Mp_ge_shift[OF sym that(1)]) (use that n' in simp)
  have pos: "(\<Sum>i\<in>{2..CARD('n)}. max (eigval i M) 0)
      \<le> (\<Sum>i\<in>{1..CARD('n)}. max (eigval i N) 0)"
  proof -
    have "(\<Sum>i\<in>{2..Suc n'}. max (eigval i M) 0)
        = (\<Sum>i\<in>{1..n'}. max (eigval (Suc i) M) 0)"
      by (rule sum.reindex_bij_witness[where i = Suc and j = "\<lambda>i. i - 1"]) auto
    also have "\<dots> \<le> (\<Sum>i\<in>{1..n'}. max (eigval i N) 0)"
      by (intro sum_mono max.mono order_refl shift) auto
    also have "\<dots> \<le> (\<Sum>i\<in>{1..Suc n'}. max (eigval i N) 0)"
      by (intro sum_mono2) auto
    finally show ?thesis
      unfolding n' .
  qed
  have neg: "(\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)
      \<le> (\<Sum>i\<in>{1..CARD('n) - k}. min (eigval i N) 0)"
  proof -
    have "(\<Sum>i\<in>{2..CARD('n) - k + 1}. min (eigval i M) 0)
        = (\<Sum>i\<in>{1..CARD('n) - k}. min (eigval (Suc i) M) 0)"
      by (rule sum.reindex_bij_witness[where i = Suc and j = "\<lambda>i. i - 1"]) auto
    also have "\<dots> \<le> (\<Sum>i\<in>{1..CARD('n) - k}. min (eigval i N) 0)"
      using k n' by (intro sum_mono min.mono order_refl shift) auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding N_def[symmetric] bracket_eq_sum[OF symN diff_le_self]
    using pos neg L by (intro add_mono mult_left_mono) auto
qed

section \<open>Continuity of the bracket in the matrix\<close>

text \<open>By Eq. (3.5), \<open>F\<close> is \<open>-\<onehalf> bracket (n-k) L M\<^sub>p\<close>, so the first clause
  of Lemma 3.1 (\<open>F\<^sub>* = F\<^sup>* = F\<close> off \<open>p = 0\<close>) needs \<open>bracket\<close> continuous in
  its matrix argument, and \<open>(p, M) \<mapsto> M\<^sub>p\<close> continuous off \<open>p = 0\<close>.  The
  first is Lipschitz, from \<open>kyfan_lipschitz\<close>.\<close>

section \<open>\<open>F\<close> only sees the symmetric part of \<open>M\<close>\<close>

text \<open>Every feasible \<open>a\<close> is symmetric, and against a symmetric \<open>a\<close> the trace
  pairing cannot distinguish \<open>M\<close> from \<open>transpose M\<close>.  So \<open>F(p, M)\<close> depends
  only on \<open>sym M = \<onehalf>(M + M\<^sup>\<top>)\<close>, letting nearby non-symmetric matrices be
  handled by results assuming symmetry.\<close>

text \<open>Consequently Eq. (3.5) holds for an arbitrary \<open>M\<close>, symmetric or not,
  with \<open>M\<close> replaced by its symmetric part on the right hand side.\<close>

section \<open>The Frobenius norm: transpose invariance and submultiplicativity\<close>

text \<open>The last two tools for the continuity clause of Lemma 3.1:
  \<open>norm (A ** B) \<le> norm A * norm B\<close>, and that the Frobenius norm inherited
  on \<open>real^'n^'n\<close> satisfies it; neither is in this HOL-Analysis.\<close>

section \<open>The conjugation expansion, and the Lipschitz bound for \<open>M\<^sub>p\<close>\<close>

text \<open>Towards continuity of \<open>(p, M) \<mapsto> M\<^sub>p\<close> off \<open>p = 0\<close>.  The correction
  coefficient \<open>min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close> does not depend on \<open>p\<close>, so the only
  \<open>p\<close>-dependence is through \<open>rank1proj p\<close>, reducing to an estimate on
  \<open>norm (rank1proj p' - rank1proj p)\<close>.  Since \<open>rank1proj p = outer_prod q q\<close>
  with \<open>q = p/|p|\<close> a unit vector, and the normalisation map is Lipschitz with
  constant \<open>2/|p|\<close> away from the origin, the estimate has constant \<open>4/|p|\<close>,
  blowing up as \<open>p \<rightarrow> 0\<close>, why Eq. (3.6) differs there.  The estimate,
  @{thm [source] norm_rank1proj_diff_le}, and the two constants that turn the
  toolkit into an explicit Lipschitz constant for \<open>(p, M) \<mapsto> M\<^sub>p\<close>,
  @{thm [source] norm_rank1proj} and @{thm [source] norm_perp_proj_le}, are in
  @{theory Symmetric_Matrix_Spectra.Orthogonal_Projections}.\<close>

text \<open>Perturbing the projection expands the conjugation into four terms.  With
  \<open>Q = I - rank1proj p\<close> and \<open>D = rank1proj p' - rank1proj p\<close>,
  \<open>I - rank1proj p' = Q - D\<close>, giving \<open>M\<^sub>p\<^sub>' - M\<^sub>p\<close> up to a correction
  \<open>c *\<^sub>R D\<close>, since \<open>c = min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close> does not depend on \<open>p\<close>.\<close>

theorem norm_Mp_diff_le:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0" and p': "p' \<noteq> 0"
  shows "norm (Mp p' M - Mp p M)
       \<le> (2 * (sqrt (real CARD('n)) + 1) * norm M + 2 * norm M
          + \<bar>min (eigval CARD('n) M) 0\<bar>) * norm (rank1proj p' - rank1proj p)"
proof -
  define P where "P = (rank1proj p :: real^'n^'n)"
  define Q where "Q = (mat 1 - P :: real^'n^'n)"
  define D where "D = (rank1proj p' - P :: real^'n^'n)"
  define c where "c = min (eigval CARD('n) M) 0"
  have QD: "(mat 1 - rank1proj p' :: real^'n^'n) = Q - D"
    unfolding Q_def D_def by simp
  have nP: "norm P = 1"
    unfolding P_def by (rule norm_rank1proj[OF p])
  have nP': "norm (rank1proj p' :: real^'n^'n) = 1"
    by (rule norm_rank1proj[OF p'])
  have nQ: "norm Q \<le> sqrt (real CARD('n)) + 1"
    unfolding Q_def P_def by (rule norm_perp_proj_le[OF p])
  have nD: "norm D \<le> 2"
  proof -
    have "norm D \<le> norm (rank1proj p' :: real^'n^'n) + norm P"
      unfolding D_def by (rule norm_triangle_ineq4)
    then show ?thesis
      using nP nP' by simp
  qed
  have nD0: "0 \<le> norm D"
    by (rule norm_ge_zero)
  have nM0: "0 \<le> norm M"
    by (rule norm_ge_zero)
  have Mp1: "Mp p M = Q ** M ** Q + c *\<^sub>R P"
    unfolding Mp_def Q_def P_def c_def using p by simp
  have Mp2: "Mp p' M = (Q - D) ** M ** (Q - D) + c *\<^sub>R rank1proj p'"
    unfolding Mp_def c_def using p' by (simp add: QD)
  have diff: "Mp p' M - Mp p M
      = ((Q - D) ** M ** (Q - D) - Q ** M ** Q) + c *\<^sub>R D"
    unfolding Mp1 Mp2 D_def by (simp add: scaleR_right_diff_distrib)
  have "norm (Mp p' M - Mp p M)
      \<le> norm ((Q - D) ** M ** (Q - D) - Q ** M ** Q) + norm (c *\<^sub>R D)"
    unfolding diff by (rule norm_triangle_ineq)
  also have "\<dots> \<le> (2 * norm Q * norm M * norm D + norm M * norm D * norm D)
      + \<bar>c\<bar> * norm D"
    using norm_conj_diff_le[where M = M and Q = Q and D = D] by simp
  also have "\<dots> \<le> (2 * (sqrt (real CARD('n)) + 1) * norm M + 2 * norm M + \<bar>c\<bar>)
      * norm D"
  proof -
    have t1: "2 * norm Q * norm M * norm D
        \<le> 2 * (sqrt (real CARD('n)) + 1) * norm M * norm D"
      using nQ nM0 nD0 by (simp add: mult_right_mono mult_left_mono)
    have t2: "norm M * norm D * norm D \<le> 2 * norm M * norm D"
    proof -
      have "norm M * norm D * norm D \<le> norm M * norm D * 2"
        by (rule mult_left_mono[OF nD]) simp
      then show ?thesis
        by (simp add: algebra_simps)
    qed
    show ?thesis
      using t1 t2 by (simp add: algebra_simps)
  qed
  finally show ?thesis
    unfolding D_def P_def c_def .
qed

text \<open>Chaining the two Lipschitz bounds: \<open>M\<^sub>p\<close> is Lipschitz in \<open>p\<close> on any set
  bounded away from the origin.  Written with an existential constant, which is
  all a continuity argument needs.\<close>

theorem Mp_lipschitz_away_from_zero:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes p: "p \<noteq> 0"
  shows "\<exists>C. 0 < C \<and> (\<forall>p'. p' \<noteq> 0
      \<longrightarrow> norm (Mp p' M - Mp p M) \<le> C * norm (p' - p))"
proof -
  define K where "K = 2 * (sqrt (real CARD('n)) + 1) * norm M + 2 * norm M
      + \<bar>min (eigval CARD('n) M) 0\<bar> + 1"
  have K0: "0 < K"
  proof -
    have "0 \<le> 2 * (sqrt (real CARD('n)) + 1) * norm M"
      by simp
    moreover have "0 \<le> 2 * norm M"
      by simp
    moreover have "0 \<le> \<bar>min (eigval CARD('n) M) 0\<bar>"
      by simp
    ultimately show ?thesis
      unfolding K_def by linarith
  qed
  have np: "0 < norm p"
    using p by simp
  define C where "C = K * (4 / norm p)"
  have C0: "0 < C"
    unfolding C_def using K0 np by simp
  show ?thesis
  proof (intro exI[of _ C] conjI allI impI C0)
    fix p' :: "real^'n"
    assume p': "p' \<noteq> 0"
    have step1: "norm (Mp p' M - Mp p M)
        \<le> (2 * (sqrt (real CARD('n)) + 1) * norm M + 2 * norm M
           + \<bar>min (eigval CARD('n) M) 0\<bar>)
          * norm (rank1proj p' - rank1proj p)"
      by (rule norm_Mp_diff_le[OF p p'])
    have step2: "norm (rank1proj p' - rank1proj p)
        \<le> 4 * norm (p' - p) / norm p"
      by (rule norm_rank1proj_diff_le[OF p p'])
    have Kge: "2 * (sqrt (real CARD('n)) + 1) * norm M + 2 * norm M
        + \<bar>min (eigval CARD('n) M) 0\<bar> \<le> K"
      unfolding K_def by simp
    have nn: "0 \<le> norm (rank1proj p' - rank1proj p)"
      by (rule norm_ge_zero)
    have "norm (Mp p' M - Mp p M)
        \<le> K * norm (rank1proj p' - rank1proj p)"
      using step1 mult_right_mono[OF Kge nn] by simp
    also have "\<dots> \<le> K * (4 * norm (p' - p) / norm p)"
      by (rule mult_left_mono[OF step2]) (use K0 in simp)
    also have "\<dots> = C * norm (p' - p)"
      unfolding C_def by simp
    finally show "norm (Mp p' M - Mp p M) \<le> C * norm (p' - p)" .
  qed
qed

section \<open>A rank obstruction: the deterministic core of Lemma 5.3\<close>

text \<open>Lemma 5.3 characterises \<open>v(x) = 0\<close>, for convex \<open>K\<close>, by
  \<open>dim F\<^sub>x \<le> n - k\<close>, the dimension of the face \<open>F\<^sub>x\<close> containing \<open>x\<close> in its
  relative interior.  A covariance matrix degenerate on \<open>W\<close> cannot satisfy
  \<open>eigen_lb a m\<close> unless \<open>m + dim W \<le> n\<close>; applied to \<open>F\<^sub>x\<close>'s normal
  directions this gives the \<open>v(x) = 0\<close> side.\<close>

text \<open>The form used on a face: if the degeneracy subspace is more than
  \<open>k\<close>-dimensional, no feasible covariance exists at all.\<close>

section \<open>From the Lipschitz bounds to the norm topology\<close>

text \<open>\<open>bracket_lipschitz\<close> and \<open>eigval_lipschitz\<close> are stated via \<open>entrysum\<close>;
  a topological continuity argument needs the norm instead.  The entrywise
  bound \<open>\<bar>D $ i $ j\<bar> \<le> norm D\<close> converts them, at the cost of a factor
  \<open>n\<^sup>2\<close>.\<close>

section \<open>Continuity of \<open>F\<close> away from \<open>p = 0\<close>\<close>

text \<open>Eq. (3.5) and Eq. (3.6) are proved (\<open>ell_op_eq_half_bracket\<close> here,
  \<open>eq36\<close> in \<open>Operator_Envelope_Continuity\<close>.thy), as is the general Poincare separation
  inequality (\<open>poincare_separation\<close>).  The remaining clause of Lemma 3.1,
  \<open>F\<^sub>* = F\<^sup>* = F\<close> on \<open>(\<real>\<^sup>n \ {0}) \<times> \<S>\<^sup>n\<close>, is continuity of \<open>F\<close> away from
  \<open>p = 0\<close>.  Writing \<open>F(p, M) = -\<onehalf> bracket (n-k) L (M\<^sub>p)\<close> with \<open>M\<close> replaced
  by its symmetric part, this reduces to the Lipschitz bounds on \<open>bracket\<close>
  and on \<open>(p, M) \<mapsto> M\<^sub>p\<close> established above.\<close>

text \<open>The estimate on \<open>F\<close> itself: for symmetric \<open>M\<close> and \<open>p \<noteq> 0\<close>,
  \<open>p' \<mapsto> F(p', M)\<close> is Lipschitz near \<open>p\<close>.  Combined with \<open>ell_op_M_gap\<close>
  (\<open>Operator_Envelopes\<close>), which absorbs the variation of the second argument, both
  semicontinuous envelopes collapse onto \<open>F\<close> off the origin.\<close>

theorem ell_op_lipschitz_in_p:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "\<exists>C. 0 < C \<and> (\<forall>p'. p' \<noteq> 0
      \<longrightarrow> \<bar>ell_op k L p' M - ell_op k L p M\<bar> \<le> C * norm (p' - p))"
proof -
  define E where "E = (L + 2) * real CARD('n) * real (CARD('n) * CARD('n))"
  have E0: "0 \<le> E"
    unfolding E_def using L by simp
  obtain C0 where C0: "0 < C0"
    and lip: "\<And>p'. p' \<noteq> 0 \<Longrightarrow> norm (Mp p' M - Mp p M) \<le> C0 * norm (p' - p)"
    using Mp_lipschitz_away_from_zero[of p M] p by blast
  define C where "C = E * C0 / 2 + 1"
  have EC: "0 \<le> E * C0"
    by (rule mult_nonneg_nonneg[OF E0]) (use C0 in simp)
  have C0': "0 < C"
    unfolding C_def using EC by simp
  show ?thesis
  proof (intro exI[of _ C] conjI allI impI C0')
    fix p' :: "real^'n"
    assume p': "p' \<noteq> 0"
    have symMp: "transpose (Mp p M) = Mp p M"
      by (rule transpose_Mp[OF sym])
    have symMp': "transpose (Mp p' M) = Mp p' M"
      by (rule transpose_Mp[OF sym])
    have mn: "CARD('n) - k \<le> CARD('n)"
      by simp
    have L0: "0 \<le> L"
      using L by simp
    have e1: "ell_op k L p' M
        = - (1/2) * bracket (CARD('n) - k) L (Mp p' M)"
      by (rule ell_op_eq_half_bracket[OF sym p' L k(1) k(2)])
    have e2: "ell_op k L p M
        = - (1/2) * bracket (CARD('n) - k) L (Mp p M)"
      by (rule ell_op_eq_half_bracket[OF sym p L k(1) k(2)])
    have br: "\<bar>bracket (CARD('n) - k) L (Mp p' M)
        - bracket (CARD('n) - k) L (Mp p M)\<bar>
        \<le> E * norm (Mp p' M - Mp p M)"
      unfolding E_def
      by (rule bracket_lipschitz_norm[OF symMp' symMp mn L0])
    have eqd: "ell_op k L p' M - ell_op k L p M
        = - (1/2) * (bracket (CARD('n) - k) L (Mp p' M)
            - bracket (CARD('n) - k) L (Mp p M))"
      unfolding e1 e2 by (simp add: algebra_simps)
    have "\<bar>ell_op k L p' M - ell_op k L p M\<bar>
        = (1/2) * \<bar>bracket (CARD('n) - k) L (Mp p' M)
            - bracket (CARD('n) - k) L (Mp p M)\<bar>"
      unfolding eqd by (simp add: abs_mult)
    also have "\<dots> \<le> (1/2) * (E * norm (Mp p' M - Mp p M))"
      using br by simp
    also have "\<dots> \<le> (1/2) * (E * (C0 * norm (p' - p)))"
      using lip[OF p'] E0 by (simp add: mult_left_mono)
    also have "\<dots> = (E * C0 / 2) * norm (p' - p)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> C * norm (p' - p)"
    proof (rule mult_right_mono)
      show "E * C0 / 2 \<le> C"
        unfolding C_def by simp
      show "0 \<le> norm (p' - p)"
        by (rule norm_ge_zero)
    qed
    finally show "\<bar>ell_op k L p' M - ell_op k L p M\<bar> \<le> C * norm (p' - p)" .
  qed
qed

section \<open>\<open>eigen_lb\<close> as an eigenvalue condition\<close>

text \<open>\<open>eigen_lb a m\<close>, an existential over subspaces, is equivalent to the
  single inequality \<open>1 \<le> eigval m a\<close>; since \<open>eigval m\<close> is Lipschitz in \<open>a\<close>
  (\<open>eigval_lipschitz\<close>), this form is visibly closed, as Lemma 2.3's
  compactness requirement needs.  \<open>eigval_ge_of_eigen_lb\<close> gives one
  direction; for the other, the span of a top-\<open>m\<close> threshold set witnesses
  \<open>eigen_lb\<close>.\<close>

theorem eigen_lb_iff_eigval_ge:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and m: "0 < m" "m \<le> CARD('n)"
  shows "eigen_lb a m \<longleftrightarrow> 1 \<le> eigval m a"
proof
  assume "eigen_lb a m"
  then show "1 \<le> eigval m a"
    by (rule eigval_ge_of_eigen_lb[OF sym _ m(1) m(2)])
next
  assume ge: "1 \<le> eigval m a"
  obtain B where B: "onormal B" "span B = UNIV"
    and finB: "finite B" and cardB: "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigendecomposition[OF sym] by metis
  have mB: "m \<le> card B"
    using m(2) cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T
        \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finB mB]
    by metis
  have onT: "onormal T"
    by (rule onormal_subset[OF B(1) T(1)])
  show "eigen_lb a m"
    unfolding eigen_lb_def
  proof (intro exI[of _ "span T"] conjI)
    show "subspace (span T)"
      by (rule subspace_span)
    show "m \<le> dim (span T)"
      using onormal_card_dim_span[OF onT] T(2) by simp
    show "\<forall>x \<in> span T. x \<bullet> x \<le> x \<bullet> (a *v x)"
    proof (intro ballI)
      fix x assume x: "x \<in> span T"
      have nn: "0 \<le> x \<bullet> x"
        by simp
      have step1: "x \<bullet> x \<le> eigval m a * (x \<bullet> x)"
      proof -
        have "x \<bullet> x = 1 * (x \<bullet> x)"
          by simp
        also have "\<dots> \<le> eigval m a * (x \<bullet> x)"
          using ge nn by (rule mult_right_mono)
        finally show ?thesis .
      qed
      have step2: "eigval m a * (x \<bullet> x) \<le> x \<bullet> (a *v x)"
        by (rule quadform_ge_on_span_threshold[OF B sym eig T(1) T(2) m(1) thresh x])
      show "x \<bullet> x \<le> x \<bullet> (a *v x)"
        using step1 step2 by simp
    qed
  qed
qed

text \<open>Restated as the membership condition on the feasible set, which is the
  form Section 2 consumes.\<close>

corollary feasible_iff_eigval:
  fixes a :: "real^'n::finite^'n" and p :: "real^'n"
  assumes k: "1 \<le> k" "k < CARD('n)"
  shows "a \<in> feasible k L p \<longleftrightarrow>
      psd a \<and> a *v p = 0 \<and> 1 \<le> eigval (CARD('n) - k) a
      \<and> eigen_ub a L"
proof -
  have m0: "0 < CARD('n) - k"
    using k(2) by simp
  have mn: "CARD('n) - k \<le> CARD('n)"
    by simp
  have "psd a \<Longrightarrow> transpose a = a"
    by (simp add: psd_def)
  then show ?thesis
    unfolding feasible_def
    using eigen_lb_iff_eigval_ge[OF _ m0 mn] by blast
qed

section \<open>Closedness of the feasible set\<close>

text \<open>
  The feasible set of Eq. (1.9) is closed.  Three of its four conditions are
  continuous inequalities, closed outright; the eigenvalue lower bound is an
  existential over subspaces, but \<open>feasible_iff_eigval\<close> trades it for
  \<open>1 \<le> eigval (n-k) a\<close>, Lipschitz on symmetric matrices.  The entrywise
  bound \<open>feasible_entry_bound\<close> makes it bounded, hence compact.
\<close>

lemma closed_eigen_ub:
  "closed {a :: real^'n::finite^'n. eigen_ub a L}"
proof -
  have eq: "{a :: real^'n^'n. eigen_ub a L}
      = (\<Inter>x. {a. x \<bullet> (a *v x) \<le> L * (x \<bullet> x)})"
    unfolding eigen_ub_def by auto
  have "closed {a :: real^'n^'n. x \<bullet> (a *v x) \<le> L * (x \<bullet> x)}" for x
    by (intro closed_Collect_le continuous_on_quadform continuous_on_const)
  thus ?thesis unfolding eq by (intro closed_INT) auto
qed

(*<*)
end
(*>*)
