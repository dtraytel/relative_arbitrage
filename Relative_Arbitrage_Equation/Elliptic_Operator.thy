section \<open>The elliptic operator of Eq. (1.9)\<close>

(*<*)
theory Elliptic_Operator
  imports
    "Symmetric_Matrix_Spectra.Poincare_Separation"
begin

(*>*)

text \<open>
  The operator \<open>F\<close> of Eq. (1.9) of Lai, Shkolnikov and Soner
  \<^cite>\<open>LaiShkolnikovSoner\<close>,

    \<open>F(p, M) = Inf {- trace (M ** a) / 2 | a. psd a \<and> a *v p = 0
       \<and> eigen_lb a (n - k) \<and> eigen_ub a L}\<close>,

  with the spectral conditions expressed through their Courant--Fischer
  variational characterizations \<open>eigen_lb\<close> and \<open>eigen_ub\<close> rather than
  ordered eigenvalues, and the facts that need no more than its
  definition: \<open>F\<close> reads only the symmetric part of \<open>M\<close>, the feasible set
  contains the rank-\<open>(n - k)\<close> orthogonal projections onto subspaces of
  \<open>p\<^sup>\<bottom>\<close> and is bounded, so that \<open>F\<close> is a real infimum, and \<open>F\<close> is
  degenerate elliptic.\<close>

unbundle inner_syntax

subsection \<open>The constraint set and the operator\<close>

text \<open>
  Positive semidefinite symmetric matrices; the spectral constraints of
  Eq. (1.9) are expressed via their Courant--Fischer variational
  characterizations, which for symmetric matrices are equivalent to
  \<open>\<lambda>\<^sub>(\<^sub>m\<^sub>)(a) \<ge> 1\<close> and \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(a) \<le> L\<close>, respectively.
\<close>

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
      by (simp add: scalar_matrix_assoc[symmetric] matrix_add_rdistrib trace_add trace_scaleR
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
    using assms diag_eq_inner_axis[where a = a and i = l, symmetric] ax
    by (auto simp: eigen_ub_def dest: spec[of _ "axis l 1"])
qed

text \<open>For a psd matrix the eigenvalue cap bounds every entry: the diagonal
  by @{thm [source] eigen_ub_diag}, the off-diagonal by the psd inequality on
  \<open>axis i 1 \<plusminus> axis j 1\<close> (a two-sided form of Cauchy--Schwarz).  Hence
  it bounds the norm by \<open>n\<sqdot>L\<close>.\<close>

lemma psd_eigen_ub_entry_abs_le:
  fixes a :: "real^'n::finite^'n"
  assumes a: "psd a" and ub: "eigen_ub a L"
  shows "\<bar>a $ i $ j\<bar> \<le> L"
proof -
  have sym: "transpose a = a" using a by (simp add: psd_def)
  have psda: "0 \<le> x \<bullet> (a *v x)" for x using a by (simp add: psd_def)
  have "0 \<le> a $ i $ i + a $ j $ j + 2 * a $ i $ j"
    "0 \<le> a $ i $ i + a $ j $ j - 2 * a $ i $ j"
    using psda[of "axis i 1 + axis j 1"] psda[of "axis i 1 - axis j 1"]
    unfolding quadform_axis_pair[OF sym] quadform_axis_pair_minus[OF sym] .
  moreover have "a $ i $ i \<le> L" "a $ j $ j \<le> L" by (rule eigen_ub_diag[OF ub])+
  ultimately show ?thesis by linarith
qed

lemma psd_eigen_ub_norm_le:
  fixes a :: "real^'n::finite^'n"
  assumes a: "psd a" and ub: "eigen_ub a L" and L: "0 \<le> L"
  shows "norm a \<le> real CARD('n) * L"
proof -
  have "a \<bullet> a = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). \<bar>a $ i $ j\<bar> * \<bar>a $ i $ j\<bar>)"
    unfolding inner_vec_def by (simp add: abs_mult[symmetric])
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). L * L)"
    using psd_eigen_ub_entry_abs_le[OF a ub] L by (intro sum_mono mult_mono) auto
  also have "\<dots> = (real CARD('n) * L)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis
    using L by (simp add: norm_eq_sqrt_inner real_sqrt_le_iff')
qed

subsection \<open>Feasibility: projections onto \<open>(n-k)\<close>-dimensional subspaces of \<open>p\<^sup>\<bottom>\<close>\<close>

text \<open>The outer-product sum of an orthonormal family \<open>T\<close> is the orthogonal
  projection onto \<open>span T\<close>: positive semidefinite, with \<open>card T\<close> eigenvalues
  at least \<open>1\<close>, all eigenvalues at most \<open>1\<close>, and trace \<open>card T\<close>.\<close>

lemma onormal_outer_sum_props:
  fixes T :: "(real^'n) set"
  assumes T: "onormal T"
  shows "psd (\<Sum>u\<in>T. outer_prod u u)"
    and "eigen_lb (\<Sum>u\<in>T. outer_prod u u) (card T)"
    and "eigen_ub (\<Sum>u\<in>T. outer_prod u u) 1"
    and "trace (\<Sum>u\<in>T. outer_prod u u) = card T"
proof -
  have quad: "x \<bullet> ((\<Sum>u\<in>T. outer_prod u u) *v x) = (\<Sum>u\<in>T. (u \<bullet> x)\<^sup>2)" for x
    by (simp add: matrix_vector_mult_sum inner_sum_right power2_eq_square inner_commute)
  show "psd (\<Sum>u\<in>T. outer_prod u u)"
    unfolding psd_def by (simp add: quad transpose_matrix_sum sum_nonneg)
  show "eigen_lb (\<Sum>u\<in>T. outer_prod u u) (card T)"
    unfolding eigen_lb_def
    by (intro exI[of _ "span T"])
      (simp add: quad onormal_span_parseval[OF T] onormal_card_dim_span[OF T])
  show "eigen_ub (\<Sum>u\<in>T. outer_prod u u) 1"
    unfolding eigen_ub_def by (simp add: quad onormal_bessel[OF T])
  show "trace (\<Sum>u\<in>T. outer_prod u u) = card T"
    using T by (simp add: trace_matrix_sum)
qed

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
    by (cases "p = 0") (simp_all add: H_def dim_hyperplane)
  obtain B where B: "B \<subseteq> H" "pairwise orthogonal B" "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
    "independent B" "card B = dim H" "span B = H"
    using orthonormal_basis_subspace[OF subH] by metis
  have "CARD('n) - k \<le> card B"
    using k(1) dimH B(5) by linarith
  then obtain T where T: "T \<subseteq> B" "card T = CARD('n) - k" "finite T"
    by (rule obtain_subset_with_card_n)
  have onT: "onormal T"
    using T B by (auto simp: onormal_def elim: pairwise_subset)
  have "(\<Sum>u\<in>T. outer_prod u u) *v p = 0"
    using T(1) B(1)
    by (auto simp: H_def matrix_vector_mult_sum inner_commute intro!: sum.neutral)
  moreover have "eigen_ub (\<Sum>u\<in>T. outer_prod u u) L"
    unfolding eigen_ub_def
  proof
    fix x :: "real^'n"
    have "x \<bullet> ((\<Sum>u\<in>T. outer_prod u u) *v x) \<le> x \<bullet> x"
      using onormal_outer_sum_props(3)[OF onT] by (simp add: eigen_ub_def)
    also have "\<dots> \<le> L * (x \<bullet> x)"
      using L by (simp add: mult_right_mono[of 1 L "x \<bullet> x", simplified])
    finally show "x \<bullet> ((\<Sum>u\<in>T. outer_prod u u) *v x) \<le> L * (x \<bullet> x)" .
  qed
  ultimately show thesis
    using onormal_outer_sum_props[OF onT] T(2)
    by (intro that[of "\<Sum>u\<in>T. outer_prod u u"]) (auto simp: feasible_def)
qed

subsection \<open>The candidate solution of Example 3.1\<close>

text \<open>\<open>v(x) = max (r\<^sup>2 - |x|\<^sup>2) 0 / (n - k)\<close> on the ball of radius \<open>r\<close>.\<close>

definition ball_v :: "real \<Rightarrow> nat \<Rightarrow> real^'n \<Rightarrow> real" where
  "ball_v r k x = max (r\<^sup>2 - x \<bullet> x) 0 / real (CARD('n) - k)"

subsection \<open>Degenerate ellipticity\<close>

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

subsection \<open>Bounds on the feasible set\<close>

lemma feasible_entry_bound:
  fixes a :: "real^'n^'n"
  assumes a: "a \<in> feasible k L p"
  shows "\<bar>a $ i $ j\<bar> \<le> L"
  using a by (auto simp: feasible_def intro: psd_eigen_ub_entry_abs_le)

text \<open>So a feasible \<open>a\<close> pairs with any matrix \<open>D\<close> to at most \<open>entrysum D * L\<close>
  in trace; in particular \<open>F\<close> is an infimum over a set bounded below, and one
  feasible witness bounds \<open>F\<close> from above.\<close>

lemma trace_mult_feasible_bound:
  fixes D :: "real^'n::finite^'n"
  assumes a: "a \<in> feasible k L p"
  shows "\<bar>trace (D ** a)\<bar> \<le> entrysum D * L"
proof -
  have "\<bar>trace (D ** a)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>D $ i $ j * a $ j $ i\<bar>)"
    unfolding trace_def matrix_matrix_mult_def
    by (auto intro!: order_trans[OF sum_abs] sum_mono)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar> * L)"
    by (intro sum_mono)
      (simp add: abs_mult mult_left_mono feasible_entry_bound[OF a])
  finally show ?thesis
    by (simp add: entrysum_def sum_distrib_right)
qed

lemma ell_op_bdd_below:
  fixes M :: "real^'n^'n"
  shows "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p)"
  by (rule bdd_belowI2[of _ "- (entrysum M * L) / 2"])
    (use trace_mult_feasible_bound[of _ k L p M] in \<open>auto simp: abs_le_iff\<close>)

lemma ell_op_le_witness:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes aF: "a \<in> feasible k L p"
  shows "ell_op k L p M \<le> - trace (M ** a) / 2"
  unfolding ell_op_def by (rule cInf_lower[OF imageI[OF aF] ell_op_bdd_below])

lemma feasible_nonempty:
  fixes p :: "real^'n"
  assumes "1 \<le> k" "k < CARD('n)" "1 \<le> L"
  shows "feasible k L p \<noteq> {}"
  using feasible_witness[OF assms] by blast

lemma ell_op_approx:
  fixes p :: "real^'n::finite" and M :: "real^'n^'n"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and e0: "0 < \<epsilon>"
  obtains a where "a \<in> feasible k L p"
    and "- trace (M ** a) / 2 < ell_op k L p M + \<epsilon>"
proof -
  have ne: "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p \<noteq> {}"
    using feasible_nonempty[OF k1 kn L1] by blast
  have "ell_op k L p M < ell_op k L p M + \<epsilon>" using e0 by simp
  then have "\<exists>v \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p.
      v < ell_op k L p M + \<epsilon>"
    unfolding ell_op_def using cInf_less_iff[OF ne ell_op_bdd_below] by blast
  then show ?thesis using that by blast
qed

(*<*)
end
(*>*)
