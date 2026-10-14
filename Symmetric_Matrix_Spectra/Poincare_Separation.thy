
(*<*)
theory Poincare_Separation
  imports Eigenvalue_Continuity
begin

(*>*)

text \<open>
  The variational facts about ordered eigenvalues on which Poincare
  separation rests: the Rayleigh bounds \<open>\<lambda>\<^sub>(\<^sub>n\<^sub>) \<le> x \<bullet> a x \<le> \<lambda>\<^sub>(\<^sub>1\<^sub>)\<close> on the
  unit sphere, the trace and quadratic form against a weighted sum of
  outer products, the dimension-counting argument that any two subspaces
  whose dimensions exceed the ambient dimension must meet, and the
  Courant--Fischer lower bound for an ordered eigenvalue
  \<^cite>\<open>HornJohnson\<close>.  Then Lipschitz estimates for the positive-part
  sums of the eigenvalues and for the bracket
  \<open>L * possum n a + (kyfan m a - possum m a)\<close>, and norm bounds for
  products and conjugates of matrices.
\<close>

unbundle inner_syntax


lemma kyfan_full_eq_trace:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "kyfan CARD('n) a = trace a"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and cardB: "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigendecomposition[OF sym] by metis
  have vac: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if "u \<in> B" "v \<in> B - B" for u v
    using that by simp
  have "kyfan CARD('n) a = (\<Sum>u\<in>B. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig subset_refl cardB vac])
  also have "\<dots> = trace (a ** (\<Sum>u\<in>B. outer_prod u u))"
    by (rule trace_mult_outer_sum[symmetric])
  also have "\<dots> = trace (a ** mat 1)"
    by (simp add: onormal_complete[OF B])
  also have "\<dots> = trace a"
    by simp
  finally show ?thesis .
qed


text \<open>A unit vector spans a one-dimensional orthonormal family, so its outer
  product is a projection of trace one (\<open>onormal_proj\<close>), and so is the
  complementary projection, of trace \<open>n - 1\<close>.\<close>

lemma is_proj_rank1:
  fixes x :: "real^'n::finite"
  assumes x: "norm x = 1"
  shows "is_proj (outer_prod x x)" and "trace (outer_prod x x) = 1"
  using onormal_proj[of "{x}"] x by (auto simp: onormal_def)

lemma is_proj_compl_rank1:
  fixes x :: "real^'n::finite"
  assumes x: "norm x = 1"
  shows "is_proj (mat 1 - outer_prod x x :: real^'n^'n)"
    and "trace (mat 1 - outer_prod x x :: real^'n^'n) = real (CARD('n) - 1)"
proof -
  have P: "is_proj (outer_prod x x)" "trace (outer_prod x x) = 1"
    by (rule is_proj_rank1[OF x])+
  then show "is_proj (mat 1 - outer_prod x x :: real^'n^'n)"
    by (simp add: is_proj_def transpose_diff_matrix matrix_mul_diff_left
        matrix_mul_diff_right)
  have "0 < CARD('n)"
    by simp
  with P(2) show "trace (mat 1 - outer_prod x x :: real^'n^'n) = real (CARD('n) - 1)"
    by (simp add: trace_sub trace_I of_nat_diff)
qed

text \<open>The trace of \<open>a\<close> against a rank-one projection is the Rayleigh
  quotient.\<close>


lemma trace_mult_rank1:
  fixes a :: "real^'n::finite^'n"
  shows "trace (a ** outer_prod x x) = x \<bullet> (a *v x)"
proof -
  have "trace (a ** outer_prod x x) = trace (outer_prod (a *v x) x)"
    by (simp add: mult_outer_prod)
  also have "\<dots> = (a *v x) \<bullet> x"
    by simp
  also have "\<dots> = x \<bullet> (a *v x)"
    by (simp add: inner_commute)
  finally show ?thesis .
qed

text \<open>The two Rayleigh bounds.  The upper one is immediate from
  \<open>kyfan_ge_trace_mult\<close>; the lower one pairs \<open>a\<close> with the complementary
  projection, using that the full Ky Fan sum is the trace.\<close>


lemma quadform_le_eigval_1:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and x: "norm x = 1"
  shows "x \<bullet> (a *v x) \<le> eigval 1 a"
proof -
  have tr1: "trace (outer_prod x x) = real 1"
    using is_proj_rank1(2)[OF x] by simp
  have e1: "eigval 1 (a :: real^'n^'n) = kyfan 1 a"
    by (rule eigval_1)
  have "trace (a ** outer_prod x x) \<le> kyfan 1 a"
    by (rule kyfan_ge_trace_mult[OF sym is_proj_rank1(1)[OF x] tr1])
  then have "x \<bullet> (a *v x) \<le> kyfan 1 a"
    by (simp add: trace_mult_rank1)
  then show ?thesis
    unfolding e1 .
qed


lemma eigval_min_le_quadform:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and x: "norm x = 1"
  shows "eigval CARD('n) a \<le> x \<bullet> (a *v x)"
proof -
  have compl: "trace (a ** (mat 1 - outer_prod x x)) \<le> kyfan (CARD('n) - 1) a"
    by (rule kyfan_ge_trace_mult[OF sym is_proj_compl_rank1(1)[OF x]
          is_proj_compl_rank1(2)[OF x]])
  have split: "trace (a ** (mat 1 - outer_prod x x)) = trace a - x \<bullet> (a *v x)"
  proof -
    have "trace (a ** (mat 1 - outer_prod x x))
        = trace (a ** mat 1) - trace (a ** outer_prod x x)"
      by (simp add: matrix_mul_diff_right trace_sub)
    also have "\<dots> = trace a - x \<bullet> (a *v x)"
      by (simp add: trace_mult_rank1)
    finally show ?thesis .
  qed
  have "eigval CARD('n) a = trace a - kyfan (CARD('n) - 1) a"
    unfolding eigval_def by (simp add: kyfan_full_eq_trace[OF sym])
  also have "\<dots> \<le> trace a - trace (a ** (mat 1 - outer_prod x x))"
    using compl by simp
  also have "\<dots> = x \<bullet> (a *v x)"
    unfolding split by simp
  finally show ?thesis .
qed


lemma trace_weighted_outer_sum:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B"
  shows "trace (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) = (\<Sum>v\<in>B. g v)"
proof -
  have "trace (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v)
      = (\<Sum>v\<in>B. trace (g v *\<^sub>R outer_prod v v))"
    by (rule trace_matrix_sum)
  also have "\<dots> = (\<Sum>v\<in>B. g v * (v \<bullet> v))"
    by (intro sum.cong refl) (simp add: trace_scaleR)
  also have "\<dots> = (\<Sum>v\<in>B. g v)"
  proof (intro sum.cong refl)
    fix v assume "v \<in> B"
    then have "norm v = 1"
      using B by (simp add: onormal_def)
    then show "g v * (v \<bullet> v) = g v"
      by (simp add: dot_square_norm)
  qed
  finally show ?thesis .
qed


lemma quadform_weighted_outer_sum:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" and u: "u \<in> B"
  shows "u \<bullet> ((\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v u) = g u"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  have nu: "norm u = 1"
    using B u by (simp add: onormal_def)
  have uu: "u \<bullet> u = 1"
    using nu by (simp add: dot_square_norm)
  have "(\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v u = (\<Sum>v\<in>B. g v *\<^sub>R ((v \<bullet> u) *\<^sub>R v))"
    by (simp add: matrix_vector_mult_sum scaleR_matrix_vector_assoc[symmetric])
  also have "\<dots> = (\<Sum>v\<in>B. if v = u then g u *\<^sub>R u else 0)"
    by (intro sum.cong refl)
      (use B u in \<open>auto dest: onormal_inner_distinct\<close>)
  also have "\<dots> = g u *\<^sub>R u"
    using finB u by simp
  finally have "(\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v u = g u *\<^sub>R u" .
  then show ?thesis
    by (simp add: uu)
qed

text \<open>Against a weighted sum of outer products, the quadratic form is the
  weighted sum of squared coefficients; no orthonormality is needed.  This
  bounds \<open>x \<bullet> (a *v x)\<close> by the largest weight in the sum.\<close>

lemma quadform_weighted_outer_sum_eq:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "finite B"
  shows "x \<bullet> ((\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v x) = (\<Sum>v\<in>B. g v * (v \<bullet> x)^2)"
proof -
  have "(\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v x = (\<Sum>v\<in>B. g v *\<^sub>R ((v \<bullet> x) *\<^sub>R v))"
    by (simp add: matrix_vector_mult_sum scaleR_matrix_vector_assoc[symmetric])
  then have "x \<bullet> ((\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v x)
      = (\<Sum>v\<in>B. g v * ((v \<bullet> x) * (x \<bullet> v)))"
    by (simp add: inner_sum_right mult.assoc)
  also have "\<dots> = (\<Sum>v\<in>B. g v * (v \<bullet> x)^2)"
    by (intro sum.cong refl) (simp add: inner_commute power2_eq_square)
  finally show ?thesis .
qed

text \<open>Every eigenvalue outside a threshold set of size \<open>m\<close> is dominated by
  \<open>eigval m a\<close>: the latter is the minimum over the threshold set, and the
  threshold property puts everything outside below that minimum.\<close>

lemma quadform_outside_threshold_le_eigval:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and T: "T \<subseteq> B" "card T = m" and m: "0 < m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and v: "v \<in> B - T"
  shows "v \<bullet> (a *v v) \<le> eigval m a"
proof -
  obtain w where w: "w \<in> T" and "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    and eigw: "eigval m a = w \<bullet> (a *v w)"
    using eigval_threshold_min[OF B sym eig T m thresh] by blast
  show ?thesis
    unfolding eigw by (rule thresh[OF w v])
qed

text \<open>The dimension-counting core of the Courant-Fischer argument (Grassmann's
  formula): two subspaces whose dimensions exceed the ambient dimension must meet
  in a nonzero vector, applied below to \<open>S\<close> of dimension \<open>\<ge> m\<close> and
  \<open>span (B - T')\<close> of dimension \<open>CARD('n) - m + 1\<close>.\<close>

lemma dim_inter_ge:
  fixes S W :: "(real^'n::finite) set"
  assumes S: "subspace S" and W: "subspace W"
  shows "dim S + dim W \<le> dim (S \<inter> W) + CARD('n)"
  using dim_sums_Int[OF S W] dim_subset_UNIV_cart[of "{x + y |x y. x \<in> S \<and> y \<in> W}"]
  by simp

lemma subspace_inter_nonzero:
  fixes S W :: "(real^'n::finite) set"
  assumes S: "subspace S" and W: "subspace W"
    and dims: "CARD('n) < dim S + dim W"
  shows "\<exists>x. x \<in> S \<and> x \<in> W \<and> x \<noteq> 0"
proof -
  have "dim (S \<inter> W) \<noteq> 0"
    using dim_inter_ge[OF S W] dims by linarith
  then have "\<not> S \<inter> W \<subseteq> {0}"
    by simp
  then show ?thesis
    by blast
qed

text \<open>Parseval's identity for a full orthonormal basis is the case \<open>g = 1\<close>
  of the expansion.  Together they give the bound the Courant-Fischer
  argument needs: \<open>x \<bullet> (a *v x) = (\<Sum>v. \<lambda>\<^sub>v * (v \<bullet> x)\<^sup>2) \<le> \<lambda>\<^sub>m\<^sub>a\<^sub>x * (x \<bullet> x)\<close>.\<close>


lemma parseval_onormal:
  fixes x :: "real^'n::finite"
  assumes B: "onormal B" "span B = UNIV"
  shows "(\<Sum>v\<in>B. (v \<bullet> x)^2) = x \<bullet> x"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have "(\<Sum>v\<in>B. (v \<bullet> x)^2) = (\<Sum>v\<in>B. 1 * (v \<bullet> x)^2)"
    by simp
  also have "\<dots> = x \<bullet> ((\<Sum>v\<in>B. 1 *\<^sub>R outer_prod v v) *v x)"
    by (rule quadform_weighted_outer_sum_eq[OF finB, symmetric])
  also have "\<dots> = x \<bullet> (mat 1 *v x)"
    by (simp add: onormal_complete[OF B])
  also have "\<dots> = x \<bullet> x"
    by simp
  finally show ?thesis .
qed

text \<open>A basis vector is orthogonal to the span of any part of the basis not
  containing it.  This kills the \<open>v \<in> T'\<close> terms of the expansion, leaving only
  eigenvalues that \<open>eigval m a\<close> dominates.\<close>


lemma onormal_orthogonal_to_span_complement:
  fixes x :: "real^'n::finite"
  assumes B: "onormal B" and v: "v \<in> B" and T: "T \<subseteq> B" "v \<notin> T"
    and x: "x \<in> span T"
  shows "v \<bullet> x = 0"
proof -
  have "T \<subseteq> {y. v \<bullet> y = 0}"
  proof
    fix u assume u: "u \<in> T"
    then have uB: "u \<in> B" and une: "u \<noteq> v"
      using T by auto
    then have "v \<bullet> u = 0"
      using B v by (auto simp: onormal_def pairwise_def orthogonal_def)
    then show "u \<in> {y. v \<bullet> y = 0}"
      by simp
  qed
  moreover have "subspace {y :: real^'n. v \<bullet> y = 0}"
    by (simp add: subspace_hyperplane)
  ultimately have "span T \<subseteq> {y. v \<bullet> y = 0}"
    by (rule span_minimal)
  then show ?thesis
    using x by auto
qed

text \<open>Over an orthonormal family, nonnegative weights give a nonnegative
  quadratic form.\<close>

lemma quadform_weighted_outer_sum_nonneg:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" and g: "\<And>v. v \<in> B \<Longrightarrow> 0 \<le> g v"
  shows "0 \<le> x \<bullet> ((\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v x)"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  show ?thesis
    unfolding quadform_weighted_outer_sum_eq[OF finB]
    using g by (intro sum_nonneg) simp
qed

text \<open>Comparison of two matrices in the same orthonormal basis: larger
  weights give a larger quadratic form.\<close>

lemma quadform_weighted_outer_mono:
  fixes N c :: "real^'n::finite^'n"
  assumes B: "onormal B"
    and N: "N = (\<Sum>v\<in>B. f v *\<^sub>R outer_prod v v)"
    and c: "c = (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v)"
    and le: "\<And>v. v \<in> B \<Longrightarrow> g v \<le> f v"
  shows "x \<bullet> (c *v x) \<le> x \<bullet> (N *v x)"
proof -
  have diff: "N - c = (\<Sum>v\<in>B. (f v - g v) *\<^sub>R outer_prod v v)"
    unfolding N c by (simp add: sum_subtractf scaleR_left_diff_distrib)
  have nn: "0 \<le> x \<bullet> ((N - c) *v x)"
    unfolding diff
    using le by (intro quadform_weighted_outer_sum_nonneg[OF B]) simp
  have "x \<bullet> ((N - c) *v x) = x \<bullet> (N *v x) - x \<bullet> (c *v x)"
    by (simp add: matrix_vector_mult_diff_rdistrib inner_diff_right)
  with nn show ?thesis
    by simp
qed


lemma transpose_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes finB: "finite B"
  shows "transpose (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
       = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
  using finB
  by (simp add: transpose_matrix_sum transpose_scalar)


lemma psd_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u"
  shows "psd (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
  unfolding psd_def
  using transpose_weighted_outer_sum[OF onormal_finite[OF B]]
    quadform_weighted_outer_sum_nonneg[OF B, of c] c0 by blast

lemma exists_top_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M"
  shows "\<exists>q. norm q = 1 \<and> M *v q = (q \<bullet> (M *v q)) *\<^sub>R q
      \<and> q \<bullet> (M *v q) = eigval 1 M"
  by (rule exists_eigenvector_eigval[OF sym]) (simp_all add: Suc_le_eq)

text \<open>On the span of a threshold set, the Rayleigh quotient is bounded below by
  the smallest eigenvalue occurring there, namely \<open>eigval m a\<close>.\<close>


lemma quadform_ge_on_span_threshold:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and T: "T \<subseteq> B" "card T = m" and m: "0 < m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and x: "x \<in> span T"
  shows "eigval m a * (x \<bullet> x) \<le> x \<bullet> (a *v x)"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    and eigw: "eigval m a = w \<bullet> (a *v w)"
    using eigval_threshold_min[OF B sym eig T m thresh] by blast
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have adecomp: "a = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])
  have vanish: "u \<bullet> x = 0" if u: "u \<in> B - T" for u
  proof (rule onormal_orthogonal_to_span_complement[OF B(1) _ T(1) _ x])
    show "u \<in> B" using u by blast
    show "u \<notin> T" using u by blast
  qed
  have lamge: "eigval m a \<le> lam u" if u: "u \<in> T" for u
    unfolding lam_def eigw by (rule wmin[OF u])
  have "eigval m a * (x \<bullet> x) = eigval m a * (\<Sum>u\<in>B. (u \<bullet> x)^2)"
    by (simp add: parseval_onormal[OF B])
  also have "\<dots> = eigval m a * (\<Sum>u\<in>T. (u \<bullet> x)^2)"
  proof -
    have "(\<Sum>u\<in>B. (u \<bullet> x)^2) = (\<Sum>u\<in>T. (u \<bullet> x)^2)"
      by (rule sum.mono_neutral_right[OF finB T(1)]) (auto simp: vanish)
    then show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>u\<in>T. eigval m a * (u \<bullet> x)^2)"
    by (simp add: sum_distrib_left)
  also have "\<dots> \<le> (\<Sum>u\<in>T. lam u * (u \<bullet> x)^2)"
    using lamge by (intro sum_mono mult_right_mono) auto
  also have "\<dots> = (\<Sum>u\<in>B. lam u * (u \<bullet> x)^2)"
    by (rule sum.mono_neutral_right[OF finB T(1), symmetric]) (auto simp: vanish)
  also have "\<dots> = x \<bullet> (a *v x)"
    unfolding adecomp by (rule quadform_weighted_outer_sum_eq[OF finB, symmetric])
  finally show ?thesis .
qed

text \<open>The general Courant-Fischer lower bound: if the Rayleigh quotient of
  \<open>a\<close> is at least \<open>c\<close> on a subspace of dimension \<open>\<ge> m\<close>, then
  \<open>c \<le> eigval m a\<close>, via a comparison subspace whose dimension, together
  with \<open>m\<close>, exceeds \<open>CARD('n)\<close>.\<close>

theorem eigval_ge_of_subspace:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
    and S: "subspace S" "m \<le> dim S"
    and quad: "\<And>x. x \<in> S \<Longrightarrow> c * (x \<bullet> x) \<le> x \<bullet> (a *v x)"
    and m: "0 < m" "m \<le> CARD('n)"
  shows "c \<le> eigval m a"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and finB: "finite B" and cardB: "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigendecomposition[OF sym] by metis
  obtain T w where T: "T \<subseteq> B" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    and w: "w \<in> T" and "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    and eigw: "eigval m a = w \<bullet> (a *v w)"
    using eigval_threshold_witness[OF B sym eig m] by blast
  define U where "U = insert w (B - T)"
  have Usub: "U \<subseteq> B"
    unfolding U_def using w T(1) by blast
  have onU: "onormal U"
    by (rule onormal_subset[OF B(1) Usub])
  have wnotin: "w \<notin> B - T"
    using w by blast
  have cardU: "card U = CARD('n) - m + 1"
    unfolding U_def
    using wnotin finB T(1) T(2) cardB
    by (simp add: card_Diff_subset finite_subset)
  have dimU: "dim (span U) = CARD('n) - m + 1"
    using onormal_card_dim_span[OF onU] cardU by simp
  text \<open>Dimensions sum past the ambient dimension, so the subspaces meet.\<close>
  have dims: "CARD('n) < dim S + dim (span U)"
    using S(2) dimU m(2) by simp
  obtain x where x: "x \<in> S" "x \<in> span U" "x \<noteq> 0"
    using subspace_inter_nonzero[OF S(1) subspace_span dims] by blast
  have xx: "0 < x \<bullet> x"
    using x(3) by simp
  text \<open>Every eigenvalue occurring in \<open>U\<close> is dominated by \<open>eigval m a\<close>.\<close>
  have Ubound: "v \<bullet> (a *v v) \<le> eigval m a" if v: "v \<in> U" for v
  proof (cases "v = w")
    case True
    then show ?thesis
      using eigw by simp
  next
    case False
    then have vBT: "v \<in> B - T"
      using v unfolding U_def by simp
    show ?thesis
      by (rule quadform_outside_threshold_le_eigval[OF B sym eig T(1) T(2) m(1)
            thresh vBT])
  qed
  text \<open>Expand \<open>x \<bullet> (a *v x)\<close> in the eigenbasis; the terms outside \<open>U\<close> vanish
    because \<open>x \<in> span U\<close>.\<close>
  text \<open>Bind the eigenvalues to a local constant before decomposing, since
    \<open>spectral_decomposition\<close> mentions \<open>a\<close> on the right as well and would loop
    as a rewrite rule.\<close>
  define lam where "lam = (\<lambda>v :: real^'n. v \<bullet> (a *v v))"
  have adecomp: "a = (\<Sum>v\<in>B. lam v *\<^sub>R outer_prod v v)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])
  have Ubound': "lam v \<le> eigval m a" if "v \<in> U" for v
    using Ubound[OF that] by (simp add: lam_def)
  have vanish: "v \<bullet> x = 0" if v: "v \<in> B - U" for v
  proof (rule onormal_orthogonal_to_span_complement[OF B(1) _ Usub _ x(2)])
    show "v \<in> B" using v by blast
    show "v \<notin> U" using v by blast
  qed
  have "x \<bullet> (a *v x) = (\<Sum>v\<in>B. lam v * (v \<bullet> x)^2)"
    unfolding adecomp by (rule quadform_weighted_outer_sum_eq[OF finB])
  also have "\<dots> = (\<Sum>v\<in>U. lam v * (v \<bullet> x)^2)"
    by (rule sum.mono_neutral_right[OF finB Usub]) (auto simp: vanish)
  also have "\<dots> \<le> (\<Sum>v\<in>U. eigval m a * (v \<bullet> x)^2)"
    using Ubound' by (intro sum_mono mult_right_mono) auto
  also have "\<dots> = eigval m a * (\<Sum>v\<in>U. (v \<bullet> x)^2)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = eigval m a * (\<Sum>v\<in>B. (v \<bullet> x)^2)"
  proof -
    have "(\<Sum>v\<in>U. (v \<bullet> x)^2) = (\<Sum>v\<in>B. (v \<bullet> x)^2)"
      by (rule sum.mono_neutral_right[OF finB Usub, symmetric]) (auto simp: vanish)
    then show ?thesis
      by simp
  qed
  also have "\<dots> = eigval m a * (x \<bullet> x)"
    by (simp add: parseval_onormal[OF B])
  finally have upper: "x \<bullet> (a *v x) \<le> eigval m a * (x \<bullet> x)" .
  have "c * (x \<bullet> x) \<le> x \<bullet> (a *v x)"
    by (rule quad[OF x(1)])
  with upper have "c * (x \<bullet> x) \<le> eigval m a * (x \<bullet> x)"
    by simp
  then show ?thesis
    using xx by (simp add: mult_right_le_imp_le)
qed


lemma possum_lipschitz:
  fixes A B :: "real^'n::finite^'n"
  assumes symA: "transpose A = A" and symB: "transpose B = B"
    and m: "m \<le> CARD('n)"
  shows "\<bar>possum m A - possum m B\<bar>
       \<le> real CARD('n) * entrysum (A - B)"
proof -
  text \<open>Each Ky Fan sum moves by at most the bound, so the maximum does too;
    the bound is symmetric in \<open>A\<close> and \<open>B\<close>, so one half suffices.\<close>
  have half: "possum m X \<le> possum m Y + real CARD('n) * entrysum (X - Y)"
    if symX: "transpose X = X" and symY: "transpose Y = Y" for X Y :: "real^'n^'n"
    unfolding possum_def[of m X]
  proof (rule Max.boundedI)
    fix y assume "y \<in> (\<lambda>j. kyfan j X) ` {..m}"
    then obtain j where j: "j \<le> m" and y: "y = kyfan j X"
      by auto
    have "kyfan j X - kyfan j Y \<le> real j * entrysum (X - Y)"
      using abs_le_D1[OF kyfan_lipschitz[OF symX symY order_trans[OF j m]]] .
    also have "\<dots> \<le> real CARD('n) * entrysum (X - Y)"
      using order_trans[OF j m] entrysum_nonneg[of "X - Y"] by (simp add: mult_right_mono)
    finally show "y \<le> possum m Y + real CARD('n) * entrysum (X - Y)"
      using possum_ge_kyfan[OF j, of Y] y by linarith
  qed simp_all
  show ?thesis
    unfolding abs_le_iff
    using half[OF symA symB] half[OF symB symA, unfolded entrysum_sym[of B A]] by linarith
qed


theorem bracket_lipschitz:
  fixes A B :: "real^'n::finite^'n"
  assumes symA: "transpose A = A" and symB: "transpose B = B"
    and m: "m \<le> CARD('n)" and L: "0 \<le> L"
  shows "\<bar>bracket m L A - bracket m L B\<bar>
       \<le> (L + 2) * real CARD('n) * entrysum (A - B)"
proof -
  define es where "es = entrysum (A - B)"
  have es0: "0 \<le> es"
    unfolding es_def by (rule entrysum_nonneg)
  have p1: "\<bar>possum CARD('n) A - possum CARD('n) B\<bar> \<le> real CARD('n) * es"
    unfolding es_def by (rule possum_lipschitz[OF symA symB order_refl])
  have p2: "\<bar>possum m A - possum m B\<bar> \<le> real CARD('n) * es"
    unfolding es_def by (rule possum_lipschitz[OF symA symB m])
  have p3: "\<bar>kyfan m A - kyfan m B\<bar> \<le> real CARD('n) * es"
  proof -
    have "\<bar>kyfan m A - kyfan m B\<bar> \<le> real m * es"
      unfolding es_def by (rule kyfan_lipschitz[OF symA symB m])
    also have "\<dots> \<le> real CARD('n) * es"
      using m es0 by (simp add: mult_right_mono)
    finally show ?thesis .
  qed
  define x where "x = L * (possum CARD('n) A - possum CARD('n) B)"
  define y where "y = kyfan m A - kyfan m B"
  define z where "z = possum m A - possum m B"
  have eq: "bracket m L A - bracket m L B = x + y - z"
    unfolding bracket_def x_def y_def z_def by (simp add: algebra_simps)
  have t1: "\<bar>x + y - z\<bar> \<le> \<bar>x + y\<bar> + \<bar>z\<bar>"
    by (rule abs_triangle_ineq4)
  have t2: "\<bar>x + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>"
    by (rule abs_triangle_ineq)
  have tri: "\<bar>x + y - z\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar> + \<bar>z\<bar>"
    using t1 t2 by simp
  have absx: "\<bar>x\<bar> = L * \<bar>possum CARD('n) A - possum CARD('n) B\<bar>"
    unfolding x_def using L by (simp add: abs_mult)
  have bx: "\<bar>x\<bar> \<le> L * (real CARD('n) * es)"
    unfolding absx using p1 L by (simp add: mult_left_mono)
  have by': "\<bar>y\<bar> \<le> real CARD('n) * es"
    unfolding y_def by (rule p3)
  have bz: "\<bar>z\<bar> \<le> real CARD('n) * es"
    unfolding z_def by (rule p2)
  have "\<bar>bracket m L A - bracket m L B\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar> + \<bar>z\<bar>"
    unfolding eq by (rule tri)
  also have "\<dots> \<le> L * (real CARD('n) * es) + real CARD('n) * es
      + real CARD('n) * es"
    using bx by' bz by linarith
  also have "\<dots> = (L + 2) * real CARD('n) * es"
    by (simp add: algebra_simps)
  finally show ?thesis
    unfolding es_def .
qed


lemma inner_transpose_self:
  fixes A :: "real^'n::finite^'n"
  shows "transpose A \<bullet> transpose A = A \<bullet> A"
proof -
  have "transpose A \<bullet> transpose A
      = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). A $ j $ i * A $ j $ i)"
    unfolding inner_vec_def transpose_def by simp
  also have "\<dots> = (\<Sum>j\<in>(UNIV :: 'n set). \<Sum>i\<in>(UNIV :: 'n set). A $ j $ i * A $ j $ i)"
    by (rule sum.swap)
  also have "\<dots> = A \<bullet> A"
    unfolding inner_vec_def by simp
  finally show ?thesis .
qed


lemma matrix_mult_entry_inner:
  fixes A B :: "real^'n::finite^'n"
  shows "(A ** B) $ i $ j = A $ i \<bullet> (transpose B) $ j"
  unfolding matrix_matrix_mult_def transpose_def inner_vec_def by simp


lemma norm_matrix_mult_le:
  fixes A B :: "real^'n::finite^'n"
  shows "norm (A ** B) \<le> norm A * norm B"
proof -
  have sq: "((A ** B) $ i $ j)^2
      \<le> (norm (A $ i))^2 * (norm ((transpose B) $ j))^2" for i j
  proof -
    have "\<bar>(A ** B) $ i $ j\<bar> \<le> norm (A $ i) * norm ((transpose B) $ j)"
      unfolding matrix_mult_entry_inner by (rule Cauchy_Schwarz_ineq2)
    then have "\<bar>(A ** B) $ i $ j\<bar>^2
        \<le> (norm (A $ i) * norm ((transpose B) $ j))^2"
      by (intro power_mono) auto
    then show ?thesis
      by (simp add: power_mult_distrib)
  qed
  have expand: "X \<bullet> X = (\<Sum>i\<in>(UNIV :: 'n set). (norm (X $ i))^2)"
    for X :: "real^'n^'n"
  proof -
    have "(\<Sum>i\<in>(UNIV :: 'n set). (norm (X $ i))^2)
        = (\<Sum>i\<in>(UNIV :: 'n set). X $ i \<bullet> X $ i)"
      by (simp add: dot_square_norm)
    also have "\<dots> = X \<bullet> X"
      by (simp add: inner_vec_def)
    finally show ?thesis
      by (rule sym)
  qed
  have "(A ** B) \<bullet> (A ** B)
      = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). ((A ** B) $ i $ j)^2)"
    unfolding inner_vec_def by (simp add: power2_eq_square)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set).
      (norm (A $ i))^2 * (norm ((transpose B) $ j))^2)"
    by (intro sum_mono sq)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (norm (A $ i))^2)
      * (\<Sum>j\<in>(UNIV :: 'n set). (norm ((transpose B) $ j))^2)"
    by (rule sum_product[symmetric])
  also have "\<dots> = (A \<bullet> A) * (transpose B \<bullet> transpose B)"
    unfolding expand by (rule refl)
  also have "\<dots> = (A \<bullet> A) * (B \<bullet> B)"
    by (simp add: inner_transpose_self)
  finally have le: "(A ** B) \<bullet> (A ** B) \<le> (A \<bullet> A) * (B \<bullet> B)" .
  have "norm (A ** B) = sqrt ((A ** B) \<bullet> (A ** B))"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> \<le> sqrt ((A \<bullet> A) * (B \<bullet> B))"
    using le by (rule real_sqrt_le_mono)
  also have "\<dots> = norm A * norm B"
    by (simp add: real_sqrt_mult norm_eq_sqrt_inner)
  finally show ?thesis .
qed

lemma conj_diff_expand:
  fixes M Q D :: "real^'n::finite^'n"
  shows "(Q - D) ** M ** (Q - D)
       = Q ** M ** Q - Q ** M ** D - D ** M ** Q + D ** M ** D"
proof -
  have "(Q - D) ** M = Q ** M - D ** M"
    by (rule matrix_mul_diff_left)
  then have "(Q - D) ** M ** (Q - D) = (Q ** M - D ** M) ** (Q - D)"
    by simp
  also have "\<dots> = (Q ** M) ** (Q - D) - (D ** M) ** (Q - D)"
    by (rule matrix_mul_diff_left)
  also have "\<dots> = (Q ** M ** Q - Q ** M ** D) - (D ** M ** Q - D ** M ** D)"
    by (simp add: matrix_mul_diff_right)
  also have "\<dots> = Q ** M ** Q - Q ** M ** D - D ** M ** Q + D ** M ** D"
    by simp
  finally show ?thesis .
qed

text \<open>The four-term bound.  Each term of the expansion is a product of at
  most three factors, so submultiplicativity of the Frobenius norm
  applies.\<close>

lemma norm_conj_diff_le:
  fixes M Q D :: "real^'n::finite^'n"
  shows "norm ((Q - D) ** M ** (Q - D) - Q ** M ** Q)
       \<le> 2 * norm Q * norm M * norm D + norm M * norm D * norm D"
proof -
  define X where "X = Q ** M ** D"
  define Y where "Y = D ** M ** Q"
  define Z where "Z = D ** M ** D"
  have eq: "(Q - D) ** M ** (Q - D) - Q ** M ** Q = - X - Y + Z"
    unfolding conj_diff_expand X_def Y_def Z_def by simp
  have tri: "norm (- X - Y + Z) \<le> norm X + norm Y + norm Z"
  proof -
    have "norm (- X - Y + Z) \<le> norm (- X - Y) + norm Z"
      by (rule norm_triangle_ineq)
    moreover have "norm (- X - Y) \<le> norm X + norm Y"
      using norm_triangle_ineq4[of "- X" Y] by simp
    ultimately show ?thesis by simp
  qed
  have bX: "norm X \<le> norm Q * norm M * norm D"
  proof -
    have "norm X \<le> norm (Q ** M) * norm D"
      unfolding X_def by (rule norm_matrix_mult_le)
    also have "\<dots> \<le> (norm Q * norm M) * norm D"
      by (rule mult_right_mono[OF norm_matrix_mult_le norm_ge_zero])
    finally show ?thesis by simp
  qed
  have bY: "norm Y \<le> norm D * norm M * norm Q"
  proof -
    have "norm Y \<le> norm (D ** M) * norm Q"
      unfolding Y_def by (rule norm_matrix_mult_le)
    also have "\<dots> \<le> (norm D * norm M) * norm Q"
      by (rule mult_right_mono[OF norm_matrix_mult_le norm_ge_zero])
    finally show ?thesis by simp
  qed
  have bZ: "norm Z \<le> norm D * norm M * norm D"
  proof -
    have "norm Z \<le> norm (D ** M) * norm D"
      unfolding Z_def by (rule norm_matrix_mult_le)
    also have "\<dots> \<le> (norm D * norm M) * norm D"
      by (rule mult_right_mono[OF norm_matrix_mult_le norm_ge_zero])
    finally show ?thesis by simp
  qed
  have "norm ((Q - D) ** M ** (Q - D) - Q ** M ** Q)
      \<le> norm X + norm Y + norm Z"
    unfolding eq by (rule tri)
  also have "\<dots> \<le> 2 * norm Q * norm M * norm D + norm M * norm D * norm D"
    using bX bY bZ by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>Hence the bracket is Lipschitz in the norm as well.\<close>

corollary bracket_lipschitz_norm:
  fixes A B :: "real^'n::finite^'n"
  assumes symA: "transpose A = A" and symB: "transpose B = B"
    and m: "m \<le> CARD('n)" and L: "0 \<le> L"
  shows "\<bar>bracket m L A - bracket m L B\<bar>
       \<le> (L + 2) * real CARD('n) * real (CARD('n) * CARD('n)) * norm (A - B)"
proof -
  have nn: "0 \<le> (L + 2) * real CARD('n)"
    using L by simp
  have "\<bar>bracket m L A - bracket m L B\<bar>
      \<le> (L + 2) * real CARD('n) * entrysum (A - B)"
    by (rule bracket_lipschitz[OF symA symB m L])
  also have "\<dots> \<le> (L + 2) * real CARD('n)
      * (real (CARD('n) * CARD('n)) * norm (A - B))"
    using entrysum_le_norm[of "A - B"] nn by (simp add: mult_left_mono)
  also have "\<dots> = (L + 2) * real CARD('n) * real (CARD('n) * CARD('n))
      * norm (A - B)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed


(*<*)
end
(*>*)
