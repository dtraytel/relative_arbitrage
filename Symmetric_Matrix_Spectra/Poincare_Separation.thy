
(*<*)
theory Poincare_Separation
  imports Eigenvalue_Continuity
begin

(*>*)

text \<open>
  The Poincare separation inequality and its Courant--Fischer scaffolding:
  the ordered eigenvalues of a compression of a symmetric matrix to a
  subspace interlace those of the matrix itself. Along the way: the trace
  read off against a weighted sum of outer products, the dimension-counting
  argument that any two subspaces whose dimensions exceed the ambient
  dimension must meet, the Courant--Fischer variational lower bound for an
  ordered eigenvalue, and the elementary continuity and Lipschitz estimates
  that make the eigenvalues, projections and outer products of a matrix
  vary continuously with it.
\<close>

unbundle inner_syntax

lemma trace_diff_matrix:
  fixes A B :: "real^'n::finite^'n"
  shows "trace (A - B) = trace A - trace B"
  unfolding trace_def by (simp add: sum_subtractf)


lemma kyfan_full_eq_trace:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  shows "kyfan CARD('n) a = trace a"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have vac: "v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)" if "u \<in> B" "v \<in> B - B" for u v
    using that by simp
  have "kyfan CARD('n) a = (\<Sum>u\<in>B. u \<bullet> (a *v u))"
    by (rule kyfan_threshold[OF B sym eig subset_refl cardB vac])
  also have "\<dots> = trace (a ** (\<Sum>u\<in>B. outer_prod u u))"
    by (rule trace_mult_spectral_proj[OF B(1) subset_refl eig, symmetric])
  also have "\<dots> = trace (a ** mat 1)"
    by (simp add: onormal_complete[OF B])
  also have "\<dots> = trace a"
    by simp
  finally show ?thesis .
qed


lemma is_proj_rank1:
  fixes x :: "real^'n::finite"
  assumes x: "norm x = 1"
  shows "is_proj (outer_prod x x)" and "trace (outer_prod x x) = 1"
proof -
  have xx: "x \<bullet> x = 1"
    using x by (simp add: dot_square_norm)
  show "is_proj (outer_prod x x)"
    unfolding is_proj_def by (simp add: outer_prod_mult xx)
  show "trace (outer_prod x x) = 1"
    by (simp add: xx)
qed


lemma is_proj_compl_rank1:
  fixes x :: "real^'n::finite"
  assumes x: "norm x = 1"
  shows "is_proj (mat 1 - outer_prod x x :: real^'n^'n)"
    and "trace (mat 1 - outer_prod x x :: real^'n^'n) = real (CARD('n) - 1)"
proof -
  have xx: "x \<bullet> x = 1"
    using x by (simp add: dot_square_norm)
  have sq: "outer_prod x x ** outer_prod x x = (outer_prod x x :: real^'n^'n)"
    by (simp add: outer_prod_mult xx)
  show "is_proj (mat 1 - outer_prod x x :: real^'n^'n)"
    unfolding is_proj_def
  proof (intro conjI)
    show "transpose (mat 1 - outer_prod x x :: real^'n^'n) = mat 1 - outer_prod x x"
      by (simp add: transpose_diff_matrix)
    have "(mat 1 - outer_prod x x) ** (mat 1 - outer_prod x x)
        = (mat 1 - outer_prod x x) ** mat 1
          - (mat 1 - outer_prod x x) ** outer_prod x x"
      by (rule matrix_mul_diff_right)
    also have "\<dots> = (mat 1 - outer_prod x x)
                  - (mat 1 ** outer_prod x x - outer_prod x x ** outer_prod x x)"
      by (simp add: matrix_mul_diff_left)
    also have "\<dots> = (mat 1 - outer_prod x x :: real^'n^'n)"
      by (simp add: sq)
    finally show "(mat 1 - outer_prod x x :: real^'n^'n)
        ** (mat 1 - outer_prod x x) = mat 1 - outer_prod x x" .
  qed
  have pos: "0 < CARD('n)"
    by (simp add: card_gt_0_iff)
  have "trace (mat 1 - outer_prod x x :: real^'n^'n)
      = trace (mat 1 :: real^'n^'n) - trace (outer_prod x x)"
    by (rule trace_diff_matrix)
  also have "\<dots> = real CARD('n) - 1"
    by (simp add: trace_I xx)
  also have "\<dots> = real (CARD('n) - 1)"
    using pos by simp
  finally show "trace (mat 1 - outer_prod x x :: real^'n^'n)
      = real (CARD('n) - 1)" .
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
  projection, using that the full Ky Fan sum is the trace.  The weak form of
  Poincare separation Eq. (3.5) needs.\<close>


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
      by (simp add: matrix_mul_diff_right trace_diff_matrix)
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
    by (simp add: matrix_vector_mult_sum scaleR_matrix_vector)
  also have "\<dots> = (\<Sum>v\<in>B. if v = u then g u *\<^sub>R u else 0)"
    by (intro sum.cong refl)
      (use B u in \<open>auto dest: onormal_inner_distinct\<close>)
  also have "\<dots> = g u *\<^sub>R u"
    using finB u by simp
  finally have "(\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v u = g u *\<^sub>R u" .
  then show ?thesis
    by (simp add: uu)
qed

text \<open>Nonnegative weights give a nonnegative quadratic form.  This makes both
  \<open>a - c\<close> and \<open>I - c\<close> positive semidefinite for the clipped matrix \<open>c\<close>, whose
  weights are \<open>max (\<mu>\<^sub>j - 1) 0\<close> and \<open>1 - min \<mu>\<^sub>j 1\<close> respectively.\<close>

text \<open>Against a weighted sum of outer products, the quadratic form is the
  weighted sum of squared coefficients; no orthonormality is needed.  This
  bounds \<open>x \<bullet> (a *v x)\<close> by the largest weight in the sum.\<close>


lemma quadform_weighted_outer_sum_eq:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "finite B"
  shows "x \<bullet> ((\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v x) = (\<Sum>v\<in>B. g v * (v \<bullet> x)^2)"
proof -
  have "(\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v x = (\<Sum>v\<in>B. g v *\<^sub>R ((v \<bullet> x) *\<^sub>R v))"
    by (simp add: matrix_vector_mult_sum scaleR_matrix_vector)
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
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have finT: "finite T"
    using T(1) finB by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using T(2) m by auto
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    using finite_arg_min_on[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
        OF finT Tne] by metis
  obtain i where mi: "m = Suc i"
    using m by (cases m) auto
  have cardT: "card T = Suc i"
    using T(2) mi by simp
  have "eigval m a = w \<bullet> (a *v w)"
    unfolding mi
    by (rule eigval_eq_min_of_threshold[OF B sym eig T(1) cardT thresh w wmin])
  moreover have "v \<bullet> (a *v v) \<le> w \<bullet> (a *v w)"
    by (rule thresh[OF w v])
  ultimately show ?thesis
    by simp
qed

text \<open>The dimension-counting core of the Courant-Fischer argument: two
  subspaces whose dimensions exceed the ambient dimension must meet in a
  nonzero vector, applied below to \<open>S\<close> of dimension \<open>\<ge> m\<close> and
  \<open>span (B - T')\<close> of dimension \<open>CARD('n) - m + 1\<close>.\<close>


lemma subspace_inter_nonzero:
  fixes S W :: "(real^'n::finite) set"
  assumes S: "subspace S" and W: "subspace W"
    and dims: "CARD('n) < dim S + dim W"
  shows "\<exists>x. x \<in> S \<and> x \<in> W \<and> x \<noteq> 0"
proof -
  have key: "dim {x + y |x y. x \<in> S \<and> y \<in> W} + dim (S \<inter> W) = dim S + dim W"
    by (rule dim_sums_Int[OF S W])
  have le: "dim {x + y |x y. x \<in> S \<and> y \<in> W} \<le> CARD('n)"
    using dim_subset_UNIV[of "{x + y |x y. x \<in> S \<and> y \<in> W}"] by simp
  have pos: "0 < dim (S \<inter> W)"
  proof (rule ccontr)
    assume "\<not> 0 < dim (S \<inter> W)"
    then have z: "dim (S \<inter> W) = 0"
      by simp
    have "dim {x + y |x y. x \<in> S \<and> y \<in> W} = dim S + dim W"
      using key z by simp
    with le dims show False
      by simp
  qed
  have "\<not> (S \<inter> W \<subseteq> {0})"
  proof
    assume "S \<inter> W \<subseteq> {0}"
    then have "dim (S \<inter> W) = 0"
      by simp
    with pos show False
      by simp
  qed
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
  weights give a larger quadratic form.  \<open>f = \<mu>\<close>, \<open>g = (\<lambda>v. min (\<mu> v) 1)\<close>
  gives \<open>x \<bullet> (c *v x) \<le> x \<bullet> (a *v x)\<close>; \<open>f = (\<lambda>_. 1)\<close> gives
  \<open>x \<bullet> (c *v x) \<le> x \<bullet> x\<close>.\<close>


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
    by (simp add: matrix_vector_mult_diff inner_diff_right)
  with nn show ?thesis
    by simp
qed


lemma transpose_sum_matrix:
  fixes f :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes "finite S"
  shows "transpose (\<Sum>u\<in>S. f u) = (\<Sum>u\<in>S. transpose (f u))"
  using assms by (induct S) (simp_all add: transpose_add transpose_def vec_eq_iff)


lemma transpose_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes finB: "finite B"
  shows "transpose (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
       = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
  using finB
  by (simp add: transpose_sum_matrix transpose_scaleR)


lemma psd_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u"
  shows "psd (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  show ?thesis
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
        = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
      by (rule transpose_weighted_outer_sum[OF finB])
    show "0 \<le> x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x)" for x
      by (rule quadform_weighted_outer_sum_nonneg[OF B c0])
  qed
qed

text \<open>The sum annihilates \<open>p\<close> as soon as every basis vector carrying a nonzero
  weight is orthogonal to \<open>p\<close>.\<close>


lemma outer_prod_scaleR_right:
  fixes u v :: "real^'n::finite"
  shows "outer_prod u (c *\<^sub>R v) = c *\<^sub>R outer_prod u v"
proof -
  have "outer_prod u (c *\<^sub>R v) = transpose (outer_prod (c *\<^sub>R v) u)"
    by simp
  also have "\<dots> = transpose (c *\<^sub>R outer_prod v u)"
    by (simp add: outer_prod_scaleR_left)
  also have "\<dots> = c *\<^sub>R outer_prod u v"
    by (simp add: transpose_scaleR)
  finally show ?thesis .
qed


lemma eigenbasis_containing_eigenvector:
  fixes A :: "real^'n::finite^'n"
  assumes sym: "transpose A = A" and q: "norm q = 1"
    and eigq: "A *v q = (q \<bullet> (A *v q)) *\<^sub>R q"
  shows "\<exists>B. onormal B \<and> span B = UNIV \<and> q \<in> B
      \<and> (\<forall>u\<in>B. A *v u = (u \<bullet> (A *v u)) *\<^sub>R u)
      \<and> (\<forall>u \<in> B - {q}. q \<bullet> u = 0)"
proof -
  define H where "H = {y :: real^'n. q \<bullet> y = 0}"
  have qq: "q \<bullet> q = 1"
    using q by (simp add: dot_square_norm)
  have subH: "subspace H"
    unfolding H_def by (simp add: subspace_hyperplane)
  text \<open>Bind the eigenvalue before using \<open>eigq\<close> as a rewrite: its right hand side
    mentions \<open>A *v q\<close> again, so unfolding it directly loops.\<close>
  define mu where "mu = q \<bullet> (A *v q)"
  have eigq': "A *v q = mu *\<^sub>R q"
    unfolding mu_def by (rule eigq)
  have invH: "\<forall>y\<in>H. A *v y \<in> H"
  proof (intro ballI)
    fix y assume y: "y \<in> H"
    then have qy: "q \<bullet> y = 0"
      unfolding H_def by simp
    have "q \<bullet> (A *v y) = y \<bullet> (A *v q)"
      by (rule sym_inner_swap[OF sym])
    also have "\<dots> = mu * (y \<bullet> q)"
      unfolding eigq' by simp
    also have "\<dots> = 0"
      using qy by (simp add: inner_commute)
    finally show "A *v y \<in> H"
      unfolding H_def by simp
  qed
  obtain B0 where B0: "onormal B0" "B0 \<subseteq> H" "span B0 = H"
    and eig0: "\<forall>u\<in>B0. A *v u = (u \<bullet> (A *v u)) *\<^sub>R u"
    using invariant_subspace_eigenbasis_ex[OF sym subH invH] by blast
  have finB0: "finite B0"
    by (rule onormal_finite[OF B0(1)])
  have qperp: "q \<bullet> u = 0" if u: "u \<in> B0" for u
    using u B0(2) unfolding H_def by blast
  have qnotin: "q \<notin> B0"
    using qq B0(2) unfolding H_def by auto
  define B where "B = insert q B0"
  have onB: "onormal B"
    unfolding B_def onormal_def
  proof (intro conjI)
    show "finite (insert q B0)"
      using finB0 by simp
    show "pairwise orthogonal (insert q B0)"
      using B0(1) qperp
      by (auto simp: onormal_def pairwise_insert orthogonal_def inner_commute)
    show "\<forall>u\<in>insert q B0. norm u = 1"
      using q B0(1) by (auto simp: onormal_def)
  qed
  have spanB: "span B = UNIV"
  proof -
    have "x \<in> span B" for x :: "real^'n"
    proof -
      define z where "z = x - (q \<bullet> x) *\<^sub>R q"
      have qz: "q \<bullet> z = 0"
        unfolding z_def by (simp add: inner_diff_right qq)
      then have zB0: "z \<in> span B0"
        using B0(3) unfolding H_def by simp
      have sub: "B0 \<subseteq> insert q B0"
        by blast
      have zB: "z \<in> span B"
        unfolding B_def using zB0 span_mono[OF sub] by blast
      have qB: "q \<in> span B"
        unfolding B_def by (simp add: span_base)
      have "x = (q \<bullet> x) *\<^sub>R q + z"
        unfolding z_def by simp
      also have "\<dots> \<in> span B"
        using qB zB by (intro span_add span_scale)
      finally show ?thesis .
    qed
    then show ?thesis by auto
  qed
  have eigB: "\<forall>u\<in>B. A *v u = (u \<bullet> (A *v u)) *\<^sub>R u"
    unfolding B_def
  proof (intro ballI)
    fix u assume uin: "u \<in> insert q B0"
    show "A *v u = (u \<bullet> (A *v u)) *\<^sub>R u"
    proof (cases "u = q")
      case True
      show ?thesis
        unfolding True by (rule eigq)
    next
      case False
      then have "u \<in> B0"
        using uin by simp
      then show ?thesis
        using eig0 by blast
    qed
  qed
  have restperp: "\<forall>u \<in> B - {q}. q \<bullet> u = 0"
    unfolding B_def using qperp by auto
  have qBmem: "q \<in> B"
    unfolding B_def by simp
  show ?thesis
    by (rule exI[of _ B]) (intro conjI onB spanB qBmem eigB restperp)
qed


lemma exists_top_eigenvector:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M"
  shows "\<exists>q. norm q = 1 \<and> M *v q = (q \<bullet> (M *v q)) *\<^sub>R q
      \<and> q \<bullet> (M *v q) = eigval 1 M"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have pos: "0 < CARD('n)"
    by (simp add: card_gt_0_iff)
  have oneB: "1 \<le> card B"
    using pos cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = 1"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T
        \<Longrightarrow> v \<bullet> (M *v v) \<le> u \<bullet> (M *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (M *v u)", OF finB oneB]
    by metis
  obtain q where Tq: "T = {q}"
    using T(2) by (metis card_1_singletonE)
  have qB: "q \<in> B"
    using T(1) Tq by blast
  have nq: "norm q = 1"
    using qB B(1) by (simp add: onormal_def)
  have eigq: "M *v q = (q \<bullet> (M *v q)) *\<^sub>R q"
    by (rule eig[OF qB])
  have "kyfan 1 M = (\<Sum>u\<in>T. u \<bullet> (M *v u))"
    by (rule kyfan_threshold[OF B sym eig T(1) T(2) thresh])
  then have "kyfan 1 M = q \<bullet> (M *v q)"
    unfolding Tq by simp
  moreover have "eigval 1 (M :: real^'n^'n) = kyfan 1 M"
    by (rule eigval_1)
  ultimately have top: "q \<bullet> (M *v q) = eigval 1 M"
    by simp
  show ?thesis
    by (rule exI[of _ q]) (intro conjI nq eigq top)
qed

text \<open>The Ky Fan sums of \<open>M\<^sub>q\<^sub>1\<close> are those of \<open>M\<close> shifted by one and reduced
  by \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close>.  Since the \<open>q\<^sub>1\<close>-direction eigenvalue of \<open>M\<^sub>q\<^sub>1\<close> is minimal, a
  top-\<open>j\<close> set can be taken inside \<open>B - {q\<^sub>1}\<close>; since \<open>q\<^sub>1\<close> attains the
  maximum for \<open>M\<close>, a top-\<open>(j+1)\<close> set can be taken to contain it.\<close>


lemma dim_inter_ge:
  fixes S W :: "(real^'n::finite) set"
  assumes S: "subspace S" and W: "subspace W"
  shows "dim S + dim W \<le> dim (S \<inter> W) + CARD('n)"
proof -
  have key: "dim {x + y |x y. x \<in> S \<and> y \<in> W} + dim (S \<inter> W) = dim S + dim W"
    by (rule dim_sums_Int[OF S W])
  have le: "dim {x + y |x y. x \<in> S \<and> y \<in> W} \<le> CARD('n)"
    by (rule dim_subset_UNIV_cart)
  show ?thesis
    using key le by simp
qed

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
  have finT: "finite T"
    using T(1) finB by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using T(2) m by auto
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    using finite_arg_min_on[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
        OF finT Tne] by metis
  obtain i where mi: "m = Suc i"
    using m by (cases m) auto
  have cardT: "card T = Suc i"
    using T(2) mi by simp
  have eigw: "eigval m a = w \<bullet> (a *v w)"
    unfolding mi
    by (rule eigval_eq_min_of_threshold[OF B sym eig T(1) cardT thresh w wmin])
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


lemma possum_lipschitz:
  fixes A B :: "real^'n::finite^'n"
  assumes symA: "transpose A = A" and symB: "transpose B = B"
    and m: "m \<le> CARD('n)"
  shows "\<bar>possum m A - possum m B\<bar>
       \<le> real CARD('n) * entrysum (A - B)"
proof -
  have fin: "finite ((\<lambda>j. kyfan j A) ` {..m})"
    by simp
  have ne: "(\<lambda>j. kyfan j A) ` {..m} \<noteq> {}"
    by simp
  have step: "\<bar>kyfan j A - kyfan j B\<bar> \<le> real CARD('n) * entrysum (A - B)"
    if j: "j \<le> m" for j
  proof -
    have jn: "j \<le> CARD('n)"
      using j m by simp
    have "\<bar>kyfan j A - kyfan j B\<bar> \<le> real j * entrysum (A - B)"
      by (rule kyfan_lipschitz[OF symA symB jn])
    also have "\<dots> \<le> real CARD('n) * entrysum (A - B)"
      using jn entrysum_nonneg[of "A - B"] by (simp add: mult_right_mono)
    finally show ?thesis .
  qed
  have "possum m A \<le> possum m B + real CARD('n) * entrysum (A - B)"
    unfolding possum_def[of m A]
  proof (rule Max.boundedI[OF fin ne])
    fix y assume "y \<in> (\<lambda>j. kyfan j A) ` {..m}"
    then obtain j where j: "j \<le> m" and y: "y = kyfan j A"
      by auto
    have a: "kyfan j A \<le> kyfan j B + real CARD('n) * entrysum (A - B)"
      using step[OF j] by simp
    have b: "kyfan j B \<le> possum m B"
      by (rule possum_ge_kyfan[OF j])
    show "y \<le> possum m B + real CARD('n) * entrysum (A - B)"
      unfolding y using a b by simp
  qed
  moreover have "possum m B \<le> possum m A + real CARD('n) * entrysum (A - B)"
  proof -
    have finB: "finite ((\<lambda>j. kyfan j B) ` {..m})"
      by simp
    have neB: "(\<lambda>j. kyfan j B) ` {..m} \<noteq> {}"
      by simp
    show ?thesis
      unfolding possum_def[of m B]
    proof (rule Max.boundedI[OF finB neB])
      fix y assume "y \<in> (\<lambda>j. kyfan j B) ` {..m}"
      then obtain j where j: "j \<le> m" and y: "y = kyfan j B"
        by auto
      have a: "kyfan j B \<le> kyfan j A + real CARD('n) * entrysum (A - B)"
        using step[OF j] by simp
      have b: "kyfan j A \<le> possum m A"
        by (rule possum_ge_kyfan[OF j])
      show "y \<le> possum m A + real CARD('n) * entrysum (A - B)"
        unfolding y using a b by simp
    qed
  qed
  ultimately show ?thesis
    by simp
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


lemma inner_outer_prod_self:
  fixes u v :: "real^'n::finite"
  shows "outer_prod u v \<bullet> outer_prod u v = (u \<bullet> u) * (v \<bullet> v)"
proof -
  have "outer_prod u v \<bullet> outer_prod u v
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (u $ i * v $ j) * (u $ i * v $ j))"
    unfolding outer_prod_def inner_vec_def by simp
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (u $ i * u $ i) * (\<Sum>j\<in>(UNIV :: 'n set). v $ j * v $ j))"
    by (intro sum.cong refl) (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). u $ i * u $ i)
      * (\<Sum>j\<in>(UNIV :: 'n set). v $ j * v $ j)"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (u \<bullet> u) * (v \<bullet> v)"
    unfolding inner_vec_def by simp
  finally show ?thesis .
qed


lemma norm_outer_prod:
  fixes u v :: "real^'n::finite"
  shows "norm (outer_prod u v) = norm u * norm v"
proof -
  have "norm (outer_prod u v) = sqrt (outer_prod u v \<bullet> outer_prod u v)"
    by (simp add: norm_eq_sqrt_inner)
  also have "\<dots> = sqrt ((u \<bullet> u) * (v \<bullet> v))"
    by (simp add: inner_outer_prod_self)
  also have "\<dots> = sqrt (u \<bullet> u) * sqrt (v \<bullet> v)"
    by (simp add: real_sqrt_mult)
  also have "\<dots> = norm u * norm v"
    by (simp add: norm_eq_sqrt_inner)
  finally show ?thesis .
qed


lemma outer_prod_diff_left:
  fixes u v w :: "real^'n::finite"
  shows "outer_prod (u - v) w = outer_prod u w - outer_prod v w"
  unfolding outer_prod_def by (simp add: vec_eq_iff left_diff_distrib)


lemma outer_prod_diff_right:
  fixes u v w :: "real^'n::finite"
  shows "outer_prod u (v - w) = outer_prod u v - outer_prod u w"
  unfolding outer_prod_def by (simp add: vec_eq_iff right_diff_distrib)


lemma norm_unit_diff_le:
  fixes p p' :: "real^'n::finite"
  assumes p: "p \<noteq> 0" and p': "p' \<noteq> 0"
  shows "norm (p' /\<^sub>R norm p' - p /\<^sub>R norm p) \<le> 2 * norm (p' - p) / norm p"
proof -
  have np: "0 < norm p"
    using p by simp
  have np': "0 < norm p'"
    using p' by simp
  have split: "p' /\<^sub>R norm p' - p /\<^sub>R norm p
      = (p' - p) /\<^sub>R norm p + (inverse (norm p') - inverse (norm p)) *\<^sub>R p'"
    by (simp add:
        algebra_simps)
  have t1: "norm ((p' - p) /\<^sub>R norm p) = norm (p' - p) / norm p"
    using np by (simp add: divide_inverse mult.commute)
  have t2: "norm ((inverse (norm p') - inverse (norm p)) *\<^sub>R p')
      \<le> norm (p' - p) / norm p"
  proof -
    have "\<bar>inverse (norm p') - inverse (norm p)\<bar>
        = \<bar>norm p - norm p'\<bar> / (norm p' * norm p)"
      using np np' by (simp add: field_simps abs_mult_pos abs_minus_commute)
    then have "norm ((inverse (norm p') - inverse (norm p)) *\<^sub>R p')
        = \<bar>norm p - norm p'\<bar> / (norm p' * norm p) * norm p'"
      by simp
    also have "\<dots> = \<bar>norm p - norm p'\<bar> / norm p"
      using np' by simp
    also have "\<dots> \<le> norm (p' - p) / norm p"
      using np norm_triangle_ineq3[of p p'] 
      by (simp add: divide_right_mono abs_minus_commute norm_minus_commute)
    finally show ?thesis .
  qed
  have "norm (p' /\<^sub>R norm p' - p /\<^sub>R norm p)
      \<le> norm ((p' - p) /\<^sub>R norm p)
        + norm ((inverse (norm p') - inverse (norm p)) *\<^sub>R p')"
    unfolding split by (rule norm_triangle_ineq)
  also have "\<dots> \<le> norm (p' - p) / norm p + norm (p' - p) / norm p"
    using t1 t2 by simp
  also have "\<dots> = 2 * norm (p' - p) / norm p"
    by simp
  finally show ?thesis .
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


lemma norm_mat_1:
  shows "norm (mat 1 :: real^'n::finite^'n) = sqrt (real CARD('n))"
proof -
  have "(mat 1 :: real^'n^'n) \<bullet> (mat 1 :: real^'n^'n)
      = (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set).
          (if i = j then 1 else 0) * (if i = j then (1 :: real) else 0))"
    unfolding inner_vec_def mat_def by simp
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (1 :: real))"
  proof (intro sum.cong refl)
    fix i :: 'n
    have "(\<Sum>j\<in>(UNIV :: 'n set).
            (if i = j then 1 else 0) * (if i = j then (1 :: real) else 0))
        = (\<Sum>j\<in>(UNIV :: 'n set). (if i = j then (1 :: real) else 0))"
      by (intro sum.cong refl) simp
    also have "\<dots> = 1"
      by simp
    finally show "(\<Sum>j\<in>(UNIV :: 'n set).
        (if i = j then 1 else 0) * (if i = j then (1 :: real) else 0)) = 1" .
  qed
  also have "\<dots> = real CARD('n)"
    by simp
  finally have "(mat 1 :: real^'n^'n) \<bullet> (mat 1 :: real^'n^'n) = real CARD('n)" .
  then show ?thesis
    by (simp add: norm_eq_sqrt_inner)
qed

text \<open>Hence the projection onto \<open>p\<^sup>\<bottom>\<close> is bounded independently of \<open>p\<close>.\<close>


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

text \<open>The four-term bound.  Each term is a product of at most three factors, so
  submultiplicativity of the Frobenius norm applies; \<open>norm D \<le> 2\<close> because both
  projections have norm \<open>1\<close>, and \<open>norm Q \<le> \<surd>n + 1\<close>.\<close>


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

text \<open>Assembling: \<open>M\<^sub>p\<close> is Lipschitz in \<open>p\<close> away from the origin.  The
  correction coefficient \<open>c = min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close> is \<open>p\<close>-independent, so it
  contributes only \<open>\<bar>c\<bar> * norm D\<close>.\<close>


lemma entry_abs_le_norm:
  fixes D :: "real^'n::finite^'n"
  shows "\<bar>D $ i $ j\<bar> \<le> norm D"
proof -
  have "\<bar>D $ i $ j\<bar> \<le> norm (D $ i)"
    by (rule component_le_norm_cart)
  also have "\<dots> \<le> norm D"
    by (rule Finite_Cartesian_Product.norm_nth_le)
  finally show ?thesis .
qed


lemma entrysum_le_norm:
  fixes D :: "real^'n::finite^'n"
  shows "entrysum D \<le> real (CARD('n) * CARD('n)) * norm D"
proof -
  have "entrysum D = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>D $ i $ j\<bar>)"
    unfolding entrysum_def by (rule refl)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). norm D)"
    by (intro sum_mono entry_abs_le_norm)
  also have "\<dots> = real (CARD('n) * CARD('n)) * norm D"
    by simp
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


text \<open>\<open>continuous_on_matrix_entry\<close> lives in
  @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

lemma continuous_on_quadform:
  fixes x :: "real^'n::finite"
  shows "continuous_on UNIV (\<lambda>a :: real^'n^'n. x \<bullet> (a *v x))"
proof -
  have eq: "x \<bullet> (a *v x) = (\<Sum>i\<in>UNIV. x $ i * (\<Sum>j\<in>UNIV. a $ i $ j * x $ j))"
    for a :: "real^'n^'n"
    unfolding inner_vec_def matrix_vector_mult_def by simp
  show ?thesis
    unfolding eq
    by (intro continuous_intros continuous_on_matrix_entry continuous_on_id)
qed


lemma closed_symmetric_matrices:
  "closed {a :: real^'n::finite^'n. transpose a = a}"
proof -
  have eq: "{a :: real^'n^'n. transpose a = a}
      = (\<Inter>i. \<Inter>j. {a. a $ j $ i = a $ i $ j})"
    unfolding transpose_def vec_eq_iff by auto
  have "closed {a :: real^'n^'n. a $ j $ i = a $ i $ j}" for i j
    by (intro closed_Collect_eq continuous_on_matrix_entry continuous_on_id)
  thus ?thesis unfolding eq by (intro closed_INT) auto
qed


lemma closed_psd: "closed {a :: real^'n::finite^'n. psd a}"
proof -
  have eq: "{a :: real^'n^'n. psd a}
      = {a. transpose a = a} \<inter> (\<Inter>x. {a. 0 \<le> x \<bullet> (a *v x)})"
    unfolding psd_def by auto
  have "closed {a :: real^'n^'n. 0 \<le> x \<bullet> (a *v x)}" for x
    by (intro closed_Collect_le continuous_on_quadform continuous_on_const)
  thus ?thesis
    unfolding eq
    by (intro closed_Int closed_symmetric_matrices closed_INT) auto
qed



(*<*)
end
(*>*)
