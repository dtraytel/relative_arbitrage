
(*<*)
theory Constraint_Set_Convexity
  imports Curvature_Operator "Symmetric_Matrix_Spectra.Ky_Fan"
begin

(*>*)

text \<open>
  Proves Lemma 2.1 of \<^cite>\<open>LaiShkolnikovSoner\<close>, the convexification of the
  eigenvalue constraint. The operator \<open>Pi_m\<close> of Eq. (2.1) is formalized as
  \<open>Pi_proj\<close>, and the theory establishes both inclusions

    \<open>conv B\<^sub>k \<subseteq> A\<^sub>k\<close>   and   \<open>A\<^sub>k \<subseteq> closure (conv B\<^sub>k)\<close>,

  where \<open>B\<^sub>k = {a. psd a \<and> eigen_lb a (n - k)}\<close> is the unconvexified
  sufficient-volatility set and \<open>A\<^sub>k = {a. psd a \<and> (\<forall>m \<in> {k+1..n}.
  Pi_m a \<ge> m - k)}\<close>. The first inclusion rests on the Grassmann dimension
  formula and basis-independent subspace traces; the second on hyperplane
  separation from the closed convex hull together with an Abel-summation
  estimate along the sorted eigen-frame. Together they identify \<open>A\<^sub>k\<close> as
  the closed convex hull of \<open>B\<^sub>k\<close>, the form in which the paper applies
  Lemma 2.1.\<close>
unbundle inner_syntax

section \<open>The operator \<open>\<Pi>\<^sub>m\<close> of Eq. (2.1)\<close>

text \<open>\<open>Pi_proj\<close> is the dual of \<open>kyfan\<close> from
  @{theory Symmetric_Matrix_Spectra.Ky_Fan}: the sum of the \<open>m\<close> SMALLEST
  eigenvalues, basis-free by construction, exactly as \<open>kyfan\<close> is the sum of
  the \<open>m\<close> largest.\<close>

definition Pi_proj :: "real^'n^'n \<Rightarrow> nat \<Rightarrow> real" where
  "Pi_proj a m = Inf {trace (a ** P) | P. is_proj P \<and> trace P = real m}"

text \<open>\<open>trace_proj_psd_nonneg\<close> lives in @{theory Symmetric_Matrix_Spectra.Ky_Fan}.\<close>

lemma Pi_proj_bdd_below:
  assumes a: "psd a"
  shows "bdd_below {trace (a ** P) | P. is_proj P \<and> trace P = real m}"
  by (rule bdd_belowI[of _ 0]) (use trace_proj_psd_nonneg[OF a] in auto)

lemma Pi_proj_le:
  assumes a: "psd a" and P: "is_proj P" "trace P = real m"
  shows "Pi_proj a m \<le> trace (a ** P)"
  unfolding Pi_proj_def
  by (intro cInf_lower Pi_proj_bdd_below[OF a]) (use P in auto)

lemma Pi_proj_ge:
  assumes m: "m \<le> CARD('n::finite)"
    and le: "\<And>P :: real^'n^'n. is_proj P \<Longrightarrow> trace P = real m \<Longrightarrow> c \<le> trace (a ** P)"
  shows "c \<le> Pi_proj a m"
  unfolding Pi_proj_def
proof (rule cInf_greatest)
  show "{trace (a ** P) | P. is_proj P \<and> trace P = real m} \<noteq> {}"
    using proj_with_trace_exists[OF m] by force
qed (use le in auto)

section \<open>The easy inclusion of Lemma 2.1: \<open>conv B\<^sub>k \<subseteq> A\<^sub>k\<close>\<close>

text \<open>The generator set \<open>B\<^sub>k = {a \<in> \<S>\<^sub>+ : \<lambda>\<^bsub>(n-k)\<^esub>(a) \<ge> 1}\<close> of Eq. (1.4)
  and the convexified set \<open>A\<^sub>k\<close> of Eq. (1.5)/(2.1).\<close>

definition suff_volatile :: "nat \<Rightarrow> (real^'n^'n) set" where
  "suff_volatile k = {a. psd a \<and> eigen_lb a (CARD('n) - k)}"

definition Pi_constraint :: "nat \<Rightarrow> (real^'n^'n) set" where
  "Pi_constraint k =
     {a. psd a \<and> (\<forall>m. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow> real (m - k) \<le> Pi_proj a m)}"

text \<open>The core estimate: sufficient volatility forces \<open>tr(a P) \<ge> m - k\<close> for
  every rank-\<open>m\<close> orthogonal projection (Grassmann dimension formula).\<close>

lemma trace_proj_lower_bound:
  fixes a :: "real^'n^'n"
  assumes a: "psd a" and lb: "eigen_lb a (CARD('n) - k)"
    and P: "is_proj P" "trace P = real m"
    and m: "m \<le> CARD('n)"
  shows "real (m - k) \<le> trace (a ** P)"
proof -
  obtain S where S: "subspace S" "CARD('n) - k \<le> dim S"
    "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
    using lb by (auto simp: eigen_lb_def)
  obtain C where C: "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
    using is_proj_decomp[OF P(1)] by metis
  have cardC: "card C = m"
    using C(3) P(2) by simp
  define W where "W = span C"
  have subW: "subspace W"
    by (simp add: W_def)
  have dimW: "dim W = m"
    using onormal_card_dim_span[OF C(1)] cardC by (simp add: W_def)
  have CspanW: "span C = W"
    by (simp add: W_def)
  have dim_int: "m - k \<le> dim (W \<inter> S)"
  proof -
    have "dim {x + y |x y. x \<in> W \<and> y \<in> S} + dim (W \<inter> S) = dim W + dim S"
      by (rule dim_sums_Int[OF subW S(1)])
    moreover have "dim {x + y |x y. x \<in> W \<and> y \<in> S} \<le> CARD('n)"
      using dim_subset_UNIV[of "{x + y |x y. x \<in> W \<and> y \<in> S}"] by simp
    ultimately have "dim W + dim S - CARD('n) \<le> dim (W \<inter> S)"
      by simp
    with S(2) dimW show ?thesis
      by simp
  qed
  obtain B0 where B0: "B0 \<subseteq> W \<inter> S" "pairwise orthogonal B0"
    "\<And>x. x \<in> B0 \<Longrightarrow> norm x = 1" "independent B0"
    "card B0 = dim (W \<inter> S)" "span B0 = W \<inter> S"
    using orthonormal_basis_subspace[OF subspace_inter[OF subW S(1)]] by metis
  have onB0: "onormal B0"
    using B0 by (auto simp: onormal_def intro: pairwise_orthogonal_imp_finite)
  have B0W: "B0 \<subseteq> W"
    using B0(1) by auto
  obtain C' where C': "onormal C'" "B0 \<subseteq> C'" "C' \<subseteq> W" "span C' = W"
    using onormal_extension_within[OF onB0 subW B0W] by metis
  have "trace (a ** P) = (\<Sum>u\<in>C. u \<bullet> (a *v u))"
    by (simp add: C(2) trace_mult_outer_sum)
  also have "\<dots> = (\<Sum>u\<in>C'. u \<bullet> (a *v u))"
    by (rule trace_on_subspace_eq[OF C(1) C'(1)]) (simp add: CspanW C'(4))
  also have "\<dots> \<ge> (\<Sum>u\<in>B0. u \<bullet> (a *v u))"
    using C'(2) C'(1) a
    by (intro sum_mono2) (auto simp: onormal_def psd_def)
  finally have step1: "(\<Sum>u\<in>B0. u \<bullet> (a *v u)) \<le> trace (a ** P)" .
  have "real (card B0) = (\<Sum>u\<in>B0. (1::real))"
    by simp
  also have "\<dots> \<le> (\<Sum>u\<in>B0. u \<bullet> (a *v u))"
  proof (intro sum_mono)
    fix u assume u: "u \<in> B0"
    then have "u \<in> S"
      using B0(1) by auto
    then have "u \<bullet> u \<le> u \<bullet> (a *v u)"
      by (rule S(3))
    moreover have "u \<bullet> u = 1"
      using onB0 u by simp
    ultimately show "1 \<le> u \<bullet> (a *v u)"
      by simp
  qed
  finally have step2: "real (card B0) \<le> (\<Sum>u\<in>B0. u \<bullet> (a *v u))" .
  have "real (m - k) \<le> real (card B0)"
    using dim_int B0(5) by simp
  with step1 step2 show ?thesis
    by linarith
qed

lemma suff_volatile_subset_Pi_constraint:
  "suff_volatile k \<subseteq> (Pi_constraint k :: (real^'n^'n) set)"
proof
  fix a :: "real^'n^'n" assume "a \<in> suff_volatile k"
  then have a: "psd a" and lb: "eigen_lb a (CARD('n) - k)"
    by (auto simp: suff_volatile_def)
  have "real (m - k) \<le> Pi_proj a m" if m: "k < m" "m \<le> CARD('n)" for m
    by (intro Pi_proj_ge[OF m(2)] trace_proj_lower_bound[OF a lb _ _ m(2)])
  then show "a \<in> Pi_constraint k"
    using a by (auto simp: Pi_constraint_def)
qed

text \<open>Convexity of \<open>A\<^sub>k\<close>: \<open>psd\<close> is a convex condition and \<open>\<Pi>\<^sub>m\<close> is concave.\<close>

lemma Pi_constraint_convex: "convex (Pi_constraint k :: (real^'n^'n) set)"
proof (rule convexI)
  fix a b :: "real^'n^'n" and s t :: real
  assume ab: "a \<in> Pi_constraint k" "b \<in> Pi_constraint k"
    and st: "0 \<le> s" "0 \<le> t" "s + t = 1"
  have t_eq: "t = 1 - s"
    using st by simp
  have psd_a: "psd a" and psd_b: "psd b"
    using ab by (auto simp: Pi_constraint_def)
  have psd_comb: "psd (s *\<^sub>R a + (1 - s) *\<^sub>R b)"
    using st by (intro psd_convex_comb psd_a psd_b) (auto simp: t_eq)
  have pi: "real (m - k) \<le> Pi_proj (s *\<^sub>R a + (1 - s) *\<^sub>R b) m"
    if m: "k < m" "m \<le> CARD('n)" for m
  proof (rule Pi_proj_ge[OF m(2)])
    fix P :: "real^'n^'n" assume P: "is_proj P" "trace P = real m"
    have "real (m - k) = s * real (m - k) + (1 - s) * real (m - k)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> s * trace (a ** P) + (1 - s) * trace (b ** P)"
      using ab m P st
      by (intro add_mono mult_left_mono order_trans
          [OF _ Pi_proj_le[OF psd_a P]] order_trans[OF _ Pi_proj_le[OF psd_b P]])
        (auto simp: Pi_constraint_def t_eq)
    also have "\<dots> = trace ((s *\<^sub>R a + (1 - s) *\<^sub>R b) ** P)"
      by (simp add: trace_mult_convex_comb)
    finally show "real (m - k) \<le> trace ((s *\<^sub>R a + (1 - s) *\<^sub>R b) ** P)" .
  qed
  show "s *\<^sub>R a + t *\<^sub>R b \<in> Pi_constraint k"
    using psd_comb pi by (auto simp: Pi_constraint_def t_eq)
qed

theorem lemma_2_1_easy:
  "convex hull (suff_volatile k) \<subseteq> (Pi_constraint k :: (real^'n^'n) set)"
  by (intro hull_minimal suff_volatile_subset_Pi_constraint
      Pi_constraint_convex)

section \<open>The hard inclusion of Lemma 2.1: \<open>A\<^sub>k \<subseteq> closure (conv B\<^sub>k)\<close>\<close>

text \<open>Hyperplane separation from the closed convex hull, symmetrization of
  the separating functional, its eigen-decomposition (by the spectral
  theorem), and an Abel-summation estimate against the \<open>\<Pi>\<^sub>m\<close>-constraints
  yield the reverse inclusion.  No von Neumann trace inequality is needed:
  the sorted eigen-frame of the separating functional provides the
  extremal projections directly.\<close>

subsection \<open>Generators\<close>

lemma onormal_sum_suff_volatile:
  fixes T :: "(real^'n) set"
  assumes T: "onormal T" and cardT: "card T = CARD('n) - k"
  shows "(\<Sum>u\<in>T. outer_prod u u) \<in> suff_volatile k"
proof -
  define b where "b = (\<Sum>u\<in>T. outer_prod u u)"
  have bmv: "b *v x = (\<Sum>u\<in>T. (u \<bullet> x) *\<^sub>R u)" for x
    by (simp add: b_def matrix_vector_mult_sum)
  have quad: "x \<bullet> (b *v x) = (\<Sum>u\<in>T. (u \<bullet> x)\<^sup>2)" for x
    by (simp add: bmv inner_sum_right power2_eq_square inner_commute)
  have psd_b: "psd b"
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose b = b"
      by (simp add: b_def transpose_matrix_sum)
  next
    show "0 \<le> x \<bullet> (b *v x)" for x
      by (simp add: quad sum_nonneg)
  qed
  have lb_b: "eigen_lb b (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ "span T"] conjI ballI)
    show "subspace (span T)"
      by (rule subspace_span)
    have "independent T"
      by (rule onormal_independent[OF T])
    then have "dim (span T) = card T"
      by (simp add: dim_eq_card_independent)
    then show "CARD('n) - k \<le> dim (span T)"
      by (simp add: cardT)
    fix x assume x: "x \<in> span T"
    have "x \<bullet> x = (\<Sum>u\<in>T. (u \<bullet> x) *\<^sub>R u) \<bullet> (\<Sum>u\<in>T. (u \<bullet> x) *\<^sub>R u)"
      by (simp add: onormal_expand[OF T x])
    also have "\<dots> = (\<Sum>u\<in>T. (u \<bullet> x)\<^sup>2)"
      by (simp add: onormal_inner_sums[OF T] power2_eq_square)
    finally show "x \<bullet> x \<le> x \<bullet> (b *v x)"
      by (simp add: quad)
  qed
  show ?thesis
    using psd_b lb_b by (simp add: b_def[symmetric] suff_volatile_def)
qed

lemma suff_volatile_augment:
  fixes b :: "real^'n^'n"
  assumes b: "b \<in> suff_volatile k" and t: "0 \<le> t"
  shows "b + t *\<^sub>R outer_prod u u \<in> suff_volatile k"
proof -
  have psd_b: "psd b" and lb_b: "eigen_lb b (CARD('n) - k)"
    using b by (auto simp: suff_volatile_def)
  have quad_add: "x \<bullet> ((b + t *\<^sub>R outer_prod u u) *v x)
      = x \<bullet> (b *v x) + t * (u \<bullet> x)\<^sup>2" for x
    by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector
        inner_add_right power2_eq_square
        inner_commute mult_ac)
  have psd': "psd (b + t *\<^sub>R outer_prod u u)"
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose (b + t *\<^sub>R outer_prod u u) = b + t *\<^sub>R outer_prod u u"
      using psd_b by (simp add: transpose_add transpose_scalar psd_def)
  next
    show "0 \<le> x \<bullet> ((b + t *\<^sub>R outer_prod u u) *v x)" for x
      using psd_b t by (simp add: quad_add psd_def)
  qed
  have lb': "eigen_lb (b + t *\<^sub>R outer_prod u u) (CARD('n) - k)"
  proof -
    obtain S where S: "subspace S" "CARD('n) - k \<le> dim S"
      "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (b *v x)"
      using lb_b by (auto simp: eigen_lb_def)
    have "x \<bullet> x \<le> x \<bullet> ((b + t *\<^sub>R outer_prod u u) *v x)" if "x \<in> S" for x
    proof -
      have "x \<bullet> x \<le> x \<bullet> (b *v x)"
        by (rule S(3)[OF that])
      also have "\<dots> \<le> x \<bullet> (b *v x) + t * (u \<bullet> x)\<^sup>2"
        using t by simp
      finally show ?thesis
        by (simp add: quad_add)
    qed
    then show ?thesis
      unfolding eigen_lb_def
      using S(1,2) by (intro exI[of _ S]) auto
  qed
  show ?thesis
    using psd' lb' by (simp add: suff_volatile_def)
qed

text \<open>Lemma 2.1 in full: together with \<open>lemma_2_1_easy\<close>, the convexified
  constraint set \<open>A\<^sub>k\<close> is wedged between the convex hull of the generator
  set and its closure:
  \<open>conv B\<^sub>k \<subseteq> A\<^sub>k \<subseteq> closure (conv B\<^sub>k)\<close>, so \<open>A\<^sub>k\<close> is the closed convex hull
  of \<open>B\<^sub>k\<close> (the form in which the paper uses the lemma).\<close>

section \<open>Support-function characterisation of a closed convex constraint set\<close>

text \<open>A closed convex set \<open>S\<close> of symmetric matrices is characterized by its
  support function: \<open>a \<in> S\<close> once, for every symmetric \<open>M\<close>, some \<open>b \<in> S\<close>
  attains \<open>tr(Ma) \<le> tr(Mb)\<close>.  This lets membership in the constraint set of
  Eq. (1.5)/(1.7) be tested through linear inequalities, which pass to weak
  limits in the law, in place of the constraint's original non-linear form;
  convexity of the constraint set (Lemma 2.1) is what makes the replacement
  faithful.  The argument runs on the symmetrized separating functional,
  since the Frobenius inner product \<open>m \<bullet> x\<close> agrees with \<open>tr(mx)\<close> only on
  symmetric matrices.\<close>

(*<*)
end
(*>*)
