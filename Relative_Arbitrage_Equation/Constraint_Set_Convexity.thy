
(*<*)
theory Constraint_Set_Convexity
  imports Elliptic_Operator "Symmetric_Matrix_Spectra.Ky_Fan"
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
  Lemma 2.1.  The last part removes the closure: \<open>A\<^sub>k = conv B\<^sub>k\<close>
  (\<open>lemma_2_1_exact\<close>).\<close>
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
  using onormal_outer_sum_props(1,2)[OF T] cardT by (simp add: suff_volatile_def)

lemma suff_volatile_augment:
  fixes b :: "real^'n^'n"
  assumes b: "b \<in> suff_volatile k" and t: "0 \<le> t"
  shows "b + t *\<^sub>R outer_prod u u \<in> suff_volatile k"
proof -
  have psd_b: "psd b" and lb_b: "eigen_lb b (CARD('n) - k)"
    using b by (auto simp: suff_volatile_def)
  have quad_add: "x \<bullet> ((b + t *\<^sub>R outer_prod u u) *v x)
      = x \<bullet> (b *v x) + t * (u \<bullet> x)\<^sup>2" for x
    by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector_assoc[symmetric]
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

section \<open>Lemma 2.1 in its exact form\<close>

text \<open>Lemma 2.1 of \<^cite>\<open>LaiShkolnikovSoner\<close> in its exact form, with
  the convex hull itself rather than its closure.  Building on
  \<open>A\<^sub>k \<subseteq> closure (conv B\<^sub>k)\<close> above, it
  establishes equality with \<open>conv B\<^sub>k\<close> in three steps: a capped trace
  bound \<open>(\<Sum>u. min (lambda\<^sub>u, 1)) \<ge> n - k\<close> for \<open>a \<in> A\<^sub>k\<close> with eigenbasis
  values \<open>lambda\<^sub>u\<close>; a hypersimplex decomposition of any combination
  \<open>\<Sum>u c\<^sub>u (u u\<^sup>T)\<close> with coefficients in \<open>[0,1]\<close> summing to \<open>n - k\<close> into
  elements of \<open>conv B\<^sub>k\<close>; and an assembly step that caps the eigenvalues
  at \<open>1\<close>, rescales, decomposes, and adds back the nonnegative remainder.\<close>

subsection \<open>The hypersimplex decomposition\<close>

text \<open>Base case of the swap induction: if every coefficient is already \<open>0\<close>
  or \<open>1\<close>, the combination is the spectral projection onto the coefficient-\<open>1\<close>
  coordinates, of which there are exactly \<open>n - k\<close>, so it is a generator.\<close>

lemma diag_integral_suff_volatile:
  fixes B :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes B: "onormal B"
    and c01: "\<And>u. u \<in> B \<Longrightarrow> c u \<in> {0, 1}"
    and csum: "(\<Sum>u\<in>B. c u) = real (CARD('n) - k)"
  shows "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) \<in> suff_volatile k"
proof -
  have finB: "finite B"
    using B by (simp add: onormal_def)
  define T where "T = {u \<in> B. c u = 1}"
  have T_sub: "T \<subseteq> B"
    by (auto simp: T_def)
  have zero_off: "c u = 0" if "u \<in> B - T" for u
    using that c01 by (auto simp: T_def)
  have sum_eq: "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) = (\<Sum>u\<in>T. outer_prod u u)"
  proof -
    have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) = (\<Sum>u\<in>T. c u *\<^sub>R outer_prod u u)"
      by (rule sum.mono_neutral_right[OF finB T_sub]) (simp add: zero_off)
    also have "\<dots> = (\<Sum>u\<in>T. outer_prod u u)"
      by (rule sum.cong[OF refl]) (simp add: T_def)
    finally show ?thesis .
  qed
  have cardT: "card T = CARD('n) - k"
  proof -
    have "(\<Sum>u\<in>B. c u) = (\<Sum>u\<in>T. c u)"
      by (rule sum.mono_neutral_right[OF finB T_sub]) (simp add: zero_off)
    also have "\<dots> = real (card T)"
      by (simp add: T_def)
    finally show ?thesis
      using csum by simp
  qed
  show ?thesis
    unfolding sum_eq
    by (rule onormal_sum_suff_volatile[OF onormal_subset[OF B T_sub] cardT])
qed

text \<open>Moving mass \<open>s\<close> from coordinate \<open>j\<close> to coordinate \<open>i\<close>.  Both swapped
  configurations of the induction step are of this form, so the arithmetic is
  done once.\<close>

definition shift :: "('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> ('a \<Rightarrow> real)" where
  "shift c i j s =
     (\<lambda>u. if u = i then c u + s else if u = j then c u - s else c u)"

lemma shift_i [simp]: "i \<noteq> j \<Longrightarrow> shift c i j s i = c i + s"
  by (simp add: shift_def)

lemma shift_j [simp]: "i \<noteq> j \<Longrightarrow> shift c i j s j = c j - s"
  by (simp add: shift_def)

lemma shift_other: "u \<noteq> i \<Longrightarrow> u \<noteq> j \<Longrightarrow> shift c i j s u = c u"
  by (simp add: shift_def)

lemma sum_shift:
  assumes fin: "finite B" and ij: "i \<in> B" "j \<in> B" "i \<noteq> j"
  shows "(\<Sum>u\<in>B. shift c i j s u) = (\<Sum>u\<in>B. c u)"
proof -
  have "(\<Sum>u\<in>B. shift c i j s u - c u) = (\<Sum>u\<in>{i, j}. shift c i j s u - c u)"
    by (rule sum.mono_neutral_right[OF fin]) (use ij in \<open>auto simp: shift_other\<close>)
  also have "\<dots> = 0"
    using ij(3) by simp
  finally have "(\<Sum>u\<in>B. shift c i j s u - c u) = 0" .
  then show ?thesis
    by (simp add: sum_subtractf)
qed

text \<open>The original coefficients are the convex combination, with weights
  \<open>d/(e+d)\<close> and \<open>e/(e+d)\<close>, of the two shifted ones.\<close>

lemma shift_convex_combination:
  assumes e: "0 < e" and d: "0 < d" and ij: "i \<noteq> j"
  shows "c u = (d / (e + d)) * shift c i j e u
             + (e / (e + d)) * shift c i j (- d) u"
proof -
  have key: "(d / (e + d)) * (x + t * e) + (e / (e + d)) * (x - t * d) = x" for x t
  proof -
    have "(d / (e + d)) * (x + t * e) + (e / (e + d)) * (x - t * d)
        = (d * (x + t * e) + e * (x - t * d)) / (e + d)"
      by (simp add: add_divide_distrib)
    also have "\<dots> = (x * (e + d)) / (e + d)"
      by (simp add: algebra_simps)
    also have "\<dots> = x"
      using e d by simp
    finally show ?thesis .
  qed
  show ?thesis
    using ij key[of "c u" 1] key[of "c u" "- 1"] key[of "c u" 0]
    by (cases "u = i"; cases "u = j") (simp_all add: shift_other)
qed

text \<open>\<open>two_fractional\<close> lives in @{theory Symmetric_Matrix_Spectra.Ky_Fan}.\<close>

text \<open>The swap induction.  The measure is the number of coefficients that are
  not yet \<open>0\<close> or \<open>1\<close>; each swap makes at least one of the two chosen
  coordinates integral without disturbing the others, and the original
  coefficients are a convex combination of the two swapped ones.\<close>

lemma diag_in_convex_hull_aux:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B"
  shows "\<And>c. card {u \<in> B. c u \<notin> {0, 1}} \<le> N \<Longrightarrow>
      (\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u) \<Longrightarrow> (\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1) \<Longrightarrow>
      (\<Sum>u\<in>B. c u) = real (CARD('n) - k) \<Longrightarrow>
      (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof (induct N)
  case 0
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  from 0(1) have "{u \<in> B. c u \<notin> {0, 1}} = {}"
    using finB by auto
  then have "c u \<in> {0, 1}" if "u \<in> B" for u
    using that by blast
  then have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) \<in> suff_volatile k"
    by (intro diag_integral_suff_volatile[OF B _ 0(4)])
  then show ?case
    using hull_subset by (rule rev_subsetD)
next
  case (Suc N)
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  show ?case
  proof (cases "{u \<in> B. c u \<notin> {0, 1}} = {}")
    case True
    then have "c u \<in> {0, 1}" if "u \<in> B" for u
      using that by blast
    then have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) \<in> suff_volatile k"
      by (intro diag_integral_suff_volatile[OF B _ Suc(5)])
    then show ?thesis
      using hull_subset by (rule rev_subsetD)
  next
    case False
    then obtain i where i: "i \<in> B" "c i \<notin> {0, 1}"
      by blast
    obtain j where j: "j \<in> B" "j \<noteq> i" "c j \<notin> {0, 1}"
      using two_fractional[OF finB i(1) i(2) Suc(3) Suc(4) Suc(5)] by blast
    have ij: "i \<noteq> j"
      using j(2) by blast
    have ci: "0 < c i" "c i < 1"
      using i(2) Suc(3)[OF i(1)] Suc(4)[OF i(1)] by auto
    have cj: "0 < c j" "c j < 1"
      using j(3) Suc(3)[OF j(1)] Suc(4)[OF j(1)] by auto
    define e where "e = min (1 - c i) (c j)"
    define d where "d = min (c i) (1 - c j)"
    have e_pos: "0 < e"
      using ci cj by (simp add: e_def)
    have d_pos: "0 < d"
      using ci cj by (simp add: d_def)
    have ed: "0 < e + d"
      using e_pos d_pos by simp

    text \<open>The two swapped coefficient vectors stay in \<open>[0,1]\<close> and keep the sum.\<close>

    have bnds: "0 \<le> shift c i j s u \<and> shift c i j s u \<le> 1"
      if s: "- d \<le> s" "s \<le> e" and u: "u \<in> B" for s u
    proof (cases "u = i")
      case True
      then show ?thesis
        using ij s ci cj by (auto simp: e_def d_def)
    next
      case ni: False
      show ?thesis
      proof (cases "u = j")
        case True
        then show ?thesis
          using ij s ci cj by (auto simp: e_def d_def)
      next
        case nj: False
        then show ?thesis
          using ni Suc(3)[OF u] Suc(4)[OF u] by (simp add: shift_other)
      qed
    qed
    have sums: "(\<Sum>u\<in>B. shift c i j s u) = real (CARD('n) - k)" for s
      using sum_shift[OF finB i(1) j(1) ij] Suc(5) by simp

    text \<open>Each swap makes \<open>i\<close> or \<open>j\<close> integral, so the measure drops.\<close>

    have drop: "card {u \<in> B. shift c i j s u \<notin> {0, 1}} \<le> N"
      if w: "w \<in> {i, j}" "shift c i j s w \<in> {0, 1}" for s w
    proof -
      have fin_frac: "finite {u \<in> B. c u \<notin> {0, 1}}"
        using finB by simp
      have wB: "w \<in> B" and wfrac: "c w \<notin> {0, 1}"
        using w(1) i j by auto
      have sub: "{u \<in> B. shift c i j s u \<notin> {0, 1}}
          \<subseteq> {u \<in> B. c u \<notin> {0, 1}} - {w}"
      proof
        fix v assume v: "v \<in> {u \<in> B. shift c i j s u \<notin> {0, 1}}"
        then have vB: "v \<in> B" and vfrac: "shift c i j s v \<notin> {0, 1}"
          by auto
        have "v \<noteq> w"
          using vfrac w(2) by blast
        moreover have "c v \<notin> {0, 1}"
        proof (cases "v \<in> {i, j}")
          case True
          then show ?thesis using i j by auto
        next
          case Fv: False
          then have "shift c i j s v = c v"
            by (simp add: shift_other)
          then show ?thesis using vfrac by simp
        qed
        ultimately show "v \<in> {u \<in> B. c u \<notin> {0, 1}} - {w}"
          using vB by simp
      qed
      have "card {u \<in> B. shift c i j s u \<notin> {0, 1}}
          \<le> card ({u \<in> B. c u \<notin> {0, 1}} - {w})"
        using fin_frac sub by (intro card_mono) auto
      also have "\<dots> = card {u \<in> B. c u \<notin> {0, 1}} - 1"
        using wB wfrac fin_frac by (simp add: card_Diff_singleton)
      also have "\<dots> \<le> N"
        using Suc(2) by simp
      finally show ?thesis .
    qed

    have bnd_e: "0 \<le> shift c i j e u" "shift c i j e u \<le> 1" if "u \<in> B" for u
      using bnds[of e u] e_pos d_pos that by auto
    have bnd_d: "0 \<le> shift c i j (- d) u" "shift c i j (- d) u \<le> 1"
      if "u \<in> B" for u
      using bnds[of "- d" u] e_pos d_pos that by auto

    have hull1: "(\<Sum>u\<in>B. shift c i j e u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    proof (rule Suc(1))
      show "card {u \<in> B. shift c i j e u \<notin> {0, 1}} \<le> N"
      proof (cases "e = 1 - c i")
        case True
        show ?thesis
        proof (rule drop[where s = e and w = i])
          show "i \<in> {i, j}" by simp
          show "shift c i j e i \<in> {0, 1}" using ij True by simp
        qed
      next
        case False
        then have ecj: "e = c j"
          using e_def by linarith
        show ?thesis
        proof (rule drop[where s = e and w = j])
          show "j \<in> {i, j}" by simp
          show "shift c i j e j \<in> {0, 1}" using ij ecj by simp
        qed
      qed
      show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> shift c i j e u"
        by (rule bnd_e)
      show "\<And>u. u \<in> B \<Longrightarrow> shift c i j e u \<le> 1"
        by (rule bnd_e)
      show "(\<Sum>u\<in>B. shift c i j e u) = real (CARD('n) - k)"
        by (rule sums)
    qed
    have hull2: "(\<Sum>u\<in>B. shift c i j (- d) u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    proof (rule Suc(1))
      show "card {u \<in> B. shift c i j (- d) u \<notin> {0, 1}} \<le> N"
      proof (cases "d = c i")
        case True
        show ?thesis
        proof (rule drop[where s = "- d" and w = i])
          show "i \<in> {i, j}" by simp
          show "shift c i j (- d) i \<in> {0, 1}" using ij True by simp
        qed
      next
        case False
        then have dcj: "d = 1 - c j"
          using d_def by linarith
        show ?thesis
        proof (rule drop[where s = "- d" and w = j])
          show "j \<in> {i, j}" by simp
          show "shift c i j (- d) j \<in> {0, 1}" using ij dcj by simp
        qed
      qed
      show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> shift c i j (- d) u"
        by (rule bnd_d)
      show "\<And>u. u \<in> B \<Longrightarrow> shift c i j (- d) u \<le> 1"
        by (rule bnd_d)
      show "(\<Sum>u\<in>B. shift c i j (- d) u) = real (CARD('n) - k)"
        by (rule sums)
    qed

    text \<open>Finally, the original combination is the convex combination.\<close>

    have ed': "e + d \<noteq> 0"
      using ed by simp
    have wsum: "d / (e + d) + e / (e + d) = 1"
    proof -
      have "d / (e + d) + e / (e + d) = (d + e) / (e + d)"
        by (rule add_divide_distrib[symmetric])
      also have "\<dots> = (e + d) / (e + d)"
        by (simp add: add.commute)
      also have "\<dots> = 1"
        using ed' by (rule div_self)
      finally show ?thesis .
    qed
    have wnn: "0 \<le> d / (e + d)" "0 \<le> e / (e + d)"
      using ed d_pos e_pos by auto
    have pt: "(d / (e + d)) * shift c i j e u
        + (e / (e + d)) * shift c i j (- d) u = c u" for u
      using shift_convex_combination[OF e_pos d_pos ij, of c u] by simp
    have comb: "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
        = (d / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j e u *\<^sub>R outer_prod u u)
        + (e / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j (- d) u *\<^sub>R outer_prod u u)"
    proof -
      have "(d / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j e u *\<^sub>R outer_prod u u)
          + (e / (e + d)) *\<^sub>R (\<Sum>u\<in>B. shift c i j (- d) u *\<^sub>R outer_prod u u)
          = (\<Sum>u\<in>B. ((d / (e + d)) * shift c i j e u
                    + (e / (e + d)) * shift c i j (- d) u) *\<^sub>R outer_prod u u)"
        by (simp add: scaleR_right.sum sum.distrib[symmetric]
            scaleR_add_left)
      also have "\<dots> = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)"
        unfolding pt ..
      finally show ?thesis ..
    qed
    show ?thesis
      unfolding comb
      by (rule convexD[OF convex_convex_hull hull1 hull2 wnn(1) wnn(2) wsum])
  qed
qed

text \<open>The hypersimplex decomposition, packaged: the measure is bounded by
  its own value.\<close>

lemma diag_in_convex_hull:
  fixes B :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes B: "onormal B"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and csum: "(\<Sum>u\<in>B. c u) = real (CARD('n) - k)"
  shows "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)
       \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof (rule diag_in_convex_hull_aux
    [OF B, where N = "card {u \<in> B. c u \<notin> {0, 1}}"])
  show "card {u \<in> B. c u \<notin> {0, 1}} \<le> card {u \<in> B. c u \<notin> {0, 1}}"
    by simp
  show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u"
    by (rule c0)
  show "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    by (rule c1)
  show "(\<Sum>u\<in>B. c u) = real (CARD('n) - k)"
    by (rule csum)
qed

subsection \<open>The capped trace bound\<close>

lemma Pi_constraint_capped_trace:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> Pi_constraint k" and k: "k < CARD('n)"
    and B: "onormal B" "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "real (CARD('n) - k) \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
proof -
  have psd_a: "psd a"
    using a by (simp add: Pi_constraint_def)
  have finB: "finite B"
    using B(1) by (simp add: onormal_def)
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_a by (simp add: lam_def psd_def)
  define T where "T = {u \<in> B. 1 \<le> lam u}"
  have T_sub: "T \<subseteq> B"
    by (auto simp: T_def)
  have finT: "finite T"
    using T_sub finB by (rule finite_subset)
  have cardT_le: "card T \<le> CARD('n)"
    using card_mono[OF finB T_sub] B(2) by simp
  have capT: "(\<Sum>u\<in>T. min (lam u) 1) = real (card T)"
    by (simp add: T_def)
  show ?thesis
  proof (cases "CARD('n) - k \<le> card T")
    case True
    have "(\<Sum>u\<in>T. min (lam u) 1) \<le> (\<Sum>u\<in>B. min (lam u) 1)"
      using lam_nn by (intro sum_mono2[OF finB T_sub]) simp
    then have "real (card T) \<le> (\<Sum>u\<in>B. min (lam u) 1)"
      using capT by simp
    moreover have "real (CARD('n) - k) \<le> real (card T)"
      using True by simp
    ultimately show ?thesis
      unfolding lam_def by simp
  next
    case False
    define S where "S = B - T"
    define m where "m = card S"
    have S_sub: "S \<subseteq> B"
      by (auto simp: S_def)
    have onS: "onormal S"
      by (rule onormal_subset[OF B(1) S_sub])
    have cardS: "m = CARD('n) - card T"
      unfolding m_def S_def using finB T_sub B(2)
      by (simp add: card_Diff_subset finT)
    have m_gt: "k < m"
      using False cardS cardT_le k by simp
    have m_le: "m \<le> CARD('n)"
      using cardS by simp
    have "real (m - k) \<le> Pi_proj a m"
      using a m_gt m_le by (simp add: Pi_constraint_def)
    also have "Pi_proj a m \<le> trace (a ** (\<Sum>u\<in>S. outer_prod u u))"
      using onormal_proj(2)[OF onS]
      by (intro Pi_proj_le[OF psd_a onormal_proj(1)[OF onS]]) (simp add: m_def)
    also have "\<dots> = (\<Sum>u\<in>S. lam u)"
      unfolding lam_def by (rule trace_mult_outer_sum)
    finally have key: "real (m - k) \<le> (\<Sum>u\<in>S. lam u)" .
    have capS: "(\<Sum>u\<in>S. min (lam u) 1) = (\<Sum>u\<in>S. lam u)"
      by (rule sum.cong[OF refl]) (auto simp: S_def T_def)
    have split: "(\<Sum>u\<in>B. min (lam u) 1)
        = (\<Sum>u\<in>S. min (lam u) 1) + (\<Sum>u\<in>T. min (lam u) 1)"
      unfolding S_def by (rule sum.subset_diff[OF T_sub finB])
    have nat_eq: "CARD('n) - k = card T + (m - k)"
      using cardS m_gt cardT_le by simp
    have "real (CARD('n) - k) = real (card T) + real (m - k)"
      unfolding nat_eq by simp
    also have "\<dots> \<le> (\<Sum>u\<in>T. min (lam u) 1) + (\<Sum>u\<in>S. min (lam u) 1)"
      using key capT capS by simp
    also have "\<dots> = (\<Sum>u\<in>B. min (lam u) 1)"
      using split by simp
    finally show ?thesis
      unfolding lam_def by simp
  qed
qed

subsection \<open>The exact inclusion\<close>

text \<open>\<open>suff_volatile k\<close> is closed under adding a nonnegative multiple of a
  rank-one projection (\<open>suff_volatile_augment\<close>), and translation commutes with
  taking the convex hull, so the hull is closed under the same operation.\<close>

lemma convex_hull_augment:
  fixes X :: "real^'n::finite^'n"
  assumes X: "X \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    and t: "0 \<le> t"
  shows "X + t *\<^sub>R outer_prod u u
       \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof -
  define z where "z = t *\<^sub>R outer_prod u u"
  have sub: "(\<lambda>y. z + y) ` suff_volatile k
      \<subseteq> (suff_volatile k :: (real^'n^'n) set)"
  proof
    fix Y assume "Y \<in> (\<lambda>y. z + y) ` suff_volatile k"
    then obtain b where b: "b \<in> suff_volatile k" and Y: "Y = z + b"
      by blast
    have "b + t *\<^sub>R outer_prod u u \<in> suff_volatile k"
      by (rule suff_volatile_augment[OF b t])
    then show "Y \<in> suff_volatile k"
      unfolding Y z_def by (simp add: add.commute)
  qed
  have "z + X
      \<in> (\<lambda>y. z + y) ` (convex hull (suff_volatile k :: (real^'n^'n) set))"
    using X by (rule imageI)
  then have "X + z
      \<in> (\<lambda>y. z + y) ` (convex hull (suff_volatile k :: (real^'n^'n) set))"
    by (simp add: add.commute)
  then have "X + z
      \<in> convex hull ((\<lambda>y. z + y) ` (suff_volatile k :: (real^'n^'n) set))"
    by (simp add: convex_hull_translation)
  then have "X + z \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    using hull_mono[OF sub] by blast
  then show ?thesis
    unfolding z_def .
qed

text \<open>Iterating over a finite index set.\<close>

lemma convex_hull_augment_sum:
  fixes X :: "real^'n::finite^'n"
  assumes X: "X \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
  shows "finite S \<Longrightarrow> (\<And>u. u \<in> S \<Longrightarrow> 0 \<le> g u) \<Longrightarrow>
      X + (\<Sum>u\<in>S. g u *\<^sub>R outer_prod u u)
        \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
proof (induct S rule: finite_induct)
  case empty
  show ?case
    using X by simp
next
  case (insert v S)
  have gv: "0 \<le> g v"
    using insert.prems by simp
  have IH: "X + (\<Sum>u\<in>S. g u *\<^sub>R outer_prod u u)
      \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    using insert.hyps(3) insert.prems by simp
  have eq: "X + (\<Sum>u\<in>insert v S. g u *\<^sub>R outer_prod u u)
      = (X + (\<Sum>u\<in>S. g u *\<^sub>R outer_prod u u)) + g v *\<^sub>R outer_prod v v"
    by (simp add: sum.insert[OF insert.hyps(1,2)] ac_simps)
  show ?case
    unfolding eq by (rule convex_hull_augment[OF IH gv])
qed

text \<open>Lemma 2.1, exact form.  Diagonalise \<open>a\<close>, cap the eigenvalues at \<open>1\<close>,
  rescale the capped vector so that its sum is exactly \<open>n - k\<close> --- possible
  because the capped sum is at least \<open>n - k\<close> by the trace bound --- decompose
  the result via the hypersimplex decomposition, and add the nonnegative
  remainder back.\<close>

theorem lemma_2_1_exact:
  fixes k :: nat
  assumes k: "k < CARD('n::finite)"
  shows "(Pi_constraint k :: (real^'n^'n) set)
       \<subseteq> convex hull (suff_volatile k)"
proof
  fix a :: "real^'n^'n"
  assume a: "a \<in> Pi_constraint k"
  have psd_a: "psd a"
    using a by (simp add: Pi_constraint_def)
  have sym_a: "transpose a = a"
    using psd_a by (simp add: psd_def)
  obtain B :: "(real^'n) set" where B: "onormal B" "span B = UNIV"
    and finB: "finite B" and cardB: "card B = CARD('n)"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigendecomposition[OF sym_a] by metis
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_a by (simp add: lam_def psd_def)
  have adecomp: "a = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])

  define cap where "cap = (\<lambda>u :: real^'n. min (lam u) 1)"
  have cap_nn: "0 \<le> cap u" for u
    using lam_nn by (simp add: cap_def)
  have cap_le1: "cap u \<le> 1" for u
    by (simp add: cap_def)
  have cap_le_lam: "cap u \<le> lam u" for u
    by (simp add: cap_def)
  have nk_pos: "0 < real (CARD('n) - k)"
    using k by simp
  have capsum: "real (CARD('n) - k) \<le> (\<Sum>u\<in>B. cap u)"
    unfolding cap_def lam_def
    by (rule Pi_constraint_capped_trace[OF a k B(1) cardB eig])
  have S_pos: "0 < (\<Sum>u\<in>B. cap u)"
    using capsum nk_pos by simp
  have S_ne: "(\<Sum>u\<in>B. cap u) \<noteq> 0"
    using S_pos by simp

  define th where "th = real (CARD('n) - k) / (\<Sum>u\<in>B. cap u)"
  have th_pos: "0 < th"
    unfolding th_def using nk_pos S_pos by simp
  have th_le1: "th \<le> 1"
    unfolding th_def using S_pos capsum by simp
  define nu where "nu = (\<lambda>u :: real^'n. th * cap u)"
  have nu_nn: "0 \<le> nu u" for u
    unfolding nu_def using th_pos cap_nn by simp
  have nu_le1: "nu u \<le> 1" for u
  proof -
    have "th * cap u \<le> 1 * 1"
      using th_pos th_le1 cap_nn cap_le1 by (intro mult_mono) auto
    then show ?thesis
      by (simp add: nu_def)
  qed
  have nu_le_lam: "nu u \<le> lam u" for u
  proof -
    have "th * cap u \<le> 1 * cap u"
      using th_le1 cap_nn by (intro mult_right_mono) auto
    also have "\<dots> = cap u"
      by simp
    also have "cap u \<le> lam u"
      by (rule cap_le_lam)
    finally show ?thesis
      by (simp add: nu_def)
  qed
  have nusum: "(\<Sum>u\<in>B. nu u) = real (CARD('n) - k)"
  proof -
    have "(\<Sum>u\<in>B. nu u) = th * (\<Sum>u\<in>B. cap u)"
      unfolding nu_def by (simp add: sum_distrib_left)
    also have "\<dots> = real (CARD('n) - k)"
      unfolding th_def using S_ne by simp
    finally show ?thesis .
  qed

  have hull_nu: "(\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
      \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
  proof (rule diag_in_convex_hull[OF B(1)])
    show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> nu u"
      by (rule nu_nn)
    show "\<And>u. u \<in> B \<Longrightarrow> nu u \<le> 1"
      by (rule nu_le1)
    show "(\<Sum>u\<in>B. nu u) = real (CARD('n) - k)"
      by (rule nusum)
  qed

  have rem: "a = (\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
      + (\<Sum>u\<in>B. (lam u - nu u) *\<^sub>R outer_prod u u)"
  proof -
    have "(\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
        + (\<Sum>u\<in>B. (lam u - nu u) *\<^sub>R outer_prod u u)
        = (\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u
                 + (lam u - nu u) *\<^sub>R outer_prod u u)"
      by (rule sum.distrib[symmetric])
    also have "\<dots> = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
      by (rule sum.cong[OF refl]) (simp add: scaleR_add_left[symmetric])
    finally have "(\<Sum>u\<in>B. nu u *\<^sub>R outer_prod u u)
        + (\<Sum>u\<in>B. (lam u - nu u) *\<^sub>R outer_prod u u)
        = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)" .
    then show ?thesis
      using adecomp by simp
  qed

  show "a \<in> convex hull (suff_volatile k :: (real^'n^'n) set)"
    unfolding rem
  proof (rule convex_hull_augment_sum[OF hull_nu finB])
    show "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u - nu u"
      using nu_le_lam by simp
  qed
qed

text \<open>Lemma 2.1 of the paper, verbatim: the convex hull of
  \<open>{a \<in> \<bbbS>\<^sup>n\<^sub>+ : \<lambda>\<^sub>(\<^sub>n\<^sub>-\<^sub>k\<^sub>)(a) \<ge> 1}\<close> equals the constraint set \<open>A\<close> of Eq. (2.1),
  with no closure.\<close>

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
