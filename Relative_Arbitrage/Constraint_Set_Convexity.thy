
(*<*)
theory Constraint_Set_Convexity
  imports Curvature_Operator
begin

(*>*)

text \<open>
  Proves Lemma 2.1 of arXiv:2512.17702, the convexification of the
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

section \<open>Subspace traces\<close>

lemma onormal_empty: "onormal {}"
  by (simp add: onormal_def pairwise_def)

lemma onormal_independent:
  assumes "onormal B"
  shows "independent B"
  using assms
  by (intro pairwise_orthogonal_independent) (auto simp: onormal_def)

lemma onormal_card_dim_span:
  assumes "onormal B"
  shows "card B = dim (span B)"
  using onormal_independent[OF assms]
  by (simp add: dim_eq_card_independent)

lemma onormal_extension_within:
  assumes B: "onormal B" and W: "subspace W" and BW: "B \<subseteq> W"
  obtains C where "onormal C" "B \<subseteq> C" "C \<subseteq> W" "span C = W"
proof -
  have orthB: "pairwise orthogonal B"
    using B by (simp add: onormal_def)
  obtain D where D: "D \<subseteq> W" "pairwise orthogonal D"
    "\<And>x. x \<in> D \<Longrightarrow> norm x = 1" "independent D" "card D = dim W" "span D = W"
    using orthonormal_basis_subspace[OF W] by metis
  obtain U where U: "pairwise orthogonal (B \<union> U)"
    "span (B \<union> U) = span (B \<union> D)"
    using orthogonal_extension[OF orthB, where T = D] by blast
  have spanBU: "span (B \<union> U) = W"
  proof -
    have "span (B \<union> D) \<subseteq> W"
      using BW D(1) W by (intro span_minimal) auto
    moreover have "W \<subseteq> span (B \<union> D)"
      using D(6) by (metis Un_upper2 span_mono)
    ultimately show ?thesis
      using U(2) by auto
  qed
  have BUW: "B \<union> U \<subseteq> W"
    by (metis spanBU span_superset)
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
    using C_orth by (rule pairwise_orthogonal_imp_finite)
  have BC: "B \<subseteq> C"
  proof
    fix b assume b: "b \<in> B"
    with B have "norm b = 1"
      by (simp add: onormal_def)
    with b show "b \<in> C"
      by (force simp: C_def intro: rev_image_eqI)
  qed
  have CW: "C \<subseteq> W"
  proof
    fix y assume "y \<in> C"
    then obtain u where u: "u \<in> (B \<union> U) - {0}" "y = u /\<^sub>R norm u"
      by (auto simp: C_def)
    then have "u \<in> W"
      using BUW by auto
    then show "y \<in> W"
      using u(2) W by (simp add: subspace_scale)
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
  then have C_span: "span C = W"
    by (simp add: spanBU)
  show thesis
    by (rule that[of C])
      (use C_fin C_orth C_norm BC CW C_span in \<open>auto simp: onormal_def\<close>)
qed

text \<open>The projection matrix of a subspace does not depend on the chosen
  orthonormal basis, hence subspace traces are well defined.\<close>

lemma onormal_outer_sum_eq:
  assumes B1: "onormal B1" and B2: "onormal B2" and sp: "span B1 = span B2"
  shows "(\<Sum>u\<in>B1. outer_prod u u) = (\<Sum>u\<in>B2. outer_prod u u)"
proof -
  have act: "(\<Sum>u\<in>B. outer_prod u u) *v x = y"
    if B: "onormal B" "span B = span B1"
      and yz: "y \<in> span B1" "\<And>w. w \<in> span B1 \<Longrightarrow> orthogonal z w" "x = y + z"
    for B x y z
  proof -
    have "(\<Sum>u\<in>B. outer_prod u u) *v x = (\<Sum>u\<in>B. (u \<bullet> x) *\<^sub>R u)"
      by (simp add: matrix_vector_mult_sum)
    also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> y) *\<^sub>R u)"
    proof (intro sum.cong refl)
      fix u assume u: "u \<in> B"
      then have "u \<in> span B1"
        using B(2) span_base by fastforce
      then have "orthogonal z u"
        by (rule yz(2))
      then have "u \<bullet> z = 0"
        by (simp add: orthogonal_def inner_commute)
      then show "(u \<bullet> x) *\<^sub>R u = (u \<bullet> y) *\<^sub>R u"
        by (simp add: yz(3) inner_add_right)
    qed
    also have "\<dots> = y"
      using B yz(1) by (intro onormal_expand) auto
    finally show ?thesis .
  qed
  have "(\<Sum>u\<in>B1. outer_prod u u) *v x = (\<Sum>u\<in>B2. outer_prod u u) *v x" for x
  proof -
    obtain y z where yz: "y \<in> span B1"
      "\<And>w. w \<in> span B1 \<Longrightarrow> orthogonal z w" "x = y + z"
      using orthogonal_subspace_decomp_exists[of B1 x] by metis
    show ?thesis
      using act[OF B1 refl yz] act[OF B2 sp[symmetric] yz] by simp
  qed
  then show ?thesis
    by (auto simp: matrix_eq)
qed

lemma trace_mult_outer_sum:
  "trace (A ** (\<Sum>u\<in>B. outer_prod u u)) = (\<Sum>u\<in>B. u \<bullet> (A *v u))"
  by (simp add: matrix_mult_sum_right trace_matrix_sum mult_outer_prod
      inner_commute)

lemma matrix_vector_mult_vsum: "A *v (\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S. A *v f x)"
proof -
  have "(A *v (\<Sum>x\<in>S. f x)) $ i = (\<Sum>x\<in>S. A *v f x) $ i" for i
  proof -
    have "(A *v (\<Sum>x\<in>S. f x)) $ i = (\<Sum>j\<in>UNIV. \<Sum>x\<in>S. A $ i $ j * f x $ j)"
      by (simp add: matrix_vector_mult_def sum_distrib_left)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>j\<in>UNIV. A $ i $ j * f x $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_vector_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma trace_on_subspace_eq:
  assumes "onormal B1" "onormal B2" "span B1 = span B2"
  shows "(\<Sum>u\<in>B1. u \<bullet> (a *v u)) = (\<Sum>u\<in>B2. u \<bullet> (a *v u))"
proof -
  have "(\<Sum>u\<in>B1. u \<bullet> (a *v u)) = trace (a ** (\<Sum>u\<in>B1. outer_prod u u))"
    by (simp add: trace_mult_outer_sum)
  also have "\<dots> = trace (a ** (\<Sum>u\<in>B2. outer_prod u u))"
    by (simp add: onormal_outer_sum_eq[OF assms])
  also have "\<dots> = (\<Sum>u\<in>B2. u \<bullet> (a *v u))"
    by (simp add: trace_mult_outer_sum)
  finally show ?thesis .
qed

section \<open>Orthogonal projections and the operator \<open>\<Pi>\<^sub>m\<close> of Eq. (2.1)\<close>

definition is_proj :: "real^'n^'n \<Rightarrow> bool" where
  "is_proj P \<longleftrightarrow> transpose P = P \<and> P ** P = P"

text \<open>Every orthogonal projection is the basis-projection onto its range.\<close>

lemma is_proj_decomp:
  assumes P: "is_proj P"
  obtains C where "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
proof -
  have symP: "transpose P = P" and idem: "P ** P = P"
    using P by (auto simp: is_proj_def)
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> P *v u = (u \<bullet> (P *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF symP] by metis
  have mu01: "u \<bullet> (P *v u) = 0 \<or> u \<bullet> (P *v u) = 1" if u: "u \<in> B" for u
  proof -
    define \<mu> where "\<mu> = u \<bullet> (P *v u)"
    have Pu: "P *v u = \<mu> *\<^sub>R u"
      unfolding \<mu>_def using eig[OF u] .
    have "\<mu> *\<^sub>R u = P *v u"
      by (simp add: Pu)
    also have "\<dots> = (P ** P) *v u"
      by (simp add: idem)
    also have "\<dots> = P *v (P *v u)"
      by (simp add: matrix_vector_mul_assoc)
    also have "\<dots> = P *v (\<mu> *\<^sub>R u)"
      by (simp add: Pu)
    also have "\<dots> = (\<mu> * \<mu>) *\<^sub>R u"
      by (simp add: matrix_vector_mult_scaleR Pu)
    finally have "\<mu> *\<^sub>R u = (\<mu> * \<mu>) *\<^sub>R u" .
    moreover have "u \<noteq> 0"
      using B(1) u by (auto simp: onormal_def)
    ultimately have "\<mu> * \<mu> = \<mu>"
      by (metis scaleR_cancel_right)
    then have "\<mu> * (\<mu> - 1) = 0"
      by (simp add: algebra_simps)
    then show ?thesis
      unfolding \<mu>_def[symmetric] by auto
  qed
  define C where "C = {u \<in> B. u \<bullet> (P *v u) = 1}"
  have CB: "C \<subseteq> B"
    by (auto simp: C_def)
  have onC: "onormal C"
    using B(1) CB
    by (auto simp: onormal_def intro: finite_subset elim: pairwise_subset)
  have Peq: "P = (\<Sum>u\<in>C. outer_prod u u)"
  proof -
    have agree: "P *v w = (\<Sum>u\<in>C. outer_prod u u) *v w" if w: "w \<in> B" for w
    proof -
      have "(\<Sum>u\<in>C. outer_prod u u) *v w = (\<Sum>u\<in>C. (u \<bullet> w) *\<^sub>R u)"
        by (simp add: matrix_vector_mult_sum)
      also have "\<dots> = (\<Sum>u\<in>C. if u = w then w else 0)"
        by (intro sum.cong refl)
          (use B(1) CB w in \<open>auto dest: onormal_inner_distinct\<close>)
      also have "\<dots> = (if w \<in> C then w else 0)"
        using onC by (simp add: onormal_def)
      also have "\<dots> = P *v w"
      proof (cases "w \<in> C")
        case True
        then have "w \<bullet> (P *v w) = 1"
          by (simp add: C_def)
        then have "P *v w = w"
          using eig[OF w] by simp
        then show ?thesis
          using True by simp
      next
        case False
        with mu01[OF w] w have "w \<bullet> (P *v w) = 0"
          by (auto simp: C_def)
        then have "P *v w = 0"
          using eig[OF w] by simp
        then show ?thesis
          using False by simp
      qed
      finally show ?thesis ..
    qed
    have "P *v x = (\<Sum>u\<in>C. outer_prod u u) *v x" for x
    proof -
      have x: "x \<in> span B"
        by (simp add: B(2))
      have "P *v x = P *v (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R w)"
        by (simp add: onormal_expand[OF B(1) x])
      also have "\<dots> = (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R (P *v w))"
        by (simp add: matrix_vector_mult_vsum matrix_vector_mult_scaleR)
      also have "\<dots> = (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R ((\<Sum>u\<in>C. outer_prod u u) *v w))"
        by (simp add: agree)
      also have "\<dots> = (\<Sum>u\<in>C. outer_prod u u) *v (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R w)"
        by (simp add: matrix_vector_mult_vsum matrix_vector_mult_scaleR)
      also have "\<dots> = (\<Sum>u\<in>C. outer_prod u u) *v x"
        by (simp add: onormal_expand[OF B(1) x])
      finally show ?thesis .
    qed
    then show ?thesis
      by (auto simp: matrix_eq)
  qed
  have trP: "real (card C) = trace P"
  proof -
    have "trace P = (\<Sum>u\<in>B. u \<bullet> (P *v u))"
      by (rule trace_onormal_basis[OF B])
    also have "\<dots> = (\<Sum>u\<in>B. if u \<in> C then 1 else 0)"
      by (intro sum.cong refl) (use mu01 in \<open>auto simp: C_def\<close>)
    also have "\<dots> = real (card C)"
    proof -
      have BC_eq: "B \<inter> C = C"
        using CB by auto
      show ?thesis
        using B(1) by (simp add: onormal_def sum.If_cases BC_eq)
    qed
    finally show ?thesis ..
  qed
  show thesis
    by (rule that[OF onC Peq trP])
qed

text \<open>Conversely, basis projections are orthogonal projections.\<close>

lemma matrix_mult_sum_left: "(\<Sum>x\<in>S. f x) ** A = (\<Sum>x\<in>S. f x ** A)"
proof -
  have "((\<Sum>x\<in>S. f x) ** A) $ i $ j = (\<Sum>x\<in>S. f x ** A) $ i $ j" for i j
  proof -
    have "((\<Sum>x\<in>S. f x) ** A) $ i $ j = (\<Sum>k\<in>UNIV. \<Sum>x\<in>S. f x $ i $ k * A $ k $ j)"
      by (simp add: matrix_matrix_mult_def sum_distrib_right)
    also have "\<dots> = (\<Sum>x\<in>S. \<Sum>k\<in>UNIV. f x $ i $ k * A $ k $ j)"
      by (rule sum.swap)
    finally show ?thesis
      by (simp add: matrix_matrix_mult_def)
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma outer_prod_scaleR_left: "outer_prod (c *\<^sub>R u) v = c *\<^sub>R outer_prod u v"
  by (simp add: outer_prod_def vec_eq_iff)

lemma outer_prod_mult: "outer_prod u v ** outer_prod w z = (v \<bullet> w) *\<^sub>R outer_prod u z"
  by (simp add: mult_outer_prod outer_prod_scaleR_left)

lemma onormal_proj:
  assumes C: "onormal C"
  shows "is_proj (\<Sum>u\<in>C. outer_prod u u)"
    and "trace (\<Sum>u\<in>C. outer_prod u u) = real (card C)"
proof -
  show "is_proj (\<Sum>u\<in>C. outer_prod u u)"
    unfolding is_proj_def
  proof
    show "transpose (\<Sum>u\<in>C. outer_prod u u) = (\<Sum>u\<in>C. outer_prod u u)"
      by (simp add: transpose_matrix_sum)
    have "(\<Sum>u\<in>C. outer_prod u u) ** (\<Sum>v\<in>C. outer_prod v v)
        = (\<Sum>v\<in>C. \<Sum>u\<in>C. (u \<bullet> v) *\<^sub>R outer_prod u v)"
      by (simp add: matrix_mult_sum_left matrix_mult_sum_right outer_prod_mult)
    also have "\<dots> = (\<Sum>u\<in>C. \<Sum>v\<in>C. (u \<bullet> v) *\<^sub>R outer_prod u v)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>u\<in>C. \<Sum>v\<in>C. if v = u then outer_prod u u else 0)"
      by (intro sum.cong refl)
        (use C in \<open>auto dest: onormal_inner_distinct
          simp: outer_prod_scaleR_left\<close>)
    also have "\<dots> = (\<Sum>u\<in>C. outer_prod u u)"
      using C by (simp add: onormal_def)
    finally show "(\<Sum>u\<in>C. outer_prod u u) ** (\<Sum>u\<in>C. outer_prod u u)
        = (\<Sum>u\<in>C. outer_prod u u)" .
  qed
  have "trace (\<Sum>u\<in>C. outer_prod u u) = (\<Sum>u\<in>C. u \<bullet> u)"
    by (simp add: trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>C. (1::real))"
    by (intro sum.cong refl) (use C in \<open>simp\<close>)
  finally show "trace (\<Sum>u\<in>C. outer_prod u u) = real (card C)"
    by simp
qed

text \<open>The operator \<open>\<Pi>\<^sub>m\<close> of Eq. (2.1).\<close>

definition Pi_proj :: "real^'n^'n \<Rightarrow> nat \<Rightarrow> real" where
  "Pi_proj a m = Inf {trace (a ** P) | P. is_proj P \<and> trace P = real m}"

lemma proj_with_trace_exists:
  assumes m: "m \<le> CARD('n::finite)"
  obtains P :: "real^'n^'n" where "is_proj P" "trace P = real m"
proof -
  obtain B :: "(real^'n) set" where B: "onormal B" "span B = UNIV"
    using onormal_extension[OF onormal_empty] by auto
  have "card B = CARD('n)"
    using onormal_card_dim_span[OF B(1)] B(2)
    by simp
  with m obtain T where T: "T \<subseteq> B" "card T = m" "finite T"
    by (metis obtain_subset_with_card_n)
  have onT: "onormal T"
    using T B(1) by (auto simp: onormal_def elim: pairwise_subset)
  show thesis
    using onormal_proj[OF onT] T(2) by (intro that[of "\<Sum>u\<in>T. outer_prod u u"]) auto
qed

lemma trace_proj_psd_nonneg:
  assumes a: "psd a" and P: "is_proj P"
  shows "0 \<le> trace (a ** P)"
proof -
  obtain C where C: "onormal C" "P = (\<Sum>u\<in>C. outer_prod u u)"
    "real (card C) = trace P"
    using is_proj_decomp[OF P] by metis
  have "trace (a ** P) = (\<Sum>u\<in>C. u \<bullet> (a *v u))"
    by (simp add: C(2) trace_mult_outer_sum)
  also have "\<dots> \<ge> 0"
    using a by (intro sum_nonneg) (auto simp: psd_def)
  finally show ?thesis .
qed

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

lemma transpose_scaleR: "transpose (c *\<^sub>R A) = c *\<^sub>R transpose A"
  by (simp add: transpose_def vec_eq_iff)

lemma transpose_add: "transpose (A + B) = transpose A + transpose B"
  by (simp add: transpose_def vec_eq_iff)

lemma psd_convex_comb:
  assumes "psd a" "psd b" and s: "0 \<le> s" "s \<le> 1"
  shows "psd (s *\<^sub>R a + (1 - s) *\<^sub>R b)"
proof -
  have "transpose (s *\<^sub>R a + (1 - s) *\<^sub>R b) = s *\<^sub>R a + (1 - s) *\<^sub>R b"
    using assms by (simp add: transpose_add transpose_scaleR psd_def)
  moreover have "0 \<le> x \<bullet> ((s *\<^sub>R a + (1 - s) *\<^sub>R b) *v x)" for x
  proof -
    have "x \<bullet> ((s *\<^sub>R a + (1 - s) *\<^sub>R b) *v x)
        = s * (x \<bullet> (a *v x)) + (1 - s) * (x \<bullet> (b *v x))"
      by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector
          inner_add_right)
    also have "\<dots> \<ge> 0"
      using assms by (intro add_nonneg_nonneg mult_nonneg_nonneg)
        (auto simp: psd_def)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (simp add: psd_def)
qed

lemma trace_mult_convex_comb:
  "trace ((s *\<^sub>R a + (1 - s) *\<^sub>R b) ** P)
     = s * trace (a ** P) + (1 - s) * trace (b ** P)"
  by (simp add: matrix_add_rdistrib scaleR_matrix_mult trace_add trace_scaleR)

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

subsection \<open>Frobenius products of matrices\<close>

subsection \<open>Spectral decomposition as a sum of outer products\<close>

lemma spectral_decomposition:
  fixes A :: "real^'n^'n"
  assumes B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> A *v u = (u \<bullet> (A *v u)) *\<^sub>R u"
  shows "A = (\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u)"
proof -
  have agree: "A *v w = (\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u) *v w"
    if w: "w \<in> B" for w
  proof -
    have "(\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u) *v w
        = (\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R ((u \<bullet> w) *\<^sub>R u))"
      by (simp add: matrix_vector_mult_sum scaleR_matrix_vector)
    also have "\<dots> = (\<Sum>u\<in>B. if u = w then (w \<bullet> (A *v w)) *\<^sub>R w else 0)"
      by (intro sum.cong refl)
        (use B(1) w in \<open>auto dest: onormal_inner_distinct
          \<close>)
    also have "\<dots> = (w \<bullet> (A *v w)) *\<^sub>R w"
      using B(1) w by (simp add: onormal_def)
    also have "\<dots> = A *v w"
      by (rule eig[OF w, symmetric])
    finally show ?thesis ..
  qed
  have "A *v x = (\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u) *v x" for x
  proof -
    have x: "x \<in> span B"
      by (simp add: B(2))
    have "A *v x = A *v (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R w)"
      by (simp add: onormal_expand[OF B(1) x])
    also have "\<dots> = (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R (A *v w))"
      by (simp add: matrix_vector_mult_vsum matrix_vector_mult_scaleR)
    also have "\<dots> = (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R
        ((\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u) *v w))"
      by (simp add: agree)
    also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u)
        *v (\<Sum>w\<in>B. (w \<bullet> x) *\<^sub>R w)"
      by (simp add: matrix_vector_mult_vsum matrix_vector_mult_scaleR)
    also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (A *v u)) *\<^sub>R outer_prod u u) *v x"
      by (simp add: onormal_expand[OF B(1) x])
    finally show ?thesis .
  qed
  then show ?thesis
    unfolding matrix_eq by blast
qed

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
      using psd_b by (simp add: transpose_add transpose_scaleR psd_def)
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

subsection \<open>Abel summation against the \<open>\<Pi>\<close>-constraints\<close>

subsection \<open>The separation argument\<close>

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
