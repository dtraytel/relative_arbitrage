
(*<*)
theory Symmetric_Spectral
  imports Orthonormal_Families Matrix_Algebra
begin

(*>*)

text \<open>
  The spectral theorem for real symmetric matrices, by the variational
  argument: a maximizer of the Rayleigh quotient \<open>x \<mapsto> x \<bullet> (a *v x)\<close> on an
  invariant subspace is an eigenvector, and induction on dimension peels off
  an orthonormal eigenbasis of the whole space. Positive semidefiniteness and
  the nonnegativity of \<open>trace (a ** b)\<close> for \<open>psd\<close> \<open>a\<close>, \<open>b\<close> follow.
\<close>

unbundle inner_syntax

section \<open>Preliminaries\<close>

text \<open>\<open>inner_transpose_matrix\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

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

section \<open>Rayleigh-quotient maximizers are eigenvectors\<close>

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

section \<open>Orthonormal eigenbases of invariant subspaces\<close>

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

section \<open>Positive semidefinite matrices\<close>

definition psd :: "real^'n^'n \<Rightarrow> bool" where
  "psd a \<longleftrightarrow> transpose a = a \<and> (\<forall>x. 0 \<le> x \<bullet> (a *v x))"

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

lemma psd_convex_comb:
  assumes "psd a" "psd b" and s: "0 \<le> s" "s \<le> 1"
  shows "psd (s *\<^sub>R a + (1 - s) *\<^sub>R b)"
proof -
  have "transpose (s *\<^sub>R a + (1 - s) *\<^sub>R b) = s *\<^sub>R a + (1 - s) *\<^sub>R b"
    using assms by (simp add: transpose_add transpose_scalar psd_def)
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

text \<open>Every symmetric matrix is the sum, over an eigenbasis, of its
  eigenvalues weighted against the rank-one projections onto each
  eigenvector.\<close>

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


subsection \<open>Positive semidefiniteness under limits, shifts and two-sided bounds\<close>

theorem psd_of_abstract_le:
  fixes X Y :: "(real^'n::finite) \<Rightarrow> (real^'n)"
  assumes lX: "linear X" and lY: "linear Y"
    and symX: "\<And>v w. v \<bullet> X w = w \<bullet> X v"
    and symY: "\<And>v w. v \<bullet> Y w = w \<bullet> Y v"
    and le: "\<And>v. v \<bullet> X v \<le> v \<bullet> Y v"
  shows "psd (matrix Y - matrix X)"
  unfolding psd_def
proof (intro conjI allI)
  have sX: "transpose (matrix X) = matrix X"
    by (rule matrix_of_symmetric[OF lX symX])
  have sY: "transpose (matrix Y) = matrix Y"
    by (rule matrix_of_symmetric[OF lY symY])
  have td: "transpose (matrix Y - matrix X)
      = transpose (matrix Y) - transpose (matrix X)"
    by (simp add: transpose_def vec_eq_iff)
  show "transpose (matrix Y - matrix X) = matrix Y - matrix X"
    unfolding td sX sY ..
next
  fix v :: "real^'n"
  have "v \<bullet> ((matrix Y - matrix X) *v v) = v \<bullet> (Y v - X v)"
    unfolding matrix_diff_vec[OF lX lY] ..
  also have "\<dots> = v \<bullet> Y v - v \<bullet> X v" by (simp add: inner_diff_right)
  finally show "0 \<le> v \<bullet> ((matrix Y - matrix X) *v v)"
    using le[of v] by simp
qed

subsection \<open>The closing chain of Theorem 4.2(a)\<close>

text \<open>A scaled subsolution and a supersolution touching an ordered jet pair
  at a common \<open>p\<close> are inconsistent: scaling supplies strictness
  (\<open>visc_subsol_scaled_strict\<close>), the ordering supplies \<open>psd\<close>
  (\<open>psd_of_abstract_le\<close>), and degenerate ellipticity closes
  (\<open>ell_op_strict_contradiction\<close>). This is Theorem 4.2(a) modulo the
  hypotheses \<open>ord\<close>, \<open>subtest\<close> and \<open>suptest\<close>, supplied by the
  development in \<open>Rademacher\<close>,
  \<open>Alexandrov\<close>,
  \<open>Jensen_Lemma\<close> and
  \<open>Theorem_On_Sums\<close>.\<close>

lemma hessian_lower_bound_of_psd:
  fixes B :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes psd: "\<And>v. 0 \<le> v \<bullet> B v"
  shows "- (c * (norm k)\<^sup>2) \<le> k \<bullet> (B k - c *\<^sub>R k)"
proof -
  have "k \<bullet> (B k - c *\<^sub>R k) = k \<bullet> B k - c * (norm k)\<^sup>2"
    by (simp add: inner_diff_right power2_norm_eq_inner)
  moreover have "0 \<le> k \<bullet> B k"
    by (rule psd)
  ultimately show ?thesis
    by linarith
qed

theorem semiconvex_hessian_two_sided:
  fixes B W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes psd: "\<And>v. 0 \<le> v \<bullet> B v"
    and neg: "\<And>v. v \<bullet> W v \<le> 0"
    and Wdef: "\<And>v. W v = B v - c *\<^sub>R v"
  shows "- (c * (norm k)\<^sup>2) \<le> k \<bullet> W k" and "k \<bullet> W k \<le> 0"
proof -
  show "- (c * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    unfolding Wdef by (rule hessian_lower_bound_of_psd[OF psd])
  show "k \<bullet> W k \<le> 0"
    by (rule neg)
qed

text \<open>The quadratic form of \<open>W\<close> is bounded in absolute value by \<open>c\<parallel>k\<parallel>\<^sup>2\<close>,
  uniformly over the family and independent of the tilt.\<close>

corollary semiconvex_hessian_abs_bound:
  fixes B W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes psd: "\<And>v. 0 \<le> v \<bullet> B v"
    and neg: "\<And>v. v \<bullet> W v \<le> 0"
    and Wdef: "\<And>v. W v = B v - c *\<^sub>R v"
    and c0: "0 \<le> c"
  shows "\<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
proof -
  have lo: "- (c * (norm k)\<^sup>2) \<le> k \<bullet> W k"
    by (rule semiconvex_hessian_two_sided(1)[OF psd neg Wdef])
  have hi: "k \<bullet> W k \<le> 0"
    by (rule neg)
  have "0 \<le> c * (norm k)\<^sup>2"
    by (rule mult_nonneg_nonneg[OF c0]) simp
  with lo hi show ?thesis
    by (intro abs_leI) linarith+
qed

subsection \<open>From the quadratic-form bound to a genuine operator bound\<close>

text \<open>\<open>polarization_symmetric\<close>, \<open>parallelogram_norm\<close>, \<open>symmetric_form_bound\<close>, \<open>symmetric_form_bound_unit\<close> live in \<open>Doubling_Of_Variables\<close>.\<close>

subsection \<open>Boundedness to a limit point, and limit point to nearby points\<close>

text \<open>\<open>bounded_seq_limit_point\<close>, \<open>nearby_of_convergent\<close> live in \<open>Doubling_Of_Variables\<close>.\<close>

text \<open>A bounded family on which the operator bound holds yields the
  nearby-point hypothesis at a produced limit point.  The closing argument
  still needs, at that limit, the ordering \<open>X \<preceq> Y\<close>, symmetry of both
  matrices, and \<open>p \<noteq> 0\<close>.  Symmetry and the ordering are closed conditions
  and pass to the limit automatically; \<open>p \<noteq> 0\<close> is not closed and needs a
  positive lower bound along the family.\<close>

subsection \<open>A positive lower bound on the shared gradient\<close>

text \<open>\<open>doubling_grad_lower_bound\<close>, \<open>doubling_grad_norm_lower_bound\<close> live in \<open>Doubling_Of_Variables\<close>.\<close>

text \<open>The same bound for the doubling run on sup-convolutions:
  \<open>supconv_lipschitz\<close> gives the modulus of continuity with the same
  constant, and \<open>doubled_value_gap_supconv\<close> gives the value gap with
  explicit loss \<open>\<epsilon>(L\<^sub>u\<^sup>2+L\<^sub>w\<^sup>2)/2\<close>.  The doubled functional is
  \<open>A(x)+B(y)-\<close>penalty with \<open>B = supconv(-w)\<epsilon>\<close>, so \<open>w\<close> is instantiated at
  \<open>-B\<close>, and the Lipschitz hypothesis transfers since negation preserves
  \<open>\<bar>\<cdot>\<bar>\<close>.\<close>

theorem psd_limit:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0" and p: "\<And>i. psd (A i)"
  shows "psd A0"
proof -
  have sym: "transpose (A i) = A i" for i
    using p[of i] unfolding psd_def by simp
  have nn: "0 \<le> x \<bullet> (A i *v x)" for i and x :: "real^'n"
    using p[of i] unfolding psd_def by simp
  have s0: "transpose A0 = A0"
    by (rule transpose_limit[OF conv sym])
  have q0: "0 \<le> x \<bullet> (A0 *v x)" for x :: "real^'n"
  proof -
    have "(\<lambda>i. x \<bullet> (A i *v x)) \<longlonglongrightarrow> x \<bullet> (A0 *v x)"
      by (rule tendsto_quadratic_form[OF conv])
    then show ?thesis
      by (rule LIMSEQ_le_const) (use nn in blast)
  qed
  show ?thesis
    unfolding psd_def using s0 q0 by blast
qed

text \<open>\<open>psd (Y-X)\<close> is preserved when both sequences converge, since subtraction
  is continuous and \<open>psd\<close> is a closed condition.\<close>

corollary psd_diff_limit:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and p: "\<And>i. psd (Y i - X i)"
  shows "psd (Y0 - X0)"
proof -
  have "(\<lambda>i. Y i - X i) \<longlonglongrightarrow> Y0 - X0"
    by (rule tendsto_diff[OF cY cX])
  from psd_limit[OF this p] show ?thesis .
qed

subsection \<open>The asymptotic ordering\<close>

text \<open>Perturbing the doubled functional by \<open>-\<delta>\<parallel>z-\<xi>\<^sub>0\<parallel>\<^sup>2\<close> shifts \<open>X\<close> to
  \<open>X+2\<delta>I\<close> and \<open>Y\<close> to \<open>Y-2\<delta>I\<close>, so \<open>(Y-X)-4\<delta>I\<close> need not be psd even when
  \<open>Y-X\<close> is: the per-index ordering is lost.  What survives is the
  ordering in the limit, since \<open>psd\<close> is closed and the defect \<open>4\<delta>\<close>
  vanishes; the right hypothesis for a shifted family is
  \<open>psd(Y\<^sub>i-X\<^sub>i+c\<^sub>iI)\<close> with \<open>c\<^sub>i \<rightarrow> 0\<close>.\<close>

corollary psd_diff_limit_shifted:
  fixes X Y :: "nat \<Rightarrow> real^'n::finite^'n" and cs :: "nat \<Rightarrow> real"
  assumes cX: "X \<longlonglongrightarrow> X0" and cY: "Y \<longlonglongrightarrow> Y0"
    and cs0: "cs \<longlonglongrightarrow> 0"
    and p: "\<And>i. psd (Y i - X i + (cs i) *\<^sub>R mat 1)"
  shows "psd (Y0 - X0)"
proof -
  have s0: "(\<lambda>i. (cs i) *\<^sub>R (mat 1 :: real^'n^'n))
      \<longlonglongrightarrow> (0::real) *\<^sub>R (mat 1 :: real^'n^'n)"
    by (rule tendsto_scaleR[OF cs0 tendsto_const])
  have "(\<lambda>i. Y i - X i + (cs i) *\<^sub>R mat 1)
      \<longlonglongrightarrow> (Y0 - X0) + (0::real) *\<^sub>R (mat 1 :: real^'n^'n)"
    by (rule tendsto_add[OF tendsto_diff[OF cY cX] s0])
  then have "(\<lambda>i. Y i - X i + (cs i) *\<^sub>R mat 1) \<longlonglongrightarrow> Y0 - X0"
    by simp
  from psd_limit[OF this p] show ?thesis .
qed

subsection \<open>Route (i), threaded\<close>

text \<open>Everything is supplied as sequences of perturbed data, produced by
  re-running Jensen with a shrinking tilt, together with their limits.
  Symmetry and the ordering are needed only along the sequence
  (\<open>transpose_limit\<close>, \<open>psd_diff_limit\<close>); only \<open>p \<noteq> 0\<close> is required at the
  limit itself, supplied by \<open>doubling_grad_norm_lower_bound\<close>.  The two
  gradient sequences must converge to the same \<open>p\<close> - the gradient
  alignment.\<close>

lemma psd_shifted_diff:
  fixes X Y :: "real^'n::finite^'n"
  assumes p: "psd (Y - X)"
  shows "psd ((Y + c *\<^sub>R mat 1) - (X + c *\<^sub>R mat 1))"
proof -
  have "(Y + c *\<^sub>R mat 1) - (X + c *\<^sub>R mat 1) = Y - X"
    by simp
  then show ?thesis using p by simp
qed

text \<open>\<open>matrix_shift_apply\<close>, \<open>norm_shifted_block\<close>, \<open>shift_cancel_matrix\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


text \<open>\<open>penalty_gradient_nearby_bound\<close> lives in \<open>Doubling_Of_Variables\<close>.\<close>

text \<open>The value gap transfers to the sup-convolutions with an explicit loss:
  \<open>supconv_le_of_lipschitz\<close> sandwiches each sup-convolution between its
  function and that function plus \<open>\<epsilon>L\<^sup>2/2\<close>, so a gap \<open>\<gamma>\<close> for
  \<open>\<theta>u,w\<close> becomes \<open>\<gamma>-\<epsilon>(L\<^sub>u\<^sup>2+L\<^sub>w\<^sup>2)/2\<close> for the sup-convolutions,
  positive for every sufficiently small \<open>\<epsilon>\<close>.\<close>

(*<*)
end
(*>*)
