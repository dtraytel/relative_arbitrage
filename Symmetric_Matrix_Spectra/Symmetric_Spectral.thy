
(*<*)
theory Symmetric_Spectral
  imports
    Orthonormal_Families
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

text \<open>The orthogonal complement of a family of eigenvectors within an
  invariant subspace is again invariant.\<close>

lemma eigen_orth_complement_invariant:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and inv: "\<forall>x\<in>S. a *v x \<in> S"
    and eigC: "\<forall>u\<in>C. a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "\<forall>x\<in>{y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}. a *v x \<in> {y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}"
proof (intro ballI)
  fix x assume x: "x \<in> {y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}"
  have "c \<bullet> (a *v x) = 0" if c: "c \<in> C" for c
  proof -
    have "c \<bullet> (a *v x) = x \<bullet> (a *v c)" by (rule sym_inner_swap[OF sym])
    also have "\<dots> = (c \<bullet> (a *v c)) * (c \<bullet> x)"
      using eigC c by (metis inner_commute inner_scaleR_right)
    finally show ?thesis using x c by simp
  qed
  then show "a *v x \<in> {y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}" using x inv by blast
qed

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
    have eig_u: "\<forall>w\<in>{u}. a *v w = (w \<bullet> (a *v w)) *\<^sub>R w"
      using rayleigh_maximizer_eigenvector[OF sym less.prems(1) _ u umax] less.prems(2)
      by blast
    define S' where "S' = {y \<in> S. \<forall>c\<in>{u}. c \<bullet> y = 0}"
    have subS': "subspace S'"
      unfolding S'_def using subspace_inter[OF less.prems(1) subspace_hyperplane[of u]]
      by (simp add: Int_def conj_commute)
    have "u \<notin> S'" using u(2) by (auto simp: S'_def norm_eq_1)
    then have "S' \<subseteq> S" "S' \<noteq> S" using u(1) unfolding S'_def by blast+
    then have dimlt: "dim S' < dim S"
      using subS' less.prems(1) by (metis dim_subset order_less_le subspace_dim_equal)
    from less.hyps[OF dimlt subS'] obtain B' where
      B': "onormal B'" "B' \<subseteq> S'" "span B' = S'"
        "\<forall>w\<in>B'. a *v w = (w \<bullet> (a *v w)) *\<^sub>R w"
      using eigen_orth_complement_invariant[OF sym less.prems(2) eig_u]
      unfolding S'_def by blast
    have u1: "onormal {u}" using u(2) by (simp add: onormal_def)
    show ?thesis
      using onormal_union_orth_complement[OF less.prems(1) u1 _ B'(1) B'(3)[unfolded S'_def]]
        u(1) B'(2,4) eig_u
      by (intro exI[of _ "{u} \<union> B'"]) (auto simp: S'_def)
  qed
qed

theorem symmetric_eigenbasis:
  fixes a :: "real^'n^'n"
  assumes "transpose a = a"
  obtains B where "onormal B" "span B = UNIV"
    "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  using invariant_subspace_eigenbasis_ex[OF assms subspace_UNIV] by auto

text \<open>Every orthonormal family of eigenvectors of a symmetric matrix extends
  to an orthonormal eigenbasis of each invariant subspace containing it.\<close>

lemma invariant_subspace_eigenbasis_extend:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and S: "subspace S" and inv: "\<forall>x\<in>S. a *v x \<in> S"
    and C: "onormal C" "C \<subseteq> S" and eigC: "\<forall>u\<in>C. a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  obtains B where "onormal B" "C \<subseteq> B" "B \<subseteq> S" "span B = S"
    "\<forall>u\<in>B. a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
proof -
  have subH: "subspace {y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}"
    using subspace_inter[OF S subspace_orthogonal_to_vectors[of C]]
    by (simp add: Int_def orthogonal_def)
  obtain B0 where B0: "onormal B0" "B0 \<subseteq> {y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}"
      "span B0 = {y \<in> S. \<forall>c\<in>C. c \<bullet> y = 0}" "\<forall>u\<in>B0. a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using invariant_subspace_eigenbasis_ex[OF sym subH
        eigen_orth_complement_invariant[OF sym inv eigC]] by blast
  show ?thesis
    using onormal_union_orth_complement[OF S C B0(1,3)] B0(2,4) C(2) eigC
    by (intro that[of "C \<union> B0"]) auto
qed

text \<open>In particular a single unit eigenvector extends to an orthonormal
  eigenbasis of the whole space.\<close>

lemma eigenbasis_containing_eigenvector:
  fixes A :: "real^'n::finite^'n"
  assumes sym: "transpose A = A" and q: "norm q = 1"
    and eigq: "A *v q = (q \<bullet> (A *v q)) *\<^sub>R q"
  shows "\<exists>B. onormal B \<and> span B = UNIV \<and> q \<in> B
      \<and> (\<forall>u\<in>B. A *v u = (u \<bullet> (A *v u)) *\<^sub>R u)
      \<and> (\<forall>u \<in> B - {q}. q \<bullet> u = 0)"
proof -
  obtain B where B: "onormal B" "q \<in> B" "span B = UNIV"
      "\<forall>u\<in>B. A *v u = (u \<bullet> (A *v u)) *\<^sub>R u"
    using invariant_subspace_eigenbasis_extend[OF sym subspace_UNIV _, of "{q}"] q eigq
    by (auto simp: onormal_def)
  then show ?thesis by (blast dest: onormal_inner_distinct)
qed

section \<open>Positive semidefinite matrices\<close>

definition psd :: "real^'n^'n \<Rightarrow> bool" where
  "psd a \<longleftrightarrow> transpose a = a \<and> (\<forall>x. 0 \<le> x \<bullet> (a *v x))"

text \<open>The identity is positive semidefinite; a positive semidefinite matrix
  has a nonnegative diagonal, and its kernel consists of the vectors on which
  its quadratic form vanishes.\<close>

lemma psd_mat_1: "psd (mat 1 :: real^'n::finite^'n)"
  by (simp add: psd_def)

lemma psd_diag_nonneg:
  fixes a :: "real^'m::finite^'m"
  assumes "psd a"
  shows "0 \<le> a $ l $ l"
  using assms diag_eq_inner_axis[where a = a and i = l, symmetric]
  by (auto simp: psd_def dest: spec[of _ "axis l 1"])

lemma psd_kernel_eq:
  fixes a :: "real^'n::finite^'n" and q :: "real^'n"
  assumes a: "psd a" and z: "q \<bullet> (a *v q) = 0"
  shows "a *v q = 0"
proof -
  have sym: "transpose a = a" using a by (simp add: psd_def)
  have nn: "0 \<le> y \<bullet> (a *v y)" for y using a by (simp add: psd_def)
  have cross: "z \<bullet> (a *v q) = 0" for z
  proof (rule ccontr)
    assume ne: "z \<bullet> (a *v q) \<noteq> 0"
    define Bc where "Bc = z \<bullet> (a *v q)"
    define Ac where "Ac = z \<bullet> (a *v z)"
    have Bc0: "Bc \<noteq> 0" using ne by (simp add: Bc_def)
    have Ac0: "0 \<le> Ac" by (simp add: Ac_def nn)
    have qa: "q \<bullet> (a *v z) = Bc"
    proof -
      have "q \<bullet> (a *v z) = (transpose a *v q) \<bullet> z"
        by (rule inner_transpose_matrix)
      also have "\<dots> = (a *v q) \<bullet> z" using sym by simp
      also have "\<dots> = z \<bullet> (a *v q)" by (rule inner_commute)
      finally show ?thesis by (simp add: Bc_def)
    qed
    have expand: "(q + r *\<^sub>R z) \<bullet> (a *v (q + r *\<^sub>R z))
        = 2 * r * Bc + r\<^sup>2 * Ac" for r
    proof -
      have lin: "a *v (q + r *\<^sub>R z) = a *v q + r *\<^sub>R (a *v z)"
        by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib
            sum_distrib_left algebra_simps)
      show ?thesis
        unfolding lin
        by (simp add: z qa Bc_def Ac_def power2_eq_square
            algebra_simps)
    qed
    show False
    proof (cases "Ac = 0")
      case True
      have "0 \<le> 2 * (- Bc) * Bc + (- Bc)\<^sup>2 * Ac"
        using nn[of "q + (- Bc) *\<^sub>R z"] expand[of "- Bc"] by simp
      then have "Bc * Bc \<le> 0" using True by (simp add: power2_eq_square)
      moreover have "0 < Bc * Bc"
        using Bc0 by (cases "0 < Bc") (auto intro: mult_pos_pos mult_neg_neg
            simp: not_less le_less)
      ultimately show False by linarith
    next
      case False
      then have AcP: "0 < Ac" using Ac0 by simp
      define r where "r = - Bc / Ac"
      have "0 \<le> 2 * r * Bc + r\<^sup>2 * Ac"
        using nn[of "q + r *\<^sub>R z"] expand[of r] by simp
      also have "2 * r * Bc + r\<^sup>2 * Ac = - (Bc\<^sup>2 / Ac)"
        unfolding r_def using AcP by (simp add: power2_eq_square field_simps)
      finally have h: "Bc\<^sup>2 / Ac \<le> 0" by simp
      have "0 < Bc * Bc"
        using Bc0 by (cases "0 < Bc") (auto intro: mult_pos_pos mult_neg_neg
            simp: not_less le_less)
      then have "0 < Bc\<^sup>2 / Ac"
        using AcP by (simp add: power2_eq_square)
      with h show False by linarith
    qed
  qed
  have "(a *v q) \<bullet> (a *v q) = 0" using cross[of "a *v q"] by simp
  then show ?thesis by simp
qed

text \<open>The trace of \<open>a ** P\<close>, read off in an orthonormal eigenbasis of the
  symmetric matrix \<open>a\<close>: the eigenvalues weighted by the diagonal of \<open>P\<close>.\<close>

lemma trace_mult_eigen_weights:
  fixes a :: "real^'n::finite^'n"
  assumes B: "onormal B" "span B = UNIV"
    and sym: "transpose a = a"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
  shows "trace (a ** P) = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (P *v u)))"
proof -
  have "trace (a ** P) = (\<Sum>u\<in>B. u \<bullet> ((a ** P) *v u))"
    by (rule trace_onormal_basis[OF B])
  also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (P *v u)))"
  proof (rule sum.cong[OF refl])
    fix u assume u: "u \<in> B"
    text \<open>Name the eigenvalue: \<open>eig\<close> rewrites \<open>a u\<close> into a term that again
      contains \<open>a u\<close>, so it must not be handed to the simplifier directly.\<close>
    define c where "c = u \<bullet> (a *v u)"
    have au: "a *v u = c *\<^sub>R u"
      unfolding c_def by (rule eig[OF u])
    have "u \<bullet> ((a ** P) *v u) = u \<bullet> (a *v (P *v u))"
      by (simp add: matrix_vector_mul_assoc)
    also have "\<dots> = (P *v u) \<bullet> (a *v u)"
      by (rule sym_inner_swap[OF sym])
    also have "\<dots> = (P *v u) \<bullet> (c *\<^sub>R u)"
      by (simp add: au)
    also have "\<dots> = c * ((P *v u) \<bullet> u)"
      by simp
    also have "\<dots> = (u \<bullet> (a *v u)) * (u \<bullet> (P *v u))"
      unfolding c_def by (simp add: inner_commute)
    finally show "u \<bullet> ((a ** P) *v u) = (u \<bullet> (a *v u)) * (u \<bullet> (P *v u))" .
  qed
  finally show ?thesis .
qed

lemma trace_mult_psd_nonneg:
  fixes a b :: "real^'n^'n"
  assumes a: "psd a" and b: "psd b"
  shows "0 \<le> trace (a ** b)"
proof -
  from a have syma: "transpose a = a"
    by (simp add: psd_def)
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF syma] by metis
  have "0 \<le> (\<Sum>u\<in>B. (u \<bullet> (a *v u)) * (u \<bullet> (b *v u)))"
    using a b by (intro sum_nonneg mult_nonneg_nonneg) (auto simp: psd_def)
  also have "\<dots> = trace (a ** b)"
    by (rule trace_mult_eigen_weights[OF B syma eig, symmetric])
  finally show ?thesis .
qed

lemma psd_convex_comb:
  assumes "psd a" "psd b" and s: "0 \<le> s" "s \<le> 1"
  shows "psd (s *\<^sub>R a + (1 - s) *\<^sub>R b)"
  using assms unfolding psd_def
  by (auto simp: transpose_add transpose_scalar quadform_convex_comb
      intro!: add_nonneg_nonneg mult_nonneg_nonneg)

lemma trace_mult_convex_comb:
  "trace ((s *\<^sub>R a + (1 - s) *\<^sub>R b) ** P)
     = s * trace (a ** P) + (1 - s) * trace (b ** P)"
  by (simp add: matrix_add_rdistrib scalar_matrix_assoc[symmetric] trace_add trace_scaleR)

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
      by (simp add: matrix_vector_mult_sum scaleR_matrix_vector_assoc[symmetric])
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

text \<open>The eigendecomposition of a symmetric matrix in the form most callers
  consume it: an orthonormal eigenbasis, its size, the spectral sum, and an
  enumeration of the basis by the index type.\<close>

lemma symmetric_eigendecomposition:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
  obtains B and f :: "'n \<Rightarrow> real^'n" where "onormal B" "span B = UNIV" "finite B"
    "card B = CARD('n)" "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    "a = (\<Sum>u\<in>B. (u \<bullet> (a *v u)) *\<^sub>R outer_prod u u)" "bij_betw f UNIV B"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  moreover have "card B = CARD('n)" by (rule onormal_span_card[OF B])
  moreover obtain f :: "'n \<Rightarrow> real^'n" where "bij_betw f UNIV B"
    using finite_same_card_bij[of "UNIV :: 'n set" B] onormal_finite[OF B(1)] calculation(4) by auto
  ultimately show thesis
    using that spectral_decomposition[OF B eig] onormal_finite[OF B(1)] by blast
qed


subsection \<open>Positive semidefiniteness from an ordering of linear maps\<close>

text \<open>An ordering \<open>v \<bullet> X v \<le> v \<bullet> Y v\<close> of two symmetric linear maps makes
  the difference of their matrices positive semidefinite.\<close>

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

subsection \<open>From a bound on the quadratic form to a bound on the norm\<close>

text \<open>The diagonal bound \<open>\<bar>k \<bullet> W k\<bar> \<le> c \<parallel>k\<parallel>\<^sup>2\<close> of a symmetric linear
  map does not by itself bound the off-diagonal entries; polarisation
  recovers them by pure algebra, and the parallelogram law turns the result
  into a bound uniform over the unit sphere, with no spectral theory.\<close>

lemma polarization_symmetric:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
  shows "4 * (u \<bullet> W v) = (u + v) \<bullet> W (u + v) - (u - v) \<bullet> W (u - v)"
proof -
  have a: "W (u + v) = W u + W v"
    using lin unfolding linear_iff by blast
  have b: "W (u - v) = W u - W v"
    using lin by (simp add: linear_diff)
  have e1: "(u + v) \<bullet> W (u + v) = u \<bullet> W u + u \<bullet> W v + (v \<bullet> W u + v \<bullet> W v)"
    unfolding a by (simp add: inner_add_left inner_add_right)
  have e2: "(u - v) \<bullet> W (u - v) = u \<bullet> W u - u \<bullet> W v - (v \<bullet> W u - v \<bullet> W v)"
    unfolding b by (simp add: inner_diff_left inner_diff_right)
  have s: "v \<bullet> W u = u \<bullet> W v"
    by (rule sym)
  show ?thesis
    unfolding e1 e2 s by simp
qed

theorem symmetric_form_bound:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
  shows "\<bar>u \<bullet> W v\<bar> \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
proof -
  have pol: "4 * (u \<bullet> W v) = (u + v) \<bullet> W (u + v) - (u - v) \<bullet> W (u - v)"
    by (rule polarization_symmetric[OF lin sym])
  have b1: "\<bar>(u + v) \<bullet> W (u + v)\<bar> \<le> c * (norm (u + v))\<^sup>2"
    by (rule bnd)
  have b2: "\<bar>(u - v) \<bullet> W (u - v)\<bar> \<le> c * (norm (u - v))\<^sup>2"
    by (rule bnd)
  have b1a: "- (c * (norm (u + v))\<^sup>2) \<le> (u + v) \<bullet> W (u + v)"
    using b1 by (simp add: abs_le_iff)
  have b1b: "(u + v) \<bullet> W (u + v) \<le> c * (norm (u + v))\<^sup>2"
    using b1 by (simp add: abs_le_iff)
  have b2a: "- (c * (norm (u - v))\<^sup>2) \<le> (u - v) \<bullet> W (u - v)"
    using b2 by (simp add: abs_le_iff)
  have b2b: "(u - v) \<bullet> W (u - v) \<le> c * (norm (u - v))\<^sup>2"
    using b2 by (simp add: abs_le_iff)
  have par: "(norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2
      = 2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2"
    by (simp add: power2_norm_eq_inner inner_add_left inner_add_right
        inner_diff_left inner_diff_right inner_commute)
  have e: "c * (norm (u + v))\<^sup>2 + c * (norm (u - v))\<^sup>2
      = 2 * (c * ((norm u)\<^sup>2 + (norm v)\<^sup>2))"
  proof -
    have "c * (norm (u + v))\<^sup>2 + c * (norm (u - v))\<^sup>2
        = c * ((norm (u + v))\<^sup>2 + (norm (u - v))\<^sup>2)"
      by (simp add: algebra_simps)
    also have "\<dots> = c * (2*(norm u)\<^sup>2 + 2*(norm v)\<^sup>2)"
      unfolding par ..
    also have "\<dots> = 2 * (c * ((norm u)\<^sup>2 + (norm v)\<^sup>2))"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro abs_leI)
    show "u \<bullet> W v \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
      using pol b1b b2a e by linarith
    show "- (u \<bullet> W v) \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
      using pol b1a b2b e by linarith
  qed
qed

text \<open>On the unit sphere the bound is simply \<open>c\<close>.\<close>

corollary symmetric_form_bound_unit:
  fixes W :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes lin: "linear W" and sym: "\<And>v w. v \<bullet> W w = w \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
    and nu: "norm u = 1" and nv: "norm v = 1"
  shows "\<bar>u \<bullet> W v\<bar> \<le> c"
proof -
  have "\<bar>u \<bullet> W v\<bar> \<le> c * ((norm u)\<^sup>2 + (norm v)\<^sup>2) / 2"
    by (rule symmetric_form_bound[OF lin sym bnd])
  then show ?thesis
    unfolding nu nv by simp
qed

text \<open>Applied to the basis matrices, the bound on the unit sphere bounds every
  entry of the matrix by \<open>c\<close>, hence its norm by the number of entries times
  \<open>c\<close>.\<close>

theorem norm_matrix_le_of_form_bound:
  fixes W :: "real^'n::finite \<Rightarrow> real^'n"
  assumes lin: "linear W" and sym: "\<And>v z. v \<bullet> W z = z \<bullet> W v"
    and bnd: "\<And>k. \<bar>k \<bullet> W k\<bar> \<le> c * (norm k)\<^sup>2"
  shows "norm (matrix W) \<le> real (card (Basis :: (real^'n^'n) set)) * c"
proof (rule norm_le_card_Basis_bound)
  fix e :: "real^'n^'n"
  assume "e \<in> Basis"
  then obtain i j where e: "e = axis i (axis j 1)"
    using matrix_Basis_cases by blast
  have nu: "norm (axis i (1::real) :: real^'n) = 1"
    by (rule norm_axis_1)
  have nv: "norm (axis j (1::real) :: real^'n) = 1"
    by (rule norm_axis_1)
  have "\<bar>(axis i 1 :: real^'n) \<bullet> W (axis j 1)\<bar> \<le> c"
    by (rule symmetric_form_bound_unit[OF lin sym bnd nu nv])
  then show "\<bar>matrix W \<bullet> e\<bar> \<le> c"
    unfolding e inner_matrix_axis[OF lin] .
qed

subsection \<open>Positive semidefiniteness passes to limits\<close>

text \<open>The quadratic form is continuous in the matrix, so positive
  semidefiniteness is a closed condition.\<close>

lemma continuous_on_quadform:
  fixes x :: "real^'n::finite"
  shows "continuous_on UNIV (\<lambda>a :: real^'n^'n. x \<bullet> (a *v x))"
  by (rule linear_continuous_on[OF bounded_linear_quadform])

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

theorem psd_limit:
  fixes A :: "nat \<Rightarrow> real^'n::finite^'n"
  assumes conv: "A \<longlonglongrightarrow> A0" and p: "\<And>i. psd (A i)"
  shows "psd A0"
  using closed_sequentially[OF closed_psd, of A A0] conv p by blast

subsection \<open>The asymptotic ordering\<close>

text \<open>Perturbing a doubled functional by \<open>-\<delta>\<parallel>z-\<xi>\<^sub>0\<parallel>\<^sup>2\<close> shifts \<open>X\<close> to
  \<open>X+2\<delta>I\<close> and \<open>Y\<close> to \<open>Y-2\<delta>I\<close>, so \<open>(Y-X)-4\<delta>I\<close> need not be psd even when
  \<open>Y-X\<close> is: the ordering is lost at each index.  What survives is the
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

(*<*)
end
(*>*)
