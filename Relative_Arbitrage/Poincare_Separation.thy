
(*<*)
theory Poincare_Separation
  imports Operator_Continuity
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
  @{theory Relative_Arbitrage.Curvature_Operator}.\<close>

lemma trace_diff_matrix:
  fixes A B :: "real^'n::finite^'n"
  shows "trace (A - B) = trace A - trace B"
  unfolding trace_def by (simp add: sum_subtractf)

section \<open>The full Ky Fan sum is the trace\<close>

text \<open>\<open>kyfan CARD('n)\<close> takes the whole spectrum, so it equals the trace, by
  evaluating \<open>kyfan\<close> on the eigenbasis via the completeness relation.\<close>

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

section \<open>The Rayleigh bounds\<close>

text \<open>A unit vector gives a rank-one projection, and its orthogonal
  complement a projection of trace \<open>n-1\<close>.\<close>

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

section \<open>\<open>M\<^sub>p\<close> on the hyperplane \<open>p\<^sup>\<bottom>\<close>\<close>

text \<open>On \<open>p\<^sup>\<bottom>\<close> the projection \<open>I - pp'/|p|\<^sup>2\<close> acts as the identity, so
  \<open>M\<^sub>p\<close> has exactly the Rayleigh quotients of \<open>M\<close> there, and its
  \<open>p\<close>-direction eigenvalue \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close> is the smallest of its
  spectrum, as needed for Eq. (3.5).\<close>

lemma rank1proj_annihilates_perp:
  fixes p :: "real^'n::finite"
  assumes y: "p \<bullet> y = 0"
  shows "rank1proj p *v y = 0"
proof -
  have "rank1proj p *v y = inverse (p \<bullet> p) *\<^sub>R (outer_prod p p *v y)"
    unfolding rank1proj_def by (rule scaleR_matrix_vector_assoc[symmetric])
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R ((p \<bullet> y) *\<^sub>R p)"
    by simp
  also have "\<dots> = 0"
    by (simp add: y)
  finally show ?thesis .
qed

lemma perp_proj_fixes_perp:
  fixes p :: "real^'n::finite"
  assumes y: "p \<bullet> y = 0"
  shows "(mat 1 - rank1proj p) *v y = y"
  by (simp add: matrix_vector_mult_diff rank1proj_annihilates_perp[OF y])

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
    unfolding MpQ by (rule matrix_vector_mult_add)
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

text \<open>The hyperplane \<open>p\<^sup>\<bottom>\<close> is \<open>M\<^sub>p\<close>-invariant, so it carries an orthonormal
  eigenbasis of \<open>M\<^sub>p\<close>; adjoining the unit eigenvector \<open>p/|p|\<close> gives an
  eigenbasis of the whole space with \<open>p\<close> distinguished and the rest in
  \<open>p\<^sup>\<bottom>\<close>.\<close>

lemma Mp_invariant_perp:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0" and y: "p \<bullet> y = 0"
  shows "p \<bullet> (Mp p M *v y) = 0"
proof -
  have symQ: "transpose (mat 1 - rank1proj p :: real^'n^'n) = mat 1 - rank1proj p"
    by (rule symmetric_perp_proj)
  have Qp: "(mat 1 - rank1proj p) *v p = 0"
    by (simp add: matrix_vector_mult_diff rank1proj_apply_self[OF p])
  have "p \<bullet> (Mp p M *v y) = p \<bullet> ((mat 1 - rank1proj p) *v (M *v y))"
    by (simp add: Mp_apply_perp[OF p y])
  also have "\<dots> = (M *v y) \<bullet> ((mat 1 - rank1proj p) *v p)"
    by (rule sym_inner_swap[OF symQ])
  also have "\<dots> = 0"
    by (simp add: Qp)
  finally show ?thesis .
qed

theorem Mp_eigenbasis_adapted:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
  shows "\<exists>B. onormal B \<and> span B = UNIV
      \<and> (\<forall>u\<in>B. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u)
      \<and> p /\<^sub>R norm p \<in> B
      \<and> (\<forall>u \<in> B - {p /\<^sub>R norm p}. p \<bullet> u = 0)"
proof -
  define q where "q = p /\<^sub>R norm p"
  define H where "H = {y :: real^'n. p \<bullet> y = 0}"
  have np: "norm p \<noteq> 0"
    using p by simp
  have nq: "norm q = 1"
    unfolding q_def using np by simp
  have symMp: "transpose (Mp p M) = Mp p M"
    by (rule transpose_Mp[OF sym])
  have subH: "subspace H"
    unfolding H_def by (simp add: subspace_hyperplane)
  have invH: "\<forall>y\<in>H. Mp p M *v y \<in> H"
    unfolding H_def using Mp_invariant_perp[OF p] by simp
  obtain B0 where B0: "onormal B0" "B0 \<subseteq> H" "span B0 = H"
    and eig0: "\<forall>u\<in>B0. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u"
    using invariant_subspace_eigenbasis_ex[OF symMp subH invH] by blast
  have finB0: "finite B0"
    by (rule onormal_finite[OF B0(1)])
  have qperp: "q \<bullet> u = 0" if u: "u \<in> B0" for u
  proof -
    have "p \<bullet> u = 0"
      using u B0(2) by (auto simp: H_def)
    then show ?thesis
      unfolding q_def by simp
  qed
  text \<open>\<open>q\<close> is not already in \<open>B\<^sub>0\<close>, since \<open>B\<^sub>0 \<subseteq> p\<^sup>\<bottom>\<close> while \<open>p \<bullet> q = |p| \<noteq> 0\<close>.\<close>
  have pq: "p \<bullet> q = norm p"
    unfolding q_def using np
    by (simp add: dot_square_norm power2_eq_square)
  have qnotin: "q \<notin> B0"
    using pq np B0(2) by (auto simp: H_def)
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
      using nq B0(1) by (auto simp: onormal_def)
  qed
  text \<open>Completeness: split \<open>x\<close> into its \<open>q\<close>-component and a remainder that is
    orthogonal to \<open>p\<close>, hence lies in \<open>span B\<^sub>0\<close>.\<close>
  have spanB: "span B = UNIV"
  proof -
    have "x \<in> span B" for x :: "real^'n"
    proof -
      define z where "z = x - (q \<bullet> x) *\<^sub>R q"
      have pz: "p \<bullet> z = 0"
      proof -
        have qx: "q \<bullet> x = inverse (norm p) * (p \<bullet> x)"
          unfolding q_def by simp
        have "p \<bullet> z = p \<bullet> x - (q \<bullet> x) * (p \<bullet> q)"
          unfolding z_def by (simp add: inner_diff_right)
        also have "\<dots> = p \<bullet> x - (inverse (norm p) * (p \<bullet> x)) * norm p"
          unfolding qx pq by (rule refl)
        also have "\<dots> = 0"
          using np by simp
        finally show ?thesis .
      qed
      have zB0: "z \<in> span B0"
        using pz B0(3) unfolding H_def by simp
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
  have eigB: "\<forall>u\<in>B. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u"
    unfolding B_def
  proof (intro ballI)
    fix u assume "u \<in> insert q B0"
    then show "Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u"
    proof (cases "u = q")
      case True
      have Mpp: "Mp p M *v p = min (eigval CARD('n) M) 0 *\<^sub>R p"
        by (rule Mp_apply_p[OF p])
      have pull: "Mp p M *v (inverse (norm p) *\<^sub>R p)
          = inverse (norm p) *\<^sub>R (Mp p M *v p)"
        by (simp add: matrix_scaleR_vector_ac scaleR_matrix_vector_assoc)
      have Mpq: "Mp p M *v q = min (eigval CARD('n) M) 0 *\<^sub>R q"
      proof -
        have "Mp p M *v q = inverse (norm p) *\<^sub>R (min (eigval CARD('n) M) 0 *\<^sub>R p)"
          unfolding q_def pull Mpp by (rule refl)
        also have "\<dots> = min (eigval CARD('n) M) 0 *\<^sub>R q"
          unfolding q_def by (simp add: mult.commute)
        finally show ?thesis .
      qed
      have qq: "q \<bullet> q = 1"
        using nq by (simp add: dot_square_norm)
      have "q \<bullet> (Mp p M *v q) = min (eigval CARD('n) M) 0"
        unfolding Mpq by (simp add: qq)
      then show ?thesis
        using True Mpq by simp
    next
      case False
      then have "u \<in> B0"
        using \<open>u \<in> insert q B0\<close> by simp
      then show ?thesis
        using eig0 by blast
    qed
  qed
  have qB: "q \<in> B"
    unfolding B_def by simp
  have restperp: "\<forall>u \<in> B - {q}. p \<bullet> u = 0"
    unfolding B_def using B0(2) by (auto simp: H_def)
  show ?thesis
    unfolding q_def[symmetric]
    by (rule exI[of _ B]) (intro conjI onB spanB eigB qB restperp)
qed

section \<open>Traces of weighted outer-product sums\<close>

text \<open>The trace of a matrix written in an orthonormal basis as a weighted sum
  of outer products is the sum of the weights, and each basis vector reads off
  its own weight as a Rayleigh quotient.\<close>

lemma trace_sum_matrix:
  fixes f :: "'a \<Rightarrow> real^'n::finite^'n"
  shows "trace (\<Sum>u\<in>S. f u) = (\<Sum>u\<in>S. trace (f u))"
proof -
  have "trace (\<Sum>u\<in>S. f u) = (\<Sum>i\<in>UNIV. \<Sum>u\<in>S. f u $ i $ i)"
    unfolding trace_def by simp
  also have "\<dots> = (\<Sum>u\<in>S. \<Sum>i\<in>UNIV. f u $ i $ i)" by (rule sum.swap)
  also have "\<dots> = (\<Sum>u\<in>S. trace (f u))" unfolding trace_def by (rule refl)
  finally show ?thesis .
qed

lemma trace_weighted_outer_sum:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B"
  shows "trace (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) = (\<Sum>v\<in>B. g v)"
proof -
  have "trace (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v)
      = (\<Sum>v\<in>B. trace (g v *\<^sub>R outer_prod v v))"
    by (rule trace_sum_matrix)
  also have "\<dots> = (\<Sum>v\<in>B. g v * (v \<bullet> v))"
    by (intro sum.cong refl) (simp add: trace_scaleR_matrix)
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

section \<open>The Courant-Fischer min-max lower bound\<close>

text \<open>The general Courant-Fischer lower bound: if the Rayleigh quotient of
  \<open>a\<close> is at least \<open>c\<close> on a subspace of dimension \<open>\<ge> m\<close>, then
  \<open>c \<le> eigval m a\<close>, via a comparison subspace whose dimension, together
  with \<open>m\<close>, exceeds \<open>CARD('n)\<close>.\<close>

lemma onormal_subset:
  assumes "onormal B" and "U \<subseteq> B"
  shows "onormal U"
  using assms by (auto simp: onormal_def pairwise_def elim: finite_subset)

theorem eigval_ge_of_subspace:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a"
    and S: "subspace S" "m \<le> dim S"
    and quad: "\<And>x. x \<in> S \<Longrightarrow> c * (x \<bullet> x) \<le> x \<bullet> (a *v x)"
    and m: "0 < m" "m \<le> CARD('n)"
  shows "c \<le> eigval m a"
proof -
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have mB: "m \<le> card B"
    using m(2) cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> B - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finB mB]
    by metis
  have finT: "finite T"
    using T(1) finB by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using T(2) m(1) by auto
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    using finite_arg_min_on[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
        OF finT Tne] by metis
  obtain i where mi: "m = Suc i"
    using m(1) by (cases m) auto
  have cardT: "card T = Suc i"
    using T(2) mi by simp
  have eigw: "eigval m a = w \<bullet> (a *v w)"
    unfolding mi
    by (rule eigval_eq_min_of_threshold[OF B sym eig T(1) cardT thresh w wmin])
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

text \<open>The original \<open>c = 1\<close> form, which is what \<open>eigen_lb\<close> delivers.\<close>

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
  have finV: "finite V"
    by (rule onormal_finite[OF V(1)])
  have cardV: "card V = CARD('n)"
    by (rule onormal_span_card[OF V])
  have mV: "m \<le> card V"
    using m(2) cardV by simp
  obtain T where T: "T \<subseteq> V" "card T = m"
    and thresh: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> V - T \<Longrightarrow> v \<bullet> (a *v v) \<le> u \<bullet> (a *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finV mV]
    by metis
  have finT: "finite T"
    using T(1) finV by (rule finite_subset)
  have Tne: "T \<noteq> {}"
    using T(2) m(1) by auto
  obtain w where w: "w \<in> T"
    and wmin: "\<And>u. u \<in> T \<Longrightarrow> w \<bullet> (a *v w) \<le> u \<bullet> (a *v u)"
    using finite_arg_min_on[where f = "\<lambda>u :: real^'n. u \<bullet> (a *v u)",
        OF finT Tne] by metis
  obtain i where mi: "m = Suc i"
    using m(1) by (cases m) auto
  have cardT: "card T = Suc i"
    using T(2) mi by simp
  have eigw: "eigval m a = w \<bullet> (a *v w)"
    unfolding mi
    by (rule eigval_eq_min_of_threshold[OF V sym eig T(1) cardT thresh w wmin])
  have one: "1 \<le> eigval m a"
    by (rule eigval_ge_of_eigen_lb[OF sym lb m])
  have inT: "min (v \<bullet> (a *v v)) 1 = 1" if v: "v \<in> T" for v
  proof -
    have "1 \<le> w \<bullet> (a *v w)"
      using one eigw by simp
    also have "\<dots> \<le> v \<bullet> (a *v v)"
      by (rule wmin[OF v])
    finally show ?thesis
      by simp
  qed
  have "real m = (\<Sum>v\<in>T. min (v \<bullet> (a *v v)) 1)"
    using inT T(2) by simp
  also have "\<dots> \<le> (\<Sum>v\<in>V. min (v \<bullet> (a *v v)) 1)"
    using finV T(1) psd by (intro sum_mono2) auto
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
    and eig: "\<And>v. v \<in> V \<Longrightarrow> a *v v = (v \<bullet> (a *v v)) *\<^sub>R v"
    using symmetric_eigenbasis[OF sym] by metis
  have finV: "finite V"
    by (rule onormal_finite[OF V(1)])
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

lemma reduce_weights_to_exact:
  fixes t :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
    and t0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t u"
    and tsum: "real m \<le> (\<Sum>u\<in>B. t u)"
  shows "\<exists>t'. (\<forall>u\<in>B. 0 \<le> t' u \<and> t' u \<le> t u) \<and> (\<Sum>u\<in>B. t' u) = real m"
proof (cases "m = 0")
  case True
  show ?thesis
    by (rule exI[of _ "\<lambda>_. 0"]) (simp add: True t0)
next
  case False
  have mpos: "0 < real m"
    using False by simp
  have pos: "0 < (\<Sum>u\<in>B. t u)"
    using mpos tsum by simp
  define r where "r = real m / (\<Sum>u\<in>B. t u)"
  have r0: "0 \<le> r"
    unfolding r_def using mpos pos by simp
  have r1: "r \<le> 1"
    unfolding r_def using tsum pos by simp
  have bounds: "0 \<le> r * t u \<and> r * t u \<le> t u" if u: "u \<in> B" for u
  proof
    show "0 \<le> r * t u"
      using r0 t0[OF u] by simp
    have "r * t u \<le> 1 * t u"
      using r1 t0[OF u] by (intro mult_right_mono) auto
    then show "r * t u \<le> t u"
      by simp
  qed
  have "(\<Sum>u\<in>B. r * t u) = r * (\<Sum>u\<in>B. t u)"
    by (rule sum_distrib_left[symmetric])
  also have "\<dots> = real m"
    unfolding r_def using pos by simp
  finally have rsum: "(\<Sum>u\<in>B. r * t u) = real m" .
  show ?thesis
    by (rule exI[of _ "\<lambda>u. r * t u"]) (intro conjI ballI bounds rsum)
qed

text \<open>The box program with \<open>(\<Sum>t) \<ge> real m\<close> rather than equality: the
  positive part uses \<open>t \<le> 1\<close> directly, and the negative part is pushed onto
  the scaled-down weights before applying \<open>sum_weighted_le_top_subset\<close>.\<close>

theorem box_program_bound:
  fixes lam t :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m: "m \<le> card B"
    and t0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t u" and t1: "\<And>u. u \<in> B \<Longrightarrow> t u \<le> 1"
    and tsum: "real m \<le> (\<Sum>u\<in>B. t u)"
  shows "\<exists>T. T \<subseteq> B \<and> card T = m
      \<and> (\<Sum>u\<in>B. lam u * t u)
          \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
proof -
  obtain t' where t': "\<forall>u\<in>B. 0 \<le> t' u \<and> t' u \<le> t u"
    and t'sum: "(\<Sum>u\<in>B. t' u) = real m"
    using reduce_weights_to_exact[OF finB t0 tsum] by blast
  have t'0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t' u"
    using t' by blast
  have t'1: "\<And>u. u \<in> B \<Longrightarrow> t' u \<le> 1"
    using t' t1 by force
  obtain T where T: "T \<subseteq> B" "card T = m"
    and neg': "(\<Sum>u\<in>B. min (lam u) 0 * t' u) \<le> (\<Sum>u\<in>T. min (lam u) 0)"
    using sum_weighted_le_top_subset[where f = "\<lambda>u. min (lam u) 0" and t = t',
        OF finB m t'0 t'1 t'sum] by metis
  have negmono: "(\<Sum>u\<in>B. min (lam u) 0 * t u) \<le> (\<Sum>u\<in>B. min (lam u) 0 * t' u)"
  proof (rule sum_mono)
    fix u assume u: "u \<in> B"
    have "t' u \<le> t u"
      using t' u by blast
    then show "min (lam u) 0 * t u \<le> min (lam u) 0 * t' u"
      by (intro mult_left_mono_neg) auto
  qed
  have pos: "(\<Sum>u\<in>B. max (lam u) 0 * t u) \<le> (\<Sum>u\<in>B. max (lam u) 0)"
  proof (rule sum_mono)
    fix u assume u: "u \<in> B"
    have "max (lam u) 0 * t u \<le> max (lam u) 0 * 1"
      using t1[OF u] by (intro mult_left_mono) auto
    then show "max (lam u) 0 * t u \<le> max (lam u) 0"
      by simp
  qed
  have split: "lam u * t u = max (lam u) 0 * t u + min (lam u) 0 * t u" for u
    by (simp add: min_def max_def)
  have "(\<Sum>u\<in>B. lam u * t u)
      = (\<Sum>u\<in>B. max (lam u) 0 * t u) + (\<Sum>u\<in>B. min (lam u) 0 * t u)"
    unfolding split by (rule sum.distrib)
  also have "\<dots> \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
    using pos negmono neg' by (intro add_mono) auto
  finally have le: "(\<Sum>u\<in>B. lam u * t u)
      \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)" .
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T(1) T(2) le)
qed

text \<open>The upper bound of Eq. (3.5): writing \<open>w = t + s\<close> with
  \<open>t u = min (w u) 1\<close> and \<open>s u = max (w u - 1) 0\<close>, the \<open>t\<close>-part is the box
  program and the \<open>s\<close>-part contributes \<open>\<le> (L-1) * (\<Sum> max (lam u) 0)\<close>,
  giving the bracket of Eq. (3.5).\<close>

theorem lp_upper_bound:
  fixes lam w :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m: "m \<le> card B" and L: "1 \<le> L"
    and w0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> w u" and wL: "\<And>u. u \<in> B \<Longrightarrow> w u \<le> L"
    and wsum: "real m \<le> (\<Sum>u\<in>B. min (w u) 1)"
  shows "\<exists>T. T \<subseteq> B \<and> card T = m
      \<and> (\<Sum>u\<in>B. lam u * w u)
          \<le> L * (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
proof -
  have t0: "0 \<le> min (w u) 1" if u: "u \<in> B" for u
    using w0[OF u] by simp
  have t1: "min (w u) 1 \<le> 1" for u
    by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and tpart: "(\<Sum>u\<in>B. lam u * min (w u) 1)
        \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
    using box_program_bound[where lam = lam and t = "\<lambda>u. min (w u) 1",
        OF finB m t0 t1 wsum] by blast
  have spart: "(\<Sum>u\<in>B. lam u * (w u - min (w u) 1))
      \<le> (L - 1) * (\<Sum>u\<in>B. max (lam u) 0)"
  proof -
    have "(\<Sum>u\<in>B. lam u * (w u - min (w u) 1))
        \<le> (\<Sum>u\<in>B. max (lam u) 0 * (L - 1))"
    proof (rule sum_mono)
      fix u assume u: "u \<in> B"
      have s0: "0 \<le> w u - min (w u) 1"
        by simp
      have sL: "w u - min (w u) 1 \<le> L - 1"
        using wL[OF u] L by (simp add: min_def)
      have "lam u * (w u - min (w u) 1) \<le> max (lam u) 0 * (w u - min (w u) 1)"
        using s0 by (intro mult_right_mono) auto
      also have "\<dots> \<le> max (lam u) 0 * (L - 1)"
        using sL by (intro mult_left_mono) auto
      finally show "lam u * (w u - min (w u) 1) \<le> max (lam u) 0 * (L - 1)" .
    qed
    also have "\<dots> = (L - 1) * (\<Sum>u\<in>B. max (lam u) 0)"
      by (simp add: sum_distrib_left mult.commute)
    finally show ?thesis .
  qed
  have decomp: "lam u * w u
      = lam u * min (w u) 1 + lam u * (w u - min (w u) 1)" for u
    by (simp add: algebra_simps)
  have "(\<Sum>u\<in>B. lam u * w u)
      = (\<Sum>u\<in>B. lam u * min (w u) 1) + (\<Sum>u\<in>B. lam u * (w u - min (w u) 1))"
    unfolding decomp by (rule sum.distrib)
  also have "\<dots> \<le> ((\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0))
      + (L - 1) * (\<Sum>u\<in>B. max (lam u) 0)"
    using tpart spart by (rule add_mono)
  also have "\<dots> = L * (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
    by (simp add: algebra_simps)
  finally have le: "(\<Sum>u\<in>B. lam u * w u)
      \<le> L * (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)" .
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T(1) T(2) le)
qed

text \<open>The box program returns an arbitrary size-\<open>m\<close> set \<open>T\<close>, whereas
  \<open>kyfan m - possum m\<close> sums over a threshold set.  Since \<open>min (\<cdot>) 0\<close> is
  monotone, a threshold set for \<open>lam\<close> is also one for
  \<open>\<lambda>u. min (lam u) 0\<close>, and \<open>threshold_sum_maximal\<close> gives the inequality.\<close>

lemma sum_min_le_threshold:
  fixes lam :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
    and T0: "T0 \<subseteq> B" "card T0 = m"
    and thresh: "\<And>u v. u \<in> T0 \<Longrightarrow> v \<in> B - T0 \<Longrightarrow> lam v \<le> lam u"
    and T: "T \<subseteq> B" "card T = m"
  shows "(\<Sum>u\<in>T. min (lam u) 0) \<le> (\<Sum>u\<in>T0. min (lam u) 0)"
proof -
  have threshmin: "min (lam v) 0 \<le> min (lam u) 0"
    if u: "u \<in> T0" and v: "v \<in> B - T0" for u v
    using thresh[OF u v] by (simp add: min_def)
  show ?thesis
    by (rule threshold_sum_maximal[where lam = "\<lambda>u. min (lam u) 0",
          OF finB T0(1) T0(2) threshmin T(1) T(2)])
qed

section \<open>The upper bound of Eq. (3.5) in bracket form\<close>

text \<open>For a symmetric \<open>N\<close> with eigenbasis \<open>B\<close>, and weights coming from any
  \<open>a\<close> satisfying the feasible-set constraints, the objective is bounded by
  \<open>bracket m L N\<close>.  The two conversions are \<open>possum_full_eq_sum_basis\<close> (the
  positive part) and \<open>kyfan_minus_possum_threshold\<close> (the negative part, via
  \<open>sum_min_le_threshold\<close>).\<close>

theorem bracket_upper_bound:
  fixes N a :: "real^'n::finite^'n"
  assumes symN: "transpose N = N"
    and B: "onormal B" "span B = UNIV"
    and eigN: "\<And>u. u \<in> B \<Longrightarrow> N *v u = (u \<bullet> (N *v u)) *\<^sub>R u"
    and m: "m \<le> CARD('n)" and L: "1 \<le> L"
    and w0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> u \<bullet> (a *v u)"
    and wL: "\<And>u. u \<in> B \<Longrightarrow> u \<bullet> (a *v u) \<le> L"
    and wsum: "real m \<le> (\<Sum>u\<in>B. min (u \<bullet> (a *v u)) 1)"
  shows "(\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u))) \<le> bracket m L N"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
  have mB: "m \<le> card B"
    using m cardB by simp
  obtain T where T: "T \<subseteq> B" "card T = m"
    and lp: "(\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u)))
        \<le> L * (\<Sum>u\<in>B. max (u \<bullet> (N *v u)) 0)
          + (\<Sum>u\<in>T. min (u \<bullet> (N *v u)) 0)"
    using lp_upper_bound[where lam = "\<lambda>u :: real^'n. u \<bullet> (N *v u)"
        and w = "\<lambda>u :: real^'n. u \<bullet> (a *v u)", OF finB mB L w0 wL wsum]
    by blast
  text \<open>Pass to a threshold set, where the negative part becomes
    \<open>kyfan m - possum m\<close>.\<close>
  obtain T0 where T0: "T0 \<subseteq> B" "card T0 = m"
    and thresh: "\<And>u v. u \<in> T0 \<Longrightarrow> v \<in> B - T0
        \<Longrightarrow> v \<bullet> (N *v v) \<le> u \<bullet> (N *v u)"
    using exists_top_subset[where f = "\<lambda>u :: real^'n. u \<bullet> (N *v u)", OF finB mB]
    by metis
  have negle: "(\<Sum>u\<in>T. min (u \<bullet> (N *v u)) 0)
      \<le> (\<Sum>u\<in>T0. min (u \<bullet> (N *v u)) 0)"
    by (rule sum_min_le_threshold[where lam = "\<lambda>u :: real^'n. u \<bullet> (N *v u)",
          OF finB T0(1) T0(2) thresh T(1) T(2)])
  have negeq: "(\<Sum>u\<in>T0. min (u \<bullet> (N *v u)) 0) = kyfan m N - possum m N"
    by (rule kyfan_minus_possum_threshold[OF B symN eigN T0(1) T0(2) thresh,
          symmetric])
  have poseq: "(\<Sum>u\<in>B. max (u \<bullet> (N *v u)) 0) = possum CARD('n) N"
    by (rule possum_full_eq_sum_basis[OF B symN eigN, symmetric])
  have "(\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u)))
      \<le> L * (\<Sum>u\<in>B. max (u \<bullet> (N *v u)) 0)
        + (\<Sum>u\<in>T0. min (u \<bullet> (N *v u)) 0)"
    using lp negle by simp
  also have "\<dots> = L * possum CARD('n) N + (kyfan m N - possum m N)"
    unfolding poseq negeq by (rule refl)
  also have "\<dots> = bracket m L N"
    by (simp add: bracket_def)
  finally show ?thesis .
qed

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
  combination of outer products (\<open>trace_Mp\<close> in @{theory Relative_Arbitrage.Operator_Continuity} gives the
  first fact).  This section carries out the expansion and its weight
  constraints.\<close>

section \<open>Feasibility of weighted outer-product sums\<close>

text \<open>For the reverse inequality of Eq. (3.5) a feasible \<open>a\<close> attaining the
  bracket must be exhibited, of the form
  \<open>a = (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u)\<close> for an orthonormal basis \<open>B\<close>.  This
  section checks each clause of \<open>feasible\<close> for such a sum.\<close>

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

lemma weighted_outer_sum_annihilates:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes finB: "finite B"
    and van: "\<And>u. u \<in> B \<Longrightarrow> c u = 0 \<or> p \<bullet> u = 0"
  shows "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v p = 0"
proof -
  have "(\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v p = (\<Sum>u\<in>B. c u *\<^sub>R ((u \<bullet> p) *\<^sub>R u))"
    by (simp add: matrix_vector_mult_sum scaleR_matrix_vector)
  also have "\<dots> = (\<Sum>u\<in>B. 0)"
  proof (intro sum.cong refl)
    fix u assume u: "u \<in> B"
    show "c u *\<^sub>R ((u \<bullet> p) *\<^sub>R u) = 0"
      using van[OF u] by (auto simp: inner_commute)
  qed
  also have "\<dots> = 0"
    by simp
  finally show ?thesis .
qed

text \<open>The upper eigenvalue bound: all weights below \<open>L\<close> gives \<open>eigen_ub \<dots> L\<close>,
  by Parseval.\<close>

lemma eigen_ub_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" "span B = UNIV"
    and cL: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> L"
  shows "eigen_ub (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) L"
  unfolding eigen_ub_def
proof (intro allI)
  fix x :: "real^'n"
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have "x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x) = (\<Sum>u\<in>B. c u * (u \<bullet> x)^2)"
    by (rule quadform_weighted_outer_sum_eq[OF finB])
  also have "\<dots> \<le> (\<Sum>u\<in>B. L * (u \<bullet> x)^2)"
    using cL by (intro sum_mono mult_right_mono) auto
  also have "\<dots> = L * (\<Sum>u\<in>B. (u \<bullet> x)^2)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = L * (x \<bullet> x)"
    by (simp add: parseval_onormal[OF B])
  finally show "x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x) \<le> L * (x \<bullet> x)" .
qed

text \<open>The lower eigenvalue bound: a subset of the basis on which the weights are
  at least \<open>1\<close> spans a subspace witnessing \<open>eigen_lb\<close>, of dimension its
  cardinality.\<close>

lemma eigen_lb_weighted_outer_sum:
  fixes c :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B" "span B = UNIV"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u"
    and S: "S \<subseteq> B" and cS: "\<And>u. u \<in> S \<Longrightarrow> 1 \<le> c u"
    and m: "m \<le> card S"
  shows "eigen_lb (\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) m"
  unfolding eigen_lb_def
proof (intro exI[of _ "span S"] conjI)
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  show "subspace (span S)"
    by (rule subspace_span)
  have onS: "onormal S"
    by (rule onormal_subset[OF B(1) S])
  have "card S = dim (span S)"
    by (rule onormal_card_dim_span[OF onS])
  then show "m \<le> dim (span S)"
    using m by simp
  show "\<forall>x\<in>span S. x \<bullet> x \<le> x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x)"
  proof (intro ballI)
    fix x assume x: "x \<in> span S"
    have vanish: "u \<bullet> x = 0" if u: "u \<in> B - S" for u
    proof (rule onormal_orthogonal_to_span_complement[OF B(1) _ S _ x])
      show "u \<in> B" using u by blast
      show "u \<notin> S" using u by blast
    qed
    have "x \<bullet> x = (\<Sum>u\<in>B. (u \<bullet> x)^2)"
      by (rule parseval_onormal[OF B, symmetric])
    also have "\<dots> = (\<Sum>u\<in>S. (u \<bullet> x)^2)"
      by (rule sum.mono_neutral_right[OF finB S]) (auto simp: vanish)
    also have "\<dots> \<le> (\<Sum>u\<in>S. c u * (u \<bullet> x)^2)"
    proof (rule sum_mono)
      fix u assume u: "u \<in> S"
      have "1 * (u \<bullet> x)^2 \<le> c u * (u \<bullet> x)^2"
        using cS[OF u] by (intro mult_right_mono) auto
      then show "(u \<bullet> x)^2 \<le> c u * (u \<bullet> x)^2"
        by simp
    qed
    also have "\<dots> = (\<Sum>u\<in>B. c u * (u \<bullet> x)^2)"
      by (rule sum.mono_neutral_right[OF finB S, symmetric]) (auto simp: vanish)
    also have "\<dots> = x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x)"
      by (rule quadform_weighted_outer_sum_eq[OF finB, symmetric])
    finally show "x \<bullet> x \<le> x \<bullet> ((\<Sum>u\<in>B. c u *\<^sub>R outer_prod u u) *v x)" .
  qed
qed

lemma Mp_quadform_unit_p:
  fixes M :: "real^'n::finite^'n"
  assumes p: "p \<noteq> 0"
  shows "(p /\<^sub>R norm p) \<bullet> (Mp p M *v (p /\<^sub>R norm p)) = min (eigval CARD('n) M) 0"
proof -
  define q where "q = p /\<^sub>R norm p"
  have np: "norm p \<noteq> 0"
    using p by simp
  have nq: "norm q = 1"
    unfolding q_def using np by simp
  have qq: "q \<bullet> q = 1"
    using nq by (simp add: dot_square_norm)
  have Mpp: "Mp p M *v p = min (eigval CARD('n) M) 0 *\<^sub>R p"
    by (rule Mp_apply_p[OF p])
  have pull: "Mp p M *v (inverse (norm p) *\<^sub>R p)
      = inverse (norm p) *\<^sub>R (Mp p M *v p)"
    by (simp add: matrix_scaleR_vector_ac scaleR_matrix_vector_assoc)
  have "Mp p M *v q = min (eigval CARD('n) M) 0 *\<^sub>R q"
  proof -
    have "Mp p M *v q
        = inverse (norm p) *\<^sub>R (min (eigval CARD('n) M) 0 *\<^sub>R p)"
      unfolding q_def pull Mpp by (rule refl)
    also have "\<dots> = min (eigval CARD('n) M) 0 *\<^sub>R q"
      unfolding q_def by (simp add: mult.commute)
    finally show ?thesis .
  qed
  then show ?thesis
    unfolding q_def[symmetric] by (simp add: qq)
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
    unfolding ell_op_def
    by (intro cInf_lower imageI a ell_op_bdd_below)
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
  \<open>bracket_eq_sum\<close> (@{theory Relative_Arbitrage.Eigenvalues}), which rewrites \<open>possum\<close> and
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

text \<open>\<open>rank1proj\<close> depends only on the line through \<open>p\<close>, so \<open>M\<^sub>p\<close> does too.
  Hence the paper's sequence \<open>(q\<^sub>1/m, M)\<close> for the lower bound of Eq. (3.6)
  is constant in \<open>m\<close>: \<open>M\<^sub>q\<^sub>1\<^sub>/\<^sub>m = M\<^sub>q\<^sub>1\<close>, so only \<open>p\<^sup>m \<longrightarrow> 0\<close> matters.\<close>

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

lemma rank1proj_scaleR:
  fixes p :: "real^'n::finite"
  assumes c: "c \<noteq> 0" and p: "p \<noteq> 0"
  shows "rank1proj (c *\<^sub>R p) = rank1proj p"
proof -
  have pp: "p \<bullet> p \<noteq> 0"
    using p by simp
  have c2: "c * c \<noteq> 0"
    using c by simp
  have num: "outer_prod (c *\<^sub>R p) (c *\<^sub>R p) = (c * c) *\<^sub>R outer_prod p p"
    by (simp add: outer_prod_scaleR_left outer_prod_scaleR_right)
  have den: "(c *\<^sub>R p) \<bullet> (c *\<^sub>R p) = (c * c) * (p \<bullet> p)"
    by simp
  have "rank1proj (c *\<^sub>R p)
      = inverse ((c * c) * (p \<bullet> p)) *\<^sub>R ((c * c) *\<^sub>R outer_prod p p)"
    unfolding rank1proj_def num den by (rule refl)
  also have "\<dots> = (inverse ((c * c) * (p \<bullet> p)) * (c * c)) *\<^sub>R outer_prod p p"
    by (rule scaleR_scaleR)
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R outer_prod p p"
    using c2 pp by (simp add: field_simps)
  finally show ?thesis
    unfolding rank1proj_def .
qed

lemma Mp_scaleR:
  fixes M :: "real^'n::finite^'n"
  assumes c: "c \<noteq> 0" and p: "p \<noteq> 0"
  shows "Mp (c *\<^sub>R p) M = Mp p M"
proof -
  have cp: "c *\<^sub>R p \<noteq> 0"
    using c p by simp
  show ?thesis
    unfolding Mp_def
    using cp p by (simp add: rank1proj_scaleR[OF c p])
qed

text \<open>Consequently \<open>F\<close> itself is constant along the paper's sequence.\<close>

corollary ell_op_scaleR_dir:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and c: "0 < c" and p: "p \<noteq> 0" and L: "1 \<le> L"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ell_op k L (c *\<^sub>R p) M = ell_op k L p M"
proof -
  have cp: "c *\<^sub>R p \<noteq> 0"
    using c p by simp
  have "ell_op k L (c *\<^sub>R p) M
      = - (1/2) * bracket (CARD('n) - k) L (Mp (c *\<^sub>R p) M)"
    by (rule ell_op_eq_half_bracket[OF sym cp L k(1) k(2)])
  also have "\<dots> = - (1/2) * bracket (CARD('n) - k) L (Mp p M)"
    using c by (simp add: Mp_scaleR[OF _ p])
  also have "\<dots> = ell_op k L p M"
    by (rule ell_op_eq_half_bracket[OF sym p L k(1) k(2), symmetric])
  finally show ?thesis .
qed

section \<open>The spectrum of \<open>M\<^sub>q\<close> when \<open>q\<close> is an eigenvector of \<open>M\<close>\<close>

text \<open>This is the computation behind Eq. (3.6).  If \<open>q\<close> is a unit eigenvector
  of \<open>M\<close>, any eigenbasis of \<open>M\<close> containing \<open>q\<close> is also an eigenbasis of
  \<open>M\<^sub>q\<close>: off \<open>q\<close> the eigenvalues agree, while \<open>M\<^sub>q\<close> carries
  \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close> at \<open>q\<close>.  Taking \<open>q = q\<^sub>1\<close> the top eigenvector deletes
  \<open>\<lambda>\<^sub>(\<^sub>1\<^sub>)(M)\<close> from the spectrum and replaces it at the bottom, the index
  shift of Eq. (3.6).\<close>

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
  text \<open>@{theory Relative_Arbitrage.Eigenvalues}: \<open>M\<^sub>q\<close> agrees with \<open>M\<close> off \<open>q\<close> and carries
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
  define n where "n = CARD('n)"
  define m where "m = n - k"
  have npos: "0 < n"
    unfolding n_def by (simp add: card_gt_0_iff)
  obtain n' where n': "n = Suc n'"
    using npos by (cases n) auto
  have mn': "m \<le> n'"
    unfolding m_def using k(1) n' by simp
  have mn: "m \<le> n"
    unfolding m_def by simp
  have shiftmax: "eigval i (Mp q M) = eigval (Suc i) M"
    if i1: "1 \<le> i" and i2: "i \<le> n'" for i
  proof -
    have "i \<le> CARD('n) - 1"
      using i2 n' unfolding n_def by simp
    then show ?thesis
      by (rule eigval_Mp_top_eigenvector[OF sym q eigq top i1])
  qed
  text \<open>The positive part: the last eigenvalue drops out, being nonpositive.\<close>
  have pos: "possum n (Mp q M) = (\<Sum>i\<in>{2..n}. max (eigval i M) 0)"
  proof -
    have "possum n (Mp q M) = (\<Sum>i\<in>{1..n}. max (eigval i (Mp q M)) 0)"
      unfolding n_def by (rule possum_eq_sum_pos[OF symMp order_refl])
    also have "\<dots> = (\<Sum>i\<in>{1..n'}. max (eigval i (Mp q M)) 0)
        + max (eigval n (Mp q M)) 0"
      unfolding n' by (simp add: atLeastAtMostSuc_conv)
    also have "\<dots> = (\<Sum>i\<in>{1..n'}. max (eigval (Suc i) M) 0) + 0"
    proof -
      have "max (eigval n (Mp q M)) 0 = 0"
        using eigval_Mp_last_nonpos[OF sym q] unfolding n_def by simp
      moreover have "(\<Sum>i\<in>{1..n'}. max (eigval i (Mp q M)) 0)
          = (\<Sum>i\<in>{1..n'}. max (eigval (Suc i) M) 0)"
        by (intro sum.cong refl) (simp add: shiftmax)
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = (\<Sum>i\<in>{2..n}. max (eigval i M) 0)"
    proof -
      have "(\<Sum>i\<in>{1..n'}. max (eigval (Suc i) M) 0)
          = (\<Sum>i\<in>{2..Suc n'}. max (eigval i M) 0)"
        by (rule sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc]) auto
      then show ?thesis
        unfolding n' by simp
    qed
    finally show ?thesis .
  qed
  text \<open>The negative part: every index involved is at most \<open>n-1\<close>, so the shift
    applies throughout.\<close>
  have neg: "kyfan m (Mp q M) - possum m (Mp q M)
      = (\<Sum>i\<in>{2..m+1}. min (eigval i M) 0)"
  proof -
    have mcard: "m \<le> CARD('n)"
      using mn unfolding n_def by simp
    have "kyfan m (Mp q M) - possum m (Mp q M)
        = (\<Sum>i\<in>{1..m}. min (eigval i (Mp q M)) 0)"
      by (rule kyfan_minus_possum[OF symMp mcard])
    also have "\<dots> = (\<Sum>i\<in>{1..m}. min (eigval (Suc i) M) 0)"
    proof (intro sum.cong refl)
      fix i assume "i \<in> {1..m}"
      then have "1 \<le> i" "i \<le> n'"
        using mn' by auto
      then show "min (eigval i (Mp q M)) 0 = min (eigval (Suc i) M) 0"
        by (simp add: shiftmax)
    qed
    also have "\<dots> = (\<Sum>i\<in>{2..m+1}. min (eigval i M) 0)"
      by (rule sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc]) auto
    finally show ?thesis .
  qed
  have "bracket m L (Mp q M)
      = L * possum n (Mp q M) + (kyfan m (Mp q M) - possum m (Mp q M))"
    unfolding bracket_def n_def by (rule refl)
  also have "\<dots> = L * (\<Sum>i\<in>{2..n}. max (eigval i M) 0)
      + (\<Sum>i\<in>{2..m+1}. min (eigval i M) 0)"
    unfolding pos neg by (rule refl)
  finally show ?thesis
    unfolding m_def n_def .
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

theorem poincare_separation:
  fixes M :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
    and i: "1 \<le> i" "i < CARD('n)"
  shows "eigval (Suc i) M \<le> eigval i (Mp p M)"
proof -
  have symMp: "transpose (Mp p M) = Mp p M"
    by (rule transpose_Mp[OF sym])
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> M *v u = (u \<bullet> (M *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
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
  define n where "n = CARD('n)"
  define m where "m = n - k"
  have npos: "0 < n"
    unfolding n_def by (simp add: card_gt_0_iff)
  obtain n' where n': "n = Suc n'"
    using npos by (cases n) auto
  have mn': "m \<le> n'"
    unfolding m_def using k(1) n' by simp
  have mcard: "m \<le> CARD('n)"
    unfolding m_def n_def by simp
  have shift: "eigval (Suc i) M \<le> eigval i N" if "1 \<le> i" and "i \<le> n'" for i
  proof -
    have "i < CARD('n)"
      using that(2) n' unfolding n_def by simp
    then show ?thesis
      unfolding N_def by (rule eigval_Mp_ge_shift[OF sym that(1)])
  qed
  text \<open>Positive part: drop the last (nonnegative) term, then shift.\<close>
  have pos: "(\<Sum>i\<in>{2..n}. max (eigval i M) 0) \<le> possum n N"
  proof -
    have "(\<Sum>i\<in>{2..n}. max (eigval i M) 0)
        = (\<Sum>i\<in>{1..n'}. max (eigval (Suc i) M) 0)"
      by (rule sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc,
            symmetric]) (auto simp: n')
    also have "\<dots> \<le> (\<Sum>i\<in>{1..n'}. max (eigval i N) 0)"
    proof (intro sum_mono)
      fix i assume "i \<in> {1..n'}"
      then have "1 \<le> i" "i \<le> n'"
        by auto
      then have "eigval (Suc i) M \<le> eigval i N"
        by (rule shift)
      then show "max (eigval (Suc i) M) 0 \<le> max (eigval i N) 0"
        by (rule max.mono[OF _ order_refl])
    qed
    also have "\<dots> \<le> (\<Sum>i\<in>{1..n}. max (eigval i N) 0)"
      unfolding n' by (intro sum_mono2) auto
    also have "\<dots> = possum n N"
      unfolding n_def by (rule possum_eq_sum_pos[OF symN order_refl, symmetric])
    finally show ?thesis .
  qed
  text \<open>Negative part: shift termwise, \<open>min (\<cdot>) 0\<close> being monotone.\<close>
  have neg: "(\<Sum>i\<in>{2..m+1}. min (eigval i M) 0) \<le> kyfan m N - possum m N"
  proof -
    have "(\<Sum>i\<in>{2..m+1}. min (eigval i M) 0)
        = (\<Sum>i\<in>{1..m}. min (eigval (Suc i) M) 0)"
      by (rule sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc,
            symmetric]) auto
    also have "\<dots> \<le> (\<Sum>i\<in>{1..m}. min (eigval i N) 0)"
    proof (intro sum_mono)
      fix i assume "i \<in> {1..m}"
      then have "1 \<le> i" "i \<le> n'"
        using mn' by auto
      then have "eigval (Suc i) M \<le> eigval i N"
        by (rule shift)
      then show "min (eigval (Suc i) M) 0 \<le> min (eigval i N) 0"
        by (rule min.mono[OF _ order_refl])
    qed
    also have "\<dots> = kyfan m N - possum m N"
      by (rule kyfan_minus_possum[OF symN mcard, symmetric])
    finally show ?thesis .
  qed
  have "L * (\<Sum>i\<in>{2..n}. max (eigval i M) 0)
      + (\<Sum>i\<in>{2..m+1}. min (eigval i M) 0)
      \<le> L * possum n N + (kyfan m N - possum m N)"
    using pos neg L by (intro add_mono mult_left_mono) auto
  also have "\<dots> = bracket m L N"
    unfolding bracket_def n_def by (rule refl)
  finally show ?thesis
    unfolding m_def n_def N_def .
qed

section \<open>Continuity of the bracket in the matrix\<close>

text \<open>By Eq. (3.5), \<open>F\<close> is \<open>-\<onehalf> bracket (n-k) L M\<^sub>p\<close>, so the first clause
  of Lemma 3.1 (\<open>F\<^sub>* = F\<^sup>* = F\<close> off \<open>p = 0\<close>) needs \<open>bracket\<close> continuous in
  its matrix argument, and \<open>(p, M) \<mapsto> M\<^sub>p\<close> continuous off \<open>p = 0\<close>.  The
  first is Lipschitz, from \<open>kyfan_lipschitz\<close>.\<close>

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

section \<open>\<open>F\<close> only sees the symmetric part of \<open>M\<close>\<close>

text \<open>Every feasible \<open>a\<close> is symmetric, and against a symmetric \<open>a\<close> the trace
  pairing cannot distinguish \<open>M\<close> from \<open>transpose M\<close>.  So \<open>F(p, M)\<close> depends
  only on \<open>sym M = \<onehalf>(M + M\<^sup>\<top>)\<close>, letting nearby non-symmetric matrices be
  handled by results assuming symmetry.\<close>

text \<open>Consequently Eq. (3.5) holds for an arbitrary \<open>M\<close>, symmetric or not,
  with \<open>M\<close> replaced by its symmetric part on the right hand side.\<close>

section \<open>The norm of an outer product, and \<open>rank1proj\<close> as a unit outer product\<close>

text \<open>Towards continuity of \<open>(p, M) \<mapsto> M\<^sub>p\<close> off \<open>p = 0\<close>.  The correction
  coefficient \<open>min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close> does not depend on \<open>p\<close>, so the only
  \<open>p\<close>-dependence is through \<open>rank1proj p\<close>, reducing to an estimate on
  \<open>norm (rank1proj p' - rank1proj p)\<close>.\<close>

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

lemma rank1proj_eq_outer_unit:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "rank1proj p = outer_prod (p /\<^sub>R norm p) (p /\<^sub>R norm p)"
proof -
  have np: "norm p \<noteq> 0"
    using p by simp
  have pp: "p \<bullet> p = norm p * norm p"
    by (simp add: dot_square_norm power2_eq_square)
  have "outer_prod (inverse (norm p) *\<^sub>R p) (inverse (norm p) *\<^sub>R p)
      = (inverse (norm p) * inverse (norm p)) *\<^sub>R outer_prod p p"
    by (simp add: outer_prod_scaleR_left outer_prod_scaleR_right)
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R outer_prod p p"
    unfolding pp using np by (simp add: field_simps)
  finally show ?thesis
    unfolding rank1proj_def by simp
qed

section \<open>\<open>rank1proj\<close> is Lipschitz away from the origin\<close>

text \<open>Since \<open>rank1proj p = outer_prod q q\<close> with \<open>q = p/|p|\<close> a unit vector,
  and \<open>outer_prod\<close> is bilinear, it suffices to bound the normalisation map,
  Lipschitz with constant \<open>2/|p|\<close> away from the origin, blowing up as
  \<open>p \<rightarrow> 0\<close>, why Eq. (3.6) differs there.\<close>

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

theorem norm_rank1proj_diff_le:
  fixes p p' :: "real^'n::finite"
  assumes p: "p \<noteq> 0" and p': "p' \<noteq> 0"
  shows "norm (rank1proj p' - rank1proj p) \<le> 4 * norm (p' - p) / norm p"
proof -
  define q where "q = p /\<^sub>R norm p"
  define q' where "q' = p' /\<^sub>R norm p'"
  have nq: "norm q = 1"
    unfolding q_def using p by simp
  have nq': "norm q' = 1"
    unfolding q'_def using p' by simp
  have r: "rank1proj p = outer_prod q q"
    unfolding q_def by (rule rank1proj_eq_outer_unit[OF p])
  have r': "rank1proj p' = outer_prod q' q'"
    unfolding q'_def by (rule rank1proj_eq_outer_unit[OF p'])
  have bil: "outer_prod q' q' - outer_prod q q
      = outer_prod (q' - q) q' + outer_prod q (q' - q)"
    by (simp add: outer_prod_diff_left outer_prod_diff_right)
  have "norm (rank1proj p' - rank1proj p)
      \<le> norm (outer_prod (q' - q) q') + norm (outer_prod q (q' - q))"
    unfolding r r' bil by (rule norm_triangle_ineq)
  also have "\<dots> = 2 * norm (q' - q)"
    by (simp add: norm_outer_prod nq nq')
  also have "\<dots> \<le> 2 * (2 * norm (p' - p) / norm p)"
    using norm_unit_diff_le[OF p p'] unfolding q_def q'_def by simp
  also have "\<dots> = 4 * norm (p' - p) / norm p"
    by simp
  finally show ?thesis .
qed

section \<open>The Frobenius norm: transpose invariance and submultiplicativity\<close>

text \<open>The last two tools for the continuity clause of Lemma 3.1:
  \<open>norm (A ** B) \<le> norm A * norm B\<close>, and that the Frobenius norm inherited
  on \<open>real^'n^'n\<close> satisfies it; neither is in this HOL-Analysis.\<close>

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

section \<open>The two constants: \<open>norm (rank1proj p)\<close> and \<open>norm (mat 1)\<close>\<close>

text \<open>The last numbers needed to turn the toolkit into an explicit Lipschitz
  constant for \<open>(p, M) \<mapsto> M\<^sub>p\<close>: a rank-one orthogonal projection has Frobenius
  norm \<open>1\<close>, and the identity has Frobenius norm \<open>\<surd>n\<close>.\<close>

lemma norm_rank1proj:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "norm (rank1proj p) = 1"
proof -
  have "norm (rank1proj p) = norm (p /\<^sub>R norm p) * norm (p /\<^sub>R norm p)"
    unfolding rank1proj_eq_outer_unit[OF p] by (rule norm_outer_prod)
  also have "\<dots> = 1"
    using p by simp
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

corollary norm_perp_proj_le:
  fixes p :: "real^'n::finite"
  assumes p: "p \<noteq> 0"
  shows "norm (mat 1 - rank1proj p :: real^'n^'n) \<le> sqrt (real CARD('n)) + 1"
proof -
  have "norm (mat 1 - rank1proj p :: real^'n^'n)
      \<le> norm (mat 1 :: real^'n^'n) + norm (rank1proj p)"
    by (rule norm_triangle_ineq4)
  also have "\<dots> = sqrt (real CARD('n)) + 1"
    by (simp add: norm_mat_1 norm_rank1proj[OF p])
  finally show ?thesis .
qed

section \<open>The conjugation expansion, and the Lipschitz bound for \<open>M\<^sub>p\<close>\<close>

text \<open>Perturbing the projection expands the conjugation into four terms.  With
  \<open>Q = I - rank1proj p\<close> and \<open>D = rank1proj p' - rank1proj p\<close>,
  \<open>I - rank1proj p' = Q - D\<close>, giving \<open>M\<^sub>p\<^sub>' - M\<^sub>p\<close> up to a correction
  \<open>c *\<^sub>R D\<close>, since \<open>c = min (\<lambda>\<^sub>(\<^sub>n\<^sub>)(M)) 0\<close> does not depend on \<open>p\<close>.\<close>

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
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by metis
  have finB: "finite B"
    by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)"
    by (rule onormal_span_card[OF B])
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
  \<open>1 \<le> eigval (n-k) a\<close>, Lipschitz on symmetric matrices.  Combined with
  boundedness (\<open>feasible_bounded\<close>, \<open>Viscosity_Solutions\<close>) this
  gives compactness of the constraint set.
\<close>

lemma continuous_on_matrix_entry:
  "continuous_on UNIV (\<lambda>a :: real^'n::finite^'n. a $ i $ j)"
  by (intro continuous_on_component continuous_on_id)

lemma continuous_on_quadform:
  fixes x :: "real^'n::finite"
  shows "continuous_on UNIV (\<lambda>a :: real^'n^'n. x \<bullet> (a *v x))"
proof -
  have eq: "x \<bullet> (a *v x) = (\<Sum>i\<in>UNIV. x $ i * (\<Sum>j\<in>UNIV. a $ i $ j * x $ j))"
    for a :: "real^'n^'n"
    unfolding inner_vec_def matrix_vector_mult_def by simp
  show ?thesis
    unfolding eq
    by (intro continuous_intros continuous_on_matrix_entry)
qed

lemma closed_symmetric_matrices:
  "closed {a :: real^'n::finite^'n. transpose a = a}"
proof -
  have eq: "{a :: real^'n^'n. transpose a = a}
      = (\<Inter>i. \<Inter>j. {a. a $ j $ i = a $ i $ j})"
    unfolding transpose_def vec_eq_iff by auto
  have "closed {a :: real^'n^'n. a $ j $ i = a $ i $ j}" for i j
    by (intro closed_Collect_eq continuous_on_matrix_entry)
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
