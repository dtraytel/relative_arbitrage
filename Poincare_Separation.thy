(*
  Title:   Poincare_Separation.thy
  Content: The eigenvalue comparison used in the proof of Lemma 3.1 of
           arXiv:2512.17702, namely the Poincare separation inequality

             lambda_(i)(M_p) >= lambda_(i+1)(M),   i = 1, ..., n-1,

           together with the Rayleigh bounds it rests on.

  The paper uses this in ONE direction only (the displayed inequality above),
  and only two consequences of it are actually needed:

  * for Eq. (3.5): the eigenvalue that M_p carries in the p-direction, namely
    min(lambda_(n)(M), 0), is the SMALLEST of the spectrum of M_p.  For that
    the weak form suffices -- every Rayleigh quotient of M is at least
    lambda_(n)(M) -- and no interlacing is required.
  * for Eq. (3.6): the limit p^m -> 0 along p^m = q_1/m, where the index shift
    in (3.6) comes from the full separation inequality.

  This theory is deliberately chained off Lemma_3_1 (rather than importing
  Eigenvalues in parallel with it) so that the import graph stays a single
  chain that PIDE can hold; see the header of Lemma_3_1.thy.
*)

theory Poincare_Separation
  imports Lemma_3_1
begin

section \<open>Elementary matrix algebra, continued\<close>

text \<open>The right-distributivity of \<open>**\<close> over subtraction and the additivity
  of \<open>trace\<close> over subtraction; neither is in this HOL-Analysis, and both are
  proved exactly like \<open>matrix_vector_mult_diff\<close> in Lemma_3_1.thy.\<close>

lemma matrix_matrix_mult_diff_right:
  fixes A B C :: "real^'n::finite^'n"
  shows "A ** (B - C) = A ** B - A ** C"
proof -
  have "(A ** (B - C)) $ i $ j = (A ** B - A ** C) $ i $ j" for i j
  proof -
    have "(A ** (B - C)) $ i $ j = (\<Sum>k\<in>UNIV. A $ i $ k * (B $ k $ j - C $ k $ j))"
      by (simp add: matrix_matrix_mult_def)
    also have "\<dots> = (\<Sum>k\<in>UNIV. A $ i $ k * B $ k $ j - A $ i $ k * C $ k $ j)"
      by (intro sum.cong refl) (simp add: right_diff_distrib)
    also have "\<dots> = (\<Sum>k\<in>UNIV. A $ i $ k * B $ k $ j)
                  - (\<Sum>k\<in>UNIV. A $ i $ k * C $ k $ j)"
      by (rule sum_subtractf)
    also have "\<dots> = (A ** B - A ** C) $ i $ j"
      by (simp add: matrix_matrix_mult_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma matrix_matrix_mult_diff_left:
  fixes A B C :: "real^'n::finite^'n"
  shows "(A - B) ** C = A ** C - B ** C"
proof -
  have "((A - B) ** C) $ i $ j = (A ** C - B ** C) $ i $ j" for i j
  proof -
    have "((A - B) ** C) $ i $ j = (\<Sum>k\<in>UNIV. (A $ i $ k - B $ i $ k) * C $ k $ j)"
      by (simp add: matrix_matrix_mult_def)
    also have "\<dots> = (\<Sum>k\<in>UNIV. A $ i $ k * C $ k $ j - B $ i $ k * C $ k $ j)"
      by (intro sum.cong refl) (simp add: left_diff_distrib)
    also have "\<dots> = (\<Sum>k\<in>UNIV. A $ i $ k * C $ k $ j)
                  - (\<Sum>k\<in>UNIV. B $ i $ k * C $ k $ j)"
      by (rule sum_subtractf)
    also have "\<dots> = (A ** C - B ** C) $ i $ j"
      by (simp add: matrix_matrix_mult_def)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp add: vec_eq_iff)
qed

lemma trace_diff_matrix:
  fixes A B :: "real^'n::finite^'n"
  shows "trace (A - B) = trace A - trace B"
  unfolding trace_def by (simp add: sum_subtractf)

section \<open>The full Ky Fan sum is the trace\<close>

text \<open>\<open>kyfan CARD('n)\<close> takes the whole spectrum, so it is the trace.  The
  proof evaluates \<open>kyfan\<close> on the eigenbasis itself: the threshold condition of
  \<open>kyfan_threshold\<close> is vacuous when the threshold set is all of \<open>B\<close>, and the
  resulting sum is the trace by the completeness relation.\<close>

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
    by (simp add: matrix_mul_rid)
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
      by (simp add: transpose_diff_matrix transpose_mat_one)
    have "(mat 1 - outer_prod x x) ** (mat 1 - outer_prod x x)
        = (mat 1 - outer_prod x x) ** mat 1
          - (mat 1 - outer_prod x x) ** outer_prod x x"
      by (rule matrix_matrix_mult_diff_right)
    also have "\<dots> = (mat 1 - outer_prod x x)
                  - (mat 1 ** outer_prod x x - outer_prod x x ** outer_prod x x)"
      by (simp add: matrix_mul_rid matrix_matrix_mult_diff_left)
    also have "\<dots> = (mat 1 - outer_prod x x :: real^'n^'n)"
      by (simp add: matrix_mul_lid sq)
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
    using pos by (simp add: of_nat_diff)
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
  \<open>kyfan_ge_trace_mult\<close>; the lower one is its mirror image, obtained by
  pairing \<open>a\<close> with the complementary projection and using that the full Ky Fan
  sum is the trace.  This is the weak form of Poincare separation that
  Eq. (3.5) needs.\<close>

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
      by (simp add: matrix_matrix_mult_diff_right trace_diff_matrix)
    also have "\<dots> = trace a - x \<bullet> (a *v x)"
      by (simp add: matrix_mul_rid trace_mult_rank1)
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

text \<open>On \<open>p\<^sup>\<bottom>\<close> the projection \<open>I - pp'/|p|\<^sup>2\<close> acts as the identity and the
  correction term vanishes, so \<open>M\<^sub>p\<close> has exactly the Rayleigh quotients of
  \<open>M\<close> there.  Combined with the Rayleigh bound above, this is precisely the
  statement that the eigenvalue \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0)\<close> that \<open>M\<^sub>p\<close> carries in the
  \<open>p\<close>-direction sorts to the BOTTOM of the spectrum of \<open>M\<^sub>p\<close> -- the sentence
  after Eq. (3.4) that makes Eq. (3.5) a clean sum over \<open>i = 1, \<dots>, n\<close>.\<close>

lemma rank1proj_annihilates_perp:
  fixes p :: "real^'n::finite"
  assumes y: "p \<bullet> y = 0"
  shows "rank1proj p *v y = 0"
proof -
  have "rank1proj p *v y = inverse (p \<bullet> p) *\<^sub>R (outer_prod p p *v y)"
    unfolding rank1proj_def by (rule scaleR_matrix_vector_assoc[symmetric])
  also have "\<dots> = inverse (p \<bullet> p) *\<^sub>R ((p \<bullet> y) *\<^sub>R p)"
    by (simp add: outer_prod_mv)
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
  eigenbasis of \<open>M\<^sub>p\<close>; adjoining the unit vector \<open>p/|p|\<close>, which is itself an
  eigenvector by \<open>Mp_apply_p\<close>, gives an eigenbasis of the whole space in which
  the \<open>p\<close>-direction is one distinguished element and all the others lie in
  \<open>p\<^sup>\<bottom>\<close>.  This is the basis in which Eq. (3.5) is read off.\<close>

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

text \<open>Towards step (A) of the linear program of Eq. (3.5) (see the closing
  note): the trace of a matrix written in an orthonormal basis as a weighted
  sum of outer products is just the sum of the weights, and each basis vector
  reads off its own weight as a Rayleigh quotient.  These are the two facts the
  clipped matrix \<open>c = \<Sum>\<^sub>j min \<mu>\<^sub>j 1 *\<^sub>R v\<^sub>j v\<^sub>j'\<close> is used through.\<close>

lemma trace_sum_matrix:
  fixes f :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes "finite S"
  shows "trace (\<Sum>u\<in>S. f u) = (\<Sum>u\<in>S. trace (f u))"
  using assms by (induct S) (simp_all add: trace_def sum.distrib)

lemma trace_weighted_outer_sum:
  fixes g :: "real^'n::finite \<Rightarrow> real"
  assumes B: "onormal B"
  shows "trace (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) = (\<Sum>v\<in>B. g v)"
proof -
  have finB: "finite B"
    by (rule onormal_finite[OF B])
  have "trace (\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v)
      = (\<Sum>v\<in>B. trace (g v *\<^sub>R outer_prod v v))"
    by (rule trace_sum_matrix[OF finB])
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
      (use B u in \<open>auto dest: onormal_inner_distinct simp: onormal_inner_self\<close>)
  also have "\<dots> = g u *\<^sub>R u"
    using finB u by simp
  finally have "(\<Sum>v\<in>B. g v *\<^sub>R outer_prod v v) *v u = g u *\<^sub>R u" .
  then show ?thesis
    by (simp add: uu)
qed

text \<open>Nonnegative weights give a nonnegative quadratic form.  This is what
  makes both \<open>a - c\<close> and \<open>I - c\<close> positive semidefinite for the clipped matrix
  \<open>c\<close>, since their weights are \<open>max (\<mu>\<^sub>j - 1) 0\<close> and \<open>1 - min \<mu>\<^sub>j 1\<close>
  respectively; that is how step (A) gets \<open>u \<bullet> (c *v u) \<le> min (w u) 1\<close> for
  basis vectors \<open>u\<close> of the OTHER basis.\<close>

text \<open>The expansion identity behind all of this: against a weighted sum of
  outer products the quadratic form is the weighted sum of squared
  coefficients.  No orthonormality is needed.  This is also the identity
  step (5) of the Courant-Fischer bound uses to dominate \<open>x \<bullet> (a *v x)\<close> by the
  largest weight occurring in the sum.\<close>

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

text \<open>Every eigenvalue OUTSIDE a threshold set of size \<open>m\<close> is dominated by
  \<open>eigval m a\<close>.  This is the link step (6) of the Courant-Fischer argument needs,
  and in exactly the pointwise form step (5) uses: \<open>eigval m a\<close> is the minimum
  over the threshold set, and the threshold property puts everything outside
  below that minimum.\<close>

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
  subspaces whose dimensions together exceed the ambient dimension must meet in
  a nonzero vector.  In step (4) this is applied to the subspace \<open>S\<close> supplied by
  \<open>eigen_lb a m\<close> (of dimension \<open>\<ge> m\<close>) and to \<open>span (B - T')\<close> (of dimension
  \<open>CARD('n) - m + 1\<close>), whose dimensions sum to at least \<open>CARD('n) + 1\<close>.\<close>

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
      by (simp add: dim_eq_0)
    with pos show False
      by simp
  qed
  then show ?thesis
    by blast
qed

text \<open>Parseval's identity for a full orthonormal basis is the special case
  \<open>g = 1\<close> of the expansion, via the completeness relation.  Together with the
  expansion it gives the bound step (5) of the Courant-Fischer argument needs:
  \<open>x \<bullet> (a *v x) = (\<Sum>v. \<lambda>\<^sub>v * (v \<bullet> x)\<^sup>2) \<le> \<lambda>\<^sub>m\<^sub>a\<^sub>x * (\<Sum>v. (v \<bullet> x)\<^sup>2) = \<lambda>\<^sub>m\<^sub>a\<^sub>x * (x \<bullet> x)\<close>.\<close>

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
  containing it.  This is the remaining elementary ingredient of step (5): it
  kills the \<open>v \<in> T'\<close> terms of the expansion, leaving only eigenvalues that
  \<open>eigval m a\<close> dominates.\<close>

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

text \<open>Comparison of two matrices written in the SAME orthonormal basis: larger
  weights give a larger quadratic form.  Both halves of step (A) are instances:
  taking \<open>f = \<mu>\<close> and \<open>g = (\<lambda>v. min (\<mu> v) 1)\<close> gives \<open>x \<bullet> (c *v x) \<le> x \<bullet> (a *v x)\<close>
  (using \<open>spectral_decomposition\<close> for \<open>a\<close>), and taking \<open>f = (\<lambda>_. 1)\<close> gives
  \<open>x \<bullet> (c *v x) \<le> x \<bullet> x\<close> (using \<open>onormal_complete\<close> for \<open>mat 1\<close>).\<close>

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

text \<open>\<open>eigen_lb a m\<close> forces \<open>eigval m a \<ge> 1\<close>.  Note the off-by-one: the
  comparison subspace must be \<open>span (insert w (B - T))\<close> where \<open>T\<close> is a top-\<open>m\<close>
  threshold set and \<open>w\<close> its minimum, giving dimension \<open>CARD('n) - m + 1\<close>, so
  that the dimensions sum to \<open>CARD('n) + 1\<close> and the intersection is nontrivial.
  Every eigenvalue occurring in that subspace is \<open>\<le> eigval m a\<close>: those outside
  \<open>T\<close> by \<open>quadform_outside_threshold_le_eigval\<close>, and \<open>w\<close> itself with equality.\<close>

lemma onormal_subset:
  assumes "onormal B" and "U \<subseteq> B"
  shows "onormal U"
  using assms by (auto simp: onormal_def pairwise_def elim: finite_subset)

theorem eigval_ge_of_eigen_lb:
  fixes a :: "real^'n::finite^'n"
  assumes sym: "transpose a = a" and lb: "eigen_lb a m"
    and m: "0 < m" "m \<le> CARD('n)"
  shows "1 \<le> eigval m a"
proof -
  obtain S where S: "subspace S" "m \<le> dim S"
    and quad: "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (a *v x)"
    using lb by (auto simp: eigen_lb_def)
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
    using x(3) by (simp add: inner_gt_zero_iff)
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
  text \<open>Bind the eigenvalues to a local constant BEFORE decomposing: the right
    hand side of \<open>spectral_decomposition\<close> mentions \<open>a\<close> again, so using it as a
    rewrite rule directly loops (\<open>Interrupt_Breakdown\<close>).\<close>
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
  have "1 * (x \<bullet> x) \<le> x \<bullet> (a *v x)"
    using quad[OF x(1)] by simp
  with upper have "1 * (x \<bullet> x) \<le> eigval m a * (x \<bullet> x)"
    by simp
  then show ?thesis
    using xx by (simp add: mult_right_le_imp_le)
qed

section \<open>Step (A) of the linear program: the clipped trace bound\<close>

text \<open>With the Courant-Fischer bound in hand, the clipped weights sum to at
  least \<open>m\<close> over an eigenbasis of \<open>a\<close>: the top-\<open>m\<close> threshold set consists of
  eigenvalues \<open>\<ge> eigval m a \<ge> 1\<close>, each contributing exactly \<open>1\<close> after clipping,
  and the remaining ones contribute \<open>\<ge> 0\<close> because \<open>a\<close> is positive
  semidefinite.\<close>

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

text \<open>Step (A) itself: the bound transfers from an eigenbasis of \<open>a\<close> to an
  ARBITRARY orthonormal basis, which is what Eq. (3.5) needs since there the
  basis is the adapted eigenbasis of \<open>M\<^sub>p\<close>, not of \<open>a\<close>.  The transfer goes
  through the clipped matrix \<open>c\<close>: it is dominated by both \<open>a\<close> and the identity,
  so its Rayleigh quotients are below the clipped weights, while its trace is
  basis-independent.\<close>

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

section \<open>Step (B) of the linear program: the box program\<close>

text \<open>The combinatorial heart of Eq. (3.5), stated without matrices.  Splitting
  \<open>lam u = max (lam u) 0 + min (lam u) 0\<close>, the positive part is bounded using
  \<open>t \<le> 1\<close> and the negative part by \<open>sum_weighted_le_top_subset\<close>, whose
  "top subset" for \<open>min (lam u) 0\<close> is precisely the set of \<open>m\<close> LEAST negative
  directions -- the ones the optimum is forced onto.  The two bounds add up to
  \<open>possum CARD('n) + (kyfan m - possum m)\<close> once read back through
  \<open>possum_eq_sum_pos\<close> and \<open>kyfan_minus_possum\<close>.\<close>

lemma box_program_bound_exact:
  fixes lam t :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m: "m \<le> card B"
    and t0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> t u" and t1: "\<And>u. u \<in> B \<Longrightarrow> t u \<le> 1"
    and tsum: "(\<Sum>u\<in>B. t u) = real m"
  shows "\<exists>T. T \<subseteq> B \<and> card T = m
      \<and> (\<Sum>u\<in>B. lam u * t u)
          \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)"
proof -
  obtain T where T: "T \<subseteq> B" "card T = m"
    and neg: "(\<Sum>u\<in>B. min (lam u) 0 * t u) \<le> (\<Sum>u\<in>T. min (lam u) 0)"
    using sum_weighted_le_top_subset[where f = "\<lambda>u. min (lam u) 0" and t = t,
        OF finB m t0 t1 tsum] by metis
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
    using pos neg by (rule add_mono)
  finally have le: "(\<Sum>u\<in>B. lam u * t u)
      \<le> (\<Sum>u\<in>B. max (lam u) 0) + (\<Sum>u\<in>T. min (lam u) 0)" .
  show ?thesis
    by (rule exI[of _ T]) (intro conjI T(1) T(2) le)
qed

text \<open>\<open>sum_weighted_le_top_subset\<close> needs the weights to sum to \<open>m\<close> EXACTLY,
  while step (A) only delivers \<open>\<ge> m\<close>.  Scaling the weights down by
  \<open>real m / (\<Sum>t)\<close> repairs that: the scaled weights are pointwise below the
  originals, which is all the negative part of the objective needs, since
  \<open>min (lam u) 0 \<le> 0\<close> means shrinking a weight can only INCREASE that
  contribution.\<close>

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

text \<open>The box program in the form step (A) actually delivers, with
  \<open>(\<Sum>t) \<ge> real m\<close> rather than equality.  The positive part is bounded using
  \<open>t \<le> 1\<close> directly; the negative part is first pushed onto the scaled-down
  weights (which only increases it, the coefficients being nonpositive) and
  then handed to \<open>sum_weighted_le_top_subset\<close>.\<close>

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

text \<open>Assembling the two halves: the upper bound of Eq. (3.5), in the abstract
  form the eigenbasis expansion delivers it.  Writing \<open>w = t + s\<close> with
  \<open>t u = min (w u) 1 \<in> [0,1]\<close> and \<open>s u = max (w u - 1) 0 \<in> [0, L-1]\<close>, the
  \<open>t\<close>-part is the box program and the \<open>s\<close>-part contributes at most
  \<open>(L-1) * (\<Sum> max (lam u) 0)\<close>.  The total is
  \<open>L * (\<Sum> max (lam u) 0) + (\<Sum>\<^sub>T min (lam u) 0)\<close>, which is the bracket of
  Eq. (3.5).\<close>

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

text \<open>The subtlety flagged for the conversion to \<open>bracket\<close> form: the box
  program returns an ARBITRARY size-\<open>m\<close> set \<open>T\<close>, whereas \<open>kyfan m - possum m\<close> is
  the sum over a THRESHOLD set.  The inequality does go the right way, because
  \<open>min (\<cdot>) 0\<close> is monotone: a threshold set for \<open>lam\<close> is therefore also a
  threshold set for \<open>\<lambda>u. min (lam u) 0\<close>, and \<open>threshold_sum_maximal\<close> says a
  threshold set maximises the sum among all subsets of its size.\<close>

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

text \<open>Everything above assembled: for a symmetric \<open>N\<close> with eigenbasis \<open>B\<close>, and
  weights coming from any \<open>a\<close> satisfying the feasible-set constraints, the
  objective is bounded by \<open>bracket m L N\<close>.  The two conversions are
  \<open>possum_full_eq_sum_basis\<close> (for the positive part) and
  \<open>kyfan_minus_possum_threshold\<close> (for the negative part, over a threshold set,
  which \<open>sum_min_le_threshold\<close> lets us pass to).\<close>

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

text \<open>The paper justifies Eq. (3.5) in one sentence: "Observing that
  \<open>tr(Ma) = tr(M\<^sub>p a)\<close> for all \<open>a \<succeq> 0\<close> with \<open>ap = 0\<close> in the definition (3.1) of
  \<open>F\<close>, and writing the symmetric \<open>M\<^sub>p\<close> as a linear combination of outer
  products, we see that ...".  Both halves are now available: \<open>trace_Mp\<close>
  (Lemma_3_1.thy) is the first observation, and the second is the expansion of
  \<open>M\<^sub>p\<close> against the adapted eigenbasis.  This section carries out that step and
  records the three constraints the feasible set puts on the resulting
  weights, which is what turns the expansion into (3.5).\<close>

lemma feasible_quadform_nonneg:
  fixes a :: "real^'n::finite^'n"
  assumes "a \<in> feasible k L p"
  shows "0 \<le> u \<bullet> (a *v u)"
  using assms by (simp add: feasible_def psd_def)

lemma feasible_quadform_le:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> feasible k L p" and u: "norm u = 1"
  shows "u \<bullet> (a *v u) \<le> L"
proof -
  have "u \<bullet> (a *v u) \<le> L * (u \<bullet> u)"
    using a by (simp add: feasible_def eigen_ub_def)
  also have "\<dots> = L"
    using u by (simp add: dot_square_norm)
  finally show ?thesis .
qed

lemma feasible_annihilates_unit:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> feasible k L p"
  shows "a *v (p /\<^sub>R norm p) = 0"
proof -
  have ap: "a *v p = 0"
    using a by (simp add: feasible_def)
  have "a *v (inverse (norm p) *\<^sub>R p) = inverse (norm p) *\<^sub>R (a *v p)"
    by (simp add: matrix_scaleR_vector_ac scaleR_matrix_vector_assoc)
  also have "\<dots> = 0"
    by (simp add: ap)
  finally show ?thesis .
qed

theorem trace_expand_adapted:
  fixes M a :: "real^'n::finite^'n"
  assumes sym: "transpose M = M" and p: "p \<noteq> 0"
    and af: "a \<in> feasible k L p"
  shows "\<exists>B. onormal B \<and> span B = UNIV \<and> p /\<^sub>R norm p \<in> B
      \<and> (\<forall>u \<in> B - {p /\<^sub>R norm p}. p \<bullet> u = 0)
      \<and> trace (M ** a) = (\<Sum>u\<in>B. (u \<bullet> (Mp p M *v u)) * (u \<bullet> (a *v u)))
      \<and> (\<forall>u\<in>B. 0 \<le> u \<bullet> (a *v u) \<and> u \<bullet> (a *v u) \<le> L)
      \<and> (p /\<^sub>R norm p) \<bullet> (a *v (p /\<^sub>R norm p)) = 0
      \<and> (\<forall>u \<in> B - {p /\<^sub>R norm p}.
            min (eigval CARD('n) M) 0 \<le> u \<bullet> (Mp p M *v u))"
proof -
  define q where "q = p /\<^sub>R norm p"
  have symMp: "transpose (Mp p M) = Mp p M"
    by (rule transpose_Mp[OF sym])
  have syma: "transpose a = a"
    using af by (simp add: feasible_def psd_def)
  have ap: "a *v p = 0"
    using af by (simp add: feasible_def)
  obtain B where B: "onormal B" "span B = UNIV"
    and eigB: "\<forall>u\<in>B. Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u"
    and qB: "q \<in> B" and restperp: "\<forall>u \<in> B - {q}. p \<bullet> u = 0"
    using Mp_eigenbasis_adapted[OF sym p] unfolding q_def by blast
  have eigB': "Mp p M *v u = (u \<bullet> (Mp p M *v u)) *\<^sub>R u" if "u \<in> B" for u
    using eigB that by blast
  text \<open>The expansion: the paper's "writing the symmetric \<open>M\<^sub>p\<close> as a linear
    combination of outer products".\<close>
  have expand: "trace (M ** a) = (\<Sum>u\<in>B. (u \<bullet> (Mp p M *v u)) * (u \<bullet> (a *v u)))"
  proof -
    have "trace (M ** a) = trace (Mp p M ** a)"
      by (rule trace_Mp[OF syma ap, symmetric])
    also have "\<dots> = (\<Sum>u\<in>B. (u \<bullet> (Mp p M *v u)) * (u \<bullet> (a *v u)))"
      by (rule trace_mult_eigen_weights[OF B symMp eigB'])
    finally show ?thesis .
  qed
  have wbounds: "\<forall>u\<in>B. 0 \<le> u \<bullet> (a *v u) \<and> u \<bullet> (a *v u) \<le> L"
  proof (intro ballI conjI)
    fix u assume u: "u \<in> B"
    show "0 \<le> u \<bullet> (a *v u)"
      by (rule feasible_quadform_nonneg[OF af])
    have "norm u = 1"
      using u B(1) by (simp add: onormal_def)
    then show "u \<bullet> (a *v u) \<le> L"
      by (rule feasible_quadform_le[OF af])
  qed
  have wq: "q \<bullet> (a *v q) = 0"
    unfolding q_def by (simp add: feasible_annihilates_unit[OF af])
  have minperp: "\<forall>u \<in> B - {q}. min (eigval CARD('n) M) 0 \<le> u \<bullet> (Mp p M *v u)"
  proof (intro ballI)
    fix u assume u: "u \<in> B - {q}"
    then have nu: "norm u = 1"
      using B(1) by (simp add: onormal_def)
    have pu: "p \<bullet> u = 0"
      using u restperp by blast
    show "min (eigval CARD('n) M) 0 \<le> u \<bullet> (Mp p M *v u)"
      by (rule Mp_perp_quadform_ge[OF sym p pu nu])
  qed
  show ?thesis
    unfolding q_def[symmetric]
    by (rule exI[of _ B])
      (intro conjI B(1) B(2) qB restperp expand wbounds wq minperp)
qed

section \<open>What remains for Eq. (3.5)\<close>

text \<open>Everything above is the SPECTRAL half of Eq. (3.5).  What remains is the
  linear program itself, and the entry point is already available:

  \<^item> \<open>trace_mult_eigen_weights\<close> (Eigenvalues.thy) expands, for the adapted
    eigenbasis \<open>B\<close> of \<open>N = M\<^sub>p\<close> produced by \<open>Mp_eigenbasis_adapted\<close>,
    \<open>trace (N ** a) = (\<Sum>u\<in>B. (u \<bullet> (N *v u)) * (u \<bullet> (a *v u)))\<close>,
    so with \<open>w u = u \<bullet> (a *v u)\<close> the objective is \<open>\<Sum>u\<in>B. \<lambda>\<^sub>u * w u\<close>.
  \<^item> For \<open>a \<in> feasible k L p\<close> the weights satisfy \<open>0 \<le> w u\<close> (\<open>psd a\<close>),
    \<open>w u \<le> L\<close> (\<open>eigen_ub a L\<close> with \<open>norm u = 1\<close>), and \<open>w q = 0\<close> for the
    distinguished \<open>q = p/|p| \<in> B\<close>, because \<open>a *v p = 0\<close>.
  \<^item> The upper bound \<open>\<Sum>u\<in>B. \<lambda>\<^sub>u * w u \<le> bracket (CARD('n) - k) L N\<close> is then the
    statement that the optimum puts weight \<open>L\<close> on the positive eigendirections
    and weight \<open>1\<close> on just enough of the least-negative ones to satisfy
    \<open>eigen_lb a (CARD('n) - k)\<close>; \<open>sum_weighted_le_top_subset\<close> (Eigenvalues.thy)
    is the combinatorial core, and \<open>kyfan_ge_of_eigen_lb\<close> /
    \<open>kyfan_le_of_eigen_ub\<close> convert the two spectral constraints on \<open>a\<close> into
    Ky Fan inequalities.
  \<^item> The matching lower bound needs a feasible \<open>a\<close> attaining it, built as
    \<open>L *\<^sub>R (\<Sum> over the positive eigendirections) + (\<Sum> over the forced ones)\<close>;
    \<open>Lemma_2_1_Exact.thy\<close> already constructs such sums of outer products and
    verifies \<open>eigen_lb\<close>/\<open>eigen_ub\<close> for them.

  The step the paper does NOT supply (it compresses Eq. (3.5) into "we see
  that", and no earlier result in Sections 1-2 discharges it) is the value of
  the linear program.  With \<open>\<lambda>\<^sub>u = u \<bullet> (M\<^sub>p *v u)\<close> and \<open>w\<^sub>u = u \<bullet> (a *v u)\<close> as
  produced by \<open>trace_expand_adapted\<close>, it splits into two independent halves:

  \<^item> (A) \<open>(\<Sum>u\<in>B. min (w u) 1) \<ge> real (CARD('n) - k)\<close>.  Route: let
    \<open>a = (\<Sum>j. \<mu>\<^sub>j *\<^sub>R outer_prod v\<^sub>j v\<^sub>j)\<close> be a spectral decomposition of \<open>a\<close> and
    put \<open>c = (\<Sum>j. min \<mu>\<^sub>j 1 *\<^sub>R outer_prod v\<^sub>j v\<^sub>j)\<close>.  Then \<open>c \<preceq> a\<close> and \<open>c \<preceq> I\<close>,
    so \<open>u \<bullet> (c *v u) \<le> min (w u) 1\<close> for every \<open>u\<close>, whence
    \<open>(\<Sum>u\<in>B. min (w u) 1) \<ge> (\<Sum>u\<in>B. u \<bullet> (c *v u)) = trace c\<close> by
    \<open>trace_onormal_basis\<close>; and \<open>trace c = (\<Sum>j. min \<mu>\<^sub>j 1) \<ge> CARD('n) - k\<close>
    because \<open>eigen_lb a (CARD('n) - k)\<close> forces at least \<open>CARD('n) - k\<close> of the
    \<open>\<mu>\<^sub>j\<close> to be \<open>\<ge> 1\<close>.

    WARNING on that last implication: it is NOT \<open>kyfan_ge_of_eigen_lb\<close>, which
    only gives \<open>real m \<le> kyfan m a\<close> and is too weak.  For \<open>m = 2\<close> with
    eigenvalues \<open>(10, 0, \<dots>)\<close> one has \<open>kyfan 2 a = 10 \<ge> 2\<close> while
    \<open>(\<Sum>\<^sub>j min \<mu>\<^sub>j 1) = 1 < 2\<close>.  What is needed is \<open>eigval m a \<ge> 1\<close>, which by
    \<open>eigval_antimono\<close> makes \<open>\<mu>\<^sub>(\<^sub>1\<^sub>), \<dots>, \<mu>\<^sub>(\<^sub>m\<^sub>)\<close> all \<open>\<ge> 1\<close>.  Deriving
    \<open>eigval m a \<ge> 1\<close> from \<open>eigen_lb a m\<close> needs the Courant-Fischer min-max
    LOWER bound: contrary to an earlier judgement in this development, that one
    piece of Courant-Fischer really is required here, even though none of the
    \<open>kyfan\<close>/\<open>possum\<close> theory needs it.
  \<^item> (B) the box program: for \<open>t \<in> [0,1]\<close> pointwise with
    \<open>(\<Sum>u\<in>B. t u) \<ge> real m\<close>,
    \<open>(\<Sum>u\<in>B. \<lambda>\<^sub>u * t u) \<le> possum CARD('n) M\<^sub>p + (kyfan m M\<^sub>p - possum m M\<^sub>p)\<close>,
    with equality when \<open>t = 1\<close> on the positive eigendirections and on just
    enough of the least-negative remaining ones.  \<open>sum_weighted_le_top_subset\<close>
    is the combinatorial core.

  Given (A) and (B), Eq. (3.5) follows by writing \<open>w\<^sub>u = t\<^sub>u + s\<^sub>u\<close> with
  \<open>t\<^sub>u = min (w\<^sub>u) 1\<close> and \<open>s\<^sub>u = max (w\<^sub>u - 1) 0 \<in> [0, L-1]\<close>: the \<open>s\<close>-part
  contributes at most \<open>(L-1) * possum CARD('n) M\<^sub>p\<close> and the \<open>t\<close>-part is (B).
  NOTE this is a proof PLAN for the compressed step, not an additional
  mathematical claim of the paper.

  The results proved here are exactly what makes the FULL spectrum of \<open>M\<^sub>p\<close> the
  right index set in Eq. (3.5): \<open>Mp_apply_p\<close> identifies the \<open>p\<close>-direction
  eigenvalue as \<open>min(\<lambda>\<^sub>(\<^sub>n\<^sub>)(M), 0) \<le> 0\<close>, so it contributes nothing to
  \<open>possum CARD('n)\<close>, and \<open>Mp_perp_quadform_ge\<close> shows it is minimal, so for
  \<open>k \<ge> 1\<close> it is excluded from \<open>kyfan (CARD('n) - k)\<close> -- which is precisely the
  role the paper's Poincare separation plays.\<close>

end
