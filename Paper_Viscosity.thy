(*
  Title:   Paper_Viscosity.thy
  Content: Towards clause (2) of Theorem 1.1 of arXiv:2512.17702 --- the two
           viscosity inequalities for `paper_v`.  PLAN section 2.1.

  Two facts shape everything here.

  (a) The operator of Eq. (1.9) is an INFIMUM,

        ell_op k L p M = Inf ((\<lambda>a. - trace (M ** a) / 2) ` feasible k L p),

      so a subsolution inequality needs only ONE witness, while a
      supersolution inequality needs the whole family.

  (b) The two halves of the DPP are not interchangeable.  The `<=` half is an
      ALMOST SURE bound, and a.s. bounds survive integration; the `>=` half
      bounds an essential infimum from below, which no mean can do.  So the
      SUBSOLUTION half is the one an expectation argument reaches.

  The class of (1.7) is a martingale-problem class, not an SDE class, so Ito's
  formula is unavailable.  For QUADRATIC test functions it is also unnecessary:
  z . (M *v z) = trace (M ** outerp z) is a linear functional of the
  compensated clause, so the expansion is exact and elementary.  That is
  paper_pair_class_quadratic_mean, and paper_v_subsol_quadratic_global is the
  subsolution inequality it yields, for the relaxed operator ell_op_s and a
  globally touching quadratic.

  The final section states precisely what separates that from visc_subsol,
  including two localisation routes that were checked and provably do not work.
*)

theory Paper_Viscosity
  imports Paper_DPP Relative_Arbitrage_PDE Envelopes
begin

section \<open>One witness suffices for the subsolution inequality\<close>

text \<open>\<^const>\<open>ell_op\<close> is an infimum over the feasible set, and
  @{thm [source] ell_op_bdd_below} says that infimum is over a set bounded
  below.  So a single feasible matrix beating the threshold settles the
  inequality --- there is no need to control the whole family.\<close>

lemma ell_op_le_of_witness:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p" and le: "- trace (M ** a) / 2 \<le> c"
  shows "ell_op k L p M \<le> c"
proof -
  have mem: "- trace (M ** a) / 2 \<in> (\<lambda>a. - trace (M ** a) / 2) ` feasible k L p"
    using a by blast
  have "ell_op k L p M \<le> - trace (M ** a) / 2"
    unfolding ell_op_def by (rule cInf_lower[OF mem ell_op_bdd_below])
  also have "\<dots> \<le> c" by (rule le)
  finally show ?thesis .
qed

corollary ell_op_le_one_of_witness:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p" and le: "- trace (M ** a) / 2 \<le> 1"
  shows "ell_op k L p M \<le> 1"
  by (rule ell_op_le_of_witness[OF a le])

section \<open>The DPP at the exit time of a ball\<close>

text \<open>The \<open>\<le>\<close> half of the DPP, @{thm [source] paper_v_cond_time}, asks of its
  random time only that it lie in \<open>[0,T]\<close> --- NOT that it be a
  \<^const>\<open>path_stopping_time\<close>.  That is what lets the SUBSOLUTION argument use
  the exit time of a ball directly.

  (The supersolution half is not so lucky: it consumes
  @{thm [source] paper_v_dpp_sup_ge_time}, whose \<open>\<theta>\<close> must be a path stopping
  time, and the exit time of a ball is one only for CONTINUOUS paths, while
  \<^const>\<open>path_stopping_time\<close> quantifies over all functions.  The fix is to
  restrict the congruence clause to the path space; that is a separate,
  small piece of work and it is recorded here so it is not rediscovered.)

  Combining with @{thm [source] enn2real_paper_v_horizon_cap} puts the
  conclusion in a form with NO varying horizon left: the value at the reduced
  horizon is the value at \<open>T\<close>, capped.\<close>

definition pball_exit :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  where "pball_exit T x \<epsilon> \<omega> = pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"

lemma pball_exit_nonneg:
  assumes T0: "0 \<le> T" shows "0 \<le> pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def by (rule pexit_nonneg[OF T0])

lemma pball_exit_le:
  assumes T0: "0 \<le> T" shows "pball_exit T x \<epsilon> \<omega> \<le> T"
  unfolding pball_exit_def by (rule pexit_le_T[OF T0])

theorem paper_v_cond_ball:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x y :: "real^'n"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> paper_pair_class k L T y"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  shows "AE \<omega> in P. c \<le> pball_exit T x \<epsilon> \<omega>
      + min (enn2real (paper_v k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
            (T - pball_exit T x \<epsilon> \<omega>)"
proof -
  have th0: "0 \<le> pball_exit T x \<epsilon> \<omega>" for \<omega> :: "'n pairpath"
    by (rule pball_exit_nonneg[OF T0])
  have thT: "pball_exit T x \<epsilon> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule pball_exit_le[OF T0])
  have "AE \<omega> in P. c \<le> pball_exit T x \<epsilon> \<omega>
      + enn2real (paper_v k L (T - pball_exit T x \<epsilon> \<omega>) K
          (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))"
    by (rule paper_v_cond_time[OF T0 L1 Kc P c th0 thT])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "c \<le> pball_exit T x \<epsilon> \<omega>
        + enn2real (paper_v k L (T - pball_exit T x \<epsilon> \<omega>) K
            (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))"
    have a: "0 \<le> T - pball_exit T x \<epsilon> \<omega>" using thT[of \<omega>] by simp
    have b: "T - pball_exit T x \<epsilon> \<omega> \<le> T" using th0[of \<omega>] by simp
    have "enn2real (paper_v k L (T - pball_exit T x \<epsilon> \<omega>) K
          (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))))
        = min (enn2real (paper_v k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
              (T - pball_exit T x \<epsilon> \<omega>)"
      by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with h show "c \<le> pball_exit T x \<epsilon> \<omega>
        + min (enn2real (paper_v k L T K (fst (\<omega> (pball_exit T x \<epsilon> \<omega>)))))
              (T - pball_exit T x \<epsilon> \<omega>)" by simp
  qed
qed

section \<open>Ito for quadratic test functions, from the martingale clauses\<close>

text \<open>The class of (1.7) is defined by MARTINGALE properties, not by an SDE,
  so Ito's formula is not available and cannot be cheaply built.  But for a
  QUADRATIC test function the expansion is EXACT and needs no stochastic
  integration at all:

    \<open>\<phi> z = c + p \<bullet> z + (z \<bullet> (M *v z))/2\<close>,

  and \<open>z \<bullet> (M *v z) = trace (M ** outerp z)\<close>, so the second-order term is a
  LINEAR functional of the compensated clause (iv) of (1.7).  Its mean is
  therefore pinned by that clause alone, and the first-order term by the
  martingale clause (iii).  What comes out is

    \<open>E[\<phi>(X\<^sub>t)] - \<phi>(x) = (t/2) \<sqdot> trace (M ** b)\<close>,  \<open>b \<in> sconstraint k L\<close>,

  which is exactly the shape the viscosity argument consumes, with \<open>b\<close> the
  averaged covariation direction.  The whole section is elementary.\<close>

subsection \<open>Matrix functionals that are bounded linear\<close>

lemma outerp_eq_outer_prod:
  fixes v :: "real^'n::finite"
  shows "outerp v = outer_prod v v"
  by (simp add: outerp_def outer_prod_def)

lemma trace_mult_outerp:
  fixes M :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (M ** outerp v) = v \<bullet> (M *v v)"
  by (simp add: outerp_eq_outer_prod mult_outer_prod inner_commute)

lemma trace_mult_sum:
  fixes M a :: "real^'n::finite^'n"
  shows "trace (M ** a) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * a $ j $ i)"
  by (simp add: trace_def matrix_matrix_mult_def)

lemma bounded_linear_trace_mult_left:
  fixes M :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>a :: real^'n^'n. trace (M ** a))"
  unfolding linear_conv_bounded_linear[symmetric]
proof (rule linearI)
  fix a b :: "real^'n^'n"
  show "trace (M ** (a + b)) = trace (M ** a) + trace (M ** b)"
    by (simp add: trace_mult_sum sum.distrib algebra_simps)
next
  fix r :: real and a :: "real^'n^'n"
  show "trace (M ** (r *\<^sub>R a)) = r *\<^sub>R trace (M ** a)"
    by (simp add: trace_mult_sum sum_distrib_left algebra_simps)
qed

lemma bounded_linear_trace_mult_right:
  fixes P :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>a :: real^'n^'n. trace (a ** P))"
  unfolding linear_conv_bounded_linear[symmetric]
proof (rule linearI)
  fix a b :: "real^'n^'n"
  show "trace ((a + b) ** P) = trace (a ** P) + trace (b ** P)"
    by (simp add: trace_mult_sum sum.distrib algebra_simps)
next
  fix r :: real and a :: "real^'n^'n"
  show "trace ((r *\<^sub>R a) ** P) = r *\<^sub>R trace (a ** P)"
    by (simp add: trace_mult_sum sum_distrib_left algebra_simps)
qed

lemma bounded_linear_quadform:
  fixes z :: "real^'n::finite"
  shows "bounded_linear (\<lambda>a :: real^'n^'n. z \<bullet> (a *v z))"
  unfolding linear_conv_bounded_linear[symmetric]
proof (rule linearI)
  fix a b :: "real^'n^'n"
  show "z \<bullet> ((a + b) *v z) = z \<bullet> (a *v z) + z \<bullet> (b *v z)"
    by (simp add: matrix_vector_mult_def inner_vec_def sum.distrib
        algebra_simps)
next
  fix r :: real and a :: "real^'n^'n"
  show "z \<bullet> ((r *\<^sub>R a) *v z) = r *\<^sub>R (z \<bullet> (a *v z))"
    by (simp add: matrix_vector_mult_def inner_vec_def sum_distrib_left
        algebra_simps)
qed

lemma trace_mult_diff:
  fixes M A B :: "real^'n::finite^'n"
  shows "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
  by (simp add: trace_mult_sum sum_subtractf right_diff_distrib)

lemma trace_mult_scaleR:
  fixes M A :: "real^'n::finite^'n"
  shows "trace (M ** (r *\<^sub>R A)) = r * trace (M ** A)"
  by (simp add: trace_mult_sum sum_distrib_left algebra_simps)

lemma bounded_linear_transpose:
  "bounded_linear (transpose :: real^'n::finite^'n \<Rightarrow> real^'n^'n)"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: transpose_def vec_eq_iff)

subsection \<open>The averaged covariation stays in the constraint set\<close>

text \<open>Every condition defining \<^const>\<open>sconstraint\<close> is a LINEAR (in)equality in
  the matrix: \<^const>\<open>psd\<close> and \<^const>\<open>eigen_ub\<close> are conditions on the quadratic
  form \<open>z \<bullet> (a *v z)\<close>, which is linear in \<open>a\<close>, and \<open>c \<le> Pi_proj a m\<close> is by
  @{thm [source] Pi_proj_ge} an intersection of the half-spaces
  \<open>c \<le> trace (a ** P)\<close>, again linear in \<open>a\<close>.  So the set is an intersection of
  closed half-spaces and passes through the integral.\<close>

lemma paper_pair_class_Y_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have meas: "(\<lambda>\<omega>. snd (\<omega> t)) \<in> borel_measurable Q"
  proof (rule measurable_compose[OF paper_pair_class_eval_measurable[OF Q t]])
    show "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
  qed
  have bd: "AE \<omega> in Q. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
    using paper_pair_class_Y_bounded_ae[OF T L Q]
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    then show "norm (snd (\<omega> t)) \<le> real CARD('n) * L * T" using t by blast
  qed
  show ?thesis by (rule P.integrable_const_bound[OF bd meas])
qed

theorem paper_pair_class_Y_mean_sconstraint:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and t: "0 < t" and tT: "t \<le> T"
  shows "(1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q) \<in> sconstraint k L"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have tI: "t \<in> {0..T}" using t tT by simp
  have iY: "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
    by (rule paper_pair_class_Y_integrable[OF T L Q tI])
  have i1: "integrable Q (\<lambda>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t))"
    using iY by simp
  define b where "b = (1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)"
  have bint: "b = (\<integral>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t) \<partial>Q)"
    unfolding b_def by simp
  text \<open>the constraint of clause (iii), read between \<open>0\<close> and \<open>t\<close>\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding paper_pair_class_def by blast
  have dq: "AE \<omega> in Q. \<forall>s u. 0 \<le> s \<longrightarrow> s < u \<longrightarrow> u \<le> T \<longrightarrow>
      (1 / (u - s)) *\<^sub>R (snd (\<omega> u) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding paper_pair_class_def by blast
  have mem: "AE \<omega> in Q. (1 / t) *\<^sub>R snd (\<omega> t) \<in> sconstraint k L"
    using st dq
  proof eventually_elim
    case (elim \<omega>)
    have "(1 / (t - 0)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> 0)) \<in> sconstraint k L"
      using elim t tT by blast
    then show ?case using elim by simp
  qed
  have memP: "AE \<omega> in Q. psd ((1 / t) *\<^sub>R snd (\<omega> t))"
    using mem by eventually_elim (simp add: sconstraint_def Pi_constraint_def)
  have memU: "AE \<omega> in Q. eigen_ub ((1 / t) *\<^sub>R snd (\<omega> t)) L"
    using mem by eventually_elim (simp add: sconstraint_def)
  have memI: "AE \<omega> in Q. \<forall>m. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow>
      real (m - k) \<le> Pi_proj ((1 / t) *\<^sub>R snd (\<omega> t)) m"
    using mem by eventually_elim (simp add: sconstraint_def Pi_constraint_def)
  text \<open>a real-valued bounded linear functional passes through the integral\<close>
  have lin: "(\<integral>\<omega>. F ((1 / t) *\<^sub>R snd (\<omega> t)) \<partial>Q) = F b"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    unfolding bint by (rule integral_of_bounded_linear[OF F i1])
  have linI: "integrable Q (\<lambda>\<omega>. F ((1 / t) *\<^sub>R snd (\<omega> t)))"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    by (rule integrable_bounded_linear[OF F i1])
  text \<open>symmetry\<close>
  have trb: "transpose b = b"
  proof -
    have "transpose b = (\<integral>\<omega>. transpose ((1 / t) *\<^sub>R snd (\<omega> t)) \<partial>Q)"
      unfolding bint
      by (rule integral_of_bounded_linear
          [OF bounded_linear_transpose i1, symmetric])
    also have "\<dots> = (\<integral>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t) \<partial>Q)"
    proof (rule integral_cong_AE)
      show "(\<lambda>\<omega>. transpose ((1 / t) *\<^sub>R snd (\<omega> t))) \<in> borel_measurable Q"
        by (rule borel_measurable_integrable
            [OF integrable_bounded_linear[OF bounded_linear_transpose i1]])
      show "(\<lambda>\<omega>. (1 / t) *\<^sub>R snd (\<omega> t)) \<in> borel_measurable Q"
        by (rule borel_measurable_integrable[OF i1])
      show "AE \<omega> in Q. transpose ((1 / t) *\<^sub>R snd (\<omega> t))
          = (1 / t) *\<^sub>R snd (\<omega> t)"
        using memP by eventually_elim (simp add: psd_def)
    qed
    finally show ?thesis unfolding bint .
  qed
  text \<open>the quadratic form, both bounds\<close>
  have quad_lo: "0 \<le> z \<bullet> (b *v z)" for z :: "real^'n"
  proof -
    have "0 \<le> (\<integral>\<omega>. z \<bullet> (((1 / t) *\<^sub>R snd (\<omega> t)) *v z) \<partial>Q)"
      by (rule integral_nonneg_AE)
        (use memP in \<open>eventually_elim, simp add: psd_def\<close>)
    then show ?thesis using lin[OF bounded_linear_quadform] by simp
  qed
  have quad_hi: "z \<bullet> (b *v z) \<le> L * (z \<bullet> z)" for z :: "real^'n"
  proof -
    have "(\<integral>\<omega>. z \<bullet> (((1 / t) *\<^sub>R snd (\<omega> t)) *v z) \<partial>Q)
        \<le> (\<integral>\<omega>. L * (z \<bullet> z) \<partial>Q)"
      by (rule integral_mono_AE)
        (use linI[OF bounded_linear_quadform] memU
          in \<open>auto elim!: eventually_mono simp: eigen_ub_def\<close>)
    then show ?thesis
      using lin[OF bounded_linear_quadform] by (simp add: P.prob_space)
  qed
  have psdb: "psd b" unfolding psd_def using trb quad_lo by blast
  text \<open>the projection bounds\<close>
  have proj: "real (m - k) \<le> Pi_proj b m"
    if m: "k < m" "m \<le> CARD('n)" for m
  proof (rule Pi_proj_ge[OF m(2)])
    fix P :: "real^'n^'n"
    assume P: "is_proj P" and trP: "trace P = real m"
    have ae: "AE \<omega> in Q.
        real (m - k) \<le> trace (((1 / t) *\<^sub>R snd (\<omega> t)) ** P)"
      using memP memI
    proof eventually_elim
      case (elim \<omega>)
      have "real (m - k) \<le> Pi_proj ((1 / t) *\<^sub>R snd (\<omega> t)) m"
        using elim(2) m by blast
      also have "\<dots> \<le> trace (((1 / t) *\<^sub>R snd (\<omega> t)) ** P)"
        by (rule Pi_proj_le[OF elim(1) P trP])
      finally show ?case .
    qed
    have "real (m - k) = (\<integral>\<omega>. real (m - k) \<partial>Q)"
      by (simp add: P.prob_space)
    also have "\<dots> \<le> (\<integral>\<omega>. trace (((1 / t) *\<^sub>R snd (\<omega> t)) ** P) \<partial>Q)"
      by (rule integral_mono_AE)
        (use linI[OF bounded_linear_trace_mult_right] ae in auto)
    also have "\<dots> = trace (b ** P)"
      by (rule lin[OF bounded_linear_trace_mult_right])
    finally show "real (m - k) \<le> trace (b ** P)" .
  qed
  have pic: "b \<in> Pi_constraint k"
    unfolding Pi_constraint_def
  proof (intro CollectI conjI allI impI)
    show "psd b" by (rule psdb)
  next
    fix m assume "k < m" and "m \<le> CARD('n)"
    then show "real (m - k) \<le> Pi_proj b m" by (rule proj)
  qed
  have eub: "b \<in> {a :: real^'n^'n. eigen_ub a L}"
    using quad_hi by (simp add: eigen_ub_def)
  have "b \<in> sconstraint k L"
    unfolding sconstraint_def using pic eub by blast
  then show ?thesis unfolding b_def[symmetric] .
qed

subsection \<open>The exact expansion of a quadratic test function\<close>

lemma paper_pair_class_X_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
proof -
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n"
    by (rule paper_pair_class_X_martingale[OF Q])
  have "integrable Q (\<lambda>\<omega>. fst (\<omega> (min t T)) :: real^'n)"
    using t by (intro MG.integrable) simp
  then show ?thesis using t by simp
qed

theorem paper_pair_class_X_mean:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. fst (\<omega> t) \<partial>Q) = x"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n"
    by (rule paper_pair_class_X_martingale[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by simp_all
  have z: "(0::real) \<in> {0..T}" using t by simp
  have i0: "integrable Q (\<lambda>\<omega>. fst (\<omega> 0) :: real^'n)"
    by (rule paper_pair_class_X_integrable[OF Q z])
  have it: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
    by (rule paper_pair_class_X_integrable[OF Q t])
  have top: "space Q \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0)"
    using sets.top[of "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) 0"] by simp
  have const: "(\<integral>\<omega>. fst (\<omega> 0) \<partial>Q) = (\<integral>\<omega>. fst (\<omega> t) \<partial>Q)"
    using MG.set_integral_eq[OF top order.refl t0] t0 tT
    by (simp add: set_integral_space[OF i0] set_integral_space[OF it])
  have start: "(\<integral>\<omega>. fst (\<omega> 0) \<partial>Q) = x"
  proof -
    have ae: "AE \<omega> in Q. fst (\<omega> 0) = x"
    proof -
      have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
        using Q unfolding paper_pair_class_def by blast
      then show ?thesis by (rule eventually_mono) simp
    qed
    have "(\<integral>\<omega>. fst (\<omega> 0) \<partial>Q) = (\<integral>\<omega>. x \<partial>Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0] _ ae])
        measurable
    then show ?thesis by (simp add: P.prob_space)
  qed
  from const start show ?thesis by simp
qed

text \<open>The second-order identity.  Note there is no symmetry hypothesis on
  \<open>M\<close> and no stopping: clause (iv) is used at the FIXED time \<open>t\<close>, exactly as
  in @{thm [source] paper_pair_class_sq_norm_mean_ge}, of which this is the
  \<open>M = 1\<close> case with the inequality replaced by an identity.\<close>

theorem paper_pair_class_quadform_mean:
  fixes Q :: "('n::finite pairpath) measure" and M :: "real^'n^'n"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
       = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
proof -
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule paper_pair_class_compensated_integrable[OF Q t])
  have iY: "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
    by (rule paper_pair_class_Y_integrable[OF T L Q t])
  have iA: "integrable Q
      (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left ci])
  have iB: "integrable Q (\<lambda>\<omega>. trace (M ** snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have tdiff: "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
    for A B :: "real^'n^'n"
    by (rule trace_mult_diff)
  have eqf: "(\<lambda>\<omega>. trace (M ** outerp (fst (\<omega> t))))
      = (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t)))
             + trace (M ** snd (\<omega> t)))"
    by (rule ext) (simp add: tdiff)
  have e1: "(\<integral>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))) \<partial>Q)
      = trace (M ** outerp x)"
  proof -
    have "(\<integral>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))) \<partial>Q)
        = trace (M ** (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q))"
      by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left ci])
    also have "\<dots> = trace (M ** outerp x)"
      by (simp add: paper_pair_class_compensated_mean[OF Q t])
    finally show ?thesis .
  qed
  have e2: "(\<integral>\<omega>. trace (M ** snd (\<omega> t)) \<partial>Q)
      = trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
    by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
      = (\<integral>\<omega>. trace (M ** outerp (fst (\<omega> t))) \<partial>Q)"
    by (simp add: trace_mult_outerp)
  also have "\<dots> = (\<integral>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))) \<partial>Q)
      + (\<integral>\<omega>. trace (M ** snd (\<omega> t)) \<partial>Q)"
    unfolding eqf by (rule Bochner_Integration.integral_add[OF iA iB])
  also have "\<dots> = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
    unfolding e1 e2 by (simp add: trace_mult_outerp)
  finally show ?thesis .
qed

lemma paper_pair_class_quadform_integrable:
  fixes Q :: "('n::finite pairpath) measure" and M :: "real^'n^'n"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)))"
proof -
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule paper_pair_class_compensated_integrable[OF Q t])
  have iY: "integrable Q (\<lambda>\<omega>. snd (\<omega> t))"
    by (rule paper_pair_class_Y_integrable[OF T L Q t])
  have iA: "integrable Q
      (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t))))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left ci])
  have iB: "integrable Q (\<lambda>\<omega>. trace (M ** snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have tdiff: "trace (M ** (A - B)) = trace (M ** A) - trace (M ** B)"
    for A B :: "real^'n^'n"
    by (rule trace_mult_diff)
  have eqf: "(\<lambda>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)))
      = (\<lambda>\<omega>. trace (M ** (outerp (fst (\<omega> t)) - snd (\<omega> t)))
             + trace (M ** snd (\<omega> t)))"
    by (rule ext) (simp add: tdiff trace_mult_outerp[symmetric])
  show ?thesis
    unfolding eqf by (rule Bochner_Integration.integrable_add[OF iA iB])
qed

text \<open>The packaged form: the mean increment of a quadratic test function
  along ANY class member is \<open>(t/2) \<sqdot> trace (M ** b)\<close> for a single averaged
  direction \<open>b\<close> of the constraint set.  This is the substitute for Ito's
  formula that the viscosity argument actually needs.\<close>

theorem paper_pair_class_quadratic_mean:
  fixes Q :: "('n::finite pairpath) measure" and M :: "real^'n^'n"
    and p :: "real^'n" and c :: real
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and t: "0 < t" and tT: "t \<le> T"
  obtains b where "b \<in> sconstraint k L"
    and "(\<integral>\<omega>. c + p \<bullet> fst (\<omega> t) + (fst (\<omega> t) \<bullet> (M *v fst (\<omega> t))) / 2 \<partial>Q)
       = c + p \<bullet> x + (x \<bullet> (M *v x)) / 2 + (t / 2) * trace (M ** b)"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have tI: "t \<in> {0..T}" using t tT by simp
  define b where "b = (1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)"
  have bmem: "b \<in> sconstraint k L"
    unfolding b_def by (rule paper_pair_class_Y_mean_sconstraint[OF T L Q t tT])
  have bY: "(\<integral>\<omega>. snd (\<omega> t) \<partial>Q) = t *\<^sub>R b"
    unfolding b_def using t by simp
  have iX: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
    by (rule paper_pair_class_X_integrable[OF Q tI])
  have iP: "integrable Q (\<lambda>\<omega>. p \<bullet> fst (\<omega> t))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have iM: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)))"
    by (rule paper_pair_class_quadform_integrable[OF T L Q tI])
  have mP: "(\<integral>\<omega>. p \<bullet> fst (\<omega> t) \<partial>Q) = p \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX]
      paper_pair_class_X_mean[OF Q tI] by simp
  have mM: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
      = x \<bullet> (M *v x) + t * trace (M ** b)"
  proof -
    have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q)
        = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
      by (rule paper_pair_class_quadform_mean[OF T L Q tI])
    also have "trace (M ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)) = t * trace (M ** b)"
      unfolding bY by (rule trace_mult_scaleR)
    finally show ?thesis .
  qed
  have "(\<integral>\<omega>. c + p \<bullet> fst (\<omega> t)
        + (fst (\<omega> t) \<bullet> (M *v fst (\<omega> t))) / 2 \<partial>Q)
      = c + (\<integral>\<omega>. p \<bullet> fst (\<omega> t) \<partial>Q)
        + (\<integral>\<omega>. fst (\<omega> t) \<bullet> (M *v fst (\<omega> t)) \<partial>Q) / 2"
    using iP iM by (simp add: P.prob_space)
  also have "\<dots> = c + p \<bullet> x + (x \<bullet> (M *v x)) / 2 + (t / 2) * trace (M ** b)"
    unfolding mP mM by (simp add: field_simps)
  finally show ?thesis using that[OF bmem] by blast
qed

subsection \<open>What the orthogonality constraint of Eq. (1.9) actually does\<close>

text \<open>A direction annihilated by the averaged covariation is FROZEN: the
  process does not move along it at all, almost surely.  The proof is the
  quadratic identity at \<open>M = outerp q\<close>, which turns the second moment of
  \<open>q \<bullet> X\<^sub>t\<close> into \<open>q \<bullet> (E[Y\<^sub>t] *v q)\<close> --- so the variance vanishes exactly when
  that number does.

  This is the mechanism behind the constraint \<open>a *v p = 0\<close> of Eq. (1.9).  For a
  quadratic test function with gradient \<open>q = p + M *v x\<close> at \<open>x\<close>,

    \<open>\<phi>(X\<^sub>t) - \<phi>(x) = q \<bullet> (X\<^sub>t - x) + (X\<^sub>t - x) \<bullet> (M *v (X\<^sub>t - x)) / 2\<close>

  when \<open>M\<close> is symmetric, and feasibility of the covariation direction kills the
  FIRST-ORDER term identically --- not just in mean.  That is what a
  supersolution argument needs and a subsolution argument does not: an a.s.
  statement, obtained from a mean-zero variance.\<close>

lemma trace_mult_commute:
  fixes A B :: "real^'n::finite^'n"
  shows "trace (A ** B) = trace (B ** A)"
  unfolding trace_mult_sum by (subst sum.swap) (simp add: mult.commute)

lemma trace_outerp_mult:
  fixes B :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (outerp v ** B) = v \<bullet> (B *v v)"
  by (subst trace_mult_commute) (rule trace_mult_outerp)

lemma quadform_outerp:
  fixes q z :: "real^'n::finite"
  shows "z \<bullet> (outerp q *v z) = (q \<bullet> z)\<^sup>2"
  by (simp add: outerp_eq_outer_prod power2_eq_square inner_commute)

theorem paper_pair_class_frozen_direction:
  fixes Q :: "('n::finite pairpath) measure" and q :: "real^'n"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
    and orth: "(\<integral>\<omega>. snd (\<omega> t) \<partial>Q) *v q = 0"
  shows "AE \<omega> in Q. q \<bullet> fst (\<omega> t) = q \<bullet> x"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have iX: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) :: real^'n)"
    by (rule paper_pair_class_X_integrable[OF Q t])
  have i1: "integrable Q (\<lambda>\<omega>. q \<bullet> fst (\<omega> t))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have i2': "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> (outerp q *v fst (\<omega> t)))"
    by (rule paper_pair_class_quadform_integrable[OF T L Q t])
  have i2: "integrable Q (\<lambda>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2)"
    using i2' by (simp add: quadform_outerp)
  have m1: "(\<integral>\<omega>. q \<bullet> fst (\<omega> t) \<partial>Q) = q \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX]
      paper_pair_class_X_mean[OF Q t] by simp
  have m2: "(\<integral>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2 \<partial>Q) = (q \<bullet> x)\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2 \<partial>Q)
        = (\<integral>\<omega>. fst (\<omega> t) \<bullet> (outerp q *v fst (\<omega> t)) \<partial>Q)"
      by (simp add: quadform_outerp)
    also have "\<dots> = x \<bullet> (outerp q *v x)
        + trace (outerp q ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))"
      by (rule paper_pair_class_quadform_mean[OF T L Q t])
    also have "trace (outerp q ** (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))
        = q \<bullet> ((\<integral>\<omega>. snd (\<omega> t) \<partial>Q) *v q)"
      by (rule trace_outerp_mult)
    finally show ?thesis by (simp add: orth quadform_outerp)
  qed
  \<comment> \<open>the second moment equals the square of the mean, so the variance is zero\<close>
  have iv: "integrable Q (\<lambda>\<omega>. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2)"
  proof -
    have "(\<lambda>\<omega>. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2)
        = (\<lambda>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2 - 2 * (q \<bullet> x) * (q \<bullet> fst (\<omega> t))
              + (q \<bullet> x)\<^sup>2)"
      by (rule ext) (simp add: power2_eq_square algebra_simps)
    have bl: "bounded_linear (\<lambda>r :: real. 2 * (q \<bullet> x) * r)"
      unfolding linear_conv_bounded_linear[symmetric]
      by (intro linearI) (simp_all add: algebra_simps)
    have i4: "integrable Q (\<lambda>\<omega>. 2 * (q \<bullet> x) * (q \<bullet> fst (\<omega> t)))"
      by (rule integrable_bounded_linear[OF bl i1])
    show ?thesis
      unfolding \<open>(\<lambda>\<omega>. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2)
        = (\<lambda>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2 - 2 * (q \<bullet> x) * (q \<bullet> fst (\<omega> t))
              + (q \<bullet> x)\<^sup>2)\<close>
      by (intro Bochner_Integration.integrable_add
          Bochner_Integration.integrable_diff i2 i4 P.integrable_const)
  qed
  have var: "(\<integral>\<omega>. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2 \<partial>Q) = 0"
  proof -
    have e: "(\<lambda>\<omega>. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2)
        = (\<lambda>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2 - 2 * (q \<bullet> x) * (q \<bullet> fst (\<omega> t))
              + (q \<bullet> x)\<^sup>2)"
      by (rule ext) (simp add: power2_eq_square algebra_simps)
    have "(\<integral>\<omega>. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2 \<partial>Q)
        = (\<integral>\<omega>. (q \<bullet> fst (\<omega> t))\<^sup>2 \<partial>Q)
          - 2 * (q \<bullet> x) * (\<integral>\<omega>. q \<bullet> fst (\<omega> t) \<partial>Q) + (q \<bullet> x)\<^sup>2"
      unfolding e using i1 i2 by (simp add: P.prob_space)
    also have "\<dots> = 0" unfolding m1 m2 by (simp add: power2_eq_square)
    finally show ?thesis .
  qed
  have nn: "AE \<omega> in Q. 0 \<le> (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2" by simp
  have "AE \<omega> in Q. (q \<bullet> fst (\<omega> t) - q \<bullet> x)\<^sup>2 = 0"
    using integral_nonneg_eq_0_iff_AE[OF iv nn] var by simp
  then show ?thesis by eventually_elim simp
qed

corollary paper_pair_class_feasible_freezes_gradient:
  fixes Q :: "('n::finite pairpath) measure" and q :: "real^'n"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and t: "0 < t" and tT: "t \<le> T"
    and a: "(1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q) \<in> feasible k L q"
  shows "AE \<omega> in Q. q \<bullet> fst (\<omega> t) = q \<bullet> x"
proof (rule paper_pair_class_frozen_direction[OF T L Q _ ])
  show "t \<in> {0..T}" using t tT by simp
  have z: "((1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)) *v q = 0"
    using a unfolding feasible_def by blast
  have "(\<integral>\<omega>. snd (\<omega> t) \<partial>Q) *v q
      = (t *\<^sub>R ((1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q))) *v q"
    using t by simp
  also have "\<dots> = t *\<^sub>R (((1 / t) *\<^sub>R (\<integral>\<omega>. snd (\<omega> t) \<partial>Q)) *v q)"
    by (rule scaleR_matrix_vector)
  also have "\<dots> = 0" unfolding z by simp
  finally show "(\<integral>\<omega>. snd (\<omega> t) \<partial>Q) *v q = 0" .
qed

section \<open>The relaxed operator, and the inequality the class really gives\<close>

text \<open>Eq. (1.9) takes its infimum over \<^const>\<open>feasible\<close>, which carries the
  ORTHOGONALITY constraint \<open>a *v p = 0\<close> on top of the spectral bounds.  The
  class of (1.7) carries no such constraint: its covariation directions live in
  \<^const>\<open>sconstraint\<close>.  The two are related in one direction only,

    \<^const>\<open>feasible\<close> \<open>k L p\<close> \<open>\<subseteq>\<close> \<^const>\<open>sconstraint\<close> \<open>k L\<close>

  (@{thm [source] suff_volatile_cap_in_sconstraint}), so the infimum over the
  larger set is SMALLER: \<open>ell_op_s \<le> ell_op\<close>.  Naming the relaxed operator is
  not a weakening for its own sake --- it is the exact record of what a
  probabilistic argument over the class can and cannot deliver, and it keeps
  the missing ingredient (the orthogonality of the OPTIMAL direction to the
  gradient) visible instead of buried.\<close>

definition ell_op_s :: "nat \<Rightarrow> real \<Rightarrow> real^'n::finite^'n \<Rightarrow> real" where
  "ell_op_s k L M = Inf ((\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L)"

lemma ell_op_s_bdd_below:
  fixes M :: "real^'n::finite^'n"
  assumes L: "0 \<le> L"
  shows "bdd_below ((\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L)"
proof (rule bdd_belowI[of _
      "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (real CARD('n) * L)) / 2"])
  fix v assume "v \<in> (\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L"
  then obtain a where a: "a \<in> sconstraint k L"
    and v: "v = - trace (M ** a) / 2" by auto
  have eb: "\<bar>a $ j $ i\<bar> \<le> real CARD('n) * L" for i j
  proof -
    have "\<bar>a $ j $ i\<bar> = norm (a $ j $ i)" by simp
    also have "\<dots> \<le> norm (a $ j)" by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> norm a" by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> real CARD('n) * L" by (rule sconstraint_norm_le[OF L a])
    finally show ?thesis .
  qed
  have "trace (M ** a) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j * a $ j $ i\<bar>)"
    unfolding trace_mult_sum by (intro sum_mono order_trans[OF _ sum_abs]) auto
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * (real CARD('n) * L))"
    by (intro sum_mono) (simp add: abs_mult mult_left_mono eb)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (real CARD('n) * L)"
    by (simp add: sum_distrib_right)
  finally show
    "- ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (real CARD('n) * L)) / 2 \<le> v"
    by (simp add: v)
qed

lemma ell_op_s_le_of_witness:
  fixes M :: "real^'n::finite^'n"
  assumes L: "0 \<le> L" and a: "a \<in> sconstraint k L"
    and le: "- trace (M ** a) / 2 \<le> c"
  shows "ell_op_s k L M \<le> c"
proof -
  have mem: "- trace (M ** a) / 2
      \<in> (\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L"
    using a by blast
  have "ell_op_s k L M \<le> - trace (M ** a) / 2"
    unfolding ell_op_s_def by (rule cInf_lower[OF mem ell_op_s_bdd_below[OF L]])
  also have "\<dots> \<le> c" by (rule le)
  finally show ?thesis .
qed

lemma feasible_subset_sconstraint:
  fixes p :: "real^'n::finite"
  shows "feasible k L p \<subseteq> sconstraint k L"
proof
  fix a :: "real^'n^'n"
  assume a: "a \<in> feasible k L p"
  have sv: "a \<in> suff_volatile k"
    using a unfolding feasible_def suff_volatile_def by blast
  have ub: "eigen_ub a L" using a unfolding feasible_def by blast
  show "a \<in> sconstraint k L"
    by (rule suff_volatile_cap_in_sconstraint[OF sv ub])
qed

lemma ell_op_s_le_ell_op:
  fixes M :: "real^'n::finite^'n" and p :: "real^'n"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
  shows "ell_op_s k L M \<le> ell_op k L p M"
proof -
  have L0: "0 \<le> L" using L by simp
  have ne: "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p \<noteq> {}"
    using feasible_nonempty[OF k L] by blast
  have sub: "(\<lambda>a. - trace (M ** a) / 2) ` feasible k L p
      \<subseteq> (\<lambda>a. - trace (M ** a) / 2) ` sconstraint k L"
    by (rule image_mono[OF feasible_subset_sconstraint])
  show ?thesis
    unfolding ell_op_s_def ell_op_def
    by (rule cInf_superset_mono[OF ne ell_op_s_bdd_below[OF L0] sub])
qed

text \<open>Now the inequality itself.  Everything the argument needs is in place:
  @{thm [source] paper_v_attained} supplies the optimizer, at which the exit
  time dominates the value ALMOST SURELY --- and that is the whole reason the
  SUBSOLUTION half is the one reachable by expectations, since the DPP bound it
  consumes is an a.s. bound and a.s. bounds survive integration, whereas the
  supersolution half needs a lower bound on an essential infimum, which a mean
  cannot give.

  The test function is quadratic and touches GLOBALLY.  Localisation ---
  turning a local touching into a global one --- is the Crandall--Ishii step and
  is not attempted here; and \<open>ell_op_s\<close> rather than \<^const>\<open>ell_op\<close> is what
  comes out, for the reason recorded above.  Both gaps are named, neither is
  hidden.\<close>

theorem paper_v_subsol_quadratic_global:
  fixes K :: "(real^'n::finite) set" and M :: "real^'n^'n"
    and p :: "real^'n" and x :: "real^'n" and c :: real
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and touch: "\<And>z. enn2real (paper_v k L T K z)
          - (c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
        \<le> enn2real (paper_v k L T K x)
          - (c + p \<bullet> x + (x \<bullet> (M *v x)) / 2)"
  shows "ell_op_s k L M \<le> 1"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have T0: "0 \<le> T" using T by simp
  define u where "u = (\<lambda>z :: real^'n. enn2real (paper_v k L T K z))"
  define \<phi> where "\<phi> = (\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)"
  define h where "h = T / 2"
  have h0: "0 < h" and hT: "h \<le> T" using T by (simp_all add: h_def)
  have hI: "h \<in> {0..T}" using h0 hT by simp
  obtain P where P: "P \<in> paper_pair_class k L T x"
    and Pv: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = paper_v k L T K x"
    using paper_v_attained[OF T L1 Kc] by blast
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  text \<open>at the optimizer the exit time dominates the value almost surely\<close>
  have cAE: "AE \<omega> in P. u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono
      [OF ess_inf_time_AE[of P "\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have le: "paper_v k L T K x \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Pv by simp
    have "enn2real (paper_v k L T K x)
        \<le> enn2real (ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule enn2real_mono[OF le ennreal_less_top])
    then show "u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      unfolding u_def
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  text \<open>the DPP at the CONSTANT time \<open>h\<close>, then the horizon cap\<close>
  have dpp: "AE \<omega> in P. u x \<le> h + enn2real (paper_v k L (T - h) K (fst (\<omega> h)))"
    by (rule paper_v_cond_time[OF T0 L1 Kc P cAE]) (use h0 hT in auto)
  have low: "AE \<omega> in P. u x - h \<le> u (fst (\<omega> h))"
  proof (rule eventually_mono[OF dpp])
    fix \<omega> :: "'n pairpath"
    assume d: "u x \<le> h + enn2real (paper_v k L (T - h) K (fst (\<omega> h)))"
    have a: "0 \<le> T - h" using hT by simp
    have b: "T - h \<le> T" using h0 by simp
    have "enn2real (paper_v k L (T - h) K (fst (\<omega> h)))
        = min (u (fst (\<omega> h))) (T - h)"
      unfolding u_def by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with d show "u x - h \<le> u (fst (\<omega> h))" by simp
  qed
  text \<open>the touching hypothesis transports it to the test function\<close>
  have phiAE: "AE \<omega> in P. \<phi> x - h \<le> \<phi> (fst (\<omega> h))"
  proof (rule eventually_mono[OF low])
    fix \<omega> :: "'n pairpath"
    assume lo: "u x - h \<le> u (fst (\<omega> h))"
    have "u (fst (\<omega> h)) - \<phi> (fst (\<omega> h)) \<le> u x - \<phi> x"
      unfolding u_def \<phi>_def by (rule touch)
    with lo show "\<phi> x - h \<le> \<phi> (fst (\<omega> h))" by simp
  qed
  text \<open>integrate, and read off the exact expansion\<close>
  obtain b where b: "b \<in> sconstraint k L"
    and mean: "(\<integral>\<omega>. c + p \<bullet> fst (\<omega> h)
          + (fst (\<omega> h) \<bullet> (M *v fst (\<omega> h))) / 2 \<partial>P)
        = c + p \<bullet> x + (x \<bullet> (M *v x)) / 2 + (h / 2) * trace (M ** b)"
    by (rule paper_pair_class_quadratic_mean[OF T0 L0 P h0 hT])
  have i1: "integrable P (\<lambda>\<omega>. p \<bullet> fst (\<omega> h))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right
        paper_pair_class_X_integrable[OF P hI]])
  have i2: "integrable P (\<lambda>\<omega>. fst (\<omega> h) \<bullet> (M *v fst (\<omega> h)))"
    by (rule paper_pair_class_quadform_integrable[OF T0 L0 P hI])
  have bl2: "bounded_linear (\<lambda>r :: real. r / 2)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (simp_all add: field_simps)
  have i3: "integrable P (\<lambda>\<omega>. (fst (\<omega> h) \<bullet> (M *v fst (\<omega> h))) / 2)"
    by (rule integrable_bounded_linear[OF bl2 i2])
  have iphi: "integrable P (\<lambda>\<omega>. \<phi> (fst (\<omega> h)))"
    unfolding \<phi>_def
    by (intro Bochner_Integration.integrable_add i1 i3 PP.integrable_const)
  have mean': "(\<integral>\<omega>. \<phi> (fst (\<omega> h)) \<partial>P) = \<phi> x + (h / 2) * trace (M ** b)"
    unfolding \<phi>_def using mean by simp
  have "\<phi> x - h = (\<integral>\<omega>. \<phi> x - h \<partial>P)" by (simp add: PP.prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. \<phi> (fst (\<omega> h)) \<partial>P)"
    by (rule integral_mono_AE) (use iphi phiAE in auto)
  finally have "\<phi> x - h \<le> \<phi> x + (h / 2) * trace (M ** b)"
    unfolding mean' .
  then have "- h \<le> (h / 2) * trace (M ** b)" by simp
  then have le2: "(- 2) * (h / 2) \<le> trace (M ** b) * (h / 2)"
    by (simp add: field_simps)
  have hp: "0 < h / 2" using h0 by simp
  have "- 2 \<le> trace (M ** b)" by (rule mult_right_le_imp_le[OF le2 hp])
  then have w: "- trace (M ** b) / 2 \<le> 1" by simp
  show ?thesis by (rule ell_op_s_le_of_witness[OF L0 b w])
qed

subsection \<open>Quadratics are test functions, and the relaxed predicates\<close>

lemma test_fun_at_quadratic:
  fixes M :: "real^'n::finite^'n" and p x :: "real^'n" and c :: real
  assumes sym: "transpose M = M"
  shows "test_fun_at (\<lambda>z. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
      (\<lambda>z. p + M *v z) M x"
  unfolding test_fun_at_def
proof (intro conjI)
  show "transpose M = M" by (rule sym)
next
  have bl: "bounded_linear (\<lambda>z :: real^'n. M *v z)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have dM: "((\<lambda>z :: real^'n. M *v z) has_derivative (\<lambda>h. M *v h)) (at y)"
    for y :: "real^'n"
    by (rule bounded_linear.has_derivative[OF bl has_derivative_ident])
  have d: "((\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
      has_derivative (\<lambda>h. (p + M *v y) \<bullet> h)) (at y)" for y :: "real^'n"
  proof -
    have "((\<lambda>z :: real^'n. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2)
        has_derivative (\<lambda>h. p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2))
        (at y)"
      by (auto intro!: derivative_eq_intros dM)
    moreover have "(\<lambda>h :: real^'n. p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2)
        = (\<lambda>h. (p + M *v y) \<bullet> h)"
    proof (rule ext)
      fix h :: "real^'n"
      have "y \<bullet> (M *v h) = (transpose M *v y) \<bullet> h"
        by (rule inner_transpose_matrix)
      then have "y \<bullet> (M *v h) = (M *v y) \<bullet> h" using sym by simp
      then show "p \<bullet> h + (h \<bullet> (M *v y) + y \<bullet> (M *v h)) / 2
          = (p + M *v y) \<bullet> h"
        by (simp add: inner_commute inner_add_right)
    qed
    ultimately show ?thesis by simp
  qed
  show "\<exists>e>0. \<forall>y \<in> ball x e.
      ((\<lambda>z. c + p \<bullet> z + (z \<bullet> (M *v z)) / 2) has_derivative
        (\<lambda>h. (p + M *v y) \<bullet> h)) (at y)"
    using d by (intro exI[of _ 1]) auto
next
  have bl: "bounded_linear (\<lambda>z :: real^'n. M *v z)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  show "((\<lambda>z. p + M *v z) has_derivative (\<lambda>h. M *v h)) (at x)"
    using bounded_linear.has_derivative[OF bl has_derivative_ident]
    by (auto intro!: derivative_eq_intros)
qed

section \<open>The ball exit time along a continuous path\<close>

text \<open>Three pathwise facts about \<^const>\<open>pball_exit\<close>.  All three are what an
  Ito-side supplier will consume, and none of them needs a law: they are
  statements about a single continuous path.

  The first is ATTAINMENT.  With \<open>K\<close> open the target \<open>-K\<close> is closed, so along
  a continuous path the infimum defining \<^const>\<open>pexit\<close> is a minimum whenever
  it is below the horizon --- the path really is outside \<open>K\<close> at the exit time.
  This is the single fact that fails for a general (discontinuous) function,
  and every other clause below is a consequence of it.\<close>

lemma pexit_le_of_mem:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" "r \<le> T" and mem: "f r \<notin> K"
  shows "pexit T K f \<le> r"
  unfolding pexit_def using T0 r mem by (intro etime_le_of_mem) auto

lemma pexit_mem_of_less_T:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and lt: "pexit T K f < T"
  shows "f (pexit T K f) \<notin> K"
proof -
  let ?S = "{r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K}"
  have cK: "closed (- K)" unfolding closed_def using Kop by simp
  have Sclosed: "closed ?S"
  proof -
    have "?S = f -` (- K) \<inter> {0..T}" by auto
    then show ?thesis using cont cK by (simp add: continuous_on_closed_vimage)
  qed
  have Sbdd: "bdd_below ?S" by (intro bdd_belowI[of _ 0]) auto
  have pe: "pexit T K f = Inf (?S \<union> {T})"
    unfolding pexit_def etime_def by simp
  have Sne: "?S \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> ?S \<noteq> {}"
    then have e: "?S = {}" by simp
    have "pexit T K f = Inf ({} \<union> {T})" unfolding pe e ..
    then have "pexit T K f = T" by simp
    with lt show False by simp
  qed
  have SleT: "Inf ?S \<le> T"
  proof -
    from Sne obtain s where s: "s \<in> ?S" by blast
    then have "Inf ?S \<le> s" using Sbdd by (intro cInf_lower)
    also have "s \<le> T" using s by simp
    finally show ?thesis .
  qed
  have "Inf (?S \<union> {T}) = inf (Inf ?S) (Inf {T})"
    by (rule cInf_union_distrib[OF Sne Sbdd]) auto
  then have "pexit T K f = Inf ?S" using pe SleT by (simp add: inf_min)
  moreover have "Inf ?S \<in> ?S"
    using Sne Sbdd Sclosed by (intro closed_contains_Inf) auto
  ultimately show ?thesis by simp
qed

text \<open>The second is the CONGRUENCE clause of a stopping time, restricted to
  continuous paths.  Note the asymmetry: the \<open>\<ge>\<close> direction is unconditional
  (a witness for \<open>g\<close> strictly below the exit time of \<open>f\<close> is a witness for \<open>f\<close>
  too), and only the \<open>\<le>\<close> direction needs attainment.\<close>

lemma pexit_cong_stopping:
  fixes f g :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and eq: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pexit T K f \<Longrightarrow> f t = g t"
  shows "pexit T K g = pexit T K f"
proof -
  have th0: "0 \<le> pexit T K f" by (rule pexit_nonneg[OF T0])
  have thT: "pexit T K f \<le> T" by (rule pexit_le_T[OF T0])
  have le: "pexit T K g \<le> pexit T K f"
  proof (cases "pexit T K f < T")
    case True
    have "f (pexit T K f) \<notin> K"
      by (rule pexit_mem_of_less_T[OF T0 Kop cont True])
    then have m: "g (pexit T K f) \<notin> K"
      using eq[OF th0 order_refl] by simp
    show ?thesis
      by (rule pexit_le_of_mem[of T "pexit T K f" g K, OF T0 th0 thT m])
  next
    case False
    with thT have "pexit T K f = T" by simp
    then show ?thesis using pexit_le_T[OF T0, of K g] by simp
  qed
  have ge: "pexit T K f \<le> pexit T K g"
  proof (rule ccontr)
    assume "\<not> pexit T K f \<le> pexit T K g"
    then have lt: "pexit T K g < pexit T K f" by simp
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> g r \<in> - K \<and> r < pexit T K f)
        \<or> T < pexit T K f"
      using lt pexit_less_iff[OF T0] by blast
    with thT obtain r where r: "0 \<le> r" "r \<le> T" "g r \<notin> K"
      "r < pexit T K f" by auto
    have "f r \<notin> K" using eq[OF r(1)] r(4) r(3) by simp
    then have "pexit T K f \<le> r"
      by (rule pexit_le_of_mem[OF T0 r(1) r(2)])
    with r(4) show False by simp
  qed
  from le ge show ?thesis by simp
qed

lemma pball_exit_cong:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and eq: "\<And>t. t \<in> {0..pball_exit T x \<epsilon> \<omega>} \<Longrightarrow> \<omega> t = \<omega>' t"
  shows "pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def
proof (rule pexit_cong_stopping[OF T0 open_ball cont])
  fix t :: real
  assume t: "0 \<le> t" "t \<le> pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"
  then have "t \<in> {0..pball_exit T x \<epsilon> \<omega>}" by (simp add: pball_exit_def)
  from eq[OF this] show "fst (\<omega> t) = fst (\<omega>' t)" by simp
qed

text \<open>The third is what makes the exit time USEFUL to the expansion: below the
  horizon the path has actually travelled the full distance \<open>\<epsilon>\<close>.\<close>

lemma pball_exit_outside:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and lt: "pball_exit T x \<epsilon> \<omega> < T"
  shows "\<epsilon> \<le> dist (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))) x"
proof -
  have "fst (\<omega> (pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t)))) \<notin> ball x \<epsilon>"
    using lt unfolding pball_exit_def
    by (intro pexit_mem_of_less_T[OF T0 open_ball cont]) simp
  then show ?thesis
    unfolding pball_exit_def by (simp add: dist_commute)
qed

text \<open>And it is strictly positive when the path starts strictly inside the
  ball --- which is exactly the situation of the subsolution argument, where
  the starting point is the touching point \<open>x\<close> itself.  Without this the DPP
  bound of @{thm [source] paper_v_cond_ball} would be vacuous.\<close>

lemma pball_exit_pos:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 < T"
    and start: "dist (fst (\<omega> 0)) x < \<epsilon>"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "0 < pball_exit T x \<epsilon> \<omega>"
proof -
  have T0': "0 \<le> T" using T0 by simp
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have e0: "0 < \<epsilon> - dist (fst (\<omega> 0)) x" using start by simp
  from cont[unfolded continuous_on_iff] z e0
  obtain \<delta> where d0: "0 < \<delta>"
    and dd: "\<And>t. t \<in> {0..T} \<Longrightarrow> dist t 0 < \<delta>
        \<Longrightarrow> dist (fst (\<omega> t)) (fst (\<omega> 0)) < \<epsilon> - dist (fst (\<omega> 0)) x"
    by blast
  have mle: "min \<delta> T \<le> pball_exit T x \<epsilon> \<omega>"
  proof (rule ccontr)
    assume "\<not> min \<delta> T \<le> pball_exit T x \<epsilon> \<omega>"
    then have lt0: "pball_exit T x \<epsilon> \<omega> < min \<delta> T" by (rule not_le_imp_less)
    then have lt: "pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t)) < min \<delta> T"
      by (simp add: pball_exit_def)
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> fst (\<omega> r) \<in> - ball x \<epsilon> \<and> r < min \<delta> T)
        \<or> T < min \<delta> T"
      using lt[unfolded pexit_less_iff[OF T0']] .
    then obtain r where r: "0 \<le> r" "r \<le> T" "fst (\<omega> r) \<notin> ball x \<epsilon>"
      "r < min \<delta> T" by auto
    have dr: "dist (fst (\<omega> r)) (fst (\<omega> 0)) < \<epsilon> - dist (fst (\<omega> 0)) x"
      using r by (intro dd) (auto simp: dist_real_def)
    have "dist (fst (\<omega> r)) x
        \<le> dist (fst (\<omega> r)) (fst (\<omega> 0)) + dist (fst (\<omega> 0)) x"
      by (rule dist_triangle)
    also have "\<dots> < \<epsilon>" using dr by simp
    finally have "fst (\<omega> r) \<in> ball x \<epsilon>" by (simp add: dist_commute)
    with r(3) show False by simp
  qed
  have m0: "0 < min \<delta> T" using d0 T0 by simp
  show ?thesis by (rule order_less_le_trans[OF m0 mle])
qed

section \<open>The ball exit time IS a stopping time\<close>

text \<open>\<^const>\<open>path_stopping_time\<close> now restricts its congruence clause to
  CONTINUOUS paths, which is exactly what @{thm [source] pexit_mem_of_less_T}
  shows is forced --- attainment of the infimum genuinely fails off the path
  space, so no redefinition of the exit time could have avoided it.  The
  restriction costs nothing, because \<open>space Q = mspace (path_metric T)\<close> IS the
  set of continuous paths, and it buys this:\<close>

theorem pball_exit_path_stopping_time:
  fixes x :: "real^'n::finite"
  assumes T0: "0 \<le> T"
  shows "path_stopping_time T (pball_exit T x \<epsilon>)"
  unfolding path_stopping_time_def
proof (intro conjI)
  show "\<forall>\<omega> :: 'n pairpath.
      0 \<le> pball_exit T x \<epsilon> \<omega> \<and> pball_exit T x \<epsilon> \<omega> \<le> T"
    using pball_exit_nonneg[OF T0] pball_exit_le[OF T0] by blast
next
  show "\<forall>\<omega> \<omega>' :: 'n pairpath.
      continuous_on {0..T} (\<lambda>t. fst (\<omega> t)) \<longrightarrow>
      continuous_on {0..T} (\<lambda>t. fst (\<omega>' t)) \<longrightarrow>
      (\<forall>t \<in> {0..pball_exit T x \<epsilon> \<omega>}. \<omega> t = \<omega>' t) \<longrightarrow>
      pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
  proof (intro allI impI)
    fix \<omega> \<omega>' :: "'n pairpath"
    assume c: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      and c': "continuous_on {0..T} (\<lambda>t. fst (\<omega>' t))"
      and e: "\<forall>t \<in> {0..pball_exit T x \<epsilon> \<omega>}. \<omega> t = \<omega>' t"
    show "pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
      by (rule pball_exit_cong[OF T0 c]) (use e in blast)
  qed
qed

text \<open>So @{thm [source] paper_v_dpp_sup_ge_time} now applies at the exit time
  of a ball, and optional sampling at \<open>\<tau> \<and> h\<close> is available --- which is what
  Gap 1's stochastic localisation needs.\<close>

section \<open>Scalar multiples through the Bochner integral\<close>

text \<open>Two tiny facts used throughout the localisation: multiplying by a real
  constant passes through integrability and the integral.  Stated once, since
  the global names for these keep shifting.\<close>

lemma integrable_cmult:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "integrable N g"
  shows "integrable N (\<lambda>\<omega>. c * g \<omega>)"
proof -
  have bl: "bounded_linear (\<lambda>r :: real. c * r)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (auto simp: algebra_simps)
  show ?thesis by (rule integrable_bounded_linear[OF bl g])
qed

lemma integral_cmult:
  fixes g :: "'a \<Rightarrow> real"
  assumes g: "integrable N g"
  shows "(\<integral>\<omega>. c * g \<omega> \<partial>N) = c * (\<integral>\<omega>. g \<omega> \<partial>N)"
proof -
  have bl: "bounded_linear (\<lambda>r :: real. c * r)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (auto simp: algebra_simps)
  show ?thesis by (rule integral_of_bounded_linear[OF bl g])
qed

lemma integral_pos_of_AE_pos:
  fixes f :: "'a \<Rightarrow> real"
  assumes PP: "prob_space N" and im: "integrable N f"
    and pos: "AE \<omega> in N. 0 < f \<omega>"
  shows "0 < (\<integral>\<omega>. f \<omega> \<partial>N)"
proof -
  interpret prob_space N by (rule PP)
  have fm: "f \<in> borel_measurable N" by (rule borel_measurable_integrable[OF im])
  define A where "A n = {\<omega> \<in> space N. 1 / real (Suc n) < f \<omega>}" for n
  have Am: "A n \<in> sets N" for n
    unfolding A_def using fm by measurable
  have un: "(\<Union>n. A n) = {\<omega> \<in> space N. 0 < f \<omega>}"
  proof (rule set_eqI)
    fix \<omega>
    show "\<omega> \<in> (\<Union>n. A n) \<longleftrightarrow> \<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}"
    proof
      assume "\<omega> \<in> (\<Union>n. A n)"
      then obtain n where an: "\<omega> \<in> A n" by blast
      have h1: "\<omega> \<in> space N" and h2: "1 / real (Suc n) < f \<omega>"
        using an unfolding A_def by auto
      have p0: "0 < 1 / real (Suc n)" by simp
      have "0 < f \<omega>" by (rule less_trans[OF p0 h2])
      with h1 show "\<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}" by simp
    next
      assume "\<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}"
      then obtain n where "inverse (real (Suc n)) < f \<omega>"
        using reals_Archimedean[of "f \<omega>"] by auto
      then show "\<omega> \<in> (\<Union>n. A n)"
        using \<open>\<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}\<close>
        unfolding A_def by (auto simp: inverse_eq_divide)
    qed
  qed
  have Um: "{\<omega> \<in> space N. 0 < f \<omega>} \<in> sets N" using fm by measurable
  have inA: "AE \<omega> in N. \<omega> \<in> {\<omega> \<in> space N. 0 < f \<omega>}"
    using pos AE_space by eventually_elim simp
  have p1: "prob {\<omega> \<in> space N. 0 < f \<omega>} = 1"
    using AE_in_set_eq_1[OF Um] inA by simp
  have ex: "\<exists>n. 0 < prob (A n)"
  proof (rule ccontr)
    assume "\<not> (\<exists>n. 0 < prob (A n))"
    then have z: "\<And>n. prob (A n) = 0"
      using measure_nonneg[of N] by (metis order.antisym not_le)
    have null: "A n \<in> null_sets N" for n
      using z Am by (intro null_setsI) (simp add: emeasure_eq_measure)
    have "(\<Union>n. A n) \<in> null_sets N" by (rule null_sets_UN) (rule null)
    then have "prob (\<Union>n. A n) = 0"
      by (simp add: measure_eq_0_null_sets)
    with p1 un show False by simp
  qed
  then obtain n where pn: "0 < prob (A n)" by blast
  have iind: "integrable N (\<lambda>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)))"
  proof -
    have "integrable N (indicat_real (A n))"
      by (rule integrable_real_indicator[OF Am]) (simp add: emeasure_eq_measure)
    then have "integrable N (\<lambda>\<omega>. (1 / real (Suc n)) * indicat_real (A n) \<omega>)"
      by (rule integrable_cmult)
    then show ?thesis by (simp add: ac_simps)
  qed
  have lb: "(\<integral>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<partial>N)
      \<le> (\<integral>\<omega>. f \<omega> \<partial>N)"
  proof (rule integral_mono_AE[OF iind im])
    show "AE \<omega> in N. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<le> f \<omega>"
      using pos
    proof (rule eventually_mono)
      fix \<omega> assume f0: "0 < f \<omega>"
      show "indicat_real (A n) \<omega> * (1 / real (Suc n)) \<le> f \<omega>"
      proof (cases "\<omega> \<in> A n")
        case True
        then have "1 / real (Suc n) < f \<omega>" unfolding A_def by simp
        with True show ?thesis by (simp add: indicator_def)
      next
        case False
        then show ?thesis using f0 by (simp add: indicator_def)
      qed
    qed
  qed
  have ind_int: "(\<integral>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<partial>N)
      = prob (A n) * (1 / real (Suc n))"
  proof -
    have "(\<integral>\<omega>. indicat_real (A n) \<omega> * (1 / real (Suc n)) \<partial>N)
        = (1 / real (Suc n)) * (\<integral>\<omega>. indicat_real (A n) \<omega> \<partial>N)"
      using integral_cmult[of N "indicat_real (A n)" "1 / real (Suc n)"]
        integrable_real_indicator[OF Am]
      by (simp add: ac_simps emeasure_eq_measure)
    also have "(\<integral>\<omega>. indicat_real (A n) \<omega> \<partial>N) = prob (A n)"
      using Am by simp
    finally show ?thesis by (simp add: ac_simps)
  qed
  have "0 < prob (A n) * (1 / real (Suc n))" using pn by simp
  with lb ind_int show ?thesis by simp
qed

section \<open>Measurability of the ball exit time\<close>

text \<open>\<open>pexit_path_measurable\<close> covers CLOSED targets and the ball is OPEN, so
  this cannot be inherited.  The route: with the closed set \<open>- ball x \<epsilon>\<close> as the
  hitting target, along a continuous path the sublevel event
  \<open>{\<tau> \<le> t}\<close> is (by @{thm [source] etime_le_iff}, i.e. by ATTAINMENT) the event
  that the path reaches distance \<open>\<ge> \<epsilon>\<close> somewhere on \<open>[0,t]\<close>, and by continuity
  that is decided by countably many times: the rationals of \<open>[0,t]\<close> and \<open>t\<close>
  itself.  A countable intersection of countable unions of evaluation events
  remains measurable.\<close>

lemma dist_eval_measurable:
  fixes x :: "real^'n::finite"
  shows "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x)
      \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
proof -
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    by (rule pair_law_eval_measurable[OF refl])
  have c: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). dist (fst pr) x)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show ?thesis by (rule measurable_compose[OF ev c])
qed

lemma pball_exit_le_iff_dense:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T" and t: "0 \<le> t" and tT: "t < T"
    and cont: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
  shows "pball_exit T x \<epsilon> \<omega> \<le> t \<longleftrightarrow>
     (\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x)"
proof -
  have Ac: "closed (- ball x \<epsilon> :: (real^'n) set)"
    by (simp add: closed_Compl)
  have hc: "continuous_on {0..T} (\<lambda>s. dist (fst (\<omega> s)) x)"
    by (intro continuous_on_dist cont continuous_on_const)
  show ?thesis
  proof
    assume le: "pball_exit T x \<epsilon> \<omega> \<le> t"
    then have "etime T (- ball x \<epsilon>) (\<lambda>r g. g r) (\<lambda>s. fst (\<omega> s)) \<le> t"
      by (simp add: pball_exit_def pexit_def)
    then have "\<exists>r\<in>{0..t}. fst (\<omega> r) \<in> - ball x \<epsilon>"
      using etime_le_iff[where X = "\<lambda>r g. g r" and \<omega> = "\<lambda>s. fst (\<omega> s)",
          OF T0 t tT Ac cont] by simp
    then obtain r0 where r0: "r0 \<in> {0..t}" and m0: "fst (\<omega> r0) \<notin> ball x \<epsilon>"
      by auto
    have d0: "\<epsilon> \<le> dist (fst (\<omega> r0)) x"
      using m0 by (simp add: mem_ball dist_commute)
    show "\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
    proof
      fix n :: nat
      show "\<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
          \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
      proof (cases "r0 = 0 \<or> r0 = t")
        case True
        have mem: "r0 \<in> insert t ({0..t} \<inter> \<rat>)"
          using True r0 t by (auto simp: Rats_0)
        have p1: "0 < 1 / real (Suc n)" by simp
        with d0 have "\<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r0)) x" by linarith
        with mem show ?thesis by blast
      next
        case False
        then have r00: "0 < r0" and r0t: "r0 < t" using r0 by auto
        have r0T: "r0 \<in> {0..T}" using r0 tT by auto
        have cw: "continuous (at r0 within {0..T}) (\<lambda>s. dist (fst (\<omega> s)) x)"
          using hc r0T by (simp add: continuous_on_eq_continuous_within)
        have e1: "0 < 1 / real (Suc n)" by simp
        obtain d where dd: "0 < d"
          and near: "\<And>s. s \<in> {0..T} \<Longrightarrow> dist s r0 < d \<Longrightarrow>
              dist (dist (fst (\<omega> s)) x) (dist (fst (\<omega> r0)) x) < 1 / real (Suc n)"
          using cw[unfolded continuous_within_eps_delta, rule_format, OF e1]
          by blast
        obtain q where q: "q \<in> \<rat>" and ql: "r0 - min d r0 < q" and qu: "q < r0"
          using Rats_dense_in_real[of "r0 - min d r0" r0] dd r00 by auto
        have q0: "0 \<le> q" using ql dd r00 by simp
        have qt: "q \<le> t" using qu r0t by simp
        have qT: "q \<in> {0..T}" using q0 qt tT by auto
        have "dist q r0 < d" using ql qu dd by (simp add: dist_real_def)
        then have "dist (dist (fst (\<omega> q)) x) (dist (fst (\<omega> r0)) x)
            < 1 / real (Suc n)"
          by (rule near[OF qT])
        then have "dist (fst (\<omega> r0)) x - 1 / real (Suc n) < dist (fst (\<omega> q)) x"
          by (simp add: dist_real_def abs_diff_less_iff)
        with d0 have "\<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> q)) x" by simp
        moreover have "q \<in> insert t ({0..t} \<inter> \<rat>)" using q q0 qt by auto
        ultimately show ?thesis by blast
      qed
    qed
  next
    assume H: "\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
    have "\<exists>r \<in> {0..t}. \<epsilon> \<le> dist (fst (\<omega> r)) x"
    proof -
      obtain rs where rs: "\<And>n :: nat. rs n \<in> insert t ({0..t} \<inter> \<rat>)
          \<and> \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> (rs n))) x"
        using H by metis
      have rng: "rs n \<in> {0..t}" for n using rs[of n] t by auto
      have bdd: "bounded (range rs)"
      proof (rule boundedI[of _ t])
        fix w assume "w \<in> range rs"
        then obtain n where "w = rs n" by blast
        then show "norm w \<le> t" using rng[of n] t by auto
      qed
      obtain l \<sigma> where sm: "strict_mono \<sigma>" and lim: "(rs \<circ> \<sigma>) \<longlonglongrightarrow> l"
        using bounded_imp_convergent_subsequence[OF bdd] by blast
      have inI: "(rs \<circ> \<sigma>) n \<in> {0..t}" for n using rng[of "\<sigma> n"] by simp
      have lI: "l \<in> {0..t}"
        by (rule closed_sequentially[OF closed_atLeastAtMost _ lim])
          (use inI in blast)
      have lT: "l \<in> {0..T}" using lI tT by auto
      have cl: "continuous (at l within {0..T}) (\<lambda>s. dist (fst (\<omega> s)) x)"
        using hc lT by (simp add: continuous_on_eq_continuous_within)
      have inT: "(rs \<circ> \<sigma>) n \<in> {0..T}" for n using inI[of n] tT by auto
      have tends: "(\<lambda>n. dist (fst (\<omega> ((rs \<circ> \<sigma>) n))) x)
          \<longlonglongrightarrow> dist (fst (\<omega> l)) x"
        using cl[unfolded continuous_within_sequentially, rule_format,
            of "rs \<circ> \<sigma>"] inT lim by (simp add: o_def)
      have low: "\<epsilon> - 1 / real (Suc n) \<le> dist (fst (\<omega> ((rs \<circ> \<sigma>) n))) x" for n
      proof -
        have "\<epsilon> - 1 / real (Suc (\<sigma> n)) < dist (fst (\<omega> (rs (\<sigma> n)))) x"
          using rs[of "\<sigma> n"] by blast
        moreover have "\<epsilon> - 1 / real (Suc n) \<le> \<epsilon> - 1 / real (Suc (\<sigma> n))"
          using seq_suble[OF sm, of n] by (simp add: frac_le)
        ultimately show ?thesis by (simp add: o_def)
      qed
      have lima: "(\<lambda>n. \<epsilon> - 1 / real (Suc n)) \<longlonglongrightarrow> \<epsilon>"
      proof -
        have "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
          using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
        then have "(\<lambda>n. \<epsilon> - 1 / real (Suc n)) \<longlonglongrightarrow> \<epsilon> - 0"
          by (intro tendsto_diff tendsto_const)
        then show ?thesis by simp
      qed
      have "\<epsilon> \<le> dist (fst (\<omega> l)) x"
        by (rule LIMSEQ_le[OF lima tends]) (use low in blast)
      then show ?thesis using lI by blast
    qed
    then obtain r where r: "r \<in> {0..t}" and rd: "\<epsilon> \<le> dist (fst (\<omega> r)) x"
      by blast
    have "fst (\<omega> r) \<notin> ball x \<epsilon>" using rd by (simp add: mem_ball dist_commute)
    then have "pexit T (ball x \<epsilon>) (\<lambda>s. fst (\<omega> s)) \<le> r"
      using r tT by (intro pexit_le_of_mem[OF T0]) auto
    then have "pball_exit T x \<epsilon> \<omega> \<le> r" by (simp add: pball_exit_def)
    then show "pball_exit T x \<epsilon> \<omega> \<le> t"
      using r by (auto intro: order_trans)
  qed
qed

theorem pball_exit_measurable:
  fixes x :: "real^'n::finite"
  assumes T0: "0 \<le> T"
  shows "pball_exit T x \<epsilon> \<in> borel_measurable (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
proof (rule borel_measurableI_le)
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  fix a :: real
  show "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} \<in> sets ?B"
  proof (cases "a < 0")
    case True
    have empty: "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} = {}"
    proof (rule set_eqI)
      fix \<omega> :: "'n pairpath"
      have "\<not> pball_exit T x \<epsilon> \<omega> \<le> a"
        using pball_exit_nonneg[OF T0, of x \<epsilon> \<omega>] True by linarith
      then show "\<omega> \<in> {\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
          \<longleftrightarrow> \<omega> \<in> {}" by simp
    qed
    show ?thesis unfolding empty by simp
  next
    case False
    then have a0: "0 \<le> a" by simp
    show ?thesis
    proof (cases "T \<le> a")
      case True
      have ya: "pball_exit T x \<epsilon> \<omega> \<le> a" for \<omega> :: "'n pairpath"
        using pball_exit_le[OF T0, of x \<epsilon> \<omega>] True by linarith
      then have "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} = space ?B" by auto
      then show ?thesis by (simp add: sets.top)
    next
      case False
      then have aT: "a < T" by simp
      let ?D = "insert a ({0..a} \<inter> \<rat>)"
      let ?S = "\<lambda>n r. {\<omega> \<in> space ?B. \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x}"
      have cntD: "countable ?D"
        by (intro countable_insert countable_Int2 countable_rat)
      have atom: "?S n r \<in> sets ?B" for n r
      proof -
        have "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x) \<in> borel_measurable ?B"
          by (rule dist_eval_measurable)
        then have "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x) -` {\<epsilon> - 1 / real (Suc n) <..}
            \<inter> space ?B \<in> sets ?B"
          by (rule measurable_sets) simp
        moreover have "?S n r = (\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x)
            -` {\<epsilon> - 1 / real (Suc n) <..} \<inter> space ?B"
          by auto
        ultimately show ?thesis by simp
      qed
      have eq: "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
          = (\<Inter>n. \<Union>r \<in> ?D. ?S n r)"
      proof (rule set_eqI)
        fix \<omega> :: "'n pairpath"
        show "\<omega> \<in> {\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
            \<longleftrightarrow> \<omega> \<in> (\<Inter>n. \<Union>r \<in> ?D. ?S n r)"
        proof (cases "\<omega> \<in> space ?B")
          case True
          have cw: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
            by (rule path_sets_fst_continuous[OF refl True])
          show ?thesis
            using pball_exit_le_iff_dense[OF T0 a0 aT cw, of x \<epsilon>] True
            by auto
        next
          case False
          then show ?thesis by auto
        qed
      qed
      have un_m: "(\<Union>r \<in> ?D. ?S n r) \<in> sets ?B" for n
        by (rule sets.countable_UN'[OF cntD]) (use atom in blast)
      have "(\<Inter>n. \<Union>r \<in> ?D. ?S n r) \<in> sets ?B"
        using un_m by blast
      with eq show ?thesis by metis
    qed
  qed
qed

section \<open>Up to the exit time the path stays in the closed ball\<close>

lemma pball_exit_stays_cball:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and start: "dist (fst (\<omega> 0)) x < \<epsilon>"
    and cont: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
    and s: "0 \<le> s" and sle: "s \<le> pball_exit T x \<epsilon> \<omega>"
  shows "dist (fst (\<omega> s)) x \<le> \<epsilon>"
proof (rule ccontr)
  assume "\<not> dist (fst (\<omega> s)) x \<le> \<epsilon>"
  then have gt: "\<epsilon> < dist (fst (\<omega> s)) x" by simp
  have sT: "s \<le> T" using sle pball_exit_le[OF T0] order_trans by blast
  have notin: "fst (\<omega> s) \<notin> ball x \<epsilon>"
    using gt by (simp add: mem_ball dist_commute)
  have le1: "pball_exit T x \<epsilon> \<omega> \<le> s"
    unfolding pball_exit_def
    by (rule pexit_le_of_mem[where f = "\<lambda>s. fst (\<omega> s)" and r = s
          and K = "ball x \<epsilon>", OF T0 s sT notin])
  with sle have seq: "s = pball_exit T x \<epsilon> \<omega>" by simp
  have h0: "dist (fst (\<omega> 0)) x \<le> \<epsilon>" using start by simp
  have hc: "continuous_on {0..s} (\<lambda>r. dist (fst (\<omega> r)) x)"
    by (rule continuous_on_subset[of "{0..T}"])
      (use sT in \<open>auto intro!: continuous_on_dist cont continuous_on_const\<close>)
  obtain r where r0: "0 \<le> r" and rs: "r \<le> s" and rd: "dist (fst (\<omega> r)) x = \<epsilon>"
    using IVT'[of "\<lambda>r. dist (fst (\<omega> r)) x" 0 \<epsilon> s] h0 gt s hc by auto
  have rlt: "r < s" using rd gt rs by (cases "r = s") auto
  have "fst (\<omega> r) \<notin> ball x \<epsilon>" using rd by (simp add: mem_ball dist_commute)
  then have "pball_exit T x \<epsilon> \<omega> \<le> r"
    unfolding pball_exit_def
    by (intro pexit_le_of_mem[OF T0 r0]) (use rs sT in auto)
  with rlt seq show False by simp
qed

section \<open>Optional sampling at a stopping time, via the stopped law\<close>

text \<open>The optional-sampling content was ALREADY PROVED for the DPP:
  @{thm [source] pstopped_law_horizon_component} and
  @{thm [source] pstopped_law_horizon_compensated} say the two martingale
  clauses of (1.7) survive stopping.  Reading those martingales' means at the
  horizon \<open>T\<close> --- where the stopped path IS the path at \<open>\<theta>\<close> --- and
  transporting along \<open>pair_law_of\<close> (a \<open>distr\<close>) yields the sampled means.  No
  new probabilistic content.\<close>

lemma X_eval_entry_measurable:
  "(\<lambda>p' :: 'n::finite pairpath. fst (p' u) $ c) \<in> borel_measurable
     (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof (rule measurable_compose[OF pair_law_eval_measurable[OF refl]])
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). fst pr $ c) \<in> borel_measurable borel"
    by (rule measurable_compose[OF f borel_measurable_nth])
qed

lemma comp_eval_entry_measurable:
  "(\<lambda>p' :: 'n::finite pairpath. (outerp (fst (p' u)) - snd (p' u)) $ cc $ dd)
     \<in> borel_measurable
       (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof (rule measurable_compose[OF pair_law_eval_measurable[OF refl]])
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have s: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have o: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). outerp (fst pr))
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF f outerp_borel])
  have dm: "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). outerp (fst pr) - snd pr)
      \<in> borel_measurable borel"
    by (rule borel_measurable_diff[OF o s])
  have n1: "(\<lambda>v :: real^'n^'n. v $ cc) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI)
      (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have n2: "(\<lambda>v :: real^'n. v $ dd) \<in> borel_measurable borel"
    by (rule borel_measurable_nth)
  show "(\<lambda>pr :: (real^'n) \<times> (real^'n^'n). (outerp (fst pr) - snd pr) $ cc $ dd)
      \<in> borel_measurable borel"
    by (rule measurable_compose[OF measurable_compose[OF dm n1] n2])
qed

lemma paper_pair_class_X_entry_stopped:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c)"
    and "(\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c \<partial>P) = x $ c"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have T0: "0 \<le> T" using T by simp
  have PS: "prob_space P" by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule paper_pair_class_sets[OF P])
  have P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding paper_pair_class_def by blast
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  interpret H: horizon_sq_int_martingale ?Q ?G
      "\<lambda>u p'. fst (p' (min u T)) $ c" T
    by (rule pstopped_law_horizon_component[OF T L0 P st thM])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have fm: "(\<lambda>p' :: 'n pairpath. fst (p' T) $ c) \<in> borel_measurable ?B"
    by (rule X_eval_entry_measurable)
  have iT: "integrable ?Q (\<lambda>p'. fst (p' (min T T)) $ c)"
    by (intro H.integrable) (rule T0)
  then have iT': "integrable ?Q (\<lambda>p'. fst (p' T) $ c)" by simp
  have i0: "integrable ?Q (\<lambda>p'. fst (p' (min 0 T)) $ c)"
    by (intro H.integrable) simp
  then have i0': "integrable ?Q (\<lambda>p'. fst (p' 0) $ c)" using T0 by simp
  have top: "space ?Q \<in> sets (?G 0)"
    using sets.top[of "?G 0"] by simp
  have const': "(\<integral>p'. fst (p' 0) $ c \<partial>?Q) = (\<integral>p'. fst (p' T) $ c \<partial>?Q)"
  proof -
    have s: "(\<integral>p'\<in>space ?Q. fst (p' (min 0 T)) $ c \<partial>?Q)
        = (\<integral>p'\<in>space ?Q. fst (p' (min T T)) $ c \<partial>?Q)"
      by (rule H.set_integral_eq[OF top order.refl T0])
    have e0: "(\<integral>p'\<in>space ?Q. fst (p' (min 0 T)) $ c \<partial>?Q)
        = (\<integral>p'. fst (p' (min 0 T)) $ c \<partial>?Q)"
      by (rule set_integral_space[OF i0])
    have eT: "(\<integral>p'\<in>space ?Q. fst (p' (min T T)) $ c \<partial>?Q)
        = (\<integral>p'. fst (p' (min T T)) $ c \<partial>?Q)"
      by (rule set_integral_space[OF iT])
    from s e0 eT show ?thesis using T0 by simp
  qed
  have Qst: "AE p' in ?Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    by (rule pstopped_law_start[OF T0 setsP st thM P0])
  have PQ1: "measure ?Q (space ?Q) = 1"
    using prob_space.prob_space[OF pstopped_law_prob[OF T0 PS setsP st thM]]
    by simp
  have start: "(\<integral>p'. fst (p' 0) $ c \<partial>?Q) = x $ c"
  proof -
    have "(\<integral>p'. fst (p' 0) $ c \<partial>?Q) = (\<integral>p'. x $ c \<partial>?Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0'] _])
        (use Qst in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = measure ?Q (space ?Q) *\<^sub>R (x $ c)"
      by (rule lebesgue_integral_const)
    finally show ?thesis by (simp add: PQ1)
  qed
  have peq: "(\<lambda>\<omega> :: 'n pairpath. fst (pstopped T \<theta> \<omega> T) $ c)
      = (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have "pstopped T \<theta> \<omega> T = \<omega> (min T (\<theta> \<omega>))"
      by (rule pstopped_apply) (use T0 in simp)
    also have "min T (\<theta> \<omega>) = \<theta> \<omega>" using thT[of \<omega>] by simp
    finally show "fst (pstopped T \<theta> \<omega> T) $ c = fst (\<omega> (\<theta> \<omega>)) $ c" by simp
  qed
  have QT: "(\<integral>p'. fst (p' T) $ c \<partial>?Q) = (\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c \<partial>P)"
  proof -
    have "(\<integral>p'. fst (p' T) $ c \<partial>?Q)
        = (\<integral>\<omega>. fst (pstopped T \<theta> \<omega> T) $ c \<partial>P)"
      unfolding pair_law_of_def by (rule integral_distr[OF m1 fm])
    then show ?thesis unfolding peq .
  qed
  show "integrable P (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c)"
  proof -
    have "integrable P (\<lambda>\<omega>. fst (pstopped T \<theta> \<omega> T) $ c)"
      using iT' unfolding pair_law_of_def integrable_distr_eq[OF m1 fm] .
    then show ?thesis unfolding peq .
  qed
  show "(\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) $ c \<partial>P) = x $ c"
    using const' start QT by simp
qed

lemma paper_pair_class_comp_entry_stopped:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd)"
    and "(\<integral>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd \<partial>P)
        = outerp x $ cc $ dd"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have T0: "0 \<le> T" using T by simp
  have PS: "prob_space P" by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule paper_pair_class_sets[OF P])
  have P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding paper_pair_class_def by blast
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  interpret H: horizon_sq_int_martingale ?Q ?G
      "\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ cc $ dd" T
    by (rule pstopped_law_horizon_compensated[OF T L0 P st thM])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have fm: "(\<lambda>p' :: 'n pairpath. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd)
      \<in> borel_measurable ?B"
    by (rule comp_eval_entry_measurable)
  have iT: "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd)"
    by (intro H.integrable) (rule T0)
  then have iT': "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd)" by simp
  have i0: "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd)"
    by (intro H.integrable) simp
  then have i0': "integrable ?Q
      (\<lambda>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd)" using T0 by simp
  have top: "space ?Q \<in> sets (?G 0)"
    using sets.top[of "?G 0"] by simp
  have const': "(\<integral>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd \<partial>?Q)
      = (\<integral>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd \<partial>?Q)"
  proof -
    have s: "(\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd \<partial>?Q)
        = (\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd \<partial>?Q)"
      by (rule H.set_integral_eq[OF top order.refl T0])
    have e0: "(\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd \<partial>?Q)
        = (\<integral>p'. (outerp (fst (p' (min 0 T))) - snd (p' (min 0 T))) $ cc $ dd \<partial>?Q)"
      by (rule set_integral_space[OF i0])
    have eT: "(\<integral>p'\<in>space ?Q.
          (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd \<partial>?Q)
        = (\<integral>p'. (outerp (fst (p' (min T T))) - snd (p' (min T T))) $ cc $ dd \<partial>?Q)"
      by (rule set_integral_space[OF iT])
    from s e0 eT show ?thesis using T0 by simp
  qed
  have Qst: "AE p' in ?Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    by (rule pstopped_law_start[OF T0 setsP st thM P0])
  have PQ1: "measure ?Q (space ?Q) = 1"
    using prob_space.prob_space[OF pstopped_law_prob[OF T0 PS setsP st thM]]
    by simp
  have start: "(\<integral>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd \<partial>?Q)
      = outerp x $ cc $ dd"
  proof -
    have "(\<integral>p'. (outerp (fst (p' 0)) - snd (p' 0)) $ cc $ dd \<partial>?Q)
        = (\<integral>p'. outerp x $ cc $ dd \<partial>?Q)"
      by (rule integral_cong_AE[OF borel_measurable_integrable[OF i0'] _])
        (use Qst in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = measure ?Q (space ?Q) *\<^sub>R (outerp x $ cc $ dd)"
      by (rule lebesgue_integral_const)
    finally show ?thesis by (simp add: PQ1)
  qed
  have peq: "(\<lambda>\<omega> :: 'n pairpath.
        (outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd)
      = (\<lambda>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have "pstopped T \<theta> \<omega> T = \<omega> (min T (\<theta> \<omega>))"
      by (rule pstopped_apply) (use T0 in simp)
    also have "min T (\<theta> \<omega>) = \<theta> \<omega>" using thT[of \<omega>] by simp
    finally show "(outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd
        = (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd" by simp
  qed
  have QT: "(\<integral>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd \<partial>?Q)
      = (\<integral>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd \<partial>P)"
  proof -
    have "(\<integral>p'. (outerp (fst (p' T)) - snd (p' T)) $ cc $ dd \<partial>?Q)
        = (\<integral>\<omega>. (outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd \<partial>P)"
      unfolding pair_law_of_def by (rule integral_distr[OF m1 fm])
    then show ?thesis unfolding peq .
  qed
  show "integrable P (\<lambda>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd)"
  proof -
    have "integrable P (\<lambda>\<omega>.
        (outerp (fst (pstopped T \<theta> \<omega> T)) - snd (pstopped T \<theta> \<omega> T)) $ cc $ dd)"
      using iT' unfolding pair_law_of_def integrable_distr_eq[OF m1 fm] .
    then show ?thesis unfolding peq .
  qed
  show "(\<integral>\<omega>. (outerp (fst (\<omega> (\<theta> \<omega>))) - snd (\<omega> (\<theta> \<omega>))) $ cc $ dd \<partial>P)
      = outerp x $ cc $ dd"
    using const' start QT by simp
qed

lemma paper_pair_class_Y_stopped_integrable:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. snd (\<omega> (\<theta> \<omega>)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule paper_pair_class_sets[OF P])
  have idm: "(\<lambda>\<omega> :: 'n pairpath. \<omega>) \<in> P \<rightarrow>\<^sub>M ?B"
    by (rule measurable_ident_sets[OF setsP])
  have thP: "\<theta> \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM)
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (\<theta> \<omega>)) \<in> borel_measurable P"
    by (rule path_eval_at_measurable_time[OF T0 idm thP])
      (simp_all add: path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st])
  have sm: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have m: "(\<lambda>\<omega>. snd (\<omega> (\<theta> \<omega>))) \<in> borel_measurable P"
    by (rule measurable_compose[OF ev sm])
  have bd: "AE \<omega> in P. norm (snd (\<omega> (\<theta> \<omega>))) \<le> real CARD('n) * L * T"
    using paper_pair_class_Y_bounded_ae[OF T0 L0 P]
    by (rule eventually_mono)
      (use path_stopping_time_nonneg[OF st] path_stopping_time_le[OF st] in auto)
  show ?thesis by (rule PP.integrable_const_bound[OF bd m])
qed

section \<open>The averaged covariation at a stopping time\<close>

text \<open>The weighted analogue of @{thm [source] paper_pair_class_Y_mean_sconstraint}:
  \<open>E[Y\<^sub>\<theta>] / E[\<theta>]\<close> lies in the constraint set.  Pathwise, \<open>(1/\<theta>) Y\<^sub>\<theta>\<close> is in the
  set (the diffquot clause at \<open>(0, \<theta>]\<close>); every defining condition is a linear
  inequality in the matrix, so it integrates against the weight \<open>\<theta>\<close> and
  divides by \<open>E[\<theta>] > 0\<close>.\<close>

theorem paper_pair_class_Y_stopped_mean_sconstraint:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and pos: "AE \<omega> in P. 0 < \<theta> \<omega>"
  shows "(1 / (\<integral>\<omega>. \<theta> \<omega> \<partial>P)) *\<^sub>R (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P) \<in> sconstraint k L"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Y = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (\<theta> \<omega>))"
  have T0: "0 \<le> T" using T by simp
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule paper_pair_class_sets[OF P])
  have thP: "\<theta> \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM)
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have ith: "integrable P \<theta>"
    by (rule PP.integrable_const_bound[of _ T])
      (auto simp: thP th0 thT abs_of_nonneg)
  define et where "et = (\<integral>\<omega>. \<theta> \<omega> \<partial>P)"
  have et0: "0 < et"
    unfolding et_def
    by (rule integral_pos_of_AE_pos[OF PP.prob_space_axioms ith pos])
  have iY: "integrable P ?Y"
    by (rule paper_pair_class_Y_stopped_integrable[OF T0 L0 P st thM])
  define EY where "EY = (\<integral>\<omega>. ?Y \<omega> \<partial>P)"
  define b where "b = (1 / et) *\<^sub>R EY"
  have stc: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding paper_pair_class_def by blast
  have dq: "AE \<omega> in P. \<forall>s t'. 0 \<le> s \<longrightarrow> s < t' \<longrightarrow> t' \<le> T \<longrightarrow>
      (1 / (t' - s)) *\<^sub>R (snd (\<omega> t') - snd (\<omega> s)) \<in> sconstraint k L"
    using P unfolding paper_pair_class_def by blast
  have mem: "AE \<omega> in P. (1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    using stc dq pos
  proof eventually_elim
    case (elim \<omega>)
    have "(1 / (\<theta> \<omega> - 0)) *\<^sub>R (snd (\<omega> (\<theta> \<omega>)) - snd (\<omega> 0)) \<in> sconstraint k L"
      using elim thT[of \<omega>] by blast
    then show ?case using elim by simp
  qed
  \<comment> \<open>the four weighted pathwise facts\<close>
  have memQ: "AE \<omega> in P. \<forall>z :: real^'n.
      0 \<le> z \<bullet> (?Y \<omega> *v z) \<and> z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))"
    using mem
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "(1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    then have hp: "psd ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>)"
      and hu: "eigen_ub ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) L"
      unfolding sconstraint_def Pi_constraint_def by auto
    have t0: "0 < \<theta> \<omega>" using h by simp
    show "\<forall>z :: real^'n.
        0 \<le> z \<bullet> (?Y \<omega> *v z) \<and> z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))"
    proof
      fix z :: "real^'n"
      have e: "z \<bullet> (((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) *v z) = (1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z))"
        by (simp add: scaleR_matrix_vector)
      have lo: "0 \<le> (1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z))"
        using hp unfolding psd_def e[symmetric] by blast
      have hi: "(1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z)) \<le> L * (z \<bullet> z)"
        using hu unfolding eigen_ub_def e[symmetric] by blast
      have lo': "0 \<le> z \<bullet> (?Y \<omega> *v z)"
      proof -
        have "0 \<le> \<theta> \<omega> * ((1 / \<theta> \<omega>) * (z \<bullet> (?Y \<omega> *v z)))"
          by (rule mult_nonneg_nonneg[OF less_imp_le[OF t0] lo])
        then show ?thesis using t0 by (simp add: field_simps)
      qed
      have hi': "z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))"
        using hi t0 by (simp add: field_simps)
      from lo' hi' show "0 \<le> z \<bullet> (?Y \<omega> *v z)
          \<and> z \<bullet> (?Y \<omega> *v z) \<le> \<theta> \<omega> * (L * (z \<bullet> z))" by blast
    qed
  qed
  have memT: "AE \<omega> in P. transpose (?Y \<omega>) = ?Y \<omega>"
    using mem
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "(1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    then have tr2: "transpose ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) = (1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>"
      unfolding sconstraint_def Pi_constraint_def psd_def by auto
    have tr1: "transpose ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>)
        = (1 / \<theta> \<omega>) *\<^sub>R transpose (?Y \<omega>)"
      by (simp add: transpose_def vec_eq_iff)
    have eqs: "(1 / \<theta> \<omega>) *\<^sub>R transpose (?Y \<omega>) = (1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>"
      unfolding tr1[symmetric] by (rule tr2)
    have t0: "0 < \<theta> \<omega>" using h by simp
    have nz: "1 / \<theta> \<omega> \<noteq> 0" using t0 by simp
    have entry: "transpose (?Y \<omega>) $ i $ j = ?Y \<omega> $ i $ j" for i j
    proof -
      have "((1 / \<theta> \<omega>) *\<^sub>R transpose (?Y \<omega>)) $ i $ j
          = ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) $ i $ j"
        by (rule arg_cong[where f = "\<lambda>A. A $ i $ j", OF eqs])
      then have "(1 / \<theta> \<omega>) * transpose (?Y \<omega>) $ i $ j
          = (1 / \<theta> \<omega>) * ?Y \<omega> $ i $ j"
        by (simp add: vector_scaleR_component)
      then show ?thesis using mult_left_cancel[OF nz] by blast
    qed
    show "transpose (?Y \<omega>) = ?Y \<omega>" using entry by (simp add: vec_eq_iff)
  qed
  have memPi: "AE \<omega> in P. \<forall>m Pm. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow>
      is_proj Pm \<longrightarrow> trace Pm = real m \<longrightarrow>
      real (m - k) * \<theta> \<omega> \<le> trace (?Y \<omega> ** Pm)"
    using mem
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "(1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega> \<in> sconstraint k L \<and> 0 < \<theta> \<omega>"
    then have hp: "psd ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>)"
      and hpi: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow>
          real (m - k) \<le> Pi_proj ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) m"
      unfolding sconstraint_def Pi_constraint_def by auto
    have t0: "0 < \<theta> \<omega>" using h by simp
    show "\<forall>m Pm. k < m \<longrightarrow> m \<le> CARD('n) \<longrightarrow>
        is_proj Pm \<longrightarrow> trace Pm = real m \<longrightarrow>
        real (m - k) * \<theta> \<omega> \<le> trace (?Y \<omega> ** Pm)"
    proof (intro allI impI)
      fix m and Pm :: "real^'n^'n"
      assume m: "k < m" "m \<le> CARD('n)"
        and pj: "is_proj Pm" and tp: "trace Pm = real m"
      have "real (m - k) \<le> Pi_proj ((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) m"
        by (rule hpi[OF m])
      also have "\<dots> \<le> trace (((1 / \<theta> \<omega>) *\<^sub>R ?Y \<omega>) ** Pm)"
        by (rule Pi_proj_le[OF hp pj tp])
      also have "\<dots> = (1 / \<theta> \<omega>) * trace (?Y \<omega> ** Pm)"
        by (simp add: scaleR_matrix_mult trace_scaleR)
      finally have "real (m - k) \<le> (1 / \<theta> \<omega>) * trace (?Y \<omega> ** Pm)" .
      then show "real (m - k) * \<theta> \<omega> \<le> trace (?Y \<omega> ** Pm)"
        using t0 by (simp add: field_simps)
    qed
  qed
  \<comment> \<open>integrate the four facts\<close>
  have lin: "(\<integral>\<omega>. F (?Y \<omega>) \<partial>P) = F EY"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    unfolding EY_def by (rule integral_of_bounded_linear[OF F iY])
  have linI: "integrable P (\<lambda>\<omega>. F (?Y \<omega>))"
    if F: "bounded_linear (F :: real^'n^'n \<Rightarrow> real)" for F
    by (rule integrable_bounded_linear[OF F iY])
  have qlo: "0 \<le> z \<bullet> (EY *v z)" for z :: "real^'n"
  proof -
    have "0 \<le> (\<integral>\<omega>. z \<bullet> (?Y \<omega> *v z) \<partial>P)"
      by (rule integral_nonneg_AE)
        (use memQ in \<open>auto elim: eventually_mono\<close>)
    then show ?thesis using lin[OF bounded_linear_quadform] by simp
  qed
  have qhi: "z \<bullet> (EY *v z) \<le> et * (L * (z \<bullet> z))" for z :: "real^'n"
  proof -
    have blc: "bounded_linear (\<lambda>r :: real. r * (L * (z \<bullet> z)))"
      unfolding linear_conv_bounded_linear[symmetric]
      by (intro linearI) (auto simp: algebra_simps)
    have "z \<bullet> (EY *v z) = (\<integral>\<omega>. z \<bullet> (?Y \<omega> *v z) \<partial>P)"
      using lin[OF bounded_linear_quadform] by simp
    also have "\<dots> \<le> (\<integral>\<omega>. \<theta> \<omega> * (L * (z \<bullet> z)) \<partial>P)"
      by (rule integral_mono_AE[OF linI[OF bounded_linear_quadform]
            integrable_bounded_linear[OF blc ith]])
        (use memQ in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = (\<integral>\<omega>. \<theta> \<omega> \<partial>P) * (L * (z \<bullet> z))"
      by (rule integral_of_bounded_linear[OF blc ith])
    also have "\<dots> = et * (L * (z \<bullet> z))" by (simp add: et_def)
    finally show ?thesis .
  qed
  have trE: "transpose EY = EY"
  proof -
    have "transpose EY = (\<integral>\<omega>. transpose (?Y \<omega>) \<partial>P)"
      unfolding EY_def
      by (rule integral_of_bounded_linear[OF bounded_linear_transpose iY, symmetric])
    also have "\<dots> = (\<integral>\<omega>. ?Y \<omega> \<partial>P)"
    proof (rule integral_cong_AE[OF _ _ memT])
      show "(\<lambda>\<omega>. transpose (?Y \<omega>)) \<in> borel_measurable P"
        by (rule borel_measurable_integrable
            [OF integrable_bounded_linear[OF bounded_linear_transpose iY]])
      show "?Y \<in> borel_measurable P"
        by (rule borel_measurable_integrable[OF iY])
    qed
    finally show ?thesis by (simp add: EY_def)
  qed
  have piE: "real (m - k) * et \<le> trace (EY ** Pm)"
    if m: "k < m" "m \<le> CARD('n)" and pj: "is_proj Pm" and tp: "trace Pm = real m"
    for m and Pm :: "real^'n^'n"
  proof -
    have blc: "bounded_linear (\<lambda>r :: real. real (m - k) * r)"
      unfolding linear_conv_bounded_linear[symmetric]
      by (intro linearI) (auto simp: algebra_simps)
    have "real (m - k) * et = (\<integral>\<omega>. real (m - k) * \<theta> \<omega> \<partial>P)"
      using integral_of_bounded_linear[OF blc ith] by (simp add: et_def)
    also have "\<dots> \<le> (\<integral>\<omega>. trace (?Y \<omega> ** Pm) \<partial>P)"
      by (rule integral_mono_AE[OF integrable_bounded_linear[OF blc ith]
            linI[OF bounded_linear_trace_mult_right]])
        (use memPi m pj tp in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> = trace (EY ** Pm)"
      by (rule lin[OF bounded_linear_trace_mult_right])
    finally show ?thesis .
  qed
  \<comment> \<open>assemble the membership of \<open>b\<close>\<close>
  have psdb: "psd b"
  proof -
    have "transpose b = b"
      unfolding b_def using trE by (simp add: transpose_def vec_eq_iff)
    moreover have "0 \<le> z \<bullet> (b *v z)" for z :: "real^'n"
    proof -
      have "z \<bullet> (b *v z) = (1 / et) * (z \<bullet> (EY *v z))"
        unfolding b_def by (simp add: scaleR_matrix_vector)
      then show ?thesis using qlo[of z] et0 by simp
    qed
    ultimately show ?thesis unfolding psd_def by blast
  qed
  have eubb: "eigen_ub b L"
  proof -
    have "z \<bullet> (b *v z) \<le> L * (z \<bullet> z)" for z :: "real^'n"
    proof -
      have "z \<bullet> (b *v z) = (1 / et) * (z \<bullet> (EY *v z))"
        unfolding b_def by (simp add: scaleR_matrix_vector)
      also have "\<dots> \<le> (1 / et) * (et * (L * (z \<bullet> z)))"
        using qhi[of z] et0 by (intro mult_left_mono) auto
      also have "\<dots> = L * (z \<bullet> z)" using et0 by simp
      finally show ?thesis .
    qed
    then show ?thesis unfolding eigen_ub_def by blast
  qed
  have pib: "real (m - k) \<le> Pi_proj b m"
    if m: "k < m" "m \<le> CARD('n)" for m
  proof (rule Pi_proj_ge[OF m(2)])
    fix Pm :: "real^'n^'n"
    assume pj: "is_proj Pm" and tp: "trace Pm = real m"
    have e1: "trace (b ** Pm) = (1 / et) * trace (EY ** Pm)"
      unfolding b_def by (simp add: scaleR_matrix_mult trace_scaleR)
    then have e2: "et * trace (b ** Pm) = trace (EY ** Pm)"
      using et0 by (simp add: field_simps)
    have "et * real (m - k) \<le> et * trace (b ** Pm)"
      using piE[OF m pj tp] e2 by (simp add: ac_simps)
    then show "real (m - k) \<le> trace (b ** Pm)"
      using et0 by (simp add: mult_le_cancel_left)
  qed
  have pic: "b \<in> Pi_constraint k"
    unfolding Pi_constraint_def
  proof (intro CollectI conjI allI impI)
    show "psd b" by (rule psdb)
  next
    fix m assume "k < m" and "m \<le> CARD('n)"
    then show "real (m - k) \<le> Pi_proj b m" by (rule pib)
  qed
  have "b \<in> sconstraint k L"
    unfolding sconstraint_def using pic eubb by blast
  then show ?thesis unfolding b_def EY_def et_def .
qed

section \<open>The localised subsolution inequality\<close>

text \<open>The DPP at the ball exit time, the touching used only on the CLOSED
  ball, and the exact quadratic expansion at the stopping time.  This is the
  stochastic localisation that Gap 1 required, and no remainder estimate
  appears anywhere: for a quadratic the expansion is exact at ANY bounded
  stopping time.\<close>

theorem paper_v_subsol_quadratic_ball:
  fixes K :: "(real^'n::finite) set" and x q :: "real^'n" and M :: "real^'n^'n"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and e0: "0 < \<epsilon>"
    and touch: "\<And>z. dist z x \<le> \<epsilon> \<Longrightarrow>
        enn2real (paper_v k L T K z)
          \<le> enn2real (paper_v k L T K x) + q \<bullet> (z - x)
            + ((z - x) \<bullet> (M *v (z - x))) / 2"
  obtains b where "b \<in> sconstraint k L" and "- trace (M ** b) / 2 \<le> 1"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L1 by simp
  define u where "u = (\<lambda>z :: real^'n. enn2real (paper_v k L T K z))"
  obtain P where P: "P \<in> paper_pair_class k L T x"
    and Pv: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = paper_v k L T K x"
    using paper_v_attained[OF T L1 Kc] by blast
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule paper_pair_class_sets[OF P])
  let ?th = "pball_exit T x \<epsilon>"
  let ?Xf = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (?th \<omega>))"
  let ?Yf = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (?th \<omega>))"
  have st: "path_stopping_time T ?th"
    by (rule pball_exit_path_stopping_time[OF T0])
  have thM: "?th \<in> borel_measurable ?B"
    by (rule pball_exit_measurable[OF T0])
  have thP: "?th \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM)
  have th0: "0 \<le> ?th \<omega>" for \<omega> :: "'n pairpath"
    by (rule pball_exit_nonneg[OF T0])
  have thT: "?th \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule pball_exit_le[OF T0])
  \<comment> \<open>the almost-sure facts\<close>
  have cAE: "AE \<omega> in P. u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono
      [OF ess_inf_time_AE[of P "\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have le: "paper_v k L T K x \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Pv by simp
    have "enn2real (paper_v k L T K x)
        \<le> enn2real (ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule enn2real_mono[OF le ennreal_less_top])
    then show "u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      unfolding u_def
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  have dpp: "AE \<omega> in P. u x \<le> ?th \<omega> + u (?Xf \<omega>)"
  proof (rule eventually_mono[OF paper_v_cond_ball
      [OF T0 L1 Kc P cAE, where x = x and \<epsilon> = \<epsilon>]])
    fix \<omega> :: "'n pairpath"
    assume "u x \<le> ?th \<omega> + min (enn2real (paper_v k L T K (?Xf \<omega>))) (T - ?th \<omega>)"
    moreover have "min (enn2real (paper_v k L T K (?Xf \<omega>))) (T - ?th \<omega>)
        \<le> enn2real (paper_v k L T K (?Xf \<omega>))"
      by (rule min.cobounded1)
    ultimately show "u x \<le> ?th \<omega> + u (?Xf \<omega>)" unfolding u_def by linarith
  qed
  have stc: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding paper_pair_class_def by blast
  have cwAE: "AE \<omega> in P. continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    then show ?thesis
    proof (rule eventually_mono)
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
      then show "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
        by (rule path_sets_fst_continuous[OF setsP])
    qed
  qed
  have posAE: "AE \<omega> in P. 0 < ?th \<omega>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim e0 by simp
    then show ?case using elim by (intro pball_exit_pos[OF T]) auto
  qed
  have inball: "AE \<omega> in P. dist (?Xf \<omega>) x \<le> \<epsilon>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim e0 by simp
    then show ?case
      using elim by (intro pball_exit_stays_cball[OF T0 _ _ th0 order.refl]) auto
  qed
  have key: "AE \<omega> in P. 0 \<le> ?th \<omega> + q \<bullet> (?Xf \<omega> - x)
      + ((?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))) / 2"
    using dpp inball
  proof eventually_elim
    case (elim \<omega>)
    have "u (?Xf \<omega>) \<le> u x + q \<bullet> (?Xf \<omega> - x)
        + ((?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))) / 2"
      unfolding u_def by (rule touch[OF elim(2)])
    with elim(1) show ?case by linarith
  qed
  \<comment> \<open>the integrable pieces and their means\<close>
  have ith: "integrable P ?th"
    by (rule PP.integrable_const_bound[of _ T])
      (auto simp: thP th0 thT abs_of_nonneg)
  define et where "et = (\<integral>\<omega>. ?th \<omega> \<partial>P)"
  have et0: "0 < et"
    unfolding et_def
    by (rule integral_pos_of_AE_pos[OF PP.prob_space_axioms ith posAE])
  have iXc: "integrable P (\<lambda>\<omega>. ?Xf \<omega> $ c)" for c
    using paper_pair_class_X_entry_stopped(1)[OF T L0 P st thM] .
  have EXc: "(\<integral>\<omega>. ?Xf \<omega> $ c \<partial>P) = x $ c" for c
    using paper_pair_class_X_entry_stopped(2)[OF T L0 P st thM] .
  have iCc: "integrable P (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" for cc dd
    using paper_pair_class_comp_entry_stopped(1)[OF T L0 P st thM] .
  have ECc: "(\<integral>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd \<partial>P) = outerp x $ cc $ dd"
    for cc dd
    using paper_pair_class_comp_entry_stopped(2)[OF T L0 P st thM] .
  have iY: "integrable P ?Yf"
    by (rule paper_pair_class_Y_stopped_integrable[OF T0 L0 P st thM])
  define EY where "EY = (\<integral>\<omega>. ?Yf \<omega> \<partial>P)"
  have iX: "integrable P ?Xf"
  proof -
    have "integrable P (\<lambda>\<omega>. \<chi> c. ?Xf \<omega> $ c)"
      by (intro integrable_vec_components iXc)
    then show ?thesis by simp
  qed
  have EX: "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) = x"
  proof -
    have "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) $ c = x $ c" for c
      using integral_of_bounded_linear[OF bounded_linear_vec_nth iX] EXc[of c]
      by simp
    then show ?thesis by (simp add: vec_eq_iff)
  qed
  \<comment> \<open>means of the four scalar pieces\<close>
  have ig1: "integrable P (\<lambda>\<omega>. q \<bullet> ?Xf \<omega>)"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have Eg1: "(\<integral>\<omega>. q \<bullet> ?Xf \<omega> \<partial>P) = q \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX] EX by simp
  have blM: "bounded_linear (\<lambda>w :: real^'n. M *v w)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have ig2: "integrable P (\<lambda>\<omega>. x \<bullet> (M *v ?Xf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_compose
          [OF bounded_linear_inner_right blM] iX])
  have Eg2: "(\<integral>\<omega>. x \<bullet> (M *v ?Xf \<omega>) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_compose
        [OF bounded_linear_inner_right blM] iX] EX by simp
  have ig3: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v x))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_left iX])
  have Eg3: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v x) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_inner_left iX] EX by simp
  \<comment> \<open>the quadratic term, through the compensated entries\<close>
  have icomp: "integrable P (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)))"
    unfolding trace_mult_sum
    by (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
  have Ecomp: "(\<integral>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) \<partial>P)
      = trace (M ** outerp x)"
  proof -
    have "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P)
        = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (\<Sum>j\<in>UNIV. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P))"
      by (rule Bochner_Integration.integral_sum)
        (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
        (\<integral>\<omega>. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i \<partial>P))"
      by (intro sum.cong refl Bochner_Integration.integral_sum
          integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * outerp x $ j $ i)"
    proof -
      have iCc': "integrable P (\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)"
        for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule iCc)
      qed
      have ECc': "(\<integral>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd \<partial>P)
          = outerp x $ cc $ dd" for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule ECc)
      qed
      show ?thesis
        by (intro sum.cong refl)
          (simp add: integral_cmult[OF iCc'] ECc')
    qed    finally show ?thesis unfolding trace_mult_sum .
  qed
  have itrY: "integrable P (\<lambda>\<omega>. trace (M ** ?Yf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have EtrY: "(\<integral>\<omega>. trace (M ** ?Yf \<omega>) \<partial>P) = trace (M ** EY)"
    unfolding EY_def
    by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have g4eq: "(\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))
      = (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) + trace (M ** ?Yf \<omega>))"
    by (rule ext) (simp add: trace_mult_diff trace_mult_outerp)
  have ig4: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))"
    unfolding g4eq by (intro Bochner_Integration.integrable_add icomp itrY)
  have Eg4: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) \<partial>P)
      = x \<bullet> (M *v x) + trace (M ** EY)"
    unfolding g4eq
    using Bochner_Integration.integral_add[OF icomp itrY] Ecomp EtrY
    by (simp add: trace_mult_outerp)
  \<comment> \<open>assemble the integrand\<close>
  define F where "F = (\<lambda>\<omega>. ?th \<omega> + q \<bullet> (?Xf \<omega> - x)
      + ((?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))) / 2)"
  have Fexp: "F = (\<lambda>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x)
      + (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>) - ?Xf \<omega> \<bullet> (M *v x)
         + x \<bullet> (M *v x)) / 2)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have lind: "M *v (a - b) = M *v a - M *v b" for a b :: "real^'n"
      using linear_diff[OF matrix_vector_mul_linear, of M] by simp
    show "F \<omega> = ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x)
        + (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>) - ?Xf \<omega> \<bullet> (M *v x)
           + x \<bullet> (M *v x)) / 2"
      unfolding F_def
      by (simp add: lind inner_diff_left inner_diff_right algebra_simps)
  qed
  have iq2: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
      - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x))"
    by (intro Bochner_Integration.integrable_add
        Bochner_Integration.integrable_diff ig4 ig2 ig3 PP.integrable_const)
  have bl2: "bounded_linear (\<lambda>r :: real. r / 2)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (simp_all add: field_simps)
  have ihalf: "integrable P (\<lambda>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
      - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2)"
    by (rule integrable_bounded_linear[OF bl2 iq2])
  have EF: "(\<integral>\<omega>. F \<omega> \<partial>P) = et + trace (M ** EY) / 2"
  proof -
    have Eq2: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
        - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x) \<partial>P) = trace (M ** EY)"
      using Bochner_Integration.integral_add[OF
          Bochner_Integration.integrable_diff[OF
            Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
          PP.integrable_const]
        Bochner_Integration.integral_diff[OF
          Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
        Bochner_Integration.integral_diff[OF ig4 ig2]
        Eg4 Eg2 Eg3 by (simp add: PP.prob_space)
    have E1: "(\<integral>\<omega>. q \<bullet> ?Xf \<omega> - q \<bullet> x \<partial>P) = 0"
      using Bochner_Integration.integral_diff[OF ig1 PP.integrable_const]
        Eg1 by (simp add: PP.prob_space)
    have iA: "integrable P (\<lambda>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x))"
      by (intro Bochner_Integration.integrable_add
          Bochner_Integration.integrable_diff ith ig1 PP.integrable_const)
    have "(\<integral>\<omega>. F \<omega> \<partial>P)
        = (\<integral>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x) \<partial>P)
          + (\<integral>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
             - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2 \<partial>P)"
      unfolding Fexp by (rule Bochner_Integration.integral_add[OF iA ihalf])
    also have "(\<integral>\<omega>. ?th \<omega> + (q \<bullet> ?Xf \<omega> - q \<bullet> x) \<partial>P) = et"
      using Bochner_Integration.integral_add[OF ith
          Bochner_Integration.integrable_diff[OF ig1 PP.integrable_const]]
        E1 by (simp add: et_def)
    also have "(\<integral>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
        - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2 \<partial>P) = trace (M ** EY) / 2"
    proof -
      have "(\<integral>\<omega>. (?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
          - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)) / 2 \<partial>P)
          = (\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
            - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x) \<partial>P) / 2"
        by (rule integral_of_bounded_linear[OF bl2 iq2])
      then show ?thesis using Eq2 by simp
    qed
    finally show ?thesis .
  qed
  have "0 \<le> (\<integral>\<omega>. F \<omega> \<partial>P)"
    by (rule integral_nonneg_AE) (use key in \<open>auto simp: F_def elim: eventually_mono\<close>)
  then have ge: "0 \<le> et + trace (M ** EY) / 2" unfolding EF .
  \<comment> \<open>the averaged direction\<close>
  have bmem: "(1 / et) *\<^sub>R EY \<in> sconstraint k L"
    unfolding et_def EY_def
    by (rule paper_pair_class_Y_stopped_mean_sconstraint[OF T L0 P st thM posAE])
  have EYb: "EY = et *\<^sub>R ((1 / et) *\<^sub>R EY)"
    using et0 by simp
  have trb: "trace (M ** EY) = et * trace (M ** ((1 / et) *\<^sub>R EY))"
    by (subst EYb) (rule trace_mult_scaleR)
  have "0 \<le> et * (1 + trace (M ** ((1 / et) *\<^sub>R EY)) / 2)"
    using ge trb by (simp add: field_simps)
  then have "0 \<le> 1 + trace (M ** ((1 / et) *\<^sub>R EY)) / 2"
    using et0 by (simp add: zero_le_mult_iff)
  then have w: "- trace (M ** ((1 / et) *\<^sub>R EY)) / 2 \<le> 1" by simp
  show ?thesis by (rule that[OF bmem w])
qed

section \<open>From quadratics to arbitrary test functions\<close>

text \<open>The classical reduction: a \<open>C\<^sup>1\<close> function whose gradient is
  differentiable at \<open>x\<close> is dominated, near \<open>x\<close>, by its second-order expansion
  with the Hessian bumped by \<open>\<delta>\<close>.  One-dimensional along each ray: the
  difference has nonpositive derivative, by the \<open>\<epsilon>\<close>-\<open>\<delta>\<close> form of
  differentiability of the gradient with \<open>\<epsilon> := \<delta>/2\<close>.\<close>

lemma sconstraint_trace_le:
  fixes b :: "real^'n::finite^'n"
  assumes L0: "0 \<le> L" and b: "b \<in> sconstraint k L"
  shows "trace b \<le> real CARD('n) * (real CARD('n) * L)"
proof -
  have entry: "b $ i $ i \<le> real CARD('n) * L" for i
  proof -
    have "b $ i $ i \<le> \<bar>b $ i $ i\<bar>" by simp
    also have "\<bar>b $ i $ i\<bar> = norm (b $ i $ i)" by simp
    also have "\<dots> \<le> norm (b $ i)"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> norm b"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> real CARD('n) * L"
      by (rule sconstraint_norm_le[OF L0 b])
    finally show ?thesis .
  qed
  have "trace b = (\<Sum>i\<in>UNIV. b $ i $ i)" by (simp add: trace_def)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). real CARD('n) * L)"
    by (rule sum_mono) (rule entry)
  also have "\<dots> = real CARD('n) * (real CARD('n) * L)"
    by simp
  finally show ?thesis .
qed

section \<open>Positive semidefinite forms kill their null directions\<close>

text \<open>The Cauchy--Schwarz inequality for a psd form, in the only shape Gap 2
  needs: if the form vanishes at \<open>q\<close> then \<open>q\<close> is in the kernel.\<close>

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
        by (simp add: inner_add_left inner_add_right inner_scaleR_left
            inner_scaleR_right z qa Bc_def Ac_def power2_eq_square algebra_simps)
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
        using AcP by (simp add: power2_eq_square divide_pos_pos)
      with h show False by linarith
    qed
  qed
  have "(a *v q) \<bullet> (a *v q) = 0" using cross[of "a *v q"] by simp
  then show ?thesis by simp
qed

section \<open>Sums of outer products: the toolkit\<close>

lemma onormal_subset:
  assumes B: "onormal B" and S: "S \<subseteq> B"
  shows "onormal S"
  using B S unfolding onormal_def
  by (auto intro: finite_subset pairwise_subset)

lemma matvec_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
proof -
  have "(\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z
      = (\<Sum>u\<in>S. (c u *\<^sub>R outer_prod u u) *v z)"
    by (rule matrix_vector_mult_sum)
  also have "\<dots> = (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
    by (rule sum.cong[OF refl])
      (simp add: scaleR_matrix_vector outer_prod_mv)
  finally show ?thesis .
qed

lemma quadform_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
  assumes finS: "finite S"
  shows "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z) = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"
proof -
  have "z \<bullet> ((\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u) *v z)
      = z \<bullet> (\<Sum>u\<in>S. (c u * (u \<bullet> z)) *\<^sub>R u)"
    by (simp add: matvec_sum_outer[OF finS])
  also have "\<dots> = (\<Sum>u\<in>S. z \<bullet> ((c u * (u \<bullet> z)) *\<^sub>R u))"
    by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>S. c u * (u \<bullet> z)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_scaleR_right inner_commute power2_eq_square
        algebra_simps)
  finally show ?thesis .
qed

lemma traceM_sum_outer:
  fixes S :: "(real^'n::finite) set" and c :: "real^'n \<Rightarrow> real"
    and M :: "real^'n^'n"
  shows "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
proof -
  have "M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u)
      = (\<Sum>u\<in>S. M ** (c u *\<^sub>R outer_prod u u))"
    by (rule matrix_mult_sum_right)
  then have "trace (M ** (\<Sum>u\<in>S. c u *\<^sub>R outer_prod u u))
      = (\<Sum>u\<in>S. trace (M ** (c u *\<^sub>R outer_prod u u)))"
    by (simp add: trace_matrix_sum)
  also have "\<dots> = (\<Sum>u\<in>S. c u * (u \<bullet> (M *v u)))"
  proof (rule sum.cong[OF refl])
    fix u assume "u \<in> S"
    have "trace (M ** (c u *\<^sub>R outer_prod u u))
        = c u * trace (M ** outer_prod u u)"
      by (rule trace_mult_scaleR)
    also have "trace (M ** outer_prod u u) = u \<bullet> (M *v u)"
      using trace_mult_outerp[of M u] by (simp add: outerp_eq_outer_prod)
    finally show "trace (M ** (c u *\<^sub>R outer_prod u u))
        = c u * (u \<bullet> (M *v u))" .
  qed
  finally show ?thesis .
qed

lemma trace_mult_add:
  fixes M A B :: "real^'n::finite^'n"
  shows "trace (M ** (A + B)) = trace (M ** A) + trace (M ** B)"
  by (simp add: trace_mult_sum sum.distrib algebra_simps)

lemma onormal_parseval:
  fixes B :: "(real^'n::finite) set"
  assumes B: "onormal B" and sp: "span B = UNIV"
  shows "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = z \<bullet> z"
proof -
  have finB: "finite B" by (rule onormal_finite[OF B])
  have "(\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) = (\<Sum>u\<in>B. 1 * (u \<bullet> z)\<^sup>2)" by simp
  also have "\<dots> = z \<bullet> ((\<Sum>u\<in>B. 1 *\<^sub>R outer_prod u u) *v z)"
    by (rule quadform_sum_outer[OF finB, symmetric])
  also have "(\<Sum>u\<in>B. (1::real) *\<^sub>R outer_prod u u) = (\<Sum>u\<in>B. outer_prod u u)"
    by simp
  also have "\<dots> = mat 1" by (rule onormal_complete[OF B sp])
  also have "z \<bullet> (mat 1 *v z) = z \<bullet> z" by (simp add: matrix_vector_mul_lid)
  finally show ?thesis .
qed

lemma onormal_span_parseval:
  fixes S :: "(real^'n::finite) set"
  assumes S: "onormal S" and x: "x \<in> span S"
  shows "(\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2) = x \<bullet> x"
proof -
  have finS: "finite S" by (rule onormal_finite[OF S])
  have "x \<bullet> x = x \<bullet> (\<Sum>u\<in>S. (u \<bullet> x) *\<^sub>R u)"
    by (simp add: onormal_expand[OF S x])
  also have "\<dots> = (\<Sum>u\<in>S. x \<bullet> ((u \<bullet> x) *\<^sub>R u))"
    by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_scaleR_right inner_commute power2_eq_square)
  finally show ?thesis by simp
qed

section \<open>Selecting a value-minimal index set: the threshold argument\<close>

text \<open>The linear-programming core of the face argument, done by hand: given
  weights \<open>c \<in> [0,1]\<close> with total mass \<open>\<ge> m\<close>, some set of \<open>\<ge> m\<close> indices beats
  the weighted value.  No convexity and no induction on fractional entries:
  one threshold comparison against the \<open>m\<close>-th smallest value settles it.\<close>

lemma exists_min_subset:
  fixes w :: "'a \<Rightarrow> real"
  assumes finB: "finite B"
  shows "m \<le> card B \<Longrightarrow> \<exists>S. S \<subseteq> B \<and> card S = m
      \<and> (\<forall>u\<in>S. \<forall>v\<in>B - S. w u \<le> w v)"
proof (induction m)
  case 0
  then show ?case by (intro exI[of _ "{}"]) simp
next
  case (Suc m)
  then obtain S where S: "S \<subseteq> B" "card S = m"
    and least: "\<forall>u\<in>S. \<forall>v\<in>B - S. w u \<le> w v"
    using Suc_leD by blast
  have ne: "B - S \<noteq> {}"
  proof
    assume "B - S = {}"
    then have "B \<subseteq> S" by blast
    with S(1) have "S = B" by blast
    with S(2) Suc.prems show False by simp
  qed
  have finD: "finite (B - S)" using finB by simp
  have "Min (w ` (B - S)) \<in> w ` (B - S)"
    by (intro Min_in finite_imageI finD) (use ne in blast)
  then obtain v0 where v0: "v0 \<in> B - S" and v0min: "w v0 = Min (w ` (B - S))"
    by auto
  have v0le: "\<And>v. v \<in> B - S \<Longrightarrow> w v0 \<le> w v"
    unfolding v0min by (intro Min_le finite_imageI finD) blast
  have cS: "card (insert v0 S) = Suc m"
    using S v0 finB by (simp add: card_insert_disjoint finite_subset)
  have sub: "insert v0 S \<subseteq> B" using S(1) v0 by blast
  have prp: "\<forall>u\<in>insert v0 S. \<forall>v\<in>B - insert v0 S. w u \<le> w v"
  proof (intro ballI)
    fix u v assume u: "u \<in> insert v0 S" and v: "v \<in> B - insert v0 S"
    have vBS: "v \<in> B - S" using v by blast
    show "w u \<le> w v"
    proof (cases "u = v0")
      case True
      then show ?thesis using v0le[OF vBS] by simp
    next
      case False
      then have "u \<in> S" using u by simp
      then show ?thesis using least vBS by blast
    qed
  qed
  show ?case by (intro exI[of _ "insert v0 S"]) (use cS sub prp in blast)
qed

lemma weighted_min_value:
  fixes w c :: "'a \<Rightarrow> real"
  assumes finB: "finite B" and m1: "1 \<le> m" and mB: "m \<le> card B"
    and c0: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> c u" and c1: "\<And>u. u \<in> B \<Longrightarrow> c u \<le> 1"
    and csum: "real m \<le> (\<Sum>u\<in>B. c u)"
  obtains S where "S \<subseteq> B" and "m \<le> card S"
    and "(\<Sum>u\<in>S. w u) \<le> (\<Sum>u\<in>B. c u * w u)"
proof -
  obtain S0 where S0: "S0 \<subseteq> B" and cS0: "card S0 = m"
    and least: "\<forall>u\<in>S0. \<forall>v\<in>B - S0. w u \<le> w v"
    using exists_min_subset[OF finB mB] by blast
  have finS0: "finite S0" using S0 finB by (rule finite_subset)
  have neS0: "S0 \<noteq> {}" using cS0 m1 by auto
  define Neg where "Neg = {u \<in> B. w u < 0}"
  have finNeg: "finite Neg" unfolding Neg_def using finB by simp
  define \<tau> where "\<tau> = Max (w ` S0)"
  have tauS0: "\<And>u. u \<in> S0 \<Longrightarrow> w u \<le> \<tau>"
    unfolding \<tau>_def by (intro Max_ge finite_imageI finS0) blast
  have tauout: "\<And>v. v \<in> B - S0 \<Longrightarrow> \<tau> \<le> w v"
    unfolding \<tau>_def
    by (intro Max.boundedI finite_imageI finS0)
      (use neS0 least in blast)+
  show ?thesis
  proof (cases "Neg \<subseteq> S0")
    case True
    \<comment> \<open>the threshold is \<open>max \<tau> 0\<close>; every term is compared against it\<close>
    define tp where "tp = max \<tau> 0"
    have tp0: "0 \<le> tp" by (simp add: tp_def)
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S0. c u * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * w u"] by simp
      have inS: "\<And>u. u \<in> S0 \<Longrightarrow> (c u - 1) * tp \<le> (c u - 1) * w u"
      proof -
        fix u assume u: "u \<in> S0"
        have wle: "w u \<le> tp" using tauS0[OF u] by (simp add: tp_def)
        have cle: "c u - 1 \<le> 0" using c1 S0 u by auto
        show "(c u - 1) * tp \<le> (c u - 1) * w u"
          using mult_left_mono_neg[OF wle cle] by simp
      qed
      have outS: "\<And>u. u \<in> B - S0 \<Longrightarrow> c u * tp \<le> c u * w u"
      proof -
        fix u assume u: "u \<in> B - S0"
        have w0: "0 \<le> w u" using True u unfolding Neg_def by auto
        have wge: "tp \<le> w u"
          using tauout[OF u] w0 by (simp add: tp_def)
        have c0': "0 \<le> c u" using c0 u by auto
        show "c u * tp \<le> c u * w u"
          by (rule mult_left_mono[OF wge c0'])
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S0. w u)
          = (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          \<le> (\<Sum>u\<in>S0. (c u - 1) * w u) + (\<Sum>u\<in>B - S0. c u * w u)"
        by (intro add_mono sum_mono inS outS)
      moreover have "(\<Sum>u\<in>S0. (c u - 1) * tp) + (\<Sum>u\<in>B - S0. c u * tp)
          = tp * ((\<Sum>u\<in>B. c u) - real m)"
      proof -
        have h1: "(\<Sum>u\<in>S0. (c u - 1) * tp)
            = (\<Sum>u\<in>S0. c u * tp) - real m * tp"
          by (simp add: sum_subtractf cS0 algebra_simps)
        have h2: "(\<Sum>u\<in>S0. c u * tp) + (\<Sum>u\<in>B - S0. c u * tp)
            = (\<Sum>u\<in>B. c u * tp)"
          using sum.subset_diff[OF S0 finB, of "\<lambda>u. c u * tp"] by simp
        have h3: "(\<Sum>u\<in>B. c u * tp) = (\<Sum>u\<in>B. c u) * tp"
          by (simp add: sum_distrib_right)
        show ?thesis using h1 h2 h3 by (simp add: algebra_simps)
      qed
      moreover have "0 \<le> tp * ((\<Sum>u\<in>B. c u) - real m)"
        using tp0 csum by simp
      ultimately show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S0]) (use S0 cS0 key in auto)
  next
    case False
    \<comment> \<open>a negative weight escaped the minimal set, so \<open>\<tau> < 0\<close> and taking all
      negatives on top of \<open>S0\<close> costs nothing\<close>
    obtain vn where vn: "vn \<in> Neg" "vn \<notin> S0" using False by blast
    have tneg: "\<tau> < 0"
    proof -
      have "\<tau> \<le> w vn"
        using tauout vn unfolding Neg_def by auto
      also have "w vn < 0" using vn unfolding Neg_def by auto
      finally show ?thesis .
    qed
    define S where "S = S0 \<union> Neg"
    have SB: "S \<subseteq> B" unfolding S_def Neg_def using S0 by auto
    have finS: "finite S" using SB finB by (rule finite_subset)
    have cardS: "m \<le> card S"
      unfolding S_def using cS0 card_mono[OF finS[unfolded S_def], of S0]
      by simp
    have inS: "\<And>u. u \<in> S \<Longrightarrow> w u \<le> 0"
    proof -
      fix u assume "u \<in> S"
      then consider "u \<in> S0" | "u \<in> Neg" unfolding S_def by blast
      then show "w u \<le> 0"
      proof cases
        case 1 then show ?thesis using tauS0 tneg by fastforce
      next
        case 2 then show ?thesis unfolding Neg_def by auto
      qed
    qed
    have key: "0 \<le> (\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)"
    proof -
      have split: "(\<Sum>u\<in>B. c u * w u)
          = (\<Sum>u\<in>S. c u * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        using sum.subset_diff[OF SB finB, of "\<lambda>u. c u * w u"] by simp
      have t1: "0 \<le> (\<Sum>u\<in>S. (c u - 1) * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> S"
        have c1': "c u - 1 \<le> 0" using c1 SB u by auto
        have w0: "w u \<le> 0" by (rule inS[OF u])
        show "0 \<le> (c u - 1) * w u" by (rule mult_nonpos_nonpos[OF c1' w0])
      qed
      have t2: "0 \<le> (\<Sum>u\<in>B - S. c u * w u)"
      proof (rule sum_nonneg)
        fix u assume u: "u \<in> B - S"
        have "0 \<le> w u" using u unfolding S_def Neg_def by auto
        then show "0 \<le> c u * w u" using c0 u by auto
      qed
      have "(\<Sum>u\<in>B. c u * w u) - (\<Sum>u\<in>S. w u)
          = (\<Sum>u\<in>S. (c u - 1) * w u) + (\<Sum>u\<in>B - S. c u * w u)"
        unfolding split by (simp add: sum_subtractf algebra_simps)
      with t1 t2 show ?thesis by linarith
    qed
    show ?thesis
      by (rule that[of S]) (use SB cardS key in auto)
  qed
qed

section \<open>From the convexified constraint to a feasible witness\<close>

text \<open>The step the paper never needs to make explicit.  A matrix of the
  CONVEXIFIED constraint set that kills \<open>q\<close> dominates, in any linear value, a
  matrix of the ORIGINAL feasible set of Eq. (1.9).  The construction is a
  capped spectral split: write \<open>b\<close> in its eigenbasis, cut the eigenvalues at
  \<open>1\<close>, decompose the capped part by the threshold selection --- its atoms are
  PROJECTIONS, so they carry eigenvalue cap \<open>1\<close> --- and hand the excess, which
  is bounded by \<open>L - 1\<close>, to the chosen atom.  The cap closes at
  \<open>1 + (L-1) = L\<close>, which is exactly why the split must happen at level \<open>1\<close>
  and nowhere else.  Orthogonality to \<open>q\<close> survives because every eigendirection
  that carries weight is orthogonal to \<open>q\<close> already.\<close>

theorem sconstraint_orth_feasible:
  fixes b M :: "real^'n::finite^'n" and q :: "real^'n"
  assumes kn: "k < CARD('n)" and L1: "1 \<le> L"
    and b: "b \<in> sconstraint k L" and orth: "b *v q = 0"
  obtains a where "a \<in> feasible k L q"
    and "- trace (M ** a) / 2 \<le> - trace (M ** b) / 2"
proof -
  have psd_b: "psd b" and Pi_b: "b \<in> Pi_constraint k" and ub_b: "eigen_ub b L"
    using b unfolding sconstraint_def Pi_constraint_def by auto
  have sym_b: "transpose b = b" using psd_b by (simp add: psd_def)
  obtain B :: "(real^'n) set" where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> b *v u = (u \<bullet> (b *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym_b] by blast
  have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF B])
  have finB: "finite B" by (rule onormal_finite[OF B(1)])
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (b *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_b by (simp add: lam_def psd_def)
  have lam_le: "\<And>u. u \<in> B \<Longrightarrow> lam u \<le> L"
  proof -
    fix u assume u: "u \<in> B"
    have "u \<bullet> (b *v u) \<le> L * (u \<bullet> u)"
      using ub_b unfolding eigen_ub_def by blast
    then show "lam u \<le> L"
      using onormal_inner_self[OF B(1) u] by (simp add: lam_def)
  qed
  have bdecomp: "b = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])
  \<comment> \<open>every eigendirection with weight is orthogonal to \<open>q\<close>\<close>
  have orthu: "\<And>u. u \<in> B \<Longrightarrow> lam u * (u \<bullet> q) = 0"
  proof -
    fix u assume u: "u \<in> B"
    have "u \<bullet> (b *v q) = 0" using orth by simp
    moreover have "u \<bullet> (b *v q) = (b *v u) \<bullet> q"
    proof -
      have "u \<bullet> (b *v q) = (transpose b *v u) \<bullet> q"
        by (rule inner_transpose_matrix)
      then show ?thesis using sym_b by simp
    qed
    moreover have "(b *v u) \<bullet> q = lam u * (u \<bullet> q)"
    proof -
      have "(b *v u) \<bullet> q = ((u \<bullet> (b *v u)) *\<^sub>R u) \<bullet> q"
        by (rule arg_cong[where f = "\<lambda>v. v \<bullet> q", OF eig[OF u]])
      then show ?thesis by (simp add: inner_scaleR_left lam_def)
    qed
    ultimately show "lam u * (u \<bullet> q) = 0" by simp
  qed
  define cap where "cap = (\<lambda>u :: real^'n. min (lam u) 1)"
  have cap_nn: "0 \<le> cap u" for u using lam_nn by (simp add: cap_def)
  have cap_le1: "cap u \<le> 1" for u by (simp add: cap_def)
  have cap_le_lam: "cap u \<le> lam u" for u by (simp add: cap_def)
  define m where "m = CARD('n) - k"
  have m1: "1 \<le> m" using kn by (simp add: m_def)
  have capsum: "real m \<le> (\<Sum>u\<in>B. cap u)"
    unfolding cap_def lam_def m_def
    by (rule Pi_constraint_capped_trace[OF Pi_b kn B(1) cardB eig])
  define B' where "B' = {u \<in> B. 0 < lam u}"
  have B'B: "B' \<subseteq> B" unfolding B'_def by blast
  have finB': "finite B'" using B'B finB by (rule finite_subset)
  have cap0: "\<And>u. u \<in> B - B' \<Longrightarrow> cap u = 0"
  proof -
    fix u assume "u \<in> B - B'"
    then have "lam u \<le> 0" unfolding B'_def by auto
    then have "lam u = 0" using lam_nn[of u] by simp
    then show "cap u = 0" by (simp add: cap_def)
  qed
  have capsum': "real m \<le> (\<Sum>u\<in>B'. cap u)"
  proof -
    have "(\<Sum>u\<in>B. cap u) = (\<Sum>u\<in>B'. cap u)"
      by (rule sum.mono_neutral_right[OF finB B'B]) (use cap0 in auto)
    then show ?thesis using capsum by simp
  qed
  have mB': "m \<le> card B'"
  proof -
    have "(\<Sum>u\<in>B'. cap u) \<le> (\<Sum>u\<in>B'. 1)"
      by (rule sum_mono) (rule cap_le1)
    then have "real m \<le> real (card B')" using capsum' by simp
    then show ?thesis by simp
  qed
  have orthB': "\<And>u. u \<in> B' \<Longrightarrow> u \<bullet> q = 0"
  proof -
    fix u assume u: "u \<in> B'"
    have "lam u * (u \<bullet> q) = 0" using orthu B'B u by blast
    moreover have "lam u \<noteq> 0" using u unfolding B'_def by auto
    ultimately show "u \<bullet> q = 0" by simp
  qed
  \<comment> \<open>select the value-minimal index set with the weights \<open>- u \<bullet> (M *v u)\<close>\<close>
  obtain S where SB': "S \<subseteq> B'" and cardS: "m \<le> card S"
    and Sval: "(\<Sum>u\<in>S. - (u \<bullet> (M *v u)))
        \<le> (\<Sum>u\<in>B'. cap u * - (u \<bullet> (M *v u)))"
    by (rule weighted_min_value[OF finB' m1 mB' cap_nn cap_le1 capsum'])
  have SB: "S \<subseteq> B" using SB' B'B by blast
  have finS: "finite S" using SB finB by (rule finite_subset)
  define rho where "rho = (\<lambda>u :: real^'n. lam u - cap u)"
  have rho_nn: "0 \<le> rho u" for u
    by (simp add: rho_def cap_le_lam)
  have rho_le: "\<And>u. u \<in> B \<Longrightarrow> rho u \<le> L - 1"
  proof -
    fix u assume u: "u \<in> B"
    show "rho u \<le> L - 1"
    proof (cases "lam u \<le> 1")
      case True
      then have "rho u = 0" by (simp add: rho_def cap_def)
      then show ?thesis using L1 by simp
    next
      case False
      then have "rho u = lam u - 1" by (simp add: rho_def cap_def)
      then show ?thesis using lam_le[OF u] by simp
    qed
  qed
  have rho_orth: "\<And>u. u \<in> B \<Longrightarrow> rho u * (u \<bullet> q) = 0"
  proof -
    fix u assume u: "u \<in> B"
    show "rho u * (u \<bullet> q) = 0"
    proof (cases "rho u = 0")
      case True then show ?thesis by simp
    next
      case False
      then have "lam u \<noteq> 0" by (simp add: rho_def cap_def min_def split: if_splits)
      then have "0 < lam u" using lam_nn[of u] by simp
      then have "u \<in> B'" using u unfolding B'_def by simp
      then show ?thesis using orthB' by simp
    qed
  qed
  define R where "R = (\<Sum>u\<in>B. rho u *\<^sub>R outer_prod u u)"
  define a where "a = (\<Sum>u\<in>S. outer_prod u u) + R"
  \<comment> \<open>the quadratic form of \<open>a\<close>\<close>
  have quad_a: "z \<bullet> (a *v z)
      = (\<Sum>u\<in>S. (u \<bullet> z)\<^sup>2) + (\<Sum>u\<in>B. rho u * (u \<bullet> z)\<^sup>2)" for z
  proof -
    have "a *v z = (\<Sum>u\<in>S. outer_prod u u) *v z + R *v z"
      unfolding a_def by (simp add: matrix_vector_mult_add_rdistrib)
    then have "z \<bullet> (a *v z)
        = z \<bullet> ((\<Sum>u\<in>S. outer_prod u u) *v z) + z \<bullet> (R *v z)"
      by (simp add: inner_add_right)
    moreover have "z \<bullet> ((\<Sum>u\<in>S. outer_prod u u) *v z) = (\<Sum>u\<in>S. (u \<bullet> z)\<^sup>2)"
      using quadform_sum_outer[OF finS, where c = "\<lambda>_. 1" and z = z] by simp
    moreover have "z \<bullet> (R *v z) = (\<Sum>u\<in>B. rho u * (u \<bullet> z)\<^sup>2)"
      unfolding R_def by (rule quadform_sum_outer[OF finB])
    ultimately show ?thesis by simp
  qed
  have quad_a_nn: "0 \<le> z \<bullet> (a *v z)" for z
    unfolding quad_a
    by (intro add_nonneg_nonneg sum_nonneg)
      (auto intro: mult_nonneg_nonneg rho_nn)
  have sym_a: "transpose a = a"
  proof -
    have t1: "transpose (\<Sum>u\<in>S. outer_prod u u) = (\<Sum>u\<in>S. outer_prod u u)"
      by (simp add: transpose_matrix_sum transpose_outer_prod)
    have t2: "transpose R = R"
    proof -
      have "transpose R = (\<Sum>u\<in>B. transpose (rho u *\<^sub>R outer_prod u u))"
        unfolding R_def by (rule transpose_matrix_sum)
      also have "\<dots> = (\<Sum>u\<in>B. rho u *\<^sub>R outer_prod u u)"
        by (rule sum.cong[OF refl])
          (simp add: transpose_def vec_eq_iff outer_prod_def mult.commute)
      finally show ?thesis unfolding R_def .
    qed
    have "transpose a = transpose (\<Sum>u\<in>S. outer_prod u u) + transpose R"
      unfolding a_def by (simp add: transpose_def vec_eq_iff)
    then show ?thesis unfolding a_def using t1 t2 by simp
  qed
  have psd_a: "psd a"
    unfolding psd_def using sym_a quad_a_nn by blast
  have aq: "a *v q = 0"
  proof -
    have "(\<Sum>u\<in>S. outer_prod u u) *v q = (\<Sum>u\<in>S. (1 * (u \<bullet> q)) *\<^sub>R u)"
      using matvec_sum_outer[OF finS, of "\<lambda>_. 1" q] by simp
    also have "\<dots> = 0"
      by (rule sum.neutral) (use orthB' SB' in auto)
    finally have z1: "(\<Sum>u\<in>S. outer_prod u u) *v q = 0" .
    have "R *v q = (\<Sum>u\<in>B. (rho u * (u \<bullet> q)) *\<^sub>R u)"
      unfolding R_def by (rule matvec_sum_outer[OF finB])
    also have "\<dots> = 0"
      by (rule sum.neutral) (use rho_orth in auto)
    finally have z2: "R *v q = 0" .
    show ?thesis
      unfolding a_def by (simp add: matrix_vector_mult_add_rdistrib z1 z2)
  qed
  have lb_a: "eigen_lb a (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ "span S"] conjI)
    show "subspace (span S)" by (rule subspace_span)
    have "card S = dim (span S)"
      by (rule onormal_card_dim_span[OF onormal_subset[OF B(1) SB]])
    then show "CARD('n) - k \<le> dim (span S)"
      using cardS m_def by simp
    show "\<forall>x\<in>span S. x \<bullet> x \<le> x \<bullet> (a *v x)"
    proof
      fix x assume x: "x \<in> span S"
      have "x \<bullet> x = (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2)"
        by (rule onormal_span_parseval[OF onormal_subset[OF B(1) SB] x,
              symmetric])
      also have "\<dots> \<le> (\<Sum>u\<in>S. (u \<bullet> x)\<^sup>2) + (\<Sum>u\<in>B. rho u * (u \<bullet> x)\<^sup>2)"
        by (simp add: sum_nonneg mult_nonneg_nonneg rho_nn)
      finally show "x \<bullet> x \<le> x \<bullet> (a *v x)" unfolding quad_a .
    qed
  qed
  have ub_a: "eigen_ub a L"
    unfolding eigen_ub_def
  proof
    fix z :: "real^'n"
    have "(\<Sum>u\<in>S. (u \<bullet> z)\<^sup>2) \<le> (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2)"
      by (rule sum_mono2[OF finB SB]) auto
    moreover have "(\<Sum>u\<in>B. rho u * (u \<bullet> z)\<^sup>2)
        \<le> (\<Sum>u\<in>B. (L - 1) * (u \<bullet> z)\<^sup>2)"
      by (rule sum_mono) (auto intro: mult_right_mono rho_le)
    ultimately have "z \<bullet> (a *v z)
        \<le> (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2) + (L - 1) * (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2)"
      unfolding quad_a by (simp add: sum_distrib_left)
    also have "\<dots> = L * (\<Sum>u\<in>B. (u \<bullet> z)\<^sup>2)" by (simp add: algebra_simps)
    also have "\<dots> = L * (z \<bullet> z)" by (simp add: onormal_parseval[OF B])
    finally show "z \<bullet> (a *v z) \<le> L * (z \<bullet> z)" .
  qed
  have feas: "a \<in> feasible k L q"
    unfolding feasible_def using psd_a aq lb_a ub_a by blast
  \<comment> \<open>the value comparison\<close>
  have val: "trace (M ** b) \<le> trace (M ** a)"
  proof -
    have capdec: "b = (\<Sum>u\<in>B. cap u *\<^sub>R outer_prod u u) + R"
    proof -
      have "(\<Sum>u\<in>B. cap u *\<^sub>R outer_prod u u) + R
          = (\<Sum>u\<in>B. cap u *\<^sub>R outer_prod u u + rho u *\<^sub>R outer_prod u u)"
        unfolding R_def by (rule sum.distrib[symmetric])
      also have "\<dots> = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
        by (rule sum.cong[OF refl])
          (simp add: rho_def scaleR_add_left[symmetric])
      finally show ?thesis using bdecomp by simp
    qed
    have vb: "trace (M ** b)
        = (\<Sum>u\<in>B. cap u * (u \<bullet> (M *v u))) + trace (M ** R)"
      by (subst capdec) (simp add: trace_mult_add traceM_sum_outer)
    have va: "trace (M ** a)
        = (\<Sum>u\<in>S. u \<bullet> (M *v u)) + trace (M ** R)"
    proof -
      have "trace (M ** (\<Sum>u\<in>S. outer_prod u u)) = (\<Sum>u\<in>S. u \<bullet> (M *v u))"
        using traceM_sum_outer[where M = M and S = S and c = "\<lambda>_. 1"] by simp
      then show ?thesis
        unfolding a_def by (simp add: trace_mult_add)
    qed
    have capval: "(\<Sum>u\<in>B. cap u * (u \<bullet> (M *v u)))
        = (\<Sum>u\<in>B'. cap u * (u \<bullet> (M *v u)))"
      by (rule sum.mono_neutral_right[OF finB B'B]) (use cap0 in auto)
    have "(\<Sum>u\<in>B'. cap u * (u \<bullet> (M *v u))) \<le> (\<Sum>u\<in>S. u \<bullet> (M *v u))"
    proof -
      have "- (\<Sum>u\<in>S. u \<bullet> (M *v u)) \<le> - (\<Sum>u\<in>B'. cap u * (u \<bullet> (M *v u)))"
        using Sval by (simp add: sum_negf mult_minus_right)
      then show ?thesis by simp
    qed
    then show ?thesis using vb va capval by simp
  qed
  have "- trace (M ** a) / 2 \<le> - trace (M ** b) / 2"
    using val by simp
  then show ?thesis using that feas by blast
qed

section \<open>The DPP capped at an arbitrary \<open>[0,T]\<close>-valued time\<close>

theorem paper_v_cond_at_time:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and y :: "real^'n" and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
    and P: "P \<in> paper_pair_class k L T y"
    and c: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "AE \<omega> in P. c \<le> \<theta> \<omega>
      + min (enn2real (paper_v k L T K (fst (\<omega> (\<theta> \<omega>))))) (T - \<theta> \<omega>)"
proof -
  have "AE \<omega> in P. c \<le> \<theta> \<omega>
      + enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
    by (rule paper_v_cond_time[OF T0 L1 Kc P c th0 thT])
  then show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "c \<le> \<theta> \<omega>
        + enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))"
    have a: "0 \<le> T - \<theta> \<omega>" using thT[of \<omega>] by simp
    have b: "T - \<theta> \<omega> \<le> T" using th0[of \<omega>] by simp
    have "enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
        = min (enn2real (paper_v k L T K (fst (\<omega> (\<theta> \<omega>))))) (T - \<theta> \<omega>)"
      by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
    with h show "c \<le> \<theta> \<omega>
        + min (enn2real (paper_v k L T K (fst (\<omega> (\<theta> \<omega>))))) (T - \<theta> \<omega>)"
      by simp
  qed
qed

section \<open>Small pointwise bounds\<close>

lemma quadform_abs_le:
  fixes M :: "real^'n::finite^'n" and v :: "real^'n"
  shows "\<bar>v \<bullet> (M *v v)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (norm v)\<^sup>2"
proof -
  have e: "v \<bullet> (M *v v) = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. v $ i * (M $ i $ j * v $ j))"
    by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)
  have "\<bar>v \<bullet> (M *v v)\<bar> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>v $ i * (M $ i $ j * v $ j)\<bar>)"
    unfolding e by (intro order_trans[OF sum_abs] sum_mono sum_abs)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * (norm v)\<^sup>2)"
  proof (intro sum_mono)
    fix i j :: 'n
    have vi: "\<bar>v $ i\<bar> \<le> norm v" by (rule component_le_norm_cart)
    have vj: "\<bar>v $ j\<bar> \<le> norm v" by (rule component_le_norm_cart)
    have "\<bar>v $ i * (M $ i $ j * v $ j)\<bar> = \<bar>M $ i $ j\<bar> * (\<bar>v $ i\<bar> * \<bar>v $ j\<bar>)"
      by (simp add: abs_mult algebra_simps)
    also have "\<dots> \<le> \<bar>M $ i $ j\<bar> * (norm v * norm v)"
      by (intro mult_left_mono mult_mono vi vj) auto
    finally show "\<bar>v $ i * (M $ i $ j * v $ j)\<bar>
        \<le> \<bar>M $ i $ j\<bar> * (norm v)\<^sup>2"
      by (simp add: power2_eq_square)
  qed
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * (norm v)\<^sup>2"
    by (simp add: sum_distrib_right)
  finally show ?thesis .
qed

lemma axis1_inner:
  fixes w :: "real^'n::finite"
  shows "axis i 1 \<bullet> w = w $ i"
proof -
  have "axis i 1 \<bullet> w = (\<Sum>l\<in>UNIV. axis i 1 $ l * w $ l)"
    by (simp add: inner_vec_def)
  also have "\<dots> = (\<Sum>l\<in>UNIV. if l = i then w $ l else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = w $ i" by (simp add: sum.delta)
  finally show ?thesis .
qed

lemma axis1_self:
  fixes i :: "'n::finite"
  shows "axis i 1 \<bullet> (axis i 1 :: real^'n) = (1::real)"
proof -
  have "axis i 1 \<bullet> (axis i 1 :: real^'n) = axis i 1 $ i"
    by (rule axis1_inner)
  also have "\<dots> = 1" by (simp add: axis_def)
  finally show ?thesis .
qed

lemma matvec_axis1:
  fixes a :: "real^'n::finite^'n"
  shows "(a *v axis i 1) $ l = a $ l $ i"
proof -
  have "(a *v axis i 1) $ l = (\<Sum>j\<in>UNIV. a $ l $ j * axis i 1 $ j)"
    by (simp add: matrix_vector_mult_def)
  also have "\<dots> = (\<Sum>j\<in>UNIV. if j = i then a $ l $ j else 0)"
    by (rule sum.cong[OF refl]) (simp add: axis_def)
  also have "\<dots> = a $ l $ i" by (simp add: sum.delta)
  finally show ?thesis .
qed

lemma trace_eq_sum_axis:
  fixes a :: "real^'n::finite^'n"
  shows "trace a = (\<Sum>i\<in>UNIV. axis i 1 \<bullet> (a *v axis i 1))"
proof -
  have e: "axis i 1 \<bullet> (a *v axis i 1) = a $ i $ i" for i :: 'n
    by (simp add: axis1_inner matvec_axis1)
  show ?thesis by (simp add: trace_def e)
qed

section \<open>Moments at a stopping time, assembled\<close>

lemma paper_pair_class_stopped_moments:
  fixes P :: "('n::finite pairpath) measure" and x q :: "real^'n"
    and M :: "real^'n^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows stopped_X_int: "integrable P (\<lambda>\<omega>. fst (\<omega> (\<theta> \<omega>)))"
    and stopped_X_mean: "(\<integral>\<omega>. fst (\<omega> (\<theta> \<omega>)) \<partial>P) = x"
    and stopped_lin_int: "integrable P (\<lambda>\<omega>. q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
    and stopped_lin_mean: "(\<integral>\<omega>. q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x) \<partial>P) = 0"
    and stopped_quad_int: "integrable P
      (\<lambda>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
    and stopped_quad_mean: "(\<integral>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x)
        \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)) \<partial>P)
      = trace (M ** (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P))"
proof -
  let ?Xf = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (\<theta> \<omega>))"
  let ?Yf = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (\<theta> \<omega>))"
  have T0: "0 \<le> T" using T by simp
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  have iXc: "integrable P (\<lambda>\<omega>. ?Xf \<omega> $ c)" for c
    using paper_pair_class_X_entry_stopped(1)[OF T L0 P st thM] .
  have EXc: "(\<integral>\<omega>. ?Xf \<omega> $ c \<partial>P) = x $ c" for c
    using paper_pair_class_X_entry_stopped(2)[OF T L0 P st thM] .
  have iCc: "integrable P (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" for cc dd
    using paper_pair_class_comp_entry_stopped(1)[OF T L0 P st thM] .
  have ECc: "(\<integral>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd \<partial>P) = outerp x $ cc $ dd"
    for cc dd
    using paper_pair_class_comp_entry_stopped(2)[OF T L0 P st thM] .
  have iY: "integrable P ?Yf"
    by (rule paper_pair_class_Y_stopped_integrable[OF T0 L0 P st thM])
  show iX: "integrable P ?Xf"
  proof -
    have "integrable P (\<lambda>\<omega>. \<chi> c. ?Xf \<omega> $ c)"
      by (intro integrable_vec_components iXc)
    then show ?thesis by simp
  qed
  show EX: "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) = x"
  proof -
    have "(\<integral>\<omega>. ?Xf \<omega> \<partial>P) $ c = x $ c" for c
      using integral_of_bounded_linear[OF bounded_linear_vec_nth iX] EXc[of c]
      by simp
    then show ?thesis by (simp add: vec_eq_iff)
  qed
  have ig1: "integrable P (\<lambda>\<omega>. q \<bullet> ?Xf \<omega>)"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_right iX])
  have Eg1: "(\<integral>\<omega>. q \<bullet> ?Xf \<omega> \<partial>P) = q \<bullet> x"
    using integral_of_bounded_linear[OF bounded_linear_inner_right iX] EX
    by simp
  have lin_eq: "(\<lambda>\<omega>. q \<bullet> (?Xf \<omega> - x)) = (\<lambda>\<omega>. q \<bullet> ?Xf \<omega> - q \<bullet> x)"
    by (simp add: fun_eq_iff inner_diff_right)
  show "integrable P (\<lambda>\<omega>. q \<bullet> (?Xf \<omega> - x))"
    unfolding lin_eq
    by (intro Bochner_Integration.integrable_diff ig1 PP.integrable_const)
  show "(\<integral>\<omega>. q \<bullet> (?Xf \<omega> - x) \<partial>P) = 0"
    unfolding lin_eq
    using Bochner_Integration.integral_diff[OF ig1 PP.integrable_const] Eg1
    by (simp add: PP.prob_space)
  \<comment> \<open>the quadratic part, through the compensated entries\<close>
  have blM: "bounded_linear (\<lambda>w :: real^'n. M *v w)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (rule matrix_vector_mul_linear)
  have ig2: "integrable P (\<lambda>\<omega>. x \<bullet> (M *v ?Xf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_compose
          [OF bounded_linear_inner_right blM] iX])
  have Eg2: "(\<integral>\<omega>. x \<bullet> (M *v ?Xf \<omega>) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_compose
        [OF bounded_linear_inner_right blM] iX] EX by simp
  have ig3: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v x))"
    by (rule integrable_bounded_linear[OF bounded_linear_inner_left iX])
  have Eg3: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v x) \<partial>P) = x \<bullet> (M *v x)"
    using integral_of_bounded_linear[OF bounded_linear_inner_left iX] EX
    by simp
  have icomp: "integrable P (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)))"
    unfolding trace_mult_sum
    by (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
  have Ecomp: "(\<integral>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) \<partial>P)
      = trace (M ** outerp x)"
  proof -
    have "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
          M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P)
        = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (\<Sum>j\<in>UNIV.
            M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i) \<partial>P))"
      by (rule Bochner_Integration.integral_sum)
        (intro Bochner_Integration.integrable_sum integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
        (\<integral>\<omega>. M $ i $ j * (outerp (?Xf \<omega>) - ?Yf \<omega>) $ j $ i \<partial>P))"
      by (intro sum.cong refl Bochner_Integration.integral_sum
          integrable_cmult iCc)
    also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j * outerp x $ j $ i)"
    proof -
      have iCc': "integrable P
          (\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)" for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule iCc)
      qed
      have ECc': "(\<integral>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd \<partial>P)
          = outerp x $ cc $ dd" for cc dd
      proof -
        have e: "(\<lambda>\<omega>. outerp (?Xf \<omega>) $ cc $ dd - ?Yf \<omega> $ cc $ dd)
            = (\<lambda>\<omega>. (outerp (?Xf \<omega>) - ?Yf \<omega>) $ cc $ dd)" by simp
        show ?thesis unfolding e by (rule ECc)
      qed
      show ?thesis
        by (intro sum.cong refl)
          (simp add: integral_cmult[OF iCc'] ECc')
    qed
    finally show ?thesis unfolding trace_mult_sum .
  qed
  have itrY: "integrable P (\<lambda>\<omega>. trace (M ** ?Yf \<omega>))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have EtrY: "(\<integral>\<omega>. trace (M ** ?Yf \<omega>) \<partial>P)
      = trace (M ** (\<integral>\<omega>. ?Yf \<omega> \<partial>P))"
    by (rule integral_of_bounded_linear[OF bounded_linear_trace_mult_left iY])
  have g4eq: "(\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))
      = (\<lambda>\<omega>. trace (M ** (outerp (?Xf \<omega>) - ?Yf \<omega>)) + trace (M ** ?Yf \<omega>))"
    by (rule ext) (simp add: trace_mult_diff trace_mult_outerp)
  have ig4: "integrable P (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>))"
    unfolding g4eq by (intro Bochner_Integration.integrable_add icomp itrY)
  have Eg4: "(\<integral>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) \<partial>P)
      = x \<bullet> (M *v x) + trace (M ** (\<integral>\<omega>. ?Yf \<omega> \<partial>P))"
    unfolding g4eq
    using Bochner_Integration.integral_add[OF icomp itrY] Ecomp EtrY
    by (simp add: trace_mult_outerp)
  have quad_eq: "(\<lambda>\<omega>. (?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x)))
      = (\<lambda>\<omega>. ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
          - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x))"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have lind: "M *v (a - b) = M *v a - M *v b" for a b :: "real^'n"
      using linear_diff[OF matrix_vector_mul_linear, of M] by simp
    show "(?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x))
        = ?Xf \<omega> \<bullet> (M *v ?Xf \<omega>) - x \<bullet> (M *v ?Xf \<omega>)
          - ?Xf \<omega> \<bullet> (M *v x) + x \<bullet> (M *v x)"
      by (simp add: lind inner_diff_left inner_diff_right algebra_simps)
  qed
  show "integrable P (\<lambda>\<omega>. (?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x)))"
    unfolding quad_eq
    by (intro Bochner_Integration.integrable_add
        Bochner_Integration.integrable_diff ig4 ig2 ig3 PP.integrable_const)
  show "(\<integral>\<omega>. (?Xf \<omega> - x) \<bullet> (M *v (?Xf \<omega> - x)) \<partial>P)
      = trace (M ** (\<integral>\<omega>. ?Yf \<omega> \<partial>P))"
    unfolding quad_eq
    using Bochner_Integration.integral_add[OF
        Bochner_Integration.integrable_diff[OF
          Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
        PP.integrable_const]
      Bochner_Integration.integral_diff[OF
        Bochner_Integration.integrable_diff[OF ig4 ig2] ig3]
      Bochner_Integration.integral_diff[OF ig4 ig2]
      Eg4 Eg2 Eg3 by (simp add: PP.prob_space)
qed

lemma paper_pair_class_stopped_var:
  fixes P :: "('n::finite pairpath) measure" and x q :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2)"
    and "(\<integral>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2 \<partial>P)
      = q \<bullet> ((\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P) *v q)"
proof -
  have e: "(\<lambda>\<omega> :: 'n pairpath. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2)
      = (\<lambda>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (outerp q *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
    by (rule ext) (simp add: quadform_outerp)
  show "integrable P (\<lambda>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2)"
    unfolding e
    by (rule paper_pair_class_stopped_moments(5)[OF T L0 P st thM])
  have "(\<integral>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2 \<partial>P)
      = trace (outerp q ** (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P))"
    unfolding e
    by (rule paper_pair_class_stopped_moments(6)[OF T L0 P st thM])
  then show "(\<integral>\<omega>. (q \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))\<^sup>2 \<partial>P)
      = q \<bullet> ((\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P) *v q)"
    by (simp add: trace_outerp_mult)
qed

lemma paper_pair_class_stopped_normsq:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L" and P: "P \<in> paper_pair_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(\<integral>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x) \<partial>P)
      = trace (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P)"
proof -
  have e: "(\<lambda>\<omega> :: 'n pairpath.
      (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))
      = (\<lambda>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (mat 1 *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
    by (simp add: fun_eq_iff matrix_vector_mul_lid)
  have "(\<integral>\<omega>. (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x) \<partial>P)
      = trace (mat 1 ** (\<integral>\<omega>. snd (\<omega> (\<theta> \<omega>)) \<partial>P))"
    unfolding e
    by (rule paper_pair_class_stopped_moments(6)[OF T L0 P st thM])
  then show ?thesis by (simp add: matrix_mul_lid)
qed

section \<open>The near-orthogonal direction: the anti-concentration dichotomy\<close>

text \<open>The Girsanov-free replacement for the paper's exponential martingale
  ((3.18)--(3.19)).  The DPP + touching inequality is ALMOST SURE, so if the
  averaged covariation kept variance \<open>\<ge> \<epsilon>\<^sub>0\<close> in the gradient direction, the
  martingale \<open>q \<bullet> X\<close> would take a negative value larger than the entire
  drift-plus-curvature budget \<open>t + C\<epsilon>\<^sup>2/2\<close> on a set of positive measure ---
  contradiction.  The quantitative form needs no fourth moment: the stopped
  increment is BOUNDED by \<open>\<bar>q\<bar>\<epsilon>\<close>, so a bare indicator split gives the
  anti-concentration, and the scaling \<open>t := \<epsilon>\<^sup>2/(2nL)\<close> closes the loop.\<close>

theorem paper_v_touch_near_orth:
  fixes K :: "(real^'n::finite) set" and x q :: "real^'n" and M :: "real^'n^'n"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and eb: "0 < ebar"
    and touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (paper_v k L T K z)
          \<le> enn2real (paper_v k L T K x) + q \<bullet> (z - x)
            + ((z - x) \<bullet> (M *v (z - x))) / 2"
    and e0: "0 < \<epsilon>\<^sub>0"
  obtains b where "b \<in> sconstraint k L" and "- trace (M ** b) / 2 \<le> 1"
    and "q \<bullet> (b *v q) < \<epsilon>\<^sub>0"
proof (cases "q = 0")
  case True
  obtain b where bmem: "b \<in> sconstraint k L"
    and w: "- trace (M ** b) / 2 \<le> 1"
    by (rule paper_v_subsol_quadratic_ball[OF T L1 Kc eb touch])
  have "q \<bullet> (b *v q) < \<epsilon>\<^sub>0" using True e0 by simp
  then show ?thesis using that bmem w by blast
next
  case False
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L1 by simp
  define nq where "nq = norm q"
  have nq0: "0 < nq" using False by (simp add: nq_def)
  define n' where "n' = real CARD('n)"
  have n'1: "1 \<le> n'" unfolding n'_def
    using zero_less_card_finite[where 'a = 'n]
    by (simp add: Suc_leI of_nat_le_iff [symmetric])
  define Cm where "Cm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  have Cm0: "0 \<le> Cm" unfolding Cm_def by (intro sum_nonneg) auto
  define \<beta> where "\<beta> = 1 / (2 * n' * n' * L)"
  have b0: "0 < \<beta>" unfolding \<beta>_def using n'1 L1 by simp
  define \<epsilon>K where "\<epsilon>K = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta>
      / (16 * nq\<^sup>2 * (\<beta> + Cm / 2))"
  have den0: "0 < 16 * nq\<^sup>2 * (\<beta> + Cm / 2)"
    using nq0 b0 Cm0 by (simp add: power2_eq_square)
  have eK0: "0 < \<epsilon>K"
    unfolding \<epsilon>K_def using e0 b0 den0 by (simp add: divide_pos_pos)
  define \<epsilon> where "\<epsilon> = min ebar (min (sqrt (T / \<beta>)) (\<epsilon>K / 2))"
  have eps0: "0 < \<epsilon>"
    unfolding \<epsilon>_def using eb T b0 eK0 by simp
  have epseb: "\<epsilon> \<le> ebar" unfolding \<epsilon>_def by simp
  have epsK: "\<epsilon> \<le> \<epsilon>K / 2" unfolding \<epsilon>_def by simp
  define t where "t = \<beta> * \<epsilon>\<^sup>2"
  have t0: "0 < t" unfolding t_def using b0 eps0 by simp
  have tT: "t \<le> T"
  proof -
    have "\<epsilon> \<le> sqrt (T / \<beta>)" unfolding \<epsilon>_def by simp
    then have "\<epsilon>\<^sup>2 \<le> (sqrt (T / \<beta>))\<^sup>2"
      using eps0 by (intro power_mono) auto
    also have "\<dots> = T / \<beta>" using T b0 by simp
    finally show ?thesis unfolding t_def using b0 by (simp add: field_simps)
  qed
  define \<theta>' where "\<theta>' = (\<lambda>\<omega> :: 'n pairpath. min t (pball_exit T x \<epsilon> \<omega>))"
  have st': "path_stopping_time T \<theta>'"
    unfolding \<theta>'_def
    by (rule path_stopping_time_min[OF pball_exit_path_stopping_time[OF T0]])
      (use t0 tT in auto)
  have thM': "\<theta>' \<in> borel_measurable ?B"
    unfolding \<theta>'_def
    by (intro borel_measurable_min borel_measurable_const
        pball_exit_measurable[OF T0])
  have th0': "0 \<le> \<theta>' \<omega>" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def using t0 pball_exit_nonneg[OF T0, of x \<epsilon> \<omega>] by simp
  have thT': "\<theta>' \<omega> \<le> T" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def using tT by simp
  have thle: "\<theta>' \<omega> \<le> pball_exit T x \<epsilon> \<omega>" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def by (rule min.cobounded2)
  have tht: "\<theta>' \<omega> \<le> t" for \<omega> :: "'n pairpath"
    unfolding \<theta>'_def by (rule min.cobounded1)
  define u where "u = (\<lambda>z :: real^'n. enn2real (paper_v k L T K z))"
  obtain P where P: "P \<in> paper_pair_class k L T x"
    and Pv: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = paper_v k L T K x"
    using paper_v_attained[OF T L1 Kc] by blast
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule paper_pair_class_sets[OF P])
  have thP': "\<theta>' \<in> borel_measurable P"
    unfolding measurable_cong_sets[OF setsP refl] by (rule thM')
  let ?Xf = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (\<theta>' \<omega>))"
  let ?Yf = "\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (\<theta>' \<omega>))"
  let ?V = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (\<theta>' \<omega>)) - x"
  \<comment> \<open>the almost-sure facts\<close>
  have cAE: "AE \<omega> in P. u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono
      [OF ess_inf_time_AE[of P "\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))"]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    then have le: "paper_v k L T K x \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Pv by simp
    have "enn2real (paper_v k L T K x)
        \<le> enn2real (ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))"
      by (rule enn2real_mono[OF le ennreal_less_top])
    then show "u x \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
      unfolding u_def
      using pexit_nonneg[OF T0, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  have dpp: "AE \<omega> in P. u x \<le> \<theta>' \<omega> + u (?Xf \<omega>)"
  proof (rule eventually_mono
      [OF paper_v_cond_at_time[OF T0 L1 Kc P cAE th0' thT']])
    fix \<omega> :: "'n pairpath"
    assume "u x \<le> \<theta>' \<omega>
        + min (enn2real (paper_v k L T K (?Xf \<omega>))) (T - \<theta>' \<omega>)"
    moreover have "min (enn2real (paper_v k L T K (?Xf \<omega>))) (T - \<theta>' \<omega>)
        \<le> enn2real (paper_v k L T K (?Xf \<omega>))"
      by (rule min.cobounded1)
    ultimately show "u x \<le> \<theta>' \<omega> + u (?Xf \<omega>)"
      unfolding u_def by linarith
  qed
  have stc: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using P unfolding paper_pair_class_def by blast
  have cwAE: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    then show ?thesis
    proof (rule eventually_mono)
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
      then show "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
        by (rule path_sets_fst_continuous[OF setsP])
    qed
  qed
  have posAE: "AE \<omega> in P. 0 < \<theta>' \<omega>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim eps0 by simp
    then have "0 < pball_exit T x \<epsilon> \<omega>"
      using elim by (intro pball_exit_pos[OF T]) auto
    then show ?case unfolding \<theta>'_def using t0 by simp
  qed
  have inball: "AE \<omega> in P. dist (?Xf \<omega>) x \<le> \<epsilon>"
    using stc cwAE
  proof eventually_elim
    case (elim \<omega>)
    have "dist (fst (\<omega> 0)) x < \<epsilon>" using elim eps0 by simp
    then show ?case
      using elim
      by (intro pball_exit_stays_cball[OF T0 _ _ th0' thle]) auto
  qed
  have key: "AE \<omega> in P. 0 \<le> \<theta>' \<omega> + q \<bullet> (?V \<omega>)
      + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2"
    using dpp inball
  proof eventually_elim
    case (elim \<omega>)
    have "dist (?Xf \<omega>) x \<le> ebar" using elim(2) epseb by simp
    then have "u (?Xf \<omega>) \<le> u x + q \<bullet> (?V \<omega>)
        + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2"
      unfolding u_def by (rule touch)
    with elim(1) show ?case by linarith
  qed
  \<comment> \<open>moments at the stopping time\<close>
  define EY where "EY = (\<integral>\<omega>. ?Yf \<omega> \<partial>P)"
  define et where "et = (\<integral>\<omega>. \<theta>' \<omega> \<partial>P)"
  have ith: "integrable P \<theta>'"
    by (rule PP.integrable_const_bound[of _ T])
      (auto simp: thP' th0' thT' abs_of_nonneg)
  have et0: "0 < et"
    unfolding et_def
    by (rule integral_pos_of_AE_pos[OF PP.prob_space_axioms ith posAE])
  have ett: "et \<le> t"
    unfolding et_def
    using integral_mono_AE[OF ith PP.integrable_const, of t] tht
    by (simp add: PP.prob_space)
  have iY: "integrable P ?Yf"
    by (rule paper_pair_class_Y_stopped_integrable[OF T0 L0 P st' thM'])
  have bmem: "(1 / et) *\<^sub>R EY \<in> sconstraint k L"
    unfolding et_def EY_def
    by (rule paper_pair_class_Y_stopped_mean_sconstraint
        [OF T L0 P st' thM' posAE])
  define b where "b = (1 / et) *\<^sub>R EY"
  have EYb: "EY = et *\<^sub>R b" unfolding b_def using et0 by simp
  \<comment> \<open>the value inequality\<close>
  have ilin: "integrable P (\<lambda>\<omega>. q \<bullet> (?V \<omega>))"
    by (rule paper_pair_class_stopped_moments(3)[OF T L0 P st' thM'])
  have Elin: "(\<integral>\<omega>. q \<bullet> (?V \<omega>) \<partial>P) = 0"
    by (rule paper_pair_class_stopped_moments(4)[OF T L0 P st' thM'])
  have iquad: "integrable P (\<lambda>\<omega>. (?V \<omega>) \<bullet> (M *v (?V \<omega>)))"
    by (rule paper_pair_class_stopped_moments(5)[OF T L0 P st' thM'])
  have Equad: "(\<integral>\<omega>. (?V \<omega>) \<bullet> (M *v (?V \<omega>)) \<partial>P) = trace (M ** EY)"
    unfolding EY_def
    by (rule paper_pair_class_stopped_moments(6)[OF T L0 P st' thM'])
  have bl2: "bounded_linear (\<lambda>r :: real. r / 2)"
    unfolding linear_conv_bounded_linear[symmetric]
    by (intro linearI) (simp_all add: field_simps)
  have ihalf: "integrable P (\<lambda>\<omega>. ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2)"
    by (rule integrable_bounded_linear[OF bl2 iquad])
  have Ehalf: "(\<integral>\<omega>. ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2 \<partial>P)
      = trace (M ** EY) / 2"
    using integral_of_bounded_linear[OF bl2 iquad] Equad by simp
  have w: "- trace (M ** b) / 2 \<le> 1"
  proof -
    have iA: "integrable P (\<lambda>\<omega>. \<theta>' \<omega> + q \<bullet> (?V \<omega>))"
      by (intro Bochner_Integration.integrable_add ith ilin)
    have "0 \<le> (\<integral>\<omega>. \<theta>' \<omega> + q \<bullet> (?V \<omega>)
        + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2 \<partial>P)"
      by (rule integral_nonneg_AE) (use key in \<open>auto elim: eventually_mono\<close>)
    also have "(\<integral>\<omega>. \<theta>' \<omega> + q \<bullet> (?V \<omega>)
        + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2 \<partial>P)
        = et + trace (M ** EY) / 2"
      using Bochner_Integration.integral_add[OF iA ihalf]
        Bochner_Integration.integral_add[OF ith ilin] Elin Ehalf
      by (simp add: et_def)
    finally have ge: "0 \<le> et + trace (M ** EY) / 2" .
    have trb: "trace (M ** EY) = et * trace (M ** b)"
      by (subst EYb) (rule trace_mult_scaleR)
    have "0 \<le> et * (1 + trace (M ** b) / 2)"
      using ge trb by (simp add: field_simps)
    then have "0 \<le> 1 + trace (M ** b) / 2"
      using et0 by (simp add: zero_le_mult_iff)
    then show ?thesis by simp
  qed
  \<comment> \<open>the martingale increment and its moments\<close>
  define W where "W = (\<lambda>\<omega> :: 'n pairpath. q \<bullet> (?V \<omega>))"
  have Wint: "integrable P W" unfolding W_def by (rule ilin)
  have Wmean: "(\<integral>\<omega>. W \<omega> \<partial>P) = 0" unfolding W_def by (rule Elin)
  have Wm: "W \<in> borel_measurable P"
    by (rule borel_measurable_integrable[OF Wint])
  have W2int: "integrable P (\<lambda>\<omega>. (W \<omega>)\<^sup>2)"
    unfolding W_def
    by (rule paper_pair_class_stopped_var(1)[OF T L0 P st' thM'])
  define s where "s = (\<integral>\<omega>. (W \<omega>)\<^sup>2 \<partial>P)"
  have svar: "s = q \<bullet> (EY *v q)"
    unfolding s_def W_def EY_def
    by (rule paper_pair_class_stopped_var(2)[OF T L0 P st' thM'])
  have s0: "0 \<le> s"
    unfolding s_def by (rule integral_nonneg_AE) auto
  have Wabs: "AE \<omega> in P. \<bar>W \<omega>\<bar> \<le> nq * \<epsilon>"
    using inball
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "dist (?Xf \<omega>) x \<le> \<epsilon>"
    have "\<bar>W \<omega>\<bar> \<le> norm q * norm (?V \<omega>)"
      unfolding W_def by (rule Cauchy_Schwarz_ineq2)
    also have "norm (?V \<omega>) = dist (?Xf \<omega>) x" by (simp add: dist_norm)
    also have "norm q * dist (?Xf \<omega>) x \<le> norm q * \<epsilon>"
      by (rule mult_left_mono[OF h norm_ge_zero])
    finally show "\<bar>W \<omega>\<bar> \<le> nq * \<epsilon>" unfolding nq_def .
  qed
  \<comment> \<open>the negative part is small\<close>
  have negbnd: "AE \<omega> in P. max (- W \<omega>) 0 \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
    using key inball
  proof eventually_elim
    case (elim \<omega>)
    have q1: "\<bar>(?V \<omega>) \<bullet> (M *v (?V \<omega>))\<bar> \<le> Cm * \<epsilon>\<^sup>2"
    proof -
      have nv2: "(norm (?V \<omega>))\<^sup>2 \<le> \<epsilon>\<^sup>2"
        using elim(2) by (intro power_mono) (auto simp: dist_norm)
      have "\<bar>(?V \<omega>) \<bullet> (M *v (?V \<omega>))\<bar> \<le> Cm * (norm (?V \<omega>))\<^sup>2"
        unfolding Cm_def by (rule quadform_abs_le)
      also have "\<dots> \<le> Cm * \<epsilon>\<^sup>2"
        by (rule mult_left_mono[OF nv2 Cm0])
      finally show ?thesis .
    qed
    have "- W \<omega> \<le> \<theta>' \<omega> + ((?V \<omega>) \<bullet> (M *v (?V \<omega>))) / 2"
      using elim(1) unfolding W_def by linarith
    also have "\<dots> \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
      using tht[of \<omega>] q1 by linarith
    finally have h: "- W \<omega> \<le> t + Cm * \<epsilon>\<^sup>2 / 2" .
    have "0 \<le> t + Cm * \<epsilon>\<^sup>2 / 2" using t0 Cm0 by simp
    with h show ?case by simp
  qed
  have nqe0: "0 \<le> nq * \<epsilon>" using nq0 eps0 by simp
  have inegint: "integrable P (\<lambda>\<omega>. max (- W \<omega>) 0)"
    by (rule PP.integrable_const_bound[of _ "nq * \<epsilon>"])
      (use Wabs Wm nqe0 in \<open>auto elim: eventually_mono\<close>)
  have iposint: "integrable P (\<lambda>\<omega>. max (W \<omega>) 0)"
    by (rule PP.integrable_const_bound[of _ "nq * \<epsilon>"])
      (use Wabs Wm nqe0 in \<open>auto elim: eventually_mono\<close>)
  have iabs: "integrable P (\<lambda>\<omega>. \<bar>W \<omega>\<bar>)"
    by (rule integrable_abs[OF Wint])
  have negE: "(\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P) \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
    using integral_mono_AE[OF inegint PP.integrable_const negbnd]
    by (simp add: PP.prob_space)
  have halfabs: "(\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P) = 2 * (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
  proof -
    have d1: "(\<lambda>\<omega>. W \<omega>) = (\<lambda>\<omega>. max (W \<omega>) 0 - max (- W \<omega>) 0)"
      by (rule ext) (simp add: max_def)
    have d2: "(\<lambda>\<omega>. \<bar>W \<omega>\<bar>) = (\<lambda>\<omega>. max (W \<omega>) 0 + max (- W \<omega>) 0)"
      by (rule ext) (simp add: max_def abs_if)
    have "(\<integral>\<omega>. W \<omega> \<partial>P)
        = (\<integral>\<omega>. max (W \<omega>) 0 \<partial>P) - (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
      by (subst d1) (rule Bochner_Integration.integral_diff[OF iposint inegint])
    with Wmean have posneg:
      "(\<integral>\<omega>. max (W \<omega>) 0 \<partial>P) = (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
      by simp
    have "(\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)
        = (\<integral>\<omega>. max (W \<omega>) 0 \<partial>P) + (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
      unfolding d2 by (rule Bochner_Integration.integral_add[OF iposint inegint])
    then show ?thesis using posneg by simp
  qed
  \<comment> \<open>anti-concentration from boundedness\<close>
  define A where "A = {\<omega> \<in> space P. sqrt (s / 2) \<le> \<bar>W \<omega>\<bar>}"
  have Am: "A \<in> sets P" unfolding A_def using Wm by measurable
  have W2b: "AE \<omega> in P. (W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2"
    using Wabs
  proof (rule eventually_mono)
    fix \<omega> assume h: "\<bar>W \<omega>\<bar> \<le> nq * \<epsilon>"
    have "\<bar>W \<omega>\<bar>\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2" by (rule power_mono[OF h abs_ge_zero])
    then show "(W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2" by simp
  qed
  have W2A_int: "integrable P (\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega>)"
  proof (rule PP.integrable_const_bound[of _ "(nq * \<epsilon>)\<^sup>2"])
    show "AE \<omega> in P. norm ((W \<omega>)\<^sup>2 * indicat_real A \<omega>) \<le> (nq * \<epsilon>)\<^sup>2"
      using W2b
    proof (rule eventually_mono)
      fix \<omega> assume h: "(W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2"
      have "(W \<omega>)\<^sup>2 * indicat_real A \<omega> \<le> (W \<omega>)\<^sup>2 * 1"
        by (intro mult_left_mono) (auto simp: indicator_def)
      then show "norm ((W \<omega>)\<^sup>2 * indicat_real A \<omega>) \<le> (nq * \<epsilon>)\<^sup>2"
        using h by (auto simp: abs_mult indicator_def)
    qed
    show "(\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega>) \<in> borel_measurable P"
      using Wm Am by measurable
  qed
  have W2Ac_int: "integrable P
      (\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>)"
  proof (rule PP.integrable_const_bound[of _ "(nq * \<epsilon>)\<^sup>2"])
    show "AE \<omega> in P. norm ((W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>)
        \<le> (nq * \<epsilon>)\<^sup>2"
      using W2b
    proof (rule eventually_mono)
      fix \<omega> assume h: "(W \<omega>)\<^sup>2 \<le> (nq * \<epsilon>)\<^sup>2"
      have "(W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<le> (W \<omega>)\<^sup>2 * 1"
        by (intro mult_left_mono) (auto simp: indicator_def)
      then show "norm ((W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>) \<le> (nq * \<epsilon>)\<^sup>2"
        using h by (auto simp: abs_mult indicator_def)
    qed
    show "(\<lambda>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega>) \<in> borel_measurable P"
      using Wm Am by measurable
  qed
  have s_split: "s = (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
      + (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)"
  proof -
    have "s = (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega>
        + (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)"
      unfolding s_def
      by (rule Bochner_Integration.integral_cong[OF refl])
        (auto simp: indicator_def)
    also have "\<dots> = (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
        + (\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)"
      by (rule Bochner_Integration.integral_add[OF W2A_int W2Ac_int])
    finally show ?thesis .
  qed
  have EAc_le: "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P) \<le> s / 2"
  proof -
    have ptw: "AE \<omega> in P. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<le> s / 2"
    proof (rule eventually_mono[OF AE_space])
      fix \<omega> assume sp: "\<omega> \<in> space P"
      show "(W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<le> s / 2"
      proof (cases "\<omega> \<in> A")
        case True
        then show ?thesis using s0 by (simp add: indicator_def)
      next
        case False
        then have "\<bar>W \<omega>\<bar> \<le> sqrt (s / 2)"
          using sp unfolding A_def by auto
        then have "\<bar>W \<omega>\<bar>\<^sup>2 \<le> (sqrt (s / 2))\<^sup>2"
          by (rule power_mono[OF _ abs_ge_zero])
        then have "(W \<omega>)\<^sup>2 \<le> s / 2" using s0 by simp
        then show ?thesis
          using sp False by (simp add: indicator_def)
      qed
    qed
    have "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real (space P - A) \<omega> \<partial>P)
        \<le> (\<integral>\<omega>. s / 2 \<partial>P)"
      by (rule integral_mono_AE[OF W2Ac_int PP.integrable_const ptw])
    then show ?thesis by (simp add: PP.prob_space)
  qed
  have indA_int: "integrable P (indicat_real A)"
    by (rule integrable_real_indicator[OF Am]) (simp add: PP.emeasure_eq_measure)
  have indA_E: "(\<integral>\<omega>. indicat_real A \<omega> \<partial>P) = PP.prob A"
    using Am by simp
  have EA_le: "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
      \<le> (nq * \<epsilon>)\<^sup>2 * PP.prob A"
  proof -
    have ptw: "AE \<omega> in P. (W \<omega>)\<^sup>2 * indicat_real A \<omega>
        \<le> (nq * \<epsilon>)\<^sup>2 * indicat_real A \<omega>"
      using W2b
      by (rule eventually_mono) (auto intro: mult_right_mono simp: indicator_def)
    have "(\<integral>\<omega>. (W \<omega>)\<^sup>2 * indicat_real A \<omega> \<partial>P)
        \<le> (\<integral>\<omega>. (nq * \<epsilon>)\<^sup>2 * indicat_real A \<omega> \<partial>P)"
      by (rule integral_mono_AE[OF W2A_int integrable_cmult[OF indA_int] ptw])
    also have "\<dots> = (nq * \<epsilon>)\<^sup>2 * PP.prob A"
      using integral_cmult[OF indA_int] indA_E by simp
    finally show ?thesis .
  qed
  have probA: "s / 2 \<le> (nq * \<epsilon>)\<^sup>2 * PP.prob A"
    using s_split EAc_le EA_le by linarith
  have EabsA: "sqrt (s / 2) * PP.prob A \<le> (\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)"
  proof -
    have ptw: "AE \<omega> in P. sqrt (s / 2) * indicat_real A \<omega> \<le> \<bar>W \<omega>\<bar>"
    proof (rule eventually_mono[OF AE_space])
      fix \<omega> assume "\<omega> \<in> space P"
      show "sqrt (s / 2) * indicat_real A \<omega> \<le> \<bar>W \<omega>\<bar>"
        unfolding A_def by (auto simp: indicator_def)
    qed
    have "sqrt (s / 2) * PP.prob A
        = (\<integral>\<omega>. sqrt (s / 2) * indicat_real A \<omega> \<partial>P)"
      using integral_cmult[OF indA_int] indA_E by simp
    also have "\<dots> \<le> (\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)"
      by (rule integral_mono_AE[OF integrable_cmult[OF indA_int] iabs ptw])
    finally show ?thesis .
  qed
  \<comment> \<open>the contradiction\<close>
  have concl: "q \<bullet> (b *v q) < \<epsilon>\<^sub>0"
  proof (rule ccontr)
    assume "\<not> q \<bullet> (b *v q) < \<epsilon>\<^sub>0"
    then have con: "\<epsilon>\<^sub>0 \<le> q \<bullet> (b *v q)" by simp
    have sEq: "s = et * (q \<bullet> (b *v q))"
    proof -
      have "EY *v q = et *\<^sub>R (b *v q)"
        by (subst EYb) (simp add: scaleR_matrix_vector)
      then have "q \<bullet> (EY *v q) = et * (q \<bullet> (b *v q))"
        by (simp add: inner_scaleR_right)
      then show ?thesis using svar by simp
    qed
    \<comment> \<open>the exit before \<open>t\<close> has probability at most \<open>1/2\<close>\<close>
    have dq: "AE \<omega> in P. \<forall>s' t'. 0 \<le> s' \<longrightarrow> s' < t' \<longrightarrow> t' \<le> T \<longrightarrow>
        (1 / (t' - s')) *\<^sub>R (snd (\<omega> t') - snd (\<omega> s')) \<in> sconstraint k L"
      using P unfolding paper_pair_class_def by blast
    have trYbnd: "AE \<omega> in P. trace (?Yf \<omega>) \<le> n' * n' * L * \<theta>' \<omega>"
      using stc dq posAE
    proof eventually_elim
      case (elim \<omega>)
      have mem: "(1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega> \<in> sconstraint k L"
      proof -
        have "(1 / (\<theta>' \<omega> - 0)) *\<^sub>R (snd (\<omega> (\<theta>' \<omega>)) - snd (\<omega> 0))
            \<in> sconstraint k L"
          using elim thT'[of \<omega>] by blast
        then show ?thesis using elim by simp
      qed
      have trsc: "trace ((1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega>) \<le> n' * (n' * L)"
        using sconstraint_trace_le[OF L0 mem] by (simp add: n'_def)
      have t0': "0 < \<theta>' \<omega>" using elim by simp
      have "trace (?Yf \<omega>) = \<theta>' \<omega> * trace ((1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega>)"
      proof -
        have "?Yf \<omega> = \<theta>' \<omega> *\<^sub>R ((1 / \<theta>' \<omega>) *\<^sub>R ?Yf \<omega>)"
          using t0' by simp
        then show ?thesis
          by (metis trace_scaleR)
      qed
      also have "\<dots> \<le> \<theta>' \<omega> * (n' * (n' * L))"
        using trsc t0' by (intro mult_left_mono) auto
      finally show ?case by (simp add: algebra_simps)
    qed
    have itrY: "integrable P (\<lambda>\<omega>. trace (?Yf \<omega>))"
      by (rule integrable_bounded_linear[OF bounded_linear_trace iY])
    have EtrY: "trace EY \<le> n' * n' * L * et"
    proof -
      have "trace EY = (\<integral>\<omega>. trace (?Yf \<omega>) \<partial>P)"
        unfolding EY_def
        by (rule integral_of_bounded_linear[OF bounded_linear_trace iY,
              symmetric])
      also have "\<dots> \<le> (\<integral>\<omega>. n' * n' * L * \<theta>' \<omega> \<partial>P)"
        by (rule integral_mono_AE[OF itrY integrable_cmult[OF ith] trYbnd])
      also have "\<dots> = n' * n' * L * et"
        using integral_cmult[OF ith] by (simp add: et_def)
      finally show ?thesis .
    qed
    have normsqE: "(\<integral>\<omega>. (?V \<omega>) \<bullet> (?V \<omega>) \<partial>P) = trace EY"
      unfolding EY_def
      by (rule paper_pair_class_stopped_normsq[OF T L0 P st' thM'])
    have inormsq: "integrable P (\<lambda>\<omega>. (?V \<omega>) \<bullet> (?V \<omega>))"
    proof -
      have e: "(\<lambda>\<omega> :: 'n pairpath. (?V \<omega>) \<bullet> (?V \<omega>))
          = (\<lambda>\<omega>. (?V \<omega>) \<bullet> (mat 1 *v (?V \<omega>)))"
        by (simp add: fun_eq_iff matrix_vector_mul_lid)
      show ?thesis
        unfolding e
        by (rule paper_pair_class_stopped_moments(5)[OF T L0 P st' thM'])
    qed
    define Ev where "Ev = {\<omega> \<in> space P. pball_exit T x \<epsilon> \<omega> < t}"
    have tauP: "pball_exit T x \<epsilon> \<in> borel_measurable P"
      unfolding measurable_cong_sets[OF setsP refl]
      by (rule pball_exit_measurable[OF T0])
    have Evm: "Ev \<in> sets P"
      unfolding Ev_def using tauP by measurable
    have chexit: "\<epsilon>\<^sup>2 * PP.prob Ev \<le> trace EY"
    proof -
      have ptw: "AE \<omega> in P. \<epsilon>\<^sup>2 * indicat_real Ev \<omega> \<le> (?V \<omega>) \<bullet> (?V \<omega>)"
        using cwAE AE_space
      proof eventually_elim
        case (elim \<omega>)
        show ?case
        proof (cases "\<omega> \<in> Ev")
          case True
          then have lt: "pball_exit T x \<epsilon> \<omega> < t" unfolding Ev_def by simp
          have th_eq: "\<theta>' \<omega> = pball_exit T x \<epsilon> \<omega>"
            unfolding \<theta>'_def using lt by (simp add: min_def)
          have ltT: "pball_exit T x \<epsilon> \<omega> < T" using lt tT by linarith
          have "fst (\<omega> (pexit T (ball x \<epsilon>) (\<lambda>s. fst (\<omega> s)))) \<notin> ball x \<epsilon>"
            by (rule pexit_mem_of_less_T[OF T0 open_ball elim(1)])
              (use ltT in \<open>simp add: pball_exit_def\<close>)
          then have "\<epsilon> \<le> dist (?Xf \<omega>) x"
            unfolding th_eq pball_exit_def
            by (simp add: mem_ball dist_commute)
          then have "\<epsilon>\<^sup>2 \<le> (dist (?Xf \<omega>) x)\<^sup>2"
            using eps0 by (intro power_mono) auto
          moreover have "(?V \<omega>) \<bullet> (?V \<omega>) = (dist (?Xf \<omega>) x)\<^sup>2"
            by (simp add: dot_square_norm dist_norm)
          ultimately show ?thesis using True by (simp add: indicator_def)
        next
          case False
          have "0 \<le> (?V \<omega>) \<bullet> (?V \<omega>)" by (rule inner_ge_zero)
          then show ?thesis using False by (simp add: indicator_def)
        qed
      qed
      have indEv_int: "integrable P (indicat_real Ev)"
        by (rule integrable_real_indicator[OF Evm])
          (simp add: PP.emeasure_eq_measure)
      have "\<epsilon>\<^sup>2 * PP.prob Ev = (\<integral>\<omega>. \<epsilon>\<^sup>2 * indicat_real Ev \<omega> \<partial>P)"
        using integral_cmult[OF indEv_int] Evm by simp
      also have "\<dots> \<le> (\<integral>\<omega>. (?V \<omega>) \<bullet> (?V \<omega>) \<partial>P)"
        by (rule integral_mono_AE[OF integrable_cmult[OF indEv_int]
              inormsq ptw])
      finally show ?thesis using normsqE by simp
    qed
    have probEv: "PP.prob Ev \<le> 1 / 2"
    proof -
      have nL0: "0 < n' * n' * L" using n'1 L1 by simp
      have "n' * n' * L * et \<le> n' * n' * L * t"
        using ett nL0 by (intro mult_left_mono) auto
      with EtrY have h1: "trace EY \<le> n' * n' * L * t" by linarith
      have n'ne: "n' \<noteq> 0" using n'1 by simp
      have Lne: "L \<noteq> 0" using L1 by simp
      have "n' * n' * L * t = \<epsilon>\<^sup>2 / 2"
        unfolding t_def \<beta>_def using n'ne Lne by (simp add: field_simps)
      with h1 chexit have h2: "\<epsilon>\<^sup>2 * PP.prob Ev \<le> \<epsilon>\<^sup>2 * (1 / 2)" by linarith
      have e20: "0 < \<epsilon>\<^sup>2" using eps0 by simp
      show ?thesis using h2 e20 by (simp add: mult_le_cancel_left)
    qed
    have etlow: "t / 2 \<le> et"
    proof -
      have ptw: "AE \<omega> in P. t * indicat_real (space P - Ev) \<omega> \<le> \<theta>' \<omega>"
      proof (rule eventually_mono[OF AE_space])
        fix \<omega> assume sp: "\<omega> \<in> space P"
        show "t * indicat_real (space P - Ev) \<omega> \<le> \<theta>' \<omega>"
        proof (cases "\<omega> \<in> Ev")
          case True
          then show ?thesis using th0'[of \<omega>] by (simp add: indicator_def)
        next
          case False
          then have "t \<le> pball_exit T x \<epsilon> \<omega>"
            using sp unfolding Ev_def by auto
          then have "\<theta>' \<omega> = t" unfolding \<theta>'_def by (simp add: min_def)
          then show ?thesis using sp False by (simp add: indicator_def)
        qed
      qed
      have indC_int: "integrable P (indicat_real (space P - Ev))"
        by (rule integrable_real_indicator)
          (auto simp: PP.emeasure_eq_measure sets.compl_sets Evm)
      have "t * PP.prob (space P - Ev)
          = (\<integral>\<omega>. t * indicat_real (space P - Ev) \<omega> \<partial>P)"
        using integral_cmult[OF indC_int] sets.compl_sets[OF Evm] by simp
      also have "\<dots> \<le> et"
        unfolding et_def
        by (rule integral_mono_AE[OF integrable_cmult[OF indC_int] ith ptw])
      finally have h: "t * PP.prob (space P - Ev) \<le> et" .
      have "PP.prob (space P - Ev) = 1 - PP.prob Ev"
        by (rule PP.prob_compl[OF Evm])
      then have "1 / 2 \<le> PP.prob (space P - Ev)" using probEv by simp
      then have "t * (1 / 2) \<le> t * PP.prob (space P - Ev)"
        using t0 by (intro mult_left_mono) auto
      then show ?thesis using h by simp
    qed
    have slow: "\<epsilon>\<^sub>0 * (t / 2) \<le> s"
    proof -
      have "\<epsilon>\<^sub>0 * (t / 2) \<le> (q \<bullet> (b *v q)) * et"
        using con etlow e0 t0 et0 by (intro mult_mono) auto
      then show ?thesis using sEq by (simp add: algebra_simps)
    qed
    \<comment> \<open>assemble the numeric contradiction\<close>
    have EnegLow: "sqrt (s / 2) * s / (4 * nq\<^sup>2 * \<epsilon>\<^sup>2)
        \<le> (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)"
    proof -
      have pA: "s / 2 / (nq * \<epsilon>)\<^sup>2 \<le> PP.prob A"
        using probA nq0 eps0 by (simp add: field_simps power2_eq_square)
      have sq0: "0 \<le> sqrt (s / 2)"
        using s0 by (simp add: real_sqrt_ge_zero)
      have "sqrt (s / 2) * (s / 2 / (nq * \<epsilon>)\<^sup>2)
          \<le> sqrt (s / 2) * PP.prob A"
        by (intro mult_left_mono pA sq0)
      also have "\<dots> \<le> (\<integral>\<omega>. \<bar>W \<omega>\<bar> \<partial>P)" by (rule EabsA)
      also have "\<dots> = 2 * (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)" by (rule halfabs)
      finally have "sqrt (s / 2) * (s / 2 / (nq * \<epsilon>)\<^sup>2)
          \<le> 2 * (\<integral>\<omega>. max (- W \<omega>) 0 \<partial>P)" .
      then show ?thesis
        using nq0 eps0 by (simp add: field_simps power_mult_distrib
            power2_eq_square)
    qed
    have upper: "sqrt (s / 2) * s \<le> 4 * nq\<^sup>2 * \<epsilon>\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>\<^sup>2"
    proof -
      have "sqrt (s / 2) * s / (4 * nq\<^sup>2 * \<epsilon>\<^sup>2) \<le> t + Cm * \<epsilon>\<^sup>2 / 2"
        using EnegLow negE by linarith
      also have "t + Cm * \<epsilon>\<^sup>2 / 2 = (\<beta> + Cm / 2) * \<epsilon>\<^sup>2"
        unfolding t_def by (simp add: algebra_simps)
      finally have h: "sqrt (s / 2) * s / (4 * nq\<^sup>2 * \<epsilon>\<^sup>2)
          \<le> (\<beta> + Cm / 2) * \<epsilon>\<^sup>2" .
      have d0: "0 < 4 * nq\<^sup>2 * \<epsilon>\<^sup>2"
        using nq0 eps0 by (simp add: power2_eq_square)
      show ?thesis
        using h d0 by (simp add: pos_divide_le_eq algebra_simps)
    qed
    have lower: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4 \<le> sqrt (s / 2) * s"
    proof -
      have s0': "\<epsilon>\<^sub>0 * t / 2 \<le> s" using slow by simp
      have st0: "0 \<le> \<epsilon>\<^sub>0 * t / 2" using e0 t0 by simp
      have r1: "sqrt (\<epsilon>\<^sub>0 * t / 4) \<le> sqrt (s / 2)"
        by (rule real_sqrt_le_mono) (use s0' in simp)
      have r2: "sqrt (\<epsilon>\<^sub>0 * t / 4) = sqrt (\<epsilon>\<^sub>0 * t) / 2"
        by (simp add: real_sqrt_divide)
      have r3: "sqrt (\<epsilon>\<^sub>0 * t) = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>"
      proof -
        have st: "sqrt t = sqrt \<beta> * \<epsilon>"
        proof -
          have "sqrt t = sqrt \<beta> * sqrt (\<epsilon>\<^sup>2)"
            unfolding t_def by (simp add: real_sqrt_mult)
          also have "sqrt (\<epsilon>\<^sup>2) = \<bar>\<epsilon>\<bar>" by (rule real_sqrt_abs)
          also have "\<bar>\<epsilon>\<bar> = \<epsilon>" using eps0 by simp
          finally show ?thesis .
        qed
        have "sqrt (\<epsilon>\<^sub>0 * t) = sqrt \<epsilon>\<^sub>0 * sqrt t"
          by (simp add: real_sqrt_mult)
        then show ?thesis using st by simp
      qed
      have f1: "sqrt (\<epsilon>\<^sub>0 * t) / 2 \<le> sqrt (s / 2)"
        using r1 r2 by simp
      have flip: "(sqrt (\<epsilon>\<^sub>0 * t) / 2) * (\<epsilon>\<^sub>0 * t / 2)
          = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4"
      proof -
        have e2: "\<epsilon>\<^sub>0 * t = \<epsilon>\<^sub>0 * \<beta> * \<epsilon>\<^sup>2"
          unfolding t_def by simp
        have "(sqrt (\<epsilon>\<^sub>0 * t) / 2) * (\<epsilon>\<^sub>0 * t / 2)
            = (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>) * (\<epsilon>\<^sub>0 * t) / 4"
          unfolding r3 by (simp add: field_simps)
        also have "\<dots> = (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>) * (\<epsilon>\<^sub>0 * \<beta> * \<epsilon>\<^sup>2) / 4"
          by (simp only: e2)
        also have "\<dots> = sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4"
          by (simp add: power2_eq_square power3_eq_cube algebra_simps)
        finally show ?thesis .
      qed
      have "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4
          = (sqrt (\<epsilon>\<^sub>0 * t) / 2) * (\<epsilon>\<^sub>0 * t / 2)"
        by (rule flip[symmetric])
      also have "\<dots> \<le> sqrt (s / 2) * s"
      proof -
        have sq0: "0 \<le> sqrt (s / 2)"
          using s0 by (simp add: real_sqrt_ge_zero)
        show ?thesis by (rule mult_mono[OF f1 s0' sq0 st0])
      qed
      finally show ?thesis .
    qed
    have final: "\<epsilon>K \<le> \<epsilon>"
    proof -
      have LU: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4
          \<le> 4 * nq\<^sup>2 * \<epsilon>\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>\<^sup>2"
        using lower upper by linarith
      have e30: "0 < \<epsilon> ^ 3" using eps0 by simp
      have ll: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> * \<epsilon> ^ 3 / 4
          = \<epsilon> ^ 3 * (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> / 4)"
        by (simp add: algebra_simps)
      have rr: "4 * nq\<^sup>2 * \<epsilon>\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>\<^sup>2
          = \<epsilon> ^ 3 * (4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>)"
        by (simp add: power2_eq_square power3_eq_cube algebra_simps)
      have "\<epsilon> ^ 3 * (sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> / 4)
          \<le> \<epsilon> ^ 3 * (4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>)"
        using LU unfolding ll rr .
      then have h3: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta> / 4
          \<le> 4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>"
        using e30 by (simp add: mult_le_cancel_left)
      have "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta>
          \<le> 4 * (4 * nq\<^sup>2 * (\<beta> + Cm / 2) * \<epsilon>)"
        using h3 by linarith
      then have h4: "sqrt \<epsilon>\<^sub>0 * sqrt \<beta> * \<epsilon>\<^sub>0 * \<beta>
          \<le> \<epsilon> * (16 * nq\<^sup>2 * (\<beta> + Cm / 2))"
        by (simp add: algebra_simps)
      show ?thesis
        unfolding \<epsilon>K_def using den0 h4 by (simp add: pos_divide_le_eq)
    qed
    show False using final epsK eK0 by linarith
  qed
  show ?thesis using that bmem[folded b_def] w concl by blast
qed

section \<open>Compactness: an exactly orthogonal direction\<close>

theorem paper_v_touch_orth:
  fixes K :: "(real^'n::finite) set" and x q :: "real^'n" and M :: "real^'n^'n"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and eb: "0 < ebar"
    and touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (paper_v k L T K z)
          \<le> enn2real (paper_v k L T K x) + q \<bullet> (z - x)
            + ((z - x) \<bullet> (M *v (z - x))) / 2"
  obtains b where "b \<in> sconstraint k L" and "- trace (M ** b) / 2 \<le> 1"
    and "b *v q = 0"
proof -
  have L0: "0 \<le> L" using L1 by simp
  have ex: "\<exists>b. b \<in> sconstraint k L \<and> - trace (M ** b) / 2 \<le> 1
      \<and> q \<bullet> (b *v q) < 1 / real (Suc n)" for n :: nat
  proof -
    obtain b where "b \<in> sconstraint k L" "- trace (M ** b) / 2 \<le> 1"
      "q \<bullet> (b *v q) < 1 / real (Suc n)"
      using paper_v_touch_near_orth[OF T L1 Kc eb touch,
          where \<epsilon>\<^sub>0 = "1 / real (Suc n)"] by auto
    then show ?thesis by blast
  qed
  then obtain bs where bs: "\<And>n :: nat. bs n \<in> sconstraint k L
      \<and> - trace (M ** bs n) / 2 \<le> 1
      \<and> q \<bullet> (bs n *v q) < 1 / real (Suc n)"
    by metis
  have rng: "range bs \<subseteq> sconstraint k L" using bs by blast
  have bdd: "bounded (range bs)"
    by (rule bounded_subset[OF bounded_sconstraint[OF L0] rng])
  obtain l \<sigma> where sm: "strict_mono \<sigma>" and lim: "(bs \<circ> \<sigma>) \<longlonglongrightarrow> l"
    using bounded_imp_convergent_subsequence[OF bdd] by blast
  have inS: "(bs \<circ> \<sigma>) n \<in> sconstraint k L" for n
    using rng by (auto simp: o_def)
  have lmem: "l \<in> sconstraint k L"
    by (rule closed_sequentially[OF closed_sconstraint inS lim])
  have psd_l: "psd l"
    using lmem unfolding sconstraint_def Pi_constraint_def by auto
  \<comment> \<open>the value passes to the limit\<close>
  have trlim: "(\<lambda>n. trace (M ** bs (\<sigma> n))) \<longlonglongrightarrow> trace (M ** l)"
  proof -
    have "(\<lambda>n. trace (M ** (bs \<circ> \<sigma>) n)) \<longlonglongrightarrow> trace (M ** l)"
      by (rule bounded_linear.tendsto[OF bounded_linear_trace_mult_left lim])    then show ?thesis by (simp add: o_def)
  qed
  have w: "- trace (M ** l) / 2 \<le> 1"
  proof -
    have h1: "(\<lambda>n. - trace (M ** bs (\<sigma> n)) / 2) \<longlonglongrightarrow> - trace (M ** l) / 2"      by (intro tendsto_intros trlim) simp
    have h2: "\<exists>N. \<forall>n\<ge>N. - trace (M ** bs (\<sigma> n)) / 2 \<le> 1"
      using bs by blast
    show ?thesis by (rule LIMSEQ_le_const2[OF h1 h2])
  qed  have qlim: "(\<lambda>n. q \<bullet> (bs (\<sigma> n) *v q)) \<longlonglongrightarrow> q \<bullet> (l *v q)"
  proof -
    have "(\<lambda>n. q \<bullet> ((bs \<circ> \<sigma>) n *v q)) \<longlonglongrightarrow> q \<bullet> (l *v q)"
      by (rule bounded_linear.tendsto[OF bounded_linear_quadform lim])    then show ?thesis by (simp add: o_def)
  qed
  have qge: "0 \<le> q \<bullet> (l *v q)"
  proof (rule LIMSEQ_le_const[OF qlim])
    have "psd (bs (\<sigma> n))" for n
      using bs[of "\<sigma> n"] unfolding sconstraint_def Pi_constraint_def by auto
    then show "\<exists>N. \<forall>n\<ge>N. 0 \<le> q \<bullet> (bs (\<sigma> n) *v q)"
      unfolding psd_def by blast
  qed
  have qle: "q \<bullet> (l *v q) \<le> 0"
  proof (rule LIMSEQ_le[OF qlim])
    show "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
      using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
    have "q \<bullet> (bs (\<sigma> n) *v q) \<le> 1 / real (Suc n)" for n
    proof -
      have "q \<bullet> (bs (\<sigma> n) *v q) < 1 / real (Suc (\<sigma> n))"
        using bs[of "\<sigma> n"] by blast
      also have "1 / real (Suc (\<sigma> n)) \<le> 1 / real (Suc n)"
        using seq_suble[OF sm, of n] by (simp add: frac_le)
      finally show ?thesis by simp
    qed
    then show "\<exists>N. \<forall>n\<ge>N. q \<bullet> (bs (\<sigma> n) *v q) \<le> 1 / real (Suc n)" by blast
  qed
  have "q \<bullet> (l *v q) = 0" using qge qle by simp
  then have "l *v q = 0" by (rule psd_kernel_eq[OF psd_l])
  then show ?thesis using that lmem w by blast
qed

section \<open>Clause (2): the subsolution property with the paper's operator\<close>

lemma feasible_trace_le:
  fixes a :: "real^'n::finite^'n" and p :: "real^'n"
  assumes a: "a \<in> feasible k L p"
  shows "trace a \<le> real CARD('n) * L"
proof -
  have "a $ i $ i \<le> L" for i
    using feasible_entry_bound[OF a, of i i] by simp
  then have "trace a \<le> (\<Sum>i\<in>(UNIV :: 'n set). L)"
    unfolding trace_def by (rule sum_mono)
  then show ?thesis by simp
qed

text \<open>Gap 2 closed: clause (2)'s SUBSOLUTION half, with the operator of
  Eq. (1.9) itself --- orthogonality constraint included.  For each test
  function and each Hessian bump \<open>\<delta>\<close>: the anti-concentration dichotomy plus
  compactness produce a convexified direction that kills the gradient
  (@{thm [source] paper_v_touch_orth}), and the capped spectral split converts
  it into a FEASIBLE witness (@{thm [source] sconstraint_orth_feasible}).
  Then \<open>\<delta> \<rightarrow> 0\<close> exactly as in the relaxed case.\<close>

theorem paper_v_visc_subsol:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and kn: "k < CARD('n)"
  shows "visc_subsol k L (interior K) (\<lambda>z. enn2real (paper_v k L T K z))"
  unfolding visc_subsol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>z \<in> ball x e.
        enn2real (paper_v k L T K z) - \<phi> z
          \<le> enn2real (paper_v k L T K x) - \<phi> x"
  have L0: "0 \<le> L" using L1 by simp
  from lm obtain e0 where e00: "0 < e0"
    and lme: "\<And>z. z \<in> ball x e0 \<Longrightarrow>
        enn2real (paper_v k L T K z) - \<phi> z
          \<le> enn2real (paper_v k L T K x) - \<phi> x"
    by blast
  define C where "C = real CARD('n) * L"
  have n0: "0 < real CARD('n)"
    using zero_less_card_finite[where 'a = 'n] by simp
  have C0: "0 < C"
    unfolding C_def by (intro mult_pos_pos n0) (use L1 in linarith)
  have key: "ell_op k L (g x) H \<le> 1 + \<delta> * C / 2" if d0: "0 < \<delta>" for \<delta>
  proof -
    obtain r where r0: "0 < r"
      and dom: "\<And>z. z \<in> ball x r \<Longrightarrow>
          \<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      using test_fun_quadratic_dominates[OF tf d0] by blast
    define ebar where "ebar = min e0 r / 2"
    have eb0: "0 < ebar" using e00 r0 by (simp add: ebar_def)
    have touch: "\<And>z. dist z x \<le> ebar \<Longrightarrow>
        enn2real (paper_v k L T K z)
          \<le> enn2real (paper_v k L T K x) + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    proof -
      fix z assume z: "dist z x \<le> ebar"
      have zin: "z \<in> ball x e0 \<inter> ball x r"
        using z e00 r0 by (auto simp: ebar_def mem_ball dist_commute)
      have "enn2real (paper_v k L T K z) - \<phi> z
          \<le> enn2real (paper_v k L T K x) - \<phi> x"
        using lme zin by blast
      moreover have "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        using dom zin by blast
      ultimately show "enn2real (paper_v k L T K z)
          \<le> enn2real (paper_v k L T K x) + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        by linarith
    qed
    obtain b where bmem: "b \<in> sconstraint k L"
      and wb: "- trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2 \<le> 1"
      and borth: "b *v (g x) = 0"
      by (rule paper_v_touch_orth[OF T L1 Kc eb0 touch])
    obtain a where afeas: "a \<in> feasible k L (g x)"
      and aval: "- trace ((H + \<delta> *\<^sub>R mat 1) ** a) / 2
          \<le> - trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2"
      by (rule sconstraint_orth_feasible[OF kn L1 bmem borth])
    have wa: "- trace ((H + \<delta> *\<^sub>R mat 1) ** a) / 2 \<le> 1"
      using aval wb by linarith
    have split: "trace ((H + \<delta> *\<^sub>R mat 1) ** a) = trace (H ** a) + \<delta> * trace a"
    proof -
      have "(H + \<delta> *\<^sub>R mat 1) ** a = H ** a + (\<delta> *\<^sub>R mat 1) ** a"
        by (rule matrix_add_rdistrib)
      moreover have "(\<delta> *\<^sub>R mat 1) ** a = \<delta> *\<^sub>R a"
        by (simp add: scaleR_matrix_mult matrix_mul_lid)
      ultimately have e1: "trace ((H + \<delta> *\<^sub>R mat 1) ** a)
          = trace (H ** a + \<delta> *\<^sub>R a)" by simp
      have e2: "trace (H ** a + \<delta> *\<^sub>R a) = trace (H ** a) + trace (\<delta> *\<^sub>R a)"
        by (simp add: trace_def sum.distrib vector_add_component)
      have e3: "trace (\<delta> *\<^sub>R a) = \<delta> * trace a" by (rule trace_scaleR)
      from e1 e2 e3 show ?thesis by simp
    qed
    have tra: "trace a \<le> C"
      unfolding C_def by (rule feasible_trace_le[OF afeas])
    have "- trace (H ** a) / 2 \<le> 1 + \<delta> * trace a / 2"
      using wa split by (simp add: field_simps)
    also have "\<dots> \<le> 1 + \<delta> * C / 2"
      using tra d0 by (simp add: mult_left_mono)
    finally have wH: "- trace (H ** a) / 2 \<le> 1 + \<delta> * C / 2" .
    show ?thesis by (rule ell_op_le_of_witness[OF afeas wH])
  qed
  show "ell_op k L (g x) H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0': "0 < e"
    have d0: "0 < 2 * e / C" using e0' C0 by simp
    have "ell_op k L (g x) H \<le> 1 + (2 * e / C) * C / 2"
      by (rule key[OF d0])
    also have "\<dots> = 1 + e" using C0 by (simp add: field_simps)
    finally show "ell_op k L (g x) H \<le> 1 + e" .
  qed
qed

section \<open>Towards the supersolution half: skew-symmetric covariance fields\<close>

text \<open>The supersolution inequality is an essential-infimum statement, so it
  needs PATHWISE control.  The paper (\<section>3.2, Case 1) gets it from a
  covariance field whose columns are \<open>S\<^sub>i \<nabla>\<phi>(y)\<close> with \<open>S\<^sub>i\<close> SKEW-symmetric:
  the field annihilates the gradient of the test function all along the
  path, so no stochastic integral ever appears --- and in this development
  none will: the field is fed to an Euler scheme glued by
  @{thm [source] paper_pair_class_kglue_law'} and passed to a weak limit.
  This section builds the algebra: the skew building block, the extraction
  of STRICT eigendata from a feasible witness (the paper's ``modify \<open>a\<close> so
  the top eigenvalues lie in \<open>(1, L)\<close>''), and the exact identities for
  sums of column outer products.\<close>

subsection \<open>The skew building block\<close>

definition skewv :: "real^'n::finite \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" where
  "skewv q u = (1 / (q \<bullet> q)) *\<^sub>R (outer_prod u q - outer_prod q u)"

lemma skewv_apply:
  "skewv q u *v z = (1 / (q \<bullet> q)) *\<^sub>R ((q \<bullet> z) *\<^sub>R u - (u \<bullet> z) *\<^sub>R q)"
proof -
  have "(outer_prod u q - outer_prod q u) *v z
      = outer_prod u q *v z - outer_prod q u *v z"
    by (simp add: matrix_vector_mult_diff_rdistrib)
  also have "\<dots> = (q \<bullet> z) *\<^sub>R u - (u \<bullet> z) *\<^sub>R q"
    by (simp add: outer_prod_mv)
  finally show ?thesis
    by (simp add: skewv_def scaleR_matrix_vector)
qed

lemma skewv_quadform: "z \<bullet> (skewv q u *v z) = 0"
proof -
  have "z \<bullet> ((q \<bullet> z) *\<^sub>R u - (u \<bullet> z) *\<^sub>R q)
      = (q \<bullet> z) * (z \<bullet> u) - (u \<bullet> z) * (z \<bullet> q)"
    by (simp add: inner_diff_right)
  also have "\<dots> = 0"
    by (simp add: inner_commute)
  finally show ?thesis
    by (simp add: skewv_apply)
qed

lemma skewv_apply_orth:
  assumes q: "q \<noteq> 0" and orth: "u \<bullet> q = 0"
  shows "skewv q u *v q = u"
proof -
  have qq: "q \<bullet> q \<noteq> 0" using q by simp
  have "skewv q u *v q = (1 / (q \<bullet> q)) *\<^sub>R ((q \<bullet> q) *\<^sub>R u - (u \<bullet> q) *\<^sub>R q)"
    by (rule skewv_apply)
  also have "\<dots> = u" using qq orth by simp
  finally show ?thesis .
qed

lemma skewv_norm_le:
  assumes q: "q \<noteq> 0"
  shows "norm (skewv q u *v z) \<le> 2 * norm u * norm z / norm q"
proof -
  have nq0: "0 < norm q" using q by simp
  have qq: "q \<bullet> q = (norm q)\<^sup>2"
    by (simp add: power2_norm_eq_inner)
  have "norm ((q \<bullet> z) *\<^sub>R u - (u \<bullet> z) *\<^sub>R q)
      \<le> norm ((q \<bullet> z) *\<^sub>R u) + norm ((u \<bullet> z) *\<^sub>R q)"
    by (rule norm_triangle_ineq4)
  also have "\<dots> = \<bar>q \<bullet> z\<bar> * norm u + \<bar>u \<bullet> z\<bar> * norm q"
    by simp
  also have "\<dots> \<le> (norm q * norm z) * norm u + (norm u * norm z) * norm q"
    by (intro add_mono mult_right_mono Cauchy_Schwarz_ineq2) simp_all
  also have "\<dots> = 2 * norm u * norm z * norm q"
    by (simp add: algebra_simps)
  finally have h: "norm ((q \<bullet> z) *\<^sub>R u - (u \<bullet> z) *\<^sub>R q)
      \<le> 2 * norm u * norm z * norm q" .
  have "norm (skewv q u *v z)
      = norm ((q \<bullet> z) *\<^sub>R u - (u \<bullet> z) *\<^sub>R q) / (norm q)\<^sup>2"
    using nq0 by (simp add: skewv_apply qq)
  also have "\<dots> \<le> (2 * norm u * norm z * norm q) / (norm q)\<^sup>2"
    using h nq0 by (intro divide_right_mono) simp_all
  also have "\<dots> = 2 * norm u * norm z / norm q"
    using nq0 by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma skewv_scaleR_arg: "skewv q (r *\<^sub>R u) = r *\<^sub>R skewv q u"
proof -
  have "outer_prod (r *\<^sub>R u) q - outer_prod q (r *\<^sub>R u)
      = r *\<^sub>R (outer_prod u q - outer_prod q u)"
    by (simp add: outer_prod_def vec_eq_iff algebra_simps)
  then show ?thesis
    by (simp add: skewv_def)
qed

subsection \<open>A crude operator bound for matrices\<close>

lemma sum_sq_le_sq_sum:
  fixes f :: "'b \<Rightarrow> real"
  assumes nn: "\<And>i. i \<in> F \<Longrightarrow> 0 \<le> f i"
  shows "(\<Sum>i\<in>F. (f i)\<^sup>2) \<le> (\<Sum>i\<in>F. f i)\<^sup>2"
proof (cases "finite F")
  case True
  then show ?thesis using nn
  proof (induction F)
    case empty
    show ?case by simp
  next
    case (insert a F)
    have fa: "0 \<le> f a" using insert.prems by simp
    have sn: "0 \<le> (\<Sum>i\<in>F. f i)"
      using insert.prems by (intro sum_nonneg) simp
    have "(\<Sum>i\<in>insert a F. (f i)\<^sup>2) = (f a)\<^sup>2 + (\<Sum>i\<in>F. (f i)\<^sup>2)"
      using insert.hyps by simp
    also have "\<dots> \<le> (f a)\<^sup>2 + (\<Sum>i\<in>F. f i)\<^sup>2"
      using insert by simp
    also have "\<dots> \<le> (f a)\<^sup>2 + 2 * f a * (\<Sum>i\<in>F. f i) + (\<Sum>i\<in>F. f i)\<^sup>2"
      using fa sn by simp
    also have "\<dots> = (f a + (\<Sum>i\<in>F. f i))\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?case using insert.hyps by simp
  qed
next
  case False
  then show ?thesis by simp
qed

lemma matvec_norm_le:
  fixes M :: "real^'n::finite^'n"
  shows "norm (M *v w) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w"
proof -
  let ?C = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  have comp: "\<bar>(M *v w) $ i\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w" for i
  proof -
    have "\<bar>(M *v w) $ i\<bar> = \<bar>\<Sum>j\<in>UNIV. M $ i $ j * w $ j\<bar>"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j * w $ j\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar> * norm w)"
      by (intro sum_mono)
        (simp add: abs_mult mult_left_mono component_le_norm_cart)
    also have "\<dots> = (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w"
      by (simp add: sum_distrib_right)
    finally show ?thesis .
  qed
  have rownn: "0 \<le> (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w" for i
    by (intro mult_nonneg_nonneg sum_nonneg) simp_all
  have "(norm (M *v w))\<^sup>2 = (M *v w) \<bullet> (M *v w)"
    by (simp add: power2_norm_eq_inner)
  also have "\<dots> = (\<Sum>i\<in>UNIV. ((M *v w) $ i)\<^sup>2)"
    by (simp add: inner_vec_def power2_eq_square)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. ((\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2)"
  proof (rule sum_mono)
    fix i :: 'n
    have "((M *v w) $ i)\<^sup>2 = \<bar>(M *v w) $ i\<bar>\<^sup>2" by simp
    also have "\<dots> \<le> ((\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2"
      using comp[of i] rownn[of i] by (intro power_mono) simp_all
    finally show "((M *v w) $ i)\<^sup>2
        \<le> ((\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2" .
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * norm w)\<^sup>2"
    by (rule sum_sq_le_sq_sum) (rule rownn)
  also have "\<dots> = (?C * norm w)\<^sup>2"
    by (simp add: sum_distrib_right)
  finally have h: "(norm (M *v w))\<^sup>2 \<le> (?C * norm w)\<^sup>2" .
  have Cnn: "0 \<le> ?C * norm w"
    by (intro mult_nonneg_nonneg sum_nonneg) simp_all
  show ?thesis
    using h Cnn by (simp add: power2_le_iff_abs_le abs_of_nonneg)
qed

subsection \<open>Extracting strict eigendata from a feasible witness\<close>

text \<open>\<open>eigen_lb\<close> is variational, so counting eigenvalues \<open>\<ge> 1\<close> is a
  dimension argument: if fewer than \<open>n - k\<close> eigenvalues were \<open>\<ge> 1\<close>, the
  span of the remaining eigenvectors would meet the witness subspace of
  \<open>eigen_lb\<close> nontrivially, and on the intersection the quadratic form is
  strictly below \<open>|v|\<^sup>2\<close> --- a contradiction.\<close>

lemma feasible_eigen_count:
  fixes a :: "real^'n::finite^'n" and q :: "real^'n"
  assumes a: "a \<in> feasible k L q" and kn: "k < CARD('n)"
  obtains B Bp where "onormal B" "span B = UNIV" "finite B"
    "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    "Bp \<subseteq> B" "card Bp = CARD('n) - k"
    "\<And>u. u \<in> Bp \<Longrightarrow> 1 \<le> u \<bullet> (a *v u)"
proof -
  have psd_a: "psd a" and lb: "eigen_lb a (CARD('n) - k)"
    using a unfolding feasible_def by auto
  have sym: "transpose a = a" using psd_a unfolding psd_def by blast
  obtain B where B: "onormal B" "span B = UNIV"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    using symmetric_eigenbasis[OF sym] by blast
  have finB: "finite B" by (rule onormal_finite[OF B(1)])
  have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF B])
  define lam where "lam = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam_nn: "0 \<le> lam u" for u
    using psd_a unfolding lam_def psd_def by blast
  define Bge where "Bge = {u \<in> B. 1 \<le> lam u}"
  have BgeB: "Bge \<subseteq> B" unfolding Bge_def by blast
  have deco: "a = (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)"
    unfolding lam_def by (rule spectral_decomposition[OF B eig])
  have count: "CARD('n) - k \<le> card Bge"
  proof (rule ccontr)
    assume "\<not> CARD('n) - k \<le> card Bge"
    then have lt: "card Bge < CARD('n) - k" by simp
    define Blt where "Blt = B - Bge"
    have BltB: "Blt \<subseteq> B" unfolding Blt_def by blast
    have finBlt: "finite Blt" using finB BltB by (rule finite_subset[rotated])
    have on_lt: "onormal Blt" by (rule onormal_subset[OF B(1) BltB])
    have z_notin: "(0 :: real^'n) \<notin> Blt"
    proof
      assume "(0 :: real^'n) \<in> Blt"
      then have "(0 :: real^'n) \<in> B" using BltB by blast
      then have "norm (0 :: real^'n) = 1"
        using B(1) unfolding onormal_def by blast
      then show False by simp
    qed
    have ind_lt: "independent Blt"
      using on_lt z_notin unfolding onormal_def
      by (intro pairwise_orthogonal_independent) auto
    have dim_lt: "dim (span Blt) = card Blt"
      by (rule dim_span_eq_card_independent[OF ind_lt])
    have card_lt: "card Blt = CARD('n) - card Bge"
      unfolding Blt_def Bge_def using finB cardB
      by (subst card_Diff_subset) auto
    from lb obtain S where S: "subspace S" "CARD('n) - k \<le> dim S"
      and Sq: "\<And>v. v \<in> S \<Longrightarrow> v \<bullet> v \<le> v \<bullet> (a *v v)"
      unfolding eigen_lb_def by blast
    have card_ge_le: "card Bge \<le> CARD('n)"
      using card_mono[OF finB BgeB] cardB by simp
    have dim_sum: "dim S + dim (span Blt) \<ge> CARD('n) + 1"
    proof -
      have "CARD('n) - card Bge \<ge> CARD('n) - (CARD('n) - k) + 1"
        using lt kn by linarith
      then have "dim (span Blt) \<ge> k + 1"
        using dim_lt card_lt kn by simp
      then show ?thesis using S(2) kn by linarith
    qed
    have inter_pos: "0 < dim (S \<inter> span Blt)"
    proof -
      have sub: "subspace (span Blt)" by (rule subspace_span)
      have "dim {x + y |x y. x \<in> S \<and> y \<in> span Blt} + dim (S \<inter> span Blt)
          = dim S + dim (span Blt)"
        by (rule dim_sums_Int[OF S(1) sub])
      moreover have "dim {x + y |x y. x \<in> S \<and> y \<in> span Blt} \<le> CARD('n)"
      proof -
        have "dim {x + y |x y. x \<in> S \<and> y \<in> span Blt}
            \<le> dim (UNIV :: (real^'n) set)"
          by (rule dim_subset) simp
        then show ?thesis by simp
      qed
      ultimately show ?thesis using dim_sum by linarith
    qed
    obtain v where v: "v \<in> S" "v \<in> span Blt" "v \<noteq> 0"
    proof -
      have "\<not> (S \<inter> span Blt \<subseteq> {0})"
      proof
        assume "S \<inter> span Blt \<subseteq> {0}"
        then have "dim (S \<inter> span Blt) = 0"
          using dim_eq_0 by blast
        then show False using inter_pos by linarith
      qed
      then obtain w where "w \<in> S \<inter> span Blt" "w \<noteq> 0" by blast
      then show ?thesis using that by blast
    qed
    have vanish: "u \<bullet> v = 0" if u: "u \<in> Bge" for u
    proof -
      have "orthogonal u y" if y: "y \<in> Blt" for y
      proof -
        have "u \<noteq> y" using u y unfolding Blt_def by blast
        moreover have "u \<in> B" using u BgeB by blast
        moreover have "y \<in> B" using y BltB by blast
        ultimately show ?thesis
          using B(1) unfolding onormal_def pairwise_def by blast
      qed
      then have "orthogonal u v"
        by (rule orthogonal_to_span[OF v(2), rotated]) blast
      then show ?thesis unfolding orthogonal_def .
    qed
    have pars: "(\<Sum>u\<in>Blt. (u \<bullet> v)\<^sup>2) = v \<bullet> v"
      by (rule onormal_span_parseval[OF on_lt v(2)])
    have vv0: "0 < v \<bullet> v"
      using v(3) by (simp add: inner_gt_zero_iff)
    obtain u0 where u0: "u0 \<in> Blt" "0 < (u0 \<bullet> v)\<^sup>2"
    proof -
      have "\<exists>u\<in>Blt. (u \<bullet> v)\<^sup>2 \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> (\<exists>u\<in>Blt. (u \<bullet> v)\<^sup>2 \<noteq> 0)"
        then have "(\<Sum>u\<in>Blt. (u \<bullet> v)\<^sup>2) = 0" by simp
        then show False using pars vv0 by simp
      qed
      then show ?thesis using that
        by (metis zero_less_power2 power2_eq_iff_nonneg zero_power2
            linorder_not_le abs_le_zero_iff abs_of_nonneg zero_le_power2)
    qed
    have expand: "v \<bullet> (a *v v) = (\<Sum>u\<in>B. lam u * (u \<bullet> v)\<^sup>2)"
      by (subst deco) (rule quadform_sum_outer[OF finB])
    have split: "v \<bullet> (a *v v) = (\<Sum>u\<in>Blt. lam u * (u \<bullet> v)\<^sup>2)"
    proof -
      have Bsplit: "B = Bge \<union> Blt" unfolding Blt_def Bge_def by blast
      have disj: "Bge \<inter> Blt = {}" unfolding Blt_def by blast
      have "(\<Sum>u\<in>B. lam u * (u \<bullet> v)\<^sup>2)
          = (\<Sum>u\<in>Bge. lam u * (u \<bullet> v)\<^sup>2) + (\<Sum>u\<in>Blt. lam u * (u \<bullet> v)\<^sup>2)"
        unfolding Bsplit
        by (rule sum.union_disjoint)
          (use finB Bsplit disj in \<open>auto intro: finite_subset\<close>)
      moreover have "(\<Sum>u\<in>Bge. lam u * (u \<bullet> v)\<^sup>2) = 0"
        using vanish by simp
      ultimately show ?thesis using expand by simp
    qed
    have "v \<bullet> (a *v v) < (\<Sum>u\<in>Blt. (u \<bullet> v)\<^sup>2)"
      unfolding split
    proof (rule sum_strict_mono_ex1[OF finBlt])
      show "\<forall>u\<in>Blt. lam u * (u \<bullet> v)\<^sup>2 \<le> (u \<bullet> v)\<^sup>2"
      proof
        fix u assume u: "u \<in> Blt"
        then have "lam u < 1" unfolding Blt_def Bge_def
          using BltB by auto
        then show "lam u * (u \<bullet> v)\<^sup>2 \<le> (u \<bullet> v)\<^sup>2"
          using lam_nn[of u] by (intro mult_left_le_one_le) simp_all
      qed
      show "\<exists>u\<in>Blt. lam u * (u \<bullet> v)\<^sup>2 < (u \<bullet> v)\<^sup>2"
      proof (intro bexI[OF _ u0(1)])
        have "lam u0 < 1" using u0(1) unfolding Blt_def Bge_def
          using BltB by auto
        then have "lam u0 * (u0 \<bullet> v)\<^sup>2 < 1 * (u0 \<bullet> v)\<^sup>2"
          by (rule mult_strict_right_mono[OF _ u0(2)])
        then show "lam u0 * (u0 \<bullet> v)\<^sup>2 < (u0 \<bullet> v)\<^sup>2" by simp
      qed
    qed
    also have "\<dots> = v \<bullet> v" by (rule pars)
    finally show False using Sq[OF v(1)] by simp
  qed
  obtain Bp where Bp: "Bp \<subseteq> Bge" "card Bp = CARD('n) - k"
    using obtain_subset_with_card_n[OF count] by metis
  show ?thesis
  proof (rule that[OF B(1) B(2) finB eig _ Bp(2)])
    show "Bp \<subseteq> B" using Bp(1) BgeB by blast
    show "\<And>u. u \<in> Bp \<Longrightarrow> 1 \<le> u \<bullet> (a *v u)"
      using Bp(1) unfolding Bge_def lam_def by blast
  qed
qed

subsection \<open>The strict blend\<close>

text \<open>Blending the witness with the projection onto \<open>Bp\<close> pushes the top
  \<open>n - k\<close> eigenvalues STRICTLY above \<open>1\<close> and all eigenvalues STRICTLY
  below \<open>L\<close> --- the margins that survive perturbation along the path.
  This is the only place the supersolution argument needs \<open>1 < L\<close>.\<close>

lemma feasible_strict_eigendata:
  fixes a :: "real^'n::finite^'n" and q :: "real^'n" and M :: "real^'n^'n"
  assumes a: "a \<in> feasible k L q" and kn: "k < CARD('n)" and L1: "1 < L"
    and tr: "2 * \<eta> \<le> 1 + trace (M ** a) / 2" and eta: "0 < \<eta>"
  obtains B Bp lam m where
    "onormal B" "span B = UNIV" "finite B"
    "Bp \<subseteq> B" "card Bp = CARD('n) - k" "0 < m"
    "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u \<and> lam u \<le> L - m"
    "\<And>u. u \<in> Bp \<Longrightarrow> 1 + m \<le> lam u"
    "\<And>u. u \<in> B \<Longrightarrow> 0 < lam u \<Longrightarrow> u \<bullet> q = 0"
    "\<eta> \<le> 1 + trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2"
proof -
  have psd_a: "psd a" and orth_a: "a *v q = 0" and ub: "eigen_ub a L"
    using a unfolding feasible_def by auto
  have sym: "transpose a = a" using psd_a unfolding psd_def by blast
  obtain B Bp where B: "onormal B" "span B = UNIV" "finite B"
    and eig: "\<And>u. u \<in> B \<Longrightarrow> a *v u = (u \<bullet> (a *v u)) *\<^sub>R u"
    and BpB: "Bp \<subseteq> B" and cardBp: "card Bp = CARD('n) - k"
    and Bp1: "\<And>u. u \<in> Bp \<Longrightarrow> 1 \<le> u \<bullet> (a *v u)"
    using feasible_eigen_count[OF a kn] by metis
  define lam0 where "lam0 = (\<lambda>u :: real^'n. u \<bullet> (a *v u))"
  have lam0_nn: "0 \<le> lam0 u" for u
    using psd_a unfolding lam0_def psd_def by blast
  have lam0_le: "lam0 u \<le> L" if u: "u \<in> B" for u
  proof -
    have "u \<bullet> (a *v u) \<le> L * (u \<bullet> u)"
      using ub unfolding eigen_ub_def by blast
    then show ?thesis unfolding lam0_def
      using onormal_inner_self[OF B(1) u] by simp
  qed
  have orth0: "u \<bullet> q = 0" if u: "u \<in> B" and pos: "0 < lam0 u" for u
  proof -
    have "u \<bullet> (a *v q) = 0" using orth_a by simp
    moreover have "u \<bullet> (a *v q) = (a *v u) \<bullet> q"
      using sym by (simp add: inner_transpose_matrix)
    ultimately have "(a *v u) \<bullet> q = 0" by simp
    then have "(lam0 u *\<^sub>R u) \<bullet> q = 0"
      using eig[OF u] unfolding lam0_def by simp
    then have "lam0 u * (u \<bullet> q) = 0" by simp
    then show ?thesis using pos by simp
  qed
  define c where "c = (1 + L) / 2"
  have c0: "0 < c" unfolding c_def using L1 by simp
  define CmB where "CmB = (\<Sum>u\<in>Bp. \<bar>u \<bullet> (M *v u)\<bar>)"
  have CmB0: "0 \<le> CmB" unfolding CmB_def by (rule sum_nonneg) simp
  define s where "s = \<eta> / (2 * \<eta> + c * CmB / 2 + 1)"
  have ccmb: "0 \<le> c * CmB"
    using c0 CmB0 by (intro mult_nonneg_nonneg) simp_all
  have den0: "0 < 2 * \<eta> + c * CmB / 2 + 1"
    using eta ccmb by linarith
  have s0: "0 < s" unfolding s_def using eta den0 by simp
  have slt: "\<eta> < 2 * \<eta> + c * CmB / 2 + 1"
    using eta ccmb by linarith
  have s1: "s < 1" unfolding s_def using den0 slt
    by (simp add: divide_less_eq)
  define lam where
    "lam = (\<lambda>u. (1 - s) * lam0 u + (if u \<in> Bp then s * c else 0))"
  define m where "m = s * (L - 1) / 2"
  have m0: "0 < m" unfolding m_def using s0 L1 by simp
  have lam_nn_le: "0 \<le> lam u \<and> lam u \<le> L - m" if u: "u \<in> B" for u
  proof (cases "u \<in> Bp")
    case True
    have "0 \<le> lam u" unfolding lam_def using True s0 s1 c0 lam0_nn[of u]
      by (simp add: mult_nonneg_nonneg)
    moreover have "lam u \<le> L - m"
    proof -
      have "lam u = (1 - s) * lam0 u + s * c"
        unfolding lam_def using True by simp
      also have "\<dots> \<le> (1 - s) * L + s * c"
        using lam0_le[OF u] s1 by (intro add_right_mono mult_left_mono) simp_all
      also have "\<dots> = L - s * (L - 1) / 2"
        unfolding c_def by (simp add: field_simps)
      finally show ?thesis unfolding m_def .
    qed
    ultimately show ?thesis by blast
  next
    case False
    have "0 \<le> lam u" unfolding lam_def using False s1 lam0_nn[of u]
      by (simp add: mult_nonneg_nonneg)
    moreover have "lam u \<le> L - m"
    proof -
      have "lam u = (1 - s) * lam0 u" unfolding lam_def using False by simp
      also have "\<dots> \<le> (1 - s) * L"
        using lam0_le[OF u] s1 by (intro mult_left_mono) simp_all
      also have "\<dots> \<le> L - s * (L - 1) / 2"
        using s0 L1 by (simp add: field_simps)
      finally show ?thesis unfolding m_def .
    qed
    ultimately show ?thesis by blast
  qed
  have lam_lb: "1 + m \<le> lam u" if u: "u \<in> Bp" for u
  proof -
    have "1 + s * (L - 1) / 2 = (1 - s) * 1 + s * c"
      unfolding c_def by (simp add: field_simps)
    also have "\<dots> \<le> (1 - s) * lam0 u + s * c"
      using Bp1[OF u] s1 unfolding lam0_def
      by (intro add_right_mono mult_left_mono) simp_all
    finally show ?thesis unfolding lam_def m_def using u by simp
  qed
  have lam_orth: "u \<bullet> q = 0" if u: "u \<in> B" and pos: "0 < lam u" for u
  proof (cases "u \<in> Bp")
    case True
    have "0 < lam0 u" using Bp1[OF True] unfolding lam0_def by simp
    then show ?thesis by (rule orth0[OF u])
  next
    case False
    then have "lam u = (1 - s) * lam0 u" unfolding lam_def by simp
    then have "0 < lam0 u" using pos s1
      by (metis lam0_nn less_le mult_pos_pos mult_zero_right
          zero_less_mult_pos linorder_neqE_linordered_idom)
    then show ?thesis by (rule orth0[OF u])
  qed
  have trace_bound:
    "\<eta> \<le> 1 + trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2"
  proof -
    have deco: "a = (\<Sum>u\<in>B. lam0 u *\<^sub>R outer_prod u u)"
      unfolding lam0_def by (rule spectral_decomposition[OF B(1,2) eig])
    have t0: "trace (M ** a) = (\<Sum>u\<in>B. lam0 u * (u \<bullet> (M *v u)))"
      by (subst deco) (rule traceM_sum_outer)
    have t1: "trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u))
        = (\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))"
      by (rule traceM_sum_outer)
    have splitsum: "(\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))
        = (1 - s) * (\<Sum>u\<in>B. lam0 u * (u \<bullet> (M *v u)))
          + s * c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u))"
    proof -
      have "(\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))
          = (\<Sum>u\<in>B. (1 - s) * (lam0 u * (u \<bullet> (M *v u)))
              + (if u \<in> Bp then s * c * (u \<bullet> (M *v u)) else 0))"
        by (rule sum.cong[OF refl]) (simp add: lam_def algebra_simps)
      also have "\<dots> = (1 - s) * (\<Sum>u\<in>B. lam0 u * (u \<bullet> (M *v u)))
          + (\<Sum>u\<in>B. if u \<in> Bp then s * c * (u \<bullet> (M *v u)) else 0)"
        by (simp add: sum.distrib sum_distrib_left)
      also have "(\<Sum>u\<in>B. if u \<in> Bp then s * c * (u \<bullet> (M *v u)) else 0)
          = s * c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u))"
        using BpB B(3)
        by (subst sum.inter_restrict[symmetric])
          (auto simp: Int_absorb1 sum_distrib_left)
      finally show ?thesis .
    qed
    have absBp: "\<bar>\<Sum>u\<in>Bp. u \<bullet> (M *v u)\<bar> \<le> CmB"
      unfolding CmB_def by (rule sum_abs)
    have "1 + trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2
        = (1 - s) * (1 + trace (M ** a) / 2)
          + s * (1 + c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u)) / 2)"
      unfolding t1 splitsum t0[symmetric] by (simp add: field_simps)
    moreover have "(1 - s) * (1 + trace (M ** a) / 2) \<ge> (1 - s) * (2 * \<eta>)"
      using tr s1 by (intro mult_left_mono) simp_all
    moreover have "s * (1 + c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u)) / 2)
        \<ge> s * (- (c * CmB / 2))"
    proof (intro mult_left_mono)
      have "- (c * CmB / 2) \<le> 1 - c * CmB / 2" by simp
      moreover have "c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u)) / 2 \<ge> - (c * CmB / 2)"
      proof -
        have "- CmB \<le> (\<Sum>u\<in>Bp. u \<bullet> (M *v u))"
          using absBp by (simp add: abs_le_iff)
        then have "c * (- CmB) \<le> c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u))"
          using c0 by (intro mult_left_mono) simp_all
        then show ?thesis by linarith
      qed
      ultimately show "- (c * CmB / 2)
          \<le> 1 + c * (\<Sum>u\<in>Bp. u \<bullet> (M *v u)) / 2" by linarith
    qed (use s0 in simp)
    moreover have "(1 - s) * (2 * \<eta>) + s * (- (c * CmB / 2)) \<ge> \<eta>"
    proof -
      have "(1 - s) * (2 * \<eta>) + s * (- (c * CmB / 2))
          = 2 * \<eta> - s * (2 * \<eta> + c * CmB / 2)"
        by (simp add: algebra_simps)
      moreover have "s * (2 * \<eta> + c * CmB / 2) \<le> \<eta>"
      proof -
        have "s * (2 * \<eta> + c * CmB / 2) \<le> s * (2 * \<eta> + c * CmB / 2 + 1)"
          using s0 by simp
        also have "\<dots> = \<eta>" unfolding s_def using den0 by simp
        finally show ?thesis .
      qed
      ultimately show ?thesis by linarith
    qed
    ultimately show ?thesis by linarith
  qed
  show ?thesis
    by (rule that[OF B(1,2,3) BpB cardBp m0 _ lam_lb lam_orth trace_bound])
      (rule lam_nn_le)
qed

subsection \<open>Sums of column outer products: exact identities\<close>

text \<open>The covariance field will be \<open>\<Sum>\<^sub>u outerp (w u)\<close> for columns \<open>w u\<close>.
  The identities here are exact regardless of any perturbation: the matrix
  action, the quadratic form as a sum of squares, positive
  semidefiniteness, the trace pairing, and --- the point of the whole
  construction --- annihilation of any vector all the columns are
  orthogonal to.\<close>

lemma matvec_zero_left: "(0 :: real^'n::finite^'n) *v z = 0"
  by (simp add: matrix_vector_mult_def vec_eq_iff)

lemma outerp_sum_matvec:
  fixes w :: "'b \<Rightarrow> real^'n::finite" and F :: "'b set"
  shows "(\<Sum>u\<in>F. outerp (w u)) *v z = (\<Sum>u\<in>F. (w u \<bullet> z) *\<^sub>R w u)"
proof (cases "finite F")
  case True
  then show ?thesis
  proof (induction F)
    case empty
    show ?case by (simp add: matvec_zero_left)
  next
    case (insert u F)
    have "(\<Sum>v\<in>insert u F. outerp (w v)) *v z
        = (outerp (w u) + (\<Sum>v\<in>F. outerp (w v))) *v z"
      using insert.hyps by simp
    also have "\<dots> = outerp (w u) *v z + (\<Sum>v\<in>F. outerp (w v)) *v z"
      by (rule matrix_vector_mult_add_rdistrib)
    also have "outerp (w u) *v z = (w u \<bullet> z) *\<^sub>R w u"
      by (simp add: outerp_eq_outer_prod outer_prod_mv)
    finally show ?case using insert by simp
  qed
next
  case False
  then show ?thesis by (simp add: matvec_zero_left)
qed

lemma outerp_sum_quadform:
  fixes w :: "'b \<Rightarrow> real^'n::finite" and F :: "'b set"
  shows "z \<bullet> ((\<Sum>u\<in>F. outerp (w u)) *v z) = (\<Sum>u\<in>F. (w u \<bullet> z)\<^sup>2)"
proof -
  have "z \<bullet> ((\<Sum>u\<in>F. outerp (w u)) *v z)
      = (\<Sum>u\<in>F. z \<bullet> ((w u \<bullet> z) *\<^sub>R w u))"
    unfolding outerp_sum_matvec by (rule inner_sum_right)
  also have "\<dots> = (\<Sum>u\<in>F. (w u \<bullet> z)\<^sup>2)"
    by (rule sum.cong[OF refl])
      (simp add: inner_scaleR_right inner_commute power2_eq_square)
  finally show ?thesis .
qed

lemma outerp_sum_annihilate:
  fixes w :: "'b \<Rightarrow> real^'n::finite" and F :: "'b set"
  assumes orth: "\<And>u. u \<in> F \<Longrightarrow> w u \<bullet> g = 0"
  shows "(\<Sum>u\<in>F. outerp (w u)) *v g = 0"
proof -
  have "(\<Sum>u\<in>F. outerp (w u)) *v g = (\<Sum>u\<in>F. (w u \<bullet> g) *\<^sub>R w u)"
    by (rule outerp_sum_matvec)
  also have "\<dots> = 0" using orth by simp
  finally show ?thesis .
qed

lemma outerp_sum_psd:
  fixes w :: "'b \<Rightarrow> real^'n::finite" and F :: "'b set"
  shows "psd (\<Sum>u\<in>F. outerp (w u))"
proof -
  have t: "transpose (\<Sum>u\<in>F. outerp (w u)) = (\<Sum>u\<in>F. outerp (w u))"
    by (simp add: transpose_matrix_sum outerp_eq_outer_prod
        transpose_outer_prod)
  have q: "0 \<le> z \<bullet> ((\<Sum>u\<in>F. outerp (w u)) *v z)" for z
    unfolding outerp_sum_quadform by (rule sum_nonneg) simp
  show ?thesis unfolding psd_def using t q by blast
qed

lemma trace_mult_zero_right: "trace (M ** (0 :: real^'n::finite^'n)) = 0"
  by (simp add: matrix_matrix_mult_def trace_def vec_eq_iff)

lemma trace_mult_outerp_sum:
  fixes M :: "real^'n::finite^'n" and w :: "'b \<Rightarrow> real^'n" and F :: "'b set"
  assumes finF: "finite F"
  shows "trace (M ** (\<Sum>u\<in>F. outerp (w u))) = (\<Sum>u\<in>F. w u \<bullet> (M *v w u))"
  using finF
proof (induction F)
  case empty
  show ?case by (simp add: trace_mult_zero_right trace_def)
next
  case (insert u F)
  have "trace (M ** (\<Sum>v\<in>insert u F. outerp (w v)))
      = trace (M ** (outerp (w u) + (\<Sum>v\<in>F. outerp (w v))))"
    using insert.hyps by simp
  also have "\<dots> = trace (M ** outerp (w u))
      + trace (M ** (\<Sum>v\<in>F. outerp (w v)))"
    by (rule trace_mult_add)
  finally show ?case
    using insert by (simp add: trace_mult_outerp)
qed

subsection \<open>Perturbation bounds for sums of column outer products\<close>

text \<open>Along the path the columns are \<open>w u = sqrt (lam u) *\<^sub>R u + d u\<close> with a
  uniform error bound \<open>norm (d u) \<le> e\<close>.  The estimates that keep the field
  inside the constraint set need no operator-norm calculus --- only the
  weighted AM--GM inequality \<open>2ab \<le> \<epsilon>a\<^sup>2 + b\<^sup>2/\<epsilon>\<close> and the finite
  \<open>L\<^sup>1\<close>--\<open>L\<^sup>2\<close> comparison.  \<open>perturbed_columns_eigen_ub\<close> is the upper
  eigenvalue bound with an EXPLICIT smallness condition on \<open>e\<close>; its \<open>lb\<close>
  and trace companions follow in the next batch.\<close>

lemma two_mult_le_weighted:
  fixes a b \<epsilon> :: real
  assumes e0: "0 < \<epsilon>"
  shows "2 * a * b \<le> \<epsilon> * a\<^sup>2 + b\<^sup>2 / \<epsilon>"
proof -
  have sq: "0 \<le> (\<epsilon> * a - b)\<^sup>2" by simp
  have expand: "(\<epsilon> * a - b)\<^sup>2 = \<epsilon> * (\<epsilon> * a\<^sup>2) - \<epsilon> * (2 * a * b) + b\<^sup>2"
    by (simp add: power2_diff power2_eq_square algebra_simps)
  have h: "\<epsilon> * (2 * a * b) \<le> \<epsilon> * (\<epsilon> * a\<^sup>2) + b\<^sup>2"
    using sq expand by linarith
  have "\<epsilon> * (\<epsilon> * a\<^sup>2) + b\<^sup>2 = \<epsilon> * (\<epsilon> * a\<^sup>2 + b\<^sup>2 / \<epsilon>)"
    using e0 by (simp add: field_simps)
  with h have "\<epsilon> * (2 * a * b) \<le> \<epsilon> * (\<epsilon> * a\<^sup>2 + b\<^sup>2 / \<epsilon>)" by simp
  then show ?thesis using e0 by (simp add: mult_le_cancel_left)
qed

lemma add_sq_le_weighted:
  fixes a b \<epsilon> :: real
  assumes e0: "0 < \<epsilon>"
  shows "(a + b)\<^sup>2 \<le> (1 + \<epsilon>) * a\<^sup>2 + (1 + 1 / \<epsilon>) * b\<^sup>2"
proof -
  have "(a + b)\<^sup>2 = a\<^sup>2 + 2 * a * b + b\<^sup>2"
    by (simp add: power2_sum)
  also have "\<dots> \<le> a\<^sup>2 + (\<epsilon> * a\<^sup>2 + b\<^sup>2 / \<epsilon>) + b\<^sup>2"
    using two_mult_le_weighted[OF e0] by simp
  also have "\<dots> = (1 + \<epsilon>) * a\<^sup>2 + (1 + 1 / \<epsilon>) * b\<^sup>2"
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma add_sq_ge_weighted:
  fixes a b \<epsilon> :: real
  assumes e0: "0 < \<epsilon>"
  shows "(1 - \<epsilon>) * a\<^sup>2 - b\<^sup>2 / \<epsilon> \<le> (a + b)\<^sup>2"
proof -
  have "2 * a * (- b) \<le> \<epsilon> * a\<^sup>2 + (- b)\<^sup>2 / \<epsilon>"
    by (rule two_mult_le_weighted[OF e0])
  then have h: "- (2 * a * b) \<le> \<epsilon> * a\<^sup>2 + b\<^sup>2 / \<epsilon>" by simp
  have "(a + b)\<^sup>2 = a\<^sup>2 + 2 * a * b + b\<^sup>2"
    by (simp add: power2_sum)
  moreover have "0 \<le> b\<^sup>2" by simp
  moreover have "(1 - \<epsilon>) * a\<^sup>2 = a\<^sup>2 - \<epsilon> * a\<^sup>2"
    by (simp add: algebra_simps)
  ultimately show ?thesis using h by linarith
qed

lemma sum_abs_sq_le_card:
  fixes f :: "'b \<Rightarrow> real"
  assumes finF: "finite F"
  shows "(\<Sum>i\<in>F. \<bar>f i\<bar>)\<^sup>2 \<le> real (card F) * (\<Sum>i\<in>F. (f i)\<^sup>2)"
  using finF
proof (induction F)
  case empty
  show ?case by simp
next
  case (insert a F)
  show ?case
  proof (cases "F = {}")
    case True
    then show ?thesis by simp
  next
    case False
    define n where "n = real (card F)"
    have n0: "0 < n" unfolding n_def
      using False insert.hyps by (simp add: card_gt_0_iff)
    define T where "T = (\<Sum>i\<in>F. \<bar>f i\<bar>)"
    define S where "S = (\<Sum>i\<in>F. (f i)\<^sup>2)"
    have IH: "T\<^sup>2 \<le> n * S"
      unfolding T_def S_def n_def by (rule insert.IH)
    have cross: "2 * \<bar>f a\<bar> * T \<le> n * \<bar>f a\<bar>\<^sup>2 + T\<^sup>2 / n"
      by (rule two_mult_le_weighted[OF n0])
    have Tdiv: "T\<^sup>2 / n \<le> S"
      using IH n0 by (simp add: divide_le_eq mult.commute)
    have "(\<Sum>i\<in>insert a F. \<bar>f i\<bar>)\<^sup>2 = (\<bar>f a\<bar> + T)\<^sup>2"
      unfolding T_def using insert.hyps by simp
    also have "\<dots> = \<bar>f a\<bar>\<^sup>2 + 2 * \<bar>f a\<bar> * T + T\<^sup>2"
      by (simp add: power2_sum)
    also have "\<dots> \<le> \<bar>f a\<bar>\<^sup>2 + (n * \<bar>f a\<bar>\<^sup>2 + S) + n * S"
      using cross Tdiv IH by linarith
    also have "\<dots> = (n + 1) * ((f a)\<^sup>2 + S)"
      by (simp add: algebra_simps)
    also have "\<dots> = real (card (insert a F)) * (\<Sum>i\<in>insert a F. (f i)\<^sup>2)"
      unfolding n_def S_def using insert.hyps by simp
    finally show ?thesis .
  qed
qed

lemma perturbed_columns_eigen_ub:
  fixes B :: "(real^'n::finite) set" and w d :: "real^'n \<Rightarrow> real^'n"
    and lam :: "real^'n \<Rightarrow> real" and L m e :: real
  assumes B: "onormal B" and sp: "span B = UNIV"
    and wu: "\<And>u. u \<in> B \<Longrightarrow> w u = sqrt (lam u) *\<^sub>R u + d u"
    and lam_nn: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u"
    and lam_ub: "\<And>u. u \<in> B \<Longrightarrow> lam u \<le> L - m"
    and mL: "0 < m" "m \<le> L"
    and de: "\<And>u. u \<in> B \<Longrightarrow> norm (d u) \<le> e" and e0: "0 \<le> e"
    and small: "(1 + 1 / (m / (2 * L))) * (real CARD('n) * e\<^sup>2) \<le> m / 2"
  shows "eigen_ub (\<Sum>u\<in>B. outerp (w u)) L"
  unfolding eigen_ub_def
proof
  fix v :: "real^'n"
  define \<epsilon> where "\<epsilon> = m / (2 * L)"
  have L0: "0 < L" using mL by linarith
  have eps0: "0 < \<epsilon>" unfolding \<epsilon>_def using mL L0 by simp
  have "v \<bullet> ((\<Sum>u\<in>B. outerp (w u)) *v v) = (\<Sum>u\<in>B. (w u \<bullet> v)\<^sup>2)"
    by (rule outerp_sum_quadform)
  also have "\<dots> \<le> (\<Sum>u\<in>B. (1 + \<epsilon>) * (lam u * (u \<bullet> v)\<^sup>2)
      + (1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v)))"
  proof (rule sum_mono)
    fix u assume u: "u \<in> B"
    have split: "w u \<bullet> v = sqrt (lam u) * (u \<bullet> v) + d u \<bullet> v"
      by (simp add: wu[OF u] inner_add_left)
    have sqterm: "(sqrt (lam u) * (u \<bullet> v))\<^sup>2 = lam u * (u \<bullet> v)\<^sup>2"
      using lam_nn[OF u] by (simp add: power_mult_distrib)
    have dv: "(d u \<bullet> v)\<^sup>2 \<le> e\<^sup>2 * (v \<bullet> v)"
    proof -
      have h1: "\<bar>d u \<bullet> v\<bar> \<le> norm (d u) * norm v"
        by (rule Cauchy_Schwarz_ineq2)
      have h2: "norm (d u) * norm v \<le> e * norm v"
        using de[OF u] by (intro mult_right_mono) simp_all
      have h3: "\<bar>d u \<bullet> v\<bar> \<le> e * norm v" using h1 h2 by linarith
      have h4: "0 \<le> e * norm v" using e0 by simp
      have "(d u \<bullet> v)\<^sup>2 = \<bar>d u \<bullet> v\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (e * norm v)\<^sup>2"
        using h3 h4 by (intro power_mono) simp_all
      finally show ?thesis
        by (simp add: power_mult_distrib power2_norm_eq_inner)
    qed
    have "(w u \<bullet> v)\<^sup>2 \<le> (1 + \<epsilon>) * (sqrt (lam u) * (u \<bullet> v))\<^sup>2
        + (1 + 1 / \<epsilon>) * (d u \<bullet> v)\<^sup>2"
      unfolding split by (rule add_sq_le_weighted[OF eps0])
    also have "\<dots> \<le> (1 + \<epsilon>) * (lam u * (u \<bullet> v)\<^sup>2)
        + (1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v))"
    proof -
      have inv0: "0 \<le> 1 + 1 / \<epsilon>" using eps0 by simp
      show ?thesis
        unfolding sqterm using dv inv0
        by (intro add_left_mono mult_left_mono)
    qed
    finally show "(w u \<bullet> v)\<^sup>2 \<le> (1 + \<epsilon>) * (lam u * (u \<bullet> v)\<^sup>2)
        + (1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v))" .
  qed
  also have "\<dots> = (1 + \<epsilon>) * (\<Sum>u\<in>B. lam u * (u \<bullet> v)\<^sup>2)
      + real (card B) * ((1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v)))"
    by (simp add: sum.distrib sum_distrib_left mult.commute)
  also have "\<dots> \<le> (1 + \<epsilon>) * ((L - m) * (v \<bullet> v))
      + real CARD('n) * ((1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v)))"
  proof (intro add_mono mult_left_mono)
    have "(\<Sum>u\<in>B. lam u * (u \<bullet> v)\<^sup>2) \<le> (\<Sum>u\<in>B. (L - m) * (u \<bullet> v)\<^sup>2)"
      by (intro sum_mono mult_right_mono lam_ub) simp_all
    also have "\<dots> = (L - m) * (\<Sum>u\<in>B. (u \<bullet> v)\<^sup>2)"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (L - m) * (v \<bullet> v)"
      by (simp add: onormal_parseval[OF B sp])
    finally show "(\<Sum>u\<in>B. lam u * (u \<bullet> v)\<^sup>2) \<le> (L - m) * (v \<bullet> v)" .
    have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF B sp])
    have term_nn: "0 \<le> (1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v))"
      using eps0 by (intro mult_nonneg_nonneg) simp_all
    show "real (card B) * ((1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v)))
        \<le> real CARD('n) * ((1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v)))"
      unfolding cardB by simp
    show "0 \<le> 1 + \<epsilon>" using eps0 by simp
  qed
  also have "\<dots> \<le> L * (v \<bullet> v)"
  proof -
    have vv: "0 \<le> v \<bullet> v" by simp
    have h1: "(1 + \<epsilon>) * (L - m) \<le> L - m / 2"
    proof -
      have "\<epsilon> * (L - m) \<le> \<epsilon> * L"
        using eps0 mL by (intro mult_left_mono) simp_all
      moreover have "\<epsilon> * L = m / 2" unfolding \<epsilon>_def using L0 by simp
      ultimately show ?thesis by (simp add: algebra_simps)
    qed
    have h2: "real CARD('n) * ((1 + 1 / \<epsilon>) * e\<^sup>2) \<le> m / 2"
      using small unfolding \<epsilon>_def by (simp add: algebra_simps)
    have "(1 + \<epsilon>) * ((L - m) * (v \<bullet> v))
        + real CARD('n) * ((1 + 1 / \<epsilon>) * (e\<^sup>2 * (v \<bullet> v)))
        = ((1 + \<epsilon>) * (L - m)
            + real CARD('n) * ((1 + 1 / \<epsilon>) * e\<^sup>2)) * (v \<bullet> v)"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> L * (v \<bullet> v)"
      using h1 h2 vv by (intro mult_right_mono) linarith+
    finally show ?thesis .
  qed
  finally show "v \<bullet> ((\<Sum>u\<in>B. outerp (w u)) *v v) \<le> L * (v \<bullet> v)" .
qed

lemma perturbed_columns_eigen_lb:
  fixes B Bp :: "(real^'n::finite) set" and w :: "real^'n \<Rightarrow> real^'n"
    and lam :: "real^'n \<Rightarrow> real" and m E :: real
  assumes finB: "finite B" and BpB: "Bp \<subseteq> B"
    and lam_lb: "\<And>u. u \<in> Bp \<Longrightarrow> 1 + m \<le> lam u"
    and m0: "0 < m"
    and gram: "\<And>u u'. u \<in> Bp \<Longrightarrow> u' \<in> Bp \<Longrightarrow>
        \<bar>w u \<bullet> w u' - (if u' = u then lam u else 0)\<bar> \<le> E"
    and E0: "0 \<le> E"
    and small: "real (card Bp) * E
        + 2 * (1 + m) / m * (real (card Bp) * E)\<^sup>2 \<le> m / 2"
  shows "eigen_lb (\<Sum>u\<in>B. outerp (w u)) (card Bp)"
proof -
  define A where "A = (\<Sum>u\<in>B. outerp (w u))"
  define np where "np = real (card Bp)"
  define \<epsilon> where "\<epsilon> = m / (2 * (1 + m))"
  define D1 where "D1 = np * E"
  define D2 where "D2 = 2 * (1 + m) / m * (np * E)\<^sup>2"
  have finBp: "finite Bp" by (rule finite_subset[OF BpB finB])
  have np0: "0 \<le> np" unfolding np_def by simp
  have m1: "0 < 1 + m" using m0 by simp
  have eps0: "0 < \<epsilon>" unfolding \<epsilon>_def using m0 m1 by simp
  have eps1: "\<epsilon> \<le> 1" unfolding \<epsilon>_def using m0 m1
    by (simp add: divide_le_eq)
  have D10: "0 \<le> D1" unfolding D1_def np_def using E0 by simp
  have D20: "0 \<le> D2" unfolding D2_def using m0 m1
    by (intro mult_nonneg_nonneg) simp_all
  have smallD: "D1 + D2 \<le> m / 2"
    using small unfolding D1_def D2_def np_def .
  have epsprod: "(1 - \<epsilon>) * (1 + m) = 1 + m / 2"
    unfolding \<epsilon>_def using m1 by (simp add: field_simps)
  have epsinv: "1 / \<epsilon> = 2 * (1 + m) / m"
    unfolding \<epsilon>_def using m0 m1 by (simp add: field_simps)
  have cores:
    "vv \<bullet> vv \<le> slc + D1 * nc2
     \<and> (1 + m / 2) * slc - D2 * nc2 \<le> vv \<bullet> (A *v vv)
     \<and> (1 + m) * nc2 \<le> slc"
    if vvdef: "vv = (\<Sum>u\<in>Bp. c u *\<^sub>R w u)"
      and slcdef: "slc = (\<Sum>u\<in>Bp. lam u * (c u)\<^sup>2)"
      and ncdef: "nc2 = (\<Sum>u\<in>Bp. (c u)\<^sup>2)"
    for c :: "real^'n \<Rightarrow> real" and vv :: "real^'n" and slc nc2 :: real
  proof -
    define g where "g = (\<lambda>u u'. w u \<bullet> w u' - (if u' = u then lam u else 0))"
    have gE: "\<bar>g u u'\<bar> \<le> E" if "u \<in> Bp" "u' \<in> Bp" for u u'
      unfolding g_def using gram[OF that] .
    define r where "r = (\<lambda>u. \<Sum>u'\<in>Bp. c u' * g u u')"
    define sac where "sac = (\<Sum>u\<in>Bp. \<bar>c u\<bar>)"
    have sac0: "0 \<le> sac" unfolding sac_def by (rule sum_nonneg) simp
    have nc0: "0 \<le> nc2" unfolding ncdef by (rule sum_nonneg) simp
    have slc0: "0 \<le> slc" unfolding slcdef
      by (rule sum_nonneg)
        (use lam_lb m0 in \<open>auto intro!: mult_nonneg_nonneg
          simp: order_trans[of 0 "1 + m"]\<close>)
    have sac2: "sac\<^sup>2 \<le> np * nc2"
      unfolding sac_def ncdef np_def by (rule sum_abs_sq_le_card[OF finBp])
    have wv: "w u \<bullet> vv = lam u * c u + r u" if u: "u \<in> Bp" for u
    proof -
      have "w u \<bullet> vv = (\<Sum>u'\<in>Bp. c u' * (w u \<bullet> w u'))"
        unfolding vvdef by (simp add: inner_sum_right inner_scaleR_right)
      also have "\<dots> = (\<Sum>u'\<in>Bp. c u' * (if u' = u then lam u else 0)
          + c u' * g u u')"
        by (rule sum.cong[OF refl]) (simp add: g_def algebra_simps)
      also have "\<dots> = (\<Sum>u'\<in>Bp. c u' * (if u' = u then lam u else 0))
          + (\<Sum>u'\<in>Bp. c u' * g u u')"
        by (rule sum.distrib)
      also have "(\<Sum>u'\<in>Bp. c u' * (if u' = u then lam u else 0))
          = (\<Sum>u'\<in>Bp. if u' = u then c u' * lam u else 0)"
        by (rule sum.cong[OF refl]) simp
      also have "\<dots> = c u * lam u"
        using u finBp by (simp add: sum.delta)
      finally show ?thesis unfolding r_def by (simp add: mult.commute)
    qed
    have rb: "\<bar>r u\<bar> \<le> E * sac" if u: "u \<in> Bp" for u
    proof -
      have "\<bar>r u\<bar> \<le> (\<Sum>u'\<in>Bp. \<bar>c u' * g u u'\<bar>)"
        unfolding r_def by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>u'\<in>Bp. \<bar>c u'\<bar> * E)"
      proof (rule sum_mono)
        fix u' assume u': "u' \<in> Bp"
        have "\<bar>c u' * g u u'\<bar> = \<bar>c u'\<bar> * \<bar>g u u'\<bar>"
          by (simp add: abs_mult)
        also have "\<dots> \<le> \<bar>c u'\<bar> * E"
          by (intro mult_left_mono gE[OF u u']) simp
        finally show "\<bar>c u' * g u u'\<bar> \<le> \<bar>c u'\<bar> * E" .
      qed
      also have "\<dots> = sac * E"
        unfolding sac_def by (rule sum_distrib_right[symmetric])
      finally show ?thesis by (simp add: mult.commute)
    qed
    have vv_eq: "vv \<bullet> vv = slc + (\<Sum>u\<in>Bp. c u * r u)"
    proof -
      have "vv \<bullet> vv = (\<Sum>u\<in>Bp. (c u *\<^sub>R w u) \<bullet> vv)"
        by (subst (1) vvdef) (rule inner_sum_left)
      also have "\<dots> = (\<Sum>u\<in>Bp. c u * (lam u * c u + r u))"
        by (rule sum.cong[OF refl]) (simp add: inner_scaleR_left wv)
      also have "\<dots> = (\<Sum>u\<in>Bp. lam u * (c u)\<^sup>2 + c u * r u)"
        by (rule sum.cong[OF refl]) (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = slc + (\<Sum>u\<in>Bp. c u * r u)"
        unfolding slcdef by (rule sum.distrib)
      finally show ?thesis .
    qed
    have crb: "\<bar>\<Sum>u\<in>Bp. c u * r u\<bar> \<le> D1 * nc2"
    proof -
      have "\<bar>\<Sum>u\<in>Bp. c u * r u\<bar> \<le> (\<Sum>u\<in>Bp. \<bar>c u * r u\<bar>)"
        by (rule sum_abs)
      also have "\<dots> \<le> (\<Sum>u\<in>Bp. \<bar>c u\<bar> * (E * sac))"
      proof (rule sum_mono)
        fix u assume u: "u \<in> Bp"
        have "\<bar>c u * r u\<bar> = \<bar>c u\<bar> * \<bar>r u\<bar>" by (simp add: abs_mult)
        also have "\<dots> \<le> \<bar>c u\<bar> * (E * sac)"
          by (intro mult_left_mono rb[OF u]) simp
        finally show "\<bar>c u * r u\<bar> \<le> \<bar>c u\<bar> * (E * sac)" .
      qed
      also have "\<dots> = sac * (E * sac)"
        unfolding sac_def by (rule sum_distrib_right[symmetric])
      also have "\<dots> = E * sac\<^sup>2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> E * (np * nc2)"
        using sac2 E0 by (intro mult_left_mono)
      also have "\<dots> = D1 * nc2"
        unfolding D1_def by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have core2: "vv \<bullet> vv \<le> slc + D1 * nc2"
      using vv_eq crb by linarith
    have Av: "vv \<bullet> (A *v vv) = (\<Sum>u\<in>B. (w u \<bullet> vv)\<^sup>2)"
      unfolding A_def by (rule outerp_sum_quadform)
    have geBp: "(\<Sum>u\<in>Bp. (w u \<bullet> vv)\<^sup>2) \<le> (\<Sum>u\<in>B. (w u \<bullet> vv)\<^sup>2)"
      by (rule sum_mono2[OF finB BpB]) simp
    have r2b: "(\<Sum>u\<in>Bp. (r u)\<^sup>2) \<le> (np * E)\<^sup>2 * nc2"
    proof -
      have "(\<Sum>u\<in>Bp. (r u)\<^sup>2) \<le> (\<Sum>u\<in>Bp. (E * sac)\<^sup>2)"
      proof (rule sum_mono)
        fix u assume u: "u \<in> Bp"
        have "(r u)\<^sup>2 = \<bar>r u\<bar>\<^sup>2" by simp
        also have "\<dots> \<le> (E * sac)\<^sup>2"
          using rb[OF u] E0 sac0 by (intro power_mono) simp_all
        finally show "(r u)\<^sup>2 \<le> (E * sac)\<^sup>2" .
      qed
      also have "\<dots> = np * (E\<^sup>2 * sac\<^sup>2)"
        unfolding np_def by (simp add: power_mult_distrib)
      also have "\<dots> \<le> np * (E\<^sup>2 * (np * nc2))"
        using sac2 np0 by (intro mult_left_mono) simp_all
      also have "\<dots> = (np * E)\<^sup>2 * nc2"
        by (simp add: power_mult_distrib power2_eq_square algebra_simps)
      finally show ?thesis .
    qed
    have lam2: "(1 + m) * slc \<le> (\<Sum>u\<in>Bp. (lam u * c u)\<^sup>2)"
    proof -
      have "(1 + m) * slc = (\<Sum>u\<in>Bp. (1 + m) * lam u * (c u)\<^sup>2)"
        unfolding slcdef by (simp add: sum_distrib_left algebra_simps)
      also have "\<dots> \<le> (\<Sum>u\<in>Bp. (lam u * c u)\<^sup>2)"
      proof (rule sum_mono)
        fix u assume u: "u \<in> Bp"
        have lu0: "0 \<le> lam u" using lam_lb[OF u] m0 by linarith
        have "(1 + m) * lam u \<le> lam u * lam u"
          by (rule mult_right_mono[OF lam_lb[OF u] lu0])
        then have "(1 + m) * lam u * (c u)\<^sup>2 \<le> lam u * lam u * (c u)\<^sup>2"
          by (rule mult_right_mono) simp
        then show "(1 + m) * lam u * (c u)\<^sup>2 \<le> (lam u * c u)\<^sup>2"
          by (simp add: power_mult_distrib power2_eq_square algebra_simps)
      qed
      finally show ?thesis .
    qed
    have core1: "(1 + m / 2) * slc - D2 * nc2 \<le> vv \<bullet> (A *v vv)"
    proof -
      have perlow: "(1 - \<epsilon>) * (lam u * c u)\<^sup>2 - (r u)\<^sup>2 / \<epsilon>
          \<le> (w u \<bullet> vv)\<^sup>2" if u: "u \<in> Bp" for u
        using add_sq_ge_weighted[OF eps0, of "lam u * c u" "r u"] wv[OF u]
        by simp
      have "(1 - \<epsilon>) * (\<Sum>u\<in>Bp. (lam u * c u)\<^sup>2)
          - (\<Sum>u\<in>Bp. (r u)\<^sup>2) / \<epsilon>
          = (\<Sum>u\<in>Bp. (1 - \<epsilon>) * (lam u * c u)\<^sup>2 - (r u)\<^sup>2 / \<epsilon>)"
        by (simp add: sum_subtractf sum_distrib_left sum_divide_distrib)
      also have "\<dots> \<le> (\<Sum>u\<in>Bp. (w u \<bullet> vv)\<^sup>2)"
        by (rule sum_mono) (rule perlow)
      also have "\<dots> \<le> vv \<bullet> (A *v vv)"
        unfolding Av by (rule geBp)
      finally have h: "(1 - \<epsilon>) * (\<Sum>u\<in>Bp. (lam u * c u)\<^sup>2)
          - (\<Sum>u\<in>Bp. (r u)\<^sup>2) / \<epsilon> \<le> vv \<bullet> (A *v vv)" .
      have h1: "(1 + m / 2) * slc
          \<le> (1 - \<epsilon>) * (\<Sum>u\<in>Bp. (lam u * c u)\<^sup>2)"
      proof -
        have "(1 + m / 2) * slc = (1 - \<epsilon>) * ((1 + m) * slc)"
          by (simp only: mult.assoc[symmetric] epsprod)
        also have "\<dots> \<le> (1 - \<epsilon>) * (\<Sum>u\<in>Bp. (lam u * c u)\<^sup>2)"
          using lam2 eps1 by (intro mult_left_mono) simp_all
        finally show ?thesis .
      qed
      have h2: "(\<Sum>u\<in>Bp. (r u)\<^sup>2) / \<epsilon> \<le> D2 * nc2"
      proof -
        have "(\<Sum>u\<in>Bp. (r u)\<^sup>2) / \<epsilon> \<le> ((np * E)\<^sup>2 * nc2) / \<epsilon>"
          by (intro divide_right_mono r2b) (use eps0 in simp)
        also have "\<dots> = (1 / \<epsilon>) * ((np * E)\<^sup>2 * nc2)"
          by simp
        also have "\<dots> = D2 * nc2"
          unfolding D2_def epsinv by (simp add: algebra_simps)
        finally show ?thesis .
      qed
      show ?thesis using h h1 h2 by linarith
    qed
    have core3: "(1 + m) * nc2 \<le> slc"
      unfolding slcdef ncdef
      by (subst sum_distrib_left)
        (rule sum_mono, intro mult_right_mono lam_lb, simp_all)
    show ?thesis using core2 core1 core3 by blast
  qed
  have bracket: "0 < (1 + m / 2) * (1 + m) - D2"
  proof -
    have "(1 + m / 2) * (1 + m) = 1 + 3 * m / 2 + m\<^sup>2 / 2"
      by (simp add: power2_eq_square field_simps)
    moreover have "D2 \<le> m / 2" using smallD D10 by linarith
    moreover have "0 \<le> m\<^sup>2 / 2" by simp
    ultimately show ?thesis using m0 by linarith
  qed
  have kernel: "c u = 0"
    if z: "(\<Sum>u\<in>Bp. c u *\<^sub>R w u) = 0" and u: "u \<in> Bp"
    for c :: "real^'n \<Rightarrow> real" and u
  proof -
    define nc2 where "nc2 = (\<Sum>u\<in>Bp. (c u)\<^sup>2)"
    define slc where "slc = (\<Sum>u\<in>Bp. lam u * (c u)\<^sup>2)"
    have h: "(\<Sum>u\<in>Bp. c u *\<^sub>R w u) \<bullet> (\<Sum>u\<in>Bp. c u *\<^sub>R w u) \<le> slc + D1 * nc2
        \<and> (1 + m / 2) * slc - D2 * nc2
          \<le> (\<Sum>u\<in>Bp. c u *\<^sub>R w u) \<bullet> (A *v (\<Sum>u\<in>Bp. c u *\<^sub>R w u))
        \<and> (1 + m) * nc2 \<le> slc"
      unfolding slc_def nc2_def by (rule cores[OF refl refl refl])
    have zero: "(1 + m / 2) * slc - D2 * nc2 \<le> 0"
      using h unfolding z by (simp add: matvec_zero_left)
    have le: "(1 + m) * nc2 \<le> slc" using h by blast
    have nc0: "0 \<le> nc2" unfolding nc2_def by (rule sum_nonneg) simp
    have "(1 + m / 2) * ((1 + m) * nc2) \<le> (1 + m / 2) * slc"
      using le m0 by (intro mult_left_mono) simp_all
    with zero have "((1 + m / 2) * (1 + m) - D2) * nc2 \<le> 0"
      by (simp add: algebra_simps)
    with bracket nc0 have nc2z: "nc2 = 0"
      by (metis mult_pos_pos not_le order_less_irrefl
          order_le_less zero_less_mult_iff)
    have "(c u)\<^sup>2 = 0"
    proof (rule ccontr)
      assume ne: "(c u)\<^sup>2 \<noteq> 0"
      have "0 < (c u)\<^sup>2" using ne by (simp add: order_less_le)
      then have "0 < nc2" unfolding nc2_def
        by (meson finBp sum_pos2 u zero_le_power2)
      then show False using nc2z by simp
    qed
    then show ?thesis by simp
  qed
  have inj: "inj_on w Bp"
  proof (rule inj_onI)
    fix u u' assume u: "u \<in> Bp" and u': "u' \<in> Bp" and eq: "w u = w u'"
    show "u = u'"
    proof (rule ccontr)
      assume neq: "u \<noteq> u'"
      define c where "c = (\<lambda>v :: real^'n.
          if v = u then 1 else if v = u' then - 1 else (0 :: real))"
      have "(\<Sum>v\<in>Bp. c v *\<^sub>R w v)
          = (\<Sum>v\<in>Bp. (if v = u then w v else 0))
            + (\<Sum>v\<in>Bp. (if v = u' then - w v else 0))"
        unfolding c_def
        by (subst sum.distrib[symmetric])
          (rule sum.cong[OF refl], use neq in auto)
      also have "\<dots> = w u - w u'"
        using u u' finBp by (simp add: sum.delta)
      also have "\<dots> = 0" using eq by simp
      finally have "c u = 0" by (rule kernel[OF _ u])
      then show False unfolding c_def by simp
    qed
  qed
  have indep: "independent (w ` Bp)"
  proof (rule ccontr)
    assume "\<not> independent (w ` Bp)"
    then have "dependent (w ` Bp)" by simp
    then obtain t cc where t: "finite t" "t \<subseteq> w ` Bp"
      and z: "(\<Sum>v\<in>t. cc v *\<^sub>R v) = 0"
      and ex: "\<exists>v\<in>t. cc v \<noteq> 0"
      unfolding dependent_explicit by blast
    obtain y where y: "y \<in> t" "cc y \<noteq> 0" using ex by blast
    define Bt where "Bt = {u \<in> Bp. w u \<in> t}"
    have BtBp: "Bt \<subseteq> Bp" unfolding Bt_def by blast
    have wBt: "w ` Bt = t"
    proof
      show "w ` Bt \<subseteq> t" unfolding Bt_def by blast
      show "t \<subseteq> w ` Bt"
      proof
        fix v assume v: "v \<in> t"
        then obtain u where u: "u \<in> Bp" "v = w u" using t(2) by blast
        then have "u \<in> Bt" unfolding Bt_def using v by blast
        then show "v \<in> w ` Bt" using u by blast
      qed
    qed
    define c where "c = (\<lambda>u. if u \<in> Bt then cc (w u) else 0)"
    have injBt: "inj_on w Bt" by (rule inj_on_subset[OF inj BtBp])
    have "(\<Sum>u\<in>Bp. c u *\<^sub>R w u) = (\<Sum>u\<in>Bt. c u *\<^sub>R w u)"
      by (rule sum.mono_neutral_right[OF finBp BtBp])
        (simp add: c_def)
    also have "\<dots> = (\<Sum>u\<in>Bt. cc (w u) *\<^sub>R w u)"
      by (rule sum.cong[OF refl]) (simp add: c_def)
    also have "\<dots> = (\<Sum>v\<in>w ` Bt. cc v *\<^sub>R v)"
      by (simp add: sum.reindex[OF injBt] o_def)
    also have "\<dots> = 0" unfolding wBt by (rule z)
    finally have zz: "(\<Sum>u\<in>Bp. c u *\<^sub>R w u) = 0" .
    obtain u0 where u0: "u0 \<in> Bt" "w u0 = y"
      using y(1) wBt by blast
    have "c u0 = 0" using kernel[OF zz] u0(1) BtBp by blast
    then show False unfolding c_def using u0 y(2) by simp
  qed
  have quad: "vv \<bullet> vv \<le> vv \<bullet> (A *v vv)"
    if vv: "vv \<in> span (w ` Bp)" for vv
  proof -
    have "span (w ` Bp) = range (\<lambda>u. \<Sum>v\<in>w ` Bp. u v *\<^sub>R v)"
      by (rule span_finite) (simp add: finBp)
    then obtain cc where ccdef: "vv = (\<Sum>v\<in>w ` Bp. cc v *\<^sub>R v)"
      using vv by auto
    define c where "c = (\<lambda>u. cc (w u))"
    have vrep: "vv = (\<Sum>u\<in>Bp. c u *\<^sub>R w u)"
      unfolding ccdef c_def by (simp add: sum.reindex[OF inj] o_def)
    define nc2 where "nc2 = (\<Sum>u\<in>Bp. (c u)\<^sup>2)"
    define slc where "slc = (\<Sum>u\<in>Bp. lam u * (c u)\<^sup>2)"
    have h: "vv \<bullet> vv \<le> slc + D1 * nc2
        \<and> (1 + m / 2) * slc - D2 * nc2 \<le> vv \<bullet> (A *v vv)
        \<and> (1 + m) * nc2 \<le> slc"
      unfolding slc_def nc2_def by (rule cores[OF vrep refl refl])
    have nc0: "0 \<le> nc2" unfolding nc2_def by (rule sum_nonneg) simp
    have le3: "(1 + m) * nc2 \<le> slc" using h by blast
    have le1: "vv \<bullet> vv \<le> slc + D1 * nc2" using h by blast
    have le2: "(1 + m / 2) * slc - D2 * nc2 \<le> vv \<bullet> (A *v vv)"
      using h by blast
    have mn: "0 \<le> m * nc2"
      using m0 nc0 by (intro mult_nonneg_nonneg) simp_all
    have "(1 + m) * nc2 = nc2 + m * nc2" by (simp add: algebra_simps)
    with le3 mn have nc_le_slc: "nc2 \<le> slc" by linarith
    have "(D1 + D2) * nc2 \<le> (m / 2) * nc2"
      using smallD nc0 by (intro mult_right_mono)
    also have "\<dots> \<le> (m / 2) * slc"
      using nc_le_slc m0 by (intro mult_left_mono) simp_all
    finally have "(D1 + D2) * nc2 \<le> (m / 2) * slc" .
    then have "slc + D1 * nc2 \<le> (1 + m / 2) * slc - D2 * nc2"
      by (simp add: algebra_simps)
    then show ?thesis using le1 le2 by linarith
  qed
  have dimS: "card Bp \<le> dim (span (w ` Bp))"
  proof -
    have "dim (span (w ` Bp)) = card (w ` Bp)"
      by (rule dim_span_eq_card_independent[OF indep])
    also have "card (w ` Bp) = card Bp"
      by (rule card_image[OF inj])
    finally show ?thesis by simp
  qed
  show ?thesis
    unfolding eigen_lb_def A_def[symmetric]
    by (intro exI[of _ "span (w ` Bp)"] conjI subspace_span dimS ballI quad)
qed

lemma perturbed_columns_trace_close:
  fixes B :: "(real^'n::finite) set" and w d :: "real^'n \<Rightarrow> real^'n"
    and lam :: "real^'n \<Rightarrow> real" and M :: "real^'n^'n" and L e :: real
  assumes finB: "finite B"
    and wu: "\<And>u. u \<in> B \<Longrightarrow> w u = sqrt (lam u) *\<^sub>R u + d u"
    and nu: "\<And>u. u \<in> B \<Longrightarrow> norm u = 1"
    and lam_nn: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u"
    and lam_ub: "\<And>u. u \<in> B \<Longrightarrow> lam u \<le> L"
    and de: "\<And>u. u \<in> B \<Longrightarrow> norm (d u) \<le> e" and e0: "0 \<le> e"
  shows "\<bar>trace (M ** (\<Sum>u\<in>B. outerp (w u)))
      - (\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))\<bar>
    \<le> real (card B) * ((\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)
        * (e * (2 * sqrt L + e)))"
proof -
  define Cm where "Cm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  have Cm0: "0 \<le> Cm" unfolding Cm_def
    by (intro sum_nonneg) simp_all
  have per_term: "\<bar>w u \<bullet> (M *v w u) - lam u * (u \<bullet> (M *v u))\<bar>
      \<le> Cm * (e * (2 * sqrt L + e))" if u: "u \<in> B" for u
  proof -
    define su where "su = sqrt (lam u) *\<^sub>R u"
    have sL: "sqrt (lam u) \<le> sqrt L"
      using lam_ub[OF u] by (rule real_sqrt_le_mono)
    have s0: "0 \<le> sqrt (lam u)"
      using lam_nn[OF u] by simp
    have nsu: "norm su \<le> sqrt L"
      unfolding su_def using nu[OF u] s0 sL by simp
    have sMs: "su \<bullet> (M *v su) = lam u * (u \<bullet> (M *v u))"
      unfolding su_def
      by (simp add: algebra_simps lam_nn[OF u])
    have wsplit: "w u = su + d u" unfolding su_def by (rule wu[OF u])
    have expand: "w u \<bullet> (M *v w u) - su \<bullet> (M *v su)
        = d u \<bullet> (M *v w u) + su \<bullet> (M *v d u)"
    proof -
      have "w u \<bullet> (M *v w u) = su \<bullet> (M *v w u) + d u \<bullet> (M *v w u)"
        by (subst (1) wsplit) (simp add: inner_add_left)
      moreover have "su \<bullet> (M *v w u)
          = su \<bullet> (M *v su) + su \<bullet> (M *v d u)"
        by (subst wsplit) (simp add: algebra_simps)
      ultimately show ?thesis by linarith
    qed
    have nw: "norm (w u) \<le> sqrt L + e"
    proof -
      have "norm (w u) \<le> norm su + norm (d u)"
        unfolding wsplit by (rule norm_triangle_ineq)
      then show ?thesis using nsu de[OF u] by linarith
    qed
    have b1: "\<bar>d u \<bullet> (M *v w u)\<bar> \<le> e * (Cm * (sqrt L + e))"
    proof -
      have "\<bar>d u \<bullet> (M *v w u)\<bar> \<le> norm (d u) * norm (M *v w u)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> e * (Cm * (sqrt L + e))"
      proof (intro mult_mono)
        show "norm (d u) \<le> e" by (rule de[OF u])
        have "norm (M *v w u) \<le> Cm * norm (w u)"
          unfolding Cm_def by (rule matvec_norm_le)
        also have "\<dots> \<le> Cm * (sqrt L + e)"
          using nw Cm0 by (intro mult_left_mono)
        finally show "norm (M *v w u) \<le> Cm * (sqrt L + e)" .
        show "0 \<le> e" by (rule e0)
        show "0 \<le> norm (M *v w u)" by simp
      qed
      finally show ?thesis .
    qed
    have b2: "\<bar>su \<bullet> (M *v d u)\<bar> \<le> sqrt L * (Cm * e)"
    proof -
      have "\<bar>su \<bullet> (M *v d u)\<bar> \<le> norm su * norm (M *v d u)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> sqrt L * (Cm * e)"
      proof (intro mult_mono)
        show "norm su \<le> sqrt L" by (rule nsu)
        have "norm (M *v d u) \<le> Cm * norm (d u)"
          unfolding Cm_def by (rule matvec_norm_le)
        also have "\<dots> \<le> Cm * e"
          using de[OF u] Cm0 by (intro mult_left_mono)
        finally show "norm (M *v d u) \<le> Cm * e" .
        show "0 \<le> sqrt L" using s0 sL by linarith
        show "0 \<le> norm (M *v d u)" by simp
      qed
      finally show ?thesis .
    qed
    have "\<bar>w u \<bullet> (M *v w u) - lam u * (u \<bullet> (M *v u))\<bar>
        \<le> \<bar>d u \<bullet> (M *v w u)\<bar> + \<bar>su \<bullet> (M *v d u)\<bar>"
      using expand sMs by linarith
    also have "\<dots> \<le> e * (Cm * (sqrt L + e)) + sqrt L * (Cm * e)"
      using b1 b2 by linarith
    also have "\<dots> = Cm * (e * (2 * sqrt L + e))"
      by (simp add: algebra_simps power2_eq_square)
    finally show ?thesis .
  qed
  have "\<bar>trace (M ** (\<Sum>u\<in>B. outerp (w u)))
      - (\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))\<bar>
      = \<bar>\<Sum>u\<in>B. w u \<bullet> (M *v w u) - lam u * (u \<bullet> (M *v u))\<bar>"
    by (simp add: trace_mult_outerp_sum[OF finB] sum_subtractf)
  also have "\<dots> \<le> (\<Sum>u\<in>B. \<bar>w u \<bullet> (M *v w u) - lam u * (u \<bullet> (M *v u))\<bar>)"
    by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>u\<in>B. Cm * (e * (2 * sqrt L + e)))"
    by (rule sum_mono) (rule per_term)
  also have "\<dots> = real (card B) * (Cm * (e * (2 * sqrt L + e)))"
    by simp
  finally show ?thesis unfolding Cm_def .
qed

subsection \<open>The skew covariance field\<close>

text \<open>The field of the paper's (3.24), Girsanov-free: at the point \<open>z\<close> the
  columns are the skew images of the CURRENT gradient \<open>q + M (z - x)\<close> of the
  quadratic minorant, so the field annihilates that gradient EVERYWHERE ---
  no stochastic integral will ever be needed to kill the first-order term.
  On a ball whose radius satisfies three explicit smallness conditions the
  field stays inside the constraint set and keeps the trace margin.\<close>

definition skewfield ::
  "(real^'n::finite) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> real^'n
     \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "skewfield B lam q M x z
    = (\<Sum>u\<in>B. outerp (skewv q (sqrt (lam u) *\<^sub>R u) *v (q + M *v (z - x))))"

theorem skewfield_properties:
  fixes B Bp :: "(real^'n::finite) set" and lam :: "real^'n \<Rightarrow> real"
    and q x z :: "real^'n" and M :: "real^'n^'n" and L m r \<eta> :: real
  defines "Cm \<equiv> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  defines "ec \<equiv> 2 * sqrt L * Cm / norm q"
  assumes B: "onormal B" and sp: "span B = UNIV"
    and BpB: "Bp \<subseteq> B" and cardBp: "card Bp = CARD('n) - k"
    and lam_box: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u \<and> lam u \<le> L - m"
    and lam_lb: "\<And>u. u \<in> Bp \<Longrightarrow> 1 + m \<le> lam u"
    and lam_orth: "\<And>u. u \<in> B \<Longrightarrow> 0 < lam u \<Longrightarrow> u \<bullet> q = 0"
    and m0: "0 < m" and mL: "m \<le> L"
    and q0: "q \<noteq> 0"
    and tr: "\<eta> \<le> 1 + trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2"
    and zr: "dist z x \<le> r" and r0: "0 \<le> r"
    and sm_ub: "(1 + 1 / (m / (2 * L)))
        * (real CARD('n) * (ec * r)\<^sup>2) \<le> m / 2"
    and sm_lb: "real CARD('n) * (ec * r * (2 * sqrt L + ec * r))
        + 2 * (1 + m) / m
          * (real CARD('n) * (ec * r * (2 * sqrt L + ec * r)))\<^sup>2 \<le> m / 2"
    and sm_tr: "real CARD('n)
        * (Cm * (ec * r * (2 * sqrt L + ec * r))) \<le> \<eta>"
  shows "skewfield B lam q M x z \<in> sconstraint k L"
    and "skewfield B lam q M x z *v (q + M *v (z - x)) = 0"
    and "\<eta> / 2 \<le> 1 + trace (M ** skewfield B lam q M x z) / 2"
proof -
  define grad where "grad = q + M *v (z - x)"
  define w where "w = (\<lambda>u. skewv q (sqrt (lam u) *\<^sub>R u) *v grad)"
  define d where "d = (\<lambda>u. w u - sqrt (lam u) *\<^sub>R u)"
  define e where "e = ec * r"
  have finB: "finite B" by (rule onormal_finite[OF B])
  have L0: "0 < L" using m0 mL by linarith
  have sqL0: "0 \<le> sqrt L" using L0 by simp
  have Cm0: "0 \<le> Cm" unfolding Cm_def by (intro sum_nonneg) simp_all
  have nq0: "0 < norm q" using q0 by simp
  have ec0: "0 \<le> ec" unfolding ec_def using sqL0 Cm0 nq0 by simp
  have e0: "0 \<le> e" unfolding e_def using ec0 r0 by simp
  have sfw: "skewfield B lam q M x z = (\<Sum>u\<in>B. outerp (w u))"
    unfolding skewfield_def w_def grad_def ..
  have lam_nn: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u"
    and lam_ub: "\<And>u. u \<in> B \<Longrightarrow> lam u \<le> L - m"
    using lam_box by blast+
  have lam_leL: "lam u \<le> L" if u: "u \<in> B" for u
    using lam_ub[OF u] m0 by linarith
  have sqlam_le: "sqrt (lam u) \<le> sqrt L" if u: "u \<in> B" for u
    using lam_leL[OF u] by (rule real_sqrt_le_mono)
  have unorm: "norm u = 1" if u: "u \<in> B" for u
    using B u unfolding onormal_def by blast
  \<comment> \<open>the split of each column into its value at \<open>x\<close> plus the error\<close>
  have wsplit: "w u = sqrt (lam u) *\<^sub>R u + d u" for u
    unfolding d_def by simp
  have dform: "d u = skewv q (sqrt (lam u) *\<^sub>R u) *v (M *v (z - x))"
    if u: "u \<in> B" for u
  proof -
    have base: "skewv q (sqrt (lam u) *\<^sub>R u) *v q = sqrt (lam u) *\<^sub>R u"
    proof (cases "lam u = 0")
      case True
      then show ?thesis
        by (simp add: skewv_apply)
    next
      case False
      then have pos: "0 < lam u"
        using lam_nn[OF u] by (simp add: order_less_le)
      have orth: "(sqrt (lam u) *\<^sub>R u) \<bullet> q = 0"
        using lam_orth[OF u pos] by (simp add: inner_scaleR_left)
      show ?thesis by (rule skewv_apply_orth[OF q0 orth])
    qed
    have "w u = skewv q (sqrt (lam u) *\<^sub>R u) *v q
        + skewv q (sqrt (lam u) *\<^sub>R u) *v (M *v (z - x))"
      unfolding w_def grad_def by (rule algebra_simps)
    then show ?thesis unfolding d_def using base by simp
  qed
  have dbound: "norm (d u) \<le> e" if u: "u \<in> B" for u
  proof -
    have n1: "norm (sqrt (lam u) *\<^sub>R u) = sqrt (lam u)"
      using unorm[OF u] lam_nn[OF u] by simp
    have s1: "norm (d u)
        \<le> 2 * norm (sqrt (lam u) *\<^sub>R u) * norm (M *v (z - x)) / norm q"
      unfolding dform[OF u] by (rule skewv_norm_le[OF q0])
    have s2: "2 * norm (sqrt (lam u) *\<^sub>R u) * norm (M *v (z - x))
        \<le> 2 * sqrt L * (Cm * r)"
    proof (rule mult_mono)
      show "2 * norm (sqrt (lam u) *\<^sub>R u) \<le> 2 * sqrt L"
        using n1 sqlam_le[OF u] by simp
      have "norm (M *v (z - x)) \<le> Cm * norm (z - x)"
        unfolding Cm_def by (rule matvec_norm_le)
      also have "\<dots> = Cm * dist z x" by (simp add: dist_norm)
      also have "\<dots> \<le> Cm * r"
        using zr Cm0 by (intro mult_left_mono)
      finally show "norm (M *v (z - x)) \<le> Cm * r" .
      show "0 \<le> 2 * sqrt L" using sqL0 by simp
      show "0 \<le> norm (M *v (z - x))" by simp
    qed
    have s3: "2 * norm (sqrt (lam u) *\<^sub>R u) * norm (M *v (z - x)) / norm q
        \<le> 2 * sqrt L * (Cm * r) / norm q"
      by (rule divide_right_mono[OF s2]) simp
    have s4: "2 * sqrt L * (Cm * r) / norm q = e"
      unfolding e_def ec_def by (simp add: field_simps)
    show ?thesis using s1 s3 s4 by linarith
  qed
  \<comment> \<open>annihilation is exact at every \<open>z\<close>\<close>
  show "skewfield B lam q M x z *v (q + M *v (z - x)) = 0"
    unfolding sfw grad_def[symmetric]
  proof (rule outerp_sum_annihilate)
    fix u assume "u \<in> B"
    have "grad \<bullet> (skewv q (sqrt (lam u) *\<^sub>R u) *v grad) = 0"
      by (rule skewv_quadform)
    then show "w u \<bullet> grad = 0"
      unfolding w_def by (simp add: inner_commute)
  qed
  \<comment> \<open>the constraint set\<close>
  have psd: "psd (skewfield B lam q M x z)"
    unfolding sfw by (rule outerp_sum_psd)
  have ub: "eigen_ub (skewfield B lam q M x z) L"
    unfolding sfw
    by (rule perturbed_columns_eigen_ub[OF B sp wsplit lam_nn lam_ub
          m0 mL dbound e0 sm_ub[folded e_def]])
  have gram: "\<bar>w u \<bullet> w u' - (if u' = u then lam u else 0)\<bar>
      \<le> e * (2 * sqrt L + e)"
    if u: "u \<in> Bp" and u': "u' \<in> Bp" for u u'
  proof -
    have uB: "u \<in> B" and uB': "u' \<in> B" using u u' BpB by blast+
    have ip: "w u \<bullet> w u'
        = (sqrt (lam u) *\<^sub>R u) \<bullet> (sqrt (lam u') *\<^sub>R u')
          + ((sqrt (lam u) *\<^sub>R u) \<bullet> d u' + d u \<bullet> (sqrt (lam u') *\<^sub>R u')
             + d u \<bullet> d u')"
      by (subst wsplit, subst wsplit)
        (simp add: inner_add_left inner_add_right algebra_simps)
    have diag: "(sqrt (lam u) *\<^sub>R u) \<bullet> (sqrt (lam u') *\<^sub>R u')
        = (if u' = u then lam u else 0)"
    proof (cases "u' = u")
      case True
      then show ?thesis
        using lam_nn[OF uB] onormal_inner_self[OF B uB]
        by (simp add: inner_scaleR_left inner_scaleR_right
            abs_of_nonneg)
    next
      case False
      have "u \<bullet> u' = 0"
        using B uB uB' False unfolding onormal_def pairwise_def
          orthogonal_def by metis
      then show ?thesis using False
        by (simp add: inner_scaleR_left inner_scaleR_right)
    qed
    have b1: "\<bar>(sqrt (lam u) *\<^sub>R u) \<bullet> d u'\<bar> \<le> sqrt L * e"
    proof -
      have "\<bar>(sqrt (lam u) *\<^sub>R u) \<bullet> d u'\<bar>
          \<le> norm (sqrt (lam u) *\<^sub>R u) * norm (d u')"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> sqrt L * e"
      proof (intro mult_mono)
        show "norm (sqrt (lam u) *\<^sub>R u) \<le> sqrt L"
          using unorm[OF uB] lam_nn[OF uB] sqlam_le[OF uB] by simp
      qed (use dbound[OF uB'] e0 L0 in simp_all)
      finally show ?thesis .
    qed
    have b2: "\<bar>d u \<bullet> (sqrt (lam u') *\<^sub>R u')\<bar> \<le> e * sqrt L"
    proof -
      have "\<bar>d u \<bullet> (sqrt (lam u') *\<^sub>R u')\<bar>
          \<le> norm (d u) * norm (sqrt (lam u') *\<^sub>R u')"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> e * sqrt L"
      proof (intro mult_mono)
        show "norm (sqrt (lam u') *\<^sub>R u') \<le> sqrt L"
          using unorm[OF uB'] lam_nn[OF uB'] sqlam_le[OF uB'] by simp
      qed (use dbound[OF uB] e0 L0 in simp_all)
      finally show ?thesis .
    qed
    have b3: "\<bar>d u \<bullet> d u'\<bar> \<le> e * e"
    proof -
      have "\<bar>d u \<bullet> d u'\<bar> \<le> norm (d u) * norm (d u')"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> e * e"
        using dbound[OF uB] dbound[OF uB'] e0 by (intro mult_mono) simp_all
      finally show ?thesis .
    qed
    have "\<bar>w u \<bullet> w u' - (if u' = u then lam u else 0)\<bar>
        = \<bar>(sqrt (lam u) *\<^sub>R u) \<bullet> d u' + d u \<bullet> (sqrt (lam u') *\<^sub>R u')
            + d u \<bullet> d u'\<bar>"
      using ip diag by simp
    also have "\<dots> \<le> sqrt L * e + e * sqrt L + e * e"
      using b1 b2 b3 by linarith
    also have "\<dots> = e * (2 * sqrt L + e)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have lb: "eigen_lb (skewfield B lam q M x z) (CARD('n) - k)"
  proof -
    define E where "E = e * (2 * sqrt L + e)"
    have E0: "0 \<le> E" unfolding E_def using e0 sqL0
      by (intro mult_nonneg_nonneg) simp_all
    have npn: "real (card Bp) \<le> real CARD('n)"
    proof -
      have "card Bp \<le> card B" by (rule card_mono[OF finB BpB])
      then show ?thesis using onormal_span_card[OF B sp] by simp
    qed
    have sm': "real (card Bp) * E
        + 2 * (1 + m) / m * (real (card Bp) * E)\<^sup>2 \<le> m / 2"
    proof -
      have h1: "real (card Bp) * E \<le> real CARD('n) * E"
        using npn E0 by (intro mult_right_mono)
      have h2: "(real (card Bp) * E)\<^sup>2 \<le> (real CARD('n) * E)\<^sup>2"
        using h1 E0 by (intro power_mono mult_nonneg_nonneg) simp_all
      have h3: "2 * (1 + m) / m * (real (card Bp) * E)\<^sup>2
          \<le> 2 * (1 + m) / m * (real CARD('n) * E)\<^sup>2"
        using h2 m0 by (intro mult_left_mono) simp_all
      show ?thesis using h1 h3 sm_lb[folded e_def]
        unfolding E_def by linarith
    qed
    have "eigen_lb (\<Sum>u\<in>B. outerp (w u)) (card Bp)"
      by (rule perturbed_columns_eigen_lb[OF finB BpB lam_lb m0
            gram[folded E_def] E0 sm'])
    then show ?thesis unfolding sfw cardBp .
  qed
  have feas: "skewfield B lam q M x z \<in> feasible k L 0"
    unfolding feasible_def using psd ub lb by simp
  show "skewfield B lam q M x z \<in> sconstraint k L"
    using feasible_subset_sconstraint feas by blast
  \<comment> \<open>the trace margin\<close>
  have close: "\<bar>trace (M ** (\<Sum>u\<in>B. outerp (w u)))
      - (\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))\<bar>
      \<le> real CARD('n) * (Cm * (e * (2 * sqrt L + e)))"
  proof -
    have "\<bar>trace (M ** (\<Sum>u\<in>B. outerp (w u)))
        - (\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))\<bar>
        \<le> real (card B) * (Cm * (e * (2 * sqrt L + e)))"
      unfolding Cm_def
      by (rule perturbed_columns_trace_close[OF finB wsplit unorm
            lam_nn lam_leL dbound e0])
    also have "\<dots> \<le> real CARD('n) * (Cm * (e * (2 * sqrt L + e)))"
    proof (intro mult_right_mono)
      show "real (card B) \<le> real CARD('n)"
        using onormal_span_card[OF B sp] by simp
      show "0 \<le> Cm * (e * (2 * sqrt L + e))"
        using Cm0 e0 sqL0 by (intro mult_nonneg_nonneg add_nonneg_nonneg) simp_all
    qed
    finally show ?thesis .
  qed
  have blend_tr: "(\<Sum>u\<in>B. lam u * (u \<bullet> (M *v u)))
      = trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u))"
    by (rule traceM_sum_outer[symmetric])
  show "\<eta> / 2 \<le> 1 + trace (M ** skewfield B lam q M x z) / 2"
  proof -
    have "trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u))
        - real CARD('n) * (Cm * (e * (2 * sqrt L + e)))
        \<le> trace (M ** (\<Sum>u\<in>B. outerp (w u)))"
      using close blend_tr by linarith
    moreover have "real CARD('n) * (Cm * (e * (2 * sqrt L + e))) \<le> \<eta>"
      using sm_tr unfolding e_def .
    ultimately show ?thesis using tr unfolding sfw by linarith
  qed
qed

subsection \<open>The constant-volatility Gaussian member\<close>

text \<open>The Euler kernels freeze the covariance at the step's left endpoint,
  so the building block is Brownian motion pushed through a CONSTANT matrix
  \<open>S\<close>: the pair \<open>(S \<cdot> W\<^sub>t, t \<cdot> S S\<^sup>T)\<close>, started at \<open>0\<close>.  Class membership
  mirrors @{thm [source] bmpair_law_in_paper_pair_class}: the martingale
  clauses are BOUNDED-LINEAR images of the Brownian ones
  (@{thm [source] martingale_bounded_linear_image}), the covariation clause
  is deterministic, and an arbitrary start comes free from
  @{thm [source] paper_pair_class_pshift}.  The only hypothesis is
  \<open>S S\<^sup>T \<in> sconstraint k L\<close>.\<close>

definition sbmpair ::
  "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "sbmpair S T \<omega> = restrict
    (\<lambda>t. (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))) {0..T}"

lemma sbmpair_apply:
  "t \<in> {0..T} \<Longrightarrow> sbmpair S T \<omega> t
     = (S *v cbmX 0 t \<omega>, t *\<^sub>R (S ** transpose S))"
  by (simp add: sbmpair_def)

lemma matvec_blin: "bounded_linear ((*v) (S :: real^'n::finite^'m::finite))"
  using matrix_vector_mul_linear linear_conv_bounded_linear by blast

lemma matmul_sandwich_blin:
  fixes S :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>A :: real^'n^'n. S ** A ** transpose S)"
  unfolding linear_conv_bounded_linear[symmetric]
proof (intro linearI)
  fix A B :: "real^'n^'n"
  show "S ** (A + B) ** transpose S = S ** A ** transpose S
      + S ** B ** transpose S"
    by (simp add: matrix_matrix_mult_def vec_eq_iff vector_add_component
        sum.distrib algebra_simps)
next
  fix c :: real and A :: "real^'n^'n"
  show "S ** (c *\<^sub>R A) ** transpose S = c *\<^sub>R (S ** A ** transpose S)"
    by (simp add: matrix_matrix_mult_def vec_eq_iff vector_scaleR_component
        sum_distrib_left algebra_simps)
qed

lemma outerp_matvec_image:
  fixes S :: "real^'n::finite^'n" and w :: "real^'n"
  shows "outerp (S *v w) = S ** outerp w ** transpose S"
proof -
  have "outerp (S *v w) $ i $ j
      = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l)"
    for i j
  proof -
    have "outerp (S *v w) $ i $ j
        = (\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (\<Sum>l\<in>UNIV. S $ j $ l * w $ l)"
      by (simp add: outerp_def matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * w $ k)
        * (S $ j $ l * w $ l))"
      by (rule sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l))
        * S $ j $ l)"
    proof (rule sum.cong[OF refl])
      fix l :: 'n
      have "(\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (S $ j $ l * w $ l)
          = (\<Sum>k\<in>UNIV. S $ i $ k * w $ k * (S $ j $ l * w $ l))"
        by (rule sum_distrib_right)
      also have "\<dots> = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l) * S $ j $ l)"
        by (rule sum.cong[OF refl]) (simp only: mult_ac)
      also have "\<dots> = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l"
        by (rule sum_distrib_right[symmetric])
      finally show "(\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (S $ j $ l * w $ l)
          = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l" .
    qed
    finally show ?thesis .
  qed
  moreover have "(S ** outerp w ** transpose S) $ i $ j
      = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l)"
    for i j
    by (simp add: matrix_matrix_mult_def transpose_def outerp_def)
  ultimately show ?thesis by (simp add: vec_eq_iff)
qed

lemma matmul_scaleR_right:
  fixes A B :: "real^'n::finite^'n"
  shows "A ** (c *\<^sub>R B) = c *\<^sub>R (A ** B)"
  by (simp add: matrix_matrix_mult_def vec_eq_iff vector_scaleR_component
      sum_distrib_left algebra_simps)

lemma sandwich_mat1:
  fixes S :: "real^'n::finite^'n"
  shows "S ** (c *\<^sub>R mat 1) ** transpose S = c *\<^sub>R (S ** transpose S)"
  by (simp add: matmul_scaleR_right matrix_mul_rid scaleR_matrix_mult)

lemma continuous_on_sbmpair_path:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real" and S :: "real^'n^'n"
  shows "continuous_on {0..T}
      (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))"
proof (intro continuous_on_Pair)
  have c1: "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  show "continuous_on {0..T} (\<lambda>t. S *v cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_compose2[OF linear_continuous_on[OF matvec_blin]
          c1]) auto
  show "continuous_on {0..T} (\<lambda>t. t *\<^sub>R (S ** transpose S))"
    by (rule linear_continuous_on[OF bounded_linear_scaleR_left])
qed

lemma sbmpair_measurable:
  assumes T: "0 \<le> T"
  shows "(sbmpair S T :: ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      \<in> bm_paths \<rightarrow>\<^sub>M borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>,
                t *\<^sub>R (S ** transpose S))) {0..T})
      \<in> bm_paths \<rightarrow>\<^sub>M borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))"
  proof (rule pathify_measurable[OF T])
    fix t :: real assume "t \<in> {0..T}"
    have c: "(\<lambda>v :: real^'n. (S *v v, t *\<^sub>R (S ** transpose S)))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_on_Pair
          continuous_on_const
          continuous_on_compose2[OF linear_continuous_on[OF matvec_blin]
            continuous_on_id])
        auto
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_compose[OF measurable_cbmX c])
  next
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    show "continuous_on {0..T}
        (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S)))"
      by (rule continuous_on_sbmpair_path)
  qed
  moreover have "(sbmpair S T :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (S *v cbmX (0 :: real^'n) t \<omega>,
                t *\<^sub>R (S ** transpose S))) {0..T})"
    by (rule ext) (simp add: sbmpair_def)
  ultimately show ?thesis by simp
qed

lemma prob_space_sbmpair_law:
  assumes T: "0 \<le> T"
  shows "prob_space (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))"
  unfolding pair_law_of_def
  by (rule BMP.prob_space_distr[OF sbmpair_measurable[OF T]])

lemma sbmpair_law_start:
  assumes T: "0 \<le> T"
  shows "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have phim: "sbmpair S T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF T])
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
      \<in> sets ?B"
  proof -
    have "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(0, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have iff: "(AE \<omega> in pair_law_of T (sbmpair S T) ?M.
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0)
      = (AE \<omega> in ?M. fst (sbmpair S T \<omega> 0) = (0 :: real^'n)
          \<and> snd (sbmpair S T \<omega> 0) = 0)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
  have z: "(0::real) \<in> {0..T}" using T by simp
  have "AE \<omega> in ?M. cbmX (0 :: real^'n) 0 \<omega> = bmX 0 0 \<omega>"
    by (intro cbmX_ae_eq) simp
  moreover have "AE \<omega> in ?M. bmX (0 :: real^'n) 0 \<omega> = 0"
    by (rule bmX_start)
  ultimately have "AE \<omega> in ?M. fst (sbmpair S T \<omega> 0) = (0 :: real^'n)
      \<and> snd (sbmpair S T \<omega> 0) = 0"
    by eventually_elim (simp add: sbmpair_apply[OF z])
  then show ?thesis unfolding iff .
qed

lemma sbmpair_law_diffquot:
  assumes T: "0 \<le> T"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (sbmpair S T) ?M"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have phim: "sbmpair S T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF T])
  have spQ: "space ?Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_pair_law_of)
  have one: "AE \<omega> in ?Q.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    if pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" for p q :: real
  proof -
    have mm: "{\<omega> \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L}
        \<in> sets ?B"
      using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
      by (simp add: space_borel_of)
    have iff: "(AE \<omega> in ?Q.
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L)
        = (AE \<omega> in ?M. (1 / (q - p))
            *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
            \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in ?M. (1 / (q - p))
        *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
        \<in> sconstraint k L"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(1 / (q - p))
          *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
          = (1 / (q - p)) *\<^sub>R ((q - p) *\<^sub>R (S ** transpose S))"
        using pq by (simp add: sbmpair_apply scaleR_left_diff_distrib)
      also have "\<dots> = S ** transpose S"
        using pq(3) by simp
      finally show "(1 / (q - p))
          *\<^sub>R (snd (sbmpair S T \<omega> q) - snd (sbmpair S T \<omega> p))
          \<in> sconstraint k L"
        using SST by simp
    qed
    then show ?thesis unfolding iff .
  qed
  have rat: "AE \<omega> in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in ?Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in ?Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      proof (cases "0 \<le> p \<and> p < q \<and> q \<le> T")
        case True
        then have "p \<in> {0..T}" "q \<in> {0..T}" "p < q" by auto
        from one[OF this] show ?thesis by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  from rat AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q
        \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      and W: "\<omega> \<in> space ?Q" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spQ by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
        by (rule diffquot_all_of_rational
            [OF closed_sconstraint cont _ uv(1) uv(2) uv(3)]) (rule R)
    qed
  qed
qed

lemma sbmpair_adapted:
  fixes r u :: real
  assumes r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. sbmpair S T \<omega> r)
      \<in> borel_measurable
      (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^'n)) u)"
proof (cases "r \<in> {0..T}")
  case True
  let ?F = "natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (cbmX (0 :: real^'n))"
  interpret MC: martingale "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure" ?F 0
      "cbmX (0 :: real^'n)"
    by (rule martingale_cbmX)
  have cr: "cbmX (0 :: real^'n) r \<in> borel_measurable (?F r)"
    by (rule MC.adapted[OF r])
  have cu: "cbmX (0 :: real^'n) r \<in> borel_measurable (?F u)"
    using MC.borel_measurable_mono[OF r ru] cr by blast
  have c: "(\<lambda>v :: real^'n. (S *v v, r *\<^sub>R (S ** transpose S)))
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_on_Pair
        continuous_on_const
        continuous_on_compose2[OF linear_continuous_on[OF matvec_blin]
          continuous_on_id])
      auto
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        (S *v cbmX (0 :: real^'n) r \<omega>, r *\<^sub>R (S ** transpose S)))
      \<in> borel_measurable (?F u)"
    by (rule measurable_compose[OF cu c])
  then show ?thesis using True by (simp add: sbmpair_apply)
next
  case False
  then have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sbmpair S T \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: sbmpair_def)
  then show ?thesis by simp
qed

theorem sbmpair_law_X_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (sbmpair S T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?G u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev fstB])
  qed
  have mg: "martingale ?M ?F 0 (\<lambda>u \<omega>. fst (sbmpair S T \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_bounded_linear_image
        [OF matvec_blin martingale_stopped_const[OF T martingale_cbmX]]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. fst (sbmpair S T \<omega> (min u T)))
        = (\<lambda>\<omega>. S *v cbmX (0 :: real^'n) (min u T) \<omega>)"
      by (rule ext) (simp add: sbmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        sbmpair_measurable[OF T] sbmpair_adapted Zm mg])
qed

theorem sbmpair_law_comp_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (sbmpair S T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
      = (\<lambda>p. \<chi> i j. fst p $ i * fst p $ j - snd p $ i $ j)"
    by (rule ext) (simp add: outerp_def vec_eq_iff)
  have cB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
      \<in> borel_measurable borel"
    unfolding e
    by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
        continuous_intros)
  have Zm: "(\<lambda>\<omega> :: 'n pairpath.
        outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
      \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev cB])
  qed
  have mg: "martingale ?M ?F 0
      (\<lambda>u \<omega>. outerp (fst (sbmpair S T \<omega> (min u T)))
        - snd (sbmpair S T \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_bounded_linear_image
        [OF matmul_sandwich_blin
          martingale_stopped_const[OF T martingale_cbm_outerp]]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          outerp (fst (sbmpair S T \<omega> (min u T)))
            - snd (sbmpair S T \<omega> (min u T)))
        = (\<lambda>\<omega>. S ** (outerp (cbmX (0 :: real^'n) (min u T) \<omega>)
                - (min u T) *\<^sub>R mat 1) ** transpose S)"
    proof (rule ext)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "S ** (outerp (cbmX (0 :: real^'n) (min u T) \<omega>)
            - (min u T) *\<^sub>R mat 1) ** transpose S
          = S ** outerp (cbmX (0 :: real^'n) (min u T) \<omega>) ** transpose S
            - S ** ((min u T) *\<^sub>R mat 1) ** transpose S"
        by (simp add: matrix_matrix_mult_def vec_eq_iff
            vector_minus_component sum_subtractf algebra_simps)
      also have "\<dots> = outerp (S *v cbmX (0 :: real^'n) (min u T) \<omega>)
          - (min u T) *\<^sub>R (S ** transpose S)"
        by (simp add: outerp_matvec_image sandwich_mat1)
      finally show "outerp (fst (sbmpair S T \<omega> (min u T)))
            - snd (sbmpair S T \<omega> (min u T))
          = S ** (outerp (cbmX (0 :: real^'n) (min u T) \<omega>)
                - (min u T) *\<^sub>R mat 1) ** transpose S"
        by (simp add: sbmpair_apply[OF mI])
    qed
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        sbmpair_measurable[OF T] sbmpair_adapted Zm mg])
qed

theorem sbmpair_law_in_paper_pair_class:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<in> paper_pair_class k L T (0 :: real^'n)"
  unfolding paper_pair_class_def
proof (intro CollectI conjI)
  show "prob_space (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
    by (rule prob_space_sbmpair_law[OF T])
  show "sets (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    by simp
  show "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
    by (rule sbmpair_law_start[OF T])
  show "AE \<omega> in pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule sbmpair_law_diffquot[OF T SST])
  show "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)) :: real^'n)"
    by (rule sbmpair_law_X_martingale[OF T])
  show "martingale (pair_law_of T (sbmpair S T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (sbmpair S T) bm_paths) 0
        (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T)) :: real^'n) - snd (\<omega> (min t T)))"
    by (rule sbmpair_law_comp_martingale[OF T])
qed

corollary sbmpair_pshift_law_in_paper_pair_class:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "pshift_law T v (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
    \<in> paper_pair_class k L T (v :: real^'n)"
proof -
  have "pshift_law T v (pair_law_of T (sbmpair S T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
    \<in> paper_pair_class k L T (v + 0)"
    by (rule paper_pair_class_pshift[OF T
          sbmpair_law_in_paper_pair_class[OF T L SST]])
  then show ?thesis by simp
qed

subsection \<open>Writing the field as a square: columns into a matrix\<close>

text \<open>\<open>sbmpair\<close> wants a volatility matrix \<open>S\<close> with \<open>S S\<^sup>T\<close> equal to the
  field value; the field is a sum of column outer products, so \<open>S\<close> is the
  matrix whose columns are those columns, indexed through any enumeration
  of the eigenbasis.\<close>

lemma cols_mult_transpose:
  fixes w :: "'m::finite \<Rightarrow> real^'n::finite"
  shows "(\<chi> i j. w j $ i) ** transpose (\<chi> i j. w j $ i)
       = (\<Sum>j\<in>UNIV. outerp (w j))"
proof -
  have "((\<chi> i j. w j $ i) ** transpose (\<chi> i j. w j $ i)) $ i $ l
      = (\<Sum>j\<in>UNIV. w j $ i * w j $ l)" for i l
    by (simp add: matrix_matrix_mult_def transpose_def)
  moreover have "(\<Sum>j\<in>UNIV. outerp (w j)) $ i $ l
      = (\<Sum>j\<in>UNIV. w j $ i * w j $ l)" for i l
    by (induction "UNIV :: 'm set" rule: infinite_finite_induct)
      (simp_all add: outerp_def vector_add_component)
  ultimately show ?thesis by (simp add: vec_eq_iff)
qed

lemma skewfield_decomp:
  fixes B :: "(real^'n::finite) set" and f :: "'n \<Rightarrow> real^'n"
  assumes bij: "bij_betw f (UNIV :: 'n set) B"
  shows "(\<chi> i j. (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
          *v (q + M *v (z - x))) $ i)
       ** transpose (\<chi> i j. (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
          *v (q + M *v (z - x))) $ i)
       = skewfield B lam q M x z"
proof -
  have "(\<chi> i j. (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
          *v (q + M *v (z - x))) $ i)
       ** transpose (\<chi> i j. (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
          *v (q + M *v (z - x))) $ i)
       = (\<Sum>j\<in>UNIV. outerp (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
          *v (q + M *v (z - x))))"
    by (rule cols_mult_transpose)
  also have "\<dots> = (\<Sum>u\<in>B. outerp (skewv q (sqrt (lam u) *\<^sub>R u)
      *v (q + M *v (z - x))))"
    by (rule sum.reindex_bij_betw[OF bij])
  finally show ?thesis unfolding skewfield_def .
qed

lemma exists_enum_of_card:
  fixes B :: "(real^'n::finite) set"
  assumes finB: "finite B" and cardB: "card B = CARD('n)"
  obtains f :: "'n \<Rightarrow> real^'n" where "bij_betw f (UNIV :: 'n set) B"
proof -
  have "\<exists>f. bij_betw f (UNIV :: 'n set) B"
    by (rule finite_same_card_bij) (use finB cardB in simp_all)
  then show ?thesis using that by blast
qed

subsection \<open>Continuity of the Gaussian member in its volatility\<close>

text \<open>The Euler kernel varies only through the frozen matrix, so its
  measurability reduces to CONTINUITY of \<open>S \<mapsto> law (sbmpair S T)\<close> in the
  weak topology: pathwise \<open>S \<mapsto> sbmpair S T \<omega>\<close> is continuous into the path
  metric (the Brownian path is bounded on \<open>[0,T]\<close>), and dominated
  convergence does the rest --- no tightness, no uniform estimates.\<close>

lemma matrix_norm_le_sum_abs:
  fixes A :: "real^'n::finite^'m::finite"
  shows "norm A \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)"
proof -
  have row: "norm (A $ i) \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)" for i
  proof -
    have "(norm (A $ i))\<^sup>2 = (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>\<^sup>2)"
      by (simp add: power2_norm_eq_inner inner_vec_def power2_eq_square[of "A $ _ $ _"])
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2"
      by (rule sum_sq_le_sq_sum) simp
    finally have h: "(norm (A $ i))\<^sup>2 \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)\<^sup>2" .
    show ?thesis
      using h by (simp add: power2_le_iff_abs_le abs_of_nonneg sum_nonneg)
  qed
  have "(norm A)\<^sup>2 = (\<Sum>i\<in>UNIV. (norm (A $ i))\<^sup>2)"
    by (simp add: power2_norm_eq_inner inner_vec_def)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. norm (A $ i))\<^sup>2"
    by (rule sum_sq_le_sq_sum) simp
  finally have h: "(norm A)\<^sup>2 \<le> (\<Sum>i\<in>UNIV. norm (A $ i))\<^sup>2" .
  have "norm A \<le> (\<Sum>i\<in>UNIV. norm (A $ i))"
    using h by (simp add: power2_le_iff_abs_le abs_of_nonneg sum_nonneg)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)"
    by (rule sum_mono) (rule row)
  finally show ?thesis .
qed

lemma dist_pair_le:
  fixes a c :: "'a::metric_space" and b d :: "'b::metric_space"
  shows "dist (a, b) (c, d) \<le> dist a c + dist b d"
proof -
  have "(dist a c + dist b d)\<^sup>2
      = (dist a c)\<^sup>2 + 2 * dist a c * dist b d + (dist b d)\<^sup>2"
    by (simp add: power2_sum)
  moreover have "0 \<le> 2 * dist a c * dist b d"
    by (intro mult_nonneg_nonneg) simp_all
  ultimately have "(dist a c)\<^sup>2 + (dist b d)\<^sup>2 \<le> (dist a c + dist b d)\<^sup>2"
    by linarith
  then have "sqrt ((dist a c)\<^sup>2 + (dist b d)\<^sup>2) \<le> dist a c + dist b d"
    by (metis real_le_lsqrt real_sqrt_le_iff zero_le_dist add_nonneg_nonneg)
  then show ?thesis by (simp add: dist_prod_def)
qed

lemma sbmpair_in_mspace:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real" and S :: "real^'n^'n"
  shows "sbmpair S T \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  unfolding sbmpair_def
  by (rule mspace_path_metricI[OF continuous_on_sbmpair_path])

lemma sbmpair_pathwise_tendsto:
  fixes Sm :: "nat \<Rightarrow> real^'n::finite^'n" and S :: "real^'n^'n"
    and \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
  assumes T: "0 \<le> T" and Sc: "Sm \<longlonglongrightarrow> S"
  shows "limitin (mtopology_of (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) sequentially"
proof -
  let ?PM = "path_metric T :: ('n pairpath) metric"
  interpret PM: Metric_space "mspace ?PM" "mdist ?PM"
    by (rule Metric_space_mspace_mdist)
  have msp: "sbmpair S' T \<omega> \<in> mspace ?PM" for S' :: "real^'n^'n"
    by (rule sbmpair_in_mspace)
  have cW: "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  have "bounded ((\<lambda>t. cbmX (0 :: real^'n) t \<omega>) ` {0..T})"
    by (intro compact_imp_bounded compact_continuous_image cW) simp
  then obtain BW where BW: "\<And>t. t \<in> {0..T}
      \<Longrightarrow> norm (cbmX (0 :: real^'n) t \<omega>) \<le> BW"
    unfolding bounded_iff by blast
  have BW0: "0 \<le> BW"
  proof -
    have z: "(0::real) \<in> {0..T}" using T by simp
    show ?thesis
      using BW[OF z] norm_ge_zero[of "cbmX (0 :: real^'n) 0 \<omega>"] by linarith
  qed
  define cs where "cs = (\<lambda>m. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>(Sm m - S) $ i $ j\<bar>)"
  define ds where "ds = (\<lambda>m. norm (Sm m ** transpose (Sm m)
      - S ** transpose S))"
  define D where "D = (\<lambda>m. cs m * BW + T * ds m)"
  have cs_nn: "0 \<le> cs m" for m
    unfolding cs_def by (intro sum_nonneg) simp_all
  have ds_nn: "0 \<le> ds m" for m unfolding ds_def by simp
  have cs0: "cs \<longlonglongrightarrow> 0"
  proof -
    have ent: "(\<lambda>m. \<bar>(Sm m - S) $ i $ j\<bar>) \<longlonglongrightarrow> 0" for i j
    proof -
      have "(\<lambda>m. Sm m - S) \<longlonglongrightarrow> S - S"
        by (intro tendsto_diff Sc tendsto_const)
      then have "(\<lambda>m. (Sm m - S) $ i $ j) \<longlonglongrightarrow> (S - S) $ i $ j"
        by (intro tendsto_vec_nth)
      then have "(\<lambda>m. (Sm m - S) $ i $ j) \<longlonglongrightarrow> 0" by simp
      then show ?thesis using tendsto_rabs_zero by blast
    qed
    have "(\<lambda>m. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>(Sm m - S) $ i $ j\<bar>)
        \<longlonglongrightarrow> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). (0::real))"
      by (intro tendsto_sum ent)
    then show ?thesis unfolding cs_def by simp
  qed
  have ds0: "ds \<longlonglongrightarrow> 0"
  proof -
    have h: "(\<lambda>m. Sm m ** transpose (Sm m)) \<longlonglongrightarrow> S ** transpose S"
    proof (intro vec_tendstoI)
      fix i j
      have e: "\<And>A :: real^'n^'n. (A ** transpose A) $ i $ j
          = (\<Sum>l\<in>UNIV. A $ i $ l * A $ j $ l)"
        by (simp add: matrix_matrix_mult_def transpose_def)
      have "(\<lambda>m. \<Sum>l\<in>UNIV. Sm m $ i $ l * Sm m $ j $ l)
          \<longlonglongrightarrow> (\<Sum>l\<in>UNIV. S $ i $ l * S $ j $ l)"
        by (intro tendsto_sum tendsto_mult tendsto_vec_nth Sc)
      then show "(\<lambda>m. (Sm m ** transpose (Sm m)) $ i $ j)
          \<longlonglongrightarrow> (S ** transpose S) $ i $ j"
        unfolding e .
    qed
    have "(\<lambda>m. Sm m ** transpose (Sm m) - S ** transpose S)
        \<longlonglongrightarrow> S ** transpose S - S ** transpose S"
      by (intro tendsto_diff h tendsto_const)
    then have "(\<lambda>m. Sm m ** transpose (Sm m) - S ** transpose S)
        \<longlonglongrightarrow> 0" by simp
    then show ?thesis unfolding ds_def
      using tendsto_norm_zero by blast
  qed
  have D0: "D \<longlonglongrightarrow> 0"
  proof -
    have "D \<longlonglongrightarrow> 0 * BW + T * 0"
      unfolding D_def by (intro tendsto_add tendsto_mult tendsto_const cs0 ds0)
    then show ?thesis by simp
  qed
  have mbound: "mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) \<le> D m" for m
  proof (rule path_mdist_le_iff_all[OF T msp msp, THEN iffD2], rule ballI)
    fix t assume t: "t \<in> {0..T}"
    have fst_b: "dist (Sm m *v cbmX (0 :: real^'n) t \<omega>)
        (S *v cbmX (0 :: real^'n) t \<omega>) \<le> cs m * BW"
    proof -
      have "dist (Sm m *v cbmX (0 :: real^'n) t \<omega>)
          (S *v cbmX (0 :: real^'n) t \<omega>)
          = norm ((Sm m - S) *v cbmX (0 :: real^'n) t \<omega>)"
        by (simp add: dist_norm matrix_vector_mult_diff_rdistrib)
      also have "\<dots> \<le> cs m * norm (cbmX (0 :: real^'n) t \<omega>)"
        unfolding cs_def by (rule matvec_norm_le)
      also have "\<dots> \<le> cs m * BW"
        using BW[OF t] cs_nn by (intro mult_left_mono)
      finally show ?thesis .
    qed
    have snd_b: "dist (t *\<^sub>R (Sm m ** transpose (Sm m)))
        (t *\<^sub>R (S ** transpose S)) \<le> T * ds m"
    proof -
      have "dist (t *\<^sub>R (Sm m ** transpose (Sm m)))
          (t *\<^sub>R (S ** transpose S))
          = \<bar>t\<bar> * ds m"
        unfolding ds_def
        by (simp add: dist_norm scaleR_diff_right[symmetric])
      also have "\<dots> \<le> T * ds m"
        using t ds_nn by (intro mult_right_mono) auto
      finally show ?thesis .
    qed
    have "dist (sbmpair (Sm m) T \<omega> t) (sbmpair S T \<omega> t)
        = dist (Sm m *v cbmX (0 :: real^'n) t \<omega>,
            t *\<^sub>R (Sm m ** transpose (Sm m)))
          (S *v cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (S ** transpose S))"
      by (simp add: sbmpair_apply[OF t])
    also have "\<dots> \<le> dist (Sm m *v cbmX (0 :: real^'n) t \<omega>)
          (S *v cbmX (0 :: real^'n) t \<omega>)
        + dist (t *\<^sub>R (Sm m ** transpose (Sm m)))
            (t *\<^sub>R (S ** transpose S))"
      by (rule dist_pair_le)
    also have "\<dots> \<le> cs m * BW + T * ds m"
      using fst_b snd_b by linarith
    finally show "dist (sbmpair (Sm m) T \<omega> t) (sbmpair S T \<omega> t) \<le> D m"
      unfolding D_def .
  qed
  show ?thesis
    unfolding mtopology_of_def
  proof (rule PM.limitin_metric[THEN iffD2], intro conjI allI impI)
    show "sbmpair S T \<omega> \<in> mspace ?PM" by (rule msp)
    fix \<epsilon> :: real assume e: "0 < \<epsilon>"
    from LIMSEQ_D[OF D0 e] obtain M0
      where M0': "\<And>m. M0 \<le> m \<Longrightarrow> norm (D m - 0) < \<epsilon>" by blast
    have M0: "\<And>m. M0 \<le> m \<Longrightarrow> norm (D m) < \<epsilon>" using M0' by simp
    show "\<forall>\<^sub>F m in sequentially. sbmpair (Sm m) T \<omega> \<in> mspace ?PM
        \<and> mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) < \<epsilon>"
    proof (intro eventually_sequentiallyI[of M0] conjI)
      fix m assume m: "M0 \<le> m"
      show "sbmpair (Sm m) T \<omega> \<in> mspace ?PM" by (rule msp)
      have "mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) \<le> D m"
        by (rule mbound)
      also have "\<dots> \<le> norm (D m)" by simp
      also have "\<dots> < \<epsilon>" by (rule M0[OF m])
      finally show "mdist ?PM (sbmpair (Sm m) T \<omega>) (sbmpair S T \<omega>) < \<epsilon>" .
    qed
  qed
qed

theorem sbm_law_weak_conv:
  fixes Sm :: "nat \<Rightarrow> real^'n::finite^'n" and S :: "real^'n^'n"
  assumes T: "0 \<le> T" and Sc: "Sm \<longlonglongrightarrow> S"
  shows "weak_conv_on
      (\<lambda>m. pair_law_of T (sbmpair (Sm m) T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (pair_law_of T (sbmpair S T) bm_paths)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?S = "mspace (path_metric T :: ('n pairpath) metric)"
  let ?law = "\<lambda>S'. pair_law_of T (sbmpair S' T) ?M"
  have fmS: "finite_measure (?law S')" for S' :: "real^'n^'n"
    using prob_space_sbmpair_law[OF T, where S = S']
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have MWfin: "mweak_conv_fin ?S
      (mdist (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. ?law (Sm m)) (?law S) sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using fmS by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin ?S
      "mdist (path_metric T :: ('n pairpath) metric)"
      "\<lambda>m. ?law (Sm m)" "?law S" sequentially
    by (rule MWfin)
  show ?thesis
    unfolding mtopology_of_def
  proof (rule MW.mweak_conv_eq1[THEN iffD2], intro allI impI)
    fix f :: "'n pairpath \<Rightarrow> real"
    assume uc: "uniformly_continuous_map MW.Self euclidean_metric f"
    assume bnd: "\<exists>B. \<forall>x \<in> ?S. \<bar>f x\<bar> \<le> B"
    from bnd obtain B where B: "\<And>x. x \<in> ?S \<Longrightarrow> \<bar>f x\<bar> \<le> B" by blast
    have cf: "continuous_map ?X euclideanreal f"
      using uniformly_continuous_imp_continuous_map[OF uc]
      by (simp add: mtopology_of_def)
    have fm: "f \<in> borel_measurable ?B"
      using continuous_map_measurable[OF cf] by (simp add: borel_of_euclidean)
    have distr_int: "(\<integral>\<omega>. f \<omega> \<partial>(?law S')) = (\<integral>\<omega>. f (sbmpair S' T \<omega>) \<partial>?M)"
      for S' :: "real^'n^'n"
      unfolding pair_law_of_def
      by (rule integral_distr[OF sbmpair_measurable[OF T] fm])
    have ptw: "(\<lambda>m. f (sbmpair (Sm m) T \<omega>)) \<longlonglongrightarrow> f (sbmpair S T \<omega>)"
      for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    proof -
      have "limitin euclideanreal
          (f \<circ> (\<lambda>m. sbmpair (Sm m) T \<omega>))
          (f (sbmpair S T \<omega>)) sequentially"
        by (rule continuous_map_limit[OF cf
              sbmpair_pathwise_tendsto[OF T Sc]])
      then show ?thesis by (simp add: o_def)
    qed
    have meas: "(\<lambda>\<omega>. f (sbmpair S' T \<omega>)) \<in> borel_measurable ?M"
      for S' :: "real^'n^'n"
      by (rule measurable_compose[OF sbmpair_measurable[OF T] fm])
    have bd: "AE \<omega> in ?M. norm (f (sbmpair S' T \<omega>)) \<le> \<bar>B\<bar>"
      for S' :: "real^'n^'n"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "\<bar>f (sbmpair S' T \<omega>)\<bar> \<le> B"
        by (rule B[OF sbmpair_in_mspace])
      then show "norm (f (sbmpair S' T \<omega>)) \<le> \<bar>B\<bar>" by simp
    qed
    interpret BMPP: prob_space ?M by (rule prob_space_bm_paths)
    have ibd: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<bar>B\<bar>)"
      by simp
    have "(\<lambda>m. \<integral>\<omega>. f (sbmpair (Sm m) T \<omega>) \<partial>?M)
        \<longlonglongrightarrow> (\<integral>\<omega>. f (sbmpair S T \<omega>) \<partial>?M)"
      by (rule integral_dominated_convergence[OF meas meas ibd _ bd])
        (simp add: ptw)
    then show "(\<lambda>m. \<integral>\<omega>. f \<omega> \<partial>(?law (Sm m)))
        \<longlonglongrightarrow> (\<integral>\<omega>. f \<omega> \<partial>(?law S))"
      unfolding distr_int .
  qed
qed

subsection \<open>The Euler kernel: measurability package\<close>

text \<open>A continuous matrix field with admissible squares induces, through
  the Gaussian member, a kernel with exactly the three measurability
  properties @{thm [source] paper_pair_class_kglue_law'} consumes.
  Sequential continuity in the LP metric comes from
  @{thm [source] sbm_law_weak_conv}; it upgrades to topological continuity
  by the closed-preimage criterion (both sides are metric), and the
  prob-algebra form follows by the same bridge as
  @{thm [source] paper_v_measurable_selector_kernel'}.\<close>

theorem sbm_kernel_package:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and T' :: real
  assumes T: "0 < T'" and L: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T')
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<in> borel \<rightarrow>\<^sub>M prob_algebra (borel_of
        (mtopology_of (path_metric T' :: ('n pairpath) metric)))"
    and "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T')
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (paper_pair_class k L T' (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric T' :: ('n pairpath) metric))
          (mdist (path_metric T' :: ('n pairpath) metric))))"
    and "\<And>z. pair_law_of T' (sbmpair (SF z) T')
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<in> paper_pair_class k L T' (0 :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?X = "mtopology_of (path_metric T' :: ('n pairpath) metric)"
  let ?B = "borel_of (mtopology_of (path_metric T' :: ('n pairpath) metric))"
  let ?W = "weak_conv_topology
      (mtopology_of (path_metric T' :: ('n pairpath) metric))"
  let ?C = "paper_pair_class k L T' (0::real^'n)"
  let ?dd = "Levy_Prokhorov.LPm
      (mspace (path_metric T' :: ('n pairpath) metric))
      (mdist (path_metric T' :: ('n pairpath) metric))"
  let ?P = "{N :: ('n pairpath) measure. prob_space N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric T' :: ('n pairpath) metric)))}"
  define KK where "KK = (\<lambda>z. pair_law_of T' (sbmpair (SF z) T') ?M)"
  have T0': "0 \<le> T'" using T by simp
  have L0: "0 \<le> L" using L by simp
  interpret MC: Metric_space ?C ?dd
    by (rule paper_pair_class_compact_metric_space(1)[OF T L0])
  have Ctop: "MC.mtopology = subtopology ?W ?C"
    by (rule paper_pair_class_compact_metric_space(2)[OF T L0])
  show KC: "\<And>z. pair_law_of T' (sbmpair (SF z) T') ?M
      \<in> paper_pair_class k L T' (0 :: real^'n)"
    by (rule sbmpair_law_in_paper_pair_class[OF T0' L SFs])
  have KCk: "KK z \<in> ?C" for z unfolding KK_def by (rule KC)
  have seq: "limitin MC.mtopology (\<lambda>m. KK (zm m)) (KK z) sequentially"
    if zc: "zm \<longlonglongrightarrow> z" for zm and z :: "real^'n"
  proof -
    have SFzc: "(\<lambda>m. SF (zm m)) \<longlonglongrightarrow> SF z"
    proof (rule isCont_tendsto_compose[OF _ zc])
      show "isCont SF z"
        using SFc continuous_on_eq_continuous_at[of UNIV SF] by simp
    qed
    have wc: "limitin ?W (\<lambda>m. KK (zm m)) (KK z) sequentially"
      unfolding KK_def by (rule sbm_law_weak_conv[OF T0' SFzc])
    show ?thesis
      unfolding Ctop limitin_subtopology
      by (intro conjI wc KCk always_eventually allI)
  qed
  have cont: "continuous_map (euclidean :: (real^'n) topology)
      MC.mtopology KK"
    unfolding continuous_map_closedin
  proof (intro conjI allI impI)
    show "KK \<in> topspace (euclidean :: (real^'n) topology)
        \<rightarrow> topspace MC.mtopology"
      using KCk by auto
    fix C' assume cl: "closedin MC.mtopology C'"
    have "closed {z. KK z \<in> C'}"
    proof (rule closed_sequential_limits[THEN iffD2], intro allI impI)
      fix zm and z :: "real^'n"
      assume h: "(\<forall>m. zm m \<in> {z. KK z \<in> C'}) \<and> zm \<longlonglongrightarrow> z"
      have lim: "limitin MC.mtopology (\<lambda>m. KK (zm m)) (KK z) sequentially"
        using h by (intro seq) blast
      have ev: "eventually (\<lambda>m. KK (zm m) \<in> C') sequentially"
        using h by (intro always_eventually) blast
      have "KK z \<in> C'"
        by (rule limitin_closedin[OF lim cl ev]) simp
      then show "z \<in> {z. KK z \<in> C'}" by blast
    qed
    then show "closedin (euclidean :: (real^'n) topology)
        {x \<in> topspace euclidean. KK x \<in> C'}"
      unfolding closed_closedin[symmetric] by simp
  qed
  show "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T') ?M)
      \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology ?C ?dd)"
    using continuous_map_measurable[OF cont]
    by (simp add: borel_of_euclidean KK_def)
  have contW: "continuous_map (euclidean :: (real^'n) topology) ?W KK"
    using cont unfolding Ctop continuous_map_in_subtopology by blast
  have SmB: "KK \<in> borel \<rightarrow>\<^sub>M borel_of ?W"
    using continuous_map_measurable[OF contW]
    by (simp add: borel_of_euclidean)
  have SP: "KK z \<in> ?P" for z
    using paper_pair_class_prob[OF KCk] paper_pair_class_sets[OF KCk]
    by simp
  have polish: "Polish_space
      (mtopology_of (path_metric T' :: ('n pairpath) metric))"
    by (rule Polish_space_path_metric)
  have setsPA: "sets (borel_of (subtopology ?W ?P)) = sets (prob_algebra ?B)"
    by (rule weak_conv_topology_eq_prob_algebra[OF polish])
  have r1: "KK \<in> borel \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?P"
    by (rule measurable_restrict_space2[OF _ SmB]) (use SP in auto)
  have r2: "KK \<in> borel \<rightarrow>\<^sub>M borel_of (subtopology ?W ?P)"
    using r1 by (simp add: borel_of_subtopology)
  show "(\<lambda>z. pair_law_of T' (sbmpair (SF z) T') ?M)
      \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
    using r2 measurable_cong_sets[OF refl setsPA] unfolding KK_def by blast
qed

subsection \<open>The Euler process\<close>

text \<open>Freeze the field at the left endpoint of each step and glue with
  @{thm [source] paper_pair_class_kglue_law'}: stage \<open>j\<close> is a member on
  the horizon \<open>(j+1)h\<close>, and membership is plain induction --- the
  continuation kernel is centred (\<open>pglue\<close> recenters), so it is exactly
  @{thm [source] sbm_kernel_package} composed with the endpoint map.\<close>

fun eulerp ::
  "(real^'n::finite \<Rightarrow> real^'n^'n) \<Rightarrow> real^'n \<Rightarrow> real \<Rightarrow> nat
     \<Rightarrow> ('n pairpath) measure"
  where
    "eulerp SF x h 0 = pshift_law h x
        (pair_law_of h (sbmpair (SF x) h) bm_paths)"
  | "eulerp SF x h (Suc j) = kglue_law' (real (Suc j) * h)
        (real (Suc (Suc j)) * h)
        (\<lambda>\<omega>. pair_law_of h (sbmpair (SF (fst (\<omega> (real (Suc j) * h)))) h)
             bm_paths)
        (eulerp SF x h j)"

theorem eulerp_in_class:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and x :: "real^'n"
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "eulerp SF x h j \<in> paper_pair_class k L (real (Suc j) * h) x"
proof (induction j)
  case 0
  have "pshift_law h x (pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<in> paper_pair_class k L h x"
    by (rule sbmpair_pshift_law_in_paper_pair_class)
      (use h0 L1 SFs in simp_all)
  then show ?case by simp
next
  case (Suc j)
  define r where "r = real (Suc j) * h"
  define T' where "T' = real (Suc (Suc j)) * h"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: field_simps)
  have r0: "0 \<le> r" unfolding r_def using h0 by simp
  have rT: "r < T'" unfolding r_def T'_def using h0 by simp
  have T0: "0 < T'" unfolding T'_def using h0 by simp
  have Q: "eulerp SF x h j \<in> paper_pair_class k L r x"
    using Suc unfolding r_def .
  have setsQ: "sets (eulerp SF x h j) = sets (borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have hpos: "0 < (h :: real)" by (rule h0)
  note pack = sbm_kernel_package[OF hpos L1 SFc SFs]
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r))
      \<in> borel_measurable (eulerp SF x h j)"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have eF: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r))
      \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M borel"
  proof (rule measurable_compose[OF _ mfst])
    show "(\<lambda>\<omega> :: 'n pairpath. \<omega> r)
        \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use r0 in auto)
  qed
  have Kp: "(\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
      \<in> eulerp SF x h j \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T' - r) :: ('n pairpath) metric)))"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Kb: "(\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
      \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r
      \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
          (paper_pair_class k L (T' - r) (0::real^'n))
          (Levy_Prokhorov.LPm
            (mspace (path_metric (T' - r) :: ('n pairpath) metric))
            (mdist (path_metric (T' - r) :: ('n pairpath) metric))))"
    unfolding hT by (rule measurable_compose[OF eF pack(2)])
  have Kc: "pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths
      \<in> paper_pair_class k L (T' - r) 0" for \<omega> :: "'n pairpath"
    unfolding hT by (rule pack(3))
  have "kglue_law' r T'
      (\<lambda>\<omega>. pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
      (eulerp SF x h j) \<in> paper_pair_class k L T' x"
  proof (rule paper_pair_class_kglue_law')
    show "0 \<le> r" by (rule r0)
    show "r < T'" by (rule rT)
    show "1 \<le> L" by (rule L1)
    show "0 < T'" by (rule T0)
    show "eulerp SF x h j \<in> paper_pair_class k L r x" by (rule Q)
    show "(\<lambda>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
        \<in> eulerp SF x h j \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
          (path_metric (T' - r) :: ('n pairpath) metric)))"
      by (rule Kp)
    show "(\<lambda>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths)
        \<in> natural_filtration (eulerp SF x h j) 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
            (paper_pair_class k L (T' - r) (0::real^'n))
            (Levy_Prokhorov.LPm
              (mspace (path_metric (T' - r) :: ('n pairpath) metric))
              (mdist (path_metric (T' - r) :: ('n pairpath) metric))))"
      by (rule Kb)
    show "\<And>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths
        \<in> paper_pair_class k L (T' - r) 0"
      by (rule Kc)
  qed
  then show ?case unfolding r_def T'_def by simp
qed

subsection \<open>Step moments of the Gaussian member\<close>

text \<open>The Euler analysis needs exactly two facts per step: the compensated
  quadratic increment has MEAN ZERO (an instance of
  @{thm [source] paper_pair_class_quadform_mean}, since the member's second
  component is deterministic), and its VARIANCE is \<open>O(h\<^sup>2)\<close>.  The variance
  needs no Wick calculus and no coordinate independence: the pointwise
  AM--GM bound \<open>a\<^sup>2b\<^sup>2 \<le> (a\<^sup>4 + b\<^sup>4)/2\<close> reduces everything to the fourth
  marginal moment \<open>3h\<^sup>2\<close> of one Brownian coordinate.\<close>

lemma trace_mult_blin:
  fixes M :: "real^'n::finite^'n"
  shows "bounded_linear (\<lambda>A :: real^'n^'n. trace (M ** A))"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI)
    (simp_all add: trace_mult_add matmul_scaleR_right trace_scaleR)

lemma sconstraint_diag_le:
  fixes a :: "real^'n::finite^'n"
  assumes a: "a \<in> sconstraint k L"
  shows "a $ i $ i \<le> L"
proof -
  have ub: "eigen_ub a L"
    using a unfolding sconstraint_def by blast
  have gen: "\<And>u :: real^'n. u \<bullet> (a *v u) \<le> L * (u \<bullet> u)"
    using ub unfolding eigen_ub_def by blast
  have inst: "axis i 1 \<bullet> (a *v axis i 1)
      \<le> L * ((axis i 1 :: real^'n) \<bullet> axis i 1)"
    using gen by blast
  have e1: "axis i 1 \<bullet> (a *v axis i 1) = a $ i $ i"
    using axis1_inner[of i "a *v axis i 1"] matvec_axis1[of a i i] by simp
  have e2: "(axis i 1 :: real^'n) \<bullet> axis i 1 = 1"
    by (rule axis1_self)
  show ?thesis using inst unfolding e1 e2 by simp
qed

lemma sbm_entry_bound:
  fixes S :: "real^'n::finite^'n"
  assumes SST: "S ** transpose S \<in> sconstraint k L"
  shows "\<bar>S $ i $ j\<bar> \<le> sqrt L"
proof -
  have diag: "(S ** transpose S) $ i $ i = (\<Sum>l\<in>UNIV. (S $ i $ l)\<^sup>2)"
    by (simp add: matrix_matrix_mult_def transpose_def power2_eq_square)
  have "(S $ i $ j)\<^sup>2 \<le> (\<Sum>l\<in>UNIV. (S $ i $ l)\<^sup>2)"
    by (rule member_le_sum) simp_all
  also have "\<dots> \<le> L"
    using sconstraint_diag_le[OF SST, of i] diag by simp
  finally have "(S $ i $ j)\<^sup>2 \<le> L" .
  then have "sqrt ((S $ i $ j)\<^sup>2) \<le> sqrt L"
    by (rule real_sqrt_le_mono)
  then show ?thesis by simp
qed

lemma bm_coordinate_pow4:
  assumes h0: "0 < h"
  shows bm_coordinate_pow4_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h) ^ 4)"
    and bm_coordinate_pow4_integral:
    "(\<integral>\<omega>. (\<omega> i h) ^ 4 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = 3 * h\<^sup>2"
proof -
  have h0': "(0::real) \<le> h" using h0 by simp
  have m: "(\<lambda>\<omega>. \<omega> i h) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using h0' by (intro measurable_bm_coordinate) simp
  have p4: "(\<lambda>y :: real. y ^ 4) \<in> borel_measurable borel"
    by measurable
  have hb: "has_bochner_integral (gauss_measure h) (\<lambda>x. x ^ (2 * 2))
      (fact (2 * 2) / (2 ^ 2 * fact 2) * h ^ 2)"
    by (rule gauss_measure_moment_even[OF h0])
  have c3: "(fact (2 * 2) / (2 ^ 2 * fact 2) :: real) = 3"
    by (simp add: fact_numeral)
  have hb4: "has_bochner_integral (gauss_measure h) (\<lambda>x. x ^ 4) (3 * h\<^sup>2)"
    using hb by (simp add: c3 fact_numeral)
  have ig: "integrable (gauss_measure h) (\<lambda>x. x ^ 4)"
    and vg: "(\<integral>x. x ^ 4 \<partial>gauss_measure h) = 3 * h\<^sup>2"
    using hb4 by (auto intro: integrable.intros
        simp: has_bochner_integral_integral_eq)
  have d: "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i h) = gauss_measure h"
    by (rule bm_coordinate_distr[OF h0'])
  have "integrable (distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i h)) (\<lambda>y. y ^ 4)"
    unfolding d by (rule ig)
  then show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h) ^ 4)"
    by (subst (asm) integrable_distr_eq[OF m p4])
  have "(\<integral>\<omega>. (\<omega> i h) ^ 4 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>y. y ^ 4 \<partial>(distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
          borel (\<lambda>\<omega>. \<omega> i h)))"
    by (rule integral_distr[OF m p4, symmetric])
  also have "\<dots> = 3 * h\<^sup>2" unfolding d by (rule vg)
  finally show "(\<integral>\<omega>. (\<omega> i h) ^ 4
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 3 * h\<^sup>2" .
qed

lemma bm_R2_moment:
  assumes h0: "0 < h"
  shows bm_R2_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2)"
    and bm_R2_integral:
    "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<le> 3 * (real CARD('n))\<^sup>2 * h\<^sup>2"
proof -
  have h0': "(0::real) \<le> h" using h0 by simp
  have m: "\<And>i. (\<lambda>\<omega>. \<omega> i h)
      \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using h0' by (intro measurable_bm_coordinate) simp
  have i4: "\<And>i. integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h) ^ 4)"
    by (rule bm_coordinate_pow4_integrable[OF h0])
  have prod_int: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)" for i j
  proof (rule Bochner_Integration.integrable_bound
      [where f = "\<lambda>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"])
    show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (\<lambda>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)"
      using i4 by auto
    show "(\<lambda>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      using m by measurable
    show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        norm ((\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
          \<le> norm ((\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2 \<le> (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"
        by (rule prod_sq_le_half_pow4)
      moreover have "0 \<le> (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2" by simp
      moreover have "0 \<le> (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"
        by (intro add_nonneg_nonneg) simp_all
      ultimately show "norm ((\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
          \<le> norm ((\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)" by simp
    qed
  qed
  have expand: "(\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)"
    for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    by (simp add: power2_eq_square sum_product)
  show int: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2)"
    unfolding expand by (intro Bochner_Integration.integrable_sum prod_int)
  have per: "(\<integral>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) \<le> 3 * h\<^sup>2" for i j
  proof -
    have "(\<integral>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
        \<le> (\<integral>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2
            \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
    proof (rule integral_mono_AE)
      show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
          (\<lambda>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)" by (rule prod_int)
      show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
          (\<lambda>\<omega>. (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2)"
        using i4 by auto
      show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
          (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
            \<le> (\<omega> i h) ^ 4 / 2 + (\<omega> j h) ^ 4 / 2"
        by (intro AE_I2 prod_sq_le_half_pow4)
    qed
    also have "\<dots> = 3 * h\<^sup>2 / 2 + 3 * h\<^sup>2 / 2"
      using i4 by (simp add: bm_coordinate_pow4_integral[OF h0])
    finally show ?thesis by simp
  qed
  have "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (\<Sum>j\<in>UNIV. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2)
          \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))"
    unfolding expand
    by (rule Bochner_Integration.integral_sum)
      (intro Bochner_Integration.integrable_sum prod_int)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (\<integral>\<omega>. (\<omega> i h)\<^sup>2 * (\<omega> j h)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))"
    by (intro sum.cong refl Bochner_Integration.integral_sum prod_int)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). 3 * h\<^sup>2)"
    by (intro sum_mono per)
  also have "\<dots> = 3 * (real CARD('n))\<^sup>2 * h\<^sup>2"
    by (simp add: power2_eq_square)
  finally show "(\<integral>\<omega>. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      \<le> 3 * (real CARD('n))\<^sup>2 * h\<^sup>2" .
qed

subsection \<open>The step increment: mean zero\<close>

theorem sbm_xi_mean0:
  fixes S :: "real^'n::finite^'n" and M :: "real^'n^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows sbm_xi_integrable:
    "integrable (pair_law_of h (sbmpair S h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (\<lambda>\<omega>'. trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))"
    and sbm_xi_mean:
    "(\<integral>\<omega>'. trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S)))
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?\<mu> = "pair_law_of h (sbmpair S h) ?M"
  let ?B = "borel_of (mtopology_of (path_metric h :: ('n pairpath) metric))"
  let ?\<xi> = "\<lambda>\<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h) - fst (\<omega>' 0)) - h *\<^sub>R (S ** transpose S)))"
  let ?g = "\<lambda>\<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h)) - snd (\<omega>' h)))"
  have h0': "(0::real) \<le> h" using h0 by simp
  have hI: "h \<in> {0..h}" using h0' by simp
  have mem: "?\<mu> \<in> paper_pair_class k L h (0 :: real^'n)"
    by (rule sbmpair_law_in_paper_pair_class[OF h0' L1 SST])
  have sets\<mu>: "sets ?\<mu> = sets ?B" by simp
  have evh: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' h) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have ev0: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' 0) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have pairm: "(\<lambda>\<omega>' :: 'n pairpath. (\<omega>' h, \<omega>' 0)) \<in> ?B \<rightarrow>\<^sub>M borel"
    using evh ev0 by (simp add: borel_prod[symmetric])
  have contxi: "(\<lambda>p :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
      trace (M ** (outerp (fst (fst p) - fst (snd p))
        - h *\<^sub>R (S ** transpose S)))) \<in> borel_measurable borel"
  proof (intro borel_measurable_continuous_onI)
    have e: "(\<lambda>p :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        trace (M ** (outerp (fst (fst p) - fst (snd p))
          - h *\<^sub>R (S ** transpose S))))
        = (\<lambda>p. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j
            * ((fst (fst p) $ j - fst (snd p) $ j)
                * (fst (fst p) $ i - fst (snd p) $ i)
              - h * (S ** transpose S) $ j $ i))"
      by (rule ext)
        (simp add: trace_def matrix_matrix_mult_def outerp_def
          vector_minus_component vector_scaleR_component
          sum_distrib_left algebra_simps sum_subtractf)
    show "continuous_on UNIV (\<lambda>p :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        trace (M ** (outerp (fst (fst p) - fst (snd p))
          - h *\<^sub>R (S ** transpose S))))"
      unfolding e by (intro continuous_intros)
  qed
  have ximeas: "?\<xi> \<in> borel_measurable ?B"
    using measurable_compose[OF pairm contxi] by (simp add: o_def)
  have ximeas\<mu>: "?\<xi> \<in> borel_measurable ?\<mu>"
    using ximeas measurable_cong_sets[OF sets\<mu>[symmetric] refl] by blast
  have contg: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n).
      trace (M ** (outerp (fst q) - snd q))) \<in> borel_measurable borel"
  proof (intro borel_measurable_continuous_onI)
    have e: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n).
        trace (M ** (outerp (fst q) - snd q)))
        = (\<lambda>q. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. M $ i $ j
            * (fst q $ j * fst q $ i - snd q $ j $ i))"
      by (rule ext)
        (simp add: trace_def matrix_matrix_mult_def outerp_def
          vector_minus_component sum_distrib_left algebra_simps
          sum_subtractf)
    show "continuous_on UNIV (\<lambda>q :: (real^'n) \<times> (real^'n^'n).
        trace (M ** (outerp (fst q) - snd q)))"
      unfolding e by (intro continuous_intros)
  qed
  have gmeas: "?g \<in> borel_measurable ?B"
    using measurable_compose[OF evh contg] by (simp add: o_def)
  have gmeas\<mu>: "?g \<in> borel_measurable ?\<mu>"
    using gmeas measurable_cong_sets[OF sets\<mu>[symmetric] refl] by blast
  have start: "AE \<omega>' in ?\<mu>. fst (\<omega>' 0) = (0 :: real^'n) \<and> snd (\<omega>' 0) = 0"
    using mem unfolding paper_pair_class_def by blast
  have snddet: "AE \<omega>' in ?\<mu>. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S)"
  proof -
    have phim: "sbmpair S h \<in> ?M \<rightarrow>\<^sub>M ?B"
      by (rule sbmpair_measurable[OF h0'])
    have sndm: "(\<lambda>\<omega>' :: 'n pairpath. snd (\<omega>' h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      using evh by (simp add: borel_prod[symmetric])
    have mset: "{\<omega>' \<in> space ?B. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S)}
        \<in> sets ?B"
    proof -
      have "{\<omega>' \<in> space ?B. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S)}
          = (\<lambda>\<omega>' :: 'n pairpath. snd (\<omega>' h))
            -` {h *\<^sub>R (S ** transpose S)} \<inter> space ?B"
        by auto
      then show ?thesis using measurable_sets[OF sndm] by simp
    qed
    have iff: "(AE \<omega>' in ?\<mu>. snd (\<omega>' h) = h *\<^sub>R (S ** transpose S))
        = (AE \<omega> in ?M. snd (sbmpair S h \<omega> h) = h *\<^sub>R (S ** transpose S))"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
    have "AE \<omega> in ?M. snd (sbmpair S h \<omega> h) = h *\<^sub>R (S ** transpose S)"
      by (intro AE_I2) (simp add: sbmpair_apply[OF hI])
    then show ?thesis unfolding iff .
  qed
  have aeq: "AE \<omega>' in ?\<mu>. ?\<xi> \<omega>' = ?g \<omega>'"
    using start snddet by eventually_elim simp
  have int_inner: "integrable ?\<mu>
      (\<lambda>\<omega>'. outerp (fst (\<omega>' h)) - snd (\<omega>' h))"
    by (rule paper_pair_class_compensated_integrable[OF mem hI])
  have intg: "integrable ?\<mu> ?g"
    by (rule integrable_bounded_linear[OF trace_mult_blin int_inner])
  show "integrable ?\<mu> ?\<xi>"
    by (rule integrable_cong_AE[THEN iffD2, OF ximeas\<mu> gmeas\<mu> aeq intg])
  have op0: "outerp (0 :: real^'n) = 0"
    by (simp add: outerp_def vec_eq_iff zero_vec_def)
  have "(\<integral>\<omega>'. ?\<xi> \<omega>' \<partial>?\<mu>) = (\<integral>\<omega>'. ?g \<omega>' \<partial>?\<mu>)"
    by (rule integral_cong_AE[OF ximeas\<mu> gmeas\<mu> aeq])
  also have "\<dots> = trace (M ** (\<integral>\<omega>'. outerp (fst (\<omega>' h)) - snd (\<omega>' h)
      \<partial>?\<mu>))"
    by (rule integral_of_bounded_linear[OF trace_mult_blin int_inner])
  also have "\<dots> = trace (M ** outerp (0 :: real^'n))"
    by (simp add: paper_pair_class_compensated_mean[OF mem hI])
  also have "\<dots> = 0"
    unfolding op0 by (rule trace_mult_zero_right)
  finally show "(\<integral>\<omega>'. ?\<xi> \<omega>' \<partial>?\<mu>) = 0" .
qed

subsection \<open>The step increment: variance of order \<open>h\<^sup>2\<close>\<close>

lemma diff_sq_le_double:
  fixes a c :: real
  shows "(a - c)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * c\<^sup>2"
proof -
  have "2 * a\<^sup>2 + 2 * c\<^sup>2 - (a - c)\<^sup>2 = (a + c)\<^sup>2"
    by (simp add: power2_diff power2_sum algebra_simps)
  moreover have "0 \<le> (a + c)\<^sup>2" by simp
  ultimately show ?thesis by linarith
qed

theorem sbm_xi_sq_bound:
  fixes S :: "real^'n::finite^'n" and M :: "real^'n^'n" and h :: real
  defines "Cmm \<equiv> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  defines "Cs \<equiv> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>S $ i $ j\<bar>)"
  defines "n' \<equiv> real (CARD('n))"
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows sbm_xi_sq_integrable:
    "integrable (pair_law_of h (sbmpair S h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (\<lambda>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2)"
    and sbm_xi_sq_integral:
    "(\<integral>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))
      \<le> (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?\<mu> = "pair_law_of h (sbmpair S h) ?M"
  let ?B = "borel_of (mtopology_of (path_metric h :: ('n pairpath) metric))"
  let ?\<xi> = "\<lambda>\<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h) - fst (\<omega>' 0)) - h *\<^sub>R (S ** transpose S)))"
  let ?V = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<chi> i. \<omega> i h) :: real^'n"
  let ?R = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<Sum>i\<in>UNIV. (\<omega> i h)\<^sup>2)"
  define b where "b = trace (M ** (S ** transpose S))"
  define CA where "CA = 2 * (Cmm * Cs\<^sup>2)\<^sup>2"
  define CB where "CB = 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2"
  have h0': "(0::real) \<le> h" using h0 by simp
  have hI: "h \<in> {0..h}" using h0' by simp
  have z0: "(0::real) \<in> {0..h}" using h0' by simp
  have L0: "0 \<le> L" using L1 by simp
  have Cmm0: "0 \<le> Cmm" unfolding Cmm_def by (intro sum_nonneg) simp_all
  have Cs0: "0 \<le> Cs" unfolding Cs_def by (intro sum_nonneg) simp_all
  have CA0: "0 \<le> CA" unfolding CA_def by simp
  have CB0: "0 \<le> CB" unfolding CB_def by simp
  interpret BMPP: prob_space ?M by (rule prob_space_bm_paths)
  \<comment> \<open>measurability of the squared increment functional\<close>
  have sets\<mu>: "sets ?\<mu> = sets ?B" by simp
  have xim\<mu>: "?\<xi> \<in> borel_measurable ?\<mu>"
    by (rule borel_measurable_integrable[OF sbm_xi_integrable[OF h0 L1 SST]])
  have ximeas: "?\<xi> \<in> borel_measurable ?B"
    using xim\<mu> measurable_cong_sets[OF sets\<mu> refl] by blast
  have xi2meas: "(\<lambda>\<omega>'. (?\<xi> \<omega>')\<^sup>2) \<in> borel_measurable ?B"
    by (intro borel_measurable_power ximeas)
  have phim: "sbmpair S h \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule sbmpair_measurable[OF h0'])
  have xi2measM: "(\<lambda>\<omega>. (?\<xi> (sbmpair S h \<omega>))\<^sup>2) \<in> borel_measurable ?M"
    using measurable_compose[OF phim xi2meas] by (simp add: o_def)
  \<comment> \<open>the increment is the matrix image of the coordinate vector, a.e.\<close>
  have aeV: "AE \<omega> in ?M.
      fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0) = S *v ?V \<omega>"
  proof -
    have a1: "AE \<omega> in ?M. cbmX (0 :: real^'n) h \<omega> = bmX 0 h \<omega>"
      by (intro cbmX_ae_eq) (use h0' in simp)
    have a2: "AE \<omega> in ?M. cbmX (0 :: real^'n) 0 \<omega> = bmX 0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    have a3: "AE \<omega> in ?M. bmX (0 :: real^'n) 0 \<omega> = 0"
      by (rule bmX_start)
    show ?thesis
      using a1 a2 a3
    proof eventually_elim
      case (elim \<omega>)
      have "fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0)
          = S *v cbmX (0 :: real^'n) h \<omega> - S *v cbmX (0 :: real^'n) 0 \<omega>"
        by (simp add: sbmpair_apply[OF hI] sbmpair_apply[OF z0])
      also have "\<dots> = S *v (cbmX (0 :: real^'n) h \<omega>
          - cbmX (0 :: real^'n) 0 \<omega>)"
        by (simp add: matrix_vector_mult_diff_distrib)
      also have "\<dots> = S *v bmX (0 :: real^'n) h \<omega>"
        using elim by simp
      also have "\<dots> = S *v ?V \<omega>"
        by (simp add: bmX_def)
      finally show ?case .
    qed
  qed
  \<comment> \<open>uniform pointwise bounds\<close>
  have qb: "\<bar>(S *v v) \<bullet> (M *v (S *v v))\<bar> \<le> Cmm * Cs\<^sup>2 * (v \<bullet> v)"
    for v :: "real^'n"
  proof -
    have "\<bar>(S *v v) \<bullet> (M *v (S *v v))\<bar>
        \<le> norm (S *v v) * norm (M *v (S *v v))"
      by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> norm (S *v v) * (Cmm * norm (S *v v))"
      unfolding Cmm_def
      by (intro mult_left_mono matvec_norm_le) simp
    also have "\<dots> = Cmm * (norm (S *v v))\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> \<le> Cmm * (Cs * norm v)\<^sup>2"
      unfolding Cs_def
      by (intro mult_left_mono power_mono matvec_norm_le)
        (simp_all add: Cmm_def[symmetric] Cmm0)
    also have "\<dots> = Cmm * Cs\<^sup>2 * (v \<bullet> v)"
      by (simp add: power_mult_distrib power2_norm_eq_inner algebra_simps)
    finally show ?thesis .
  qed
  have bb: "\<bar>b\<bar> \<le> n'\<^sup>2 * Cmm * L"
  proof -
    define col where "col = (\<lambda>j. (\<chi> i. S $ i $ j) :: real^'n)"
    have Se: "S = (\<chi> i j. col j $ i)"
      unfolding col_def by (simp add: vec_eq_iff)
    have deco: "S ** transpose S = (\<Sum>j\<in>UNIV. outerp (col j))"
      using Se cols_mult_transpose by blast
    have beq: "b = (\<Sum>j\<in>UNIV. col j \<bullet> (M *v col j))"
      unfolding b_def deco by (simp add: trace_mult_outerp_sum)
    have per: "\<bar>col j \<bullet> (M *v col j)\<bar> \<le> Cmm * (n' * L)" for j
    proof -
      have "\<bar>col j \<bullet> (M *v col j)\<bar> \<le> norm (col j) * norm (M *v col j)"
        by (rule Cauchy_Schwarz_ineq2)
      also have "\<dots> \<le> norm (col j) * (Cmm * norm (col j))"
        unfolding Cmm_def by (intro mult_left_mono matvec_norm_le) simp
      also have "\<dots> = Cmm * (norm (col j))\<^sup>2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> Cmm * (n' * L)"
      proof (intro mult_left_mono Cmm0)
        have "(norm (col j))\<^sup>2 = (\<Sum>i\<in>UNIV. (S $ i $ j)\<^sup>2)"
          unfolding col_def
          by (simp add: power2_norm_eq_inner inner_vec_def
              power2_eq_square[of "S $ _ $ _"])
        also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). L)"
        proof (rule sum_mono)
          fix i :: 'n
          have "(S $ i $ j)\<^sup>2 = \<bar>S $ i $ j\<bar>\<^sup>2" by simp
          also have "\<dots> \<le> (sqrt L)\<^sup>2"
            using sbm_entry_bound[OF SST, of i j]
            by (intro power_mono) simp_all
          also have "\<dots> = L" using L0 by simp
          finally show "(S $ i $ j)\<^sup>2 \<le> L" .
        qed
        also have "\<dots> = n' * L" unfolding n'_def by simp
        finally show "(norm (col j))\<^sup>2 \<le> n' * L" .
      qed
      finally show ?thesis .
    qed
    have "\<bar>b\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>col j \<bullet> (M *v col j)\<bar>)"
      unfolding beq by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>(UNIV :: 'n set). Cmm * (n' * L))"
      by (intro sum_mono per)
    also have "\<dots> = n' * (Cmm * (n' * L))" unfolding n'_def by simp
    also have "\<dots> = n'\<^sup>2 * Cmm * L"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have Vsq: "?V \<omega> \<bullet> ?V \<omega> = ?R \<omega>" for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    by (simp add: inner_vec_def power2_eq_square)
  \<comment> \<open>the pointwise domination\<close>
  have ptw: "AE \<omega> in ?M. (?\<xi> (sbmpair S h \<omega>))\<^sup>2
      \<le> CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2"
    using aeV
  proof eventually_elim
    case (elim \<omega>)
    have xieq: "?\<xi> (sbmpair S h \<omega>)
        = (S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)) - h * b"
    proof -
      have "?\<xi> (sbmpair S h \<omega>) = trace (M ** (outerp (S *v ?V \<omega>)
          - h *\<^sub>R (S ** transpose S)))"
        using elim by simp
      also have "\<dots> = trace (M ** outerp (S *v ?V \<omega>))
          - trace (M ** (h *\<^sub>R (S ** transpose S)))"
        by (simp add: trace_mult_diff)
      also have "trace (M ** (h *\<^sub>R (S ** transpose S))) = h * b"
        unfolding b_def by (simp add: matmul_scaleR_right trace_scaleR)
      also have "trace (M ** outerp (S *v ?V \<omega>))
          = (S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>))"
        by (rule trace_mult_outerp)
      finally show ?thesis by simp
    qed
    have step1: "(?\<xi> (sbmpair S h \<omega>))\<^sup>2
        \<le> 2 * ((S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)))\<^sup>2 + 2 * (h * b)\<^sup>2"
      unfolding xieq by (rule diff_sq_le_double)
    have step2: "((S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)))\<^sup>2
        \<le> (Cmm * Cs\<^sup>2)\<^sup>2 * (?R \<omega>)\<^sup>2"
    proof -
      have nnq: "0 \<le> Cmm * Cs\<^sup>2 * (?V \<omega> \<bullet> ?V \<omega>)"
        using Cmm0 Cs0 by (intro mult_nonneg_nonneg) simp_all
      have "((S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>)))\<^sup>2
          = \<bar>(S *v ?V \<omega>) \<bullet> (M *v (S *v ?V \<omega>))\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (Cmm * Cs\<^sup>2 * (?V \<omega> \<bullet> ?V \<omega>))\<^sup>2"
        using qb[of "?V \<omega>"] nnq by (intro power_mono) simp_all
      also have "\<dots> = (Cmm * Cs\<^sup>2)\<^sup>2 * (?R \<omega>)\<^sup>2"
        unfolding Vsq by (simp add: power_mult_distrib)
      finally show ?thesis .
    qed
    have step3: "(h * b)\<^sup>2 \<le> (n'\<^sup>2 * Cmm * L)\<^sup>2 * h\<^sup>2"
    proof -
      have nb: "0 \<le> n'\<^sup>2 * Cmm * L"
        using Cmm0 L0 by (intro mult_nonneg_nonneg) simp_all
      have "(h * b)\<^sup>2 = h\<^sup>2 * \<bar>b\<bar>\<^sup>2"
        by (simp add: power_mult_distrib)
      also have "\<dots> \<le> h\<^sup>2 * (n'\<^sup>2 * Cmm * L)\<^sup>2"
        using bb nb by (intro mult_left_mono power_mono) simp_all
      finally show ?thesis by (simp add: algebra_simps)
    qed
    show ?case using step1 step2 step3
      unfolding CA_def CB_def by linarith
  qed
  \<comment> \<open>integrability of the dominating function and of the square\<close>
  have Rint: "integrable ?M (\<lambda>\<omega>. (?R \<omega>)\<^sup>2)"
    by (rule bm_R2_integrable[OF h0])
  have domint: "integrable ?M (\<lambda>\<omega>. CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2)"
    by (intro Bochner_Integration.integrable_add integrable_cmult Rint
        BMP.integrable_const)
  have int2M: "integrable ?M (\<lambda>\<omega>. (?\<xi> (sbmpair S h \<omega>))\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound[OF domint xi2measM])
    show "AE \<omega> in ?M. norm ((?\<xi> (sbmpair S h \<omega>))\<^sup>2)
        \<le> norm (CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2)"
      using ptw
    proof eventually_elim
      case (elim \<omega>)
      have "0 \<le> CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2"
        using CA0 CB0 by (intro add_nonneg_nonneg mult_nonneg_nonneg)
          simp_all
      then show ?case using elim by simp
    qed
  qed
  show "integrable ?\<mu> (\<lambda>\<omega>'. (?\<xi> \<omega>')\<^sup>2)"
    unfolding pair_law_of_def
    by (subst integrable_distr_eq[OF phim xi2meas]) (rule int2M)
  \<comment> \<open>the integral bound\<close>
  have "(\<integral>\<omega>'. (?\<xi> \<omega>')\<^sup>2 \<partial>?\<mu>) = (\<integral>\<omega>. (?\<xi> (sbmpair S h \<omega>))\<^sup>2 \<partial>?M)"
    unfolding pair_law_of_def by (rule integral_distr[OF phim xi2meas])
  also have "\<dots> \<le> (\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2 \<partial>?M)"
    by (rule integral_mono_AE[OF int2M domint ptw])
  also have "\<dots> = CA * (\<integral>\<omega>. (?R \<omega>)\<^sup>2 \<partial>?M) + CB * h\<^sup>2"
  proof -
    have ic: "integrable ?M (\<lambda>\<omega>. CA * (?R \<omega>)\<^sup>2)"
      by (rule integrable_cmult[OF Rint])
    have icc: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. CB * h\<^sup>2)"
      by simp
    have "(\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 + CB * h\<^sup>2 \<partial>?M)
        = (\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 \<partial>?M) + (\<integral>\<omega>. CB * h\<^sup>2 \<partial>?M)"
      by (rule Bochner_Integration.integral_add[OF ic icc])
    also have "(\<integral>\<omega>. CA * (?R \<omega>)\<^sup>2 \<partial>?M) = CA * (\<integral>\<omega>. (?R \<omega>)\<^sup>2 \<partial>?M)"
      by (rule integral_cmult[OF Rint])
    also have "(\<integral>\<omega>. CB * h\<^sup>2 \<partial>?M) = measure ?M (space ?M) *\<^sub>R (CB * h\<^sup>2)"
      by (rule lebesgue_integral_const)
    finally show ?thesis
      by (simp add: BMP.prob_space)
  qed
  also have "\<dots> \<le> CA * (3 * n'\<^sup>2 * h\<^sup>2) + CB * h\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (?R \<omega>)\<^sup>2 \<partial>?M) \<le> 3 * (real CARD('n))\<^sup>2 * h\<^sup>2"
      by (rule bm_R2_integral[OF h0])
    then show ?thesis
      using CA0 unfolding n'_def by (intro add_right_mono mult_left_mono)
  qed
  also have "\<dots> = (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2"
    unfolding CA_def CB_def by (simp add: algebra_simps)
  finally show "(\<integral>\<omega>'. (?\<xi> \<omega>')\<^sup>2 \<partial>?\<mu>)
      \<le> (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2" .
qed

subsection \<open>A volatility-uniform variance constant\<close>

definition xiC :: "real^'n::finite^'n \<Rightarrow> real \<Rightarrow> real" where
  "xiC M L = (let n' = real (CARD('n));
      Cmm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)
    in 6 * (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2)"

lemma xiC_nonneg: "0 \<le> xiC M L"
proof -
  have "0 \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
    by (intro sum_nonneg) simp_all
  then show ?thesis
    unfolding xiC_def Let_def
    by (intro add_nonneg_nonneg mult_nonneg_nonneg zero_le_power2) simp_all
qed

corollary sbm_xi_sq_bound_uniform:
  fixes S :: "real^'n::finite^'n" and M :: "real^'n^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SST: "S ** transpose S \<in> sconstraint k L"
  shows "(\<integral>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))
      \<le> xiC M L * h\<^sup>2"
proof -
  define Cmm where "Cmm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  define Cs where "Cs = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>S $ i $ j\<bar>)"
  define n' where "n' = real (CARD('n))"
  have Cmm0: "0 \<le> Cmm" unfolding Cmm_def by (intro sum_nonneg) simp_all
  have Cs0: "0 \<le> Cs" unfolding Cs_def by (intro sum_nonneg) simp_all
  have Csle: "Cs \<le> n'\<^sup>2 * sqrt L"
  proof -
    have "Cs \<le> (\<Sum>i\<in>(UNIV :: 'n set). \<Sum>j\<in>(UNIV :: 'n set). sqrt L)"
      unfolding Cs_def by (intro sum_mono sbm_entry_bound[OF SST])
    also have "\<dots> = n'\<^sup>2 * sqrt L"
      unfolding n'_def by (simp add: power2_eq_square mult_ac)
    finally show ?thesis .
  qed
  have base: "(\<integral>\<omega>'. (trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
        - h *\<^sub>R (S ** transpose S))))\<^sup>2
      \<partial>(pair_law_of h (sbmpair S h)
          (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)))
      \<le> (6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2) * h\<^sup>2"
    unfolding Cmm_def Cs_def n'_def by (rule sbm_xi_sq_bound[OF h0 L1 SST])
  have mono1: "Cmm * Cs\<^sup>2 \<le> Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2"
    by (intro mult_left_mono power_mono Csle Cs0 Cmm0)
  have mono2: "(Cmm * Cs\<^sup>2)\<^sup>2 \<le> (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2"
    by (intro power_mono mono1 mult_nonneg_nonneg Cmm0) simp_all
  have mono3: "6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 \<le> 6 * (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2 * n'\<^sup>2"
    by (intro mult_right_mono mult_left_mono mono2) simp_all
  have xiCe: "xiC M L = 6 * (Cmm * (n'\<^sup>2 * sqrt L)\<^sup>2)\<^sup>2 * n'\<^sup>2
      + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2"
    unfolding xiC_def Let_def Cmm_def n'_def by (rule refl)
  have tot: "6 * (Cmm * Cs\<^sup>2)\<^sup>2 * n'\<^sup>2 + 2 * (n'\<^sup>2 * Cmm * L)\<^sup>2 \<le> xiC M L"
    unfolding xiCe using mono3 by linarith
  have h2: "(0::real) \<le> h\<^sup>2" by simp
  from base mult_right_mono[OF tot h2] show ?thesis by linarith
qed

subsection \<open>The compensated grid functional of the Euler process\<close>

definition euXi :: "(real^'n::finite \<Rightarrow> real^'n^'n) \<Rightarrow> real^'n^'n \<Rightarrow> real
    \<Rightarrow> nat \<Rightarrow> 'n pairpath \<Rightarrow> real" where
  "euXi SF M h m \<omega> = (\<Sum>j<m. trace (M ** (outerp
      (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
      - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
          ** transpose (SF (fst (\<omega> (real j * h))))))))"

lemma euXi_term_cont:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and h :: real
  assumes SFc: "continuous_on UNIV SF"
  shows "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
      trace (M ** (outerp (fst (fst ab) - fst (snd ab))
        - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))))"
proof -
  have entry: "continuous_on UNIV (\<lambda>z :: real^'n. SF z $ i $ j)" for i j
  proof -
    have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ j)"
      using bounded_linear_vec_nth bounded_linear_compose by blast
    show ?thesis
      by (rule continuous_on_compose2[OF linear_continuous_on[OF bl] SFc])
        auto
  qed
  have proj2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab))"
    by (intro continuous_on_fst continuous_on_snd continuous_on_id)
  have proj1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab))"
    by (intro continuous_on_fst continuous_on_id)
  have SFcomp: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). SF (fst (snd ab)) $ i $ j)" for i j
    by (rule continuous_on_compose2[OF entry proj2]) auto
  have vcomp1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab) $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] proj1]) auto
  have vcomp2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab) $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] proj2]) auto
  have inner: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
      \<times> ((real^'n) \<times> (real^'n^'n)).
      outerp (fst (fst ab) - fst (snd ab))
        - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))"
  proof -
    have e: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        outerp (fst (fst ab) - fst (snd ab))
          - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))
        = (\<lambda>ab. \<chi> i j. (fst (fst ab) $ i - fst (snd ab) $ i)
              * (fst (fst ab) $ j - fst (snd ab) $ j)
            - h * (\<Sum>l\<in>UNIV. SF (fst (snd ab)) $ i $ l
                * SF (fst (snd ab)) $ j $ l))"
      by (rule ext) (simp add: outerp_def matrix_matrix_mult_def
          transpose_def vec_eq_iff vector_minus_component
          vector_scaleR_component)
    show ?thesis unfolding e
      by (intro continuous_on_vec_lambda continuous_intros
          SFcomp vcomp1 vcomp2)
  qed
  show ?thesis
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF trace_mult_blin] inner]) auto
qed

lemma euXi_measurable:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and h :: real
  assumes SFc: "continuous_on UNIV SF"
  shows "euXi SF M h m \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have tm: "(\<lambda>\<omega> :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
      - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
          ** transpose (SF (fst (\<omega> (real j * h))))))))
      \<in> borel_measurable ?B" for j
  proof -
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real (Suc j) * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have evv: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real j * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have pairm: "(\<lambda>\<omega> :: 'n pairpath.
        (\<omega> (real (Suc j) * h), \<omega> (real j * h))) \<in> ?B \<rightarrow>\<^sub>M borel"
      using evu evv by (simp add: borel_prod[symmetric])
    have cm: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        trace (M ** (outerp (fst (fst ab) - fst (snd ab))
          - h *\<^sub>R (SF (fst (snd ab)) ** transpose (SF (fst (snd ab)))))))
        \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF euXi_term_cont[OF SFc]])
    show ?thesis using measurable_compose[OF pairm cm] by simp
  qed
  show ?thesis unfolding euXi_def by (intro borel_measurable_sum tm)
qed

lemma euXi_pglue_split:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and \<omega> \<omega>' :: "'n pairpath" and h :: real
  assumes h0: "0 \<le> h"
  shows "euXi SF M h (Suc (Suc N)) (pglue (real (Suc N) * h)
        (real (Suc (Suc N)) * h) \<omega> \<omega>')
      = euXi SF M h (Suc N) \<omega>
        + trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
            - h *\<^sub>R (SF (fst (\<omega> (real (Suc N) * h)))
                ** transpose (SF (fst (\<omega> (real (Suc N) * h)))))))"
proof -
  let ?r = "real (Suc N) * h"
  let ?T = "real (Suc (Suc N)) * h"
  let ?g = "pglue ?r ?T \<omega> \<omega>'"
  have mem: "real j * h \<in> {0..?T}" if le: "j \<le> Suc (Suc N)" for j
  proof -
    have a: "0 \<le> real j * h"
      by (intro mult_nonneg_nonneg h0) simp_all
    have b: "real j * h \<le> ?T"
      using le h0 by (intro mult_right_mono) simp_all
    show ?thesis using a b by simp
  qed
  have prefl: "?g (real j * h) = \<omega> (real j * h)" if j: "j \<le> Suc N" for j
  proof (rule pglue_le)
    show "real j * h \<in> {0..?T}" using j by (intro mem) simp
    show "real j * h \<le> ?r" using j h0 by (intro mult_right_mono) simp_all
  qed
  have rleT: "?r \<le> ?T" using h0 by (intro mult_right_mono) simp_all
  have Tmem: "?T \<in> {0..?T}" by (rule mem) simp
  have gT: "?g ?T = \<omega> ?r + (\<omega>' (?T - ?r) - \<omega>' 0)"
    by (rule pglue_ge[OF Tmem rleT])
  have gr: "?g ?r = \<omega> ?r" by (rule prefl) simp
  have Tr: "?T - ?r = h" by (simp add: algebra_simps)
  have head: "fst (?g ?T) - fst (?g ?r) = fst (\<omega>' h) - fst (\<omega>' 0)"
    unfolding gT gr Tr by simp
  have "euXi SF M h (Suc (Suc N)) ?g
      = (\<Sum>j<Suc N. trace (M ** (outerp
          (fst (?g (real (Suc j) * h)) - fst (?g (real j * h)))
          - h *\<^sub>R (SF (fst (?g (real j * h)))
              ** transpose (SF (fst (?g (real j * h))))))))
        + trace (M ** (outerp
          (fst (?g (real (Suc (Suc N)) * h)) - fst (?g (real (Suc N) * h)))
          - h *\<^sub>R (SF (fst (?g (real (Suc N) * h)))
              ** transpose (SF (fst (?g (real (Suc N) * h)))))))"
    unfolding euXi_def by (subst sum.lessThan_Suc) (simp add: add.commute)
  also have "(\<Sum>j<Suc N. trace (M ** (outerp
        (fst (?g (real (Suc j) * h)) - fst (?g (real j * h)))
        - h *\<^sub>R (SF (fst (?g (real j * h)))
            ** transpose (SF (fst (?g (real j * h))))))))
      = euXi SF M h (Suc N) \<omega>"
    unfolding euXi_def
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {..<Suc N}"
    then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" by auto
    show "trace (M ** (outerp
        (fst (?g (real (Suc j) * h)) - fst (?g (real j * h)))
        - h *\<^sub>R (SF (fst (?g (real j * h)))
            ** transpose (SF (fst (?g (real j * h)))))))
      = trace (M ** (outerp
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
            ** transpose (SF (fst (\<omega> (real j * h)))))))"
      by (simp only: prefl[OF j1] prefl[OF j2])
  qed
  also have "trace (M ** (outerp
        (fst (?g (real (Suc (Suc N)) * h)) - fst (?g (real (Suc N) * h)))
        - h *\<^sub>R (SF (fst (?g (real (Suc N) * h)))
            ** transpose (SF (fst (?g (real (Suc N) * h)))))))
      = trace (M ** (outerp (fst (\<omega>' h) - fst (\<omega>' 0))
          - h *\<^sub>R (SF (fst (\<omega> ?r)) ** transpose (SF (fst (\<omega> ?r))))))"
  proof -
    have "fst (?g ?T) - fst (?g ?r) = fst (\<omega>' h) - fst (\<omega>' 0)"
      by (rule head)
    moreover have "fst (?g ?r) = fst (\<omega> ?r)" unfolding gr by (rule refl)
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

subsection \<open>The second moment of the grid functional grows linearly\<close>

theorem eulerp_Xi_sq_bound:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "integrable (eulerp SF x h N) (\<lambda>\<omega>. (euXi SF M h (Suc N) \<omega>)\<^sup>2)
      \<and> (\<integral>\<omega>. (euXi SF M h (Suc N) \<omega>)\<^sup>2 \<partial>(eulerp SF x h N))
        \<le> real (Suc N) * xiC M L * h\<^sup>2"
proof (induction N)
  case 0
  have h0': "(0::real) \<le> h" using h0 by simp
  let ?\<mu>0 = "pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  let ?Bh = "borel_of (mtopology_of (path_metric h :: ('n pairpath) metric))"
  note SFsx = SFs[of x]
  have E0: "eulerp SF x h 0 = pshift_law h x ?\<mu>0" by simp
  have sets\<mu>: "sets ?\<mu>0 = sets ?Bh" by simp
  have shm: "pshift h x \<in> ?\<mu>0 \<rightarrow>\<^sub>M ?Bh"
    using pshift_measurable[OF h0'] measurable_cong_sets[OF sets\<mu> refl]
    by blast
  have Gm2: "(\<lambda>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2) \<in> borel_measurable ?Bh"
    by (intro borel_measurable_power euXi_measurable[OF SFc])
  have st: "AE \<omega> in ?\<mu>0. fst (\<omega> 0) = (0 :: real^'n)"
    using sbmpair_law_start[OF h0', of "SF x"]
    by (rule eventually_mono) simp
  have cong: "AE \<omega> in ?\<mu>0. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2
      = (trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
          - h *\<^sub>R (SF x ** transpose (SF x)))))\<^sup>2"
    using st
  proof eventually_elim
    case (elim \<omega>)
    have m1: "h \<in> {0..h}" using h0' by simp
    have m2: "(0::real) \<in> {0..h}" using h0' by simp
    have "euXi SF M h (Suc 0) (pshift h x \<omega>)
        = trace (M ** (outerp
            (fst (pshift h x \<omega> h) - fst (pshift h x \<omega> 0))
            - h *\<^sub>R (SF (fst (pshift h x \<omega> 0))
                ** transpose (SF (fst (pshift h x \<omega> 0))))))"
      unfolding euXi_def by simp
    also have "\<dots> = trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
        - h *\<^sub>R (SF (x + fst (\<omega> 0)) ** transpose (SF (x + fst (\<omega> 0))))))"
      by (simp add: pshift_fst[OF m1] pshift_fst[OF m2])
    also have "\<dots> = trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
        - h *\<^sub>R (SF x ** transpose (SF x))))"
      using elim by simp
    finally show ?case by simp
  qed
  have measL: "(\<lambda>\<omega>. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2)
      \<in> borel_measurable ?\<mu>0"
    by (rule measurable_compose[OF shm Gm2])
  have measR: "(\<lambda>\<omega>. (trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
      - h *\<^sub>R (SF x ** transpose (SF x)))))\<^sup>2) \<in> borel_measurable ?\<mu>0"
    by (intro borel_measurable_power
        borel_measurable_integrable[OF sbm_xi_integrable[OF h0 L1 SFsx]])
  have iB: "integrable (eulerp SF x h 0) (\<lambda>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2)"
  proof -
    have "integrable ?\<mu>0 (\<lambda>\<omega>. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2)"
      using integrable_cong_AE[OF measL measR cong]
        sbm_xi_sq_integrable[OF h0 L1 SFsx] by blast
    then show ?thesis
      unfolding E0 pshift_law_def
      using integrable_distr_eq[OF shm Gm2] by blast
  qed
  have bB: "(\<integral>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2 \<partial>(eulerp SF x h 0))
      \<le> real (Suc 0) * xiC M L * h\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (euXi SF M h (Suc 0) \<omega>)\<^sup>2 \<partial>(eulerp SF x h 0))
        = (\<integral>\<omega>. (euXi SF M h (Suc 0) (pshift h x \<omega>))\<^sup>2 \<partial>?\<mu>0)"
      unfolding E0 pshift_law_def by (rule integral_distr[OF shm Gm2])
    also have "\<dots> = (\<integral>\<omega>. (trace (M ** (outerp (fst (\<omega> h) - fst (\<omega> 0))
        - h *\<^sub>R (SF x ** transpose (SF x)))))\<^sup>2 \<partial>?\<mu>0)"
      by (rule integral_cong_AE[OF measL measR cong])
    also have "\<dots> \<le> xiC M L * h\<^sup>2"
      by (rule sbm_xi_sq_bound_uniform[OF h0 L1 SFsx])
    finally show ?thesis by simp
  qed
  show ?case using iB bB by blast
next
  case (Suc N)
  have h0': "(0::real) \<le> h" using h0 by simp
  define r where "r = real (Suc N) * h"
  define T' where "T' = real (Suc (Suc N)) * h"
  let ?Q = "eulerp SF x h N"
  let ?Br = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Bt = "borel_of (mtopology_of (path_metric T' :: ('n pairpath) metric))"
  let ?MR = "borel_of (mtopology_of
      (path_metric (T' - r) :: ('n pairpath) metric))"
  let ?K = "\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
  let ?A = "euXi SF M h (Suc N)"
  let ?xi = "\<lambda>\<omega> \<omega>' :: 'n pairpath. trace (M ** (outerp
      (fst (\<omega>' h) - fst (\<omega>' 0))
      - h *\<^sub>R (SF (fst (\<omega> r)) ** transpose (SF (fst (\<omega> r))))))"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
  have r0: "0 \<le> r" unfolding r_def using h0' by simp
  have rleT: "r \<le> T'" unfolding r_def T'_def
    using h0' by (intro mult_right_mono) simp_all
  have Qc: "?Q \<in> paper_pair_class k L r x"
    unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  interpret PQ: prob_space ?Q by (rule paper_pair_class_prob[OF Qc])
  have setsQ: "sets ?Q = sets ?Br" by (rule paper_pair_class_sets[OF Qc])
  have ne: "space ?Q \<noteq> {}" by (rule PQ.not_empty)
  note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
    by (simp add: r_def T'_def)
  have phim: "(\<lambda>p. pglue r T' (fst p) (snd p))
      \<in> ksemi ?Q ?MR ?K \<rightarrow>\<^sub>M ?Bt"
    by (rule kglue_law'_measurable[OF r0 rleT setsQ Kp ne])
  have sksemi: "sets (ksemi ?Q ?MR ?K) = sets (?Q \<Otimes>\<^sub>M ?MR)"
    by (rule sets_ksemi[OF Kp ne])
  have Em: "euXi SF M h (Suc (Suc N)) \<in> borel_measurable ?Bt"
    by (rule euXi_measurable[OF SFc])
  have Gmsq: "(\<lambda>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
      \<in> borel_measurable ?Bt"
    by (intro borel_measurable_power Em)
  have Gm2e: "(\<lambda>\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2))
      \<in> borel_measurable ?Bt"
    using Gmsq by measurable
  have Gm2e': "(\<lambda>\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2))
      \<in> borel_measurable (distr (ksemi ?Q ?MR ?K) ?Bt
        (\<lambda>p. pglue r T' (fst p) (snd p)))"
    using Gm2e measurable_cong_sets[OF sets_distr refl] by blast
  have Fsplit: "(euXi SF M h (Suc (Suc N)) (pglue r T' (fst p) (snd p)))\<^sup>2
      = (?A (fst p) + ?xi (fst p) (snd p))\<^sup>2"
    for p :: "'n pairpath \<times> 'n pairpath"
    unfolding r_def T'_def by (simp only: euXi_pglue_split[OF h0'])
  have Feq: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        (euXi SF M h (Suc (Suc N)) (pglue r T' (fst p) (snd p)))\<^sup>2)
      = (\<lambda>p. (?A (fst p) + ?xi (fst p) (snd p))\<^sup>2)"
    by (rule ext) (rule Fsplit)
  have Fm0: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        (euXi SF M h (Suc (Suc N)) (pglue r T' (fst p) (snd p)))\<^sup>2)
      \<in> borel_measurable (ksemi ?Q ?MR ?K)"
    by (intro borel_measurable_power measurable_compose[OF phim Em])
  have Fsq: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        (?A (fst p) + ?xi (fst p) (snd p))\<^sup>2)
      \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?MR)"
    using Fm0 unfolding Feq
    using measurable_cong_sets[OF sksemi refl] by blast
  have Fme: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        ennreal ((?A (fst p) + ?xi (fst p) (snd p))\<^sup>2))
      \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?MR)"
    using Fsq by measurable
  \<comment> \<open>the inner conditional bound, valid for every prefix path\<close>
  have inner: "(\<integral>\<^sup>+\<omega>'. ennreal ((?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2) \<partial>(?K \<omega>))
      \<le> ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2)" for \<omega> :: "'n pairpath"
  proof -
    note SSTw = SFs[of "fst (\<omega> r)"]
    note i1 = sbm_xi_integrable[OF h0 L1 SSTw]
    note i2 = sbm_xi_sq_integrable[OF h0 L1 SSTw]
    note m0 = sbm_xi_mean[OF h0 L1 SSTw]
    note v1 = sbm_xi_sq_bound_uniform[OF h0 L1 SSTw, where M = M]
    interpret KP: prob_space "?K \<omega>"
      by (rule prob_space_sbmpair_law[OF h0'])
    have exl: "(\<lambda>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2)
        = (\<lambda>\<omega>'. (?A \<omega>)\<^sup>2
            + ((2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2))"
      by (rule ext) (simp add: power2_sum algebra_simps)
    have iconst: "integrable (?K \<omega>) (\<lambda>\<omega>'. (?A \<omega>)\<^sup>2)"
      by (rule KP.integrable_const)
    have ia: "integrable (?K \<omega>) (\<lambda>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>')"
      by (rule integrable_cmult[OF i1])
    have ib: "integrable (?K \<omega>)
        (\<lambda>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2)"
      by (rule Bochner_Integration.integrable_add[OF ia i2])
    have icc: "integrable (?K \<omega>) (\<lambda>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2)"
      unfolding exl by (rule Bochner_Integration.integrable_add[OF iconst ib])
    have c1: "(\<integral>\<omega>'. (?A \<omega>)\<^sup>2 \<partial>(?K \<omega>)) = (?A \<omega>)\<^sup>2"
      using lebesgue_integral_const[of "?K \<omega>" "(?A \<omega>)\<^sup>2"] KP.prob_space
      by simp
    have c2: "(\<integral>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
        = (2 * ?A \<omega>) * (\<integral>\<omega>'. ?xi \<omega> \<omega>' \<partial>(?K \<omega>))
          + (\<integral>\<omega>'. (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
      by (simp add: Bochner_Integration.integral_add[OF ia i2]
          integral_cmult[OF i1])
    have split: "(\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
        = (\<integral>\<omega>'. (?A \<omega>)\<^sup>2 \<partial>(?K \<omega>))
          + (\<integral>\<omega>'. (2 * ?A \<omega>) * ?xi \<omega> \<omega>' + (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
      unfolding exl
      by (rule Bochner_Integration.integral_add[OF iconst ib])
    have Eval: "(\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
        \<le> (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2"
    proof -
      have "(\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))
          = (?A \<omega>)\<^sup>2 + (\<integral>\<omega>'. (?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
        using split c1 c2 m0 by simp
      then show ?thesis using v1 by linarith
    qed
    have nn: "AE \<omega>' in ?K \<omega>. 0 \<le> (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2" by simp
    have "(\<integral>\<^sup>+\<omega>'. ennreal ((?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2) \<partial>(?K \<omega>))
        = ennreal (\<integral>\<omega>'. (?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2 \<partial>(?K \<omega>))"
      by (rule nn_integral_eq_integral[OF icc nn])
    also have "\<dots> \<le> ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2)"
      by (intro ennreal_leI Eval)
    finally show ?thesis .
  qed
  \<comment> \<open>the outer bound through the induction hypothesis\<close>
  have IHi: "integrable ?Q (\<lambda>\<omega>. (?A \<omega>)\<^sup>2)"
    and IHb: "(\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) \<le> real (Suc N) * xiC M L * h\<^sup>2"
    using Suc.IH by blast+
  have iQc: "integrable ?Q (\<lambda>\<omega>. (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2)"
    by (intro Bochner_Integration.integrable_add IHi PQ.integrable_const)
  have nnQ: "AE \<omega> in ?Q. 0 \<le> (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2"
    by (intro always_eventually allI add_nonneg_nonneg
        mult_nonneg_nonneg xiC_nonneg) simp_all
  have step2: "(\<integral>\<^sup>+\<omega>. ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2) \<partial>?Q)
      = ennreal ((\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) + xiC M L * h\<^sup>2)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2) \<partial>?Q)
        = ennreal (\<integral>\<omega>. (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2 \<partial>?Q)"
      by (rule nn_integral_eq_integral[OF iQc nnQ])
    also have "(\<integral>\<omega>. (?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2 \<partial>?Q)
        = (\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) + (\<integral>\<omega>. xiC M L * h\<^sup>2 \<partial>?Q)"
      by (rule Bochner_Integration.integral_add[OF IHi PQ.integrable_const])
    also have "(\<integral>\<omega>. xiC M L * h\<^sup>2 \<partial>?Q)
        = measure ?Q (space ?Q) *\<^sub>R (xiC M L * h\<^sup>2)"
      by (rule lebesgue_integral_const)
    finally show ?thesis by (simp add: PQ.prob_space)
  qed
  have main: "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
      \<partial>(eulerp SF x h (Suc N)))
      \<le> ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2)"
  proof -
    have kd: "kglue_law' r T' ?K ?Q = distr (ksemi ?Q ?MR ?K) ?Bt
        (\<lambda>p. pglue r T' (fst p) (snd p))"
      unfolding kglue_law'_def pair_law_of_def by (rule refl)
    have "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
        \<partial>(eulerp SF x h (Suc N)))
        = (\<integral>\<^sup>+p. ennreal ((euXi SF M h (Suc (Suc N))
            (pglue r T' (fst p) (snd p)))\<^sup>2) \<partial>(ksemi ?Q ?MR ?K))"
      unfolding Ee kd by (rule nn_integral_distr[OF phim Gm2e'])
    also have "\<dots> = (\<integral>\<^sup>+p. ennreal ((?A (fst p)
        + ?xi (fst p) (snd p))\<^sup>2) \<partial>(ksemi ?Q ?MR ?K))"
      by (rule nn_integral_cong) (simp only: Fsplit)
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal ((?A (fst (\<omega>, \<omega>'))
        + ?xi (fst (\<omega>, \<omega>')) (snd (\<omega>, \<omega>')))\<^sup>2) \<partial>(?K \<omega>)) \<partial>?Q)"
      by (rule nn_integral_ksemi[OF Kp Fme])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal ((?A \<omega> + ?xi \<omega> \<omega>')\<^sup>2)
        \<partial>(?K \<omega>)) \<partial>?Q)"
      by simp
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal ((?A \<omega>)\<^sup>2 + xiC M L * h\<^sup>2) \<partial>?Q)"
      by (rule nn_integral_mono) (rule inner)
    also have "\<dots> = ennreal ((\<integral>\<omega>. (?A \<omega>)\<^sup>2 \<partial>?Q) + xiC M L * h\<^sup>2)"
      by (rule step2)
    also have "\<dots> \<le> ennreal (real (Suc N) * xiC M L * h\<^sup>2
        + xiC M L * h\<^sup>2)"
      by (intro ennreal_leI add_right_mono IHb)
    also have "\<dots> = ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have setsE: "sets (eulerp SF x h (Suc N)) = sets ?Bt"
    unfolding Ee by simp
  have Gme: "(\<lambda>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
      \<in> borel_measurable (eulerp SF x h (Suc N))"
    using Gmsq measurable_cong_sets[OF setsE refl] by blast
  have nnG: "AE \<omega> in eulerp SF x h (Suc N).
      0 \<le> (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2" by simp
  have intS: "integrable (eulerp SF x h (Suc N))
      (\<lambda>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)"
  proof (rule integrableI_nonneg[OF Gme nnG])
    have "ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2) < \<infinity>" by simp
    with main show "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
        \<partial>(eulerp SF x h (Suc N))) < \<infinity>"
      by (rule le_less_trans)
  qed
  have c0: "0 \<le> real (Suc (Suc N)) * xiC M L * h\<^sup>2"
    by (intro mult_nonneg_nonneg xiC_nonneg) simp_all
  have bndS: "(\<integral>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2
      \<partial>(eulerp SF x h (Suc N)))
      \<le> real (Suc (Suc N)) * xiC M L * h\<^sup>2"
  proof -
    have "ennreal (\<integral>\<omega>. (euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2
        \<partial>(eulerp SF x h (Suc N)))
        = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h (Suc (Suc N)) \<omega>)\<^sup>2)
          \<partial>(eulerp SF x h (Suc N)))"
      by (rule nn_integral_eq_integral[OF intS nnG, symmetric])
    also have "\<dots> \<le> ennreal (real (Suc (Suc N)) * xiC M L * h\<^sup>2)"
      by (rule main)
    finally show ?thesis using c0 by (simp add: ennreal_le_iff)
  qed
  show ?case using intS bndS by blast
qed

subsection \<open>The increments are almost surely orthogonal to a killed field\<close>

lemma transpose_kill:
  fixes S :: "real^'n::finite^'n" and w :: "real^'n"
  assumes z: "(S ** transpose S) *v w = 0"
  shows "transpose S *v w = 0"
proof -
  have "(norm (transpose S *v w))\<^sup>2
      = (transpose S *v w) \<bullet> (transpose S *v w)"
    by (simp add: power2_norm_eq_inner)
  also have "\<dots> = w \<bullet> (S *v (transpose S *v w))"
    by (simp add: inner_transpose_matrix)
  also have "S *v (transpose S *v w) = (S ** transpose S) *v w"
    by (metis matrix_vector_mul_assoc)
  also have "w \<bullet> ((S ** transpose S) *v w) = 0" by (simp add: z)
  finally have "(norm (transpose S *v w))\<^sup>2 = 0" by simp
  then show ?thesis by simp
qed

lemma sbm_orth_increment:
  fixes S :: "real^'n::finite^'n" and w :: "real^'n"
  assumes h0: "0 \<le> h" and orth: "transpose S *v w = 0"
  shows "AE \<omega>' in pair_law_of h (sbmpair S h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "borel_of (mtopology_of (path_metric h :: ('n pairpath) metric))"
  have phim: "sbmpair S h \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule sbmpair_measurable[OF h0])
  have evh: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' h) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have ev0: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' 0) \<in> ?B \<rightarrow>\<^sub>M borel"
    by (rule pair_law_eval_measurable[OF refl])
  have pairm: "(\<lambda>\<omega>' :: 'n pairpath. (\<omega>' h, \<omega>' 0)) \<in> ?B \<rightarrow>\<^sub>M borel"
    using evh ev0 by (simp add: borel_prod[symmetric])
  have contf: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
      w \<bullet> (fst (fst ab) - fst (snd ab))) \<in> borel_measurable borel"
  proof (intro borel_measurable_continuous_onI)
    have p1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab))"
      by (intro continuous_on_fst continuous_on_id)
    have p2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab))"
      by (intro continuous_on_fst continuous_on_snd continuous_on_id)
    show "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
        \<times> ((real^'n) \<times> (real^'n^'n)).
        w \<bullet> (fst (fst ab) - fst (snd ab)))"
      by (intro continuous_intros p1 p2)
  qed
  have fm: "(\<lambda>\<omega>' :: 'n pairpath. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)))
      \<in> borel_measurable ?B"
    using measurable_compose[OF pairm contf] by simp
  have mset: "{\<omega>' \<in> space ?B. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0}
      \<in> sets ?B"
  proof -
    have "{\<omega>' \<in> space ?B. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0}
        = (\<lambda>\<omega>' :: 'n pairpath. w \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)))
          -` {0} \<inter> space ?B"
      by auto
    then show ?thesis using measurable_sets[OF fm] by simp
  qed
  have ptw: "w \<bullet> (fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0)) = 0"
    for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
  proof -
    have hI: "h \<in> {0..h}" and zI: "(0::real) \<in> {0..h}"
      using h0 by simp_all
    have "fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0)
        = S *v (cbmX (0::real^'n) h \<omega> - cbmX (0::real^'n) 0 \<omega>)"
      by (simp add: sbmpair_apply[OF hI] sbmpair_apply[OF zI]
          matrix_vector_mult_diff_distrib)
    then have "w \<bullet> (fst (sbmpair S h \<omega> h) - fst (sbmpair S h \<omega> 0))
        = (transpose S *v w)
          \<bullet> (cbmX (0::real^'n) h \<omega> - cbmX (0::real^'n) 0 \<omega>)"
      by (simp add: inner_transpose_matrix)
    then show ?thesis using orth by simp
  qed
  show ?thesis
    unfolding pair_law_of_def
    by (subst AE_distr_iff[OF phim mset]) (simp add: ptw)
qed

lemma euOrth_mset:
  fixes G :: "real^'n::finite \<Rightarrow> real^'n" and h :: real
  assumes Gc: "continuous_on UNIV G"
  shows "{\<omega> \<in> space (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))).
      \<forall>j<m. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
    \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have per: "{\<omega> \<in> space ?B. G (fst (\<omega> (real j * h))) \<bullet>
      (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets ?B" for j
  proof -
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real (Suc j) * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have evv: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real j * h)) \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule pair_law_eval_measurable[OF refl])
    have pairm: "(\<lambda>\<omega> :: 'n pairpath.
        (\<omega> (real (Suc j) * h), \<omega> (real j * h))) \<in> ?B \<rightarrow>\<^sub>M borel"
      using evu evv by (simp add: borel_prod[symmetric])
    have contf: "(\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
        G (fst (snd ab)) \<bullet> (fst (fst ab) - fst (snd ab)))
        \<in> borel_measurable borel"
    proof (intro borel_measurable_continuous_onI)
      have p1: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)). fst (fst ab))"
        by (intro continuous_on_fst continuous_on_id)
      have p2: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)). fst (snd ab))"
        by (intro continuous_on_fst continuous_on_snd continuous_on_id)
      have Gcomp: "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)). G (fst (snd ab)))"
        by (rule continuous_on_compose2[OF Gc p2]) auto
      show "continuous_on UNIV (\<lambda>ab :: ((real^'n) \<times> (real^'n^'n))
          \<times> ((real^'n) \<times> (real^'n^'n)).
          G (fst (snd ab)) \<bullet> (fst (fst ab) - fst (snd ab)))"
        by (intro continuous_intros Gcomp p1 p2)
    qed
    have fm: "(\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
        \<in> borel_measurable ?B"
      using measurable_compose[OF pairm contf] by simp
    have "{\<omega> \<in> space ?B. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
          -` {0} \<inter> space ?B"
      by auto
    then show ?thesis using measurable_sets[OF fm] by simp
  qed
  show ?thesis
  proof (induction m)
    case 0
    show ?case by simp
  next
    case (Suc m)
    have eq: "{\<omega> \<in> space ?B. \<forall>j<Suc m. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = {\<omega> \<in> space ?B. \<forall>j<m. G (fst (\<omega> (real j * h))) \<bullet>
            (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          \<inter> {\<omega> \<in> space ?B. G (fst (\<omega> (real m * h))) \<bullet>
            (fst (\<omega> (real (Suc m) * h)) - fst (\<omega> (real m * h))) = 0}"
      by (auto simp: less_Suc_eq)
    show ?case unfolding eq by (intro sets.Int Suc.IH per)
  qed
qed

theorem eulerp_orth_increments:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and G :: "real^'n \<Rightarrow> real^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and Gc: "continuous_on UNIV G"
    and kill: "\<And>z. transpose (SF z) *v G z = 0"
  shows "AE \<omega> in eulerp SF x h N. \<forall>j<Suc N.
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
proof (induction N)
  case 0
  have h0': "(0::real) \<le> h" using h0 by simp
  let ?\<mu>0 = "pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  have E0: "eulerp SF x h 0 = pshift_law h x ?\<mu>0" by simp
  have sets\<mu>: "sets ?\<mu>0 = sets (borel_of (mtopology_of
      (path_metric h :: ('n pairpath) metric)))" by simp
  have st: "AE \<omega> in ?\<mu>0. fst (\<omega> 0) = (0 :: real^'n)"
    using sbmpair_law_start[OF h0', of "SF x"]
    by (rule eventually_mono) simp
  have orth0: "AE \<omega> in ?\<mu>0. G x \<bullet> (fst (\<omega> h) - fst (\<omega> 0)) = 0"
    by (rule sbm_orth_increment[OF h0' kill])
  have ae: "AE \<omega> in ?\<mu>0. \<forall>j<Suc 0.
      G (fst (pshift h x \<omega> (real j * h))) \<bullet>
        (fst (pshift h x \<omega> (real (Suc j) * h))
          - fst (pshift h x \<omega> (real j * h))) = 0"
    using st orth0
  proof eventually_elim
    case (elim \<omega>)
    have m1: "h \<in> {0..h}" and m2: "(0::real) \<in> {0..h}"
      using h0' by simp_all
    show ?case using elim
      by (simp add: pshift_fst[OF m1] pshift_fst[OF m2])
  qed
  show ?case unfolding E0 by (rule AE_pshift_law[OF h0' sets\<mu> ae])
next
  case (Suc N)
  have h0': "(0::real) \<le> h" using h0 by simp
  define r where "r = real (Suc N) * h"
  define T' where "T' = real (Suc (Suc N)) * h"
  let ?Q = "eulerp SF x h N"
  let ?Br = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?MR = "borel_of (mtopology_of
      (path_metric (T' - r) :: ('n pairpath) metric))"
  let ?K = "\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
  have r0: "0 \<le> r" unfolding r_def using h0' by simp
  have rleT: "r \<le> T'" unfolding r_def T'_def
    using h0' by (intro mult_right_mono) simp_all
  have Qc: "?Q \<in> paper_pair_class k L r x"
    unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  have PQ: "prob_space ?Q" by (rule paper_pair_class_prob[OF Qc])
  have setsQ: "sets ?Q = sets ?Br" by (rule paper_pair_class_sets[OF Qc])
  have ne: "space ?Q \<noteq> {}" using PQ by (rule prob_space.not_empty)
  note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
    by (simp add: r_def T'_def)
  have msetP: "{\<omega> \<in> mspace (path_metric T' :: ('n pairpath) metric).
      \<forall>j<Suc (Suc N). G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets (borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric)))"
  proof -
    have spB: "space (borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric)))
        = mspace (path_metric T' :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF refl])
    show ?thesis
      using euOrth_mset[OF Gc, where h = h and T = T' and m = "Suc (Suc N)"]
      unfolding spB .
  qed
  show ?case
    unfolding Ee
  proof (rule Paper_Bridge.AE_kglue_law'[OF r0 rleT PQ setsQ Kp msetP])
    show "AE \<omega> in ?Q. \<forall>j<Suc N. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
      by (rule Suc.IH)
    show "AE \<omega>' in ?K \<omega>. G (fst (\<omega> r)) \<bullet>
        (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
      if "\<omega> \<in> space ?Q" for \<omega> :: "'n pairpath"
      by (rule sbm_orth_increment[OF h0' kill])
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T' - r) :: ('n pairpath) metric)"
      and A: "\<forall>j<Suc N. G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
      and B: "G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
    have mem: "real j * h \<in> {0..T'}" if le: "j \<le> Suc (Suc N)" for j
    proof -
      have a: "0 \<le> real j * h"
        by (intro mult_nonneg_nonneg h0') simp_all
      have b: "real j * h \<le> T'" unfolding T'_def
        using le h0' by (intro mult_right_mono) simp_all
      show ?thesis using a b by simp
    qed
    have prefl: "pglue r T' \<omega> \<omega>' (real j * h) = \<omega> (real j * h)"
      if j: "j \<le> Suc N" for j
    proof (rule pglue_le)
      show "real j * h \<in> {0..T'}" using j by (intro mem) simp
      show "real j * h \<le> r" unfolding r_def
        using j h0' by (intro mult_right_mono) simp_all
    qed
    have Tmem: "T' \<in> {0..T'}"
      using mem[of "Suc (Suc N)"] unfolding T'_def by simp
    have gT: "pglue r T' \<omega> \<omega>' T' = \<omega> r + (\<omega>' (T' - r) - \<omega>' 0)"
      by (rule pglue_ge[OF Tmem rleT])
    have gr: "pglue r T' \<omega> \<omega>' r = \<omega> r"
      using prefl[of "Suc N"] unfolding r_def by simp
    have head: "fst (pglue r T' \<omega> \<omega>' T') - fst (pglue r T' \<omega> \<omega>' r)
        = fst (\<omega>' h) - fst (\<omega>' 0)"
      unfolding gT gr hT by simp
    show "\<forall>j<Suc (Suc N). G (fst (pglue r T' \<omega> \<omega>' (real j * h))) \<bullet>
        (fst (pglue r T' \<omega> \<omega>' (real (Suc j) * h))
          - fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
    proof (intro allI impI)
      fix j assume jle: "j < Suc (Suc N)"
      show "G (fst (pglue r T' \<omega> \<omega>' (real j * h))) \<bullet>
          (fst (pglue r T' \<omega> \<omega>' (real (Suc j) * h))
            - fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
      proof (cases "j < Suc N")
        case True
        then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" by simp_all
        show ?thesis
          using A True by (simp only: prefl[OF j1] prefl[OF j2])
      next
        case False
        with jle have jeq: "j = Suc N" by simp
        have e1: "real (Suc j) * h = T'" unfolding jeq T'_def by (rule refl)
        have e2: "real j * h = r" unfolding jeq r_def by (rule refl)
        show ?thesis unfolding e1 e2 gT gr hT using B by simp
      qed
    qed
  qed
qed

subsection \<open>Partial grid sums: peel, moment bound, Chebyshev\<close>

lemma euXi_pglue_prefix:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and \<omega> \<omega>' :: "'n pairpath" and h :: real
  assumes h0: "0 \<le> h" and m: "m \<le> Suc N"
  shows "euXi SF M h m (pglue (real (Suc N) * h)
      (real (Suc (Suc N)) * h) \<omega> \<omega>') = euXi SF M h m \<omega>"
proof -
  let ?r = "real (Suc N) * h"
  let ?T = "real (Suc (Suc N)) * h"
  have prefl: "pglue ?r ?T \<omega> \<omega>' (real j * h) = \<omega> (real j * h)"
    if j: "j \<le> Suc N" for j
  proof (rule pglue_le)
    have a: "0 \<le> real j * h"
      by (intro mult_nonneg_nonneg h0) simp_all
    have b: "real j * h \<le> ?T"
      using j h0 by (intro mult_right_mono) simp_all
    show "real j * h \<in> {0..?T}" using a b by simp
    show "real j * h \<le> ?r" using j h0 by (intro mult_right_mono) simp_all
  qed
  show ?thesis unfolding euXi_def
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {..<m}"
    then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" using m by auto
    show "trace (M ** (outerp
        (fst (pglue ?r ?T \<omega> \<omega>' (real (Suc j) * h))
          - fst (pglue ?r ?T \<omega> \<omega>' (real j * h)))
        - h *\<^sub>R (SF (fst (pglue ?r ?T \<omega> \<omega>' (real j * h)))
            ** transpose (SF (fst (pglue ?r ?T \<omega> \<omega>' (real j * h)))))))
      = trace (M ** (outerp
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        - h *\<^sub>R (SF (fst (\<omega> (real j * h)))
            ** transpose (SF (fst (\<omega> (real j * h)))))))"
      by (simp only: prefl[OF j1] prefl[OF j2])
  qed
qed

theorem eulerp_Xi_sq_bound_le:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and m: "m \<le> Suc N"
  shows "integrable (eulerp SF x h N) (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)
      \<and> (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>(eulerp SF x h N))
        \<le> real m * xiC M L * h\<^sup>2"
  using m
proof (induction N)
  case 0
  then consider (z) "m = 0" | (o) "m = Suc 0" by linarith
  then show ?case
  proof cases
    case z
    have e: "(\<lambda>\<omega> :: 'n pairpath. (euXi SF M h m \<omega>)\<^sup>2) = (\<lambda>\<omega>. 0)"
      by (rule ext) (simp add: z euXi_def)
    show ?thesis unfolding e by (simp add: z)
  next
    case o
    show ?thesis unfolding o
      by (rule eulerp_Xi_sq_bound[OF h0 L1 SFc SFs])
  qed
next
  case (Suc N)
  show ?case
  proof (cases "m = Suc (Suc N)")
    case True
    show ?thesis unfolding True
      by (rule eulerp_Xi_sq_bound[OF h0 L1 SFc SFs])
  next
    case False
    with Suc.prems have mle: "m \<le> Suc N" by simp
    have IHi: "integrable (eulerp SF x h N) (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)"
      and IHb: "(\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>(eulerp SF x h N))
        \<le> real m * xiC M L * h\<^sup>2"
      using Suc.IH[OF mle] by blast+
    have h0': "(0::real) \<le> h" using h0 by simp
    define r where "r = real (Suc N) * h"
    define T' where "T' = real (Suc (Suc N)) * h"
    let ?Q = "eulerp SF x h N"
    let ?Br = "borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric))"
    let ?Bt = "borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric))"
    let ?MR = "borel_of (mtopology_of
        (path_metric (T' - r) :: ('n pairpath) metric))"
    let ?K = "\<lambda>\<omega> :: 'n pairpath.
        pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
    have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
    have r0: "0 \<le> r" unfolding r_def using h0' by simp
    have rleT: "r \<le> T'" unfolding r_def T'_def
      using h0' by (intro mult_right_mono) simp_all
    have Qc: "?Q \<in> paper_pair_class k L r x"
      unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
    interpret PQ: prob_space ?Q by (rule paper_pair_class_prob[OF Qc])
    have setsQ: "sets ?Q = sets ?Br" by (rule paper_pair_class_sets[OF Qc])
    have ne: "space ?Q \<noteq> {}" by (rule PQ.not_empty)
    note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
    have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      using measurable_fst[of "borel :: (real^'n) measure"
          "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
    have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
      by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
    have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
      unfolding hT by (rule measurable_compose[OF eQ pack(1)])
    have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
      by (simp add: r_def T'_def)
    have phim: "(\<lambda>p. pglue r T' (fst p) (snd p))
        \<in> ksemi ?Q ?MR ?K \<rightarrow>\<^sub>M ?Bt"
      by (rule kglue_law'_measurable[OF r0 rleT setsQ Kp ne])
    have Gmsq: "(\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2) \<in> borel_measurable ?Bt"
      by (intro borel_measurable_power euXi_measurable[OF SFc])
    have Gm2e: "(\<lambda>\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2))
        \<in> borel_measurable ?Bt"
      using Gmsq by measurable
    have Gm2e': "(\<lambda>\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2))
        \<in> borel_measurable (distr (ksemi ?Q ?MR ?K) ?Bt
          (\<lambda>p. pglue r T' (fst p) (snd p)))"
      using Gm2e measurable_cong_sets[OF sets_distr refl] by blast
    have euQ: "euXi SF M h m \<in> borel_measurable ?Q"
      using euXi_measurable[OF SFc]
        measurable_cong_sets[OF setsQ refl] by blast
    have Fme: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
          ennreal ((euXi SF M h m (fst p))\<^sup>2))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?MR)"
      using measurable_compose[OF measurable_fst euQ] by measurable
    have Fsplit: "(euXi SF M h m (pglue r T' (fst p) (snd p)))\<^sup>2
        = (euXi SF M h m (fst p))\<^sup>2"
      for p :: "'n pairpath \<times> 'n pairpath"
      unfolding r_def T'_def
      by (simp only: euXi_pglue_prefix[OF h0' mle])
    have kd: "kglue_law' r T' ?K ?Q = distr (ksemi ?Q ?MR ?K) ?Bt
        (\<lambda>p. pglue r T' (fst p) (snd p))"
      unfolding kglue_law'_def pair_law_of_def by (rule refl)
    have KP1: "emeasure (pair_law_of h (sbmpair (SF (fst (\<omega> r))) h)
        bm_paths) (space (pair_law_of h (sbmpair (SF (fst (\<omega> r))) h)
          bm_paths)) = 1" for \<omega> :: "'n pairpath"
      by (rule prob_space.emeasure_space_1[OF prob_space_sbmpair_law[OF h0']])
    have nnA: "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
        \<partial>(eulerp SF x h (Suc N)))
        = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2) \<partial>?Q)"
    proof -
      have "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
          \<partial>(eulerp SF x h (Suc N)))
          = (\<integral>\<^sup>+p. ennreal ((euXi SF M h m
              (pglue r T' (fst p) (snd p)))\<^sup>2) \<partial>(ksemi ?Q ?MR ?K))"
        unfolding Ee kd by (rule nn_integral_distr[OF phim Gm2e'])
      also have "\<dots> = (\<integral>\<^sup>+p. ennreal ((euXi SF M h m (fst p))\<^sup>2)
          \<partial>(ksemi ?Q ?MR ?K))"
        by (rule nn_integral_cong) (simp only: Fsplit)
      also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal
          ((euXi SF M h m (fst (\<omega>, \<omega>')))\<^sup>2) \<partial>(?K \<omega>)) \<partial>?Q)"
        by (rule nn_integral_ksemi[OF Kp Fme])
      also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2) \<partial>?Q)"
        by (simp add: KP1)
      finally show ?thesis .
    qed
    have nnQfin: "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2) \<partial>?Q)
        = ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?Q)"
      by (rule nn_integral_eq_integral[OF IHi]) simp
    have setsE: "sets (eulerp SF x h (Suc N)) = sets ?Bt"
      unfolding Ee by simp
    have Gme: "(\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)
        \<in> borel_measurable (eulerp SF x h (Suc N))"
      using Gmsq measurable_cong_sets[OF setsE refl] by blast
    have nnG: "AE \<omega> in eulerp SF x h (Suc N).
        0 \<le> (euXi SF M h m \<omega>)\<^sup>2" by simp
    have intS: "integrable (eulerp SF x h (Suc N))
        (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)"
    proof (rule integrableI_nonneg[OF Gme nnG])
      have "ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?Q) < \<infinity>" by simp
      then show "(\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
          \<partial>(eulerp SF x h (Suc N))) < \<infinity>"
        unfolding nnA nnQfin .
    qed
    have c0: "0 \<le> real m * xiC M L * h\<^sup>2"
      by (intro mult_nonneg_nonneg xiC_nonneg) simp_all
    have bndS: "(\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>(eulerp SF x h (Suc N)))
        \<le> real m * xiC M L * h\<^sup>2"
    proof -
      have "ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2
          \<partial>(eulerp SF x h (Suc N)))
          = (\<integral>\<^sup>+\<omega>. ennreal ((euXi SF M h m \<omega>)\<^sup>2)
            \<partial>(eulerp SF x h (Suc N)))"
        by (rule nn_integral_eq_integral[OF intS nnG, symmetric])
      also have "\<dots> = ennreal (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?Q)"
        unfolding nnA nnQfin by (rule refl)
      also have "\<dots> \<le> ennreal (real m * xiC M L * h\<^sup>2)"
        by (intro ennreal_leI IHb)
      finally show ?thesis using c0 by (simp add: ennreal_le_iff)
    qed
    show ?thesis using intS bndS by blast
  qed
qed

corollary eulerp_Xi_chebyshev:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and x :: "real^'n" and h \<beta> :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and m: "m \<le> Suc N" and b: "0 < \<beta>"
  shows "measure (eulerp SF x h N) {\<omega> \<in> space (eulerp SF x h N).
      \<beta> \<le> \<bar>euXi SF M h m \<omega>\<bar>}
    \<le> real m * xiC M L * h\<^sup>2 / \<beta>\<^sup>2"
proof -
  let ?P = "eulerp SF x h N"
  have int: "integrable ?P (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)"
    and bnd: "(\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?P)
      \<le> real m * xiC M L * h\<^sup>2"
    using eulerp_Xi_sq_bound_le[OF h0 L1 SFc SFs m] by blast+
  have seteq: "{\<omega> \<in> space ?P. \<beta>\<^sup>2 \<le> (euXi SF M h m \<omega>)\<^sup>2}
      = {\<omega> \<in> space ?P. \<beta> \<le> \<bar>euXi SF M h m \<omega>\<bar>}"
  proof -
    have iff: "\<beta>\<^sup>2 \<le> y\<^sup>2 \<longleftrightarrow> \<beta> \<le> \<bar>y\<bar>" for y :: real
    proof
      assume "\<beta>\<^sup>2 \<le> y\<^sup>2"
      then have "\<beta>\<^sup>2 \<le> \<bar>y\<bar>\<^sup>2" by simp
      then show "\<beta> \<le> \<bar>y\<bar>" by (rule power2_le_imp_le) simp
    next
      assume a: "\<beta> \<le> \<bar>y\<bar>"
      have "\<beta>\<^sup>2 \<le> \<bar>y\<bar>\<^sup>2"
        using a b by (intro power_mono) simp_all
      then show "\<beta>\<^sup>2 \<le> y\<^sup>2" by simp
    qed
    show ?thesis using iff by auto
  qed
  have b2: "0 < \<beta>\<^sup>2" using b by simp
  have "measure ?P {\<omega> \<in> space ?P. \<beta>\<^sup>2 \<le> (euXi SF M h m \<omega>)\<^sup>2}
      \<le> (\<integral>\<omega>. (euXi SF M h m \<omega>)\<^sup>2 \<partial>?P) / \<beta>\<^sup>2"
  proof (rule integral_Markov_inequality_measure)
    show "integrable ?P (\<lambda>\<omega>. (euXi SF M h m \<omega>)\<^sup>2)" by (rule int)
    show "space ?P \<in> sets ?P" by (rule sets.top)
    show "AE \<omega> in ?P. 0 \<le> (euXi SF M h m \<omega>)\<^sup>2" by simp
    show "0 < \<beta>\<^sup>2" by (rule b2)
  qed
  also have "\<dots> \<le> real m * xiC M L * h\<^sup>2 / \<beta>\<^sup>2"
    using bnd b2 by (intro divide_right_mono) simp_all
  finally show ?thesis using seteq by simp
qed

subsection \<open>The exact quadratic lower bound along the grid\<close>

lemma quad_taylor_step:
  fixes M :: "real^'n::finite^'n" and q x a b :: "real^'n"
  assumes sym: "transpose M = M"
  shows "q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
       - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))
     = (q + M *v (a - x)) \<bullet> (b - a)
       + (1/2) * ((b - a) \<bullet> (M *v (b - a)))"
proof -
  define u where "u = a - x"
  define d where "d = b - a"
  have bx: "b - x = u + d" unfolding u_def d_def by simp
  have swap: "d \<bullet> (M *v u) = u \<bullet> (M *v d)"
  proof -
    have "d \<bullet> (M *v u) = (transpose M *v d) \<bullet> u"
      by (rule inner_transpose_matrix)
    also have "\<dots> = (M *v d) \<bullet> u" by (simp add: sym)
    also have "\<dots> = u \<bullet> (M *v d)" by (rule inner_commute)
    finally show ?thesis .
  qed
  have e12: "(b - x) \<bullet> (M *v (b - x))
      = u \<bullet> (M *v u) + 2 * (u \<bullet> (M *v d)) + d \<bullet> (M *v d)"
  proof -
    have "(b - x) \<bullet> (M *v (b - x)) = (u + d) \<bullet> (M *v (u + d))"
      unfolding bx by (rule refl)
    also have "\<dots> = u \<bullet> (M *v u) + u \<bullet> (M *v d)
        + (d \<bullet> (M *v u) + d \<bullet> (M *v d))"
      by (simp add: matrix_vector_right_distrib inner_add_left
          inner_add_right)
    also have "d \<bullet> (M *v u) = u \<bullet> (M *v d)" by (rule swap)
    finally show ?thesis by simp
  qed
  have e0: "q \<bullet> (b - x) = q \<bullet> u + q \<bullet> d"
    unfolding bx by (simp add: inner_add_right)
  have e3: "q \<bullet> (a - x) = q \<bullet> u" unfolding u_def by (rule refl)
  have e4: "(a - x) \<bullet> (M *v (a - x)) = u \<bullet> (M *v u)"
    unfolding u_def by (rule refl)
  have e5: "(q + M *v (a - x)) \<bullet> (b - a) = q \<bullet> d + u \<bullet> (M *v d)"
  proof -
    have "(q + M *v (a - x)) \<bullet> (b - a) = (q + M *v u) \<bullet> d"
      unfolding u_def d_def by (rule refl)
    also have "\<dots> = q \<bullet> d + (M *v u) \<bullet> d" by (simp add: inner_add_left)
    also have "(M *v u) \<bullet> d = d \<bullet> (M *v u)" by (rule inner_commute)
    also have "d \<bullet> (M *v u) = u \<bullet> (M *v d)" by (rule swap)
    finally show ?thesis .
  qed
  have e6: "(b - a) \<bullet> (M *v (b - a)) = d \<bullet> (M *v d)"
    unfolding d_def by (rule refl)
  show ?thesis using e0 e12 e3 e4 e5 e6 by linarith
qed

theorem eulerp_quad_lower:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and h rb cm :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M" and rb0: "0 \<le> rb"
    and kill: "\<And>z. transpose (SF z) *v
        (q + M *v (closest_point (cball x rb) z - x)) = 0"
    and marg: "\<And>z. cm \<le> trace (M ** (SF z ** transpose (SF z)))"
  shows "AE \<omega> in eulerp SF x h N. \<forall>m\<le>Suc N.
      (\<forall>j<m. fst (\<omega> (real j * h)) \<in> cball x rb) \<longrightarrow>
      (1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
        \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
          + (1/2) * ((fst (\<omega> (real m * h)) - x)
              \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
proof -
  have cpc: "continuous_on UNIV (closest_point (cball x rb))"
    by (rule continuous_on_closest_point)
      (use rb0 in \<open>auto simp: convex_cball closed_cball\<close>)
  have Gc: "continuous_on UNIV (\<lambda>z :: real^'n.
      q + M *v (closest_point (cball x rb) z - x))"
  proof -
    have d: "continuous_on UNIV (\<lambda>z :: real^'n.
        closest_point (cball x rb) z - x)"
      by (intro continuous_intros cpc)
    have mv: "continuous_on UNIV (\<lambda>z :: real^'n.
        M *v (closest_point (cball x rb) z - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  note orth = eulerp_orth_increments[OF h0 L1 SFc SFs Gc kill]
  have Qc: "eulerp SF x h N \<in> paper_pair_class k L (real (Suc N) * h) x"
    by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  have st: "AE \<omega> in eulerp SF x h N. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Qc unfolding paper_pair_class_def by blast
  show ?thesis
    using orth st
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix m assume mle: "m \<le> Suc N"
        and inb: "\<forall>j<m. fst (\<omega> (real j * h)) \<in> cball x rb"
      define X where "X j = fst (\<omega> (real j * h))" for j
      define \<psi> where "\<psi> z = q \<bullet> (z - x)
          + (1/2) * ((z - x) \<bullet> (M *v (z - x)))" for z
      have x0: "X 0 = x" unfolding X_def using elim by simp
      have step: "\<psi> (X (Suc j)) - \<psi> (X j)
          = (1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))"
        if j: "j < m" for j
      proof -
        have cps: "closest_point (cball x rb) (X j) = X j"
          using inb j unfolding X_def by (intro closest_point_self) auto
        have jN: "j < Suc N" using j mle by simp
        have k0: "(q + M *v (X j - x)) \<bullet> (X (Suc j) - X j) = 0"
          using elim(1) jN cps unfolding X_def by metis
        have "\<psi> (X (Suc j)) - \<psi> (X j)
            = (q + M *v (X j - x)) \<bullet> (X (Suc j) - X j)
              + (1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))"
          unfolding \<psi>_def by (rule quad_taylor_step[OF sym])
        then show ?thesis using k0 by simp
      qed
      have tele: "\<psi> (X m) - \<psi> (X 0)
          = (\<Sum>j<m. \<psi> (X (Suc j)) - \<psi> (X j))"
        by (rule sum_lessThan_telescope[symmetric])
      have quadsum: "\<psi> (X m) - \<psi> (X 0)
          = (\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
              \<bullet> (M *v (X (Suc j) - X j))))"
        unfolding tele
        by (rule sum.cong[OF refl]) (use step in simp)
      have perj: "(1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))
          = (1/2) * (trace (M ** (outerp (X (Suc j) - X j)
              - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            + h * trace (M ** (SF (X j) ** transpose (SF (X j)))))" for j
      proof -
        have "trace (M ** (outerp (X (Suc j) - X j)
            - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            = trace (M ** outerp (X (Suc j) - X j))
              - h * trace (M ** (SF (X j) ** transpose (SF (X j))))"
          by (simp add: trace_mult_diff matmul_scaleR_right trace_scaleR)
        then show ?thesis by (simp add: trace_mult_outerp)
      qed
      have persum: "(\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
            \<bullet> (M *v (X (Suc j) - X j))))
          = (1/2) * euXi SF M h m \<omega>
            + (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
      proof -
        have "(\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
              \<bullet> (M *v (X (Suc j) - X j))))
            = (\<Sum>j<m. (1/2) * (trace (M ** (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
              + h * trace (M ** (SF (X j) ** transpose (SF (X j))))))"
          by (rule sum.cong[OF refl]) (rule perj)
        also have "\<dots> = (\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            + (h/2) * trace (M ** (SF (X j) ** transpose (SF (X j)))))"
          by (rule sum.cong[OF refl]) (simp add: field_simps)
        also have "\<dots> = (\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            + (\<Sum>j<m. (h/2) * trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
          by (rule sum.distrib)
        also have "(\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            = (1/2) * (\<Sum>j<m. trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))"
          by (rule sum_distrib_left[symmetric])
        also have "(\<Sum>j<m. (h/2) * trace (M ** (SF (X j)
              ** transpose (SF (X j)))))
            = (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
          by (rule sum_distrib_left[symmetric])
        also have "(\<Sum>j<m. trace (M ** (outerp (X (Suc j) - X j)
              - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            = euXi SF M h m \<omega>"
          unfolding euXi_def X_def by (rule refl)
        finally show ?thesis .
      qed
      have margsum: "real m * cm
          \<le> (\<Sum>j<m. trace (M ** (SF (X j) ** transpose (SF (X j)))))"
      proof -
        have "real m * cm = (\<Sum>j\<in>{..<m}. cm)" by simp
        also have "\<dots> \<le> (\<Sum>j<m. trace (M ** (SF (X j)
            ** transpose (SF (X j)))))"
          by (rule sum_mono) (rule marg)
        finally show ?thesis .
      qed
      have psi0: "\<psi> (X 0) = 0" unfolding \<psi>_def x0 by simp
      have hm: "(h/2) * (real m * cm)
          \<le> (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
              ** transpose (SF (X j)))))"
        using h0 margsum by (intro mult_left_mono) simp_all
      have ee: "real m * h * cm / 2 = (h/2) * (real m * cm)" by simp
      have main: "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
          \<le> \<psi> (X m)"
        using quadsum persum psi0 hm ee by linarith
      show "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
          \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
            + (1/2) * ((fst (\<omega> (real m * h)) - x)
                \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
        using main unfolding \<psi>_def X_def .
    qed
  qed
qed

subsection \<open>The weak limit of the Euler laws\<close>

text \<open>Batch 3d of the supersolution plan.  The Euler laws at mesh
  \<open>c / (i + 1)\<close> all live in the compact class
  \<open>paper_pair_class k L c x\<close> (@{thm [source]
  paper_pair_class_compact_metric_space}), so some subsequence converges
  weakly to a class member \<open>P\<close>.  The transfer principle we record is the
  portmanteau bound against limits along the FULL sequence: if the
  measures of an open set converge to \<open>b\<close>, the limit member gives the set
  at most \<open>b\<close> (and dually for closed sets).  Batch 3e will apply the open
  half to the "stayed in the ball but the quadratic dropped" event, whose
  probability vanishes with the mesh by
  @{thm [source] eulerp_Xi_chebyshev} and @{thm [source]
  eulerp_quad_lower}.

  The topological brick first: staying strictly inside an open set
  through time \<open>t\<close> is an OPEN condition on the path.  The image of
  \<open>{0..t}\<close> is compact, so it sits at a positive distance from the
  complement (@{thm [source] separate_compact_closed}), and any path
  uniformly closer than that distance stays inside as well
  (@{thm [source] path_mdist_le_iff_all}).\<close>

lemma open_stay_inside:
  fixes T t :: real and A :: "'b::{polish_space, heine_borel} set"
  assumes T0: "0 \<le> T" and A: "open A" and t0: "0 \<le> t" and tT: "t \<le> T"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
        \<forall>s\<in>{0..t}. f s \<in> A}"
proof -
  interpret PM: Metric_space
      "mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      "mdist (path_metric T :: (real \<Rightarrow> 'b) metric)"
    by (rule Metric_space_mspace_mdist)
  have topeq: "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)
      = PM.mtopology"
    by (simp add: mtopology_of_def)
  let ?S = "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      \<forall>s\<in>{0..t}. f s \<in> A}"
  have ball: "\<exists>e>0. PM.mball f e \<subseteq> ?S" if f: "f \<in> ?S" for f
  proof -
    have fm: "f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using f by auto
    have fc: "continuous_on {0..T} f"
      by (rule mspace_path_metricD[OF fm])
    have fc': "continuous_on {0..t} f"
      using fc by (rule continuous_on_subset) (use t0 tT in auto)
    have cK: "compact (f ` {0..t})"
      by (intro compact_continuous_image fc' compact_Icc)
    have KA: "f ` {0..t} \<subseteq> A" using f by auto
    have dis: "f ` {0..t} \<inter> (- A) = {}" using KA by auto
    have clA: "closed (- A)" using A by (simp add: closed_Compl)
    obtain e where e0: "0 < e"
      and esep: "\<forall>y\<in>f ` {0..t}. \<forall>z\<in>- A. e \<le> dist y z"
      using separate_compact_closed[OF cK clA dis] by blast
    have sub: "PM.mball f e \<subseteq> ?S"
    proof
      fix g assume g: "g \<in> PM.mball f e"
      have gm: "g \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
        and dfg: "mdist (path_metric T :: (real \<Rightarrow> 'b) metric) f g < e"
        using g by auto
      have all: "\<forall>u\<in>{0..T}. dist (f u) (g u)
          \<le> mdist (path_metric T :: (real \<Rightarrow> 'b) metric) f g"
        using path_mdist_le_iff_all[OF T0 fm gm,
            of "mdist (path_metric T :: (real \<Rightarrow> 'b) metric) f g"]
        by simp
      have inA: "g s \<in> A" if s: "s \<in> {0..t}" for s
      proof (rule ccontr)
        assume "g s \<notin> A"
        then have "g s \<in> - A" by simp
        then have "e \<le> dist (f s) (g s)"
          using esep s by blast
        moreover have "dist (f s) (g s)
            \<le> mdist (path_metric T :: (real \<Rightarrow> 'b) metric) f g"
          using all s t0 tT by auto
        ultimately show False using dfg by linarith
      qed
      show "g \<in> ?S" using gm inA by auto
    qed
    show ?thesis using e0 sub by blast
  qed
  have "openin PM.mtopology ?S"
    unfolding PM.openin_mtopology
  proof (intro conjI allI impI)
    show "?S \<subseteq> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" by auto
    fix f assume "f \<in> ?S"
    then show "\<exists>e>0. PM.mball f e \<subseteq> ?S" by (rule ball)
  qed
  then show ?thesis by (simp add: topeq)
qed

text \<open>The transfer principle.  Sequential compactness of the class
  extracts a convergent subsequence; membership clause (2) of
  @{thm [source] paper_pair_class_compact_metric_space} identifies the
  limit as weak convergence, and the AFP portmanteau
  (@{thm [source] mweak_conv_fin.mweak_conv_eq2},
  @{thm [source] mweak_conv_fin.mweak_conv_eq3}) turns it into the
  open/closed set bounds.  Convergence along the full sequence pins the
  Liminf and Limsup along any subsequence, so the subsequence never
  appears in the statement.\<close>

theorem paper_pair_class_weak_limit:
  fixes Pseq :: "nat \<Rightarrow> ('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L0: "0 \<le> L"
    and mem: "\<And>i. Pseq i \<in> paper_pair_class k L T x"
  shows "\<exists>P \<in> paper_pair_class k L T x.
      (\<forall>U b. openin (mtopology_of
            (path_metric T :: ('n pairpath) metric)) U
          \<longrightarrow> (\<lambda>i. measure (Pseq i) U) \<longlonglongrightarrow> b
          \<longrightarrow> measure P U \<le> b)
      \<and> (\<forall>D b. closedin (mtopology_of
            (path_metric T :: ('n pairpath) metric)) D
          \<longrightarrow> (\<lambda>i. measure (Pseq i) D) \<longlonglongrightarrow> b
          \<longrightarrow> b \<le> measure P D)"
proof -
  let ?pm = "path_metric T :: ('n pairpath) metric"
  let ?C = "paper_pair_class k L T x"
  let ?E = "Levy_Prokhorov.LPm (mspace ?pm) (mdist ?pm)"
  interpret CM: Metric_space ?C ?E
    by (rule paper_pair_class_compact_metric_space(1)[OF T L0])
  have cs: "compact_space CM.mtopology"
    by (rule paper_pair_class_compact_metric_space(3)[OF T L0])
  have rng: "range Pseq \<subseteq> ?C" using mem by auto
  obtain P r where P: "P \<in> ?C" and r: "strict_mono r"
    and liml: "limitin CM.mtopology (Pseq \<circ> r) P sequentially"
    using cs[unfolded CM.compact_space_sequentially] rng by blast
  have Ctop: "CM.mtopology = subtopology
      (weak_conv_topology (mtopology_of ?pm)) ?C"
    by (rule paper_pair_class_compact_metric_space(2)[OF T L0])
  have limW: "limitin (weak_conv_topology (mtopology_of ?pm))
      (Pseq \<circ> r) P sequentially"
    using liml unfolding Ctop limitin_subtopology by blast
  have mwc: "limitin (weak_conv_topology
      (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))
      (Pseq \<circ> r) P sequentially"
    using limW by (simp add: mtopology_of_def)
  have fmi: "finite_measure (Pseq i)" for i
    using paper_pair_class_prob[OF mem, of i]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmP: "finite_measure P"
    using paper_pair_class_prob[OF P]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have setsP: "sets P = sets (borel_of
      (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))"
    using paper_pair_class_sets[OF P] by (simp add: mtopology_of_def)
  have ev1: "\<forall>\<^sub>F i in sequentially. sets ((Pseq \<circ> r) i)
      = sets (borel_of (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))"
  proof (intro always_eventually allI)
    fix i show "sets ((Pseq \<circ> r) i)
        = sets (borel_of (Metric_space.mtopology (mspace ?pm) (mdist ?pm)))"
      using paper_pair_class_sets[OF mem, of "r i"]
      by (simp add: mtopology_of_def)
  qed
  have ev2: "\<forall>\<^sub>F i in sequentially. finite_measure ((Pseq \<circ> r) i)"
    by (intro always_eventually allI) (simp add: fmi)
  have MWfin: "mweak_conv_fin (mspace ?pm) (mdist ?pm)
      (Pseq \<circ> r) P sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using ev1 ev2 fmP setsP by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin "mspace ?pm" "mdist ?pm"
      "Pseq \<circ> r" P sequentially
    by (rule MWfin)
  note eq3 = MW.mweak_conv_eq3[THEN iffD1, OF mwc,
      THEN conjunct2, rule_format]
  note eq2 = MW.mweak_conv_eq2[THEN iffD1, OF mwc,
      THEN conjunct2, rule_format]
  have main_open: "measure P U \<le> b"
    if U: "openin (mtopology_of ?pm) U"
      and cb: "(\<lambda>i. measure (Pseq i) U) \<longlonglongrightarrow> b" for U b
  proof -
    have U': "openin (Metric_space.mtopology (mspace ?pm) (mdist ?pm)) U"
      using U by (simp add: mtopology_of_def)
    have sub: "(\<lambda>n. ereal (measure ((Pseq \<circ> r) n) U))
        \<longlonglongrightarrow> ereal b"
      using LIMSEQ_subseq_LIMSEQ[OF cb r] by (simp add: o_def)
    have Linf: "Liminf sequentially
        (\<lambda>n. ereal (measure ((Pseq \<circ> r) n) U)) = ereal b"
      by (rule lim_imp_Liminf[OF _ sub]) simp
    have "ereal (measure P U) \<le> ereal b"
      using eq3[OF U'] Linf by simp
    then show ?thesis by simp
  qed
  have main_closed: "b \<le> measure P D"
    if D: "closedin (mtopology_of ?pm) D"
      and cb: "(\<lambda>i. measure (Pseq i) D) \<longlonglongrightarrow> b" for D b
  proof -
    have D': "closedin (Metric_space.mtopology (mspace ?pm) (mdist ?pm)) D"
      using D by (simp add: mtopology_of_def)
    have sub: "(\<lambda>n. ereal (measure ((Pseq \<circ> r) n) D))
        \<longlonglongrightarrow> ereal b"
      using LIMSEQ_subseq_LIMSEQ[OF cb r] by (simp add: o_def)
    have Lsup: "Limsup sequentially
        (\<lambda>n. ereal (measure ((Pseq \<circ> r) n) D)) = ereal b"
      by (rule lim_imp_Limsup[OF _ sub]) simp
    have "ereal b \<le> ereal (measure P D)"
      using eq2[OF D'] Lsup by simp
    then show ?thesis by simp
  qed
  show ?thesis using P main_open main_closed by blast
qed

text \<open>The Euler laws at mesh \<open>c / (i + 1)\<close>: exactly \<open>i + 1\<close> steps of
  length \<open>c / (i + 1)\<close> land on the horizon \<open>c\<close> on the nose, so
  @{thm [source] eulerp_in_class} puts every member of the sequence in
  the SAME class and the transfer principle applies verbatim.\<close>

lemma eulerp_seq_in_class:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and x :: "real^'n"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "eulerp SF x (c / real (Suc i)) i \<in> paper_pair_class k L c x"
proof -
  have h0: "0 < c / real (Suc i)" using c0 by simp
  have "eulerp SF x (c / real (Suc i)) i
      \<in> paper_pair_class k L (real (Suc i) * (c / real (Suc i))) x"
    by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  moreover have "real (Suc i) * (c / real (Suc i)) = c" by simp
  ultimately show ?thesis by simp
qed

theorem eulerp_weak_limit:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and x :: "real^'n"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
  shows "\<exists>P \<in> paper_pair_class k L c x.
      (\<forall>U b. openin (mtopology_of
            (path_metric c :: ('n pairpath) metric)) U
          \<longrightarrow> (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U)
              \<longlonglongrightarrow> b
          \<longrightarrow> measure P U \<le> b)
      \<and> (\<forall>D b. closedin (mtopology_of
            (path_metric c :: ('n pairpath) metric)) D
          \<longrightarrow> (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) D)
              \<longlonglongrightarrow> b
          \<longrightarrow> b \<le> measure P D)"
proof -
  have L0: "0 \<le> L" using L1 by linarith
  show ?thesis
    by (rule paper_pair_class_weak_limit[OF c0 L0
        eulerp_seq_in_class[OF c0 L1 SFc SFs]])
qed

subsection \<open>The bad event vanishes with the mesh\<close>

text \<open>Batch 3e(i).  The OPEN bad event --- the path stays strictly inside
  the ball through time \<open>t\<close> yet the quadratic drops below its guaranteed
  growth --- has vanishing probability under the Euler laws.  Three
  estimates feed the proof: the grid functional's Chebyshev bound
  (@{thm [source] eulerp_Xi_chebyshev}), the pathwise lower bound at the
  nearest grid point (@{thm [source] eulerp_quad_lower}), and a
  fourth-moment tail for the one-step gap between the grid point and
  \<open>t\<close>, which we derive first from
  @{thm [source] paper_pair_class_fourth_moment}.\<close>

lemma paper_pair_class_increment_tail:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
    and l: "0 < l"
  shows "measure Q {\<omega> \<in> space Q.
      l \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}
    \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2 / l^4"
proof -
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have int4: "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
    by (rule paper_pair_class_fourth_moment_integrable[OF T L Q st stt ttT])
  have nn: "AE \<omega> in Q. 0 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4"
    by (simp add: zero_le_fourth)
  have intgl: "(\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
      \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
  proof -
    have eq: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
        = ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)"
      by (rule nn_integral_eq_integral[OF int4 nn])
    have le: "ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
        \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
    proof -
      have f4: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
          \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
        by (rule paper_pair_class_fourth_moment[OF T L setsQ Q st stt ttT])
      show ?thesis using f4 unfolding eq .
    qed
    have y0: "0 \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
      by (auto intro!: mult_nonneg_nonneg)
    show ?thesis using le y0 by (simp add: ennreal_le_iff)
  qed
  have seteq: "{\<omega> \<in> space Q. l^4 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4}
      = {\<omega> \<in> space Q. l \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}"
  proof -
    have iff: "l^4 \<le> y^4 \<longleftrightarrow> l \<le> \<bar>y\<bar>" for y :: real
    proof
      assume "l^4 \<le> y^4"
      then have "l ^ Suc 3 \<le> \<bar>y\<bar> ^ Suc 3"
        by (simp add: power_even_abs eval_nat_numeral)
      then show "l \<le> \<bar>y\<bar>" by (rule power_le_imp_le_base) simp
    next
      assume a: "l \<le> \<bar>y\<bar>"
      then have "l^4 \<le> \<bar>y\<bar>^4" using l by (intro power_mono) simp_all
      then show "l^4 \<le> y^4" by (simp add: power_even_abs)
    qed
    show ?thesis using iff by auto
  qed
  have l4: "0 < l^4" using l by simp
  have "measure Q {\<omega> \<in> space Q.
      l^4 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4}
      \<le> (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q) / l^4"
  proof (rule integral_Markov_inequality_measure)
    show "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
      by (rule int4)
    show "space Q \<in> sets Q" by (rule sets.top)
    show "AE \<omega> in Q. 0 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4"
      by (rule nn)
    show "0 < l^4" by (rule l4)
  qed
  also have "\<dots> \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2 / l^4"
    using intgl l4 by (intro divide_right_mono) simp_all
  finally show ?thesis using seteq by simp
qed

lemma paper_pair_class_increment_tail_norm:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
    and l: "0 < l"
  shows "measure Q {\<omega> \<in> space Q. l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}
    \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (tt - s)\<^sup>2) / l^4"
proof -
  let ?n = "real (CARD('n))"
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  interpret PQ: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have cpos: "0 < CARD('n)" by (simp add: card_gt_0_iff)
  have n0: "0 < ?n" using cpos by simp
  define l' where "l' = l / ?n"
  have l'0: "0 < l'" unfolding l'_def using l n0 by simp
  have sI: "s \<in> {0..T}" using st stt ttT by simp
  have tI: "tt \<in> {0..T}" using st stt ttT by simp
  have fmi: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> tt) $ i - fst (\<omega> s) $ i)
      \<in> borel_measurable Q" for i
    by (intro borel_measurable_diff pair_law_coord_measurable[OF setsQ tI]
        pair_law_coord_measurable[OF setsQ sI])
  have Em: "{\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}
      \<in> sets Q" for i
  proof -
    have am: "(\<lambda>\<omega>. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>)
        \<in> borel_measurable Q"
      by (intro borel_measurable_abs fmi)
    have "{\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}
        = (\<lambda>\<omega>. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>) -` {l'..} \<inter> space Q"
      by auto
    then show ?thesis
      using measurable_sets[OF am borel_closed[OF closed_atLeast]] by simp
  qed
  have incl: "{\<omega> \<in> space Q. l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}
      \<subseteq> (\<Union>i\<in>(UNIV :: 'n set).
          {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
  proof
    fix \<omega> assume w: "\<omega> \<in> {\<omega> \<in> space Q.
        l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}"
    then have sp: "\<omega> \<in> space Q"
      and ln: "l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))" by auto
    have ex: "\<exists>i. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>"
    proof (rule ccontr)
      assume nc: "\<not> (\<exists>i. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>)"
      then have all: "\<And>i. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar> < l'"
        by (auto simp: not_le)
      have "norm (fst (\<omega> tt) - fst (\<omega> s))
          \<le> (\<Sum>i\<in>UNIV. \<bar>(fst (\<omega> tt) - fst (\<omega> s)) $ i\<bar>)"
        by (rule norm_le_l1_cart)
      also have "\<dots> = (\<Sum>i\<in>UNIV. \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>)"
        by simp
      also have "\<dots> < (\<Sum>i\<in>(UNIV :: 'n set). l')"
        by (rule sum_strict_mono) (use all in simp_all)
      also have "\<dots> = ?n * l'" by simp
      also have "\<dots> = l" unfolding l'_def using n0 by simp
      finally show False using ln by simp
    qed
    then show "\<omega> \<in> (\<Union>i\<in>(UNIV :: 'n set).
        {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
      using sp by auto
  qed
  have UNs: "(\<Union>i\<in>(UNIV :: 'n set).
      {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>}) \<in> sets Q"
    using Em by blast
  have "measure Q {\<omega> \<in> space Q. l \<le> norm (fst (\<omega> tt) - fst (\<omega> s))}
      \<le> measure Q (\<Union>i\<in>(UNIV :: 'n set).
          {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
    by (rule PQ.finite_measure_mono[OF incl UNs])
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). measure Q
      {\<omega> \<in> space Q. l' \<le> \<bar>fst (\<omega> tt) $ i - fst (\<omega> s) $ i\<bar>})"
    by (rule measure_UNION_le) (use Em in simp_all)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). 8 * L\<^sup>2 * (tt - s)\<^sup>2 / l'^4)"
    by (rule sum_mono)
      (rule paper_pair_class_increment_tail[OF T L Q st stt ttT l'0])
  also have "\<dots> = ?n * (8 * L\<^sup>2 * (tt - s)\<^sup>2 / l'^4)" by simp
  also have "\<dots> = ?n ^ 5 * (8 * L\<^sup>2 * (tt - s)\<^sup>2) / l^4"
  proof -
    have l'4: "l'^4 = l^4 / ?n^4"
      unfolding l'_def by (simp add: power_divide)
    have ln0: "l^4 \<noteq> 0" using l by simp
    have nn0: "(?n :: real)^4 \<noteq> 0" using n0 by simp
    have "?n * (8 * L\<^sup>2 * (tt - s)\<^sup>2 / l'^4)
        = ?n * (8 * L\<^sup>2 * (tt - s)\<^sup>2 * ?n^4 / l^4)"
      unfolding l'4 using ln0 nn0 by (simp add: field_simps)
    also have "\<dots> = ?n ^ 5 * (8 * L\<^sup>2 * (tt - s)\<^sup>2) / l^4"
      by (simp add: eval_nat_numeral field_simps)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

text \<open>The quadratic is Lipschitz on the ball, with the explicit constant
  \<open>norm q + 2 C\<^sub>M rb\<close>; the exact one-step Taylor identity
  @{thm [source] quad_taylor_step} does all the work.\<close>

lemma quad_diff_bound:
  fixes M :: "real^'n::finite^'n" and q x a b :: "real^'n" and rb :: real
  assumes sym: "transpose M = M"
    and a: "a \<in> cball x rb" and b: "b \<in> cball x rb"
  shows "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
       - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> (norm q + 2 * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * rb)
          * norm (b - a)"
proof -
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have ax: "norm (a - x) \<le> rb"
    using a by (simp add: mem_cball dist_norm norm_minus_commute)
  have bx: "norm (b - x) \<le> rb"
    using b by (simp add: mem_cball dist_norm norm_minus_commute)
  have dble: "norm (b - a) \<le> 2 * rb"
  proof -
    have deq: "b - a = (b - x) + (x - a)" by simp
    have "norm (b - a) \<le> norm (b - x) + norm (x - a)"
      by (subst deq) (rule norm_triangle_ineq)
    moreover have "norm (x - a) \<le> rb"
      using ax by (simp add: norm_minus_commute)
    ultimately show ?thesis using bx by linarith
  qed
  have step: "q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))
      = (q + M *v (a - x)) \<bullet> (b - a)
        + (1/2) * ((b - a) \<bullet> (M *v (b - a)))"
    by (rule quad_taylor_step[OF sym])
  have t1: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
      \<le> (norm q + ?CM * rb) * norm (b - a)"
  proof -
    have cs: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        \<le> norm (q + M *v (a - x)) * norm (b - a)"
      by (rule Cauchy_Schwarz_ineq2)
    have "norm (q + M *v (a - x)) \<le> norm q + ?CM * rb"
    proof -
      have "norm (q + M *v (a - x)) \<le> norm q + norm (M *v (a - x))"
        by (rule norm_triangle_ineq)
      moreover have "norm (M *v (a - x)) \<le> ?CM * norm (a - x)"
        by (rule matvec_norm_le)
      moreover have "?CM * norm (a - x) \<le> ?CM * rb"
        by (rule mult_left_mono[OF ax CM0])
      ultimately show ?thesis by linarith
    qed
    then have "norm (q + M *v (a - x)) * norm (b - a)
        \<le> (norm q + ?CM * rb) * norm (b - a)"
      by (rule mult_right_mono) simp
    then show ?thesis using cs by linarith
  qed
  have t2: "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
      \<le> ?CM * rb * norm (b - a)"
  proof -
    have "\<bar>(b - a) \<bullet> (M *v (b - a))\<bar>
        \<le> norm (b - a) * norm (M *v (b - a))"
      by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> norm (b - a) * (?CM * norm (b - a))"
      by (rule mult_left_mono[OF matvec_norm_le norm_ge_zero])
    finally have h: "\<bar>(b - a) \<bullet> (M *v (b - a))\<bar>
        \<le> ?CM * norm (b - a) * norm (b - a)"
      by (simp add: mult_ac)
    have h2: "?CM * norm (b - a) * norm (b - a)
        \<le> ?CM * (2 * rb) * norm (b - a)"
      by (rule mult_right_mono[OF mult_left_mono[OF dble CM0] norm_ge_zero])
    have "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
        = (1/2) * \<bar>(b - a) \<bullet> (M *v (b - a))\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> (1/2) * (?CM * (2 * rb) * norm (b - a))"
      using h h2 by linarith
    also have "\<dots> = ?CM * rb * norm (b - a)" by simp
    finally show ?thesis .
  qed
  have tri: "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> \<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        + \<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>"
    unfolding step by (rule abs_triangle_ineq)
  have fin: "(norm q + ?CM * rb) * norm (b - a)
      + ?CM * rb * norm (b - a)
      = (norm q + 2 * ?CM * rb) * norm (b - a)"
    by (simp add: algebra_simps)
  show ?thesis using tri t1 t2 fin by linarith
qed

text \<open>The bad event is open: staying strictly inside the ball is
  @{thm [source] open_stay_inside} through the first projection, and the
  strict quadratic drop is an open condition on the evaluation at \<open>t\<close>
  (@{thm [source] open_eval_preimage}).\<close>

lemma open_quad_bad_event:
  fixes x q :: "real^'n::finite" and M :: "real^'n^'n"
    and t T rb thr :: real
  assumes t0: "0 \<le> t" and tT: "t \<le> T"
  shows "openin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}"
proof -
  have T0: "0 \<le> T" using t0 tT by linarith
  let ?pm = "path_metric T :: ('n pairpath) metric"
  have o1: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` ball x rb}"
    by (rule open_stay_inside[OF T0 open_vimage_fst[OF open_ball] t0 tT])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  have oU: "open {p :: (real^'n) \<times> (real^'n^'n).
      q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}"
    by (rule open_Collect_less[OF contf continuous_on_const])
  have o2: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
        + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by (rule open_eval_preimage[OF _ oU]) (use t0 tT in simp)
  have eq: "{\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}
      = {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` ball x rb}
        \<inter> {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
          + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by auto
  show ?thesis unfolding eq by (rule openin_Int[OF o1 o2])
qed

text \<open>The main estimate.  At mesh \<open>c / (i + 1)\<close> the bad-event probability
  is at most \<open>A h + B h\<^sup>2\<close> once the mesh is fine enough, hence it tends to
  zero.  Inside: pick the last grid point \<open>m h \<le> t\<close>; on the almost-sure
  event of @{thm [source] eulerp_quad_lower}, in-ball through \<open>t\<close> and a
  quadratic drop force either a large \<open>euXi\<close> (Chebyshev) or a large
  one-step increment (the fourth-moment tail).\<close>

theorem eulerp_bad_event_null:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c rb cm t \<beta> L :: real
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M" and rb0: "0 \<le> rb"
    and kill: "\<And>z. transpose (SF z) *v
        (q + M *v (closest_point (cball x rb) z - x)) = 0"
    and marg: "\<And>z. cm \<le> trace (M ** (SF z ** transpose (SF z)))"
    and t0: "0 < t" and tc: "t \<le> c" and b0: "0 < \<beta>"
  shows "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
      {\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
          < t * cm / 2 - \<beta>}) \<longlonglongrightarrow> 0"
proof -
  let ?U = "{\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric).
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
        < t * cm / 2 - \<beta>}"
  let ?h = "\<lambda>i. c / real (Suc i)"
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  define C\<psi> where "C\<psi> = norm q + 2 * ?CM * rb + 1"
  define \<delta> where "\<delta> = \<beta> / (4 * C\<psi>)"
  define h\<^sub>0 where "h\<^sub>0 = \<beta> / (2 * (\<bar>cm\<bar> + 1))"
  define A where "A = 4 * c * xiC M L / \<beta>\<^sup>2"
  define B where "B = real (CARD('n)) ^ 5 * 8 * L\<^sup>2 / \<delta>^4"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have C\<psi>1: "1 \<le> C\<psi>"
  proof -
    have "0 \<le> 2 * ?CM * rb"
      using CM0 rb0 by (auto intro!: mult_nonneg_nonneg)
    then show ?thesis
      unfolding C\<psi>_def using norm_ge_zero[of q] by linarith
  qed
  have C\<psi>0: "0 < C\<psi>" using C\<psi>1 by linarith
  have \<delta>0: "0 < \<delta>" unfolding \<delta>_def using b0 C\<psi>0 by simp
  have h\<^sub>00: "0 < h\<^sub>0" unfolding h\<^sub>0_def using b0 by simp
  have L0: "0 \<le> L" using L1 by linarith
  have bound: "measure (eulerp SF x (?h i) i) ?U \<le> A * ?h i + B * (?h i)\<^sup>2"
    if hs: "?h i \<le> h\<^sub>0" for i
  proof -
    define h where "h = ?h i"
    have hs': "h \<le> h\<^sub>0" using hs unfolding h_def .
    have h0: "0 < h" unfolding h_def using c0 by simp
    have hc: "real (Suc i) * h = c" unfolding h_def by simp
    let ?Q = "eulerp SF x h i"
    have Qc: "?Q \<in> paper_pair_class k L c x"
      unfolding h_def by (rule eulerp_seq_in_class[OF c0 L1 SFc SFs])
    have setsQ: "sets ?Q = sets (borel_of (mtopology_of
        (path_metric c :: ('n pairpath) metric)))"
      by (rule paper_pair_class_sets[OF Qc])
    have spQ: "space ?Q = mspace (path_metric c :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF setsQ])
    interpret PQ: prob_space ?Q by (rule paper_pair_class_prob[OF Qc])
    define m where "m = nat \<lfloor>t / h\<rfloor>"
    have tdh0: "0 \<le> t / h" using t0 h0 by simp
    have fl0: "0 \<le> \<lfloor>t / h\<rfloor>" using tdh0 by simp
    have mreal: "real m = real_of_int \<lfloor>t / h\<rfloor>"
      unfolding m_def using fl0 by (simp add: of_nat_nat)
    have mh_le: "real m * h \<le> t"
    proof -
      have "real_of_int \<lfloor>t / h\<rfloor> \<le> t / h" by (rule of_int_floor_le)
      then have "real m \<le> t / h" using mreal by simp
      then show ?thesis
        using h0 by (simp add: pos_le_divide_eq mult_ac)
    qed
    have mh0: "0 \<le> real m * h" using h0 by simp
    have t_mh: "t - real m * h \<le> h"
    proof -
      have "t / h < real_of_int \<lfloor>t / h\<rfloor> + 1"
        using floor_correct[of "t / h"] by linarith
      then have "t / h < real m + 1" using mreal by simp
      then have "t < (real m + 1) * h"
        using h0 by (simp add: pos_divide_less_eq)
      then show ?thesis by (simp add: algebra_simps)
    qed
    have mSuc: "m \<le> Suc i"
    proof -
      have "t / h \<le> real (Suc i)"
        using tc hc h0 by (simp add: pos_divide_le_eq mult_ac)
      then have "\<lfloor>t / h\<rfloor> \<le> int (Suc i)"
        by (simp add: floor_le_iff)
      then show ?thesis unfolding m_def by simp
    qed
    define E1 where "E1 = {\<omega> \<in> space ?Q. \<beta> / 2 \<le> \<bar>euXi SF M h m \<omega>\<bar>}"
    define E2 where "E2 = {\<omega> \<in> space ?Q.
        \<delta> \<le> norm (fst (\<omega> t) - fst (\<omega> (real m * h)))}"
    have b20: "0 < \<beta> / 2" using b0 by simp
    have mE1: "measure ?Q E1 \<le> real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2"
      unfolding E1_def
      by (rule eulerp_Xi_chebyshev[OF h0 L1 SFc SFs mSuc b20])
    have mE2: "measure ?Q E2
        \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4"
      unfolding E2_def
      by (rule paper_pair_class_increment_tail_norm[OF c0 L0 Qc
          mh0 mh_le tc \<delta>0])
    have sE1: "E1 \<in> sets ?Q"
    proof -
      have xm: "euXi SF M h m \<in> borel_measurable ?Q"
        using euXi_measurable[OF SFc]
          measurable_cong_sets[OF setsQ refl] by blast
      have am: "(\<lambda>\<omega>. \<bar>euXi SF M h m \<omega>\<bar>) \<in> borel_measurable ?Q"
        by (intro borel_measurable_abs xm)
      have "E1 = (\<lambda>\<omega>. \<bar>euXi SF M h m \<omega>\<bar>) -` {\<beta>/2..} \<inter> space ?Q"
        unfolding E1_def by auto
      then show ?thesis
        using measurable_sets[OF am borel_closed[OF closed_atLeast]]
        by simp
    qed
    have sE2: "E2 \<in> sets ?Q"
    proof -
      have e1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> borel_measurable ?Q"
        using pair_law_eval_measurable[OF setsQ] by blast
      have e2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real m * h))
          \<in> borel_measurable ?Q"
        using pair_law_eval_measurable[OF setsQ] by blast
      have fm: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_onI[OF
            continuous_on_fst[OF continuous_on_id]])
      have dd: "(\<lambda>\<omega>. fst (\<omega> t) - fst (\<omega> (real m * h)))
          \<in> borel_measurable ?Q"
        by (intro borel_measurable_diff
            measurable_compose[OF e1 fm] measurable_compose[OF e2 fm])
      have nm: "(\<lambda>\<omega>. norm (fst (\<omega> t) - fst (\<omega> (real m * h))))
          \<in> borel_measurable ?Q"
        by (rule measurable_compose[OF dd borel_measurable_norm])
      have "E2 = (\<lambda>\<omega>. norm (fst (\<omega> t) - fst (\<omega> (real m * h)))) -` {\<delta>..}
          \<inter> space ?Q"
        unfolding E2_def by auto
      then show ?thesis
        using measurable_sets[OF nm borel_closed[OF closed_atLeast]]
        by simp
    qed
    have QL: "AE \<omega> in ?Q. \<forall>m'\<le>Suc i.
        (\<forall>j<m'. fst (\<omega> (real j * h)) \<in> cball x rb) \<longrightarrow>
        (1/2) * euXi SF M h m' \<omega> + real m' * h * cm / 2
          \<le> q \<bullet> (fst (\<omega> (real m' * h)) - x)
            + (1/2) * ((fst (\<omega> (real m' * h)) - x)
                \<bullet> (M *v (fst (\<omega> (real m' * h)) - x)))"
      by (rule eulerp_quad_lower[OF h0 L1 SFc SFs sym rb0 kill marg])
    have incl: "AE \<omega> in ?Q. \<omega> \<in> ?U \<longrightarrow> \<omega> \<in> E1 \<union> E2"
      using QL
    proof (eventually_elim)
      case (elim \<omega>)
      show ?case
      proof (intro impI)
        assume U: "\<omega> \<in> ?U"
        show "\<omega> \<in> E1 \<union> E2"
        proof (cases "\<omega> \<in> E1")
          case True then show ?thesis by simp
        next
          case False
          have wsp: "\<omega> \<in> space ?Q" using U spQ by auto
          have inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> ball x rb"
            using U by auto
          have bad: "q \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
              < t * cm / 2 - \<beta>"
            using U by auto
          have small: "\<bar>euXi SF M h m \<omega>\<bar> < \<beta> / 2"
            using False wsp unfolding E1_def by (auto simp: not_le)
          have grid: "\<And>j. j < m \<Longrightarrow> fst (\<omega> (real j * h)) \<in> cball x rb"
          proof -
            fix j assume jm: "j < m"
            have "real j * h < real m * h"
              using jm h0 by (intro mult_strict_right_mono) simp_all
            then have jh2: "real j * h \<le> t" using mh_le by linarith
            have jh1: "0 \<le> real j * h" using h0 by simp
            have "real j * h \<in> {0..t}" using jh1 jh2 by simp
            then show "fst (\<omega> (real j * h)) \<in> cball x rb"
              using inb ball_subset_cball by blast
          qed
          have QLm: "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
              \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
                + (1/2) * ((fst (\<omega> (real m * h)) - x)
                    \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
            using elim mSuc grid by blast
          have tin: "t \<in> {0..t}" using t0 by simp
          have min': "real m * h \<in> {0..t}" using mh0 mh_le by simp
          have aT: "fst (\<omega> t) \<in> cball x rb"
            using inb[OF tin] ball_subset_cball by blast
          have aM: "fst (\<omega> (real m * h)) \<in> cball x rb"
            using inb[OF min'] ball_subset_cball by blast
          define p1 where "p1 = q \<bullet> (fst (\<omega> (real m * h)) - x)
              + (1/2) * ((fst (\<omega> (real m * h)) - x)
                  \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
          define p2 where "p2 = q \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
          define nd where "nd = norm (fst (\<omega> t) - fst (\<omega> (real m * h)))"
          have nd0: "0 \<le> nd" unfolding nd_def by simp
          have habs: "\<bar>real m * h - t\<bar> \<le> h"
          proof -
            have "real m * h - t \<le> h" using mh_le h0 by linarith
            moreover have "- h \<le> real m * h - t" using t_mh by linarith
            ultimately show ?thesis by (simp add: abs_le_iff)
          qed
          have g1: "\<bar>(real m * h - t) * cm\<bar> \<le> h * \<bar>cm\<bar>"
          proof -
            have "\<bar>(real m * h - t) * cm\<bar> = \<bar>real m * h - t\<bar> * \<bar>cm\<bar>"
              by (rule abs_mult)
            also have "\<dots> \<le> h * \<bar>cm\<bar>"
              by (rule mult_right_mono[OF habs abs_ge_zero])
            finally show ?thesis .
          qed
          have g2: "h * \<bar>cm\<bar> \<le> \<beta> / 2"
          proof -
            have "h * (2 * (\<bar>cm\<bar> + 1)) \<le> \<beta>"
              using hs' unfolding h\<^sub>0_def
              by (simp add: pos_le_divide_eq)
            moreover have "h * (2 * (\<bar>cm\<bar> + 1))
                = 2 * (h * (\<bar>cm\<bar> + 1))" by simp
            ultimately have hcm1: "h * (\<bar>cm\<bar> + 1) \<le> \<beta> / 2" by linarith
            have "h * \<bar>cm\<bar> \<le> h * (\<bar>cm\<bar> + 1)"
              using h0 by (intro mult_left_mono) simp_all
            then show ?thesis using hcm1 by linarith
          qed
          have cmb: "- (\<beta> / 4) \<le> (real m * h - t) * cm / 2"
          proof -
            have "- (h * \<bar>cm\<bar>) \<le> (real m * h - t) * cm"
              using g1 by linarith
            then show ?thesis using g2 by linarith
          qed
          have p1low: "- (\<beta> / 4) + real m * h * cm / 2 \<le> p1"
            using QLm small unfolding p1_def by linarith
          have badp: "p2 < t * cm / 2 - \<beta>"
            unfolding p2_def by (rule bad)
          have distrib: "(real m * h - t) * cm
              = real m * h * cm - t * cm"
            by (simp add: algebra_simps)
          have gap: "\<beta> / 2 < p1 - p2"
            using p1low badp cmb distrib by linarith
          have db: "\<bar>p1 - p2\<bar> \<le> (norm q + 2 * ?CM * rb) * nd"
            unfolding p1_def p2_def nd_def
            using quad_diff_bound[OF sym aT aM]
            by (simp add: norm_minus_commute)
          have Cle: "norm q + 2 * ?CM * rb \<le> C\<psi>"
            unfolding C\<psi>_def by simp
          have bCn: "\<beta> / 2 < C\<psi> * nd"
          proof -
            have "\<beta> / 2 < (norm q + 2 * ?CM * rb) * nd"
              using gap db by linarith
            also have "\<dots> \<le> C\<psi> * nd"
              by (rule mult_right_mono[OF Cle nd0])
            finally show ?thesis .
          qed
          have b2Cn: "\<beta> < nd * (2 * C\<psi>)"
          proof -
            have "\<beta> < 2 * (C\<psi> * nd)" using bCn by linarith
            then show ?thesis by (simp add: mult_ac)
          qed
          have lt: "\<beta> / (2 * C\<psi>) < nd"
            using b2Cn C\<psi>0 by (simp add: pos_divide_less_eq)
          have dle: "\<delta> \<le> \<beta> / (2 * C\<psi>)"
            unfolding \<delta>_def
          proof (rule divide_left_mono)
            show "2 * C\<psi> \<le> 4 * C\<psi>" using C\<psi>0 by linarith
            show "0 \<le> \<beta>" using b0 by linarith
            show "0 < 4 * C\<psi> * (2 * C\<psi>)"
              using C\<psi>0 by (simp add: zero_less_mult_iff)
          qed
          have ndl: "\<delta> \<le> nd" using lt dle by linarith
          show ?thesis
            using wsp ndl unfolding E2_def nd_def by auto
        qed
      qed
    qed
    have s1: "measure ?Q ?U \<le> measure ?Q (E1 \<union> E2)"
      by (rule PQ.finite_measure_mono_AE[OF incl sets.Un[OF sE1 sE2]])
    have s2: "measure ?Q (E1 \<union> E2) \<le> measure ?Q E1 + measure ?Q E2"
      by (rule measure_Un_le[OF sE1 sE2])
    have n1: "real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2 \<le> A * h"
    proof -
      have mhc: "real m * h \<le> c"
      proof -
        have "real m \<le> real (Suc i)" using mSuc by simp
        then have "real m * h \<le> real (Suc i) * h"
          using h0 by (intro mult_right_mono) simp_all
        then show ?thesis using hc by simp
      qed
      have e1: "real m * xiC M L * h\<^sup>2 = real m * h * xiC M L * h"
        by (simp add: power2_eq_square algebra_simps)
      have e2: "real m * h * xiC M L * h \<le> c * xiC M L * h"
        by (intro mult_right_mono mult_right_mono[OF mhc xiC_nonneg])
          (use h0 in simp_all)
      have num: "real m * xiC M L * h\<^sup>2 \<le> c * xiC M L * h"
        unfolding e1 by (rule e2)
      have "real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2
          \<le> c * xiC M L * h / (\<beta> / 2)\<^sup>2"
        by (rule divide_right_mono[OF num]) simp
      also have "\<dots> = A * h"
        unfolding A_def using b0 by (simp add: power_divide field_simps)
      finally show ?thesis .
    qed
    have n2: "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
        \<le> B * h\<^sup>2"
    proof -
      have sq: "(t - real m * h)\<^sup>2 \<le> h\<^sup>2"
        using t_mh mh_le by (intro power_mono) simp_all
      have inner8: "8 * L\<^sup>2 * (t - real m * h)\<^sup>2 \<le> 8 * L\<^sup>2 * h\<^sup>2"
        by (intro mult_left_mono[OF sq]) simp
      have "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2)
          \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * h\<^sup>2)"
        by (intro mult_left_mono[OF inner8]) simp
      then have "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
          \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * h\<^sup>2) / \<delta>^4"
        by (intro divide_right_mono) simp_all
      also have "\<dots> = B * h\<^sup>2"
        unfolding B_def using \<delta>0 by (simp add: field_simps)
      finally show ?thesis .
    qed
    have "measure ?Q ?U \<le> A * h + B * h\<^sup>2"
      using s1 s2 mE1 mE2 n1 n2 by linarith
    then show ?thesis unfolding h_def .
  qed
  have hlim: "(\<lambda>i. ?h i) \<longlonglongrightarrow> 0"
    using tendsto_mult[OF tendsto_const LIMSEQ_inverse_real_of_nat, of c]
    by (simp add: divide_inverse)
  have ev: "\<forall>\<^sub>F i in sequentially.
      measure (eulerp SF x (?h i) i) ?U \<le> A * ?h i + B * (?h i)\<^sup>2"
  proof -
    have "\<forall>\<^sub>F i in sequentially. ?h i < h\<^sub>0"
      by (rule order_tendstoD(2)[OF hlim h\<^sub>00])
    then show ?thesis
    proof (eventually_elim)
      case (elim i)
      show ?case by (rule bound[OF less_imp_le[OF elim]])
    qed
  qed
  have ev0: "\<forall>\<^sub>F i in sequentially.
      (0 :: real) \<le> measure (eulerp SF x (?h i) i) ?U"
    by (intro always_eventually allI measure_nonneg)
  have glim: "(\<lambda>i. A * ?h i + B * (?h i)\<^sup>2) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>i. A * ?h i + B * (?h i)\<^sup>2) \<longlonglongrightarrow> A * 0 + B * 0\<^sup>2"
      by (intro tendsto_add tendsto_mult tendsto_const
          tendsto_power hlim)
    then show ?thesis by simp
  qed
  show ?thesis
    by (rule tendsto_sandwich[OF ev0 ev tendsto_const glim])
qed

subsection \<open>The limit member grows along the quadratic, almost surely\<close>

text \<open>Batch 3e(ii).  Combining the weak-limit transfer with the vanishing
  bad events: SOME class member \<open>P\<close> satisfies, almost surely, for EVERY
  time \<open>t\<close> --- not just rational ones --- that staying strictly inside
  the ball through \<open>t\<close> forces the quadratic to grow at rate \<open>cm/2\<close>.
  The countable skeleton (rational \<open>t\<close>, margins \<open>1/(n+1)\<close>) comes from
  @{thm [source] eulerp_weak_limit} + @{thm [source] eulerp_bad_event_null}
  + @{thm [source] open_quad_bad_event}; the upgrade to real \<open>t\<close> is
  pathwise, using only that members of the path space are continuous.\<close>

lemma quad_eval_cont:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c :: real
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
  shows "continuous_on {0..c} (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
proof -
  have wc: "continuous_on {0..c} \<omega>" by (rule mspace_path_metricD[OF wm])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  show ?thesis
    by (rule continuous_on_compose2[OF contf wc]) auto
qed

lemma quad_good_rat_to_real:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm rb t :: real
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and rat: "\<And>r. r \<in> \<rat> \<Longrightarrow> 0 < r \<Longrightarrow> r \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> ball x rb) \<Longrightarrow>
      r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> ball x rb"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  have exr: "\<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t" for j
  proof -
    have "max 0 (t - inverse (real (Suc j))) < t"
      using t0 by (simp add: max_less_iff_conj)
    then show ?thesis
      using Rats_dense_in_real[of
          "max 0 (t - inverse (real (Suc j)))" t] by blast
  qed
  have exr': "\<forall>j. \<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t"
    using exr by blast
  obtain rj where rjprop: "\<forall>j. rj j \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < rj j \<and> rj j < t"
    using choice[OF exr'] by blast
  have rjQ: "rj j \<in> \<rat>" for j using rjprop by blast
  have rjl: "max 0 (t - inverse (real (Suc j))) < rj j" for j
    using rjprop by blast
  have rju: "rj j < t" for j using rjprop by blast
  have rj0: "0 < rj j" for j
  proof -
    have "(0::real) \<le> max 0 (t - inverse (real (Suc j)))" by simp
    then show ?thesis using rjl[of j] by linarith
  qed
  have rjc: "rj j \<le> c" for j using rju[of j] tc by linarith
  have glow: "rj j * cm / 2 \<le> g (rj j)" for j
    unfolding g_def
  proof (rule rat)
    show "rj j \<in> \<rat>" by (rule rjQ)
    show "0 < rj j" by (rule rj0)
    show "rj j \<le> c" by (rule rjc)
    show "\<forall>s\<in>{0..rj j}. fst (\<omega> s) \<in> ball x rb"
    proof
      fix s assume "s \<in> {0..rj j}"
      then have "s \<in> {0..t}" using rju[of j] by auto
      then show "fst (\<omega> s) \<in> ball x rb" by (rule inb)
    qed
  qed
  have rjlim: "rj \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of
      "\<lambda>j. t - inverse (real (Suc j))" rj sequentially "\<lambda>_. t"])
    show "\<forall>\<^sub>F j in sequentially. t - inverse (real (Suc j)) \<le> rj j"
    proof (intro always_eventually allI)
      fix j
      have "t - inverse (real (Suc j))
          \<le> max 0 (t - inverse (real (Suc j)))"
        by (rule max.cobounded2)
      then show "t - inverse (real (Suc j)) \<le> rj j"
        using rjl[of j] by linarith
    qed
    show "\<forall>\<^sub>F j in sequentially. rj j \<le> t"
      by (intro always_eventually allI less_imp_le rju)
    show "(\<lambda>j. t - inverse (real (Suc j))) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const
          LIMSEQ_inverse_real_of_nat, of t] by simp
    show "(\<lambda>_. t) \<longlonglongrightarrow> t" by (rule tendsto_const)
  qed
  have gcomp: "(\<lambda>j. g (rj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. rj n \<in> {0..c}"
      using rj0 rjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> rj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS rjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. rj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF rjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

theorem eulerp_limit_good:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c rb cm L :: real
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M" and rb0: "0 \<le> rb"
    and kill: "\<And>z. transpose (SF z) *v
        (q + M *v (closest_point (cball x rb) z - x)) = 0"
    and marg: "\<And>z. cm \<le> trace (M ** (SF z ** transpose (SF z)))"
  shows "\<exists>P \<in> paper_pair_class k L c x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb) \<longrightarrow>
      t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  let ?pm = "path_metric c :: ('n pairpath) metric"
  define Us where "Us = (\<lambda>r \<beta> :: real. {\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> ball x rb)
      \<and> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))
        < r * cm / 2 - \<beta>})"
  obtain P where P: "P \<in> paper_pair_class k L c x"
    and Praw: "\<forall>U b'. openin (mtopology_of ?pm) U \<longrightarrow>
      (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U) \<longlonglongrightarrow> b' \<longrightarrow>
      measure P U \<le> b'"
    using eulerp_weak_limit[OF c0 L1 SFc SFs] by blast
  interpret FP: prob_space P by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets (borel_of (mtopology_of ?pm))"
    by (rule paper_pair_class_sets[OF P])
  have spaceP: "space P = mspace ?pm"
    by (rule space_of_path_sets[OF setsP])
  have AErn: "AE \<omega> in P. \<omega> \<notin> Us r (inverse (real (Suc n)))"
    if r0: "0 < r" and rc: "r \<le> c" for r and n :: nat
  proof -
    have inv0: "(0::real) < inverse (real (Suc n))" by simp
    have opn: "openin (mtopology_of ?pm) (Us r (inverse (real (Suc n))))"
      unfolding Us_def
      by (rule open_quad_bad_event[OF less_imp_le[OF r0] rc])
    have tnd: "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
        (Us r (inverse (real (Suc n))))) \<longlonglongrightarrow> 0"
      unfolding Us_def
      by (rule eulerp_bad_event_null[OF c0 L1 SFc SFs sym rb0 kill marg
          r0 rc inv0])
    have le0: "measure P (Us r (inverse (real (Suc n)))) \<le> 0"
      using Praw opn tnd by blast
    have m0: "measure P (Us r (inverse (real (Suc n)))) = 0"
      using le0 measure_nonneg[of P "Us r (inverse (real (Suc n)))"]
      by linarith
    have Uset: "Us r (inverse (real (Suc n))) \<in> sets P"
      using borel_of_open[OF opn] by (simp add: setsP)
    have "Us r (inverse (real (Suc n))) \<in> null_sets P"
    proof (rule null_setsI)
      show "emeasure P (Us r (inverse (real (Suc n)))) = 0"
        using m0 by (simp add: FP.emeasure_eq_measure)
      show "Us r (inverse (real (Suc n))) \<in> sets P" by (rule Uset)
    qed
    then show ?thesis by (rule AE_not_in)
  qed
  define I where "I = {r. r \<in> \<rat> \<and> 0 < r \<and> r \<le> c}"
  have cI: "countable I"
    unfolding I_def by (rule countable_subset[OF _ countable_rat]) auto
  have AEall: "AE \<omega> in P. \<forall>r\<in>I. \<forall>n::nat.
      \<omega> \<notin> Us r (inverse (real (Suc n)))"
    unfolding AE_ball_countable[OF cI]
  proof
    fix r assume "r \<in> I"
    then have r0: "0 < r" and rc: "r \<le> c" unfolding I_def by auto
    show "AE \<omega> in P. \<forall>n::nat. \<omega> \<notin> Us r (inverse (real (Suc n)))"
      unfolding AE_all_countable by (intro allI AErn[OF r0 rc])
  qed
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  show ?thesis
  proof (intro bexI[OF _ P])
    show "AE \<omega> in P. \<forall>t. 0 < t \<longrightarrow> t \<le> c \<longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb) \<longrightarrow>
        t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
      using AEall sp
    proof (eventually_elim)
      case (elim \<omega>)
      have wm: "\<omega> \<in> mspace ?pm" using elim(2) by (simp add: spaceP)
      have notin: "\<And>r n. r \<in> I \<Longrightarrow>
          \<omega> \<notin> Us r (inverse (real (Suc n)))"
        using elim(1) by blast
      show ?case
      proof (intro allI impI)
        fix t assume t0: "0 < t" and tc: "t \<le> c"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb"
        have rat: "r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
          if rQ: "r \<in> \<rat>" and r0: "0 < r" and rc: "r \<le> c"
            and rball: "\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> ball x rb" for r
        proof (rule ccontr)
          assume nle: "\<not> r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
          have pos: "0 < r * cm / 2 - (q \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x))))"
            using nle by simp
          obtain n where nsm: "inverse (real (Suc n))
              < r * cm / 2 - (q \<bullet> (fst (\<omega> r) - x)
                + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x))))"
            using reals_Archimedean[OF pos] by auto
          have drop: "q \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))
              < r * cm / 2 - inverse (real (Suc n))"
            using nsm by linarith
          have "\<omega> \<in> Us r (inverse (real (Suc n)))"
            unfolding Us_def using wm rball drop by auto
          moreover have "r \<in> I" unfolding I_def using rQ r0 rc by simp
          ultimately show False using notin by blast
        qed
        show "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
        proof (rule quad_good_rat_to_real[OF wm rat t0 tc])
          fix s assume "s \<in> {0..t}"
          then show "fst (\<omega> s) \<in> ball x rb" using inb by blast
        qed
      qed
    qed
  qed
qed

subsection \<open>The limit member at the exit time\<close>

text \<open>Batch 3e(iii).  The almost-sure growth statement, specialised to the
  exit time of the ball.  Pathwise: before the exit the path is strictly
  inside (@{thm [source] pexit_le_of_mem}), so the growth bound holds at
  every earlier time and passes to the exit by continuity; the exit is
  strictly positive because the path starts at the centre
  (@{thm [source] pball_exit_pos}), stays in the closed ball through the
  exit (@{thm [source] pball_exit_stays_cball}), and lands on the sphere
  whenever it happens before the cap (@{thm [source] pball_exit_outside}).
  This is everything the DPP contradiction needs from the process.\<close>

lemma quad_good_upto:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm rb t :: real
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and good: "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> ball x rb) \<Longrightarrow>
      t' * cm / 2 \<le> q \<bullet> (fst (\<omega> t') - x)
        + (1/2) * ((fst (\<omega> t') - x) \<bullet> (M *v (fst (\<omega> t') - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> fst (\<omega> s) \<in> ball x rb"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  define tj where "tj = (\<lambda>j. t - t / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "t / (2 * real (Suc j)) \<le> t / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> t" using t0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using t0 by linarith
  qed
  have tju: "tj j < t" for j
  proof -
    have "0 < t / (2 * real (Suc j))" using t0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjc: "tj j \<le> c" for j using tju[of j] tc by linarith
  have glow: "tj j * cm / 2 \<le> g (tj j)" for j
    unfolding g_def
  proof (rule good)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> c" by (rule tjc)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> ball x rb"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have s0: "0 \<le> s" and st: "s < t" using tju[of j] by auto
      show "fst (\<omega> s) \<in> ball x rb" by (rule inb[OF s0 st])
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> t"
  proof -
    have eq: "(\<lambda>j. (t / 2) * inverse (real (Suc j)))
        = (\<lambda>j. t / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (t / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (t / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. t / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. t - t / (2 * real (Suc j))) \<longlonglongrightarrow> t - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..c}"
      using tjl tjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. tj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF tjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

theorem eulerp_limit_exit:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c rb cm L :: real
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M" and rb0: "0 < rb"
    and kill: "\<And>z. transpose (SF z) *v
        (q + M *v (closest_point (cball x rb) z - x)) = 0"
    and marg: "\<And>z. cm \<le> trace (M ** (SF z ** transpose (SF z)))"
  shows "\<exists>P \<in> paper_pair_class k L c x. AE \<omega> in P.
      0 < pball_exit c x rb \<omega>
      \<and> (\<forall>s\<in>{0..pball_exit c x rb \<omega>}. fst (\<omega> s) \<in> cball x rb)
      \<and> (pball_exit c x rb \<omega> < c \<longrightarrow>
          dist (fst (\<omega> (pball_exit c x rb \<omega>))) x = rb)
      \<and> pball_exit c x rb \<omega> * cm / 2
          \<le> q \<bullet> (fst (\<omega> (pball_exit c x rb \<omega>)) - x)
            + (1/2) * ((fst (\<omega> (pball_exit c x rb \<omega>)) - x)
                \<bullet> (M *v (fst (\<omega> (pball_exit c x rb \<omega>)) - x)))
      \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s < pball_exit c x rb \<omega> \<longrightarrow>
          fst (\<omega> s) \<in> ball x rb)
      \<and> (\<forall>t. 0 < t \<longrightarrow> t \<le> c \<longrightarrow>
          (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb) \<longrightarrow>
          t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))))"
proof -
  let ?pm = "path_metric c :: ('n pairpath) metric"
  have rb0': "0 \<le> rb" using rb0 by linarith
  have c0': "0 \<le> c" using c0 by linarith
  obtain P where P: "P \<in> paper_pair_class k L c x"
    and good: "AE \<omega> in P. \<forall>t. 0 < t \<longrightarrow> t \<le> c \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb) \<longrightarrow>
      t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
    using eulerp_limit_good[OF c0 L1 SFc SFs sym rb0' kill marg] by blast
  have setsP: "sets P = sets (borel_of (mtopology_of ?pm))"
    by (rule paper_pair_class_sets[OF P])
  have spaceP: "space P = mspace ?pm"
    by (rule space_of_path_sets[OF setsP])
  have start: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule paper_pair_class_start[OF P])
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  show ?thesis
  proof (intro bexI[OF _ P])
    show "AE \<omega> in P.
        0 < pball_exit c x rb \<omega>
        \<and> (\<forall>s\<in>{0..pball_exit c x rb \<omega>}. fst (\<omega> s) \<in> cball x rb)
        \<and> (pball_exit c x rb \<omega> < c \<longrightarrow>
            dist (fst (\<omega> (pball_exit c x rb \<omega>))) x = rb)
        \<and> pball_exit c x rb \<omega> * cm / 2
            \<le> q \<bullet> (fst (\<omega> (pball_exit c x rb \<omega>)) - x)
              + (1/2) * ((fst (\<omega> (pball_exit c x rb \<omega>)) - x)
                  \<bullet> (M *v (fst (\<omega> (pball_exit c x rb \<omega>)) - x)))
        \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s < pball_exit c x rb \<omega> \<longrightarrow>
            fst (\<omega> s) \<in> ball x rb)
        \<and> (\<forall>t. 0 < t \<longrightarrow> t \<le> c \<longrightarrow>
            (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rb) \<longrightarrow>
            t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))))"
      using good start sp
    proof (eventually_elim)
      case (elim \<omega>)
      have wsp: "\<omega> \<in> space P" using elim(3) .
      have wm: "\<omega> \<in> mspace ?pm" using wsp by (simp add: spaceP)
      have cont: "continuous_on {0..c} (\<lambda>t. fst (\<omega> t))"
        by (rule path_sets_fst_continuous[OF setsP wsp])
      have x0: "fst (\<omega> 0) = x" using elim(2) by blast
      have sdist: "dist (fst (\<omega> 0)) x < rb" using x0 rb0 by simp
      define \<theta> where "\<theta> = pball_exit c x rb \<omega>"
      have th_pos: "0 < \<theta>" unfolding \<theta>_def
        by (rule pball_exit_pos[OF c0 sdist cont])
      have th_le: "\<theta> \<le> c" unfolding \<theta>_def by (rule pball_exit_le[OF c0'])
      have stays: "fst (\<omega> s) \<in> cball x rb" if s: "s \<in> {0..\<theta>}" for s
      proof -
        have "dist (fst (\<omega> s)) x \<le> rb"
          using pball_exit_stays_cball[OF c0' sdist cont, of s] s
          unfolding \<theta>_def by auto
        then show ?thesis by (simp add: mem_cball dist_commute)
      qed
      have inside: "fst (\<omega> s) \<in> ball x rb"
        if s0: "0 \<le> s" and st: "s < \<theta>" for s
      proof (rule ccontr)
        assume nb: "fst (\<omega> s) \<notin> ball x rb"
        have sc: "s \<le> c" using st th_le by linarith
        have "pexit c (ball x rb) (\<lambda>t. fst (\<omega> t)) \<le> s"
          by (rule pexit_le_of_mem[OF c0' s0 sc]) (use nb in simp)
        then have "\<theta> \<le> s" unfolding \<theta>_def pball_exit_def .
        then show False using st by linarith
      qed
      have bdry: "dist (fst (\<omega> \<theta>)) x = rb" if lt: "\<theta> < c"
      proof -
        have lt': "pball_exit c x rb \<omega> < c" using lt unfolding \<theta>_def .
        have ge: "rb \<le> dist (fst (\<omega> \<theta>)) x"
          using pball_exit_outside[OF c0' cont lt'] unfolding \<theta>_def by simp
        have inc: "fst (\<omega> \<theta>) \<in> cball x rb"
          using stays[of \<theta>] th_pos by simp
        then have le: "dist (fst (\<omega> \<theta>)) x \<le> rb"
          by (simp add: mem_cball dist_commute)
        show ?thesis using ge le by linarith
      qed
      have grow: "\<theta> * cm / 2 \<le> q \<bullet> (fst (\<omega> \<theta>) - x)
          + (1/2) * ((fst (\<omega> \<theta>) - x) \<bullet> (M *v (fst (\<omega> \<theta>) - x)))"
      proof (rule quad_good_upto[OF wm _ th_pos th_le])
        show "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> c \<Longrightarrow>
            (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> ball x rb) \<Longrightarrow>
            t' * cm / 2 \<le> q \<bullet> (fst (\<omega> t') - x)
              + (1/2) * ((fst (\<omega> t') - x) \<bullet> (M *v (fst (\<omega> t') - x)))"
          using elim(1) by blast
        show "\<And>s. 0 \<le> s \<Longrightarrow> s < \<theta> \<Longrightarrow> fst (\<omega> s) \<in> ball x rb"
          by (rule inside)
      qed
      show ?case
        using th_pos stays bdry grow inside elim(1)
        unfolding \<theta>_def by blast
    qed
  qed
qed

subsection \<open>The quadratic minorant and the concrete field\<close>

text \<open>Batch 4a.  Two independent bricks for the supersolution assembly.

  First, the mirror of @{thm [source] test_fun_quadratic_dominates}: a
  test function DOMINATES the quadratic with the softened Hessian
  \<open>H - \<delta>\<cdot>1\<close> near the touching point.  The proof is the same
  one-dimensional ray argument with every inequality reversed.

  Second, the concrete volatility field for the Euler construction: the
  columns of @{const skewfield} through a fixed eigenbasis enumeration,
  evaluated at the clamped point.  @{thm [source] skewfield_decomp}
  identifies its square with the field itself, so the three hypotheses
  of the Euler machinery --- admissible square, gradient kill, trace
  margin --- are @{thm [source] skewfield_properties} verbatim; the
  transpose kill needs one extra line of linear algebra
  (\<open>|S\<^sup>Tg|\<^sup>2 = ((SS\<^sup>T)g)\<bullet>g = 0\<close>).\<close>

definition skewSF ::
  "(real^'n::finite \<Rightarrow> real) \<Rightarrow> ('n \<Rightarrow> real^'n) \<Rightarrow> real^'n
     \<Rightarrow> real^'n^'n \<Rightarrow> real^'n \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "skewSF lam f q M x r z
    = (\<chi> i j. (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
        *v (q + M *v (closest_point (cball x r) z - x))) $ i)"

lemma skewSF_cont:
  fixes q x :: "real^'n::finite" and M :: "real^'n^'n" and r :: real
  assumes r0: "0 \<le> r"
  shows "continuous_on UNIV (skewSF lam f q M x r)"
proof -
  have cpc: "continuous_on UNIV (closest_point (cball x r))"
    by (rule continuous_on_closest_point)
      (use r0 in \<open>auto simp: convex_cball closed_cball\<close>)
  have gradc: "continuous_on UNIV (\<lambda>z :: real^'n.
      q + M *v (closest_point (cball x r) z - x))"
  proof -
    have d: "continuous_on UNIV (\<lambda>z :: real^'n.
        closest_point (cball x r) z - x)"
      by (intro continuous_intros cpc)
    have mv: "continuous_on UNIV (\<lambda>z :: real^'n.
        M *v (closest_point (cball x r) z - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  have entry: "continuous_on UNIV (\<lambda>z.
      (skewv q (sqrt (lam (f j)) *\<^sub>R f j)
        *v (q + M *v (closest_point (cball x r) z - x))) $ i)" for i j
  proof -
    have col: "continuous_on UNIV (\<lambda>z.
        skewv q (sqrt (lam (f j)) *\<^sub>R f j)
          *v (q + M *v (closest_point (cball x r) z - x)))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] gradc]) auto
    show ?thesis
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF bounded_linear_vec_nth] col]) auto
  qed
  show ?thesis
    unfolding skewSF_def by (intro continuous_on_vec_lambda entry)
qed

lemma skewSF_square:
  fixes B :: "(real^'n::finite) set" and f :: "'n \<Rightarrow> real^'n"
  assumes bij: "bij_betw f (UNIV :: 'n set) B"
  shows "skewSF lam f q M x r z ** transpose (skewSF lam f q M x r z)
      = skewfield B lam q M x (closest_point (cball x r) z)"
  unfolding skewSF_def by (rule skewfield_decomp[OF bij])

theorem skewSF_package:
  fixes B Bp :: "(real^'n::finite) set" and lam :: "real^'n \<Rightarrow> real"
    and f :: "'n \<Rightarrow> real^'n" and q x :: "real^'n" and M :: "real^'n^'n"
    and L m r \<eta> :: real
  defines "Cm \<equiv> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  defines "ec \<equiv> 2 * sqrt L * Cm / norm q"
  assumes bij: "bij_betw f (UNIV :: 'n set) B"
    and B: "onormal B" and sp: "span B = UNIV"
    and BpB: "Bp \<subseteq> B" and cardBp: "card Bp = CARD('n) - k"
    and lam_box: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u \<and> lam u \<le> L - m"
    and lam_lb: "\<And>u. u \<in> Bp \<Longrightarrow> 1 + m \<le> lam u"
    and lam_orth: "\<And>u. u \<in> B \<Longrightarrow> 0 < lam u \<Longrightarrow> u \<bullet> q = 0"
    and m0: "0 < m" and mL: "m \<le> L"
    and q0: "q \<noteq> 0"
    and tr: "\<eta> \<le> 1 + trace (M ** (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2"
    and r0: "0 \<le> r"
    and sm_ub: "(1 + 1 / (m / (2 * L)))
        * (real CARD('n) * (ec * r)\<^sup>2) \<le> m / 2"
    and sm_lb: "real CARD('n) * (ec * r * (2 * sqrt L + ec * r))
        + 2 * (1 + m) / m
          * (real CARD('n) * (ec * r * (2 * sqrt L + ec * r)))\<^sup>2 \<le> m / 2"
    and sm_tr: "real CARD('n)
        * (Cm * (ec * r * (2 * sqrt L + ec * r))) \<le> \<eta>"
  shows skewSF_sconstraint: "\<And>z. skewSF lam f q M x r z
        ** transpose (skewSF lam f q M x r z) \<in> sconstraint k L"
    and skewSF_kill: "\<And>z. transpose (skewSF lam f q M x r z)
        *v (q + M *v (closest_point (cball x r) z - x)) = 0"
    and skewSF_marg: "\<And>z. \<eta> - 2 \<le> trace (M ** (skewSF lam f q M x r z
        ** transpose (skewSF lam f q M x r z)))"
proof -
  have cin: "closest_point (cball x r) z \<in> cball x r" for z
    by (rule closest_point_in_set) (use r0 in \<open>auto simp: closed_cball\<close>)
  have zr: "dist (closest_point (cball x r) z) x \<le> r" for z
    using cin[of z] by (simp add: mem_cball dist_commute)
  note props = skewfield_properties[OF B sp BpB cardBp lam_box lam_lb
      lam_orth m0 mL q0 tr zr r0 sm_ub[unfolded ec_def Cm_def]
      sm_lb[unfolded ec_def Cm_def] sm_tr[unfolded ec_def Cm_def]]
  have sq: "skewSF lam f q M x r z ** transpose (skewSF lam f q M x r z)
      = skewfield B lam q M x (closest_point (cball x r) z)" for z
    by (rule skewSF_square[OF bij])
  show "skewSF lam f q M x r z ** transpose (skewSF lam f q M x r z)
      \<in> sconstraint k L" for z
    unfolding sq by (rule props(1))
  show "transpose (skewSF lam f q M x r z)
      *v (q + M *v (closest_point (cball x r) z - x)) = 0" for z
  proof -
    define A where "A = skewSF lam f q M x r z"
    define gr where "gr = q + M *v (closest_point (cball x r) z - x)"
    have a0: "(A ** transpose A) *v gr = 0"
      unfolding A_def gr_def sq by (rule props(2))
    have e1: "(transpose A *v gr) \<bullet> (transpose A *v gr)
        = (transpose (transpose A) *v (transpose A *v gr)) \<bullet> gr"
      by (rule inner_transpose_matrix)
    have e2: "transpose (transpose A) *v (transpose A *v gr)
        = A *v (transpose A *v gr)"
      by (simp only: transpose_transpose)
    have e3: "A *v (transpose A *v gr) = (A ** transpose A) *v gr"
      by (metis matrix_vector_mul_assoc)
    have e4: "((A ** transpose A) *v gr) \<bullet> gr = 0"
      using a0 by simp
    have "(transpose A *v gr) \<bullet> (transpose A *v gr) = 0"
      by (metis e1 e2 e3 e4)
    then have "transpose A *v gr = 0" by simp
    then show ?thesis unfolding A_def gr_def .
  qed
  show "\<eta> - 2 \<le> trace (M ** (skewSF lam f q M x r z
      ** transpose (skewSF lam f q M x r z)))" for z
  proof -
    have "\<eta> / 2 \<le> 1 + trace (M ** skewfield B lam q M x
        (closest_point (cball x r) z)) / 2"
      by (rule props(3))
    then show ?thesis unfolding sq by linarith
  qed
qed

subsection \<open>Bricks for the Case-1 contradiction\<close>

text \<open>Batch 4b(i).  Small independent pieces the contradiction assembles:
  algebra for the softened Hessian, a generic small-radius chooser, the
  witness extraction from a failed operator inequality, the value bound
  \<open>v(x) < T\<close> forced by a nonzero touching gradient, and the exit-time
  identity on paths that never leave \<open>K\<close>.\<close>

lemma transpose_sub_smat:
  fixes H :: "real^'n::finite^'n" and s :: real
  assumes symH: "transpose H = H"
  shows "transpose (H - s *\<^sub>R mat 1) = H - s *\<^sub>R mat 1"
proof -
  have "transpose (H - s *\<^sub>R mat 1)
      = transpose H - transpose (s *\<^sub>R mat 1)"
    by (simp add: transpose_def vec_eq_iff)
  then show ?thesis by (simp add: transpose_scalar symH)
qed

lemma trace_msub_mat:
  fixes H a :: "real^'n::finite^'n" and s :: real
  shows "trace ((H - s *\<^sub>R mat 1) ** a) = trace (H ** a) - s * trace a"
proof -
  have e1: "(H - s *\<^sub>R mat 1) ** a = H ** a - (s *\<^sub>R mat 1) ** a"
    by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf
        left_diff_distrib)
  have e2: "(s *\<^sub>R mat 1) ** a = s *\<^sub>R a"
    by (simp add: scaleR_matrix_mult matrix_mul_lid)
  have e3: "trace (H ** a - s *\<^sub>R a) = trace (H ** a) - s * trace a"
    by (simp add: trace_def sum_subtractf sum_distrib_left)
  show ?thesis unfolding e1 e2 by (rule e3)
qed

lemma quad_soften_split:
  fixes H :: "real^'n::finite^'n" and v :: "real^'n" and \<gamma> \<delta> :: real
  shows "v \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v v)
      = v \<bullet> ((H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1) *v v) + 2 * \<gamma> * (v \<bullet> v)"
proof -
  have e1: "(H - \<delta> *\<^sub>R mat 1) *v v = H *v v - \<delta> *\<^sub>R v"
    by (simp add: matrix_vector_mult_diff_rdistrib scaleR_matrix_vector
        matrix_vector_mul_lid)
  have e2: "(H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1) *v v
      = H *v v - (2 * \<gamma> + \<delta>) *\<^sub>R v"
    by (simp add: matrix_vector_mult_diff_rdistrib scaleR_matrix_vector
        matrix_vector_mul_lid)
  show ?thesis unfolding e1 e2
    by (simp add: inner_diff_right inner_scaleR_right algebra_simps)
qed

lemma small_radius_exists:
  fixes f1 f2 f3 :: "real \<Rightarrow> real" and b1 b2 b3 rmax :: real
  assumes c1: "isCont f1 0" and c2: "isCont f2 0" and c3: "isCont f3 0"
    and z1: "f1 0 = 0" and z2: "f2 0 = 0" and z3: "f3 0 = 0"
    and p1: "0 < b1" and p2: "0 < b2" and p3: "0 < b3" and rm: "0 < rmax"
  obtains r where "0 < r" and "r \<le> rmax"
    and "f1 r \<le> b1" and "f2 r \<le> b2" and "f3 r \<le> b3"
proof -
  have l1: "f1 \<midarrow>0\<rightarrow> 0" using c1 z1 by (simp add: isCont_def)
  have l2: "f2 \<midarrow>0\<rightarrow> 0" using c2 z2 by (simp add: isCont_def)
  have l3: "f3 \<midarrow>0\<rightarrow> 0" using c3 z3 by (simp add: isCont_def)
  obtain d1 where d10: "0 < d1"
    and h1: "\<And>y :: real. y \<noteq> 0 \<Longrightarrow> \<bar>y\<bar> < d1 \<Longrightarrow> \<bar>f1 y\<bar> < b1"
    using LIM_D[OF l1 p1] by auto
  obtain d2 where d20: "0 < d2"
    and h2: "\<And>y :: real. y \<noteq> 0 \<Longrightarrow> \<bar>y\<bar> < d2 \<Longrightarrow> \<bar>f2 y\<bar> < b2"
    using LIM_D[OF l2 p2] by auto
  obtain d3 where d30: "0 < d3"
    and h3: "\<And>y :: real. y \<noteq> 0 \<Longrightarrow> \<bar>y\<bar> < d3 \<Longrightarrow> \<bar>f3 y\<bar> < b3"
    using LIM_D[OF l3 p3] by auto
  define r where "r = min rmax (min d1 (min d2 d3)) / 2"
  have r0: "0 < r" unfolding r_def using rm d10 d20 d30 by simp
  have rr: "r \<le> rmax" unfolding r_def using rm by simp
  have rd1: "r < d1" and rd2: "r < d2" and rd3: "r < d3"
    unfolding r_def using rm d10 d20 d30 by auto
  have rne: "r \<noteq> 0" using r0 by simp
  have ra: "\<bar>r\<bar> = r" using r0 by simp
  have b1': "f1 r \<le> b1" using h1[OF rne] rd1 ra by fastforce
  have b2': "f2 r \<le> b2" using h2[OF rne] rd2 ra by fastforce
  have b3': "f3 r \<le> b3" using h3[OF rne] rd3 ra by fastforce
  show ?thesis by (rule that[OF r0 rr b1' b2' b3'])
qed

lemma ell_op_lt_witness:
  fixes p :: "real^'n::finite" and H :: "real^'n^'n"
  assumes k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
    and lt: "ell_op k L p H < 1"
  obtains a where "a \<in> feasible k L p" and "- trace (H ** a) / 2 < 1"
proof -
  have L0: "0 \<le> L" using L1 by linarith
  have ne: "(\<lambda>a. - trace (H ** a) / 2) ` feasible k L p \<noteq> {}"
    using feasible_nonempty[OF k1 kn L1] by blast
  have bdd: "bdd_below ((\<lambda>a. - trace (H ** a) / 2) ` feasible k L p)"
    by (rule bdd_below_mono[OF ell_op_s_bdd_below[OF L0]
        image_mono[OF feasible_subset_sconstraint]])
  have "\<exists>v \<in> (\<lambda>a. - trace (H ** a) / 2) ` feasible k L p. v < 1"
    using lt unfolding ell_op_def using cInf_less_iff[OF ne bdd] by blast
  then obtain a where a: "a \<in> feasible k L p"
    and tr: "- trace (H ** a) / 2 < 1" by blast
  show ?thesis by (rule that[OF a tr])
qed

lemma pexit_eq_of_stays:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T'" and stays: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T' \<Longrightarrow> f s \<in> K"
  shows "pexit T' K f = T'"
proof (rule order.antisym)
  show "pexit T' K f \<le> T'" by (rule pexit_le_T[OF T0])
  show "T' \<le> pexit T' K f"
  proof (rule ccontr)
    assume "\<not> T' \<le> pexit T' K f"
    then have "pexit T' K f < T'" by simp
    then have "(\<exists>r. 0 \<le> r \<and> r \<le> T' \<and> f r \<in> - K \<and> r < T') \<or> T' < T'"
      using pexit_less_iff[OF T0] by blast
    then show False using stays by auto
  qed
qed

text \<open>A nonzero touching gradient forces \<open>v(x) < T\<close>: the test function
  strictly increases along its gradient, the global minimum of \<open>v - \<phi>\<close>
  transfers the increase to \<open>v\<close>, and \<open>v \<le> T\<close> caps the other end.  This
  is what neutralises the horizon cap in the Case-1 functional.\<close>

lemma touching_grad_lt_horizon:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow>
      enn2real (paper_v k L T K x) - \<phi> x
        \<le> enn2real (paper_v k L T K y) - \<phi> y"
    and gx0: "g x \<noteq> 0"
  shows "enn2real (paper_v k L T K x) < T"
proof -
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  define h where "h = (\<lambda>s. \<phi> (x + s *\<^sub>R g x))"
  have hd: "(h has_field_derivative (g x \<bullet> g x)) (at 0)"
  proof -
    have i1: "((\<lambda>s :: real. x + s *\<^sub>R g x)
        has_derivative (\<lambda>u. u *\<^sub>R g x)) (at 0)"
      by (auto intro!: derivative_eq_intros)
    have mem0: "x + (0::real) *\<^sub>R g x \<in> ball x e" using e0 by simp
    have i2: "(\<phi> has_derivative (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> u))
        (at (x + (0::real) *\<^sub>R g x))"
      by (rule dphi[OF mem0])
    have "((\<lambda>s. \<phi> (x + s *\<^sub>R g x)) has_derivative
        (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> (u *\<^sub>R g x))) (at 0)"
      using diff_chain_at[OF i1 i2] by (simp add: o_def)
    then show ?thesis unfolding h_def
      by (rule has_derivative_imp_has_field_derivative)
        (simp add: inner_scaleR_right ac_simps)
  qed
  have gg0: "0 < g x \<bullet> g x"
    using gx0 by (simp add: inner_gt_zero_iff)
  have "((\<lambda>s. (h s - h 0) / (s - 0)) \<longlongrightarrow> g x \<bullet> g x) (at 0)"
    using hd by (simp add: has_field_derivative_iff)
  then have "\<forall>\<^sub>F s in at (0::real). 0 < (h s - h 0) / (s - 0)"
    by (rule order_tendstoD(1)[OF _ gg0])
  then obtain d where d0: "0 < d"
    and hpos: "\<And>s :: real. s \<noteq> 0 \<Longrightarrow> \<bar>s\<bar> < d \<Longrightarrow> 0 < (h s - h 0) / s"
    unfolding eventually_at by (auto simp: dist_real_def)
  define ng where "ng = norm (g x) + 1"
  have ng0: "0 < ng" unfolding ng_def
    using norm_ge_zero[of "g x"] by linarith
  define s where "s = min (min d (e / ng)) (eK / ng) / 2"
  have s0: "0 < s"
    unfolding s_def using d0 e0 eK0 ng0 by simp
  have sd: "s < d" unfolding s_def using d0 e0 eK0 ng0 by auto
  have se: "s * ng < e"
  proof -
    have "s \<le> (e / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> e / 2"
      using ng0 by (simp add: field_simps)
    then show ?thesis using e0 by linarith
  qed
  have sK: "s * ng < eK"
  proof -
    have "s \<le> (eK / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> eK / 2"
      using ng0 by (simp add: field_simps)
    then show ?thesis using eK0 by linarith
  qed
  have sg_lt: "s * norm (g x) < min e eK"
  proof -
    have "s * norm (g x) \<le> s * ng"
      unfolding ng_def using s0 by (intro mult_left_mono) auto
    then show ?thesis using se sK by simp
  qed
  define z where "z = x + s *\<^sub>R g x"
  have dz: "dist x z = s * norm (g x)"
    unfolding z_def dist_norm using s0 by (simp add: abs_of_nonneg)
  have zK: "z \<in> K"
  proof -
    have "z \<in> ball x eK" using dz sg_lt by (simp add: mem_ball)
    then show ?thesis using eKK by blast
  qed
  have hgt: "\<phi> x < \<phi> z"
  proof -
    have "0 < (h s - h 0) / s"
      using hpos[of s] s0 sd by simp
    then have "0 < h s - h 0"
      using s0 by (simp add: zero_less_divide_iff)
    then show ?thesis unfolding h_def z_def by simp
  qed
  have zT: "enn2real (paper_v k L T K z) \<le> T"
  proof -
    have "enn2real (paper_v k L T K z)
        = min (enn2real (paper_v k L T K z)) T"
      by (rule enn2real_paper_v_horizon_cap[OF less_imp_le[OF T0]
          order_refl L1 Kc])
    then show ?thesis by (metis min.cobounded2)
  qed
  have "enn2real (paper_v k L T K x)
      \<le> enn2real (paper_v k L T K z) - (\<phi> z - \<phi> x)"
    using tmin[OF zK] by simp
  also have "\<dots> < enn2real (paper_v k L T K z)" using hgt by simp
  also have "\<dots> \<le> T" by (rule zT)
  finally show ?thesis .
qed

subsection \<open>Case 1: a nonzero gradient contradicts a failed supersolution
  inequality\<close>

text \<open>Batch 4b(ii).  The full contradiction.  If the supersolution
  inequality fails at a touching point with nonzero gradient, then: the
  failure yields a feasible witness with slack \<open>2\<eta>\<^sub>0\<close>; softening the
  Hessian by \<open>(2\<gamma>+\<delta>)\<cdot>1\<close> keeps slack \<open>2\<eta>\<close> and buys both the Taylor
  minorant (via \<open>\<delta>\<close>) and a strict sphere margin (via \<open>\<gamma>\<close>); the strict
  eigendata builds the skew field, the Euler limit produces a class
  member whose paths grow along the quadratic, and at the stopping time
  \<open>min cc (pball_exit T x rr)\<close> the DPP functional is at least
  \<open>v(x) + mg\<close> almost surely --- the exit branch is paid by \<open>\<gamma> rr\<^sup>2\<close>, the
  no-exit branch by \<open>cc \<eta> / 2\<close>, and the horizon cap by \<open>T - v(x) > 0\<close>,
  which a nonzero gradient forces.  That contradicts
  @{thm [source] paper_v_dpp_sup_ge_time}.\<close>

theorem paper_v_supersol_contradiction_case1:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow>
      enn2real (paper_v k L T K x) - \<phi> x
        \<le> enn2real (paper_v k L T K y) - \<phi> y"
    and gx0: "g x \<noteq> 0"
    and fail: "ell_op k L (g x) H < 1"
  shows False
proof -
  have L1': "1 \<le> L" using L1 by linarith
  have L0: "0 \<le> L" using L1 by linarith
  have T0': "0 \<le> T" using T0 by linarith
  define tv where "tv = (\<lambda>y. enn2real (paper_v k L T K y))"
  have vxT: "tv x < T"
    unfolding tv_def
    by (rule touching_grad_lt_horizon[OF T0 L1' Kc xi tf tmin gx0])
  obtain a where aF: "a \<in> feasible k L (g x)"
    and aTr: "- trace (H ** a) / 2 < 1"
    by (rule ell_op_lt_witness[OF k1 kn L1' fail])
  define \<eta>\<^sub>0 where "\<eta>\<^sub>0 = (1 - (- trace (H ** a) / 2)) / 2"
  have h00: "0 < \<eta>\<^sub>0" unfolding \<eta>\<^sub>0_def using aTr by simp
  have trH: "2 * \<eta>\<^sub>0 \<le> 1 + trace (H ** a) / 2"
    unfolding \<eta>\<^sub>0_def by simp
  have aS: "a \<in> sconstraint k L"
    using aF feasible_subset_sconstraint by blast
  define TB where "TB = real CARD('n) * (real CARD('n) * L)"
  have trab: "trace a \<le> TB"
    unfolding TB_def by (rule sconstraint_trace_le[OF L0 aS])
  have tra0: "0 \<le> trace a"
    using sconstraint_trace_ge[OF kn aS] by linarith
  have TB1: "0 < TB + 1"
  proof -
    have "0 \<le> TB" using trab tra0 by linarith
    then show ?thesis by linarith
  qed
  define sft where "sft = min (\<eta>\<^sub>0 / (TB + 1)) 1"
  have sft0: "0 < sft"
    unfolding sft_def using h00 TB1 by simp
  define \<gamma> where "\<gamma> = sft / 4"
  define \<delta> where "\<delta> = sft / 2"
  have g0: "0 < \<gamma>" unfolding \<gamma>_def using sft0 by simp
  have d0: "0 < \<delta>" unfolding \<delta>_def using sft0 by simp
  have gd_le: "2 * \<gamma> + \<delta> \<le> sft" unfolding \<gamma>_def \<delta>_def by simp
  have gd0: "0 \<le> 2 * \<gamma> + \<delta>" using g0 d0 by linarith
  define M where "M = H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have symM: "transpose M = M"
    unfolding M_def by (rule transpose_sub_smat[OF symH])
  define \<eta> where "\<eta> = \<eta>\<^sub>0 / 2"
  have e0: "0 < \<eta>" unfolding \<eta>_def using h00 by simp
  have trM: "2 * \<eta> \<le> 1 + trace (M ** a) / 2"
  proof -
    have tr_eq: "trace (M ** a) = trace (H ** a) - (2 * \<gamma> + \<delta>) * trace a"
      unfolding M_def by (rule trace_msub_mat)
    have "(2 * \<gamma> + \<delta>) * trace a \<le> sft * trace a"
      by (rule mult_right_mono[OF gd_le tra0])
    also have "\<dots> \<le> (\<eta>\<^sub>0 / (TB + 1)) * (TB + 1)"
    proof (rule mult_mono)
      show "sft \<le> \<eta>\<^sub>0 / (TB + 1)" unfolding sft_def by simp
      show "trace a \<le> TB + 1" using trab by linarith
      show "0 \<le> \<eta>\<^sub>0 / (TB + 1)" using h00 TB1 by simp
      show "0 \<le> trace a" by (rule tra0)
    qed
    also have "\<dots> = \<eta>\<^sub>0" using TB1 by simp
    finally have "(2 * \<gamma> + \<delta>) * trace a \<le> \<eta>\<^sub>0" .
    then show ?thesis unfolding \<eta>_def using trH tr_eq h00 by linarith
  qed
  show False
  proof (rule feasible_strict_eigendata[OF aF kn L1 trM e0])
    fix B Bp :: "(real^'n) set" and lam :: "real^'n \<Rightarrow> real" and m :: real
    assume Bon: "onormal B" and Bsp: "span B = UNIV" and Bfin: "finite B"
      and BpB: "Bp \<subseteq> B" and cBp: "card Bp = CARD('n) - k" and m0: "0 < m"
      and lam_box: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u \<and> lam u \<le> L - m"
      and lam_lb: "\<And>u. u \<in> Bp \<Longrightarrow> 1 + m \<le> lam u"
      and lam_orth: "\<And>u. u \<in> B \<Longrightarrow> 0 < lam u \<Longrightarrow> u \<bullet> (g x) = 0"
      and treig: "\<eta> \<le> 1 + trace (M **
          (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2"
    show False
    proof -
  have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF Bon Bsp])
  have mL: "m \<le> L"
  proof -
    have "B \<noteq> {}" using cardB kn by auto
    then obtain u where uB: "u \<in> B" by blast
    from lam_box[OF uB] show ?thesis using m0 by linarith
  qed
  obtain f where bijf: "bij_betw f (UNIV :: 'n set) B"
    by (rule exists_enum_of_card[OF Bfin cardB])
  obtain rphi where rphi0: "0 < rphi"
    and mino: "\<And>z. z \<in> ball x rphi \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    using test_fun_quadratic_minorates[OF tf d0] by metis
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  define Cm where "Cm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
  define ec where "ec = 2 * sqrt L * Cm / norm (g x)"
  define f1 where "f1 = (\<lambda>r. (1 + 1 / (m / (2 * L)))
      * (real CARD('n) * (ec * r)\<^sup>2))"
  define f2 where "f2 = (\<lambda>r. real CARD('n)
      * (ec * r * (2 * sqrt L + ec * r))
      + 2 * (1 + m) / m
        * (real CARD('n) * (ec * r * (2 * sqrt L + ec * r)))\<^sup>2)"
  define f3 where "f3 = (\<lambda>r. real CARD('n)
      * (Cm * (ec * r * (2 * sqrt L + ec * r))))"
  have c1: "isCont f1 0" unfolding f1_def by (auto intro!: continuous_intros)
  have c2: "isCont f2 0" unfolding f2_def
    using m0 by (auto intro!: continuous_intros)
  have c3: "isCont f3 0" unfolding f3_def by (auto intro!: continuous_intros)
  have z1: "f1 0 = 0" unfolding f1_def by simp
  have z2: "f2 0 = 0" unfolding f2_def by simp
  have z3: "f3 0 = 0" unfolding f3_def by simp
  have m20: "0 < m / 2" using m0 by simp
  have rmx0: "0 < min (rphi / 2) (eK / 2)" using rphi0 eK0 by simp
  obtain rr where rr0: "0 < rr" and rrx: "rr \<le> min (rphi / 2) (eK / 2)"
    and s1: "f1 rr \<le> m / 2" and s2: "f2 rr \<le> m / 2" and s3: "f3 rr \<le> \<eta>"
    by (rule small_radius_exists[OF c1 c2 c3 z1 z2 z3 m20 m20 e0 rmx0])
  have rr_phi: "rr < rphi" and rr_K: "rr < eK"
    using rrx rphi0 eK0 by auto
  have cb_phi: "cball x rr \<subseteq> ball x rphi"
    using rr_phi by (auto simp: mem_cball mem_ball)
  have cb_K: "cball x rr \<subseteq> K"
  proof -
    have "cball x rr \<subseteq> ball x eK"
      using rr_K by (auto simp: mem_cball mem_ball)
    then show ?thesis using eKK by blast
  qed
  define SF where "SF = skewSF lam f (g x) M x rr"
  have SFc: "continuous_on UNIV SF"
    unfolding SF_def by (rule skewSF_cont[OF less_imp_le[OF rr0]])
  note pack = skewSF_package[OF bijf Bon Bsp BpB cBp lam_box lam_lb
      lam_orth m0 mL gx0 treig less_imp_le[OF rr0]
      s1[unfolded f1_def ec_def Cm_def]
      s2[unfolded f2_def ec_def Cm_def]
      s3[unfolded f3_def ec_def Cm_def]]
  have SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    unfolding SF_def by (rule pack(1))
  have kill: "\<And>z. transpose (SF z) *v
      (g x + M *v (closest_point (cball x rr) z - x)) = 0"
    unfolding SF_def by (rule pack(2))
  have marg: "\<And>z. \<eta> - 2 \<le> trace (M ** (SF z ** transpose (SF z)))"
    unfolding SF_def by (rule pack(3))
  obtain P where Pc: "P \<in> paper_pair_class k L T x"
    and AEpack: "AE \<omega> in P.
      0 < pball_exit T x rr \<omega>
      \<and> (\<forall>s\<in>{0..pball_exit T x rr \<omega>}. fst (\<omega> s) \<in> cball x rr)
      \<and> (pball_exit T x rr \<omega> < T \<longrightarrow>
          dist (fst (\<omega> (pball_exit T x rr \<omega>))) x = rr)
      \<and> pball_exit T x rr \<omega> * (\<eta> - 2) / 2
          \<le> g x \<bullet> (fst (\<omega> (pball_exit T x rr \<omega>)) - x)
            + (1/2) * ((fst (\<omega> (pball_exit T x rr \<omega>)) - x)
                \<bullet> (M *v (fst (\<omega> (pball_exit T x rr \<omega>)) - x)))
      \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s < pball_exit T x rr \<omega> \<longrightarrow>
          fst (\<omega> s) \<in> ball x rr)
      \<and> (\<forall>t. 0 < t \<longrightarrow> t \<le> T \<longrightarrow>
          (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rr) \<longrightarrow>
          t * (\<eta> - 2) / 2 \<le> g x \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))))"
    using eulerp_limit_exit[OF T0 L1' SFc SFs symM rr0 kill marg] by blast
  define cc where "cc = T / 2"
  have cc0: "0 < cc" unfolding cc_def using T0 by simp
  have ccT: "cc < T" unfolding cc_def using T0 by simp
  have ccT': "cc \<le> T" using ccT by linarith
  define \<theta> where "\<theta> = (\<lambda>\<omega> :: 'n pairpath. min cc (pball_exit T x rr \<omega>))"
  have st: "path_stopping_time T \<theta>"
    unfolding \<theta>_def
    by (rule path_stopping_time_min[OF pball_exit_path_stopping_time[OF T0']
        less_imp_le[OF cc0] ccT'])
  have thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    unfolding \<theta>_def
    by (intro borel_measurable_min pball_exit_measurable[OF T0']
        borel_measurable_const)
  define FN where "FN = (\<lambda>\<omega> :: 'n pairpath.
      pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>
            \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
         else 0))"
  have dpp: "(SUP P' \<in> paper_pair_class k L T x. ess_inf_time P' FN)
      \<le> paper_v k L T K x"
    unfolding FN_def
    by (rule paper_v_dpp_sup_ge_time[OF T0 L1' Kc st thM])
  define mg where "mg = min (min (\<gamma> * rr\<^sup>2) (cc * \<eta> / 2)) (T - tv x)"
  have mg0: "0 < mg"
  proof -
    have "0 < \<gamma> * rr\<^sup>2" using g0 rr0 by simp
    moreover have "0 < cc * \<eta> / 2" using cc0 e0 by simp
    moreover have "0 < T - tv x" using vxT by simp
    ultimately show ?thesis unfolding mg_def by simp
  qed
  have AEfun: "AE \<omega> in P. ennreal (tv x + mg) \<le> ennreal (FN \<omega>)"
    using AEpack
  proof (eventually_elim)
    case (elim \<omega>)
    define \<tau> where "\<tau> = pball_exit T x rr \<omega>"
    note elim' = elim[folded \<tau>_def]
    have tau0: "0 < \<tau>" using elim' by blast
    have stays: "\<And>s. s \<in> {0..\<tau>} \<Longrightarrow> fst (\<omega> s) \<in> cball x rr"
      using elim' by blast
    have bdry: "\<tau> < T \<Longrightarrow> dist (fst (\<omega> \<tau>)) x = rr"
      using elim' by blast
    have growtau: "\<tau> * (\<eta> - 2) / 2
        \<le> g x \<bullet> (fst (\<omega> \<tau>) - x)
          + (1/2) * ((fst (\<omega> \<tau>) - x) \<bullet> (M *v (fst (\<omega> \<tau>) - x)))"
      using elim' by blast
    have inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < \<tau> \<Longrightarrow> fst (\<omega> s) \<in> ball x rr"
      using elim' by blast
    have growall: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rr) \<Longrightarrow>
        t * (\<eta> - 2) / 2 \<le> g x \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
      using elim' by blast
    have tauT: "\<tau> \<le> T" unfolding \<tau>_def by (rule pball_exit_le[OF T0'])
    have thw: "\<theta> \<omega> = min cc \<tau>" unfolding \<theta>_def \<tau>_def by (rule refl)
    have th0: "0 < \<theta> \<omega>" unfolding thw using cc0 tau0 by simp
    have thcc: "\<theta> \<omega> \<le> cc" unfolding thw by simp
    have thtau: "\<theta> \<omega> \<le> \<tau>" unfolding thw by simp
    have thT: "\<theta> \<omega> < T" using thcc ccT by linarith
    have inK: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> \<theta> \<omega> \<Longrightarrow> fst (\<omega> s) \<in> K"
    proof -
      fix s assume s0: "0 \<le> s" and sth: "s \<le> \<theta> \<omega>"
      have "s \<in> {0..\<tau>}" using s0 sth thtau by simp
      then have "fst (\<omega> s) \<in> cball x rr" by (rule stays)
      then show "fst (\<omega> s) \<in> K" using cb_K by blast
    qed
    have pex: "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>"
      by (rule pexit_eq_of_stays[OF less_imp_le[OF th0]]) (use inK in simp)
    have XinK: "fst (\<omega> (\<theta> \<omega>)) \<in> K"
      using inK[of "\<theta> \<omega>"] th0 by simp
    have cap: "enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
        = min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
      unfolding tv_def
      by (rule enn2real_paper_v_horizon_cap[OF _ _ L1' Kc])
        (use thT th0 in auto)
    have feq: "FN \<omega> = \<theta> \<omega> + min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
      unfolding FN_def using pex XinK cap by simp
    have Xcb: "fst (\<omega> (\<theta> \<omega>)) \<in> cball x rr"
      using stays[of "\<theta> \<omega>"] th0 thtau by simp
    have Xphi: "fst (\<omega> (\<theta> \<omega>)) \<in> ball x rphi"
      using Xcb cb_phi by blast
    have touch: "tv x + (\<phi> (fst (\<omega> (\<theta> \<omega>))) - \<phi> x)
        \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
      using tmin[OF XinK] unfolding tv_def by linarith
    have minor: "\<phi> x + g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
        + ((fst (\<omega> (\<theta> \<omega>)) - x)
            \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))) / 2
        \<le> \<phi> (fst (\<omega> (\<theta> \<omega>)))"
      by (rule mino[OF Xphi])
    have soften: "(fst (\<omega> (\<theta> \<omega>)) - x)
        \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))
        = (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x))
          + 2 * \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
      unfolding M_def by (rule quad_soften_split)
    have tvX: "tv x + (g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
        + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
            \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
        + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)))
        \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
      using touch minor soften by linarith
    have QQ: "\<theta> \<omega> * (\<eta> - 2) / 2
        + (if \<tau> \<le> cc then \<gamma> * rr\<^sup>2 else 0)
        \<le> g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
          + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
              \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
          + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
    proof (cases "\<tau> \<le> cc")
      case True
      have theq: "\<theta> \<omega> = \<tau>" unfolding thw using True by simp
      have tauTs: "\<tau> < T" using True ccT by linarith
      have sphere: "dist (fst (\<omega> \<tau>)) x = rr" by (rule bdry[OF tauTs])
      have nrm: "norm (fst (\<omega> \<tau>) - x) = rr"
        using sphere by (simp add: dist_norm norm_minus_commute)
      have dsq: "(fst (\<omega> \<tau>) - x) \<bullet> (fst (\<omega> \<tau>) - x) = rr\<^sup>2"
        using nrm by (simp add: dot_square_norm)
      show ?thesis
        unfolding theq using growtau dsq True by simp
    next
      case False
      have theq: "\<theta> \<omega> = cc" unfolding thw using False by simp
      have inb: "\<forall>s\<in>{0..cc}. fst (\<omega> s) \<in> ball x rr"
      proof
        fix s assume "s \<in> {0..cc}"
        then have "0 \<le> s" and "s < \<tau>" using False by auto
        then show "fst (\<omega> s) \<in> ball x rr" by (rule inside)
      qed
      have gq: "cc * (\<eta> - 2) / 2 \<le> g x \<bullet> (fst (\<omega> cc) - x)
          + (1/2) * ((fst (\<omega> cc) - x) \<bullet> (M *v (fst (\<omega> cc) - x)))"
        by (rule growall[OF cc0 ccT' inb])
      have nn: "0 \<le> \<gamma> * ((fst (\<omega> cc) - x) \<bullet> (fst (\<omega> cc) - x))"
        using g0 inner_ge_zero by (simp add: mult_nonneg_nonneg)
      show ?thesis unfolding theq using gq nn False by simp
    qed
    have fun_ge: "tv x + mg \<le> FN \<omega>"
    proof (cases "tv (fst (\<omega> (\<theta> \<omega>))) \<le> T - \<theta> \<omega>")
      case True
      have mfe: "FN \<omega> = \<theta> \<omega> + tv (fst (\<omega> (\<theta> \<omega>)))"
        unfolding feq using True by simp
      have id1: "\<theta> \<omega> * (\<eta> - 2) / 2 + \<theta> \<omega> = \<theta> \<omega> * \<eta> / 2"
        by (simp add: field_simps)
      show ?thesis
      proof (cases "\<tau> \<le> cc")
        case True
        have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2 + \<gamma> * rr\<^sup>2
            \<le> g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
              + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
          using QQ True by simp
        have the0: "0 \<le> \<theta> \<omega> * \<eta> / 2"
          using th0 e0 by simp
        have mg1: "mg \<le> \<gamma> * rr\<^sup>2" unfolding mg_def by linarith
        show ?thesis
          unfolding mfe using tvX QQc id1 the0 mg1 by linarith
      next
        case False
        have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2
            \<le> g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))
              + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
          using QQ False by simp
        have theq: "\<theta> \<omega> = cc" unfolding thw using False by simp
        have mg2: "mg \<le> cc * \<eta> / 2" unfolding mg_def by linarith
        show ?thesis
          unfolding mfe theq
          using tvX[unfolded theq] QQc[unfolded theq] id1[unfolded theq] mg2
          by linarith
      qed
    next
      case False
      have mfe: "FN \<omega> = \<theta> \<omega> + (T - \<theta> \<omega>)"
        unfolding feq using False by simp
      have "FN \<omega> = T" unfolding mfe by simp
      moreover have "mg \<le> T - tv x" unfolding mg_def by simp
      ultimately show ?thesis by linarith
    qed
    show ?case by (rule ennreal_leI[OF fun_ge])
  qed
  have essge: "ennreal (tv x + mg) \<le> ess_inf_time P FN"
    unfolding ess_inf_time_def
    by (rule Sup_upper) (use AEfun in blast)
  have esle: "ess_inf_time P FN \<le> paper_v k L T K x"
  proof -
    have "ess_inf_time P FN
        \<le> (SUP P' \<in> paper_pair_class k L T x. ess_inf_time P' FN)"
      by (rule SUP_upper[OF Pc])
    then show ?thesis using dpp by (rule order_trans)
  qed
  have vfin: "ennreal (tv x) = paper_v k L T K x"
    unfolding tv_def
    using paper_v_neq_top[OF T0', of k L K x]
    by (simp add: ennreal_enn2real less_top)
  have chain: "ennreal (tv x + mg) \<le> paper_v k L T K x"
    by (rule order_trans[OF essge esle])
  have "ennreal (tv x + mg) \<le> ennreal (tv x)"
    using chain by (simp add: vfin)
  moreover have "0 \<le> tv x" unfolding tv_def by simp
  ultimately have "tv x + mg \<le> tv x" by (simp add: ennreal_le_iff)
  then show False using mg0 by linarith
    qed
  qed
qed

subsection \<open>Case 1, packaged for the envelope form\<close>

text \<open>Batch 4c(i).  The contradiction, read back as the positive
  statement the envelope supersolution definition wants: at any interior
  touching point with a NONZERO gradient the usc envelope of the
  operator is at least one, since \<open>F \<le> F\<^sup>*\<close>
  (@{thm [source] ell_op_le_ell_op_usc}) turns a failed envelope
  inequality into a failed plain one.\<close>

theorem paper_v_supersol_env_case1:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow>
      enn2real (paper_v k L T K x) - \<phi> x
        \<le> enn2real (paper_v k L T K y) - \<phi> y"
    and gx0: "g x \<noteq> 0"
  shows "1 \<le> ell_op_usc k L (g x) H"
proof (rule ccontr)
  assume nle: "\<not> 1 \<le> ell_op_usc k L (g x) H"
  then have lt: "ell_op_usc k L (g x) H < 1" by simp
  have "ereal (ell_op k L (g x) H) < 1"
    using ell_op_le_ell_op_usc[of k L "g x" H] lt by (rule le_less_trans)
  then have fail: "ell_op k L (g x) H < 1" by (simp add: one_ereal_def)
  show False
    by (rule paper_v_supersol_contradiction_case1[OF T0 L1 k1 kn Kc xi
        tf tmin gx0 fail])
qed

subsection \<open>Bricks for Case 2: the envelope limit and the tangential field\<close>

text \<open>Batch 4c(ii).  The sphere-tangential projector field.  (The
  companion input --- that the usc envelope passes \<open>\<ge> 1\<close> through limits
  in \<open>(p, M)\<close>, which is what turns the Case-1 conclusions at perturbed
  touching points into \<open>1 \<le> F\<^sup>*(0, H)\<close> --- is
  @{thm [source] ell_op_usc_ge_one_limit}, now in Envelopes with the
  rest of the envelope theory.)  Clamped to a ball separated from clamped to a ball separated from
  its centre \<open>y\<^sub>0\<close>, it is an admissible volatility that kills the radial
  direction EXACTLY, so the squared distance to \<open>y\<^sub>0\<close> moves at the
  deterministic rate \<open>CARD('n) - 1\<close>; this feeds the same Euler
  machinery as Case 1 and is the positivity input for the second horn
  of the dichotomy (and for Example 3.1's lower bound).\<close>

text \<open>Matrix difference distributes over the product --- inline bricks,
  entrywise.\<close>

lemma matrix_msub_rdistrib:
  fixes A B C :: "real^'n::finite^'n"
  shows "(A - B) ** C = A ** C - B ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf
      left_diff_distrib)

lemma matrix_msub_ldistrib:
  fixes A B C :: "real^'n::finite^'n"
  shows "A ** (B - C) = A ** B - A ** C"
  by (simp add: matrix_matrix_mult_def vec_eq_iff sum_subtractf
      right_diff_distrib)

subsubsection \<open>The tangential projector\<close>

definition tanp :: "real^'n::finite \<Rightarrow> real^'n^'n"
  where "tanp u = mat 1 - outerp u"

lemma tanp_mv: "tanp u *v w = w - (u \<bullet> w) *\<^sub>R u"
  unfolding tanp_def outerp_eq_outer_prod
  by (simp add: matrix_vector_mult_diff_rdistrib matrix_vector_mul_lid)

lemma tanp_sym: "transpose (tanp u) = tanp u"
proof -
  have "transpose (tanp u) = transpose (mat 1) - transpose (outerp u)"
    unfolding tanp_def by (simp add: transpose_def vec_eq_iff)
  also have "transpose (outerp u) = outerp u"
    by (simp add: transpose_def outerp_def vec_eq_iff mult_ac)
  finally show ?thesis by (simp add: tanp_def)
qed

lemma tanp_quadform: "x \<bullet> (tanp u *v x) = x \<bullet> x - (u \<bullet> x)\<^sup>2"
  unfolding tanp_mv
  by (simp add: inner_diff_right inner_scaleR_right
      power2_eq_square inner_commute)

lemma tanp_psd:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1"
  shows "psd (tanp u)"
  unfolding psd_def
proof (intro conjI allI)
  show "transpose (tanp u) = tanp u" by (rule tanp_sym)
next
  fix x :: "real^'n"
  have "\<bar>u \<bullet> x\<bar> \<le> norm u * norm x" by (rule Cauchy_Schwarz_ineq2)
  also have "\<dots> \<le> 1 * norm x"
    by (rule mult_right_mono[OF u1 norm_ge_zero])
  finally have cs: "\<bar>u \<bullet> x\<bar> \<le> norm x" by simp
  have sq: "(u \<bullet> x)\<^sup>2 \<le> (norm x)\<^sup>2"
    using cs by (metis abs_ge_zero power2_abs power_mono)
  have xx: "x \<bullet> x = (norm x)\<^sup>2" by (simp add: dot_square_norm)
  show "0 \<le> x \<bullet> (tanp u *v x)"
    unfolding tanp_quadform using sq xx by linarith
qed

lemma tanp_eigen_ub:
  fixes u :: "real^'n::finite"
  assumes L1: "1 \<le> L"
  shows "eigen_ub (tanp u) L"
  unfolding eigen_ub_def
proof
  fix x :: "real^'n"
  have "x \<bullet> (tanp u *v x) \<le> x \<bullet> x"
    unfolding tanp_quadform by simp
  also have "\<dots> = 1 * (x \<bullet> x)" by simp
  also have "\<dots> \<le> L * (x \<bullet> x)"
    by (rule mult_right_mono[OF L1 inner_ge_zero])
  finally show "x \<bullet> (tanp u *v x) \<le> L * (x \<bullet> x)" .
qed

lemma tanp_eigen_lb:
  fixes u :: "real^'n::finite"
  assumes k1: "1 \<le> k"
  shows "eigen_lb (tanp u) (CARD('n) - k)"
  unfolding eigen_lb_def
proof (intro exI[of _ "{x :: real^'n. u \<bullet> x = 0}"] conjI ballI)
  show "subspace {x :: real^'n. u \<bullet> x = 0}"
    by (rule subspace_hyperplane)
  show "CARD('n) - k \<le> dim {x :: real^'n. u \<bullet> x = 0}"
  proof (cases "u = 0")
    case True
    then have "{x :: real^'n. u \<bullet> x = 0} = UNIV" by simp
    then show ?thesis by simp
  next
    case False
    then have "dim {x :: real^'n. u \<bullet> x = 0} = CARD('n) - 1"
      by (simp add: dim_hyperplane)
    then show ?thesis using k1 by simp
  qed
next
  fix x :: "real^'n" assume "x \<in> {x. u \<bullet> x = 0}"
  then have "u \<bullet> x = 0" by simp
  then show "x \<bullet> x \<le> x \<bullet> (tanp u *v x)"
    unfolding tanp_quadform by simp
qed

lemma tanp_feasible:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1" and k1: "1 \<le> k" and L1: "1 \<le> L"
  shows "tanp u \<in> feasible k L 0"
  unfolding feasible_def
  using tanp_psd[OF u1] tanp_eigen_ub[OF L1, of u]
    tanp_eigen_lb[OF k1, of u]
  by (simp add: matrix_vector_mult_0_right)

lemma tanp_sconstraint:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1" and k1: "1 \<le> k" and L1: "1 \<le> L"
  shows "tanp u \<in> sconstraint k L"
  using tanp_feasible[OF u1 k1 L1] feasible_subset_sconstraint by blast

lemma outerp_sq: "outerp u ** outerp u = (u \<bullet> u) *\<^sub>R outerp u"
proof -
  have "(outerp u ** outerp u) $ i $ j = ((u \<bullet> u) *\<^sub>R outerp u) $ i $ j"
    for i j
  proof -
    have "(outerp u ** outerp u) $ i $ j
        = (\<Sum>l\<in>UNIV. (u $ i * u $ l) * (u $ l * u $ j))"
      by (simp add: outerp_def matrix_matrix_mult_def)
    also have "\<dots> = u $ i * u $ j * (\<Sum>l\<in>UNIV. u $ l * u $ l)"
      by (simp add: sum_distrib_left mult_ac)
    also have "\<dots> = ((u \<bullet> u) *\<^sub>R outerp u) $ i $ j"
      by (simp add: outerp_def inner_vec_def mult_ac)
    finally show ?thesis .
  qed
  then show ?thesis by (simp add: vec_eq_iff)
qed

lemma tanp_sq:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1"
  shows "tanp u ** tanp u = tanp u"
proof -
  have uu: "u \<bullet> u = 1"
    using u1 by (metis norm_eq_1)
  have "tanp u ** tanp u
      = mat 1 ** tanp u - outerp u ** tanp u"
    unfolding tanp_def by (rule matrix_msub_rdistrib)
  also have "mat 1 ** tanp u = tanp u" by (rule matrix_mul_lid)
  also have "outerp u ** tanp u
      = outerp u ** mat 1 - outerp u ** outerp u"
    unfolding tanp_def by (rule matrix_msub_ldistrib)
  also have "\<dots> = outerp u - outerp u"
    by (simp add: matrix_mul_rid outerp_sq uu)
  finally show ?thesis by (simp add: tanp_def)
qed

lemma tanp_trace:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1"
  shows "trace (tanp u) = real CARD('n) - 1"
proof -
  have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have tm: "trace (mat 1 :: real^'n^'n) = real CARD('n)"
    by (simp add: trace_def mat_def)
  have td: "trace (tanp u :: real^'n^'n)
      = trace (mat 1 :: real^'n^'n) - trace (outerp u)"
    unfolding tanp_def by (simp add: trace_def sum_subtractf)
  show ?thesis unfolding td tm trace_outerp uu by simp
qed

lemma tanp_kill:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u = 1" and par: "w = (norm w) *\<^sub>R u"
  shows "tanp u *v w = 0"
proof -
  have uu: "u \<bullet> u = 1" using u1 by (metis norm_eq_1)
  have "u \<bullet> w = u \<bullet> ((norm w) *\<^sub>R u)"
    by (rule arg_cong[where f = "\<lambda>v. u \<bullet> v", OF par])
  also have "\<dots> = norm w * (u \<bullet> u)"
    by (simp add: inner_scaleR_right)
  also have "\<dots> = norm w" using uu by simp
  finally have uw: "u \<bullet> w = norm w" .
  have "tanp u *v w = w - (u \<bullet> w) *\<^sub>R u" by (rule tanp_mv)
  also have "\<dots> = w - (norm w) *\<^sub>R u" using uw by simp
  also have "\<dots> = 0" using par by simp
  finally show ?thesis .
qed

subsubsection \<open>The guarded unit radial and the clamped field\<close>

definition uvec :: "real^'n::finite \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n"
  where "uvec y\<^sub>0 \<rho> w = (1 / max \<rho> (norm (w - y\<^sub>0))) *\<^sub>R (w - y\<^sub>0)"

lemma uvec_unit:
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (w - y\<^sub>0)"
  shows "norm (uvec y\<^sub>0 \<rho> w) = 1"
proof -
  have mx: "max \<rho> (norm (w - y\<^sub>0)) = norm (w - y\<^sub>0)"
    using far by (simp add: max_def)
  have n0: "norm (w - y\<^sub>0) \<noteq> 0" using rho0 far by linarith
  show ?thesis unfolding uvec_def mx using n0 by simp
qed

lemma uvec_norm_le:
  assumes rho0: "0 < \<rho>"
  shows "norm (uvec y\<^sub>0 \<rho> w) \<le> 1"
proof -
  have mx0: "0 < max \<rho> (norm (w - y\<^sub>0))" using rho0 by simp
  have le: "norm (w - y\<^sub>0) \<le> max \<rho> (norm (w - y\<^sub>0))" by simp
  have "norm (uvec y\<^sub>0 \<rho> w)
      = norm (w - y\<^sub>0) / max \<rho> (norm (w - y\<^sub>0))"
    unfolding uvec_def using mx0 by simp
  also have "\<dots> \<le> 1" using mx0 le by (simp add: divide_le_eq_1)
  finally show ?thesis .
qed

lemma uvec_par:
  assumes rho0: "0 < \<rho>" and far: "\<rho> \<le> norm (w - y\<^sub>0)"
  shows "w - y\<^sub>0 = norm (w - y\<^sub>0) *\<^sub>R uvec y\<^sub>0 \<rho> w"
proof -
  have mx: "max \<rho> (norm (w - y\<^sub>0)) = norm (w - y\<^sub>0)"
    using far by (simp add: max_def)
  have n0: "norm (w - y\<^sub>0) \<noteq> 0" using rho0 far by linarith
  show ?thesis unfolding uvec_def mx using n0 by simp
qed

lemma uvec_cont:
  fixes y\<^sub>0 :: "real^'n::finite"
  assumes rho0: "0 < \<rho>"
  shows "continuous_on UNIV (uvec y\<^sub>0 \<rho>)"
proof -
  have nz: "\<And>w :: real^'n. max \<rho> (norm (w - y\<^sub>0)) \<noteq> 0"
    using rho0 by simp
  show ?thesis
    unfolding uvec_def
    by (intro continuous_intros) (use nz in simp_all)
qed

definition tanSF ::
  "real^'n::finite \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  where "tanSF y\<^sub>0 \<rho> x rb z
    = tanp (uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z))"

theorem tanSF_package:
  fixes y\<^sub>0 x :: "real^'n::finite" and \<rho> rb :: real
  assumes rho0: "0 < \<rho>" and rb0: "0 \<le> rb"
    and sep: "\<rho> + rb \<le> dist x y\<^sub>0"
    and k1: "1 \<le> k" and kn: "k < CARD('n)" and L1: "1 \<le> L"
  shows tanSF_cont: "continuous_on UNIV (tanSF y\<^sub>0 \<rho> x rb)"
    and tanSF_sconstraint: "\<And>z. tanSF y\<^sub>0 \<rho> x rb z
        ** transpose (tanSF y\<^sub>0 \<rho> x rb z) \<in> sconstraint k L"
    and tanSF_kill: "\<And>z c. transpose (tanSF y\<^sub>0 \<rho> x rb z)
        *v (c *\<^sub>R (x - y\<^sub>0) + (c *\<^sub>R mat 1)
            *v (closest_point (cball x rb) z - x)) = 0"
    and tanSF_trace: "\<And>z. trace (tanSF y\<^sub>0 \<rho> x rb z
        ** transpose (tanSF y\<^sub>0 \<rho> x rb z)) = real CARD('n) - 1"
proof -
  have cin: "closest_point (cball x rb) z \<in> cball x rb" for z
    by (rule closest_point_in_set) (use rb0 in \<open>auto simp: closed_cball\<close>)
  have far: "\<rho> \<le> norm (closest_point (cball x rb) z - y\<^sub>0)" for z
  proof -
    have "dist (closest_point (cball x rb) z) x \<le> rb"
      using cin[of z] by (simp add: mem_cball dist_commute)
    moreover have "dist x y\<^sub>0
        \<le> dist x (closest_point (cball x rb) z)
          + dist (closest_point (cball x rb) z) y\<^sub>0"
      by (rule dist_triangle)
    ultimately have "\<rho> \<le> dist (closest_point (cball x rb) z) y\<^sub>0"
      using sep by (simp add: dist_commute)
    then show ?thesis by (simp add: dist_norm)
  qed
  have unit: "norm (uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z)) = 1" for z
    by (rule uvec_unit[OF rho0 far])
  show "continuous_on UNIV (tanSF y\<^sub>0 \<rho> x rb)"
  proof -
    have cpc: "continuous_on UNIV (closest_point (cball x rb))"
      by (rule continuous_on_closest_point)
        (use rb0 in \<open>auto simp: convex_cball closed_cball\<close>)
    have uc: "continuous_on UNIV
        (\<lambda>z. uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z))"
      by (rule continuous_on_compose2[OF uvec_cont[OF rho0] cpc]) auto
    have ci: "continuous_on UNIV
        (\<lambda>z. uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z) $ i)" for i
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF bounded_linear_vec_nth] uc]) auto
    have eq: "tanSF y\<^sub>0 \<rho> x rb = (\<lambda>z. \<chi> i j.
        (if i = j then 1 else 0)
        - uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z) $ i
          * uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z) $ j)"
      by (rule ext)
        (simp add: tanSF_def tanp_def outerp_def mat_def vec_eq_iff)
    show ?thesis unfolding eq
      by (intro continuous_on_vec_lambda continuous_intros ci)
  qed
  have sq: "tanSF y\<^sub>0 \<rho> x rb z ** transpose (tanSF y\<^sub>0 \<rho> x rb z)
      = tanSF y\<^sub>0 \<rho> x rb z" for z
    unfolding tanSF_def
    by (simp add: tanp_sym tanp_sq[OF unit])
  show "tanSF y\<^sub>0 \<rho> x rb z ** transpose (tanSF y\<^sub>0 \<rho> x rb z)
      \<in> sconstraint k L" for z
    unfolding sq unfolding tanSF_def
    by (rule tanp_sconstraint[OF uvec_norm_le[OF rho0] k1 L1])
  show "transpose (tanSF y\<^sub>0 \<rho> x rb z)
      *v (c *\<^sub>R (x - y\<^sub>0) + (c *\<^sub>R mat 1)
          *v (closest_point (cball x rb) z - x)) = 0" for z c
  proof -
    have arg: "c *\<^sub>R (x - y\<^sub>0) + (c *\<^sub>R mat 1)
        *v (closest_point (cball x rb) z - x)
        = c *\<^sub>R (closest_point (cball x rb) z - y\<^sub>0)"
      by (simp add: scaleR_matrix_vector matrix_vector_mul_lid
          scaleR_right_diff_distrib scaleR_add_right)
    have k0: "tanp (uvec y\<^sub>0 \<rho> (closest_point (cball x rb) z))
        *v (closest_point (cball x rb) z - y\<^sub>0) = 0"
      by (rule tanp_kill[OF unit uvec_par[OF rho0 far]])
    have "transpose (tanSF y\<^sub>0 \<rho> x rb z)
        *v (c *\<^sub>R (closest_point (cball x rb) z - y\<^sub>0))
        = c *\<^sub>R (tanSF y\<^sub>0 \<rho> x rb z
            *v (closest_point (cball x rb) z - y\<^sub>0))"
      unfolding tanSF_def tanp_sym
      by (simp add: matrix_vector_mult_scaleR)
    also have "\<dots> = 0" unfolding tanSF_def using k0 by simp
    finally show ?thesis unfolding arg .
  qed
  show "trace (tanSF y\<^sub>0 \<rho> x rb z
      ** transpose (tanSF y\<^sub>0 \<rho> x rb z)) = real CARD('n) - 1" for z
    unfolding sq unfolding tanSF_def by (rule tanp_trace[OF unit])
qed

subsection \<open>Conditional orthogonality: the kill checked at the point\<close>

text \<open>Batch 4d(i).  The Euler increments annihilate a continuous field
  WHEREVER the field is killed by the volatility --- the kill condition
  moves from a global hypothesis into the conclusion, checked at each
  grid point.  This is what lets a field be tangential only away from
  its singular centre: the growth telescope only ever uses
  orthogonality at grid points inside the good region, where the kill
  holds.  The proof is the committed induction of
  @{thm [source] eulerp_orth_increments} with the implication carried
  through the glue.\<close>

lemma euOrth_mset_cond:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n"
    and G :: "real^'n \<Rightarrow> real^'n" and h :: real
  assumes SFc: "continuous_on UNIV SF" and Gc: "continuous_on UNIV G"
  shows "{\<omega> \<in> space (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))).
      \<forall>j<m. transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
    \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have evm: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> ?B \<rightarrow>\<^sub>M borel" for u
    by (rule pair_law_eval_measurable[OF refl])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF
        continuous_on_fst[OF continuous_on_id]])
  have evf: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u)) \<in> ?B \<rightarrow>\<^sub>M borel" for u
    by (rule measurable_compose[OF evm mfst])
  have condm: "(\<lambda>\<omega> :: 'n pairpath.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h)))) \<in> ?B \<rightarrow>\<^sub>M borel" for j
  proof -
    have c: "continuous_on UNIV (\<lambda>w :: real^'n. transpose (SF w) *v G w)"
    proof -
      have ct: "continuous_on UNIV (\<lambda>w :: real^'n. transpose (SF w))"
      proof -
        have e: "(\<lambda>w :: real^'n. transpose (SF w))
            = (\<lambda>w. \<chi> i j. SF w $ j $ i)"
          by (rule ext) (simp add: transpose_def)
        have entry: "continuous_on UNIV (\<lambda>w :: real^'n. SF w $ j $ i)"
          for i j
        proof -
          have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ j $ i)"
            using bounded_linear_vec_nth bounded_linear_compose by blast
          show ?thesis
            by (rule continuous_on_compose2[OF
                linear_continuous_on[OF bl] SFc]) auto
        qed
        show ?thesis unfolding e
          by (intro continuous_on_vec_lambda entry)
      qed
      have prodc: "continuous_on UNIV (\<lambda>w :: real^'n.
          transpose (SF w) *v G w)"
      proof -
        have e: "(\<lambda>w :: real^'n. transpose (SF w) *v G w)
            = (\<lambda>w. \<chi> i. (\<Sum>l\<in>UNIV. transpose (SF w) $ i $ l * G w $ l))"
          by (rule ext) (simp add: matrix_vector_mult_def)
        have entry: "continuous_on UNIV (\<lambda>w :: real^'n.
            \<Sum>l\<in>UNIV. transpose (SF w) $ i $ l * G w $ l)" for i
        proof -
          have tc: "continuous_on UNIV
              (\<lambda>w :: real^'n. transpose (SF w) $ i $ l)" for l
          proof -
            have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ l)"
              using bounded_linear_vec_nth bounded_linear_compose by blast
            show ?thesis
              by (rule continuous_on_compose2[OF
                  linear_continuous_on[OF bl] ct]) auto
          qed
          have gc: "continuous_on UNIV (\<lambda>w :: real^'n. G w $ l)" for l
            by (rule continuous_on_compose2[OF
                linear_continuous_on[OF bounded_linear_vec_nth] Gc]) auto
          show ?thesis
            by (intro continuous_on_sum continuous_on_mult tc gc)
        qed
        show ?thesis unfolding e
          by (intro continuous_on_vec_lambda entry)
      qed
      show ?thesis by (rule prodc)
    qed
    show ?thesis
      by (rule measurable_compose[OF evf
          borel_measurable_continuous_onI[OF c]])
  qed
  have orthm: "(\<lambda>\<omega> :: 'n pairpath.
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
      \<in> ?B \<rightarrow>\<^sub>M borel" for j
  proof -
    have gc: "(\<lambda>\<omega> :: 'n pairpath. G (fst (\<omega> (real j * h))))
        \<in> ?B \<rightarrow>\<^sub>M borel"
      by (rule measurable_compose[OF evf
          borel_measurable_continuous_onI[OF Gc]])
    have dc: "(\<lambda>\<omega> :: 'n pairpath.
        fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h)))
        \<in> ?B \<rightarrow>\<^sub>M borel"
      by (intro borel_measurable_diff evf)
    show ?thesis by (intro borel_measurable_inner gc dc)
  qed
  have per: "{\<omega> \<in> space ?B.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets ?B" for j
  proof -
    have cset: "{\<omega> \<in> space ?B.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B.
          transpose (SF (fst (\<omega> (real j * h))))
            *v G (fst (\<omega> (real j * h))) = 0}
          = (\<lambda>\<omega> :: 'n pairpath.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h)))) -` {0} \<inter> space ?B"
        by auto
      then show ?thesis
        using measurable_sets[OF condm[of j], of "{0}"]
        by (simp add: borel_closed)
    qed
    have oset: "{\<omega> \<in> space ?B.
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B.
          G (fst (\<omega> (real j * h))) \<bullet>
            (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          = (\<lambda>\<omega> :: 'n pairpath.
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))))
            -` {0} \<inter> space ?B"
        by auto
      then show ?thesis
        using measurable_sets[OF orthm[of j], of "{0}"]
        by (simp add: borel_closed)
    qed
    have eq: "{\<omega> \<in> space ?B.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = (space ?B - {\<omega> \<in> space ?B.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h))) = 0})
          \<union> {\<omega> \<in> space ?B.
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}"
      by auto
    show ?thesis unfolding eq
      by (intro sets.Un sets.Diff sets.top cset oset)
  qed
  show ?thesis
  proof (induction m)
    case 0
    show ?case by simp
  next
    case (Suc m)
    have eq: "{\<omega> \<in> space ?B. \<forall>j<Suc m.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
        = {\<omega> \<in> space ?B. \<forall>j<m.
            transpose (SF (fst (\<omega> (real j * h))))
              *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
            G (fst (\<omega> (real j * h))) \<bullet>
              (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
          \<inter> {\<omega> \<in> space ?B.
            transpose (SF (fst (\<omega> (real m * h))))
              *v G (fst (\<omega> (real m * h))) = 0 \<longrightarrow>
            G (fst (\<omega> (real m * h))) \<bullet>
              (fst (\<omega> (real (Suc m) * h)) - fst (\<omega> (real m * h))) = 0}"
      by (auto simp: less_Suc_eq)
    show ?case unfolding eq by (intro sets.Int Suc.IH per)
  qed
qed

theorem eulerp_orth_increments_cond:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and G :: "real^'n \<Rightarrow> real^'n"
    and x :: "real^'n" and h :: real
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and Gc: "continuous_on UNIV G"
  shows "AE \<omega> in eulerp SF x h N. \<forall>j<Suc N.
      transpose (SF (fst (\<omega> (real j * h))))
        *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (\<omega> (real j * h))) \<bullet>
        (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
proof (induction N)
  case 0
  have h0': "(0::real) \<le> h" using h0 by simp
  let ?\<mu>0 = "pair_law_of h (sbmpair (SF x) h)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  have E0: "eulerp SF x h 0 = pshift_law h x ?\<mu>0" by simp
  have sets\<mu>: "sets ?\<mu>0 = sets (borel_of (mtopology_of
      (path_metric h :: ('n pairpath) metric)))" by simp
  have st: "AE \<omega> in ?\<mu>0. fst (\<omega> 0) = (0 :: real^'n)"
    using sbmpair_law_start[OF h0', of "SF x"]
    by (rule eventually_mono) simp
  have orth0: "AE \<omega> in ?\<mu>0. transpose (SF x) *v G x = 0 \<longrightarrow>
      G x \<bullet> (fst (\<omega> h) - fst (\<omega> 0)) = 0"
  proof (cases "transpose (SF x) *v G x = 0")
    case True
    have "AE \<omega> in ?\<mu>0. G x \<bullet> (fst (\<omega> h) - fst (\<omega> 0)) = 0"
      by (rule sbm_orth_increment[OF h0' True])
    then show ?thesis by (rule eventually_mono) simp
  next
    case False
    then show ?thesis by simp
  qed
  have ae: "AE \<omega> in ?\<mu>0. \<forall>j<Suc 0.
      transpose (SF (fst (pshift h x \<omega> (real j * h))))
        *v G (fst (pshift h x \<omega> (real j * h))) = 0 \<longrightarrow>
      G (fst (pshift h x \<omega> (real j * h))) \<bullet>
        (fst (pshift h x \<omega> (real (Suc j) * h))
          - fst (pshift h x \<omega> (real j * h))) = 0"
    using st orth0
  proof eventually_elim
    case (elim \<omega>)
    have m1: "h \<in> {0..h}" and m2: "(0::real) \<in> {0..h}"
      using h0' by simp_all
    show ?case using elim
      by (simp add: pshift_fst[OF m1] pshift_fst[OF m2])
  qed
  show ?case unfolding E0 by (rule AE_pshift_law[OF h0' sets\<mu> ae])
next
  case (Suc N)
  have h0': "(0::real) \<le> h" using h0 by simp
  define r where "r = real (Suc N) * h"
  define T' where "T' = real (Suc (Suc N)) * h"
  let ?Q = "eulerp SF x h N"
  let ?Br = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?MR = "borel_of (mtopology_of
      (path_metric (T' - r) :: ('n pairpath) metric))"
  let ?K = "\<lambda>\<omega> :: 'n pairpath.
      pair_law_of h (sbmpair (SF (fst (\<omega> r))) h) bm_paths"
  have hT: "T' - r = h" unfolding r_def T'_def by (simp add: algebra_simps)
  have r0: "0 \<le> r" unfolding r_def using h0' by simp
  have rleT: "r \<le> T'" unfolding r_def T'_def
    using h0' by (intro mult_right_mono) simp_all
  have Qc: "?Q \<in> paper_pair_class k L r x"
    unfolding r_def by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  have PQ: "prob_space ?Q" by (rule paper_pair_class_prob[OF Qc])
  have setsQ: "sets ?Q = sets ?Br" by (rule paper_pair_class_sets[OF Qc])
  note pack = sbm_kernel_package[OF h0 L1 SFc SFs]
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have Kp: "?K \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding hT by (rule measurable_compose[OF eQ pack(1)])
  have Ee: "eulerp SF x h (Suc N) = kglue_law' r T' ?K ?Q"
    by (simp add: r_def T'_def)
  have msetP: "{\<omega> \<in> mspace (path_metric T' :: ('n pairpath) metric).
      \<forall>j<Suc (Suc N).
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0}
      \<in> sets (borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric)))"
  proof -
    have spB: "space (borel_of (mtopology_of
        (path_metric T' :: ('n pairpath) metric)))
        = mspace (path_metric T' :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF refl])
    show ?thesis
      using euOrth_mset_cond[OF SFc Gc,
          where h = h and T = T' and m = "Suc (Suc N)"]
      unfolding spB .
  qed
  show ?case
    unfolding Ee
  proof (rule Paper_Bridge.AE_kglue_law'[OF r0 rleT PQ setsQ Kp msetP])
    show "AE \<omega> in ?Q. \<forall>j<Suc N.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
      by (rule Suc.IH)
    show "AE \<omega>' in ?K \<omega>.
        transpose (SF (fst (\<omega> r))) *v G (fst (\<omega> r)) = 0 \<longrightarrow>
        G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
      if "\<omega> \<in> space ?Q" for \<omega> :: "'n pairpath"
    proof (cases "transpose (SF (fst (\<omega> r))) *v G (fst (\<omega> r)) = 0")
      case True
      have "AE \<omega>' in ?K \<omega>. G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
        by (rule sbm_orth_increment[OF h0' True])
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by simp
    qed
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T' - r) :: ('n pairpath) metric)"
      and A: "\<forall>j<Suc N.
        transpose (SF (fst (\<omega> (real j * h))))
          *v G (fst (\<omega> (real j * h))) = 0 \<longrightarrow>
        G (fst (\<omega> (real j * h))) \<bullet>
          (fst (\<omega> (real (Suc j) * h)) - fst (\<omega> (real j * h))) = 0"
      and B: "transpose (SF (fst (\<omega> r))) *v G (fst (\<omega> r)) = 0 \<longrightarrow>
        G (fst (\<omega> r)) \<bullet> (fst (\<omega>' h) - fst (\<omega>' 0)) = 0"
    have mem: "real j * h \<in> {0..T'}" if le: "j \<le> Suc (Suc N)" for j
    proof -
      have a: "0 \<le> real j * h"
        by (intro mult_nonneg_nonneg h0') simp_all
      have b: "real j * h \<le> T'" unfolding T'_def
        using le h0' by (intro mult_right_mono) simp_all
      show ?thesis using a b by simp
    qed
    have prefl: "pglue r T' \<omega> \<omega>' (real j * h) = \<omega> (real j * h)"
      if j: "j \<le> Suc N" for j
    proof (rule pglue_le)
      show "real j * h \<in> {0..T'}" using j by (intro mem) simp
      show "real j * h \<le> r" unfolding r_def
        using j h0' by (intro mult_right_mono) simp_all
    qed
    have Tmem: "T' \<in> {0..T'}"
      using mem[of "Suc (Suc N)"] unfolding T'_def by simp
    have gT: "pglue r T' \<omega> \<omega>' T' = \<omega> r + (\<omega>' (T' - r) - \<omega>' 0)"
      by (rule pglue_ge[OF Tmem rleT])
    have gr: "pglue r T' \<omega> \<omega>' r = \<omega> r"
      using prefl[of "Suc N"] unfolding r_def by simp
    show "\<forall>j<Suc (Suc N).
        transpose (SF (fst (pglue r T' \<omega> \<omega>' (real j * h))))
          *v G (fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0 \<longrightarrow>
        G (fst (pglue r T' \<omega> \<omega>' (real j * h))) \<bullet>
          (fst (pglue r T' \<omega> \<omega>' (real (Suc j) * h))
            - fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
    proof (intro allI impI)
      fix j assume jle: "j < Suc (Suc N)"
        and cnd: "transpose (SF (fst (pglue r T' \<omega> \<omega>' (real j * h))))
          *v G (fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
      show "G (fst (pglue r T' \<omega> \<omega>' (real j * h))) \<bullet>
          (fst (pglue r T' \<omega> \<omega>' (real (Suc j) * h))
            - fst (pglue r T' \<omega> \<omega>' (real j * h))) = 0"
      proof (cases "j < Suc N")
        case True
        then have j1: "Suc j \<le> Suc N" and j2: "j \<le> Suc N" by simp_all
        show ?thesis
          using A True cnd by (simp only: prefl[OF j1] prefl[OF j2])
      next
        case False
        with jle have jeq: "j = Suc N" by simp
        have e1: "real (Suc j) * h = T'" unfolding jeq T'_def by (rule refl)
        have e2: "real j * h = r" unfolding jeq r_def by (rule refl)
        show ?thesis
          using B cnd unfolding e1 e2 gT gr hT by simp
      qed
    qed
  qed
qed

subsection \<open>The growth telescope on an arbitrary region\<close>

text \<open>Batch 4d(ii).  The exact quadratic lower bound of
  @{thm [source] eulerp_quad_lower}, with the confinement region
  decoupled from the start-centred clamp: the kill and the trace margin
  are only assumed ON the region, and the conclusion holds on the event
  that the grid stays there.  The conditional orthogonality
  (@{thm [source] eulerp_orth_increments_cond}) checks the kill at each
  grid point, so no clamp and no global hypothesis are needed.  This is
  the form the tangential field of Case 2 can feed: tangential exactly
  on an annulus around its centre, arbitrary elsewhere.\<close>

theorem eulerp_quad_lower_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and h cm :: real and R :: "(real^'n) set"
  assumes h0: "0 < h" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M"
    and kill: "\<And>z. z \<in> R \<Longrightarrow>
        transpose (SF z) *v (q + M *v (z - x)) = 0"
    and marg: "\<And>z. z \<in> R \<Longrightarrow>
        cm \<le> trace (M ** (SF z ** transpose (SF z)))"
  shows "AE \<omega> in eulerp SF x h N. \<forall>m\<le>Suc N.
      (\<forall>j<m. fst (\<omega> (real j * h)) \<in> R) \<longrightarrow>
      (1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
        \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
          + (1/2) * ((fst (\<omega> (real m * h)) - x)
              \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
proof -
  have Gc: "continuous_on UNIV (\<lambda>z :: real^'n. q + M *v (z - x))"
  proof -
    have d: "continuous_on UNIV (\<lambda>z :: real^'n. z - x)"
      by (intro continuous_intros)
    have mv: "continuous_on UNIV (\<lambda>z :: real^'n. M *v (z - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  note orth = eulerp_orth_increments_cond[OF h0 L1 SFc SFs Gc]
  have Qc: "eulerp SF x h N \<in> paper_pair_class k L (real (Suc N) * h) x"
    by (rule eulerp_in_class[OF h0 L1 SFc SFs])
  have st: "AE \<omega> in eulerp SF x h N. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Qc unfolding paper_pair_class_def by blast
  show ?thesis
    using orth st
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix m assume mle: "m \<le> Suc N"
        and inb: "\<forall>j<m. fst (\<omega> (real j * h)) \<in> R"
      define X where "X j = fst (\<omega> (real j * h))" for j
      define \<psi> where "\<psi> z = q \<bullet> (z - x)
          + (1/2) * ((z - x) \<bullet> (M *v (z - x)))" for z
      have x0: "X 0 = x" unfolding X_def using elim by simp
      have XR: "X j \<in> R" if j: "j < m" for j
        using inb j unfolding X_def by blast
      have step: "\<psi> (X (Suc j)) - \<psi> (X j)
          = (1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))"
        if j: "j < m" for j
      proof -
        have jN: "j < Suc N" using j mle by simp
        have cnd: "transpose (SF (X j)) *v (q + M *v (X j - x)) = 0"
          by (rule kill[OF XR[OF j]])
        have k0: "(q + M *v (X j - x)) \<bullet> (X (Suc j) - X j) = 0"
          using elim(1) jN cnd unfolding X_def by metis
        have "\<psi> (X (Suc j)) - \<psi> (X j)
            = (q + M *v (X j - x)) \<bullet> (X (Suc j) - X j)
              + (1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))"
          unfolding \<psi>_def by (rule quad_taylor_step[OF sym])
        then show ?thesis using k0 by simp
      qed
      have tele: "\<psi> (X m) - \<psi> (X 0)
          = (\<Sum>j<m. \<psi> (X (Suc j)) - \<psi> (X j))"
        by (rule sum_lessThan_telescope[symmetric])
      have quadsum: "\<psi> (X m) - \<psi> (X 0)
          = (\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
              \<bullet> (M *v (X (Suc j) - X j))))"
        unfolding tele
        by (rule sum.cong[OF refl]) (use step in simp)
      have perj: "(1/2) * ((X (Suc j) - X j) \<bullet> (M *v (X (Suc j) - X j)))
          = (1/2) * (trace (M ** (outerp (X (Suc j) - X j)
              - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            + h * trace (M ** (SF (X j) ** transpose (SF (X j)))))" for j
      proof -
        have "trace (M ** (outerp (X (Suc j) - X j)
            - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            = trace (M ** outerp (X (Suc j) - X j))
              - h * trace (M ** (SF (X j) ** transpose (SF (X j))))"
          by (simp add: trace_mult_diff matmul_scaleR_right trace_scaleR)
        then show ?thesis by (simp add: trace_mult_outerp)
      qed
      have persum: "(\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
            \<bullet> (M *v (X (Suc j) - X j))))
          = (1/2) * euXi SF M h m \<omega>
            + (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
      proof -
        have "(\<Sum>j<m. (1/2) * ((X (Suc j) - X j)
              \<bullet> (M *v (X (Suc j) - X j))))
            = (\<Sum>j<m. (1/2) * (trace (M ** (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
              + h * trace (M ** (SF (X j) ** transpose (SF (X j))))))"
          by (rule sum.cong[OF refl]) (rule perj)
        also have "\<dots> = (\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j)))))
            + (h/2) * trace (M ** (SF (X j) ** transpose (SF (X j)))))"
          by (rule sum.cong[OF refl]) (simp add: field_simps)
        also have "\<dots> = (\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            + (\<Sum>j<m. (h/2) * trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
          by (rule sum.distrib)
        also have "(\<Sum>j<m. (1/2) * trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            = (1/2) * (\<Sum>j<m. trace (M **
              (outerp (X (Suc j) - X j)
                - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))"
          by (rule sum_distrib_left[symmetric])
        also have "(\<Sum>j<m. (h/2) * trace (M ** (SF (X j)
              ** transpose (SF (X j)))))
            = (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
                ** transpose (SF (X j)))))"
          by (rule sum_distrib_left[symmetric])
        also have "(\<Sum>j<m. trace (M ** (outerp (X (Suc j) - X j)
              - h *\<^sub>R (SF (X j) ** transpose (SF (X j))))))
            = euXi SF M h m \<omega>"
          unfolding euXi_def X_def by (rule refl)
        finally show ?thesis .
      qed
      have margsum: "real m * cm
          \<le> (\<Sum>j<m. trace (M ** (SF (X j) ** transpose (SF (X j)))))"
      proof -
        have "real m * cm = (\<Sum>j\<in>{..<m}. cm)" by simp
        also have "\<dots> \<le> (\<Sum>j<m. trace (M ** (SF (X j)
            ** transpose (SF (X j)))))"
        proof (rule sum_mono)
          fix j assume "j \<in> {..<m}"
          then have "X j \<in> R" by (intro XR) simp
          then show "cm \<le> trace (M ** (SF (X j) ** transpose (SF (X j))))"
            by (rule marg)
        qed
        finally show ?thesis .
      qed
      have psi0: "\<psi> (X 0) = 0" unfolding \<psi>_def x0 by simp
      have hm: "(h/2) * (real m * cm)
          \<le> (h/2) * (\<Sum>j<m. trace (M ** (SF (X j)
              ** transpose (SF (X j)))))"
        using h0 margsum by (intro mult_left_mono) simp_all
      have ee: "real m * h * cm / 2 = (h/2) * (real m * cm)" by simp
      have main: "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
          \<le> \<psi> (X m)"
        using quadsum persum psi0 hm ee by linarith
      show "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
          \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
            + (1/2) * ((fst (\<omega> (real m * h)) - x)
                \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
        using main unfolding \<psi>_def X_def .
    qed
  qed
qed

subsection \<open>Region variants of the Lipschitz bound and the open event\<close>

text \<open>Batch 4d(iii).  Two committed Case-1 lemmas, re-stated with the
  confinement region decoupled from the quadratic's centre.  The
  Lipschitz bound needs only the two norm bounds, and the bad event
  stays open for ANY open region: the stay-condition and the quadratic
  no longer share a centre.  These feed the region versions of the
  vanishing-probability and limit theorems.\<close>

lemma quad_diff_bound_gen:
  fixes M :: "real^'n::finite^'n" and q x a b :: "real^'n" and R :: real
  assumes sym: "transpose M = M"
    and na: "norm (a - x) \<le> R" and nb: "norm (b - x) \<le> R"
  shows "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
       - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> (norm q + 2 * (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>) * R)
          * norm (b - a)"
proof -
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have dble: "norm (b - a) \<le> 2 * R"
  proof -
    have deq: "b - a = (b - x) + (x - a)" by simp
    have "norm (b - a) \<le> norm (b - x) + norm (x - a)"
      by (subst deq) (rule norm_triangle_ineq)
    moreover have "norm (x - a) \<le> R"
      using na by (simp add: norm_minus_commute)
    ultimately show ?thesis using nb by linarith
  qed
  have step: "q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))
      = (q + M *v (a - x)) \<bullet> (b - a)
        + (1/2) * ((b - a) \<bullet> (M *v (b - a)))"
    by (rule quad_taylor_step[OF sym])
  have t1: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
      \<le> (norm q + ?CM * R) * norm (b - a)"
  proof -
    have cs: "\<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        \<le> norm (q + M *v (a - x)) * norm (b - a)"
      by (rule Cauchy_Schwarz_ineq2)
    have "norm (q + M *v (a - x)) \<le> norm q + ?CM * R"
    proof -
      have "norm (q + M *v (a - x)) \<le> norm q + norm (M *v (a - x))"
        by (rule norm_triangle_ineq)
      moreover have "norm (M *v (a - x)) \<le> ?CM * norm (a - x)"
        by (rule matvec_norm_le)
      moreover have "?CM * norm (a - x) \<le> ?CM * R"
        by (rule mult_left_mono[OF na CM0])
      ultimately show ?thesis by linarith
    qed
    then have "norm (q + M *v (a - x)) * norm (b - a)
        \<le> (norm q + ?CM * R) * norm (b - a)"
      by (rule mult_right_mono) simp
    then show ?thesis using cs by linarith
  qed
  have t2: "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
      \<le> ?CM * R * norm (b - a)"
  proof -
    have "\<bar>(b - a) \<bullet> (M *v (b - a))\<bar>
        \<le> norm (b - a) * norm (M *v (b - a))"
      by (rule Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> norm (b - a) * (?CM * norm (b - a))"
      by (rule mult_left_mono[OF matvec_norm_le norm_ge_zero])
    finally have h: "\<bar>(b - a) \<bullet> (M *v (b - a))\<bar>
        \<le> ?CM * norm (b - a) * norm (b - a)"
      by (simp add: mult_ac)
    have h2: "?CM * norm (b - a) * norm (b - a)
        \<le> ?CM * (2 * R) * norm (b - a)"
      by (rule mult_right_mono[OF mult_left_mono[OF dble CM0] norm_ge_zero])
    have "\<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>
        = (1/2) * \<bar>(b - a) \<bullet> (M *v (b - a))\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> (1/2) * (?CM * (2 * R) * norm (b - a))"
      using h h2 by linarith
    also have "\<dots> = ?CM * R * norm (b - a)" by simp
    finally show ?thesis .
  qed
  have tri: "\<bar>q \<bullet> (b - x) + (1/2) * ((b - x) \<bullet> (M *v (b - x)))
      - (q \<bullet> (a - x) + (1/2) * ((a - x) \<bullet> (M *v (a - x))))\<bar>
      \<le> \<bar>(q + M *v (a - x)) \<bullet> (b - a)\<bar>
        + \<bar>(1/2) * ((b - a) \<bullet> (M *v (b - a)))\<bar>"
    unfolding step by (rule abs_triangle_ineq)
  have fin: "(norm q + ?CM * R) * norm (b - a)
      + ?CM * R * norm (b - a)
      = (norm q + 2 * ?CM * R) * norm (b - a)"
    by (simp add: algebra_simps)
  show ?thesis using tri t1 t2 fin by linarith
qed

lemma open_quad_bad_event_region:
  fixes x q :: "real^'n::finite" and M :: "real^'n^'n"
    and t T thr :: real and RO :: "(real^'n) set"
  assumes t0: "0 \<le> t" and tT: "t \<le> T" and RO: "open RO"
  shows "openin (mtopology_of (path_metric T :: ('n pairpath) metric))
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}"
proof -
  have T0: "0 \<le> T" using t0 tT by linarith
  let ?pm = "path_metric T :: ('n pairpath) metric"
  have o1: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` RO}"
    by (rule open_stay_inside[OF T0 open_vimage_fst[OF RO] t0 tT])
  have c0: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p - x)"
    by (intro continuous_intros)
  have c1: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). M *v (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF matvec_blin] c0]) auto
  have cq: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). q \<bullet> (fst p - x))"
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_inner_right] c0]) auto
  have cin: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        (fst p - x) \<bullet> (M *v (fst p - x)))"
    by (rule bounded_bilinear.continuous_on[OF bounded_bilinear_inner c0 c1])
  have contf: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n).
        q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))))"
    by (intro continuous_on_add continuous_on_mult
        continuous_on_const cq cin)
  have oU: "open {p :: (real^'n) \<times> (real^'n^'n).
      q \<bullet> (fst p - x) + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}"
    by (rule open_Collect_less[OF contf continuous_on_const])
  have o2: "openin (mtopology_of ?pm)
      {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
        + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by (rule open_eval_preimage[OF _ oU]) (use t0 tT in simp)
  have eq: "{\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x))) < thr}
      = {\<omega> \<in> mspace ?pm. \<forall>s\<in>{0..t}. \<omega> s \<in> fst -` RO}
        \<inter> {\<omega> \<in> mspace ?pm. \<omega> t \<in> {p. q \<bullet> (fst p - x)
          + (1/2) * ((fst p - x) \<bullet> (M *v (fst p - x))) < thr}}"
    by auto
  show ?thesis unfolding eq by (rule openin_Int[OF o1 o2])
qed

subsection \<open>The bad event vanishes on a region\<close>

text \<open>Batch 4d(iv).  The vanishing-probability theorem of
  @{thm [source] eulerp_bad_event_null}, over an arbitrary bounded open
  stay-region: the kill and the trace margin hold on the region, the
  region is contained in a ball of radius \<open>Rn\<close> around the quadratic's
  centre, and the same Chebyshev-plus-gap dissection gives the
  \<open>A h + B h\<^sup>2\<close> bound once the mesh is fine.\<close>

theorem eulerp_bad_event_null_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M :: "real^'n^'n"
    and q x :: "real^'n" and c cm t \<beta> Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym: "transpose M = M"
    and ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
    and kill: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q + M *v (z - x)) = 0"
    and marg: "\<And>z. z \<in> RO \<Longrightarrow>
        cm \<le> trace (M ** (SF z ** transpose (SF z)))"
    and t0: "0 < t" and tc: "t \<le> c" and b0: "0 < \<beta>"
  shows "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
      {\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric).
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
        \<and> q \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
          < t * cm / 2 - \<beta>}) \<longlonglongrightarrow> 0"
proof -
  let ?U = "{\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric).
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO)
      \<and> q \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
        < t * cm / 2 - \<beta>}"
  let ?h = "\<lambda>i. c / real (Suc i)"
  let ?CM = "\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>"
  define C\<psi> where "C\<psi> = norm q + 2 * ?CM * Rn + 1"
  define \<delta> where "\<delta> = \<beta> / (4 * C\<psi>)"
  define h\<^sub>0 where "h\<^sub>0 = \<beta> / (2 * (\<bar>cm\<bar> + 1))"
  define A where "A = 4 * c * xiC M L / \<beta>\<^sup>2"
  define B where "B = real (CARD('n)) ^ 5 * 8 * L\<^sup>2 / \<delta>^4"
  have CM0: "0 \<le> ?CM" by (auto intro!: sum_nonneg)
  have Rn0: "0 \<le> Rn \<or> RO = {}"
  proof (cases "RO = {}")
    case False
    then obtain z where "z \<in> RO" by blast
    then have "0 \<le> Rn" using ROb norm_ge_zero order_trans by metis
    then show ?thesis by simp
  qed simp
  have C\<psi>1: "1 \<le> C\<psi> \<or> RO = {}"
  proof (cases "RO = {}")
    case False
    then have "0 \<le> Rn" using Rn0 by simp
    then have "0 \<le> 2 * ?CM * Rn"
      using CM0 by (auto intro!: mult_nonneg_nonneg)
    then have "1 \<le> C\<psi>"
      unfolding C\<psi>_def using norm_ge_zero[of q] by linarith
    then show ?thesis by simp
  qed simp
  show ?thesis
  proof (cases "RO = {}")
    case True
    have Ue: "?U = {}" unfolding True using t0 by auto
    show ?thesis unfolding Ue by simp
  next
    case ne: False
    have C\<psi>1': "1 \<le> C\<psi>" using C\<psi>1 ne by simp
    have C\<psi>0: "0 < C\<psi>" using C\<psi>1' by linarith
    have \<delta>0: "0 < \<delta>" unfolding \<delta>_def using b0 C\<psi>0 by simp
    have h\<^sub>00: "0 < h\<^sub>0" unfolding h\<^sub>0_def using b0 by simp
    have L0: "0 \<le> L" using L1 by linarith
    have bound: "measure (eulerp SF x (?h i) i) ?U
        \<le> A * ?h i + B * (?h i)\<^sup>2"
      if hs: "?h i \<le> h\<^sub>0" for i
    proof -
      define h where "h = ?h i"
      have hs': "h \<le> h\<^sub>0" using hs unfolding h_def .
      have h0: "0 < h" unfolding h_def using c0 by simp
      have hc: "real (Suc i) * h = c" unfolding h_def by simp
      let ?Q = "eulerp SF x h i"
      have Qc: "?Q \<in> paper_pair_class k L c x"
        unfolding h_def by (rule eulerp_seq_in_class[OF c0 L1 SFc SFs])
      have setsQ: "sets ?Q = sets (borel_of (mtopology_of
          (path_metric c :: ('n pairpath) metric)))"
        by (rule paper_pair_class_sets[OF Qc])
      have spQ: "space ?Q = mspace (path_metric c :: ('n pairpath) metric)"
        by (rule space_of_path_sets[OF setsQ])
      interpret PQ: prob_space ?Q by (rule paper_pair_class_prob[OF Qc])
      define m where "m = nat \<lfloor>t / h\<rfloor>"
      have tdh0: "0 \<le> t / h" using t0 h0 by simp
      have fl0: "0 \<le> \<lfloor>t / h\<rfloor>" using tdh0 by simp
      have mreal: "real m = real_of_int \<lfloor>t / h\<rfloor>"
        unfolding m_def using fl0 by (simp add: of_nat_nat)
      have mh_le: "real m * h \<le> t"
      proof -
        have "real_of_int \<lfloor>t / h\<rfloor> \<le> t / h" by (rule of_int_floor_le)
        then have "real m \<le> t / h" using mreal by simp
        then show ?thesis
          using h0 by (simp add: pos_le_divide_eq mult_ac)
      qed
      have mh0: "0 \<le> real m * h" using h0 by simp
      have t_mh: "t - real m * h \<le> h"
      proof -
        have "t / h < real_of_int \<lfloor>t / h\<rfloor> + 1"
          using floor_correct[of "t / h"] by linarith
        then have "t / h < real m + 1" using mreal by simp
        then have "t < (real m + 1) * h"
          using h0 by (simp add: pos_divide_less_eq)
        then show ?thesis by (simp add: algebra_simps)
      qed
      have mSuc: "m \<le> Suc i"
      proof -
        have "t / h \<le> real (Suc i)"
          using tc hc h0 by (simp add: pos_divide_le_eq mult_ac)
        then have "\<lfloor>t / h\<rfloor> \<le> int (Suc i)"
          by (simp add: floor_le_iff)
        then show ?thesis unfolding m_def by simp
      qed
      define E1 where "E1 = {\<omega> \<in> space ?Q. \<beta> / 2 \<le> \<bar>euXi SF M h m \<omega>\<bar>}"
      define E2 where "E2 = {\<omega> \<in> space ?Q.
          \<delta> \<le> norm (fst (\<omega> t) - fst (\<omega> (real m * h)))}"
      have b20: "0 < \<beta> / 2" using b0 by simp
      have mE1: "measure ?Q E1 \<le> real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2"
        unfolding E1_def
        by (rule eulerp_Xi_chebyshev[OF h0 L1 SFc SFs mSuc b20])
      have mE2: "measure ?Q E2
          \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4"
        unfolding E2_def
        by (rule paper_pair_class_increment_tail_norm[OF c0 L0 Qc
            mh0 mh_le tc \<delta>0])
      have sE1: "E1 \<in> sets ?Q"
      proof -
        have xm: "euXi SF M h m \<in> borel_measurable ?Q"
          using euXi_measurable[OF SFc]
            measurable_cong_sets[OF setsQ refl] by blast
        have am: "(\<lambda>\<omega>. \<bar>euXi SF M h m \<omega>\<bar>) \<in> borel_measurable ?Q"
          by (intro borel_measurable_abs xm)
        have "E1 = (\<lambda>\<omega>. \<bar>euXi SF M h m \<omega>\<bar>) -` {\<beta>/2..} \<inter> space ?Q"
          unfolding E1_def by auto
        then show ?thesis
          using measurable_sets[OF am borel_closed[OF closed_atLeast]]
          by simp
      qed
      have sE2: "E2 \<in> sets ?Q"
      proof -
        have e1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> borel_measurable ?Q"
          using pair_law_eval_measurable[OF setsQ] by blast
        have e2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (real m * h))
            \<in> borel_measurable ?Q"
          using pair_law_eval_measurable[OF setsQ] by blast
        have fm: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
            \<in> borel_measurable borel"
          by (rule borel_measurable_continuous_onI[OF
              continuous_on_fst[OF continuous_on_id]])
        have dd: "(\<lambda>\<omega>. fst (\<omega> t) - fst (\<omega> (real m * h)))
            \<in> borel_measurable ?Q"
          by (intro borel_measurable_diff
              measurable_compose[OF e1 fm] measurable_compose[OF e2 fm])
        have nm: "(\<lambda>\<omega>. norm (fst (\<omega> t) - fst (\<omega> (real m * h))))
            \<in> borel_measurable ?Q"
          by (rule measurable_compose[OF dd borel_measurable_norm])
        have "E2 = (\<lambda>\<omega>. norm (fst (\<omega> t) - fst (\<omega> (real m * h)))) -` {\<delta>..}
            \<inter> space ?Q"
          unfolding E2_def by auto
        then show ?thesis
          using measurable_sets[OF nm borel_closed[OF closed_atLeast]]
          by simp
      qed
      have QL: "AE \<omega> in ?Q. \<forall>m'\<le>Suc i.
          (\<forall>j<m'. fst (\<omega> (real j * h)) \<in> RO) \<longrightarrow>
          (1/2) * euXi SF M h m' \<omega> + real m' * h * cm / 2
            \<le> q \<bullet> (fst (\<omega> (real m' * h)) - x)
              + (1/2) * ((fst (\<omega> (real m' * h)) - x)
                  \<bullet> (M *v (fst (\<omega> (real m' * h)) - x)))"
        by (rule eulerp_quad_lower_region[OF h0 L1 SFc SFs sym kill marg])
      have incl: "AE \<omega> in ?Q. \<omega> \<in> ?U \<longrightarrow> \<omega> \<in> E1 \<union> E2"
        using QL
      proof (eventually_elim)
        case (elim \<omega>)
        show ?case
        proof (intro impI)
          assume U: "\<omega> \<in> ?U"
          show "\<omega> \<in> E1 \<union> E2"
          proof (cases "\<omega> \<in> E1")
            case True then show ?thesis by simp
          next
            case False
            have wsp: "\<omega> \<in> space ?Q" using U spQ by auto
            have inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> RO"
              using U by auto
            have bad: "q \<bullet> (fst (\<omega> t) - x)
                + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))
                < t * cm / 2 - \<beta>"
              using U by auto
            have small: "\<bar>euXi SF M h m \<omega>\<bar> < \<beta> / 2"
              using False wsp unfolding E1_def by (auto simp: not_le)
            have grid: "\<And>j. j < m \<Longrightarrow> fst (\<omega> (real j * h)) \<in> RO"
            proof -
              fix j assume jm: "j < m"
              have "real j * h < real m * h"
                using jm h0 by (intro mult_strict_right_mono) simp_all
              then have jh2: "real j * h \<le> t" using mh_le by linarith
              have jh1: "0 \<le> real j * h" using h0 by simp
              have "real j * h \<in> {0..t}" using jh1 jh2 by simp
              then show "fst (\<omega> (real j * h)) \<in> RO" by (rule inb)
            qed
            have QLm: "(1/2) * euXi SF M h m \<omega> + real m * h * cm / 2
                \<le> q \<bullet> (fst (\<omega> (real m * h)) - x)
                  + (1/2) * ((fst (\<omega> (real m * h)) - x)
                      \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
              using elim mSuc grid by blast
            have tin: "t \<in> {0..t}" using t0 by simp
            have min': "real m * h \<in> {0..t}" using mh0 mh_le by simp
            have nT: "norm (fst (\<omega> t) - x) \<le> Rn"
              by (rule ROb[OF inb[OF tin]])
            have nM: "norm (fst (\<omega> (real m * h)) - x) \<le> Rn"
              by (rule ROb[OF inb[OF min']])
            define p1 where "p1 = q \<bullet> (fst (\<omega> (real m * h)) - x)
                + (1/2) * ((fst (\<omega> (real m * h)) - x)
                    \<bullet> (M *v (fst (\<omega> (real m * h)) - x)))"
            define p2 where "p2 = q \<bullet> (fst (\<omega> t) - x)
                + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
            define nd where "nd = norm (fst (\<omega> t) - fst (\<omega> (real m * h)))"
            have nd0: "0 \<le> nd" unfolding nd_def by simp
            have habs: "\<bar>real m * h - t\<bar> \<le> h"
            proof -
              have "real m * h - t \<le> h" using mh_le h0 by linarith
              moreover have "- h \<le> real m * h - t" using t_mh by linarith
              ultimately show ?thesis by (simp add: abs_le_iff)
            qed
            have g1: "\<bar>(real m * h - t) * cm\<bar> \<le> h * \<bar>cm\<bar>"
            proof -
              have "\<bar>(real m * h - t) * cm\<bar> = \<bar>real m * h - t\<bar> * \<bar>cm\<bar>"
                by (rule abs_mult)
              also have "\<dots> \<le> h * \<bar>cm\<bar>"
                by (rule mult_right_mono[OF habs abs_ge_zero])
              finally show ?thesis .
            qed
            have g2: "h * \<bar>cm\<bar> \<le> \<beta> / 2"
            proof -
              have "h * (2 * (\<bar>cm\<bar> + 1)) \<le> \<beta>"
                using hs' unfolding h\<^sub>0_def
                by (simp add: pos_le_divide_eq)
              moreover have "h * (2 * (\<bar>cm\<bar> + 1))
                  = 2 * (h * (\<bar>cm\<bar> + 1))" by simp
              ultimately have hcm1: "h * (\<bar>cm\<bar> + 1) \<le> \<beta> / 2" by linarith
              have "h * \<bar>cm\<bar> \<le> h * (\<bar>cm\<bar> + 1)"
                using h0 by (intro mult_left_mono) simp_all
              then show ?thesis using hcm1 by linarith
            qed
            have cmb: "- (\<beta> / 4) \<le> (real m * h - t) * cm / 2"
            proof -
              have "- (h * \<bar>cm\<bar>) \<le> (real m * h - t) * cm"
                using g1 by linarith
              then show ?thesis using g2 by linarith
            qed
            have p1low: "- (\<beta> / 4) + real m * h * cm / 2 \<le> p1"
              using QLm small unfolding p1_def by linarith
            have badp: "p2 < t * cm / 2 - \<beta>"
              unfolding p2_def by (rule bad)
            have distrib: "(real m * h - t) * cm
                = real m * h * cm - t * cm"
              by (simp add: algebra_simps)
            have gap: "\<beta> / 2 < p1 - p2"
              using p1low badp cmb distrib by linarith
            have db: "\<bar>p1 - p2\<bar> \<le> (norm q + 2 * ?CM * Rn) * nd"
              unfolding p1_def p2_def nd_def
              using quad_diff_bound_gen[OF sym nT nM]
              by (simp add: norm_minus_commute)
            have Cle: "norm q + 2 * ?CM * Rn \<le> C\<psi>"
              unfolding C\<psi>_def by simp
            have bCn: "\<beta> / 2 < C\<psi> * nd"
            proof -
              have "\<beta> / 2 < (norm q + 2 * ?CM * Rn) * nd"
                using gap db by linarith
              also have "\<dots> \<le> C\<psi> * nd"
                by (rule mult_right_mono[OF Cle nd0])
              finally show ?thesis .
            qed
            have b2Cn: "\<beta> < nd * (2 * C\<psi>)"
            proof -
              have "\<beta> < 2 * (C\<psi> * nd)" using bCn by linarith
              then show ?thesis by (simp add: mult_ac)
            qed
            have lt: "\<beta> / (2 * C\<psi>) < nd"
              using b2Cn C\<psi>0 by (simp add: pos_divide_less_eq)
            have dle: "\<delta> \<le> \<beta> / (2 * C\<psi>)"
              unfolding \<delta>_def
            proof (rule divide_left_mono)
              show "2 * C\<psi> \<le> 4 * C\<psi>" using C\<psi>0 by linarith
              show "0 \<le> \<beta>" using b0 by linarith
              show "0 < 4 * C\<psi> * (2 * C\<psi>)"
                using C\<psi>0 by (simp add: zero_less_mult_iff)
            qed
            have ndl: "\<delta> \<le> nd" using lt dle by linarith
            show ?thesis
              using wsp ndl unfolding E2_def nd_def by auto
          qed
        qed
      qed
      have s1: "measure ?Q ?U \<le> measure ?Q (E1 \<union> E2)"
        by (rule PQ.finite_measure_mono_AE[OF incl sets.Un[OF sE1 sE2]])
      have s2: "measure ?Q (E1 \<union> E2) \<le> measure ?Q E1 + measure ?Q E2"
        by (rule measure_Un_le[OF sE1 sE2])
      have n1: "real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2 \<le> A * h"
      proof -
        have mhc: "real m * h \<le> c"
        proof -
          have "real m \<le> real (Suc i)" using mSuc by simp
          then have "real m * h \<le> real (Suc i) * h"
            using h0 by (intro mult_right_mono) simp_all
          then show ?thesis using hc by simp
        qed
        have e1: "real m * xiC M L * h\<^sup>2 = real m * h * xiC M L * h"
          by (simp add: power2_eq_square algebra_simps)
        have e2: "real m * h * xiC M L * h \<le> c * xiC M L * h"
          by (intro mult_right_mono mult_right_mono[OF mhc xiC_nonneg])
            (use h0 in simp_all)
        have num: "real m * xiC M L * h\<^sup>2 \<le> c * xiC M L * h"
          unfolding e1 by (rule e2)
        have "real m * xiC M L * h\<^sup>2 / (\<beta> / 2)\<^sup>2
            \<le> c * xiC M L * h / (\<beta> / 2)\<^sup>2"
          by (rule divide_right_mono[OF num]) simp
        also have "\<dots> = A * h"
          unfolding A_def using b0 by (simp add: power_divide field_simps)
        finally show ?thesis .
      qed
      have n2: "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
          \<le> B * h\<^sup>2"
      proof -
        have sq: "(t - real m * h)\<^sup>2 \<le> h\<^sup>2"
          using t_mh mh_le by (intro power_mono) simp_all
        have inner8: "8 * L\<^sup>2 * (t - real m * h)\<^sup>2 \<le> 8 * L\<^sup>2 * h\<^sup>2"
          by (intro mult_left_mono[OF sq]) simp
        have "real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2)
            \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * h\<^sup>2)"
          by (intro mult_left_mono[OF inner8]) simp
        then have "real (CARD('n)) ^ 5
            * (8 * L\<^sup>2 * (t - real m * h)\<^sup>2) / \<delta>^4
            \<le> real (CARD('n)) ^ 5 * (8 * L\<^sup>2 * h\<^sup>2) / \<delta>^4"
          by (intro divide_right_mono) simp_all
        also have "\<dots> = B * h\<^sup>2"
          unfolding B_def using \<delta>0 by (simp add: field_simps)
        finally show ?thesis .
      qed
      have "measure ?Q ?U \<le> A * h + B * h\<^sup>2"
        using s1 s2 mE1 mE2 n1 n2 by linarith
      then show ?thesis unfolding h_def .
    qed
    have hlim: "(\<lambda>i. ?h i) \<longlonglongrightarrow> 0"
      using tendsto_mult[OF tendsto_const LIMSEQ_inverse_real_of_nat, of c]
      by (simp add: divide_inverse)
    have ev: "\<forall>\<^sub>F i in sequentially.
        measure (eulerp SF x (?h i) i) ?U \<le> A * ?h i + B * (?h i)\<^sup>2"
    proof -
      have "\<forall>\<^sub>F i in sequentially. ?h i < h\<^sub>0"
        by (rule order_tendstoD(2)[OF hlim h\<^sub>00])
      then show ?thesis
      proof (eventually_elim)
        case (elim i)
        show ?case by (rule bound[OF less_imp_le[OF elim]])
      qed
    qed
    have ev0: "\<forall>\<^sub>F i in sequentially.
        (0 :: real) \<le> measure (eulerp SF x (?h i) i) ?U"
      by (intro always_eventually allI measure_nonneg)
    have glim: "(\<lambda>i. A * ?h i + B * (?h i)\<^sup>2) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>i. A * ?h i + B * (?h i)\<^sup>2) \<longlonglongrightarrow> A * 0 + B * 0\<^sup>2"
        by (intro tendsto_add tendsto_mult tendsto_const
            tendsto_power hlim)
      then show ?thesis by simp
    qed
    show ?thesis
      by (rule tendsto_sandwich[OF ev0 ev tendsto_const glim])
  qed
qed

subsection \<open>One limit member, two quadratics, one region\<close>

text \<open>Batch 4d(v).  The region version of the almost-sure growth
  statement, carrying TWO quadratic packages against ONE field and ONE
  limit member: the weak-limit transfer serves every vanishing open
  event of a single member simultaneously, so both growth directions
  hold together.  For the tangential field with \<open>\<pm>(2(x-y\<^sub>0), 2\<cdot>1)\<close> this
  pins \<open>|X\<^sub>t - y\<^sub>0|\<^sup>2\<close> to the deterministic line
  \<open>|x - y\<^sub>0|\<^sup>2 + (n-1) t\<close> while the path stays in the region.\<close>

lemma quad_good_rat_to_real_region:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm t :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and rat: "\<And>r. r \<in> \<rat> \<Longrightarrow> 0 < r \<Longrightarrow> r \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      r * cm / 2 \<le> q \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M *v (fst (\<omega> r) - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. s \<in> {0..t} \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  have exr: "\<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t" for j
  proof -
    have "max 0 (t - inverse (real (Suc j))) < t"
      using t0 by (simp add: max_less_iff_conj)
    then show ?thesis
      using Rats_dense_in_real[of
          "max 0 (t - inverse (real (Suc j)))" t] by blast
  qed
  have exr': "\<forall>j. \<exists>r. r \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < r \<and> r < t"
    using exr by blast
  obtain rj where rjprop: "\<forall>j. rj j \<in> \<rat>
      \<and> max 0 (t - inverse (real (Suc j))) < rj j \<and> rj j < t"
    using choice[OF exr'] by blast
  have rjQ: "rj j \<in> \<rat>" for j using rjprop by blast
  have rjl: "max 0 (t - inverse (real (Suc j))) < rj j" for j
    using rjprop by blast
  have rju: "rj j < t" for j using rjprop by blast
  have rj0: "0 < rj j" for j
  proof -
    have "(0::real) \<le> max 0 (t - inverse (real (Suc j)))" by simp
    then show ?thesis using rjl[of j] by linarith
  qed
  have rjc: "rj j \<le> c" for j using rju[of j] tc by linarith
  have glow: "rj j * cm / 2 \<le> g (rj j)" for j
    unfolding g_def
  proof (rule rat)
    show "rj j \<in> \<rat>" by (rule rjQ)
    show "0 < rj j" by (rule rj0)
    show "rj j \<le> c" by (rule rjc)
    show "\<forall>s\<in>{0..rj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume "s \<in> {0..rj j}"
      then have "s \<in> {0..t}" using rju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inb)
    qed
  qed
  have rjlim: "rj \<longlonglongrightarrow> t"
  proof (rule tendsto_sandwich[of
      "\<lambda>j. t - inverse (real (Suc j))" rj sequentially "\<lambda>_. t"])
    show "\<forall>\<^sub>F j in sequentially. t - inverse (real (Suc j)) \<le> rj j"
    proof (intro always_eventually allI)
      fix j
      have "t - inverse (real (Suc j))
          \<le> max 0 (t - inverse (real (Suc j)))"
        by (rule max.cobounded2)
      then show "t - inverse (real (Suc j)) \<le> rj j"
        using rjl[of j] by linarith
    qed
    show "\<forall>\<^sub>F j in sequentially. rj j \<le> t"
      by (intro always_eventually allI less_imp_le rju)
    show "(\<lambda>j. t - inverse (real (Suc j))) \<longlonglongrightarrow> t"
      using tendsto_diff[OF tendsto_const
          LIMSEQ_inverse_real_of_nat, of t] by simp
    show "(\<lambda>_. t) \<longlonglongrightarrow> t" by (rule tendsto_const)
  qed
  have gcomp: "(\<lambda>j. g (rj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. rj n \<in> {0..c}"
      using rj0 rjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> rj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS rjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. rj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF rjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

theorem eulerp_limit_good2_region:
  fixes SF :: "real^'n::finite \<Rightarrow> real^'n^'n" and M1 M2 :: "real^'n^'n"
    and q1 q2 x :: "real^'n" and c cm1 cm2 Rn :: real
    and RO :: "(real^'n) set"
  assumes c0: "0 < c" and L1: "1 \<le> L"
    and SFc: "continuous_on UNIV SF"
    and SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    and sym1: "transpose M1 = M1" and sym2: "transpose M2 = M2"
    and ROo: "open RO"
    and ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
    and kill1: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q1 + M1 *v (z - x)) = 0"
    and marg1: "\<And>z. z \<in> RO \<Longrightarrow>
        cm1 \<le> trace (M1 ** (SF z ** transpose (SF z)))"
    and kill2: "\<And>z. z \<in> RO \<Longrightarrow>
        transpose (SF z) *v (q2 + M2 *v (z - x)) = 0"
    and marg2: "\<And>z. z \<in> RO \<Longrightarrow>
        cm2 \<le> trace (M2 ** (SF z ** transpose (SF z)))"
  shows "\<exists>P \<in> paper_pair_class k L c x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x))))
      \<and> (t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
        + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x))))"
proof -
  let ?pm = "path_metric c :: ('n pairpath) metric"
  define U1 where "U1 = (\<lambda>r \<beta> :: real. {\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO)
      \<and> q1 \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))
        < r * cm1 / 2 - \<beta>})"
  define U2 where "U2 = (\<lambda>r \<beta> :: real. {\<omega> \<in> mspace ?pm.
      (\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO)
      \<and> q2 \<bullet> (fst (\<omega> r) - x)
        + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))
        < r * cm2 / 2 - \<beta>})"
  obtain P where P: "P \<in> paper_pair_class k L c x"
    and Praw: "\<forall>U b'. openin (mtopology_of ?pm) U \<longrightarrow>
      (\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i) U) \<longlonglongrightarrow> b' \<longrightarrow>
      measure P U \<le> b'"
    using eulerp_weak_limit[OF c0 L1 SFc SFs] by blast
  interpret FP: prob_space P by (rule paper_pair_class_prob[OF P])
  have setsP: "sets P = sets (borel_of (mtopology_of ?pm))"
    by (rule paper_pair_class_sets[OF P])
  have spaceP: "space P = mspace ?pm"
    by (rule space_of_path_sets[OF setsP])
  have AErn1: "AE \<omega> in P. \<omega> \<notin> U1 r (inverse (real (Suc n)))"
    if r0: "0 < r" and rc: "r \<le> c" for r and n :: nat
  proof -
    have inv0: "(0::real) < inverse (real (Suc n))" by simp
    have opn: "openin (mtopology_of ?pm) (U1 r (inverse (real (Suc n))))"
      unfolding U1_def
      by (rule open_quad_bad_event_region[OF less_imp_le[OF r0] rc ROo])
    have tnd: "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
        (U1 r (inverse (real (Suc n))))) \<longlonglongrightarrow> 0"
      unfolding U1_def
      by (rule eulerp_bad_event_null_region[OF c0 L1 SFc SFs sym1
          ROb kill1 marg1 r0 rc inv0])
    have le0: "measure P (U1 r (inverse (real (Suc n)))) \<le> 0"
      using Praw opn tnd by blast
    have m0: "measure P (U1 r (inverse (real (Suc n)))) = 0"
      using le0 measure_nonneg[of P "U1 r (inverse (real (Suc n)))"]
      by linarith
    have Uset: "U1 r (inverse (real (Suc n))) \<in> sets P"
      using borel_of_open[OF opn] by (simp add: setsP)
    have "U1 r (inverse (real (Suc n))) \<in> null_sets P"
    proof (rule null_setsI)
      show "emeasure P (U1 r (inverse (real (Suc n)))) = 0"
        using m0 by (simp add: FP.emeasure_eq_measure)
      show "U1 r (inverse (real (Suc n))) \<in> sets P" by (rule Uset)
    qed
    then show ?thesis by (rule AE_not_in)
  qed
  have AErn2: "AE \<omega> in P. \<omega> \<notin> U2 r (inverse (real (Suc n)))"
    if r0: "0 < r" and rc: "r \<le> c" for r and n :: nat
  proof -
    have inv0: "(0::real) < inverse (real (Suc n))" by simp
    have opn: "openin (mtopology_of ?pm) (U2 r (inverse (real (Suc n))))"
      unfolding U2_def
      by (rule open_quad_bad_event_region[OF less_imp_le[OF r0] rc ROo])
    have tnd: "(\<lambda>i. measure (eulerp SF x (c / real (Suc i)) i)
        (U2 r (inverse (real (Suc n))))) \<longlonglongrightarrow> 0"
      unfolding U2_def
      by (rule eulerp_bad_event_null_region[OF c0 L1 SFc SFs sym2
          ROb kill2 marg2 r0 rc inv0])
    have le0: "measure P (U2 r (inverse (real (Suc n)))) \<le> 0"
      using Praw opn tnd by blast
    have m0: "measure P (U2 r (inverse (real (Suc n)))) = 0"
      using le0 measure_nonneg[of P "U2 r (inverse (real (Suc n)))"]
      by linarith
    have Uset: "U2 r (inverse (real (Suc n))) \<in> sets P"
      using borel_of_open[OF opn] by (simp add: setsP)
    have "U2 r (inverse (real (Suc n))) \<in> null_sets P"
    proof (rule null_setsI)
      show "emeasure P (U2 r (inverse (real (Suc n)))) = 0"
        using m0 by (simp add: FP.emeasure_eq_measure)
      show "U2 r (inverse (real (Suc n))) \<in> sets P" by (rule Uset)
    qed
    then show ?thesis by (rule AE_not_in)
  qed
  define I where "I = {r. r \<in> \<rat> \<and> 0 < r \<and> r \<le> c}"
  have cI: "countable I"
    unfolding I_def by (rule countable_subset[OF _ countable_rat]) auto
  have AEall1: "AE \<omega> in P. \<forall>r\<in>I. \<forall>n::nat.
      \<omega> \<notin> U1 r (inverse (real (Suc n)))"
    unfolding AE_ball_countable[OF cI]
  proof
    fix r assume "r \<in> I"
    then have r0: "0 < r" and rc: "r \<le> c" unfolding I_def by auto
    show "AE \<omega> in P. \<forall>n::nat. \<omega> \<notin> U1 r (inverse (real (Suc n)))"
      unfolding AE_all_countable by (intro allI AErn1[OF r0 rc])
  qed
  have AEall2: "AE \<omega> in P. \<forall>r\<in>I. \<forall>n::nat.
      \<omega> \<notin> U2 r (inverse (real (Suc n)))"
    unfolding AE_ball_countable[OF cI]
  proof
    fix r assume "r \<in> I"
    then have r0: "0 < r" and rc: "r \<le> c" unfolding I_def by auto
    show "AE \<omega> in P. \<forall>n::nat. \<omega> \<notin> U2 r (inverse (real (Suc n)))"
      unfolding AE_all_countable by (intro allI AErn2[OF r0 rc])
  qed
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  show ?thesis
  proof (intro bexI[OF _ P])
    show "AE \<omega> in P. \<forall>t.
        0 < t \<longrightarrow> t \<le> c \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
        (t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x))))
        \<and> (t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x))))"
      using AEall1 AEall2 sp
    proof (eventually_elim)
      case (elim \<omega>)
      have wm: "\<omega> \<in> mspace ?pm" using elim(3) by (simp add: spaceP)
      have notin1: "\<And>r n. r \<in> I \<Longrightarrow>
          \<omega> \<notin> U1 r (inverse (real (Suc n)))"
        using elim(1) by blast
      have notin2: "\<And>r n. r \<in> I \<Longrightarrow>
          \<omega> \<notin> U2 r (inverse (real (Suc n)))"
        using elim(2) by blast
      show ?case
      proof (intro allI impI conjI)
        fix t assume t0: "0 < t" and tc: "t \<le> c"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
        have rat1: "r * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))"
          if rQ: "r \<in> \<rat>" and r0: "0 < r" and rc: "r \<le> c"
            and rball: "\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO" for r
        proof (rule ccontr)
          assume nle: "\<not> r * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))"
          have pos: "0 < r * cm1 / 2 - (q1 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x))))"
            using nle by simp
          obtain n where nsm: "inverse (real (Suc n))
              < r * cm1 / 2 - (q1 \<bullet> (fst (\<omega> r) - x)
                + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x))))"
            using reals_Archimedean[OF pos] by auto
          have drop: "q1 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M1 *v (fst (\<omega> r) - x)))
              < r * cm1 / 2 - inverse (real (Suc n))"
            using nsm by linarith
          have "\<omega> \<in> U1 r (inverse (real (Suc n)))"
            unfolding U1_def using wm rball drop by auto
          moreover have "r \<in> I" unfolding I_def using rQ r0 rc by simp
          ultimately show False using notin1 by blast
        qed
        have rat2: "r * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> r) - x)
            + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))"
          if rQ: "r \<in> \<rat>" and r0: "0 < r" and rc: "r \<le> c"
            and rball: "\<forall>s\<in>{0..r}. fst (\<omega> s) \<in> RO" for r
        proof (rule ccontr)
          assume nle: "\<not> r * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))"
          have pos: "0 < r * cm2 / 2 - (q2 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x))))"
            using nle by simp
          obtain n where nsm: "inverse (real (Suc n))
              < r * cm2 / 2 - (q2 \<bullet> (fst (\<omega> r) - x)
                + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x))))"
            using reals_Archimedean[OF pos] by auto
          have drop: "q2 \<bullet> (fst (\<omega> r) - x)
              + (1/2) * ((fst (\<omega> r) - x) \<bullet> (M2 *v (fst (\<omega> r) - x)))
              < r * cm2 / 2 - inverse (real (Suc n))"
            using nsm by linarith
          have "\<omega> \<in> U2 r (inverse (real (Suc n)))"
            unfolding U2_def using wm rball drop by auto
          moreover have "r \<in> I" unfolding I_def using rQ r0 rc by simp
          ultimately show False using notin2 by blast
        qed
        show "t * cm1 / 2 \<le> q1 \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M1 *v (fst (\<omega> t) - x)))"
        proof (rule quad_good_rat_to_real_region[OF wm rat1 t0 tc])
          fix s assume "s \<in> {0..t}"
          then show "fst (\<omega> s) \<in> RO" using inb by blast
        qed
        show "t * cm2 / 2 \<le> q2 \<bullet> (fst (\<omega> t) - x)
            + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M2 *v (fst (\<omega> t) - x)))"
        proof (rule quad_good_rat_to_real_region[OF wm rat2 t0 tc])
          fix s assume "s \<in> {0..t}"
          then show "fst (\<omega> s) \<in> RO" using inb by blast
        qed
      qed
    qed
  qed
qed

subsection \<open>The tangential member: exact radial growth\<close>

text \<open>Batch 4d(vi).  The unclamped tangential field is admissible
  everywhere --- even where the guarded radial is short, its square
  keeps a full \<open>(n-1)\<close>-dimensional unit eigenspace --- and on the region
  where the guard is inactive it kills the radial exactly.  Feeding the
  two-quadratic limit theorem with \<open>\<pm>(2(x-y\<^sub>0), 2\<cdot>1)\<close> pins the squared
  distance to \<open>y\<^sub>0\<close> to the deterministic line
  \<open>|x-y\<^sub>0|\<^sup>2 + (CARD('n)-1) t\<close> while the path stays in the region.  This
  is the engine behind the second horn of Case 2 and Example 3.1's
  lower bound: exit times of concentric balls are deterministic.\<close>

lemma tanp_sq_sconstraint:
  fixes u :: "real^'n::finite"
  assumes u1: "norm u \<le> 1" and k1: "1 \<le> k" and L1: "1 \<le> L"
  shows "tanp u ** transpose (tanp u) \<in> sconstraint k L"
proof -
  have tr: "transpose (tanp u) = tanp u" by (rule tanp_sym)
  define A where "A = tanp u ** tanp u"
  have symA: "transpose A = A"
    unfolding A_def by (simp add: matrix_transpose_mul tanp_sym)
  have qf: "v \<bullet> (A *v v) = (tanp u *v v) \<bullet> (tanp u *v v)" for v
  proof -
    have assoc: "A *v v = tanp u *v (tanp u *v v)"
      unfolding A_def by (metis matrix_vector_mul_assoc)
    have "v \<bullet> (tanp u *v (tanp u *v v))
        = (transpose (tanp u) *v v) \<bullet> (tanp u *v v)"
      by (rule inner_transpose_matrix)
    then show ?thesis unfolding assoc tr .
  qed
  have contract: "(tanp u *v v) \<bullet> (tanp u *v v) \<le> v \<bullet> v" for v
  proof -
    have e: "(tanp u *v v) \<bullet> (tanp u *v v)
        = v \<bullet> v - (2 - u \<bullet> u) * (u \<bullet> v)\<^sup>2"
      unfolding tanp_mv
      by (simp add: inner_diff_left inner_diff_right
          inner_scaleR_left inner_scaleR_right inner_commute
          power2_eq_square algebra_simps)
    have uu1: "u \<bullet> u \<le> 1"
    proof -
      have "u \<bullet> u = (norm u)\<^sup>2" by (simp add: dot_square_norm)
      also have "\<dots> \<le> 1"
        using u1 norm_ge_zero[of u] by (simp add: power_le_one)
      finally show ?thesis .
    qed
    have "0 \<le> (2 - u \<bullet> u) * (u \<bullet> v)\<^sup>2"
      using uu1 by (intro mult_nonneg_nonneg) simp_all
    then show ?thesis unfolding e by linarith
  qed
  have psdA: "psd A"
    unfolding psd_def
  proof (intro conjI allI)
    show "transpose A = A" by (rule symA)
    show "0 \<le> v \<bullet> (A *v v)" for v
      unfolding qf by (rule inner_ge_zero)
  qed
  have ubA: "eigen_ub A L"
    unfolding eigen_ub_def
  proof
    fix v :: "real^'n"
    have "v \<bullet> (A *v v) \<le> v \<bullet> v" unfolding qf by (rule contract)
    also have "\<dots> = 1 * (v \<bullet> v)" by simp
    also have "\<dots> \<le> L * (v \<bullet> v)"
      by (rule mult_right_mono[OF L1 inner_ge_zero])
    finally show "v \<bullet> (A *v v) \<le> L * (v \<bullet> v)" .
  qed
  have lbA: "eigen_lb A (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ "{v :: real^'n. u \<bullet> v = 0}"] conjI ballI)
    show "subspace {v :: real^'n. u \<bullet> v = 0}"
      by (rule subspace_hyperplane)
    show "CARD('n) - k \<le> dim {v :: real^'n. u \<bullet> v = 0}"
    proof (cases "u = 0")
      case True
      then have "{v :: real^'n. u \<bullet> v = 0} = UNIV" by simp
      then show ?thesis by simp
    next
      case False
      then have "dim {v :: real^'n. u \<bullet> v = 0} = CARD('n) - 1"
        by (simp add: dim_hyperplane)
      then show ?thesis using k1 by simp
    qed
  next
    fix v :: "real^'n" assume "v \<in> {v. u \<bullet> v = 0}"
    then have uv: "u \<bullet> v = 0" by simp
    have "tanp u *v v = v" unfolding tanp_mv uv by simp
    then show "v \<bullet> v \<le> v \<bullet> (A *v v)" unfolding qf by simp
  qed
  have "A \<in> feasible k L 0"
    unfolding feasible_def
    using psdA ubA lbA by (simp add: matrix_vector_mult_0_right)
  then have "A \<in> sconstraint k L"
    using feasible_subset_sconstraint by blast
  then show ?thesis unfolding A_def tr .
qed

lemma tanRF_cont:
  fixes y\<^sub>0 :: "real^'n::finite"
  assumes rho0: "0 < \<rho>"
  shows "continuous_on UNIV (\<lambda>z. tanp (uvec y\<^sub>0 \<rho> z))"
proof -
  have uc: "continuous_on UNIV (uvec y\<^sub>0 \<rho>)"
    by (rule uvec_cont[OF rho0])
  have ci: "continuous_on UNIV (\<lambda>z. uvec y\<^sub>0 \<rho> z $ i)" for i
    by (rule continuous_on_compose2[OF
        linear_continuous_on[OF bounded_linear_vec_nth] uc]) auto
  have eq: "(\<lambda>z. tanp (uvec y\<^sub>0 \<rho> z)) = (\<lambda>z. \<chi> i j.
      (if i = j then 1 else 0)
      - uvec y\<^sub>0 \<rho> z $ i * uvec y\<^sub>0 \<rho> z $ j)"
    by (rule ext) (simp add: tanp_def outerp_def mat_def vec_eq_iff)
  show ?thesis unfolding eq
    by (intro continuous_on_vec_lambda continuous_intros ci)
qed

theorem tangential_exact_growth:
  fixes y\<^sub>0 x :: "real^'n::finite" and \<rho> rB T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)"
    and rho0: "0 < \<rho>"
  shows "\<exists>P \<in> paper_pair_class k L T x. AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB) \<longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
        = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
proof -
  define RO where "RO = {w :: real^'n. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
  define SF where "SF = (\<lambda>z. tanp (uvec y\<^sub>0 \<rho> z))"
  define Rn where "Rn = rB + norm (y\<^sub>0 - x)"
  have SFc: "continuous_on UNIV SF"
    unfolding SF_def by (rule tanRF_cont[OF rho0])
  have SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
    unfolding SF_def
    by (rule tanp_sq_sconstraint[OF uvec_norm_le[OF rho0] k1 L1])
  have ROo: "open RO"
  proof -
    have "open {w :: real^'n. \<rho> < norm (w - y\<^sub>0)}"
      by (intro open_Collect_less continuous_intros
          continuous_on_const)
    then show ?thesis unfolding RO_def
      by (intro open_Int open_ball)
  qed
  have ROb: "\<And>z. z \<in> RO \<Longrightarrow> norm (z - x) \<le> Rn"
  proof -
    fix z assume "z \<in> RO"
    then have "norm (z - y\<^sub>0) < rB"
      unfolding RO_def by (simp add: mem_ball dist_norm norm_minus_commute)
    moreover have "norm (z - x) \<le> norm (z - y\<^sub>0) + norm (y\<^sub>0 - x)"
    proof -
      have "z - x = (z - y\<^sub>0) + (y\<^sub>0 - x)" by simp
      then show ?thesis
        by (metis norm_triangle_ineq)
    qed
    ultimately show "norm (z - x) \<le> Rn" unfolding Rn_def by linarith
  qed
  have unitRO: "norm (uvec y\<^sub>0 \<rho> z) = 1" if z: "z \<in> RO" for z
  proof -
    have "\<rho> \<le> norm (z - y\<^sub>0)" using z unfolding RO_def by auto
    then show ?thesis by (rule uvec_unit[OF rho0])
  qed
  have killRO: "transpose (SF z) *v (c' *\<^sub>R (x - y\<^sub>0)
      + (c' *\<^sub>R mat 1) *v (z - x)) = 0"
    if z: "z \<in> RO" for z c'
  proof -
    have far: "\<rho> \<le> norm (z - y\<^sub>0)" using z unfolding RO_def by auto
    have arg: "c' *\<^sub>R (x - y\<^sub>0) + (c' *\<^sub>R mat 1) *v (z - x)
        = c' *\<^sub>R (z - y\<^sub>0)"
      by (simp add: scaleR_matrix_vector matrix_vector_mul_lid
          scaleR_right_diff_distrib scaleR_add_right)
    have k0: "tanp (uvec y\<^sub>0 \<rho> z) *v (z - y\<^sub>0) = 0"
      by (rule tanp_kill[OF unitRO[OF z] uvec_par[OF rho0 far]])
    have "transpose (SF z) *v (c' *\<^sub>R (z - y\<^sub>0))
        = c' *\<^sub>R (SF z *v (z - y\<^sub>0))"
      unfolding SF_def tanp_sym
      by (simp add: matrix_vector_mult_scaleR)
    also have "\<dots> = 0" unfolding SF_def using k0 by simp
    finally show ?thesis unfolding arg .
  qed
  have sqRO: "SF z ** transpose (SF z) = tanp (uvec y\<^sub>0 \<rho> z)"
    if z: "z \<in> RO" for z
    unfolding SF_def
    by (simp add: tanp_sym tanp_sq[OF unitRO[OF z]])
  have trRO: "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
      = c' * (real CARD('n) - 1)"
    if z: "z \<in> RO" for z c'
  proof -
    have "(c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z))
        = c' *\<^sub>R (SF z ** transpose (SF z))"
      by (simp add: scaleR_matrix_mult matrix_mul_lid)
    then have "trace ((c' *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))
        = c' * trace (SF z ** transpose (SF z))"
      by (simp add: trace_scaleR)
    also have "trace (SF z ** transpose (SF z))
        = real CARD('n) - 1"
      unfolding sqRO[OF z] by (rule tanp_trace[OF unitRO[OF z]])
    finally show ?thesis .
  qed
  have sym1: "transpose ((2::real) *\<^sub>R mat 1 :: real^'n^'n)
      = (2::real) *\<^sub>R mat 1"
    by (simp add: transpose_scalar)
  have sym2: "transpose ((-2::real) *\<^sub>R mat 1 :: real^'n^'n)
      = (-2::real) *\<^sub>R mat 1"
    by (simp add: transpose_def vec_eq_iff mat_def)
  obtain P where P: "P \<in> paper_pair_class k L T x"
    and AE2: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<longrightarrow>
      (t * (2 * (real CARD('n) - 1)) / 2
        \<le> (2 *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x))))
      \<and> (t * (- 2 * (real CARD('n) - 1)) / 2
        \<le> ((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
          + (1/2) * ((fst (\<omega> t) - x)
              \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x))))"
  proof -
    have kill1: "\<And>z. z \<in> RO \<Longrightarrow> transpose (SF z)
        *v (2 *\<^sub>R (x - y\<^sub>0) + ((2::real) *\<^sub>R mat 1) *v (z - x)) = 0"
      using killRO by blast
    have kill2: "\<And>z. z \<in> RO \<Longrightarrow> transpose (SF z)
        *v ((-2) *\<^sub>R (x - y\<^sub>0) + ((-2::real) *\<^sub>R mat 1) *v (z - x)) = 0"
      using killRO by blast
    have marg1: "\<And>z. z \<in> RO \<Longrightarrow> 2 * (real CARD('n) - 1)
        \<le> trace (((2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
      using trRO by simp
    have marg2: "\<And>z. z \<in> RO \<Longrightarrow> - 2 * (real CARD('n) - 1)
        \<le> trace (((-2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
    proof -
      fix z assume zRO: "z \<in> RO"
      show "- 2 * (real CARD('n) - 1)
          \<le> trace (((-2::real) *\<^sub>R mat 1) ** (SF z ** transpose (SF z)))"
        using trRO[OF zRO, of "-2"] by simp
    qed
    show ?thesis
      using eulerp_limit_good2_region[OF T0 L1 SFc SFs sym1 sym2
          ROo ROb kill1 marg1 kill2 marg2] that by blast
  qed
  show ?thesis
  proof (intro bexI[OF _ P])
    show "AE \<omega> in P. \<forall>t.
        0 < t \<longrightarrow> t \<le> T \<longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB)
        \<longrightarrow> (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
          = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
      using AE2
    proof (eventually_elim)
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix t assume t0: "0 < t" and tT: "t \<le> T"
          and inb: "\<forall>s\<in>{0..t}. fst (\<omega> s)
            \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
        have inb': "\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO"
          using inb unfolding RO_def by blast
        have g1: "t * (2 * (real CARD('n) - 1)) / 2
            \<le> (2 *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x)
                  \<bullet> (((2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x)))"
          and g2: "t * (- 2 * (real CARD('n) - 1)) / 2
            \<le> ((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> (fst (\<omega> t) - x)
              + (1/2) * ((fst (\<omega> t) - x)
                  \<bullet> (((-2::real) *\<^sub>R mat 1) *v (fst (\<omega> t) - x)))"
          using elim t0 tT inb' by blast+
        define d where "d = fst (\<omega> t) - x"
        have e1: "(2 *\<^sub>R (x - y\<^sub>0)) \<bullet> d = 2 * ((x - y\<^sub>0) \<bullet> d)"
          by (simp add: inner_scaleR_left)
        have e2: "((-2) *\<^sub>R (x - y\<^sub>0)) \<bullet> d = - 2 * ((x - y\<^sub>0) \<bullet> d)"
          by (simp add: inner_scaleR_left)
        have e3: "d \<bullet> (((2::real) *\<^sub>R mat 1) *v d) = 2 * (d \<bullet> d)"
          by (simp add: scaleR_matrix_vector matrix_vector_mul_lid
              inner_scaleR_right)
        have negmv: "\<And>A :: real^'n^'n. (- A) *v d = - (A *v d)"
          by (simp add: matrix_vector_mult_def vec_eq_iff sum_negf)
        have e4: "d \<bullet> (((-2::real) *\<^sub>R mat 1) *v d) = - 2 * (d \<bullet> d)"
          by (simp add: negmv scaleR_matrix_vector matrix_vector_mul_lid
              inner_scaleR_right inner_minus_right)
        have id1: "t * (2 * (real CARD('n) - 1)) / 2
            = t * (real CARD('n) - 1)" by simp
        have id2: "t * (- 2 * (real CARD('n) - 1)) / 2
            = - (t * (real CARD('n) - 1))" by (simp add: field_simps)
        have both: "2 * ((x - y\<^sub>0) \<bullet> d) + d \<bullet> d
            = t * (real CARD('n) - 1)"
          using g1[unfolded id1] g2[unfolded id2]
          unfolding d_def[symmetric] e1 e2 e3 e4
          by linarith
        have split: "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
            = (norm (x - y\<^sub>0))\<^sup>2 + (2 * ((x - y\<^sub>0) \<bullet> d) + d \<bullet> d)"
        proof -
          have dd: "fst (\<omega> t) - y\<^sub>0 = (x - y\<^sub>0) + d"
            unfolding d_def by simp
          have "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
              = (fst (\<omega> t) - y\<^sub>0) \<bullet> (fst (\<omega> t) - y\<^sub>0)"
            by (simp add: dot_square_norm)
          also have "\<dots> = (x - y\<^sub>0) \<bullet> (x - y\<^sub>0)
              + 2 * ((x - y\<^sub>0) \<bullet> d) + d \<bullet> d"
            unfolding dd
            by (simp add: inner_add_left inner_add_right
                inner_commute)
          also have "(x - y\<^sub>0) \<bullet> (x - y\<^sub>0) = (norm (x - y\<^sub>0))\<^sup>2"
            by (simp add: dot_square_norm)
          finally show ?thesis by simp
        qed
        show "(norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
            = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
          unfolding split both by (rule refl)
      qed
    qed
  qed
qed

subsection \<open>Deterministic confinement and the ball lower bound\<close>

text \<open>Batch 4d(vii).  The payoff of the exact radial growth: paths of
  the tangential member CANNOT leave the annulus before the
  deterministic time \<open>(rB\<^sup>2 - |x-y\<^sub>0|\<^sup>2)/(n-1)\<close> --- the inner boundary is
  unreachable because the squared distance only grows, and reaching the
  outer sphere pins the time exactly.  Feeding the constant-time DPP
  (@{thm [source] paper_v_dpp_sup_ge}) turns confinement into the
  POSITIVE lower bound \<open>v(x) \<ge> min(T/2, \<delta>/2)\<close> whenever the ball sits
  inside \<open>K\<close>.  This is the second horn's contradiction input in Case 2,
  and a (non-sharp) form of Example 3.1's missing half.\<close>

lemma radial_sq_upto:
  fixes \<omega> :: "'n::finite pairpath" and y\<^sub>0 x :: "real^'n"
    and TT e cn :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric TT :: ('n pairpath) metric)"
    and grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> TT \<Longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * cn"
    and e0: "0 < e" and eT: "e \<le> TT"
    and inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
proof -
  define g where "g = (\<lambda>s. (norm (fst (\<omega> s) - y\<^sub>0))\<^sup>2)"
  have gc: "continuous_on {0..TT} g"
  proof -
    have wc: "continuous_on {0..TT} \<omega>"
      by (rule mspace_path_metricD[OF wm])
    have fc: "continuous_on {0..TT} (\<lambda>s. fst (\<omega> s))"
      by (rule continuous_on_fst[OF wc])
    show ?thesis
      unfolding g_def by (intro continuous_intros fc)
  qed
  define tj where "tj = (\<lambda>j. e - e / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "e / (2 * real (Suc j)) \<le> e / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> e" using e0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using e0 by linarith
  qed
  have tju: "tj j < e" for j
  proof -
    have "0 < e / (2 * real (Suc j))" using e0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjT: "tj j \<le> TT" for j using tju[of j] eT by linarith
  have glow: "g (tj j) = (norm (x - y\<^sub>0))\<^sup>2 + tj j * cn" for j
    unfolding g_def
  proof (rule grow)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> TT" by (rule tjT)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < e" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inside)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> e"
  proof -
    have eq: "(\<lambda>j. (e / 2) * inverse (real (Suc j)))
        = (\<lambda>j. e / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (e / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (e / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. e / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. e - e / (2 * real (Suc j))) \<longlonglongrightarrow> e - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g e"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..TT}"
      using tjl tjT by (auto intro: less_imp_le)
    have eS: "e \<in> {0..TT}" using e0 eT by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g e"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS eS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have vlim: "(\<lambda>j. (norm (x - y\<^sub>0))\<^sup>2 + tj j * cn)
      \<longlonglongrightarrow> (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    by (intro tendsto_add tendsto_const tendsto_mult tjlim)
  have "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    using vlim unfolding glow by simp
  then have "g e = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
    using gcomp LIMSEQ_unique by blast
  then show ?thesis unfolding g_def .
qed

theorem paper_v_ball_lower_plus:
  fixes K :: "(real^'n::finite) set" and y\<^sub>0 x :: "real^'n"
    and rB T \<beta> :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)"
    and Kc: "closed K" and sub: "cball y\<^sub>0 rB \<subseteq> K"
    and xy: "x \<noteq> y\<^sub>0" and xin: "norm (x - y\<^sub>0) < rB"
    and b0: "0 \<le> \<beta>"
    and vlow: "\<And>w. w \<in> ball y\<^sub>0 rB \<Longrightarrow>
      \<beta> \<le> enn2real (paper_v k L T K w)"
  shows "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min \<beta> (T / 2))
      \<le> paper_v k L T K x"
proof -
  define \<rho>\<^sub>0 where "\<rho>\<^sub>0 = norm (x - y\<^sub>0)"
  define \<rho> where "\<rho> = \<rho>\<^sub>0 / 2"
  define cn where "cn = real CARD('n) - 1"
  define \<delta>f where "\<delta>f = (rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2) / cn"
  define cc where "cc = min (T / 2) (\<delta>f / 2)"
  let ?RO = "{w :: real^'n. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
  have r00: "0 < \<rho>\<^sub>0" unfolding \<rho>\<^sub>0_def using xy by simp
  have rho0: "0 < \<rho>" unfolding \<rho>_def using r00 by simp
  have n2: "2 \<le> CARD('n)" using k1 kn by linarith
  have cn1: "1 \<le> cn"
  proof -
    have "(2::real) \<le> real CARD('n)"
      using n2 by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis unfolding cn_def by linarith
  qed
  have cn0: "0 < cn" using cn1 by linarith
  have rr: "\<rho>\<^sub>0 < rB" using xin unfolding \<rho>\<^sub>0_def .
  have rB0: "0 < rB" using r00 rr by linarith
  have sq_lt: "\<rho>\<^sub>0\<^sup>2 < rB\<^sup>2"
    using r00 rr by (intro power_strict_mono) simp_all
  have df0: "0 < \<delta>f" unfolding \<delta>f_def using sq_lt cn0 by simp
  have cc0: "0 < cc" unfolding cc_def using T0 df0 by simp
  have ccT: "cc < T" unfolding cc_def using T0 by simp
  have ccT2: "cc \<le> T / 2" unfolding cc_def by simp
  have ccdf: "cc < \<delta>f" unfolding cc_def using df0 by simp
  obtain P where P: "P \<in> paper_pair_class k L T x"
    and AEg: "AE \<omega> in P. \<forall>t.
      0 < t \<longrightarrow> t \<le> T \<longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<longrightarrow>
      (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2
        = (norm (x - y\<^sub>0))\<^sup>2 + t * (real CARD('n) - 1)"
    using tangential_exact_growth[OF T0 L1 k1 kn rho0,
        where y\<^sub>0 = y\<^sub>0 and rB = rB and x = x]
    by blast
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF P])
  have spaceP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have start: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule paper_pair_class_start[OF P])
  have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
  have AEfun: "AE \<omega> in P. ennreal (cc + min \<beta> (T / 2))
      \<le> ennreal (pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (paper_v k L (T - cc) K (fst (\<omega> cc))) else 0))"
    using AEg start sp
  proof (eventually_elim)
    case (elim \<omega>)
    have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using elim(3) by (simp add: spaceP)
    have x0: "fst (\<omega> 0) = x" using elim(2) by blast
    have cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      by (rule path_sets_fst_continuous[OF setsP])
        (use elim(3) in simp)
    have grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> T \<Longrightarrow>
        (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ?RO) \<Longrightarrow>
        (norm (fst (\<omega> t) - y\<^sub>0))\<^sup>2 = (norm (x - y\<^sub>0))\<^sup>2 + t * cn"
      unfolding cn_def using elim(1) by blast
    have xRO: "x \<in> ?RO"
      using rho0 rr r00 unfolding \<rho>_def \<rho>\<^sub>0_def
      by (auto simp: mem_ball dist_norm norm_minus_commute)
    have ROopen: "open ?RO"
    proof -
      have "open {w :: real^'n. \<rho> < norm (w - y\<^sub>0)}"
        by (intro open_Collect_less continuous_intros
            continuous_on_const)
      then show ?thesis by (intro open_Int open_ball)
    qed
    have cc0': "0 \<le> cc" using cc0 by linarith
    have contc: "continuous_on {0..cc} (\<lambda>t. fst (\<omega> t))"
      by (rule continuous_on_subset[OF cont]) (use ccT in auto)
    \<comment> \<open>the path stays in the annulus strictly before \<open>cc\<close>\<close>
    have IN: "fst (\<omega> s) \<in> ?RO" if s0: "0 \<le> s" and sc: "s < cc" for s
    proof -
      define e where "e = pexit cc ?RO (\<lambda>t. fst (\<omega> t))"
      have eup: "e \<le> cc" unfolding e_def by (rule pexit_le_T[OF cc0'])
      have before: "fst (\<omega> u) \<in> ?RO"
        if u0: "0 \<le> u" and ue: "u < e" for u
      proof (rule ccontr)
        assume nb: "fst (\<omega> u) \<notin> ?RO"
        have uc: "u \<le> cc" using ue eup by linarith
        have "pexit cc ?RO (\<lambda>t. fst (\<omega> t)) \<le> u"
          by (rule pexit_le_of_mem[OF cc0' u0 uc]) (use nb in simp)
        then show False using ue unfolding e_def by linarith
      qed
      have ecc: "e = cc"
      proof (rule ccontr)
        assume "e \<noteq> cc"
        then have elt: "e < cc" using eup by linarith
        have Xe: "fst (\<omega> e) \<notin> ?RO"
          using pexit_mem_of_less_T[OF cc0' ROopen contc]
          using elt unfolding e_def by simp
        have e0': "0 < e"
        proof (rule ccontr)
          assume "\<not> 0 < e"
          moreover have "0 \<le> e"
            unfolding e_def by (rule pexit_nonneg[OF cc0'])
          ultimately have "e = 0" by linarith
          then show False using Xe x0 xRO by simp
        qed
        have esq: "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2
            = (norm (x - y\<^sub>0))\<^sup>2 + e * cn"
        proof (rule radial_sq_upto[OF wm grow e0'])
          show "e \<le> T" using elt ccT by linarith
          show "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> ?RO"
            by (rule before)
        qed
        have dichot: "norm (fst (\<omega> e) - y\<^sub>0) \<le> \<rho>
            \<or> rB \<le> norm (fst (\<omega> e) - y\<^sub>0)"
          using Xe
          by (auto simp: mem_ball dist_norm norm_minus_commute)
        show False
        proof (cases rule: disjE[OF dichot])
          case 1
          have "(norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2 \<le> \<rho>\<^sup>2"
            using 1 rho0 by (intro power_mono) simp_all
          moreover have "\<rho>\<^sup>2 < \<rho>\<^sub>0\<^sup>2"
            unfolding \<rho>_def using r00 by (simp add: power_divide)
          moreover have "\<rho>\<^sub>0\<^sup>2 \<le> (norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2"
            unfolding esq \<rho>\<^sub>0_def using e0' cn0
            by (simp add: mult_nonneg_nonneg)
          ultimately show False by linarith
        next
          case 2
          have "rB\<^sup>2 \<le> (norm (fst (\<omega> e) - y\<^sub>0))\<^sup>2"
            using 2 rB0 by (intro power_mono) simp_all
          then have "rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2 \<le> e * cn"
            unfolding esq \<rho>\<^sub>0_def by linarith
          then have "\<delta>f \<le> e"
            unfolding \<delta>f_def using cn0 by (simp add: pos_divide_le_eq)
          then show False using elt ccdf by linarith
        qed
      qed
      show ?thesis using before[OF s0] sc unfolding ecc by simp
    qed
    \<comment> \<open>hence in \<open>K\<close> through \<open>cc\<close>, including the endpoint\<close>
    have inB: "fst (\<omega> s) \<in> ball y\<^sub>0 rB"
      if s0: "0 \<le> s" and sc: "s \<le> cc" for s
    proof (cases "s < cc")
      case True
      show ?thesis using IN[OF s0 True] by blast
    next
      case False
      then have seq: "s = cc" using sc by linarith
      have csq: "(norm (fst (\<omega> cc) - y\<^sub>0))\<^sup>2
          = (norm (x - y\<^sub>0))\<^sup>2 + cc * cn"
      proof (rule radial_sq_upto[OF wm grow cc0])
        show "cc \<le> T" using ccT by linarith
        show "\<And>s. 0 \<le> s \<Longrightarrow> s < cc \<Longrightarrow> fst (\<omega> s)
            \<in> {w. \<rho> < norm (w - y\<^sub>0)} \<inter> ball y\<^sub>0 rB"
          by (rule IN)
      qed
      have "(norm (fst (\<omega> cc) - y\<^sub>0))\<^sup>2 < rB\<^sup>2"
      proof -
        have "cc * cn < \<delta>f * cn"
          using ccdf cn0 by (intro mult_strict_right_mono)
        also have "\<delta>f * cn = rB\<^sup>2 - \<rho>\<^sub>0\<^sup>2"
          unfolding \<delta>f_def using cn0 by simp
        finally show ?thesis
          unfolding csq \<rho>\<^sub>0_def[symmetric] by linarith
      qed
      then have "norm (fst (\<omega> cc) - y\<^sub>0) < rB"
        using rB0 by (metis norm_ge_zero power2_le_imp_le
            linorder_not_less nless_le)
      then have "fst (\<omega> cc) \<in> ball y\<^sub>0 rB"
        by (simp add: mem_ball dist_norm norm_minus_commute)
      then show ?thesis unfolding seq .
    qed
    have inK: "fst (\<omega> s) \<in> K" if s0: "0 \<le> s" and sc: "s \<le> cc" for s
      using inB[OF s0 sc] sub ball_subset_cball by blast
    have pex: "pexit cc K (\<lambda>t. fst (\<omega> t)) = cc"
      by (rule pexit_eq_of_stays[OF cc0']) (use inK in simp)
    have XccK: "fst (\<omega> cc) \<in> K" using inK[of cc] cc0 by simp
    have fn: "pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (paper_v k L (T - cc) K (fst (\<omega> cc))) else 0)
        = cc + enn2real (paper_v k L (T - cc) K (fst (\<omega> cc)))"
      using pex XccK by simp
    have XccB: "fst (\<omega> cc) \<in> ball y\<^sub>0 rB"
      using inB[of cc] cc0 by simp
    have s1: "0 \<le> T - cc" using ccT by linarith
    have s2: "T - cc \<le> T" using cc0 by linarith
    have cap: "enn2real (paper_v k L (T - cc) K (fst (\<omega> cc)))
        = min (enn2real (paper_v k L T K (fst (\<omega> cc)))) (T - cc)"
      by (rule enn2real_paper_v_horizon_cap[OF s1 s2 L1 Kc])
    have vge: "min \<beta> (T / 2)
        \<le> enn2real (paper_v k L (T - cc) K (fst (\<omega> cc)))"
    proof -
      have b1: "\<beta> \<le> enn2real (paper_v k L T K (fst (\<omega> cc)))"
        by (rule vlow[OF XccB])
      have b2: "T / 2 \<le> T - cc" using ccT2 by linarith
      have c1: "min \<beta> (T / 2) \<le> \<beta>" by (rule min.cobounded1)
      have c2: "min \<beta> (T / 2) \<le> T / 2" by (rule min.cobounded2)
      have d1: "min \<beta> (T / 2)
          \<le> enn2real (paper_v k L T K (fst (\<omega> cc)))"
        using c1 b1 by linarith
      have d2: "min \<beta> (T / 2) \<le> T - cc" using c2 b2 by linarith
      show ?thesis unfolding cap using d1 d2 by simp
    qed
    have "cc + min \<beta> (T / 2)
        \<le> cc + enn2real (paper_v k L (T - cc) K (fst (\<omega> cc)))"
      using vge by linarith
    then show ?case unfolding fn by (intro ennreal_leI) simp
  qed
  have essge: "ennreal (cc + min \<beta> (T / 2)) \<le> ess_inf_time P
      (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (paper_v k L (T - cc) K (fst (\<omega> cc))) else 0))"
    unfolding ess_inf_time_def
    by (rule Sup_upper) (use AEfun in blast)
  have esle: "ess_inf_time P
      (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
        + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
           then enn2real (paper_v k L (T - cc) K (fst (\<omega> cc))) else 0))
      \<le> paper_v k L T K x"
  proof -
    have "ess_inf_time P
        (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
          + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
             then enn2real (paper_v k L (T - cc) K (fst (\<omega> cc))) else 0))
        \<le> (SUP P' \<in> paper_pair_class k L T x. ess_inf_time P'
          (\<lambda>\<omega>. pexit cc K (\<lambda>t. fst (\<omega> t))
            + (if pexit cc K (\<lambda>t. fst (\<omega> t)) = cc \<and> fst (\<omega> cc) \<in> K
               then enn2real (paper_v k L (T - cc) K (fst (\<omega> cc)))
               else 0)))"
      by (rule SUP_upper[OF P])
    also have "\<dots> \<le> paper_v k L T K x"
      by (rule paper_v_dpp_sup_ge[OF less_imp_le[OF cc0] ccT L1 Kc])
    finally show ?thesis .
  qed
  have "ennreal (cc + min \<beta> (T / 2)) \<le> paper_v k L T K x"
    by (rule order_trans[OF essge esle])
  moreover have "cc = min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))"
  proof -
    have e: "\<delta>f / 2
        = (rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))"
      unfolding \<delta>f_def \<rho>\<^sub>0_def cn_def
      using cn0 unfolding cn_def by (simp add: mult_ac)
    show ?thesis unfolding cc_def e by (rule refl)
  qed
  ultimately show ?thesis by simp
qed

text \<open>The original ball bound is the case \<open>\<beta> = 0\<close>: the value at the
  exit point is simply dropped.\<close>

corollary paper_v_ball_lower:
  fixes K :: "(real^'n::finite) set" and y\<^sub>0 x :: "real^'n"
    and rB T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)"
    and Kc: "closed K" and sub: "cball y\<^sub>0 rB \<subseteq> K"
    and xy: "x \<noteq> y\<^sub>0" and xin: "norm (x - y\<^sub>0) < rB"
  shows "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))))
      \<le> paper_v k L T K x"
proof -
  have z: "(0 :: real) \<le> 0" by simp
  have v0: "\<And>w. w \<in> ball y\<^sub>0 rB \<Longrightarrow>
      (0 :: real) \<le> enn2real (paper_v k L T K w)" by simp
  have "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (x - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min 0 (T / 2))
      \<le> paper_v k L T K x"
    by (rule paper_v_ball_lower_plus[OF T0 L1 k1 kn Kc sub xy xin z v0])
  then show ?thesis using T0 by simp
qed

section \<open>The paper's supersolution: touching the lower envelope\<close>

text \<open>Definition 3.1(b) of the paper touches the LOWER SEMICONTINUOUS
  ENVELOPE \<open>u\<^sub>*\<close>, not \<open>u\<close> itself.  That is what makes the minimisers in
  the Case-2 dichotomy exist, and it is the form the comparison
  principle consumes.  This section builds the envelope, states the
  faithful supersolution notion, and records the two algebraic facts
  that let the ALREADY VERIFIED Euler machinery serve a process whose
  START is separated from the quadratic's CENTRE --- which is exactly
  what the envelope argument needs, since it runs the construction at
  points APPROACHING the touching point rather than at the touching
  point itself.\<close>

subsection \<open>The lower semicontinuous envelope\<close>

definition lsc_env :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real"
  where "lsc_env u x = (SUP e \<in> {0<..}. INF y \<in> ball x e. u y)"

lemma lsc_env_bdd_above:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "bdd_above ((\<lambda>e. INF y \<in> ball x e. u y) ` {0<..})"
proof (rule bdd_aboveI[of _ "u x"])
  fix z assume "z \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
  then obtain e where e: "0 < e" and z: "z = (INF y \<in> ball x e. u y)"
    by auto
  have bdd: "bdd_below (u ` ball x e)"
    by (rule bdd_belowI[of _ B]) (use B in auto)
  have "u x \<in> u ` ball x e" using e by auto
  then show "z \<le> u x" unfolding z by (rule cInf_lower[OF _ bdd])
qed

lemma lsc_env_le_self:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "lsc_env u x \<le> u x"
  unfolding lsc_env_def
proof (rule cSup_least)
  show "(\<lambda>e. INF y \<in> ball x e. u y) ` {0<..} \<noteq> {}" by auto
next
  fix z assume "z \<in> (\<lambda>e. INF y \<in> ball x e. u y) ` {0<..}"
  then obtain e where e: "0 < e" and z: "z = (INF y \<in> ball x e. u y)"
    by auto
  have bdd: "bdd_below (u ` ball x e)"
    by (rule bdd_belowI[of _ B]) (use B in auto)
  have "u x \<in> u ` ball x e" using e by auto
  then show "z \<le> u x" unfolding z by (rule cInf_lower[OF _ bdd])
qed

lemma lsc_env_ge:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y"
  shows "B \<le> lsc_env u x"
proof -
  have bdd: "bdd_below (u ` ball x 1)"
    by (rule bdd_belowI[of _ B]) (use B in auto)
  have "B \<le> (INF y \<in> ball x 1. u y)"
    by (rule cInf_greatest) (use B in auto)
  also have "\<dots> \<le> lsc_env u x"
    unfolding lsc_env_def
    by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) auto
  finally show ?thesis .
qed

text \<open>The property the envelope exists for: arbitrarily near \<open>x\<close> there
  are points where \<open>u\<close> is arbitrarily close to \<open>u\<^sub>*(x)\<close> from above.  This
  is what supplies the approximating sequence along which the
  construction is run.\<close>

lemma lsc_env_approx:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and d0: "0 < \<delta>" and e0: "0 < \<epsilon>"
  obtains y where "dist x y < \<delta>" and "u y < lsc_env u x + \<epsilon>"
proof -
  have bdd: "bdd_below (u ` ball x \<delta>)"
    by (rule bdd_belowI[of _ B]) (use B in auto)
  have ne: "u ` ball x \<delta> \<noteq> {}" using d0 by auto
  have le: "(INF y \<in> ball x \<delta>. u y) \<le> lsc_env u x"
    unfolding lsc_env_def
    by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use d0 in auto)
  have "(INF y \<in> ball x \<delta>. u y) < lsc_env u x + \<epsilon>"
    using le e0 by linarith
  then obtain z where z: "z \<in> u ` ball x \<delta>" and zlt: "z < lsc_env u x + \<epsilon>"
    using cInf_less_iff[OF ne bdd] by blast
  from z obtain y where y: "y \<in> ball x \<delta>" and uy: "z = u y" by auto
  show ?thesis
  proof (rule that)
    show "dist x y < \<delta>" using y by (simp add: mem_ball)
    show "u y < lsc_env u x + \<epsilon>" using zlt unfolding uy .
  qed
qed

subsection \<open>The faithful supersolution property\<close>

text \<open>Definition 3.1(b), verbatim: the test function touches the LOWER
  ENVELOPE from below, globally on \<open>K\<close>, and the conclusion is the
  inequality for the UPPER envelope \<open>F\<^sup>*\<close> of the operator.\<close>

definition visc_supersol_lsc ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> (real^'n) set
     \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_lsc k L K \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H)"

subsection \<open>Recentring the quadratic\<close>

text \<open>The two facts that make the envelope argument affordable.  A
  quadratic centred at \<open>x\<close> IS, up to the additive constant of its value
  at \<open>y\<close>, the quadratic centred at \<open>y\<close> with gradient \<open>q + M(y-x)\<close> ---
  and the two have the SAME gradient field \<open>q + M(\<sqdot> - x)\<close>, so the kill
  hypothesis is literally unchanged.  Consequently every verified
  theorem about a process started at its quadratic's centre applies
  verbatim to a process started at \<open>y\<close> with the quadratic centred at
  \<open>x\<close>, and no part of the Euler chain has to be re-derived.\<close>

lemma quad_grad_shift:
  fixes M :: "real^'n::finite^'n" and q x y z :: "real^'n"
  shows "(q + M *v (y - x)) + M *v (z - y) = q + M *v (z - x)"
proof -
  have "M *v (z - x) = M *v ((y - x) + (z - y))"
    by (rule arg_cong[where f = "\<lambda>v. M *v v"]) simp
  also have "\<dots> = M *v (y - x) + M *v (z - y)"
    by (rule matrix_vector_right_distrib)
  finally show ?thesis by simp
qed

lemma quad_shift:
  fixes M :: "real^'n::finite^'n" and q x y z :: "real^'n"
  assumes sym: "transpose M = M"
  shows "q \<bullet> (z - x) + (1/2) * ((z - x) \<bullet> (M *v (z - x)))
      = (q \<bullet> (y - x) + (1/2) * ((y - x) \<bullet> (M *v (y - x))))
        + ((q + M *v (y - x)) \<bullet> (z - y)
           + (1/2) * ((z - y) \<bullet> (M *v (z - y))))"
  using quad_taylor_step[OF sym, where q = q and x = x and a = y and b = z]
  by linarith

subsection \<open>Growth up to a time, on a region\<close>

text \<open>@{thm [source] quad_good_upto} with the confinement region and the
  quadratic's centre both free.  Only reachability from below is used,
  so the proof is the same sequence-and-continuity passage.\<close>

lemma quad_good_upto_region:
  fixes \<omega> :: "'n::finite pairpath" and q x :: "real^'n"
    and M :: "real^'n^'n" and c cm t :: real and RO :: "(real^'n) set"
  assumes wm: "\<omega> \<in> mspace (path_metric c :: ('n pairpath) metric)"
    and good: "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> c \<Longrightarrow>
      (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> RO) \<Longrightarrow>
      t' * cm / 2 \<le> q \<bullet> (fst (\<omega> t') - x)
        + (1/2) * ((fst (\<omega> t') - x) \<bullet> (M *v (fst (\<omega> t') - x)))"
    and t0: "0 < t" and tc: "t \<le> c"
    and inb: "\<And>s. 0 \<le> s \<Longrightarrow> s < t \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "t * cm / 2 \<le> q \<bullet> (fst (\<omega> t) - x)
      + (1/2) * ((fst (\<omega> t) - x) \<bullet> (M *v (fst (\<omega> t) - x)))"
proof -
  define g where "g = (\<lambda>s. q \<bullet> (fst (\<omega> s) - x)
      + (1/2) * ((fst (\<omega> s) - x) \<bullet> (M *v (fst (\<omega> s) - x))))"
  have gc: "continuous_on {0..c} g"
    unfolding g_def by (rule quad_eval_cont[OF wm])
  define tj where "tj = (\<lambda>j. t - t / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "t / (2 * real (Suc j)) \<le> t / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> t" using t0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using t0 by linarith
  qed
  have tju: "tj j < t" for j
  proof -
    have "0 < t / (2 * real (Suc j))" using t0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjc: "tj j \<le> c" for j using tju[of j] tc by linarith
  have glow: "tj j * cm / 2 \<le> g (tj j)" for j
    unfolding g_def
  proof (rule good)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> c" by (rule tjc)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < t" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inb)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> t"
  proof -
    have eq: "(\<lambda>j. (t / 2) * inverse (real (Suc j)))
        = (\<lambda>j. t / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (t / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (t / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. t / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. t - t / (2 * real (Suc j))) \<longlonglongrightarrow> t - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g t"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..c}"
      using tjl tjc by (auto intro: less_imp_le)
    have tS: "t \<in> {0..c}" using t0 tc by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g t"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS tS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have lim1: "(\<lambda>j. tj j * cm / 2) \<longlonglongrightarrow> t * cm / 2"
    by (rule tendsto_divide[OF
        tendsto_mult[OF tjlim tendsto_const] tendsto_const]) simp
  have "t * cm / 2 \<le> g t"
    by (rule LIMSEQ_le[OF lim1 gcomp]) (use glow in blast)
  then show ?thesis unfolding g_def .
qed

subsection \<open>Case 1 for the lower envelope\<close>

text \<open>The touching-point argument at the ENVELOPE.  Two things change
  relative to @{thm [source] paper_v_supersol_contradiction_case1}.
  First, the horizon lemma is applied to the envelope, so it is stated
  for an arbitrary touching function with an explicit cap.  Second --
  and this is the whole point of the envelope -- the value at the
  touching point need not be attained there, so the construction is run
  at an approximating point \<open>y\<close> supplied by
  @{thm [source] lsc_env_approx}, with the quadratic still centred at
  \<open>x\<close>.  @{thm [source] quad_shift} and @{thm [source] quad_grad_shift}
  make the verified machinery serve that configuration unchanged: the
  gradient field is the same, so the kill hypothesis is the same, and
  the only trace of the displacement is the additive constant \<open>\<psi>(y)\<close>,
  which the choice of \<open>y\<close> drives below any prescribed margin.\<close>

lemma touching_grad_lt_horizon_gen:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and W :: "real^'n \<Rightarrow> real"
  assumes xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and rho0: "0 < \<rho>"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      W x - \<phi> x \<le> W y - \<phi> y"
    and bnd: "\<And>y. y \<in> K \<Longrightarrow> W y \<le> T"
    and gx0: "g x \<noteq> 0"
  shows "W x < T"
proof -
  obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
    using xi mem_interior by blast
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  define h where "h = (\<lambda>s. \<phi> (x + s *\<^sub>R g x))"
  have hd: "(h has_field_derivative (g x \<bullet> g x)) (at 0)"
  proof -
    have i1: "((\<lambda>s :: real. x + s *\<^sub>R g x)
        has_derivative (\<lambda>u. u *\<^sub>R g x)) (at 0)"
      by (auto intro!: derivative_eq_intros)
    have mem0: "x + (0::real) *\<^sub>R g x \<in> ball x e" using e0 by simp
    have i2: "(\<phi> has_derivative (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> u))
        (at (x + (0::real) *\<^sub>R g x))"
      by (rule dphi[OF mem0])
    have "((\<lambda>s. \<phi> (x + s *\<^sub>R g x)) has_derivative
        (\<lambda>u. g (x + (0::real) *\<^sub>R g x) \<bullet> (u *\<^sub>R g x))) (at 0)"
      using diff_chain_at[OF i1 i2] by (simp add: o_def)
    then show ?thesis unfolding h_def
      by (rule has_derivative_imp_has_field_derivative)
        (simp add: inner_scaleR_right ac_simps)
  qed
  have gg0: "0 < g x \<bullet> g x"
    using gx0 by (simp add: inner_gt_zero_iff)
  have "((\<lambda>s. (h s - h 0) / (s - 0)) \<longlongrightarrow> g x \<bullet> g x) (at 0)"
    using hd by (simp add: has_field_derivative_iff)
  then have "\<forall>\<^sub>F s in at (0::real). 0 < (h s - h 0) / (s - 0)"
    by (rule order_tendstoD(1)[OF _ gg0])
  then obtain d where d0: "0 < d"
    and hpos: "\<And>s :: real. s \<noteq> 0 \<Longrightarrow> \<bar>s\<bar> < d \<Longrightarrow> 0 < (h s - h 0) / s"
    unfolding eventually_at by (auto simp: dist_real_def)
  define ng where "ng = norm (g x) + 1"
  have ng0: "0 < ng" unfolding ng_def
    using norm_ge_zero[of "g x"] by linarith
  define s where
    "s = min (min d (e / ng)) (min (eK / ng) (\<rho> / ng)) / 2"
  have s0: "0 < s"
    unfolding s_def using d0 e0 eK0 ng0 rho0 by simp
  have sd: "s < d" unfolding s_def using d0 e0 eK0 ng0 rho0 by auto
  have se: "s * ng < e"
  proof -
    have "s \<le> (e / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> e / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using e0 by linarith
  qed
  have sK: "s * ng < eK"
  proof -
    have "s \<le> (eK / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> eK / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using eK0 by linarith
  qed
  have sR: "s * ng < \<rho>"
  proof -
    have "s \<le> (\<rho> / ng) / 2" unfolding s_def by simp
    then have "s * ng \<le> \<rho> / 2" using ng0 by (simp add: field_simps)
    then show ?thesis using rho0 by linarith
  qed
  have sg_lt: "s * norm (g x) < min e (min eK \<rho>)"
  proof -
    have "s * norm (g x) \<le> s * ng"
      unfolding ng_def using s0 by (intro mult_left_mono) auto
    then show ?thesis using se sK sR by simp
  qed
  define z where "z = x + s *\<^sub>R g x"
  have dz: "dist x z = s * norm (g x)"
    unfolding z_def dist_norm using s0 by (simp add: abs_of_nonneg)
  have zK: "z \<in> K"
  proof -
    have "z \<in> ball x eK" using dz sg_lt by (simp add: mem_ball)
    then show ?thesis using eKK by blast
  qed
  have zR: "dist x z < \<rho>" using dz sg_lt by simp
  have hgt: "\<phi> x < \<phi> z"
  proof -
    have "0 < (h s - h 0) / s" using hpos[of s] s0 sd by simp
    then have "0 < h s - h 0" using s0 by (simp add: zero_less_divide_iff)
    then show ?thesis unfolding h_def z_def by simp
  qed
  have "W x \<le> W z - (\<phi> z - \<phi> x)" using tmin[OF zK zR] by simp
  also have "\<dots> < W z" using hgt by simp
  also have "\<dots> \<le> T" by (rule bnd[OF zK])
  finally show ?thesis .
qed

theorem paper_v_supersol_contradiction_case1_lsc:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k"
    and kn: "k < CARD('n)" and Kc: "closed K"
    and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and rho0: "0 < \<rho>"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      lsc_env (\<lambda>z. enn2real (paper_v k L T K z)) x - \<phi> x
        \<le> lsc_env (\<lambda>z. enn2real (paper_v k L T K z)) y - \<phi> y"
    and gx0: "g x \<noteq> 0"
    and fail: "ell_op k L (g x) H < 1"
  shows False
proof -
  have L1': "1 \<le> L" using L1 by linarith
  have L0: "0 \<le> L" using L1 by linarith
  have T0': "0 \<le> T" using T0 by linarith
  define tv where "tv = (\<lambda>y. enn2real (paper_v k L T K y))"
  define vs where "vs = lsc_env tv"
  have tv0: "\<And>z. 0 \<le> tv z" unfolding tv_def by simp
  have tvT: "\<And>z. tv z \<le> T"
  proof -
    fix z :: "real^'n"
    have "tv z = min (tv z) T"
      unfolding tv_def
      by (rule enn2real_paper_v_horizon_cap[OF T0' order_refl L1' Kc])
    then show "tv z \<le> T" by linarith
  qed
  have vs_le: "\<And>z. vs z \<le> tv z"
    unfolding vs_def by (rule lsc_env_le_self[OF tv0])
  have vs_ge: "\<And>z. 0 \<le> vs z"
    unfolding vs_def by (rule lsc_env_ge[OF tv0])
  have tminv: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      vs x - \<phi> x \<le> vs y - \<phi> y"
    unfolding vs_def tv_def by (rule tmin)
  have vxT: "vs x < T"
  proof (rule touching_grad_lt_horizon_gen[OF xi tf rho0 tminv _ gx0])
    fix y :: "real^'n" assume "y \<in> K"
    show "vs y \<le> T" using vs_le[of y] tvT[of y] by linarith
  qed
  obtain a where aF: "a \<in> feasible k L (g x)"
    and aTr: "- trace (H ** a) / 2 < 1"
    by (rule ell_op_lt_witness[OF k1 kn L1' fail])
  define \<eta>\<^sub>0 where "\<eta>\<^sub>0 = (1 - (- trace (H ** a) / 2)) / 2"
  have h00: "0 < \<eta>\<^sub>0" unfolding \<eta>\<^sub>0_def using aTr by simp
  have trH: "2 * \<eta>\<^sub>0 \<le> 1 + trace (H ** a) / 2"
    unfolding \<eta>\<^sub>0_def by simp
  have aS: "a \<in> sconstraint k L"
    using aF feasible_subset_sconstraint by blast
  define TB where "TB = real CARD('n) * (real CARD('n) * L)"
  have trab: "trace a \<le> TB"
    unfolding TB_def by (rule sconstraint_trace_le[OF L0 aS])
  have tra0: "0 \<le> trace a"
    using sconstraint_trace_ge[OF kn aS] by linarith
  have TB1: "0 < TB + 1"
  proof -
    have "0 \<le> TB" using trab tra0 by linarith
    then show ?thesis by linarith
  qed
  define sft where "sft = min (\<eta>\<^sub>0 / (TB + 1)) 1"
  have sft0: "0 < sft"
    unfolding sft_def using h00 TB1 by simp
  define \<gamma> where "\<gamma> = sft / 4"
  define \<delta> where "\<delta> = sft / 2"
  have g0: "0 < \<gamma>" unfolding \<gamma>_def using sft0 by simp
  have d0: "0 < \<delta>" unfolding \<delta>_def using sft0 by simp
  have gd_le: "2 * \<gamma> + \<delta> \<le> sft" unfolding \<gamma>_def \<delta>_def by simp
  define M where "M = H - (2 * \<gamma> + \<delta>) *\<^sub>R mat 1"
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have symM: "transpose M = M"
    unfolding M_def by (rule transpose_sub_smat[OF symH])
  define \<eta> where "\<eta> = \<eta>\<^sub>0 / 2"
  have e0: "0 < \<eta>" unfolding \<eta>_def using h00 by simp
  have trM: "2 * \<eta> \<le> 1 + trace (M ** a) / 2"
  proof -
    have tr_eq: "trace (M ** a) = trace (H ** a) - (2 * \<gamma> + \<delta>) * trace a"
      unfolding M_def by (rule trace_msub_mat)
    have "(2 * \<gamma> + \<delta>) * trace a \<le> sft * trace a"
      by (rule mult_right_mono[OF gd_le tra0])
    also have "\<dots> \<le> (\<eta>\<^sub>0 / (TB + 1)) * (TB + 1)"
    proof (rule mult_mono)
      show "sft \<le> \<eta>\<^sub>0 / (TB + 1)" unfolding sft_def by simp
      show "trace a \<le> TB + 1" using trab by linarith
      show "0 \<le> \<eta>\<^sub>0 / (TB + 1)" using h00 TB1 by simp
      show "0 \<le> trace a" by (rule tra0)
    qed
    also have "\<dots> = \<eta>\<^sub>0" using TB1 by simp
    finally have "(2 * \<gamma> + \<delta>) * trace a \<le> \<eta>\<^sub>0" .
    then show ?thesis unfolding \<eta>_def using trH tr_eq h00 by linarith
  qed
  show False
  proof (rule feasible_strict_eigendata[OF aF kn L1 trM e0])
    fix B Bp :: "(real^'n) set" and lam :: "real^'n \<Rightarrow> real" and m :: real
    assume Bon: "onormal B" and Bsp: "span B = UNIV" and Bfin: "finite B"
      and BpB: "Bp \<subseteq> B" and cBp: "card Bp = CARD('n) - k" and m0: "0 < m"
      and lam_box: "\<And>u. u \<in> B \<Longrightarrow> 0 \<le> lam u \<and> lam u \<le> L - m"
      and lam_lb: "\<And>u. u \<in> Bp \<Longrightarrow> 1 + m \<le> lam u"
      and lam_orth: "\<And>u. u \<in> B \<Longrightarrow> 0 < lam u \<Longrightarrow> u \<bullet> (g x) = 0"
      and treig: "\<eta> \<le> 1 + trace (M **
          (\<Sum>u\<in>B. lam u *\<^sub>R outer_prod u u)) / 2"
    show False
    proof -
      have cardB: "card B = CARD('n)" by (rule onormal_span_card[OF Bon Bsp])
      have mL: "m \<le> L"
      proof -
        have "B \<noteq> {}" using cardB kn by auto
        then obtain u where uB: "u \<in> B" by blast
        from lam_box[OF uB] show ?thesis using m0 by linarith
      qed
      obtain f where bijf: "bij_betw f (UNIV :: 'n set) B"
        by (rule exists_enum_of_card[OF Bfin cardB])
      obtain rphi where rphi0: "0 < rphi"
        and mino: "\<And>z. z \<in> ball x rphi \<Longrightarrow>
          \<phi> x + g x \<bullet> (z - x)
            + ((z - x) \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
        using test_fun_quadratic_minorates[OF tf d0] by metis
      obtain eK where eK0: "0 < eK" and eKK: "ball x eK \<subseteq> K"
        using xi mem_interior by blast
      define Cm where "Cm = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>M $ i $ j\<bar>)"
      have Cm0: "0 \<le> Cm" unfolding Cm_def by (intro sum_nonneg) simp_all
      define ec where "ec = 2 * sqrt L * Cm / norm (g x)"
      define f1 where "f1 = (\<lambda>r. (1 + 1 / (m / (2 * L)))
          * (real CARD('n) * (ec * r)\<^sup>2))"
      define f2 where "f2 = (\<lambda>r. real CARD('n)
          * (ec * r * (2 * sqrt L + ec * r))
          + 2 * (1 + m) / m
            * (real CARD('n) * (ec * r * (2 * sqrt L + ec * r)))\<^sup>2)"
      define f3 where "f3 = (\<lambda>r. real CARD('n)
          * (Cm * (ec * r * (2 * sqrt L + ec * r))))"
      have c1: "isCont f1 0" unfolding f1_def
        by (auto intro!: continuous_intros)
      have c2: "isCont f2 0" unfolding f2_def
        using m0 by (auto intro!: continuous_intros)
      have c3: "isCont f3 0" unfolding f3_def
        by (auto intro!: continuous_intros)
      have z1: "f1 0 = 0" unfolding f1_def by simp
      have z2: "f2 0 = 0" unfolding f2_def by simp
      have z3: "f3 0 = 0" unfolding f3_def by simp
      have m20: "0 < m / 2" using m0 by simp
      have rmx0: "0 < min (rphi / 2) (min (eK / 2) (\<rho> / 2))"
        using rphi0 eK0 rho0 by simp
      obtain rr where rr0: "0 < rr"
        and rrx: "rr \<le> min (rphi / 2) (min (eK / 2) (\<rho> / 2))"
        and s1: "f1 rr \<le> m / 2" and s2: "f2 rr \<le> m / 2" and s3: "f3 rr \<le> \<eta>"
        by (rule small_radius_exists[OF c1 c2 c3 z1 z2 z3 m20 m20 e0 rmx0])
      have rr_phi: "rr < rphi" and rr_K: "rr < eK" and rr_rho: "rr < \<rho>"
        using rrx rphi0 eK0 rho0 by auto
      have cb_phi: "cball x rr \<subseteq> ball x rphi"
        using rr_phi by (auto simp: mem_cball mem_ball)
      have cb_K: "cball x rr \<subseteq> K"
      proof -
        have "cball x rr \<subseteq> ball x eK"
          using rr_K by (auto simp: mem_cball mem_ball)
        then show ?thesis using eKK by blast
      qed
      define SF where "SF = skewSF lam f (g x) M x rr"
      have SFc: "continuous_on UNIV SF"
        unfolding SF_def by (rule skewSF_cont[OF less_imp_le[OF rr0]])
      note pack = skewSF_package[OF bijf Bon Bsp BpB cBp lam_box lam_lb
          lam_orth m0 mL gx0 treig less_imp_le[OF rr0]
          s1[unfolded f1_def ec_def Cm_def]
          s2[unfolded f2_def ec_def Cm_def]
          s3[unfolded f3_def ec_def Cm_def]]
      have SFs: "\<And>z. SF z ** transpose (SF z) \<in> sconstraint k L"
        unfolding SF_def by (rule pack(1))
      have killc: "\<And>z. transpose (SF z) *v
          (g x + M *v (closest_point (cball x rr) z - x)) = 0"
        unfolding SF_def by (rule pack(2))
      have marg: "\<And>z. \<eta> - 2 \<le> trace (M ** (SF z ** transpose (SF z)))"
        unfolding SF_def by (rule pack(3))
      \<comment> \<open>on the ball the clamp is the identity, so the kill is the plain one\<close>
      have killR: "\<And>z. z \<in> ball x rr \<Longrightarrow>
          transpose (SF z) *v (g x + M *v (z - x)) = 0"
      proof -
        fix z :: "real^'n" assume "z \<in> ball x rr"
        then have "z \<in> cball x rr" using ball_subset_cball by blast
        then have "closest_point (cball x rr) z = z"
          by (intro closest_point_self)
        then show "transpose (SF z) *v (g x + M *v (z - x)) = 0"
          using killc[of z] by simp
      qed
      define cc where "cc = T / 2"
      have cc0: "0 < cc" unfolding cc_def using T0 by simp
      have ccT: "cc < T" unfolding cc_def using T0 by simp
      have ccT': "cc \<le> T" using ccT by linarith
      define mg where "mg = min (min (\<gamma> * rr\<^sup>2) (cc * \<eta> / 2)) ((T - vs x) / 2)"
      have mg0: "0 < mg"
      proof -
        have "0 < \<gamma> * rr\<^sup>2" using g0 rr0 by simp
        moreover have "0 < cc * \<eta> / 2" using cc0 e0 by simp
        moreover have "0 < (T - vs x) / 2" using vxT by simp
        ultimately show ?thesis unfolding mg_def by simp
      qed
      define cy where "cy = norm (g x) + 2 * Cm + 1"
      have cy1: "1 \<le> cy" unfolding cy_def
        using norm_ge_zero[of "g x"] Cm0 by linarith
      have cy0: "0 < cy" using cy1 by linarith
      define \<delta>y where "\<delta>y = min (rr / 2) (min 1 ((mg / 4) / cy))"
      have dy0: "0 < \<delta>y" unfolding \<delta>y_def using rr0 mg0 cy0 by simp
      have mg20: "0 < mg / 2" using mg0 by simp
      obtain y where dxy: "dist x y < \<delta>y"
          and tvy0: "tv y < lsc_env tv x + mg / 2"
        by (rule lsc_env_approx[OF tv0 dy0 mg20])
      have tvy: "tv y < vs x + mg / 2" unfolding vs_def by (rule tvy0)
      have nyx: "norm (y - x) < \<delta>y"
        using dxy by (simp add: dist_norm norm_minus_commute)
      have ny_rr: "norm (y - x) < rr"
      proof -
        have "\<delta>y \<le> rr / 2" unfolding \<delta>y_def by simp
        then show ?thesis using nyx rr0 by linarith
      qed
      have ny1: "norm (y - x) \<le> 1"
      proof -
        have "\<delta>y \<le> 1" unfolding \<delta>y_def by simp
        then show ?thesis using nyx by linarith
      qed
      have ny_c: "norm (y - x) \<le> (mg / 4) / cy"
      proof -
        have "\<delta>y \<le> (mg / 4) / cy" unfolding \<delta>y_def by simp
        then show ?thesis using nyx by linarith
      qed
      define qy where "qy = g x + M *v (y - x)"
      define psiY where "psiY = g x \<bullet> (y - x)
          + (1/2) * ((y - x) \<bullet> (M *v (y - x)))"
      \<comment> \<open>the displacement costs only the constant \<open>\<psi>(y)\<close>, and it is small\<close>
      have psiY_small: "\<bar>psiY\<bar> \<le> mg / 4"
      proof -
        have nx: "norm (x - x) \<le> norm (y - x)" by simp
        have nyy: "norm (y - x) \<le> norm (y - x)" by simp
        have "\<bar>g x \<bullet> (y - x) + (1/2) * ((y - x) \<bullet> (M *v (y - x)))
            - (g x \<bullet> (x - x) + (1/2) * ((x - x) \<bullet> (M *v (x - x))))\<bar>
            \<le> (norm (g x) + 2 * Cm * norm (y - x)) * norm (y - x)"
          unfolding Cm_def
          by (rule quad_diff_bound_gen[OF symM nx nyy])
        then have base: "\<bar>psiY\<bar>
            \<le> (norm (g x) + 2 * Cm * norm (y - x)) * norm (y - x)"
          unfolding psiY_def by simp
        have "(norm (g x) + 2 * Cm * norm (y - x)) \<le> cy"
        proof -
          have "2 * Cm * norm (y - x) \<le> 2 * Cm * 1"
            using Cm0 ny1 by (intro mult_left_mono) simp_all
          then show ?thesis unfolding cy_def by simp
        qed
        then have "(norm (g x) + 2 * Cm * norm (y - x)) * norm (y - x)
            \<le> cy * norm (y - x)"
          by (rule mult_right_mono) simp
        also have "\<dots> \<le> cy * ((mg / 4) / cy)"
          by (rule mult_left_mono[OF ny_c]) (use cy0 in simp)
        also have "\<dots> = mg / 4" using cy0 by simp
        finally show ?thesis using base by linarith
      qed
      have psiY_ub: "psiY \<le> mg / 4"
        using psiY_small[unfolded abs_le_iff] by linarith
      \<comment> \<open>the growth package, run at \<open>y\<close> with the quadratic centred at \<open>x\<close>\<close>
      obtain P where Pc: "P \<in> paper_pair_class k L T y"
        and AEg: "AE \<omega> in P. \<forall>t.
          0 < t \<longrightarrow> t \<le> T \<longrightarrow> (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> ball x rr) \<longrightarrow>
          (t * (\<eta> - 2) / 2 \<le> qy \<bullet> (fst (\<omega> t) - y)
            + (1/2) * ((fst (\<omega> t) - y) \<bullet> (M *v (fst (\<omega> t) - y))))
          \<and> (t * (\<eta> - 2) / 2 \<le> qy \<bullet> (fst (\<omega> t) - y)
            + (1/2) * ((fst (\<omega> t) - y) \<bullet> (M *v (fst (\<omega> t) - y))))"
      proof -
        have ROo: "open (ball x rr)" by (rule open_ball)
        have ROb: "\<And>z. z \<in> ball x rr \<Longrightarrow> norm (z - y) \<le> 2 * rr"
        proof -
          fix z :: "real^'n" assume "z \<in> ball x rr"
          then have nz: "norm (z - x) < rr"
            by (simp add: mem_ball dist_norm norm_minus_commute)
          have "z - y = (z - x) + (x - y)" by simp
          then have "norm (z - y) \<le> norm (z - x) + norm (x - y)"
            by (metis norm_triangle_ineq)
          moreover have "norm (x - y) < rr"
            using ny_rr by (simp add: norm_minus_commute)
          ultimately show "norm (z - y) \<le> 2 * rr" using nz by linarith
        qed
        have killy: "\<And>z. z \<in> ball x rr \<Longrightarrow>
            transpose (SF z) *v (qy + M *v (z - y)) = 0"
        proof -
          fix z :: "real^'n" assume zb: "z \<in> ball x rr"
          have "qy + M *v (z - y) = g x + M *v (z - x)"
            unfolding qy_def by (rule quad_grad_shift)
          then show "transpose (SF z) *v (qy + M *v (z - y)) = 0"
            using killR[OF zb] by simp
        qed
        have margy: "\<And>z. z \<in> ball x rr \<Longrightarrow>
            \<eta> - 2 \<le> trace (M ** (SF z ** transpose (SF z)))"
          using marg by blast
        show ?thesis
          using eulerp_limit_good2_region[OF T0 L1' SFc SFs symM symM
              ROo ROb killy margy killy margy] that by blast
      qed
      have setsP: "sets P = sets (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
        by (rule paper_pair_class_sets[OF Pc])
      have spaceP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
        by (rule space_of_path_sets[OF setsP])
      have start: "AE \<omega> in P. fst (\<omega> 0) = y \<and> snd (\<omega> 0) = 0"
        by (rule paper_pair_class_start[OF Pc])
      have sp: "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
      define \<theta> where "\<theta> = (\<lambda>\<omega> :: 'n pairpath. min cc (pball_exit T x rr \<omega>))"
      have st: "path_stopping_time T \<theta>"
        unfolding \<theta>_def
        by (rule path_stopping_time_min[OF
              pball_exit_path_stopping_time[OF T0']
              less_imp_le[OF cc0] ccT'])
      have thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
        unfolding \<theta>_def
        by (intro borel_measurable_min pball_exit_measurable[OF T0']
            borel_measurable_const)
      define FN where "FN = (\<lambda>\<omega> :: 'n pairpath.
          pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
          + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>
                \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
             then enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
             else 0))"
      have dpp: "(SUP P' \<in> paper_pair_class k L T y. ess_inf_time P' FN)
          \<le> paper_v k L T K y"
        unfolding FN_def
        by (rule paper_v_dpp_sup_ge_time[OF T0 L1' Kc st thM])
      have AEfun: "AE \<omega> in P. ennreal (vs x + mg + psiY) \<le> ennreal (FN \<omega>)"
        using AEg start sp
      proof (eventually_elim)
        case (elim \<omega>)
        have wsp: "\<omega> \<in> space P" using elim(3) .
        have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using wsp by (simp add: spaceP)
        have y0: "fst (\<omega> 0) = y" using elim(2) by blast
        have cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
          by (rule path_sets_fst_continuous[OF setsP wsp])
        have sdist: "dist (fst (\<omega> 0)) x < rr"
          using y0 ny_rr by (simp add: dist_norm norm_minus_commute)
        define \<tau> where "\<tau> = pball_exit T x rr \<omega>"
        have tau0: "0 < \<tau>" unfolding \<tau>_def
          by (rule pball_exit_pos[OF T0 sdist cont])
        have tauT: "\<tau> \<le> T" unfolding \<tau>_def by (rule pball_exit_le[OF T0'])
        have thw: "\<theta> \<omega> = min cc \<tau>" unfolding \<theta>_def \<tau>_def by (rule refl)
        have th0: "0 < \<theta> \<omega>" unfolding thw using cc0 tau0 by simp
        have thcc: "\<theta> \<omega> \<le> cc" unfolding thw by simp
        have thtau: "\<theta> \<omega> \<le> \<tau>" unfolding thw by simp
        have thT: "\<theta> \<omega> < T" using thcc ccT by linarith
        have stays: "\<And>s. s \<in> {0..\<tau>} \<Longrightarrow> fst (\<omega> s) \<in> cball x rr"
        proof -
          fix s assume s: "s \<in> {0..\<tau>}"
          have "dist (fst (\<omega> s)) x \<le> rr"
            using pball_exit_stays_cball[OF T0' sdist cont, of s] s
            unfolding \<tau>_def by auto
          then show "fst (\<omega> s) \<in> cball x rr"
            by (simp add: mem_cball dist_commute)
        qed
        have inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < \<tau> \<Longrightarrow> fst (\<omega> s) \<in> ball x rr"
        proof -
          fix s assume s0: "0 \<le> s" and st': "s < \<tau>"
          show "fst (\<omega> s) \<in> ball x rr"
          proof (rule ccontr)
            assume nb: "fst (\<omega> s) \<notin> ball x rr"
            have sT: "s \<le> T" using st' tauT by linarith
            have "pexit T (ball x rr) (\<lambda>t. fst (\<omega> t)) \<le> s"
              by (rule pexit_le_of_mem[OF T0' s0 sT]) (use nb in simp)
            then have "\<tau> \<le> s" unfolding \<tau>_def pball_exit_def .
            then show False using st' by linarith
          qed
        qed
        have inK: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> \<theta> \<omega> \<Longrightarrow> fst (\<omega> s) \<in> K"
        proof -
          fix s assume s0: "0 \<le> s" and sth: "s \<le> \<theta> \<omega>"
          have "s \<in> {0..\<tau>}" using s0 sth thtau by simp
          then have "fst (\<omega> s) \<in> cball x rr" by (rule stays)
          then show "fst (\<omega> s) \<in> K" using cb_K by blast
        qed
        have pex: "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega>"
          by (rule pexit_eq_of_stays[OF less_imp_le[OF th0]])
            (use inK in simp)
        have XinK: "fst (\<omega> (\<theta> \<omega>)) \<in> K" using inK[of "\<theta> \<omega>"] th0 by simp
        have cap: "enn2real (paper_v k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>))))
            = min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
          unfolding tv_def
          by (rule enn2real_paper_v_horizon_cap[OF _ _ L1' Kc])
            (use thT th0 in auto)
        have feq: "FN \<omega> = \<theta> \<omega> + min (tv (fst (\<omega> (\<theta> \<omega>)))) (T - \<theta> \<omega>)"
          unfolding FN_def using pex XinK cap by simp
        \<comment> \<open>growth at the stopping time, in the shifted coordinates\<close>
        have growth: "\<theta> \<omega> * (\<eta> - 2) / 2
            \<le> qy \<bullet> (fst (\<omega> (\<theta> \<omega>)) - y)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - y)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - y)))"
        proof (rule quad_good_upto_region[OF wm _ th0])
          show "\<theta> \<omega> \<le> T" using thT by linarith
          show "\<And>t'. 0 < t' \<Longrightarrow> t' \<le> T \<Longrightarrow>
              (\<forall>s\<in>{0..t'}. fst (\<omega> s) \<in> ball x rr) \<Longrightarrow>
              t' * (\<eta> - 2) / 2 \<le> qy \<bullet> (fst (\<omega> t') - y)
                + (1/2) * ((fst (\<omega> t') - y) \<bullet> (M *v (fst (\<omega> t') - y)))"
            using elim(1) by blast
          show "\<And>s. 0 \<le> s \<Longrightarrow> s < \<theta> \<omega> \<Longrightarrow> fst (\<omega> s) \<in> ball x rr"
          proof -
            fix s assume s0: "0 \<le> s" and sth: "s < \<theta> \<omega>"
            have "s < \<tau>" using sth thtau by linarith
            then show "fst (\<omega> s) \<in> ball x rr" using inside[OF s0] by blast
          qed
        qed
        \<comment> \<open>back to the quadratic centred at \<open>x\<close>\<close>
        define \<psi>X where "\<psi>X = g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
            + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - x)
                \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x)))"
        have shift: "\<psi>X = psiY
            + (qy \<bullet> (fst (\<omega> (\<theta> \<omega>)) - y)
              + (1/2) * ((fst (\<omega> (\<theta> \<omega>)) - y)
                  \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - y))))"
          unfolding \<psi>X_def psiY_def qy_def
          by (rule quad_shift[OF symM])
        have gX: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY \<le> \<psi>X"
          unfolding shift using growth by linarith
        \<comment> \<open>touching at the envelope, then the minorant\<close>
        have Xcb: "fst (\<omega> (\<theta> \<omega>)) \<in> cball x rr"
          using stays[of "\<theta> \<omega>"] th0 thtau by simp
        have Xphi: "fst (\<omega> (\<theta> \<omega>)) \<in> ball x rphi" using Xcb cb_phi by blast
        have XinR: "dist x (fst (\<omega> (\<theta> \<omega>))) < \<rho>"
        proof -
          have "dist x (fst (\<omega> (\<theta> \<omega>))) \<le> rr"
            using Xcb by (simp add: mem_cball dist_commute)
          then show ?thesis using rr_rho by linarith
        qed
        have touch: "vs x + (\<phi> (fst (\<omega> (\<theta> \<omega>))) - \<phi> x)
            \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
        proof -
          have "vs x + (\<phi> (fst (\<omega> (\<theta> \<omega>))) - \<phi> x) \<le> vs (fst (\<omega> (\<theta> \<omega>)))"
            using tminv[OF XinK XinR] by linarith
          then show ?thesis using vs_le[of "fst (\<omega> (\<theta> \<omega>))"] by linarith
        qed
        have minor: "\<phi> x + g x \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
            + ((fst (\<omega> (\<theta> \<omega>)) - x)
                \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))) / 2
            \<le> \<phi> (fst (\<omega> (\<theta> \<omega>)))"
          by (rule mino[OF Xphi])
        have soften: "(fst (\<omega> (\<theta> \<omega>)) - x)
            \<bullet> ((H - \<delta> *\<^sub>R mat 1) *v (fst (\<omega> (\<theta> \<omega>)) - x))
            = (fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (M *v (fst (\<omega> (\<theta> \<omega>)) - x))
              + 2 * \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
          unfolding M_def by (rule quad_soften_split)
        have tvX: "vs x + \<psi>X
            + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))
            \<le> tv (fst (\<omega> (\<theta> \<omega>)))"
          using touch minor soften unfolding \<psi>X_def by linarith
        have QQ: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY
            + (if \<tau> \<le> cc then \<gamma> * rr\<^sup>2 else 0)
            \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
        proof (cases "\<tau> \<le> cc")
          case True
          have theq: "\<theta> \<omega> = \<tau>" unfolding thw using True by simp
          have tauTs: "\<tau> < T" using True ccT by linarith
          have sphere: "dist (fst (\<omega> \<tau>)) x = rr"
          proof -
            have ge: "rr \<le> dist (fst (\<omega> \<tau>)) x"
              using pball_exit_outside[OF T0' cont] tauTs
              unfolding \<tau>_def by simp
            have inc: "fst (\<omega> \<tau>) \<in> cball x rr"
              using stays[of \<tau>] tau0 by simp
            then have "dist (fst (\<omega> \<tau>)) x \<le> rr"
              by (simp add: mem_cball dist_commute)
            then show ?thesis using ge by linarith
          qed
          have nrm: "norm (fst (\<omega> \<tau>) - x) = rr"
            using sphere by (simp add: dist_norm norm_minus_commute)
          have dsq: "(fst (\<omega> \<tau>) - x) \<bullet> (fst (\<omega> \<tau>) - x) = rr\<^sup>2"
            using nrm by (simp add: dot_square_norm)
          have dsq': "(fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x)
              = rr\<^sup>2"
            unfolding theq by (rule dsq)
          have "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY + \<gamma> * rr\<^sup>2
              \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
            unfolding dsq' using gX by linarith
          then show ?thesis using True by simp
        next
          case False
          have nn: "0 \<le> \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x) \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
            using g0 inner_ge_zero by (simp add: mult_nonneg_nonneg)
          have "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY
              \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                  \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
            using gX nn by linarith
          then show ?thesis using False by simp
        qed
        have fun_ge: "vs x + mg + psiY \<le> FN \<omega>"
        proof (cases "tv (fst (\<omega> (\<theta> \<omega>))) \<le> T - \<theta> \<omega>")
          case True
          have mfe: "FN \<omega> = \<theta> \<omega> + tv (fst (\<omega> (\<theta> \<omega>)))"
            unfolding feq using True by simp
          have id1: "\<theta> \<omega> * (\<eta> - 2) / 2 + \<theta> \<omega> = \<theta> \<omega> * \<eta> / 2"
            by (simp add: field_simps)
          show ?thesis
          proof (cases "\<tau> \<le> cc")
            case True
            have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY + \<gamma> * rr\<^sup>2
                \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                    \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
              using QQ True by simp
            have the0: "0 \<le> \<theta> \<omega> * \<eta> / 2" using th0 e0 by simp
            have mg1: "mg \<le> \<gamma> * rr\<^sup>2" unfolding mg_def by linarith
            show ?thesis
              unfolding mfe using tvX QQc id1 the0 mg1 by linarith
          next
            case False
            have QQc: "\<theta> \<omega> * (\<eta> - 2) / 2 + psiY
                \<le> \<psi>X + \<gamma> * ((fst (\<omega> (\<theta> \<omega>)) - x)
                    \<bullet> (fst (\<omega> (\<theta> \<omega>)) - x))"
              using QQ False by simp
            have theq: "\<theta> \<omega> = cc" unfolding thw using False by simp
            have mg2: "mg \<le> cc * \<eta> / 2" unfolding mg_def by linarith
            show ?thesis
              unfolding mfe theq
              using tvX[unfolded theq] QQc[unfolded theq]
                id1[unfolded theq] mg2
              by linarith
          qed
        next
          case False
          have mfe: "FN \<omega> = \<theta> \<omega> + (T - \<theta> \<omega>)"
            unfolding feq using False by simp
          have fT: "FN \<omega> = T" unfolding mfe by simp
          have m3: "mg \<le> (T - vs x) / 2"
            unfolding mg_def by (rule min.cobounded2)
          have mgT: "vs x + 2 * mg \<le> T"
          proof -
            have "(2::real) * mg \<le> 2 * ((T - vs x) / 2)"
              by (rule mult_left_mono[OF m3]) simp
            then have "2 * mg \<le> T - vs x" by simp
            then show ?thesis by (metis le_diff_eq add.commute)
          qed
          have "vs x + mg + psiY \<le> vs x + mg + mg / 4"
            using psiY_ub by linarith
          also have "\<dots> \<le> vs x + 2 * mg" using mg0 by linarith
          also have "\<dots> \<le> T" by (rule mgT)
          finally show ?thesis unfolding fT .
        qed
        show ?case by (rule ennreal_leI[OF fun_ge])
      qed
      have essge: "ennreal (vs x + mg + psiY) \<le> ess_inf_time P FN"
        unfolding ess_inf_time_def
        by (rule Sup_upper) (use AEfun in blast)
      have esle: "ess_inf_time P FN \<le> paper_v k L T K y"
      proof -
        have "ess_inf_time P FN
            \<le> (SUP P' \<in> paper_pair_class k L T y. ess_inf_time P' FN)"
          by (rule SUP_upper[OF Pc])
        then show ?thesis using dpp by (rule order_trans)
      qed
      have vfin: "ennreal (tv y) = paper_v k L T K y"
        unfolding tv_def
        using paper_v_neq_top[OF T0', of k L K y]
        by (simp add: ennreal_enn2real less_top)
      have chain: "ennreal (vs x + mg + psiY) \<le> ennreal (tv y)"
        using order_trans[OF essge esle] by (simp add: vfin)
      have nn: "0 \<le> tv y" by (rule tv0)
      have "vs x + mg + psiY \<le> tv y"
        using chain nn by (simp add: ennreal_le_iff)
      then show False using tvy psiY_small mg0 by linarith
    qed
  qed
qed

subsection \<open>Where the envelope is invisible\<close>

text \<open>Batch 5, first piece.  The uniqueness theorem of
  \<open>Theorem_1_1\<close> (downstream, so not citable here) works with
  CONTINUOUS solutions, and at a point of continuity the lower envelope
  is the function itself.  So on that class the faithful notion
  @{const visc_supersol_lsc} and the repo's @{const visc_supersol_env}
  agree, and the envelope costs nothing at the interface.  What the
  interface still needs is the OTHER envelope --- \<open>F\<^sup>* = F\<close> away from
  \<open>p = 0\<close> --- which is a separate, purely analytic matter recorded at the
  end of this file.\<close>

lemma lsc_env_eq_self:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and c: "isCont u x"
  shows "lsc_env u x = u x"
proof (rule antisym)
  show "lsc_env u x \<le> u x" by (rule lsc_env_le_self[OF B])
next
  show "u x \<le> lsc_env u x"
  proof (rule field_le_epsilon)
    fix e :: real assume e0: "0 < e"
    obtain d where d0: "0 < d"
      and dd: "\<And>z. dist z x < d \<Longrightarrow> dist (u z) (u x) < e"
      using c[unfolded continuous_at_eps_delta] e0 by blast
    have bdd: "bdd_below (u ` ball x d)"
      by (rule bdd_belowI[of _ B]) (use B in auto)
    have "u x - e \<le> (INF y \<in> ball x d. u y)"
    proof (rule cInf_greatest)
      show "u ` ball x d \<noteq> {}" using d0 by auto
    next
      fix z assume "z \<in> u ` ball x d"
      then obtain y where y: "y \<in> ball x d" and zy: "z = u y" by auto
      have "dist y x < d" using y by (simp add: mem_ball dist_commute)
      then have "dist (u y) (u x) < e" by (rule dd)
      then show "u x - e \<le> z" unfolding zy by (simp add: dist_real_def)
    qed
    also have "\<dots> \<le> lsc_env u x"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use d0 in auto)
    finally show "u x \<le> lsc_env u x + e" by linarith
  qed
qed

lemma visc_supersol_lsc_iff_env:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and sub: "\<Omega> \<subseteq> K"
    and cont: "\<And>y. y \<in> K \<Longrightarrow> isCont u y"
  shows "visc_supersol_lsc k L K \<Omega> u \<longleftrightarrow> visc_supersol_env k L K \<Omega> u"
proof -
  have eqK: "\<And>y. y \<in> K \<Longrightarrow> lsc_env u y = u y"
    by (rule lsc_env_eq_self[OF B cont])
  have eqO: "\<And>y. y \<in> \<Omega> \<Longrightarrow> lsc_env u y = u y"
    using eqK sub by blast
  show ?thesis
    unfolding visc_supersol_lsc_def visc_supersol_env_def
  proof (intro iffI ballI allI impI)
    fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
    assume h: "\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H"
      and x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
      and tm: "\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y"
    have "\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
    proof
      fix y assume y: "y \<in> K"
      show "lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
        unfolding eqO[OF x] eqK[OF y] using tm y by blast
    qed
    then show "1 \<le> ell_op_usc k L (g x) H" using h x tf by blast
  next
    fix x :: "real^'n" and \<phi> g and H :: "real^'n^'n"
    assume h: "\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_usc k L (g x) H"
      and x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
      and tm: "\<forall>y\<in>K. lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
    have "\<forall>y\<in>K. u x - \<phi> x \<le> u y - \<phi> y"
    proof
      fix y assume y: "y \<in> K"
      have h1: "lsc_env u x - \<phi> x \<le> lsc_env u y - \<phi> y"
        using tm y by blast
      show "u x - \<phi> x \<le> u y - \<phi> y"
        using h1 unfolding eqO[OF x] eqK[OF y] .
    qed
    then show "1 \<le> ell_op_usc k L (g x) H" using h x tf by blast
  qed
qed

subsection \<open>The envelope is lower semicontinuous, and attains its infimum\<close>

text \<open>Case 2 tilts the test function and reads off a MINIMISER of
  \<open>v\<^sub>* - \<psi>\<close> over a small closed ball.  The minimiser exists because the
  lower envelope is lower semicontinuous --- which is the point of the
  envelope --- and an lsc function attains its infimum on a nonempty
  compact set.  Neither fact is in the library for this setting, so both
  are proved here.

  Lower semicontinuity is immediate from the definition: if
  \<open>c < lsc_env u z\<close> then some ball around \<open>z\<close> already has \<open>u > c\<close> on it,
  and every point of the half-sized ball inherits that ball's infimum as
  a lower bound for its own envelope.\<close>

lemma lsc_env_lower:
  fixes u :: "real^'n::finite \<Rightarrow> real"
  assumes B: "\<And>y. B \<le> u y" and lt: "c < lsc_env u z"
  obtains e where "0 < e"
    and "\<forall>y. dist z y < e \<longrightarrow> c < lsc_env u y"
proof -
  have ne: "(\<lambda>e. INF y \<in> ball z e. u y) ` {0<..} \<noteq> {}" by auto
  have "c < Sup ((\<lambda>e. INF y \<in> ball z e. u y) ` {0<..})"
    using lt unfolding lsc_env_def .
  then obtain w where wmem: "w \<in> (\<lambda>e. INF y \<in> ball z e. u y) ` {0<..}"
    and wc: "c < w"
    using less_cSup_iff[OF ne lsc_env_bdd_above[OF B]] by blast
  from wmem obtain e where e0: "0 < e"
    and we: "w = (INF y \<in> ball z e. u y)" by auto
  have key: "c < lsc_env u y" if dzy: "dist z y < e / 2" for y
  proof -
    have sub: "ball y (e / 2) \<subseteq> ball z e"
    proof
      fix q assume "q \<in> ball y (e / 2)"
      then have "dist y q < e / 2" by (simp add: mem_ball)
      then have "dist z q < e"
        using dzy dist_triangle[of z q y] by (simp add: dist_commute)
      then show "q \<in> ball z e" by (simp add: mem_ball)
    qed
    have bdd: "bdd_below (u ` ball z e)"
      by (rule bdd_belowI[of _ B]) (use B in auto)
    have "(INF y \<in> ball z e. u y) \<le> (INF q \<in> ball y (e / 2). u q)"
    proof (rule cInf_greatest)
      show "u ` ball y (e / 2) \<noteq> {}" using e0 by auto
    next
      fix t assume "t \<in> u ` ball y (e / 2)"
      then obtain q where q: "q \<in> ball y (e / 2)" and tq: "t = u q" by auto
      have "q \<in> ball z e" using sub q by blast
      then have "u q \<in> u ` ball z e" by blast
      then show "(INF y \<in> ball z e. u y) \<le> t"
        unfolding tq by (rule cInf_lower[OF _ bdd])
    qed
    also have "(INF q \<in> ball y (e / 2). u q) \<le> lsc_env u y"
      unfolding lsc_env_def
      by (rule cSup_upper[OF _ lsc_env_bdd_above[OF B]]) (use e0 in auto)
    finally show ?thesis using wc unfolding we by linarith
  qed
  show ?thesis by (rule that[of "e / 2"]) (use e0 key in auto)+
qed

lemma lsc_env_attains_inf:
  fixes u :: "real^'n::finite \<Rightarrow> real" and S :: "(real^'n) set"
  assumes B: "\<And>y. B \<le> u y" and cS: "compact S" and neS: "S \<noteq> {}"
  obtains z where "z \<in> S"
    and "\<And>y. y \<in> S \<Longrightarrow> lsc_env u z \<le> lsc_env u y"
proof -
  define m where "m = (INF y \<in> S. lsc_env u y)"
  have bdd: "bdd_below (lsc_env u ` S)"
    by (rule bdd_belowI[of _ B]) (use lsc_env_ge[OF B] in auto)
  have neI: "lsc_env u ` S \<noteq> {}" using neS by auto
  have mlow: "\<And>y. y \<in> S \<Longrightarrow> m \<le> lsc_env u y"
    unfolding m_def by (rule cInf_lower[OF _ bdd]) auto
  have pick: "\<exists>zz \<in> S. lsc_env u zz < m + 1 / real (Suc j)" for j
  proof -
    have "m < m + 1 / real (Suc j)" by simp
    then have "\<exists>t \<in> lsc_env u ` S. t < m + 1 / real (Suc j)"
      unfolding m_def using cInf_less_iff[OF neI bdd] by blast
    then show ?thesis by auto
  qed
  have "\<forall>j. \<exists>zz. zz \<in> S \<and> lsc_env u zz < m + 1 / real (Suc j)"
    using pick by blast
  then obtain zs where zsS: "\<And>j. zs j \<in> S"
    and zsm: "\<And>j. lsc_env u (zs j) < m + 1 / real (Suc j)"
    by metis
  have sq: "seq_compact S" using cS by (simp add: compact_eq_seq_compact_metric)
  obtain z r where zS: "z \<in> S" and rm: "strict_mono r"
    and lim: "(zs \<circ> r) \<longlonglongrightarrow> z"
    using sq[unfolded seq_compact_def] zsS by blast
  have zle: "lsc_env u z \<le> m"
  proof (rule ccontr)
    assume "\<not> lsc_env u z \<le> m"
    then have mlt: "m < lsc_env u z" by simp
    define c where "c = (m + lsc_env u z) / 2"
    have cm: "m < c" unfolding c_def using mlt by simp
    have cz: "c < lsc_env u z" unfolding c_def using mlt by simp
    obtain e where e0: "0 < e"
      and enearA: "\<forall>y. dist z y < e \<longrightarrow> c < lsc_env u y"
      by (rule lsc_env_lower[OF B cz])
    have enear: "\<And>y. dist z y < e \<Longrightarrow> c < lsc_env u y"
      using enearA by blast
    have ev1: "\<forall>\<^sub>F l in sequentially. dist ((zs \<circ> r) l) z < e"
      using lim e0 by (simp add: tendsto_iff)
    have ev2: "\<forall>\<^sub>F l in sequentially. 1 / real (Suc (r l)) < c - m"
    proof -
      have "(\<lambda>l. 1 / real (Suc l)) \<longlonglongrightarrow> 0"
        using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
      then have "(\<lambda>l. 1 / real (Suc (r l))) \<longlonglongrightarrow> 0"
        using LIMSEQ_subseq_LIMSEQ[OF _ rm] by (simp add: o_def)
      then show ?thesis using cm by (simp add: order_tendstoD(2))
    qed
    from ev1 obtain N1 where N1: "\<And>l. N1 \<le> l \<Longrightarrow>
        dist ((zs \<circ> r) l) z < e"
      by (auto simp: eventually_sequentially)
    from ev2 obtain N2 where N2: "\<And>l. N2 \<le> l \<Longrightarrow>
        1 / real (Suc (r l)) < c - m"
      by (auto simp: eventually_sequentially)
    define l where "l = max N1 N2"
    have dl: "dist z ((zs \<circ> r) l) < e"
      using N1[of l] unfolding l_def by (simp add: dist_commute)
    have gl: "1 / real (Suc (r l)) < c - m"
      using N2[of l] unfolding l_def by simp
    have "c < lsc_env u (zs (r l))"
      using enear[OF dl] by (simp add: o_def)
    moreover have "lsc_env u (zs (r l)) < m + 1 / real (Suc (r l))"
      by (rule zsm)
    ultimately show False using gl by linarith
  qed
  show ?thesis
  proof (rule that[OF zS])
    fix y assume yS: "y \<in> S"
    show "lsc_env u z \<le> lsc_env u y" using zle mlow[OF yS] by linarith
  qed
qed

subsection \<open>Case 2: minimisers of a tilted quadratic\<close>

text \<open>Case 2 of the supersolution proof perturbs the test function and
  reads off a minimiser of \<open>v\<^sub>* - \<psi>\<close>.  Three ingredients are needed and
  none of them mentions the value function, so all three are proved here
  in the abstract.

  First, an infimum-attainment statement for a lower semicontinuous
  function.  The envelope version proved above attains the infimum of
  \<open>lsc_env u\<close> itself, but what Case 2 minimises is \<open>lsc_env u\<close> MINUS a
  quadratic, so the argument is redone with lower semicontinuity as a
  hypothesis rather than as a property of the envelope.\<close>

lemma lsc_attains_inf_gen:
  fixes f :: "real^'n::finite \<Rightarrow> real" and S :: "(real^'n) set"
  assumes lsc: "\<And>c z. c < f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y"
    and B: "\<And>y. y \<in> S \<Longrightarrow> B \<le> f y"
    and cS: "compact S" and neS: "S \<noteq> {}"
  obtains z where "z \<in> S" and "\<And>y. y \<in> S \<Longrightarrow> f z \<le> f y"
proof -
  define m where "m = (INF y \<in> S. f y)"
  have bdd: "bdd_below (f ` S)"
    by (rule bdd_belowI[of _ B]) (use B in auto)
  have neI: "f ` S \<noteq> {}" using neS by auto
  have mlow: "\<And>y. y \<in> S \<Longrightarrow> m \<le> f y"
    unfolding m_def by (rule cInf_lower[OF _ bdd]) auto
  have pick: "\<exists>zz \<in> S. f zz < m + 1 / real (Suc j)" for j
  proof -
    have "m < m + 1 / real (Suc j)" by simp
    then have "\<exists>t \<in> f ` S. t < m + 1 / real (Suc j)"
      unfolding m_def using cInf_less_iff[OF neI bdd] by blast
    then show ?thesis by auto
  qed
  have "\<forall>j. \<exists>zz. zz \<in> S \<and> f zz < m + 1 / real (Suc j)"
    using pick by blast
  then obtain zs where zsS: "\<And>j. zs j \<in> S"
    and zsm: "\<And>j. f (zs j) < m + 1 / real (Suc j)"
    by metis
  have sq: "seq_compact S" using cS by (simp add: compact_eq_seq_compact_metric)
  obtain z r where zS: "z \<in> S" and rm: "strict_mono r"
    and lim: "(zs \<circ> r) \<longlonglongrightarrow> z"
    using sq[unfolded seq_compact_def] zsS by blast
  have zle: "f z \<le> m"
  proof (rule ccontr)
    assume "\<not> f z \<le> m"
    then have mlt: "m < f z" by simp
    define c where "c = (m + f z) / 2"
    have cm: "m < c" unfolding c_def using mlt by simp
    have cz: "c < f z" unfolding c_def using mlt by simp
    obtain e where e0: "0 < e"
      and enear: "\<forall>y. dist z y < e \<longrightarrow> c < f y"
      using lsc[OF cz] by blast
    have ev1: "\<forall>\<^sub>F l in sequentially. dist ((zs \<circ> r) l) z < e"
      using lim e0 by (simp add: tendsto_iff)
    have ev2: "\<forall>\<^sub>F l in sequentially. 1 / real (Suc (r l)) < c - m"
    proof -
      have "(\<lambda>l. 1 / real (Suc l)) \<longlonglongrightarrow> 0"
        using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
      then have "(\<lambda>l. 1 / real (Suc (r l))) \<longlonglongrightarrow> 0"
        using LIMSEQ_subseq_LIMSEQ[OF _ rm] by (simp add: o_def)
      then show ?thesis using cm by (simp add: order_tendstoD(2))
    qed
    from ev1 obtain N1 where N1: "\<And>l. N1 \<le> l \<Longrightarrow>
        dist ((zs \<circ> r) l) z < e"
      by (auto simp: eventually_sequentially)
    from ev2 obtain N2 where N2: "\<And>l. N2 \<le> l \<Longrightarrow>
        1 / real (Suc (r l)) < c - m"
      by (auto simp: eventually_sequentially)
    define l where "l = max N1 N2"
    have dl: "dist z ((zs \<circ> r) l) < e"
      using N1[of l] unfolding l_def by (simp add: dist_commute)
    have gl: "1 / real (Suc (r l)) < c - m"
      using N2[of l] unfolding l_def by simp
    have "c < f (zs (r l))"
      using enear dl by (simp add: o_def)
    moreover have "f (zs (r l)) < m + 1 / real (Suc (r l))"
      by (rule zsm)
    ultimately show False using gl by linarith
  qed
  show ?thesis
  proof (rule that[OF zS])
    fix y assume yS: "y \<in> S"
    then show "f z \<le> f y" using zle mlow[OF yS] by linarith
  qed
qed

text \<open>Second, lower semicontinuity is stable under subtracting a
  continuous function --- which is what turns the envelope into
  something whose minimiser over a small closed ball exists.\<close>

lemma lsc_diff_continuous:
  fixes f \<psi> :: "real^'n::finite \<Rightarrow> real"
  assumes lsc: "\<And>c z. c < f z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y"
    and cont: "continuous_on UNIV \<psi>"
    and lt: "c < f z - \<psi> z"
  shows "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> c < f y - \<psi> y"
proof -
  define d where "d = (f z - \<psi> z - c) / 2"
  have d0: "0 < d" using lt unfolding d_def by simp
  have cz: "continuous (at z) \<psi>"
    using cont by (simp add: continuous_on_eq_continuous_at)
  obtain s where s0: "0 < s"
    and sd: "\<And>y. dist y z < s \<Longrightarrow> dist (\<psi> y) (\<psi> z) < d"
    using cz d0 unfolding continuous_at_eps_delta by blast
  have dd: "2 * d = f z - \<psi> z - c" unfolding d_def by simp
  have big: "c + \<psi> z + d < f z" using lt dd d0 by linarith
  obtain e where e0: "0 < e"
    and en: "\<forall>y. dist z y < e \<longrightarrow> c + \<psi> z + d < f y"
    using lsc[OF big] by blast
  have "0 < min e s" using e0 s0 by simp
  moreover have "\<forall>y. dist z y < min e s \<longrightarrow> c < f y - \<psi> y"
  proof (intro allI impI)
    fix y assume dy: "dist z y < min e s"
    then have f1: "c + \<psi> z + d < f y" using en by simp
    have "dist (\<psi> y) (\<psi> z) < d"
      using dy by (intro sd) (simp add: dist_commute)
    then have f2: "\<psi> y - \<psi> z < d" by (simp add: dist_real_def abs_less_iff)
    show "c < f y - \<psi> y" using f1 f2 by linarith
  qed
  ultimately show ?thesis by blast
qed

text \<open>The tilted test function of Case 2 is a quadratic plus a linear
  term, so it is continuous.\<close>

lemma continuous_on_quad_tilt:
  fixes M :: "real^'n::finite^'n" and x \<eta> :: "real^'n"
  shows "continuous_on S (\<lambda>z. ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))"
proof -
  have c1: "continuous_on S (\<lambda>z. z - x)" by (intro continuous_intros)
  have c2: "continuous_on S (\<lambda>z. M *v (z - x))"
    by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matrix_vector_mul_bounded_linear] c1]) auto
  show ?thesis using c1 c2 by (intro continuous_intros) auto
qed

text \<open>Third, the STRICT quadratic minorant.  This is what replaces the
  paper's bump construction.  The paper builds a \<open>C\<^sup>2\<close> function
  \<open>\<phi>\<^sup>m\<close> lying strictly below \<open>v\<^sub>*\<close> off the touching point, exactly
  quadratic near it with a nonsingular Hessian tending to
  \<open>\<nabla>\<^sup>2\<phi>(0)\<close>.  All three of those properties come for free from
  \<open>test_fun_quadratic_minorates\<close> applied at level \<open>\<epsilon>/2\<close>: since
  \<open>H - (\<epsilon>/2) \<cdot> 1 = (H - \<epsilon> \<cdot> 1) + (\<epsilon>/2) \<cdot> 1\<close>, the surplus
  \<open>(\<epsilon>/2)|z - x|\<^sup>2/2\<close> is exactly the strict separation wanted, while
  \<open>H - \<epsilon> \<cdot> 1\<close> is quadratic by construction and tends to \<open>H\<close>.\<close>

lemma test_fun_strict_minorant_zero_grad:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<epsilon> :: real
  assumes tf: "test_fun_at \<phi> g H x" and g0: "g x = 0" and e0: "0 < \<epsilon>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z"
proof -
  have he: "0 < \<epsilon> / 2" using e0 by simp
  obtain r where r0: "0 < r"
    and min2: "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))) / 2 \<le> \<phi> z"
    by (rule test_fun_quadratic_minorates[OF tf he]) blast
  have key: "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
      + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z" if zr: "z \<in> ball x r" for z
  proof -
    have e1: "(H - \<epsilon> *\<^sub>R mat 1) *v (z - x) = H *v (z - x) - \<epsilon> *\<^sub>R (z - x)"
      by (simp add: matrix_vector_mult_diff_rdistrib scaleR_matrix_vector
          matrix_vector_mul_lid)
    have e2: "(H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x)
        = H *v (z - x) - (\<epsilon>/2) *\<^sub>R (z - x)"
      by (simp add: matrix_vector_mult_diff_rdistrib scaleR_matrix_vector
          matrix_vector_mul_lid)
    have i1: "(z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))
        = (z - x) \<bullet> (H *v (z - x)) - \<epsilon> * ((z - x) \<bullet> (z - x))"
      unfolding e1 by (simp add: inner_diff_right)
    have i2: "(z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))
        = (z - x) \<bullet> (H *v (z - x)) - (\<epsilon>/2) * ((z - x) \<bullet> (z - x))"
      unfolding e2 by (simp add: inner_diff_right)
    have "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      = \<phi> x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H - (\<epsilon>/2) *\<^sub>R mat 1) *v (z - x))) / 2"
      unfolding i1 i2 g0 by (simp add: field_simps)
    also have "\<dots> \<le> \<phi> z" by (rule min2[OF zr])
    finally show ?thesis .
  qed
  show ?thesis by (rule that[OF r0]) (use key in blast)
qed

text \<open>Finally the quantitative part of the tilt.  If \<open>W\<close> is bounded
  below by \<open>W x + Q\<close> with a quadratic surplus \<open>c|z - x|\<^sup>2\<close>, and \<open>y\<close>
  minimises \<open>W - Q - \<langle>\<eta>, \<cdot> - x\<rangle>\<close> over the ball, then \<open>y\<close> is within
  \<open>\<bar>\<eta>\<bar>/c\<close> of \<open>x\<close>.  The paper only records that the minimisers converge
  to the touching point; the explicit rate is what makes them INTERIOR
  to the ball for small \<open>\<eta>\<close>, which is what the now-local Case 1 needs.\<close>

lemma tilted_minimiser_close:
  fixes W Q :: "real^'n::finite \<Rightarrow> real" and x y \<eta> :: "real^'n"
  assumes sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and Qx: "Q x = 0" and c0: "0 < c"
    and xin: "x \<in> cball x \<rho>" and yin: "y \<in> cball x \<rho>"
    and mn: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W y - Q y - \<eta> \<bullet> (y - x) \<le> W z - Q z - \<eta> \<bullet> (z - x)"
  shows "norm (y - x) \<le> norm \<eta> / c"
proof -
  have a1: "W y - Q y - \<eta> \<bullet> (y - x) \<le> W x"
    using mn[OF xin] Qx by simp
  have a2: "W x + Q y + c * ((y - x) \<bullet> (y - x)) \<le> W y"
    by (rule sep[OF yin])
  have step: "c * ((y - x) \<bullet> (y - x)) \<le> \<eta> \<bullet> (y - x)"
    using a1 a2 by linarith
  have cs: "\<eta> \<bullet> (y - x) \<le> norm \<eta> * norm (y - x)"
    by (rule norm_cauchy_schwarz)
  have sq: "(y - x) \<bullet> (y - x) = norm (y - x) * norm (y - x)"
    by (simp add: dot_square_norm power2_eq_square)
  show ?thesis
  proof (cases "norm (y - x) = 0")
    case True
    then show ?thesis using c0 by simp
  next
    case False
    then have pos: "0 < norm (y - x)" by simp
    have "(c * norm (y - x)) * norm (y - x) \<le> norm \<eta> * norm (y - x)"
      using step cs sq by (simp add: mult.assoc)
    then have "c * norm (y - x) \<le> norm \<eta>"
      using pos by (rule mult_right_le_imp_le)
    then show ?thesis using c0 by (simp add: pos_le_divide_eq mult.commute)
  qed
qed


text \<open>The tilted test function of Case 2 is the quadratic
  \<open>b + \<onehalf>(z - x)\<^sup>T M (z - x) + \<langle>\<eta>, z - x\<rangle>\<close>, centred at the touching point
  \<open>x\<close> but examined at a nearby point \<open>y\<close>.  Recentring it into the normal
  form \<open>c + \<langle>p, z\<rangle> + \<onehalf>z\<^sup>T M z\<close> uses only symmetry of \<open>M\<close>, which
  \<open>test_fun_at\<close> supplies as part of its own definition.\<close>

lemma test_fun_at_shifted_quadratic:
  fixes M :: "real^'n::finite^'n" and x \<eta> y :: "real^'n" and b :: real
  assumes sym: "transpose M = M"
  shows "test_fun_at (\<lambda>z. b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. M *v (z - x) + \<eta>) M y"
proof -
  define p where "p = \<eta> - M *v x"
  define cc where "cc = b + (x \<bullet> (M *v x)) / 2 - \<eta> \<bullet> x"
  have f_eq: "(\<lambda>z. b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      = (\<lambda>z. cc + p \<bullet> z + (z \<bullet> (M *v z)) / 2)"
  proof (rule ext)
    fix z :: "real^'n"
    have m1: "M *v (z - x) = M *v z - M *v x"
      by (simp add: matrix_vector_mult_diff_distrib)
    have s1: "x \<bullet> (M *v z) = z \<bullet> (M *v x)"
    proof -
      have "x \<bullet> (M *v z) = (transpose M *v x) \<bullet> z"
        by (rule inner_transpose_matrix)
      also have "\<dots> = (M *v x) \<bullet> z" using sym by simp
      finally show ?thesis by (simp add: inner_commute)
    qed
    have s2: "(M *v x) \<bullet> z = z \<bullet> (M *v x)" by (rule inner_commute)
    have e: "(z - x) \<bullet> (M *v (z - x))
        = z \<bullet> (M *v z) - 2 * (z \<bullet> (M *v x)) + x \<bullet> (M *v x)"
      unfolding m1 using s1
      by (simp add: inner_diff_left inner_diff_right)
    have pz: "p \<bullet> z = \<eta> \<bullet> z - z \<bullet> (M *v x)"
      unfolding p_def by (simp add: inner_diff_left s2)
    have ez: "\<eta> \<bullet> (z - x) = \<eta> \<bullet> z - \<eta> \<bullet> x"
      by (simp add: inner_diff_right)
    show "b + ((z - x) \<bullet> (M *v (z - x))) / 2 + \<eta> \<bullet> (z - x)
        = cc + p \<bullet> z + (z \<bullet> (M *v z)) / 2"
      unfolding e cc_def pz ez by (simp add: field_simps)
  qed
  have g_eq: "(\<lambda>z :: real^'n. M *v (z - x) + \<eta>) = (\<lambda>z. p + M *v z)"
    by (rule ext) (simp add: p_def matrix_vector_mult_diff_rdistrib algebra_simps)
  show ?thesis
    unfolding f_eq g_eq by (rule test_fun_at_quadratic[OF sym])
qed

text \<open>The heart of Case 2.  Given a STRICT quadratic separation on a
  closed ball --- which is what \<open>test_fun_strict_minorate_zero_grad\<close>
  delivers once the gradient vanishes --- a tilt by \<open>\<eta>\<close> has a minimiser
  \<open>y\<close>, and that minimiser is within \<open>\<bar>\<eta>\<bar>/c\<close> of the centre.  For
  \<open>\<bar>\<eta>\<bar> < c\<rho>\<close> that puts \<open>y\<close> strictly inside the ball, so the minimality
  is a genuine LOCAL touching at \<open>y\<close> --- exactly the hypothesis the
  localised Case 1 consumes.

  No properties of \<open>W\<close> are used beyond lower semicontinuity: the lower
  bound needed for the infimum comes from the separation itself, since
  \<open>W \<ge> W x + Q + c\<bar>z - x\<bar>\<^sup>2\<close> already forces \<open>W - Q - \<langle>\<eta>, \<cdot> - x\<rangle> \<ge> W x - \<bar>\<eta>\<bar>\<rho>\<close>
  on the ball.\<close>

lemma tilted_local_touching:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n"
    and x \<eta> :: "real^'n"
  assumes lsc: "\<And>a z. a < W z \<Longrightarrow> \<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a < W y"
    and rho0: "0 < \<rho>" and c0: "0 < c"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + ((z - x) \<bullet> (M *v (z - x))) / 2 + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and hsmall: "norm \<eta> < c * \<rho>"
  obtains y where "dist x y < \<rho>" and "norm (y - x) \<le> norm \<eta> / c"
    and "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
proof -
  define Q where "Q = (\<lambda>z :: real^'n. ((z - x) \<bullet> (M *v (z - x))) / 2)"
  define \<psi> where "\<psi> = (\<lambda>z :: real^'n. Q z + \<eta> \<bullet> (z - x))"
  have Qx: "Q x = 0" unfolding Q_def by simp
  have cpsi: "continuous_on UNIV \<psi>"
    unfolding \<psi>_def Q_def by (rule continuous_on_quad_tilt)
  have flsc: "\<exists>e>0. \<forall>y. dist z y < e \<longrightarrow> a < W y - \<psi> y"
    if "a < W z - \<psi> z" for a and z :: "real^'n"
    by (rule lsc_diff_continuous[OF lsc cpsi that])
  have sep': "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    unfolding Q_def by (rule sep)
  have Bnd: "W x - norm \<eta> * \<rho> \<le> W z - \<psi> z" if zc: "z \<in> cball x \<rho>" for z
  proof -
    have s: "W x + Q z + c * ((z - x) \<bullet> (z - x)) \<le> W z" by (rule sep'[OF zc])
    have q0: "0 \<le> c * ((z - x) \<bullet> (z - x))"
      by (rule mult_nonneg_nonneg[OF less_imp_le[OF c0] inner_ge_zero])
    have n1: "norm (z - x) \<le> \<rho>"
      using zc by (simp add: dist_norm norm_minus_commute)
    have "norm \<eta> * norm (z - x) \<le> norm \<eta> * \<rho>"
      by (rule mult_left_mono[OF n1 norm_ge_zero])
    then have cs: "\<eta> \<bullet> (z - x) \<le> norm \<eta> * \<rho>"
      using norm_cauchy_schwarz[of \<eta> "z - x"] by linarith
    show ?thesis unfolding \<psi>_def using s q0 cs by linarith
  qed
  have cc: "compact (cball x \<rho>)" by simp
  have ne: "cball x \<rho> \<noteq> {}" using rho0 by auto
  obtain y where yc: "y \<in> cball x \<rho>"
    and ymin: "\<And>w. w \<in> cball x \<rho> \<Longrightarrow> W y - \<psi> y \<le> W w - \<psi> w"
  proof (rule lsc_attains_inf_gen[OF flsc Bnd cc ne])
    fix z :: "real^'n" assume a1: "z \<in> cball x \<rho>"
      and a2: "\<And>w. w \<in> cball x \<rho> \<Longrightarrow> W z - \<psi> z \<le> W w - \<psi> w"
    show thesis by (rule that[OF a1 a2])
  qed
  have xc: "x \<in> cball x \<rho>" using rho0 by simp
  have close: "norm (y - x) \<le> norm \<eta> / c"
  proof (rule tilted_minimiser_close[OF sep' Qx c0 xc yc])
    fix z :: "real^'n" assume zc: "z \<in> cball x \<rho>"
    show "W y - Q y - \<eta> \<bullet> (y - x) \<le> W z - Q z - \<eta> \<bullet> (z - x)"
      using ymin[OF zc] unfolding \<psi>_def by simp
  qed
  have hlt: "norm \<eta> / c < \<rho>"
    using hsmall c0 by (simp add: pos_divide_less_eq mult.commute)
  have dxy: "dist x y < \<rho>"
  proof -
    have "dist x y = norm (y - x)" by (simp add: dist_norm norm_minus_commute)
    then show ?thesis using close hlt by linarith
  qed
  have loc: "W y - \<psi> y \<le> W w - \<psi> w" if dw: "dist y w < \<rho> - dist x y" for w
  proof -
    have "dist x w \<le> dist x y + dist y w" by (rule dist_triangle)
    then have "dist x w < \<rho>" using dw by linarith
    then have "w \<in> cball x \<rho>" by (auto simp: dist_commute)
    then show ?thesis by (rule ymin)
  qed
  show ?thesis
  proof (rule that[OF dxy close])
    fix w :: "real^'n" assume dw: "dist y w < \<rho> - dist x y"
    show "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      using loc[OF dw] by (simp add: \<psi>_def Q_def)
  qed
qed


text \<open>Assembling the separation for the value function.  On a small
  enough ball the touching hypothesis and the strict quadratic minorant
  combine into exactly the separation \<open>tilted_local_touching\<close> wants:
  the touching gives \<open>\<phi> z - \<phi> x \<le> W z - W x\<close> and the minorant gives
  \<open>Q\<^sub>\<epsilon>(z) + (\<epsilon>/4)\<bar>z - x\<bar>\<^sup>2 \<le> \<phi> z - \<phi> x\<close>.  The radius is also shrunk
  below the distance to the complement of \<open>interior K\<close>, so that every
  point of the ball is an admissible touching point in its own right.\<close>

lemma paper_v_case2_separation:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x" and gx0: "g x = 0"
    and rho0: "0 < \<rho>\<^sub>0"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho>\<^sub>0 \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y - \<phi> y"
    and e0: "0 < \<epsilon>"
  obtains \<rho> where "0 < \<rho>" and "cball x \<rho> \<subseteq> interior K"
    and "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x
        + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) z"
proof -
  obtain r where r0: "0 < r"
    and mino: "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z"
    by (rule test_fun_strict_minorant_zero_grad[OF tf gx0 e0]) blast
  have exb: "\<exists>e>0. ball x e \<subseteq> interior K"
    using open_interior[of K, unfolded open_contains_ball] xi by blast
  obtain e where e0': "0 < e" and eK: "ball x e \<subseteq> interior K"
    using exb by blast
  define \<rho> where "\<rho> = min (r / 2) (min (\<rho>\<^sub>0 / 2) (e / 2))"
  have rho: "0 < \<rho>" unfolding \<rho>_def using r0 rho0 e0' by simp
  have rlt: "\<rho> < r" unfolding \<rho>_def using r0 rho0 e0' by simp
  have rholt: "\<rho> < \<rho>\<^sub>0" unfolding \<rho>_def using r0 rho0 e0' by simp
  have elt: "\<rho> < e" unfolding \<rho>_def using r0 rho0 e0' by simp
  have sub: "cball x \<rho> \<subseteq> interior K"
  proof
    fix z :: "real^'n" assume "z \<in> cball x \<rho>"
    then have "dist x z \<le> \<rho>" by simp
    then have "dist x z < e" using elt by linarith
    then show "z \<in> interior K" using eK by auto
  qed
  have key: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x
      + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
      + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
    \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) z"
    if zc: "z \<in> cball x \<rho>" for z
  proof -
    have dzx: "dist x z \<le> \<rho>" using zc by simp
    have zb: "z \<in> ball x r" using dzx rlt by auto
    have zK: "z \<in> K" using sub zc interior_subset by blast
    have dxz: "dist x z < \<rho>\<^sub>0" using dzx rholt by linarith
    have t: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) z - \<phi> z"
      by (rule tmin[OF zK dxz])
    have m: "\<phi> x + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> \<phi> z" by (rule mino[OF zb])
    show ?thesis using t m by linarith
  qed
  show ?thesis by (rule that[OF rho sub]) (use key in blast)
qed

text \<open>Case 2's tilt step for the value function.  The minimiser \<open>y\<close>
  produced by \<open>tilted_local_touching\<close> lies strictly inside the ball, so
  it is an interior point of \<open>K\<close> at which the tilted quadratic touches
  \<open>v\<^sub>*\<close> from below on a whole neighbourhood.  That is precisely the
  hypothesis of the LOCALISED Case 1, which therefore applies at \<open>y\<close>
  whenever the tilted gradient there is nonzero.\<close>

theorem paper_v_case2_tilt_step:
  fixes K :: "(real^'n::finite) set" and x \<eta> :: "real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and symH: "transpose H = H"
    and e0: "0 < \<epsilon>" and rho: "0 < \<rho>"
    and sub: "cball x \<rho> \<subseteq> interior K"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x
        + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x))
      \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) z"
    and hsm: "norm \<eta> < (\<epsilon> / 4) * \<rho>"
  obtains y where "dist x y < \<rho>" and "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
    and "(H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta> \<noteq> 0 \<Longrightarrow>
      1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>) (H - \<epsilon> *\<^sub>R mat 1)"
proof -
  have symM: "transpose (H - \<epsilon> *\<^sub>R mat 1) = H - \<epsilon> *\<^sub>R mat 1"
    by (rule transpose_sub_smat[OF symH])
  have c0: "0 < \<epsilon> / 4" using e0 by simp
  have tv0: "\<And>u. 0 \<le> enn2real (paper_v k L T K u)" by simp
  have lscW: "\<exists>d>0. \<forall>u. dist z u < d \<longrightarrow>
      a < lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) u"
    if lt: "a < lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) z"
    for a and z :: "real^'n"
  proof (rule lsc_env_lower[OF tv0 lt])
    fix d assume "0 < d"
      and "\<forall>u. dist z u < d \<longrightarrow>
        a < lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) u"
    then show ?thesis by blast
  qed
  obtain y where dxy: "dist x y < \<rho>"
    and close: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
    and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y
          - (((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) w
          - (((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
  proof (rule tilted_local_touching[OF lscW rho c0 sep hsm])
    fix yy :: "real^'n"
    assume a1: "dist x yy < \<rho>" and a2: "norm (yy - x) \<le> norm \<eta> / (\<epsilon> / 4)"
      and a3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
        lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) yy
            - (((yy - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (yy - x))) / 2
               + \<eta> \<bullet> (yy - x))
          \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) w
            - (((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2
               + \<eta> \<bullet> (w - x))"
    show thesis by (rule that[OF a1 a2 a3])
  qed
  have rp: "0 < \<rho> - dist x y" using dxy by simp
  have yi: "y \<in> interior K"
  proof -
    have "y \<in> cball x \<rho>" using dxy by (auto simp: dist_commute)
    then show ?thesis using sub by blast
  qed
  have tfy: "test_fun_at
      (\<lambda>z. 0 + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. (H - \<epsilon> *\<^sub>R mat 1) *v (z - x) + \<eta>) (H - \<epsilon> *\<^sub>R mat 1) y"
    by (rule test_fun_at_shifted_quadratic[OF symM])
  have tminy: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y
        - (0 + ((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
      \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) w
        - (0 + ((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    if wK: "w \<in> K" and dw: "dist y w < \<rho> - dist x y" for w
    using loc[OF dw] by simp
  have gt: "1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
      (H - \<epsilon> *\<^sub>R mat 1)"
    if gy: "(H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta> \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1)"
    then have flt: "ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1) < 1" by simp
    show False
      by (rule paper_v_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc yi
            tfy rp tminy gy flt])
  qed
  show ?thesis by (rule that[OF dxy close]) (use gt in blast)
qed


subsection \<open>Case 2, second horn: quadratic pinching forces local constancy\<close>

text \<open>The other horn of Case 2's dichotomy is that the tilted gradient
  vanishes at every tilted minimiser.  Because the test function is
  EXACTLY quadratic, a vanishing gradient makes the first-order terms of
  the minimality inequality cancel identically, leaving the purely
  quadratic bound

    \<open>W w - W y \<ge> \<onehalf>(w - y)\<^sup>T M (w - y) \<ge> -C\<bar>w - y\<bar>\<^sup>2\<close>

  for every \<open>w\<close> near \<open>y\<close>.  If that holds for every \<open>y\<close> in a ball ---
  which it does, once the tilted minimisers sweep out a neighbourhood ---
  then the bound is available in BOTH directions between any two points
  of the ball, and a function whose increments are \<open>O(\<bar>\<Delta>\<bar>\<^sup>2)\<close> along
  every segment is constant: subdividing a segment into \<open>n\<close> pieces costs
  \<open>n \<cdot> C(\<bar>\<Delta>\<bar>/n)\<^sup>2 = C\<bar>\<Delta>\<bar>\<^sup>2/n\<close>, which vanishes.

  Both statements below are pure real analysis; neither mentions the
  value function or the operator.\<close>

lemma pinch_segment_bound:
  fixes W :: "real^'n::finite \<Rightarrow> real" and a b :: "real^'n"
    and S :: "(real^'n) set"
  assumes C0: "0 \<le> C" and n0: "0 < n"
    and pin: "\<And>u w. u \<in> S \<Longrightarrow> w \<in> S \<Longrightarrow>
      W u - C * (dist u w * dist u w) \<le> W w"
    and seg: "\<And>i. i \<le> n \<Longrightarrow> a + (real i / real n) *\<^sub>R (b - a) \<in> S"
  shows "W a - W b \<le> C * (dist a b * dist a b) / real n"
proof -
  define p where "p = (\<lambda>i :: nat. a + (real i / real n) *\<^sub>R (b - a))"
  define d where "d = dist a b / real n"
  have rn0: "(0 :: real) < real n" using n0 by simp
  have p0: "p 0 = a" unfolding p_def by simp
  have pn: "p n = b" unfolding p_def using rn0 by simp
  have pd: "dist (p i) (p (Suc i)) = d" for i
  proof -
    have c1: "p i - p (Suc i)
        = (real i / real n - real (Suc i) / real n) *\<^sub>R (b - a)"
      unfolding p_def by (simp add: scaleR_left_diff_distrib)
    have c2: "real i / real n - real (Suc i) / real n = - (1 / real n)"
      using rn0 by (simp add: field_simps)
    have "dist (p i) (p (Suc i)) = norm ((- (1 / real n)) *\<^sub>R (b - a))"
      unfolding dist_norm c1 c2 by (rule refl)
    also have "\<dots> = (1 / real n) * norm (b - a)"
      using rn0 by simp
    finally show ?thesis
      unfolding d_def by (simp add: dist_norm norm_minus_commute)
  qed
  have d0: "0 \<le> d" unfolding d_def using rn0 by simp
  have step: "W a - W (p j) \<le> real j * (C * (d * d))" if "j \<le> n" for j
    using that
  proof (induction j)
    case 0
    show ?case unfolding p0 by simp
  next
    case (Suc j)
    have jn: "j \<le> n" using Suc.prems by simp
    have ih: "W a - W (p j) \<le> real j * (C * (d * d))" by (rule Suc.IH[OF jn])
    have "W (p j) - C * (dist (p j) (p (Suc j)) * dist (p j) (p (Suc j)))
        \<le> W (p (Suc j))"
      unfolding p_def by (rule pin[OF seg[OF jn] seg[OF Suc.prems]])
    then have "W (p j) - W (p (Suc j)) \<le> C * (d * d)"
      unfolding pd by simp
    then show ?case using ih by (simp add: field_simps)
  qed
  have "W a - W b \<le> real n * (C * (d * d))"
    using step[OF order_refl] unfolding pn .
  also have "real n * (C * (d * d)) = C * (dist a b * dist a b) / real n"
    unfolding d_def using rn0 by (simp add: field_simps)
  finally show ?thesis .
qed

lemma pinch_implies_constant:
  fixes W :: "real^'n::finite \<Rightarrow> real" and x y :: "real^'n"
  assumes r0: "0 < r" and C0: "0 \<le> C"
    and pin: "\<And>u w. u \<in> ball x r \<Longrightarrow> w \<in> ball x r \<Longrightarrow>
      W u - C * (dist u w * dist u w) \<le> W w"
    and yb: "y \<in> ball x r"
  shows "W y = W x"
proof -
  have xb: "x \<in> ball x r" using r0 by simp
  have segb: "a + (real i / real n) *\<^sub>R (b - a) \<in> ball x r"
    if ab: "a \<in> ball x r" and bb: "b \<in> ball x r" and inn: "i \<le> n" and n0: "0 < n"
    for a b :: "real^'n" and i n :: nat
  proof -
    define t where "t = real i / real n"
    have t0: "0 \<le> t" unfolding t_def by simp
    have t1: "t \<le> 1" unfolding t_def using inn n0 by simp
    have conv: "a + t *\<^sub>R (b - a) = (1 - t) *\<^sub>R a + t *\<^sub>R b"
      by (simp add: algebra_simps scaleR_left_diff_distrib
          scaleR_right_diff_distrib)
    have "(1 - t) *\<^sub>R a + t *\<^sub>R b \<in> ball x r"
      by (rule convexD[OF convex_ball ab bb]) (use t0 t1 in auto)
    then show ?thesis unfolding t_def conv[unfolded t_def] .
  qed
  have half: "W u - W w \<le> C * (dist u w * dist u w) / real n"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" and n0: "0 < n"
    for u w :: "real^'n" and n :: nat
  proof (rule pinch_segment_bound[OF C0 n0 pin])
    fix i assume "i \<le> n"
    then show "u + (real i / real n) *\<^sub>R (w - u) \<in> ball x r"
      by (rule segb[OF ub wb _ n0])
  qed
  have zero: "W u \<le> W w"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" for u w :: "real^'n"
  proof (rule ccontr)
    assume "\<not> W u \<le> W w"
    then have pos: "0 < W u - W w" by simp
    obtain n :: nat where nn: "C * (dist u w * dist u w) / (W u - W w) < real n"
      using reals_Archimedean2 by blast
    have nneg: "0 \<le> C * (dist u w * dist u w) / (W u - W w)"
      using C0 pos by (simp add: zero_le_mult_iff)
    have n0: "0 < n" using nn nneg by simp
    have h1: "W u - W w \<le> C * (dist u w * dist u w) / real n"
      by (rule half[OF ub wb n0])
    have h2: "C * (dist u w * dist u w) / real n < W u - W w"
      using nn pos n0 by (simp add: pos_divide_less_eq field_simps)
    show False using h1 h2 by linarith
  qed
  show ?thesis using zero[OF yb xb] zero[OF xb yb] by linarith
qed


text \<open>Three ingredients for the second horn.

  First, a quadratic form is bounded below by a multiple of the squared
  norm --- the constant \<open>C\<close> that \<open>pinch_implies_constant\<close> consumes.

  Second, the pinch itself.  At a tilted minimiser whose gradient
  vanishes, the first-order terms of the minimality inequality cancel
  IDENTICALLY, because the test function is exactly quadratic: expanding
  around the minimiser, the cross term is \<open>\<langle>u, Mv\<rangle>\<close> and the tilt
  contributes \<open>\<langle>\<eta>, u\<rangle>\<close>, and \<open>Mv + \<eta> = 0\<close> is precisely the statement
  that they cancel.  What is left is purely quadratic.

  Third, the SINGULAR case is free.  If \<open>M\<close> is not invertible then it is
  not surjective, so some \<open>u\<close> is missed; a small multiple of \<open>u\<close> is then
  a tilt for which \<open>M z + \<eta> = 0\<close> has NO solution at all, so the gradient
  at the tilted minimiser cannot vanish and the FIRST horn fires
  instead.  The second horn therefore only has to be run for invertible
  \<open>M\<close>, which is what makes the tilted minimisers sweep out a whole
  neighbourhood.\<close>

lemma quad_form_bounded_below:
  fixes M :: "real^'n::finite^'n"
  obtains C where "0 \<le> C"
    and "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
proof -
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define C where "C = onorm ((*v) M)"
  have C0: "0 \<le> C" unfolding C_def by (rule onorm_pos_le[OF bl])
  have key: "- (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    for u :: "real^'n"
  proof -
    have cs: "\<bar>u \<bullet> (M *v u)\<bar> \<le> norm u * norm (M *v u)"
      by (rule Cauchy_Schwarz_ineq2)
    have on: "norm (M *v u) \<le> C * norm u"
      unfolding C_def by (rule onorm[OF bl])
    have m: "norm u * norm (M *v u) \<le> norm u * (C * norm u)"
      by (rule mult_left_mono[OF on norm_ge_zero])
    have eq: "norm u * (C * norm u) = C * (norm u * norm u)"
      by (simp add: mult.assoc mult.left_commute)
    have ab: "\<bar>u \<bullet> (M *v u)\<bar> \<le> C * (norm u * norm u)"
      using cs m eq by linarith
    have nn: "0 \<le> C * (norm u * norm u)"
      by (rule mult_nonneg_nonneg[OF C0
            mult_nonneg_nonneg[OF norm_ge_zero norm_ge_zero]])
    show ?thesis using ab[unfolded abs_le_iff] nn by linarith
  qed
  show ?thesis by (rule that[OF C0]) (use key in blast)
qed

lemma quad_minimality_pinch:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n"
    and x y \<eta> w :: "real^'n" and C :: real
  assumes sym: "transpose M = M"
    and Cb: "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    and grad0: "M *v (y - x) + \<eta> = 0"
    and mn: "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
      \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
  shows "W y - C * (dist y w * dist y w) \<le> W w"
proof -
  define v where "v = y - x"
  define u where "u = w - y"
  have wx: "w - x = v + u" unfolding v_def u_def by simp
  have s1: "v \<bullet> (M *v u) = u \<bullet> (M *v v)"
  proof -
    have "v \<bullet> (M *v u) = (transpose M *v v) \<bullet> u"
      by (rule inner_transpose_matrix)
    also have "\<dots> = (M *v v) \<bullet> u" using sym by simp
    finally show ?thesis by (simp add: inner_commute)
  qed
  have expand: "(w - x) \<bullet> (M *v (w - x))
      = v \<bullet> (M *v v) + 2 * (u \<bullet> (M *v v)) + u \<bullet> (M *v u)"
    unfolding wx using s1
    by (simp add: matrix_vector_right_distrib inner_add_left inner_add_right)
  have etaw: "\<eta> \<bullet> (w - x) = \<eta> \<bullet> v + \<eta> \<bullet> u"
    unfolding wx by (rule inner_add_right)
  have kill: "u \<bullet> (M *v v) + \<eta> \<bullet> u = 0"
  proof -
    have z: "M *v v + \<eta> = 0" unfolding v_def by (rule grad0)
    have "u \<bullet> (M *v v) + \<eta> \<bullet> u = u \<bullet> (M *v v + \<eta>)"
      by (simp add: inner_add_right inner_commute)
    also have "\<dots> = u \<bullet> (0 :: real^'n)" using z by simp
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed
  have main: "W y - W w \<le> - ((u \<bullet> (M *v u)) / 2)"
  proof -
    have "W y - W w \<le> (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      using mn by linarith
    also have "\<dots> = - ((u \<bullet> (M *v u)) / 2 + (u \<bullet> (M *v v) + \<eta> \<bullet> u))"
      unfolding expand etaw v_def[symmetric] by (simp add: field_simps)
    also have "\<dots> = - ((u \<bullet> (M *v u)) / 2)" unfolding kill by simp
    finally show ?thesis .
  qed
  have cb: "- (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2" by (rule Cb)
  have dyw: "dist y w = norm u"
    unfolding u_def by (simp add: dist_norm norm_minus_commute)
  show ?thesis using main cb unfolding dyw by linarith
qed

lemma singular_matrix_avoids_range:
  fixes M :: "real^'n::finite^'n"
  assumes ni: "\<not> invertible M" and d0: "0 < \<delta>"
  obtains \<eta> where "norm \<eta> < \<delta>" and "\<And>z :: real^'n. M *v z + \<eta> \<noteq> 0"
proof -
  have ns: "\<not> surj ((*v) M)"
  proof
    assume "surj ((*v) M)"
    then have "\<exists>B. M ** B = mat 1"
      using matrix_right_invertible_surjective by blast
    then show False using ni invertible_right_inverse by blast
  qed
  obtain u :: "real^'n" where nu: "\<And>z :: real^'n. u \<noteq> M *v z"
    using ns unfolding surj_def by blast
  have u0: "u \<noteq> 0" using nu[of 0] by simp
  have nu0: "0 < norm u" using u0 by simp
  define c where "c = \<delta> / (2 * norm u)"
  have c0: "0 < c" unfolding c_def using d0 nu0 by simp
  have nrm: "norm ((- c) *\<^sub>R u) = c * norm u" using c0 by simp
  have lt: "norm ((- c) *\<^sub>R u) < \<delta>"
    unfolding nrm c_def using nu0 d0 by (simp add: field_simps)
  have nz: "M *v z + (- c) *\<^sub>R u \<noteq> 0" for z :: "real^'n"
  proof
    assume "M *v z + (- c) *\<^sub>R u = 0"
    then have mz: "M *v z = c *\<^sub>R u" by (simp add: algebra_simps)
    have "M *v ((1 / c) *\<^sub>R z) = (1 / c) *\<^sub>R (M *v z)"
      by (rule matrix_vector_mult_scaleR)
    also have "\<dots> = (1 / c) *\<^sub>R (c *\<^sub>R u)" unfolding mz by (rule refl)
    also have "\<dots> = u" using c0 by simp
    finally have "u = M *v ((1 / c) *\<^sub>R z)" by (rule sym)
    then show False using nu by blast
  qed
  show ?thesis by (rule that[OF lt]) (use nz in blast)
qed


text \<open>The sweep.  With \<open>M\<close> invertible the tilt \<open>\<eta> := -M(y - x)\<close> selects
  \<open>y\<close> itself as the tilted minimiser: whatever minimiser \<open>y'\<close> the
  machinery returns, the second horn says \<open>M(y' - x) + \<eta> = 0\<close>, i.e.
  \<open>M(y' - x) = M(y - x)\<close>, and injectivity forces \<open>y' = y\<close>.  So the pinch
  is available at EVERY point of a neighbourhood of \<open>x\<close>, not just at the
  minimisers of one fixed tilt --- and that is exactly the hypothesis of
  \<open>pinch_implies_constant\<close>.\<close>

lemma invertible_matrix_vector_inj:
  fixes M :: "real^'n::finite^'n"
  assumes inv: "invertible M" and eq: "M *v a = M *v b"
  shows "a = b"
proof -
  obtain M' where M': "M' ** M = mat 1"
    using inv invertible_left_inverse by blast
  have "a = (M' ** M) *v a" unfolding M' by (simp add: matrix_vector_mul_lid)
  also have "\<dots> = M' *v (M *v a)" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = M' *v (M *v b)" unfolding eq by (rule refl)
  also have "\<dots> = (M' ** M) *v b" by (simp add: matrix_vector_mul_assoc)
  also have "\<dots> = b" unfolding M' by (simp add: matrix_vector_mul_lid)
  finally show ?thesis .
qed

lemma horn_B_locally_constant:
  fixes W :: "real^'n::finite \<Rightarrow> real" and M :: "real^'n^'n" and x :: "real^'n"
  assumes lsc: "\<And>a z. a < W z \<Longrightarrow> \<exists>d>0. \<forall>u. dist z u < d \<longrightarrow> a < W u"
    and symM: "transpose M = M" and inv: "invertible M"
    and rho: "0 < \<rho>" and c0: "0 < c"
    and h0: "0 < h" and hle: "h \<le> c * \<rho>"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      W x + ((z - x) \<bullet> (M *v (z - x))) / 2 + c * ((z - x) \<bullet> (z - x)) \<le> W z"
    and hornB: "\<And>\<eta> y. norm \<eta> < h \<Longrightarrow> dist x y < \<rho> \<Longrightarrow>
      norm (y - x) \<le> norm \<eta> / c \<Longrightarrow>
      (\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
        W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x)))
      \<Longrightarrow> M *v (y - x) + \<eta> = 0"
  obtains r where "0 < r" and "\<And>y. dist x y < r \<Longrightarrow> W y = W x"
proof -
  obtain C where C0: "0 \<le> C"
    and Cb: "\<And>u :: real^'n. - (C * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
  proof (rule quad_form_bounded_below[where M = M])
    fix CC :: real
    assume a1: "0 \<le> CC"
      and a2: "\<And>u :: real^'n.
        - (CC * (norm u * norm u)) \<le> (u \<bullet> (M *v u)) / 2"
    show thesis by (rule that[OF a1 a2])
  qed
  have bl: "bounded_linear ((*v) M)" by (rule matrix_vector_mul_bounded_linear)
  define N where "N = onorm ((*v) M)"
  have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
  have N1: "0 < N + 1" using N0 by simp
  define r0 where "r0 = min (\<rho> / 2) (h / (2 * (N + 1)))"
  have r00: "0 < r0" unfolding r0_def using rho h0 N1 by simp
  have cp: "0 < c * \<rho>" using c0 rho by simp
  have pinch0: "W y - C * (dist y w * dist y w) \<le> W w"
    if dy: "dist x y < r0" and dw: "dist y w < \<rho> - dist x y"
    for y w :: "real^'n"
  proof -
    define \<eta> where "\<eta> = - (M *v (y - x))"
    have nyx: "norm (y - x) = dist x y"
      by (simp add: dist_norm norm_minus_commute)
    have e1: "norm \<eta> = norm (M *v (y - x))" unfolding \<eta>_def by simp
    have e2: "norm (M *v (y - x)) \<le> N * norm (y - x)"
      unfolding N_def by (rule onorm[OF bl])
    have s1: "N * norm (y - x) \<le> N * r0"
      by (rule mult_left_mono) (use nyx dy N0 in auto)
    have s2: "N * r0 \<le> (N + 1) * r0"
      by (rule mult_right_mono) (use r00 in auto)
    have hb: "norm \<eta> \<le> (N + 1) * r0" using e1 e2 s1 s2 by linarith
    have q1: "(N + 1) * r0 \<le> (N + 1) * (h / (2 * (N + 1)))"
      by (rule mult_left_mono) (use r0_def N1 in auto)
    have q2: "(N + 1) * (h / (2 * (N + 1))) = h / 2"
      using N1 by (simp add: field_simps)
    have hlth: "norm \<eta> < h" using hb q1 q2 h0 by linarith
    have hlt: "norm \<eta> < c * \<rho>" using hlth hle by linarith
    obtain y' where dxy': "dist x y' < \<rho>"
      and cl': "norm (y' - x) \<le> norm \<eta> / c"
      and loc': "\<And>w. dist y' w < \<rho> - dist x y' \<Longrightarrow>
        W y' - (((y' - x) \<bullet> (M *v (y' - x))) / 2 + \<eta> \<bullet> (y' - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    proof (rule tilted_local_touching[OF lsc rho c0 sep hlt])
      fix yy :: "real^'n"
      assume b1: "dist x yy < \<rho>" and b2: "norm (yy - x) \<le> norm \<eta> / c"
        and b3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
          W yy - (((yy - x) \<bullet> (M *v (yy - x))) / 2 + \<eta> \<bullet> (yy - x))
            \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      show thesis by (rule that[OF b1 b2 b3])
    qed
    have g0: "M *v (y' - x) + \<eta> = 0"
      by (rule hornB[OF hlth dxy' cl' loc'])
    have meq: "M *v (y' - x) = M *v (y - x)"
      using g0 unfolding \<eta>_def by (simp add: algebra_simps)
    have yeq: "y' = y"
      using invertible_matrix_vector_inj[OF inv meq] by simp
    show ?thesis
    proof (rule quad_minimality_pinch[OF symM Cb])
      show "M *v (y - x) + \<eta> = 0" using g0 unfolding yeq .
      show "W y - (((y - x) \<bullet> (M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> W w - (((w - x) \<bullet> (M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        using loc'[of w] dw unfolding yeq by simp
    qed
  qed
  define r where "r = min r0 (\<rho> / 4)"
  have r0': "0 < r" unfolding r_def using r00 rho by simp
  have pin: "W u - C * (dist u w * dist u w) \<le> W w"
    if ub: "u \<in> ball x r" and wb: "w \<in> ball x r" for u w :: "real^'n"
  proof -
    have du: "dist x u < r" using ub by simp
    have dw: "dist x w < r" using wb by simp
    have a1: "dist x u < r0" using du unfolding r_def by simp
    have a2: "dist u w < \<rho> - dist x u"
    proof -
      have t: "dist u w \<le> dist u x + dist x w" by (rule dist_triangle)
      have "dist u x < r" using du by (simp add: dist_commute)
      then have lt2: "dist u w < 2 * r" using t dw by linarith
      have g1: "2 * r \<le> \<rho> / 2" unfolding r_def using rho by simp
      have g2: "dist x u < \<rho> / 4" using du unfolding r_def by simp
      show ?thesis using lt2 g1 g2 rho by linarith
    qed
    show ?thesis by (rule pinch0[OF a1 a2])
  qed
  have const: "W y = W x" if dy: "dist x y < r" for y :: "real^'n"
  proof (rule pinch_implies_constant[OF r0' C0])
    show "\<And>u w. u \<in> ball x r \<Longrightarrow> w \<in> ball x r \<Longrightarrow>
        W u - C * (dist u w * dist u w) \<le> W w"
      by (rule pin)
    show "y \<in> ball x r" using dy by simp
  qed
  show ?thesis by (rule that[OF r0']) (use const in blast)
qed


text \<open>The second horn dies here.  Suppose \<open>v\<^sub>*\<close> were constant \<open>= c\<close> on a
  ball around \<open>x\<close> whose closure lies in \<open>K\<close>.  The envelope's own defining
  property supplies points \<open>z\<close> arbitrarily close to \<open>x\<close> at which \<open>v\<close>
  itself is within \<open>\<theta>/2\<close> of \<open>c\<close>.  But the deterministic-radius member
  started at such a \<open>z\<close> stays inside the ball for a time \<open>\<theta>\<close> that does
  NOT shrink with \<open>z\<close>, and its endpoint is again in the ball where
  \<open>v \<ge> c\<close>; so \<open>paper_v_ball_lower_plus\<close> gives \<open>v z \<ge> \<theta> + c\<close>.  Those two
  are incompatible.

  The hypothesis \<open>c < T/2\<close> is what keeps the horizon cap inert.  It
  cannot be dropped: if \<open>v \<equiv> T\<close> on an open set then \<open>v\<^sub>*\<close> IS locally
  constant there, and no contradiction is available --- indeed the
  supersolution inequality itself fails at such a point, since a
  constant test function would demand \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.  For a
  bounded \<open>K\<close> the hypothesis is discharged by
  @{thm [source] paper_v_le_ball_bound} once \<open>T\<close> exceeds twice the ball
  bound.\<close>

theorem paper_v_not_locally_constant:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and tv :: "real^'n \<Rightarrow> real" and r T :: real
  assumes T0: "0 < T" and L1: "1 \<le> L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K"
    and tvdef: "tv = (\<lambda>u. enn2real (paper_v k L T K u))"
    and r0: "0 < r" and sub: "cball x r \<subseteq> K"
    and cap: "lsc_env tv x < T / 2"
    and const: "\<And>y. dist x y < r \<Longrightarrow> lsc_env tv y = lsc_env tv x"
  shows False
proof -
  have tv0: "\<And>u. 0 \<le> tv u" unfolding tvdef by simp
  have c0: "0 \<le> lsc_env tv x" by (rule lsc_env_ge[OF tv0])
  define rB where "rB = r / 4"
  have rB0: "0 < rB" unfolding rB_def using r0 by simp
  have rBr: "5 * rB / 4 \<le> r" unfolding rB_def using r0 by simp
  define e :: "real^'n" where "e = axis (undefined :: 'n) (1 :: real)"
  have e1: "norm e = 1" unfolding e_def by simp
  define y\<^sub>0 where "y\<^sub>0 = x + (rB / 4) *\<^sub>R e"
  have dxy: "dist x y\<^sub>0 = rB / 4"
  proof -
    have "dist x y\<^sub>0 = norm ((rB / 4) *\<^sub>R e)"
      unfolding y\<^sub>0_def by (simp add: dist_norm)
    also have "\<dots> = \<bar>rB / 4\<bar> * norm e" by simp
    finally show ?thesis using rB0 e1 by simp
  qed
  have near: "dist x w \<le> 5 * rB / 4" if "dist y\<^sub>0 w \<le> rB" for w
  proof -
    have "dist x w \<le> dist x y\<^sub>0 + dist y\<^sub>0 w" by (rule dist_triangle)
    then show ?thesis using dxy that by linarith
  qed
  have subB: "cball y\<^sub>0 rB \<subseteq> K"
  proof
    fix w :: "real^'n" assume "w \<in> cball y\<^sub>0 rB"
    then have "dist y\<^sub>0 w \<le> rB" by simp
    then have "dist x w \<le> r" using near[of w] rBr by linarith
    then show "w \<in> K" using sub by auto
  qed
  have cn0: "0 < real CARD('n) - 1"
  proof -
    have "2 \<le> CARD('n)" using k1 kn by linarith
    then have "(2 :: real) \<le> real CARD('n)"
      by (simp add: of_nat_le_iff [where m = 2, symmetric])
    then show ?thesis by linarith
  qed
  define \<theta> where "\<theta> = min (T / 2) (rB\<^sup>2 / (4 * (real CARD('n) - 1)))"
  have th0: "0 < \<theta>" unfolding \<theta>_def using T0 rB0 cn0 by simp
  have vlow: "lsc_env tv x \<le> tv w" if wb: "w \<in> ball y\<^sub>0 rB" for w
  proof -
    have lt: "dist y\<^sub>0 w < rB" using wb by simp
    have tr: "dist x w \<le> dist x y\<^sub>0 + dist y\<^sub>0 w" by (rule dist_triangle)
    have "dist x w < r" using tr lt dxy rBr by linarith
    then have "lsc_env tv w = lsc_env tv x" by (rule const)
    moreover have "lsc_env tv w \<le> tv w" by (rule lsc_env_le_self[OF tv0])
    ultimately show ?thesis by linarith
  qed
  have d8: "0 < rB / 8" using rB0 by simp
  have t2: "0 < \<theta> / 2" using th0 by simp
  obtain z where dz: "dist x z < rB / 8"
    and vz: "tv z < lsc_env tv x + \<theta> / 2"
  proof (rule lsc_env_approx[OF tv0 d8 t2])
    fix zz :: "real^'n"
    assume a1: "dist x zz < rB / 8" and a2: "tv zz < lsc_env tv x + \<theta> / 2"
    show thesis by (rule that[OF a1 a2])
  qed
  have dzy: "dist z y\<^sub>0 < 3 * rB / 8"
  proof -
    have "dist z y\<^sub>0 \<le> dist z x + dist x y\<^sub>0" by (rule dist_triangle)
    moreover have "dist z x = dist x z" by (rule dist_commute)
    ultimately show ?thesis using dz dxy by linarith
  qed
  have dzy': "rB / 8 < dist z y\<^sub>0"
  proof -
    have "dist x y\<^sub>0 \<le> dist x z + dist z y\<^sub>0" by (rule dist_triangle)
    then show ?thesis using dz dxy by linarith
  qed
  have nzy: "norm (z - y\<^sub>0) = dist z y\<^sub>0" by (simp add: dist_norm)
  have zy: "z \<noteq> y\<^sub>0" using dzy' rB0 by auto
  have zin: "norm (z - y\<^sub>0) < rB" unfolding nzy using dzy rB0 by linarith
  have pv: "ennreal (min (T / 2)
      ((rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min (lsc_env tv x) (T / 2))
      \<le> paper_v k L T K z"
  proof (rule paper_v_ball_lower_plus[OF T0 L1 k1 kn Kc subB zy zin c0])
    fix w :: "real^'n" assume "w \<in> ball y\<^sub>0 rB"
    then have "lsc_env tv x \<le> tv w" by (rule vlow)
    then show "lsc_env tv x \<le> enn2real (paper_v k L T K w)"
      using tvdef by simp
  qed
  have sq: "(norm (z - y\<^sub>0))\<^sup>2 \<le> rB\<^sup>2 / 2"
  proof -
    have n0: "0 \<le> norm (z - y\<^sub>0)" by simp
    have rBsq: "0 \<le> rB\<^sup>2" by simp
    have "(norm (z - y\<^sub>0))\<^sup>2 \<le> (3 * rB / 8)\<^sup>2"
      using zin dzy n0 unfolding nzy by (intro power_mono) auto
    also have "\<dots> = 9 / 64 * rB\<^sup>2"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> \<le> 1 / 2 * rB\<^sup>2"
      by (rule mult_right_mono[OF _ rBsq]) simp
    also have "\<dots> = rB\<^sup>2 / 2" by simp
    finally show ?thesis .
  qed
  have B: "rB\<^sup>2 / (4 * (real CARD('n) - 1))
      \<le> (rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))"
  proof -
    have m0: "0 \<le> 2 * (real CARD('n) - 1)" using cn0 by auto
    have a: "rB\<^sup>2 / 2 \<le> rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2" using sq by linarith
    have eqd: "(rB\<^sup>2 / 2) / (2 * (real CARD('n) - 1))
        = rB\<^sup>2 / (4 * (real CARD('n) - 1))"
      by (simp add: field_simps)
    have "(rB\<^sup>2 / 2) / (2 * (real CARD('n) - 1))
        \<le> (rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1))"
      by (rule divide_right_mono[OF a m0])
    then show ?thesis unfolding eqd[symmetric] .
  qed
  have mc: "min (lsc_env tv x) (T / 2) = lsc_env tv x" using cap by simp
  have fin: "\<theta> + lsc_env tv x \<le> min (T / 2)
      ((rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
      + min (lsc_env tv x) (T / 2)"
    unfolding \<theta>_def mc using B by linarith
  have T0': "0 \<le> T" using T0 by linarith
  have ltop: "paper_v k L T K z < \<top>"
    using paper_v_neq_top[OF T0'] by (simp add: less_top)
  have eq: "ennreal (tv z) = paper_v k L T K z"
    unfolding tvdef using ltop by (simp add: ennreal_enn2real)
  have "ennreal (\<theta> + lsc_env tv x) \<le> paper_v k L T K z"
  proof -
    have "ennreal (\<theta> + lsc_env tv x) \<le> ennreal (min (T / 2)
        ((rB\<^sup>2 - (norm (z - y\<^sub>0))\<^sup>2) / (2 * (real CARD('n) - 1)))
        + min (lsc_env tv x) (T / 2))"
      by (rule ennreal_leI[OF fin])
    then show ?thesis using pv by (rule order_trans)
  qed
  then have "ennreal (\<theta> + lsc_env tv x) \<le> ennreal (tv z)"
    unfolding eq .
  then have ge: "\<theta> + lsc_env tv x \<le> tv z"
    using tv0[of z] by (simp add: ennreal_le_iff)
  show False using ge vz th0 by linarith
qed


text \<open>Horn A at a GIVEN local minimiser.  \<open>paper_v_case2_tilt_step\<close>
  produces its own minimiser; the assembly instead has one handed to it
  by the case split, so the last step of that proof is isolated here.\<close>

lemma paper_v_case2_at_minimiser:
  fixes K :: "(real^'n::finite) set" and x y \<eta> :: "real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and symH: "transpose H = H"
    and rho: "0 < \<rho>" and sub: "cball x \<rho> \<subseteq> interior K"
    and dxy: "dist x y < \<rho>"
    and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y
          - (((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
        \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) w
          - (((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    and gy: "(H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta> \<noteq> 0"
  shows "1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
      (H - \<epsilon> *\<^sub>R mat 1)"
proof -
  have symM: "transpose (H - \<epsilon> *\<^sub>R mat 1) = H - \<epsilon> *\<^sub>R mat 1"
    by (rule transpose_sub_smat[OF symH])
  have rp: "0 < \<rho> - dist x y" using dxy by simp
  have yi: "y \<in> interior K"
  proof -
    have "y \<in> cball x \<rho>" using dxy by (auto simp: dist_commute)
    then show ?thesis using sub by blast
  qed
  have tfy: "test_fun_at
      (\<lambda>z. 0 + ((z - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (z - x))) / 2 + \<eta> \<bullet> (z - x))
      (\<lambda>z. (H - \<epsilon> *\<^sub>R mat 1) *v (z - x) + \<eta>) (H - \<epsilon> *\<^sub>R mat 1) y"
    by (rule test_fun_at_shifted_quadratic[OF symM])
  have tminy: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y
        - (0 + ((y - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
      \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) w
        - (0 + ((w - x) \<bullet> ((H - \<epsilon> *\<^sub>R mat 1) *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
    if wK: "w \<in> K" and dw: "dist y w < \<rho> - dist x y" for w
    using loc[OF dw] by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> 1 \<le> ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1)"
    then have flt: "ell_op k L ((H - \<epsilon> *\<^sub>R mat 1) *v (y - x) + \<eta>)
        (H - \<epsilon> *\<^sub>R mat 1) < 1" by simp
    show False
      by (rule paper_v_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc yi
            tfy rp tminy gy flt])
  qed
qed


subsection \<open>Case 2 assembled at a fixed \<open>\<epsilon>\<close>\<close>

text \<open>The dichotomy.  Either arbitrarily small tilts admit a local
  minimiser with NONZERO gradient --- and then Case 1 fires at each of
  them, the gradients tend to \<open>0\<close> because \<open>\<bar>y - x\<bar> \<le> 4\<bar>\<eta>\<bar>/\<epsilon>\<close>, and
  \<open>ell_op_usc_ge_one_limit\<close> delivers the inequality at \<open>p = 0\<close> --- or
  some threshold fails, which is exactly the hypothesis of
  \<open>horn_B_locally_constant\<close>, and then \<open>v\<^sub>*\<close> is locally constant, which
  \<open>paper_v_not_locally_constant\<close> refutes.

  A singular \<open>H - \<epsilon>\<cdot>1\<close> needs no separate treatment: it supplies
  arbitrarily small tilts for which the gradient can never vanish, so
  the first branch always applies.  That is why the second branch may
  assume invertibility.\<close>

theorem paper_v_case2_eps:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x" and gx0: "g x = 0"
    and rho0: "0 < \<rho>\<^sub>0"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho>\<^sub>0 \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y - \<phi> y"
    and cap: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x < T / 2"
    and e0: "0 < \<epsilon>"
  shows "1 \<le> ell_op_usc k L 0 (H - \<epsilon> *\<^sub>R mat 1)"
proof -
  let ?W = "lsc_env (\<lambda>u. enn2real (paper_v k L T K u))"
  let ?M = "H - \<epsilon> *\<^sub>R mat 1"
  have L1': "1 \<le> L" using L1 by linarith
  have symH: "transpose H = H" using tf unfolding test_fun_at_def by blast
  have symM: "transpose ?M = ?M" by (rule transpose_sub_smat[OF symH])
  have c0: "0 < \<epsilon> / 4" using e0 by simp
  have tv0: "\<And>u. (0 :: real) \<le> enn2real (paper_v k L T K u)" by simp
  have lscW: "\<exists>d>0. \<forall>u. dist z u < d \<longrightarrow> a < ?W u"
    if lt: "a < ?W z" for a and z :: "real^'n"
  proof (rule lsc_env_lower[OF tv0 lt])
    fix d assume "0 < d" and "\<forall>u. dist z u < d \<longrightarrow> a < ?W u"
    then show ?thesis by blast
  qed
  obtain \<rho> where rho: "0 < \<rho>" and subK: "cball x \<rho> \<subseteq> interior K"
    and sep: "\<And>z. z \<in> cball x \<rho> \<Longrightarrow>
      ?W x + ((z - x) \<bullet> (?M *v (z - x))) / 2
        + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> ?W z"
  proof (rule paper_v_case2_separation[OF xi tf gx0 rho0 tmin e0])
    fix rr :: real
    assume a1: "0 < rr" and a2: "cball x rr \<subseteq> interior K"
      and a3: "\<And>z. z \<in> cball x rr \<Longrightarrow>
        ?W x + ((z - x) \<bullet> (?M *v (z - x))) / 2
          + (\<epsilon> / 4) * ((z - x) \<bullet> (z - x)) \<le> ?W z"
    show thesis by (rule that[OF a1 a2 a3])
  qed
  define good where "good = (\<lambda>\<delta> :: real. \<exists>\<eta> y :: real^'n.
      norm \<eta> < \<delta> \<and> dist x y < \<rho> \<and> norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4) \<and>
      (\<forall>w. dist y w < \<rho> - dist x y \<longrightarrow>
        ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
          \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x)))
      \<and> ?M *v (y - x) + \<eta> \<noteq> 0)"
  define \<delta>s where "\<delta>s = (\<lambda>j :: nat. min ((\<epsilon> / 4) * \<rho>) (1 / real (Suc j)))"
  have ds0: "0 < \<delta>s j" for j unfolding \<delta>s_def using c0 rho by simp
  show ?thesis
  proof (cases "\<forall>j. good (\<delta>s j)")
    case True
    have bl: "bounded_linear ((*v) ?M)"
      by (rule matrix_vector_mul_bounded_linear)
    define N where "N = onorm ((*v) ?M)"
    have N0: "0 \<le> N" unfolding N_def by (rule onorm_pos_le[OF bl])
    have Cpos: "0 \<le> 4 * N / \<epsilon> + 1" using N0 e0 by simp
    have ex: "\<exists>p :: real^'n. 1 \<le> ell_op k L p ?M
        \<and> norm p \<le> (4 * N / \<epsilon> + 1) * \<delta>s j" for j
    proof -
      have gd: "good (\<delta>s j)" using True by blast
      obtain \<eta> y :: "real^'n" where hn: "norm \<eta> < \<delta>s j"
        and dxy: "dist x y < \<rho>"
        and cl: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
        and loc: "\<forall>w. dist y w < \<rho> - dist x y \<longrightarrow>
          ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
            \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        and gy: "?M *v (y - x) + \<eta> \<noteq> 0"
        using gd unfolding good_def by blast
      have ge: "1 \<le> ell_op k L (?M *v (y - x) + \<eta>) ?M"
      proof (rule paper_v_case2_at_minimiser[OF T0 L1 k1 kn Kc symH rho subK
              dxy _ gy])
        fix w :: "real^'n" assume "dist y w < \<rho> - dist x y"
        then show "?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
            \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
          using loc by blast
      qed
      have nb: "norm (?M *v (y - x) + \<eta>) \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
      proof -
        have t1: "norm (?M *v (y - x) + \<eta>) \<le> norm (?M *v (y - x)) + norm \<eta>"
          by (rule norm_triangle_ineq)
        have t2: "norm (?M *v (y - x)) \<le> N * norm (y - x)"
          unfolding N_def by (rule onorm[OF bl])
        have t3: "N * norm (y - x) \<le> N * (norm \<eta> / (\<epsilon> / 4))"
          by (rule mult_left_mono[OF cl N0])
        have t4: "N * (norm \<eta> / (\<epsilon> / 4)) = (4 * N / \<epsilon>) * norm \<eta>"
          using e0 by (simp add: field_simps)
        have t5: "(4 * N / \<epsilon>) * norm \<eta> + norm \<eta> = (4 * N / \<epsilon> + 1) * norm \<eta>"
          by (simp add: field_simps)
        have t6: "(4 * N / \<epsilon> + 1) * norm \<eta> \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
          by (rule mult_left_mono[OF _ Cpos]) (use hn in linarith)
        show ?thesis using t1 t2 t3 t4 t5 t6 by linarith
      qed
      show ?thesis using ge nb by blast
    qed
    obtain ps :: "nat \<Rightarrow> real^'n" where
      psge: "\<And>j. 1 \<le> ell_op k L (ps j) ?M"
      and psn: "\<And>j. norm (ps j) \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
      using ex by metis
    have dslim: "\<delta>s \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich)
      show "\<forall>\<^sub>F j in sequentially. (0 :: real) \<le> \<delta>s j"
        using ds0 by (simp add: less_imp_le)
      show "\<forall>\<^sub>F j in sequentially. \<delta>s j \<le> 1 / real (Suc j)"
        unfolding \<delta>s_def by simp
      show "((\<lambda>j. 0 :: real) \<longlongrightarrow> 0) sequentially" by simp
      show "((\<lambda>j :: nat. 1 / real (Suc j)) \<longlongrightarrow> 0) sequentially"
        using LIMSEQ_inverse_real_of_nat by (simp add: divide_inverse)
    qed
    have d1: "(\<lambda>j. (4 * N / \<epsilon> + 1) * \<delta>s j) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>j. (4 * N / \<epsilon> + 1) * \<delta>s j) \<longlonglongrightarrow> (4 * N / \<epsilon> + 1) * 0"
        by (intro tendsto_mult tendsto_const dslim)
      then show ?thesis by simp
    qed
    have d2: "(\<lambda>j. norm (ps j)) \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich)
      show "\<forall>\<^sub>F j in sequentially. (0 :: real) \<le> norm (ps j)" by simp
      show "\<forall>\<^sub>F j in sequentially. norm (ps j) \<le> (4 * N / \<epsilon> + 1) * \<delta>s j"
        using psn by simp
      show "((\<lambda>j. 0 :: real) \<longlongrightarrow> 0) sequentially" by simp
      show "((\<lambda>j. (4 * N / \<epsilon> + 1) * \<delta>s j) \<longlongrightarrow> 0) sequentially" by (rule d1)
    qed
    have plim: "ps \<longlonglongrightarrow> 0" using d2 by (simp add: tendsto_norm_zero_iff)
    have lim: "(\<lambda>j. (ps j, ?M)) \<longlonglongrightarrow> (0, ?M)"
      by (intro tendsto_Pair plim tendsto_const)
    have gew: "1 \<le> ell_op_usc k L (ps j) ?M" for j
    proof -
      have "(1 :: ereal) \<le> ereal (ell_op k L (ps j) ?M)"
        using psge[of j] by simp
      also have "\<dots> \<le> ell_op_usc k L (ps j) ?M"
        by (rule ell_op_le_ell_op_usc)
      finally show ?thesis .
    qed
    show ?thesis by (rule ell_op_usc_ge_one_limit[OF gew lim])
  next
    case False
    then obtain j where nj: "\<not> good (\<delta>s j)" by blast
    have h0: "0 < \<delta>s j" by (rule ds0)
    have hle: "\<delta>s j \<le> (\<epsilon> / 4) * \<rho>" unfolding \<delta>s_def by simp
    show ?thesis
    proof (cases "invertible ?M")
      case False
      \<comment> \<open>a singular \<open>?M\<close> yields tilts whose gradient never vanishes\<close>
      obtain \<eta> :: "real^'n" where hn: "norm \<eta> < \<delta>s j"
        and nz: "\<And>z :: real^'n. ?M *v z + \<eta> \<noteq> 0"
      proof (rule singular_matrix_avoids_range[OF False h0])
        fix ee :: "real^'n"
        assume b1: "norm ee < \<delta>s j" and b2: "\<And>z :: real^'n. ?M *v z + ee \<noteq> 0"
        show thesis by (rule that[OF b1 b2])
      qed
      have hlt: "norm \<eta> < (\<epsilon> / 4) * \<rho>" using hn hle by linarith
      obtain y :: "real^'n" where dxy: "dist x y < \<rho>"
        and cl: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
        and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
          ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
            \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
      proof (rule tilted_local_touching[OF lscW rho c0 sep hlt])
        fix yy :: "real^'n"
        assume b1: "dist x yy < \<rho>" and b2: "norm (yy - x) \<le> norm \<eta> / (\<epsilon> / 4)"
          and b3: "\<And>w. dist yy w < \<rho> - dist x yy \<Longrightarrow>
            ?W yy - (((yy - x) \<bullet> (?M *v (yy - x))) / 2 + \<eta> \<bullet> (yy - x))
              \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        show thesis by (rule that[OF b1 b2 b3])
      qed
      have gd: "good (\<delta>s j)"
        unfolding good_def using hn dxy cl loc nz[of "y - x"] by blast
      show ?thesis using gd nj by simp
    next
      case True
      \<comment> \<open>the second horn: \<open>v\<^sub>*\<close> would be locally constant\<close>
      have hornB: "?M *v (y - x) + \<eta> = 0"
        if hn: "norm \<eta> < \<delta>s j" and dxy: "dist x y < \<rho>"
          and cl: "norm (y - x) \<le> norm \<eta> / (\<epsilon> / 4)"
          and loc: "\<And>w. dist y w < \<rho> - dist x y \<Longrightarrow>
            ?W y - (((y - x) \<bullet> (?M *v (y - x))) / 2 + \<eta> \<bullet> (y - x))
              \<le> ?W w - (((w - x) \<bullet> (?M *v (w - x))) / 2 + \<eta> \<bullet> (w - x))"
        for \<eta> y :: "real^'n"
      proof (rule ccontr)
        assume "?M *v (y - x) + \<eta> \<noteq> 0"
        then have "good (\<delta>s j)"
          unfolding good_def using hn dxy cl loc by blast
        then show False using nj by simp
      qed
      obtain rr where rr0: "0 < rr"
        and rc: "\<And>y. dist x y < rr \<Longrightarrow> ?W y = ?W x"
      proof (rule horn_B_locally_constant[OF lscW symM True rho c0 h0 hle sep
              hornB])
        fix r' :: real
        assume b1: "0 < r'" and b2: "\<And>y. dist x y < r' \<Longrightarrow> ?W y = ?W x"
        show thesis by (rule that[OF b1 b2])
      qed
      define r2 where "r2 = min (rr / 2) (\<rho> / 2)"
      have r20: "0 < r2" unfolding r2_def using rr0 rho by simp
      have r2K: "cball x r2 \<subseteq> K"
      proof -
        have "cball x r2 \<subseteq> cball x \<rho>"
          unfolding r2_def using rho by (auto simp: mem_cball)
        then show ?thesis using subK interior_subset by blast
      qed
      have contra: False
      proof (rule paper_v_not_locally_constant[OF T0 L1' k1 kn Kc refl r20 r2K])
        show "?W x < T / 2" by (rule cap)
      next
        fix y :: "real^'n" assume dy: "dist x y < r2"
        have "r2 \<le> rr / 2" unfolding r2_def by simp
        then have "dist x y < rr" using dy rr0 by linarith
        then show "?W y = ?W x" by (rule rc)
      qed
      then show ?thesis by simp
    qed
  qed
qed


subsection \<open>Case 2, and the supersolution property\<close>

text \<open>Letting \<open>\<epsilon> \<rightarrow> 0\<close> along \<open>1/(j+1)\<close> moves the Hessian back to \<open>H\<close>,
  and one more application of \<open>ell_op_usc_ge_one_limit\<close> --- this time in
  the matrix argument rather than the gradient --- finishes Case 2.\<close>

theorem paper_v_case2:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<phi> :: "real^'n \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K" and xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x" and gx0: "g x = 0"
    and rho0: "0 < \<rho>\<^sub>0"
    and tmin: "\<And>y. y \<in> K \<Longrightarrow> dist x y < \<rho>\<^sub>0 \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x - \<phi> x
        \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y - \<phi> y"
    and cap: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x < T / 2"
  shows "1 \<le> ell_op_usc k L 0 H"
proof -
  define es where "es = (\<lambda>j :: nat. 1 / real (Suc j))"
  have es0: "0 < es j" for j unfolding es_def by simp
  have eslim: "es \<longlonglongrightarrow> 0"
    unfolding es_def using LIMSEQ_inverse_real_of_nat
    by (simp add: divide_inverse)
  have ge: "1 \<le> ell_op_usc k L 0 (H - es j *\<^sub>R mat 1)" for j
    by (rule paper_v_case2_eps[OF T0 L1 k1 kn Kc xi tf gx0 rho0 tmin cap es0])
  have lim: "(\<lambda>j. (0 :: real^'n, H - es j *\<^sub>R mat 1)) \<longlonglongrightarrow> (0, H)"
  proof -
    have "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0 *\<^sub>R mat 1"
      by (rule tendsto_scaleR[OF eslim tendsto_const])
    then have z: "(\<lambda>j. es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> 0" by simp
    have "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H - 0"
      by (rule tendsto_diff[OF tendsto_const z])
    then have m: "(\<lambda>j. H - es j *\<^sub>R (mat 1 :: real^'n^'n)) \<longlonglongrightarrow> H" by simp
    show ?thesis by (rule tendsto_Pair[OF tendsto_const m])
  qed
  show ?thesis by (rule ell_op_usc_ge_one_limit[OF ge lim])
qed

text \<open>Definition 3.1(b) for the paper's own value function.  Case 1
  (\<open>\<nabla>\<phi>(x) \<noteq> 0\<close>) is the skew-trick contradiction, lifted from
  \<open>ell_op\<close> to \<open>ell_op_usc\<close>; Case 2 (\<open>\<nabla>\<phi>(x) = 0\<close>) is the dichotomy
  above.  A global touching over \<open>K\<close> is in particular a local one, which
  is all either case consumes.

  The hypothesis \<open>cap\<close> says the horizon never binds on the interior.  It
  is needed only by Case 2 --- Case 1 DERIVES it from the nonvanishing
  gradient --- and it is faithful to the paper, which has no horizon at
  all.  For a bounded \<open>K\<close> it follows from
  @{thm [source] paper_v_le_ball_bound}.\<close>

theorem paper_v_supersol_lsc:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 < L" and k1: "1 \<le> k" and kn: "k < CARD('n)"
    and Kc: "closed K"
    and cap: "\<And>x :: real^'n. x \<in> interior K \<Longrightarrow>
      lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x < T / 2"
  shows "visc_supersol_lsc k L K (interior K)
      (\<lambda>u. enn2real (paper_v k L T K u))"
  unfolding visc_supersol_lsc_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume xi: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and tmin: "\<forall>y\<in>K. lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x - \<phi> x
      \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y - \<phi> y"
  have loc: "lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) x - \<phi> x
      \<le> lsc_env (\<lambda>u. enn2real (paper_v k L T K u)) y - \<phi> y"
    if yK: "y \<in> K" and dy: "dist x y < 1" for y
    using tmin yK by blast
  show "1 \<le> ell_op_usc k L (g x) H"
  proof (cases "g x = 0")
    case False
    have plain: "1 \<le> ell_op k L (g x) H"
    proof (rule ccontr)
      assume "\<not> 1 \<le> ell_op k L (g x) H"
      then have flt: "ell_op k L (g x) H < 1" by simp
      show False
        by (rule paper_v_supersol_contradiction_case1_lsc[OF T0 L1 k1 kn Kc xi
              tf zero_less_one loc False flt])
    qed
    have "(1 :: ereal) \<le> ereal (ell_op k L (g x) H)" using plain by simp
    also have "\<dots> \<le> ell_op_usc k L (g x) H" by (rule ell_op_le_ell_op_usc)
    finally show ?thesis .
  next
    case True
    have "1 \<le> ell_op_usc k L 0 H"
      by (rule paper_v_case2[OF T0 L1 k1 kn Kc xi tf True zero_less_one loc
            cap[OF xi]])
    then show ?thesis unfolding True .
  qed
qed


section \<open>What remains for clause (2)\<close>

text \<open>Where clause (2) stands after this file.

  \<^bold>\<open>PROVED --- the SUBSOLUTION half, with the operator of Eq. (1.9) itself.\<close>
  @{thm [source] paper_v_visc_subsol}: for every \<open>0 < T\<close>, \<open>1 \<le> L\<close>, closed \<open>K\<close>
  and \<open>k < CARD('n)\<close>, \<open>enn2real \<circ> paper_v k L T K\<close> is a viscosity subsolution
  on \<open>interior K\<close>.

  \<^bold>\<open>Gap 1 (localisation) --- CLOSED.\<close>  The argument stops at the exit time of a
  ball, uses the touching only on the closed ball, and the quadratic expansion
  is EXACT at the stopping time, so no remainder estimate ever appears.  The
  chain: @{thm [source] pball_exit_path_stopping_time},
  @{thm [source] pball_exit_measurable},
  @{thm [source] paper_pair_class_X_entry_stopped},
  @{thm [source] paper_pair_class_Y_stopped_mean_sconstraint},
  @{thm [source] paper_v_subsol_quadratic_ball},
  @{thm [source] test_fun_quadratic_dominates}.

  \<^bold>\<open>Gap 2 (orthogonality: from \<open>ell_op_s\<close> to \<open>ell_op\<close>) --- CLOSED, and NOT by
  the paper's route.\<close>  The paper (\<section>3.1, (3.13)--(3.19)) argues by
  contradiction, splitting the time axis by whether \<open>\<nabla>\<phi>\<^sup>T a\<^sub>t \<nabla>\<phi> \<ge> \<epsilon>\<close> and
  killing the non-orthogonal times with an exponential local martingale (3.18)
  under optional sampling at \<open>\<tau>\<^bsub>B\<^sub>\<epsilon>\<^esub> \<and> v(x)\<close>.  That needs stochastic integrals
  against the class member.  This development has none, and needed none.  The
  replacement is in two steps, both elementary.

  \<^item> \<^emph>\<open>Anti-concentration\<close> (@{thm [source] paper_v_touch_near_orth}).  Because
    the touching inequality is ALMOST SURE, one positive-probability
    fluctuation contradicts it --- no measure change.  At \<open>\<theta>' = \<tau>\<^bsub>B\<^sub>\<epsilon>\<^esub> \<and> t\<close> with
    \<open>t = \<beta>\<epsilon>\<^sup>2\<close>, \<open>\<beta> = 1/(2n\<^sup>2L)\<close>: the increment \<open>W = q \<bullet> (X\<^bsub>\<theta>'\<^esub> - x)\<close> is BOUNDED by
    \<open>\<bar>q\<bar>\<epsilon>\<close>, has mean \<open>0\<close> and variance \<open>q \<bullet> (E[Y\<^bsub>\<theta>'\<^esub>] *v q)\<close> EXACTLY
    (@{thm [source] paper_pair_class_stopped_var} --- the frozen-direction
    identity), while the touching forces \<open>W\<^sup>- \<le> t + C\<^sub>M\<epsilon>\<^sup>2/2\<close> a.s.  Boundedness
    replaces the fourth moment: an indicator split bounds \<open>E[W\<^sup>-]\<close> from above by
    \<open>\<bar>q\<bar>\<^sup>2\<epsilon>\<^sup>2\<close> times a tail probability, and from below by the variance, and
    Chebyshev on the exit (\<open>\<epsilon>\<^sup>2 P(\<tau> < t) \<le> trace E[Y] \<le> n\<^sup>2Lt\<close>) gives
    \<open>E[\<theta>'] \<ge> t/2\<close>.  For \<open>\<epsilon> < \<epsilon>K\<close> the two bounds collide.  So for EVERY
    \<open>\<epsilon>\<^sub>0 > 0\<close> there is \<open>b \<in> sconstraint k L\<close> with \<open>- trace (M ** b)/2 \<le> 1\<close> and
    \<open>q \<bullet> (b *v q) < \<epsilon>\<^sub>0\<close>.  Compactness of the constraint set then gives an
    exactly orthogonal \<open>b\<^sup>*\<close> (@{thm [source] paper_v_touch_orth}): the limit has
    \<open>q \<bullet> (b\<^sup>* *v q) = 0\<close>, hence \<open>b\<^sup>* *v q = 0\<close> by psd Cauchy--Schwarz
    (@{thm [source] psd_kernel_eq}).  \<^emph>\<open>No Doob, no fourth moments, no
    stochastic integration.\<close>

  \<^item> \<^emph>\<open>Capped spectral split\<close> (@{thm [source] sconstraint_orth_feasible}).  \<open>b\<^sup>*\<close>
    lives in the CONVEXIFIED set, not in the feasible set of (1.9).  The
    planned route through \<open>lemma_2_1_exact\<close> and a face of the psd cone was
    dropped: the generators of \<open>suff_volatile\<close> need not respect the eigenvalue
    CAP \<open>L\<close>.  What works instead is direct.  Diagonalise \<open>b\<^sup>*\<close>
    (@{thm [source] symmetric_eigenbasis}); cap the eigenvalues at \<open>1\<close>;
    @{thm [source] Pi_constraint_capped_trace} says the capped eigenvalues
    still sum to at least \<open>n - k\<close>; a threshold argument
    (@{thm [source] exists_min_subset}, @{thm [source] weighted_min_value})
    selects a subset \<open>S\<close> of eigendirections carrying that mass, and the
    witness is the projection \<open>P\<^sub>S\<close> plus a remainder of size \<open>\<le> L - 1\<close>, so its
    eigenvalues cap at \<open>1 + (L-1) = L\<close> exactly.  Orthogonality comes for free:
    \<open>b\<^sup>* *v q = 0\<close> puts \<open>q\<close> in the zero eigenspace, and every direction the
    witness uses has POSITIVE \<open>b\<^sup>*\<close>-eigenvalue, hence is orthogonal to \<open>q\<close>.

  \<^bold>\<open>PROVED --- the SUPERSOLUTION half, in the paper's own Definition
  3.1(b).\<close>  @{thm [source] paper_v_supersol_lsc}: the LOWER SEMICONTINUOUS
  ENVELOPE of \<open>enn2real \<circ> paper_v k L T K\<close> satisfies
  \<open>1 \<le> F\<^sup>*(\<nabla>\<phi>(x), \<nabla>\<^sup>2\<phi>(x))\<close> at every global touching over \<open>K\<close> from an
  interior point.  Two cases, split on the gradient.

  \<^item> \<^emph>\<open>Case 1, \<open>\<nabla>\<phi>(x) \<noteq> 0\<close>\<close>
    (@{thm [source] paper_v_supersol_contradiction_case1_lsc}): the skew
    trick.  A skew-symmetric diffusion field kills the Ito martingale term
    IDENTICALLY, so the touching inequality holds PATHWISE, which is what an
    essential infimum needs.  The process is built by Euler pasting of
    endpoint-frozen Gaussian kernels and a weak limit --- no stochastic
    integral and no SDE well-posedness.  This case consults the touching only
    on a ball, which is what lets Case 2 use it at perturbed points.

  \<^item> \<^emph>\<open>Case 2, \<open>\<nabla>\<phi>(x) = 0\<close>\<close> (@{thm [source] paper_v_case2}): a
    dichotomy, and NOT the paper's bump construction.  Applying
    @{thm [source] test_fun_quadratic_minorates} at level \<open>\<epsilon>/2\<close> and splitting
    \<open>H - (\<epsilon>/2)\<cdot>1 = (H - \<epsilon>\<cdot>1) + (\<epsilon>/2)\<cdot>1\<close> supplies, for free, all three
    properties the paper's \<open>\<phi>\<^sup>m\<close> was built for.  Tilting by \<open>\<eta>\<close> then either
    yields local minimisers with NONZERO gradient arbitrarily close to \<open>x\<close>
    --- Case 1 fires at each, and the gradients vanish in the limit because
    \<open>\<bar>y - x\<bar> \<le> 4\<bar>\<eta>\<bar>/\<epsilon>\<close> (@{thm [source] tilted_minimiser_close}) --- or the
    gradient vanishes at every one of them, and then
    @{thm [source] horn_B_locally_constant} makes \<open>v\<^sub>*\<close> locally constant,
    which @{thm [source] paper_v_not_locally_constant} refutes through the
    DPP and the deterministic-radius member.

  \<^bold>\<open>The one hypothesis, and why it is faithful.\<close>
  @{thm [source] paper_v_supersol_lsc} assumes the horizon never binds on the
  interior, \<open>v\<^sub>*(x) < T/2\<close>.  Only Case 2 needs it: Case 1 DERIVES it from the
  nonvanishing gradient (@{thm [source] touching_grad_lt_horizon_gen}).  It
  cannot be dropped, because where \<open>v \<equiv> T\<close> on an open set the supersolution
  inequality is genuinely FALSE --- a constant test function would demand
  \<open>1 \<le> F\<^sup>*(0,0) = 0\<close>.  The paper has no horizon at all, so \<open>T\<close> large enough to
  be inert IS the paper's setting; for a bounded \<open>K\<close> the hypothesis follows
  from @{thm [source] paper_v_le_ball_bound}.

  \<^bold>\<open>Why the supersolution is stated at the ENVELOPE and the subsolution is
  not.\<close>  The envelope-free notions of Relative\_Arbitrage\_PDE are the
  STRONGER ones, and for the subsolution the stronger one is available:
  \<open>ell_op k L 0 0 = 0 \<le> 1\<close>, so a constant test function at an interior local
  MAXIMUM costs nothing.  On the supersolution side the same test function at
  an interior local MINIMUM would demand \<open>1 \<le> ell_op k L 0 0 = 0\<close>, so
  @{const visc_supersol} rules out interior local minima outright and cannot
  hold for \<open>paper_v\<close>.  That asymmetry is exactly what Definition 3.1's
  envelopes exist to repair, and it is why this file proves the subsolution in
  the envelope-free form and the supersolution in the envelope form.\<close>

end
