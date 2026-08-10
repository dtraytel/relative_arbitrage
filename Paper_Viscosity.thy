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

text \<open>The relaxed viscosity predicates.  Because \<open>ell_op_s \<le> ell_op\<close>, the
  relaxed SUBsolution property is implied by the true one and the relaxed
  SUPERsolution property IMPLIES the true one --- so the half this development
  can reach probabilistically (the subsolution) is the half where the relaxed
  form is the weaker statement.  That asymmetry is the honest summary of where
  \<open>\<section>3\<close> stands here.\<close>

definition visc_subsol_s ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_subsol_s k L \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x) \<longrightarrow>
        ell_op_s k L H \<le> 1)"

definition visc_supersol_s ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n) set \<Rightarrow> (real^'n \<Rightarrow> real) \<Rightarrow> bool"
  where
  "visc_supersol_s k L \<Omega> u \<longleftrightarrow>
     (\<forall>x\<in>\<Omega>. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y) \<longrightarrow>
        1 \<le> ell_op_s k L H)"

lemma visc_supersol_s_imp_visc_supersol:
  fixes \<Omega> :: "(real^'n::finite) set"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and S: "visc_supersol_s k L \<Omega> u"
  shows "visc_supersol k L \<Omega> u"
  unfolding visc_supersol_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. u x - \<phi> x \<le> u y - \<phi> y"
  have "1 \<le> ell_op_s k L H"
    using S[unfolded visc_supersol_s_def] x tf lm by blast
  also have "\<dots> \<le> ell_op k L (g x) H" by (rule ell_op_s_le_ell_op[OF k L])
  finally show "1 \<le> ell_op k L (g x) H" .
qed

lemma visc_subsol_imp_visc_subsol_s:
  fixes \<Omega> :: "(real^'n::finite) set"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L"
    and S: "visc_subsol k L \<Omega> u"
  shows "visc_subsol_s k L \<Omega> u"
  unfolding visc_subsol_s_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> \<Omega>" and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>y \<in> ball x e. u y - \<phi> y \<le> u x - \<phi> x"
  have "ell_op_s k L H \<le> ell_op k L (g x) H" by (rule ell_op_s_le_ell_op[OF k L])
  also have "\<dots> \<le> 1" using S[unfolded visc_subsol_def] x tf lm by blast
  finally show "ell_op_s k L H \<le> 1" .
qed

section \<open>The analytic input, isolated\<close>

text \<open>Everything above is unconditional.  What the subsolution proof still
  needs from \<^const>\<open>paper_pair_class\<close> is ONE statement, and it is exactly
  Ito's formula applied to a test function along a class member:

  for a test function \<open>\<phi>\<close> touching \<^const>\<open>paper_v\<close> from above at \<open>x\<close>, the
  DPP bound of @{thm [source] paper_v_cond_ball} forces the second-order
  expansion of \<open>\<phi>\<close> against the member's covariation to beat \<open>-2\<close>, and the
  covariation direction is feasible because a class member's \<open>d\<langle>X\<rangle>\<close> lies in
  \<^const>\<open>sconstraint\<close> and is orthogonal to the gradient at the touching
  point.

  We name that output as a predicate rather than assume Ito itself, so the
  interface is the smallest possible: a supplier only has to produce the
  WITNESS.  This is the same discipline
  @{thm [source] paper_pair_class_aglue} was built with --- hypotheses first,
  suppliers later --- and it means the reduction below can be checked now.\<close>

definition class_expansion_witness ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> bool"
  where
  "class_expansion_witness k L T K \<longleftrightarrow>
     (\<forall>x \<in> interior K. \<forall>\<phi> g H. test_fun_at \<phi> g H x \<longrightarrow>
        (\<exists>e>0. \<forall>z \<in> ball x e.
           enn2real (paper_v k L T K z) - \<phi> z
             \<le> enn2real (paper_v k L T K x) - \<phi> x) \<longrightarrow>
        (\<exists>a \<in> feasible k L (g x). - trace (H ** a) / 2 \<le> 1))"

theorem paper_v_visc_subsol_of_witness:
  fixes K :: "(real^'n::finite) set"
  assumes W: "class_expansion_witness k L T K"
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
  from W[unfolded class_expansion_witness_def] x tf lm
  obtain a where a: "a \<in> feasible k L (g x)"
    and le: "- trace (H ** a) / 2 \<le> 1" by blast
  show "ell_op k L (g x) H \<le> 1" by (rule ell_op_le_one_of_witness[OF a le])
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
        using un_m by (intro sets.countable_INT) auto
      with eq show ?thesis by simp
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

lemma test_fun_quadratic_dominates:
  fixes \<phi> :: "real^'n::finite \<Rightarrow> real" and g :: "real^'n \<Rightarrow> real^'n"
    and H :: "real^'n^'n" and x :: "real^'n" and \<delta> :: real
  assumes tf: "test_fun_at \<phi> g H x" and d0: "0 < \<delta>"
  obtains r where "0 < r"
    and "\<And>z. z \<in> ball x r \<Longrightarrow>
      \<phi> z \<le> \<phi> x + g x \<bullet> (z - x) + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
proof -
  have symH: "transpose H = H"
    and dg: "(g has_derivative (\<lambda>h. H *v h)) (at x)"
    using tf unfolding test_fun_at_def by blast+
  obtain e where e0: "0 < e"
    and dphi: "\<And>y. y \<in> ball x e \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. g y \<bullet> h)) (at y)"
    using tf unfolding test_fun_at_def by blast
  have "\<forall>e>0. \<exists>d>0. \<forall>y. norm (y - x) < d \<longrightarrow>
      norm (g y - g x - (H *v (y - x))) \<le> e * norm (y - x)"
    using dg unfolding has_derivative_at_alt by blast
  moreover have "0 < \<delta> / 2" using d0 by simp
  ultimately obtain d where dd: "0 < d"
    and bnd: "\<And>y. norm (y - x) < d \<Longrightarrow>
        norm (g y - g x - (H *v (y - x))) \<le> (\<delta> / 2) * norm (y - x)"
    by blast
  define r where "r = min e d"
  have r0: "0 < r" using e0 dd by (simp add: r_def)
  have main: "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
      + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
    if z: "z \<in> ball x r" for z
  proof -
    define v where "v = z - x"
    have nv: "norm v < r"
      using z by (simp add: v_def mem_ball dist_norm norm_minus_commute)
    define A where "A = g x \<bullet> v"
    define B where "B = v \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v v)"
    define f where "f t = \<phi> (x + t *\<^sub>R v) - (\<phi> x + t * A + t\<^sup>2 * B / 2)" for t
    have f0: "f 0 = 0" by (simp add: f_def)
    have deriv: "\<exists>y. (f has_field_derivative y) (at t) \<and> y \<le> 0"
      if t: "0 \<le> t" "t \<le> 1" for t
    proof -
      have ntv: "norm (t *\<^sub>R v) \<le> norm v"
        using t by (simp add: mult_left_le_one_le)
      have mem: "x + t *\<^sub>R v \<in> ball x e"
        using ntv nv by (simp add: mem_ball dist_norm r_def)
      have d1: "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_field_derivative
          g (x + t *\<^sub>R v) \<bullet> v) (at t)"
      proof -
        have i1: "((\<lambda>t :: real. x + t *\<^sub>R v) has_derivative (\<lambda>h. h *\<^sub>R v)) (at t)"
          by (auto intro!: derivative_eq_intros)
        have i2: "(\<phi> has_derivative (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> h)) (at (x + t *\<^sub>R v))"
          by (rule dphi[OF mem])
        have "((\<lambda>t. \<phi> (x + t *\<^sub>R v)) has_derivative
            (\<lambda>h. g (x + t *\<^sub>R v) \<bullet> (h *\<^sub>R v))) (at t)"
          using diff_chain_at[OF i1 i2] by (simp add: o_def)
        then show ?thesis
          by (rule has_derivative_imp_has_field_derivative)
            (simp add: inner_scaleR_right ac_simps)
      qed
      have d2: "((\<lambda>t. \<phi> x + t * A + t\<^sup>2 * B / 2) has_field_derivative
          A + t * B) (at t)"
        by (auto intro!: derivative_eq_intros)
      have df: "(f has_field_derivative
          (g (x + t *\<^sub>R v) \<bullet> v - (A + t * B))) (at t)"
        unfolding f_def by (rule DERIV_diff[OF d1 d2])
      have expand: "g (x + t *\<^sub>R v) \<bullet> v - (A + t * B)
          = (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v - t * (\<delta> * (v \<bullet> v))"
      proof -
        have m1: "(H + \<delta> *\<^sub>R mat 1) *v v = H *v v + \<delta> *\<^sub>R v"
          by (simp add: matrix_vector_mult_add_rdistrib scaleR_matrix_vector
              matrix_vector_mul_lid)
        have m2: "H *v (t *\<^sub>R v) = t *\<^sub>R (H *v v)"
          by (simp add: matrix_vector_mult_scaleR)
        show ?thesis
          unfolding A_def B_def m1 m2
          by (simp add: inner_diff_left inner_add_right inner_scaleR_left
              inner_scaleR_right inner_commute algebra_simps)
      qed
      have small: "(g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v
          \<le> (\<delta> / 2) * (t * norm v) * norm v"
      proof -
        have "norm (t *\<^sub>R v) < d"
          using ntv nv by (simp add: r_def)
        moreover have "(x + t *\<^sub>R v) - x = t *\<^sub>R v" by simp
        ultimately have nb: "norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v)))
            \<le> (\<delta> / 2) * norm (t *\<^sub>R v)"
          using bnd[of "x + t *\<^sub>R v"] by simp
        have "(g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) \<bullet> v
            \<le> norm (g (x + t *\<^sub>R v) - g x - (H *v (t *\<^sub>R v))) * norm v"
          by (rule norm_cauchy_schwarz)
        also have "\<dots> \<le> ((\<delta> / 2) * norm (t *\<^sub>R v)) * norm v"
          by (rule mult_right_mono[OF nb norm_ge_zero])
        also have "\<dots> = (\<delta> / 2) * (t * norm v) * norm v"
          using t by (simp add: abs_of_nonneg)
        finally show ?thesis .
      qed
      have vv: "v \<bullet> v = norm v * norm v"
        by (simp add: dot_square_norm power2_eq_square)
      have "g (x + t *\<^sub>R v) \<bullet> v - (A + t * B)
          \<le> (\<delta> / 2) * (t * norm v) * norm v - t * (\<delta> * (norm v * norm v))"
        unfolding expand vv by (rule diff_right_mono[OF small])
      also have "\<dots> = - (\<delta> / 2) * t * (norm v * norm v)"
        by (simp add: field_simps)
      also have "\<dots> \<le> 0"
        using d0 t by (simp add: mult_nonneg_nonneg)
      finally show ?thesis using df by blast
    qed
    have "f 1 \<le> f 0"
      by (rule DERIV_nonpos_imp_nonincreasing[of 0 1 f])
        (use deriv in auto)
    then have "\<phi> (x + 1 *\<^sub>R v) \<le> \<phi> x + 1 * A + 1\<^sup>2 * B / 2"
      using f0 by (simp add: f_def)
    then show ?thesis by (simp add: v_def A_def B_def)
  qed
  show ?thesis by (rule that[OF r0 main])
qed

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

section \<open>Gap 1 closed: the relaxed subsolution property of \<open>paper_v\<close>\<close>

theorem paper_v_visc_subsol_s:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
  shows "visc_subsol_s k L (interior K) (\<lambda>z. enn2real (paper_v k L T K z))"
  unfolding visc_subsol_s_def
proof (intro ballI allI impI)
  fix x :: "real^'n" and \<phi> :: "real^'n \<Rightarrow> real"
    and g :: "real^'n \<Rightarrow> real^'n" and H :: "real^'n^'n"
  assume x: "x \<in> interior K"
    and tf: "test_fun_at \<phi> g H x"
    and lm: "\<exists>e>0. \<forall>z \<in> ball x e.
        enn2real (paper_v k L T K z) - \<phi> z
          \<le> enn2real (paper_v k L T K x) - \<phi> x"
  have L0: "0 \<le> L" using L1 by simp
  define u where "u = (\<lambda>z :: real^'n. enn2real (paper_v k L T K z))"
  from lm obtain e0 where e00: "0 < e0"
    and lme: "\<And>z. z \<in> ball x e0 \<Longrightarrow> u z - \<phi> z \<le> u x - \<phi> x"
    unfolding u_def by blast
  define C where "C = real CARD('n) * (real CARD('n) * L)"
  have n0: "0 < real CARD('n)"
    using zero_less_card_finite[where 'a = 'n] by simp
  have C0: "0 < C"
    unfolding C_def by (intro mult_pos_pos n0) (use L1 in linarith)
  have key: "ell_op_s k L H \<le> 1 + \<delta> * C / 2" if d0: "0 < \<delta>" for \<delta>
  proof -
    obtain r where r0: "0 < r"
      and dom: "\<And>z. z \<in> ball x r \<Longrightarrow>
          \<phi> z \<le> \<phi> x + g x \<bullet> (z - x) + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      using test_fun_quadratic_dominates[OF tf d0] by blast
    define \<epsilon> where "\<epsilon> = min e0 r / 2"
    have eps0: "0 < \<epsilon>" using e00 r0 by (simp add: \<epsilon>_def)
    have touch: "u z \<le> u x + g x \<bullet> (z - x)
        + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      if z: "dist z x \<le> \<epsilon>" for z
    proof -
      have zin: "z \<in> ball x e0 \<inter> ball x r"
        using z e00 r0 by (auto simp: \<epsilon>_def mem_ball dist_commute)
      have "u z - \<phi> z \<le> u x - \<phi> x" using lme zin by blast
      moreover have "\<phi> z \<le> \<phi> x + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
        using dom zin by blast
      ultimately show ?thesis by linarith
    qed
    have touch': "\<And>z. dist z x \<le> \<epsilon> \<Longrightarrow> enn2real (paper_v k L T K z)
        \<le> enn2real (paper_v k L T K x) + g x \<bullet> (z - x)
          + ((z - x) \<bullet> ((H + \<delta> *\<^sub>R mat 1) *v (z - x))) / 2"
      using touch[unfolded u_def] by simp
    obtain b where bmem: "b \<in> sconstraint k L"
      and w: "- trace ((H + \<delta> *\<^sub>R mat 1) ** b) / 2 \<le> 1"
      using paper_v_subsol_quadratic_ball[OF T L1 Kc eps0 touch'] by blast
    have split: "trace ((H + \<delta> *\<^sub>R mat 1) ** b) = trace (H ** b) + \<delta> * trace b"
    proof -
      have "(H + \<delta> *\<^sub>R mat 1) ** b = H ** b + (\<delta> *\<^sub>R mat 1) ** b"
        by (rule matrix_add_rdistrib)
      moreover have "(\<delta> *\<^sub>R mat 1) ** b = \<delta> *\<^sub>R b"
        by (simp add: scaleR_matrix_mult matrix_mul_lid)
      ultimately have e1: "trace ((H + \<delta> *\<^sub>R mat 1) ** b)
          = trace (H ** b + \<delta> *\<^sub>R b)" by simp
      have e2: "trace (H ** b + \<delta> *\<^sub>R b) = trace (H ** b) + trace (\<delta> *\<^sub>R b)"
        by (simp add: trace_def sum.distrib vector_add_component)
      have e3: "trace (\<delta> *\<^sub>R b) = \<delta> * trace b" by (rule trace_scaleR)
      from e1 e2 e3 show ?thesis by simp
    qed
    have trb: "trace b \<le> C"
      unfolding C_def by (rule sconstraint_trace_le[OF L0 bmem])
    have "- trace (H ** b) / 2 \<le> 1 + \<delta> * trace b / 2"
      using w split by (simp add: field_simps)
    also have "\<dots> \<le> 1 + \<delta> * C / 2"
      using trb d0 by (simp add: mult_left_mono)
    finally have wb: "- trace (H ** b) / 2 \<le> 1 + \<delta> * C / 2" .
    show ?thesis by (rule ell_op_s_le_of_witness[OF L0 bmem wb])
  qed
  show "ell_op_s k L H \<le> 1"
  proof (rule field_le_epsilon)
    fix e :: real assume e0: "0 < e"
    have d0: "0 < 2 * e / C" using e0 C0 by simp
    have "ell_op_s k L H \<le> 1 + (2 * e / C) * C / 2"
      by (rule key[OF d0])
    also have "\<dots> = 1 + e" using C0 by (simp add: field_simps)
    finally show "ell_op_s k L H \<le> 1 + e" .
  qed
qed

section \<open>What remains for clause (2)\<close>

text \<open>What is PROVED here, unconditionally:

  \<^item> @{thm [source] paper_pair_class_quadratic_mean} --- the exact expansion of
    a quadratic test function along any class member, from the two martingale
    clauses alone.  This is the substitute for Ito's formula, and it is not an
    approximation: for a quadratic the expansion has no remainder.

  \<^item> @{thm [source] paper_v_subsol_quadratic_global} --- the subsolution
    inequality \<open>ell_op_s k L M \<le> 1\<close> at a GLOBALLY touching quadratic.

  Two gaps separate that from \<open>visc_subsol\<close>, and both are named rather than
  hidden.  Neither is a gap in the argument; each is a gap in what the class,
  used through expectations, can say.

  \<^bold>\<open>Gap 1: localisation.\<close>  \<^const>\<open>visc_subsol\<close> gives a LOCAL touching, on some
  \<open>ball x e\<close>.  Two routes were checked and BOTH FAIL; do not retry them.

  \<^item> \<^emph>\<open>Penalisation.\<close>  Replacing \<open>\<phi>\<close> by \<open>\<phi> + A\<sqdot>\<bar>\<sqdot>-x\<bar>\<^sup>2\<close> does turn a local
    touching into a global one for \<open>A\<close> large, because \<^const>\<open>paper_v\<close> is
    bounded by \<open>T\<close> (@{thm [source] paper_v_le_T}) and the penalty dominates the
    quadratic off the ball.  But the Hessian becomes \<open>M + 2A\<sqdot>1\<close>, and
    \<open>- trace ((M + 2A\<sqdot>1) ** b) / 2 = - trace (M ** b)/2 - A \<sqdot> trace b\<close> with
    \<open>trace b \<ge> n - k > 0\<close> (@{thm [source] sconstraint_trace_ge}).  So the
    conclusion is \<open>- trace (M ** b)/2 \<le> 1 + A \<sqdot> trace b\<close>: strictly WEAKER, and
    worse the larger \<open>A\<close> gets.  Quadratic test functions cannot be localised by
    penalisation.

  \<^item> \<^emph>\<open>An error estimate.\<close>  Split the integral at \<open>{X\<^sub>h \<in> ball x e}\<close>.  The bad
    event has \<open>P \<le> E\<bar>X\<^sub>h-x\<bar>\<^sup>2/e\<^sup>2 = trace (E Y\<^sub>h)/e\<^sup>2 \<le> n L h/e\<^sup>2\<close>, and
    Cauchy--Schwarz against a fourth moment controls the QUADRATIC part of the
    error by \<open>O(h\<^sup>3\<^sup>/\<^sup>2) = o(h)\<close>, which would be fine.  The LINEAR part
    \<open>p \<bullet> (X\<^sub>h - x)\<close> does not: it is bounded only by
    \<open>\<bar>p\<bar>\<sqdot>\<surd>P(bad)\<sqdot>\<surd>(E\<bar>X\<^sub>h-x\<bar>\<^sup>2) = O(h)/e\<close> --- the SAME order as the term it is
    compared against.  The estimate yields \<open>trace (M ** b) \<ge> - 2 - C\<bar>p\<bar>nL/e\<close>
    and does not close as \<open>h \<rightarrow> 0\<close>.

  What WOULD work is STOCHASTIC localisation: stop at \<open>\<tau>\<^bsub>B\<^sub>e\<^bsub>(x)\<^esub>\<^esub> \<and> h\<close> and apply
  optional sampling to clauses (iii) and (iv), so that the path never leaves
  the ball and the touching hypothesis applies unconditionally.
  \<open>Optional_Sampling\<close> and @{thm [source] path_stopping_time_event_filtration}
  are the tools.  The blocker is the recorded one:
  \<^const>\<open>path_stopping_time\<close>'s congruence clause quantifies over ALL functions,
  while @{thm [source] pball_exit_cong} delivers it only along CONTINUOUS
  paths, and @{thm [source] pexit_mem_of_less_T} shows that restriction is
  forced --- attainment of the infimum genuinely fails off the path space.
  Weakening \<^const>\<open>path_stopping_time\<close> inside \<open>Paper_DPP\<close> is mechanical but not
  small: the congruence is consumed only through
  @{thm [source] path_stopping_time_cong}, at four sites, but each is stated
  for all \<open>\<omega>\<close> and the continuity hypothesis would have to be threaded through
  the downstream \<open>pstopped_law_*\<close> and \<open>path_stopping_time_*\<close> layer.

  \<^bold>\<open>Gap 2: orthogonality.\<close>  Eq. (1.9) takes its infimum over
  \<^const>\<open>feasible\<close>, which requires \<open>a *v p = 0\<close>; the class of (1.7) constrains
  its covariation to \<^const>\<open>sconstraint\<close>, which says nothing of the kind.  So a
  probabilistic argument over the class produces a witness in
  \<^const>\<open>sconstraint\<close> and \<^const>\<open>ell_op_s\<close>, never \<^const>\<open>ell_op\<close>.  In the
  paper the orthogonality comes from OPTIMALITY of the direction --- along an
  optimizer of a minimal-time problem \<open>v(X\<^sub>t) + t\<close> cannot carry a nonzero
  martingale part, which forces \<open>a Dv = 0\<close>.  That is an almost-sure RIGIDITY
  statement about the optimizer, not a statement about means, so it is not
  reachable by the route of this section.
  \<^const>\<open>class_expansion_witness\<close> is the interface for it: a supplier
  has only to produce the feasible witness.

  What the constraint DOES is now precise, and proved:
  @{thm [source] paper_pair_class_frozen_direction} says a direction
  annihilated by the averaged covariation is frozen almost surely.  So for a
  quadratic test function with gradient \<open>q\<close> at \<open>x\<close>, feasibility of the
  covariation direction makes the first-order term \<open>q \<bullet> (X\<^sub>t - x)\<close> vanish
  IDENTICALLY, leaving a purely second-order increment.  That is the device
  that makes an essential infimum and a mean agree to first order --- which is
  exactly what the supersolution half is short of, and exactly why the
  constraint sits in Eq. (1.9) rather than in (1.7).

  \<^bold>\<open>The supersolution half.\<close>  Unchanged, and structurally harder.  It consumes
  @{thm [source] paper_v_dpp_sup_ge_time} plus a weak solution of the SDE
  (3.24), and the DPP bound it needs is a LOWER bound on an essential infimum.
  No mean gives one --- that is exactly why the expectation route of this
  section proves the subsolution half and cannot touch the supersolution half.
  The paper's device is the exponential local martingale with optional sampling
  ((3.18)--(3.19)).  One simplification is available here and is worth using:
  by @{thm [source] visc_supersol_s_imp_visc_supersol} the RELAXED supersolution
  property already implies the true one, so that half may be attacked entirely
  in \<^const>\<open>ell_op_s\<close>, where the class's own \<^const>\<open>sconstraint\<close> is the right
  index set and Gap 2 does not arise at all.\<close>

end
