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

lemma matvec_scaleR_right: "M *v (c *\<^sub>R x) = c *\<^sub>R (M *v x)"
  by (simp add: matrix_vector_mult_def vec_eq_iff vector_scaleR_component
      sum_distrib_left algebra_simps)

lemma matvec_add_right: "M *v (x + y) = M *v x + M *v y"
  by (simp add: matrix_vector_mult_def vec_eq_iff vector_add_component
      sum.distrib algebra_simps)

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
      by (simp add: matvec_scaleR_right inner_scaleR_left
          inner_scaleR_right lam_nn[OF u])
    have wsplit: "w u = su + d u" unfolding su_def by (rule wu[OF u])
    have expand: "w u \<bullet> (M *v w u) - su \<bullet> (M *v su)
        = d u \<bullet> (M *v w u) + su \<bullet> (M *v d u)"
    proof -
      have "w u \<bullet> (M *v w u) = su \<bullet> (M *v w u) + d u \<bullet> (M *v w u)"
        by (subst (1) wsplit) (simp add: inner_add_left)
      moreover have "su \<bullet> (M *v w u)
          = su \<bullet> (M *v su) + su \<bullet> (M *v d u)"
        by (subst wsplit) (simp add: matvec_add_right inner_add_right)
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
      unfolding w_def grad_def by (rule matvec_add_right)
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

section \<open>What remains for clause (2)\<close>

text \<open>Where clause (2) stands after this file.

  \<^bold>\<open>PROVED --- the SUBSOLUTION half, with the operator of Eq. (1.9) itself.\<close>
  @{thm [source] paper_v_visc_subsol}: for every \<open>0 < T\<close>, \<open>1 \<le> L\<close>, closed \<open>K\<close>
  and \<open>k < CARD('n)\<close>, \<open>enn2real \<circ> paper_v k L T K\<close> is a viscosity subsolution
  on \<open>interior K\<close>.  The relaxed form @{thm [source] paper_v_visc_subsol_s},
  over \<open>ell_op_s\<close>, is the intermediate result and is kept: the supersolution
  half should be attacked there (see below).

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

  \<^bold>\<open>What is LEFT of clause (2): the supersolution half only.\<close>  It consumes
  @{thm [source] paper_v_dpp_sup_ge_time} (proved) plus a weak solution of the
  SDE (3.24), which this development does not have.  Work in \<open>ell_op_s\<close>
  throughout: by @{thm [source] visc_supersol_s_imp_visc_supersol} the relaxed
  supersolution property implies the true one, so Gap 2 does not arise on that
  side at all --- and Gap 1's localisation machinery
  (@{thm [source] pball_exit_path_stopping_time} and the stopped moments)
  transfers verbatim.\<close>


end
