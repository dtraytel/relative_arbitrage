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
