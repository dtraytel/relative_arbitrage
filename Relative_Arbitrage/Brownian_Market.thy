section \<open>The Brownian market\<close>

(*<*)
theory Brownian_Market
  imports "Wiener_Measure.Continuous_Brownian_Motion" Volatile_Market
begin

(*>*)

text \<open>The continuous vector Brownian motion of
  @{theory Wiener_Measure.Continuous_Brownian_Motion}, read as a market: with the
  identity covariation it satisfies every assumption of
  \<open>sufficiently_volatile_market\<close>, which is what makes the class of
  Eq. (1.7) and the locale of \<open>Volatile_Market\<close> non-vacuous.\<close>

theorem Brownian_market_sufficiently_volatile:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and c: "0 \<le> c"
    and K: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> cbmX x0 s \<omega> \<in> K"
  shows "sufficiently_volatile_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
    (\<lambda>_ _. mat 1) k L K x0 (\<lambda>_. c)"
proof (intro sufficiently_volatile_market.intro
    sufficiently_volatile_market_axioms.intro)
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0 (cbmX x0)"
    by (rule martingale_cbmX)
  show "prob_space ?M" by simp
  show "1 \<le> k" "k < CARD('n)" "1 \<le> L" by fact+
  show "AE \<omega> in ?M. cbmX x0 0 \<omega> = x0"
  proof -
    have "AE \<omega> in ?M. cbmX x0 0 \<omega> = bmX x0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    with bmX_start[of x0] show ?thesis
      by eventually_elim simp
  qed
  show "AE \<omega> in ?M. 0 \<le> c" using c by simp
  show "(\<lambda>_. c) \<in> borel_measurable ?M" by simp
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> cbmX x0 s \<omega> \<in> K"
    by (rule K)
  have psd1: "psd (mat 1 :: real^'n^'n)"
    by (simp add: psd_def)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> psd (mat 1 :: real^'n^'n)"
    using psd1 by simp
  have elb: "eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ UNIV] conjI)
    show "subspace (UNIV :: (real^'n) set)" by simp
    show "CARD('n) - k \<le> dim (UNIV :: (real^'n) set)" by simp
    show "\<forall>x\<in>(UNIV :: (real^'n) set). x \<bullet> x \<le> x \<bullet> (mat 1 *v x)"
      by simp
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    using elb by simp
  have eub: "eigen_ub (mat 1 :: real^'n^'n) L"
  proof -
    have "x \<bullet> x \<le> L * (x \<bullet> x)" for x :: "real^'n"
      using mult_right_mono[OF L inner_ge_zero] by simp
    then show ?thesis
      by (simp add: eigen_ub_def)
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_ub (mat 1 :: real^'n^'n) L"
    using eub by simp
  have ti: "set_integrable lborel {0..t}
      (\<lambda>s. trace (mat 1 :: real^'n^'n))" for t :: real
  proof -
    have "integrable lborel
        (\<lambda>s. indicator {0..t} s *\<^sub>R trace (mat 1 :: real^'n^'n))"
    proof (intro integrable_scaleR_left integrable_real_indicator)
      show "{0..t} \<in> sets lborel"
        unfolding sets_lborel
        by (intro borel_closed closed_atLeastAtMost)
      show "emeasure lborel {0..t} < \<infinity>"
        by (simp add: emeasure_lborel_Icc_eq)
    qed
    then show ?thesis
      unfolding set_integrable_def .
  qed
  show "AE \<omega> in ?M. set_borel_measurable lborel {0..}
      (\<lambda>s :: real. mat 1 :: real^'n^'n)"
    unfolding set_borel_measurable_def by (intro AE_I2) simp
  show "AE \<omega> in ?M. \<forall>t :: real. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
    using ti by (intro AE_I2) blast
  have sq_ae: "AE \<omega> in ?M. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>
      = bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>" if t: "0 \<le> t" for t
  proof -
    have "AE \<omega> in ?M. cbmX x0 (min t c) \<omega> = bmX x0 (min t c) \<omega>"
      using t c by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  have sq_meas_b: "(\<lambda>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>)
      \<in> borel_measurable ?M" if t: "0 \<le> t" for t
    using t c by (intro borel_measurable_inner measurable_bmX) simp_all
  have sq_meas_c: "(\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)
      \<in> borel_measurable ?M" for t
    by (intro borel_measurable_inner measurable_cbmX)
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)"
  proof -
    fix t :: real assume t: "0 \<le> t"
    have u: "0 \<le> min t c" using t c by simp
    show "integrable ?M (\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)"
      using integrable_cong_AE[OF sq_meas_c sq_meas_b[OF t] sq_ae[OF t]]
        bmX_sq_integrable[OF u] by simp
  qed
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (rule BMP.integrable_const)
  show "(\<integral>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega> \<partial>?M)
      - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t c}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)) \<partial>?M) = x0 \<bullet> x0"
    if t: "0 \<le> t" for t
  proof -
    have u: "0 \<le> min t c" using t c by simp
    have 0: "(\<integral>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega> \<partial>?M)
        = (\<integral>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega> \<partial>?M)"
      by (rule integral_cong_AE[OF sq_meas_c sq_meas_b[OF t] sq_ae[OF t]])
    have 1: "(\<integral>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega> \<partial>?M)
        = x0 \<bullet> x0 + real CARD('n) * min t c"
      by (rule bmX_sq_integral[OF u])
    have 2: "set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)) = real CARD('n) * min t c"
      by (rule bm_compensator_const[OF u])
    show ?thesis
      unfolding 0 1 2 by (simp add: BMP.prob_space)
  qed
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0
      (coord_Z (cbmX x0) (\<lambda>_ _. mat 1) i)" for i
    unfolding coord_Z_def by (rule martingale_cbm_coord_square)
  text \<open>A constant horizon is a stopping time for free: the event is the whole
    space or empty, and both lie in every sub-\<open>\<sigma>\<close>-algebra.\<close>
  show "\<And>s. 0 \<le> s \<Longrightarrow>
      {\<omega> \<in> space ?M. c \<le> s} \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
  proof -
    fix s :: real assume s: "0 \<le> s"
    show "{\<omega> \<in> space ?M. c \<le> s}
        \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
    proof (cases "c \<le> s")
      case True
      have "{\<omega> \<in> space ?M. c \<le> s}
          = space (natural_filtration ?M 0 (cbmX x0) s)"
        using True by simp
      moreover have "space (natural_filtration ?M 0 (cbmX x0) s)
          \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
        by (rule sets.top)
      ultimately show ?thesis by simp
    next
      case False
      have "{\<omega> \<in> space ?M. c \<le> s} = {}" using False by simp
      moreover have "{} \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
        by (rule sets.empty_sets)
      ultimately show ?thesis by metis
    qed
  qed
  show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. cbmX x0 s \<omega>)"
    by (rule cbmX_cont)
qed

section \<open>A concrete instance: the class \<open>\<P>\<^sub>x\<close> is inhabited\<close>

text \<open>Specialising the theorem above to the planar market with
  \<open>k = L = 1\<close>, horizon \<open>1\<close> and start \<open>0\<close> discharges all its side
  conditions numerically, so the following statement has no hypotheses
  whatsoever: the axiomatised market class of
  @{theory Relative_Arbitrage.Volatile_Market} is non-vacuous.\<close>

theorem sufficiently_volatile_market_nonvacuous:
  "sufficiently_volatile_market
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX 0)) (cbmX (0 :: real^2))
    (\<lambda>_ _. mat 1) 1 1 UNIV 0 (\<lambda>_. 1)"
  by (rule Brownian_market_sufficiently_volatile) simp_all

interpretation BM2: sufficiently_volatile_market
    "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
    "natural_filtration bm_paths 0 (cbmX 0)" "cbmX (0 :: real^2)"
    "\<lambda>_ _. mat 1" 1 1 UNIV 0 "\<lambda>_. 1"
  by (rule sufficiently_volatile_market_nonvacuous)

text \<open>With the interpretation in place, the locale's martingale-problem
  identity --- an \<^emph>\<open>assumption\<close> there, here a proved consequence ---
  gives an unconditional fact: planar Brownian motion started at the
  origin has expected squared norm \<open>2\<close> at time \<open>1\<close>.\<close>

text \<open>The exit-time bound \<open>E[\<tau>] \<le> v(x0)\<close> of Example 3.1 is available
  as \<open>expected_exit_time_bound\<close>; a non-degenerate instance with
  \<open>K = cball 0 r\<close> needs the ball's first exit time, a genuine stopping
  time of the continuous modification.\<close>

section \<open>The process form of the martingale problem is inhabited\<close>

text \<open>Ito's formula for the test function \<open>|x|\<^sup>2\<close> is a theorem for the
  continuous Brownian motion (\<open>martingale_cbmX_square\<close>), and for
  \<open>acov = mat 1\<close> the process it is about is literally \<open>ito_Z\<close>.  Hence the
  continuous Brownian market with a deterministic horizon inhabits
  \<open>ito_const_horizon_market\<close>: every assumption of that locale is proved
  for this instance, so the exit-time bound of Lemma 2.1 follows from the
  martingale problem in process form with nothing assumed.\<close>

text \<open>Specialised to the planar market with \<open>k = L = 1\<close>, horizon \<open>1\<close> and
  start \<open>0\<close>, the statement has no hypotheses at all.\<close>

(*<*)
end
(*>*)
