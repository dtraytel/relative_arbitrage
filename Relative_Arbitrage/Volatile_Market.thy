

(*<*)
theory Volatile_Market
  imports
    Curvature_Operator
    "HOL-Probability.Probability"
    "Martingales.Martingale"
begin

(*>*)

text \<open>
  Formalizes the probabilistic side of J.-H. Lai, M. Shkolnikov and
  H. M. Soner, Relative arbitrage problem under eigenvalue lower bounds
  (arXiv:2512.17702): Definition 1.1, relative arbitrage, for an
  abstract relative value process \<open>V\<close>, and the locale
  \<open>sufficiently_volatile_market\<close> capturing the class of measures
  \<open>P \<in> P\<^sub>x\<close> of Section 1. In this locale \<open>X\<close> is a continuous-time
  martingale started at \<open>x0\<close>, staying in the compact set \<open>K\<close> up to a
  pre-exit time \<open>tau\<close>, whose instantaneous covariation \<open>acov\<close>
  satisfies the eigenvalue constraints of Eqs. (1.4)-(1.5) via the
  Courant-Fischer characterizations \<open>eigen_lb\<close> and \<open>eigen_ub\<close> of
  \<open>Curvature_Operator\<close>; the dynamics are specified in
  martingale-problem form through Dynkin's formula for the quadratic
  test function \<open>y \<mapsto> y \<bullet> y\<close> at stopped times, the locale assumption
  \<open>dynkin_quadratic\<close>. It proves the quantitative content of Example 3.1
  on the probabilistic side: in every sufficiently volatile market on
  \<open>K \<subseteq> cball 0 r\<close>, the expected stopped pre-exit time is bounded by
  \<open>v(x0) = (r\<^sup>2 - \<bar>x0\<bar>\<^sup>2) / (n - k)\<close>, the value function of Theorem 1.1.\<close>
section \<open>Relative arbitrage (Definition 1.1)\<close>

text \<open>
  \<open>V t \<omega>\<close> is the value of a trading strategy relative to the market at time
  \<open>t\<close>.  Definition 1.1 of the paper: \<open>V \<ge> 0\<close>, \<open>V T \<ge> V 0\<close> a.s., and
  \<open>V T > V 0\<close> with positive probability; the last condition is expressed
  as \<open>\<not> (AE \<omega>. V T \<omega> \<le> V 0 \<omega>)\<close>, which is equivalent for measurable \<open>V\<close>.
\<close>

definition relative_arbitrage :: "'a measure \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where
  "relative_arbitrage M V T \<longleftrightarrow>
     (\<forall>t\<in>{0..T}. AE \<omega> in M. 0 \<le> V t \<omega>) \<and>
     (AE \<omega> in M. V 0 \<omega> \<le> V T \<omega>) \<and>
     \<not> (AE \<omega> in M. V T \<omega> \<le> V 0 \<omega>)"

lemma (in prob_space) relative_arbitrage_prob_pos:
  assumes ra: "relative_arbitrage M V T"
    and meas: "(\<lambda>\<omega>. V T \<omega> - V 0 \<omega>) \<in> borel_measurable M"
  shows "0 < prob {\<omega> \<in> space M. V 0 \<omega> < V T \<omega>}"
proof -
  have set_eq: "{\<omega> \<in> space M. V 0 \<omega> < V T \<omega>}
      = {\<omega> \<in> space M. 0 < V T \<omega> - V 0 \<omega>}"
    by auto
  have setm: "{\<omega> \<in> space M. V 0 \<omega> < V T \<omega>} \<in> sets M"
    unfolding set_eq using meas by measurable
  have nae: "\<not> (AE \<omega> in M. V T \<omega> \<le> V 0 \<omega>)"
    using ra by (simp add: relative_arbitrage_def)
  have "emeasure M {\<omega> \<in> space M. V 0 \<omega> < V T \<omega>} \<noteq> 0"
  proof
    assume "emeasure M {\<omega> \<in> space M. V 0 \<omega> < V T \<omega>} = 0"
    then have "AE \<omega> in M. \<not> (V 0 \<omega> < V T \<omega>)"
      using AE_iff_measurable[OF setm] by auto
    then have "AE \<omega> in M. V T \<omega> \<le> V 0 \<omega>"
      by (simp add: not_less)
    with nae show False ..
  qed
  then show ?thesis
    using setm by (simp add: emeasure_eq_measure zero_less_measure_iff)
qed

section \<open>Sufficiently volatile markets: the class \<open>\<P>\<^sub>x\<close> in martingale-problem form\<close>

text \<open>The compensated square of a single coordinate.  The trace analogue is
  \<open>Ito_Market.ito_Z\<close>, but the trace version alone -- the weak form
  \<open>dynkin_quadratic\<close>, saying only that an expectation is constant in \<open>t\<close> -- is
  strictly weaker than the paper's class (1.7), a martingale problem in which
  \<open>X\<close> and \<open>X X\<^sup>T - \<int>a\<close> are both martingales.  Lemma 2.2's tightness chain
  needs a fourth-moment bound coordinate by coordinate, which a trace
  identity alone does not give; hence \<open>coord_Z_martingale\<close> below.\<close>

definition coord_Z ::
  "(real \<Rightarrow> 'a \<Rightarrow> real^'n::finite) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real^'n^'n)
     \<Rightarrow> 'n \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  where
  "coord_Z X acov i t \<omega> = (X t \<omega> $ i)\<^sup>2
     - set_lebesgue_integral lborel {0..t} (\<lambda>s. acov s \<omega> $ i $ i)"

locale sufficiently_volatile_market =
  martingale M F 0 X
  for M :: "'a measure"
    and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  fixes acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
    and k :: nat and L :: real
    and K :: "(real^'n) set"
    and x0 :: "real^'n"
    and tau :: "'a \<Rightarrow> real"
  assumes prob_space_M: "prob_space M"
    and k_lb: "1 \<le> k" and k_ub: "k < CARD('n)" and L_ge: "1 \<le> L"
    and X_start: "AE \<omega> in M. X 0 \<omega> = x0"
    and tau_nonneg: "AE \<omega> in M. 0 \<le> tau \<omega>"
    and tau_meas: "tau \<in> borel_measurable M"
    and X_in_K: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
    and acov_psd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
    and acov_eigen_lb:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
         eigen_lb (acov s \<omega>) (CARD('n) - k)"
    and acov_eigen_ub:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
    and acov_time_measurable:
      "AE \<omega> in M. set_borel_measurable lborel {0..} (\<lambda>s. acov s \<omega>)"
    and acov_trace_integrable:
      "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
         set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
    and stopped_sq_integrable:
      "\<And>t. 0 \<le> t \<Longrightarrow>
         integrable M (\<lambda>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega>)"
    and compensator_integrable:
      "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
         (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                (\<lambda>s. trace (acov s \<omega>)))"
    and dynkin_quadratic:
      "\<And>t. 0 \<le> t \<Longrightarrow>
         (\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M)
           - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                    (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
         = x0 \<bullet> x0"

    and coord_Z_martingale: "\<And>i. martingale M F 0 (coord_Z X acov i)"
    and tau_stopping: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and X_paths_cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"

sublocale sufficiently_volatile_market \<subseteq> prob_space M
  by (rule prob_space_M)

context sufficiently_volatile_market
begin

lemma c_pos: "0 < real (CARD('n) - k)"
  using k_ub by simp

text \<open>The pointwise trace bound from the eigenvalue constraint (Lemma 2.1 /
  Ky Fan): sufficient volatility forces \<open>trace (acov s \<omega>) \<ge> n - k\<close>.\<close>

lemma trace_bound_pointwise:
  assumes "psd (acov s \<omega>)" and "eigen_lb (acov s \<omega>) (CARD('n) - k)"
  shows "real (CARD('n) - k) \<le> trace (acov s \<omega>)"
proof -
  from assms(2) obtain S where S: "subspace S" "CARD('n) - k \<le> dim S"
    "\<And>x. x \<in> S \<Longrightarrow> x \<bullet> x \<le> x \<bullet> (acov s \<omega> *v x)"
    by (auto simp: eigen_lb_def)
  have "real (CARD('n) - k) \<le> real (dim S)"
    using S(2) by simp
  also have "\<dots> \<le> trace (acov s \<omega>)"
    using assms(1) S by (intro trace_ge_dim) (auto simp: psd_def)
  finally show ?thesis .
qed

lemma stopped_time_integrable:
  assumes t: "0 \<le> t"
  shows "integrable M (\<lambda>\<omega>. min t (tau \<omega>))"
proof (rule integrable_const_bound[of _ t])
  show "AE \<omega> in M. norm (min t (tau \<omega>)) \<le> t"
    using tau_nonneg by eventually_elim (use t in auto)
  show "(\<lambda>\<omega>. min t (tau \<omega>)) \<in> borel_measurable M"
    using tau_meas by measurable
qed

lemma compensator_lower:
  assumes t: "0 \<le> t"
  shows "real (CARD('n) - k) * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M)
      \<le> (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
              (\<lambda>s. trace (acov s \<omega>)) \<partial>M)"
proof -
  define c where "c = real (CARD('n) - k)"
  have ptwise: "AE \<omega> in M. c * min t (tau \<omega>)
      \<le> set_lebesgue_integral lborel {0..min t (tau \<omega>)}
           (\<lambda>s. trace (acov s \<omega>))"
    using tau_nonneg acov_psd acov_eigen_lb acov_trace_integrable
  proof eventually_elim
    case (elim \<omega>)
    define tt where "tt = min t (tau \<omega>)"
    have tt_nonneg: "0 \<le> tt"
      using elim t by (simp add: tt_def)
    have tt_le_tau: "tt \<le> tau \<omega>"
      by (simp add: tt_def)
    have f_int: "set_integrable lborel {0..tt} (\<lambda>s. trace (acov s \<omega>))"
      using elim tt_nonneg by blast
    have c_int: "set_integrable lborel {0..tt} (\<lambda>_. c)"
      unfolding set_integrable_def
      using tt_nonneg
      by (intro integrable_scaleR_left integrable_real_indicator)
        auto
    have mono: "c \<le> trace (acov s \<omega>)" if s: "s \<in> {0..tt}" for s
    proof -
      have "0 \<le> s" "s \<le> tau \<omega>"
        using s tt_le_tau by auto
      then show ?thesis
        unfolding c_def using elim by (intro trace_bound_pointwise) auto
    qed
    have "set_lebesgue_integral lborel {0..tt} (\<lambda>_. c)
        \<le> set_lebesgue_integral lborel {0..tt} (\<lambda>s. trace (acov s \<omega>))"
      by (rule set_integral_mono[OF c_int f_int mono])
    moreover have "set_lebesgue_integral lborel {0..tt} (\<lambda>_. c) = tt * c"
      using tt_nonneg
      by (subst set_integral_const) auto
    ultimately show ?case
      by (simp add: tt_def mult_ac)
  qed
  have int1: "integrable M (\<lambda>\<omega>. c * min t (tau \<omega>))"
    using stopped_time_integrable[OF t] by simp
  have "(\<integral>\<omega>. c * min t (tau \<omega>) \<partial>M)
      \<le> (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
              (\<lambda>s. trace (acov s \<omega>)) \<partial>M)"
    by (rule integral_mono_AE[OF int1 compensator_integrable[OF t] ptwise])
  then show ?thesis
    by (simp add: c_def)
qed

lemma x0_in_K: "x0 \<in> K"
proof (rule ccontr)
  assume notK: "x0 \<notin> K"
  have "AE \<omega> in M. x0 \<in> K"
    using X_start X_in_K tau_nonneg by eventually_elim auto
  then obtain N where N: "{\<omega> \<in> space M. \<not> x0 \<in> K} \<subseteq> N"
    "emeasure M N = 0" "N \<in> sets M"
    by (rule AE_E)
  have "space M \<subseteq> N"
    using N(1) notK by auto
  then have "emeasure M (space M) = 0"
    using emeasure_mono[OF _ N(3)] N(2) by (metis le_zero_eq)
  with emeasure_space_1 show False
    by simp
qed

theorem expected_stopped_time_bound:
  assumes Kball: "K \<subseteq> cball 0 r" and t: "0 \<le> t"
  shows "real (CARD('n) - k) * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> r\<^sup>2 - x0 \<bullet> x0"
proof -
  have sq_bound: "AE \<omega> in M. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<le> r\<^sup>2"
    using X_in_K tau_nonneg
  proof eventually_elim
    case (elim \<omega>)
    have "X (min t (tau \<omega>)) \<omega> \<in> K"
      using elim t by auto
    with Kball have "norm (X (min t (tau \<omega>)) \<omega>) \<le> r"
      by (auto simp: dist_norm)
    then have "(norm (X (min t (tau \<omega>)) \<omega>))\<^sup>2 \<le> r\<^sup>2"
      by (intro power_mono) auto
    then show ?case
      by (simp add: dot_square_norm)
  qed
  have "(\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M) \<le> (\<integral>\<omega>. r\<^sup>2 \<partial>M)"
    by (rule integral_mono_AE[OF stopped_sq_integrable[OF t] _ sq_bound]) auto
  also have "\<dots> = r\<^sup>2"
    by (simp add: prob_space)
  finally have sq: "(\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M) \<le> r\<^sup>2" .
  have "real (CARD('n) - k) * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M)
      \<le> (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
              (\<lambda>s. trace (acov s \<omega>)) \<partial>M)"
    by (rule compensator_lower[OF t])
  also have "\<dots> = (\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M) - x0 \<bullet> x0"
    using dynkin_quadratic[OF t] by simp
  also have "\<dots> \<le> r\<^sup>2 - x0 \<bullet> x0"
    using sq by simp
  finally show ?thesis .
qed

corollary expected_stopped_time_ball_v:
  assumes K_def: "K = cball 0 r" and t: "0 \<le> t"
  shows "(\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> ball_v r k x0"
proof -
  have x0r: "x0 \<bullet> x0 \<le> r\<^sup>2"
  proof -
    have "norm x0 \<le> r"
      using x0_in_K by (simp add: K_def dist_norm)
    then have "(norm x0)\<^sup>2 \<le> r\<^sup>2"
      by (intro power_mono) auto
    then show ?thesis
      by (simp add: dot_square_norm)
  qed
  have "real (CARD('n) - k) * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> r\<^sup>2 - x0 \<bullet> x0"
    using expected_stopped_time_bound[OF _ t] K_def by simp
  then have "(\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> (r\<^sup>2 - x0 \<bullet> x0) / real (CARD('n) - k)"
    using c_pos by (simp add: pos_le_divide_eq mult_ac)
  also have "\<dots> = ball_v r k x0"
    using x0r by (simp add: ball_v_def max_def)
  finally show ?thesis .
qed

text \<open>
  The bound extends from stopped times to the pre-exit time itself by
  monotone convergence: \<open>E[tau] \<le> v(x0)\<close> --- the quantitative statement of
  Example 3.1 that the value function of Theorem 1.1 dominates expected
  exit times in every sufficiently volatile market.
\<close>

theorem expected_exit_time_bound:
  assumes K_def: "K = cball 0 r"
  shows "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) \<le> ennreal (ball_v r k x0)"
proof -
  have meas_min: "(\<lambda>\<omega>. min (real n) (tau \<omega>)) \<in> borel_measurable M" for n
    using tau_meas by measurable
  have bound_n: "(\<integral>\<^sup>+\<omega>. ennreal (min (real n) (tau \<omega>)) \<partial>M)
      \<le> ennreal (ball_v r k x0)" for n
  proof -
    have nn: "AE \<omega> in M. 0 \<le> min (real n) (tau \<omega>)"
      using tau_nonneg by eventually_elim auto
    have "(\<integral>\<^sup>+\<omega>. ennreal (min (real n) (tau \<omega>)) \<partial>M)
        = ennreal (\<integral>\<omega>. min (real n) (tau \<omega>) \<partial>M)"
      by (rule nn_integral_eq_integral[OF stopped_time_integrable nn]) simp
    also have "\<dots> \<le> ennreal (ball_v r k x0)"
      by (intro ennreal_leI expected_stopped_time_ball_v[OF K_def]) simp
    finally show ?thesis .
  qed
  have sup_eq: "AE \<omega> in M. (SUP n. ennreal (min (real n) (tau \<omega>)))
      = ennreal (tau \<omega>)"
    using tau_nonneg
  proof eventually_elim
    case (elim \<omega>)
    obtain m where m: "tau \<omega> \<le> real m"
      using real_arch_simple by blast
    have le: "(SUP n. ennreal (min (real n) (tau \<omega>))) \<le> ennreal (tau \<omega>)"
      by (intro SUP_least ennreal_leI) auto
    have "ennreal (tau \<omega>) = ennreal (min (real m) (tau \<omega>))"
      using m by (simp add: min_def)
    also have "\<dots> \<le> (SUP n. ennreal (min (real n) (tau \<omega>)))"
      by (rule SUP_upper) simp
    finally show ?case
      using le by (rule antisym[rotated])
  qed
  have incseq: "incseq (\<lambda>n \<omega>. ennreal (min (real n) (tau \<omega>)))"
    by (intro incseq_SucI le_funI ennreal_leI) (auto simp: min_def)
  have "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)
      = (\<integral>\<^sup>+\<omega>. (SUP n. ennreal (min (real n) (tau \<omega>))) \<partial>M)"
    by (rule nn_integral_cong_AE) (use sup_eq in \<open>simp add: eq_commute\<close>)
  also have "\<dots> = (SUP n. \<integral>\<^sup>+\<omega>. ennreal (min (real n) (tau \<omega>)) \<partial>M)"
    by (rule nn_integral_monotone_convergence_SUP[OF incseq]) (use meas_min in measurable)
  also have "\<dots> \<le> ennreal (ball_v r k x0)"
    by (rule SUP_least) (rule bound_n)
  finally show ?thesis .
qed

end


(*<*)
end
(*>*)
