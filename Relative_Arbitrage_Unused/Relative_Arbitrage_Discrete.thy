

(*<*)
theory Relative_Arbitrage_Discrete
  imports
    "Martingale_Sampling.Quadratic_Variation"
    "Relative_Arbitrage.Volatile_Market"
begin

(*>*)

text \<open>
  The market bound of arXiv:2512.17702 (Example 3.1) in discrete
             time, with NO martingale-problem assumption.

    In continuous time the identity

      \<open>E[|X (t \<sqinter> \<tau>)|\<^sup>2] - E[\<integral>\<^sub>0\<^sup>(t \<sqinter> \<tau>) tr(acov\<^sub>s) ds] = |x\<^sub>0|\<^sup>2\<close>

    is Ito's formula plus optional sampling, and is the locale assumption
    \<open>dynkin_quadratic\<close> of \<open>Volatile_Market\<close>.  Here the whole
    development is redone in discrete time, where the corresponding
    \<open>identity is a THEOREM: the compensator of |X|\<^sup>2 is the discrete\<close>
    quadratic variation of \<open>Quadratic_Variation\<close>, summed over coordinates.
    Consequently the horizon bound of Example 3.1,

      \<open>N \<le> v(x\<^sub>0) = (r\<^sup>2 - |x\<^sub>0|\<^sup>2)/(n - k),\<close>

    holds with no assumption about stochastic integration whatsoever: the
    hypotheses are only that the coordinates of X are square-integrable
    martingales, that X stays in the ball up to time N, and that each step
    carries at least the volatility that the eigenvalue constraint (1.4)
    of the paper forces on the trace.\<close>
section \<open>Vector-valued quadratic variation\<close>

definition qvar_vec :: "(nat \<Rightarrow> 'a \<Rightarrow> real^'n) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "qvar_vec X n \<omega> =
     (\<Sum>k<n. (X (Suc k) \<omega> - X k \<omega>) \<bullet> (X (Suc k) \<omega> - X k \<omega>))"

lemma qvar_vec_zero [simp]: "qvar_vec X 0 \<omega> = 0"
  by (simp add: qvar_vec_def)

lemma qvar_vec_nonneg: "0 \<le> qvar_vec X n \<omega>"
  unfolding qvar_vec_def by (intro sum_nonneg) simp

lemma qvar_vec_eq_sum_components:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  shows "qvar_vec X n \<omega>
     = (\<Sum>i\<in>UNIV. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega>)"
proof -
  have "qvar_vec X n \<omega>
      = (\<Sum>k<n. \<Sum>i\<in>UNIV. (X (Suc k) \<omega> $ i - X k \<omega> $ i)\<^sup>2)"
    unfolding qvar_vec_def
    by (intro sum.cong refl) (simp add: inner_vec_def power2_eq_square)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>k<n. (X (Suc k) \<omega> $ i - X k \<omega> $ i)\<^sup>2)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i\<in>UNIV. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega>)"
    by (simp add: qvar_def)
  finally show ?thesis .
qed

section \<open>Square-integrable vector martingales\<close>

locale discrete_vec_martingale = nat_sigma_finite_filtered_measure M F
  for M :: "'a measure" and F
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  assumes comp_martingale: "\<And>i. martingale M F 0 (\<lambda>n \<omega>. X n \<omega> $ i)"
    and comp_sq_integrable:
      "\<And>i n. integrable M (\<lambda>\<omega>. (X n \<omega> $ i)\<^sup>2)"

sublocale discrete_vec_martingale \<subseteq> C: sq_int_martingale M F "\<lambda>n \<omega>. X n \<omega> $ i"
proof -
  have parent: "nat_sigma_finite_filtered_measure M F"
    by unfold_locales
  show "sq_int_martingale M F (\<lambda>n \<omega>. X n \<omega> $ i)"
    by (intro sq_int_martingale.intro[OF parent]
        sq_int_martingale_axioms.intro comp_martingale comp_sq_integrable)
qed

context discrete_vec_martingale
begin

lemma norm_sq_eq_sum: "X n \<omega> \<bullet> X n \<omega> = (\<Sum>i\<in>UNIV. (X n \<omega> $ i)\<^sup>2)"
  by (simp add: inner_vec_def power2_eq_square)

lemma norm_sq_integrable: "integrable M (\<lambda>\<omega>. X n \<omega> \<bullet> X n \<omega>)"
  unfolding norm_sq_eq_sum
  by (intro Bochner_Integration.integrable_sum comp_sq_integrable)

lemma qvar_vec_eq_fun:
  "qvar_vec X n = (\<lambda>\<omega>. \<Sum>i\<in>UNIV. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega>)"
  by (rule ext) (rule qvar_vec_eq_sum_components)

lemma qvar_vec_integrable: "integrable M (qvar_vec X n)"
  unfolding qvar_vec_eq_fun
  by (intro Bochner_Integration.integrable_sum C.qvar_integrable)

text \<open>The discrete martingale-problem identity: what
  \<open>dynkin_quadratic\<close> assumes in continuous time is here proved, with the
  compensator given by the quadratic variation.\<close>

theorem expectation_norm_sq_qvar_vec:
  "(\<integral>\<omega>. X n \<omega> \<bullet> X n \<omega> \<partial>M)
     = (\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M) + (\<integral>\<omega>. qvar_vec X n \<omega> \<partial>M)"
proof -
  have "(\<integral>\<omega>. X n \<omega> \<bullet> X n \<omega> \<partial>M)
      = (\<Sum>i\<in>UNIV. \<integral>\<omega>. (X n \<omega> $ i)\<^sup>2 \<partial>M)"
    unfolding norm_sq_eq_sum
    by (intro Bochner_Integration.integral_sum comp_sq_integrable)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
        + (\<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega> \<partial>M))"
    by (intro sum.cong refl C.expectation_sq_qvar)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). \<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
      + (\<Sum>i\<in>(UNIV :: 'n set).
          \<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega> \<partial>M)"
    by (rule sum.distrib)
  also have "(\<Sum>i\<in>(UNIV :: 'n set). \<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M)"
    unfolding norm_sq_eq_sum
    by (intro Bochner_Integration.integral_sum[symmetric] comp_sq_integrable)
  also have "(\<Sum>i\<in>(UNIV :: 'n set).
        \<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega> \<partial>M)
      = (\<integral>\<omega>. qvar_vec X n \<omega> \<partial>M)"
  proof -
    have "(\<integral>\<omega>. qvar_vec X n \<omega> \<partial>M)
        = (\<integral>\<omega>. (\<Sum>i\<in>UNIV. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega>) \<partial>M)"
      by (simp add: qvar_vec_eq_sum_components)
    also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
        \<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega> \<partial>M)"
      by (intro Bochner_Integration.integral_sum C.qvar_integrable)
    finally show ?thesis by simp
  qed
  finally show ?thesis .
qed

end

section \<open>Optional sampling for vector martingales\<close>

lemma inner_self_eq_sum_components:
  fixes v :: "real^'n::finite"
  shows "v \<bullet> v = (\<Sum>i\<in>UNIV. (v $ i)\<^sup>2)"
  by (simp add: inner_vec_def power2_eq_square)

locale discrete_vec_stopped_martingale = discrete_vec_martingale M F X
  for M :: "'a measure" and F
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  fixes T :: "'a \<Rightarrow> nat"
  assumes stopping_time_T: "\<And>n. {\<omega> \<in> space M. T \<omega> \<le> n} \<in> sets (F n)"

sublocale discrete_vec_stopped_martingale
  \<subseteq> S: stopped_sq_int_martingale M F "\<lambda>n \<omega>. X n \<omega> $ i" T
proof -
  have parent: "nat_sigma_finite_filtered_measure M F"
    by unfold_locales
  have sq: "sq_int_martingale M F (\<lambda>n \<omega>. X n \<omega> $ i)"
    by (intro sq_int_martingale.intro[OF parent]
        sq_int_martingale_axioms.intro comp_martingale comp_sq_integrable)
  show "stopped_sq_int_martingale M F (\<lambda>n \<omega>. X n \<omega> $ i) T"
    by (intro stopped_sq_int_martingale.intro[OF sq]
        stopped_sq_int_martingale_axioms.intro stopping_time_T)
qed

context discrete_vec_stopped_martingale
begin

lemma comp_sq_stopped_integrable:
  "integrable M (\<lambda>\<omega>. (X (min n (T \<omega>)) \<omega> $ i)\<^sup>2)"
proof -
  have "integrable M (\<lambda>\<omega>. (stopped T (\<lambda>m \<omega>. X m \<omega> $ i) n \<omega>)\<^sup>2)"
    by (rule S.stopped_sq_integrable)
  then show ?thesis
    by (simp add: stopped_def)
qed

lemma comp_qvar_stopped_integrable:
  "integrable M (\<lambda>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega>)"
proof -
  have eq: "qvar (stopped T (\<lambda>m \<omega>. X m \<omega> $ i)) n
      = (\<lambda>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega>)"
    by (simp add: fun_eq_iff qvar_stopped)
  have "integrable M (qvar (stopped T (\<lambda>m \<omega>. X m \<omega> $ i)) n)"
    by (rule sq_int_martingale.qvar_integrable[OF S.sq_int_martingale_stopped])
  then show ?thesis
    unfolding eq .
qed

lemma norm_sq_stopped_integrable:
  "integrable M (\<lambda>\<omega>. X (min n (T \<omega>)) \<omega> \<bullet> X (min n (T \<omega>)) \<omega>)"
proof -
  have eq: "(\<lambda>\<omega>. X (min n (T \<omega>)) \<omega> \<bullet> X (min n (T \<omega>)) \<omega>)
      = (\<lambda>\<omega>. \<Sum>i\<in>UNIV. (X (min n (T \<omega>)) \<omega> $ i)\<^sup>2)"
    by (simp add: fun_eq_iff inner_self_eq_sum_components)
  show ?thesis
    unfolding eq
    by (intro Bochner_Integration.integrable_sum comp_sq_stopped_integrable)
qed

lemma qvar_vec_stopped_integrable:
  "integrable M (\<lambda>\<omega>. qvar_vec X (min n (T \<omega>)) \<omega>)"
proof -
  have eq: "(\<lambda>\<omega>. qvar_vec X (min n (T \<omega>)) \<omega>)
      = (\<lambda>\<omega>. \<Sum>i\<in>UNIV. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega>)"
    by (simp add: fun_eq_iff qvar_vec_eq_sum_components)
  show ?thesis
    unfolding eq
    by (intro Bochner_Integration.integrable_sum comp_qvar_stopped_integrable)
qed

text \<open>The stopped discrete martingale-problem identity: exactly the shape
  of \<open>dynkin_quadratic\<close>, with the stopping time in place, and proved.\<close>

theorem expectation_norm_sq_qvar_vec_stopped:
  "(\<integral>\<omega>. X (min n (T \<omega>)) \<omega> \<bullet> X (min n (T \<omega>)) \<omega> \<partial>M)
     = (\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M)
       + (\<integral>\<omega>. qvar_vec X (min n (T \<omega>)) \<omega> \<partial>M)"
proof -
  have comp_dynkin: "(\<integral>\<omega>. (X (min n (T \<omega>)) \<omega> $ i)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
        + (\<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega> \<partial>M)" for i
    using S.stopped_expectation_sq_qvar[of n] by simp
  have "(\<integral>\<omega>. X (min n (T \<omega>)) \<omega> \<bullet> X (min n (T \<omega>)) \<omega> \<partial>M)
      = (\<Sum>i\<in>(UNIV :: 'n set). \<integral>\<omega>. (X (min n (T \<omega>)) \<omega> $ i)\<^sup>2 \<partial>M)"
  proof -
    have eq: "(\<lambda>\<omega>. X (min n (T \<omega>)) \<omega> \<bullet> X (min n (T \<omega>)) \<omega>)
        = (\<lambda>\<omega>. \<Sum>i\<in>UNIV. (X (min n (T \<omega>)) \<omega> $ i)\<^sup>2)"
      by (simp add: fun_eq_iff inner_self_eq_sum_components)
    show ?thesis
      unfolding eq
      by (intro Bochner_Integration.integral_sum comp_sq_stopped_integrable)
  qed
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (\<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
      + (\<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega> \<partial>M))"
    by (intro sum.cong refl comp_dynkin)
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). \<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
      + (\<Sum>i\<in>(UNIV :: 'n set).
          \<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega> \<partial>M)"
    by (rule sum.distrib)
  also have "(\<Sum>i\<in>(UNIV :: 'n set). \<integral>\<omega>. (X 0 \<omega> $ i)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M)"
    unfolding norm_sq_eq_sum
    by (intro Bochner_Integration.integral_sum[symmetric] comp_sq_integrable)
  also have "(\<Sum>i\<in>(UNIV :: 'n set).
        \<integral>\<omega>. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. qvar_vec X (min n (T \<omega>)) \<omega> \<partial>M)"
  proof -
    have eq: "(\<lambda>\<omega>. qvar_vec X (min n (T \<omega>)) \<omega>)
        = (\<lambda>\<omega>. \<Sum>i\<in>UNIV. qvar (\<lambda>m \<omega>. X m \<omega> $ i) (min n (T \<omega>)) \<omega>)"
      by (simp add: fun_eq_iff qvar_vec_eq_sum_components)
    show ?thesis
      unfolding eq
      by (intro Bochner_Integration.integral_sum[symmetric]
          comp_qvar_stopped_integrable)
  qed
  finally show ?thesis .
qed

subsection \<open>Measurability and integrability of the stopped horizon\<close>

text \<open>The stopped horizon is the number of steps actually taken, i.e. the
  sum of the indicators of the events of not having stopped yet; this makes
  it measurable without any extra assumption on \<open>T\<close>.\<close>

lemma Ev_sets_M: "{\<omega> \<in> space M. j < T \<omega>} \<in> sets M"
proof -
  have "S.Tgt j \<in> sets M"
    by (rule S.Tgt_sets_M)
  then show ?thesis
    by (simp add: S.Tgt_def)
qed

lemma min_horizon_eq_sum:
  assumes w: "\<omega> \<in> space M"
  shows "real (min N (T \<omega>))
    = (\<Sum>j<N. indicator {\<omega> \<in> space M. j < T \<omega>} \<omega>)"
proof -
  have "(\<Sum>j<N. indicator {\<omega> \<in> space M. j < T \<omega>} \<omega> :: real)
      = (\<Sum>j<N. if j \<in> {j. j < T \<omega>} then 1 else 0)"
    using w by (intro sum.cong refl) auto
  also have "\<dots> = (\<Sum>j \<in> {..<N} \<inter> {j. j < T \<omega>}. (1 :: real))"
    by (subst sum.inter_restrict) auto
  also have "{..<N} \<inter> {j. j < T \<omega>} = {..< min N (T \<omega>)}"
    by auto
  finally show ?thesis
    by simp
qed

lemma min_horizon_measurable:
  "(\<lambda>\<omega>. real (min N (T \<omega>))) \<in> borel_measurable M"
proof -
  have ind: "(\<lambda>w. indicator {v \<in> space M. j < T v} w :: real)
      \<in> borel_measurable M" for j
    using Ev_sets_M by (simp add: borel_measurable_indicator_iff)
  have g_meas: "(\<lambda>w. \<Sum>j<N. indicator {v \<in> space M. j < T v} w :: real)
      \<in> borel_measurable M"
    by (intro borel_measurable_sum ind)
  have eq: "\<And>w. w \<in> space M \<Longrightarrow>
      real (min N (T w)) = (\<Sum>j<N. indicator {v \<in> space M. j < T v} w)"
    by (rule min_horizon_eq_sum)
  have iff: "(\<lambda>w. real (min N (T w))) \<in> borel_measurable M
      \<longleftrightarrow> (\<lambda>w. \<Sum>j<N. indicator {v \<in> space M. j < T v} w :: real)
            \<in> borel_measurable M"
    by (rule measurable_cong[OF eq])
  show ?thesis
    using iff g_meas by simp
qed

end

section \<open>Sufficiently volatile discrete markets\<close>

text \<open>The discrete counterpart of the class \<open>\<P>\<^sub>x\<close>: the transformed
  weight process is a square-integrable vector martingale started at
  \<open>x\<^sub>0\<close> and every step carries at least the volatility \<open>n - k\<close> that the
  eigenvalue constraint of Eq. (1.4) forces on the trace of the
  covariance (see \<open>trace_bound_pointwise\<close> of the companion theory).
  There is no martingale-problem assumption.\<close>

locale discrete_volatile_base = discrete_vec_martingale M F X
  for M :: "'a measure" and F
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
    and k :: nat and r :: real and x0 :: "real^'n" and N :: nat +
  assumes prob_space_M: "prob_space M"
    and k_lb: "1 \<le> k" and k_ub: "k < CARD('n)"
    and X_start: "AE \<omega> in M. X 0 \<omega> = x0"
    and volatile: "AE \<omega> in M. \<forall>j. j < N \<longrightarrow>
      real (CARD('n) - k)
        \<le> (X (Suc j) \<omega> - X j \<omega>) \<bullet> (X (Suc j) \<omega> - X j \<omega>)"
begin

sublocale P: prob_space M
  by (rule prob_space_M)

lemma c_pos: "0 < real (CARD('n) - k)"
  using k_ub by simp

text \<open>Sufficient volatility forces the quadratic variation to grow at
  least linearly --- the discrete form of \<open>compensator_pathwise\<close>.\<close>

lemma qvar_vec_lower:
  "AE \<omega> in M. \<forall>j. j \<le> N \<longrightarrow>
     real (CARD('n) - k) * real j \<le> qvar_vec X j \<omega>"
  using volatile
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix j assume j: "j \<le> N"
    have "real (CARD('n) - k) * real j = (\<Sum>i<j. real (CARD('n) - k))"
      by simp
    also have "\<dots> \<le> (\<Sum>i<j. (X (Suc i) \<omega> - X i \<omega>)
        \<bullet> (X (Suc i) \<omega> - X i \<omega>))"
      using elim j by (intro sum_mono) auto
    finally show "real (CARD('n) - k) * real j \<le> qvar_vec X j \<omega>"
      by (simp add: qvar_vec_def)
  qed
qed

section \<open>The discrete gradient strategy realizes relative arbitrage\<close>

text \<open>The discrete relative value process of the gradient strategy: the
  ball value function of the current position plus the accumulated
  quadratic variation, normalised as in Eq. (1.1).  In continuous time
  this is \<open>arb_V\<close> of \<open>Optimal\_Exit\_Time;\<close> here it needs no
  stochastic integral at all, and the pathwise lower bound below is a
  theorem rather than a consequence of Ito's formula.\<close>

definition dV :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
  "dV j \<omega> = ball_v r k (X j \<omega>)
     + qvar_vec X j \<omega> / real (CARD('n) - k)"

lemma dV_start: "AE \<omega> in M. dV 0 \<omega> = ball_v r k x0"
  using X_start by eventually_elim (simp add: dV_def)

lemma dV_pathwise:
  "AE \<omega> in M. \<forall>j. j \<le> N \<longrightarrow>
     ball_v r k (X j \<omega>) + real j \<le> dV j \<omega>"
  using qvar_vec_lower
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix j assume j: "j \<le> N"
    have "real (CARD('n) - k) * real j \<le> qvar_vec X j \<omega>"
      using elim j by blast
    then have "real j \<le> qvar_vec X j \<omega> / real (CARD('n) - k)"
      using c_pos by (simp add: mult_ac pos_le_divide_eq)
    then show "ball_v r k (X j \<omega>) + real j \<le> dV j \<omega>"
      by (simp add: dV_def)
  qed
qed

lemma nat_floor_le:
  assumes "t \<in> {0..real N}"
  shows "nat \<lfloor>t\<rfloor> \<le> N"
proof -
  have "\<lfloor>t\<rfloor> \<le> int N"
    using assms by (simp add: floor_le_iff)
  then show ?thesis by simp
qed

text \<open>Definition 1.1 for the discrete gradient strategy, with no
  assumption whatsoever about stochastic integration: beyond the
  critical horizon \<open>v(x\<^sub>0)\<close> the strategy is a relative arbitrage.\<close>

theorem discrete_relative_arbitrage:
  assumes horizon: "ball_v r k x0 < real N"
  shows "relative_arbitrage M (\<lambda>t \<omega>. dV (nat \<lfloor>t\<rfloor>) \<omega>) (real N)"
  unfolding relative_arbitrage_def
proof (intro conjI)
  show "\<forall>t\<in>{0..real N}. AE \<omega> in M. 0 \<le> dV (nat \<lfloor>t\<rfloor>) \<omega>"
  proof
    fix t assume t: "t \<in> {0..real N}"
    then have j: "nat \<lfloor>t\<rfloor> \<le> N" by (rule nat_floor_le)
    show "AE \<omega> in M. 0 \<le> dV (nat \<lfloor>t\<rfloor>) \<omega>"
      using dV_pathwise
    proof eventually_elim
      case (elim \<omega>)
      have "ball_v r k (X (nat \<lfloor>t\<rfloor>) \<omega>) + real (nat \<lfloor>t\<rfloor>)
          \<le> dV (nat \<lfloor>t\<rfloor>) \<omega>"
        using elim j by blast
      moreover have "0 \<le> ball_v r k (X (nat \<lfloor>t\<rfloor>) \<omega>)"
        by (rule ball_v_nonneg)
      ultimately show ?case by simp
    qed
  qed
next
  have gain: "AE \<omega> in M. dV 0 \<omega> < dV N \<omega>"
    using dV_pathwise dV_start
  proof eventually_elim
    case (elim \<omega>)
    have "dV 0 \<omega> = ball_v r k x0"
      using elim by blast
    also have "\<dots> < real N"
      by (fact horizon)
    also have "real N \<le> ball_v r k (X N \<omega>) + real N"
      using ball_v_nonneg[of r k "X N \<omega>"] by simp
    also have "\<dots> \<le> dV N \<omega>"
      using elim by blast
    finally show ?case .
  qed
  have flo: "nat \<lfloor>real N\<rfloor> = N" and flo0: "nat \<lfloor>(0 :: real)\<rfloor> = 0"
    by simp_all
  show "AE \<omega> in M. dV (nat \<lfloor>(0 :: real)\<rfloor>) \<omega>
      \<le> dV (nat \<lfloor>real N\<rfloor>) \<omega>"
    unfolding flo flo0 using gain by eventually_elim auto
  show "\<not> (AE \<omega> in M. dV (nat \<lfloor>real N\<rfloor>) \<omega>
      \<le> dV (nat \<lfloor>(0 :: real)\<rfloor>) \<omega>)"
    unfolding flo flo0
  proof
    assume "AE \<omega> in M. dV N \<omega> \<le> dV 0 \<omega>"
    with gain have "AE \<omega> in M. False"
      by eventually_elim auto
    then show False
      using P.AE_False by simp
  qed
qed

end

section \<open>The horizon bound of Example 3.1\<close>

text \<open>Adding the requirement that the market stays in the ball up to the
  horizon gives the bound of Example 3.1 --- and, together with the
  arbitrage theorem above, the critical horizon: beyond \<open>v(x\<^sub>0)\<close> the
  market cannot remain sufficiently volatile inside the ball.\<close>

locale discrete_volatile_market =
  discrete_volatile_base M F X k r x0 N
  for M :: "'a measure" and F
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
    and k :: nat and r :: real and x0 :: "real^'n" and N :: nat +
  assumes X_in_ball: "AE \<omega> in M. \<forall>n. n \<le> N \<longrightarrow> X n \<omega> \<in> cball 0 r"
begin

lemma x0_in_ball: "x0 \<bullet> x0 \<le> r\<^sup>2"
proof -
  have "AE \<omega> in M. x0 \<bullet> x0 \<le> r\<^sup>2"
    using X_start X_in_ball
  proof eventually_elim
    case (elim \<omega>)
    then have "x0 \<in> cball 0 r" by auto
    then have "norm x0 \<le> r"
      by (simp add: dist_norm)
    then have "(norm x0)\<^sup>2 \<le> r\<^sup>2"
      by (intro power_mono) auto
    then show ?case
      by (simp add: dot_square_norm)
  qed
  then show ?thesis
    using P.AE_False by fastforce
qed

text \<open>The main theorem: the horizon of a sufficiently volatile discrete
  market that stays in the ball is bounded by the value function of
  Example 3.1.  No martingale-problem assumption is used --- the
  identity that replaces it is
  \<open>expectation_norm_sq_qvar_vec\<close>.\<close>

theorem horizon_le_ball_v: "real N \<le> ball_v r k x0"
proof -
  have start_sq: "(\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M) = x0 \<bullet> x0"
  proof -
    have ae: "AE \<omega> in M. X 0 \<omega> \<bullet> X 0 \<omega> = x0 \<bullet> x0"
      using X_start by eventually_elim simp
    have m1: "(\<lambda>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega>) \<in> borel_measurable M"
      using norm_sq_integrable by (rule borel_measurable_integrable)
    have "(\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M) = (\<integral>\<omega>. x0 \<bullet> x0 \<partial>M)"
      by (rule integral_cong_AE[OF m1 _ ae]) simp
    then show ?thesis
      by (simp add: P.prob_space)
  qed
  have end_sq: "(\<integral>\<omega>. X N \<omega> \<bullet> X N \<omega> \<partial>M) \<le> r\<^sup>2"
  proof -
    have "AE \<omega> in M. X N \<omega> \<bullet> X N \<omega> \<le> r\<^sup>2"
      using X_in_ball
    proof eventually_elim
      case (elim \<omega>)
      then have "X N \<omega> \<in> cball 0 r" by auto
      then have "norm (X N \<omega>) \<le> r"
        by (simp add: dist_norm)
      then have "(norm (X N \<omega>))\<^sup>2 \<le> r\<^sup>2"
        by (intro power_mono) auto
      then show ?case
        by (simp add: dot_square_norm)
    qed
    then have "(\<integral>\<omega>. X N \<omega> \<bullet> X N \<omega> \<partial>M) \<le> (\<integral>\<omega>. r\<^sup>2 \<partial>M)"
      by (intro integral_mono_AE norm_sq_integrable) simp_all
    then show ?thesis
      by (simp add: P.prob_space)
  qed
  have qvar_lb: "real (CARD('n) - k) * real N
      \<le> (\<integral>\<omega>. qvar_vec X N \<omega> \<partial>M)"
  proof -
    have ae: "AE \<omega> in M. real (CARD('n) - k) * real N \<le> qvar_vec X N \<omega>"
      using qvar_vec_lower by eventually_elim blast
    have "(\<integral>\<omega>. real (CARD('n) - k) * real N \<partial>M)
        \<le> (\<integral>\<omega>. qvar_vec X N \<omega> \<partial>M)"
      by (intro integral_mono_AE qvar_vec_integrable ae) simp
    then show ?thesis
      by (simp add: P.prob_space)
  qed
  have "real (CARD('n) - k) * real N \<le> r\<^sup>2 - x0 \<bullet> x0"
  proof -
    have "(\<integral>\<omega>. qvar_vec X N \<omega> \<partial>M)
        = (\<integral>\<omega>. X N \<omega> \<bullet> X N \<omega> \<partial>M) - (\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M)"
      using expectation_norm_sq_qvar_vec[of N] by simp
    also have "\<dots> \<le> r\<^sup>2 - x0 \<bullet> x0"
      using end_sq start_sq by simp
    finally show ?thesis
      using qvar_lb by simp
  qed
  then have "real N \<le> (r\<^sup>2 - x0 \<bullet> x0) / real (CARD('n) - k)"
    using c_pos by (simp add: mult_ac pos_le_divide_eq)
  also have "\<dots> = ball_v r k x0"
    using x0_in_ball by (simp add: ball_v_def max_def)
  finally show ?thesis .
qed

text \<open>Consequently the critical horizon is exactly \<open>v(x\<^sub>0)\<close>: a
  sufficiently volatile market can stay in the ball for at most
  \<open>v(x\<^sub>0)\<close> steps, and by \<open>discrete_relative_arbitrage\<close> any longer
  horizon yields relative arbitrage.\<close>

corollary horizon_critical:
  assumes "ball_v r k x0 < real N"
  shows False
  using assms horizon_le_ball_v by simp

end

section \<open>The exit-time bound of Example 3.1, with a stopping time\<close>

text \<open>The full discrete analogue of \<open>expected_stopped_time_ball_v\<close> of
  @{theory Relative_Arbitrage.Volatile_Market}: the market need only stay in the ball
  up to the stopping time \<open>T\<close>, and the conclusion bounds the expected
  stopped horizon.  Unlike the continuous-time version, no
  martingale-problem assumption enters: the identity used is the stopped
  Dynkin identity \<open>expectation_norm_sq_qvar_vec_stopped\<close>, which is a
  theorem of optional sampling.\<close>

locale discrete_volatile_stopped_market =
  discrete_volatile_base M F X k r x0 N +
  discrete_vec_stopped_martingale M F X T
  for M :: "'a measure" and F
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
    and k :: nat and r :: real and x0 :: "real^'n" and N :: nat
    and T :: "'a \<Rightarrow> nat" +
  assumes X_in_ball_stopped:
    "AE \<omega> in M. \<forall>n. n \<le> N \<longrightarrow> X (min n (T \<omega>)) \<omega> \<in> cball 0 r"
begin

lemma x0_in_ball_stopped: "x0 \<bullet> x0 \<le> r\<^sup>2"
proof -
  have "AE \<omega> in M. x0 \<bullet> x0 \<le> r\<^sup>2"
    using X_start X_in_ball_stopped
  proof eventually_elim
    case (elim \<omega>)
    then have "X (min 0 (T \<omega>)) \<omega> \<in> cball 0 r" by auto
    then have "x0 \<in> cball 0 r"
      using elim by simp
    then have "norm x0 \<le> r"
      by (simp add: dist_norm)
    then have "(norm x0)\<^sup>2 \<le> r\<^sup>2"
      by (intro power_mono) auto
    then show ?case
      by (simp add: dot_square_norm)
  qed
  then show ?thesis
    using P.AE_False by fastforce
qed

lemma min_horizon_integrable: "integrable M (\<lambda>\<omega>. real (min N (T \<omega>)))"
proof (rule P.integrable_const_bound[of _ "real N"])
  show "AE \<omega> in M. norm (real (min N (T \<omega>))) \<le> real N"
    by simp
  show "(\<lambda>\<omega>. real (min N (T \<omega>))) \<in> borel_measurable M"
    by (rule min_horizon_measurable)
qed

theorem expected_stopped_horizon_le_ball_v:
  "(\<integral>\<omega>. real (min N (T \<omega>)) \<partial>M) \<le> ball_v r k x0"
proof -
  have start_sq: "(\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M) = x0 \<bullet> x0"
  proof -
    have ae: "AE \<omega> in M. X 0 \<omega> \<bullet> X 0 \<omega> = x0 \<bullet> x0"
      using X_start by eventually_elim simp
    have m1: "(\<lambda>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega>) \<in> borel_measurable M"
      using norm_sq_integrable by (rule borel_measurable_integrable)
    have "(\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M) = (\<integral>\<omega>. x0 \<bullet> x0 \<partial>M)"
      by (rule integral_cong_AE[OF m1 _ ae]) simp
    then show ?thesis
      by (simp add: P.prob_space)
  qed
  have end_sq: "(\<integral>\<omega>. X (min N (T \<omega>)) \<omega> \<bullet> X (min N (T \<omega>)) \<omega> \<partial>M) \<le> r\<^sup>2"
  proof -
    have "AE \<omega> in M.
        X (min N (T \<omega>)) \<omega> \<bullet> X (min N (T \<omega>)) \<omega> \<le> r\<^sup>2"
      using X_in_ball_stopped
    proof eventually_elim
      case (elim \<omega>)
      then have "X (min N (T \<omega>)) \<omega> \<in> cball 0 r" by auto
      then have "norm (X (min N (T \<omega>)) \<omega>) \<le> r"
        by (simp add: dist_norm)
      then have "(norm (X (min N (T \<omega>)) \<omega>))\<^sup>2 \<le> r\<^sup>2"
        by (intro power_mono) auto
      then show ?case
        by (simp add: dot_square_norm)
    qed
    then have "(\<integral>\<omega>. X (min N (T \<omega>)) \<omega> \<bullet> X (min N (T \<omega>)) \<omega> \<partial>M)
        \<le> (\<integral>\<omega>. r\<^sup>2 \<partial>M)"
      by (intro integral_mono_AE norm_sq_stopped_integrable) simp_all
    then show ?thesis
      by (simp add: P.prob_space)
  qed
  have qvar_lb: "real (CARD('n) - k) * (\<integral>\<omega>. real (min N (T \<omega>)) \<partial>M)
      \<le> (\<integral>\<omega>. qvar_vec X (min N (T \<omega>)) \<omega> \<partial>M)"
  proof -
    have ae: "AE \<omega> in M. real (CARD('n) - k) * real (min N (T \<omega>))
        \<le> qvar_vec X (min N (T \<omega>)) \<omega>"
      using qvar_vec_lower by eventually_elim simp
    have "(\<integral>\<omega>. real (CARD('n) - k) * real (min N (T \<omega>)) \<partial>M)
        \<le> (\<integral>\<omega>. qvar_vec X (min N (T \<omega>)) \<omega> \<partial>M)"
      by (intro integral_mono_AE qvar_vec_stopped_integrable ae
          Bochner_Integration.integrable_mult_right min_horizon_integrable)
    then show ?thesis by simp
  qed
  have "real (CARD('n) - k) * (\<integral>\<omega>. real (min N (T \<omega>)) \<partial>M)
      \<le> r\<^sup>2 - x0 \<bullet> x0"
  proof -
    have "(\<integral>\<omega>. qvar_vec X (min N (T \<omega>)) \<omega> \<partial>M)
        = (\<integral>\<omega>. X (min N (T \<omega>)) \<omega> \<bullet> X (min N (T \<omega>)) \<omega> \<partial>M)
          - (\<integral>\<omega>. X 0 \<omega> \<bullet> X 0 \<omega> \<partial>M)"
      using expectation_norm_sq_qvar_vec_stopped[of N] by simp
    also have "\<dots> \<le> r\<^sup>2 - x0 \<bullet> x0"
      using end_sq start_sq by simp
    finally show ?thesis
      using qvar_lb by simp
  qed
  then have "(\<integral>\<omega>. real (min N (T \<omega>)) \<partial>M)
      \<le> (r\<^sup>2 - x0 \<bullet> x0) / real (CARD('n) - k)"
    using c_pos by (simp add: mult_ac pos_le_divide_eq)
  also have "\<dots> = ball_v r k x0"
    using x0_in_ball_stopped by (simp add: ball_v_def max_def)
  finally show ?thesis .
qed

end


(*<*)
end
(*>*)
