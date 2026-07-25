(*
  Title:   Ito_Market.thy
  Content: The martingale-problem identity of Relative_Arbitrage_Stochastic
           becomes a theorem.

  The locale sufficiently_volatile_market assumes the identity

    E[|X (t /\ tau)|^2] - E[int_0^(t /\ tau) tr(a s) ds] = |x0|^2   (dynkin_quadratic)

  at every horizon t.  Ito's formula produces it in the process form

    Z t = |X t|^2 - int_0^t tr(a s) ds   is a martingale,

  from which the identity at a stopped time is exactly optional sampling.
  The locale ito_volatile_market below assumes the process form together
  with the regularity that optional sampling needs -- continuous paths and
  an integrable bound on the horizon -- and PROVES
  sufficiently_volatile_market.  So every result of the probabilistic part
  of the paper (Lemma 2.1, the exit-time bound, the arbitrage and
  optimality theorems) holds under the martingale property of Z instead of
  the ad hoc identity.
*)

theory Ito_Market
  imports
    Optional_Sampling
    Brownian_Market
begin

section \<open>An auxiliary fact on Lebesgue integrals over singletons\<close>

lemma set_integral_lborel_singleton [simp]:
  fixes f :: "real \<Rightarrow> real"
  shows "set_lebesgue_integral lborel {c} f = 0"
proof -
  have "AE s in lborel. indicat_real {c} s *\<^sub>R f s = 0"
    using AE_lborel_singleton[of c] by auto
  then show ?thesis
    unfolding set_lebesgue_integral_def by (rule integral_eq_zero_AE)
qed

section \<open>The process of Ito's formula\<close>

definition ito_Z ::
  "(real \<Rightarrow> 'a \<Rightarrow> real^'n) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real^'n^'n) \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
  where
  "ito_Z X acov t \<omega> = X t \<omega> \<bullet> X t \<omega>
     - set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"

section \<open>Markets given by the martingale problem in process form\<close>

locale ito_volatile_market =
  martingale M F 0 X
  for M :: "'a measure"
    and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  fixes acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
    and k :: nat and L :: real
    and K :: "(real^'n) set"
    and x0 :: "real^'n"
    and tau :: "'a \<Rightarrow> real"
    and Dom :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes prob_space_M: "prob_space M"
    and k_lb: "1 \<le> k" and k_ub: "k < CARD('n)" and L_ge: "1 \<le> L"
    and X_start: "AE \<omega> in M. X 0 \<omega> = x0"
    and tau_nonneg': "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_meas: "tau \<in> borel_measurable M"
    and tau_stopping: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and X_in_K: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
    and acov_psd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
    and acov_eigen_lb:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
         eigen_lb (acov s \<omega>) (CARD('n) - k)"
    and acov_eigen_ub:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
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
    and Z_martingale: "martingale M F 0 (ito_Z X acov)"
    and Z_paths_cont: "AE \<omega> in M. continuous_on {0..} (\<lambda>s. ito_Z X acov s \<omega>)"
    and Z_dom: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M.
         \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>ito_Z X acov s \<omega>\<bar> \<le> Dom u \<omega>"
    and Dom_integrable: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (Dom u)"

sublocale ito_volatile_market \<subseteq> prob_space M
  by (rule prob_space_M)

sublocale ito_volatile_market \<subseteq> Mz: martingale M F 0 "ito_Z X acov"
  by (rule Z_martingale)

context ito_volatile_market
begin

subsection \<open>The stopped process of Ito's formula\<close>

lemma stopped_Z_measurable:
  assumes t: "0 \<le> t"
  shows "(\<lambda>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega>) \<in> borel_measurable M"
proof -
  have m1: "(\<lambda>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega>)
      \<in> borel_measurable M"
    using stopped_sq_integrable[OF t] by (rule borel_measurable_integrable)
  have m2: "(\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
        (\<lambda>s. trace (acov s \<omega>))) \<in> borel_measurable M"
    using compensator_integrable[OF t] by (rule borel_measurable_integrable)
  show ?thesis
    unfolding ito_Z_def by (intro borel_measurable_diff m1 m2)
qed

lemma Z_zero_expectation: "(\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M) = x0 \<bullet> x0"
proof -
  have ae: "AE \<omega> in M. ito_Z X acov 0 \<omega> = x0 \<bullet> x0"
    using X_start
  proof eventually_elim
    case (elim \<omega>)
    have z: "ito_Z X acov 0 \<omega> = X 0 \<omega> \<bullet> X 0 \<omega>
        - set_lebesgue_integral lborel {0..0} (\<lambda>s. trace (acov s \<omega>))"
      unfolding ito_Z_def ..
    have i0: "set_lebesgue_integral lborel {0..0 :: real}
        (\<lambda>s. trace (acov s \<omega>)) = 0"
      by simp
    show ?case
      unfolding z i0 elim by (rule diff_zero)
  qed
  have meas: "ito_Z X acov 0 \<in> borel_measurable M"
    using Mz.integrable[of 0] by (auto intro: borel_measurable_integrable)
  have "(\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M) = (\<integral>\<omega>. x0 \<bullet> x0 \<partial>M)"
    using meas ae by (intro integral_cong_AE) auto
  then show ?thesis
    by (simp add: prob_space)
qed

subsection \<open>Optional sampling gives the martingale-problem identity\<close>

lemma stopped_cont_martingale_at:
  assumes t: "0 < t"
  shows "stopped_cont_martingale M F (ito_Z X acov) tau t (Dom t)"
proof (intro stopped_cont_martingale.intro[OF Z_martingale]
    stopped_cont_martingale_axioms.intro)
  show "0 < t" by (rule t)
  show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>" by (rule tau_nonneg')
  show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    by (rule tau_stopping)
  show "AE \<omega> in M. continuous_on {0..t} (\<lambda>s. ito_Z X acov s \<omega>)"
    using Z_paths_cont by eventually_elim (auto intro: continuous_on_subset)
  show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> \<bar>ito_Z X acov s \<omega>\<bar> \<le> Dom t \<omega>"
    using t by (intro Z_dom) simp
  show "integrable M (Dom t)"
    using t by (intro Dom_integrable) simp
  show "(\<lambda>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega>) \<in> borel_measurable M"
    using t by (intro stopped_Z_measurable) simp
qed

theorem stopped_Z_expectation:
  assumes t: "0 \<le> t"
  shows "(\<integral>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega> \<partial>M) = x0 \<bullet> x0"
proof (cases "0 < t")
  case True
  have "(\<integral>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M)"
    by (rule stopped_cont_martingale.optional_sampling
        [OF stopped_cont_martingale_at[OF True]])
  then show ?thesis
    by (simp add: Z_zero_expectation)
next
  case False
  with t have t0: "t = 0" by simp
  have "AE \<omega> in M. ito_Z X acov (min t (tau \<omega>)) \<omega> = ito_Z X acov 0 \<omega>"
    using AE_space by eventually_elim (simp add: t0 tau_nonneg')
  moreover have "(\<lambda>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega>) \<in> borel_measurable M"
    using t by (rule stopped_Z_measurable)
  moreover have "ito_Z X acov 0 \<in> borel_measurable M"
    using Mz.integrable[of 0] by (auto intro: borel_measurable_integrable)
  ultimately have "(\<integral>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M)"
    by (intro integral_cong_AE) auto
  then show ?thesis
    by (simp add: Z_zero_expectation)
qed

theorem dynkin_quadratic_holds:
  assumes t: "0 \<le> t"
  shows "(\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M)
       - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
       = x0 \<bullet> x0"
proof -
  have "(\<integral>\<omega>. ito_Z X acov (min t (tau \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M)
        - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                 (\<lambda>s. trace (acov s \<omega>)) \<partial>M)"
    unfolding ito_Z_def
    by (intro Bochner_Integration.integral_diff stopped_sq_integrable[OF t]
        compensator_integrable[OF t])
  with stopped_Z_expectation[OF t] show ?thesis by simp
qed

end

section \<open>The martingale problem in process form implies the market locale\<close>

sublocale ito_volatile_market
  \<subseteq> SV: sufficiently_volatile_market M F X acov k L K x0 tau
proof -
  have mg: "martingale M F (0 :: real) X"
    by unfold_locales
  show "sufficiently_volatile_market M F X acov k L K x0 tau"
  proof (intro sufficiently_volatile_market.intro[OF mg]
      sufficiently_volatile_market_axioms.intro)
    show "prob_space M" by (rule prob_space_M)
    show "1 \<le> k" by (rule k_lb)
    show "k < CARD('n)" by (rule k_ub)
    show "1 \<le> L" by (rule L_ge)
    show "AE \<omega> in M. X 0 \<omega> = x0" by (rule X_start)
    show "AE \<omega> in M. 0 \<le> tau \<omega>"
      using AE_space by eventually_elim (rule tau_nonneg')
    show "tau \<in> borel_measurable M" by (rule tau_meas)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
      by (rule X_in_K)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
      by (rule acov_psd)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
        eigen_lb (acov s \<omega>) (CARD('n) - k)"
      by (rule acov_eigen_lb)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
      by (rule acov_eigen_ub)
    show "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (rule acov_trace_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        integrable M (\<lambda>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega>)"
      by (rule stopped_sq_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
               (\<lambda>s. trace (acov s \<omega>)))"
      by (rule compensator_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        (\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                   (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
        = x0 \<bullet> x0"
      by (rule dynkin_quadratic_holds)
  qed
qed

text \<open>Consequently every theorem of the probabilistic part is available in
  the process form of the martingale problem; for instance the exit-time
  bound of Lemma 2.1.\<close>

theorem (in ito_volatile_market) ito_expected_stopped_time_bound:
  assumes Kball: "K \<subseteq> cball 0 r" and t: "0 \<le> t"
  shows "real (CARD('n) - k) * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> r\<^sup>2 - x0 \<bullet> x0"
  using assms by (rule SV.expected_stopped_time_bound)

section \<open>Removing the domination assumption for stopped markets\<close>

text \<open>Two-sided pointwise bounds on the trace, from the eigenvalue
  conditions: positive semidefiniteness makes the diagonal, hence the trace,
  nonnegative, and the eigenvalue upper bound of Eq. (1.7) caps every
  diagonal entry by \<open>L\<close>.\<close>

lemma diag_eq_inner_axis:
  fixes a :: "real^'n^'n"
  shows "a $ i $ i = axis i (1 :: real) \<bullet> (a *v axis i 1)"
proof -
  have "axis i (1 :: real) \<bullet> (a *v axis i 1) = (a *v axis i 1) $ i"
    by (simp add: inner_axis')
  also have "\<dots> = a $ i $ i"
    by (simp add: matrix_vector_mult_basis column_def)
  finally show ?thesis ..
qed

lemma trace_nonneg_psd:
  fixes a :: "real^'n^'n"
  assumes "\<And>x. 0 \<le> x \<bullet> (a *v x)"
  shows "0 \<le> trace a"
proof -
  have "0 \<le> a $ i $ i" for i
    unfolding diag_eq_inner_axis by (rule assms)
  then show ?thesis
    unfolding trace_def by (intro sum_nonneg) simp
qed

lemma trace_le_eigen_ub:
  fixes a :: "real^'n^'n"
  assumes ub: "eigen_ub a L"
  shows "trace a \<le> L * real CARD('n)"
proof -
  have diag: "a $ i $ i \<le> L" for i
  proof -
    have "a $ i $ i = axis i (1 :: real) \<bullet> (a *v axis i 1)"
      by (rule diag_eq_inner_axis)
    also have "\<dots> \<le> L * (axis i (1 :: real) \<bullet> axis i 1)"
      using ub unfolding eigen_ub_def by blast
    also have "\<dots> = L"
      by (simp add: inner_axis')
    finally show ?thesis .
  qed
  have "trace a = (\<Sum>i\<in>(UNIV :: 'n set). a $ i $ i)"
    unfolding trace_def ..
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). L)"
    by (intro sum_mono diag)
  also have "\<dots> = L * real CARD('n)"
    by simp
  finally show ?thesis .
qed

text \<open>In a market whose process and covariance are already stopped at
  \<open>tau\<close> --- which is no restriction, since nothing after \<open>tau\<close> enters any
  statement of the paper --- the process of Ito's formula is bounded by a
  constant on every horizon, so the domination hypothesis of
  \<open>ito_volatile_market\<close> is automatic.\<close>

locale ito_stopped_market =
  martingale M F 0 X
  for M :: "'a measure"
    and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  fixes acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
    and k :: nat and L :: real
    and K :: "(real^'n) set"
    and x0 :: "real^'n"
    and tau :: "'a \<Rightarrow> real"
    and r :: real
  assumes prob_space_M: "prob_space M"
    and k_lb: "1 \<le> k" and k_ub: "k < CARD('n)" and L_ge: "1 \<le> L"
    and X_start: "AE \<omega> in M. X 0 \<omega> = x0"
    and tau_nonneg': "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_meas: "tau \<in> borel_measurable M"
    and tau_stopping: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and X_in_K: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
    and K_ball: "K \<subseteq> cball 0 r"
    and X_stopped: "\<And>s \<omega>. \<omega> \<in> space M \<Longrightarrow> X s \<omega> = X (min s (tau \<omega>)) \<omega>"
    and acov_stopped: "\<And>s \<omega>. \<omega> \<in> space M \<Longrightarrow> tau \<omega> < s \<Longrightarrow> acov s \<omega> = 0"
    and acov_psd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
    and acov_eigen_lb:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
         eigen_lb (acov s \<omega>) (CARD('n) - k)"
    and acov_eigen_ub:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
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
    and Z_martingale: "martingale M F 0 (ito_Z X acov)"
    and Z_paths_cont: "AE \<omega> in M. continuous_on {0..} (\<lambda>s. ito_Z X acov s \<omega>)"

sublocale ito_stopped_market \<subseteq> prob_space M
  by (rule prob_space_M)

context ito_stopped_market
begin

lemma nL_nonneg: "0 \<le> L * real CARD('n)"
  using L_ge by simp

lemma sq_bounded:
  assumes w: "\<omega> \<in> space M"
    and inK: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
    and s: "0 \<le> s"
  shows "X s \<omega> \<bullet> X s \<omega> \<le> r\<^sup>2"
proof -
  have "0 \<le> min s (tau \<omega>)"
    using s tau_nonneg'[OF w] by simp
  moreover have "min s (tau \<omega>) \<le> tau \<omega>" by simp
  ultimately have "X (min s (tau \<omega>)) \<omega> \<in> K"
    using inK by blast
  then have "X s \<omega> \<in> K"
    using X_stopped[OF w, of s] by simp
  then have "norm (X s \<omega>) \<le> r"
    using K_ball by (auto simp: dist_norm)
  then have "(norm (X s \<omega>))\<^sup>2 \<le> r\<^sup>2"
    by (intro power_mono) auto
  then show ?thesis
    by (simp add: power2_norm_eq_inner)
qed

lemma trace_bounded:
  assumes w: "\<omega> \<in> space M"
    and psd: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
    and ub: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
    and s: "0 \<le> s"
  shows "0 \<le> trace (acov s \<omega>) \<and> trace (acov s \<omega>) \<le> L * real CARD('n)"
proof (cases "s \<le> tau \<omega>")
  case True
  have "0 \<le> trace (acov s \<omega>)"
    using psd s True by (intro trace_nonneg_psd) (auto simp: psd_def)
  moreover have "trace (acov s \<omega>) \<le> L * real CARD('n)"
    using ub s True by (intro trace_le_eigen_ub) auto
  ultimately show ?thesis by simp
next
  case False
  then have "acov s \<omega> = 0"
    using w by (intro acov_stopped) auto
  then show ?thesis
    using nL_nonneg by (simp add: trace_def)
qed

lemma compensator_bounded:
  assumes w: "\<omega> \<in> space M"
    and psd: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
    and ub: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
    and int: "\<forall>t. 0 \<le> t \<longrightarrow> set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
    and s: "0 \<le> s"
  shows "0 \<le> set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))
    \<and> set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))
        \<le> L * real CARD('n) * s"
proof -
  define c where "c = L * real CARD('n)"
  have c_nonneg: "0 \<le> c"
    unfolding c_def by (rule nL_nonneg)
  have f_int: "set_integrable lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))"
    using int s by blast
  have c_int: "set_integrable lborel {0..s} (\<lambda>_. c)"
    unfolding set_integrable_def using s
    by (intro integrable_scaleR_left integrable_real_indicator)
      (auto simp: emeasure_lborel_Icc)
  have zero_int: "set_integrable lborel {0..s} (\<lambda>_. 0 :: real)"
    unfolding set_integrable_def by simp
  have pt: "0 \<le> trace (acov \<sigma> \<omega>) \<and> trace (acov \<sigma> \<omega>) \<le> c"
    if "\<sigma> \<in> {0..s}" for \<sigma>
    unfolding c_def using that by (intro trace_bounded[OF w psd ub]) auto
  have lower: "0 \<le> set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))"
  proof -
    have "set_lebesgue_integral lborel {0..s} (\<lambda>_. 0 :: real)
        \<le> set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))"
      by (rule set_integral_mono[OF zero_int f_int]) (use pt in blast)
    then show ?thesis by simp
  qed
  have "set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))
      \<le> set_lebesgue_integral lborel {0..s} (\<lambda>_. c)"
    by (rule set_integral_mono[OF f_int c_int]) (use pt in blast)
  also have "set_lebesgue_integral lborel {0..s} (\<lambda>_. c) = c * s"
  proof -
    have m: "measure lborel {0..s} = s"
    proof -
      have "measure lborel {0..s} = s - 0"
        by (rule measure_lborel_Icc[OF s])
      also have "s - 0 = s"
        by (rule diff_zero)
      finally show ?thesis .
    qed
    have "set_lebesgue_integral lborel {0..s} (\<lambda>_. c)
        = measure lborel {0..s} *\<^sub>R c"
      using s by (intro set_integral_const) auto
    also have "measure lborel {0..s} *\<^sub>R c = c * s"
      unfolding m by (simp only: real_scaleR_def mult.commute)
    finally show ?thesis .
  qed
  finally have "set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))
      \<le> c * s" .
  with lower show ?thesis
    unfolding c_def by simp
qed

lemma Z_dominated:
  assumes u: "0 \<le> u"
  shows "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
    \<bar>ito_Z X acov s \<omega>\<bar> \<le> r\<^sup>2 + L * real CARD('n) * u"
  using AE_space X_in_K acov_psd acov_eigen_ub acov_trace_integrable
proof eventually_elim
  case (elim \<omega>)
  then have w: "\<omega> \<in> space M"
    and inK: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
    and psd: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
    and ub: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
    and int: "\<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
    by auto
  show ?case
  proof (intro allI impI)
    fix s :: real
    assume s: "0 \<le> s" and su: "s \<le> u"
    have sq_nonneg: "0 \<le> X s \<omega> \<bullet> X s \<omega>"
      by (simp add: inner_ge_zero)
    have sq_le: "X s \<omega> \<bullet> X s \<omega> \<le> r\<^sup>2"
      using w inK s by (rule sq_bounded)
    have comp: "0 \<le> set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))
        \<and> set_lebesgue_integral lborel {0..s} (\<lambda>\<sigma>. trace (acov \<sigma> \<omega>))
            \<le> L * real CARD('n) * s"
      using w psd ub int s by (rule compensator_bounded)
    have mono: "L * real CARD('n) * s \<le> L * real CARD('n) * u"
      using su nL_nonneg by (rule mult_left_mono)
    have "0 \<le> r\<^sup>2" by simp
    then show "\<bar>ito_Z X acov s \<omega>\<bar> \<le> r\<^sup>2 + L * real CARD('n) * u"
      unfolding ito_Z_def using sq_nonneg sq_le comp mono by linarith
  qed
qed

end

sublocale ito_stopped_market
  \<subseteq> IV: ito_volatile_market M F X acov k L K x0 tau
      "\<lambda>u _. r\<^sup>2 + L * real CARD('n) * u"
proof -
  have mg: "martingale M F (0 :: real) X"
    by unfold_locales
  show "ito_volatile_market M F X acov k L K x0 tau
      (\<lambda>u _. r\<^sup>2 + L * real CARD('n) * u)"
  proof (intro ito_volatile_market.intro[OF mg]
      ito_volatile_market_axioms.intro)
    show "prob_space M" by (rule prob_space_M)
    show "1 \<le> k" by (rule k_lb)
    show "k < CARD('n)" by (rule k_ub)
    show "1 \<le> L" by (rule L_ge)
    show "AE \<omega> in M. X 0 \<omega> = x0" by (rule X_start)
    show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>" by (rule tau_nonneg')
    show "tau \<in> borel_measurable M" by (rule tau_meas)
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
      by (rule tau_stopping)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K"
      by (rule X_in_K)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
      by (rule acov_psd)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
        eigen_lb (acov s \<omega>) (CARD('n) - k)"
      by (rule acov_eigen_lb)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
      by (rule acov_eigen_ub)
    show "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (rule acov_trace_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        integrable M (\<lambda>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega>)"
      by (rule stopped_sq_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
               (\<lambda>s. trace (acov s \<omega>)))"
      by (rule compensator_integrable)
    show "martingale M F 0 (ito_Z X acov)" by (rule Z_martingale)
    show "AE \<omega> in M. continuous_on {0..} (\<lambda>s. ito_Z X acov s \<omega>)"
      by (rule Z_paths_cont)
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>ito_Z X acov s \<omega>\<bar> \<le> r\<^sup>2 + L * real CARD('n) * u"
      by (rule Z_dominated)
    show "\<And>u. 0 \<le> u \<Longrightarrow>
        integrable M (\<lambda>\<omega>. r\<^sup>2 + L * real CARD('n) * u)"
      by simp
  qed
qed

section \<open>Deterministic horizons need no optional sampling at all\<close>

text \<open>If the horizon is a constant --- the situation of Example 3.1 and of
  the Brownian market --- then the martingale-problem identity is just the
  constancy of the expectation of a martingale, so neither path regularity
  nor a domination hypothesis is required.  This is the cheapest witness
  that the process form of the martingale problem is a usable hypothesis.\<close>

locale ito_const_horizon_market =
  martingale M F 0 X
  for M :: "'a measure"
    and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  fixes acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
    and k :: nat and L :: real
    and K :: "(real^'n) set"
    and x0 :: "real^'n"
    and c :: real
  assumes prob_space_M: "prob_space M"
    and k_lb: "1 \<le> k" and k_ub: "k < CARD('n)" and L_ge: "1 \<le> L"
    and c_nonneg: "0 \<le> c"
    and X_start: "AE \<omega> in M. X 0 \<omega> = x0"
    and X_in_K: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> X s \<omega> \<in> K"
    and acov_psd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> psd (acov s \<omega>)"
    and acov_eigen_lb:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
         eigen_lb (acov s \<omega>) (CARD('n) - k)"
    and acov_eigen_ub:
      "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> eigen_ub (acov s \<omega>) L"
    and acov_trace_integrable:
      "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
         set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
    and stopped_sq_integrable:
      "\<And>t. 0 \<le> t \<Longrightarrow>
         integrable M (\<lambda>\<omega>. X (min t c) \<omega> \<bullet> X (min t c) \<omega>)"
    and compensator_integrable:
      "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
         (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
                (\<lambda>s. trace (acov s \<omega>)))"
    and Z_martingale: "martingale M F 0 (ito_Z X acov)"

sublocale ito_const_horizon_market \<subseteq> prob_space M
  by (rule prob_space_M)

sublocale ito_const_horizon_market \<subseteq> Mc: martingale M F 0 "ito_Z X acov"
  by (rule Z_martingale)

context ito_const_horizon_market
begin

lemma Z_expectation_const:
  assumes v: "0 \<le> v"
  shows "(\<integral>\<omega>. ito_Z X acov v \<omega> \<partial>M) = (\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M)"
proof -
  have sp: "space M \<in> sets (F 0)"
  proof -
    have "space (F (0 :: real)) = space M"
      by (intro space_F) simp
    then show ?thesis
      using sets.top[of "F (0 :: real)"] by simp
  qed
  have space_int: "set_lebesgue_integral M (space M) (ito_Z X acov j)
      = (\<integral>\<omega>. ito_Z X acov j \<omega> \<partial>M)" if "0 \<le> j" for j
    using that by (intro set_integral_space Mc.integrable)
  have e0: "set_lebesgue_integral M (space M) (ito_Z X acov 0)
      = (\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M)"
    by (rule space_int) simp
  have ev: "set_lebesgue_integral M (space M) (ito_Z X acov v)
      = (\<integral>\<omega>. ito_Z X acov v \<omega> \<partial>M)"
    by (rule space_int) (rule v)
  have "set_lebesgue_integral M (space M) (ito_Z X acov 0)
      = set_lebesgue_integral M (space M) (ito_Z X acov v)"
    using sp v by (intro Mc.set_integral_eq) auto
  with e0 ev show ?thesis by simp
qed

lemma Z_zero_expectation_const: "(\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M) = x0 \<bullet> x0"
proof -
  have ae: "AE \<omega> in M. ito_Z X acov 0 \<omega> = x0 \<bullet> x0"
    using X_start
  proof eventually_elim
    case (elim \<omega>)
    have z: "ito_Z X acov 0 \<omega> = X 0 \<omega> \<bullet> X 0 \<omega>
        - set_lebesgue_integral lborel {0..0} (\<lambda>s. trace (acov s \<omega>))"
      unfolding ito_Z_def ..
    have i0: "set_lebesgue_integral lborel {0..0 :: real}
        (\<lambda>s. trace (acov s \<omega>)) = 0"
      by simp
    show ?case
      unfolding z i0 elim by (rule diff_zero)
  qed
  have meas: "ito_Z X acov 0 \<in> borel_measurable M"
    using Mc.integrable[of 0] by (auto intro: borel_measurable_integrable)
  have "(\<integral>\<omega>. ito_Z X acov 0 \<omega> \<partial>M) = (\<integral>\<omega>. x0 \<bullet> x0 \<partial>M)"
    using meas ae by (intro integral_cong_AE) auto
  then show ?thesis
    by (simp add: prob_space)
qed

theorem const_dynkin_quadratic:
  assumes t: "0 \<le> t"
  shows "(\<integral>\<omega>. X (min t c) \<omega> \<bullet> X (min t c) \<omega> \<partial>M)
       - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t c}
                (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
       = x0 \<bullet> x0"
proof -
  have tc: "0 \<le> min t c"
    using t c_nonneg by simp
  have "(\<integral>\<omega>. ito_Z X acov (min t c) \<omega> \<partial>M)
      = (\<integral>\<omega>. X (min t c) \<omega> \<bullet> X (min t c) \<omega> \<partial>M)
        - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t c}
                 (\<lambda>s. trace (acov s \<omega>)) \<partial>M)"
    unfolding ito_Z_def
    by (intro Bochner_Integration.integral_diff stopped_sq_integrable[OF t]
        compensator_integrable[OF t])
  moreover have "(\<integral>\<omega>. ito_Z X acov (min t c) \<omega> \<partial>M) = x0 \<bullet> x0"
    using Z_expectation_const[OF tc] Z_zero_expectation_const by simp
  ultimately show ?thesis by simp
qed

end

sublocale ito_const_horizon_market
  \<subseteq> CV: sufficiently_volatile_market M F X acov k L K x0 "\<lambda>_. c"
proof -
  have mg: "martingale M F (0 :: real) X"
    by unfold_locales
  show "sufficiently_volatile_market M F X acov k L K x0 (\<lambda>_. c)"
  proof (intro sufficiently_volatile_market.intro[OF mg]
      sufficiently_volatile_market_axioms.intro)
    show "prob_space M" by (rule prob_space_M)
    show "1 \<le> k" by (rule k_lb)
    show "k < CARD('n)" by (rule k_ub)
    show "1 \<le> L" by (rule L_ge)
    show "AE \<omega> in M. X 0 \<omega> = x0" by (rule X_start)
    show "AE \<omega> in M. 0 \<le> c" using c_nonneg by simp
    show "(\<lambda>_. c) \<in> borel_measurable M" by simp
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> X s \<omega> \<in> K"
      by (rule X_in_K)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> psd (acov s \<omega>)"
      by (rule acov_psd)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
        eigen_lb (acov s \<omega>) (CARD('n) - k)"
      by (rule acov_eigen_lb)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> eigen_ub (acov s \<omega>) L"
      by (rule acov_eigen_ub)
    show "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (rule acov_trace_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        integrable M (\<lambda>\<omega>. X (min t c) \<omega> \<bullet> X (min t c) \<omega>)"
      by (rule stopped_sq_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
               (\<lambda>s. trace (acov s \<omega>)))"
      by (rule compensator_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        (\<integral>\<omega>. X (min t c) \<omega> \<bullet> X (min t c) \<omega> \<partial>M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t c}
                   (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
        = x0 \<bullet> x0"
      by (rule const_dynkin_quadratic)
  qed
qed

text \<open>The final statement of this development: for a stopped market, the
  martingale property of the process of Ito's formula alone (with continuous
  paths) yields the exit-time bound of Lemma 2.1, with no
  martingale-problem identity assumed anywhere.\<close>

theorem (in ito_stopped_market) stopped_expected_time_bound:
  assumes t: "0 \<le> t"
  shows "real (CARD('n) - k) * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> r\<^sup>2 - x0 \<bullet> x0"
  using K_ball t by (rule IV.SV.expected_stopped_time_bound)

section \<open>The process form of the martingale problem is inhabited\<close>

text \<open>Ito's formula for the test function \<open>|x|\<^sup>2\<close> is a theorem for the
  constructed Brownian motion (\<open>martingale_bm_square\<close> of
  Brownian\_Market), and for \<open>acov = mat 1\<close> the process it is about is
  literally \<open>ito_Z\<close>.  Hence the Brownian market with a deterministic
  horizon inhabits \<open>ito_const_horizon_market\<close>: every assumption of that
  locale is proved for this instance, so the exit-time bound of Lemma 2.1
  follows from the martingale problem in process form with nothing
  assumed.\<close>

theorem Brownian_ito_const_horizon_market:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and c: "0 \<le> c"
    and K: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> bmX x0 s \<omega> \<in> K"
  shows "ito_const_horizon_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) (bmX x0)
    (\<lambda>_ _. mat 1) k L K x0 c"
proof (intro ito_const_horizon_market.intro
    ito_const_horizon_market_axioms.intro)
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0 (bmX x0)"
    by (rule martingale_bmX)
  show "prob_space ?M" by simp
  show "1 \<le> k" "k < CARD('n)" "1 \<le> L" "0 \<le> c" by fact+
  show "AE \<omega> in ?M. bmX x0 0 \<omega> = x0" by (rule bmX_start)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> bmX x0 s \<omega> \<in> K"
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
  show "AE \<omega> in ?M. \<forall>t :: real. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
    using ti by (intro AE_I2) blast
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>)"
    using c by (intro bmX_sq_integrable) simp
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (rule BMP.integrable_const)
  have Zeq: "ito_Z (bmX x0) (\<lambda>_ _. mat 1 :: real^'n^'n)
      = (\<lambda>t \<omega>. bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>
          - set_lebesgue_integral lborel {0..t}
              (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (intro ext) (simp add: ito_Z_def)
  show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0
      (ito_Z (bmX x0) (\<lambda>_ _. mat 1))"
    unfolding Zeq by (rule martingale_bm_square)
qed

text \<open>Specialised to the planar market with \<open>k = L = 1\<close>, horizon \<open>1\<close> and
  start \<open>0\<close>, the statement has no hypotheses at all.\<close>

theorem ito_const_horizon_market_nonvacuous:
  "ito_const_horizon_market
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX 0)) (bmX (0 :: real^2))
    (\<lambda>_ _. mat 1) 1 1 UNIV 0 1"
  by (rule Brownian_ito_const_horizon_market) simp_all

end
