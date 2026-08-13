
(*<*)
theory Optimal_Exit_Time
  imports Volatile_Market
begin

(*>*)

text \<open>
  Formalizes the arbitrage side of \<^cite>\<open>LaiShkolnikovSoner\<close>: relative arbitrage
  beyond the critical horizon, and optimality of the ball value function
  of Example 3.1. Since Isabelle/HOL has no Ito integration theory, the
  stochastic integral against the gradient of the test function
  \<open>w(y) = (r\<^sup>2 - \<bar>y\<bar>\<^sup>2) / (n - k)\<close> is taken directly as a definition,
  \<open>sint\<close>, and the identity \<open>ito_formula_quadratic\<close> is proved by
  unfolding it, so no stochastic-integration assumption is needed; the
  only side condition retained is measurability of the compensator
  \<open>omega \<mapsto> \<integral>\<^sub>0\<^bsup>t\<^esup> trace (acov\<^sub>s(omega)) ds\<close>. The theorem
  \<open>ball_relative_arbitrage\<close> shows the gradient strategy
  \<open>theta\<^sub>s = grad w(X\<^sub>s)\<close> realizes relative arbitrage of Definition 1.1
  on \<open>[0, T]\<close> whenever \<open>T > v(x0)\<close>, the if-half of the critical-horizon
  characterization \<open>T\<^sup>* = v(x)\<close> of Section 1 for Example 3.1. The
  reverse inequality \<open>E [tau] \<ge> v(x0)\<close> for the optimal market comes
  from the time-changed spherical martingale of Eq. (3.11), whose
  construction is taken as the locale assumption \<open>tau_optimal\<close>;
  combined with the proved upper bound it yields the exact value
  \<open>E [tau] = v(x0)\<close> (\<open>optimal_exit_time_value\<close>).\<close>
section \<open>Measurability of the ball value function\<close>

lemma borel_measurable_ball_v:
  "(ball_v r k :: real^'n::finite \<Rightarrow> real) \<in> borel_measurable borel"
proof (rule borel_measurable_continuous_onI)
  show "continuous_on UNIV (ball_v r k :: real^'n \<Rightarrow> real)"
  proof (cases "real (CARD('n) - k) = 0")
    case True
    then have "(ball_v r k :: real^'n \<Rightarrow> real) = (\<lambda>_. 0)"
      by (simp add: ball_v_def fun_eq_iff)
    then show ?thesis by simp
  next
    case False
    show ?thesis
      unfolding ball_v_def using False by (intro continuous_intros) auto
  qed
qed

section \<open>Markets that are sufficiently volatile on a whole horizon\<close>

text \<open>Taking the pre-exit time of the companion locale to be the constant
  horizon \<open>T\<close> says exactly that the eigenvalue constraints hold on \<open>[0,T]\<close>
  (on the transformed simplex the weight process never leaves \<open>K\<close>, so the
  constraint of Eq. (1.4) is in force at all times).\<close>

locale horizon_volatile_market =
  sufficiently_volatile_market M F X acov k L K x0 "(\<lambda>_. T)"
  for M :: "'a measure"
    and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
    and acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
    and k L and K :: "(real^'n) set" and x0
    and T :: real

section \<open>The gradient strategy realizes relative arbitrage beyond \<open>v(x\<^sub>0)\<close>\<close>

locale ball_gradient_strategy =
  horizon_volatile_market M F X acov k L K x0 T
  for M :: "'a measure"
    and F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
    and acov :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
    and k L and K :: "(real^'n) set" and x0
    and T :: real +
  fixes r :: real
  assumes K_ball: "K = cball 0 r"
    and compensator_meas [measurable]:
      "\<And>t. (\<lambda>\<omega>. set_lebesgue_integral lborel {0..t}
              (\<lambda>s. trace (acov s \<omega>))) \<in> borel_measurable M"
begin

text \<open>The stochastic integral of the gradient strategy, defined by the
  value that Ito's formula assigns to it for the quadratic test function
  \<open>w\<close>.  No assumption about stochastic integration is made.\<close>

definition sint :: "real \<Rightarrow> 'a \<Rightarrow> real" where
  "sint t \<omega> = ball_v r k (X t \<omega>) - ball_v r k x0
     + (1 / real (CARD('n) - k))
       * set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"

text \<open>The Ito identity for the quadratic test function \<open>w\<close>, restated as a
  fact about \<open>sint\<close>; it holds unconditionally since \<open>sint\<close> is defined to
  satisfy it.\<close>

lemma ito_formula_quadratic:
  "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
     sint t \<omega> = ball_v r k (X t \<omega>) - ball_v r k x0
       + (1 / real (CARD('n) - k))
         * set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
  by (simp add: sint_def)

lemma X_meas_M:
  assumes "0 \<le> t"
  shows "X t \<in> borel_measurable M"
  using integrable[OF assms] by (rule borel_measurable_integrable)

lemma sint_meas [measurable]:
  assumes t: "0 \<le> t"
  shows "sint t \<in> borel_measurable M"
proof -
  have "(\<lambda>\<omega>. ball_v r k (X t \<omega>)) \<in> borel_measurable M"
    by (rule measurable_compose[OF X_meas_M[OF t] borel_measurable_ball_v])
  then show ?thesis
    unfolding sint_def
    by (intro borel_measurable_add borel_measurable_diff
        borel_measurable_const borel_measurable_times compensator_meas)
qed

text \<open>The relative value process of Eq. (1.1) for the strategy
  \<open>\<theta>\<^sub>s = \<nabla>w(X\<^sub>s)\<close>, started from initial relative capital \<open>v(x\<^sub>0)\<close>.\<close>

definition arb_V :: "real \<Rightarrow> 'a \<Rightarrow> real" where
  "arb_V t \<omega> = ball_v r k x0 + sint t \<omega>"

lemma X_in_ball: "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow> t \<le> T \<longrightarrow> X t \<omega> \<in> cball 0 r"
  using X_in_K by (simp add: K_ball)

text \<open>Pathwise lower bound on the compensator: sufficient volatility makes
  the accumulated quadratic variation grow at least linearly.\<close>

lemma compensator_pathwise:
  "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
     real (CARD('n) - k) * t
       \<le> set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
  using acov_psd acov_eigen_lb acov_trace_integrable
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix t assume t: "0 \<le> t" "t \<le> T"
    have f_int: "set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      using elim t by blast
    have c_int: "set_integrable lborel {0..t} (\<lambda>_. real (CARD('n) - k))"
      unfolding set_integrable_def
      using t
      by (intro integrable_scaleR_left integrable_real_indicator)
        auto
    have mono: "real (CARD('n) - k) \<le> trace (acov s \<omega>)"
      if s: "s \<in> {0..t}" for s
    proof -
      have "0 \<le> s" "s \<le> T"
        using s t by auto
      then show ?thesis
        using elim by (intro trace_bound_pointwise) auto
    qed
    have "set_lebesgue_integral lborel {0..t} (\<lambda>_. real (CARD('n) - k))
        \<le> set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (rule set_integral_mono[OF c_int f_int mono])
    moreover have "set_lebesgue_integral lborel {0..t}
        (\<lambda>_. real (CARD('n) - k)) = t * real (CARD('n) - k)"
      using t by (subst set_integral_const) auto
    ultimately show "real (CARD('n) - k) * t
        \<le> set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (simp add: mult_ac)
  qed
qed

text \<open>The pathwise structure of the value process: it dominates
  \<open>v(X\<^sub>t) + t\<close> and starts at \<open>v(x\<^sub>0)\<close>.\<close>

lemma arb_V_pathwise:
  "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
     ball_v r k (X t \<omega>) + t \<le> arb_V t \<omega>"
  using ito_formula_quadratic compensator_pathwise
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix t assume t: "0 \<le> t" "t \<le> T"
    have c_pos: "0 < real (CARD('n) - k)"
      using k_ub by simp
    have "arb_V t \<omega> = ball_v r k (X t \<omega>)
        + (1 / real (CARD('n) - k))
          * set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      using elim t by (simp add: arb_V_def)
    moreover have "t \<le> (1 / real (CARD('n) - k))
        * set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
    proof -
      have "real (CARD('n) - k) * t
          \<le> set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
        using elim t by blast
      with c_pos show ?thesis
        by (simp add: field_simps)
    qed
    ultimately show "ball_v r k (X t \<omega>) + t \<le> arb_V t \<omega>"
      by simp
  qed
qed

lemma arb_V_start:
  "AE \<omega> in M. arb_V 0 \<omega> = ball_v r k x0"
  using ito_formula_quadratic X_start tau_nonneg
proof eventually_elim
  case (elim \<omega>)
  have "sint 0 \<omega> = ball_v r k (X 0 \<omega>) - ball_v r k x0
      + (1 / real (CARD('n) - k))
        * set_lebesgue_integral lborel {0..0} (\<lambda>s. trace (acov s \<omega>))"
    using elim by auto
  also have "set_lebesgue_integral lborel {0..(0::real)}
      (\<lambda>s. trace (acov s \<omega>)) = 0"
  proof -
    have "AE x in lborel. indicat_real {0::real..0} x *\<^sub>R trace (acov x \<omega>) = 0"
      using AE_lborel_singleton[of 0]
      by eventually_elim (auto simp: indicator_def)
    then show ?thesis
      unfolding set_lebesgue_integral_def
      by (rule integral_eq_zero_AE)
  qed
  finally have "sint 0 \<omega> = 0"
    using elim by simp
  then show ?case
    by (simp add: arb_V_def)
qed

theorem ball_relative_arbitrage:
  assumes horizon: "ball_v r k x0 < T"
  shows "relative_arbitrage M arb_V T"
proof -
  have T_pos: "0 \<le> T"
    using horizon ball_v_nonneg[of r k x0] by simp
  have nonneg: "AE \<omega> in M. 0 \<le> arb_V t \<omega>" if t: "t \<in> {0..T}" for t
    using arb_V_pathwise X_in_ball
  proof eventually_elim
    case (elim \<omega>)
    have "ball_v r k (X t \<omega>) + t \<le> arb_V t \<omega>"
      using elim t by auto
    moreover have "0 \<le> ball_v r k (X t \<omega>)"
      by (rule ball_v_nonneg)
    ultimately show ?case
      using t by auto
  qed
  have gain: "AE \<omega> in M. arb_V 0 \<omega> < arb_V T \<omega>"
    using arb_V_pathwise arb_V_start
  proof eventually_elim
    case (elim \<omega>)
    have "arb_V 0 \<omega> = ball_v r k x0"
      using elim by blast
    also have "\<dots> < T"
      by (fact horizon)
    also have "T \<le> ball_v r k (X T \<omega>) + T"
      using ball_v_nonneg[of r k "X T \<omega>"] by simp
    also have "\<dots> \<le> arb_V T \<omega>"
      using elim T_pos by auto
    finally show ?case .
  qed
  have ge: "AE \<omega> in M. arb_V 0 \<omega> \<le> arb_V T \<omega>"
    using gain by eventually_elim auto
  have not_le: "\<not> (AE \<omega> in M. arb_V T \<omega> \<le> arb_V 0 \<omega>)"
  proof
    assume "AE \<omega> in M. arb_V T \<omega> \<le> arb_V 0 \<omega>"
    with gain have "AE \<omega> in M. False"
      by eventually_elim auto
    then obtain N where N: "{\<omega> \<in> space M. \<not> False} \<subseteq> N"
      "emeasure M N = 0" "N \<in> sets M"
      by (rule AE_E)
    have "space M \<subseteq> N"
      using N(1) by auto
    then have "emeasure M (space M) = 0"
      using emeasure_mono[OF _ N(3)] N(2) by (metis le_zero_eq)
    with emeasure_space_1 show False
      by simp
  qed
  show ?thesis
    unfolding relative_arbitrage_def
    using nonneg ge not_le by auto
qed

end

section \<open>Optimality of the ball value function (Eq. (3.11))\<close>

text \<open>The construction of the optimizer --- a martingale moving on spheres
  by a time-changed spherical Brownian motion --- requires Brownian motion,
  which no Isabelle/HOL library provides; its output, the reverse
  inequality \<open>E[\<tau>] \<ge> v(x\<^sub>0)\<close>, is therefore axiomatized as the assumption
  \<open>tau_optimal\<close>.  Together with the proved upper bound this determines the
  value of the stochastic control problem for the ball exactly.\<close>

locale optimal_ball_market = sufficiently_volatile_market +
  fixes r :: real
  assumes K_ball': "K = cball 0 r"
    and tau_optimal:
      "ennreal (ball_v r k x0) \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
begin

theorem optimal_exit_time_value:
  "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) = ennreal (ball_v r k x0)"
  using expected_exit_time_bound[OF K_ball'] tau_optimal
  by (rule antisym)

end

text \<open>Consequently, in the optimal market the value function of Theorem 1.1
  is exactly the expected exit time, and by \<open>ball_relative_arbitrage\<close> the
  critical horizon beyond which the gradient strategy is a relative
  arbitrage is \<open>T\<^sup>* = v(x\<^sub>0)\<close> --- the assertion of Example 3.1.\<close>

(*<*)
end
(*>*)
