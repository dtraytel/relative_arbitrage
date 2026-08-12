

(*<*)
theory Random_Walk_Market
  imports
    Relative_Arbitrage_Discrete
    "Martingales.Example_Coin_Toss"
begin

(*>*)

text \<open>
  A concrete sufficiently volatile discrete market: the simple
             symmetric random walk in the plane, stopped when it leaves a
             ball.

    Everything here is a theorem.  The market instantiates the locale
    \<open>discrete_volatile_stopped_market\<close> of \<open>Relative_Arbitrage_Discrete\<close>, so the
    discrete-time development of Example 3.1 is non-vacuous, and the
    exit-time bound of Example 3.1 specializes to an assumption-free
    statement about the random walk:

      E[exit time from the ball of radius m+1, capped at N] <= (m+1)^2.

    The coin-tossing probability space, the fortune process and its
    martingale property are taken from the AFP entry Martingales
    (\<open>Example_Coin_Toss\<close>); only the centring, the embedding into the plane
    and the stopping time are new.\<close>
section \<open>The centred fortune process\<close>

abbreviation coin :: "bool stream measure" where
  "coin \<equiv> bernoulli_stream (1/2)"

abbreviation coin_filtration :: "nat \<Rightarrow> bool stream measure" where
  "coin_filtration \<equiv> toss_filtration (1/2)"

lemma prob_space_coin: "prob_space coin"
  unfolding bernoulli_stream_def
  by (simp add: measure_pmf.prob_space_axioms prob_space.prob_space_stream_space)

lemma nat_sigma_finite_coin:
  "nat_sigma_finite_filtered_measure coin coin_filtration"
  by intro_locales

lemma filtered_measure_coin: "filtered_measure coin coin_filtration (0::nat)"
  by intro_locales

lemma space_coin_filtration [simp]: "space (coin_filtration n) = UNIV"
  using bernoulli_stream_natural_filtration.subalg[of n]
  by (simp add: subalgebra_def)

lemma fortune_measurable_F:
  assumes "j \<le> n"
  shows "fortune j \<in> borel_measurable (coin_filtration n)"
  using assms by (intro fortune.adaptedD) auto

text \<open>The fortune process of the AFP example starts at a coin toss; we
  centre it so that the process starts at the origin.\<close>

definition walk :: "nat \<Rightarrow> bool stream \<Rightarrow> real" where
  "walk n s = fortune n s - fortune 0 s"

lemma walk_0 [simp]: "walk 0 s = 0"
  by (simp add: walk_def)

lemma walk_Suc: "walk (Suc n) s = walk n s + toss (Suc n) s"
  by (simp add: walk_def fortune_Suc)

lemma walk_incr_abs: "\<bar>walk (Suc n) s - walk n s\<bar> = 1"
  by (simp add: walk_Suc toss_def)

lemma walk_incr_sq: "(walk (Suc n) s - walk n s)\<^sup>2 = 1"
  using walk_incr_abs[of n s] by (metis power2_abs one_power2)

lemma walk_bound: "\<bar>walk n s\<bar> \<le> real n + 2"
proof -
  have "\<bar>walk n s\<bar> \<le> \<bar>fortune n s\<bar> + \<bar>fortune 0 s\<bar>"
    by (simp add: walk_def)
  moreover have "\<bar>fortune n s\<bar> \<le> real (Suc n)" and "\<bar>fortune 0 s\<bar> \<le> real (Suc 0)"
    using fortune_bound[of n s] fortune_bound[of 0 s] by simp_all
  ultimately show ?thesis by simp
qed

lemma walk_random_variable [measurable]: "walk n \<in> borel_measurable coin"
  unfolding walk_def using fortune.random_variable by measurable

lemma integrable_walk: "integrable coin (walk n)"
  unfolding walk_def
  by (intro Bochner_Integration.integrable_diff integrable_fortune)

section \<open>The centred walk is a martingale\<close>

lemma adapted_walk: "adapted_process coin coin_filtration 0 walk"
proof (intro adapted_process.intro[OF filtered_measure_coin]
    adapted_process_axioms.intro)
  fix i :: nat assume "0 \<le> i"
  have 1: "fortune i \<in> borel_measurable (coin_filtration i)"
    by (intro fortune_measurable_F) simp
  have 2: "fortune 0 \<in> borel_measurable (coin_filtration i)"
    by (intro fortune_measurable_F) simp
  show "walk i \<in> borel_measurable (coin_filtration i)"
    unfolding walk_def using 1 2 by measurable
qed

theorem martingale_walk: "martingale coin coin_filtration 0 walk"
proof (rule bernoulli_stream_natural_filtration.martingale_of_cond_exp_diff_Suc_eq_zero)
  show "adapted_process coin coin_filtration 0 walk"
    by (rule adapted_walk)
  show "\<And>i. integrable coin (walk i)"
    by (rule integrable_walk)
next
  fix i :: nat
  interpret Fm: martingale coin coin_filtration 0 fortune
    by (rule fortune_martingale) simp
  have fun_eq: "(\<lambda>s. walk (Suc i) s - walk i s)
      = (\<lambda>s. fortune (Suc i) s - fortune i s)"
    by (simp add: walk_def fun_eq_iff)
  show "AE s in coin.
      cond_exp coin (coin_filtration i) (\<lambda>s. walk (Suc i) s - walk i s) s = 0"
    unfolding fun_eq by (rule Fm.cond_exp_diff_eq_zero) auto
qed

section \<open>The walk as a planar market\<close>

text \<open>The market moves along the first coordinate axis of the plane; both
  coordinates are square-integrable martingales, and every step carries
  exactly the volatility \<open>CARD(2) - 1 = 1\<close> that Eq. (1.4) demands.\<close>

definition rw :: "nat \<Rightarrow> bool stream \<Rightarrow> real^2" where
  "rw n s = walk n s *\<^sub>R axis 1 1"

lemma rw_0 [simp]: "rw 0 s = 0"
  by (simp add: rw_def)

lemma rw_component: "rw n s $ i = walk n s * (axis (1::2) (1::real) $ i)"
  by (simp add: rw_def)

lemma card_two [simp]: "CARD(2) = 2"
  by simp

lemma axis_inner_self: "(axis (1::2) (1::real)) \<bullet> (axis 1 1) = 1"
  by (simp add: inner_axis)

lemma rw_incr: "rw (Suc n) s - rw n s = (walk (Suc n) s - walk n s) *\<^sub>R axis 1 1"
  by (simp add: rw_def scaleR_diff_left)

lemma rw_incr_sq:
  "(rw (Suc n) s - rw n s) \<bullet> (rw (Suc n) s - rw n s) = 1"
proof -
  have "(rw (Suc n) s - rw n s) \<bullet> (rw (Suc n) s - rw n s)
      = ((walk (Suc n) s - walk n s) * (walk (Suc n) s - walk n s))
        * ((axis (1::2) (1::real)) \<bullet> axis 1 1)"
    unfolding rw_incr by simp
  also have "\<dots> = 1"
    using walk_incr_sq[of n s]
    by (simp add: axis_inner_self power2_eq_square)
  finally show ?thesis .
qed

lemma rw_comp_martingale: "martingale coin coin_filtration 0 (\<lambda>n s. rw n s $ i)"
proof (cases "i = 1")
  case True
  have "(\<lambda>n s. rw n s $ i) = walk"
    using True by (simp add: fun_eq_iff rw_component)
  then show ?thesis
    using martingale_walk by simp
next
  case False
  have "(\<lambda>n s. rw n s $ i) = (\<lambda>_ _. 0)"
    using False by (simp add: fun_eq_iff rw_component axis_def)
  then show ?thesis
    using bernoulli_stream_natural_filtration.martingale_const by simp
qed

lemma rw_comp_sq_integrable: "integrable coin (\<lambda>s. (rw n s $ i)\<^sup>2)"
proof -
  have meas: "(\<lambda>s. (rw n s $ i)\<^sup>2) \<in> borel_measurable coin"
    by (simp add: rw_component)
  have bound: "\<bar>(rw n s $ i)\<^sup>2\<bar> \<le> (real n + 2)\<^sup>2" for s
  proof -
    have le: "\<bar>rw n s $ i\<bar> \<le> real n + 2"
    proof -
      have "\<bar>rw n s $ i\<bar> \<le> \<bar>walk n s\<bar>"
        by (cases "i = 1") (simp_all add: rw_component axis_def)
      also have "\<dots> \<le> real n + 2"
        by (rule walk_bound)
      finally show ?thesis .
    qed
    have "\<bar>(rw n s $ i)\<^sup>2\<bar> = \<bar>rw n s $ i\<bar>\<^sup>2"
      by simp
    also have "\<dots> \<le> (real n + 2)\<^sup>2"
      using le by (intro power_mono) simp_all
    finally show ?thesis .
  qed
  show ?thesis
    by (rule Bochner_Integration.integrable_bound[
          OF integrable_const[of _ "(real n + 2)\<^sup>2"] meas])
      (use bound in \<open>auto intro!: AE_I2\<close>)
qed

theorem discrete_vec_martingale_rw:
  "discrete_vec_martingale coin coin_filtration rw"
  by (intro discrete_vec_martingale.intro[OF nat_sigma_finite_coin]
      discrete_vec_martingale_axioms.intro rw_comp_martingale rw_comp_sq_integrable)

section \<open>The exit time from a ball\<close>

text \<open>The first time the walk reaches distance \<open>m\<close> from the origin,
  capped at the horizon \<open>N\<close> so that the definition is total and the
  event of having stopped is observable at each time.\<close>

definition exitN :: "nat \<Rightarrow> nat \<Rightarrow> bool stream \<Rightarrow> nat" where
  "exitN m N s = (LEAST n. n = N \<or> real m \<le> \<bar>walk n s\<bar>)"

lemma exitN_witness: "exitN m N s = N \<or> real m \<le> \<bar>walk (exitN m N s) s\<bar>"
  unfolding exitN_def
  by (rule LeastI[of "\<lambda>n. n = N \<or> real m \<le> \<bar>walk n s\<bar>" N]) simp

lemma exitN_le: "exitN m N s \<le> N"
  unfolding exitN_def by (intro Least_le) simp

lemma exitN_before:
  assumes "n < exitN m N s"
  shows "\<bar>walk n s\<bar> < real m"
  using not_less_Least[OF assms[unfolded exitN_def]] by auto

lemma exitN_le_iff: "exitN m N s \<le> n \<longleftrightarrow> (\<exists>j\<le>n. j = N \<or> real m \<le> \<bar>walk j s\<bar>)"
proof
  assume "exitN m N s \<le> n"
  then show "\<exists>j\<le>n. j = N \<or> real m \<le> \<bar>walk j s\<bar>"
    using exitN_witness[of m N s] by blast
next
  assume "\<exists>j\<le>n. j = N \<or> real m \<le> \<bar>walk j s\<bar>"
  then obtain j where j: "j \<le> n" "j = N \<or> real m \<le> \<bar>walk j s\<bar>"
    by blast
  have "exitN m N s \<le> j"
    unfolding exitN_def using j(2) by (intro Least_le)
  with j(1) show "exitN m N s \<le> n" by simp
qed

text \<open>Up to the exit time the walk stays in the ball of radius \<open>m + 1\<close>:
  before the exit time it is at distance less than \<open>m\<close>, and one step
  moves it by exactly one.\<close>

lemma walk_bounded_upto_exitN:
  assumes "n \<le> exitN m N s"
  shows "\<bar>walk n s\<bar> \<le> real m + 1"
proof (cases "n < exitN m N s")
  case True
  then show ?thesis
    using exitN_before[OF True] by simp
next
  case False
  with assms have n_eq: "n = exitN m N s" by simp
  show ?thesis
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have "j < exitN m N s"
      using n_eq Suc by simp
    then have "\<bar>walk j s\<bar> < real m"
      by (rule exitN_before)
    moreover have "\<bar>walk n s\<bar> \<le> \<bar>walk j s\<bar> + 1"
      using walk_incr_abs[of j s] Suc by simp
    ultimately show ?thesis by simp
  qed
qed

lemma walk_measurable_F:
  assumes "j \<le> n"
  shows "walk j \<in> borel_measurable (coin_filtration n)"
proof -
  have 1: "fortune j \<in> borel_measurable (coin_filtration n)"
    by (intro fortune_measurable_F assms)
  have 2: "fortune 0 \<in> borel_measurable (coin_filtration n)"
    by (intro fortune_measurable_F) simp
  show ?thesis
    unfolding walk_def using 1 2 by measurable
qed

lemma walk_event_sets:
  assumes "j \<le> n"
  shows "{s. real m \<le> \<bar>walk j s\<bar>} \<in> sets (coin_filtration n)"
proof -
  have "walk j \<in> borel_measurable (coin_filtration n)"
    by (intro walk_measurable_F assms)
  then have "{s \<in> space (coin_filtration n). real m \<le> \<bar>walk j s\<bar>}
      \<in> sets (coin_filtration n)"
    by measurable
  then show ?thesis by simp
qed

theorem exitN_stopping_time:
  "{s \<in> space coin. exitN m N s \<le> n} \<in> sets (coin_filtration n)"
proof (cases "N \<le> n")
  case True
  have "{s \<in> space coin. exitN m N s \<le> n} = space (coin_filtration n)"
    using True exitN_le[of m N] by (auto intro: le_trans)
  then show ?thesis
    using sets.top[of "coin_filtration n"] by simp
next
  case False
  have eq: "{s \<in> space coin. exitN m N s \<le> n}
      = (\<Union>j\<in>{..n}. {s. real m \<le> \<bar>walk j s\<bar>})"
    using False by (auto simp: exitN_le_iff)
  have "(\<Union>j\<in>{..n}. {s. real m \<le> \<bar>walk j s\<bar>}) \<in> sets (coin_filtration n)"
  proof (rule sets.finite_UN)
    show "finite {..n}" by simp
    fix j assume "j \<in> {..n}"
    then show "{s. real m \<le> \<bar>walk j s\<bar>} \<in> sets (coin_filtration n)"
      by (intro walk_event_sets) simp
  qed
  then show ?thesis
    unfolding eq .
qed

theorem discrete_vec_stopped_martingale_rw:
  "discrete_vec_stopped_martingale coin coin_filtration rw (exitN m N)"
  by (intro discrete_vec_stopped_martingale.intro[OF discrete_vec_martingale_rw]
      discrete_vec_stopped_martingale_axioms.intro exitN_stopping_time)

section \<open>The random walk is a sufficiently volatile market\<close>

theorem random_walk_volatile_market:
  "discrete_volatile_stopped_market coin coin_filtration rw
     1 (real m + 1) 0 N (exitN m N)"
proof (intro discrete_volatile_stopped_market.intro
    discrete_volatile_base.intro[OF discrete_vec_martingale_rw]
    discrete_volatile_base_axioms.intro
    discrete_vec_stopped_martingale_rw
    discrete_volatile_stopped_market_axioms.intro)
  show "prob_space coin"
    by (rule prob_space_coin)
  show "(1 :: nat) \<le> 1" by simp
  show "(1 :: nat) < CARD(2)" by simp
  show "AE s in coin. rw 0 s = 0"
    by simp
  show "AE s in coin. \<forall>j. j < N \<longrightarrow>
      real (CARD(2) - 1) \<le> (rw (Suc j) s - rw j s) \<bullet> (rw (Suc j) s - rw j s)"
    by (intro AE_I2 allI impI) (simp add: rw_incr_sq)
  show "AE s in coin. \<forall>n. n \<le> N \<longrightarrow>
      rw (min n (exitN m N s)) s \<in> cball 0 (real m + 1)"
  proof (intro AE_I2 allI impI)
    fix s :: "bool stream" and n :: nat
    assume "n \<le> N"
    have "\<bar>walk (min n (exitN m N s)) s\<bar> \<le> real m + 1"
      by (rule walk_bounded_upto_exitN[of "min n (exitN m N s)" m N s]) simp
    then have "norm (rw (min n (exitN m N s)) s) \<le> real m + 1"
      by (simp add: rw_def)
    then show "rw (min n (exitN m N s)) s \<in> cball 0 (real m + 1)"
      by (simp add: dist_norm)
  qed
qed

text \<open>Example 3.1 for the random walk, with no assumption at all: the
  expected exit time from the ball of radius \<open>m + 1\<close> (capped at the
  horizon) is at most \<open>(m + 1)\<^sup>2\<close>, the value \<open>v(0)\<close> of Eq. (3.9) for
  \<open>k = 1\<close> in the plane.\<close>

corollary random_walk_expected_exit_time:
  "(\<integral>s. real (min N (exitN m N s)) \<partial>coin) \<le> (real m + 1)\<^sup>2"
proof -
  have v: "ball_v (real m + 1) 1 (0 :: real^2) = (real m + 1)\<^sup>2"
    by (simp add: ball_v_def)
  have "(\<integral>s. real (min N (exitN m N s)) \<partial>coin)
      \<le> ball_v (real m + 1) 1 (0 :: real^2)"
    by (rule discrete_volatile_stopped_market.expected_stopped_horizon_le_ball_v[
          OF random_walk_volatile_market])
  with v show ?thesis by simp
qed

corollary random_walk_expected_exit_time':
  "(\<integral>s. real (exitN m N s) \<partial>coin) \<le> (real m + 1)\<^sup>2"
proof -
  have "(\<lambda>s. real (min N (exitN m N s))) = (\<lambda>s. real (exitN m N s))"
    by (rule ext) (simp add: min_absorb2 exitN_le)
  then show ?thesis
    using random_walk_expected_exit_time[of N m] by simp
qed

section \<open>Sharpness of the bound\<close>

text \<open>Every step of the walk contributes exactly one to the quadratic
  variation, so the stopped Dynkin identity of @{theory Relative_Arbitrage_Unused.Relative_Arbitrage_Discrete}
  turns into an EQUALITY between the expected exit time and the expected
  squared displacement.  Since the walk sits at distance at least \<open>m\<close> from
  the origin whenever it has left the ball, the bound \<open>v(0)\<close> of Example 3.1
  is attained up to the unit step size --- this is the discrete counterpart
  of the optimality statement of Eq. (3.11).\<close>

lemma qvar_vec_rw: "qvar_vec rw n s = real n"
  unfolding qvar_vec_def by (simp add: rw_incr_sq)

theorem random_walk_exit_time_eq_expected_sq:
  "(\<integral>s. real (min N (exitN m N s)) \<partial>coin)
     = (\<integral>s. rw (min N (exitN m N s)) s \<bullet> rw (min N (exitN m N s)) s \<partial>coin)"
proof -
  have "(\<integral>s. rw (min N (exitN m N s)) s \<bullet> rw (min N (exitN m N s)) s \<partial>coin)
      = (\<integral>s. rw 0 s \<bullet> rw 0 s \<partial>coin)
        + (\<integral>s. qvar_vec rw (min N (exitN m N s)) s \<partial>coin)"
    by (rule discrete_vec_stopped_martingale.expectation_norm_sq_qvar_vec_stopped[
          OF discrete_vec_stopped_martingale_rw])
  also have "(\<integral>s. rw 0 s \<bullet> rw 0 s \<partial>coin) = 0"
    by simp
  also have "(\<integral>s. qvar_vec rw (min N (exitN m N s)) s \<partial>coin)
      = (\<integral>s. real (min N (exitN m N s)) \<partial>coin)"
    by (simp add: qvar_vec_rw)
  finally show ?thesis by simp
qed

lemma norm_rw_at_exitN:
  assumes "exitN m N s < N"
  shows "real m \<le> \<bar>walk (exitN m N s) s\<bar>"
  using exitN_witness[of m N s] assms by auto

text \<open>A numerical check of the whole chain: for radius one the exit time
  is the first step on every path, so both sides of Example 3.1 can be
  computed --- the expected exit time is \<open>1\<close>, the bound \<open>v(0)\<close> is \<open>4\<close>.\<close>

lemma walk_one_abs: "\<bar>walk 1 s\<bar> = 1"
  using walk_incr_abs[of 0 s] by simp

lemma exitN_one:
  assumes "1 \<le> N"
  shows "exitN 1 N s = 1"
  unfolding exitN_def
proof (rule Least_equality)
  show "1 = N \<or> real 1 \<le> \<bar>walk 1 s\<bar>"
    using walk_incr_abs[of 0 s] by simp
next
  fix y assume y: "y = N \<or> real 1 \<le> \<bar>walk y s\<bar>"
  show "1 \<le> y"
  proof (rule ccontr)
    assume "\<not> 1 \<le> y"
    then have "y = 0" by simp
    with y assms show False by simp
  qed
qed

corollary random_walk_expected_exit_time_radius_one:
  assumes "1 \<le> N"
  shows "(\<integral>s. real (exitN 1 N s) \<partial>coin) = 1"
proof -
  have fn: "(\<lambda>s. real (exitN 1 N s)) = (\<lambda>s. 1 :: real)"
  proof (rule ext)
    fix s
    have "exitN 1 N s = 1"
      by (rule exitN_one[OF assms])
    then show "real (exitN 1 N s) = 1"
      by simp
  qed
  have "(\<integral>s. real (exitN 1 N s) \<partial>coin) = (\<integral>s. (1 :: real) \<partial>coin)"
    unfolding fn by (rule refl)
  also have "\<dots> = 1"
    using prob_space.prob_space[OF prob_space_coin] by simp
  finally show ?thesis .
qed

section \<open>The gradient strategy of the random walk is a relative arbitrage\<close>

text \<open>The radius \<open>r\<close> does not occur in the assumptions of
  \<open>discrete_volatile_base\<close>, so it is absent from its locale predicate; the
  walk is a sufficiently volatile market for every choice of \<open>r\<close>.\<close>

theorem random_walk_volatile_base:
  "discrete_volatile_base coin coin_filtration rw (1::nat) (0::real^2) (N::nat)"
proof (intro discrete_volatile_base.intro[OF discrete_vec_martingale_rw]
    discrete_volatile_base_axioms.intro)
  show "prob_space coin"
    by (rule prob_space_coin)
  show "(1 :: nat) \<le> 1" by simp
  show "(1 :: nat) < CARD(2)" by simp
  show "AE s in coin. rw 0 s = 0"
    by simp
  show "AE s in coin. \<forall>j. j < N \<longrightarrow>
      real (CARD(2) - 1) \<le> (rw (Suc j) s - rw j s) \<bullet> (rw (Suc j) s - rw j s)"
    by (intro AE_I2 allI impI) (simp add: rw_incr_sq)
qed

text \<open>Definition 1.1 for the random walk: past the critical horizon
  \<open>v(0) = r\<^sup>2\<close> the value process of the gradient strategy --- here simply
  \<open>v(X\<^sub>j) + j\<close>, since the walk accumulates one unit of quadratic variation
  per step --- is a relative arbitrage.\<close>

corollary random_walk_relative_arbitrage:
  assumes N: "r\<^sup>2 < real N"
  shows "relative_arbitrage coin
     (\<lambda>t s. ball_v r 1 (rw (nat \<lfloor>t\<rfloor>) s) + real (nat \<lfloor>t\<rfloor>)) (real N)"
proof -
  interpret RW: discrete_volatile_base coin coin_filtration rw 1 r 0 N
    by (rule random_walk_volatile_base)
  have dV_eq: "(\<lambda>t s. RW.dV (nat \<lfloor>t\<rfloor>) s)
      = (\<lambda>t s. ball_v r 1 (rw (nat \<lfloor>t\<rfloor>) s) + real (nat \<lfloor>t\<rfloor>))"
    unfolding RW.dV_def by (simp add: fun_eq_iff qvar_vec_rw)
  have "ball_v r 1 (0 :: real^2) < real N"
    using N by (simp add: ball_v_def)
  from RW.discrete_relative_arbitrage[OF this] show ?thesis
    unfolding dV_eq[symmetric] .
qed


(*<*)
end
(*>*)
