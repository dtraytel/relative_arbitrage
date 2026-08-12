(*
  Title:   Optional_Sampling.thy
  Content: Stochastic integration, layer 3b: optional sampling in continuous
           time.

  The martingale-problem identity that the probabilistic part of the paper
  needs is

    E[Z (t /\ tau)] = E[Z 0]                                          (star)

  for the process Z t = |X t|^2 - int_0^t tr(a s) ds, which Ito's formula
  makes a martingale.  Deriving (star) from "Z is a martingale" is exactly
  optional sampling at the bounded stopping time t /\ tau, and that is what
  is proved here, in three steps:

    1. discrete time, arbitrary stopping time: the stopped process is the
       martingale transform of Z by the indicators of {T > k}, so its
       expectation is constant (no square integrability needed, unlike the
       optional-sampling section of Quadratic_Variation);

    2. a continuous-time martingale sampled on a grid is a discrete-time
       martingale, so (star) holds for stopping times taking finitely many
       values on the grid;

    3. an arbitrary stopping time is approximated from above by the dyadic
       stopping times of step 2, and right continuity of the paths plus an
       integrable bound give (star) in general by dominated convergence.
*)

theory Optional_Sampling
  imports Doob_Inequality
begin

section \<open>Discrete-time optional sampling for integrable martingales\<close>

locale nat_stopped_martingale = martingale M F "0 :: nat" Y
  for M :: "'a measure" and F and Y :: "nat \<Rightarrow> 'a \<Rightarrow> real" +
  fixes T :: "'a \<Rightarrow> nat"
  assumes stopping_time_T: "\<And>n. {\<omega> \<in> space M. T \<omega> \<le> n} \<in> sets (F n)"
begin

lemma Y_integrable [intro, simp]: "integrable M (Y n)"
  by (rule integrable) simp

definition Tgt :: "nat \<Rightarrow> 'a set" where
  "Tgt n = {\<omega> \<in> space M. n < T \<omega>}"

lemma Tgt_sets_F: "Tgt n \<in> sets (F n)"
proof -
  have eq: "Tgt n = space (F n) - {\<omega> \<in> space M. T \<omega> \<le> n}"
    unfolding Tgt_def by (auto simp: not_le)
  show ?thesis
    unfolding eq using stopping_time_T[of n] by (rule sets.compl_sets)
qed

lemma Tgt_sets_M: "Tgt n \<in> sets M"
proof -
  have "sets (F n) \<subseteq> sets M"
    by (intro sets_F_subset) simp
  then show ?thesis
    using Tgt_sets_F by blast
qed

text \<open>The increments of the stopped process.\<close>

definition inc :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
  "inc k \<omega> = indicat_real (Tgt k) \<omega> * (Y (Suc k) \<omega> - Y k \<omega>)"

lemma inc_integrable [intro, simp]: "integrable M (inc k)"
proof -
  have "integrable M (\<lambda>\<omega>. indicat_real (Tgt k) \<omega> *\<^sub>R (Y (Suc k) \<omega> - Y k \<omega>))"
    by (intro integrable_mult_indicator Tgt_sets_M
        Bochner_Integration.integrable_diff Y_integrable)
  then show ?thesis
    unfolding inc_def by simp
qed

lemma indicator_times_integrable:
  "integrable M (\<lambda>\<omega>. indicat_real (Tgt k) \<omega> * Y j \<omega>)"
proof -
  have "integrable M (\<lambda>\<omega>. indicat_real (Tgt k) \<omega> *\<^sub>R Y j \<omega>)"
    by (intro integrable_mult_indicator Tgt_sets_M Y_integrable)
  then show ?thesis by simp
qed

lemma set_incr_integrable:
  assumes B: "B \<in> sets M"
  shows "integrable M (\<lambda>\<omega>. indicat_real B \<omega> * Y j \<omega>)"
proof -
  have "integrable M (\<lambda>\<omega>. indicat_real B \<omega> *\<^sub>R Y j \<omega>)"
    by (intro integrable_mult_indicator B Y_integrable)
  then show ?thesis by simp
qed

text \<open>An increment of \<open>Y\<close> integrates to zero over any event of its own
  past.  This is the only property of the martingale that the stopping
  arguments below use.\<close>

lemma set_incr_zero:
  assumes B: "B \<in> sets (F k)"
  shows "(\<integral>\<omega>. indicat_real B \<omega> * (Y (Suc k) \<omega> - Y k \<omega>) \<partial>M) = 0"
proof -
  have B_M: "B \<in> sets M"
  proof -
    have "sets (F k) \<subseteq> sets M"
      by (intro sets_F_subset) simp
    then show ?thesis using B by blast
  qed
  have set_eq: "set_lebesgue_integral M B (Y j)
      = (\<integral>\<omega>. indicat_real B \<omega> * Y j \<omega> \<partial>M)" for j
    unfolding set_lebesgue_integral_def by simp
  have "set_lebesgue_integral M B (Y k) = set_lebesgue_integral M B (Y (Suc k))"
    using B by (intro set_integral_eq) auto
  then have eq: "(\<integral>\<omega>. indicat_real B \<omega> * Y k \<omega> \<partial>M)
      = (\<integral>\<omega>. indicat_real B \<omega> * Y (Suc k) \<omega> \<partial>M)"
    unfolding set_eq .
  have "(\<integral>\<omega>. indicat_real B \<omega> * (Y (Suc k) \<omega> - Y k \<omega>) \<partial>M)
      = (\<integral>\<omega>. indicat_real B \<omega> * Y (Suc k) \<omega>
             - indicat_real B \<omega> * Y k \<omega> \<partial>M)"
    by (simp add: right_diff_distrib)
  also have "\<dots> = (\<integral>\<omega>. indicat_real B \<omega> * Y (Suc k) \<omega> \<partial>M)
      - (\<integral>\<omega>. indicat_real B \<omega> * Y k \<omega> \<partial>M)"
    by (intro Bochner_Integration.integral_diff set_incr_integrable B_M)
  also have "\<dots> = 0"
    using eq by simp
  finally show ?thesis .
qed

lemma inc_zero: "(\<integral>\<omega>. inc k \<omega> \<partial>M) = 0"
  unfolding inc_def by (rule set_incr_zero[OF Tgt_sets_F])

text \<open>The stopped process is the martingale transform of \<open>Y\<close> by the
  indicators of the events \<open>{T > k}\<close>.\<close>

lemma stopped_eq_sum:
  assumes w: "\<omega> \<in> space M"
  shows "Y (min n (T \<omega>)) \<omega> = Y 0 \<omega> + (\<Sum>k<n. inc k \<omega>)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "n < T \<omega>")
    case True
    then have ind: "indicat_real (Tgt n) \<omega> = 1"
      using w by (simp add: Tgt_def)
    from True have m1: "min (Suc n) (T \<omega>) = Suc n" and m2: "min n (T \<omega>) = n"
      by auto
    have "Y (min (Suc n) (T \<omega>)) \<omega> = Y n \<omega> + (Y (Suc n) \<omega> - Y n \<omega>)"
      unfolding m1 by simp
    also have "\<dots> = Y 0 \<omega> + (\<Sum>k<n. inc k \<omega>) + (Y (Suc n) \<omega> - Y n \<omega>)"
      using Suc unfolding m2 by simp
    also have "\<dots> = Y 0 \<omega> + (\<Sum>k<Suc n. inc k \<omega>)"
      unfolding inc_def using ind by simp
    finally show ?thesis .
  next
    case False
    then have ind: "indicat_real (Tgt n) \<omega> = 0"
      by (simp add: Tgt_def)
    from False have m: "min (Suc n) (T \<omega>) = min n (T \<omega>)"
      by auto
    have "Y (min (Suc n) (T \<omega>)) \<omega> = Y 0 \<omega> + (\<Sum>k<n. inc k \<omega>)"
      unfolding m by (rule Suc)
    then show ?thesis
      unfolding inc_def using ind by simp
  qed
qed

lemma stopped_integrable: "integrable M (\<lambda>\<omega>. Y (min n (T \<omega>)) \<omega>)"
proof -
  have cong: "integrable M (\<lambda>\<omega>. Y (min n (T \<omega>)) \<omega>)
      \<longleftrightarrow> integrable M (\<lambda>\<omega>. Y 0 \<omega> + (\<Sum>k<n. inc k \<omega>))"
    by (intro Bochner_Integration.integrable_cong refl) (rule stopped_eq_sum)
  show ?thesis
    unfolding cong
    by (intro Bochner_Integration.integrable_add Y_integrable
        Bochner_Integration.integrable_sum inc_integrable)
qed

theorem stopped_expectation:
  "(\<integral>\<omega>. Y (min n (T \<omega>)) \<omega> \<partial>M) = (\<integral>\<omega>. Y 0 \<omega> \<partial>M)"
proof -
  have "(\<integral>\<omega>. Y (min n (T \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. Y 0 \<omega> + (\<Sum>k<n. inc k \<omega>) \<partial>M)"
    by (intro Bochner_Integration.integral_cong refl stopped_eq_sum)
  also have "\<dots> = (\<integral>\<omega>. Y 0 \<omega> \<partial>M) + (\<integral>\<omega>. (\<Sum>k<n. inc k \<omega>) \<partial>M)"
    by (intro Bochner_Integration.integral_add Y_integrable
        Bochner_Integration.integrable_sum inc_integrable)
  also have "(\<integral>\<omega>. (\<Sum>k<n. inc k \<omega>) \<partial>M) = (\<Sum>k<n. (\<integral>\<omega>. inc k \<omega> \<partial>M))"
    by (intro Bochner_Integration.integral_sum inc_integrable)
  also have "\<dots> = 0"
    by (simp add: inc_zero)
  finally show ?thesis by simp
qed

subsection \<open>The stopped process is itself a martingale\<close>

text \<open>Localising the argument above to an event of the past turns the
  constancy of the expectation into the martingale property of the stopped
  process: the increments beyond time \<open>m\<close> are still increments of \<open>Y\<close>
  restricted to events of \<open>F k\<close> for \<open>k \<ge> m\<close>, so they integrate to zero
  over any \<open>A \<in> F m\<close>.\<close>

lemma inc_set_zero:
  assumes A: "A \<in> sets (F m)" and mk: "m \<le> k"
  shows "(\<integral>\<omega>. indicat_real A \<omega> * inc k \<omega> \<partial>M) = 0"
proof -
  have AF: "A \<in> sets (F k)"
  proof -
    have "sets (F m) \<subseteq> sets (F k)"
      using mk by (intro sets_F_mono) simp_all
    then show ?thesis using A by blast
  qed
  have inter: "A \<inter> Tgt k \<in> sets (F k)"
    using AF Tgt_sets_F by (rule sets.Int)
  have eq: "(\<lambda>\<omega>. indicat_real A \<omega> * inc k \<omega>)
      = (\<lambda>\<omega>. indicat_real (A \<inter> Tgt k) \<omega> * (Y (Suc k) \<omega> - Y k \<omega>))"
    unfolding inc_def by (simp add: fun_eq_iff indicator_def)
  show ?thesis
    unfolding eq by (rule set_incr_zero[OF inter])
qed

lemma ind_inc_integrable:
  assumes A: "A \<in> sets M"
  shows "integrable M (\<lambda>\<omega>. indicat_real A \<omega> * inc k \<omega>)"
proof -
  have "integrable M (\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R inc k \<omega>)"
    by (intro integrable_mult_indicator A inc_integrable)
  then show ?thesis by simp
qed

theorem set_stopped_expectation:
  assumes A: "A \<in> sets (F m)" and mn: "m \<le> n"
  shows "(\<integral>\<omega>. indicat_real A \<omega> * Y (min n (T \<omega>)) \<omega> \<partial>M)
       = (\<integral>\<omega>. indicat_real A \<omega> * Y (min m (T \<omega>)) \<omega> \<partial>M)"
proof -
  have A_M: "A \<in> sets M"
  proof -
    have "sets (F m) \<subseteq> sets M"
      by (intro sets_F_subset) simp
    then show ?thesis using A by blast
  qed
  have int_m: "integrable M (\<lambda>\<omega>. indicat_real A \<omega> * Y (min m (T \<omega>)) \<omega>)"
  proof -
    have "integrable M (\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R Y (min m (T \<omega>)) \<omega>)"
      by (intro integrable_mult_indicator A_M stopped_integrable)
    then show ?thesis by simp
  qed
  have pt: "indicat_real A \<omega> * Y (min n (T \<omega>)) \<omega>
      = indicat_real A \<omega> * Y (min m (T \<omega>)) \<omega>
        + (\<Sum>k\<in>{m..<n}. indicat_real A \<omega> * inc k \<omega>)"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have en: "Y (min n (T \<omega>)) \<omega> = Y 0 \<omega> + (\<Sum>k<n. inc k \<omega>)"
      by (rule stopped_eq_sum[OF w])
    have em: "Y (min m (T \<omega>)) \<omega> = Y 0 \<omega> + (\<Sum>k<m. inc k \<omega>)"
      by (rule stopped_eq_sum[OF w])
    have "(\<Sum>k\<in>{0..<m}. inc k \<omega>) + (\<Sum>k\<in>{m..<n}. inc k \<omega>)
        = (\<Sum>k\<in>{0..<n}. inc k \<omega>)"
      using mn by (intro sum.atLeastLessThan_concat) auto
    then have "(\<Sum>k<n. inc k \<omega>)
        = (\<Sum>k<m. inc k \<omega>) + (\<Sum>k\<in>{m..<n}. inc k \<omega>)"
      by (simp add: atLeast0LessThan)
    then show ?thesis
      unfolding en em by (simp add: sum_distrib_left algebra_simps)
  qed
  have sum_zero: "(\<integral>\<omega>. (\<Sum>k\<in>{m..<n}. indicat_real A \<omega> * inc k \<omega>) \<partial>M) = 0"
  proof -
    have "(\<integral>\<omega>. (\<Sum>k\<in>{m..<n}. indicat_real A \<omega> * inc k \<omega>) \<partial>M)
        = (\<Sum>k\<in>{m..<n}. (\<integral>\<omega>. indicat_real A \<omega> * inc k \<omega> \<partial>M))"
      by (intro Bochner_Integration.integral_sum ind_inc_integrable A_M)
    also have "\<dots> = 0"
      using inc_set_zero[OF A] by simp
    finally show ?thesis .
  qed
  have "(\<integral>\<omega>. indicat_real A \<omega> * Y (min n (T \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. indicat_real A \<omega> * Y (min m (T \<omega>)) \<omega>
          + (\<Sum>k\<in>{m..<n}. indicat_real A \<omega> * inc k \<omega>) \<partial>M)"
    by (intro Bochner_Integration.integral_cong refl pt)
  also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * Y (min m (T \<omega>)) \<omega> \<partial>M)
      + (\<integral>\<omega>. (\<Sum>k\<in>{m..<n}. indicat_real A \<omega> * inc k \<omega>) \<partial>M)"
    by (intro Bochner_Integration.integral_add int_m
        Bochner_Integration.integrable_sum ind_inc_integrable A_M)
  also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * Y (min m (T \<omega>)) \<omega> \<partial>M)"
    unfolding sum_zero by simp
  finally show ?thesis .
qed

corollary set_stopped_expectation':
  assumes A: "A \<in> sets (F m)" and mn: "m \<le> n"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. Y (min n (T \<omega>)) \<omega>)
       = set_lebesgue_integral M A (\<lambda>\<omega>. Y (min m (T \<omega>)) \<omega>)"
  using set_stopped_expectation[OF A mn]
  unfolding set_lebesgue_integral_def by simp

end

section \<open>Sampling a continuous-time martingale on a grid\<close>

locale sampled_cont_martingale = martingale M F "0 :: real" Z + time_grid t
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"

sublocale sampled_cont_martingale
  \<subseteq> D: martingale M "\<lambda>n. F (t n)" "0 :: nat" "\<lambda>n. Z (t n)"
proof -
  have fm: "filtered_measure M (\<lambda>n. F (t n)) (0 :: nat)"
  proof (intro filtered_measure.intro)
    show "\<And>i :: nat. 0 \<le> i \<Longrightarrow> subalgebra M (F (t i))"
      by (intro subalgebras t_ge_0)
    show "\<And>i j :: nat. 0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> sets (F (t i)) \<le> sets (F (t j))"
      by (intro sets_F_mono t_ge_0 t_mono_le)
  qed
  have sff: "sigma_finite_filtered_measure M (\<lambda>n. F (t n)) (0 :: nat)"
    by (intro sigma_finite_filtered_measure.intro[OF fm]
        sigma_finite_filtered_measure_axioms.intro)
      (intro sigma_finite_subalgebra_F t_ge_0)
  have ap: "adapted_process M (\<lambda>n. F (t n)) 0 (\<lambda>n. Z (t n))"
    by (intro adapted_process.intro[OF fm] adapted_process_axioms.intro)
      (intro adapted t_ge_0)
  show "martingale M (\<lambda>n. F (t n)) (0 :: nat) (\<lambda>n. Z (t n))"
  proof (intro martingale.intro[OF sff ap] martingale_axioms.intro)
    show "\<And>i :: nat. 0 \<le> i \<Longrightarrow> integrable M (Z (t i))"
      by (intro integrable t_ge_0)
    show "\<And>i j :: nat. 0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow>
        AE \<xi> in M. Z (t i) \<xi> = cond_exp M (F (t i)) (Z (t j)) \<xi>"
      by (intro martingale_property t_ge_0 t_mono_le)
  qed
qed

section \<open>Optional sampling at a simple stopping time\<close>

text \<open>A stopping time taking finitely many values, all of them on the grid.
  No path regularity whatsoever is needed for this case.\<close>

locale simple_stopped_martingale = sampled_cont_martingale M F Z t
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" +
  fixes tau :: "'a \<Rightarrow> real" and N :: nat
  assumes tau_range: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<exists>m\<le>N. tau \<omega> = t m"
    and tau_stop: "\<And>n. {\<omega> \<in> space M. tau \<omega> \<le> t n} \<in> sets (F (t n))"
begin

definition Tidx :: "'a \<Rightarrow> nat" where
  "Tidx \<omega> = (LEAST m. tau \<omega> \<le> t m)"

lemma tau_ex: "\<omega> \<in> space M \<Longrightarrow> \<exists>m. tau \<omega> \<le> t m"
  using tau_range by force

lemma Tidx_ge: "\<omega> \<in> space M \<Longrightarrow> tau \<omega> \<le> t (Tidx \<omega>)"
  unfolding Tidx_def using tau_ex by (auto intro: LeastI_ex)

lemma Tidx_le_iff:
  assumes w: "\<omega> \<in> space M"
  shows "Tidx \<omega> \<le> n \<longleftrightarrow> tau \<omega> \<le> t n"
proof
  assume "Tidx \<omega> \<le> n"
  then have "t (Tidx \<omega>) \<le> t n"
    by (rule t_mono_le)
  with Tidx_ge[OF w] show "tau \<omega> \<le> t n" by simp
next
  assume "tau \<omega> \<le> t n"
  then show "Tidx \<omega> \<le> n"
    unfolding Tidx_def by (rule Least_le)
qed

lemma t_Tidx:
  assumes w: "\<omega> \<in> space M"
  shows "t (Tidx \<omega>) = tau \<omega>"
proof -
  from tau_range[OF w] obtain m where m: "tau \<omega> = t m" by blast
  then have "Tidx \<omega> \<le> m"
    unfolding Tidx_def by (intro Least_le) simp
  then have "t (Tidx \<omega>) \<le> t m"
    by (rule t_mono_le)
  with m Tidx_ge[OF w] show ?thesis by simp
qed

lemma Tidx_stopping: "{\<omega> \<in> space M. Tidx \<omega> \<le> n} \<in> sets (F (t n))"
proof -
  have "{\<omega> \<in> space M. Tidx \<omega> \<le> n} = {\<omega> \<in> space M. tau \<omega> \<le> t n}"
    using Tidx_le_iff by auto
  then show ?thesis
    using tau_stop[of n] by simp
qed

sublocale S: nat_stopped_martingale M "\<lambda>n. F (t n)" "\<lambda>n. Z (t n)" Tidx
  by (intro nat_stopped_martingale.intro nat_stopped_martingale_axioms.intro
      D.martingale_axioms) (rule Tidx_stopping)

lemma t_min_Tidx:
  assumes w: "\<omega> \<in> space M"
  shows "t (min n (Tidx \<omega>)) = min (t n) (tau \<omega>)"
proof (cases "Tidx \<omega> \<le> n")
  case True
  then have "min n (Tidx \<omega>) = Tidx \<omega>" by simp
  moreover have "tau \<omega> \<le> t n"
    using True Tidx_le_iff[OF w] by simp
  ultimately show ?thesis
    using t_Tidx[OF w] by simp
next
  case False
  then have "min n (Tidx \<omega>) = n" by simp
  moreover have "\<not> tau \<omega> \<le> t n"
    using False Tidx_le_iff[OF w] by simp
  ultimately show ?thesis by simp
qed

theorem simple_optional_sampling:
  "(\<integral>\<omega>. Z (min (t n) (tau \<omega>)) \<omega> \<partial>M) = (\<integral>\<omega>. Z (t 0) \<omega> \<partial>M)"
proof -
  have "(\<integral>\<omega>. Z (min (t n) (tau \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. Z (t (min n (Tidx \<omega>))) \<omega> \<partial>M)"
    by (intro Bochner_Integration.integral_cong refl)
      (simp add: t_min_Tidx)
  also have "\<dots> = (\<integral>\<omega>. Z (t 0) \<omega> \<partial>M)"
    by (rule S.stopped_expectation)
  finally show ?thesis .
qed

theorem simple_stopped_integrable:
  "integrable M (\<lambda>\<omega>. Z (min (t n) (tau \<omega>)) \<omega>)"
proof -
  have "integrable M (\<lambda>\<omega>. Z (t (min n (Tidx \<omega>))) \<omega>)"
    by (rule S.stopped_integrable)
  moreover have "integrable M (\<lambda>\<omega>. Z (t (min n (Tidx \<omega>))) \<omega>)
      \<longleftrightarrow> integrable M (\<lambda>\<omega>. Z (min (t n) (tau \<omega>)) \<omega>)"
    by (intro Bochner_Integration.integrable_cong refl) (simp add: t_min_Tidx)
  ultimately show ?thesis by simp
qed

text \<open>The localised version: over an event of the past the stopped values
  at two grid times have the same integral.\<close>

theorem set_simple_optional_sampling:
  assumes A: "A \<in> sets (F (t m))" and mn: "m \<le> n"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. Z (min (t n) (tau \<omega>)) \<omega>)
       = set_lebesgue_integral M A (\<lambda>\<omega>. Z (min (t m) (tau \<omega>)) \<omega>)"
proof -
  have e: "Z (t (min j (Tidx \<omega>))) \<omega> = Z (min (t j) (tau \<omega>)) \<omega>"
    if w: "\<omega> \<in> space M" for j \<omega>
    using t_min_Tidx[OF w] by simp
  have "set_lebesgue_integral M A (\<lambda>\<omega>. Z (min (t n) (tau \<omega>)) \<omega>)
      = set_lebesgue_integral M A (\<lambda>\<omega>. Z (t (min n (Tidx \<omega>))) \<omega>)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong refl) (simp add: e)
  also have "\<dots> = set_lebesgue_integral M A (\<lambda>\<omega>. Z (t (min m (Tidx \<omega>))) \<omega>)"
    by (rule S.set_stopped_expectation'[OF A mn])
  also have "\<dots> = set_lebesgue_integral M A (\<lambda>\<omega>. Z (min (t m) (tau \<omega>)) \<omega>)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong refl) (simp add: e)
  finally show ?thesis .
qed

end

section \<open>Optional sampling at an arbitrary bounded stopping time\<close>

text \<open>An arbitrary stopping time is approximated from above by its dyadic
  ceilings, which are simple stopping times of the previous section.  With
  continuous paths and an integrable bound on the process up to the
  horizon, dominated convergence transfers the identity to the limit.  The
  measurability of the stopped process is assumed; in the intended
  application it comes for free, since the market locale already assumes the
  stopped process to be integrable.\<close>

locale stopped_cont_martingale = martingale M F "0 :: real" Z
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" +
  fixes tau :: "'a \<Rightarrow> real" and u :: real and D :: "'a \<Rightarrow> real"
  assumes u_pos: "0 < u"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and paths_cont: "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. Z s \<omega>)"
    and Z_dom: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D \<omega>"
    and D_integrable: "integrable M D"
    and stopped_measurable:
      "(\<lambda>\<omega>. Z (min u (tau \<omega>)) \<omega>) \<in> borel_measurable M"
begin

subsection \<open>The dyadic grids and the dyadic ceilings of \<open>tau\<close>\<close>

definition dgrid :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "dgrid n k = u * real k / 2 ^ n"

definition didx :: "nat \<Rightarrow> 'a \<Rightarrow> nat" where
  "didx n \<omega> = min (2 ^ n) (LEAST k. tau \<omega> \<le> dgrid n k)"

definition dtime :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
  "dtime n \<omega> = dgrid n (didx n \<omega>)"

lemma dgrid_0 [simp]: "dgrid n 0 = 0"
  unfolding dgrid_def by simp

lemma dgrid_top [simp]: "dgrid n (2 ^ n) = u"
  unfolding dgrid_def by simp

lemma dgrid_nonneg: "0 \<le> dgrid n k"
  unfolding dgrid_def using u_pos by simp

lemma dgrid_le_iff: "dgrid n k \<le> dgrid n j \<longleftrightarrow> k \<le> j"
proof -
  have "dgrid n k \<le> dgrid n j \<longleftrightarrow> u * real k \<le> u * real j"
    unfolding dgrid_def by (simp add: divide_le_cancel)
  also have "\<dots> \<longleftrightarrow> real k \<le> real j"
    using u_pos by simp
  finally show ?thesis by simp
qed

lemma dgrid_mono: "k \<le> j \<Longrightarrow> dgrid n k \<le> dgrid n j"
  using dgrid_le_iff by simp

lemma dgrid_Suc: "dgrid n (Suc k) = dgrid n k + u / 2 ^ n"
  unfolding dgrid_def by (simp add: field_simps)

lemma dgrid_unbounded: "\<exists>k. x \<le> dgrid n k"
proof -
  obtain m :: nat where m: "x * 2 ^ n / u \<le> real m"
    using real_arch_simple by blast
  have "x = u * (x * 2 ^ n / u) / 2 ^ n"
    using u_pos by simp
  also have "\<dots> \<le> u * real m / 2 ^ n"
    using m u_pos by (intro divide_right_mono mult_left_mono) auto
  finally show ?thesis
    unfolding dgrid_def by blast
qed

lemma Least_dgrid_le_iff: "(LEAST k. tau \<omega> \<le> dgrid n k) \<le> j \<longleftrightarrow> tau \<omega> \<le> dgrid n j"
proof
  assume "(LEAST k. tau \<omega> \<le> dgrid n k) \<le> j"
  moreover have "tau \<omega> \<le> dgrid n (LEAST k. tau \<omega> \<le> dgrid n k)"
    using dgrid_unbounded by (auto intro: LeastI_ex)
  ultimately show "tau \<omega> \<le> dgrid n j"
    using dgrid_mono[of "LEAST k. tau \<omega> \<le> dgrid n k" j n] by simp
next
  assume "tau \<omega> \<le> dgrid n j"
  then show "(LEAST k. tau \<omega> \<le> dgrid n k) \<le> j"
    by (rule Least_le)
qed

lemma dtime_nonneg: "0 \<le> dtime n \<omega>"
  unfolding dtime_def by (rule dgrid_nonneg)

lemma dtime_le_u: "dtime n \<omega> \<le> u"
  unfolding dtime_def didx_def
  using dgrid_mono[of "min (2 ^ n) (LEAST k. tau \<omega> \<le> dgrid n k)" "2 ^ n" n]
  by simp

lemma dtime_le_iff: "dtime n \<omega> \<le> dgrid n j \<longleftrightarrow> 2 ^ n \<le> j \<or> tau \<omega> \<le> dgrid n j"
  unfolding dtime_def didx_def
  by (simp add: dgrid_le_iff Least_dgrid_le_iff min_le_iff_disj)

lemma dtime_ge:
  assumes w: "\<omega> \<in> space M"
  shows "min u (tau \<omega>) \<le> dtime n \<omega>"
proof (cases "(LEAST k. tau \<omega> \<le> dgrid n k) \<le> 2 ^ n")
  case True
  then have "dtime n \<omega> = dgrid n (LEAST k. tau \<omega> \<le> dgrid n k)"
    unfolding dtime_def didx_def by simp
  moreover have "tau \<omega> \<le> dgrid n (LEAST k. tau \<omega> \<le> dgrid n k)"
    using dgrid_unbounded by (auto intro: LeastI_ex)
  ultimately show ?thesis by simp
next
  case False
  then have "dtime n \<omega> = u"
    unfolding dtime_def didx_def by simp
  then show ?thesis by simp
qed

lemma dtime_le:
  assumes w: "\<omega> \<in> space M"
  shows "dtime n \<omega> \<le> min u (tau \<omega>) + u / 2 ^ n"
proof (cases "(LEAST k. tau \<omega> \<le> dgrid n k) \<le> 2 ^ n")
  case True
  define L where "L = (LEAST k. tau \<omega> \<le> dgrid n k)"
  from True have dt: "dtime n \<omega> = dgrid n L"
    unfolding dtime_def didx_def L_def by simp
  have tau_le_u: "tau \<omega> \<le> u"
    using True Least_dgrid_le_iff[of \<omega> n "2 ^ n"] by simp
  then have mn: "min u (tau \<omega>) = tau \<omega>" by simp
  have "dgrid n L \<le> tau \<omega> + u / 2 ^ n"
  proof (cases L)
    case 0
    have "0 \<le> tau \<omega>"
      by (rule tau_nonneg[OF w])
    moreover have "0 < u / 2 ^ n"
      using u_pos by simp
    ultimately show ?thesis
      unfolding 0 by simp
  next
    case (Suc m)
    have "\<not> tau \<omega> \<le> dgrid n m"
      using Suc unfolding L_def by (metis lessI not_less_Least)
    then have "dgrid n m \<le> tau \<omega>" by simp
    then show ?thesis
      unfolding Suc by (simp add: dgrid_Suc)
  qed
  with dt mn show ?thesis by simp
next
  case False
  then have dt: "dtime n \<omega> = u"
    unfolding dtime_def didx_def by simp
  from False have "\<not> tau \<omega> \<le> u"
    using Least_dgrid_le_iff[of \<omega> n "2 ^ n"] by simp
  then have "min u (tau \<omega>) = u" by simp
  with dt show ?thesis
    using u_pos by simp
qed

lemma dtime_tendsto:
  assumes w: "\<omega> \<in> space M"
  shows "(\<lambda>n. dtime n \<omega>) \<longlonglongrightarrow> min u (tau \<omega>)"
proof (rule tendsto_sandwich
    [of "\<lambda>n. min u (tau \<omega>)" "\<lambda>n. dtime n \<omega>" sequentially
        "\<lambda>n. min u (tau \<omega>) + u / 2 ^ n"])
  show "\<forall>\<^sub>F n in sequentially. min u (tau \<omega>) \<le> dtime n \<omega>"
    using dtime_ge[OF w] by simp
  show "\<forall>\<^sub>F n in sequentially. dtime n \<omega> \<le> min u (tau \<omega>) + u / 2 ^ n"
    using dtime_le[OF w] by simp
  show "(\<lambda>n. min u (tau \<omega>)) \<longlonglongrightarrow> min u (tau \<omega>)" by simp
  have "(\<lambda>n. u / 2 ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_divide_realpow_zero) simp
  then have "(\<lambda>n. min u (tau \<omega>) + u / 2 ^ n) \<longlonglongrightarrow> min u (tau \<omega>) + 0"
    by (intro tendsto_add tendsto_const)
  then show "(\<lambda>n. min u (tau \<omega>) + u / 2 ^ n) \<longlonglongrightarrow> min u (tau \<omega>)" by simp
qed

subsection \<open>Dyadic ceilings of a deterministic time\<close>

text \<open>The same ceiling construction applied to a constant: it produces the
  grid point just above a given time, which is what localises the sampling
  identity to an event of the past.\<close>

definition dcidx :: "nat \<Rightarrow> real \<Rightarrow> nat" where
  "dcidx n x = min (2 ^ n) (LEAST k. x \<le> dgrid n k)"

definition dceil :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "dceil n x = dgrid n (dcidx n x)"

lemma dcidx_le: "dcidx n x \<le> 2 ^ n"
  unfolding dcidx_def by simp

lemma dceil_grid: "dceil n x = dgrid n (dcidx n x)"
  unfolding dceil_def ..

lemma dtime_eq_dceil: "dtime n \<omega> = dceil n (tau \<omega>)"
  unfolding dtime_def dceil_def didx_def dcidx_def ..

lemma Least_dgrid_le_iff2:
  "(LEAST k. x \<le> dgrid n k) \<le> j \<longleftrightarrow> x \<le> dgrid n j"
proof
  assume "(LEAST k. x \<le> dgrid n k) \<le> j"
  moreover have "x \<le> dgrid n (LEAST k. x \<le> dgrid n k)"
    using dgrid_unbounded by (auto intro: LeastI_ex)
  ultimately show "x \<le> dgrid n j"
    using dgrid_mono[of "LEAST k. x \<le> dgrid n k" j n] by simp
next
  assume "x \<le> dgrid n j"
  then show "(LEAST k. x \<le> dgrid n k) \<le> j"
    by (rule Least_le)
qed

lemma dceil_nonneg: "0 \<le> dceil n x"
  unfolding dceil_def by (rule dgrid_nonneg)

lemma dceil_le_u: "dceil n x \<le> u"
proof -
  have "dgrid n (dcidx n x) \<le> dgrid n (2 ^ n)"
    by (intro dgrid_mono dcidx_le)
  then show ?thesis
    unfolding dceil_def by simp
qed

lemma dceil_ge: "min u x \<le> dceil n x"
proof (cases "(LEAST k. x \<le> dgrid n k) \<le> 2 ^ n")
  case True
  then have "dceil n x = dgrid n (LEAST k. x \<le> dgrid n k)"
    unfolding dceil_def dcidx_def by simp
  moreover have "x \<le> dgrid n (LEAST k. x \<le> dgrid n k)"
    using dgrid_unbounded by (auto intro: LeastI_ex)
  ultimately show ?thesis by simp
next
  case False
  then have "dceil n x = u"
    unfolding dceil_def dcidx_def by simp
  then show ?thesis by simp
qed

lemma dceil_le:
  assumes x: "0 \<le> x"
  shows "dceil n x \<le> min u x + u / 2 ^ n"
proof (cases "(LEAST k. x \<le> dgrid n k) \<le> 2 ^ n")
  case True
  define L where "L = (LEAST k. x \<le> dgrid n k)"
  from True have dt: "dceil n x = dgrid n L"
    unfolding dceil_def dcidx_def L_def by simp
  have x_le_u: "x \<le> u"
    using True Least_dgrid_le_iff2[of x n "2 ^ n"] by simp
  then have mn: "min u x = x" by simp
  have "dgrid n L \<le> x + u / 2 ^ n"
  proof (cases L)
    case 0
    have "0 < u / 2 ^ n"
      using u_pos by simp
    then show ?thesis
      unfolding 0 using x by simp
  next
    case (Suc m)
    have "\<not> x \<le> dgrid n m"
      using Suc unfolding L_def by (metis lessI not_less_Least)
    then have "dgrid n m \<le> x" by simp
    then show ?thesis
      unfolding Suc by (simp add: dgrid_Suc)
  qed
  with dt mn show ?thesis by simp
next
  case False
  then have dt: "dceil n x = u"
    unfolding dceil_def dcidx_def by simp
  from False have "\<not> x \<le> u"
    using Least_dgrid_le_iff2[of x n "2 ^ n"] by simp
  then have "min u x = u" by simp
  with dt show ?thesis
    using u_pos by simp
qed

lemma dceil_tendsto:
  assumes x: "0 \<le> x"
  shows "(\<lambda>n. dceil n x) \<longlonglongrightarrow> min u x"
proof (rule tendsto_sandwich
    [of "\<lambda>n. min u x" "\<lambda>n. dceil n x" sequentially
        "\<lambda>n. min u x + u / 2 ^ n"])
  show "\<forall>\<^sub>F n in sequentially. min u x \<le> dceil n x"
    using dceil_ge by simp
  show "\<forall>\<^sub>F n in sequentially. dceil n x \<le> min u x + u / 2 ^ n"
    using dceil_le[OF x] by simp
  show "(\<lambda>n. min u x) \<longlonglongrightarrow> min u x" by simp
  have "(\<lambda>n. u / 2 ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_divide_realpow_zero) simp
  then have "(\<lambda>n. min u x + u / 2 ^ n) \<longlonglongrightarrow> min u x + 0"
    by (intro tendsto_add tendsto_const)
  then show "(\<lambda>n. min u x + u / 2 ^ n) \<longlonglongrightarrow> min u x" by simp
qed

subsection \<open>The dyadic ceilings are simple stopping times\<close>

lemma simple_dyadic:
  "simple_stopped_martingale M F Z (dgrid n) (dtime n) (2 ^ n)"
proof -
  have mg: "martingale M F (0 :: real) Z"
    by unfold_locales
  have tg: "time_grid (dgrid n)"
    by (intro time_grid.intro) (auto intro: dgrid_nonneg dgrid_mono)
  have scm: "sampled_cont_martingale M F Z (dgrid n)"
    by (intro sampled_cont_martingale.intro mg tg)
  show ?thesis
  proof (intro simple_stopped_martingale.intro[OF scm]
      simple_stopped_martingale_axioms.intro)
    show "\<exists>m\<le>2 ^ n. dtime n \<omega> = dgrid n m" for \<omega>
    proof (intro exI[of _ "didx n \<omega>"] conjI)
      show "didx n \<omega> \<le> 2 ^ n"
        unfolding didx_def by simp
      show "dtime n \<omega> = dgrid n (didx n \<omega>)"
        unfolding dtime_def ..
    qed
    show "{\<omega> \<in> space M. dtime n \<omega> \<le> dgrid n j} \<in> sets (F (dgrid n j))" for j
    proof (cases "2 ^ n \<le> j")
      case True
      have "{\<omega> \<in> space M. dtime n \<omega> \<le> dgrid n j} = space M"
        using True by (auto simp: dtime_le_iff)
      moreover have "space (F (dgrid n j)) = space M"
        by (intro space_F dgrid_nonneg)
      ultimately show ?thesis
        using sets.top[of "F (dgrid n j)"] by simp
    next
      case False
      have "{\<omega> \<in> space M. dtime n \<omega> \<le> dgrid n j}
          = {\<omega> \<in> space M. tau \<omega> \<le> dgrid n j}"
        using False by (auto simp: dtime_le_iff)
      moreover have "{\<omega> \<in> space M. tau \<omega> \<le> dgrid n j} \<in> sets (F (dgrid n j))"
        by (intro tau_stop dgrid_nonneg)
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma dyadic_expectation: "(\<integral>\<omega>. Z (dtime n \<omega>) \<omega> \<partial>M) = (\<integral>\<omega>. Z 0 \<omega> \<partial>M)"
proof -
  have "(\<integral>\<omega>. Z (min (dgrid n (2 ^ n)) (dtime n \<omega>)) \<omega> \<partial>M)
      = (\<integral>\<omega>. Z (dgrid n 0) \<omega> \<partial>M)"
    by (rule simple_stopped_martingale.simple_optional_sampling[OF simple_dyadic])
  then show ?thesis
    by (simp add: min_absorb2 dtime_le_u)
qed

lemma dyadic_integrable: "integrable M (\<lambda>\<omega>. Z (dtime n \<omega>) \<omega>)"
proof -
  have "integrable M (\<lambda>\<omega>. Z (min (dgrid n (2 ^ n)) (dtime n \<omega>)) \<omega>)"
    by (rule simple_stopped_martingale.simple_stopped_integrable[OF simple_dyadic])
  then show ?thesis
    by (simp add: min_absorb2 dtime_le_u)
qed

subsection \<open>The limit\<close>

theorem optional_sampling:
  "(\<integral>\<omega>. Z (min u (tau \<omega>)) \<omega> \<partial>M) = (\<integral>\<omega>. Z 0 \<omega> \<partial>M)"
proof -
  have meas: "(\<lambda>\<omega>. Z (dtime n \<omega>) \<omega>) \<in> borel_measurable M" for n
    using dyadic_integrable[of n] by (rule borel_measurable_integrable)
  have bound: "AE \<omega> in M. norm (Z (dtime n \<omega>) \<omega>) \<le> D \<omega>" for n
    using Z_dom by eventually_elim (use dtime_nonneg dtime_le_u in auto)
  have lim: "AE \<omega> in M. (\<lambda>n. Z (dtime n \<omega>) \<omega>) \<longlonglongrightarrow> Z (min u (tau \<omega>)) \<omega>"
    using paths_cont AE_space
  proof eventually_elim
    case (elim \<omega>)
    then have cont: "continuous_on {0..u} (\<lambda>s. Z s \<omega>)" and w: "\<omega> \<in> space M"
      by auto
    have inS: "dtime n \<omega> \<in> {0..u}" for n
      using dtime_nonneg dtime_le_u by auto
    have limS: "min u (tau \<omega>) \<in> {0..u}"
      using tau_nonneg[OF w] u_pos by auto
    have seq: "\<And>x a. a \<in> {0..u} \<Longrightarrow> (\<forall>n. x n \<in> {0..u}) \<Longrightarrow> x \<longlonglongrightarrow> a
        \<Longrightarrow> ((\<lambda>s. Z s \<omega>) \<circ> x) \<longlonglongrightarrow> Z a \<omega>"
      using cont unfolding continuous_on_sequentially by blast
    have "((\<lambda>s. Z s \<omega>) \<circ> (\<lambda>n. dtime n \<omega>)) \<longlonglongrightarrow> Z (min u (tau \<omega>)) \<omega>"
    proof (rule seq)
      show "min u (tau \<omega>) \<in> {0..u}" by (rule limS)
      show "\<forall>n. dtime n \<omega> \<in> {0..u}" using inS by blast
      show "(\<lambda>n. dtime n \<omega>) \<longlonglongrightarrow> min u (tau \<omega>)"
        by (rule dtime_tendsto[OF w])
    qed
    then show ?case
      by (simp add: comp_def)
  qed
  have "(\<lambda>n. (\<integral>\<omega>. Z (dtime n \<omega>) \<omega> \<partial>M)) \<longlonglongrightarrow> (\<integral>\<omega>. Z (min u (tau \<omega>)) \<omega> \<partial>M)"
    by (intro integral_dominated_convergence[where w = D]
        stopped_measurable meas D_integrable lim bound)
  moreover have "(\<lambda>n. (\<integral>\<omega>. Z (dtime n \<omega>) \<omega> \<partial>M)) \<longlonglongrightarrow> (\<integral>\<omega>. Z 0 \<omega> \<partial>M)"
    by (simp add: dyadic_expectation)
  ultimately show ?thesis
    by (rule LIMSEQ_unique)
qed

subsection \<open>The localised limit: optional sampling over an event of the past\<close>

text \<open>Localising the limit argument to an event \<open>A\<close> of the past at a time
  \<open>v \<le> u\<close>.  The dyadic ceiling of \<open>v\<close> is a grid point above \<open>v\<close>, so \<open>A\<close>
  lies in the filtration at that grid point and the discrete localised
  identity applies; both sides then converge by dominated convergence.  This
  is the set-integral form of optional sampling, i.e. exactly what turns the
  stopped process into a martingale.\<close>

theorem set_optional_sampling:
  assumes v: "0 \<le> v" and vu: "v \<le> u" and A: "A \<in> sets (F v)"
    and meas_v: "(\<lambda>\<omega>. Z (min v (tau \<omega>)) \<omega>) \<in> borel_measurable M"
  shows "(\<integral>\<omega>. indicat_real A \<omega> * Z (min u (tau \<omega>)) \<omega> \<partial>M)
       = (\<integral>\<omega>. indicat_real A \<omega> * Z (min v (tau \<omega>)) \<omega> \<partial>M)"
proof -
  have A_M: "A \<in> sets M"
  proof -
    have "sets (F v) \<subseteq> sets M"
      using v by (intro sets_F_subset)
    then show ?thesis using A by blast
  qed
  have ind_le: "\<bar>indicat_real A \<omega> * y\<bar> \<le> \<bar>y\<bar>" for \<omega> y
    by (simp add: indicator_def)
  have v_le: "v \<le> dceil n v" for n
  proof -
    have "min u v \<le> dceil n v"
      by (rule dceil_ge)
    then show ?thesis using vu by simp
  qed
  have A_grid: "A \<in> sets (F (dgrid n (dcidx n v)))" for n
  proof -
    have "sets (F v) \<subseteq> sets (F (dceil n v))"
      using v v_le[of n] by (intro sets_F_mono)
    then show ?thesis
      using A unfolding dceil_def by blast
  qed
  have mix_integrable: "integrable M (\<lambda>\<omega>. Z (min (dceil n v) (dtime n \<omega>)) \<omega>)"
    for n
  proof -
    have "integrable M
        (\<lambda>\<omega>. Z (min (dgrid n (dcidx n v)) (dtime n \<omega>)) \<omega>)"
      by (rule simple_stopped_martingale.simple_stopped_integrable
          [OF simple_dyadic])
    then show ?thesis
      unfolding dceil_def .
  qed
  have level: "(\<integral>\<omega>. indicat_real A \<omega> * Z (dtime n \<omega>) \<omega> \<partial>M)
      = (\<integral>\<omega>. indicat_real A \<omega> * Z (min (dceil n v) (dtime n \<omega>)) \<omega> \<partial>M)"
    for n
  proof -
    have "set_lebesgue_integral M A
          (\<lambda>\<omega>. Z (min (dgrid n (2 ^ n)) (dtime n \<omega>)) \<omega>)
        = set_lebesgue_integral M A
          (\<lambda>\<omega>. Z (min (dgrid n (dcidx n v)) (dtime n \<omega>)) \<omega>)"
      by (rule simple_stopped_martingale.set_simple_optional_sampling
          [OF simple_dyadic A_grid dcidx_le])
    then show ?thesis
      unfolding set_lebesgue_integral_def dceil_def
      by (simp add: min_absorb2 dtime_le_u)
  qed
  have measu: "(\<lambda>\<omega>. indicat_real A \<omega> * Z (dtime n \<omega>) \<omega>) \<in> borel_measurable M"
    for n
  proof -
    have "(\<lambda>\<omega>. Z (dtime n \<omega>) \<omega>) \<in> borel_measurable M"
      using dyadic_integrable[of n] by (rule borel_measurable_integrable)
    then show ?thesis
      using A_M by (intro borel_measurable_times) simp_all
  qed
  have measmix: "(\<lambda>\<omega>. indicat_real A \<omega> * Z (min (dceil n v) (dtime n \<omega>)) \<omega>)
      \<in> borel_measurable M" for n
  proof -
    have "(\<lambda>\<omega>. Z (min (dceil n v) (dtime n \<omega>)) \<omega>) \<in> borel_measurable M"
      using mix_integrable[of n] by (rule borel_measurable_integrable)
    then show ?thesis
      using A_M by (intro borel_measurable_times) simp_all
  qed
  have boundu: "AE \<omega> in M.
      norm (indicat_real A \<omega> * Z (dtime n \<omega>) \<omega>) \<le> D \<omega>" for n
    using Z_dom
  proof eventually_elim
    case (elim \<omega>)
    have "\<bar>indicat_real A \<omega> * Z (dtime n \<omega>) \<omega>\<bar> \<le> \<bar>Z (dtime n \<omega>) \<omega>\<bar>"
      by (rule ind_le)
    also have "\<dots> \<le> D \<omega>"
      using elim dtime_nonneg dtime_le_u by blast
    finally show ?case by simp
  qed
  have boundmix: "AE \<omega> in M.
      norm (indicat_real A \<omega> * Z (min (dceil n v) (dtime n \<omega>)) \<omega>) \<le> D \<omega>"
    for n
    using Z_dom
  proof eventually_elim
    case (elim \<omega>)
    have nn: "0 \<le> min (dceil n v) (dtime n \<omega>)"
      by (intro min.boundedI dceil_nonneg dtime_nonneg)
    have ub: "min (dceil n v) (dtime n \<omega>) \<le> u"
      by (rule min.coboundedI1[OF dceil_le_u])
    have "\<bar>indicat_real A \<omega> * Z (min (dceil n v) (dtime n \<omega>)) \<omega>\<bar>
        \<le> \<bar>Z (min (dceil n v) (dtime n \<omega>)) \<omega>\<bar>"
      by (rule ind_le)
    also have "\<dots> \<le> D \<omega>"
      using elim nn ub by blast
    finally show ?case by simp
  qed
  have limu: "AE \<omega> in M. (\<lambda>n. indicat_real A \<omega> * Z (dtime n \<omega>) \<omega>)
      \<longlonglongrightarrow> indicat_real A \<omega> * Z (min u (tau \<omega>)) \<omega>"
    using paths_cont AE_space
  proof eventually_elim
    case (elim \<omega>)
    then have cont: "continuous_on {0..u} (\<lambda>s. Z s \<omega>)" and w: "\<omega> \<in> space M"
      by auto
    have seq: "\<And>x a. a \<in> {0..u} \<Longrightarrow> (\<forall>n. x n \<in> {0..u}) \<Longrightarrow> x \<longlonglongrightarrow> a
        \<Longrightarrow> ((\<lambda>s. Z s \<omega>) \<circ> x) \<longlonglongrightarrow> Z a \<omega>"
      using cont unfolding continuous_on_sequentially by blast
    have "((\<lambda>s. Z s \<omega>) \<circ> (\<lambda>n. dtime n \<omega>)) \<longlonglongrightarrow> Z (min u (tau \<omega>)) \<omega>"
    proof (rule seq)
      show "min u (tau \<omega>) \<in> {0..u}"
        using tau_nonneg[OF w] u_pos by auto
      show "\<forall>n. dtime n \<omega> \<in> {0..u}"
        using dtime_nonneg dtime_le_u by auto
      show "(\<lambda>n. dtime n \<omega>) \<longlonglongrightarrow> min u (tau \<omega>)"
        by (rule dtime_tendsto[OF w])
    qed
    then have "(\<lambda>n. Z (dtime n \<omega>) \<omega>) \<longlonglongrightarrow> Z (min u (tau \<omega>)) \<omega>"
      by (simp add: comp_def)
    then show ?case
      by (intro tendsto_mult tendsto_const)
  qed
  have limmix: "AE \<omega> in M.
      (\<lambda>n. indicat_real A \<omega> * Z (min (dceil n v) (dtime n \<omega>)) \<omega>)
      \<longlonglongrightarrow> indicat_real A \<omega> * Z (min v (tau \<omega>)) \<omega>"
    using paths_cont AE_space
  proof eventually_elim
    case (elim \<omega>)
    then have cont: "continuous_on {0..u} (\<lambda>s. Z s \<omega>)" and w: "\<omega> \<in> space M"
      by auto
    have seq: "\<And>x a. a \<in> {0..u} \<Longrightarrow> (\<forall>n. x n \<in> {0..u}) \<Longrightarrow> x \<longlonglongrightarrow> a
        \<Longrightarrow> ((\<lambda>s. Z s \<omega>) \<circ> x) \<longlonglongrightarrow> Z a \<omega>"
      using cont unfolding continuous_on_sequentially by blast
    have tmin: "(\<lambda>n. min (dceil n v) (dtime n \<omega>)) \<longlonglongrightarrow> min v (tau \<omega>)"
    proof -
      have c1: "(\<lambda>n. dceil n v) \<longlonglongrightarrow> min u v"
        by (rule dceil_tendsto[OF v])
      have c2: "(\<lambda>n. dtime n \<omega>) \<longlonglongrightarrow> min u (tau \<omega>)"
        by (rule dtime_tendsto[OF w])
      have "(\<lambda>n. min (dceil n v) (dtime n \<omega>))
          \<longlonglongrightarrow> min (min u v) (min u (tau \<omega>))"
        by (intro tendsto_min c1 c2)
      moreover have "min (min u v) (min u (tau \<omega>)) = min v (tau \<omega>)"
        using vu by (simp add: min_def)
      ultimately show ?thesis by simp
    qed
    have "((\<lambda>s. Z s \<omega>) \<circ> (\<lambda>n. min (dceil n v) (dtime n \<omega>)))
        \<longlonglongrightarrow> Z (min v (tau \<omega>)) \<omega>"
    proof (rule seq)
      show "min v (tau \<omega>) \<in> {0..u}"
        using tau_nonneg[OF w] v vu by auto
      show "\<forall>n. min (dceil n v) (dtime n \<omega>) \<in> {0..u}"
      proof
        fix n
        have "0 \<le> min (dceil n v) (dtime n \<omega>)"
          by (intro min.boundedI dceil_nonneg dtime_nonneg)
        moreover have "min (dceil n v) (dtime n \<omega>) \<le> u"
          by (rule min.coboundedI1[OF dceil_le_u])
        ultimately show "min (dceil n v) (dtime n \<omega>) \<in> {0..u}"
          by simp
      qed
      show "(\<lambda>n. min (dceil n v) (dtime n \<omega>)) \<longlonglongrightarrow> min v (tau \<omega>)"
        by (rule tmin)
    qed
    then have "(\<lambda>n. Z (min (dceil n v) (dtime n \<omega>)) \<omega>)
        \<longlonglongrightarrow> Z (min v (tau \<omega>)) \<omega>"
      by (simp add: comp_def)
    then show ?case
      by (intro tendsto_mult tendsto_const)
  qed
  have cu: "(\<lambda>n. (\<integral>\<omega>. indicat_real A \<omega> * Z (dtime n \<omega>) \<omega> \<partial>M))
      \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real A \<omega> * Z (min u (tau \<omega>)) \<omega> \<partial>M)"
  proof (intro integral_dominated_convergence[where w = D] measu D_integrable
      limu boundu)
    show "(\<lambda>\<omega>. indicat_real A \<omega> * Z (min u (tau \<omega>)) \<omega>)
        \<in> borel_measurable M"
      using stopped_measurable A_M by (intro borel_measurable_times) simp_all
  qed
  have cv: "(\<lambda>n. (\<integral>\<omega>. indicat_real A \<omega>
        * Z (min (dceil n v) (dtime n \<omega>)) \<omega> \<partial>M))
      \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real A \<omega> * Z (min v (tau \<omega>)) \<omega> \<partial>M)"
  proof (intro integral_dominated_convergence[where w = D] measmix
      D_integrable limmix boundmix)
    show "(\<lambda>\<omega>. indicat_real A \<omega> * Z (min v (tau \<omega>)) \<omega>)
        \<in> borel_measurable M"
      using meas_v A_M by (intro borel_measurable_times) simp_all
  qed
  from cu have "(\<lambda>n. (\<integral>\<omega>. indicat_real A \<omega>
        * Z (min (dceil n v) (dtime n \<omega>)) \<omega> \<partial>M))
      \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real A \<omega> * Z (min u (tau \<omega>)) \<omega> \<partial>M)"
    unfolding level .
  with cv show ?thesis
    by (rule LIMSEQ_unique[symmetric])
qed

theorem stopped_integrable: "integrable M (\<lambda>\<omega>. Z (min u (tau \<omega>)) \<omega>)"
proof -
  have bound: "AE \<omega> in M. norm (Z (min u (tau \<omega>)) \<omega>) \<le> norm (D \<omega>)"
    using Z_dom AE_space
  proof eventually_elim
    case (elim \<omega>)
    then have nn: "0 \<le> min u (tau \<omega>)"
      using tau_nonneg u_pos by auto
    have "norm (Z (min u (tau \<omega>)) \<omega>) \<le> D \<omega>"
      using elim nn by auto
    also have "D \<omega> \<le> norm (D \<omega>)" by simp
    finally show ?case .
  qed
  show ?thesis
    by (intro Bochner_Integration.integrable_bound[OF D_integrable]
        stopped_measurable bound)
qed

end

section \<open>Optional stopping: the stopped process is a martingale\<close>

text \<open>Doob's optional stopping theorem in process form.  Given a martingale
  with continuous paths that is dominated on every bounded time interval,
  and a stopping time \<open>tau\<close>, the stopped process is again a martingale.  The
  proof combines the localised sampling identity of the previous section,
  applied at a horizon beyond both times, with the characterisation of
  martingales by set integrals.  Adaptedness of the stopped process is a
  hypothesis: it is immediate in applications, whereas deriving it here would
  need a null-set completion argument.\<close>

theorem optional_stopping:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
    and D :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Z"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and paths: "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in M. continuous_on {0..u} (\<lambda>s. Z s \<omega>)"
    and dom: "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D u \<omega>"
    and D_int: "\<And>u. 0 < u \<Longrightarrow> integrable M (D u)"
    and stopped_adapted: "\<And>v. 0 \<le> v \<Longrightarrow>
      (\<lambda>\<omega>. Z (min v (tau \<omega>)) \<omega>) \<in> borel_measurable (F v)"
  shows "martingale M F 0 (\<lambda>v \<omega>. Z (min v (tau \<omega>)) \<omega>)"
proof -
  interpret Mg: martingale M F 0 Z
    by (rule mg)
  have fm: "filtered_measure M F (0 :: real)"
    by (intro filtered_measure.intro Mg.subalgebras Mg.sets_F_mono)
  have meas_M: "(\<lambda>\<omega>. Z (min v (tau \<omega>)) \<omega>) \<in> borel_measurable M"
    if v: "0 \<le> v" for v
    by (rule measurable_from_subalg[OF Mg.subalgebras[OF v]
          stopped_adapted[OF v]])
  have loc: "stopped_cont_martingale M F Z tau u (D u)" if u: "0 < u" for u
    using u by (intro stopped_cont_martingale.intro[OF mg]
        stopped_cont_martingale_axioms.intro tau_nonneg tau_stop
        paths[OF u] dom[OF u] D_int[OF u] meas_M) auto
  have int: "integrable M (\<lambda>\<omega>. Z (min i (tau \<omega>)) \<omega>)" if i: "0 \<le> i" for i
  proof -
    have u: "0 < i + 1" using i by simp
    have "AE \<omega> in M. norm (Z (min i (tau \<omega>)) \<omega>) \<le> norm (D (i + 1) \<omega>)"
      using dom[OF u] AE_space
    proof eventually_elim
      case (elim \<omega>)
      then have "0 \<le> min i (tau \<omega>)"
        using tau_nonneg i by auto
      moreover have "min i (tau \<omega>) \<le> i + 1" by simp
      ultimately have "\<bar>Z (min i (tau \<omega>)) \<omega>\<bar> \<le> D (i + 1) \<omega>"
        using elim by blast
      then show ?case by simp
    qed
    then show ?thesis
      by (intro Bochner_Integration.integrable_bound[OF D_int[OF u]]
          meas_M[OF i])
  qed
  show ?thesis
  proof (rule Mg.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>v \<omega>. Z (min v (tau \<omega>)) \<omega>)"
      by (intro adapted_process.intro[OF fm] adapted_process_axioms.intro
          stopped_adapted)
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. Z (min i (tau \<omega>)) \<omega>)"
      by (rule int)
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j" and A: "A \<in> sets (F i)"
    have j: "0 \<le> j" using i ij by simp
    have u: "0 < j + 1" using j by simp
    have iu: "i \<le> j + 1" using ij by simp
    have Aj: "A \<in> sets (F j)"
    proof -
      have "sets (F i) \<subseteq> sets (F j)"
        using i ij by (intro Mg.sets_F_mono)
      then show ?thesis using A by blast
    qed
    have ei: "(\<integral>\<omega>. indicat_real A \<omega> * Z (min (j + 1) (tau \<omega>)) \<omega> \<partial>M)
        = (\<integral>\<omega>. indicat_real A \<omega> * Z (min i (tau \<omega>)) \<omega> \<partial>M)"
      by (rule stopped_cont_martingale.set_optional_sampling
          [OF loc[OF u] i iu A meas_M[OF i]])
    have ej: "(\<integral>\<omega>. indicat_real A \<omega> * Z (min (j + 1) (tau \<omega>)) \<omega> \<partial>M)
        = (\<integral>\<omega>. indicat_real A \<omega> * Z (min j (tau \<omega>)) \<omega> \<partial>M)"
      by (rule stopped_cont_martingale.set_optional_sampling
          [OF loc[OF u] j _ Aj meas_M[OF j]]) simp
    show "set_lebesgue_integral M A (\<lambda>\<omega>. Z (min i (tau \<omega>)) \<omega>)
        = set_lebesgue_integral M A (\<lambda>\<omega>. Z (min j (tau \<omega>)) \<omega>)"
      using ei ej unfolding set_lebesgue_integral_def by simp
  qed
qed

end
