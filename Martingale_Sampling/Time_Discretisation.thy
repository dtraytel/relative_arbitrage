

(*<*)
theory Time_Discretisation
  imports Quadratic_Variation
begin

(*>*)

text \<open>
  Stochastic integration, layer 2: sampling a continuous-time
             martingale on a time grid.

    Every result of the discrete-time calculus (\<open>Quadratic_Variation\<close>:
    compensated square, optional sampling, stopped Dynkin identity) becomes
    available for a CONTINUOUS-TIME martingale along an arbitrary increasing
    grid of times, because the sampled process is a discrete-time
    square-integrable martingale for the sampled filtration.

    The payoff proved here:

      \<open>E[Y(t\<^sub>n)\<^sup>2] - E[Y(t\<^sub>0)\<^sup>2] = E[\<Sum>\<^sub>k<\<^sub>n (Y(t\<^sub>k\<^sub>+\<^sub>1) - Y(t\<^sub>k))\<^sup>2],\<close>

    i.e. the expected discrete quadratic variation of a continuous-time
    martingale along a grid depends only on the end points of the grid, not
    on the grid itself.  That is the first half of the construction of the
    quadratic variation <Y> (whose existence as a process is layer 3, and is
    what turns the martingale-problem assumption \<open>dynkin_quadratic\<close> of
    \<open>Volatile_Market\<close> into a theorem).\<close>
section \<open>Time grids\<close>

locale time_grid =
  fixes t :: "nat \<Rightarrow> real"
  assumes t_nonneg: "0 \<le> t 0"
    and t_step: "\<And>n. t n \<le> t (Suc n)"
begin

lemma t_mono_le: "m \<le> n \<Longrightarrow> t m \<le> t n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m \<le> n")
    case True
    then have "t m \<le> t n" by (rule Suc)
    also have "\<dots> \<le> t (Suc n)" by (rule t_step)
    finally show ?thesis .
  next
    case False
    with Suc have "m = Suc n" by simp
    then show ?thesis by simp
  qed
qed

lemma t_ge_0: "0 \<le> t n"
  using t_nonneg t_mono_le[of 0 n] by simp

end

section \<open>A continuous-time martingale sampled on a grid\<close>

locale sampled_martingale = martingale M F "0 :: real" Y + time_grid t
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" +
  assumes Y_sq_integrable: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (Y u \<omega>)\<^sup>2)"

sublocale sampled_martingale
  \<subseteq> D: sq_int_martingale M "\<lambda>n. F (t n)" "\<lambda>n. Y (t n)"
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
  have nsff: "nat_sigma_finite_filtered_measure M (\<lambda>n. F (t n))"
    by (rule nat_sigma_finite_filtered_measure.intro[OF sff])
  have ap: "adapted_process M (\<lambda>n. F (t n)) 0 (\<lambda>n. Y (t n))"
    by (intro adapted_process.intro[OF fm] adapted_process_axioms.intro)
      (intro adapted t_ge_0)
  have mg: "martingale M (\<lambda>n. F (t n)) 0 (\<lambda>n. Y (t n))"
  proof (intro martingale.intro[OF sff ap] martingale_axioms.intro)
    show "\<And>i :: nat. 0 \<le> i \<Longrightarrow> integrable M (Y (t i))"
      by (intro integrable t_ge_0)
    show "\<And>i j :: nat. 0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow>
        AE \<xi> in M. Y (t i) \<xi> = cond_exp M (F (t i)) (Y (t j)) \<xi>"
      by (intro martingale_property t_ge_0 t_mono_le)
  qed
  show "sq_int_martingale M (\<lambda>n. F (t n)) (\<lambda>n. Y (t n))"
    by (intro sq_int_martingale.intro[OF nsff] sq_int_martingale_axioms.intro
        mg) (intro Y_sq_integrable t_ge_0)
qed

context sampled_martingale
begin

text \<open>The discrete quadratic variation of the sampled process, written out.\<close>

lemma qvar_sampled_fun:
  "qvar (\<lambda>m. Y (t m)) n
     = (\<lambda>\<omega>. \<Sum>k<n. (Y (t (Suc k)) \<omega> - Y (t k) \<omega>)\<^sup>2)"
  by (rule ext) (simp add: qvar_def)

text \<open>The Dynkin identity along the grid: for a continuous-time
  square-integrable martingale, the expected sum of squared increments over
  a grid equals the increase of the second moment between the end points.
  In particular it does not depend on the grid in between.\<close>

theorem grid_expected_qvar:
  "(\<integral>\<omega>. (\<Sum>k<n. (Y (t (Suc k)) \<omega> - Y (t k) \<omega>)\<^sup>2) \<partial>M)
     = (\<integral>\<omega>. (Y (t n) \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. (Y (t 0) \<omega>)\<^sup>2 \<partial>M)"
proof -
  have "(\<integral>\<omega>. (Y (t n) \<omega>)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. (Y (t 0) \<omega>)\<^sup>2 \<partial>M)
        + (\<integral>\<omega>. qvar (\<lambda>m. Y (t m)) n \<omega> \<partial>M)"
    by (rule D.expectation_sq_qvar)
  then show ?thesis
    unfolding qvar_sampled_fun by simp
qed

text \<open>The compensated square along the grid is a martingale, and the
  optional-sampling results of @{theory Martingale_Sampling.Quadratic_Variation} apply verbatim to the
  sampled process.\<close>

theorem grid_qvar_compensates:
  "martingale M (\<lambda>n. F (t n)) 0
     (\<lambda>n \<omega>. (Y (t n) \<omega>)\<^sup>2 - qvar (\<lambda>m. Y (t m)) n \<omega>)"
  by (rule D.qvar_compensates)

theorem grid_expectation_sq_mono:
  assumes "m \<le> n"
  shows "(\<integral>\<omega>. (Y (t m) \<omega>)\<^sup>2 \<partial>M) \<le> (\<integral>\<omega>. (Y (t n) \<omega>)\<^sup>2 \<partial>M)"
  by (rule D.expectation_sq_mono[OF assms])

end

section \<open>Grid independence of the expected quadratic variation\<close>

text \<open>Two grids with the same end points give the same expected sum of
  squared increments.  This is the statement that makes the quadratic
  variation of a continuous-time martingale well defined in expectation,
  before any limit is taken.\<close>

theorem grid_expected_qvar_indep:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes A: "sampled_martingale M F Y t" and B: "sampled_martingale M F Y t'"
    and start: "t 0 = t' 0" and end_pt: "t n = t' n'"
  shows "(\<integral>\<omega>. (\<Sum>k<n. (Y (t (Suc k)) \<omega> - Y (t k) \<omega>)\<^sup>2) \<partial>M)
     = (\<integral>\<omega>. (\<Sum>k<n'. (Y (t' (Suc k)) \<omega> - Y (t' k) \<omega>)\<^sup>2) \<partial>M)"
proof -
  have "(\<integral>\<omega>. (\<Sum>k<n. (Y (t (Suc k)) \<omega> - Y (t k) \<omega>)\<^sup>2) \<partial>M)
      = (\<integral>\<omega>. (Y (t n) \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. (Y (t 0) \<omega>)\<^sup>2 \<partial>M)"
    by (rule sampled_martingale.grid_expected_qvar[OF A])
  also have "\<dots> = (\<integral>\<omega>. (Y (t' n') \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. (Y (t' 0) \<omega>)\<^sup>2 \<partial>M)"
    by (simp add: start end_pt)
  also have "\<dots> = (\<integral>\<omega>. (\<Sum>k<n'. (Y (t' (Suc k)) \<omega> - Y (t' k) \<omega>)\<^sup>2) \<partial>M)"
    by (rule sampled_martingale.grid_expected_qvar[OF B, symmetric])
  finally show ?thesis .
qed


(*<*)
end
(*>*)
