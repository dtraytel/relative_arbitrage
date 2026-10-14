

(*<*)
theory Quadratic_Variation
  imports "Martingales.Martingale" Power_Inequalities
begin

(*>*)

text \<open>
  Quadratic variation of square-integrable discrete-time martingales.

  The AFP entry Martingales provides filtrations, adapted and predictable
  processes, Banach-valued conditional expectation and martingales, but no
  quadratic variation and no optional sampling.  This theory supplies the
  first: for a square-integrable martingale \<open>X\<close> in discrete time, the
  quadratic variation \<open>[X]\<^sub>n = \<Sum>\<^sub>k\<^sub><\<^sub>n (X\<^sub>k\<^sub>+\<^sub>1 - X\<^sub>k)\<^sup>2\<close> compensates the
  square: \<open>X\<^sup>2 - [X]\<close> is again a martingale (the discrete Ito formula for
  the square function), whence the Dynkin identity
  \<open>E[X\<^sub>n\<^sup>2] = E[X\<^sub>0\<^sup>2] + E[[X]\<^sub>n]\<close>.

  The stopped process and its quadratic variation are defined here; the
  stopped Dynkin identity is in \<open>Optional_Sampling\<close>.\<close>
section \<open>Elementary square bounds\<close>


lemma integrable_prod_of_squares:
  fixes u v :: "'b \<Rightarrow> real"
  assumes usq: "integrable M (\<lambda>\<omega>. (u \<omega>)\<^sup>2)"
    and vsq: "integrable M (\<lambda>\<omega>. (v \<omega>)\<^sup>2)"
    and u [measurable]: "u \<in> borel_measurable M"
    and v [measurable]: "v \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. u \<omega> * v \<omega>)"
proof -
  have dom: "integrable M (\<lambda>\<omega>. (u \<omega>)\<^sup>2 + (v \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add usq vsq)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF dom])
  show "(\<lambda>\<omega>. u \<omega> * v \<omega>) \<in> borel_measurable M"
    by measurable
  show "AE \<omega> in M. norm (u \<omega> * v \<omega>) \<le> norm ((u \<omega>)\<^sup>2 + (v \<omega>)\<^sup>2)"
  proof (intro AE_I2)
    fix \<omega>
    have "\<bar>u \<omega> * v \<omega>\<bar> \<le> (u \<omega>)\<^sup>2 + (v \<omega>)\<^sup>2"
      by (rule abs_prod_le_sq)
    moreover have "0 \<le> (u \<omega>)\<^sup>2 + (v \<omega>)\<^sup>2"
      by simp
    ultimately show "norm (u \<omega> * v \<omega>) \<le> norm ((u \<omega>)\<^sup>2 + (v \<omega>)\<^sup>2)"
      by simp
  qed
  qed
qed

text \<open>A square-integrable function is integrable on a finite measure.\<close>

lemma integrable_of_sq_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes fm: "finite_measure N" and m: "f \<in> borel_measurable N"
    and sq: "integrable N (\<lambda>\<omega>. (f \<omega>)\<^sup>2)"
  shows "integrable N f"
proof (rule Bochner_Integration.integrable_bound)
  show "integrable N (\<lambda>\<omega>. 1 + (f \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add
        finite_measure.integrable_const[OF fm] sq)
  show "f \<in> borel_measurable N" by (rule m)
  show "AE \<omega> in N. norm (f \<omega>) \<le> norm (1 + (f \<omega>)\<^sup>2)"
  proof (intro AE_I2)
    fix \<omega>
    have nn: "(0::real) \<le> (1 - \<bar>f \<omega>\<bar>)\<^sup>2" by simp
    have exp: "(1 - \<bar>f \<omega>\<bar>)\<^sup>2 = 1 - 2 * \<bar>f \<omega>\<bar> + (f \<omega>)\<^sup>2"
      by (simp add: power2_diff)
    have "\<bar>f \<omega>\<bar> \<le> 1 + (f \<omega>)\<^sup>2"
      using nn abs_ge_zero[of "f \<omega>"] unfolding exp by linarith
    then show "norm (f \<omega>) \<le> norm (1 + (f \<omega>)\<^sup>2)" by simp
  qed
qed

section \<open>Quadratic variation\<close>

definition qvar :: "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "qvar X n \<omega> = (\<Sum>k<n. (X (Suc k) \<omega> - X k \<omega>)\<^sup>2)"

lemma qvar_zero [simp]: "qvar X 0 \<omega> = 0"
  by (simp add: qvar_def)

lemma qvar_Suc: "qvar X (Suc n) \<omega> = qvar X n \<omega> + (X (Suc n) \<omega> - X n \<omega>)\<^sup>2"
  by (simp add: qvar_def)

lemma qvar_nonneg: "0 \<le> qvar X n \<omega>"
  by (simp add: qvar_def sum_nonneg)

lemma qvar_mono:
  assumes "n \<le> m"
  shows "qvar X n \<omega> \<le> qvar X m \<omega>"
  unfolding qvar_def using assms by (intro sum_mono2) auto

section \<open>Square-integrable discrete-time martingales\<close>

locale sq_int_martingale = nat_sigma_finite_filtered_measure M F
  for M :: "'a measure" and F and X :: "nat \<Rightarrow> 'a \<Rightarrow> real" +
  assumes martingale_X: "martingale M F 0 X"
    and sq_integrable: "\<And>n. integrable M (\<lambda>\<omega>. (X n \<omega>)\<^sup>2)"

sublocale sq_int_martingale \<subseteq> Mg: martingale M F 0 X
  by (rule martingale_X)

context sq_int_martingale
begin

lemma X_integrable [intro, simp]: "integrable M (X n)"
  using Mg.integrable by simp

lemma X_measurable_F:
  assumes "j \<le> i"
  shows "X j \<in> borel_measurable (F i)"
  using assms by (intro Mg.adaptedD) auto

lemma X_measurable [measurable]: "X n \<in> borel_measurable M"
  using X_integrable[of n] by (rule borel_measurable_integrable)

subsection \<open>Integrability of increments and quadratic variation\<close>

lemma incr_sq_integrable: "integrable M (\<lambda>\<omega>. (X (Suc n) \<omega> - X n \<omega>)\<^sup>2)"
proof -
  have dom: "integrable M (\<lambda>\<omega>. 2 * (X (Suc n) \<omega>)\<^sup>2 + 2 * (X n \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add integrable_mult_right
        sq_integrable)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF dom])
  show "(\<lambda>\<omega>. (X (Suc n) \<omega> - X n \<omega>)\<^sup>2) \<in> borel_measurable M"
    by measurable
  show "AE \<omega> in M. norm ((X (Suc n) \<omega> - X n \<omega>)\<^sup>2)
      \<le> norm (2 * (X (Suc n) \<omega>)\<^sup>2 + 2 * (X n \<omega>)\<^sup>2)"
  proof (intro AE_I2)
    fix \<omega>
    have le: "(X (Suc n) \<omega> - X n \<omega>)\<^sup>2
        \<le> 2 * (X (Suc n) \<omega>)\<^sup>2 + 2 * (X n \<omega>)\<^sup>2"
      by (rule sq_diff_le)
    have nn: "0 \<le> 2 * (X (Suc n) \<omega>)\<^sup>2 + 2 * (X n \<omega>)\<^sup>2"
      by simp
    show "norm ((X (Suc n) \<omega> - X n \<omega>)\<^sup>2)
        \<le> norm (2 * (X (Suc n) \<omega>)\<^sup>2 + 2 * (X n \<omega>)\<^sup>2)"
      using le nn by simp
  qed
  qed
qed

lemma qvar_integrable [intro, simp]: "integrable M (qvar X n)"
  unfolding qvar_def
  by (intro Bochner_Integration.integrable_sum incr_sq_integrable)

lemma qvar_measurable_F: "qvar X n \<in> borel_measurable (F n)"
  unfolding qvar_def
proof (intro borel_measurable_sum)
  fix k assume k: "k \<in> {..<n}"
  have 1: "X (Suc k) \<in> borel_measurable (F n)"
    using k by (intro X_measurable_F) auto
  have 2: "X k \<in> borel_measurable (F n)"
    using k by (intro X_measurable_F) auto
  show "(\<lambda>\<omega>. (X (Suc k) \<omega> - X k \<omega>)\<^sup>2) \<in> borel_measurable (F n)"
    using 1 2 by measurable
qed

lemma sq_measurable_F: "(\<lambda>\<omega>. (X n \<omega>)\<^sup>2) \<in> borel_measurable (F n)"
proof -
  have "X n \<in> borel_measurable (F n)"
    by (intro X_measurable_F) auto
  then show ?thesis by measurable
qed

subsection \<open>Increments are conditionally orthogonal to the past\<close>

lemma incr_integrable: "integrable M (\<lambda>\<omega>. X (Suc n) \<omega> - X n \<omega>)"
  by (intro Bochner_Integration.integrable_diff X_integrable)

lemma cross_integrable:
  "integrable M (\<lambda>\<omega>. X n \<omega> * (X (Suc n) \<omega> - X n \<omega>))"
proof (rule integrable_prod_of_squares)
  show "integrable M (\<lambda>\<omega>. (X n \<omega>)\<^sup>2)"
    by (rule sq_integrable)
  show "integrable M (\<lambda>\<omega>. (X (Suc n) \<omega> - X n \<omega>)\<^sup>2)"
    by (rule incr_sq_integrable)
  show "X n \<in> borel_measurable M"
    by measurable
  show "(\<lambda>\<omega>. X (Suc n) \<omega> - X n \<omega>) \<in> borel_measurable M"
    by measurable
qed

lemma cross_cond_exp_zero:
  "AE \<omega> in M. cond_exp M (F n) (\<lambda>\<omega>. X n \<omega> * (X (Suc n) \<omega> - X n \<omega>)) \<omega> = 0"
proof -
  have pull: "AE \<omega> in M.
      cond_exp M (F n) (\<lambda>\<omega>. X n \<omega> * (X (Suc n) \<omega> - X n \<omega>)) \<omega>
      = X n \<omega> * cond_exp M (F n) (\<lambda>\<omega>. X (Suc n) \<omega> - X n \<omega>) \<omega>"
  proof (rule cond_exp_measurable_mult)
    show "integrable M (\<lambda>\<omega>. X n \<omega> * (X (Suc n) \<omega> - X n \<omega>))"
      by (rule cross_integrable)
    show "integrable M (\<lambda>\<omega>. X (Suc n) \<omega> - X n \<omega>)"
      by (rule incr_integrable)
    show "X n \<in> borel_measurable (F n)"
      by (intro X_measurable_F) auto
  qed
  have zero: "AE \<omega> in M.
      cond_exp M (F n) (\<lambda>\<omega>. X (Suc n) \<omega> - X n \<omega>) \<omega> = 0"
    by (rule Mg.cond_exp_diff_eq_zero) auto
  from pull zero show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then show ?case by simp
  qed
qed

subsection \<open>The compensated square is a martingale\<close>

text \<open>The discrete Ito formula for the square function: the compensator
  of the square of a square-integrable martingale is its quadratic
  variation.\<close>

theorem qvar_compensates:
  "martingale M F 0 (\<lambda>n \<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega>)"
proof (rule martingale_of_cond_exp_diff_Suc_eq_zero)
  show "adapted_process M F 0 (\<lambda>n \<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega>)"
  proof (unfold_locales)
    fix i :: nat assume "0 \<le> i"
    show "(\<lambda>\<omega>. (X i \<omega>)\<^sup>2 - qvar X i \<omega>) \<in> borel_measurable (F i)"
      using sq_measurable_F qvar_measurable_F by measurable
  qed
  show "\<And>i. integrable M (\<lambda>\<omega>. (X i \<omega>)\<^sup>2 - qvar X i \<omega>)"
    by (intro Bochner_Integration.integrable_diff sq_integrable
        qvar_integrable)
next
  fix i :: nat
  have fun_eq: "(\<lambda>\<omega>. ((X (Suc i) \<omega>)\<^sup>2 - qvar X (Suc i) \<omega>)
        - ((X i \<omega>)\<^sup>2 - qvar X i \<omega>))
      = (\<lambda>\<omega>. 2 * (X i \<omega> * (X (Suc i) \<omega> - X i \<omega>)))"
  proof
    fix \<omega>
    have "((X (Suc i) \<omega>)\<^sup>2 - qvar X (Suc i) \<omega>)
        - ((X i \<omega>)\<^sup>2 - qvar X i \<omega>)
        = (X (Suc i) \<omega>)\<^sup>2 - (X i \<omega>)\<^sup>2 - (X (Suc i) \<omega> - X i \<omega>)\<^sup>2"
      by (simp add: qvar_Suc)
    also have "\<dots> = 2 * (X i \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
      by (simp add: power2_diff power2_eq_square algebra_simps)
    finally show "((X (Suc i) \<omega>)\<^sup>2 - qvar X (Suc i) \<omega>)
        - ((X i \<omega>)\<^sup>2 - qvar X i \<omega>)
        = 2 * (X i \<omega> * (X (Suc i) \<omega> - X i \<omega>))" .
  qed
  have scale: "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. 2 * (X i \<omega> * (X (Suc i) \<omega> - X i \<omega>))) \<omega>
      = 2 * cond_exp M (F i) (\<lambda>\<omega>. X i \<omega> * (X (Suc i) \<omega> - X i \<omega>)) \<omega>"
    by (intro cond_exp_cmult cross_integrable)
  from scale cross_cond_exp_zero[of i]
  show "AE \<omega> in M. cond_exp M (F i)
      (\<lambda>\<omega>. ((X (Suc i) \<omega>)\<^sup>2 - qvar X (Suc i) \<omega>)
        - ((X i \<omega>)\<^sup>2 - qvar X i \<omega>)) \<omega> = 0"
    unfolding fun_eq
  proof eventually_elim
    case (elim \<omega>)
    then show ?case by simp
  qed
qed

subsection \<open>The Dynkin identity\<close>

text \<open>Taking expectations in the martingale property of \<open>X\<^sup>2 - [X]\<close>
  gives the Dynkin identity: the second moment grows exactly by the
  expected quadratic variation.\<close>

theorem expectation_sq_qvar:
  "(\<integral>\<omega>. (X n \<omega>)\<^sup>2 \<partial>M)
     = (\<integral>\<omega>. (X 0 \<omega>)\<^sup>2 \<partial>M) + (\<integral>\<omega>. qvar X n \<omega> \<partial>M)"
proof -
  interpret Q: martingale M F 0 "\<lambda>n \<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega>"
    by (rule qvar_compensates)
  have sp: "space M \<in> sets (F 0)"
    using sets.top[of "F 0"] by simp
  have int_n: "integrable M (\<lambda>\<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega>)"
    by (intro Bochner_Integration.integrable_diff sq_integrable
        qvar_integrable)
  have int_0: "integrable M (\<lambda>\<omega>. (X 0 \<omega>)\<^sup>2 - qvar X 0 \<omega>)"
    by (intro Bochner_Integration.integrable_diff sq_integrable
        qvar_integrable)
  have eq: "set_lebesgue_integral M (space M)
        (\<lambda>\<omega>. (X 0 \<omega>)\<^sup>2 - qvar X 0 \<omega>)
      = set_lebesgue_integral M (space M)
        (\<lambda>\<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega>)"
    by (rule Q.set_integral_eq[OF sp]) auto
  have l: "set_lebesgue_integral M (space M)
      (\<lambda>\<omega>. (X 0 \<omega>)\<^sup>2 - qvar X 0 \<omega>)
      = (\<integral>\<omega>. (X 0 \<omega>)\<^sup>2 - qvar X 0 \<omega> \<partial>M)"
    by (rule set_integral_space[OF int_0])
  have r: "set_lebesgue_integral M (space M)
      (\<lambda>\<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega>)
      = (\<integral>\<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega> \<partial>M)"
    by (rule set_integral_space[OF int_n])
  have step: "(\<integral>\<omega>. (X 0 \<omega>)\<^sup>2 - qvar X 0 \<omega> \<partial>M)
      = (\<integral>\<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega> \<partial>M)"
    using eq l r by simp
  have d0: "(\<integral>\<omega>. (X 0 \<omega>)\<^sup>2 - qvar X 0 \<omega> \<partial>M) = (\<integral>\<omega>. (X 0 \<omega>)\<^sup>2 \<partial>M)"
    by simp
  have dn: "(\<integral>\<omega>. (X n \<omega>)\<^sup>2 - qvar X n \<omega> \<partial>M)
      = (\<integral>\<omega>. (X n \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. qvar X n \<omega> \<partial>M)"
    by (rule Bochner_Integration.integral_diff[OF sq_integrable
        qvar_integrable])
  show ?thesis
    using step d0 dn by simp
qed

corollary expectation_sq_mono:
  assumes nm: "n \<le> m"
  shows "(\<integral>\<omega>. (X n \<omega>)\<^sup>2 \<partial>M) \<le> (\<integral>\<omega>. (X m \<omega>)\<^sup>2 \<partial>M)"
proof -
  have "(\<integral>\<omega>. qvar X n \<omega> \<partial>M) \<le> (\<integral>\<omega>. qvar X m \<omega> \<partial>M)"
    by (rule integral_mono_AE[OF qvar_integrable qvar_integrable])
      (intro AE_I2 qvar_mono[OF nm])
  then show ?thesis
    using expectation_sq_qvar[of n] expectation_sq_qvar[of m] by simp
qed

end

section \<open>The stopped process\<close>

text \<open>The process stopped at a random time \<open>T\<close>.  Optional sampling for it,
  with \<open>T\<close> a stopping time, is in \<open>Optional_Sampling\<close>.\<close>

definition stopped ::
  "('a \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "stopped T Y n \<omega> = Y (min n (T \<omega>)) \<omega>"

lemma stopped_0 [simp]: "stopped T Y 0 = Y 0"
  by (simp add: stopped_def fun_eq_iff)

lemma stopped_incr:
  "stopped T Y (Suc n) \<omega> - stopped T Y n \<omega>
     = (if n < T \<omega> then Y (Suc n) \<omega> - Y n \<omega> else 0)"
proof (cases "n < T \<omega>")
  case True
  then have "min (Suc n) (T \<omega>) = Suc n" and "min n (T \<omega>) = n"
    by auto
  with True show ?thesis by (simp add: stopped_def)
next
  case False
  then have "min (Suc n) (T \<omega>) = T \<omega>" and "min n (T \<omega>) = T \<omega>"
    by auto
  with False show ?thesis by (simp add: stopped_def)
qed

text \<open>The quadratic variation of the stopped process is the stopped
  quadratic variation.\<close>

lemma qvar_stopped: "qvar (stopped T Y) n \<omega> = qvar Y (min n (T \<omega>)) \<omega>"
proof -
  have "qvar (stopped T Y) n \<omega>
      = (\<Sum>k<n. (if k < T \<omega> then (Y (Suc k) \<omega> - Y k \<omega>)\<^sup>2 else 0))"
    unfolding qvar_def
  proof (intro sum.cong refl)
    fix k assume "k \<in> {..<n}"
    show "(stopped T Y (Suc k) \<omega> - stopped T Y k \<omega>)\<^sup>2
        = (if k < T \<omega> then (Y (Suc k) \<omega> - Y k \<omega>)\<^sup>2 else 0)"
      by (simp add: stopped_incr)
  qed
  also have "\<dots> = (\<Sum>k \<in> {..<n} \<inter> {k. k < T \<omega>}.
      (Y (Suc k) \<omega> - Y k \<omega>)\<^sup>2)"
    by (subst sum.inter_restrict) auto
  also have "\<dots> = (\<Sum>k < min n (T \<omega>). (Y (Suc k) \<omega> - Y k \<omega>)\<^sup>2)"
  proof -
    have "{..<n} \<inter> {k. k < T \<omega>} = {..< min n (T \<omega>)}"
      by auto
    then show ?thesis by simp
  qed
  finally show ?thesis
    by (simp add: qvar_def)
qed

(*<*)
end
(*>*)
