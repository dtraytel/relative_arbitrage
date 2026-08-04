(*
  Title:   Deterministic_Radius_Market.thy
  Content: Towards Example 3.1 of arXiv:2512.17702 for n - k = 1: the
           explicit trigonometric representation of the deterministic-radius
           market and its Gaussian toolkit.

  The process X_t = sqrt(|x|^2 + t) (cos(W_c(t) + phi), sin(W_c(t) + phi)),
  c(t) = ln(1 + t/|x|^2), is a martingale whose covariance is the sphere
  projection a(X) = I - X X^T/|X|^2; its radius is deterministic, so with
  the constant horizon tau = r^2 - |x|^2 it realises ball_v exactly and
  witnesses stopped_val_fn = ball_v at nonzero interior points for
  k = CARD('n) - 1.  See PLAN_THEOREM_1_1.md, item N4, for the brick
  sequence.  This theory provides bricks 1 and 2: the increment
  distribution of the product Brownian model and the characteristic
  function of gauss_measure.

  VERIFICATION NOTE: proved interactively against the running PIDE session
  (scratch with identical imports); the theory is registered in ROOT but a
  freshly started PIDE snapshots ROOT, so cross-check with the batch build.
*)

theory Deterministic_Radius_Market
  imports Brownian_Continuous
begin

section \<open>The coordinate increment of the product model is Gaussian\<close>

lemma bm_increment_distr:
  fixes i :: "'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s) = gauss_measure (t - s)"
proof -
  have cm: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i) \<in> bm_paths \<rightarrow>\<^sub>M wiener_pre"
    unfolding bm_paths_def
    by (rule measurable_component_singleton) simp
  have inc: "(\<lambda>\<omega>' :: real \<Rightarrow> real. \<omega>' t - \<omega>' s)
      \<in> wiener_pre \<rightarrow>\<^sub>M borel"
    using s st
    by (intro borel_measurable_diff measurable_coord) auto
  have "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s)
      = distr (distr bm_paths wiener_pre (\<lambda>\<omega>. \<omega> i)) borel
          (\<lambda>\<omega>'. \<omega>' t - \<omega>' s)"
    by (subst distr_distr[OF inc cm]) (simp add: o_def)
  also have "distr bm_paths wiener_pre (\<lambda>\<omega>. \<omega> i) = wiener_pre"
    by (rule bm_paths_component)
  also have "distr wiener_pre borel (\<lambda>\<omega>'. \<omega>' t - \<omega>' s)
      = gauss_measure (t - s)"
    by (rule wiener_pre_increment[OF s st])
  finally show ?thesis .
qed

section \<open>The characteristic function of \<open>gauss_measure\<close>\<close>

text \<open>Change of variables \<open>x = \<surd>v\<cdot>y\<close> reduces to the standard normal
  characteristic function of HOL-Probability.\<close>

lemma char_gauss_measure:
  assumes v: "0 < v"
  shows "char (gauss_measure v) a
      = complex_of_real (exp (- a\<^sup>2 * v / 2))"
proof -
  have sv: "0 < sqrt v" using v by simp
  have "char (gauss_measure v) a
      = (CLINT x|density lborel
          (\<lambda>x. ennreal (normal_density 0 (sqrt v) x)). iexp (a * x))"
    unfolding char_def gauss_measure_def using v by simp
  also have "\<dots> = (CLINT x|lborel.
      normal_density 0 (sqrt v) x *\<^sub>R iexp (a * x))"
    by (intro integral_density borel_measurable_normal_density)
      (auto simp: normal_density_nonneg)
  also have "\<dots> = \<bar>sqrt v\<bar> *\<^sub>R (CLINT y|lborel.
      normal_density 0 (sqrt v) (sqrt v * y)
        *\<^sub>R iexp (a * (sqrt v * y)))"
    by (rule lborel_integral_real_affine[where c = "sqrt v" and t = 0,
        simplified]) (use sv in simp)
  also have "\<dots> = (CLINT y|lborel. \<bar>sqrt v\<bar> *\<^sub>R
      (normal_density 0 (sqrt v) (sqrt v * y)
        *\<^sub>R iexp (a * (sqrt v * y))))"
    by (rule integral_scaleR_right[symmetric])
  also have "\<dots> = (CLINT y|lborel.
      std_normal_density y *\<^sub>R iexp ((a * sqrt v) * y))"
  proof (intro Bochner_Integration.integral_cong refl)
    fix y :: real
    have nd: "\<bar>sqrt v\<bar> * normal_density 0 (sqrt v) (sqrt v * y)
        = std_normal_density y"
      using sv
      by (simp add: normal_density_def std_normal_density_def
          power_mult_distrib abs_of_pos field_simps real_sqrt_mult)
    show "\<bar>sqrt v\<bar> *\<^sub>R (normal_density 0 (sqrt v) (sqrt v * y)
          *\<^sub>R iexp (a * (sqrt v * y)))
        = std_normal_density y *\<^sub>R iexp ((a * sqrt v) * y)"
      using nd by (simp add: mult.assoc mult.left_commute)
  qed
  also have "\<dots> = (CLINT y|std_normal_distribution.
      iexp ((a * sqrt v) * y))"
    by (intro integral_density[symmetric])
      (auto simp: std_normal_density_def)
  also have "\<dots> = char std_normal_distribution (a * sqrt v)"
    unfolding char_def ..
  also have "\<dots> = complex_of_real (exp (- (a * sqrt v)\<^sup>2 / 2))"
    by (simp add: char_std_normal_distribution)
  also have "(a * sqrt v)\<^sup>2 = a\<^sup>2 * v"
    using v by (simp add: power_mult_distrib)
  finally show ?thesis by simp
qed

section \<open>Trigonometric moments of \<open>gauss_measure\<close>\<close>

text \<open>Real and imaginary parts of the characteristic function; the
  degenerate case \<open>v = 0\<close> is the point mass at the origin.\<close>

lemma gauss_measure_cos:
  assumes v: "0 \<le> v"
  shows "(\<integral>y. cos (a * y) \<partial>gauss_measure v) = exp (- a\<^sup>2 * v / 2)"
proof (cases "v = 0")
  case True
  then have g0: "gauss_measure v = return borel 0"
    by (simp add: gauss_measure_def)
  show ?thesis
    unfolding g0 using True by (subst integral_return) auto
next
  case False
  with v have v': "0 < v" by simp
  interpret G: prob_space "gauss_measure v"
    by (rule prob_space_gauss_measure)
  have setsG: "sets (gauss_measure v) = sets borel"
    using v' by (simp add: gauss_measure_def)
  have fm': "(\<lambda>y :: real. complex_of_real (a * y))
      \<in> borel_measurable borel"
    by measurable
  have fm: "(\<lambda>y. complex_of_real (a * y))
      \<in> borel_measurable (gauss_measure v)"
    using fm' measurable_cong_sets[OF setsG refl] by blast
  have ii: "complex_integrable (gauss_measure v) (\<lambda>y. iexp (a * y))"
    using G.integrable_iexp[OF fm] by simp
  have iic: "complex_integrable (gauss_measure v) (\<lambda>y. cis (a * y))"
    using ii by (simp add: cis_conv_exp)
  have "(\<integral>y. cos (a * y) \<partial>gauss_measure v)
      = (\<integral>y. Re (cis (a * y)) \<partial>gauss_measure v)"
    by simp
  also have "\<dots> = Re (CLINT y|gauss_measure v. cis (a * y))"
    by (rule integral_Re[OF iic])
  also have "\<dots> = Re (char (gauss_measure v) a)"
    unfolding char_def by (simp add: cis_conv_exp)
  also have "\<dots> = exp (- a\<^sup>2 * v / 2)"
    by (simp add: char_gauss_measure[OF v'])
  finally show ?thesis .
qed

lemma gauss_measure_sin:
  assumes v: "0 \<le> v"
  shows "(\<integral>y. sin (a * y) \<partial>gauss_measure v) = 0"
proof (cases "v = 0")
  case True
  then have g0: "gauss_measure v = return borel 0"
    by (simp add: gauss_measure_def)
  show ?thesis
    unfolding g0 by (subst integral_return) auto
next
  case False
  with v have v': "0 < v" by simp
  interpret G: prob_space "gauss_measure v"
    by (rule prob_space_gauss_measure)
  have setsG: "sets (gauss_measure v) = sets borel"
    using v' by (simp add: gauss_measure_def)
  have fm': "(\<lambda>y :: real. complex_of_real (a * y))
      \<in> borel_measurable borel"
    by measurable
  have fm: "(\<lambda>y. complex_of_real (a * y))
      \<in> borel_measurable (gauss_measure v)"
    using fm' measurable_cong_sets[OF setsG refl] by blast
  have ii: "complex_integrable (gauss_measure v) (\<lambda>y. iexp (a * y))"
    using G.integrable_iexp[OF fm] by simp
  have iic: "complex_integrable (gauss_measure v) (\<lambda>y. cis (a * y))"
    using ii by (simp add: cis_conv_exp)
  have "(\<integral>y. sin (a * y) \<partial>gauss_measure v)
      = (\<integral>y. Im (cis (a * y)) \<partial>gauss_measure v)"
    by simp
  also have "\<dots> = Im (CLINT y|gauss_measure v. cis (a * y))"
    by (rule integral_Im[OF iic])
  also have "\<dots> = Im (char (gauss_measure v) a)"
    unfolding char_def by (simp add: cis_conv_exp)
  also have "\<dots> = 0"
    by (simp add: char_gauss_measure[OF v'])
  finally show ?thesis .
qed

section \<open>Conditional expectation of a function of an increment\<close>

text \<open>A bounded measurable function of a coordinate increment has as its
  conditional expectation, given the natural filtration of the market
  process at the earlier time, simply its Gaussian mean: the past and the
  increment are independent (\<open>bm_indicator_increment_indep_var\<close>), so the
  set-integral characterisation factorises.  Note the qualified locale
  name: \<open>Kolmogorov_Chentsov\<close> shadows the \<open>Martingales\<close> notion of
  \<open>stochastic_process\<close> in this import closure.\<close>

lemma bm_increment_has_cond_exp:
  fixes g :: "real \<Rightarrow> real" and i :: "'n::finite" and x0 :: "real^'n"
  assumes s: "0 \<le> s" and st: "s < t"
    and gm: "g \<in> borel_measurable borel" and gb: "\<And>y. \<bar>g y\<bar> \<le> C"
  shows "has_cond_exp (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (bmX x0) s)
      (\<lambda>\<omega>. g (\<omega> i t - \<omega> i s))
      (\<lambda>\<omega>. \<integral>y. g y \<partial>gauss_measure (t - s))"
proof (rule has_cond_expI')
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s"
  let ?c = "\<integral>y. g y \<partial>gauss_measure (t - s)"
  have t0: "0 \<le> t" using s st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have Dm: "?D \<in> borel_measurable ?M"
    using s t0
    by (intro borel_measurable_diff measurable_bm_coordinate) auto
  have gDm: "(\<lambda>\<omega>. g (?D \<omega>)) \<in> borel_measurable ?M"
    by (rule measurable_compose[OF Dm gm])
  have int_gD: "integrable ?M (\<lambda>\<omega>. g (?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = C])
      (use gb gDm in \<open>auto intro!: AE_I2\<close>)
  show "integrable ?M (\<lambda>\<omega>. g (?D \<omega>))" by (rule int_gD)
  show "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. ?c)" by simp
  show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. ?c) \<in> borel_measurable ?F"
    by simp
  fix A assume A: "A \<in> sets ?F"
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have indA_int: "integrable ?M (indicat_real A)"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use A_M in \<open>auto intro!: AE_I2 simp: indicator_def\<close>)
  have iv: "BMP.indep_var borel (indicat_real A) borel (\<lambda>\<omega>. g (?D \<omega>))"
    using BMP.indep_var_compose[OF bm_indicator_increment_indep_var
        [OF s st A] measurable_ident gm]
    by (simp add: o_def)
  have EgD: "(\<integral>\<omega>. g (?D \<omega>) \<partial>?M) = ?c"
  proof -
    have "(\<integral>\<omega>. g (?D \<omega>) \<partial>?M) = (\<integral>y. g y \<partial>distr ?M borel ?D)"
      by (rule Bochner_Integration.integral_distr[OF Dm gm, symmetric])
    also have "distr ?M borel ?D = gauss_measure (t - s)"
      by (rule bm_increment_distr[OF s less_imp_le[OF st]])
    finally show ?thesis .
  qed
  have "(\<integral>\<omega> \<in> A. g (?D \<omega>) \<partial>?M)
      = (\<integral>\<omega>. indicat_real A \<omega> * g (?D \<omega>) \<partial>?M)"
    unfolding set_lebesgue_integral_def by (simp add: mult.commute)
  also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> \<partial>?M) * (\<integral>\<omega>. g (?D \<omega>) \<partial>?M)"
    by (rule BMP.indep_var_lebesgue_integral[OF iv indA_int int_gD])
  also have "\<dots> = measure ?M A * ?c"
    using A_M EgD by simp
  also have "\<dots> = (\<integral>\<omega> \<in> A. ?c \<partial>?M)"
    unfolding set_lebesgue_integral_def
    using A_M by (simp add: finite_measure.emeasure_eq_measure
        [OF BMP.finite_measure])
  finally show "(\<integral>\<omega> \<in> A. g (?D \<omega>) \<partial>?M) = (\<integral>\<omega> \<in> A. ?c \<partial>?M)" .
qed

lemma bm_increment_cond_exp_AE:
  fixes g :: "real \<Rightarrow> real" and i :: "'n::finite" and x0 :: "real^'n"
  assumes s: "0 \<le> s" and st: "s < t"
    and gm: "g \<in> borel_measurable borel" and gb: "\<And>y. \<bar>g y\<bar> \<le> C"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cond_exp bm_paths (natural_filtration bm_paths 0 (bmX x0) s)
        (\<lambda>\<omega>. g (\<omega> i t - \<omega> i s)) \<omega>
      = (\<integral>y. g y \<partial>gauss_measure (t - s))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fm
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  show ?thesis
    using sigma_finite_subalgebra.has_cond_exp_charact(2)
        [OF sfs bm_increment_has_cond_exp[OF s st gm gb]]
    by eventually_elim simp
qed

end
