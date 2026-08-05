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


text \<open>Generalize the indicator/increment independence to any past-measurable
  real variable (the proof of \<open>bm_indicator_increment_indep_var\<close> verbatim,
  with the indicator replaced by \<open>Z\<close>).\<close>

lemma bm_past_increment_indep_var:
  fixes x0 :: "real^'n::finite" and Z :: "('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
  assumes s: "0 \<le> s" and st: "s < t"
    and Zm: "Z \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "BMP.indep_var borel Z
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  let ?V = "vimage_algebra (space ?M) ?D borel"
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have Z_M: "Z \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg Zm])
  have base: "BMP.indep_set (sets ?F) (sets ?V)"
    by (rule bm_filtration_increment_indep[OF s st])
  have L: "sigma_sets (space ?M)
      {Z -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets ?F"
  proof -
    have gen: "{Z -` B \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?F"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have ZB: "Z -` B \<inter> space ?F \<in> sets ?F"
        by (rule measurable_sets[OF Zm B])
      have "space ?F = space ?M"
        using subalg by (auto simp: subalgebra_def)
      then show "Z -` B \<inter> space ?M \<in> sets ?F"
        using ZB by simp
    qed
    show ?thesis
      using sets.sigma_sets_subset[OF gen] by simp
  qed
  have nth_meas: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis
      by simp
  qed
  have Dcomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
      = (\<lambda>\<omega>. ?D \<omega> $ i)"
    by (simp add: fun_eq_iff bmX_def)
  have R: "sigma_sets (space ?M)
      {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?V"
  proof -
    have gen: "{(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
        \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?V"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have Ci: "(\<lambda>v :: real^'n. v $ i) -` B \<in> sets borel"
        using measurable_sets[OF nth_meas B] by simp
      have veq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
          \<inter> space ?M
          = ?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M"
        unfolding Dcomp by auto
      have "?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M
          \<in> {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        using Ci by blast
      then have "?D -` ((\<lambda>v. v $ i) -` B) \<inter> space ?M
          \<in> sigma_sets (space ?M) {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        by (rule sigma_sets.Basic)
      then show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B
          \<inter> space ?M \<in> sets ?V"
        unfolding veq sets_vimage_algebra .
    qed
    show ?thesis
      using sets.sigma_sets_subset[OF gen] by simp
  qed
  show ?thesis
    unfolding BMP.indep_var_eq
  proof (intro conjI)
    show "Z \<in> borel_measurable ?M"
      by (rule Z_M)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
        \<in> borel_measurable ?M"
      using s st
      by (intro borel_measurable_diff measurable_bm_coordinate) auto
    have "BMP.indep_sets (case_bool (sets ?F) (sets ?V)) UNIV"
      using base unfolding BMP.indep_set_def .
    then have "BMP.indep_sets (case_bool
        (sigma_sets (space ?M)
          {Z -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})) UNIV"
      by (rule BMP.indep_sets_mono_sets)
        (auto split: bool.split simp: L R)
    then show "BMP.indep_set
        (sigma_sets (space ?M)
          {Z -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})"
      unfolding BMP.indep_set_def .
  qed
qed


lemma bm_past_increment_cond_exp:
  fixes g :: "real \<Rightarrow> real"
    and Z :: "('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
    and i :: 'n and x0 :: "real^'n"
  assumes s: "0 \<le> s" and st: "s < t"
    and Zm: "Z \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
    and Zb: "\<And>\<omega>. \<bar>Z \<omega>\<bar> \<le> B"
    and gm: "g \<in> borel_measurable borel" and gb: "\<And>y. \<bar>g y\<bar> \<le> C"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cond_exp bm_paths (natural_filtration bm_paths 0 (bmX x0) s)
        (\<lambda>\<omega>. Z \<omega> * g (\<omega> i t - \<omega> i s)) \<omega>
      = Z \<omega> * (\<integral>y. g y \<partial>gauss_measure (t - s))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s"
  let ?c = "\<integral>y. g y \<partial>gauss_measure (t - s)"
  have t0: "0 \<le> t" using s st by simp
  have B0: "0 \<le> B" using Zb[of undefined] by auto
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have Z_M: "Z \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg Zm])
  have Dm: "?D \<in> borel_measurable ?M"
    using s t0
    by (intro borel_measurable_diff measurable_bm_coordinate) auto
  have gDm: "(\<lambda>\<omega>. g (?D \<omega>)) \<in> borel_measurable ?M"
    by (rule measurable_compose[OF Dm gm])
  have int_gD: "integrable ?M (\<lambda>\<omega>. g (?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = C])
      (use gb gDm in \<open>auto intro!: AE_I2\<close>)
  have int_Z: "integrable ?M Z"
    by (rule BMP.integrable_const_bound[where B = B])
      (use Zb Z_M in \<open>auto intro!: AE_I2\<close>)
  have int_ZgD: "integrable ?M (\<lambda>\<omega>. Z \<omega> * g (?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = "B * C"])
      (use Zb gb Z_M gDm in
        \<open>auto intro!: AE_I2 mult_mono' abs_ge_zero
          simp: abs_mult intro: order_trans\<close>)
  have hce: "has_cond_exp ?M ?F (\<lambda>\<omega>. Z \<omega> * g (?D \<omega>)) (\<lambda>\<omega>. Z \<omega> * ?c)"
  proof (rule has_cond_expI')
    show "integrable ?M (\<lambda>\<omega>. Z \<omega> * g (?D \<omega>))" by (rule int_ZgD)
    show "integrable ?M (\<lambda>\<omega>. Z \<omega> * ?c)"
      by (rule integrable_mult_left[OF int_Z])
    show "(\<lambda>\<omega>. Z \<omega> * ?c) \<in> borel_measurable ?F"
      by (intro borel_measurable_times Zm borel_measurable_const)
    fix A assume A: "A \<in> sets ?F"
    have A_M: "A \<in> sets ?M"
      using A subalg by (auto simp: subalgebra_def)
    have iAZ_F: "(\<lambda>\<omega>. indicat_real A \<omega> * Z \<omega>) \<in> borel_measurable ?F"
      by (intro borel_measurable_times borel_measurable_indicator[OF A] Zm)
    have iAZ_M: "(\<lambda>\<omega>. indicat_real A \<omega> * Z \<omega>) \<in> borel_measurable ?M"
      by (rule measurable_from_subalg[OF subalg iAZ_F])
    have int_iAZ: "integrable ?M (\<lambda>\<omega>. indicat_real A \<omega> * Z \<omega>)"
      by (rule BMP.integrable_const_bound[where B = B])
        (use Zb iAZ_M B0 in
          \<open>auto intro!: AE_I2 simp: abs_mult indicator_def\<close>)
    have iv: "BMP.indep_var borel (\<lambda>\<omega>. indicat_real A \<omega> * Z \<omega>)
        borel (\<lambda>\<omega>. g (?D \<omega>))"
      using BMP.indep_var_compose[OF bm_past_increment_indep_var
          [OF s st iAZ_F] measurable_ident gm]
      by (simp add: o_def)
    have EgD: "(\<integral>\<omega>. g (?D \<omega>) \<partial>?M) = ?c"
    proof -
      have "(\<integral>\<omega>. g (?D \<omega>) \<partial>?M) = (\<integral>y. g y \<partial>distr ?M borel ?D)"
        by (rule Bochner_Integration.integral_distr[OF Dm gm, symmetric])
      also have "distr ?M borel ?D = gauss_measure (t - s)"
        by (rule bm_increment_distr[OF s less_imp_le[OF st]])
      finally show ?thesis .
    qed
    have "(\<integral>\<omega> \<in> A. Z \<omega> * g (?D \<omega>) \<partial>?M)
        = (\<integral>\<omega>. (indicat_real A \<omega> * Z \<omega>) * g (?D \<omega>) \<partial>?M)"
      unfolding set_lebesgue_integral_def
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: mult.assoc)
    also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * Z \<omega> \<partial>?M)
        * (\<integral>\<omega>. g (?D \<omega>) \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral[OF iv int_iAZ int_gD])
    also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * Z \<omega> \<partial>?M) * ?c"
      using EgD by simp
    also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * (Z \<omega> * ?c) \<partial>?M)"
      by (simp add: mult.assoc[symmetric])
    also have "\<dots> = (\<integral>\<omega> \<in> A. Z \<omega> * ?c \<partial>?M)"
      unfolding set_lebesgue_integral_def
      by (intro Bochner_Integration.integral_cong refl) simp
    finally show "(\<integral>\<omega> \<in> A. Z \<omega> * g (?D \<omega>) \<partial>?M)
        = (\<integral>\<omega> \<in> A. Z \<omega> * ?c \<partial>?M)" .
  qed
  show ?thesis
    using sigma_finite_subalgebra.has_cond_exp_charact(2)[OF sfs hce]
    by eventually_elim simp
qed


lemma bm_cos_cond_exp:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cond_exp bm_paths (natural_filtration bm_paths 0 (bmX x0) s)
        (\<lambda>\<omega>. cos (a * \<omega> i t + b)) \<omega>
      = cos (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s"
  have ts0: "0 \<le> t - s" using st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have bs: "bmX x0 s \<in> borel_measurable ?F"
    by (rule Stochastic_Process.adapted_process.adapted[OF
        Stochastic_Process.stochastic_process.adapted_process_natural_filtration
        [OF SPfact] s])
  have nth: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have wsF: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable ?F"
  proof -
    have eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s)
        = (\<lambda>\<omega>. (bmX x0 s \<omega> - x0) $ i)"
      by (simp add: fun_eq_iff bmX_def)
    show ?thesis
      unfolding eq
      by (intro measurable_compose[OF _ nth] borel_measurable_diff bs
          borel_measurable_const)
  qed
  have Z1F: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i s + b))
      \<in> borel_measurable ?F"
    using wsF by measurable
  have Z2F: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i s + b))
      \<in> borel_measurable ?F"
    using wsF by measurable
  have cosm: "(\<lambda>y :: real. cos (a * y)) \<in> borel_measurable borel"
    by measurable
  have sinm: "(\<lambda>y :: real. sin (a * y)) \<in> borel_measurable borel"
    by measurable
  have T1: "AE \<omega> in ?M. cond_exp ?M ?F
      (\<lambda>\<omega>. cos (a * \<omega> i s + b) * cos (a * ?D \<omega>)) \<omega>
      = cos (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
    using bm_past_increment_cond_exp[OF s st Z1F _ cosm,
        of 1 1, simplified]
    by (simp add: gauss_measure_cos[OF ts0])
  have T2: "AE \<omega> in ?M. cond_exp ?M ?F
      (\<lambda>\<omega>. sin (a * \<omega> i s + b) * sin (a * ?D \<omega>)) \<omega> = 0"
    using bm_past_increment_cond_exp[OF s st Z2F _ sinm,
        of 1 1, simplified]
    by (simp add: gauss_measure_sin[OF ts0])
  have Dm: "?D \<in> borel_measurable ?M"
    using s st
    by (intro borel_measurable_diff measurable_bm_coordinate) auto
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have Z1M: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i s + b))
      \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg Z1F])
  have Z2M: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i s + b))
      \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg Z2F])
  have m1: "(\<lambda>\<omega>. cos (a * \<omega> i s + b) * cos (a * ?D \<omega>))
      \<in> borel_measurable ?M"
    using Z1M Dm by measurable
  have m2: "(\<lambda>\<omega>. sin (a * \<omega> i s + b) * sin (a * ?D \<omega>))
      \<in> borel_measurable ?M"
    using Z2M Dm by measurable
  have int1: "integrable ?M
      (\<lambda>\<omega>. cos (a * \<omega> i s + b) * cos (a * ?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use m1 in \<open>auto intro!: AE_I2 mult_le_one
        abs_cos_le_one abs_sin_le_one simp: abs_mult\<close>)
  have int2: "integrable ?M
      (\<lambda>\<omega>. sin (a * \<omega> i s + b) * sin (a * ?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use m2 in \<open>auto intro!: AE_I2 mult_le_one
        abs_cos_le_one abs_sin_le_one simp: abs_mult\<close>)
  have fun_eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i t + b))
      = (\<lambda>\<omega>. cos (a * \<omega> i s + b) * cos (a * ?D \<omega>)
          - sin (a * \<omega> i s + b) * sin (a * ?D \<omega>))"
    by (rule ext) (simp add: cos_add[symmetric] algebra_simps)
  have "AE \<omega> in ?M. cond_exp ?M ?F
      (\<lambda>\<omega>. cos (a * \<omega> i s + b) * cos (a * ?D \<omega>)
        - sin (a * \<omega> i s + b) * sin (a * ?D \<omega>)) \<omega>
      = cond_exp ?M ?F (\<lambda>\<omega>. cos (a * \<omega> i s + b) * cos (a * ?D \<omega>)) \<omega>
        - cond_exp ?M ?F (\<lambda>\<omega>. sin (a * \<omega> i s + b) * sin (a * ?D \<omega>)) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff[OF sfs int1 int2])
  with T1 T2 show ?thesis
    unfolding fun_eq by eventually_elim simp
qed


lemma bm_sin_cond_exp:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cond_exp bm_paths (natural_filtration bm_paths 0 (bmX x0) s)
        (\<lambda>\<omega>. sin (a * \<omega> i t + b)) \<omega>
      = sin (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s"
  have ts0: "0 \<le> t - s" using st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have bs: "bmX x0 s \<in> borel_measurable ?F"
    by (rule Stochastic_Process.adapted_process.adapted[OF
        Stochastic_Process.stochastic_process.adapted_process_natural_filtration
        [OF SPfact] s])
  have nth: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have wsF: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable ?F"
  proof -
    have eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s)
        = (\<lambda>\<omega>. (bmX x0 s \<omega> - x0) $ i)"
      by (simp add: fun_eq_iff bmX_def)
    show ?thesis
      unfolding eq
      by (intro measurable_compose[OF _ nth] borel_measurable_diff bs
          borel_measurable_const)
  qed
  have Z1F: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i s + b))
      \<in> borel_measurable ?F"
    using wsF by measurable
  have Z2F: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i s + b))
      \<in> borel_measurable ?F"
    using wsF by measurable
  have cosm: "(\<lambda>y :: real. cos (a * y)) \<in> borel_measurable borel"
    by measurable
  have sinm: "(\<lambda>y :: real. sin (a * y)) \<in> borel_measurable borel"
    by measurable
  have T1: "AE \<omega> in ?M. cond_exp ?M ?F
      (\<lambda>\<omega>. sin (a * \<omega> i s + b) * cos (a * ?D \<omega>)) \<omega>
      = sin (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
    using bm_past_increment_cond_exp[OF s st Z1F _ cosm,
        of 1 1, simplified]
    by (simp add: gauss_measure_cos[OF ts0])
  have T2: "AE \<omega> in ?M. cond_exp ?M ?F
      (\<lambda>\<omega>. cos (a * \<omega> i s + b) * sin (a * ?D \<omega>)) \<omega> = 0"
    using bm_past_increment_cond_exp[OF s st Z2F _ sinm,
        of 1 1, simplified]
    by (simp add: gauss_measure_sin[OF ts0])
  have Dm: "?D \<in> borel_measurable ?M"
    using s st
    by (intro borel_measurable_diff measurable_bm_coordinate) auto
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have Z1M: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i s + b))
      \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg Z1F])
  have Z2M: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i s + b))
      \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg Z2F])
  have m1: "(\<lambda>\<omega>. sin (a * \<omega> i s + b) * cos (a * ?D \<omega>))
      \<in> borel_measurable ?M"
    using Z1M Dm by measurable
  have m2: "(\<lambda>\<omega>. cos (a * \<omega> i s + b) * sin (a * ?D \<omega>))
      \<in> borel_measurable ?M"
    using Z2M Dm by measurable
  have int1: "integrable ?M
      (\<lambda>\<omega>. sin (a * \<omega> i s + b) * cos (a * ?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use m1 in \<open>auto intro!: AE_I2 mult_le_one
        abs_cos_le_one abs_sin_le_one simp: abs_mult\<close>)
  have int2: "integrable ?M
      (\<lambda>\<omega>. cos (a * \<omega> i s + b) * sin (a * ?D \<omega>))"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use m2 in \<open>auto intro!: AE_I2 mult_le_one
        abs_cos_le_one abs_sin_le_one simp: abs_mult\<close>)
  have fun_eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i t + b))
      = (\<lambda>\<omega>. sin (a * \<omega> i s + b) * cos (a * ?D \<omega>)
          + cos (a * \<omega> i s + b) * sin (a * ?D \<omega>))"
  proof (rule ext)
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    have "a * \<omega> i t + b = (a * \<omega> i s + b) + a * (\<omega> i t - \<omega> i s)"
      by (simp add: algebra_simps)
    then have "sin (a * \<omega> i t + b)
        = sin ((a * \<omega> i s + b) + a * (\<omega> i t - \<omega> i s))"
      by (simp add: algebra_simps)
    also have "\<dots> = sin (a * \<omega> i s + b) * cos (a * (\<omega> i t - \<omega> i s))
        + cos (a * \<omega> i s + b) * sin (a * (\<omega> i t - \<omega> i s))"
      by (rule sin_add)
    finally show "sin (a * \<omega> i t + b)
        = sin (a * \<omega> i s + b) * cos (a * ?D \<omega>)
          + cos (a * \<omega> i s + b) * sin (a * ?D \<omega>)" .
  qed
  have "AE \<omega> in ?M. cond_exp ?M ?F
      (\<lambda>\<omega>. sin (a * \<omega> i s + b) * cos (a * ?D \<omega>)
        + cos (a * \<omega> i s + b) * sin (a * ?D \<omega>)) \<omega>
      = cond_exp ?M ?F (\<lambda>\<omega>. sin (a * \<omega> i s + b) * cos (a * ?D \<omega>)) \<omega>
        + cond_exp ?M ?F (\<lambda>\<omega>. cos (a * \<omega> i s + b) * sin (a * ?D \<omega>)) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_add[OF sfs int1 int2])
  with T1 T2 show ?thesis
    unfolding fun_eq by eventually_elim simp
qed


text \<open>The centered set-integral form of the trig identities, the input to
  \<open>Modification_Transfer.set_integral_zero_transfer\<close>.\<close>

lemma bm_cos_set_integral:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
    and B: "B \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicat_real B \<omega> *
      (cos (a * \<omega> i t + b)
        - cos (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2))
      \<partial>bm_paths) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?f = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i t + b)"
  let ?g = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      cos (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  have t0: "0 \<le> t" using s st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have B_M: "B \<in> sets ?M"
    using B subalg by (auto simp: subalgebra_def)
  have wtM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t) \<in> borel_measurable ?M"
    using t0 by (intro measurable_bm_coordinate) auto
  have wsM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable ?M"
    using s by (intro measurable_bm_coordinate) auto
  have fM: "?f \<in> borel_measurable ?M"
    using wtM by measurable
  have gM: "?g \<in> borel_measurable ?M"
    using wsM by measurable
  have int_f: "integrable ?M ?f"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use fM in \<open>auto intro!: AE_I2 abs_cos_le_one\<close>)
  have int_g: "integrable ?M ?g"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use gM st in \<open>auto intro!: AE_I2 mult_le_one abs_cos_le_one
        mult_nonneg_nonneg zero_le_power2 simp: abs_mult\<close>)
  have e1: "(\<integral>\<omega> \<in> B. ?f \<omega> \<partial>?M) = (\<integral>\<omega> \<in> B. cond_exp ?M ?F ?f \<omega> \<partial>?M)"
    by (rule sigma_finite_subalgebra.cond_exp_set_integral
        [OF sfs int_f B])
  have ce_M: "cond_exp ?M ?F ?f \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg borel_measurable_cond_exp])
  have e2: "(\<integral>\<omega> \<in> B. cond_exp ?M ?F ?f \<omega> \<partial>?M) = (\<integral>\<omega> \<in> B. ?g \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def
  proof (rule integral_cong_AE)
    show "(\<lambda>\<omega>. indicat_real B \<omega> *\<^sub>R cond_exp ?M ?F ?f \<omega>)
        \<in> borel_measurable ?M"
      by (intro borel_measurable_scaleR
          borel_measurable_indicator B_M ce_M)
    show "(\<lambda>\<omega>. indicat_real B \<omega> *\<^sub>R ?g \<omega>) \<in> borel_measurable ?M"
      by (intro borel_measurable_scaleR
          borel_measurable_indicator B_M gM)
    show "AE \<omega> in ?M. indicat_real B \<omega> *\<^sub>R cond_exp ?M ?F ?f \<omega>
        = indicat_real B \<omega> *\<^sub>R ?g \<omega>"
      using bm_cos_cond_exp[OF s st, of x0 a i b]
      by eventually_elim simp
  qed
  have "(\<integral>\<omega>. indicat_real B \<omega> * (?f \<omega> - ?g \<omega>) \<partial>?M)
      = (\<integral>\<omega>. indicat_real B \<omega> *\<^sub>R ?f \<omega>
          - indicat_real B \<omega> *\<^sub>R ?g \<omega> \<partial>?M)"
    by (intro Bochner_Integration.integral_cong refl)
      (simp add: right_diff_distrib)
  also have "\<dots> = (\<integral>\<omega> \<in> B. ?f \<omega> \<partial>?M) - (\<integral>\<omega> \<in> B. ?g \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_diff
        integrable_mult_indicator[OF B_M] int_f int_g)
  also have "\<dots> = 0"
    using e1 e2 by simp
  finally show ?thesis .
qed


lemma bm_sin_set_integral:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
    and B: "B \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicat_real B \<omega> *
      (sin (a * \<omega> i t + b)
        - sin (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2))
      \<partial>bm_paths) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?f = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i t + b)"
  let ?g = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      sin (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  have t0: "0 \<le> t" using s st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have B_M: "B \<in> sets ?M"
    using B subalg by (auto simp: subalgebra_def)
  have wtM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t) \<in> borel_measurable ?M"
    using t0 by (intro measurable_bm_coordinate) auto
  have wsM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable ?M"
    using s by (intro measurable_bm_coordinate) auto
  have fM: "?f \<in> borel_measurable ?M"
    using wtM by measurable
  have gM: "?g \<in> borel_measurable ?M"
    using wsM by measurable
  have int_f: "integrable ?M ?f"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use fM in \<open>auto intro!: AE_I2 abs_sin_le_one\<close>)
  have int_g: "integrable ?M ?g"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use gM st in \<open>auto intro!: AE_I2 mult_le_one abs_sin_le_one
        mult_nonneg_nonneg zero_le_power2 simp: abs_mult\<close>)
  have e1: "(\<integral>\<omega> \<in> B. ?f \<omega> \<partial>?M) = (\<integral>\<omega> \<in> B. cond_exp ?M ?F ?f \<omega> \<partial>?M)"
    by (rule sigma_finite_subalgebra.cond_exp_set_integral
        [OF sfs int_f B])
  have ce_M: "cond_exp ?M ?F ?f \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg borel_measurable_cond_exp])
  have e2: "(\<integral>\<omega> \<in> B. cond_exp ?M ?F ?f \<omega> \<partial>?M) = (\<integral>\<omega> \<in> B. ?g \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def
  proof (rule integral_cong_AE)
    show "(\<lambda>\<omega>. indicat_real B \<omega> *\<^sub>R cond_exp ?M ?F ?f \<omega>)
        \<in> borel_measurable ?M"
      by (intro borel_measurable_scaleR
          borel_measurable_indicator B_M ce_M)
    show "(\<lambda>\<omega>. indicat_real B \<omega> *\<^sub>R ?g \<omega>) \<in> borel_measurable ?M"
      by (intro borel_measurable_scaleR
          borel_measurable_indicator B_M gM)
    show "AE \<omega> in ?M. indicat_real B \<omega> *\<^sub>R cond_exp ?M ?F ?f \<omega>
        = indicat_real B \<omega> *\<^sub>R ?g \<omega>"
      using bm_sin_cond_exp[OF s st, of x0 a i b]
      by eventually_elim simp
  qed
  have "(\<integral>\<omega>. indicat_real B \<omega> * (?f \<omega> - ?g \<omega>) \<partial>?M)
      = (\<integral>\<omega>. indicat_real B \<omega> *\<^sub>R ?f \<omega>
          - indicat_real B \<omega> *\<^sub>R ?g \<omega> \<partial>?M)"
    by (intro Bochner_Integration.integral_cong refl)
      (simp add: right_diff_distrib)
  also have "\<dots> = (\<integral>\<omega> \<in> B. ?f \<omega> \<partial>?M) - (\<integral>\<omega> \<in> B. ?g \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_diff
        integrable_mult_indicator[OF B_M] int_f int_g)
  also have "\<dots> = 0"
    using e1 e2 by simp
  finally show ?thesis .
qed


text \<open>The transfer to the continuous modification's filtration.\<close>

lemma cbm_cos_set_integral:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (cbmX x0) s)"
  shows "(\<integral>\<omega>. indicat_real A \<omega> *
      (cos (a * Bcont t (\<omega> i) + b)
        - cos (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2))
      \<partial>bm_paths) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * \<omega> i t + b)
      - cos (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  let ?D' = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * Bcont t (\<omega> i) + b)
      - cos (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  have t0: "0 \<le> t" using s st by simp
  have aecoord: "AE \<omega> in ?M. Bcont u (\<omega> i) = \<omega> i u"
    if u: "0 \<le> u" for u
  proof -
    have "AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (rule cbmX_ae_eq) (use u in simp)
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      then have "cbmX x0 u \<omega> $ i = bmX x0 u \<omega> $ i" by simp
      then show ?case by (simp add: cbmX_def bmX_def)
    qed
  qed
  have wM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i u) \<in> borel_measurable ?M"
    if u: "0 \<le> u" for u
    using u by (intro measurable_bm_coordinate) auto
  have cwM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont u (\<omega> i))
      \<in> borel_measurable ?M" for u
    by (rule measurable_cbmX_coord)
  have Dm: "?D \<in> borel_measurable ?M"
    using wM[OF t0] wM[OF s] by measurable
  have D'm: "?D' \<in> borel_measurable ?M"
    using cwM by measurable
  have expnn: "0 \<le> a\<^sup>2 * (t - s)"
    using st by (intro mult_nonneg_nonneg) auto
  have exple: "exp (- a\<^sup>2 * (t - s) / 2) \<le> 1"
    using expnn by (simp add: exp_le_one_iff)
  have Dabs: "\<bar>?D \<omega>\<bar> \<le> 2" for \<omega>
  proof -
    have "\<bar>?D \<omega>\<bar> \<le> \<bar>cos (a * \<omega> i t + b)\<bar>
        + \<bar>cos (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> 1 + 1"
      by (intro add_mono abs_cos_le_one)
        (use exple in \<open>auto simp: abs_mult
          intro!: mult_le_one abs_cos_le_one\<close>)
    finally show ?thesis by simp
  qed
  have D'abs: "\<bar>?D' \<omega>\<bar> \<le> 2" for \<omega>
  proof -
    have "\<bar>?D' \<omega>\<bar> \<le> \<bar>cos (a * Bcont t (\<omega> i) + b)\<bar>
        + \<bar>cos (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> 1 + 1"
      by (intro add_mono abs_cos_le_one)
        (use exple in \<open>auto simp: abs_mult
          intro!: mult_le_one abs_cos_le_one\<close>)
    finally show ?thesis by simp
  qed
  have D_int: "integrable ?M ?D"
    by (rule BMP.integrable_const_bound[where B = 2])
      (use Dm Dabs in \<open>auto intro!: AE_I2\<close>)
  have D'_int: "integrable ?M ?D'"
    by (rule BMP.integrable_const_bound[where B = 2])
      (use D'm D'abs in \<open>auto intro!: AE_I2\<close>)
  have ae_D: "AE \<omega> in ?M. ?D' \<omega> = ?D \<omega>"
    using aecoord[OF t0] aecoord[OF s]
    by eventually_elim simp
  show ?thesis
  proof (rule set_integral_zero_transfer[where X = "bmX x0"
      and X' = "cbmX x0" and t = s])
    show "\<And>u. 0 \<le> u \<Longrightarrow> bmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_bmX) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_cbmX)
    show "\<And>u. u \<in> {0..s} \<Longrightarrow> AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (rule cbmX_ae_eq) auto
    show "integrable ?M ?D" by (rule D_int)
    show "integrable ?M ?D'" by (rule D'_int)
    show "AE \<omega> in ?M. ?D' \<omega> = ?D \<omega>" by (rule ae_D)
    show "\<And>B. B \<in> sets (natural_filtration ?M 0 (bmX x0) s)
        \<Longrightarrow> (\<integral>\<omega>. indicat_real B \<omega> * ?D \<omega> \<partial>?M) = 0"
      by (rule bm_cos_set_integral[OF s st])
    show "A \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
      by (rule A)
  qed
qed


lemma cbm_sin_set_integral:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (cbmX x0) s)"
  shows "(\<integral>\<omega>. indicat_real A \<omega> *
      (sin (a * Bcont t (\<omega> i) + b)
        - sin (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2))
      \<partial>bm_paths) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * \<omega> i t + b)
      - sin (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  let ?D' = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * Bcont t (\<omega> i) + b)
      - sin (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  have t0: "0 \<le> t" using s st by simp
  have aecoord: "AE \<omega> in ?M. Bcont u (\<omega> i) = \<omega> i u"
    if u: "0 \<le> u" for u
  proof -
    have "AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (rule cbmX_ae_eq) (use u in simp)
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      then have "cbmX x0 u \<omega> $ i = bmX x0 u \<omega> $ i" by simp
      then show ?case by (simp add: cbmX_def bmX_def)
    qed
  qed
  have wM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i u) \<in> borel_measurable ?M"
    if u: "0 \<le> u" for u
    using u by (intro measurable_bm_coordinate) auto
  have cwM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont u (\<omega> i))
      \<in> borel_measurable ?M" for u
    by (rule measurable_cbmX_coord)
  have Dm: "?D \<in> borel_measurable ?M"
    using wM[OF t0] wM[OF s] by measurable
  have D'm: "?D' \<in> borel_measurable ?M"
    using cwM by measurable
  have expnn: "0 \<le> a\<^sup>2 * (t - s)"
    using st by (intro mult_nonneg_nonneg) auto
  have exple: "exp (- a\<^sup>2 * (t - s) / 2) \<le> 1"
    using expnn by (simp add: exp_le_one_iff)
  have Dabs: "\<bar>?D \<omega>\<bar> \<le> 2" for \<omega>
  proof -
    have "\<bar>?D \<omega>\<bar> \<le> \<bar>sin (a * \<omega> i t + b)\<bar>
        + \<bar>sin (a * \<omega> i s + b) * exp (- a\<^sup>2 * (t - s) / 2)\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> 1 + 1"
      by (intro add_mono abs_sin_le_one)
        (use exple in \<open>auto simp: abs_mult
          intro!: mult_le_one abs_sin_le_one\<close>)
    finally show ?thesis by simp
  qed
  have D'abs: "\<bar>?D' \<omega>\<bar> \<le> 2" for \<omega>
  proof -
    have "\<bar>?D' \<omega>\<bar> \<le> \<bar>sin (a * Bcont t (\<omega> i) + b)\<bar>
        + \<bar>sin (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)\<bar>"
      by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> 1 + 1"
      by (intro add_mono abs_sin_le_one)
        (use exple in \<open>auto simp: abs_mult
          intro!: mult_le_one abs_sin_le_one\<close>)
    finally show ?thesis by simp
  qed
  have D_int: "integrable ?M ?D"
    by (rule BMP.integrable_const_bound[where B = 2])
      (use Dm Dabs in \<open>auto intro!: AE_I2\<close>)
  have D'_int: "integrable ?M ?D'"
    by (rule BMP.integrable_const_bound[where B = 2])
      (use D'm D'abs in \<open>auto intro!: AE_I2\<close>)
  have ae_D: "AE \<omega> in ?M. ?D' \<omega> = ?D \<omega>"
    using aecoord[OF t0] aecoord[OF s]
    by eventually_elim simp
  show ?thesis
  proof (rule set_integral_zero_transfer[where X = "bmX x0"
      and X' = "cbmX x0" and t = s])
    show "\<And>u. 0 \<le> u \<Longrightarrow> bmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_bmX) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_cbmX)
    show "\<And>u. u \<in> {0..s} \<Longrightarrow> AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (rule cbmX_ae_eq) auto
    show "integrable ?M ?D" by (rule D_int)
    show "integrable ?M ?D'" by (rule D'_int)
    show "AE \<omega> in ?M. ?D' \<omega> = ?D \<omega>" by (rule ae_D)
    show "\<And>B. B \<in> sets (natural_filtration ?M 0 (bmX x0) s)
        \<Longrightarrow> (\<integral>\<omega>. indicat_real B \<omega> * ?D \<omega> \<partial>?M) = 0"
      by (rule bm_sin_set_integral[OF s st])
    show "A \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
      by (rule A)
  qed
qed


text \<open>Repackage the transferred identities as conditional expectations
  against the cbmX filtration.\<close>

lemma cbm_cos_cond_exp:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cond_exp bm_paths (natural_filtration bm_paths 0 (cbmX x0) s)
        (\<lambda>\<omega>. cos (a * Bcont t (\<omega> i) + b)) \<omega>
      = cos (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0) s"
  let ?f = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cos (a * Bcont t (\<omega> i) + b)"
  let ?g = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      cos (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  have t0: "0 \<le> t" using s st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (cbmX x0)"
    by unfold_locales (auto intro: measurable_cbmX)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have expnn: "0 \<le> a\<^sup>2 * (t - s)"
    using st by (intro mult_nonneg_nonneg) auto
  have exple: "exp (- a\<^sup>2 * (t - s) / 2) \<le> 1"
    using expnn by (simp add: exp_le_one_iff)
  have cwM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont u (\<omega> i))
      \<in> borel_measurable ?M" for u
    by (rule measurable_cbmX_coord)
  have fM: "?f \<in> borel_measurable ?M"
    using cwM by measurable
  have gM: "?g \<in> borel_measurable ?M"
    using cwM by measurable
  have int_f: "integrable ?M ?f"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use fM in \<open>auto intro!: AE_I2 abs_cos_le_one\<close>)
  have int_g: "integrable ?M ?g"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use gM exple in \<open>auto intro!: AE_I2 mult_le_one abs_cos_le_one
        simp: abs_mult\<close>)
  have bs: "cbmX x0 s \<in> borel_measurable ?F"
    by (rule Stochastic_Process.adapted_process.adapted[OF
        Stochastic_Process.stochastic_process.adapted_process_natural_filtration
        [OF SPfact] s])
  have nth: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have cwsF: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont s (\<omega> i))
      \<in> borel_measurable ?F"
  proof -
    have eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont s (\<omega> i))
        = (\<lambda>\<omega>. (cbmX x0 s \<omega> - x0) $ i)"
      by (simp add: fun_eq_iff cbmX_def)
    show ?thesis
      unfolding eq
      by (intro measurable_compose[OF _ nth] borel_measurable_diff bs
          borel_measurable_const)
  qed
  have gF: "?g \<in> borel_measurable ?F"
    using cwsF by measurable
  have hce: "has_cond_exp ?M ?F ?f ?g"
  proof (rule has_cond_expI')
    show "integrable ?M ?f" by (rule int_f)
    show "integrable ?M ?g" by (rule int_g)
    show "?g \<in> borel_measurable ?F" by (rule gF)
    fix A assume A: "A \<in> sets ?F"
    have A_M: "A \<in> sets ?M"
      using A subalg by (auto simp: subalgebra_def)
    have "(\<integral>\<omega> \<in> A. ?f \<omega> \<partial>?M) - (\<integral>\<omega> \<in> A. ?g \<omega> \<partial>?M)
        = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?f \<omega>
            - indicat_real A \<omega> *\<^sub>R ?g \<omega> \<partial>?M)"
      unfolding set_lebesgue_integral_def
      by (rule Bochner_Integration.integral_diff
          [OF integrable_mult_indicator[OF A_M int_f]
              integrable_mult_indicator[OF A_M int_g], symmetric])
    also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * (?f \<omega> - ?g \<omega>) \<partial>?M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: right_diff_distrib)
    also have "\<dots> = 0"
      by (rule cbm_cos_set_integral[OF s st A])
    finally show "(\<integral>\<omega> \<in> A. ?f \<omega> \<partial>?M) = (\<integral>\<omega> \<in> A. ?g \<omega> \<partial>?M)"
      by simp
  qed
  show ?thesis
    using sigma_finite_subalgebra.has_cond_exp_charact(2)[OF sfs hce]
    by eventually_elim simp
qed

lemma cbm_sin_cond_exp:
  fixes i :: "'n::finite" and x0 :: "real^'n" and a b :: real
  assumes s: "0 \<le> s" and st: "s < t"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cond_exp bm_paths (natural_filtration bm_paths 0 (cbmX x0) s)
        (\<lambda>\<omega>. sin (a * Bcont t (\<omega> i) + b)) \<omega>
      = sin (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0) s"
  let ?f = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. sin (a * Bcont t (\<omega> i) + b)"
  let ?g = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      sin (a * Bcont s (\<omega> i) + b) * exp (- a\<^sup>2 * (t - s) / 2)"
  have t0: "0 \<le> t" using s st by simp
  have SPfact: "Stochastic_Process.stochastic_process
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (cbmX x0)"
    by unfold_locales (auto intro: measurable_cbmX)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have fmeas: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M ?F"
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fmeas
        Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have expnn: "0 \<le> a\<^sup>2 * (t - s)"
    using st by (intro mult_nonneg_nonneg) auto
  have exple: "exp (- a\<^sup>2 * (t - s) / 2) \<le> 1"
    using expnn by (simp add: exp_le_one_iff)
  have cwM: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont u (\<omega> i))
      \<in> borel_measurable ?M" for u
    by (rule measurable_cbmX_coord)
  have fM: "?f \<in> borel_measurable ?M"
    using cwM by measurable
  have gM: "?g \<in> borel_measurable ?M"
    using cwM by measurable
  have int_f: "integrable ?M ?f"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use fM in \<open>auto intro!: AE_I2 abs_sin_le_one\<close>)
  have int_g: "integrable ?M ?g"
    by (rule BMP.integrable_const_bound[where B = 1])
      (use gM exple in \<open>auto intro!: AE_I2 mult_le_one abs_sin_le_one
        simp: abs_mult\<close>)
  have bs: "cbmX x0 s \<in> borel_measurable ?F"
    by (rule Stochastic_Process.adapted_process.adapted[OF
        Stochastic_Process.stochastic_process.adapted_process_natural_filtration
        [OF SPfact] s])
  have nth: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have cwsF: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont s (\<omega> i))
      \<in> borel_measurable ?F"
  proof -
    have eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. Bcont s (\<omega> i))
        = (\<lambda>\<omega>. (cbmX x0 s \<omega> - x0) $ i)"
      by (simp add: fun_eq_iff cbmX_def)
    show ?thesis
      unfolding eq
      by (intro measurable_compose[OF _ nth] borel_measurable_diff bs
          borel_measurable_const)
  qed
  have gF: "?g \<in> borel_measurable ?F"
    using cwsF by measurable
  have hce: "has_cond_exp ?M ?F ?f ?g"
  proof (rule has_cond_expI')
    show "integrable ?M ?f" by (rule int_f)
    show "integrable ?M ?g" by (rule int_g)
    show "?g \<in> borel_measurable ?F" by (rule gF)
    fix A assume A: "A \<in> sets ?F"
    have A_M: "A \<in> sets ?M"
      using A subalg by (auto simp: subalgebra_def)
    have "(\<integral>\<omega> \<in> A. ?f \<omega> \<partial>?M) - (\<integral>\<omega> \<in> A. ?g \<omega> \<partial>?M)
        = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?f \<omega>
            - indicat_real A \<omega> *\<^sub>R ?g \<omega> \<partial>?M)"
      unfolding set_lebesgue_integral_def
      by (rule Bochner_Integration.integral_diff
          [OF integrable_mult_indicator[OF A_M int_f]
              integrable_mult_indicator[OF A_M int_g], symmetric])
    also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> * (?f \<omega> - ?g \<omega>) \<partial>?M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: right_diff_distrib)
    also have "\<dots> = 0"
      by (rule cbm_sin_set_integral[OF s st A])
    finally show "(\<integral>\<omega> \<in> A. ?f \<omega> \<partial>?M) = (\<integral>\<omega> \<in> A. ?g \<omega> \<partial>?M)"
      by simp
  qed
  show ?thesis
    using sigma_finite_subalgebra.has_cond_exp_charact(2)[OF sfs hce]
    by eventually_elim simp
qed


text \<open>The deterministic layer: time change and radius.\<close>

definition drc :: "real \<Rightarrow> real \<Rightarrow> real" where "drc q t = ln (1 + t / q)"
definition drR :: "real \<Rightarrow> real \<Rightarrow> real" where "drR q t = sqrt (q + t)"

lemma drc_zero [simp]: "drc q 0 = 0"
  by (simp add: drc_def)

lemma drR_pos: "0 < q \<Longrightarrow> 0 \<le> t \<Longrightarrow> 0 < drR q t"
  by (simp add: drR_def add_pos_nonneg)

lemma drc_nonneg: "0 < q \<Longrightarrow> 0 \<le> t \<Longrightarrow> 0 \<le> drc q t"
  by (simp add: drc_def divide_nonneg_pos)

lemma drc_mono:
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
  shows "drc q s \<le> drc q t"
proof -
  have ps: "0 < 1 + s / q" and pt: "0 < 1 + t / q"
    using q s st by (auto simp: add_pos_nonneg divide_nonneg_pos)
  have "1 + s / q \<le> 1 + t / q"
    using st q by (simp add: divide_right_mono)
  then show ?thesis
    unfolding drc_def using ps pt by (simp add: ln_le_cancel_iff)
qed

lemma drc_strict_mono:
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s < t"
  shows "drc q s < drc q t"
proof -
  have ps: "0 < 1 + s / q" and pt: "0 < 1 + t / q"
    using q s st by (auto simp: add_pos_nonneg divide_nonneg_pos)
  have "1 + s / q < 1 + t / q"
    using st q by (simp add: divide_strict_right_mono)
  then show ?thesis
    unfolding drc_def using ps pt by (simp add: ln_less_cancel_iff)
qed

lemma exp_neg_ln_half:
  assumes x: "0 < x"
  shows "exp (- ln x / 2) = 1 / sqrt x"
proof -
  have "exp (- ln x / 2) = exp (ln x * (- (1 / 2)))"
    by (simp add: field_simps)
  also have "\<dots> = x powr (- (1 / 2))"
    using x by (simp add: powr_def mult.commute)
  also have "\<dots> = 1 / x powr (1 / 2)"
    by (simp add: powr_minus_divide)
  also have "\<dots> = 1 / sqrt x"
    using x by (simp add: powr_half_sqrt)
  finally show ?thesis .
qed

lemma drR_decay:
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
  shows "drR q t * exp (- (drc q t - drc q s) / 2) = drR q s"
proof -
  have qs: "0 < q + s" and qt: "0 < q + t" using q s st by auto
  have a1: "0 < 1 + t / q" and a2: "0 < 1 + s / q"
    using q s st by (auto simp: add_pos_nonneg divide_nonneg_pos)
  have "drc q t - drc q s = ln ((1 + t / q) / (1 + s / q))"
    unfolding drc_def using a1 a2 by (simp add: ln_div)
  also have "(1 + t / q) / (1 + s / q) = (q + t) / (q + s)"
    using a2 qs q by (subst frac_eq_eq) (auto simp: field_simps)
  finally have dd: "drc q t - drc q s = ln ((q + t) / (q + s))" .
  have pos: "0 < (q + t) / (q + s)" using qt qs by simp
  have "exp (- (drc q t - drc q s) / 2) = 1 / sqrt ((q + t) / (q + s))"
    unfolding dd by (rule exp_neg_ln_half[OF pos])
  also have "sqrt ((q + t) / (q + s)) = sqrt (q + t) / sqrt (q + s)"
    by (rule real_sqrt_divide)
  also have "1 / (sqrt (q + t) / sqrt (q + s))
      = sqrt (q + s) / sqrt (q + t)"
    using qt by (simp add: field_simps)
  finally have e: "exp (- (drc q t - drc q s) / 2)
      = sqrt (q + s) / sqrt (q + t)" .
  show ?thesis
    unfolding drR_def e using qt by (simp add: field_simps)
qed

lemma drc_cont:
  assumes q: "0 < q"
  shows "continuous_on {0..} (drc q)"
proof -
  have ne: "1 + t / q \<noteq> 0" if "0 \<le> t" for t
  proof -
    have "0 \<le> t / q" by (rule divide_nonneg_pos[OF that q])
    then show ?thesis by linarith
  qed
  show ?thesis
    unfolding drc_def
    by (intro continuous_intros) (use ne q in auto)
qed

text \<open>The process.\<close>

definition drW :: "real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real" where
  "drW u \<omega> = Bcont u (\<omega> 1)"

definition drX :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^2"
  where
  "drX q \<phi> t \<omega> = drR q t *\<^sub>R
     (\<chi> j. if j = 1 then cos (drW (drc q t) \<omega> + \<phi>)
           else sin (drW (drc q t) \<omega> + \<phi>))"

lemma drX_norm:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "norm (drX q \<phi> t \<omega>) = drR q t"
proof -
  define c where "c = cos (drW (drc q t) \<omega> + \<phi>)"
  define sn where "sn = sin (drW (drc q t) \<omega> + \<phi>)"
  have cs: "c * c + sn * sn = 1"
    unfolding c_def sn_def by (rule sin_cos_squared_add3)
  have "drX q \<phi> t \<omega> \<bullet> drX q \<phi> t \<omega>
      = (drR q t * c) * (drR q t * c) + (drR q t * sn) * (drR q t * sn)"
    by (simp add: drX_def inner_vec_def UNIV_2 c_def sn_def)
  also have "\<dots> = drR q t * drR q t * (c * c + sn * sn)"
    by (simp add: algebra_simps)
  also have "\<dots> = drR q t * drR q t"
    unfolding cs by simp
  finally have "norm (drX q \<phi> t \<omega>) = sqrt (drR q t * drR q t)"
    by (simp add: norm_eq_sqrt_inner)
  then show ?thesis
    using drR_pos[OF q t]
    by (simp add: power2_eq_square[symmetric])
qed


text \<open>The martingale property of the trig components, from the conditional
  trigonometric expectations and the decay law.\<close>

lemma martingale_drX_cos:
  fixes q \<phi> :: real
  assumes q: "0 < q"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (\<lambda>t \<omega>. drR q t * cos (drW (drc q t) \<omega> + \<phi>))"
proof -
  let ?M = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
  let ?FB = "natural_filtration ?M 0 (cbmX (0 :: real^2))"
  let ?G = "\<lambda>t. ?FB (drc q t)"
  let ?Y = "\<lambda>t \<omega>. drR q t * cos (drW (drc q t) \<omega> + \<phi>)"
  have SPfact: "Stochastic_Process.stochastic_process ?M 0
      (cbmX (0 :: real^2))"
    by unfold_locales
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have subB: "subalgebra ?M (?FB u)" for u
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have sfsB: "sigma_finite_subalgebra ?M (?FB u)" for u
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fm subB)
  have FMbase: "filtered_measure ?M ?FB 0"
    by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration
        [OF SPfact])
  have Gmono: "sets (?G s) \<subseteq> sets (?G t)"
    if st: "0 \<le> s" "s \<le> t" for s t
    using filtered_measure.subalgebra_F[OF FMbase
        drc_nonneg[OF q st(1)] drc_mono[OF q st(1) st(2)]]
    by (auto simp: subalgebra_def)
  have FMG: "filtered_measure ?M ?G 0"
    unfolding filtered_measure_def using subB Gmono by auto
  have sffG: "sigma_finite_filtered_measure ?M ?G 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro FMG sfsB)
  have drW_cbmX: "drW u \<omega> = cbmX (0 :: real^2) u \<omega> $ 1" for u \<omega>
    by (simp add: drW_def cbmX_def)
  have nth1: "(\<lambda>v :: real^2. v $ 1) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^2. v $ 1) = (\<lambda>v. inner v (axis 1 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have YM: "?Y t \<in> borel_measurable ?M" for t
    using measurable_cbmX_coord[of "drc q t" "1 :: 2"]
    by (simp add: drW_def) measurable
  have drWF: "(\<lambda>\<omega>. drW u \<omega>) \<in> borel_measurable (?FB u)"
    if u: "0 \<le> u" for u
  proof -
    have bu: "cbmX (0 :: real^2) u \<in> borel_measurable (?FB u)"
      by (rule Stochastic_Process.adapted_process.adapted[OF
          Stochastic_Process.stochastic_process.adapted_process_natural_filtration
          [OF SPfact] u])
    show ?thesis
      unfolding drW_cbmX
      by (rule measurable_compose[OF bu nth1])
  qed
  have YF: "?Y t \<in> borel_measurable (?G t)" if t: "0 \<le> t" for t
    using drWF[OF drc_nonneg[OF q t]] by measurable
  have Yabs: "\<bar>?Y t \<omega>\<bar> \<le> \<bar>drR q t\<bar>" for t \<omega>
  proof -
    have "\<bar>?Y t \<omega>\<bar> = \<bar>drR q t\<bar> * \<bar>cos (drW (drc q t) \<omega> + \<phi>)\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>drR q t\<bar> * 1"
      by (intro mult_left_mono abs_cos_le_one abs_ge_zero)
    finally show ?thesis by simp
  qed
  have Yint: "integrable ?M (?Y t)" for t
    by (rule BMP.integrable_const_bound[where B = "\<bar>drR q t\<bar>"])
      (use YM Yabs in \<open>auto intro!: AE_I2\<close>)
  have intcos: "integrable ?M (\<lambda>\<omega>. cos (Bcont (drc q u) (\<omega> 1) + \<phi>))"
    for u
  proof -
    have m: "(\<lambda>\<omega> :: 2 \<Rightarrow> real \<Rightarrow> real. cos (Bcont (drc q u) (\<omega> 1) + \<phi>))
        \<in> borel_measurable ?M"
      using measurable_cbmX_coord[of "drc q u" "1 :: 2"] by measurable
    show ?thesis
      by (rule BMP.integrable_const_bound[where B = 1])
        (use m in \<open>auto intro!: AE_I2 abs_cos_le_one\<close>)
  qed
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?G 0"
      by (rule sffG)
    show "adapted_process ?M ?G 0 ?Y"
      by unfold_locales
        (auto intro: subB YF dest: Gmono[THEN subsetD])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (?Y i)"
      by (rule Yint)
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    show "AE \<omega> in ?M. ?Y i \<omega> = cond_exp ?M (?G i) (?Y j) \<omega>"
    proof (cases "i = j")
      case True
      show ?thesis
        unfolding True
        by (rule sigma_finite_subalgebra.cond_exp_F_meas
            [OF sfsB Yint YF[OF order_trans[OF ij(1) ij(2)]],
              THEN AE_symmetric])
    next
      case False
      with ij have iltj: "i < j" by simp
      have ci0: "0 \<le> drc q i" by (rule drc_nonneg[OF q ij(1)])
      have cicj: "drc q i < drc q j"
        by (rule drc_strict_mono[OF q ij(1) iltj])
      have CE: "AE \<omega> in ?M. cond_exp ?M (?G i)
          (\<lambda>\<omega>. cos (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>
          = cos (Bcont (drc q i) (\<omega> 1) + \<phi>)
            * exp (- (drc q j - drc q i) / 2)"
      proof -
        have "AE \<omega> in ?M. cond_exp ?M (?G i)
            (\<lambda>\<omega>. cos (1 * Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>
            = cos (1 * Bcont (drc q i) (\<omega> 1) + \<phi>)
              * exp (- (1 :: real)\<^sup>2 * (drc q j - drc q i) / 2)"
          by (rule cbm_cos_cond_exp[OF ci0 cicj])
        then show ?thesis by simp
      qed
      have SC: "AE \<omega> in ?M. cond_exp ?M (?G i) (?Y j) \<omega>
          = drR q j *\<^sub>R cond_exp ?M (?G i)
              (\<lambda>\<omega>. cos (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>"
      proof -
        have "AE \<omega> in ?M. cond_exp ?M (?G i)
            (\<lambda>\<omega>. drR q j *\<^sub>R cos (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>
            = drR q j *\<^sub>R cond_exp ?M (?G i)
                (\<lambda>\<omega>. cos (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>"
          by (rule sigma_finite_subalgebra.cond_exp_scaleR_right
              [OF sfsB intcos])
        then show ?thesis by (simp add: drW_def)
      qed
      show ?thesis
        using SC CE
      proof eventually_elim
        case (elim \<omega>)
        have Ydecay: "drR q j * exp (- (drc q j - drc q i) / 2)
            = drR q i"
          by (rule drR_decay[OF q ij(1) ij(2)])
        have "?Y i \<omega> = drR q j
            * (cos (Bcont (drc q i) (\<omega> 1) + \<phi>)
                * exp (- (drc q j - drc q i) / 2))"
          unfolding drW_def using Ydecay by auto
        with elim show ?case by simp
      qed
    qed
  qed
qed


lemma martingale_drX_sin:
  fixes q \<phi> :: real
  assumes q: "0 < q"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (\<lambda>t \<omega>. drR q t * sin (drW (drc q t) \<omega> + \<phi>))"
proof -
  let ?M = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
  let ?FB = "natural_filtration ?M 0 (cbmX (0 :: real^2))"
  let ?G = "\<lambda>t. ?FB (drc q t)"
  let ?Y = "\<lambda>t \<omega>. drR q t * sin (drW (drc q t) \<omega> + \<phi>)"
  have SPfact: "Stochastic_Process.stochastic_process ?M 0
      (cbmX (0 :: real^2))"
    by unfold_locales
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have subB: "subalgebra ?M (?FB u)" for u
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
        [OF SPfact])
  have sfsB: "sigma_finite_subalgebra ?M (?FB u)" for u
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fm subB)
  have FMbase: "filtered_measure ?M ?FB 0"
    by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration
        [OF SPfact])
  have Gmono: "sets (?G s) \<subseteq> sets (?G t)"
    if st: "0 \<le> s" "s \<le> t" for s t
    using filtered_measure.subalgebra_F[OF FMbase
        drc_nonneg[OF q st(1)] drc_mono[OF q st(1) st(2)]]
    by (auto simp: subalgebra_def)
  have FMG: "filtered_measure ?M ?G 0"
    unfolding filtered_measure_def using subB Gmono by auto
  have sffG: "sigma_finite_filtered_measure ?M ?G 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro FMG sfsB)
  have drW_cbmX: "drW u \<omega> = cbmX (0 :: real^2) u \<omega> $ 1" for u \<omega>
    by (simp add: drW_def cbmX_def)
  have nth1: "(\<lambda>v :: real^2. v $ 1) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^2. v $ 1) = (\<lambda>v. inner v (axis 1 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have YM: "?Y t \<in> borel_measurable ?M" for t
    using measurable_cbmX_coord[of "drc q t" "1 :: 2"]
    by (simp add: drW_def) measurable
  have drWF: "(\<lambda>\<omega>. drW u \<omega>) \<in> borel_measurable (?FB u)"
    if u: "0 \<le> u" for u
  proof -
    have bu: "cbmX (0 :: real^2) u \<in> borel_measurable (?FB u)"
      by (rule Stochastic_Process.adapted_process.adapted[OF
          Stochastic_Process.stochastic_process.adapted_process_natural_filtration
          [OF SPfact] u])
    show ?thesis
      unfolding drW_cbmX
      by (rule measurable_compose[OF bu nth1])
  qed
  have YF: "?Y t \<in> borel_measurable (?G t)" if t: "0 \<le> t" for t
    using drWF[OF drc_nonneg[OF q t]] by measurable
  have Yabs: "\<bar>?Y t \<omega>\<bar> \<le> \<bar>drR q t\<bar>" for t \<omega>
  proof -
    have "\<bar>?Y t \<omega>\<bar> = \<bar>drR q t\<bar> * \<bar>sin (drW (drc q t) \<omega> + \<phi>)\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>drR q t\<bar> * 1"
      by (intro mult_left_mono abs_sin_le_one abs_ge_zero)
    finally show ?thesis by simp
  qed
  have Yint: "integrable ?M (?Y t)" for t
    by (rule BMP.integrable_const_bound[where B = "\<bar>drR q t\<bar>"])
      (use YM Yabs in \<open>auto intro!: AE_I2\<close>)
  have intsin: "integrable ?M (\<lambda>\<omega>. sin (Bcont (drc q u) (\<omega> 1) + \<phi>))"
    for u
  proof -
    have m: "(\<lambda>\<omega> :: 2 \<Rightarrow> real \<Rightarrow> real. sin (Bcont (drc q u) (\<omega> 1) + \<phi>))
        \<in> borel_measurable ?M"
      using measurable_cbmX_coord[of "drc q u" "1 :: 2"] by measurable
    show ?thesis
      by (rule BMP.integrable_const_bound[where B = 1])
        (use m in \<open>auto intro!: AE_I2 abs_sin_le_one\<close>)
  qed
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?G 0"
      by (rule sffG)
    show "adapted_process ?M ?G 0 ?Y"
      by unfold_locales
        (auto intro: subB YF dest: Gmono[THEN subsetD])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (?Y i)"
      by (rule Yint)
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    show "AE \<omega> in ?M. ?Y i \<omega> = cond_exp ?M (?G i) (?Y j) \<omega>"
    proof (cases "i = j")
      case True
      show ?thesis
        unfolding True
        by (rule sigma_finite_subalgebra.cond_exp_F_meas
            [OF sfsB Yint YF[OF order_trans[OF ij(1) ij(2)]],
              THEN AE_symmetric])
    next
      case False
      with ij have iltj: "i < j" by simp
      have ci0: "0 \<le> drc q i" by (rule drc_nonneg[OF q ij(1)])
      have cicj: "drc q i < drc q j"
        by (rule drc_strict_mono[OF q ij(1) iltj])
      have CE: "AE \<omega> in ?M. cond_exp ?M (?G i)
          (\<lambda>\<omega>. sin (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>
          = sin (Bcont (drc q i) (\<omega> 1) + \<phi>)
            * exp (- (drc q j - drc q i) / 2)"
      proof -
        have "AE \<omega> in ?M. cond_exp ?M (?G i)
            (\<lambda>\<omega>. sin (1 * Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>
            = sin (1 * Bcont (drc q i) (\<omega> 1) + \<phi>)
              * exp (- (1 :: real)\<^sup>2 * (drc q j - drc q i) / 2)"
          by (rule cbm_sin_cond_exp[OF ci0 cicj])
        then show ?thesis by simp
      qed
      have SC: "AE \<omega> in ?M. cond_exp ?M (?G i) (?Y j) \<omega>
          = drR q j *\<^sub>R cond_exp ?M (?G i)
              (\<lambda>\<omega>. sin (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>"
      proof -
        have "AE \<omega> in ?M. cond_exp ?M (?G i)
            (\<lambda>\<omega>. drR q j *\<^sub>R sin (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>
            = drR q j *\<^sub>R cond_exp ?M (?G i)
                (\<lambda>\<omega>. sin (Bcont (drc q j) (\<omega> 1) + \<phi>)) \<omega>"
          by (rule sigma_finite_subalgebra.cond_exp_scaleR_right
              [OF sfsB intsin])
        then show ?thesis by (simp add: drW_def)
      qed
      show ?thesis
        using SC CE
      proof eventually_elim
        case (elim \<omega>)
        have Ydecay: "drR q j * exp (- (drc q j - drc q i) / 2)
            = drR q i"
          by (rule drR_decay[OF q ij(1) ij(2)])
        have "?Y i \<omega> = drR q j
            * (sin (Bcont (drc q i) (\<omega> 1) + \<phi>)
                * exp (- (drc q j - drc q i) / 2))"
          unfolding drW_def using Ydecay by auto
        with elim show ?case by simp
      qed
    qed
  qed
qed

theorem martingale_drX:
  fixes q \<phi> :: real
  assumes q: "0 < q"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (drX q \<phi>)"
proof (rule martingale_vecI)
  fix k :: 2
  show "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (\<lambda>t \<omega>. drX q \<phi> t \<omega> $ k)"
  proof (cases "k = 1")
    case True
    have "(\<lambda>t \<omega>. drX q \<phi> t \<omega> $ k)
        = (\<lambda>t \<omega>. drR q t * cos (drW (drc q t) \<omega> + \<phi>))"
      by (simp add: drX_def fun_eq_iff True)
    then show ?thesis
      using martingale_drX_cos[OF q, of \<phi>] by simp
  next
    case False
    then have k2: "k = 2" using exhaust_2 by auto
    have "(\<lambda>t \<omega>. drX q \<phi> t \<omega> $ k)
        = (\<lambda>t \<omega>. drR q t * sin (drW (drc q t) \<omega> + \<phi>))"
      by (simp add: drX_def fun_eq_iff k2)
    then show ?thesis
      using martingale_drX_sin[OF q, of \<phi>] by simp
  qed
qed

text \<open>Stopping a martingale at a DETERMINISTIC time needs no optional
  stopping: below the horizon it is the base property, above it the
  stopped value is measurable at the earlier time.\<close>

lemma martingale_stopped_deterministic:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
    and T0 :: real
  assumes mg: "martingale M F 0 Y" and T0: "0 \<le> T0"
  shows "martingale M F 0 (\<lambda>t. Y (min t T0))"
proof -
  interpret MY: martingale M F 0 Y by (rule mg)
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure M F 0"
      by (rule MY.sigma_finite_filtered_measure_axioms)
    show "adapted_process M F 0 (\<lambda>t \<omega>. Y (min t T0) \<omega>)"
    proof (unfold_locales)
      fix i :: real assume i: "0 \<le> i"
      have m0: "0 \<le> min i T0" using i T0 by simp
      have "Y (min i T0) \<in> borel_measurable (F (min i T0))"
        by (rule MY.adapted[OF m0])
      then show "(\<lambda>\<omega>. Y (min i T0) \<omega>) \<in> borel_measurable (F i)"
        using MY.subalgebra_F[OF m0, of i] i
        by (auto intro: measurable_from_subalg)
    qed
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. Y (min i T0) \<omega>)"
      using T0 by (intro MY.integrable) simp
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    show "AE \<omega> in M. Y (min i T0) \<omega>
        = cond_exp M (F i) (\<lambda>\<omega>. Y (min j T0) \<omega>) \<omega>"
    proof (cases "T0 \<le> i")
      case True
      then have mi: "min i T0 = T0" and mj: "min j T0 = T0"
        using ij by auto
      have YT0F: "Y T0 \<in> borel_measurable (F i)"
        using MY.adapted[OF T0] MY.subalgebra_F[OF T0 True] ij(1)
        by (auto intro: measurable_from_subalg)
      show ?thesis
        unfolding mi mj
        by (rule sigma_finite_subalgebra.cond_exp_F_meas
            [OF MY.sigma_finite_subalgebra_F[OF ij(1)]
              MY.integrable[OF T0] YT0F, THEN AE_symmetric])
    next
      case False
      then have mi: "min i T0 = i" by simp
      have imj: "i \<le> min j T0" using False ij by simp
      have mj0: "0 \<le> min j T0" using ij(1) imj by simp
      have "AE \<omega> in M. Y i \<omega>
          = cond_exp M (F i) (Y (min j T0)) \<omega>"
        by (rule MY.martingale_property[OF ij(1) imj])
      then show ?thesis
        unfolding mi by simp
    qed
  qed
qed

theorem martingale_drXs:
  fixes q \<phi> T0 :: real
  assumes q: "0 < q" and T0: "0 \<le> T0"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (\<lambda>t. drX q \<phi> (min t T0))"
  by (rule martingale_stopped_deterministic[OF martingale_drX[OF q] T0])

subsection \<open>Joint measurability of time-continuous processes\<close>

text \<open>A function that is continuous in time and measurable in the sample
  point is jointly measurable (dyadic discretization of time).  Needed to
  interchange the compensator's time integral with expectations.\<close>

lemma borel_measurable_continuous_time_process:
  fixes f :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on UNIV (\<lambda>u. f u \<omega>)"
    and meas: "\<And>u. f u \<in> borel_measurable M"
  shows "(\<lambda>p. f (fst p) (snd p)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)"
proof -
  define g :: "nat \<Rightarrow> real \<Rightarrow> real"
    where "g n u = real_of_int \<lfloor>u * 2 ^ n\<rfloor> / 2 ^ n" for n u
  have mul_meas: "(\<lambda>u :: real. u * 2 ^ n) \<in> borel_measurable borel" for n
    by measurable
  have g_meas: "g n \<in> borel_measurable borel" for n
    unfolding g_def
    by (intro borel_measurable_divide borel_measurable_const
        measurable_compose[OF mul_meas borel_measurable_real_floor])
  have g_range: "range (g n) \<subseteq> (\<lambda>k. real_of_int k / 2 ^ n) ` UNIV" for n
    unfolding g_def by auto
  have g_cnt: "countable (range (g n))" for n
    by (rule countable_subset[OF g_range]) auto
  have pow_pos: "0 < (2 :: real) ^ n" for n by simp
  have g_le: "g n u \<le> u" for n u
  proof -
    have "real_of_int \<lfloor>u * 2 ^ n\<rfloor> / 2 ^ n \<le> (u * 2 ^ n) / 2 ^ n"
      by (intro divide_right_mono of_int_floor_le) simp
    then show ?thesis unfolding g_def by simp
  qed
  have g_ge: "u - 1 / 2 ^ n \<le> g n u" for n u
  proof -
    have "(u * 2 ^ n - 1) / 2 ^ n \<le> real_of_int \<lfloor>u * 2 ^ n\<rfloor> / 2 ^ n"
      by (intro divide_right_mono) simp_all
    then show ?thesis
      unfolding g_def by (simp add: diff_divide_distrib)
  qed
  have g_lim: "(\<lambda>n. g n u) \<longlonglongrightarrow> u" for u
  proof (rule tendsto_sandwich)
    show "\<forall>\<^sub>F n in sequentially. u - (1 / 2) ^ n \<le> g n u"
      using g_ge by (intro always_eventually allI) (simp add: power_one_over)
    show "\<forall>\<^sub>F n in sequentially. g n u \<le> u"
      using g_le by (intro always_eventually allI)
    have "(\<lambda>n. (1 / 2 :: real) ^ n) \<longlonglongrightarrow> 0"
      by (rule LIMSEQ_realpow_zero) auto
    then have "(\<lambda>n. u - (1 / 2 :: real) ^ n) \<longlonglongrightarrow> u - 0"
      by (intro tendsto_diff tendsto_const)
    then show "(\<lambda>n. u - (1 / 2 :: real) ^ n) \<longlonglongrightarrow> u" by simp
  qed simp
  have g_meas_l: "g n \<in> borel_measurable lborel" for n
    using g_meas measurable_cong_sets[OF sets_lborel refl] by blast
  have m: "(\<lambda>p :: real \<times> 'a. g n (fst p))
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)" for n
    by (intro measurable_compose[OF measurable_fst g_meas_l])
  have step: "(\<lambda>p. f (g n (fst p)) (snd p))
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)" for n
  proof (rule measurable_compose_countable'
      [where g = "\<lambda>p. g n (fst p)" and I = "range (g n)"])
    show "\<And>i. i \<in> range (g n) \<Longrightarrow>
        (\<lambda>p :: real \<times> 'a. f i (snd p)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)"
      by (intro measurable_compose[OF measurable_snd meas])
    show "countable (range (g n))" by (rule g_cnt)
    have pre: "(\<lambda>p :: real \<times> 'a. g n (fst p)) -` {a} \<inter> space (lborel \<Otimes>\<^sub>M M)
        \<in> sets (lborel \<Otimes>\<^sub>M M)" for a
      by (rule measurable_sets[OF m]) simp
    show "(\<lambda>p :: real \<times> 'a. g n (fst p))
        \<in> measurable (lborel \<Otimes>\<^sub>M M) (count_space (range (g n)))"
      by (rule measurable_count_space_eq_countable[THEN iffD2, OF g_cnt])
        (use pre in auto)
  qed
  show ?thesis
  proof (rule borel_measurable_LIMSEQ_real[OF _ step])
    fix p :: "real \<times> 'a" assume p: "p \<in> space (lborel \<Otimes>\<^sub>M M)"
    then have "snd p \<in> space M"
      by (auto simp: space_pair_measure mem_Times_iff)
    then have "isCont (\<lambda>u. f u (snd p)) (fst p)"
      using cont continuous_on_interior[of UNIV "\<lambda>u. f u (snd p)"]
      by (simp add: interior_UNIV)
    then show "(\<lambda>n. f (g n (fst p)) (snd p)) \<longlonglongrightarrow> f (fst p) (snd p)"
      using g_lim[of "fst p"]
      by (rule isCont_tendsto_compose)
  qed
qed

lemma borel_measurable_time_integral:
  fixes f :: "real \<Rightarrow> 'a \<Rightarrow> real" and a b :: real
  assumes cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on UNIV (\<lambda>u. f u \<omega>)"
    and meas: "\<And>u. f u \<in> borel_measurable M"
  shows "(\<lambda>\<omega>. \<integral>u\<in>{a..b}. f u \<omega> \<partial>lborel) \<in> borel_measurable M"
proof -
  have jm: "(\<lambda>p. f (fst p) (snd p)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)"
    by (rule borel_measurable_continuous_time_process[OF cont meas])
  have jm2: "(\<lambda>p. indicat_real {a..b} (fst p) * f (fst p) (snd p))
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)"
    using jm by measurable
  have jm3: "(\<lambda>p. indicat_real {a..b} (snd p) * f (snd p) (fst p))
      \<in> borel_measurable (M \<Otimes>\<^sub>M lborel)"
    using measurable_pair_swap[OF jm2] by (simp add: case_prod_beta)
  have "(\<lambda>\<omega>. \<integral>u. indicat_real {a..b} u * f u \<omega> \<partial>lborel) \<in> borel_measurable M"
    by (rule sigma_finite_measure.borel_measurable_lebesgue_integral
        [OF lborel.sigma_finite_measure_axioms])
      (use jm3 in \<open>simp add: case_prod_beta\<close>)
  then show ?thesis
    unfolding set_lebesgue_integral_def by simp
qed

lemma time_integral_swap_event:
  fixes f :: "real \<Rightarrow> 'a \<Rightarrow> real" and a b C :: real
  assumes fin: "finite_measure M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on UNIV (\<lambda>u. f u \<omega>)"
    and meas: "\<And>u. f u \<in> borel_measurable M"
    and bnd: "\<And>u \<omega>. \<omega> \<in> space M \<Longrightarrow> \<bar>f u \<omega>\<bar> \<le> C"
    and B: "B \<in> sets M"
  shows "(\<integral>\<omega>. indicat_real B \<omega> * (\<integral>u\<in>{a..b}. f u \<omega> \<partial>lborel) \<partial>M)
       = (\<integral>u\<in>{a..b}. (\<integral>\<omega>. indicat_real B \<omega> * f u \<omega> \<partial>M) \<partial>lborel)"
proof -
  interpret finite_measure M by fact
  interpret P: pair_sigma_finite lborel M
    by (intro pair_sigma_finite.intro lborel.sigma_finite_measure_axioms
        sigma_finite_measure_axioms)
  define F where "F u \<omega> = indicat_real {a..b} u * (indicat_real B \<omega> * f u \<omega>)"
    for u \<omega>
  have jm: "(\<lambda>p. f (fst p) (snd p)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)"
    by (rule borel_measurable_continuous_time_process[OF cont meas])
  have Fm: "(\<lambda>p. F (fst p) (snd p)) \<in> borel_measurable (lborel \<Otimes>\<^sub>M M)"
    unfolding F_def using jm B by measurable
  have rect: "{a..b} \<times> B \<in> sets (lborel \<Otimes>\<^sub>M M)"
    using B by (intro pair_measureI) auto
  have rect_fin: "emeasure (lborel \<Otimes>\<^sub>M M) ({a..b} \<times> B) < \<infinity>"
  proof -
    have "emeasure (lborel \<Otimes>\<^sub>M M) ({a..b} \<times> B)
        = emeasure lborel {a..b} * emeasure M B"
      using B by (intro emeasure_pair_measure_Times) auto
    also have "\<dots> < \<infinity>"
    proof -
      have "emeasure M B < \<infinity>"
        by (simp add: emeasure_eq_measure)
      moreover have "emeasure lborel {a..b} < \<infinity>"
        by (cases "a \<le> b") (auto simp: emeasure_lborel_Icc)
      ultimately show ?thesis
        by (auto simp: ennreal_mult_less_top)
    qed
    finally show ?thesis .
  qed
  have int_ind: "integrable (lborel \<Otimes>\<^sub>M M)
      (\<lambda>p. indicat_real ({a..b} \<times> B) p)"
    using rect rect_fin
    by (intro integrable_indicator_iff[THEN iffD2])
      (auto simp: Int_absorb2 sets.sets_into_space)
  have int_bnd: "integrable (lborel \<Otimes>\<^sub>M M)
      (\<lambda>p. \<bar>C\<bar> * indicat_real ({a..b} \<times> B) p)"
    by (intro integrable_mult_right int_ind)
  have Fbound: "AE p in lborel \<Otimes>\<^sub>M M.
      norm (F (fst p) (snd p)) \<le> norm (\<bar>C\<bar> * indicat_real ({a..b} \<times> B) p)"
  proof (intro AE_I2)
    fix p :: "real \<times> 'a" assume p: "p \<in> space (lborel \<Otimes>\<^sub>M M)"
    then have sp: "snd p \<in> space M"
      by (auto simp: space_pair_measure mem_Times_iff)
    have "\<bar>f (fst p) (snd p)\<bar> \<le> C" by (rule bnd[OF sp])
    then show "norm (F (fst p) (snd p))
        \<le> norm (\<bar>C\<bar> * indicat_real ({a..b} \<times> B) p)"
      by (cases p)
        (auto simp: F_def indicator_def abs_mult mem_Times_iff)
  qed
  have intF: "integrable (lborel \<Otimes>\<^sub>M M) (\<lambda>p. F (fst p) (snd p))"
    by (rule Bochner_Integration.integrable_bound[OF int_bnd Fm Fbound])
  have intF': "integrable (lborel \<Otimes>\<^sub>M M) (case_prod F)"
    using intF by (simp add: case_prod_beta')
  have swap: "(\<integral>\<omega>. (\<integral>u. F u \<omega> \<partial>lborel) \<partial>M) = (\<integral>u. (\<integral>\<omega>. F u \<omega> \<partial>M) \<partial>lborel)"
    by (rule P.Fubini_integral[OF intF'])
  have lhs: "(\<integral>\<omega>. (\<integral>u. F u \<omega> \<partial>lborel) \<partial>M)
      = (\<integral>\<omega>. indicat_real B \<omega> * (\<integral>u\<in>{a..b}. f u \<omega> \<partial>lborel) \<partial>M)"
    unfolding set_lebesgue_integral_def F_def
    by (simp add: mult_ac flip: integral_mult_right_zero)
  have rhs: "(\<integral>u. (\<integral>\<omega>. F u \<omega> \<partial>M) \<partial>lborel)
      = (\<integral>u\<in>{a..b}. (\<integral>\<omega>. indicat_real B \<omega> * f u \<omega> \<partial>M) \<partial>lborel)"
    unfolding set_lebesgue_integral_def F_def
    by (simp flip: integral_mult_right_zero)
  show ?thesis
    using swap lhs rhs by simp
qed

subsection \<open>The doubled decay and the compensator integral\<close>

lemma drc_exp_diff:
  fixes q s t :: real
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
  shows "exp (- (drc q t - drc q s)) = (q + s) / (q + t)"
proof -
  have qs: "0 < q + s" and qt: "0 < q + t" using q s st by auto
  have e1: "1 + t / q = (q + t) / q" and e2: "1 + s / q = (q + s) / q"
    using q by (simp_all add: field_simps)
  have "drc q t - drc q s = ln ((q + t) / q) - ln ((q + s) / q)"
    unfolding drc_def e1 e2 ..
  also have "\<dots> = ln (q + t) - ln (q + s)"
    using q qs qt by (simp add: ln_div)
  finally have *: "drc q t - drc q s = ln (q + t) - ln (q + s)" .
  have "exp (- (drc q t - drc q s)) = exp (ln (q + s) - ln (q + t))"
    unfolding * by simp
  also have "\<dots> = (q + s) / (q + t)"
    using qs qt by (simp add: exp_diff exp_ln)
  finally show ?thesis .
qed

lemma drc_exp_diff_sq:
  fixes q s t :: real
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
  shows "exp (- (2::real)\<^sup>2 * (drc q t - drc q s) / 2)
       = ((q + s) / (q + t))\<^sup>2"
proof -
  have eq: "- (2::real)\<^sup>2 * (drc q t - drc q s) / 2
      = (- (drc q t - drc q s)) + (- (drc q t - drc q s))"
    by simp
  have "exp (- (2::real)\<^sup>2 * (drc q t - drc q s) / 2)
      = exp (- (drc q t - drc q s)) * exp (- (drc q t - drc q s))"
    unfolding eq by (rule exp_add)
  also have "\<dots> = ((q + s) / (q + t))\<^sup>2"
    unfolding drc_exp_diff[OF q s st] by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma drN_compensator_integral:
  fixes q s t :: real
  assumes qs: "0 < q + s" and st: "s \<le> t"
  shows "(\<integral>u\<in>{s..t}. ((q + s) / (q + u))\<^sup>2 \<partial>lborel)
       = (q + s) - (q + s)\<^sup>2 / (q + t)"
proof -
  have qu: "0 < q + u" if "s \<le> u" for u using qs that by auto
  have cont: "continuous_on {s..t} (\<lambda>u. ((q + s) / (q + u))\<^sup>2)"
    by (intro continuous_intros) (fastforce dest: qu)
  have deriv: "((\<lambda>u. - (q + s)\<^sup>2 / (q + u)) has_vector_derivative
      ((q + s) / (q + u))\<^sup>2) (at u within {s..t})"
    if u: "s \<le> u" "u \<le> t" for u
  proof -
    have "((\<lambda>u. - (q + s)\<^sup>2 / (q + u)) has_real_derivative
        (q + s)\<^sup>2 / (q + u)\<^sup>2) (at u within {s..t})"
      using qu[OF u(1)]
      by (auto intro!: derivative_eq_intros simp: power2_eq_square)
    then show ?thesis
      by (simp add: has_real_derivative_iff_has_vector_derivative
          power_divide)
  qed
  have "(\<integral>x. indicat_real {s..t} x *\<^sub>R ((q + s) / (q + x))\<^sup>2 \<partial>lborel)
      = (- (q + s)\<^sup>2 / (q + t)) - (- (q + s)\<^sup>2 / (q + s))"
    by (rule integral_FTC_atLeastAtMost[OF st deriv cont])
  also have "\<dots> = (q + s) - (q + s)\<^sup>2 / (q + t)"
    using qs by (simp add: power2_eq_square)
  finally show ?thesis
    unfolding set_lebesgue_integral_def .
qed

subsection \<open>The double-angle process\<close>

definition drC2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real" where
  "drC2 q \<phi> u \<omega> = cos (2 * drW (drc q (max u 0)) \<omega> + 2 * \<phi>)"

lemma drC2_eq:
  "0 \<le> u \<Longrightarrow> drC2 q \<phi> u \<omega> = cos (2 * Bcont (drc q u) (\<omega> 1) + 2 * \<phi>)"
  by (simp add: drC2_def drW_def max.absorb1)

lemma drC2_abs: "\<bar>drC2 q \<phi> u \<omega>\<bar> \<le> 1"
  by (simp add: drC2_def abs_cos_le_one)

lemma drC2_cont:
  assumes q: "0 < q"
  shows "continuous_on UNIV (\<lambda>u. drC2 q \<phi> u \<omega>)"
proof -
  have m1: "continuous_on UNIV (\<lambda>u :: real. max u 0)"
    by (intro continuous_intros)
  have m2: "continuous_on UNIV (\<lambda>u :: real. drc q (max u 0))"
    by (rule continuous_on_compose2[OF drc_cont[OF q] m1]) auto
  have img: "(\<lambda>u :: real. drc q (max u 0)) ` UNIV \<subseteq> {0..}"
    by (auto intro!: drc_nonneg[OF q])
  have m3: "continuous_on UNIV (\<lambda>u. Bcont (drc q (max u 0)) (\<omega> 1))"
    by (rule continuous_on_compose2[OF Bcont_cont m2 img])
  show ?thesis
    unfolding drC2_def drW_def
    by (auto intro!: continuous_intros m3)
qed

lemma drC2_meas:
  "drC2 q \<phi> u \<in> borel_measurable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
  using measurable_cbmX_coord[of "drc q (max u 0)" "1 :: 2"]
  unfolding drC2_def drW_def by measurable

lemma SP_cbmX2: "Stochastic_Process.stochastic_process
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0 (cbmX (0 :: real^2))"
  by unfold_locales

lemma drG_subalgebra: "subalgebra (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX (0 :: real^2)) u)"
  by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration
      [OF SP_cbmX2])

lemma drG_filtered: "filtered_measure
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX (0 :: real^2))) 0"
  by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration
      [OF SP_cbmX2])

lemma drG_subalgebra_mono:
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
  shows "subalgebra
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q t))
      (natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q s))"
  by (rule filtered_measure.subalgebra_F[OF drG_filtered
      drc_nonneg[OF q s] drc_mono[OF q s st]])

lemma nth1_meas: "(\<lambda>v :: real^2. v $ 1) \<in> borel_measurable borel"
proof -
  have "(\<lambda>v :: real^2. v $ 1) = (\<lambda>v. inner v (axis 1 1))"
    by (simp add: fun_eq_iff cart_eq_inner_axis)
  then show ?thesis by simp
qed

lemma drW_adapted:
  assumes u: "0 \<le> u"
  shows "drW u \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) u)"
proof -
  have bu: "cbmX (0 :: real^2) u \<in> borel_measurable
      (natural_filtration bm_paths 0 (cbmX (0 :: real^2)) u)"
    by (rule Stochastic_Process.adapted_process.adapted[OF
        Stochastic_Process.stochastic_process.adapted_process_natural_filtration
        [OF SP_cbmX2] u])
  have drW_cbmX: "drW u \<omega> = cbmX (0 :: real^2) u \<omega> $ 1" for \<omega>
    by (simp add: drW_def cbmX_def)
  show ?thesis
    unfolding drW_cbmX[abs_def]
    by (rule measurable_compose[OF bu nth1_meas])
qed

lemma drC2_adapted:
  assumes q: "0 < q" and u: "0 \<le> u" and us: "u \<le> s"
  shows "drC2 q \<phi> u \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q s))"
proof -
  have "drW (drc q u) \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q u))"
    by (rule drW_adapted[OF drc_nonneg[OF q u]])
  then have m: "drW (drc q u) \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q s))"
    using drG_subalgebra_mono[OF q u us]
    by (auto intro: measurable_from_subalg)
  have "drC2 q \<phi> u = (\<lambda>\<omega>. cos (2 * drW (drc q u) \<omega> + 2 * \<phi>))"
    unfolding drC2_def using u by (simp add: max.absorb1)
  then show ?thesis
    using m by simp measurable
qed

subsection \<open>The decay of the double-angle cosine against past events\<close>

lemma drC2_event_integrable:
  assumes B: "B \<in> sets (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
  shows "integrable bm_paths (\<lambda>\<omega>. indicat_real B \<omega> * drC2 q \<phi> v \<omega>)"
proof -
  have m: "(\<lambda>\<omega>. indicat_real B \<omega> * drC2 q \<phi> v \<omega>)
      \<in> borel_measurable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
    using B drC2_meas by measurable
  show ?thesis
    by (rule BMP.integrable_const_bound[where B = 1])
      (use m drC2_abs in \<open>auto intro!: AE_I2 mult_le_one
        simp: abs_mult indicator_def\<close>)
qed

lemma drC2_set_integral_decay:
  fixes q \<phi> s u :: real
  assumes q: "0 < q" and s: "0 \<le> s" and su: "s \<le> u"
    and B: "B \<in> sets (natural_filtration
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
      (cbmX (0 :: real^2)) (drc q s))"
  shows "(\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega> \<partial>bm_paths)
       = ((q + s) / (q + u))\<^sup>2
         * (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> \<partial>bm_paths)"
proof (cases "s = u")
  case True
  have "0 < q + u" using q s su by simp
  then show ?thesis unfolding True[symmetric] using q s by simp
next
  case False
  then have slu: "s < u" using su by simp
  have c0: "0 \<le> drc q s" by (rule drc_nonneg[OF q s])
  have clt: "drc q s < drc q u" by (rule drc_strict_mono[OF q s slu])
  have BM: "B \<in> sets (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
    using B drG_subalgebra by (auto simp: subalgebra_def)
  have KEY: "(\<integral>\<omega>. indicat_real B \<omega> *
      (cos (2 * Bcont (drc q u) (\<omega> 1) + 2 * \<phi>)
        - cos (2 * Bcont (drc q s) (\<omega> 1) + 2 * \<phi>)
          * exp (- (2::real)\<^sup>2 * (drc q u - drc q s) / 2))
      \<partial>bm_paths) = 0"
    by (rule cbm_cos_set_integral[OF c0 clt B])
  let ?e = "exp (- (2::real)\<^sup>2 * (drc q u - drc q s) / 2)"
  have intu: "integrable bm_paths (\<lambda>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega>)"
    and ints: "integrable bm_paths (\<lambda>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega>)"
    by (rule drC2_event_integrable[OF BM])+
  have ints': "integrable bm_paths
      (\<lambda>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> * ?e)"
    by (rule integrable_mult_left[OF ints])
  have expand: "indicat_real B \<omega> *
      (cos (2 * Bcont (drc q u) (\<omega> 1) + 2 * \<phi>)
        - cos (2 * Bcont (drc q s) (\<omega> 1) + 2 * \<phi>) * ?e)
      = indicat_real B \<omega> * drC2 q \<phi> u \<omega>
        - indicat_real B \<omega> * drC2 q \<phi> s \<omega> * ?e" for \<omega>
    using s su
    by (simp add: drC2_eq[OF s] drC2_eq[OF order_trans[OF s su]]
        right_diff_distrib mult_ac)
  have Z: "(\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega>
        - indicat_real B \<omega> * drC2 q \<phi> s \<omega> * ?e \<partial>bm_paths) = 0"
    using KEY unfolding expand .
  have D: "(\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega>
        - indicat_real B \<omega> * drC2 q \<phi> s \<omega> * ?e \<partial>bm_paths)
      = (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega> \<partial>bm_paths)
        - (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> * ?e \<partial>bm_paths)"
    by (rule Bochner_Integration.integral_diff[OF intu ints'])
  have pull: "(\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> * ?e \<partial>bm_paths)
      = (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> \<partial>bm_paths) * ?e"
    by (rule integral_mult_left_zero)
  have *: "(\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega> \<partial>bm_paths)
      = ?e * (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> \<partial>bm_paths)"
    using Z unfolding D pull by simp
  show ?thesis
    using * unfolding drc_exp_diff_sq[OF q s su] .
qed

subsection \<open>The compensated double-angle process\<close>

definition drN :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real" where
  "drN q \<phi> t \<omega> = (q + t) * drC2 q \<phi> t \<omega>
     + set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"

lemma drC2_time_integrable:
  assumes q: "0 < q"
  shows "set_integrable lborel {a..b} (\<lambda>u. drC2 q \<phi> u \<omega>)"
  by (rule borel_integrable_atLeastAtMost')
    (rule continuous_on_subset[OF drC2_cont[OF q] subset_UNIV])

lemma drC2_time_integral_abs:
  assumes q: "0 < q" and ab: "a \<le> b"
  shows "\<bar>set_lebesgue_integral lborel {a..b} (\<lambda>u. drC2 q \<phi> u \<omega>)\<bar> \<le> b - a"
proof -
  have int: "integrable lborel
      (\<lambda>u. indicat_real {a..b} u *\<^sub>R drC2 q \<phi> u \<omega>)"
    using drC2_time_integrable[OF q, of a b \<phi> \<omega>]
    by (simp add: set_integrable_def)
  have int1: "integrable lborel (indicat_real {a..b})"
    by (auto simp: integrable_indicator_iff emeasure_lborel_Icc ab)
  have "\<bar>set_lebesgue_integral lborel {a..b} (\<lambda>u. drC2 q \<phi> u \<omega>)\<bar>
      \<le> (\<integral>u. \<bar>indicat_real {a..b} u *\<^sub>R drC2 q \<phi> u \<omega>\<bar> \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by (rule integral_abs_bound)
  also have "\<dots> \<le> (\<integral>u. indicat_real {a..b} u \<partial>lborel)"
    by (intro integral_mono integrable_abs int int1)
      (use drC2_abs in \<open>auto simp: indicator_def abs_mult mult_le_one\<close>)
  also have "\<dots> = b - a"
    using ab by (simp add: measure_lborel_Icc)
  finally show ?thesis .
qed

lemma drC2_time_integral_meas:
  assumes q: "0 < q"
  shows "(\<lambda>\<omega>. set_lebesgue_integral lborel {a..b} (\<lambda>u. drC2 q \<phi> u \<omega>))
      \<in> borel_measurable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
  by (rule borel_measurable_time_integral)
    (auto intro: drC2_cont[OF q] drC2_meas)

lemma drC2_integral_split:
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
  shows "set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)
       = set_lebesgue_integral lborel {0..s} (\<lambda>u. drC2 q \<phi> u \<omega>)
         + set_lebesgue_integral lborel {s..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
proof -
  have un: "{0..t} = {0..s} \<union> {s<..t}"
    using s st by auto
  have dis: "{0..s} \<inter> {s<..t} = {}" by auto
  have intA: "set_integrable lborel {0..s} (\<lambda>u. drC2 q \<phi> u \<omega>)"
    by (rule drC2_time_integrable[OF q])
  have intT: "set_integrable lborel {s..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
    by (rule drC2_time_integrable[OF q])
  have intB: "set_integrable lborel {s<..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
    by (rule set_integrable_subset[OF intT]) auto
  have "set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)
      = set_lebesgue_integral lborel {0..s} (\<lambda>u. drC2 q \<phi> u \<omega>)
        + set_lebesgue_integral lborel {s<..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
    unfolding un by (rule set_integral_Un[OF dis intA intB])
  moreover have "set_lebesgue_integral lborel {s<..t} (\<lambda>u. drC2 q \<phi> u \<omega>)
      = set_lebesgue_integral lborel {s..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
  proof (rule set_integral_cong_set)
    show "AE x in lborel. x \<in> {s..t} \<longleftrightarrow> x \<in> {s<..t}"
      by (rule AE_I'[where N = "{s}"]) auto
    show "set_borel_measurable lborel {s<..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
      using intB unfolding set_integrable_def set_borel_measurable_def
      by (rule borel_measurable_integrable)
    show "set_borel_measurable lborel {s..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
      using intT unfolding set_integrable_def set_borel_measurable_def
      by (rule borel_measurable_integrable)
  qed
  ultimately show ?thesis by simp
qed

lemma drN_event_integrable:
  assumes q: "0 < q" and t: "0 \<le> t"
    and B: "B \<in> sets (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
  shows "integrable bm_paths (\<lambda>\<omega>. indicat_real B \<omega> * drN q \<phi> t \<omega>)"
proof -
  have m: "(\<lambda>\<omega>. indicat_real B \<omega> * drN q \<phi> t \<omega>)
      \<in> borel_measurable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
    unfolding drN_def
    using B drC2_meas drC2_time_integral_meas[OF q] by measurable
  have bnd: "\<bar>indicat_real B \<omega> * drN q \<phi> t \<omega>\<bar> \<le> (q + t) + t" for \<omega>
  proof -
    have "\<bar>drN q \<phi> t \<omega>\<bar> \<le> \<bar>(q + t) * drC2 q \<phi> t \<omega>\<bar>
        + \<bar>set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)\<bar>"
      unfolding drN_def by (rule abs_triangle_ineq)
    also have "\<dots> \<le> \<bar>q + t\<bar> * 1 + (t - 0)"
    proof (intro add_mono)
      have "\<bar>(q + t) * drC2 q \<phi> t \<omega>\<bar> = \<bar>q + t\<bar> * \<bar>drC2 q \<phi> t \<omega>\<bar>"
        by (simp add: abs_mult)
      also have "\<dots> \<le> \<bar>q + t\<bar> * 1"
        by (intro mult_left_mono drC2_abs abs_ge_zero)
      finally show "\<bar>(q + t) * drC2 q \<phi> t \<omega>\<bar> \<le> \<bar>q + t\<bar> * 1" .
      show "\<bar>set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)\<bar>
          \<le> t - 0"
        by (rule drC2_time_integral_abs[OF q t])
    qed
    also have "\<dots> = \<bar>q + t\<bar> + t" by simp
    also have "\<dots> = (q + t) + t" using q t by simp
    finally have *: "\<bar>drN q \<phi> t \<omega>\<bar> \<le> (q + t) + t" .
    have "\<bar>indicat_real B \<omega> * drN q \<phi> t \<omega>\<bar> \<le> \<bar>drN q \<phi> t \<omega>\<bar>"
      by (simp add: abs_mult indicator_def)
    with * show ?thesis by linarith
  qed
  show ?thesis
    by (rule BMP.integrable_const_bound[where B = "(q + t) + t"])
      (use m bnd in \<open>auto intro!: AE_I2\<close>)
qed

lemma drN_set_integral_identity:
  fixes q \<phi> s t :: real
  assumes q: "0 < q" and s: "0 \<le> s" and st: "s \<le> t"
    and B: "B \<in> sets (natural_filtration
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
      (cbmX (0 :: real^2)) (drc q s))"
  shows "(\<integral>\<omega>. indicat_real B \<omega> * drN q \<phi> t \<omega> \<partial>bm_paths)
       = (\<integral>\<omega>. indicat_real B \<omega> * drN q \<phi> s \<omega> \<partial>bm_paths)"
proof -
  let ?M = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
  let ?I = "\<lambda>v \<omega>. set_lebesgue_integral lborel {0..v} (\<lambda>u. drC2 q \<phi> u \<omega>)"
  let ?Is = "\<lambda>\<omega>. set_lebesgue_integral lborel {s..t} (\<lambda>u. drC2 q \<phi> u \<omega>)"
  have qs: "0 < q + s" and qt: "0 < q + t" using q s st by auto
  have t0: "0 \<le> t" using s st by simp
  have BM: "B \<in> sets ?M"
    using B drG_subalgebra by (auto simp: subalgebra_def)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  let ?J = "\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> s \<omega> \<partial>?M"
  have T1: "(\<integral>\<omega>. indicat_real B \<omega> * ((q + t) * drC2 q \<phi> t \<omega>) \<partial>?M)
      = (q + s)\<^sup>2 / (q + t) * ?J"
  proof -
    have "(\<integral>\<omega>. indicat_real B \<omega> * ((q + t) * drC2 q \<phi> t \<omega>) \<partial>?M)
        = (q + t) * (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> t \<omega> \<partial>?M)"
      by (subst integral_mult_right_zero[symmetric])
        (simp add: mult_ac)
    also have "\<dots> = (q + t) * (((q + s) / (q + t))\<^sup>2 * ?J)"
      unfolding drC2_set_integral_decay[OF q s st B] ..
    also have "\<dots> = (q + s)\<^sup>2 / (q + t) * ?J"
      using qt by (simp add: power_divide power2_eq_square)
    finally show ?thesis .
  qed
  have T3: "(\<integral>\<omega>. indicat_real B \<omega> * ?Is \<omega> \<partial>?M)
      = ((q + s) - (q + s)\<^sup>2 / (q + t)) * ?J"
  proof -
    have "(\<integral>\<omega>. indicat_real B \<omega> * ?Is \<omega> \<partial>?M)
        = (\<integral>u\<in>{s..t}. (\<integral>\<omega>. indicat_real B \<omega> * drC2 q \<phi> u \<omega> \<partial>?M) \<partial>lborel)"
      by (rule time_integral_swap_event[OF fm _ _ _ BM, of _ 1])
        (auto intro: drC2_cont[OF q] drC2_meas drC2_abs)
    also have "\<dots> = (\<integral>u\<in>{s..t}. ((q + s) / (q + u))\<^sup>2 * ?J \<partial>lborel)"
      by (rule set_lebesgue_integral_cong)
        (auto intro!: drC2_set_integral_decay[OF q s _ B])
    also have "\<dots> = (\<integral>u\<in>{s..t}. ((q + s) / (q + u))\<^sup>2 \<partial>lborel) * ?J"
      by (rule set_integral_mult_left)
    also have "\<dots> = ((q + s) - (q + s)\<^sup>2 / (q + t)) * ?J"
      unfolding drN_compensator_integral[OF qs st] ..
    finally show ?thesis .
  qed
  have i_dc_t: "integrable ?M
      (\<lambda>\<omega>. indicat_real B \<omega> * ((q + t) * drC2 q \<phi> t \<omega>))"
    using drC2_event_integrable[OF BM, of q \<phi> t]
    by (subst mult.left_commute) (rule integrable_mult_right)
  have i_dc_s: "integrable ?M
      (\<lambda>\<omega>. indicat_real B \<omega> * ((q + s) * drC2 q \<phi> s \<omega>))"
    using drC2_event_integrable[OF BM, of q \<phi> s]
    by (subst mult.left_commute) (rule integrable_mult_right)
  have i_I: "integrable ?M (\<lambda>\<omega>. indicat_real B \<omega> * ?I v \<omega>)"
    if v: "0 \<le> v" for v
  proof -
    have m: "(\<lambda>\<omega>. indicat_real B \<omega> * ?I v \<omega>) \<in> borel_measurable ?M"
      using BM drC2_time_integral_meas[OF q] by measurable
    have bnd: "\<bar>indicat_real B \<omega> * ?I v \<omega>\<bar> \<le> v" for \<omega>
    proof -
      have "\<bar>indicat_real B \<omega> * ?I v \<omega>\<bar> \<le> \<bar>?I v \<omega>\<bar>"
        by (simp add: abs_mult indicator_def)
      also have "\<dots> \<le> v - 0"
        by (rule drC2_time_integral_abs[OF q v])
      finally show ?thesis by simp
    qed
    show ?thesis
      by (rule BMP.integrable_const_bound[where B = v])
        (use m bnd in \<open>auto intro!: AE_I2\<close>)
  qed
  have i_Is: "integrable ?M (\<lambda>\<omega>. indicat_real B \<omega> * ?Is \<omega>)"
  proof -
    have m: "(\<lambda>\<omega>. indicat_real B \<omega> * ?Is \<omega>) \<in> borel_measurable ?M"
      using BM drC2_time_integral_meas[OF q] by measurable
    have bnd: "\<bar>indicat_real B \<omega> * ?Is \<omega>\<bar> \<le> t - s" for \<omega>
    proof -
      have "\<bar>indicat_real B \<omega> * ?Is \<omega>\<bar> \<le> \<bar>?Is \<omega>\<bar>"
        by (simp add: abs_mult indicator_def)
      also have "\<dots> \<le> t - s"
        by (rule drC2_time_integral_abs[OF q st])
      finally show ?thesis .
    qed
    show ?thesis
      by (rule BMP.integrable_const_bound[where B = "t - s"])
        (use m bnd in \<open>auto intro!: AE_I2\<close>)
  qed
  have exp_t: "indicat_real B \<omega> * drN q \<phi> t \<omega>
      = indicat_real B \<omega> * ((q + t) * drC2 q \<phi> t \<omega>)
        + indicat_real B \<omega> * ?I s \<omega>
        + indicat_real B \<omega> * ?Is \<omega>" for \<omega>
    unfolding drN_def drC2_integral_split[OF q s st, of \<phi> \<omega>]
    by (simp add: distrib_left)
  have exp_s: "indicat_real B \<omega> * drN q \<phi> s \<omega>
      = indicat_real B \<omega> * ((q + s) * drC2 q \<phi> s \<omega>)
        + indicat_real B \<omega> * ?I s \<omega>" for \<omega>
    unfolding drN_def by (simp add: distrib_left)
  have LHS: "(\<integral>\<omega>. indicat_real B \<omega> * drN q \<phi> t \<omega> \<partial>?M)
      = (\<integral>\<omega>. indicat_real B \<omega> * ((q + t) * drC2 q \<phi> t \<omega>) \<partial>?M)
        + (\<integral>\<omega>. indicat_real B \<omega> * ?I s \<omega> \<partial>?M)
        + (\<integral>\<omega>. indicat_real B \<omega> * ?Is \<omega> \<partial>?M)"
    unfolding exp_t
    by (simp add: Bochner_Integration.integral_add[OF
        Bochner_Integration.integrable_add[OF i_dc_t i_I[OF s]] i_Is]
        Bochner_Integration.integral_add[OF i_dc_t i_I[OF s]])
  have RHS: "(\<integral>\<omega>. indicat_real B \<omega> * drN q \<phi> s \<omega> \<partial>?M)
      = (\<integral>\<omega>. indicat_real B \<omega> * ((q + s) * drC2 q \<phi> s \<omega>) \<partial>?M)
        + (\<integral>\<omega>. indicat_real B \<omega> * ?I s \<omega> \<partial>?M)"
    unfolding exp_s
    by (rule Bochner_Integration.integral_add[OF i_dc_s i_I[OF s]])
  have S1: "(\<integral>\<omega>. indicat_real B \<omega> * ((q + s) * drC2 q \<phi> s \<omega>) \<partial>?M)
      = (q + s) * ?J"
    by (subst integral_mult_right_zero[symmetric]) (simp add: mult_ac)
  have "(\<integral>\<omega>. indicat_real B \<omega> * drN q \<phi> t \<omega> \<partial>?M)
      = (q + s)\<^sup>2 / (q + t) * ?J + (\<integral>\<omega>. indicat_real B \<omega> * ?I s \<omega> \<partial>?M)
        + ((q + s) - (q + s)\<^sup>2 / (q + t)) * ?J"
    unfolding LHS T1 T3 ..
  also have "\<dots> = (q + s) * ?J + (\<integral>\<omega>. indicat_real B \<omega> * ?I s \<omega> \<partial>?M)"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<integral>\<omega>. indicat_real B \<omega> * drN q \<phi> s \<omega> \<partial>?M)"
    unfolding RHS S1 ..
  finally show ?thesis .
qed

subsection \<open>The compensated double-angle process is a martingale\<close>

lemma drN_meas:
  assumes q: "0 < q"
  shows "drN q \<phi> t \<in> borel_measurable
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
  unfolding drN_def
  using drC2_meas drC2_time_integral_meas[OF q] by measurable

lemma drN_abs:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "\<bar>drN q \<phi> t \<omega>\<bar> \<le> (q + t) + t"
proof -
  have "\<bar>drN q \<phi> t \<omega>\<bar> \<le> \<bar>(q + t) * drC2 q \<phi> t \<omega>\<bar>
      + \<bar>set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)\<bar>"
    unfolding drN_def by (rule abs_triangle_ineq)
  also have "\<dots> \<le> \<bar>q + t\<bar> * 1 + (t - 0)"
  proof (intro add_mono)
    have "\<bar>(q + t) * drC2 q \<phi> t \<omega>\<bar> = \<bar>q + t\<bar> * \<bar>drC2 q \<phi> t \<omega>\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>q + t\<bar> * 1"
      by (intro mult_left_mono drC2_abs abs_ge_zero)
    finally show "\<bar>(q + t) * drC2 q \<phi> t \<omega>\<bar> \<le> \<bar>q + t\<bar> * 1" .
    show "\<bar>set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)\<bar>
        \<le> t - 0"
      by (rule drC2_time_integral_abs[OF q t])
  qed
  also have "\<dots> = (q + t) + t" using q t by simp
  finally show ?thesis .
qed

lemma drN_integrable:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "integrable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) (drN q \<phi> t)"
  by (rule BMP.integrable_const_bound[where B = "(q + t) + t"])
    (use drN_meas[OF q] drN_abs[OF q t] in \<open>auto intro!: AE_I2\<close>)

lemma drC2_max: "drC2 q \<phi> (max u 0) = drC2 q \<phi> u"
proof -
  have eq: "max (max u 0) 0 = max u 0"
    by (metis max.assoc max.idem)
  show ?thesis
    by (intro ext) (simp add: drC2_def eq)
qed

lemma drC2_adapted':
  assumes q: "0 < q" and t: "0 \<le> t" and ut: "u \<le> t"
  shows "drC2 q \<phi> u \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q t))"
proof -
  have "drC2 q \<phi> (max u 0) \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q t))"
    by (rule drC2_adapted[OF q]) (use t ut in auto)
  then show ?thesis unfolding drC2_max .
qed

lemma drN_adapted:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "drN q \<phi> t \<in> borel_measurable
      (natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^2)) (drc q t))"
proof -
  let ?G = "natural_filtration (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure) 0
      (cbmX (0 :: real^2)) (drc q t)"
  have part1: "(\<lambda>\<omega>. (q + t) * drC2 q \<phi> t \<omega>) \<in> borel_measurable ?G"
    using drC2_adapted[OF q t order_refl] by measurable
  have eqI: "set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)
      = set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> (min u t) \<omega>)"
    for \<omega>
    by (rule set_lebesgue_integral_cong) (auto simp: min_absorb1)
  have mc: "continuous_on UNIV (\<lambda>u :: real. min u t)"
    by (intro continuous_intros)
  have contmin: "continuous_on UNIV (\<lambda>u. drC2 q \<phi> (min u t) \<omega>)" for \<omega>
    by (rule continuous_on_compose2[OF drC2_cont[OF q] mc]) auto
  have measmin: "drC2 q \<phi> (min u t) \<in> borel_measurable ?G" for u
    by (rule drC2_adapted'[OF q t]) simp
  have part2: "(\<lambda>\<omega>. set_lebesgue_integral lborel {0..t}
      (\<lambda>u. drC2 q \<phi> (min u t) \<omega>)) \<in> borel_measurable ?G"
    by (rule borel_measurable_time_integral)
      (use contmin measmin in auto)
  have expand: "drN q \<phi> t = (\<lambda>\<omega>. (q + t) * drC2 q \<phi> t \<omega>
      + set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> (min u t) \<omega>))"
    unfolding drN_def using eqI by (intro ext) simp
  show ?thesis
    unfolding expand by (intro borel_measurable_add part1 part2)
qed

lemma drG_sigma_finite_subalgebra:
  "sigma_finite_subalgebra (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX (0 :: real^2)) u)"
proof -
  have fm: "finite_measure (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  show ?thesis
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fm drG_subalgebra)
qed

lemma drG_sigma_finite_filtered:
  assumes q: "0 < q"
  shows "sigma_finite_filtered_measure
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t)) 0"
proof -
  have FMG: "filtered_measure (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t)) 0"
    unfolding filtered_measure_def
    using drG_subalgebra drG_subalgebra_mono[OF q]
    by (auto simp: subalgebra_def)
  show ?thesis
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro FMG
        drG_sigma_finite_subalgebra)
qed

theorem martingale_drN:
  fixes q \<phi> :: real
  assumes q: "0 < q"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (drN q \<phi>)"
proof -
  let ?M = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
  let ?G = "\<lambda>t. natural_filtration ?M 0 (cbmX (0 :: real^2)) (drc q t)"
  have Gmono: "sets (?G s) \<subseteq> sets (?G t)" if "0 \<le> s" "s \<le> t" for s t
    using drG_subalgebra_mono[OF q that]
    by (auto simp: subalgebra_def)
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?G 0"
      by (rule drG_sigma_finite_filtered[OF q])
    show "adapted_process ?M ?G 0 (drN q \<phi>)"
      by unfold_locales
        (auto intro: drG_subalgebra drN_adapted[OF q]
          dest: Gmono[THEN subsetD])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (drN q \<phi> i)"
      by (rule drN_integrable[OF q])
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    have hce: "has_cond_exp ?M (?G i) (drN q \<phi> j) (drN q \<phi> i)"
    proof (rule has_cond_expI')
      show "integrable ?M (drN q \<phi> j)"
        by (rule drN_integrable[OF q order_trans[OF ij(1) ij(2)]])
      show "integrable ?M (drN q \<phi> i)"
        by (rule drN_integrable[OF q ij(1)])
      show "drN q \<phi> i \<in> borel_measurable (?G i)"
        by (rule drN_adapted[OF q ij(1)])
      fix A assume A: "A \<in> sets (?G i)"
      show "(\<integral>\<omega>\<in>A. drN q \<phi> j \<omega> \<partial>?M) = (\<integral>\<omega>\<in>A. drN q \<phi> i \<omega> \<partial>?M)"
        using drN_set_integral_identity[OF q ij(1) ij(2) A]
        unfolding set_lebesgue_integral_def by simp
    qed
    show "AE \<omega> in ?M. drN q \<phi> i \<omega> = cond_exp ?M (?G i) (drN q \<phi> j) \<omega>"
      using sigma_finite_subalgebra.has_cond_exp_charact(2)
          [OF drG_sigma_finite_subalgebra hce]
      by eventually_elim simp
  qed
qed

subsection \<open>The tangent covariance and the coordinate identities\<close>

text \<open>The instantaneous covariance of the deterministic-radius market is
  the projection onto the tangent direction \<open>v = (sin \<Theta>, −cos \<Theta>)\<close>:
  \<open>a(X) = v vᵀ = I − X Xᵀ/|X|²\<close>.\<close>

definition dra :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^2^2"
  where
  "dra q \<phi> u \<omega> = (\<chi> j. \<chi> l.
     (if j = 1 then sin (drW (drc q u) \<omega> + \<phi>)
      else - cos (drW (drc q u) \<omega> + \<phi>))
     * (if l = 1 then sin (drW (drc q u) \<omega> + \<phi>)
        else - cos (drW (drc q u) \<omega> + \<phi>)))"

text \<open>Continuity of \<^const>\<open>dra\<close> in TIME, by the same route as
  \<^const>\<open>drC2\<close>'s continuity lemma: the clock is continuous on the
  nonnegative reals, the Brownian path is continuous, and the entries are
  sines and cosines of their composition.  This is what the market locale's
  covariance time-measurability assumption needs.  The paper gets that
  property for free, because there the covariation density is an a.e.
  derivative and so measurable by construction; here the density is
  primitive, so it has to be proved.\<close>

lemma dra_cont:
  assumes q: "0 < q"
  shows "continuous_on UNIV (\<lambda>u. dra q \<phi> (max u 0) \<omega>)"
proof -
  have m1: "continuous_on UNIV (\<lambda>u :: real. max u 0)"
    by (intro continuous_intros)
  have m2: "continuous_on UNIV (\<lambda>u :: real. drc q (max u 0))"
    by (rule continuous_on_compose2[OF drc_cont[OF q] m1]) auto
  have img: "(\<lambda>u :: real. drc q (max u 0)) ` UNIV \<subseteq> {0..}"
    by (auto intro!: drc_nonneg[OF q])
  have m3: "continuous_on UNIV (\<lambda>u. Bcont (drc q (max u 0)) (\<omega> 1))"
    by (rule continuous_on_compose2[OF Bcont_cont m2 img])
  have ent: "continuous_on UNIV
      (\<lambda>u. dra q \<phi> (max u 0) \<omega> $ j $ l)" for j l
    unfolding dra_def drW_def
    by (cases "j = 1"; cases "l = 1")
      (auto intro!: continuous_intros m3)
  have "continuous_on UNIV
      (\<lambda>u. \<chi> j. \<chi> l. dra q \<phi> (max u 0) \<omega> $ j $ l)"
    by (intro continuous_on_vec_lambda ent)
  then show ?thesis by simp
qed

lemma dra_11: "dra q \<phi> u \<omega> $ 1 $ 1 = (sin (drW (drc q u) \<omega> + \<phi>))\<^sup>2"
  by (simp add: dra_def power2_eq_square)

lemma dra_22: "dra q \<phi> u \<omega> $ 2 $ 2 = (cos (drW (drc q u) \<omega> + \<phi>))\<^sup>2"
  by (simp add: dra_def power2_eq_square)

lemma drC2_cos2:
  assumes u: "0 \<le> u"
  shows "cos (2 * (drW (drc q u) \<omega> + \<phi>)) = drC2 q \<phi> u \<omega>"
  unfolding drC2_eq[OF u] drW_def by (simp add: algebra_simps)

lemma dra_diag_integrable:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "set_integrable lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega> / 2)"
    and "set_integrable lborel {0..t} (\<lambda>_ :: real. 1 / 2 :: real)"
proof -
  show "set_integrable lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega> / 2)"
    by (rule borel_integrable_atLeastAtMost')
      (auto intro!: continuous_intros
        continuous_on_subset[OF drC2_cont[OF q] subset_UNIV])
  show "set_integrable lborel {0..t} (\<lambda>_ :: real. 1 / 2 :: real)"
    by (rule borel_integrable_atLeastAtMost') simp
qed

lemma dra_compensator_11:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "set_lebesgue_integral lborel {0..t} (\<lambda>u. dra q \<phi> u \<omega> $ 1 $ 1)
       = t / 2
         - (set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)) / 2"
proof -
  have ptw: "dra q \<phi> u \<omega> $ 1 $ 1 = 1 / 2 - drC2 q \<phi> u \<omega> / 2"
    if u: "u \<in> {0..t}" for u
  proof -
    have "dra q \<phi> u \<omega> $ 1 $ 1 = (sin (drW (drc q u) \<omega> + \<phi>))\<^sup>2"
      by (rule dra_11)
    also have "\<dots> = (1 - cos (2 * (drW (drc q u) \<omega> + \<phi>))) / 2"
      using cos_double_sin[of "drW (drc q u) \<omega> + \<phi>"] by simp
    also have "\<dots> = (1 - drC2 q \<phi> u \<omega>) / 2"
      using u by (simp add: drC2_eq drW_def)
    finally show ?thesis by simp
  qed
  have "set_lebesgue_integral lborel {0..t} (\<lambda>u. dra q \<phi> u \<omega> $ 1 $ 1)
      = set_lebesgue_integral lborel {0..t}
          (\<lambda>u. 1 / 2 - drC2 q \<phi> u \<omega> / 2)"
    by (rule set_lebesgue_integral_cong) (use ptw in auto)
  also have "\<dots> = (set_lebesgue_integral lborel {0..t} (\<lambda>_. 1 / 2 :: real))
      - (set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega> / 2))"
    by (intro set_integral_diff dra_diag_integrable[OF q t])
  also have "set_lebesgue_integral lborel {0..t} (\<lambda>_. 1 / 2 :: real)
      = t / 2"
    using t by (subst set_integral_const)
      (auto simp: emeasure_lborel_Icc measure_lborel_Icc)
  also have "set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega> / 2)
      = (set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)) / 2"
    by (rule set_integral_divide_zero)
  finally show ?thesis .
qed

lemma dra_compensator_22:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "set_lebesgue_integral lborel {0..t} (\<lambda>u. dra q \<phi> u \<omega> $ 2 $ 2)
       = t / 2
         + (set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)) / 2"
proof -
  have ptw: "dra q \<phi> u \<omega> $ 2 $ 2 = 1 / 2 + drC2 q \<phi> u \<omega> / 2"
    if u: "u \<in> {0..t}" for u
  proof -
    have "dra q \<phi> u \<omega> $ 2 $ 2 = (cos (drW (drc q u) \<omega> + \<phi>))\<^sup>2"
      by (rule dra_22)
    also have "\<dots> = (1 + cos (2 * (drW (drc q u) \<omega> + \<phi>))) / 2"
      using cos_double_cos[of "drW (drc q u) \<omega> + \<phi>"] by simp
    also have "\<dots> = (1 + drC2 q \<phi> u \<omega>) / 2"
      using u by (simp add: drC2_eq drW_def)
    finally show ?thesis by simp
  qed
  have "set_lebesgue_integral lborel {0..t} (\<lambda>u. dra q \<phi> u \<omega> $ 2 $ 2)
      = set_lebesgue_integral lborel {0..t}
          (\<lambda>u. 1 / 2 + drC2 q \<phi> u \<omega> / 2)"
    by (rule set_lebesgue_integral_cong) (use ptw in auto)
  also have "\<dots> = (set_lebesgue_integral lborel {0..t} (\<lambda>_. 1 / 2 :: real))
      + (set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega> / 2))"
    by (intro set_integral_add dra_diag_integrable[OF q t])
  also have "set_lebesgue_integral lborel {0..t} (\<lambda>_. 1 / 2 :: real)
      = t / 2"
    using t by (subst set_integral_const)
      (auto simp: emeasure_lborel_Icc measure_lborel_Icc)
  also have "set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega> / 2)
      = (set_lebesgue_integral lborel {0..t} (\<lambda>u. drC2 q \<phi> u \<omega>)) / 2"
    by (rule set_integral_divide_zero)
  finally show ?thesis .
qed

lemma coord_Z_drX_1:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "coord_Z (drX q \<phi>) (dra q \<phi>) 1 t \<omega> = q / 2 + drN q \<phi> t \<omega> / 2"
proof -
  have comp1: "drX q \<phi> t \<omega> $ 1 = drR q t * cos (drW (drc q t) \<omega> + \<phi>)"
    by (simp add: drX_def)
  have drRsq: "(drR q t)\<^sup>2 = q + t"
    using q t by (simp add: drR_def)
  have sq: "(drX q \<phi> t \<omega> $ 1)\<^sup>2
      = (q + t) * (cos (drW (drc q t) \<omega> + \<phi>))\<^sup>2"
    unfolding comp1 power_mult_distrib drRsq ..
  have cossq: "(q + t) * (cos (drW (drc q t) \<omega> + \<phi>))\<^sup>2
      = (q + t) / 2 + (q + t) * drC2 q \<phi> t \<omega> / 2"
  proof -
    have c2: "(cos (drW (drc q t) \<omega> + \<phi>))\<^sup>2 = (1 + drC2 q \<phi> t \<omega>) / 2"
    proof -
      have "(cos (drW (drc q t) \<omega> + \<phi>))\<^sup>2
          = (1 + cos (2 * (drW (drc q t) \<omega> + \<phi>))) / 2"
        using cos_double_cos[of "drW (drc q t) \<omega> + \<phi>"] by simp
      also have "\<dots> = (1 + drC2 q \<phi> t \<omega>) / 2"
        using t by (simp add: drC2_eq drW_def)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding c2 by (simp add: distrib_left add_divide_distrib)
  qed
  show ?thesis
    unfolding coord_Z_def sq cossq dra_compensator_11[OF q t] drN_def
    by argo
qed

lemma coord_Z_drX_2:
  assumes q: "0 < q" and t: "0 \<le> t"
  shows "coord_Z (drX q \<phi>) (dra q \<phi>) 2 t \<omega> = q / 2 - drN q \<phi> t \<omega> / 2"
proof -
  have comp2: "drX q \<phi> t \<omega> $ 2 = drR q t * sin (drW (drc q t) \<omega> + \<phi>)"
    by (simp add: drX_def)
  have drRsq: "(drR q t)\<^sup>2 = q + t"
    using q t by (simp add: drR_def)
  have sq: "(drX q \<phi> t \<omega> $ 2)\<^sup>2
      = (q + t) * (sin (drW (drc q t) \<omega> + \<phi>))\<^sup>2"
    unfolding comp2 power_mult_distrib drRsq ..
  have sinsq: "(q + t) * (sin (drW (drc q t) \<omega> + \<phi>))\<^sup>2
      = (q + t) / 2 - (q + t) * drC2 q \<phi> t \<omega> / 2"
  proof -
    have s2: "(sin (drW (drc q t) \<omega> + \<phi>))\<^sup>2 = (1 - drC2 q \<phi> t \<omega>) / 2"
    proof -
      have "(sin (drW (drc q t) \<omega> + \<phi>))\<^sup>2
          = (1 - cos (2 * (drW (drc q t) \<omega> + \<phi>))) / 2"
        using cos_double_sin[of "drW (drc q t) \<omega> + \<phi>"] by simp
      also have "\<dots> = (1 - drC2 q \<phi> t \<omega>) / 2"
        using t by (simp add: drC2_eq drW_def)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding s2 by (simp add: right_diff_distrib diff_divide_distrib)
  qed
  show ?thesis
    unfolding coord_Z_def sq sinsq dra_compensator_22[OF q t] drN_def
    by argo
qed

subsection \<open>The compensated coordinate squares are martingales\<close>

lemma coord_Z_drX_meas_neg:
  fixes i :: 2
  assumes q: "0 < q" and t: "t < 0"
  shows "coord_Z (drX q \<phi>) (dra q \<phi>) i t \<in> borel_measurable
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
proof -
  have e: "{0..t} = ({} :: real set)" using t by auto
  have z: "coord_Z (drX q \<phi>) (dra q \<phi>) i t = (\<lambda>\<omega>. (drX q \<phi> t \<omega> $ i)\<^sup>2)"
    unfolding coord_Z_def e
    by (simp add: fun_eq_iff set_lebesgue_integral_def)
  have comp: "drX q \<phi> t \<omega> $ i
      = drR q t * (if i = 1 then cos (drW (drc q t) \<omega> + \<phi>)
          else sin (drW (drc q t) \<omega> + \<phi>))" for \<omega>
    by (simp add: drX_def)
  have m: "(\<lambda>\<omega>. drX q \<phi> t \<omega> $ i) \<in> borel_measurable
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
  proof (cases "i = 1")
    case True
    have m1: "(\<lambda>\<omega> :: 2 \<Rightarrow> real \<Rightarrow> real.
        drR q t * cos (Bcont (drc q t) (\<omega> 1) + \<phi>))
        \<in> borel_measurable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
      using measurable_cbmX_coord[of "drc q t" "1 :: 2"] by measurable
    have comp1: "(\<lambda>\<omega> :: 2 \<Rightarrow> real \<Rightarrow> real. drX q \<phi> t \<omega> $ i)
        = (\<lambda>\<omega>. drR q t * cos (drW (drc q t) \<omega> + \<phi>))"
      by (simp add: fun_eq_iff drX_def True)
    show ?thesis
      unfolding comp1 using m1 by (simp add: drW_def)
  next
    case False
    have m2: "(\<lambda>\<omega> :: 2 \<Rightarrow> real \<Rightarrow> real.
        drR q t * sin (Bcont (drc q t) (\<omega> 1) + \<phi>))
        \<in> borel_measurable (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)"
      using measurable_cbmX_coord[of "drc q t" "1 :: 2"] by measurable
    show ?thesis
      using m2 False by (simp add: comp[abs_def] drW_def)
  qed
  show ?thesis
    unfolding z by (intro borel_measurable_power m)
qed

theorem martingale_coord_Z_drX:
  fixes q \<phi> :: real and i :: 2
  assumes q: "0 < q"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (coord_Z (drX q \<phi>) (dra q \<phi>) i)"
proof -
  let ?M = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
  let ?G = "\<lambda>t. natural_filtration ?M 0 (cbmX (0 :: real^2)) (drc q t)"
  define d where "d = (if i = 1 then (1 :: real) else - 1)"
  have ID: "coord_Z (drX q \<phi>) (dra q \<phi>) i t
      = (\<lambda>\<omega>. q / 2 + d / 2 * drN q \<phi> t \<omega>)" if t: "0 \<le> t" for t
    using exhaust_2[of i] coord_Z_drX_1[OF q t, of \<phi>]
      coord_Z_drX_2[OF q t, of \<phi>]
    by (auto simp: d_def fun_eq_iff)
  have Gmono: "sets (?G s) \<subseteq> sets (?G t)" if "0 \<le> s" "s \<le> t" for s t
    using drG_subalgebra_mono[OF q that]
    by (auto simp: subalgebra_def)
  have adaptedI: "coord_Z (drX q \<phi>) (dra q \<phi>) i t
      \<in> borel_measurable (?G t)" if t: "0 \<le> t" for t
    unfolding ID[OF t]
    using drN_adapted[OF q t, of \<phi>] by measurable
  have measI: "coord_Z (drX q \<phi>) (dra q \<phi>) i t \<in> borel_measurable ?M"
    for t
  proof (cases "0 \<le> t")
    case True
    show ?thesis
      unfolding ID[OF True] using drN_meas[OF q, of \<phi> t] by measurable
  next
    case False
    then show ?thesis by (intro coord_Z_drX_meas_neg[OF q]) simp
  qed
  have intI: "integrable ?M (coord_Z (drX q \<phi>) (dra q \<phi>) i t)"
    if t: "0 \<le> t" for t
    unfolding ID[OF t]
    by (intro Bochner_Integration.integrable_add BMP.integrable_const
        integrable_mult_right drN_integrable[OF q t])
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?G 0"
      by (rule drG_sigma_finite_filtered[OF q])
    show "adapted_process ?M ?G 0 (coord_Z (drX q \<phi>) (dra q \<phi>) i)"
      by unfold_locales
        (auto intro: drG_subalgebra adaptedI measI
          dest: Gmono[THEN subsetD])
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M (coord_Z (drX q \<phi>) (dra q \<phi>) i t)"
      by (rule intI)
    fix s t :: real assume st: "0 \<le> s" "s \<le> t"
    have t0: "0 \<le> t" using st by simp
    have int_c: "integrable ?M (\<lambda>_ :: 2 \<Rightarrow> real \<Rightarrow> real. q / 2)"
      by (rule BMP.integrable_const)
    have int_d: "integrable ?M (\<lambda>\<omega>. (d / 2) *\<^sub>R drN q \<phi> t \<omega>)"
      by (intro integrable_scaleR_right drN_integrable[OF q t0])
    have E_add: "AE \<omega> in ?M. cond_exp ?M (?G s)
        (\<lambda>\<omega>. q / 2 + (d / 2) *\<^sub>R drN q \<phi> t \<omega>) \<omega>
        = cond_exp ?M (?G s) (\<lambda>_. q / 2) \<omega>
          + cond_exp ?M (?G s) (\<lambda>\<omega>. (d / 2) *\<^sub>R drN q \<phi> t \<omega>) \<omega>"
      by (rule sigma_finite_subalgebra.cond_exp_add
          [OF drG_sigma_finite_subalgebra int_c int_d])
    have E_c: "AE \<omega> in ?M. cond_exp ?M (?G s)
        (\<lambda>_ :: 2 \<Rightarrow> real \<Rightarrow> real. q / 2) \<omega> = q / 2"
      by (rule sigma_finite_subalgebra.cond_exp_F_meas
          [OF drG_sigma_finite_subalgebra int_c]) simp
    have E_d: "AE \<omega> in ?M. cond_exp ?M (?G s)
        (\<lambda>\<omega>. (d / 2) *\<^sub>R drN q \<phi> t \<omega>) \<omega>
        = (d / 2) *\<^sub>R cond_exp ?M (?G s) (drN q \<phi> t) \<omega>"
      by (rule sigma_finite_subalgebra.cond_exp_scaleR_right
          [OF drG_sigma_finite_subalgebra drN_integrable[OF q t0]])
    have P: "AE \<omega> in ?M. drN q \<phi> s \<omega>
        = cond_exp ?M (?G s) (drN q \<phi> t) \<omega>"
      by (rule martingale.martingale_property
          [OF martingale_drN[OF q] st])
    show "AE \<omega> in ?M. coord_Z (drX q \<phi>) (dra q \<phi>) i s \<omega>
        = cond_exp ?M (?G s) (coord_Z (drX q \<phi>) (dra q \<phi>) i t) \<omega>"
      unfolding ID[OF st(1)] ID[OF t0]
      using E_add E_c E_d P by eventually_elim simp
  qed
qed

subsection \<open>The stopped market\<close>

definition drXs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^2"
  where "drXs q \<phi> T0 t = drX q \<phi> (min t T0)"

definition dras ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^2^2"
  where "dras q \<phi> T0 u \<omega> = (if u \<le> T0 then dra q \<phi> u \<omega> else 0)"

lemma dras_measurable_time:
  assumes q: "0 < q"
  shows "set_borel_measurable lborel {0..} (\<lambda>u. dras q \<phi> T0 u \<omega>)"
  unfolding set_borel_measurable_def
proof -
  have c: "(\<lambda>u. dra q \<phi> (max u 0) \<omega>) \<in> borel_measurable lborel"
    using dra_cont[OF q] by (simp add: borel_measurable_continuous_onI)
  \<comment> \<open>On the nonnegative axis — all the locale asks about, and all the
      paper's (1.7) constrains — the truncation by \<open>max u 0\<close> is invisible,
      so the continuous representative may be used.  Off it the claim
      would be FALSE: for \<open>u < 0\<close> one has \<open>dras \<dots> u \<omega> = dra q \<phi> u \<omega>\<close>,
      which is not \<open>dra q \<phi> 0 \<omega>\<close>.\<close>
  have eq: "(\<lambda>u. indicat_real {0..} u *\<^sub>R dras q \<phi> T0 u \<omega>)
      = (\<lambda>u. indicat_real {0..} u *\<^sub>R
           (if u \<le> T0 then dra q \<phi> (max u 0) \<omega> else 0))"
  proof
    fix u :: real
    show "indicat_real {0..} u *\<^sub>R dras q \<phi> T0 u \<omega>
        = indicat_real {0..} u *\<^sub>R
            (if u \<le> T0 then dra q \<phi> (max u 0) \<omega> else 0)"
      by (cases "0 \<le> u") (simp_all add: dras_def)
  qed
  show "(\<lambda>u. indicat_real {0..} u *\<^sub>R dras q \<phi> T0 u \<omega>)
      \<in> borel_measurable lborel"
    unfolding eq using c
    by (intro borel_measurable_scaleR measurable_If) auto
qed

lemma set_integral_stopped_split:
  fixes g :: "real \<Rightarrow> real" and T0 t :: real
  assumes T0: "0 \<le> T0"
    and int: "\<And>a b :: real. 0 \<le> a \<Longrightarrow> set_integrable lborel {a..b} g"
  shows "set_lebesgue_integral lborel {0..t} (\<lambda>u. if u \<le> T0 then g u else 0)
       = set_lebesgue_integral lborel {0..min t T0} g"
proof (cases "t \<le> T0")
  case True
  then have m: "min t T0 = t" by simp
  show ?thesis
    unfolding m
    by (rule set_lebesgue_integral_cong) (use True in auto)
next
  case False
  then have m: "min t T0 = T0" and Tt: "T0 \<le> t" by auto
  have un: "{0..t} = {0..T0} \<union> {T0<..t}"
    using T0 Tt by auto
  have dis: "{0..T0} \<inter> {T0<..t} = {}" by auto
  have intA: "set_integrable lborel {0..T0}
      (\<lambda>u. if u \<le> T0 then g u else 0)"
  proof -
    have "(\<lambda>u. indicat_real {0..T0} u *\<^sub>R (if u \<le> T0 then g u else 0))
        = (\<lambda>u. indicat_real {0..T0} u *\<^sub>R g u)"
      by (auto simp: fun_eq_iff indicator_def)
    then show ?thesis
      using int[OF order_refl, of T0]
      unfolding set_integrable_def by simp
  qed
  have intB: "set_integrable lborel {T0<..t}
      (\<lambda>u. if u \<le> T0 then g u else 0)"
  proof -
    have "(\<lambda>u. indicat_real {T0<..t} u *\<^sub>R (if u \<le> T0 then g u else 0))
        = (\<lambda>_. 0)"
      by (auto simp: fun_eq_iff indicator_def)
    then show ?thesis
      unfolding set_integrable_def by simp
  qed
  have "set_lebesgue_integral lborel {0..t} (\<lambda>u. if u \<le> T0 then g u else 0)
      = set_lebesgue_integral lborel {0..T0}
          (\<lambda>u. if u \<le> T0 then g u else 0)
        + set_lebesgue_integral lborel {T0<..t}
            (\<lambda>u. if u \<le> T0 then g u else 0)"
    unfolding un by (rule set_integral_Un[OF dis intA intB])
  moreover have "set_lebesgue_integral lborel {0..T0}
      (\<lambda>u. if u \<le> T0 then g u else 0)
      = set_lebesgue_integral lborel {0..T0} g"
    by (rule set_lebesgue_integral_cong) auto
  moreover have "set_lebesgue_integral lborel {T0<..t}
      (\<lambda>u. if u \<le> T0 then g u else 0) = 0"
  proof -
    have "set_lebesgue_integral lborel {T0<..t}
        (\<lambda>u. if u \<le> T0 then g u else 0)
        = set_lebesgue_integral lborel {T0<..t} (\<lambda>_. 0)"
      by (rule set_lebesgue_integral_cong) auto
    then show ?thesis
      by (simp add: set_lebesgue_integral_def)
  qed
  ultimately show ?thesis unfolding m by simp
qed

lemma dra_diag_drC2:
  fixes i :: 2
  assumes u: "0 \<le> u"
  shows "dra q \<phi> u \<omega> $ i $ i
      = (if i = 1 then (1 - drC2 q \<phi> u \<omega>) / 2
         else (1 + drC2 q \<phi> u \<omega>) / 2)"
proof (cases "i = 1")
  case True
  have "dra q \<phi> u \<omega> $ 1 $ 1 = (sin (drW (drc q u) \<omega> + \<phi>))\<^sup>2"
    by (rule dra_11)
  also have "\<dots> = (1 - cos (2 * (drW (drc q u) \<omega> + \<phi>))) / 2"
    using cos_double_sin[of "drW (drc q u) \<omega> + \<phi>"] by simp
  also have "\<dots> = (1 - drC2 q \<phi> u \<omega>) / 2"
    using u by (simp add: drC2_eq drW_def)
  finally show ?thesis using True by simp
next
  case False
  then have i2: "i = 2" using exhaust_2[of i] by auto
  have "dra q \<phi> u \<omega> $ 2 $ 2 = (cos (drW (drc q u) \<omega> + \<phi>))\<^sup>2"
    by (rule dra_22)
  also have "\<dots> = (1 + cos (2 * (drW (drc q u) \<omega> + \<phi>))) / 2"
    using cos_double_cos[of "drW (drc q u) \<omega> + \<phi>"] by simp
  also have "\<dots> = (1 + drC2 q \<phi> u \<omega>) / 2"
    using u by (simp add: drC2_eq drW_def)
  finally show ?thesis using i2 False by simp
qed

lemma dra_diag_set_integrable:
  fixes i :: 2
  assumes q: "0 < q" and a: "0 \<le> a"
  shows "set_integrable lborel {a..b} (\<lambda>u. dra q \<phi> u \<omega> $ i $ i)"
proof -
  have int1: "set_integrable lborel {a..b}
      (\<lambda>u. (if i = 1 then (1 - drC2 q \<phi> u \<omega>) / 2
            else (1 + drC2 q \<phi> u \<omega>) / 2))"
  proof (cases "i = 1")
    case True
    show ?thesis
      unfolding True
      by (rule borel_integrable_atLeastAtMost')
        (auto intro!: continuous_intros
          continuous_on_subset[OF drC2_cont[OF q] subset_UNIV])
  next
    case False
    show ?thesis
      using False
      by (simp, intro borel_integrable_atLeastAtMost')
        (auto intro!: continuous_intros
          continuous_on_subset[OF drC2_cont[OF q] subset_UNIV])
  qed
  have eq: "(\<lambda>u. indicat_real {a..b} u *\<^sub>R (dra q \<phi> u \<omega> $ i $ i))
      = (\<lambda>u. indicat_real {a..b} u *\<^sub>R
          (if i = 1 then (1 - drC2 q \<phi> u \<omega>) / 2
           else (1 + drC2 q \<phi> u \<omega>) / 2))"
    using a by (auto simp: fun_eq_iff indicator_def dra_diag_drC2)
  show ?thesis
    using int1 unfolding set_integrable_def eq .
qed

lemma coord_Z_drXs_eq:
  fixes i :: 2
  assumes q: "0 < q" and T0: "0 \<le> T0"
  shows "coord_Z (drXs q \<phi> T0) (dras q \<phi> T0) i
       = (\<lambda>t. coord_Z (drX q \<phi>) (dra q \<phi>) i (min t T0))"
proof (intro ext)
  fix t :: real and \<omega> :: "2 \<Rightarrow> real \<Rightarrow> real"
  have "set_lebesgue_integral lborel {0..t}
      (\<lambda>u. dras q \<phi> T0 u \<omega> $ i $ i)
      = set_lebesgue_integral lborel {0..t}
          (\<lambda>u. if u \<le> T0 then dra q \<phi> u \<omega> $ i $ i else 0)"
    by (rule set_lebesgue_integral_cong)
      (auto simp: dras_def zero_vec_def)
  also have "\<dots> = set_lebesgue_integral lborel {0..min t T0}
      (\<lambda>u. dra q \<phi> u \<omega> $ i $ i)"
    by (rule set_integral_stopped_split[OF T0
        dra_diag_set_integrable[OF q]])
  finally show "coord_Z (drXs q \<phi> T0) (dras q \<phi> T0) i t \<omega>
      = coord_Z (drX q \<phi>) (dra q \<phi>) i (min t T0) \<omega>"
    unfolding coord_Z_def drXs_def by simp
qed

theorem martingale_coord_Z_drXs:
  fixes q \<phi> T0 :: real and i :: 2
  assumes q: "0 < q" and T0: "0 \<le> T0"
  shows "martingale (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      0 (coord_Z (drXs q \<phi> T0) (dras q \<phi> T0) i)"
  unfolding coord_Z_drXs_eq[OF q T0]
  by (rule martingale_stopped_deterministic
      [OF martingale_coord_Z_drX[OF q] T0])

subsection \<open>Spectral facts of the tangent projection\<close>

definition drv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (2 \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^2"
  where
  "drv q \<phi> u \<omega> = (\<chi> j. if j = 1 then sin (drW (drc q u) \<omega> + \<phi>)
                       else - cos (drW (drc q u) \<omega> + \<phi>))"

lemma dra_outer:
  "dra q \<phi> u \<omega> $ j $ l = drv q \<phi> u \<omega> $ j * drv q \<phi> u \<omega> $ l"
  by (simp add: dra_def drv_def)

lemma drv_norm: "drv q \<phi> u \<omega> \<bullet> drv q \<phi> u \<omega> = 1"
proof -
  define sn where "sn = sin (drW (drc q u) \<omega> + \<phi>)"
  define c where "c = cos (drW (drc q u) \<omega> + \<phi>)"
  have "drv q \<phi> u \<omega> \<bullet> drv q \<phi> u \<omega> = sn * sn + c * c"
    by (simp add: drv_def inner_vec_def UNIV_2 sn_def c_def)
  also have "\<dots> = 1"
    unfolding sn_def c_def
    by (metis sin_cos_squared_add3 add.commute)
  finally show ?thesis .
qed

lemma dra_mult_vec:
  "dra q \<phi> u \<omega> *v x = (drv q \<phi> u \<omega> \<bullet> x) *\<^sub>R drv q \<phi> u \<omega>"
  by (simp add: matrix_vector_mult_def dra_outer inner_vec_def
      vec_eq_iff UNIV_2 algebra_simps)

lemma dra_sym: "transpose (dra q \<phi> u \<omega>) = dra q \<phi> u \<omega>"
  by (simp add: transpose_def vec_eq_iff dra_outer mult.commute)

lemma dra_psd: "psd (dra q \<phi> u \<omega>)"
proof -
  have "0 \<le> x \<bullet> (dra q \<phi> u \<omega> *v x)" for x
  proof -
    have "x \<bullet> (dra q \<phi> u \<omega> *v x)
        = (drv q \<phi> u \<omega> \<bullet> x) * (drv q \<phi> u \<omega> \<bullet> x)"
      by (simp add: dra_mult_vec inner_commute)
    then show ?thesis by simp
  qed
  then show ?thesis by (simp add: psd_def dra_sym)
qed

lemma dra_eigen_lb: "eigen_lb (dra q \<phi> u \<omega>) 1"
  unfolding eigen_lb_def
proof (intro exI[of _ "span {drv q \<phi> u \<omega>}"] conjI)
  show "subspace (span {drv q \<phi> u \<omega>})" by (rule subspace_span)
  have v0: "drv q \<phi> u \<omega> \<noteq> 0"
    using drv_norm[of q \<phi> u \<omega>] by auto
  have "drv q \<phi> u \<omega> \<in> span {drv q \<phi> u \<omega>}"
    by (rule span_base) simp
  with v0 have ne: "\<not> span {drv q \<phi> u \<omega>} \<subseteq> {0}" by auto
  have "dim (span {drv q \<phi> u \<omega>}) \<noteq> 0"
    using ne dim_eq_0 by blast
  then show "1 \<le> dim (span {drv q \<phi> u \<omega>})" by linarith
  show "\<forall>x \<in> span {drv q \<phi> u \<omega>}.
      x \<bullet> x \<le> x \<bullet> (dra q \<phi> u \<omega> *v x)"
  proof
    fix x assume "x \<in> span {drv q \<phi> u \<omega>}"
    then obtain c where x: "x = c *\<^sub>R drv q \<phi> u \<omega>"
      by (auto simp: span_singleton)
    have "x \<bullet> x = c * c"
      unfolding x by (simp add: drv_norm)
    moreover have "x \<bullet> (dra q \<phi> u \<omega> *v x) = c * c"
      unfolding x by (simp add: dra_mult_vec drv_norm inner_commute)
    ultimately show "x \<bullet> x \<le> x \<bullet> (dra q \<phi> u \<omega> *v x)" by simp
  qed
qed

lemma dra_eigen_ub:
  assumes L: "1 \<le> L"
  shows "eigen_ub (dra q \<phi> u \<omega>) L"
  unfolding eigen_ub_def
proof
  fix x :: "real^2"
  have "x \<bullet> (dra q \<phi> u \<omega> *v x) = (drv q \<phi> u \<omega> \<bullet> x)\<^sup>2"
    by (simp add: dra_mult_vec inner_commute power2_eq_square)
  also have "\<dots> \<le> (drv q \<phi> u \<omega> \<bullet> drv q \<phi> u \<omega>) * (x \<bullet> x)"
    by (rule Cauchy_Schwarz_ineq)
  also have "\<dots> = x \<bullet> x" by (simp add: drv_norm)
  also have "\<dots> \<le> L * (x \<bullet> x)"
    using mult_right_mono[OF L inner_ge_zero] by simp
  finally show "x \<bullet> (dra q \<phi> u \<omega> *v x) \<le> L * (x \<bullet> x)" .
qed

lemma dra_trace: "trace (dra q \<phi> u \<omega>) = 1"
proof -
  have "trace (dra q \<phi> u \<omega>) = drv q \<phi> u \<omega> \<bullet> drv q \<phi> u \<omega>"
    by (simp add: trace_def dra_outer inner_vec_def)
  then show ?thesis by (simp add: drv_norm)
qed

subsection \<open>Geometric facts of the stopped process\<close>

lemma drXs_norm:
  assumes q: "0 < q" and t: "0 \<le> t" and T0: "0 \<le> T0"
  shows "norm (drXs q \<phi> T0 t \<omega>) = drR q (min t T0)"
  unfolding drXs_def
  by (rule drX_norm[OF q]) (use t T0 in auto)

lemma drXs_stopped: "drXs q \<phi> T0 s \<omega> = drXs q \<phi> T0 (min s T0) \<omega>"
proof -
  have "min (min s T0) T0 = min s T0"
    by (metis min.assoc min.idem)
  then show ?thesis by (simp add: drXs_def)
qed

lemma drXs_start_AE:
  fixes q \<phi> T0 :: real
  assumes q: "0 < q" and T0: "0 \<le> T0"
  shows "AE \<omega> in (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure).
      drXs q \<phi> T0 0 \<omega>
      = sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>)"
proof -
  have "AE \<omega> in (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure).
      cbmX (0 :: real^2) 0 \<omega> = bmX (0 :: real^2) 0 \<omega>"
    by (intro cbmX_ae_eq) simp
  moreover have "AE \<omega> in (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure).
      bmX (0 :: real^2) 0 \<omega> = 0"
    by (rule bmX_start)
  ultimately have z: "AE \<omega> in (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure).
      Bcont 0 (\<omega> 1) = 0"
  proof (eventually_elim)
    case (elim \<omega>)
    then have "cbmX (0 :: real^2) 0 \<omega> = 0" by simp
    then have "cbmX (0 :: real^2) 0 \<omega> $ 1 = 0" by simp
    then show ?case by (simp add: cbmX_def)
  qed
  show ?thesis
    using z
  proof (eventually_elim)
    case (elim \<omega>)
    have m0: "min 0 T0 = 0" using T0 by simp
    show ?case
      unfolding drXs_def m0
      by (simp add: drX_def drW_def elim drR_def cong: if_cong)
  qed
qed

lemma drX_cont:
  assumes q: "0 < q"
  shows "continuous_on {0..} (\<lambda>t. drX q \<phi> t \<omega>)"
proof -
  have cW: "continuous_on {0..} (\<lambda>t. Bcont (drc q t) (\<omega> 1))"
    by (rule continuous_on_compose2[OF Bcont_cont drc_cont[OF q]])
      (auto intro: drc_nonneg[OF q])
  have cR: "continuous_on {0..} (\<lambda>t. drR q t)"
    unfolding drR_def by (intro continuous_intros)
  have comp: "continuous_on {0..}
      (\<lambda>t. if i = (1 :: 2) then cos (drW (drc q t) \<omega> + \<phi>)
           else sin (drW (drc q t) \<omega> + \<phi>))" for i
  proof (cases "i = 1")
    case True
    show ?thesis
      unfolding True drW_def by (auto intro!: continuous_intros cW)
  next
    case False
    show ?thesis
      using False unfolding drW_def
      by (auto intro!: continuous_intros cW)
  qed
  show ?thesis
    unfolding drX_def
    by (intro continuous_intros cR comp)
qed

lemma drXs_cont:
  assumes q: "0 < q" and T0: "0 \<le> T0"
  shows "continuous_on {0..} (\<lambda>t. drXs q \<phi> T0 t \<omega>)"
  unfolding drXs_def
  by (rule continuous_on_compose2[OF drX_cont[OF q]])
    (auto intro!: continuous_intros simp: T0)

subsection \<open>The deterministic-radius market is sufficiently volatile\<close>

text \<open>The \<open>stopped_market\<close> packaging (which additionally records that the
  process is stopped, the covariance killed, and the diagonal
  compensators integrable) lives in \<open>Section_2_Usc\<close>, outside this
  theory's import closure; the three extra clauses are provided as
  standalone lemmas below and assembled where both theories are in
  scope.\<close>

theorem deterministic_radius_sufficiently_volatile:
  fixes q \<phi> r L :: real
  assumes q: "0 < q" and L: "1 \<le> L" and qr: "q \<le> r\<^sup>2" and r0: "0 \<le> r"
  shows "sufficiently_volatile_market
      (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>t. natural_filtration bm_paths 0 (cbmX (0 :: real^2)) (drc q t))
      (drXs q \<phi> (r\<^sup>2 - q)) (dras q \<phi> (r\<^sup>2 - q)) 1 L (cball 0 r)
      (sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>))
      (\<lambda>_. r\<^sup>2 - q)"
proof -
  let ?M = "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "\<lambda>t. natural_filtration ?M 0 (cbmX (0 :: real^2)) (drc q t)"
  let ?x0 = "sqrt q *\<^sub>R (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>)"
  define T0 where "T0 = r\<^sup>2 - q"
  have T0: "0 \<le> T0" unfolding T0_def using qr by simp
  have qT0: "q + T0 = r\<^sup>2" unfolding T0_def by simp
  have SVM: "sufficiently_volatile_market ?M ?F (drXs q \<phi> T0)
      (dras q \<phi> T0) 1 L (cball 0 r) ?x0 (\<lambda>_. T0)"
  proof (intro sufficiently_volatile_market.intro
      sufficiently_volatile_market_axioms.intro)
    show "martingale ?M ?F 0 (drXs q \<phi> T0)"
      unfolding drXs_def[abs_def]
      by (rule martingale_drXs[OF q T0])
    show "prob_space ?M" by simp
    show "1 \<le> (1 :: nat)" "(1 :: nat) < CARD(2)" "1 \<le> L"
      using L by simp_all
    show "AE \<omega> in ?M. drXs q \<phi> T0 0 \<omega> = ?x0"
      by (rule drXs_start_AE[OF q T0])
    show "AE \<omega> in ?M. 0 \<le> T0" using T0 by simp
    show "(\<lambda>_. T0) \<in> borel_measurable ?M" by simp
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T0 \<longrightarrow>
        drXs q \<phi> T0 s \<omega> \<in> cball 0 r"
    proof (intro AE_I2 allI impI)
      fix \<omega> :: "2 \<Rightarrow> real \<Rightarrow> real" and s :: real
      assume s: "0 \<le> s" and sT: "s \<le> T0"
      have "norm (drXs q \<phi> T0 s \<omega>) = drR q (min s T0)"
        by (rule drXs_norm[OF q s T0])
      also have "\<dots> \<le> drR q T0"
        unfolding drR_def using s sT
        by (intro real_sqrt_le_mono) simp
      also have "\<dots> = r"
        unfolding drR_def qT0 using r0
        by (simp add: real_sqrt_abs)
      finally show "drXs q \<phi> T0 s \<omega> \<in> cball 0 r"
        by (simp add: mem_cball_0)
    qed
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T0 \<longrightarrow> psd (dras q \<phi> T0 s \<omega>)"
      by (intro AE_I2 allI impI) (simp add: dras_def dra_psd)
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T0 \<longrightarrow>
        eigen_lb (dras q \<phi> T0 s \<omega>) (CARD(2) - 1)"
      by (intro AE_I2 allI impI)
        (simp add: dras_def dra_eigen_lb[unfolded One_nat_def])
    show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T0 \<longrightarrow>
        eigen_ub (dras q \<phi> T0 s \<omega>) L"
      by (intro AE_I2 allI impI) (simp add: dras_def dra_eigen_ub[OF L])
    have trace0: "trace (0 :: real^2^2) = 0"
      by (simp add: trace_def zero_vec_def)
    have trace_dras: "trace (dras q \<phi> T0 s \<omega>)
        = (if s \<le> T0 then 1 else 0)" for s \<omega>
      by (simp add: dras_def dra_trace trace0)
    have trace_int: "set_integrable lborel {0..t}
        (\<lambda>s. trace (dras q \<phi> T0 s \<omega>))" if t: "0 \<le> t" for t \<omega>
    proof -
      have eq: "(\<lambda>s. indicat_real {0..t} s *\<^sub>R trace (dras q \<phi> T0 s \<omega>))
          = (\<lambda>s. indicat_real {0..min t T0} s)"
        using T0 by (auto simp: fun_eq_iff indicator_def trace_dras)
      have "integrable lborel (\<lambda>s. indicat_real {0..min t T0} s)"
        by (auto simp: integrable_indicator_iff emeasure_lborel_Icc_eq)
      then show ?thesis
        unfolding set_integrable_def eq .
    qed
    show "AE \<omega> in ?M. set_borel_measurable lborel {0..} (\<lambda>s. dras q \<phi> T0 s \<omega>)"
      by (intro AE_I2) (rule dras_measurable_time[OF q])
    show "AE \<omega> in ?M. \<forall>t. 0 \<le> t \<longrightarrow> set_integrable lborel {0..t}
        (\<lambda>s. trace (dras q \<phi> T0 s \<omega>))"
      by (intro AE_I2 allI impI) (rule trace_int)
    have sq_const: "(\<lambda>\<omega>. drXs q \<phi> T0 (min t T0) \<omega> \<bullet> drXs q \<phi> T0 (min t T0) \<omega>)
        = (\<lambda>_. q + min t T0)" if t: "0 \<le> t" for t
    proof (intro ext)
      fix \<omega> :: "2 \<Rightarrow> real \<Rightarrow> real"
      have m0: "0 \<le> min t T0" using t T0 by simp
      have mm: "min (min t T0) T0 = min t T0"
        by (metis min.assoc min.idem)
      have "drXs q \<phi> T0 (min t T0) \<omega> \<bullet> drXs q \<phi> T0 (min t T0) \<omega>
          = (norm (drXs q \<phi> T0 (min t T0) \<omega>))\<^sup>2"
        by (simp add: power2_norm_eq_inner)
      also have "\<dots> = (drR q (min t T0))\<^sup>2"
        unfolding drXs_norm[OF q m0 T0] mm ..
      also have "\<dots> = q + min t T0"
        unfolding drR_def using q m0 by simp
      finally show "drXs q \<phi> T0 (min t T0) \<omega> \<bullet> drXs q \<phi> T0 (min t T0) \<omega>
          = q + min t T0" .
    qed
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
        (\<lambda>\<omega>. drXs q \<phi> T0 (min t T0) \<omega> \<bullet> drXs q \<phi> T0 (min t T0) \<omega>)"
      by (subst sq_const) (simp_all add: BMP.integrable_const)
    have comp_const: "(\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t T0}
        (\<lambda>s. trace (dras q \<phi> T0 s \<omega>))) = (\<lambda>_ :: 2 \<Rightarrow> real \<Rightarrow> real. min t T0)"
      if t: "0 \<le> t" for t
    proof (intro ext)
      fix \<omega> :: "2 \<Rightarrow> real \<Rightarrow> real"
      have m0: "0 \<le> min t T0" using t T0 by simp
      have "set_lebesgue_integral lborel {0..min t T0}
          (\<lambda>s. trace (dras q \<phi> T0 s \<omega>))
          = set_lebesgue_integral lborel {0..min t T0} (\<lambda>_. 1 :: real)"
        by (rule set_lebesgue_integral_cong) (auto simp: trace_dras)
      also have "\<dots> = min t T0"
        using m0
        by (subst set_integral_const)
          (auto simp: emeasure_lborel_Icc measure_lborel_Icc)
      finally show "set_lebesgue_integral lborel {0..min t T0}
          (\<lambda>s. trace (dras q \<phi> T0 s \<omega>)) = min t T0" .
    qed
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t T0}
          (\<lambda>s. trace (dras q \<phi> T0 s \<omega>)))"
      by (subst comp_const) (simp_all add: BMP.integrable_const)
    have x0sq: "?x0 \<bullet> ?x0 = q"
    proof -
      have v1: "(\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>)
          \<bullet> (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>) = 1"
        by (simp add: inner_vec_def UNIV_2 sin_cos_squared_add3)
      have "?x0 \<bullet> ?x0 = sqrt q * sqrt q *
          ((\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>)
            \<bullet> (\<chi> j. if j = (1 :: 2) then cos \<phi> else sin \<phi>))"
        by (simp add: algebra_simps)
      also have "\<dots> = sqrt q * sqrt q" unfolding v1 by simp
      also have "\<dots> = q" using q by simp
      finally show ?thesis .
    qed
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        (\<integral>\<omega>. drXs q \<phi> T0 (min t T0) \<omega> \<bullet> drXs q \<phi> T0 (min t T0) \<omega> \<partial>?M)
        - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t T0}
            (\<lambda>s. trace (dras q \<phi> T0 s \<omega>)) \<partial>?M) = ?x0 \<bullet> ?x0"
    proof -
      fix t :: real assume t: "0 \<le> t"
      show "(\<integral>\<omega>. drXs q \<phi> T0 (min t T0) \<omega> \<bullet> drXs q \<phi> T0 (min t T0) \<omega> \<partial>?M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t T0}
              (\<lambda>s. trace (dras q \<phi> T0 s \<omega>)) \<partial>?M) = ?x0 \<bullet> ?x0"
        unfolding sq_const[OF t] comp_const[OF t] x0sq
        by (simp add: BMP.prob_space)
    qed
    show "\<And>i. martingale ?M ?F 0 (coord_Z (drXs q \<phi> T0) (dras q \<phi> T0) i)"
      by (rule martingale_coord_Z_drXs[OF q T0])
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space ?M. T0 \<le> s} \<in> sets (?F s)"
    proof -
      fix s :: real assume "0 \<le> s"
      show "{\<omega> \<in> space ?M. T0 \<le> s} \<in> sets (?F s)"
      proof (cases "T0 \<le> s")
        case True
        have "{\<omega> \<in> space ?M. T0 \<le> s} = space (?F s)"
          using True drG_subalgebra[of "drc q s"]
          by (auto simp: subalgebra_def)
        then show ?thesis
          by (metis sets.top)
      next
        case False
        have "{\<omega> \<in> space ?M. T0 \<le> s} = {}" using False by simp
        then show ?thesis
          by (metis sets.empty_sets)
      qed
    qed
    show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow>
        continuous_on {0..} (\<lambda>s. drXs q \<phi> T0 s \<omega>)"
      by (rule drXs_cont[OF q T0])
  qed
  show ?thesis
    using SVM unfolding T0_def .
qed

lemma dras_killed: "T0 < s \<Longrightarrow> dras q \<phi> T0 s \<omega> = 0"
  by (simp add: dras_def)

lemma dras_diag_time_integrable:
  fixes l :: 2
  assumes q: "0 < q" and T0: "0 \<le> T0" and t: "0 \<le> t"
  shows "set_integrable lborel {0..t} (\<lambda>s. dras q \<phi> T0 s \<omega> $ l $ l)"
proof -
  have eq: "(\<lambda>s. indicat_real {0..t} s *\<^sub>R (dras q \<phi> T0 s \<omega> $ l $ l))
      = (\<lambda>s. indicat_real {0..min t T0} s *\<^sub>R (dra q \<phi> s \<omega> $ l $ l))"
    using T0 by (auto simp: fun_eq_iff indicator_def dras_def
        zero_vec_def)
  show ?thesis
    using dra_diag_set_integrable[OF q order_refl, of "min t T0" \<phi> \<omega> l]
    unfolding set_integrable_def eq .
qed

end
