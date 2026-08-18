section \<open>The vector Brownian motion is a martingale, and so is its compensated square\<close>

(*<*)
theory Vector_Brownian_Martingales
  imports Product_Brownian_Motion
begin

(*>*)

section \<open>Coordinate means and vector integrability\<close>

lemma bm_coordinate_mean:
  assumes u: "0 \<le> u"
  shows bm_coordinate_mean_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i u)"
    and bm_coordinate_mean_integral:
    "(\<integral>\<omega>. \<omega> i u \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  have m: "(\<lambda>\<omega>. \<omega> i u) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_bm_coordinate) simp
  have idm: "(\<lambda>y :: real. y) \<in> borel_measurable borel"
    by (rule measurable_ident_sets) simp
  have "integrable (distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i u)) (\<lambda>y. y)"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_measure_mean_integrable)
  then show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i u)"
    by (rule integrable_distr[OF m])
  have "(\<integral>\<omega>. \<omega> i u \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>y. y \<partial>distr bm_paths borel (\<lambda>\<omega>. \<omega> i u))"
    by (rule integral_distr[OF m idm, symmetric])
  also have "\<dots> = 0"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_measure_mean_integral)
  finally show "(\<integral>\<omega>. \<omega> i u
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0" .
qed

text \<open>\<open>integrable_vec_components\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

lemma bmX_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows "integrable bm_paths (bmX x0 u)"
proof -
  have eq: "bmX x0 u = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<chi> i. x0 $ i + \<omega> i u)"
    by (simp add: bmX_def fun_eq_iff vec_eq_iff)
  show ?thesis
    unfolding eq
    by (intro integrable_vec_components Bochner_Integration.integrable_add
        BMP.integrable_const bm_coordinate_mean_integrable[OF u])
qed

lemma bm_increment_component:
  assumes s: "0 \<le> s" and t: "0 \<le> t"
  shows bm_increment_component_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s)"
    and bm_increment_component_integral:
    "(\<integral>\<omega>. \<omega> i t - \<omega> i s
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s)"
    by (intro Bochner_Integration.integrable_diff
        bm_coordinate_mean_integrable s t)
  show "(\<integral>\<omega>. \<omega> i t - \<omega> i s
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
    by (subst Bochner_Integration.integral_diff)
      (simp_all add: bm_coordinate_mean_integrable
        bm_coordinate_mean_integral s t)
qed

section \<open>The increment has zero conditional expectation\<close>

lemma bm_indicator_increment_indep_var:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "BMP.indep_var borel (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  let ?V = "vimage_algebra (space ?M) ?D borel"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have base: "BMP.indep_set (sets ?F) (sets ?V)"
    by (rule bm_filtration_increment_indep[OF s st])
  have ind_meas_F: "(indicator A :: _ \<Rightarrow> real) \<in> borel_measurable ?F"
    by (rule borel_measurable_indicator[OF A])
  have L: "sigma_sets (space ?M)
      {(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets ?F"
  proof -
    have gen: "{(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?F"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have "(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?F \<in> sets ?F"
        by (rule measurable_sets[OF ind_meas_F B])
      then show "(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M \<in> sets ?F"
        by simp
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
    show "(indicator A :: _ \<Rightarrow> real) \<in> borel_measurable ?M"
      by (rule borel_measurable_indicator[OF A_M])
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
        \<in> borel_measurable ?M"
      using s st
      by (intro borel_measurable_diff measurable_bm_coordinate) auto
    have "BMP.indep_sets (case_bool (sets ?F) (sets ?V)) UNIV"
      using base unfolding BMP.indep_set_def .
    then have "BMP.indep_sets (case_bool
        (sigma_sets (space ?M)
          {(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})) UNIV"
      by (rule BMP.indep_sets_mono_sets)
        (auto split: bool.split simp: L R)
    then show "BMP.indep_set
        (sigma_sets (space ?M)
          {(indicator A :: _ \<Rightarrow> real) -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})"
      unfolding BMP.indep_set_def .
  qed
qed

lemma bmX_increment_set_integral_zero:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>)
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof (cases "s = t")
  case True
  then show ?thesis by simp
next
  case False
  with st have st': "s < t" by simp
  have t0: "0 \<le> t" using s st by simp
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have D_int: "integrable ?M ?D"
    by (intro Bochner_Integration.integrable_diff bmX_integrable s t0)
  have setD_int: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R ?D \<omega>)"
    by (rule integrable_mult_indicator[OF A_M D_int])
  have indA_int: "integrable ?M (indicator A :: _ \<Rightarrow> real)"
  proof (rule BMP.integrable_const_bound[where B = 1])
    show "AE \<omega> in ?M. norm (indicator A \<omega> :: real) \<le> 1"
      by (intro AE_I2) (simp add: indicator_def)
    show "(indicator A :: _ \<Rightarrow> real) \<in> borel_measurable ?M"
      by (rule borel_measurable_indicator[OF A_M])
  qed
  have comp0: "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R ?D \<omega> \<partial>?M) $ i = 0" for i
  proof -
    have inc_int: "integrable ?M
        (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
      by (rule bm_increment_component_integrable[OF s t0])
    have "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R ?D \<omega> \<partial>?M) $ i
        = (\<integral>\<omega>. (indicator A \<omega> *\<^sub>R ?D \<omega>) $ i \<partial>?M)"
      by (rule integral_bounded_linear
          [OF bounded_linear_vec_nth setD_int, symmetric])
    also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (\<omega> i t - \<omega> i s) \<partial>?M)"
      by (intro Bochner_Integration.integral_cong refl)
        (simp add: bmX_def)
    also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> \<partial>?M)
        * (\<integral>\<omega>. \<omega> i t - \<omega> i s \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral
          [OF bm_indicator_increment_indep_var[OF s st' A]
            indA_int inc_int])
    also have "\<dots> = 0"
      by (simp add: bm_increment_component_integral[OF s t0])
    finally show ?thesis .
  qed
  show ?thesis
    using comp0 by (simp add: vec_eq_iff)
qed

lemma bmX_has_cond_exp:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "has_cond_exp (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0) s) (bmX x0 t) (bmX x0 s)"
proof (rule has_cond_expI')
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  have t0: "0 \<le> t" using s st by simp
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  show "integrable ?M (bmX x0 t)"
    by (rule bmX_integrable[OF t0])
  show "integrable ?M (bmX x0 s)"
    by (rule bmX_integrable[OF s])
  show "bmX x0 s \<in> borel_measurable ?F"
    by (rule adapted_process.adapted
        [OF SP.adapted_process_natural_filtration s])
  fix A assume A: "A \<in> sets ?F"
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have int_s: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega>)"
    by (rule integrable_mult_indicator[OF A_M bmX_integrable[OF s]])
  have int_D: "integrable ?M
      (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>))"
    by (intro integrable_mult_indicator[OF A_M]
        Bochner_Integration.integrable_diff bmX_integrable s t0)
  have "(\<integral>\<omega> \<in> A. bmX x0 t \<omega> \<partial>?M)
      = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 t \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def ..
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega>
      + indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>) \<partial>?M)"
    by (intro Bochner_Integration.integral_cong refl)
      (simp add: scaleR_add_right scaleR_diff_right)
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega> \<partial>?M)
      + (\<integral>\<omega>. indicator A \<omega> *\<^sub>R (bmX x0 t \<omega> - bmX x0 s \<omega>) \<partial>?M)"
    by (rule Bochner_Integration.integral_add[OF int_s int_D])
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> *\<^sub>R bmX x0 s \<omega> \<partial>?M)"
    by (simp add: bmX_increment_set_integral_zero[OF s st A])
  also have "\<dots> = (\<integral>\<omega> \<in> A. bmX x0 s \<omega> \<partial>?M)"
    unfolding set_lebesgue_integral_def ..
  finally show "(\<integral>\<omega> \<in> A. bmX x0 t \<omega> \<partial>?M)
      = (\<integral>\<omega> \<in> A. bmX x0 s \<omega> \<partial>?M)" .
qed

section \<open>The market is a martingale\<close>

theorem martingale_bmX:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0 (bmX x0)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M (?F i)" for i
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro
        fm SP.subalgebra_natural_filtration)
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?F 0"
      by (intro sigma_finite_filtered_measure.intro
          sigma_finite_filtered_measure_axioms.intro
          SP.filtered_measure_natural_filtration sfs)
    show "adapted_process ?M ?F 0 (bmX x0)"
      by (rule SP.adapted_process_natural_filtration)
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (bmX x0 i)"
      by (rule bmX_integrable)
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    interpret S: sigma_finite_subalgebra ?M "?F i"
      by (rule sfs)
    show "AE \<xi> in ?M. bmX x0 i \<xi> = cond_exp ?M (?F i) (bmX x0 j) \<xi>"
      by (rule S.has_cond_exp_charact(2)
          [OF bmX_has_cond_exp[OF ij], THEN AE_symmetric])
  qed
qed

section \<open>The Brownian market is sufficiently volatile\<close>

text \<open>The martingale property \<open>martingale_bmX\<close> above, together with the
  martingale-problem identity \<open>dynkin_quadratic\<close> proved in the next
  section, assembles into an instance of \<open>sufficiently_volatile_market\<close>
  from \<open>Volatile_Market\<close>; the concrete instantiation, for the
  continuous modification of the market, is carried out in
  \<open>Continuous_Brownian_Motion\<close>.\<close>

section \<open>Ito's formula for the square: the compensated square is a martingale\<close>

text \<open>The martingale-problem identity used above is the \<^emph>\<open>expectation\<close>
  form of Ito's formula for the test function \<open>|x|\<^sup>2\<close>.  Its process form,

    \<open>Z t = |B t|\<^sup>2 - int_0^t tr(mat 1) ds\<close> is a martingale,

  is proved in this section.  It is what the locales of \<open>Ito\_Market\<close> take as
  their hypothesis, so it shows that the martingale problem in process form
  is inhabited as well.  Everything rests on the independence of the
  increment from the past, generalised here from indicators of past events
  to arbitrary past-measurable factors.\<close>

lemma bm_meas_increment_indep_var:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
    and g_meas: "g \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "BMP.indep_var borel (g :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  let ?V = "vimage_algebra (space ?M) ?D borel"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have g_M: "g \<in> borel_measurable ?M"
    by (rule measurable_from_subalg[OF subalg g_meas])
  have base: "BMP.indep_set (sets ?F) (sets ?V)"
    by (rule bm_filtration_increment_indep[OF s st])
  have L: "sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets ?F"
  proof -
    have gen: "{g -` B \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?F"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have "g -` B \<inter> space ?F \<in> sets ?F"
        by (rule measurable_sets[OF g_meas B])
      then show "g -` B \<inter> space ?M \<in> sets ?F"
        using subalg by (simp add: subalgebra_def)
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
    show "g \<in> borel_measurable ?M"
      by (rule g_M)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
        \<in> borel_measurable ?M"
      using s st
      by (intro borel_measurable_diff measurable_bm_coordinate) auto
    have "BMP.indep_sets (case_bool (sets ?F) (sets ?V)) UNIV"
      using base unfolding BMP.indep_set_def .
    then have "BMP.indep_sets (case_bool
        (sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})) UNIV"
      by (rule BMP.indep_sets_mono_sets)
        (auto split: bool.split simp: L R)
    then show "BMP.indep_set
        (sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s) -` B \<inter> space ?M
            |B. B \<in> sets borel})"
      unfolding BMP.indep_set_def .
  qed
qed

lemma bm_meas_increment_product:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and g_meas: "g \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
    and g_int: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) g"
  shows bm_meas_increment_product_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s))"
    and bm_meas_increment_product_zero:
    "(\<integral>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s)
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  have t0: "0 \<le> t" using s st by simp
  show "integrable ?M (\<lambda>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s))"
  proof (cases "s = t")
    case True
    then show ?thesis by simp
  next
    case False
    with st have st': "s < t" by simp
    show ?thesis
      by (rule BMP.indep_var_integrable
          [OF bm_meas_increment_indep_var[OF s st' g_meas] g_int
            bm_increment_component_integrable[OF s t0]])
  qed
  show "(\<integral>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s) \<partial>?M) = 0"
  proof (cases "s = t")
    case True
    then show ?thesis by simp
  next
    case False
    with st have st': "s < t" by simp
    have "(\<integral>\<omega>. g \<omega> * (\<omega> i t - \<omega> i s) \<partial>?M)
        = (\<integral>\<omega>. g \<omega> \<partial>?M) * (\<integral>\<omega>. \<omega> i t - \<omega> i s \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral
          [OF bm_meas_increment_indep_var[OF s st' g_meas] g_int
            bm_increment_component_integrable[OF s t0]])
    also have "\<dots> = 0"
      by (simp add: bm_increment_component_integral[OF s t0])
    finally show ?thesis .
  qed
qed

lemma bm_coordinate_measurable_F:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s"
  shows "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable
    (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (bmX x0) s)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  interpret AP: adapted_process ?M "natural_filtration ?M 0 (bmX x0)" 0
    "bmX x0"
    by (rule SP.adapted_process_natural_filtration)
  have X_F: "bmX x0 s \<in> borel_measurable ?F"
    by (intro AP.adaptedD s order.refl)
  have nth_meas: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel"
  proof -
    have "(\<lambda>v :: real^'n. v $ i) = (\<lambda>v. inner v (axis i 1))"
      by (simp add: fun_eq_iff cart_eq_inner_axis)
    then show ?thesis by simp
  qed
  have comp_F: "(\<lambda>\<omega>. bmX x0 s \<omega> $ i) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF X_F nth_meas])
  have eq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s)
      = (\<lambda>\<omega>. bmX x0 s \<omega> $ i - x0 $ i)"
    by (simp add: fun_eq_iff bmX_def)
  show ?thesis
    unfolding eq using comp_F by simp
qed

lemma bm_increment_sq:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows bm_increment_sq_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2)"
    and bm_increment_sq_integral:
    "(\<integral>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = t - s"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  have t0: "0 \<le> t" using s st by simp
  have sq_t: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t)\<^sup>2)"
    using bm_coordinate_sq_integrable[OF t0, of 0 i] by simp
  have sq_s: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i s)\<^sup>2)"
    using bm_coordinate_sq_integrable[OF s, of 0 i] by simp
  have sq_t_val: "(\<integral>\<omega>. (\<omega> i t)\<^sup>2 \<partial>?M) = t"
    using bm_coordinate_sq_integral[OF t0, of 0 i] by simp
  have sq_s_val: "(\<integral>\<omega>. (\<omega> i s)\<^sup>2 \<partial>?M) = s"
    using bm_coordinate_sq_integral[OF s, of 0 i] by simp
  have cross_int: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s * (\<omega> i t - \<omega> i s))"
    by (rule bm_meas_increment_product_integrable
        [OF s st bm_coordinate_measurable_F[OF s]
          bm_coordinate_mean_integrable[OF s]])
  have cross_val: "(\<integral>\<omega>. \<omega> i s * (\<omega> i t - \<omega> i s) \<partial>?M) = 0"
    by (rule bm_meas_increment_product_zero
        [OF s st bm_coordinate_measurable_F[OF s]
          bm_coordinate_mean_integrable[OF s]])
  have decomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t - \<omega> i s)\<^sup>2)
      = (\<lambda>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2
            - 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)))"
    by (simp add: fun_eq_iff power2_eq_square algebra_simps)
  have int': "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2 - 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)))"
    by (intro Bochner_Integration.integrable_diff sq_t sq_s
        integrable_mult_right cross_int)
  show "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t - \<omega> i s)\<^sup>2)"
    unfolding decomp by (rule int')
  have step1: "(\<integral>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2 \<partial>?M)
      = (\<integral>\<omega>. (\<omega> i t)\<^sup>2 \<partial>?M) - (\<integral>\<omega>. (\<omega> i s)\<^sup>2 \<partial>?M)"
    by (intro Bochner_Integration.integral_diff sq_t sq_s)
  have step2: "(\<integral>\<omega>. 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)) \<partial>?M) = 0"
    using cross_int cross_val by simp
  have "(\<integral>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2 \<partial>?M)
      = (\<integral>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2
            - 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)) \<partial>?M)"
    unfolding decomp ..
  also have "\<dots> = (\<integral>\<omega>. (\<omega> i t)\<^sup>2 - (\<omega> i s)\<^sup>2 \<partial>?M)
      - (\<integral>\<omega>. 2 * (\<omega> i s * (\<omega> i t - \<omega> i s)) \<partial>?M)"
    by (intro Bochner_Integration.integral_diff
        Bochner_Integration.integrable_diff sq_t sq_s
        integrable_mult_right cross_int)
  also have "\<dots> = t - s"
    using step1 step2 by (simp add: sq_t_val sq_s_val)
  finally show "(\<integral>\<omega>. (\<omega> i t - \<omega> i s)\<^sup>2 \<partial>?M) = t - s" .
qed

section \<open>The compensated square has constant set integrals\<close>

lemma bm_indicator_coord_sq_integrable:
  assumes u: "0 \<le> u" and A: "A \<in> sets (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. indicator A \<omega> * (c + \<omega> i u)\<^sup>2)"
proof -
  have "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (c + \<omega> i u)\<^sup>2)"
    by (intro integrable_mult_indicator A bm_coordinate_sq_integrable[OF u])
  then show ?thesis by simp
qed

lemma bm_indicator_int:
  assumes A: "A \<in> sets (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)"
  shows bm_indicator_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
    and bm_indicator_integral:
    "(\<integral>\<omega>. indicator A \<omega>
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = BMP.prob A"
proof -
  show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
  proof (rule BMP.integrable_const_bound[where B = 1])
    show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        norm (indicator A \<omega> :: real) \<le> 1"
      by (intro AE_I2) (simp add: indicator_def)
    show "(indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule borel_measurable_indicator[OF A])
  qed
  have ins: "A \<inter> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) = A"
    using A sets.sets_into_space by blast
  show "(\<integral>\<omega>. indicator A \<omega>
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = BMP.prob A"
    using ins by simp
qed

text \<open>One coordinate at a time: the conditional second moment increases by
  exactly the elapsed time.\<close>

lemma bm_set_integral_coord_sq_eq:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
        + (t - s) * BMP.prob A"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?d = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s"
  let ?g = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
    indicator A \<omega> * (x0 $ i + \<omega> i s)"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have ind_F: "(indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
      \<in> borel_measurable ?F"
    by (rule borel_measurable_indicator[OF A])
  have ind_int: "integrable ?M (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
    by (rule bm_indicator_integrable[OF A_M])
  have ind_val: "(\<integral>\<omega>. indicator A \<omega> \<partial>?M) = BMP.prob A"
    by (rule bm_indicator_integral[OF A_M])
  have ins: "A \<inter> space ?M = A"
    using A_M sets.sets_into_space by blast
  have g_F: "?g \<in> borel_measurable ?F"
  proof -
    have c1: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i s) \<in> borel_measurable ?F"
      by (rule bm_coordinate_measurable_F[OF s])
    show ?thesis
      by (intro borel_measurable_times ind_F borel_measurable_add
          borel_measurable_const c1)
  qed
  have coord_int: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. x0 $ i + \<omega> i s)"
    by (intro Bochner_Integration.integrable_add BMP.integrable_const
        bm_coordinate_mean_integrable[OF s])
  have g_int: "integrable ?M ?g"
  proof -
    have "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (x0 $ i + \<omega> i s))"
      by (intro integrable_mult_indicator A_M coord_int)
    then show ?thesis by simp
  qed
  have cross_int: "integrable ?M (\<lambda>\<omega>. ?g \<omega> * ?d \<omega>)"
    by (rule bm_meas_increment_product_integrable[OF s st g_F g_int])
  have cross_val: "(\<integral>\<omega>. ?g \<omega> * ?d \<omega> \<partial>?M) = 0"
    by (rule bm_meas_increment_product_zero[OF s st g_F g_int])
  have inc_sq_int: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (?d \<omega>)\<^sup>2)"
    by (rule bm_increment_sq_integrable[OF s st])
  have sq_int: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2)"
  proof -
    have "integrable ?M (\<lambda>\<omega>. indicator A \<omega> *\<^sub>R (?d \<omega>)\<^sup>2)"
      by (intro integrable_mult_indicator A_M inc_sq_int)
    then show ?thesis by simp
  qed
  have sq_val: "(\<integral>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)
      = BMP.prob A * (t - s)"
  proof (cases "s = t")
    case True
    then show ?thesis by simp
  next
    case False
    with st have st': "s < t" by simp
    have base: "BMP.indep_var borel
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real) borel ?d"
      by (rule bm_meas_increment_indep_var[OF s st' ind_F])
    have "BMP.indep_var borel
        ((\<lambda>x :: real. x) \<circ> (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real))
        borel ((\<lambda>x :: real. x\<^sup>2) \<circ> ?d)"
      by (rule BMP.indep_var_compose[OF base]) simp_all
    then have indep2: "BMP.indep_var borel
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
        borel (\<lambda>\<omega>. (?d \<omega>)\<^sup>2)"
      by (simp add: comp_def)
    have "(\<integral>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)
        = (\<integral>\<omega>. indicator A \<omega> \<partial>?M) * (\<integral>\<omega>. (?d \<omega>)\<^sup>2 \<partial>?M)"
      by (rule BMP.indep_var_lebesgue_integral[OF indep2 ind_int inc_sq_int])
    also have "\<dots> = BMP.prob A * (t - s)"
      by (simp add: ind_val ins bm_increment_sq_integral[OF s st])
    finally show ?thesis .
  qed
  have decomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2)
      = (\<lambda>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
          + 2 * (?g \<omega> * ?d \<omega>) + indicator A \<omega> * (?d \<omega>)\<^sup>2)"
    by (simp add: fun_eq_iff power2_eq_square algebra_simps)
  have int_s: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2)"
    by (rule bm_indicator_coord_sq_integrable[OF s A_M])
  have inner_split: "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
        + 2 * (?g \<omega> * ?d \<omega>) \<partial>?M)
      = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M)
        + (\<integral>\<omega>. 2 * (?g \<omega> * ?d \<omega>) \<partial>?M)"
    by (intro Bochner_Integration.integral_add int_s integrable_mult_right
        cross_int)
  have cross2_val: "(\<integral>\<omega>. 2 * (?g \<omega> * ?d \<omega>) \<partial>?M) = 0"
    using cross_int cross_val by simp
  have "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2 \<partial>?M)
      = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
          + 2 * (?g \<omega> * ?d \<omega>) + indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)"
    unfolding decomp ..
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2
          + 2 * (?g \<omega> * ?d \<omega>) \<partial>?M)
      + (\<integral>\<omega>. indicator A \<omega> * (?d \<omega>)\<^sup>2 \<partial>?M)"
    by (intro Bochner_Integration.integral_add
        Bochner_Integration.integrable_add int_s integrable_mult_right
        cross_int sq_int)
  also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M)
      + (t - s) * BMP.prob A"
    using inner_split cross2_val sq_val by (simp add: mult_ac)
  finally show ?thesis .
qed

text \<open>Summing the coordinates: the compensated square has equal set
  integrals over events of the past.\<close>

lemma bm_indicator_sq_sum:
  fixes x0 :: "real^'n::finite"
  shows "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>))
    = (\<lambda>\<omega>. \<Sum>i\<in>(UNIV :: 'n set). indicator A \<omega> * (x0 $ i + \<omega> i u)\<^sup>2)"
  by (simp add: fun_eq_iff inner_vec_def bmX_def power2_eq_square
      sum_distrib_left)

lemma bm_indicator_sq_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
    and A: "A \<in> sets (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>))"
  unfolding bm_indicator_sq_sum
  by (intro Bochner_Integration.integrable_sum
      bm_indicator_coord_sq_integrable[OF u A])

lemma bm_set_integral_sq_eq:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicator A \<omega> * (bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>)
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> \<bullet> bmX x0 s \<omega>)
        \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
        + real CARD('n) * (t - s) * BMP.prob A"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have A_M: "A \<in> sets ?M"
    using A SP.subalgebra_natural_filtration by (auto simp: subalgebra_def)
  have t0: "0 \<le> t" using s st by simp
  have "(\<integral>\<omega>. indicator A \<omega> * (bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>) \<partial>?M)
      = (\<Sum>i\<in>(UNIV :: 'n set).
          (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i t)\<^sup>2 \<partial>?M))"
    unfolding bm_indicator_sq_sum
    by (intro Bochner_Integration.integral_sum
        bm_indicator_coord_sq_integrable[OF t0 A_M])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M)
        + (t - s) * BMP.prob A)"
    by (intro sum.cong refl bm_set_integral_coord_sq_eq[OF s st A])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M))
      + real CARD('n) * ((t - s) * BMP.prob A)"
    by (simp add: sum.distrib)
  also have "(\<Sum>i\<in>(UNIV :: 'n set).
      (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i s)\<^sup>2 \<partial>?M))
      = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> \<bullet> bmX x0 s \<omega>) \<partial>?M)"
    unfolding bm_indicator_sq_sum
    by (intro Bochner_Integration.integral_sum[symmetric]
        bm_indicator_coord_sq_integrable[OF s A_M])
  finally show ?thesis
    by (simp add: mult_ac)
qed

section \<open>The compensated square is a martingale\<close>

theorem martingale_bm_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0
    (\<lambda>t \<omega>. bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  let ?Z = "\<lambda>t \<omega>. bmX x0 t \<omega> \<bullet> bmX x0 t \<omega>
    - set_lebesgue_integral lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  interpret AP: adapted_process ?M ?F 0 "bmX x0"
    by (rule SP.adapted_process_natural_filtration)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M (?F i)" for i
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro
        fm SP.subalgebra_natural_filtration)
  have sff: "sigma_finite_filtered_measure ?M ?F 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro
        SP.filtered_measure_natural_filtration sfs)
  interpret SFF: sigma_finite_filtered_measure ?M ?F 0
    by (rule sff)
  have Zmeas: "?Z u \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
  proof -
    have X_F: "bmX x0 u \<in> borel_measurable (?F u)"
      by (intro AP.adaptedD u order.refl)
    have "(\<lambda>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>) \<in> borel_measurable (?F u)"
      by (intro borel_measurable_inner X_F)
    then show ?thesis
      by (intro borel_measurable_diff borel_measurable_const)
  qed
  have Zint: "integrable ?M (?Z u)" if u: "0 \<le> u" for u
    by (intro Bochner_Integration.integrable_diff bmX_sq_integrable[OF u]
        BMP.integrable_const)
  have ap: "adapted_process ?M ?F 0 ?Z"
    by (intro adapted_process.intro[OF SP.filtered_measure_natural_filtration]
        adapted_process_axioms.intro Zmeas)
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq[OF ap])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (?Z i)"
      by (rule Zint)
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (?F u)"
    have v: "0 \<le> v" using u uv by simp
    have A_M: "A \<in> sets ?M"
      using A SP.subalgebra_natural_filtration by (auto simp: subalgebra_def)
    have ind_int: "integrable ?M
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
      by (rule bm_indicator_integrable[OF A_M])
    have ind_val: "(\<integral>\<omega>. indicator A \<omega> \<partial>?M) = BMP.prob A"
      by (rule bm_indicator_integral[OF A_M])
    have ins: "A \<inter> space ?M = A"
      using A_M sets.sets_into_space by blast
    have cst: "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M) = BMP.prob A * c" for c :: real
    proof -
      have "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M)
          = (\<integral>\<omega>. indicator A \<omega> \<partial>?M) * c"
        using ind_int by simp
      then show ?thesis
        by (simp add: ind_val ins)
    qed
    have split: "set_lebesgue_integral ?M A (?Z w)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * w)" if w: "0 \<le> w" for w
    proof -
      have comp: "set_lebesgue_integral lborel {0..w}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)) = real CARD('n) * w"
        by (rule bm_compensator_const[OF w])
      have comp': "(LBINT x. indicat_real {0..w} x
            *\<^sub>R trace (mat 1 :: real^'n^'n)) = real CARD('n) * w"
        using comp unfolding set_lebesgue_integral_def .
      have i1: "integrable ?M
          (\<lambda>\<omega>. indicator A \<omega> * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>))"
        by (rule bm_indicator_sq_integrable[OF w A_M])
      have i2: "integrable ?M
          (\<lambda>\<omega>. indicator A \<omega> * (real CARD('n) * w))"
        by (intro integrable_mult_left ind_int)
      have "set_lebesgue_integral ?M A (?Z w)
          = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>)
              - indicator A \<omega> * (real CARD('n) * w) \<partial>?M)"
        unfolding set_lebesgue_integral_def
        by (intro Bochner_Integration.integral_cong refl)
          (simp add: comp' trace_I w algebra_simps)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega>
            * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>) \<partial>?M)
          - (\<integral>\<omega>. indicator A \<omega> * (real CARD('n) * w) \<partial>?M)"
        by (intro Bochner_Integration.integral_diff i1 i2)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega>
            * (bmX x0 w \<omega> \<bullet> bmX x0 w \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * w)"
        by (simp add: cst ins)
      finally show ?thesis .
    qed
    have vsplit: "set_lebesgue_integral ?M A (?Z v)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 v \<omega> \<bullet> bmX x0 v \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * v)"
      by (rule split[OF v])
    have usplit: "set_lebesgue_integral ?M A (?Z u)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>) \<partial>?M)
          - BMP.prob A * (real CARD('n) * u)"
      by (rule split[OF u])
    have vu: "(\<integral>\<omega>. indicator A \<omega> * (bmX x0 v \<omega> \<bullet> bmX x0 v \<omega>) \<partial>?M)
        = (\<integral>\<omega>. indicator A \<omega> * (bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>) \<partial>?M)
          + real CARD('n) * (v - u) * BMP.prob A"
      by (rule bm_set_integral_sq_eq[OF u uv A])
    show "set_lebesgue_integral ?M A (?Z u)
        = set_lebesgue_integral ?M A (?Z v)"
      unfolding usplit vsplit vu by (simp add: algebra_simps)
  qed
qed

text \<open>Consequently the process form of the martingale problem is
  inhabited: with \<open>acov = mat 1\<close> the process of \<open>ito_Z\<close> is exactly \<open>?Z\<close>
  above, so \<open>martingale_bm_square\<close> discharges the hypothesis
  \<open>Z_martingale\<close> of \<open>ito_const_horizon_market\<close>.  The instantiation
  itself belongs to \<open>Ito\_Market,\<close> which imports this theory's ambient
  definitions.\<close>

section \<open>The compensated square of a single coordinate is a martingale\<close>

text \<open>\<open>bm_compensator_coord\<close> is in \<open>Product_Brownian_Motion\<close>.\<close>


theorem martingale_bm_coord_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0
    (\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  let ?Z = "\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2
    - set_lebesgue_integral lborel {0..t}
        (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  interpret AP: adapted_process ?M ?F 0 "bmX x0"
    by (rule SP.adapted_process_natural_filtration)
  have fm: "finite_measure ?M"
    by (rule finite_measureI) (simp add: BMP.emeasure_space_1)
  have sfs: "sigma_finite_subalgebra ?M (?F j)" for j
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro
        fm SP.subalgebra_natural_filtration)
  have sff: "sigma_finite_filtered_measure ?M ?F 0"
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro
        SP.filtered_measure_natural_filtration sfs)
  interpret SFF: sigma_finite_filtered_measure ?M ?F 0
    by (rule sff)
  have coord: "bmX x0 w \<omega> $ i = x0 $ i + \<omega> i w" for w \<omega>
    by (simp add: bmX_def)
  have Zmeas: "?Z u \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
  proof -
    have X_F: "bmX x0 u \<in> borel_measurable (?F u)"
      by (intro AP.adaptedD u order.refl)
    have cnt: "continuous_on UNIV (\<lambda>x :: real^'n. x $ i)"
      by (intro linear_continuous_on bounded_linear_vec_nth)
    have prj: "(\<lambda>x :: real^'n. x $ i) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI[OF cnt])
    have "(\<lambda>\<omega>. bmX x0 u \<omega> $ i) \<in> borel_measurable (?F u)"
      by (rule measurable_compose[OF X_F prj])
    hence "(\<lambda>\<omega>. (bmX x0 u \<omega> $ i)\<^sup>2) \<in> borel_measurable (?F u)"
      by (intro borel_measurable_power)
    then show ?thesis
      by (intro borel_measurable_diff borel_measurable_const)
  qed
  have Zint: "integrable ?M (?Z u)" if u: "0 \<le> u" for u
    unfolding coord
    by (intro Bochner_Integration.integrable_diff
        bm_coordinate_sq_integrable[OF u] BMP.integrable_const)
  have ap: "adapted_process ?M ?F 0 ?Z"
    by (intro adapted_process.intro[OF SP.filtered_measure_natural_filtration]
        adapted_process_axioms.intro Zmeas)
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq[OF ap])
    show "\<And>j. 0 \<le> j \<Longrightarrow> integrable ?M (?Z j)"
      by (rule Zint)
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (?F u)"
    have v: "0 \<le> v" using u uv by simp
    have A_M: "A \<in> sets ?M"
      using A SP.subalgebra_natural_filtration by (auto simp: subalgebra_def)
    have ind_int: "integrable ?M
        (indicator A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)"
      by (rule bm_indicator_integrable[OF A_M])
    have ind_val: "(\<integral>\<omega>. indicator A \<omega> \<partial>?M) = BMP.prob A"
      by (rule bm_indicator_integral[OF A_M])
    have ins: "A \<inter> space ?M = A"
      using A_M sets.sets_into_space by blast
    have cst: "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M) = BMP.prob A * c" for c :: real
    proof -
      have "(\<integral>\<omega>. indicator A \<omega> * c \<partial>?M) = (\<integral>\<omega>. indicator A \<omega> \<partial>?M) * c"
        using ind_int by simp
      then show ?thesis by (simp add: ind_val ins)
    qed
    have split: "set_lebesgue_integral ?M A (?Z w)
        = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2 \<partial>?M) - BMP.prob A * w"
      if w: "0 \<le> w" for w
    proof -
      have comp: "set_lebesgue_integral lborel {0..w}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i) = w"
        by (rule bm_compensator_coord[OF w])
      have i1: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2)"
        by (rule bm_indicator_coord_sq_integrable[OF w A_M])
      have i2: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * w)"
        by (intro integrable_mult_left ind_int)
      have "set_lebesgue_integral ?M A (?Z w)
          = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2
              - indicator A \<omega> * w \<partial>?M)"
        unfolding set_lebesgue_integral_def
        by (intro Bochner_Integration.integral_cong refl)
          (simp add: comp coord mat_def w algebra_simps)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2 \<partial>?M)
          - (\<integral>\<omega>. indicator A \<omega> * w \<partial>?M)"
        by (intro Bochner_Integration.integral_diff i1 i2)
      also have "\<dots> = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i w)\<^sup>2 \<partial>?M)
          - BMP.prob A * w"
        by (simp add: cst ins)
      finally show ?thesis .
    qed
    have vu: "(\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i v)\<^sup>2 \<partial>?M)
        = (\<integral>\<omega>. indicator A \<omega> * (x0 $ i + \<omega> i u)\<^sup>2 \<partial>?M)
          + (v - u) * BMP.prob A"
      by (rule bm_set_integral_coord_sq_eq[OF u uv A])
    show "set_lebesgue_integral ?M A (?Z u)
        = set_lebesgue_integral ?M A (?Z v)"
      unfolding split[OF u] split[OF v] vu by (simp add: algebra_simps)
  qed
qed

(*<*)
end
(*>*)
