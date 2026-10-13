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
  using bm_coordinate_integral[OF u _ gauss_measure_moment_odd[of u 0], of i]
  by (simp_all add: has_bochner_integral_iff)

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

text \<open>Everything rests on the independence of the increment from the past:
  any Borel function of the vector increment after \<open>s\<close> is independent of any
  variable measurable for the natural filtration at \<open>s\<close>.\<close>

lemma bm_meas_increment_fun_indep_var:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
    and g_meas: "g \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
    and h: "h \<in> borel_measurable (borel :: (real^'n) measure)"
  shows "BMP.indep_var borel (g :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (bmX x0 t \<omega> - bmX x0 s \<omega>))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?D = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> - bmX x0 s \<omega>"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have gen: "{g -` B \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?F"
    using measurable_sets[OF g_meas] by auto
  have L: "sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel} \<subseteq> sets ?F"
    using sets.sigma_sets_subset[OF gen] by simp
  have "{(\<lambda>\<omega>. h (?D \<omega>)) -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets (vimage_algebra (space ?M) ?D borel)"
  proof safe
    fix B :: "real set" assume "B \<in> sets borel"
    then have "?D -` (h -` B) \<inter> space ?M \<in> sets (vimage_algebra (space ?M) ?D borel)"
      using measurable_sets[OF h] by (intro in_vimage_algebra) simp
    then show "(\<lambda>\<omega>. h (?D \<omega>)) -` B \<inter> space ?M \<in> sets (vimage_algebra (space ?M) ?D borel)"
      by (simp add: vimage_def)
  qed
  from sets.sigma_sets_subset[OF this] have R: "sigma_sets (space ?M)
      {(\<lambda>\<omega>. h (?D \<omega>)) -` B \<inter> space ?M |B. B \<in> sets borel}
      \<subseteq> sets (vimage_algebra (space ?M) ?D borel)"
    by simp
  show ?thesis
    unfolding BMP.indep_var_eq
    using measurable_from_subalg[OF subalg g_meas] s st
      BMP.indep_set_mono[OF bm_filtration_increment_indep[OF s st] L R]
    by (auto intro: measurable_compose[OF _ h] borel_measurable_diff measurable_bmX)
qed

lemma bm_meas_increment_indep_var:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
    and g_meas: "g \<in> borel_measurable (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "BMP.indep_var borel (g :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
    borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)"
  using bm_meas_increment_fun_indep_var[OF s st g_meas borel_measurable_nth[of i]]
  by (simp add: bmX_def)

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
          [OF bm_meas_increment_indep_var[OF s st' borel_measurable_indicator[OF A]]
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
  interpret FF: finite_filtered_measure ?M ?F 0
    by (rule SP.finite_filtered_measure_natural_filtration[OF fm])
  show ?thesis
  proof (intro martingale.intro martingale_axioms.intro)
    show "sigma_finite_filtered_measure ?M ?F 0"
      by (rule FF.sigma_finite_filtered_measure_axioms)
    show "adapted_process ?M ?F 0 (bmX x0)"
      by (rule SP.adapted_process_natural_filtration)
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M (bmX x0 i)"
      by (rule bmX_integrable)
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    interpret S: sigma_finite_subalgebra ?M "?F i"
      using ij by (intro FF.sigma_finite_subalgebra_F) simp
    show "AE \<xi> in ?M. bmX x0 i \<xi> = cond_exp ?M (?F i) (bmX x0 j) \<xi>"
      by (rule S.has_cond_exp_charact(2)
          [OF bmX_has_cond_exp[OF ij], THEN AE_symmetric])
  qed
qed

section \<open>Ito's formula for the square: the compensated square is a martingale\<close>

text \<open>The Dynkin identity \<open>bmX_sq\<close> is the \<^emph>\<open>expectation\<close>
  form of Ito's formula for the test function \<open>|x|\<^sup>2\<close>.  Its process form,

    \<open>Z t = |B t|\<^sup>2 - int_0^t tr(mat 1) ds\<close> is a martingale,

  is proved in this section, through the compensated products of the
  coordinates \<open>X\<^sub>i X\<^sub>j - t \<delta>\<^sub>i\<^sub>j\<close>.\<close>

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

text \<open>The coordinates are independent, so the cross increments have mean zero
  and the products of two increments have mean \<open>(t - s) \<delta>\<^sub>i\<^sub>j\<close>.\<close>

lemma bm_coordinates_indep:
  "prob_space.indep_vars (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>_. wiener_pre) (\<lambda>k \<omega>. \<omega> k) UNIV"
  using BMC.indep_vars_PiM_coordinate by (simp add: bm_paths_def)

lemma bm_increment_coord_indep:
  fixes i j :: "'n::finite"
  assumes ij: "i \<noteq> j" and s: "0 \<le> s" and st: "s \<le> t"
  shows "prob_space.indep_var (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      borel (\<lambda>\<omega>. \<omega> i t - \<omega> i s) borel (\<lambda>\<omega>. \<omega> j t - \<omega> j s)"
proof -
  have "BMP.indep_vars (\<lambda>_. borel)
      (\<lambda>k \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> k t - \<omega> k s) UNIV"
    using s st by (intro BMP.indep_vars_compose2[OF bm_coordinates_indep]
        borel_measurable_diff measurable_coord) auto
  from BMP.indep_vars_indep_var[OF this, of i j] ij show ?thesis by simp
qed

lemma bm_increment_cross:
  fixes i j :: "'n::finite"
  assumes ij: "i \<noteq> j" and s: "0 \<le> s" and st: "s \<le> t"
  shows bm_increment_cross_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
       (\<lambda>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))"
  and bm_increment_cross_integral:
    "(\<integral>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s)
       \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  have t0: "0 \<le> t" using s st by simp
  note ind = bm_increment_coord_indep[OF ij s st]
  note ints = bm_increment_component_integrable[OF s t0]
  show "integrable bm_paths (\<lambda>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))"
    by (rule BMP.indep_var_integrable[OF ind ints ints])
  show "(\<integral>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s) \<partial>bm_paths) = 0"
    by (simp add: BMP.indep_var_lebesgue_integral[OF ind ints ints]
        bm_increment_component_integral[OF s t0])
qed

lemma bm_increment_prod:
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "has_bochner_integral (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s)) ((t - s) * mat 1 $ i $ j)"
  using bm_increment_sq[OF s st, of i] bm_increment_cross[OF _ s st, of i j]
  by (cases "i = j") (simp_all add: has_bochner_integral_iff power2_eq_square mat_def)

section \<open>The compensated products of the coordinates are martingales\<close>

lemma bm_set_integral_prod:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "has_bochner_integral (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. indicator A \<omega> * (bmX x0 t \<omega> $ i * bmX x0 t \<omega> $ j - t * mat 1 $ i $ j))
    (\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> $ i * bmX x0 s \<omega> $ j - s * mat 1 $ i $ j)
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  let ?a = "\<lambda>k \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 s \<omega> $ k"
  let ?d = "\<lambda>k \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> k t - \<omega> k s"
  interpret SP: stochastic_process ?M 0 "bmX x0"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule SP.subalgebra_natural_filtration)
  have A_M: "A \<in> sets ?M"
    using A subalg by (auto simp: subalgebra_def)
  have t0: "0 \<le> t" using s st by simp
  have a_F: "?a k \<in> borel_measurable ?F" for k
    using bm_coordinate_measurable_F[OF s, of k x0] by (simp add: bmX_def)
  have a_M: "?a k \<in> borel_measurable ?M" for k
    by (rule measurable_from_subalg[OF subalg a_F])
  have a_sq: "integrable ?M (\<lambda>\<omega>. (?a k \<omega>)\<^sup>2)" for k
    using bm_coordinate_sq_integrable[OF s, of "x0 $ k" k] by (simp add: bmX_def)
  have a_int: "integrable ?M (\<lambda>\<omega>. indicator A \<omega> * ?a k \<omega>)" for k
    using integrable_mult_indicator[OF A_M Bochner_Integration.integrable_add[OF
        BMP.integrable_const bm_coordinate_mean_integrable[OF s]], of "x0 $ k" k]
    by (simp add: bmX_def)
  have z0: "has_bochner_integral ?M (\<lambda>\<omega>. indicator A \<omega> * (?a i \<omega> * ?a j \<omega> - s * mat 1 $ i $ j))
      (\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> $ i * bmX x0 s \<omega> $ j - s * mat 1 $ i $ j) \<partial>?M)"
    using has_bochner_integral_integrable[OF integrable_mult_indicator[OF A_M
        Bochner_Integration.integrable_diff[OF integrable_prod_of_squares[OF
          a_sq[of i] a_sq[of j] a_M[of i] a_M[of j]] BMP.integrable_const]]]
    by simp
  have z1: "has_bochner_integral ?M (\<lambda>\<omega>. (indicator A \<omega> * ?a k \<omega>) * ?d l \<omega>) 0" for k l
    using bm_meas_increment_product[OF s st borel_measurable_times[OF
        borel_measurable_indicator[OF A] a_F[of k]] a_int[of k], where i = l]
    by (simp add: has_bochner_integral_iff)
  have z3: "has_bochner_integral ?M
      (\<lambda>\<omega>. indicator A \<omega> * (?d i \<omega> * ?d j \<omega> - (t - s) * mat 1 $ i $ j)) 0"
  proof (cases "s = t")
    case False
    with st have st': "s < t" by simp
    have ind: "BMP.indep_var borel (indicator A :: _ \<Rightarrow> real) borel
        (\<lambda>\<omega>. ?d i \<omega> * ?d j \<omega> - (t - s) * mat 1 $ i $ j)"
      using bm_meas_increment_fun_indep_var[OF s st' borel_measurable_indicator[OF A],
          of "\<lambda>v. v $ i * v $ j - (t - s) * mat 1 $ i $ j"]
      by (simp add: bmX_def)
    have dd: "has_bochner_integral ?M (\<lambda>\<omega>. ?d i \<omega> * ?d j \<omega> - (t - s) * mat 1 $ i $ j) 0"
      using has_bochner_integral_diff[OF bm_increment_prod[OF s st, of i j]
          has_bochner_integral_integrable[OF BMP.integrable_const[of "(t - s) * mat 1 $ i $ j"]]]
      by (simp add: BMP.prob_space)
    have ii: "integrable ?M (indicator A :: _ \<Rightarrow> real)"
      using A_M by (simp add: BMP.emeasure_eq_measure)
    show ?thesis
      using BMP.indep_var_integrable[OF ind ii integrable.intros[OF dd]]
        BMP.indep_var_lebesgue_integral[OF ind ii integrable.intros[OF dd]]
        has_bochner_integral_integral_eq[OF dd]
      by (simp add: has_bochner_integral_iff)
  qed (simp add: has_bochner_integral_zero)
  have "has_bochner_integral ?M
      (\<lambda>\<omega>. indicator A \<omega> * (?a i \<omega> * ?a j \<omega> - s * mat 1 $ i $ j)
        + (indicator A \<omega> * ?a i \<omega>) * ?d j \<omega> + (indicator A \<omega> * ?a j \<omega>) * ?d i \<omega>
        + indicator A \<omega> * (?d i \<omega> * ?d j \<omega> - (t - s) * mat 1 $ i $ j))
      ((\<integral>\<omega>. indicator A \<omega> * (bmX x0 s \<omega> $ i * bmX x0 s \<omega> $ j - s * mat 1 $ i $ j) \<partial>?M)
        + 0 + 0 + 0)"
    by (intro has_bochner_integral_add z0 z1 z3)
  then show ?thesis
    by (simp add: bmX_def algebra_simps)
qed


theorem martingale_bm_prod:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0
    (\<lambda>t \<omega>. bmX x0 t \<omega> $ i * bmX x0 t \<omega> $ j - t * mat 1 $ i $ j)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  interpret MX: martingale ?M ?F 0 "bmX x0" by (rule martingale_bmX)
  let ?Z = "\<lambda>t \<omega>. bmX x0 t \<omega> $ i * bmX x0 t \<omega> $ j - t * mat 1 $ i $ j"
  have Z: "has_bochner_integral ?M (\<lambda>\<omega>. indicator A \<omega> * ?Z v \<omega>)
      (\<integral>\<omega>. indicator A \<omega> * ?Z u \<omega> \<partial>?M)"
    if "0 \<le> u" "u \<le> v" "A \<in> sets (?F u)" for A u v
    by (rule bm_set_integral_prod[OF that])
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process ?M ?F 0 ?Z"
      by unfold_locales (intro borel_measurable_diff borel_measurable_times
          measurable_compose[OF MX.adapted borel_measurable_nth] borel_measurable_const)
    show "integrable ?M (?Z u)" if "0 \<le> u" for u
      using integrable.intros[OF Z[OF that order.refl sets.top]]
      by (subst (asm) Bochner_Integration.integrable_cong[OF refl, where g = "?Z u"]) auto
    show "set_lebesgue_integral ?M A (?Z u) = set_lebesgue_integral ?M A (?Z v)"
      if "0 \<le> u" "u \<le> v" "A \<in> sets (?F u)" for A u v
      using has_bochner_integral_integral_eq[OF Z[OF that]]
      by (simp add: set_lebesgue_integral_def)
  qed
qed

theorem martingale_bm_coord_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (bmX x0)) 0
    (\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))"
  by (rule martingale_cong_ge[OF martingale_bm_prod[of x0 i i]])
    (simp add: fun_eq_iff power2_eq_square set_integral_const mat_def)

section \<open>The compensated square is a martingale\<close>

text \<open>Summing the coordinates: the compensated squared norm is the sum of the
  compensated squares of the coordinates, a bounded linear image of the vector
  of them.\<close>

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
  let ?V = "\<lambda>t \<omega>. \<chi> i. (bmX x0 t \<omega> $ i)\<^sup>2
    - set_lebesgue_integral lborel {0..t} (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"
  have c: "set_lebesgue_integral lborel {0..u} (\<lambda>s. c) = u * c"
    if "0 \<le> u" for u c :: real
    using that by (simp add: set_integral_const)
  have "martingale ?M ?F 0 ?V"
    by (rule martingale_vecI) (unfold vec_lambda_beta, rule martingale_bm_coord_square)
  then have "martingale ?M ?F 0 (\<lambda>t \<omega>. \<Sum>i\<in>UNIV. ?V t \<omega> $ i)"
    by (rule martingale_bounded_linear_image[where T = "\<lambda>v :: real^'n. \<Sum>i\<in>UNIV. v $ i",
          rotated]) (intro bounded_linear_sum bounded_linear_vec_nth)
  then show ?thesis
    by (rule martingale_cong_ge)
      (simp add: fun_eq_iff c inner_vec_def power2_eq_square sum_subtractf
        sum_distrib_left trace_def)
qed

(*<*)
end
(*>*)
