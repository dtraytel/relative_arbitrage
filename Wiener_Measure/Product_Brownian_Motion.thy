section \<open>The product Brownian model and its increments\<close>

(*<*)
theory Product_Brownian_Motion
  imports Brownian_Motion
    "Kolmogorov_Chentsov.Kolmogorov_Chentsov_Extras"
    "Continuous_Time_Martingales.Martingale_Algebra"
    "Continuous_Time_Martingales.Integrability_Criteria"
begin

(*>*)


text \<open>
  An n-dimensional Brownian market model discharging the locale
             "\<open>sufficiently_volatile_market\<close>" of \<open>Volatile_Market\<close>.

    The market is the product of CARD('n) independent copies of the Wiener
    measure \<open>wiener_pre\<close> from \<open>Brownian_Motion\<close>, started at x0, with constant
    instantaneous covariance mat 1 and a deterministic horizon.  For this
    model every assumption of \<open>sufficiently_volatile_market\<close> --- including the
    martingale property with respect to the natural filtration and the
    martingale-problem identity \<open>dynkin_quadratic\<close> --- becomes a theorem,
    \<open>showing that the axiomatization of the class \<P>\<^sub>x is non-vacuous.\<close>\<close>
section \<open>Independence toolkit\<close>

text \<open>\<open>indep_var_distr_iff\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


text \<open>\<open>indep_vars_cong_sets\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


text \<open>\<open>indep_var_PiM_components\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


section \<open>The past and an increment of the Wiener measure are independent\<close>

text \<open>The finite past and an increment of the Wiener measure are
  independent.  Since @{const prob_space.indep_var} forces both variables
  to take values in a common type, the increment is encoded as a
  one-point function.\<close>

lemma wiener_pre_past_increment_indep:
  assumes U: "finite U" "U \<subseteq> {0..s}" and s: "0 \<le> s" and st: "s < t"
  shows "W.indep_var (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>\<omega>. restrict \<omega> U)
    (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>\<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s)"
proof -
  define J where "J = U \<union> {s, t}"
  have finJ: "finite J" using U by (simp add: J_def)
  have J0: "J \<subseteq> {0..}" using U s st by (auto simp: J_def)
  have sJ: "s \<in> J" and tJ: "t \<in> J" and UJ: "U \<subseteq> J"
    by (auto simp: J_def)
  define grp1 where "grp1 = {v \<in> J. v \<le> s}"
  define grp2 where "grp2 = {v \<in> J. s < v}"
  have grp1_eq: "grp1 = U \<union> {s}"
    using U st by (auto simp: grp1_def J_def)
  have grp2_eq: "grp2 = {t}"
    using U st by (auto simp: grp2_def J_def)
  interpret IP: prob_space "inc_prod 0 J" by simp
  \<comment> \<open>the coordinates of the increment product are independent\<close>
  interpret PPS: product_prob_space
    "\<lambda>u. gauss_measure (u - prevt 0 J u)" J
    by (intro product_prob_space.intro product_sigma_finite.intro
        product_prob_space_axioms.intro sigma_finite_gauss_measure
        prob_space_gauss_measure)
  have coords: "IP.indep_vars (\<lambda>_. borel) (\<lambda>u w. w u) J"
  proof -
    have "prob_space.indep_vars (Pi\<^sub>M J (\<lambda>u. gauss_measure (u - prevt 0 J u)))
        (\<lambda>u. gauss_measure (u - prevt 0 J u)) (\<lambda>u w. w u) J"
      using finJ sJ by (intro PPS.indep_vars_PiM_coordinate) auto
    then have "IP.indep_vars (\<lambda>u. gauss_measure (u - prevt 0 J u))
        (\<lambda>u w. w u) J"
      by (simp add: inc_prod_def)
    then show ?thesis
      by (rule IP.indep_vars_cong_sets[rotated]) simp
  qed
  \<comment> \<open>group them into past and future coordinates\<close>
  have grouped: "IP.indep_var
      (Pi\<^sub>M grp1 (\<lambda>_. borel)) (\<lambda>w. restrict w grp1)
      (Pi\<^sub>M grp2 (\<lambda>_. borel)) (\<lambda>w. restrict w grp2)"
  proof -
    have disj: "grp1 \<inter> grp2 = {}"
      by (auto simp: grp1_def grp2_def)
    have s1: "grp1 \<subseteq> J" and s2: "grp2 \<subseteq> J"
      by (auto simp: grp1_def grp2_def)
    show ?thesis
      using IP.indep_var_restrict[OF coords disj s1 s2] by simp
  qed
  \<comment> \<open>past values and the increment are functions of the two groups\<close>
  define ph1 where "ph1 = (\<lambda>h :: real \<Rightarrow> real.
      \<lambda>u\<in>U. \<Sum>v\<in>{v \<in> grp1. v \<le> u}. h v)"
  define ph2 where "ph2 = (\<lambda>h :: real \<Rightarrow> real. \<lambda>u\<in>{t}. h t)"
  have ph1m: "ph1 \<in> Pi\<^sub>M grp1 (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M U (\<lambda>_. (borel :: real measure))"
    unfolding ph1_def
    by (intro measurable_restrict borel_measurable_sum
        measurable_component_singleton) auto
  have ph2m: "ph2 \<in> Pi\<^sub>M grp2 (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))"
    unfolding ph2_def grp2_eq
    by (intro measurable_restrict measurable_component_singleton) simp
  have comp_ind: "IP.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
      (\<lambda>w. ph1 (restrict w grp1)) (Pi\<^sub>M {t} (\<lambda>_. borel))
      (\<lambda>w. ph2 (restrict w grp2))"
    using IP.indep_var_compose[OF grouped ph1m ph2m]
    by (simp add: comp_def)
  \<comment> \<open>identify the composed maps with restriction/increment after csum\<close>
  have csum_val: "csum J w u = (\<Sum>v\<in>{v \<in> J. v \<le> u}. w v)"
    if "u \<in> J" for w u
    using that by (simp add: csum_def)
  have past_eq: "(\<lambda>w. ph1 (restrict w grp1))
      = (\<lambda>w. restrict (csum J w) U)"
  proof
    fix w :: "real \<Rightarrow> real"
    show "ph1 (restrict w grp1) = restrict (csum J w) U"
      unfolding ph1_def
    proof (rule restrict_ext)
      fix u assume u: "u \<in> U"
      have uJ: "u \<in> J" using u UJ by blast
      have us: "u \<le> s" using u U by auto
      have seteq: "{v \<in> grp1. v \<le> u} = {v \<in> J. v \<le> u}"
        using us by (auto simp: grp1_def)
      have "(\<Sum>v\<in>{v \<in> grp1. v \<le> u}. restrict w grp1 v)
          = (\<Sum>v\<in>{v \<in> grp1. v \<le> u}. w v)"
        by (intro sum.cong refl) (auto simp: grp1_def)
      then show "(\<Sum>v\<in>{v \<in> grp1. v \<le> u}. restrict w grp1 v)
          = csum J w u"
        by (simp add: csum_val[OF uJ] seteq)
    qed
  qed
  have inc_eq: "(\<lambda>w. ph2 (restrict w grp2))
      = (\<lambda>w. \<lambda>u\<in>{t}. csum J w t - csum J w s)"
  proof
    fix w :: "real \<Rightarrow> real"
    have subs: "{v \<in> J. v \<le> s} \<subseteq> {v \<in> J. v \<le> t}"
      using st by auto
    have ddiff: "{v \<in> J. v \<le> t} - {v \<in> J. v \<le> s} = {t}"
      using U st tJ by (auto simp: J_def)
    have "csum J w t - csum J w s
        = (\<Sum>v\<in>{v \<in> J. v \<le> t}. w v) - (\<Sum>v\<in>{v \<in> J. v \<le> s}. w v)"
      by (simp add: csum_val[OF tJ] csum_val[OF sJ])
    also have "\<dots> = (\<Sum>v\<in>{v \<in> J. v \<le> t} - {v \<in> J. v \<le> s}. w v)"
      using finJ subs by (subst sum_diff) auto
    also have "\<dots> = w t"
      unfolding ddiff by simp
    finally have wt: "csum J w t - csum J w s = w t" .
    have "restrict w grp2 t = w t"
      using st tJ by (simp add: grp2_def)
    then show "ph2 (restrict w grp2) = (\<lambda>u\<in>{t}. csum J w t - csum J w s)"
      by (simp add: ph2_def wt)
  qed
  have over_inc: "IP.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
      (\<lambda>w. restrict (csum J w) U) (Pi\<^sub>M {t} (\<lambda>_. borel))
      (\<lambda>w. \<lambda>u\<in>{t}. csum J w t - csum J w s)"
    using comp_ind unfolding past_eq inc_eq .
  \<comment> \<open>transport along csum to the finite-dimensional distribution\<close>
  have restrU: "(\<lambda>h. restrict h U)
      \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M U (\<lambda>_. (borel :: real measure))"
    by (rule measurable_restrict_subset[OF UJ])
  have DJ: "(\<lambda>h. \<lambda>u\<in>{t}. h t - h s)
      \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))"
    using sJ tJ
    by (intro measurable_restrict borel_measurable_diff
        measurable_component_singleton)
  have iff1: "prob_space.indep_var (distr (inc_prod 0 J)
        (Pi\<^sub>M J (\<lambda>_. borel)) (csum J))
      (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>h. restrict h U)
      (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>h. \<lambda>u\<in>{t}. h t - h s)
      \<longleftrightarrow> IP.indep_var (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>w. restrict (csum J w) U)
        (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>w. \<lambda>u\<in>{t}. csum J w t - csum J w s)"
    by (rule indep_var_distr_iff[OF prob_space_inc_prod
        measurable_csum_inc_prod restrU DJ])
  have over_fdd: "prob_space.indep_var (bm_fdd J)
      (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>h. restrict h U)
      (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>h. \<lambda>u\<in>{t}. h t - h s)"
    using iff1 over_inc by (simp add: bm_fdd_def)
  \<comment> \<open>transport along the marginal map to the Wiener measure\<close>
  have iff2: "prob_space.indep_var (distr wiener_pre
        (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J))
      (Pi\<^sub>M U (\<lambda>_. borel)) (\<lambda>h. restrict h U)
      (Pi\<^sub>M {t} (\<lambda>_. borel)) (\<lambda>h. \<lambda>u\<in>{t}. h t - h s)
      \<longleftrightarrow> W.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
        (\<lambda>\<omega>. restrict (restrict \<omega> J) U)
        (Pi\<^sub>M {t} (\<lambda>_. borel))
        (\<lambda>\<omega>. \<lambda>u\<in>{t}. restrict \<omega> J t - restrict \<omega> J s)"
    by (rule indep_var_distr_iff[OF prob_space_wiener_pre
        measurable_restrict_wiener_pre[OF J0] restrU DJ])
  have "W.indep_var (Pi\<^sub>M U (\<lambda>_. borel))
      (\<lambda>\<omega>. restrict (restrict \<omega> J) U)
      (Pi\<^sub>M {t} (\<lambda>_. borel))
      (\<lambda>\<omega>. \<lambda>u\<in>{t}. restrict \<omega> J t - restrict \<omega> J s)"
    using over_fdd iff2 by (simp add: wiener_pre_marginal[OF finJ J0])
  moreover have "(\<lambda>\<omega> :: real \<Rightarrow> real. restrict (restrict \<omega> J) U)
      = (\<lambda>\<omega>. restrict \<omega> U)"
    using UJ by (auto simp: restrict_def fun_eq_iff)
  moreover have "(\<lambda>\<omega> :: real \<Rightarrow> real. \<lambda>u\<in>{t}. restrict \<omega> J t - restrict \<omega> J s)
      = (\<lambda>\<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s)"
    using sJ tJ by (auto simp: restrict_def fun_eq_iff)
  ultimately show ?thesis by simp
qed

section \<open>The product Brownian model\<close>

definition bm_paths :: "('n::finite \<Rightarrow> real \<Rightarrow> real) measure" where
  "bm_paths = Pi\<^sub>M UNIV (\<lambda>_. wiener_pre)"

lemma prob_space_bm_paths [intro, simp]: "prob_space bm_paths"
  unfolding bm_paths_def
  by (intro prob_space_PiM prob_space_wiener_pre)

interpretation BMP: prob_space "bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure"
  by simp

interpretation BMC: product_prob_space "\<lambda>_ :: 'n::finite. wiener_pre" UNIV
  by (intro product_prob_space.intro product_sigma_finite.intro
      product_prob_space_axioms.intro prob_space_imp_sigma_finite
      prob_space_wiener_pre)

lemma bm_paths_component:
  "distr (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure) wiener_pre
    (\<lambda>\<omega>. \<omega> i) = wiener_pre"
  unfolding bm_paths_def by (rule BMC.PiM_component) simp

lemma measurable_bm_coordinate [measurable]:
  assumes u: "u \<in> {0..}"
  shows "(\<lambda>\<omega>. \<omega> i u) \<in> (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<rightarrow>\<^sub>M (borel :: real measure)"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i)
      \<in> Pi\<^sub>M UNIV (\<lambda>_. wiener_pre) \<rightarrow>\<^sub>M wiener_pre"
    by (rule measurable_component_singleton) simp
  then show ?thesis
    unfolding bm_paths_def
    by (rule measurable_compose[OF _ measurable_coord[OF u]])
qed

section \<open>Gaussian first and second moments\<close>

lemma gauss_measure_mean:
  shows gauss_measure_mean_integrable:
    "integrable (gauss_measure v) (\<lambda>y. y)"
    and gauss_measure_mean_integral:
    "(\<integral>y. y \<partial>gauss_measure v) = 0"
proof -
  have both: "integrable (gauss_measure v) (\<lambda>y. y)
      \<and> (\<integral>y. y \<partial>gauss_measure v) = 0"
  proof (cases "v \<le> 0")
    case True
    then have g: "gauss_measure v = return borel 0"
      by (simp add: gauss_measure_def)
    have "integrable (return borel (0 :: real)) (\<lambda>y. y)"
      by (auto simp: integrable_iff_bounded nn_integral_return)
    moreover have "(\<integral>y. y \<partial>return borel (0 :: real)) = 0"
      by (subst integral_return) auto
    ultimately show ?thesis by (simp add: g)
  next
    case False
    then have v: "0 < v" by simp
    have "has_bochner_integral lborel
        (\<lambda>x. normal_density 0 (sqrt v) x * (x - 0) ^ (2 * 0 + 1)) 0"
      using normal_moment_odd[of "sqrt v" 0 0] v by simp
    then have "has_bochner_integral lborel
        (\<lambda>x. normal_density 0 (sqrt v) x * x) 0"
      by simp
    then have "has_bochner_integral
        (density lborel (normal_density 0 (sqrt v))) (\<lambda>y. y) 0"
      by (subst has_bochner_integral_density)
        (auto simp: mult_ac)
    then have "has_bochner_integral (gauss_measure v) (\<lambda>y. y) 0"
      using v by (simp add: gauss_measure_pos)
    then show ?thesis
      by (auto intro: integrable.intros has_bochner_integral_integral_eq)
  qed
  from both show "integrable (gauss_measure v) (\<lambda>y. y)"
    and "(\<integral>y. y \<partial>gauss_measure v) = 0" by auto
qed

lemma gauss_measure_snd_moment:
  assumes v: "0 \<le> v"
  shows gauss_measure_snd_moment_integrable:
    "integrable (gauss_measure v) (\<lambda>y. y\<^sup>2)"
    and gauss_measure_snd_moment_integral:
    "(\<integral>y. y\<^sup>2 \<partial>gauss_measure v) = v"
proof -
  have both: "integrable (gauss_measure v) (\<lambda>y. y\<^sup>2)
      \<and> (\<integral>y. y\<^sup>2 \<partial>gauss_measure v) = v"
  proof (cases "v = 0")
    case True
    have "integrable (return borel (0 :: real)) (\<lambda>y. y\<^sup>2)"
      by (auto simp: integrable_iff_bounded nn_integral_return)
    moreover have "(\<integral>y. y\<^sup>2 \<partial>return borel (0 :: real)) = 0"
      by (subst integral_return) auto
    ultimately show ?thesis
      by (simp add: True gauss_measure_zero)
  next
    case False
    with v have v': "0 < v" by simp
    have "has_bochner_integral (gauss_measure v) (\<lambda>x. x ^ (2 * 1))
        (fact (2 * 1) / (2 ^ 1 * fact 1) * v ^ 1)"
      by (rule gauss_measure_moment_even[OF v'])
    then have "has_bochner_integral (gauss_measure v) (\<lambda>y. y\<^sup>2) v"
      by simp
    then show ?thesis
      by (auto intro: integrable.intros has_bochner_integral_integral_eq)
  qed
  from both show "integrable (gauss_measure v) (\<lambda>y. y\<^sup>2)"
    and "(\<integral>y. y\<^sup>2 \<partial>gauss_measure v) = v" by auto
qed

lemma gauss_shifted_square:
  assumes v: "0 \<le> v"
  shows gauss_shifted_square_integrable:
    "integrable (gauss_measure v) (\<lambda>y. (c + y)\<^sup>2)"
    and gauss_shifted_square_integral:
    "(\<integral>y. (c + y)\<^sup>2 \<partial>gauss_measure v) = c\<^sup>2 + v"
proof -
  interpret G: prob_space "gauss_measure v" by simp
  note mean_int = gauss_measure_mean_integrable[of v]
  note mean_val = gauss_measure_mean_integral[of v]
  note sq_int = gauss_measure_snd_moment_integrable[OF v]
  note sq_val = gauss_measure_snd_moment_integral[OF v]
  have expand: "\<And>y :: real. (c + y)\<^sup>2 = c\<^sup>2 + ((2 * c) * y + y\<^sup>2)"
    by (simp add: power2_eq_square field_simps)
  have int_lin: "integrable (gauss_measure v) (\<lambda>y. (2 * c) * y)"
    by (intro integrable_mult_right mean_int)
  have int_rest: "integrable (gauss_measure v) (\<lambda>y. (2 * c) * y + y\<^sup>2)"
    by (intro Bochner_Integration.integrable_add int_lin sq_int)
  show "integrable (gauss_measure v) (\<lambda>y. (c + y)\<^sup>2)"
    unfolding expand
    by (intro Bochner_Integration.integrable_add int_rest
        G.integrable_const)
  have pu: "G.prob UNIV = 1"
    using G.prob_space by simp
  have e2: "(\<integral>y. (2 * c) * y + y\<^sup>2 \<partial>gauss_measure v) = v"
  proof -
    have "(\<integral>y. (2 * c) * y + y\<^sup>2 \<partial>gauss_measure v)
        = (\<integral>y. (2 * c) * y \<partial>gauss_measure v) + (\<integral>y. y\<^sup>2 \<partial>gauss_measure v)"
      by (rule Bochner_Integration.integral_add[OF int_lin sq_int])
    then show ?thesis
      by (simp add: mean_val sq_val)
  qed
  show "(\<integral>y. (c + y)\<^sup>2 \<partial>gauss_measure v) = c\<^sup>2 + v"
    unfolding expand
    by (subst Bochner_Integration.integral_add[OF G.integrable_const
        int_rest]) (simp add: pu e2)
qed

section \<open>Coordinate moments of the product model\<close>

lemma wiener_pre_coord':
  assumes u: "0 \<le> u"
  shows "distr wiener_pre borel (\<lambda>\<omega>. \<omega> u) = gauss_measure u"
proof -
  have ae: "AE \<omega> in wiener_pre. \<omega> u = \<omega> u - \<omega> 0"
    using wiener_pre_start by eventually_elim simp
  have m1: "(\<lambda>\<omega>. \<omega> u) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_coord) simp
  have m2: "(\<lambda>\<omega>. \<omega> u - \<omega> 0) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro borel_measurable_diff measurable_coord) simp_all
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> u)
      = distr wiener_pre borel (\<lambda>\<omega>. \<omega> u - \<omega> 0)"
    by (rule distr_cong_AE[OF refl refl ae m1 m2])
  also have "\<dots> = gauss_measure (u - 0)"
    by (rule wiener_pre_increment[OF order_refl u])
  finally show ?thesis by simp
qed

lemma bm_coordinate_distr:
  assumes u: "0 \<le> u"
  shows "distr (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure) borel
    (\<lambda>\<omega>. \<omega> i u) = gauss_measure u"
proof -
  have cu: "(\<lambda>\<omega>. \<omega> u) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_coord) simp
  have ci: "(\<lambda>\<omega>. \<omega> i) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M wiener_pre"
    unfolding bm_paths_def
    by (rule measurable_component_singleton) simp
  have "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel (\<lambda>\<omega>. \<omega> i u)
      = distr (distr bm_paths wiener_pre (\<lambda>\<omega>. \<omega> i)) borel (\<lambda>\<omega>. \<omega> u)"
    by (subst distr_distr[OF cu ci]) (simp add: comp_def)
  also have "\<dots> = distr wiener_pre borel (\<lambda>\<omega>. \<omega> u)"
    by (simp add: bm_paths_component)
  also have "\<dots> = gauss_measure u"
    by (rule wiener_pre_coord'[OF u])
  finally show ?thesis .
qed

lemma bm_coordinate_sq:
  assumes u: "0 \<le> u"
  shows bm_coordinate_sq_integrable:
    "integrable (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (c + \<omega> i u)\<^sup>2)"
    and bm_coordinate_sq_integral:
    "(\<integral>\<omega>. (c + \<omega> i u)\<^sup>2 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = c\<^sup>2 + u"
proof -
  have m: "(\<lambda>\<omega>. \<omega> i u) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    using u by (intro measurable_bm_coordinate) simp
  have sq_meas: "(\<lambda>y :: real. (c + y)\<^sup>2) \<in> borel_measurable borel"
    by measurable
  have "integrable (distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i u)) (\<lambda>y. (c + y)\<^sup>2)"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_shifted_square_integrable[OF u])
  then show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (c + \<omega> i u)\<^sup>2)"
    by (rule integrable_distr[OF m])
  have "(\<integral>\<omega>. (c + \<omega> i u)\<^sup>2 \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = (\<integral>y. (c + y)\<^sup>2 \<partial>distr bm_paths borel (\<lambda>\<omega>. \<omega> i u))"
    by (rule integral_distr[OF m sq_meas, symmetric])
  also have "\<dots> = c\<^sup>2 + u"
    unfolding bm_coordinate_distr[OF u]
    by (rule gauss_shifted_square_integral[OF u])
  finally show "(\<integral>\<omega>. (c + \<omega> i u)\<^sup>2
      \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = c\<^sup>2 + u" .
qed

section \<open>The market process\<close>

text \<open>\<open>measurable_vec_components\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

definition bmX :: "real^'n::finite \<Rightarrow> real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n"
  where "bmX x0 t \<omega> = x0 + (\<chi> i. \<omega> i t)"

lemma measurable_bmX [measurable]:
  assumes "t \<in> {0..}"
  shows "bmX x0 t \<in> bm_paths \<rightarrow>\<^sub>M (borel :: (real^'n::finite) measure)"
  unfolding bmX_def
  by (intro borel_measurable_add borel_measurable_const
      measurable_vec_components measurable_bm_coordinate[OF assms])

lemma bmX_start:
  fixes x0 :: "real^'n::finite"
  shows "AE \<omega> in bm_paths. bmX x0 0 \<omega> = x0"
proof -
  have coord0: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure). \<omega> i 0 = 0"
    for i :: 'n
  proof -
    have ci: "(\<lambda>\<omega>. \<omega> i) \<in> (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        \<rightarrow>\<^sub>M wiener_pre"
      unfolding bm_paths_def by (intro measurable_component_singleton) simp
    have c0: "(\<lambda>p. p (0 :: real)) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
      by (rule measurable_coord) simp
    have pred: "{p \<in> space wiener_pre. p 0 = 0} \<in> sets wiener_pre"
    proof -
      have "{p \<in> space wiener_pre. p 0 = 0}
          = (\<lambda>p. p (0 :: real)) -` {0} \<inter> space wiener_pre"
        by auto
      then show ?thesis
        using measurable_sets[OF c0, of "{0}"] by simp
    qed
    have pred': "{p \<in> space wiener_pre. p 0 = 0}
        \<in> sets (Pi\<^sub>M {0..} (\<lambda>_. borel :: real measure))"
      using pred unfolding sets_wiener_pre .
    have "AE p in distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        wiener_pre (\<lambda>\<omega>. \<omega> i). p 0 = 0"
      unfolding bm_paths_component by (rule wiener_pre_start)
    then show ?thesis
      by (subst (asm) AE_distr_iff) (auto intro: ci pred')
  qed
  have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>i\<in>(UNIV :: 'n set). \<omega> i 0 = 0"
    by (subst AE_ball_countable)
      (auto intro: coord0 simp: countable_finite)
  then show ?thesis
    unfolding bmX_def
  proof eventually_elim
    case (elim \<omega>)
    then show ?case
      by (simp add: vec_eq_iff)
  qed
qed

section \<open>The Dynkin identity for a deterministic time\<close>

text \<open>\<open>trace (mat 1) = CARD('n)\<close> is HOL-Analysis's \<open>trace_I\<close>.\<close>


lemma bmX_sq:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows bmX_sq_integrable:
    "integrable bm_paths (\<lambda>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>)"
    and bmX_sq_integral:
    "(\<integral>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega> \<partial>bm_paths)
      = x0 \<bullet> x0 + real CARD('n) * u"
proof -
  have expand: "bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>
      = (\<Sum>i\<in>UNIV. (x0 $ i + \<omega> i u)\<^sup>2)" for \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    by (simp add: bmX_def inner_vec_def power2_eq_square)
  show "integrable bm_paths (\<lambda>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega>)"
    unfolding expand
    by (intro Bochner_Integration.integrable_sum
        bm_coordinate_sq_integrable[OF u])
  have "(\<integral>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega> \<partial>bm_paths)
      = (\<Sum>i\<in>UNIV. \<integral>\<omega>. (x0 $ i + \<omega> i u)\<^sup>2 \<partial>bm_paths)"
    unfolding expand
    by (intro Bochner_Integration.integral_sum
        bm_coordinate_sq_integrable[OF u])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (x0 $ i)\<^sup>2 + u)"
    by (intro sum.cong refl bm_coordinate_sq_integral[OF u])
  also have "\<dots> = (\<Sum>i\<in>(UNIV :: 'n set). (x0 $ i)\<^sup>2) + real CARD('n) * u"
    by (simp add: sum.distrib)
  also have "(\<Sum>i\<in>(UNIV :: 'n set). (x0 $ i)\<^sup>2) = x0 \<bullet> x0"
    by (simp add: inner_vec_def power2_eq_square)
  finally show "(\<integral>\<omega>. bmX x0 u \<omega> \<bullet> bmX x0 u \<omega> \<partial>bm_paths)
      = x0 \<bullet> x0 + real CARD('n) * u" .
qed

lemma bm_compensator_const:
  assumes u: "0 \<le> u"
  shows "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. trace (mat 1 :: real^'n::finite^'n))
    = real CARD('n) * u"
proof -
  have "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. trace (mat 1 :: real^'n^'n)) = u * trace (mat 1 :: real^'n^'n)"
    using u by (subst set_integral_const) auto
  then show ?thesis
    by (simp add: trace_I mult_ac)
qed

text \<open>The compensated squared norm compensates \<open>|X\<^sub>t|\<^sup>2\<close> by the trace of the
  covariation.  A tightness argument needs more than that: it needs a
  fourth-moment bound on each coordinate separately, so the compensated
  square of each coordinate has to be a martingale in its own right, and a
  trace identity alone does not give this.  The per-coordinate compensator
  is \<open>w\<close> rather than \<open>CARD('n) * w\<close>, since \<open>mat 1 $ i $ i = 1\<close>.\<close>

lemma bm_compensator_coord:
  assumes u: "0 \<le> u"
  shows "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. (mat 1 :: real^'n::finite^'n) $ i $ i) = u"
proof -
  have "set_lebesgue_integral lborel {0..u}
      (\<lambda>_. (mat 1 :: real^'n^'n) $ i $ i)
      = u * ((mat 1 :: real^'n^'n) $ i $ i)"
    using u by (subst set_integral_const) auto
  then show ?thesis by (simp add: mat_def)
qed

text \<open>Two-sided pointwise bounds on the trace, from the eigenvalue
  conditions: positive semidefiniteness makes the diagonal, hence the trace,
  nonnegative, and an eigenvalue upper bound \<open>L\<close> caps every diagonal
  entry by \<open>L\<close>.\<close>


section \<open>Past and increments of the market are independent\<close>

lemma bm_paths_past_increment_indep:
  fixes U :: "real set"
  assumes U: "finite U" "U \<subseteq> {0..s}" and s: "0 \<le> s" and st: "s < t"
  shows "BMP.indep_var
      (Pi\<^sub>M (UNIV :: 'n::finite set) (\<lambda>_. Pi\<^sub>M U (\<lambda>_. borel)))
      (\<lambda>\<omega>. \<lambda>i\<in>UNIV. restrict (\<omega> i) U)
      (Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel)))
      (\<lambda>\<omega>. \<lambda>i\<in>UNIV. \<lambda>u\<in>{t}. \<omega> i t - \<omega> i s)"
proof -
  have gU: "(\<lambda>\<omega>. restrict \<omega> U)
      \<in> wiener_pre \<rightarrow>\<^sub>M Pi\<^sub>M U (\<lambda>_. (borel :: real measure))"
  proof (rule measurable_restrict)
    fix u assume "u \<in> U"
    then show "(\<lambda>\<omega>. \<omega> u) \<in> wiener_pre \<rightarrow>\<^sub>M borel"
      using U s by (intro measurable_coord) auto
  qed
  have hI: "(\<lambda>\<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s)
      \<in> wiener_pre \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))"
    using s st
    by (intro measurable_restrict borel_measurable_diff measurable_coord) auto
  show ?thesis
    unfolding bm_paths_def
    by (rule indep_var_PiM_components[where g = "\<lambda>_ \<omega>. restrict \<omega> U"
        and h = "\<lambda>_ \<omega>. \<lambda>u\<in>{t}. \<omega> t - \<omega> s"
        and N = "\<lambda>_. wiener_pre"])
      (auto intro!: prob_space_wiener_pre gU hI
        wiener_pre_past_increment_indep[OF U s st])
qed

section \<open>Increments are independent of the natural filtration\<close>

lemma bmX_increment_eq:
  "(\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>)
    = (\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. \<chi> i. \<omega> i t - \<omega> i s)"
  by (auto simp: bmX_def vec_eq_iff fun_eq_iff)

lemma bm_filtration_increment_indep:
  fixes x0 :: "real^'n::finite"
  assumes s: "0 \<le> s" and st: "s < t"
  shows "BMP.indep_set
    (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (bmX x0) s)
    (vimage_algebra (space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>) borel)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  define D where "D = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<chi> i. \<omega> i t - \<omega> i s)"
  define G1 where "G1 = {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      \<lambda>u\<in>V. bmX x0 u \<omega>) -` B \<inter> space ?M | V B.
      finite V \<and> V \<noteq> {} \<and> V \<subseteq> {0..s}
      \<and> B \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))}"
  define G2 where "G2 = {D -` C \<inter> space ?M | C.
      C \<in> sets (borel :: (real^'n) measure)}"
  have Xvec_meas: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<lambda>u\<in>V. bmX x0 u \<omega>)
      \<in> ?M \<rightarrow>\<^sub>M Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)"
    if V: "V \<subseteq> {0..s}" for V
  proof (rule measurable_restrict)
    fix u assume "u \<in> V"
    then have "u \<in> {0..}" using V s by auto
    then show "bmX x0 u \<in> ?M \<rightarrow>\<^sub>M borel"
      by (rule measurable_bmX)
  qed
  have D_meas: "D \<in> ?M \<rightarrow>\<^sub>M (borel :: (real^'n) measure)"
    unfolding D_def
    using s st
    by (intro measurable_vec_components borel_measurable_diff
        measurable_bm_coordinate) auto
  \<comment> \<open>the finite-dimensional independence, composed to the market process\<close>
  have Xvec_ind: "BMP.indep_var
      (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)) (\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>)
      (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure)) (\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>)"
    if V: "finite V" "V \<noteq> {}" "V \<subseteq> {0..s}" for V
  proof -
    note base = bm_paths_past_increment_indep[OF V(1,3) s st]
    define F1 where "F1 = (\<lambda>p :: 'n \<Rightarrow> real \<Rightarrow> real.
        \<lambda>u\<in>V. x0 + (\<chi> i. p i u))"
    define F2 where "F2 = (\<lambda>q :: 'n \<Rightarrow> real \<Rightarrow> real.
        \<lambda>u\<in>{t}. 0 *\<^sub>R x0 + (\<chi> i. q i t))"
    have cV: "(\<lambda>p :: 'n \<Rightarrow> real \<Rightarrow> real. p i)
        \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M V (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M V (\<lambda>_. (borel :: real measure))" for i
      by (rule measurable_component_singleton) simp
    have ct: "(\<lambda>p :: 'n \<Rightarrow> real \<Rightarrow> real. p i)
        \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. (borel :: real measure))" for i
      by (rule measurable_component_singleton) simp
    have F1m: "F1 \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M V (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)"
      unfolding F1_def
    proof (rule measurable_restrict)
      fix u assume u: "u \<in> V"
      have hu: "(\<lambda>h :: real \<Rightarrow> real. h u)
          \<in> Pi\<^sub>M V (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
        by (rule measurable_component_singleton[OF u])
      show "(\<lambda>p. x0 + (\<chi> i. p i u))
          \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M V (\<lambda>_. borel)) \<rightarrow>\<^sub>M borel"
        by (intro borel_measurable_add borel_measurable_const
            measurable_vec_components measurable_compose[OF cV hu])
    qed
    have F2m: "F2 \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel))
        \<rightarrow>\<^sub>M Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure)"
      unfolding F2_def
    proof (rule measurable_restrict)
      fix u assume "u \<in> {t}"
      have ht: "(\<lambda>h :: real \<Rightarrow> real. h t)
          \<in> Pi\<^sub>M {t} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
        by (rule measurable_component_singleton) simp
      show "(\<lambda>q. 0 *\<^sub>R x0 + (\<chi> i. q i t))
          \<in> Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_. Pi\<^sub>M {t} (\<lambda>_. borel)) \<rightarrow>\<^sub>M borel"
        by (intro borel_measurable_add borel_measurable_const
            measurable_vec_components measurable_compose[OF ct ht])
    qed
    have cmp1: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<lambda>u\<in>V. bmX x0 u \<omega>)
        = (\<lambda>\<omega>. F1 (\<lambda>i\<in>UNIV. restrict (\<omega> i) V))"
      by (auto simp: F1_def bmX_def fun_eq_iff restrict_def vec_eq_iff)
    have cmp2: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<lambda>u\<in>{t}. D \<omega>)
        = (\<lambda>\<omega>. F2 (\<lambda>i\<in>UNIV. \<lambda>u\<in>{t}. \<omega> i t - \<omega> i s))"
      by (auto simp: F2_def D_def fun_eq_iff restrict_def vec_eq_iff)
    show ?thesis
      unfolding cmp1 cmp2
      using BMP.indep_var_compose[OF base F1m F2m]
      by (simp add: comp_def)
  qed
  have Dvec_eq: "D -` C \<inter> space ?M
      = (\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -`
        ((\<lambda>h. h t) -` C \<inter> space (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure)))
        \<inter> space ?M"
    for C :: "(real^'n) set"
    by (auto simp: space_PiM PiE_iff extensional_def)
  have Dvec_set: "(\<lambda>h. h t) -` C
      \<inter> space (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))
      \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))"
    if that: "C \<in> sets (borel :: (real^'n) measure)" for C
  proof -
    have "(\<lambda>h :: real \<Rightarrow> real^'n. h t)
        \<in> Pi\<^sub>M {t} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: (real^'n) measure)"
      by (rule measurable_component_singleton) simp
    from measurable_sets[OF this that] show ?thesis .
  qed
  \<comment> \<open>pairwise factorization on the generators\<close>
  have fact_ab: "BMP.prob (a \<inter> b) = BMP.prob a * BMP.prob b"
    if a: "a \<in> G1" and b: "b \<in> G2" for a b
  proof -
    from a obtain V B where V: "finite V" "V \<noteq> {}" "V \<subseteq> {0..s}"
      and B: "B \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))"
      and a_def: "a = (\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` B \<inter> space ?M"
      by (auto simp: G1_def)
    from b obtain C where C: "C \<in> sets (borel :: (real^'n) measure)"
      and b_def: "b = D -` C \<inter> space ?M"
      by (auto simp: G2_def)
    have "BMP.indep_set
        (sigma_sets (space ?M) {(\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))})
        (sigma_sets (space ?M) {(\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))})"
      using Xvec_ind[OF V] unfolding BMP.indep_var_eq by blast
    moreover have "a \<in> sigma_sets (space ?M)
        {(\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))}"
      unfolding a_def using B by (intro sigma_sets.Basic) auto
    moreover have "b \<in> sigma_sets (space ?M)
        {(\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))}"
    proof -
      have "b \<in> {(\<lambda>\<omega>. \<lambda>u\<in>{t}. D \<omega>) -` X' \<inter> space ?M
          |X'. X' \<in> sets (Pi\<^sub>M {t} (\<lambda>_. borel :: (real^'n) measure))}"
        unfolding b_def Dvec_eq[of C]
        using Dvec_set[OF C] by blast
      then show ?thesis by (rule sigma_sets.Basic)
    qed
    ultimately show ?thesis
      by (rule BMP.indep_setD)
  qed
  have G1_events: "G1 \<subseteq> BMP.events"
    unfolding G1_def
    by (auto intro!: measurable_sets[OF Xvec_meas])
  have G2_events: "G2 \<subseteq> BMP.events"
    unfolding G2_def
    by (auto intro!: measurable_sets[OF D_meas])
  have G1_Int: "Int_stable G1"
  proof (rule Int_stableI)
    fix a b assume "a \<in> G1" "b \<in> G1"
    then obtain V1 B1 V2 B2 where
      V1: "finite V1" "V1 \<noteq> {}" "V1 \<subseteq> {0..s}"
      and B1: "B1 \<in> sets (Pi\<^sub>M V1 (\<lambda>_. borel :: (real^'n) measure))"
      and a_def: "a = (\<lambda>\<omega>. \<lambda>u\<in>V1. bmX x0 u \<omega>) -` B1 \<inter> space ?M"
      and V2: "finite V2" "V2 \<noteq> {}" "V2 \<subseteq> {0..s}"
      and B2: "B2 \<in> sets (Pi\<^sub>M V2 (\<lambda>_. borel :: (real^'n) measure))"
      and b_def: "b = (\<lambda>\<omega>. \<lambda>u\<in>V2. bmX x0 u \<omega>) -` B2 \<inter> space ?M"
      by (auto simp: G1_def)
    define V where "V = V1 \<union> V2"
    have V: "finite V" "V \<noteq> {}" "V \<subseteq> {0..s}"
      using V1 V2 by (auto simp: V_def)
    have sub1: "V1 \<subseteq> V" and sub2: "V2 \<subseteq> V" by (auto simp: V_def)
    define B where "B = ((\<lambda>h. restrict h V1) -` B1
        \<inter> space (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)))
        \<inter> ((\<lambda>h. restrict h V2) -` B2
        \<inter> space (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure)))"
    have Bs: "B \<in> sets (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))"
      unfolding B_def
      by (intro sets.Int
          measurable_sets[OF measurable_restrict_subset[OF sub1] B1]
          measurable_sets[OF measurable_restrict_subset[OF sub2] B2])
    have iv1: "V \<inter> V1 = V1" and iv2: "V \<inter> V2 = V2"
      using sub1 sub2 by auto
    have restr_eval: "restrict (\<lambda>u\<in>V. bmX x0 u \<omega>) V1 = (\<lambda>u\<in>V1. bmX x0 u \<omega>)"
      "restrict (\<lambda>u\<in>V. bmX x0 u \<omega>) V2 = (\<lambda>u\<in>V2. bmX x0 u \<omega>)"
      for \<omega> using sub1 sub2 by (auto simp: restrict_def fun_eq_iff)
    have sp: "(\<lambda>u\<in>V. bmX x0 u \<omega>)
        \<in> space (Pi\<^sub>M V (\<lambda>_. borel :: (real^'n) measure))" for \<omega>
      by (auto simp: space_PiM PiE_iff extensional_def)
    have "a \<inter> b = (\<lambda>\<omega>. \<lambda>u\<in>V. bmX x0 u \<omega>) -` B \<inter> space ?M"
      unfolding a_def b_def B_def
      by (auto simp: restr_eval sp iv1 iv2)
    then show "a \<inter> b \<in> G1"
      unfolding G1_def using V Bs by blast
  qed
  have G2_Int: "Int_stable G2"
  proof (rule Int_stableI)
    fix a b assume "a \<in> G2" "b \<in> G2"
    then obtain C1 C2 where C: "C1 \<in> sets (borel :: (real^'n) measure)"
      "C2 \<in> sets (borel :: (real^'n) measure)"
      and ab: "a = D -` C1 \<inter> space ?M" "b = D -` C2 \<inter> space ?M"
      by (auto simp: G2_def)
    have "a \<inter> b = D -` (C1 \<inter> C2) \<inter> space ?M"
      unfolding ab by auto
    then show "a \<inter> b \<in> G2"
      unfolding G2_def using C by blast
  qed
  have "BMP.indep_set G1 G2"
    by (rule BMP.indep_setI[OF G1_events G2_events fact_ab])
  then have "BMP.indep_sets (case_bool G1 G2) UNIV"
    unfolding BMP.indep_set_def .
  then have "BMP.indep_sets (\<lambda>b. sigma_sets (space ?M)
      (case_bool G1 G2 b)) UNIV"
    by (rule BMP.indep_sets_sigma)
      (auto split: bool.split simp: G1_Int G2_Int)
  then have sig: "BMP.indep_set (sigma_sets (space ?M) G1)
      (sigma_sets (space ?M) G2)"
    unfolding BMP.indep_set_def
    by (rule BMP.indep_sets_cong[THEN iffD1, OF refl, rotated])
      (auto split: bool.split)
  \<comment> \<open>the natural filtration is generated by @{text G1}\<close>
  have E1G1: "(\<Union>u\<in>{0..s}. {bmX x0 u -` A \<inter> space ?M | A. A \<in> sets borel})
      \<subseteq> G1"
  proof safe
    fix u A assume u: "u \<in> {0..s}"
      and A: "A \<in> sets (borel :: (real^'n) measure)"
    have hu: "(\<lambda>h :: real \<Rightarrow> real^'n. h u)
        \<in> Pi\<^sub>M {u} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: (real^'n) measure)"
      by (rule measurable_component_singleton) simp
    define B where "B = (\<lambda>h. h u) -` A
        \<inter> space (Pi\<^sub>M {u} (\<lambda>_. borel :: (real^'n) measure))"
    have Bs: "B \<in> sets (Pi\<^sub>M {u} (\<lambda>_. borel :: (real^'n) measure))"
      unfolding B_def by (rule measurable_sets[OF hu A])
    have eq: "bmX x0 u -` A \<inter> space ?M
        = (\<lambda>\<omega>. \<lambda>u'\<in>{u}. bmX x0 u' \<omega>) -` B \<inter> space ?M"
      unfolding B_def by (auto simp: space_PiM PiE_iff extensional_def)
    have "(\<lambda>\<omega>. \<lambda>u'\<in>{u}. bmX x0 u' \<omega>) -` B \<inter> space ?M \<in> G1"
      unfolding G1_def using u Bs by blast
    then show "bmX x0 u -` A \<inter> space ?M \<in> G1"
      unfolding eq .
  qed
  have F_sub: "sets (natural_filtration ?M 0 (bmX x0) s)
      \<subseteq> sigma_sets (space ?M) G1"
  proof -
    have "sets (natural_filtration ?M 0 (bmX x0) s)
        = sigma_sets (space ?M) (\<Union>u\<in>{0..s}.
          {bmX x0 u -` A \<inter> space ?M | A. A \<in> sets borel})"
      by (rule sets_natural_filtration)
    also have "\<dots> \<subseteq> sigma_sets (space ?M) G1"
      using E1G1 by (intro sigma_sets_mono) auto
    finally show ?thesis .
  qed
  have D_sub: "sets (vimage_algebra (space ?M)
      (\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>) borel) \<subseteq> sigma_sets (space ?M) G2"
  proof -
    have "{(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<chi> i. \<omega> i t - \<omega> i s) -` A
        \<inter> space ?M |A. A \<in> sets borel} \<subseteq> G2"
      by (auto simp: G2_def D_def)
    then show ?thesis
      unfolding sets_vimage_algebra bmX_increment_eq
      by (intro sigma_sets_mono) auto
  qed
  have "BMP.indep_sets (case_bool (sigma_sets (space ?M) G1)
      (sigma_sets (space ?M) G2)) UNIV"
    using sig unfolding BMP.indep_set_def .
  then have "BMP.indep_sets (case_bool
      (sets (natural_filtration ?M 0 (bmX x0) s))
      (sets (vimage_algebra (space ?M)
        (\<lambda>\<omega>. bmX x0 t \<omega> - bmX x0 s \<omega>) borel))) UNIV"
    by (rule BMP.indep_sets_mono_sets)
      (auto split: bool.split simp: F_sub D_sub)
  then show ?thesis
    unfolding BMP.indep_set_def .
qed


(*<*)
end
(*>*)
