(*
  Title:   Brownian_Stopped.thy
  Content: Stopping the continuous Brownian state process at the ball exit time.

  Optional stopping is available for real-valued martingales, so the vector
  state process is stopped componentwise and reassembled with martingale_vecI.
  The domination hypothesis of optional_stopping concerns the unstopped
  process, so it is discharged by the running-maximum bound Dsup of
  Doob_Inequality.
*)

theory Brownian_Stopped
  imports Brownian_Exit Stopped_Adaptedness
begin

section \<open>Components of the continuous state process\<close>

lemma cbmX_comp_measurable:
  "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. cbmX x0 u \<omega> $ k)
    \<in> borel_measurable bm_paths"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      cbmX x0 u \<omega> \<bullet> (axis k 1 :: real^'n))
      \<in> borel_measurable bm_paths"
    by (intro borel_measurable_inner borel_measurable_const measurable_cbmX)
  then show ?thesis
    by (simp add: inner_axis)
qed

lemma bmX_comp_measurable:
  assumes u: "u \<in> {0..}"
  shows "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. bmX x0 u \<omega> $ k)
    \<in> borel_measurable bm_paths"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
      bmX x0 u \<omega> \<bullet> (axis k 1 :: real^'n))
      \<in> borel_measurable bm_paths"
    by (intro borel_measurable_inner borel_measurable_const
        measurable_bmX[OF u])
  then show ?thesis
    by (simp add: inner_axis)
qed

lemma cbmX_comp_sq_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (\<lambda>\<omega>. (cbmX x0 u \<omega> $ k)\<^sup>2)"
proof -
  have "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (x0 $ k + \<omega> k u)\<^sup>2)"
    by (rule bm_coordinate_sq_integrable[OF u])
  moreover have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (x0 $ k + \<omega> k u)\<^sup>2)
      = (\<lambda>\<omega>. (bmX x0 u \<omega> $ k)\<^sup>2)"
    by (simp add: bmX_def)
  ultimately have bm: "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (bmX x0 u \<omega> $ k)\<^sup>2)"
    by simp
  have ae: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      (cbmX x0 u \<omega> $ k)\<^sup>2 = (bmX x0 u \<omega> $ k)\<^sup>2"
  proof -
    have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        cbmX x0 u \<omega> = bmX x0 u \<omega>"
      using u by (intro cbmX_ae_eq) simp
    then show ?thesis
      by eventually_elim simp
  qed
  have "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (cbmX x0 u \<omega> $ k)\<^sup>2)
      \<longleftrightarrow> integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (\<lambda>\<omega>. (bmX x0 u \<omega> $ k)\<^sup>2)"
    using u
    by (intro integrable_cong_AE ae borel_measurable_power
        cbmX_comp_measurable bmX_comp_measurable) simp_all
  then show ?thesis
    using bm by simp
qed

lemma cbmX_comp_martingale:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>t \<omega>. cbmX x0 t \<omega> $ k)"
  by (rule martingale_vec_component[OF martingale_cbmX])

lemma cbmX_comp_cont:
  fixes x0 :: "real^'n::finite"
  shows "continuous_on {0..} (\<lambda>s. cbmX x0 s \<omega> $ k)"
proof -
  have "continuous_on {0..}
      (\<lambda>s. cbmX x0 s \<omega> \<bullet> (axis k 1 :: real^'n))"
    by (intro continuous_on_inner continuous_on_const cbmX_cont)
  then show ?thesis
    by (simp add: inner_axis)
qed

lemma cbmX_comp_cont_le:
  fixes x0 :: "real^'n::finite"
  shows "continuous_on {0..u} (\<lambda>s. cbmX x0 s \<omega> $ k)"
  by (rule continuous_on_subset[OF cbmX_comp_cont]) auto

section \<open>An integrable dominating function on a finite horizon\<close>

lemma cbmX_comp_horizon:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 < u"
  shows "horizon_sq_int_martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0))
    (\<lambda>t \<omega>. cbmX x0 t \<omega> $ k) u"
  by (intro horizon_sq_int_martingale.intro
      horizon_sq_int_martingale_axioms.intro cbmX_comp_martingale u
      prob_space_bm_paths cbmX_comp_sq_integrable)

theorem cbmX_comp_dominated:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 < u"
  shows "\<exists>D. integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) D
    \<and> integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (\<lambda>\<omega>. (D \<omega>)\<^sup>2)
    \<and> (AE \<omega> in bm_paths.
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
          \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> D \<omega>)"
proof -
  interpret H: horizon_sq_int_martingale
    "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
    "natural_filtration bm_paths 0 (cbmX x0)"
    "\<lambda>t \<omega>. cbmX x0 t \<omega> $ k" u
    by (rule cbmX_comp_horizon[OF u])
  show ?thesis
  proof (intro exI conjI)
    show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) H.Dsup"
      by (rule H.Dsup_integrable)
    show "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (\<lambda>\<omega>. (H.Dsup \<omega>)\<^sup>2)"
      by (rule H.Dsup_sq_integrable)
    show "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
          \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> H.Dsup \<omega>"
      by (intro H.Dsup_dominates always_eventually allI cbmX_comp_cont_le)
  qed
qed

definition cbmD :: "real^'n::finite \<Rightarrow> 'n \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
  where "cbmD x0 k u = (SOME D. integrable bm_paths D
    \<and> integrable bm_paths (\<lambda>\<omega>. (D \<omega>)\<^sup>2)
    \<and> (AE \<omega> in bm_paths.
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
          \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> D \<omega>))"

lemma cbmD:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 < u"
  shows cbmD_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) (cbmD x0 k u)"
    and cbmD_sq_integrable:
    "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. (cbmD x0 k u \<omega>)\<^sup>2)"
    and cbmD_dominates:
    "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> cbmD x0 k u \<omega>"
  using someI_ex[OF cbmX_comp_dominated[OF u]] unfolding cbmD_def by auto

section \<open>Stopping at the ball exit time\<close>

lemma cbmX_comp_adapted:
  fixes x0 :: "real^'n::finite"
  shows "adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (\<lambda>t \<omega>. cbmX x0 t \<omega> $ k)"
proof (rule adapted_of_natural_filtration[where f = "\<lambda>u y. y $ k"])
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      cbmX x0 u \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by (rule measurable_cbmX)
  have "(\<lambda>y :: real^'n. y \<bullet> (axis k 1 :: real^'n))
      \<in> borel_measurable borel"
    by (intro borel_measurable_inner borel_measurable_const) measurable
  then show "\<And>u. (\<lambda>y :: real^'n. y $ k) \<in> borel_measurable borel"
    by (simp add: inner_axis)
qed

theorem cbmX_comp_stopped_martingale:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega> $ k)"
proof (rule optional_stopping[where D = "\<lambda>u. cbmD x0 k u"])
  show "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) 0 (\<lambda>t \<omega>. cbmX x0 t \<omega> $ k)"
    by (rule cbmX_comp_martingale)
  show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
      0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  show "\<And>s. 0 \<le> s \<Longrightarrow>
      {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        btau T r x0 \<omega> \<le> s}
      \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
    by (rule btau_stopping_time[OF T])
  show "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        continuous_on {0..u} (\<lambda>s. cbmX x0 s \<omega> $ k)"
    by (intro always_eventually allI cbmX_comp_cont_le)
  show "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
          \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> cbmD x0 k u \<omega>"
    by (rule cbmD_dominates)
  show "\<And>u. 0 < u \<Longrightarrow>
      integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) (cbmD x0 k u)"
    by (rule cbmD_integrable)
  fix v :: real assume v: "0 \<le> v"
  show "(\<lambda>\<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega> $ k)
      \<in> borel_measurable (natural_filtration bm_paths 0 (cbmX x0) v)"
  proof (rule stopped_adapted_of_cont[where tau = "btau T r x0"])
    show "adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (natural_filtration bm_paths 0 (cbmX x0)) 0
        (\<lambda>t \<omega>. cbmX x0 t \<omega> $ k)"
      by (rule cbmX_comp_adapted)
    show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
        0 \<le> btau T r x0 \<omega>"
      by (rule btau_nonneg[OF T])
    show "\<And>s. 0 \<le> s \<Longrightarrow>
        {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
          btau T r x0 \<omega> \<le> s}
        \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
      by (rule btau_stopping_time[OF T])
    show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
        continuous_on {0..} (\<lambda>s. cbmX x0 s \<omega> $ k)"
      by (rule cbmX_comp_cont)
    show "0 \<le> v"
      by (rule v)
  qed
qed

theorem martingale_cbmX_stopped:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)"
  by (rule martingale_vecI) (rule cbmX_comp_stopped_martingale[OF T])

section \<open>The compensated square\<close>

definition cbmZ :: "real^'n::finite \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
  where "cbmZ x0 t \<omega> = cbmX x0 t \<omega> \<bullet> cbmX x0 t \<omega>
    - set_lebesgue_integral lborel {0..t}
        (\<lambda>s. trace (mat 1 :: real^'n^'n))"

lemma martingale_cbmZ:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmZ x0)"
  unfolding cbmZ_def by (rule martingale_cbmX_square)

lemma cbmZ_alt:
  fixes x0 :: "real^'n::finite"
  assumes t: "0 \<le> t"
  shows "cbmZ x0 t \<omega>
    = cbmX x0 t \<omega> \<bullet> cbmX x0 t \<omega> - real CARD('n) * t"
  unfolding cbmZ_def by (simp add: bm_compensator_const[OF t])

lemma cbmZ_cont:
  fixes x0 :: "real^'n::finite"
  shows "continuous_on {0..} (\<lambda>s. cbmZ x0 s \<omega>)"
proof (rule continuous_on_cong[OF refl, THEN iffD1])
  show "cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega> - real CARD('n) * s
      = cbmZ x0 s \<omega>" if "s \<in> {0..}" for s
    using that by (intro cbmZ_alt[symmetric]) simp
  show "continuous_on {0..}
      (\<lambda>s. cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega> - real CARD('n) * s)"
    by (intro continuous_on_diff continuous_on_inner cbmX_cont
        continuous_on_mult continuous_on_const continuous_on_id)
qed

lemma cbmZ_measurable:
  fixes x0 :: "real^'n::finite"
  shows "cbmZ x0 t \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
  unfolding cbmZ_def
  by (intro borel_measurable_diff borel_measurable_const
      borel_measurable_inner measurable_cbmX)

definition cbmDZ :: "real^'n::finite \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
  where "cbmDZ x0 u \<omega>
    = (\<Sum>k\<in>(UNIV :: 'n set). (cbmD x0 k u \<omega>)\<^sup>2) + real CARD('n) * u"

lemma cbmDZ_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 < u"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) (cbmDZ x0 u)"
  unfolding cbmDZ_def
  by (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_sum
      cbmD_sq_integrable[OF u] BMP.integrable_const)

lemma cbmZ_dominated:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 < u"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
      \<bar>cbmZ x0 s \<omega>\<bar> \<le> cbmDZ x0 u \<omega>"
proof -
  have all_k: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>k\<in>(UNIV :: 'n set). \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> cbmD x0 k u \<omega>"
    by (intro AE_finite_allI) (auto intro: cbmD_dominates[OF u])
  then show ?thesis
  proof eventually_elim
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    assume bnd: "\<forall>k\<in>(UNIV :: 'n set). \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>cbmX x0 s \<omega> $ k\<bar> \<le> cbmD x0 k u \<omega>"
    show "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>cbmZ x0 s \<omega>\<bar> \<le> cbmDZ x0 u \<omega>"
    proof (intro allI impI)
      fix s :: real
      assume s: "0 \<le> s" and su: "s \<le> u"
      have comp: "(cbmX x0 s \<omega> $ k)\<^sup>2 \<le> (cbmD x0 k u \<omega>)\<^sup>2" for k
      proof -
        have "\<bar>cbmX x0 s \<omega> $ k\<bar> \<le> cbmD x0 k u \<omega>"
          using bnd s su by blast
        then have "\<bar>cbmX x0 s \<omega> $ k\<bar>\<^sup>2 \<le> (cbmD x0 k u \<omega>)\<^sup>2"
          by (intro power_mono) auto
        then show ?thesis by simp
      qed
      have sq: "cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega>
          = (\<Sum>k\<in>(UNIV :: 'n set). (cbmX x0 s \<omega> $ k)\<^sup>2)"
        by (simp add: inner_vec_def power2_eq_square)
      have le_sum: "cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega>
          \<le> (\<Sum>k\<in>(UNIV :: 'n set). (cbmD x0 k u \<omega>)\<^sup>2)"
        unfolding sq by (intro sum_mono comp)
      have nn: "0 \<le> cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega>"
        by simp
      have cs: "real CARD('n) * s \<le> real CARD('n) * u"
        using su by (intro mult_left_mono) auto
      have cnn: "0 \<le> real CARD('n) * s"
        using s by simp
      have "\<bar>cbmZ x0 s \<omega>\<bar>
          = \<bar>cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega> - real CARD('n) * s\<bar>"
        using s by (simp add: cbmZ_alt)
      also have "\<dots> \<le> cbmX x0 s \<omega> \<bullet> cbmX x0 s \<omega> + real CARD('n) * s"
        using nn cnn by (simp add: abs_diff_le_iff mult.commute)
      also have "\<dots> \<le> cbmDZ x0 u \<omega>"
        unfolding cbmDZ_def using le_sum cs by linarith
      finally show "\<bar>cbmZ x0 s \<omega>\<bar> \<le> cbmDZ x0 u \<omega>" .
    qed
  qed
qed

lemma cbmZ_adapted:
  fixes x0 :: "real^'n::finite"
  shows "adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmZ x0)"
  unfolding cbmZ_def
proof (rule adapted_of_natural_filtration
    [where f = "\<lambda>u y. y \<bullet> y
      - set_lebesgue_integral lborel {0..u} (\<lambda>s. trace (mat 1 :: real^'n^'n))"])
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      cbmX x0 u \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by (rule measurable_cbmX)
  show "\<And>u. (\<lambda>y :: real^'n. y \<bullet> y
      - set_lebesgue_integral lborel {0..u} (\<lambda>s. trace (mat 1 :: real^'n^'n)))
      \<in> borel_measurable borel"
    by (intro borel_measurable_diff borel_measurable_const
        borel_measurable_inner) measurable
qed

theorem cbmZ_stopped_martingale:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>v \<omega>. cbmZ x0 (min v (btau T r x0 \<omega>)) \<omega>)"
proof (rule optional_stopping[where D = "\<lambda>u. cbmDZ x0 u"])
  show "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmZ x0)"
    by (rule martingale_cbmZ)
  show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
      0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  show "\<And>s. 0 \<le> s \<Longrightarrow>
      {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        btau T r x0 \<omega> \<le> s}
      \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
    by (rule btau_stopping_time[OF T])
  show "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        continuous_on {0..u} (\<lambda>s. cbmZ x0 s \<omega>)"
    by (intro always_eventually allI continuous_on_subset[OF cbmZ_cont]) auto
  show "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
          \<bar>cbmZ x0 s \<omega>\<bar> \<le> cbmDZ x0 u \<omega>"
    by (rule cbmZ_dominated)
  show "\<And>u. 0 < u \<Longrightarrow>
      integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) (cbmDZ x0 u)"
    by (rule cbmDZ_integrable)
  fix v :: real assume v: "0 \<le> v"
  show "(\<lambda>\<omega>. cbmZ x0 (min v (btau T r x0 \<omega>)) \<omega>)
      \<in> borel_measurable (natural_filtration bm_paths 0 (cbmX x0) v)"
  proof (rule stopped_adapted_of_cont[where tau = "btau T r x0"])
    show "adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmZ x0)"
      by (rule cbmZ_adapted)
    show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
        0 \<le> btau T r x0 \<omega>"
      by (rule btau_nonneg[OF T])
    show "\<And>s. 0 \<le> s \<Longrightarrow>
        {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
          btau T r x0 \<omega> \<le> s}
        \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
      by (rule btau_stopping_time[OF T])
    show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
        continuous_on {0..} (\<lambda>s. cbmZ x0 s \<omega>)"
      by (rule cbmZ_cont)
    show "0 \<le> v"
      by (rule v)
  qed
qed

section \<open>The covariance of the stopped market\<close>

definition cbmA :: "real \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n^'n"
  where "cbmA T r x0 s \<omega> = (if s \<le> btau T r x0 \<omega> then mat 1 else 0)"

lemma trace_cbmA:
  fixes x0 :: "real^'n::finite"
  shows "trace (cbmA T r x0 s \<omega> :: real^'n^'n)
    = (if s \<le> btau T r x0 \<omega> then real CARD('n) else 0)"
proof (cases "s \<le> btau T r x0 \<omega>")
  case True
  then show ?thesis
    unfolding cbmA_def by (simp add: trace_mat1)
next
  case False
  then show ?thesis
    unfolding cbmA_def by (simp add: trace_def)
qed

lemma compensator_cbmA:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T" and v: "0 \<le> v"
  shows "set_lebesgue_integral lborel {0..v}
      (\<lambda>s. trace (cbmA T r x0 s \<omega> :: real^'n^'n))
    = real CARD('n) * min v (btau T r x0 \<omega>)"
proof -
  have tau: "0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  have "set_lebesgue_integral lborel {0..v}
      (\<lambda>s. trace (cbmA T r x0 s \<omega> :: real^'n^'n))
      = set_lebesgue_integral lborel {0..min v (btau T r x0 \<omega>)}
          (\<lambda>_. real CARD('n))"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong refl)
      (auto simp: trace_cbmA indicator_def)
  also have "\<dots> = min v (btau T r x0 \<omega>) * real CARD('n)"
    using v tau by (subst set_integral_const) auto
  finally show ?thesis
    by (simp add: mult_ac)
qed

lemma ito_Z_cbmA:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "ito_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
      (cbmA T r x0) v \<omega>
    = cbmZ x0 (min v (btau T r x0 \<omega>)) \<omega>"
proof (cases "0 \<le> v")
  case True
  have tau: "0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  have m: "0 \<le> min v (btau T r x0 \<omega>)"
    using True tau by simp
  show ?thesis
    unfolding ito_Z_def
    by (simp add: compensator_cbmA[OF T True] cbmZ_alt[OF m])
next
  case False
  then have empty: "{0..v} = {}"
    by simp
  have mv: "min v (btau T r x0 \<omega>) = v"
  proof (rule min_absorb1)
    show "v \<le> btau T r x0 \<omega>"
      using False btau_nonneg[OF T, of r x0 \<omega>] by simp
  qed
  show ?thesis
    unfolding ito_Z_def cbmZ_def mv empty
    by (simp add: set_lebesgue_integral_def)
qed

lemma ito_Z_cbmA_cont:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "continuous_on {0..}
    (\<lambda>s. ito_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
      (cbmA T r x0) s \<omega>)"
proof -
  have img: "(\<lambda>s. min s (btau T r x0 \<omega>)) ` {0..} \<subseteq> {0..}"
    using btau_nonneg[OF T, of r x0 \<omega>] by auto
  have "continuous_on {0..}
      ((\<lambda>t. cbmZ x0 t \<omega>) \<circ> (\<lambda>s. min s (btau T r x0 \<omega>)))"
  proof (rule continuous_on_compose)
    show "continuous_on {0..} (\<lambda>s. min s (btau T r x0 \<omega>))"
      by (intro continuous_on_min continuous_on_id continuous_on_const)
    show "continuous_on ((\<lambda>s. min s (btau T r x0 \<omega>)) ` {0..})
        (\<lambda>t. cbmZ x0 t \<omega>)"
      by (rule continuous_on_subset[OF cbmZ_cont img])
  qed
  then have "continuous_on {0..}
      (\<lambda>s. cbmZ x0 (min s (btau T r x0 \<omega>)) \<omega>)"
    by (simp add: comp_def)
  then show ?thesis
    by (simp add: ito_Z_cbmA[OF T])
qed

theorem martingale_ito_Z_cbmA:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (ito_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>) (cbmA T r x0))"
proof -
  have eq: "ito_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>) (cbmA T r x0)
      = (\<lambda>v \<omega>. cbmZ x0 (min v (btau T r x0 \<omega>)) \<omega>)"
    by (intro ext ito_Z_cbmA[OF T])
  show ?thesis
    unfolding eq by (rule cbmZ_stopped_martingale[OF T])
qed

section \<open>The compensated coordinate square of the stopped market\<close>

text \<open>The martingale-problem form of the market class also demands the
  compensated square COORDINATE BY COORDINATE.  The chain below mirrors the
  trace chain above verbatim: the unstopped coordinate martingale is
  \<open>martingale_cbm_coord_square\<close>, optional stopping transfers it to the ball
  exit time, and the \<open>coord_Z\<close> of the stopped process with covariance
  \<open>cbmA\<close> is literally that stopped process.\<close>

definition cbmC :: "real^'n::finite \<Rightarrow> 'n \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
  where "cbmC x0 i t \<omega> = (cbmX x0 t \<omega> $ i)\<^sup>2
    - set_lebesgue_integral lborel {0..t}
        (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"

lemma martingale_cbmC:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmC x0 i)"
  unfolding cbmC_def by (rule martingale_cbm_coord_square)

lemma cbmC_alt:
  fixes x0 :: "real^'n::finite"
  assumes t: "0 \<le> t"
  shows "cbmC x0 i t \<omega> = (cbmX x0 t \<omega> $ i)\<^sup>2 - t"
  unfolding cbmC_def by (simp add: bm_compensator_coord[OF t])

lemma cbmC_cont:
  fixes x0 :: "real^'n::finite"
  shows "continuous_on {0..} (\<lambda>s. cbmC x0 i s \<omega>)"
proof (rule continuous_on_cong[OF refl, THEN iffD1])
  show "cbmX x0 s \<omega> $ i * (cbmX x0 s \<omega> $ i) - s = cbmC x0 i s \<omega>"
    if "s \<in> {0..}" for s
    using that by (simp add: cbmC_alt power2_eq_square)
  show "continuous_on {0..} (\<lambda>s. cbmX x0 s \<omega> $ i * (cbmX x0 s \<omega> $ i) - s)"
    by (intro continuous_on_diff continuous_on_mult cbmX_comp_cont
        continuous_on_id)
qed

lemma cbmC_measurable:
  fixes x0 :: "real^'n::finite"
  shows "cbmC x0 i t
    \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
proof -
  have prj: "(\<lambda>x :: real^'n. x $ i) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  show ?thesis
    unfolding cbmC_def
    by (intro borel_measurable_diff borel_measurable_const
        borel_measurable_power measurable_compose[OF measurable_cbmX prj])
qed

lemma cbmC_dominated:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 < u"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
      \<bar>cbmC x0 i s \<omega>\<bar> \<le> (cbmD x0 i u \<omega>)\<^sup>2 + u"
proof -
  from cbmD_dominates[OF u] show ?thesis
  proof eventually_elim
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    assume bnd: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>cbmX x0 s \<omega> $ i\<bar> \<le> cbmD x0 i u \<omega>"
    show "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>cbmC x0 i s \<omega>\<bar> \<le> (cbmD x0 i u \<omega>)\<^sup>2 + u"
    proof (intro allI impI)
      fix s :: real
      assume s: "0 \<le> s" and su: "s \<le> u"
      have "\<bar>cbmX x0 s \<omega> $ i\<bar> \<le> cbmD x0 i u \<omega>"
        using bnd s su by blast
      then have "\<bar>cbmX x0 s \<omega> $ i\<bar>\<^sup>2 \<le> (cbmD x0 i u \<omega>)\<^sup>2"
        by (intro power_mono) auto
      then have sq: "(cbmX x0 s \<omega> $ i)\<^sup>2 \<le> (cbmD x0 i u \<omega>)\<^sup>2"
        by simp
      have nn: "0 \<le> (cbmX x0 s \<omega> $ i)\<^sup>2"
        by simp
      have "\<bar>cbmC x0 i s \<omega>\<bar> = \<bar>(cbmX x0 s \<omega> $ i)\<^sup>2 - s\<bar>"
        using s by (simp add: cbmC_alt)
      also have "\<dots> \<le> (cbmX x0 s \<omega> $ i)\<^sup>2 + s"
        using nn s by (simp add: abs_diff_le_iff)
      also have "\<dots> \<le> (cbmD x0 i u \<omega>)\<^sup>2 + u"
        using sq su by linarith
      finally show "\<bar>cbmC x0 i s \<omega>\<bar> \<le> (cbmD x0 i u \<omega>)\<^sup>2 + u" .
    qed
  qed
qed

lemma cbmC_adapted:
  fixes x0 :: "real^'n::finite"
  shows "adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmC x0 i)"
proof -
  have prj: "(\<lambda>x :: real^'n. x $ i) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  show ?thesis
    unfolding cbmC_def
  proof (rule adapted_of_natural_filtration
      [where f = "\<lambda>u y. (y $ i)\<^sup>2
        - set_lebesgue_integral lborel {0..u}
            (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"])
    show "\<And>u. 0 \<le> u \<Longrightarrow>
        cbmX x0 u \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_cbmX)
    show "\<And>u. (\<lambda>y :: real^'n. (y $ i)\<^sup>2
        - set_lebesgue_integral lborel {0..u}
            (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))
        \<in> borel_measurable borel"
      by (intro borel_measurable_diff borel_measurable_const
          borel_measurable_power prj)
  qed
qed

theorem cbmC_stopped_martingale:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>v \<omega>. cbmC x0 i (min v (btau T r x0 \<omega>)) \<omega>)"
proof (rule optional_stopping[where D = "\<lambda>u \<omega>. (cbmD x0 i u \<omega>)\<^sup>2 + u"])
  show "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmC x0 i)"
    by (rule martingale_cbmC)
  show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
      0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  show "\<And>s. 0 \<le> s \<Longrightarrow>
      {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        btau T r x0 \<omega> \<le> s}
      \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
    by (rule btau_stopping_time[OF T])
  show "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        continuous_on {0..u} (\<lambda>s. cbmC x0 i s \<omega>)"
    by (intro always_eventually allI continuous_on_subset[OF cbmC_cont]) auto
  show "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
          \<bar>cbmC x0 i s \<omega>\<bar> \<le> (cbmD x0 i u \<omega>)\<^sup>2 + u"
    by (rule cbmC_dominated)
  show "\<And>u. 0 < u \<Longrightarrow>
      integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (\<lambda>\<omega>. (cbmD x0 i u \<omega>)\<^sup>2 + u)"
    by (intro Bochner_Integration.integrable_add cbmD_sq_integrable
        BMP.integrable_const)
  fix v :: real assume v: "0 \<le> v"
  show "(\<lambda>\<omega>. cbmC x0 i (min v (btau T r x0 \<omega>)) \<omega>)
      \<in> borel_measurable (natural_filtration bm_paths 0 (cbmX x0) v)"
  proof (rule stopped_adapted_of_cont[where tau = "btau T r x0"])
    show "adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmC x0 i)"
      by (rule cbmC_adapted)
    show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
        0 \<le> btau T r x0 \<omega>"
      by (rule btau_nonneg[OF T])
    show "\<And>s. 0 \<le> s \<Longrightarrow>
        {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
          btau T r x0 \<omega> \<le> s}
        \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
      by (rule btau_stopping_time[OF T])
    show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
        continuous_on {0..} (\<lambda>s. cbmC x0 i s \<omega>)"
      by (rule cbmC_cont)
    show "0 \<le> v"
      by (rule v)
  qed
qed

lemma compensator_coord_cbmA:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T" and v: "0 \<le> v"
  shows "set_lebesgue_integral lborel {0..v}
      (\<lambda>s. (cbmA T r x0 s \<omega> :: real^'n^'n) $ i $ i)
    = min v (btau T r x0 \<omega>)"
proof -
  have tau: "0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  have entry: "(cbmA T r x0 s \<omega> :: real^'n^'n) $ i $ i
      = (if s \<le> btau T r x0 \<omega> then 1 else 0)" for s
    unfolding cbmA_def by (simp add: mat_def)
  have "set_lebesgue_integral lborel {0..v}
      (\<lambda>s. (cbmA T r x0 s \<omega> :: real^'n^'n) $ i $ i)
      = set_lebesgue_integral lborel {0..min v (btau T r x0 \<omega>)}
          (\<lambda>_. 1 :: real)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong refl)
      (auto simp: entry indicator_def)
  also have "\<dots> = min v (btau T r x0 \<omega>) * 1"
    using v tau by (subst set_integral_const) auto
  finally show ?thesis
    by simp
qed

lemma coord_Z_cbmA:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "coord_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
      (cbmA T r x0) i v \<omega>
    = cbmC x0 i (min v (btau T r x0 \<omega>)) \<omega>"
proof (cases "0 \<le> v")
  case True
  have tau: "0 \<le> btau T r x0 \<omega>"
    by (rule btau_nonneg[OF T])
  have m: "0 \<le> min v (btau T r x0 \<omega>)"
    using True tau by simp
  show ?thesis
    unfolding coord_Z_def
    by (simp add: compensator_coord_cbmA[OF T True] cbmC_alt[OF m])
next
  case False
  then have empty: "{0..v} = {}"
    by simp
  have mv: "min v (btau T r x0 \<omega>) = v"
  proof (rule min_absorb1)
    show "v \<le> btau T r x0 \<omega>"
      using False btau_nonneg[OF T, of r x0 \<omega>] by simp
  qed
  show ?thesis
    unfolding coord_Z_def cbmC_def mv empty
    by (simp add: set_lebesgue_integral_def)
qed

theorem martingale_coord_Z_cbmA:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (coord_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>) (cbmA T r x0) i)"
proof -
  have eq: "coord_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
      (cbmA T r x0) i
      = (\<lambda>v \<omega>. cbmC x0 i (min v (btau T r x0 \<omega>)) \<omega>)"
    by (intro ext coord_Z_cbmA[OF T])
  show ?thesis
    unfolding eq by (rule cbmC_stopped_martingale[OF T])
qed

section \<open>The ball exit time gives an Ito stopped market\<close>

theorem Brownian_ball_exit_market:
  fixes x0 :: "real^'n::finite" and T r :: real
  assumes T: "0 \<le> T" and r: "0 < r" and start: "norm x0 < r"
    and k: "1 \<le> k" "k < CARD('n)"
  shows "ito_stopped_market (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0))
    (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
    (cbmA T r x0) k 1 (cball 0 r) x0 (btau T r x0) r"
proof (intro ito_stopped_market.intro[OF martingale_cbmX_stopped[OF T]]
    ito_stopped_market_axioms.intro)
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?tau = "btau T r x0"
  have tau0: "0 \<le> ?tau \<omega>" for \<omega>
    by (rule btau_nonneg[OF T])
  show "prob_space ?M"
    by simp
  show "1 \<le> k" "k < CARD('n)" "1 \<le> (1 :: real)"
    using k by simp_all
  show "AE \<omega> in ?M. cbmX x0 (min 0 (?tau \<omega>)) \<omega> = x0"
  proof -
    have "AE \<omega> in ?M. cbmX x0 0 \<omega> = bmX x0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    moreover have "AE \<omega> in ?M. bmX x0 0 \<omega> = x0"
      by (rule bmX_start)
    ultimately show ?thesis
      by eventually_elim (simp add: tau0 min_absorb1)
  qed
  show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> 0 \<le> ?tau \<omega>"
    by (rule tau0)
  show "?tau \<in> borel_measurable ?M"
    by (rule btau_measurable[OF T])
  show "\<And>s. 0 \<le> s \<Longrightarrow>
      {\<omega> \<in> space ?M. ?tau \<omega> \<le> s}
      \<in> sets (natural_filtration bm_paths 0 (cbmX x0) s)"
    by (rule btau_stopping_time[OF T])
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow>
      cbmX x0 (min s (?tau \<omega>)) \<omega> \<in> cball 0 r"
    using cbmX_in_cball_AE[OF T r start]
    by eventually_elim (simp add: min_absorb1)
  show "cball (0 :: real^'n) r \<subseteq> cball 0 r"
    by simp
  show "\<And>s \<omega>. \<omega> \<in> space ?M \<Longrightarrow>
      cbmX x0 (min s (?tau \<omega>)) \<omega>
      = cbmX x0 (min (min s (?tau \<omega>)) (?tau \<omega>)) \<omega>"
    by simp
  show "\<And>s \<omega>. \<omega> \<in> space ?M \<Longrightarrow> ?tau \<omega> < s \<Longrightarrow>
      cbmA T r x0 s \<omega> = 0"
    unfolding cbmA_def by simp
  have psd1: "psd (mat 1 :: real^'n^'n)"
    by (simp add: psd_def)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow>
      psd (cbmA T r x0 s \<omega>)"
    using psd1 by (simp add: cbmA_def)
  have elb: "eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ UNIV] conjI)
    show "subspace (UNIV :: (real^'n) set)" by simp
    show "CARD('n) - k \<le> dim (UNIV :: (real^'n) set)" by simp
    show "\<forall>x\<in>(UNIV :: (real^'n) set). x \<bullet> x \<le> x \<bullet> (mat 1 *v x)"
      by simp
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow>
      eigen_lb (cbmA T r x0 s \<omega>) (CARD('n) - k)"
    using elb by (simp add: cbmA_def)
  have eub: "eigen_ub (mat 1 :: real^'n^'n) 1"
    by (simp add: eigen_ub_def)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> ?tau \<omega> \<longrightarrow>
      eigen_ub (cbmA T r x0 s \<omega>) 1"
    using eub by (simp add: cbmA_def)
  have ti: "set_integrable lborel {0..t}
      (\<lambda>s. trace (cbmA T r x0 s \<omega> :: real^'n^'n))" for t \<omega>
  proof -
    have "integrable lborel
        (\<lambda>s. indicat_real {0..min t (?tau \<omega>)} s *\<^sub>R real CARD('n))"
    proof (intro integrable_scaleR_left integrable_real_indicator)
      show "{0..min t (?tau \<omega>)} \<in> sets lborel"
        unfolding sets_lborel
        by (intro borel_closed closed_atLeastAtMost)
      show "emeasure lborel {0..min t (?tau \<omega>)} < \<infinity>"
        by (simp add: emeasure_lborel_Icc_eq)
    qed
    moreover have "(\<lambda>s. indicat_real {0..t} s
          *\<^sub>R trace (cbmA T r x0 s \<omega> :: real^'n^'n))
        = (\<lambda>s. indicat_real {0..min t (?tau \<omega>)} s *\<^sub>R real CARD('n))"
      by (intro ext) (auto simp: trace_cbmA indicator_def)
    ultimately show ?thesis
      unfolding set_integrable_def by simp
  qed
  show "AE \<omega> in ?M. \<forall>t. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t}
        (\<lambda>s. trace (cbmA T r x0 s \<omega> :: real^'n^'n))"
    using ti by simp
  have int_c: "integrable ?M (\<lambda>\<omega>. real CARD('n) * min t (?tau \<omega>))"
    if t: "0 \<le> t" for t :: real
  proof (rule Bochner_Integration.integrable_bound
      [OF BMP.integrable_const])
    show "(\<lambda>\<omega>. real CARD('n) * min t (?tau \<omega>))
        \<in> borel_measurable ?M"
      using btau_measurable[OF T] by measurable
    show "AE \<omega> in ?M.
        norm (real CARD('n) * min t (?tau \<omega>))
          \<le> norm (real CARD('n) * t)"
      using tau0 t by (intro AE_I2) (simp add: mult_left_mono)
  qed
  show "integrable ?M
      (\<lambda>\<omega>. cbmX x0 (min (min t (?tau \<omega>)) (?tau \<omega>)) \<omega>
        \<bullet> cbmX x0 (min (min t (?tau \<omega>)) (?tau \<omega>)) \<omega>)"
    if t: "0 \<le> t" for t :: real
  proof -
    have int_Z: "integrable ?M (\<lambda>\<omega>. cbmZ x0 (min t (?tau \<omega>)) \<omega>)"
      by (rule martingale.integrable[OF cbmZ_stopped_martingale[OF T] t])
    have eq: "cbmX x0 (min t (?tau \<omega>)) \<omega>
        \<bullet> cbmX x0 (min t (?tau \<omega>)) \<omega>
        = cbmZ x0 (min t (?tau \<omega>)) \<omega>
          + real CARD('n) * min t (?tau \<omega>)" for \<omega>
    proof -
      have m: "0 \<le> min t (?tau \<omega>)"
        using t tau0[of \<omega>] by simp
      show ?thesis
        using cbmZ_alt[OF m, of x0 \<omega>] by simp
    qed
    have "integrable ?M (\<lambda>\<omega>. cbmZ x0 (min t (?tau \<omega>)) \<omega>
        + real CARD('n) * min t (?tau \<omega>))"
      by (intro Bochner_Integration.integrable_add int_Z int_c[OF t])
    then have "integrable ?M (\<lambda>\<omega>. cbmX x0 (min t (?tau \<omega>)) \<omega>
        \<bullet> cbmX x0 (min t (?tau \<omega>)) \<omega>)"
      by (simp add: eq)
    then show ?thesis
      by simp
  qed
  show "integrable ?M
      (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (?tau \<omega>)}
        (\<lambda>s. trace (cbmA T r x0 s \<omega> :: real^'n^'n)))"
    if t: "0 \<le> t" for t :: real
  proof -
    have eq: "set_lebesgue_integral lborel {0..min t (?tau \<omega>)}
        (\<lambda>s. trace (cbmA T r x0 s \<omega> :: real^'n^'n))
        = real CARD('n) * min t (?tau \<omega>)" for \<omega>
    proof -
      have m: "0 \<le> min t (?tau \<omega>)"
        using t tau0[of \<omega>] by simp
      show ?thesis
        using compensator_cbmA[OF T m, of r x0 \<omega>] by simp
    qed
    show ?thesis
      unfolding eq by (rule int_c[OF t])
  qed
  show "martingale ?M (natural_filtration bm_paths 0 (cbmX x0)) 0
      (ito_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>) (cbmA T r x0))"
    by (rule martingale_ito_Z_cbmA[OF T])
  show "AE \<omega> in ?M. continuous_on {0..}
      (\<lambda>s. ito_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
        (cbmA T r x0) s \<omega>)"
    by (intro always_eventually allI ito_Z_cbmA_cont[OF T])
  show "\<And>i. martingale ?M (natural_filtration bm_paths 0 (cbmX x0)) 0
      (coord_Z (\<lambda>v \<omega>. cbmX x0 (min v (btau T r x0 \<omega>)) \<omega>)
        (cbmA T r x0) i)"
    by (rule martingale_coord_Z_cbmA[OF T])
  show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow>
      continuous_on {0..} (\<lambda>s. cbmX x0 (min s (?tau \<omega>)) \<omega>)"
  proof -
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real" assume "\<omega> \<in> space ?M"
    have cm: "continuous_on {0..} (\<lambda>s. min s (?tau \<omega>))"
      by (intro continuous_intros)
    have sub: "(\<lambda>s. min s (?tau \<omega>)) ` {0..} \<subseteq> {0..}"
      using tau0[of \<omega>] by auto
    have "continuous_on {0..}
        ((\<lambda>v. cbmX x0 v \<omega>) \<circ> (\<lambda>s. min s (?tau \<omega>)))"
      by (rule continuous_on_compose
          [OF cm continuous_on_subset[OF cbmX_cont sub]])
    then show "continuous_on {0..} (\<lambda>s. cbmX x0 (min s (?tau \<omega>)) \<omega>)"
      by (simp add: comp_def)
  qed
next
  \<comment> \<open>The volatility is an INDICATOR in time, so its time-measurability
      is the same one-line \<open>measurable_If\<close> as
      \<open>Paper_Class.acont_set_borel_measurable\<close>.  \<open>lborel\<close> has to be pinned
      at \<open>real measure\<close> and every binder annotated: it is polymorphic, and
      \<open>real^'n^'n\<close> has an \<open>ord\<close> instance, so an unannotated binder
      elaborates at the MATRIX type.\<close>
  show "AE \<omega> in bm_paths. set_borel_measurable lborel {0..}
                        (\<lambda>s. cbmA T r x0 s \<omega>)"
  proof (intro always_eventually allI)
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    have e: "(\<lambda>u::real. indicat_real {0..} u *\<^sub>R cbmA T r x0 u \<omega>)
        = (\<lambda>u::real. if u \<le> btau T r x0 \<omega>
              then (if u < 0 then 0 else (mat 1 :: real^'n^'n)) else 0)"
      by (rule ext) (simp add: cbmA_def)
    have "(\<lambda>u::real. if u \<le> btau T r x0 \<omega>
              then (if u < 0 then 0 else (mat 1 :: real^'n^'n)) else 0)
        \<in> borel_measurable (lborel :: real measure)"
    proof (rule measurable_If)
      \<comment> \<open>the \<^verbatim>\<open>if u < 0\<close> form, not an indicator: the \<open>measurable\<close>
          method reduces the branch condition to \<open>open {..<0}\<close>, whereas the
          indicator form leaves the FALSE goal \<open>open {0..}\<close>.\<close>
      show "(\<lambda>u::real. if u < 0 then 0 else (mat 1 :: real^'n^'n))
          \<in> borel_measurable (lborel :: real measure)"
        by measurable
      show "(\<lambda>u::real. 0 :: real^'n^'n)
          \<in> borel_measurable (lborel :: real measure)"
        by measurable
      show "{u \<in> space (lborel :: real measure). u \<le> btau T r x0 \<omega>}
          \<in> sets (lborel :: real measure)"
        by simp
    qed
    with e show "set_borel_measurable lborel {0..}
        (\<lambda>s. cbmA T r x0 s \<omega>)"
      unfolding set_borel_measurable_def by simp
  qed
qed


section \<open>The exit-time bound for the constructed Brownian motion\<close>

text \<open>With the locale instance in place, its conclusion --- the exit-time
  bound of Lemma 2.1 --- becomes an ordinary theorem about the constructed
  Brownian motion stopped on leaving the ball of radius \<open>r\<close>.  Nothing is
  assumed here beyond the numerical side conditions: the martingale
  property, the eigenvalue bounds and the integrability requirements are
  all consequences of the construction.\<close>

corollary Brownian_ball_exit_time_bound:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T" and r: "0 < r" and start: "norm x0 < r"
    and k: "1 \<le> k" "k < CARD('n)" and t: "0 \<le> t"
  shows "real (CARD('n) - k)
      * (\<integral>\<omega>. min t (btau T r x0 \<omega>)
          \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
    \<le> r\<^sup>2 - x0 \<bullet> x0"
  by (rule ito_stopped_market.stopped_expected_time_bound
      [OF Brownian_ball_exit_market[OF T r start k] t])

text \<open>Specialising to the plane, the unit ball, start at the origin,
  horizon \<open>1\<close> and \<open>k = L = 1\<close> discharges every side condition
  numerically, so the following two statements have no hypotheses
  whatsoever: the stopped-market locale is non-vacuous, and planar
  Brownian motion started at the centre of the unit disc spends expected
  time at most \<open>1\<close> before leaving it.\<close>

theorem Brownian_ball_exit_market_nonvacuous:
  "ito_stopped_market
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX (0 :: real^2)))
    (\<lambda>v \<omega>. cbmX (0 :: real^2) (min v (btau 1 1 (0 :: real^2) \<omega>)) \<omega>)
    (cbmA 1 1 (0 :: real^2)) 1 1 (cball 0 1) 0
    (btau 1 1 (0 :: real^2)) 1"
proof (rule Brownian_ball_exit_market)
  show "(0 :: real) \<le> 1" by simp
  show "(0 :: real) < 1" by simp
  show "norm (0 :: real^2) < 1" by simp
  show "(1 :: nat) \<le> 1" by simp
  show "(1 :: nat) < CARD(2)" by simp
qed

corollary bm2_ball_exit_time_bound:
  assumes t: "0 \<le> t"
  shows "(\<integral>\<omega>. min t (btau 1 1 (0 :: real^2) \<omega>)
      \<partial>(bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)) \<le> 1"
proof -
  have "real (CARD(2) - 1)
      * (\<integral>\<omega>. min t (btau 1 1 (0 :: real^2) \<omega>)
          \<partial>(bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure))
    \<le> 1\<^sup>2 - (0 :: real^2) \<bullet> 0"
  proof (rule Brownian_ball_exit_time_bound)
    show "(0 :: real) \<le> 1" by simp
    show "(0 :: real) < 1" by simp
    show "norm (0 :: real^2) < 1" by simp
    show "(1 :: nat) \<le> 1" by simp
    show "(1 :: nat) < CARD(2)" by simp
    show "0 \<le> t" by (rule t)
  qed
  then show ?thesis by simp
qed

end