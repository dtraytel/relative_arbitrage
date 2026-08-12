

(*<*)
theory Brownian_Continuous
  imports Modification_Transfer "Wiener_Measure.Brownian_Motion_Continuity"
begin

(*>*)

text \<open>
  The continuous Brownian state process on the product path space,
             and the transfer of its martingale property to its own natural
             filtration.

    The product model \<open>bm_paths\<close> of \<open>Brownian_Market\<close> has no continuous paths: its
    sample points are arbitrary functions.  The Kolmogorov-Chentsov theorem
    provides a continuous modification Bcont of the coordinate process, and
    \<open>Modification_Transfer\<close> moves the martingale property of the state process
    to the natural filtration of the modification.  The continuous state
    process built here is what the exit-time market needs.\<close>
section \<open>A continuous version of the coordinate process\<close>

definition Bcont :: "(real, real \<Rightarrow> real, real) stochastic_process" where
  "Bcont = (SOME B. modification bm_coord B
     \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. B t \<omega>)))"

lemma Bcont_ex: "modification bm_coord Bcont
    \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. Bcont t \<omega>))"
  unfolding Bcont_def
proof (rule someI_ex)
  show "\<exists>B. modification bm_coord B
      \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. B t \<omega>))"
    by (rule Brownian_motion_exists[of "1/8"]) auto
qed

lemma Bcont_mod: "modification bm_coord Bcont"
  using Bcont_ex by simp

lemma Bcont_cont: "continuous_on {0..} (\<lambda>t. Bcont t \<omega>)"
  using Bcont_ex by simp

lemma Bcont_source: "proc_source Bcont = wiener_pre"
  using modificationD(1)[OF Bcont_mod]
  by (auto simp: compatible_source)

lemma Bcont_target: "sets (proc_target Bcont) = sets (borel :: real measure)"
  using modificationD(1)[OF Bcont_mod] compatible_target by fastforce

lemma Bcont_meas: "process Bcont u \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
proof -
  have "process Bcont u \<in> proc_source Bcont \<rightarrow>\<^sub>M proc_target Bcont"
    by (rule stochastic_process_measurable)
  then show ?thesis
    using Bcont_source
    by (simp add: measurable_cong_sets[OF refl Bcont_target])
qed

lemma Bcont_coord:
  assumes u: "u \<in> {0..}"
  shows "AE \<omega> in wiener_pre. Bcont u \<omega> = \<omega> u"
proof -
  have "AE \<omega> in proc_source bm_coord.
      process bm_coord u \<omega> = process Bcont u \<omega>"
    using u by (intro modificationD(2)[OF Bcont_mod]) simp
  then have "AE \<omega> in wiener_pre. process bm_coord u \<omega> = process Bcont u \<omega>"
    unfolding source_bm_coord .
  then show ?thesis
    by (simp add: process_bm_coord[OF u] eq_commute)
qed

section \<open>The continuous state process\<close>

definition cbmX :: "real^'n::finite \<Rightarrow> real
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n"
  where "cbmX x0 t \<omega> = x0 + (\<chi> i. Bcont t (\<omega> i))"

lemma measurable_cbmX_coord:
  "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. Bcont t (\<omega> i))
    \<in> bm_paths \<rightarrow>\<^sub>M (borel :: real measure)"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i)
      \<in> Pi\<^sub>M UNIV (\<lambda>_. wiener_pre) \<rightarrow>\<^sub>M wiener_pre"
    by (rule measurable_component_singleton) simp
  then show ?thesis
    unfolding bm_paths_def by (rule measurable_compose[OF _ Bcont_meas])
qed

lemma measurable_cbmX [measurable]:
  "cbmX x0 t \<in> bm_paths \<rightarrow>\<^sub>M (borel :: (real^'n::finite) measure)"
  unfolding cbmX_def
  by (intro borel_measurable_add borel_measurable_const
      measurable_vec_components measurable_cbmX_coord)

lemma cbmX_ae_eq:
  fixes x0 :: "real^'n::finite"
  assumes t: "t \<in> {0..}"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    cbmX x0 t \<omega> = bmX x0 t \<omega>"
proof -
  have coord: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      Bcont t (\<omega> i) = \<omega> i t" for i :: 'n
  proof -
    have proj: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i)
        \<in> bm_paths \<rightarrow>\<^sub>M wiener_pre"
      unfolding bm_paths_def by (rule measurable_component_singleton) simp
    have "AE \<omega> in distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
        wiener_pre (\<lambda>\<omega>. \<omega> i). Bcont t \<omega> = \<omega> t"
      unfolding bm_paths_component using Bcont_coord[OF t] by simp
    from AE_distrD[OF proj this] show ?thesis by simp
  qed
  have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>i \<in> (UNIV :: 'n set). Bcont t (\<omega> i) = \<omega> i t"
    by (intro AE_finite_allI) (auto intro: coord)
  then show ?thesis
    by eventually_elim (simp add: cbmX_def bmX_def vec_eq_iff)
qed

section \<open>The continuous state process is a martingale\<close>

theorem martingale_cbmX:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0 (cbmX x0)"
proof (rule martingale_of_modification_vec[where X = "bmX x0"])
  show "prob_space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by simp
  show "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (bmX x0)) 0 (bmX x0)"
    by (rule martingale_bmX)
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      cbmX x0 u \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by (rule measurable_cbmX)
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        cbmX x0 u \<omega> = bmX x0 u \<omega>"
    by (intro cbmX_ae_eq) simp
qed

section \<open>The compensated square is a martingale for the same filtration\<close>

text \<open>The market locales need both the state process and its compensated
  square to be martingales for one filtration, namely the natural filtration
  of the continuous process.  This is what the general transfer theorem
  provides; adaptedness of the compensated square to that filtration holds
  because it is a continuous function of the state.\<close>

theorem martingale_cbmX_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>t \<omega>. cbmX x0 t \<omega> \<bullet> cbmX x0 t \<omega>
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0)"
  let ?c = "\<lambda>t. set_lebesgue_integral lborel {0..t}
    (\<lambda>s. trace (mat 1 :: real^'n^'n))"
  let ?Z = "\<lambda>t \<omega>. bmX x0 t \<omega> \<bullet> bmX x0 t \<omega> - ?c t"
  let ?Z' = "\<lambda>t \<omega>. cbmX x0 t \<omega> \<bullet> cbmX x0 t \<omega> - ?c t"
  have measZ': "?Z' u \<in> borel_measurable ?M" for u
    by (intro borel_measurable_diff borel_measurable_const
        borel_measurable_inner measurable_cbmX)
  have aeZ: "AE \<omega> in ?M. ?Z' u \<omega> = ?Z u \<omega>" if u: "0 \<le> u" for u
  proof -
    have "AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      using u by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  have adaptZ': "adapted_process ?M ?F 0 ?Z'"
  proof (rule adapted_of_natural_filtration
      [where f = "\<lambda>u y. y \<bullet> y - ?c u"])
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. (\<lambda>y :: real^'n. y \<bullet> y - ?c u)
        \<in> borel_measurable borel"
      by (intro borel_measurable_diff borel_measurable_const
          borel_measurable_inner) auto
  qed
  show ?thesis
  proof (rule martingale_of_modification_gen[where X = "bmX x0" and Y = ?Z])
    show "prob_space ?M"
      by simp
    show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0 ?Z"
      by (rule martingale_bm_square)
    show "\<And>u. 0 \<le> u \<Longrightarrow> bmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_bmX) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (intro cbmX_ae_eq) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> ?Z' u \<in> borel_measurable ?M"
      by (rule measZ')
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. ?Z' u \<omega> = ?Z u \<omega>"
      by (rule aeZ)
    show "adapted_process ?M ?F 0 ?Z'"
      by (rule adaptZ')
  qed
qed

section \<open>Path continuity\<close>

lemma continuous_on_vec_lambda:
  fixes f :: "'a::topological_space \<Rightarrow> 'n::finite \<Rightarrow> 'b::topological_space"
  assumes "\<And>i. continuous_on S (\<lambda>x. f x i)"
  shows "continuous_on S (\<lambda>x. (\<chi> i. f x i) :: ('b, 'n) vec)"
  using assms unfolding continuous_on_def by (auto intro: tendsto_vec_lambda)

lemma cbmX_cont:
  fixes x0 :: "real^'n::finite"
  shows "continuous_on {0..} (\<lambda>t. cbmX x0 t \<omega>)"
  unfolding cbmX_def
  by (intro continuous_on_add continuous_on_const continuous_on_vec_lambda
      Bcont_cont)

text \<open>The same compensated coordinate square, transferred to the continuous
  modification and its own natural filtration, by the general modification
  transfer theorem.  Adaptedness holds because the compensated square is a
  Borel function of the state.\<close>

theorem martingale_cbm_coord_square:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) 0
    (\<lambda>t \<omega>. (cbmX x0 t \<omega> $ i)\<^sup>2
      - set_lebesgue_integral lborel {0..t}
          (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0)"
  let ?c = "\<lambda>t. set_lebesgue_integral lborel {0..t}
    (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)"
  let ?Z = "\<lambda>t \<omega>. (bmX x0 t \<omega> $ i)\<^sup>2 - ?c t"
  let ?Z' = "\<lambda>t \<omega>. (cbmX x0 t \<omega> $ i)\<^sup>2 - ?c t"
  have prj: "(\<lambda>x :: real^'n. x $ i) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have measZ': "?Z' u \<in> borel_measurable ?M" for u
    by (intro borel_measurable_diff borel_measurable_const
        borel_measurable_power measurable_compose[OF measurable_cbmX prj])
  have aeZ: "AE \<omega> in ?M. ?Z' u \<omega> = ?Z u \<omega>" if u: "0 \<le> u" for u
  proof -
    have "AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      using u by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  have adaptZ': "adapted_process ?M ?F 0 ?Z'"
  proof (rule adapted_of_natural_filtration
      [where f = "\<lambda>u y. (y $ i)\<^sup>2 - ?c u"])
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. (\<lambda>y :: real^'n. (y $ i)\<^sup>2 - ?c u)
        \<in> borel_measurable borel"
      by (intro borel_measurable_diff borel_measurable_const
          borel_measurable_power prj)
  qed
  show ?thesis
  proof (rule martingale_of_modification_gen[where X = "bmX x0" and Y = ?Z])
    show "prob_space ?M"
      by simp
    show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0 ?Z"
      by (rule martingale_bm_coord_square)
    show "\<And>u. 0 \<le> u \<Longrightarrow> bmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_bmX) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (intro cbmX_ae_eq) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> ?Z' u \<in> borel_measurable ?M"
      by (rule measZ')
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. ?Z' u \<omega> = ?Z u \<omega>"
      by (rule aeZ)
    show "adapted_process ?M ?F 0 ?Z'"
      by (rule adaptZ')
  qed
qed

theorem Brownian_market_sufficiently_volatile:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and c: "0 \<le> c"
    and K: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> cbmX x0 s \<omega> \<in> K"
  shows "sufficiently_volatile_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
    (\<lambda>_ _. mat 1) k L K x0 (\<lambda>_. c)"
proof (intro sufficiently_volatile_market.intro
    sufficiently_volatile_market_axioms.intro)
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0 (cbmX x0)"
    by (rule martingale_cbmX)
  show "prob_space ?M" by simp
  show "1 \<le> k" "k < CARD('n)" "1 \<le> L" by fact+
  show "AE \<omega> in ?M. cbmX x0 0 \<omega> = x0"
  proof -
    have "AE \<omega> in ?M. cbmX x0 0 \<omega> = bmX x0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    with bmX_start[of x0] show ?thesis
      by eventually_elim simp
  qed
  show "AE \<omega> in ?M. 0 \<le> c" using c by simp
  show "(\<lambda>_. c) \<in> borel_measurable ?M" by simp
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> cbmX x0 s \<omega> \<in> K"
    by (rule K)
  have psd1: "psd (mat 1 :: real^'n^'n)"
    by (simp add: psd_def)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> psd (mat 1 :: real^'n^'n)"
    using psd1 by simp
  have elb: "eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ UNIV] conjI)
    show "subspace (UNIV :: (real^'n) set)" by simp
    show "CARD('n) - k \<le> dim (UNIV :: (real^'n) set)" by simp
    show "\<forall>x\<in>(UNIV :: (real^'n) set). x \<bullet> x \<le> x \<bullet> (mat 1 *v x)"
      by simp
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    using elb by simp
  have eub: "eigen_ub (mat 1 :: real^'n^'n) L"
  proof -
    have "x \<bullet> x \<le> L * (x \<bullet> x)" for x :: "real^'n"
      using mult_right_mono[OF L inner_ge_zero] by simp
    then show ?thesis
      by (simp add: eigen_ub_def)
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_ub (mat 1 :: real^'n^'n) L"
    using eub by simp
  have ti: "set_integrable lborel {0..t}
      (\<lambda>s. trace (mat 1 :: real^'n^'n))" for t :: real
  proof -
    have "integrable lborel
        (\<lambda>s. indicator {0..t} s *\<^sub>R trace (mat 1 :: real^'n^'n))"
    proof (intro integrable_scaleR_left integrable_real_indicator)
      show "{0..t} \<in> sets lborel"
        unfolding sets_lborel
        by (intro borel_closed closed_atLeastAtMost)
      show "emeasure lborel {0..t} < \<infinity>"
        by (simp add: emeasure_lborel_Icc_eq)
    qed
    then show ?thesis
      unfolding set_integrable_def .
  qed
  show "AE \<omega> in ?M. set_borel_measurable lborel {0..}
      (\<lambda>s :: real. mat 1 :: real^'n^'n)"
    unfolding set_borel_measurable_def by (intro AE_I2) simp
  show "AE \<omega> in ?M. \<forall>t :: real. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
    using ti by (intro AE_I2) blast
  have sq_ae: "AE \<omega> in ?M. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>
      = bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>" if t: "0 \<le> t" for t
  proof -
    have "AE \<omega> in ?M. cbmX x0 (min t c) \<omega> = bmX x0 (min t c) \<omega>"
      using t c by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  have sq_meas_b: "(\<lambda>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>)
      \<in> borel_measurable ?M" if t: "0 \<le> t" for t
    using t c by (intro borel_measurable_inner measurable_bmX) simp_all
  have sq_meas_c: "(\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)
      \<in> borel_measurable ?M" for t
    by (intro borel_measurable_inner measurable_cbmX)
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)"
  proof -
    fix t :: real assume t: "0 \<le> t"
    have u: "0 \<le> min t c" using t c by simp
    show "integrable ?M (\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)"
      using integrable_cong_AE[OF sq_meas_c sq_meas_b[OF t] sq_ae[OF t]]
        bmX_sq_integrable[OF u] by simp
  qed
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (rule BMP.integrable_const)
  show "(\<integral>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega> \<partial>?M)
      - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t c}
          (\<lambda>s. trace (mat 1 :: real^'n^'n)) \<partial>?M) = x0 \<bullet> x0"
    if t: "0 \<le> t" for t
  proof -
    have u: "0 \<le> min t c" using t c by simp
    have 0: "(\<integral>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega> \<partial>?M)
        = (\<integral>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega> \<partial>?M)"
      by (rule integral_cong_AE[OF sq_meas_c sq_meas_b[OF t] sq_ae[OF t]])
    have 1: "(\<integral>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega> \<partial>?M)
        = x0 \<bullet> x0 + real CARD('n) * min t c"
      by (rule bmX_sq_integral[OF u])
    have 2: "set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)) = real CARD('n) * min t c"
      by (rule bm_compensator_const[OF u])
    show ?thesis
      unfolding 0 1 2 by (simp add: BMP.prob_space)
  qed
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0
      (coord_Z (cbmX x0) (\<lambda>_ _. mat 1) i)" for i
    unfolding coord_Z_def by (rule martingale_cbm_coord_square)
  text \<open>A constant horizon is a stopping time for free: the event is the whole
    space or empty, and both lie in every sub-\<open>\<sigma>\<close>-algebra.\<close>
  show "\<And>s. 0 \<le> s \<Longrightarrow>
      {\<omega> \<in> space ?M. c \<le> s} \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
  proof -
    fix s :: real assume s: "0 \<le> s"
    show "{\<omega> \<in> space ?M. c \<le> s}
        \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
    proof (cases "c \<le> s")
      case True
      have "{\<omega> \<in> space ?M. c \<le> s}
          = space (natural_filtration ?M 0 (cbmX x0) s)"
        using True by simp
      moreover have "space (natural_filtration ?M 0 (cbmX x0) s)
          \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
        by (rule sets.top)
      ultimately show ?thesis by simp
    next
      case False
      have "{\<omega> \<in> space ?M. c \<le> s} = {}" using False by simp
      moreover have "{} \<in> sets (natural_filtration ?M 0 (cbmX x0) s)"
        by (rule sets.empty_sets)
      ultimately show ?thesis by metis
    qed
  qed
  show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. cbmX x0 s \<omega>)"
    by (rule cbmX_cont)
qed

section \<open>A concrete instance: the class \<open>\<P>\<^sub>x\<close> is inhabited\<close>

text \<open>Specialising the theorem above to the planar market with
  \<open>k = L = 1\<close>, horizon \<open>1\<close> and start \<open>0\<close> discharges all its side
  conditions numerically, so the following statement has no hypotheses
  whatsoever: the axiomatised market class of
  @{theory Relative_Arbitrage.Volatile_Market} is non-vacuous.\<close>

theorem sufficiently_volatile_market_nonvacuous:
  "sufficiently_volatile_market
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX 0)) (cbmX (0 :: real^2))
    (\<lambda>_ _. mat 1) 1 1 UNIV 0 (\<lambda>_. 1)"
  by (rule Brownian_market_sufficiently_volatile) simp_all

interpretation BM2: sufficiently_volatile_market
    "bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure"
    "natural_filtration bm_paths 0 (cbmX 0)" "cbmX (0 :: real^2)"
    "\<lambda>_ _. mat 1" 1 1 UNIV 0 "\<lambda>_. 1"
  by (rule sufficiently_volatile_market_nonvacuous)

text \<open>With the interpretation in place, the locale's martingale-problem
  identity --- an \<^emph>\<open>assumption\<close> there, here a proved consequence ---
  gives an unconditional fact: planar Brownian motion started at the
  origin has expected squared norm \<open>2\<close> at time \<open>1\<close>.\<close>

corollary bm2_expected_square:
  "(\<integral>\<omega>. cbmX (0 :: real^2) 1 \<omega> \<bullet> cbmX 0 1 \<omega>
      \<partial>(bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)) = 2"
proof -
  have comp: "set_lebesgue_integral lborel {0..(1 :: real)}
      (\<lambda>s. trace (mat 1 :: real^2^2)) = 2"
    by (subst bm_compensator_const) simp_all
  show ?thesis
    using BM2.dynkin_quadratic[of 1]
    by (simp add: BMP.prob_space comp)
qed

text \<open>The exit-time bound \<open>E[\<tau>] \<le> v(x0)\<close> of Example 3.1 is available
  as \<open>expected_exit_time_bound\<close>; a non-degenerate instance with
  \<open>K = cball 0 r\<close> needs the ball's first exit time, a genuine stopping
  time of the continuous modification.\<close>

section \<open>The process form of the martingale problem is inhabited\<close>

text \<open>Ito's formula for the test function \<open>|x|\<^sup>2\<close> is a theorem for the
  continuous Brownian motion (\<open>martingale_cbmX_square\<close>), and for
  \<open>acov = mat 1\<close> the process it is about is literally \<open>ito_Z\<close>.  Hence the
  continuous Brownian market with a deterministic horizon inhabits
  \<open>ito_const_horizon_market\<close>: every assumption of that locale is proved
  for this instance, so the exit-time bound of Lemma 2.1 follows from the
  martingale problem in process form with nothing assumed.\<close>

theorem Brownian_ito_const_horizon_market:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and c: "0 \<le> c"
    and K: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> cbmX x0 s \<omega> \<in> K"
  shows "ito_const_horizon_market
    (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
    (\<lambda>_ _. mat 1) k L K x0 c"
proof (intro ito_const_horizon_market.intro
    ito_const_horizon_market_axioms.intro)
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0 (cbmX x0)"
    by (rule martingale_cbmX)
  show "prob_space ?M" by simp
  show "1 \<le> k" "k < CARD('n)" "1 \<le> L" "0 \<le> c" by fact+
  show "AE \<omega> in ?M. cbmX x0 0 \<omega> = x0"
  proof -
    have "AE \<omega> in ?M. cbmX x0 0 \<omega> = bmX x0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    with bmX_start[of x0] show ?thesis
      by eventually_elim simp
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> cbmX x0 s \<omega> \<in> K"
    by (rule K)
  have psd1: "psd (mat 1 :: real^'n^'n)"
    by (simp add: psd_def)
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow> psd (mat 1 :: real^'n^'n)"
    using psd1 by simp
  have elb: "eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    unfolding eigen_lb_def
  proof (intro exI[of _ UNIV] conjI)
    show "subspace (UNIV :: (real^'n) set)" by simp
    show "CARD('n) - k \<le> dim (UNIV :: (real^'n) set)" by simp
    show "\<forall>x\<in>(UNIV :: (real^'n) set). x \<bullet> x \<le> x \<bullet> (mat 1 *v x)"
      by simp
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_lb (mat 1 :: real^'n^'n) (CARD('n) - k)"
    using elb by simp
  have eub: "eigen_ub (mat 1 :: real^'n^'n) L"
  proof -
    have "x \<bullet> x \<le> L * (x \<bullet> x)" for x :: "real^'n"
      using mult_right_mono[OF L inner_ge_zero] by simp
    then show ?thesis
      by (simp add: eigen_ub_def)
  qed
  show "AE \<omega> in ?M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> c \<longrightarrow>
      eigen_ub (mat 1 :: real^'n^'n) L"
    using eub by simp
  have ti: "set_integrable lborel {0..t}
      (\<lambda>s. trace (mat 1 :: real^'n^'n))" for t :: real
  proof -
    have "integrable lborel
        (\<lambda>s. indicator {0..t} s *\<^sub>R trace (mat 1 :: real^'n^'n))"
    proof (intro integrable_scaleR_left integrable_real_indicator)
      show "{0..t} \<in> sets lborel"
        unfolding sets_lborel
        by (intro borel_closed closed_atLeastAtMost)
      show "emeasure lborel {0..t} < \<infinity>"
        by (simp add: emeasure_lborel_Icc_eq)
    qed
    then show ?thesis
      unfolding set_integrable_def .
  qed
  show "AE \<omega> in ?M. set_borel_measurable lborel {0..}
      (\<lambda>s :: real. mat 1 :: real^'n^'n)"
    unfolding set_borel_measurable_def by (intro AE_I2) simp
  show "AE \<omega> in ?M. \<forall>t :: real. 0 \<le> t \<longrightarrow>
      set_integrable lborel {0..t} (\<lambda>s. trace (mat 1 :: real^'n^'n))"
    using ti by (intro AE_I2) blast
  have sq_ae: "AE \<omega> in ?M. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>
      = bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>" if t: "0 \<le> t" for t
  proof -
    have "AE \<omega> in ?M. cbmX x0 (min t c) \<omega> = bmX x0 (min t c) \<omega>"
      using t c by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  have sq_meas_b: "(\<lambda>\<omega>. bmX x0 (min t c) \<omega> \<bullet> bmX x0 (min t c) \<omega>)
      \<in> borel_measurable ?M" if t: "0 \<le> t" for t
    using t c by (intro borel_measurable_inner measurable_bmX) simp_all
  have sq_meas_c: "(\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)
      \<in> borel_measurable ?M" for t
    by (intro borel_measurable_inner measurable_cbmX)
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)"
  proof -
    fix t :: real assume t: "0 \<le> t"
    have u: "0 \<le> min t c" using t c by simp
    show "integrable ?M (\<lambda>\<omega>. cbmX x0 (min t c) \<omega> \<bullet> cbmX x0 (min t c) \<omega>)"
      using integrable_cong_AE[OF sq_meas_c sq_meas_b[OF t] sq_ae[OF t]]
        bmX_sq_integrable[OF u] by simp
  qed
  show "\<And>t. 0 \<le> t \<Longrightarrow> integrable ?M
      (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t c}
        (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (rule BMP.integrable_const)
  have Zeq: "ito_Z (cbmX x0) (\<lambda>_ _. mat 1 :: real^'n^'n)
      = (\<lambda>t \<omega>. cbmX x0 t \<omega> \<bullet> cbmX x0 t \<omega>
          - set_lebesgue_integral lborel {0..t}
              (\<lambda>s. trace (mat 1 :: real^'n^'n)))"
    by (intro ext) (simp add: ito_Z_def)
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0
      (ito_Z (cbmX x0) (\<lambda>_ _. mat 1))"
    unfolding Zeq by (rule martingale_cbmX_square)
  show "martingale ?M (natural_filtration ?M 0 (cbmX x0)) 0
      (coord_Z (cbmX x0) (\<lambda>_ _. mat 1) i)" for i
    unfolding coord_Z_def by (rule martingale_cbm_coord_square)
  show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. cbmX x0 s \<omega>)"
    by (rule cbmX_cont)
qed

text \<open>Specialised to the planar market with \<open>k = L = 1\<close>, horizon \<open>1\<close> and
  start \<open>0\<close>, the statement has no hypotheses at all.\<close>

theorem ito_const_horizon_market_nonvacuous:
  "ito_const_horizon_market
    (bm_paths :: (2 \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX 0)) (cbmX (0 :: real^2))
    (\<lambda>_ _. mat 1) 1 1 UNIV 0 1"
  by (rule Brownian_ito_const_horizon_market) simp_all


(*<*)
end
(*>*)
