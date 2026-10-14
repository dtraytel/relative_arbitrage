section \<open>Sampling a path law at a stopping time\<close>

(*<*)
theory Path_Law_Sampling
  imports
    "Continuous_Time_Martingales.Modification_Transfer" Path_Law_Pasting
begin

(*>*)

text \<open>What optional sampling looks like on the path space: the increment
  identity at the sampled time \<open>u \<or> \<theta>\<close>, the integrand it produces, and the
  clauses that survive the sampling.\<close>


subsection \<open>Events of the past at the sampled time\<close>

text \<open>A \<open>pcut i\<close>-set intersected with \<open>{\<theta> > i}\<close> is an \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<and>\<^sub> \<^sub>\<theta>\<^sub>)\<close>-set: below
  \<open>i\<close> the cut \<open>{i \<and> \<theta> \<le> t}\<close> forces \<open>\<theta> \<le> t < i\<close> and so meets \<open>{\<theta> > i}\<close> in
  nothing, while from \<open>i\<close> on the cut is everything and the set is already
  \<open>\<F>\<^sub>i\<close>-measurable.\<close>

lemma pcut_after_in_pre_sigma:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and B: "B \<in> sets (path_borel i :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}
      \<in> pre_sigma_of Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) (\<lambda>p'. min i (\<theta> p'))"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v)"
  let ?C = "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}"
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spQ])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that])
  have cutB: "pcut i -` B \<inter> space Q \<in> sets (?F i)"
    by (rule pcut_vimage_natural_filtration[OF i0 iT setsQ B])
  have evi: "{p' \<in> space Q. \<theta> p' \<le> i} \<in> sets (?F i)"
    unfolding FB spQ
    by (rule path_stopping_time_event_filtration[OF T0 st thM i0 iT])
  have QP: "?C \<in> sets Q"
  proof -
    have "sets (?F i) \<subseteq> sets Q"
      by (rule sets_natural_filtration_subset)
         (rule path_law_evaluation_measurable[OF setsQ])
    moreover have "?C = (pcut i -` B \<inter> space Q)
        - ((pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. \<theta> p' \<le> i})" by auto
    ultimately show ?thesis
      using cutB evi sets.Diff sets.Int by (metis (no_types, lifting) subsetD)
  qed
  show ?thesis
  proof (rule pre_sigma_ofI[OF QP])
    fix t :: real assume t: "0 \<le> t"
    show "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} \<in> sets (?F t)"
    proof (cases "i \<le> t")
      case True
      have "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} = ?C"
        using True by auto
      moreover have "?C \<in> sets (?F i)"
      proof -
        have "?C = (pcut i -` B \<inter> space Q)
            - ((pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. \<theta> p' \<le> i})" by auto
        then show ?thesis using cutB evi by (simp add: sets.Diff sets.Int)
      qed
      ultimately show ?thesis using mono[OF True] by auto
    next
      case False
      have "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} = {}"
        using False by auto
      then show ?thesis by simp
    qed
  qed
qed

text \<open>The stopped path, evaluated at a time \<open>r \<le> u\<close>, is \<open>\<F>\<^sub>u\<close>-measurable
  as a path point, with no componentwise decomposition.  The trick reads it off the \<open>u\<close>-cut
  rather than off the whole path: \<^const>\<open>pcut\<close> is measurable into the
  \<open>u\<close>-horizon space by the description of the natural filtration
  (@{thm [source] sets_natural_filtration_eq_pcut_vimage}), the truncated
  stopping time \<open>r \<and> \<theta>\<close> is \<open>\<F>\<^sub>u\<close>-measurable because \<open>{r \<and> \<theta> \<le> t}\<close> is
  either everything or \<open>{\<theta> \<le> t}\<close> with \<open>t < r\<close>, and
  @{thm [source] path_eval_at_measurable_time} joins the two.\<close>

lemma pstopped_eval_filtration:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and r0: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> \<omega> r)
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<le> T")
  case False
  then have "r \<notin> {0..T}" by simp
  then have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (simp add: pstopped_outside)
  then show ?thesis by simp
next
  case True
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?G = "natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v)"
  define u' where "u' = min u T"
  have u'0: "0 \<le> u'" using r0 ru True unfolding u'_def by simp
  have u'T: "u' \<le> T" unfolding u'_def by simp
  have u'u: "u' \<le> u" unfolding u'_def by simp
  have ru': "r \<le> u'" using ru True unfolding u'_def by simp
  have rmem: "r \<in> {0..T}" using r0 True by simp
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have spG: "space (?G v) = space P" for v
    unfolding natural_filtration_def by simp
  have nf: "?G v = natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_nonneg[OF st])
  let ?Bu = "(path_borel u' :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"

  \<comment> \<open>the truncated stopping time is measurable at level \<open>u'\<close>\<close>
  have gm: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). min r (\<theta> \<omega>)) \<in> borel_measurable (?G u')"
  proof (rule borel_measurableI_le)
    fix t :: real
    show "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} \<in> sets (?G u')"
    proof (cases "r \<le> t")
      case True
      have e: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} = space (?G u')"
        using True by auto
      show ?thesis unfolding e by (rule sets.top)
    next
      case False
      then have lt: "t < r" by simp
      show ?thesis
      proof (cases "0 \<le> t")
        case True
        have eqs: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t}
            = {\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}" using lt sp spG by auto
        have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}
            \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t)"
          by (rule path_stopping_time_event_filtration_all[OF T0 st thM True])
        then have inG: "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t} \<in> sets (?G t)" unfolding nf .
        have "sets (?G t) \<subseteq> sets (?G u')"
          using lt ru' by (intro sets_natural_filtration_mono) simp
        with inG show ?thesis unfolding eqs by blast
      next
        case False
        then have tneg: "t < 0" by simp
        have e: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} = {}"
        proof (rule equals0I)
          fix x :: "(real \<Rightarrow> 'a \<times> 'b)"
          assume "x \<in> {\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t}"
          then have le: "min r (\<theta> x) \<le> t" by blast
          have "0 \<le> min r (\<theta> x)" using r0 th0[of x] by simp
          with le tneg show False by simp
        qed
        show ?thesis unfolding e by simp
      qed
    qed
  qed

  \<comment> \<open>the \<open>u'\<close>-cut is measurable at level \<open>u'\<close>\<close>
  have cutP: "pcut u' \<in> P \<rightarrow>\<^sub>M ?Bu" by (rule pcut_measurable[OF u'0 u'T setsP])
  have cutm: "pcut u' \<in> ?G u' \<rightarrow>\<^sub>M ?Bu"
  proof (rule measurableI)
    fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" assume "\<omega> \<in> space (?G u')"
    then have "\<omega> \<in> space P" using spG by simp
    then show "pcut u' \<omega> \<in> space ?Bu" by (rule measurable_space[OF cutP])
  next
    fix A :: "((real \<Rightarrow> 'a \<times> 'b)) set" assume A: "A \<in> sets ?Bu"
    have "pcut u' -` A \<inter> space P \<in> sets (?G u')"
      unfolding sets_natural_filtration_eq_pcut_vimage[OF setsP u'0 u'T]
      using A by blast
    then show "pcut u' -` A \<inter> space (?G u') \<in> sets (?G u')"
      unfolding spG .
  qed

  have g0: "0 \<le> min r (\<theta> \<omega>)" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" using r0 th0[of \<omega>] by simp
  have gu: "min r (\<theta> \<omega>) \<le> u'" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" using ru' by simp
  have ev: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pcut u' \<omega> (min r (\<theta> \<omega>)))
      \<in> borel_measurable (?G u')"
    by (rule path_eval_at_measurable_time
        [where X = "pcut u'" and g = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). min r (\<theta> \<omega>)",
          OF u'0 cutm gm g0 gu])
  have same: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pcut u' \<omega> (min r (\<theta> \<omega>)))
      = (\<lambda>\<omega>. pstopped T \<theta> \<omega> r)"
  proof (rule ext)
    fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    have m: "min r (\<theta> \<omega>) \<in> {0..u'}" using g0[of \<omega>] gu[of \<omega>] by simp
    have "pcut u' \<omega> (min r (\<theta> \<omega>)) = \<omega> (min r (\<theta> \<omega>))" by (rule pcut_apply[OF m])
    also have "\<dots> = pstopped T \<theta> \<omega> r" by (rule pstopped_apply[OF rmem, symmetric])
    finally show "pcut u' \<omega> (min r (\<theta> \<omega>)) = pstopped T \<theta> \<omega> r" .
  qed
  have sub: "subalgebra (?G u) (?G u')"
    unfolding subalgebra_def using spG sets_natural_filtration_mono[OF u'u] by simp
  show ?thesis
    by (rule measurable_from_subalg[OF sub]) (use ev same in simp)
qed

subsection \<open>The inner-integral identity along the additive glue\<close>

text \<open>The engine behind the \<open>X\<close> and the compensated clause (iv), stated
  once for a continuous real functional \<open>F\<close> of the path value.  Along the
  additive glue \<open>F\<close> splits into its value on the past \<open>p'\<close> and a remainder
  \<open>\<Psi> u p' w\<close> that has mean zero under the continuation kernel and, on a
  past already stopped before \<open>i\<close>, the increment property against
  \<open>\<F>\<^sub>i\<close>: for \<open>F\<close> a coordinate of \<open>X\<close> the remainder is that coordinate of
  the continuation; for a compensated entry \<^const>\<open>outerp\<close> is quadratic
  and the remainder also carries two cross terms.  The outer integral then
  splits into \<open>{\<theta> \<le> i}\<close>, handled pointwise, and \<open>{\<theta> > i}\<close>, where
  optional sampling of the horizon martingale \<open>F (p' (min u T))\<close> closes it.\<close>

theorem aglue_inner_increment_F:
  fixes Q :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
    and \<Psi> :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) (\<lambda>u p'. F (p' (min u T))) T"
    and Fc: "continuous_on UNIV F"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and dec: "\<And>u p' w. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> F (padd T p' w (min u T)) = F (p' (min u T)) + \<Psi> u p' w"
    and \<Psi>int: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<Psi> u p')"
    and \<Psi>mean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. \<Psi> u p' w \<partial>(\<kappa> p')) = 0"
    and \<Psi>inc: "\<And>p' C. p' \<in> space Q \<Longrightarrow> pstopped T \<theta> p' = p' \<Longrightarrow> \<theta> p' \<le> i
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<Psi> i p')
        = set_lebesgue_integral (\<kappa> p') C (\<Psi> j p')"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * F (padd T p' w (min u T)) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * F (padd T p' w (min i T)) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * F (padd T p' w (min j T)) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Y = "\<lambda>u p' :: 'n pairpath. F (p' (min u T))"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * F (padd T p' w (min u T)) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
  have fcB: "F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF Fc])
  have Fm: "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> t)) \<in> borel_measurable ?B" for t
    by (rule measurable_compose[OF path_law_evaluation_measurable[OF refl] fcB])

  \<comment> \<open>the two pointwise halves\<close>
  have after: "?g u p' = indicator B (pcut i p') * ?Y u p'"
    if sp: "p' \<in> space Q" and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
    for p' u
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    have pdm: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> \<kappa> p' \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsK refl]
      by (rule padd_measurable_left[OF T0' pmem])
    have icm: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mL: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * F (padd T p' w (min u T))) \<in> borel_measurable (\<kappa> p')"
      using icm measurable_compose[OF pdm Fm] by simp
    have mR: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Y u p' + \<Psi> u p' w)) \<in> borel_measurable (\<kappa> p')"
      using borel_measurable_integrable[OF \<Psi>int[OF sp u0 uT]] by simp
    have cutAE: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Y u p' + \<Psi> u p' w) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mL mR])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * F (padd T p' w (min u T))
          = indicator B (pcut i p') * (?Y u p' + \<Psi> u p' w)"
        using cutAE by eventually_elim (simp add: dec[OF u0 uT])
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (?Y u p' + (\<integral>w. \<Psi> u p' w \<partial>(\<kappa> p')))"
      using Bochner_Integration.integral_add[OF PKi.integrable_const
        \<Psi>int[OF sp u0 uT]] by (simp add: PKi.prob_space)
    finally show ?thesis using \<Psi>mean[OF sp u0 uT] by simp
  qed

  have before: "?g j p' = ?g i p'"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'" and le: "\<theta> p' \<le> i"
    for p'
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    define C where "C = {w \<in> space (\<kappa> p'). pcut i (padd T p' w) \<in> B}"
    have Cf: "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)"
      unfolding C_def
      by (rule section_padd_in_filtration[OF i0 iT setsK pmem B])
    have CK: "C \<in> sets (\<kappa> p')"
    proof -
      have "sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w :: 'n pairpath. w s) i)
          \<subseteq> sets (\<kappa> p')"
        by (rule sets_natural_filtration_subset)
           (rule path_law_evaluation_measurable[OF setsK])
      then show ?thesis using Cf by blast
    qed
    have same: "?Y j p' = ?Y i p'"
    proof -
      have e1: "p' (min i T) = p' (min (min i T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' i0])
      have e2: "p' (min j T) = p' (min (min j T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' j0])
      have m1: "min (min i T) (\<theta> p') = \<theta> p'" using le iT th0[of p'] by simp
      have m2: "min (min j T) (\<theta> p') = \<theta> p'"
        using le ij jT th0[of p'] by simp
      show ?thesis using e1 e2 m1 m2 by simp
    qed
    have dec2: "?g u p' = ?Y u p' * measure (\<kappa> p') C
        + set_lebesgue_integral (\<kappa> p') C (\<Psi> u p')"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
      have i1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Y u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Y u p'"] by simp
      have i2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * \<Psi> u p' w)"
        using integrable_mult_indicator[OF CK \<Psi>int[OF sp u0 uT]] by simp
      have "?g u p' = (\<integral>w. indicator C w * ?Y u p'
          + indicator C w * \<Psi> u p' w \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: C_def dec[OF u0 uT] indicator_def)
      also have "\<dots> = (\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p'))
          + (\<integral>w. indicator C w * \<Psi> u p' w \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_add[OF i1 i2])
      also have "(\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p')) = ?Y u p' * measure (\<kappa> p') C"
        by (simp add: mult.commute Int_absorb2[OF Csub])
      finally show ?thesis unfolding set_lebesgue_integral_def by simp
    qed
    show ?thesis
      unfolding dec2[OF j0 jT] dec2[OF i0 iT] same
      using \<Psi>inc[OF sp idem le Cf] by simp
  qed
  \<comment> \<open>the outer split: pointwise on the complement, optional sampling on \<open>?E\<close>\<close>
  have si: "set_integrable Q S (?g u)"
    if "S \<in> sets Q" "0 \<le> u" "u \<le> T" for S u
    unfolding set_integrable_def
    by (rule integrable_mult_indicator[OF that(1) gint[OF that(2,3)]])
  have spint: "set_lebesgue_integral Q (space Q) (?g u) = (\<integral>p'. ?g u p' \<partial>Q)"
    if "0 \<le> u" "u \<le> T" for u
    by (rule set_integral_space[OF gint[OF that]])
  have Esplit: "(\<integral>p'. ?g u p' \<partial>Q)
      = set_lebesgue_integral Q ?E (?g u)
        + set_lebesgue_integral Q (space Q - ?E) (?g u)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have dis: "?E \<inter> (space Q - ?E) = {}" by auto
    have cm: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
    have un: "?E \<union> (space Q - ?E) = space Q" by auto
    have "set_lebesgue_integral Q (?E \<union> (space Q - ?E)) (?g u)
        = set_lebesgue_integral Q ?E (?g u)
          + set_lebesgue_integral Q (space Q - ?E) (?g u)"
      by (rule set_integral_Un[OF dis si[OF Emeas u0 uT] si[OF cm u0 uT]])
    then show ?thesis unfolding un spint[OF u0 uT] .
  qed
  have cmQ: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
  have compl: "set_lebesgue_integral Q (space Q - ?E) (?g j)
      = set_lebesgue_integral Q (space Q - ?E) (?g i)"
  proof (rule set_lebesgue_integral_cong_AE[OF cmQ])
    show "?g j \<in> borel_measurable Q"
      using gint[OF j0 jT] by (simp add: borel_measurable_integrable)
    show "?g i \<in> borel_measurable Q"
      using gint[OF i0 iT] by (simp add: borel_measurable_integrable)
    show "AE x \<in> (space Q - ?E) in Q. ?g j x = ?g i x"
      using Qst AE_space
    proof eventually_elim
      case (elim x)
      then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
      show "x \<in> space Q - ?E \<longrightarrow> ?g j x = ?g i x"
      proof
        assume "x \<in> space Q - ?E"
        then have le: "\<theta> x \<le> i" using sp by simp
        show "?g j x = ?g i x" by (rule before[OF sp idem le])
      qed
    qed
  qed
  have Epart: "set_lebesgue_integral Q ?E (?g j)
      = set_lebesgue_integral Q ?E (?g i)"
  proof -
    have rew: "set_lebesgue_integral Q ?E (?g u)
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y u)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix x assume x: "x \<in> space Q"
      show "indicator ?E x *\<^sub>R ?g u x = indicator (?D \<inter> ?E) x *\<^sub>R ?Y u x"
      proof (cases "x \<in> ?E")
        case True
        then have lt: "i < \<theta> x" by simp
        have gv: "?g u x = indicator B (pcut i x) * ?Y u x"
          by (rule after[OF x lt u0 uT])
        have iv: "indicator (?D \<inter> ?E) x = (indicator B (pcut i x) :: real)"
          using True x by (simp add: indicator_def)
        show ?thesis unfolding gv iv using True by simp
      next
        case False
        then have e1: "indicator ?E x = (0::real)" by simp
        have e2: "indicator (?D \<inter> ?E) x = (0::real)" using False by simp
        show ?thesis unfolding e1 e2 by simp
      qed
    qed
    have sti: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min i (\<theta> p'))"
      by (rule path_stopping_time_min[OF st i0 iT])
    have stj: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min j (\<theta> p'))"
      by (rule path_stopping_time_min[OF st j0 jT])
    have sMi: "(\<lambda>p' :: 'n pairpath. min i (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have sMj: "(\<lambda>p' :: 'n pairpath. min j (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have lemin: "min i (\<theta> p') \<le> min j (\<theta> p')" for p' :: "'n pairpath"
      using ij by simp
    have Cpre: "?D \<inter> ?E \<in> pre_sigma_of Q ?F (\<lambda>p'. min i (\<theta> p'))"
      by (rule pcut_after_in_pre_sigma[OF T0' setsQ st thM i0 iT B])
    have Ycont: "continuous_on {0..T} (\<lambda>s. ?Y s p')"
      if sp: "p' \<in> space Q" for p'
    proof -
      have "continuous_on {0..T} (\<lambda>s. F (p' s))"
        by (rule continuous_on_compose2[OF Fc Qcont[OF sp]]) simp
      then show ?thesis by (rule continuous_on_eq) simp
    qed
    have samp: "set_lebesgue_integral Q (?D \<inter> ?E)
          (\<lambda>p'. ?Y (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min j (\<theta> p')) p')"
      by (rule stopped_increment_of_horizon_gen
          [OF T0 setsQ QH Ycont sti sMi stj sMj lemin Cpre])
    have valE: "?Y (min u (\<theta> p')) p' = ?Y u p'"
      if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
        and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
        and ui: "i \<le> u" for p' u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u0])
      moreover have "min (min u (\<theta> p')) T = min (min u T) (\<theta> p')"
        using u0 uT th0[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have Yfix: "?Y v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule path_law_evaluation_measurable[OF setsQ])
      then show ?thesis by (rule measurable_compose[OF _ fcB])
    qed
    have Ym: "(\<lambda>p' :: 'n pairpath. ?Y (min v (\<theta> p')) p') \<in> borel_measurable Q"
      if v0: "0 \<le> v" for v
    proof -
      have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> Q \<rightarrow>\<^sub>M ?B"
        by (rule measurable_ident_sets[OF setsQ])
      have thQ: "\<theta> \<in> borel_measurable Q"
        using thM measurable_cong_sets[OF setsQ refl] by blast
      have gm: "(\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T) \<in> borel_measurable Q"
        using thQ by measurable
      have g0: "0 \<le> min (min v (\<theta> p')) T"
        if "p' \<in> space Q" for p' :: "'n pairpath"
        using v0 th0[of p'] T0' by simp
      have gT: "min (min v (\<theta> p')) T \<le> T"
        if "p' \<in> space Q" for p' :: "'n pairpath" by simp
      have ev: "(\<lambda>p' :: 'n pairpath. p' (min (min v (\<theta> p')) T))
          \<in> borel_measurable Q"
        by (rule path_eval_at_measurable_time
            [where X = "\<lambda>p' :: 'n pairpath. p'"
              and g = "\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T",
              OF T0' idm gm g0 gT])
      show ?thesis by (rule measurable_compose[OF ev fcB])
    qed
    have e1: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y i)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Ym[OF i0] Yfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Y (min i (\<theta> x)) x = ?Y i x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Y (min i (\<theta> x)) x = ?Y i x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Y (min i (\<theta> x)) x = ?Y i x"
            by (rule valE[OF sp idem lt i0 iT order.refl])
        qed
      qed
    qed
    have e2: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min j (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y j)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Ym[OF j0] Yfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Y (min j (\<theta> x)) x = ?Y j x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Y (min j (\<theta> x)) x = ?Y j x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Y (min j (\<theta> x)) x = ?Y j x"
            by (rule valE[OF sp idem lt j0 jT ij])
        qed
      qed
    qed
    show ?thesis
      unfolding rew[OF i0 iT] rew[OF j0 jT]
      using samp e1 e2 by simp
  qed
  show ?thesis
    unfolding Esplit[OF i0 iT] Esplit[OF j0 jT]
    using compl Epart by simp
qed

subsection \<open>Clause (iv) for the glued law\<close>

text \<open>The martingale property of \<open>F (\<omega> (min u T))\<close> under the glued law.
  @{thm [source] sets_natural_filtration_eq_pcut_vimage} presents the
  conditioning set as a \<^const>\<open>pcut\<close>-preimage,
  @{thm [source] integral_aglue_law} carries the set integral to the past
  and the continuation, and there @{thm [source] aglue_inner_increment_F}
  closes it; \<open>martingale_of_set_integral_eq\<close> turns the identity into the
  martingale property.  Past the horizon the process is constant, so an
  index above \<open>T\<close> is pulled back to \<open>T\<close> first.\<close>

theorem aglue_law_F_martingale:
  fixes Q :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
    and \<Psi> :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) (\<lambda>u p'. F (p' (min u T))) T"
    and Fc: "continuous_on UNIV F"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and dec: "\<And>u p' w. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> F (padd T p' w (min u T)) = F (p' (min u T)) + \<Psi> u p' w"
    and \<Psi>int: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<Psi> u p')"
    and \<Psi>mean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. \<Psi> u p' w \<partial>(\<kappa> p')) = 0"
    and \<Psi>inc: "\<And>p' C i j. p' \<in> space Q \<Longrightarrow> pstopped T \<theta> p' = p'
      \<Longrightarrow> \<theta> p' \<le> i \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> j \<le> T
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<Psi> i p')
        = set_lebesgue_integral (\<kappa> p') C (\<Psi> j p')"
    and Rint: "\<And>u. 0 \<le> u
      \<Longrightarrow> integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. F (\<omega> (min u T)))"
    and msec: "\<And>A u. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * F (padd T p' w (min u T)) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * F (padd T p' w (min u T)) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. F (\<omega> (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. F (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_process_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule path_law_evaluation_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have fcB: "F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF Fc])
  have Xm: "?X u \<in> borel_measurable ?B" for u
    by (rule measurable_compose[OF path_law_evaluation_measurable[OF refl] fcB])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      by (rule natural_filtration_eval) (use u T0' in auto)
    then show ?thesis by (rule measurable_compose[OF _ fcB])
  qed
  \<comment> \<open>the increment identity, transported to the past and the continuation\<close>
  have incr: "set_lebesgue_integral ?R A (?X i) = set_lebesgue_integral ?R A (?X j)"
    if i0: "0 \<le> i" and ij: "i \<le> j" and jT: "j \<le> T" and A: "A \<in> sets (?G i)"
    for A i j
  proof -
    have iT: "i \<le> T" using ij jT by simp
    have j0: "0 \<le> j" using i0 ij by simp
    obtain B where B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
      and Aeq: "A = pcut i -` B \<inter> space ?R"
      using A unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT]
      by blast
    have AR: "A \<in> sets ?R" using A SF.sets_F_subset[OF i0] by blast
    have AB: "A \<in> sets ?B" using AR setsR by simp
    have tr: "set_lebesgue_integral ?R A (?X u)
        = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * F (padd T p' w (min u T)) \<partial>(\<kappa> p')) \<partial>Q)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * ?X u \<omega>) \<in> borel_measurable ?B"
        using AB Xm[of u] by measurable
      have hi: "integrable ?R (\<lambda>\<omega>. indicator A \<omega> * ?X u \<omega>)"
        using integrable_mult_indicator[OF AR Rint[OF u0]] by simp
      have "set_lebesgue_integral ?R A (?X u) = (\<integral>\<omega>. indicator A \<omega> * ?X u \<omega> \<partial>?R)"
        unfolding set_lebesgue_integral_def by simp
      also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
          * F (padd T p' w (min u T)) \<partial>(\<kappa> p')) \<partial>Q)"
        by (rule integral_aglue_law[OF T0' PQ setsQ Kp hm hi msec[OF AR u0 uT]])
      also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * F (padd T p' w (min u T)) \<partial>(\<kappa> p')) \<partial>Q)"
      proof (intro Bochner_Integration.integral_cong refl)
        fix p' w assume sp: "p' \<in> space Q" and sw: "w \<in> space (\<kappa> p')"
        have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sp spQ by (simp add: space_borel_of)
        have spK: "space (\<kappa> p') = space ?B"
          by (rule sets_eq_imp_space_eq[OF ksemi_sets_kernel(1)[OF Kp sp]])
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        then show "indicator A (padd T p' w) * F (padd T p' w (min u T))
            = indicator B (pcut i (padd T p' w)) * F (padd T p' w (min u T))"
          unfolding Aeq by (simp add: indicator_def)
      qed
      finally show ?thesis .
    qed
    show ?thesis
      unfolding tr[OF i0 iT] tr[OF j0 jT]
      by (rule aglue_inner_increment_F
          [OF T0 PQ setsQ Kp st thM Qst QH Fc Qcont Kfr dec \<Psi>int \<Psi>mean
            \<Psi>inc[OF _ _ _ i0 ij jT] i0 ij iT jT B gint[OF _ _ B i0 iT]])
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule Rint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      have "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X (min v T))"
        by (rule incr[OF uv(1) _ _ C]) (use uv False in simp_all)
      then show ?thesis by simp
    qed
  qed
qed

theorem aglue_law_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "\<And>c. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u c. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u c. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v c. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and RXint: "\<And>u. 0 \<le> u
      \<Longrightarrow> integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
    and msec: "\<And>A u c. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB c i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
proof (rule martingale_vecI)
  fix c :: 'n
  have Fc: "continuous_on UNIV (\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)"
    by (intro continuous_intros)
  have dec: "fst (padd T p' w (min u T)) $ c = fst (p' (min u T)) $ c + fst (w (min u T)) $ c"
    if "0 \<le> u" "u \<le> T" for u p' w using that by (simp add: padd_apply)
  have inc: "set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min i T)) $ c)
      = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min j T)) $ c)"
    if "p' \<in> space Q" "pstopped T \<theta> p' = p'" "\<theta> p' \<le> i" "0 \<le> i" "i \<le> j" "j \<le> T"
      "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)" for p' C i j
    by (rule Kinc[OF that(1,7,4,5,6)])
  have Rint: "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)" if "0 \<le> u" for u
    by (rule integrable_bounded_linear[OF bounded_linear_vec_nth RXint[OF that]])
  show "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ c)"
    by (rule aglue_law_F_martingale[where F = "\<lambda>z. fst z $ c"
          and \<Psi> = "\<lambda>u p' w. fst (w (min u T)) $ c",
          OF T0 PQ setsQ Kp st thM Qst QH Fc Qcont Kfr dec Kint Kmean inc Rint
            msec gint])
qed

theorem aglue_law_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "\<And>c d. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v c d. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and RCint: "\<And>u. 0 \<le> u \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    and msec: "\<And>A u c d. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gint: "\<And>u BB c d i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof (rule martingale_matI)
  fix c d :: 'n
  \<comment> \<open>the compensated entry along the glue: a past entry, a continuation
      entry and two cross terms, whose past factor is constant under \<open>\<kappa> p'\<close>\<close>
  let ?Z = "\<lambda>u w :: 'n pairpath. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d"
  let ?x = "\<lambda>e u w :: 'n pairpath. fst (w (min u T)) $ e"
  let ?\<Psi> = "\<lambda>u p' w. ?Z u w + (?x c u p' * ?x d u w + ?x c u w * ?x d u p')"
  have dec: "?Z u (padd T p' w) = ?Z u p' + ?\<Psi> u p' w" if "0 \<le> u" "u \<le> T" for u p' w
  proof -
    have m: "min u T \<in> {0..T}" using that by simp
    show ?thesis unfolding padd_apply[OF m] by (simp add: outerp_def algebra_simps)
  qed
  have ints: "integrable (\<kappa> p') (?Z u)" "integrable (\<kappa> p') (\<lambda>w. ?x c u p' * ?x d u w)"
    "integrable (\<kappa> p') (\<lambda>w. ?x c u w * ?x d u p')"
    if "p' \<in> space Q" "0 \<le> u" "u \<le> T" for p' u
    using KintC[OF that] Kint[OF that] by auto
  have \<Psi>int: "integrable (\<kappa> p') (?\<Psi> u p')" if "p' \<in> space Q" "0 \<le> u" "u \<le> T" for p' u
    using ints[OF that] by auto
  have \<Psi>mean: "(\<integral>w. ?\<Psi> u p' w \<partial>(\<kappa> p')) = 0"
    if "p' \<in> space Q" "0 \<le> u" "u \<le> T" for p' u
    using ints[OF that] KmeanC[OF that] Kmean[OF that] by simp
  have \<Psi>inc: "set_lebesgue_integral (\<kappa> p') C (?\<Psi> i p')
      = set_lebesgue_integral (\<kappa> p') C (?\<Psi> j p')"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'" and le: "\<theta> p' \<le> i"
      and i0: "0 \<le> i" and ij: "i \<le> j" and jT: "j \<le> T"
      and C: "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)" for p' C i j
  proof -
    have sK: "sets (\<kappa> p') = sets (path_borel T :: ('n pairpath) measure)"
      by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have "sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w :: 'n pairpath. w s) i)
        \<subseteq> sets (\<kappa> p')"
      by (rule sets_natural_filtration_subset) (rule path_law_evaluation_measurable[OF sK])
    then have CK: "C \<in> sets (\<kappa> p')" using C by blast
    have same: "p' (min j T) = p' (min i T)"
    proof -
      have "p' (min u T) = p' (\<theta> p')" if "0 \<le> u" "i \<le> u" for u
      proof -
        have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
          by (rule pstopped_eval_min[OF st idem less_imp_le[OF T0] that(1)])
        also have "min (min u T) (\<theta> p') = \<theta> p'"
          using le that path_stopping_time_le[OF st, of p'] by simp
        finally show ?thesis .
      qed
      from this[OF i0 order_refl] this[OF order_trans[OF i0 ij] ij] show ?thesis
        by simp
    qed
    have si: "set_integrable (\<kappa> p') C f" if "integrable (\<kappa> p') f" for f :: "_ \<Rightarrow> real"
      unfolding set_integrable_def using integrable_mult_indicator[OF CK that] .
    have sdec: "set_lebesgue_integral (\<kappa> p') C (?\<Psi> u p')
        = set_lebesgue_integral (\<kappa> p') C (?Z u)
          + (?x c u p' * set_lebesgue_integral (\<kappa> p') C (?x d u)
             + set_lebesgue_integral (\<kappa> p') C (?x c u) * ?x d u p')"
      if "0 \<le> u" "u \<le> T" for u
      using si[OF ints(1)[OF sp that]] si[OF ints(2)[OF sp that]] si[OF ints(3)[OF sp that]]
      by (simp add: set_integral_add)
    show ?thesis
      unfolding sdec[OF i0 order_trans[OF ij jT]] sdec[OF order_trans[OF i0 ij] jT]
      unfolding KincC[OF sp C i0 ij jT] Kinc[OF sp C i0 ij jT] same ..
  qed
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  have Rint: "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. ?Z u \<omega>)" if "0 \<le> u" for u
    by (rule integrable_bounded_linear[OF bl RCint[OF that]])
  show "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)"
    by (rule aglue_law_F_martingale[where F = "\<lambda>z. (outerp (fst z) - snd z) $ c $ d"
          and \<Psi> = ?\<Psi>, OF T0 PQ setsQ Kp st thM Qst QHC comp_entry_cont Qcont Kfr
            dec \<Psi>int \<Psi>mean \<Psi>inc Rint msec gint])
qed

subsection \<open>Past and future events in the natural filtration\<close>

lemma pfut_vimage_natural_filtration:
  fixes P :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure)) 0 (\<lambda>v w. w v) i)"
  shows "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  let ?Y = "(path_borel (T - r) :: (real \<Rightarrow> 'p) measure)"
  have sp: "space (process_law (T - r) (pfut r T) P) = space ?Y"
    by (simp add: space_process_law space_borel_of)
  have nfeq: "natural_filtration (process_law (T - r) (pfut r T) P) 0
        (\<lambda>v w :: (real \<Rightarrow> 'p). w v) i
      = natural_filtration ?Y 0 (\<lambda>v w. w v) i"
    by (rule natural_filtration_cong_space[OF sp])
  have AQ: "A' \<in> sets (natural_filtration (process_law (T - r) (pfut r T) P) 0
      (\<lambda>v w :: (real \<Rightarrow> 'p). w v) i)"
    unfolding nfeq using A' .
  have m: "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) (r + min i (T - r))
        \<rightarrow>\<^sub>M natural_filtration (process_law (T - r) (pfut r T) P) 0
            (\<lambda>v w. w v) i"
    by (rule pfut_filtration_measurable[OF r rT setsP])
  have mm: "min i (T - r) = i" using iS by simp
  have "pfut r T -` A' \<inter> space (natural_filtration P 0
      (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) (r + i))
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
    using measurable_sets[OF m AQ] unfolding mm .
  then show ?thesis by simp
qed

lemma rect_vimage_natural_filtration:
  fixes P :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A: "A \<in> sets (path_borel r :: (real \<Rightarrow> 'p) measure)"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure)) 0 (\<lambda>v w. w v) i)"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  have c1: "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) r)"
    by (rule pcut_vimage_natural_filtration[OF r rT setsP A])
  have c1': "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) (r + i))"
    using c1 sets_natural_filtration_mono[of r "r + i"] i by auto
  have c2: "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) (r + i))"
    by (rule pfut_vimage_natural_filtration[OF r rT setsP i iS A'])
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      = (pcut r -` A \<inter> space P) \<inter> (pfut r T -` A' \<inter> space P)" by auto
  then show ?thesis using sets.Int[OF c1' c2] by simp
qed


subsection \<open>The martingale increment vanishes under the kernel\<close>

text \<open>The per-\<open>(i,j,A')\<close> statement, for a real functional \<open>F\<close> of the
  rebased future whose shifted process \<open>F (pfut r T \<omega> u)\<close> has the
  martingale increment property under \<open>P\<close> in \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>u\<^sub>)\<close>.  It is chained
  as follows: @{thm [source] AE_kernel_integral_zero} reduces the
  almost-sure vanishing of the kernel integral to the vanishing of every
  rectangle integral; @{thm [source] integral_ksemi_rect_of_set_integral}
  turns each rectangle integral into a set integral over \<open>P\<close>; @{thm [source]
  rect_vimage_natural_filtration} puts that set into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>; and there
  the increment property closes it, with integrability from @{thm [source]
  integrable_ksemi_of_distr_rect} and @{thm [source]
  integrable_kernel_integral}.  The statement is real-valued, since the
  workhorse @{thm [source] AE_zero_of_set_integral_zero} is.\<close>

lemma pfut_rcd_F_increment_zero:
  fixes P :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and F :: "'p \<Rightarrow> real"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: (real \<Rightarrow> 'p) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure))"
    and eq: "distr P
          ((path_borel r :: (real \<Rightarrow> 'p) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: (real \<Rightarrow> 'p) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (process_law r (pcut r) P)
            ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure)) \<kappa>"
    and Fb: "F \<in> borel_measurable borel"
    and Pint: "\<And>u. u \<in> {0..T - r} \<Longrightarrow> integrable P (\<lambda>\<omega>. F (pfut r T \<omega> u))"
    and Pinc: "\<And>C u v. C \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + u))
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T - r
      \<Longrightarrow> set_lebesgue_integral P C (\<lambda>\<omega>. F (pfut r T \<omega> u))
        = set_lebesgue_integral P C (\<lambda>\<omega>. F (pfut r T \<omega> v))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure)) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in process_law r (pcut r) P.
      (\<integral>w. indicator A' w * (F (w j) - F (w i)) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "(path_borel r :: (real \<Rightarrow> 'p) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: (real \<Rightarrow> 'p) measure)"
  let ?Q = "process_law r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: (real \<Rightarrow> 'p). (pcut r \<omega>, pfut r T \<omega>)"
  let ?h = "\<lambda>w :: (real \<Rightarrow> 'p). F (w j) - F (w i)"
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding process_law_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_process_law)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have A'Y: "A' \<in> sets ?Y"
    using A' sets_natural_filtration_path_subset[of ?S i] by blast

  \<comment> \<open>transport \<open>eq\<close> from the Borel algebra to the cut law, which have the
      same sets but are different terms\<close>
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast

  \<comment> \<open>the integrand and its integrability under \<open>P\<close>\<close>
  have Fm: "(\<lambda>w :: (real \<Rightarrow> 'p). F (w u)) \<in> borel_measurable ?Y" for u
    by (rule measurable_compose[OF path_law_evaluation_measurable[OF refl] Fb])
  have hm: "?h \<in> borel_measurable ?Y" using Fm by measurable
  have hi: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'p). ?h (snd (?\<phi> \<omega>)))"
    using Bochner_Integration.integrable_diff[OF Pint[OF j0S] Pint[OF i0S]] by simp
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). ?h (snd p))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
      by (rule measurable_compose[OF measurable_snd hm])
    have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) (\<lambda>p. ?h (snd p))"
      unfolding integrable_distr_eq[OF mphi' hm2] by (rule hi)
    then show ?thesis unfolding eq' .
  qed

  \<comment> \<open>the three hypotheses of @{thm [source] AE_kernel_integral_zero}\<close>
  have gi: "integrable (ksemi ?Q ?Y \<kappa>)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p)))"
    if A: "A \<in> sets ?Q" for A
    by (rule integrable_ksemi_of_distr_rect[OF eq'[symmetric] mphi' hm A A'Y])
       (use hi in simp)
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    let ?S' = "?\<phi> -` (A \<times> A') \<inter> space P"
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?S' \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) (r + i))"
      by (rule rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'])
    have "sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'p). \<omega> v) (r + i))
        \<subseteq> sets P"
      by (rule sets_natural_filtration_subset) (rule path_law_evaluation_measurable[OF setsP])
    then have SP: "?S' \<in> sets P" using Sfilt by blast
    have si: "set_integrable P ?S' (\<lambda>\<omega> :: (real \<Rightarrow> 'p). F (pfut r T \<omega> u))"
      if u: "u \<in> {0..?S}" for u
      unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP Pint[OF u]])
    have "set_lebesgue_integral P ?S' (\<lambda>\<omega> :: (real \<Rightarrow> 'p). ?h (snd (?\<phi> \<omega>)))
        = set_lebesgue_integral P ?S' (\<lambda>\<omega>. F (pfut r T \<omega> j))
          - set_lebesgue_integral P ?S' (\<lambda>\<omega>. F (pfut r T \<omega> i))"
      using set_integral_diff(2)[OF si[OF j0S] si[OF i0S]] by simp
    also have "\<dots> = 0" using Pinc[OF Sfilt i0 ij jS] by simp
    finally have zero: "set_lebesgue_integral P ?S'
        (\<lambda>\<omega> :: (real \<Rightarrow> 'p). ?h (snd (?\<phi> \<omega>))) = 0" .
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

text \<open>The other hypothesis of
  \<open>sigma_finite_filtered_measure.martingale_of_set_integral_eq\<close>
  wants: the functional is \<open>\<kappa> p'\<close>-integrable at almost every \<open>p'\<close>.
  This needs no filtration at all --- only that the section of a
  \<open>ksemi\<close>-integrable function is almost surely integrable, which is
  @{thm [source] AE_integrable_ksemi_section}.\<close>

lemma pfut_rcd_F_integrable:
  fixes P :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and F :: "'p \<Rightarrow> real"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: (real \<Rightarrow> 'p) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure))"
    and eq: "distr P
          ((path_borel r :: (real \<Rightarrow> 'p) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: (real \<Rightarrow> 'p) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (process_law r (pcut r) P)
            ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure)) \<kappa>"
    and Fb: "F \<in> borel_measurable borel"
    and Pint: "integrable P (\<lambda>\<omega>. F (pfut r T \<omega> u))"
  shows "AE p' in process_law r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w u))"
proof -
  let ?X = "(path_borel r :: (real \<Rightarrow> 'p) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: (real \<Rightarrow> 'p) measure)"
  let ?Q = "process_law r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: (real \<Rightarrow> 'p). (pcut r \<omega>, pfut r T \<omega>)"
  let ?g = "\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). F (snd p u)"
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding process_law_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_process_law)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd
        measurable_compose[OF path_law_evaluation_measurable[OF refl] Fb]])
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] using Pint by simp
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

subsection \<open>Integrability under the additive glue\<close>

text \<open>Integrability under the glued law, for a functional \<open>H\<close> of the path value
  whose norm along the glue is bounded by a \<open>Q\<close>-integrable term of the past
  plus a term of the continuation with \<open>Q\<close>-integrably bounded \<open>\<kappa> p'\<close>-mean:
  the bound has the shape @{thm [source] integrable_ksemi_of_past_bound} was
  written for.\<close>

lemma aglue_law_integrable_of_bound:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and H :: "'p \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and Hb: "H \<in> borel_measurable borel"
    and dom: "\<And>p' w. norm (H (padd T p' w t)) \<le> a p' + G p' w"
    and aint: "integrable Q a" and bint: "integrable Q b"
    and Gint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p') (G p')"
    and Gbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w. G p' w \<partial>(\<kappa> p')) \<le> b p'"
  shows "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. H (\<omega> t))"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  let ?S = "ksemi Q ?B \<kappa>"
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pmP: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have pm: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using pmP measurable_cong_sets[OF setsS refl] by blast
  have hb: "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). H (\<omega> t)) \<in> borel_measurable ?B"
    by (rule measurable_compose[OF path_law_evaluation_measurable[OF refl] Hb])
  have gm: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p).
      H (padd T (fst p) (snd p) t)) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (H (padd T (fst (p', w)) (snd (p', w)) t))) \<partial>(\<kappa> p'))
      \<le> ennreal (a p' + b p')"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have iB: "integrable (\<kappa> p') (\<lambda>w. a p' + G p' w)"
      by (rule Bochner_Integration.integrable_add[OF PK.integrable_const Gint[OF sp]])
    have mP: "(\<lambda>w. norm (H (padd T p' w t))) \<in> borel_measurable (\<kappa> p')"
    proof -
      have "(\<lambda>w :: (real \<Rightarrow> 'p). padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
        by (rule padd_measurable_left[OF T0])
           (use sp space_of_path_sets[OF setsQ] in simp)
      from measurable_compose[OF this hb]
      have "(\<lambda>w :: (real \<Rightarrow> 'p). H (padd T p' w t)) \<in> borel_measurable (\<kappa> p')"
        using measurable_cong_sets[OF sK refl] by blast
      then show ?thesis by measurable
    qed
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (H (padd T p' w t)))"
      by (rule Bochner_Integration.integrable_bound[OF iB mP])
         (rule AE_I2, simp, rule order_trans[OF dom abs_ge_self])
    have "(\<integral>w. norm (H (padd T p' w t)) \<partial>(\<kappa> p')) \<le> (\<integral>w. a p' + G p' w \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono[OF iP iB dom])
    also have "\<dots> = a p' + (\<integral>w. G p' w \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PK.integrable_const Gint[OF sp]]
      by (simp add: PK.prob_space)
    also have "\<dots> \<le> a p' + b p'" using Gbnd[OF sp] by simp
    finally have le: "(\<integral>w. norm (H (padd T p' w t)) \<partial>(\<kappa> p')) \<le> a p' + b p'" .
    have "(\<integral>\<^sup>+w. ennreal (norm (H (padd T p' w t))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (H (padd T p' w t)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (a p' + b p')" using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. H (padd T (fst p) (snd p) t))"
    by (rule integrable_ksemi_of_past_bound
        [OF Kp ne gm Bochner_Integration.integrable_add[OF aint bint]])
       (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. H (\<omega> t))
      = integrable ?S (\<lambda>p. H (padd T (fst p) (snd p) t))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

lemma aglue_law_X_integrable:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
  shows "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
proof -
  interpret PQ': prob_space Q by (rule PQ)
  have tm: "min u T \<in> {0..T}" using u T0 by simp
  have dom: "norm (fst (padd T p' w (min u T)))
      \<le> norm (fst (p' (min u T))) + norm (fst (w (min u T)))"
    for p' w :: "real \<Rightarrow> 'a \<times> 'b"
    unfolding padd_eval_split(1)[OF tm] by (rule norm_triangle_ineq)
  show ?thesis
    by (rule aglue_law_integrable_of_bound[OF T0 PQ setsQ Kp pair_fst_borel dom
          integrable_norm[OF QXint] PQ'.integrable_const integrable_norm[OF KXint] KXbnd])
qed

text \<open>For the compensated process \<^const>\<open>outerp\<close> is quadratic, so the glued
  entry is not the sum of the two factors': @{thm [source] padd_comp_norm_le}
  bounds it by the two entries and two cross terms, and the past factor of
  the cross terms pulls out of the inner integral.\<close>

lemma aglue_law_comp_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and QCint: "integrable Q
      (\<lambda>p'. outerp (fst (p' (min u T))) - snd (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KCint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. outerp (fst (w (min u T))) - snd (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
    and KCbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w.
      norm (outerp (fst (w (min u T))) - snd (w (min u T))) \<partial>(\<kappa> p')) \<le> CC"
  shows "integrable (aglue_law T \<kappa> Q)
      (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof -
  let ?t = "min u T"
  let ?C = "\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z"
  let ?G = "\<lambda>p' w :: 'n pairpath. norm (?C (w ?t))
      + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t)))"
  interpret PQ': prob_space Q by (rule PQ)
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have dom: "norm (?C (padd T p' w ?t)) \<le> norm (?C (p' ?t)) + ?G p' w" for p' w
    using padd_comp_norm_le[OF tm, of p' w] by (simp add: add.assoc)
  have Gint: "integrable (\<kappa> p') (?G p')" if "p' \<in> space Q" for p'
    using integrable_norm[OF KCint[OF that]] integrable_norm[OF KXint[OF that]] by simp
  have Gbnd: "(\<integral>w. ?G p' w \<partial>(\<kappa> p')) \<le> CC + 2 * (norm (fst (p' ?t)) * CX)"
    if sp: "p' \<in> space Q" for p'
    using integrable_norm[OF KCint[OF sp]] integrable_norm[OF KXint[OF sp]]
      KCbnd[OF sp] mult_left_mono[OF KXbnd[OF sp] norm_ge_zero, of "fst (p' ?t)"]
    by simp
  show ?thesis
    by (rule aglue_law_integrable_of_bound[OF T0 PQ setsQ Kp compensated_map_borel dom
          integrable_norm[OF QCint] _ Gint Gbnd])
       (intro Bochner_Integration.integrable_add PQ'.integrable_const
          Bochner_Integration.integrable_mult_right integrable_mult_left
          integrable_norm[OF QXint])
qed

subsection \<open>\<open>msecX\<close> and \<open>msecC\<close>\<close>

text \<open>One generic lemma covers both, and \<open>gintX\<close>/\<open>gintC\<close> too: the
  conditioning factor enters only through being measurable and bounded by
  \<open>1\<close> --- an \<open>indicator\<close> for \<open>msec\<close>, an indicator composed with
  \<^const>\<open>pcut\<close> for \<open>gint\<close>.\<close>

lemma aglue_section_int_at:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and h cc :: "(real \<Rightarrow> 'p) \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and sp: "p' \<in> space Q"
  shows "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
proof (rule Bochner_Integration.integrable_bound[OF Kint])
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
  have pl: "(\<lambda>w :: (real \<Rightarrow> 'p). padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule padd_measurable_left[OF T0])
       (use sp space_of_path_sets[OF setsQ] in simp)
  have "(\<lambda>w :: (real \<Rightarrow> 'p). cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable ?B"
    using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
  then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable (\<kappa> p')"
    using measurable_cong_sets[OF sK refl] by blast
next
  show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
      \<le> norm (h (padd T p' w))"
    by (intro AE_I2) (simp add: abs_mult mult_left_le_one_le c1)
qed

lemma aglue_section_measurable:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and h cc :: "(real \<Rightarrow> 'p) \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
  shows "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  have pmP: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have gm: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p).
      cc (padd T (fst p) (snd p)) * h (padd T (fst p) (snd p)))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    using measurable_compose[OF pmP cb] measurable_compose[OF pmP hb] by simp
  have gi: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
    if sp: "p' \<in> space Q" for p'
    by (rule aglue_section_int_at[OF T0 setsQ Kp hb cb c1 Kint[OF sp] sp])
  show ?thesis
    by (rule integral_kernel_measurable
        [where g = "\<lambda>p' w. cc (padd T p' w) * h (padd T p' w)", OF Kp gm gi])
qed

corollary aglue_msec_X:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and A: "A \<in> sets (aglue_law T \<kappa> Q)"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
  shows "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
      * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have AB: "A \<in> sets ?B" using A by (simp add: sets_process_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e)
      \<in> borel_measurable ?B"
    by (rule X_eval_entry_measurable)
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

text \<open>\<open>gintX\<close>/\<open>gintC\<close>: the same section integral, now integrable in the
  past.  Bounded by \<open>1\<close>, the conditioning factor cannot enlarge the inner
  integral, so the past bound that already served \<open>RXint\<close>/\<open>RCint\<close> serves
  here too.\<close>

lemma aglue_section_integrable:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and h cc HB :: "(real \<Rightarrow> 'p) \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. \<bar>h (padd T p' w)\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))"
proof -
  have m: "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF HBi m])
    show "AE p' in Q. norm (\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
        \<le> norm (HB p')"
    proof (rule eventually_mono[OF AE_space])
      fix p' :: "(real \<Rightarrow> 'p)" assume sp: "p' \<in> space Q"
      have iH: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))" by (rule Kint[OF sp])
      have iA: "integrable (\<kappa> p') (\<lambda>w. \<bar>h (padd T p' w)\<bar>)"
        using iH by simp
      have iCH: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
        by (rule aglue_section_int_at[OF T0 setsQ Kp hb cb c1 iH sp])
      have "\<bar>\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p')\<bar>
          \<le> (\<integral>w. \<bar>cc (padd T p' w) * h (padd T p' w)\<bar> \<partial>(\<kappa> p'))"
        by (rule integral_abs_bound)
      also have "\<dots> \<le> (\<integral>w. \<bar>h (padd T p' w)\<bar> \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_mono[OF _ iA])
        show "integrable (\<kappa> p') (\<lambda>w. \<bar>cc (padd T p' w) * h (padd T p' w)\<bar>)"
          using iCH by simp
        show "\<bar>cc (padd T p' w) * h (padd T p' w)\<bar>
            \<le> \<bar>h (padd T p' w)\<bar>" for w :: "(real \<Rightarrow> 'p)"
          by (simp add: abs_mult mult_left_le_one_le c1)
      qed
      also have "\<dots> \<le> HB p'" by (rule Kbnd[OF sp])
      finally show "norm (\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
          \<le> norm (HB p')" by simp
    qed
  qed
qed

corollary aglue_msec_C:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and A: "A \<in> sets (aglue_law T \<kappa> Q)"
    and Kint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
  shows "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
      * ((outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have AB: "A \<in> sets ?B" using A by (simp add: sets_process_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
    by (rule comp_eval_entry_measurable)
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

subsection \<open>\<open>gintX\<close> and \<open>gintC\<close>\<close>

corollary aglue_gint_X:
  fixes Q :: "('n::finite pairpath) measure" and HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and BB: "BB \<in> sets (path_borel i :: ('n pairpath) measure)"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. \<bar>fst (padd T p' w (min u T)) $ e\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
      * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p'))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  have cb: "(\<lambda>x :: 'n pairpath. indicator BB (pcut i x) :: real)
      \<in> borel_measurable ?B"
  proof -
    have pc: "pcut i \<in> ?B \<rightarrow>\<^sub>M ?Bi" by (rule pcut_measurable[OF i0 iT refl])
    have ib: "(\<lambda>x :: 'n pairpath. indicator BB x :: real)
        \<in> borel_measurable ?Bi" using BB by (rule borel_measurable_indicator)
    show ?thesis by (rule measurable_compose[OF pc ib])
  qed
  have c1: "\<bar>(indicator BB (pcut i x) :: real)\<bar> \<le> 1" for x :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e) \<in> borel_measurable ?B"
    by (rule X_eval_entry_measurable)
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed

corollary aglue_gint_C:
  fixes Q :: "('n::finite pairpath) measure" and HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and BB: "BB \<in> sets (path_borel i :: ('n pairpath) measure)"
    and Kint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w.
        \<bar>(outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
      * ((outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  have cb: "(\<lambda>x :: 'n pairpath. indicator BB (pcut i x) :: real)
      \<in> borel_measurable ?B"
  proof -
    have pc: "pcut i \<in> ?B \<rightarrow>\<^sub>M ?Bi" by (rule pcut_measurable[OF i0 iT refl])
    have ib: "(\<lambda>x :: 'n pairpath. indicator BB x :: real)
        \<in> borel_measurable ?Bi" using BB by (rule borel_measurable_indicator)
    show ?thesis by (rule measurable_compose[OF pc ib])
  qed
  have c1: "\<bar>(indicator BB (pcut i x) :: real)\<bar> \<le> 1" for x :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
    by (rule comp_eval_entry_measurable)
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed

subsection \<open>Clause (iv) for the conditional law\<close>

text \<open>Only countably many conditions survive the passage from "for each,
  almost surely" to "almost surely, for all", so the martingale identity
  arrives at rational times only.  Extending it to every real time is not a
  matter of path continuity alone: pointwise convergence does not move a set
  integral, so uniform integrability is needed.  The family in question is a
  family of conditional expectations of the single terminal value, so
  \<open>prob_space.unif_integrable_of_averaging\<close> applies verbatim
  and \<open>finite_measure.vitali_convergence\<close> finishes, both from
  @{theory Continuous_Time_Martingales.Conditional_UI}.

  Larsson and Ruf \<^cite>\<open>LarssonRuf\<close> instead use a regular conditional
  distribution, citing Stroock--Varadhan, Thm 1.3.4; that classical conditioning
  theorem needs none of this because the martingale problem there is stated with
  test functions in \<open>C\<^sub>c\<^sup>\<infinity>\<close>, whose martingales are bounded, while the
  covariation class makes \<open>X\<close> itself and \<open>outerp X - Y\<close> the martingales,
  and those are not.

  The countably many almost-sure conditions of
  @{thm [source] pfut_rcd_F_increment_zero} (rational times, a countable
  \<open>\<pi>\<close>-system per time) and @{thm [source] pfut_rcd_F_integrable} hold
  together at almost every \<open>p'\<close>; there the \<open>\<pi>\<close>-system widens to \<open>\<F>\<^sub>q\<close> and
  \<open>martingale_of_rational_set_integral_eq\<close> extends the rational times to
  all times.\<close>

theorem pfut_rcd_F_martingale:
  fixes P :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
    and F :: "'p \<Rightarrow> real"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: (real \<Rightarrow> 'p) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure))"
    and eq: "distr P
          ((path_borel r :: (real \<Rightarrow> 'p) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: (real \<Rightarrow> 'p) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (process_law r (pcut r) P)
            ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure)) \<kappa>"
    and Fc: "continuous_on UNIV F"
    and Pint: "\<And>u. u \<in> {0..T - r} \<Longrightarrow> integrable P (\<lambda>\<omega>. F (pfut r T \<omega> u))"
    and Pinc: "\<And>C u v. C \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + u))
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T - r
      \<Longrightarrow> set_lebesgue_integral P C (\<lambda>\<omega>. F (pfut r T \<omega> u))
        = set_lebesgue_integral P C (\<lambda>\<omega>. F (pfut r T \<omega> v))"
  shows "AE p' in process_law r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. F (w (min u (T - r))))"
proof -
  let ?X = "(path_borel r :: (real \<Rightarrow> 'p) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: (real \<Rightarrow> 'p) measure)"
  let ?Q = "process_law r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: (real \<Rightarrow> 'p). w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  have Fb: "F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF Fc])
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding process_law_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_process_law)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  \<comment> \<open>the countable \<open>\<pi>\<close>-system, one per time\<close>
  from countable_pi_systems_natural_filtration_path[OF refl, where T = ?S]
  obtain Eg where Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  note Espec = bspec[OF Espec0]

  \<comment> \<open>the countably many almost-sure conditions\<close>
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. (\<integral>w. indicator A' w * (F (w ?S) - F (w q)) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> (\<forall>A' \<in> Eg q.
        (\<integral>w. indicator A' w * (F (w ?S) - F (w q)) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have "AE p' in ?Q. \<forall>A' \<in> Eg q.
          (\<integral>w. indicator A' w * (F (w ?S) - F (w q)) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ conjunct1[OF Espec[OF True]]])
        fix A' assume "A' \<in> Eg q"
        then have AG: "A' \<in> sets (?G q)" using Espec[OF True] by auto
        show "AE p' in ?Q.
            (\<integral>w. indicator A' w * (F (w ?S) - F (w q)) \<partial>(\<kappa> p')) = 0"
          by (rule pfut_rcd_F_increment_zero[OF r rT setsP PS K eq Fb Pint Pinc _ _ _ AG])
             (use True in auto)
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_F_integrable[OF r rT setsP PS K eq Fb Pint[OF True]]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S))"
    by (rule pfut_rcd_F_integrable[OF r rT setsP PS K eq Fb Pint[OF SS]])

  \<comment> \<open>and the assembly at each good \<open>p'\<close>\<close>
  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A'. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * (F (w ?S) - F (w q)) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow>
          integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w q))"
      and SI: "integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: (real \<Rightarrow> 'p). w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: (real \<Rightarrow> 'p) metric)"
      by (simp add: space_borel_of)
    have Fm: "(\<lambda>w :: (real \<Rightarrow> 'p). F (w (min u ?S)))
        \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
      if "0 \<le> u" for u
    proof -
      have "(\<lambda>w :: (real \<Rightarrow> 'p). w (min u ?S))
          \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
        by (rule natural_filtration_eval) (use that Tr in auto)
      then show ?thesis by (rule measurable_compose[OF _ Fb])
    qed
    show ?case
    proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
      show "(\<lambda>w :: (real \<Rightarrow> 'p). F (w (min u ?S)))
          \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
        if "u \<in> {0..?S}" for u by (rule Fm) (use that in simp)
      show "(\<lambda>w :: (real \<Rightarrow> 'p). F (w (min u ?S)))
          \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
        if "0 \<le> u" for u by (rule Fm[OF that])
      show "integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w (min q ?S)))"
        if "q \<in> \<rat>" "q \<in> {0..?S}" for q using RI[OF that] that(2) by simp
      show "integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w (min ?S ?S)))"
        using SI by simp
      show "continuous_on {0..?S} (\<lambda>u. F (w (min u ?S)))"
        if "w \<in> space (\<kappa> p')" for w :: "(real \<Rightarrow> 'p)"
      proof -
        have "continuous_on {0..?S} w"
          by (rule mspace_path_metricD) (use that spK spY in simp)
        then have "continuous_on {0..?S} (\<lambda>u. F (w u))"
          by (rule continuous_on_compose2[OF Fc]) simp
        then show ?thesis by (rule continuous_on_eq) simp
      qed
      show "(\<lambda>w :: (real \<Rightarrow> 'p). F (w (min u ?S))) = (\<lambda>w. F (w (min ?S ?S)))"
        if "?S \<le> u" for u using that by simp
      \<comment> \<open>the \<open>\<pi>\<close>-system widens to \<open>\<F>\<^sub>q\<close> at this fixed \<open>p'\<close>\<close>
      fix q :: real and A
      assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
        and A: "A \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>v w :: (real \<Rightarrow> 'p). w v) q)"
      have AG: "A \<in> sets (?G q)" using A nfK by simp
      have EgS: "countable (Eg q)" "Int_stable (Eg q)"
        "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
        "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
        using Espec[OF q] by blast+
      have subG: "subalgebra (\<kappa> p') (?G q)"
        using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
      have iq: "integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w q))" by (rule RI[OF qrat q])
      have gi: "integrable (\<kappa> p') (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S) - F (w q))"
        by (rule Bochner_Integration.integrable_diff[OF SI iq])
      have gz: "set_lebesgue_integral (\<kappa> p') B
          (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S) - F (w q)) = 0"
        if B: "B \<in> Eg q" for B
        using Z0[OF qrat q B] unfolding set_lebesgue_integral_def by simp
      have zA: "set_lebesgue_integral (\<kappa> p') A
          (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S) - F (w q)) = 0"
        by (rule set_integral_zero_of_generator
            [OF subG gi EgS(2) _ _ _ gz AG])
           (use EgS(3) EgS(4) EgS(5) spK in simp_all)
      have AQ: "A \<in> sets (\<kappa> p')"
        using AG subG by (auto simp: subalgebra_def)
      have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S))"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ SI])
      have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: (real \<Rightarrow> 'p). F (w q))"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ iq])
      have "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: (real \<Rightarrow> 'p). F (w ?S))
          - set_lebesgue_integral (\<kappa> p') A (\<lambda>w. F (w q)) = 0"
        using set_integral_diff(2)[OF s1 s2] zA by simp
      then show "set_lebesgue_integral (\<kappa> p') A
            (\<lambda>w :: (real \<Rightarrow> 'p). F (w (min q ?S)))
          = set_lebesgue_integral (\<kappa> p') A (\<lambda>w. F (w (min ?S ?S)))"
        using q by simp
    qed
  qed
qed

text \<open>The two instances.  For a coordinate of \<open>X\<close>, the shifted process is
  \<open>X\<^sub>r\<^sub>+\<^sub>u - X\<^sub>r\<close>, whose increment property is the martingale property of \<open>X\<close>
  under \<open>P\<close>; for a compensated entry it is the martingale
  \<open>covariation_class_pfut_comp_martingale\<close> in the shifted filtration, which agrees
  with \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>u\<^sub>)\<close> for \<open>u \<le> T - r\<close>.\<close>

theorem pfut_rcd_X_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (process_law r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  shows "AE p' in process_law r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + s)))"
    if "s \<in> {0..T - r}" for s
    using Mg.integrable[of "r + s"] that r by (simp add: min_absorb1)
  have pf: "fst (pfut r T \<omega> s) $ c = fst (\<omega> (r + s)) $ c - fst (\<omega> (r + 0)) $ c"
    if "s \<in> {0..T - r}" for \<omega> s c
    using pfut_fst[OF that, of \<omega>] by simp
  have Xc: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + s)) $ c)"
    if "s \<in> {0..T - r}" for s c
    by (rule integrable_bounded_linear[OF bounded_linear_vec_nth Xint[OF that]])
  have Pint: "integrable P (\<lambda>\<omega>. fst (pfut r T \<omega> s) $ c)" if s: "s \<in> {0..T - r}" for s c
    unfolding pf[OF s]
    by (rule Bochner_Integration.integrable_diff[OF Xc[OF s] Xc]) (use rT in simp)
  have Pinc: "set_lebesgue_integral P C (\<lambda>\<omega>. fst (pfut r T \<omega> u) $ c)
      = set_lebesgue_integral P C (\<lambda>\<omega>. fst (pfut r T \<omega> v) $ c)"
    if C: "C \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + u))"
      and u: "0 \<le> u" "u \<le> v" "v \<le> T - r" for C u v c
  proof -
    have "sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + u))
        \<subseteq> sets P"
      by (rule sets_natural_filtration_subset) (rule path_law_evaluation_measurable[OF setsP])
    then have CP: "C \<in> sets P" using C by blast
    have mem: "u \<in> {0..T - r}" "v \<in> {0..T - r}" "0 \<in> {0..T - r}" using u by auto
    have si: "set_integrable P C (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + s)) $ c)"
      if "s \<in> {0..T - r}" for s
      unfolding set_integrable_def by (rule integrable_mult_indicator[OF CP Xc[OF that]])
    have "set_lebesgue_integral P C (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + u) T)))
        = set_lebesgue_integral P C (\<lambda>\<omega>. fst (\<omega> (min (r + v) T)))"
      by (rule Mg.set_integral_eq[OF C]) (use r u in simp_all)
    then have "set_lebesgue_integral P C (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u))) $ c
        = set_lebesgue_integral P C (\<lambda>\<omega>. fst (\<omega> (r + v))) $ c"
      using u by (simp add: min_absorb1)
    then have "set_lebesgue_integral P C (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)
        = set_lebesgue_integral P C (\<lambda>\<omega>. fst (\<omega> (r + v)) $ c)"
      unfolding set_integral_vec_component[OF CP Xint[OF mem(1)]]
        set_integral_vec_component[OF CP Xint[OF mem(2)]] .
    then show ?thesis
      unfolding pf[OF mem(1)] pf[OF mem(2)]
        set_integral_diff(2)[OF si[OF mem(1)] si[OF mem(3)]]
        set_integral_diff(2)[OF si[OF mem(2)] si[OF mem(3)]] by simp
  qed
  have mc: "AE p' in process_law r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))) $ c)" for c
    by (rule pfut_rcd_F_martingale[where F = "\<lambda>z. fst z $ c",
          OF r rT setsP PS K eq _ Pint Pinc]) (intro continuous_intros)
  have "AE p' in process_law r (pcut r) P. \<forall>c.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))) $ c)"
    by (intro eventually_all_finite mc)
  then show ?thesis by eventually_elim (rule martingale_vecI, blast)
qed

theorem pfut_rcd_comp_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> (path_borel r :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (process_law r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
  shows "AE p' in process_law r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  interpret Mg: martingale P
      "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u (T - r))" 0
      "\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r)))) - snd (pfut r T \<omega> (min u (T - r)))"
    by (rule mg)
  have Cint: "integrable P (\<lambda>\<omega>. outerp (fst (pfut r T \<omega> s)) - snd (pfut r T \<omega> s))"
    if "s \<in> {0..T - r}" for s
    using Mg.integrable[of s] that by (simp add: min_absorb1)
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)" for c d
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  have Pint: "integrable P (\<lambda>\<omega>. (outerp (fst (pfut r T \<omega> s)) - snd (pfut r T \<omega> s)) $ c $ d)"
    if "s \<in> {0..T - r}" for s c d
    by (rule integrable_bounded_linear[OF bl Cint[OF that]])
  have Pinc: "set_lebesgue_integral P C
        (\<lambda>\<omega>. (outerp (fst (pfut r T \<omega> u)) - snd (pfut r T \<omega> u)) $ c $ d)
      = set_lebesgue_integral P C
        (\<lambda>\<omega>. (outerp (fst (pfut r T \<omega> v)) - snd (pfut r T \<omega> v)) $ c $ d)"
    if C: "C \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + u))"
      and u: "0 \<le> u" "u \<le> v" "v \<le> T - r" for C u v c d
  proof -
    have mem: "u \<in> {0..T - r}" "v \<in> {0..T - r}" using u by auto
    have CF: "C \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)
        (r + min u (T - r)))" using C mem by (simp add: min_absorb1)
    have CP: "C \<in> sets P" using CF Mg.sets_F_subset[OF u(1)] by blast
    have "set_lebesgue_integral P C
          (\<lambda>\<omega>. outerp (fst (pfut r T \<omega> (min u (T - r)))) - snd (pfut r T \<omega> (min u (T - r))))
        = set_lebesgue_integral P C
          (\<lambda>\<omega>. outerp (fst (pfut r T \<omega> (min v (T - r)))) - snd (pfut r T \<omega> (min v (T - r))))"
      by (rule Mg.set_integral_eq[OF CF u(1,2)])
    then show ?thesis
      using mem unfolding set_integral_mat_component[OF CP Cint[OF mem(1)]]
        set_integral_mat_component[OF CP Cint[OF mem(2)]] by (simp add: min_absorb1)
  qed
  have mc: "AE p' in process_law r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. (outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r)))) $ c $ d)"
    for c d
    by (rule pfut_rcd_F_martingale[where F = "\<lambda>z. (outerp (fst z) - snd z) $ c $ d",
          OF r rT setsP PS K eq comp_entry_cont Pint Pinc])
  have "AE p' in process_law r (pcut r) P. \<forall>c d.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. (outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r)))) $ c $ d)"
    by (intro eventually_all_finite mc)
  then show ?thesis by eventually_elim (rule martingale_matI, blast)
qed

(*<*)
end
(*>*)
