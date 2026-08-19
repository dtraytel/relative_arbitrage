section \<open>Sampling a path law at a stopping time\<close>

(*<*)
theory Path_Law_Sampling
  imports Path_Law_Pasting
begin

(*>*)

text \<open>What optional sampling looks like on the path space: the increment
  identity at the sampled time \<open>u \<or> \<theta>\<close>, the integrand it produces, and the
  clauses that survive the sampling.\<close>


text \<open>\<open>stopped_increment_of_horizon_gen\<close> is stated for the offset
  family \<open>(\<theta>+i) \<and> T\<close>; the additive split instead uses the delayed family
  \<open>u \<or> \<theta>\<close>.  Both are instances of one statement about an arbitrary pair of
  ordered bounded path stopping times, proved here and already abstract in
  @{thm [source] set_martingale_sampling_two}.

  Integrability of the sampled process, free in the deterministic
  development from the martingale locale, is reconstructed here from the
  dyadic approximation and the same dominating function.\<close>

lemma pcut_after_in_pre_sigma:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
  shows "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}
      \<in> pre_sigma_of Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) (\<lambda>p'. min i (\<theta> p'))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?C = "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}"
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
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
         (rule pair_law_eval_measurable[OF setsQ])
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

subsection \<open>Clause (iv): the inner-integral identity\<close>

lemma pstopped_eval_filtration:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
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

subsection \<open>Stopping a horizon-capped square-integrable martingale\<close>

text \<open>The engine behind \<open>QH\<close> and \<open>QHC\<close>, abstracted out of
  \<open>exit_class_stopped_coord_martingale\<close>: its proof uses
  the localisation time only through nonnegativity and the stopping
  property, so it generalises to any stopping time verbatim.  Doob's
  envelope \<^term>\<open>Dsup\<close> supplies both the dominating function
  \<open>optional_stopping\<close> needs and the square-integrability of the stopped
  process, which is what promotes the conclusion back to a
  \<^const>\<open>horizon_sq_int_martingale\<close>.\<close>

theorem aglue_inner_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min i T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min j T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Y = "\<lambda>u p' :: 'n pairpath. fst (p' (min u T)) $ c"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])

  \<comment> \<open>the two pointwise halves\<close>
  have after: "?g u p' = indicator B (pcut i p') * ?Y u p'"
    if sp: "p' \<in> space Q" and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
    for p' u
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have m: "min u T \<in> {0..T}" using u0 uT by simp
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    have pdm: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> \<kappa> p' \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsK refl]
      by (rule padd_measurable_left[OF T0' pmem])
    have Xm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) \<bullet> (axis c 1 :: real^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF pair_law_eval_measurable[OF refl]
              pair_fst_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have icm: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mL: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ c)) \<in> borel_measurable (\<kappa> p')"
      using icm measurable_compose[OF pdm Xm] by simp
    have mR: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Y u p' + fst (w (min u T)) $ c)) \<in> borel_measurable (\<kappa> p')"
      using Xm unfolding measurable_cong_sets[OF setsK refl] by simp
    have cutAE: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Y u p' + fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mL mR])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c)
          = indicator B (pcut i p') * (?Y u p' + fst (w (min u T)) $ c)"
        using cutAE
      proof eventually_elim
        case (elim w)
        show ?case unfolding elim padd_apply[OF m] by simp
      qed
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (\<integral>w. ?Y u p' + fst (w (min u T)) $ c \<partial>(\<kappa> p'))" by simp
    also have "(\<integral>w. ?Y u p' + fst (w (min u T)) $ c \<partial>(\<kappa> p'))
        = ?Y u p' + (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PKi.integrable_const
        Kint[OF sp u0 uT]] by (simp add: PKi.prob_space)
    finally show ?thesis using Kmean[OF sp u0 uT] by simp
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
           (rule pair_law_eval_measurable[OF setsK])
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
    have dec: "?g u p' = ?Y u p' * measure (\<kappa> p') C
        + set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have m: "min u T \<in> {0..T}" using u0 uT by simp
      have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
      have i1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Y u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Y u p'"] by simp
      have i2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * (fst (w (min u T)) $ c))"
        using integrable_mult_indicator[OF CK Kint[OF sp u0 uT]] by simp
      have "?g u p' = (\<integral>w. indicator C w * ?Y u p'
          + indicator C w * (fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: C_def padd_apply[OF m] indicator_def)
      also have "\<dots> = (\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p'))
          + (\<integral>w. indicator C w * (fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_add[OF i1 i2])
      also have "(\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p')) = ?Y u p' * measure (\<kappa> p') C"
        by (simp add: mult.commute Int_absorb2[OF Csub])
      finally show ?thesis unfolding set_lebesgue_integral_def by simp
    qed
    show ?thesis
      unfolding dec[OF j0 jT] dec[OF i0 iT] same
      using Kinc[OF sp Cf i0 ij jT] by simp
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
      have "continuous_on {0..T} (\<lambda>s. fst (p' s) $ c)"
        using Qcont[OF sp] by (intro continuous_intros)
      moreover have "continuous_on {0..T} (\<lambda>s. fst (p' (min s T)) $ c)
          = continuous_on {0..T} (\<lambda>s. fst (p' s) $ c)"
        by (rule continuous_on_cong[OF refl]) simp
      ultimately show ?thesis by simp
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
    have Dmeas: "?D \<in> sets Q"
      by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
        \<in> borel_measurable borel"
    proof -
      have s: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis by (rule measurable_compose[OF s borel_measurable_nth])
    qed
    have Yfix: "?Y v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule pair_law_eval_measurable[OF setsQ])
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

subsection \<open>Clause (iv): the increment identity for the glued law\<close>

text \<open>The wrapper.  @{thm [source] sets_natural_filtration_eq_pcut_vimage}
  presents the conditioning set as a \<^const>\<open>pcut\<close>-preimage,
  @{thm [source] integral_aglue_law} carries the set integral to the past
  and the continuation, and there @{thm [source] aglue_inner_increment}
  closes it.\<close>

theorem aglue_law_X_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and A: "A \<in> sets (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v) i)"
    and hi: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. indicator A \<omega> * (fst (\<omega> (min u T)) $ c))"
    and msec: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "set_lebesgue_integral (aglue_law T \<kappa> Q) A (\<lambda>\<omega>. fst (\<omega> (min i T)) $ c)
       = set_lebesgue_integral (aglue_law T \<kappa> Q) A (\<lambda>\<omega>. fst (\<omega> (min j T)) $ c)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  obtain B where B: "B \<in> sets ?Bi" and Aeq: "A = pcut i -` B \<inter> space ?R"
    using A
    unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B" for u
    by (rule pair_law_eval_measurable[OF refl])
  have Xm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c) \<in> borel_measurable ?B"
    for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) \<bullet> (axis c 1 :: real^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_fst_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have AR: "A \<in> sets ?R"
  proof -
    have "sets (natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) i)
        \<subseteq> sets ?R"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsR])
    then show ?thesis using A by blast
  qed
  have AB: "A \<in> sets ?B" using AR setsR by simp
  have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * (fst (\<omega> (min u T)) $ c))
      \<in> borel_measurable ?B" for u
    using AB Xm[of u] by measurable

  \<comment> \<open>transport one side\<close>
  have tr: "set_lebesgue_integral ?R A (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
      = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have "set_lebesgue_integral ?R A (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
        = (\<integral>\<omega>. indicator A \<omega> * (fst (\<omega> (min u T)) $ c) \<partial>?R)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
        * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
      by (rule integral_aglue_law
          [OF T0' PQ setsQ Kp hm hi[OF u0 uT] msec[OF u0 uT]])
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix p' assume sp: "p' \<in> space Q"
      have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sp spQ by (simp add: space_borel_of)
      have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
      have spK: "space (\<kappa> p') = space ?B"
        by (rule sets_eq_imp_space_eq[OF setsK])
      show "(\<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))
          = (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have inR: "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        have "indicator A (padd T p' w)
            = (indicator B (pcut i (padd T p' w)) :: real)"
          unfolding Aeq using inR by (simp add: indicator_def)
        then show "indicator A (padd T p' w)
              * (fst (padd T p' w (min u T)) $ c)
            = indicator B (pcut i (padd T p' w))
              * (fst (padd T p' w (min u T)) $ c)" by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding tr[OF i0 iT] tr[OF j0 jT]
    by (rule aglue_inner_increment
        [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
          i0 ij iT jT B gint[OF _ _ B]])
qed

subsection \<open>Clause (iv) for the glue: the \<open>X\<close> martingale\<close>

text \<open>Assembly.  The componentwise identity is
  @{thm [source] aglue_law_X_increment}; the vector one follows by
  @{thm [source] set_integral_vec_component}, and
  \<open>martingale_of_set_integral_eq\<close> turns it into the martingale property.
  Past the horizon the process is constant, so an index above \<open>T\<close> is pulled
  back to \<open>T\<close> before the identity is applied.\<close>

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
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have m: "min u T \<in> {0..u}" using u T0' by simp
    have Rb: "?G u = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
      by (rule natural_filtration_cong_space
          [OF sets_eq_imp_space_eq[OF setsR]])
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      unfolding Rb by (rule path_eval_measurable_natural_filtration'[OF m])
    then show ?thesis by (rule measurable_compose) (rule pair_fst_borel)
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule RXint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    have v0: "0 \<le> v" using uv by simp
    have CR: "C \<in> sets ?R" using C SF.sets_F_subset[OF uv(1)] by blast
    have comp: "set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X u \<omega> $ c)
        = set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X v \<omega> $ c)" for c
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      then have uT: "u \<le> T" by simp
      have vT: "min v T \<le> T" by simp
      have uvT: "u \<le> min v T" using uv uT by simp
      have hiA: "integrable ?R (\<lambda>\<omega>. indicator C \<omega> * (fst (\<omega> (min s T)) $ c))"
        if s: "0 \<le> s" for s
      proof -
        have ii: "integrable ?R (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min s T)) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RXint[OF s]])
        show ?thesis using integrable_mult_indicator[OF CR ii] by simp
      qed
      have "set_lebesgue_integral ?R C (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
          = set_lebesgue_integral ?R C (\<lambda>\<omega>. fst (\<omega> (min (min v T) T)) $ c)"
        by (rule aglue_law_X_increment
            [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
              uv(1) uvT uT vT C hiA msec[OF CR] gint[OF _ _ _ uv(1) uT]])
      then show ?thesis by simp
    qed
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof -
      have "set_lebesgue_integral ?R C (?X u) $ c
          = set_lebesgue_integral ?R C (?X v) $ c" for c
        using comp[of c]
        unfolding set_integral_vec_component[OF CR RXint[OF uv(1)]]
          set_integral_vec_component[OF CR RXint[OF v0]] .
      then show ?thesis by (simp add: vec_eq_iff)
    qed
  qed
qed

subsection \<open>Clause (iv): the compensated inner-integral identity\<close>

text \<open>\<^const>\<open>outerp\<close> is quadratic, so on the product

  \<open>(outerp (fst (padd p' w s)) - snd (padd p' w s)) $ c $ d
     = Zp s p' + Zw s w + (fst (p' s) $ c * fst (w s) $ d
                           + fst (w s) $ c * fst (p' s) $ d)\<close>

  --- a past compensated entry, a continuation compensated entry, and two
  cross terms.  Inside the inner integral the past factor
  \<^term>\<open>fst (p' s)\<close> is constant, so it pulls out and what remains is a
  continuation increment: on \<open>{\<theta> > i}\<close> the vanishing of the continuation's
  mean, on \<open>{\<theta> \<le> i}\<close> its own increment identity against the section.  The
  four-cell shape is thus unchanged from the \<open>X\<close> clause, with no extra
  cross-term machinery needed.\<close>

theorem aglue_inner_increment_comp:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (path_borel i :: ('n pairpath) measure)"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min i T)))
                - snd (padd T p' w (min i T))) $ c $ d) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min j T)))
                - snd (padd T p' w (min j T))) $ c $ d) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * ?Z u (padd T p' w) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])

  \<comment> \<open>the pathwise expansion of the compensated entry along the glue\<close>
  have expand: "?Z u (padd T p' w)
      = ?Z u p' + (?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
    if "0 \<le> u" and "u \<le> T" for u p' w
  proof -
    have m: "min u T \<in> {0..T}" using that by simp
    show ?thesis
      unfolding padd_apply[OF m] by (simp add: outerp_def algebra_simps)
  qed

  have after: "?g u p' = indicator B (pcut i p') * ?Z u p'"
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
    have cut: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have evB: "(\<lambda>w :: 'n pairpath. w s) \<in> borel_measurable ?B" for s
      by (rule pair_law_eval_measurable[OF refl])
    have femB: "(\<lambda>w :: 'n pairpath. fst (w s) $ e) \<in> borel_measurable ?B"
      for s e
    proof -
      have "(\<lambda>w :: 'n pairpath. fst (w s) \<bullet> (axis e 1 :: real^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF evB pair_fst_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have semB: "(\<lambda>w :: 'n pairpath. snd (w s) $ e $ f) \<in> borel_measurable ?B"
      for s e f
    proof -
      have "(\<lambda>w :: 'n pairpath. snd (w s) \<bullet> (axis e (axis f 1) :: real^'n^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF evB pair_snd_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have ZmB: "?Z v \<in> borel_measurable ?B" for v
    proof -
      have e: "?Z v = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min v T)) $ c
          * fst (\<omega> (min v T)) $ d - snd (\<omega> (min v T)) $ c $ d)"
        by (rule ext) (rule comp_entry_eq)
      show ?thesis unfolding e
        by (intro borel_measurable_diff borel_measurable_times femB semB)
    qed
    have icmc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mLc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * ?Z u (padd T p' w)) \<in> borel_measurable (\<kappa> p')"
      using icmc measurable_compose[OF pdm ZmB] by simp
    have mRc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))))
        \<in> borel_measurable (\<kappa> p')"
      using ZmB[of u] femB
      unfolding measurable_cong_sets[OF setsK refl] by simp
    have i1: "integrable (\<kappa> p') (\<lambda>w. ?Z u w)" by (rule KintC[OF sp u0 uT])
    have i2: "integrable (\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d)"
      by (rule integrable_mult_right) (rule Kint[OF sp u0 uT])
    have i3: "integrable (\<kappa> p')
        (\<lambda>w. fst (w (min u T)) $ c * fst (p' (min u T)) $ d)"
      using integrable_mult_right[OF Kint[OF sp u0 uT],
        of "fst (p' (min u T)) $ d"] by (simp add: mult.commute)
    have z2: "(\<integral>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      using Kmean[OF sp u0 uT] by simp
    have z3: "(\<integral>w. fst (w (min u T)) $ c * fst (p' (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      using Kmean[OF sp u0 uT] by simp
    have i23: "integrable (\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)"
      by (rule Bochner_Integration.integrable_add[OF i2 i3])
    have z23: "(\<integral>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      unfolding Bochner_Integration.integral_add[OF i2 i3] z2 z3 by simp
    have i123: "integrable (\<kappa> p') (\<lambda>w. ?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
      by (rule Bochner_Integration.integrable_add[OF i1 i23])
    have z123: "(\<integral>w. ?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d) \<partial>(\<kappa> p')) = 0"
      unfolding Bochner_Integration.integral_add[OF i1 i23]
        KmeanC[OF sp u0 uT] z23 by simp
    have inner: "(\<integral>w. ?Z u p' + (?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)) \<partial>(\<kappa> p'))
        = ?Z u p'"
      unfolding Bochner_Integration.integral_add[OF PKi.integrable_const i123]
        z123 by (simp add: PKi.prob_space)
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mLc mRc])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * ?Z u (padd T p' w)
          = indicator B (pcut i p')
            * (?Z u p' + (?Z u w
              + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
                 + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)))"
        using cut
      proof eventually_elim
        case (elim w)
        show ?case unfolding elim expand[OF u0 uT] ..
      qed
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (\<integral>w. ?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)) \<partial>(\<kappa> p'))"
      by simp
    finally show ?thesis unfolding inner .
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
           (rule pair_law_eval_measurable[OF setsK])
      then show ?thesis using Cf by blast
    qed
    have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
    have samev: "p' (min u T) = p' (\<theta> p')" if u: "0 \<le> u" and ui: "i \<le> u" for u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u])
      moreover have "min (min u T) (\<theta> p') = \<theta> p'"
        using le ui th0[of p'] thT[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have dec: "?g u p' = (\<integral>w. indicator C w * ?Z u p' \<partial>(\<kappa> p'))
        + ((\<integral>w. indicator C w * ?Z u w \<partial>(\<kappa> p'))
           + ((\<integral>w. indicator C w * (fst (p' (min u T)) $ c
                * fst (w (min u T)) $ d) \<partial>(\<kappa> p'))
              + (\<integral>w. indicator C w * (fst (w (min u T)) $ c
                * fst (p' (min u T)) $ d) \<partial>(\<kappa> p'))))"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have j1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Z u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Z u p'"] by simp
      have j2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Z u w)"
        using integrable_mult_indicator[OF CK KintC[OF sp u0 uT]] by simp
      have j3: "integrable (\<kappa> p') (\<lambda>w. indicator C w
          * (fst (p' (min u T)) $ c * fst (w (min u T)) $ d))"
        using integrable_mult_indicator[OF CK
          integrable_mult_right[OF Kint[OF sp u0 uT]]] by simp
      have j4: "integrable (\<kappa> p') (\<lambda>w. indicator C w
          * (fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
        using integrable_mult_indicator[OF CK
          integrable_mult_right[OF Kint[OF sp u0 uT],
            of "fst (p' (min u T)) $ d"]] by (simp add: mult.commute)
      have "?g u p' = (\<integral>w. indicator C w * ?Z u p'
          + (indicator C w * ?Z u w
             + (indicator C w * (fst (p' (min u T)) $ c
                  * fst (w (min u T)) $ d)
                + indicator C w * (fst (w (min u T)) $ c
                  * fst (p' (min u T)) $ d))) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have ic: "indicator B (pcut i (padd T p' w)) = (indicator C w :: real)"
          unfolding C_def using sw by (simp add: indicator_def)
        show "indicator B (pcut i (padd T p' w)) * ?Z u (padd T p' w)
            = indicator C w * ?Z u p'
              + (indicator C w * ?Z u w
                 + (indicator C w * (fst (p' (min u T)) $ c
                      * fst (w (min u T)) $ d)
                    + indicator C w * (fst (w (min u T)) $ c
                      * fst (p' (min u T)) $ d)))"
          unfolding ic expand[OF u0 uT] by (simp add: field_simps)
      qed
      also have "\<dots> = (\<integral>w. indicator C w * ?Z u p' \<partial>(\<kappa> p'))
          + ((\<integral>w. indicator C w * ?Z u w \<partial>(\<kappa> p'))
             + ((\<integral>w. indicator C w * (fst (p' (min u T)) $ c
                  * fst (w (min u T)) $ d) \<partial>(\<kappa> p'))
                + (\<integral>w. indicator C w * (fst (w (min u T)) $ c
                  * fst (p' (min u T)) $ d) \<partial>(\<kappa> p'))))"
        using Bochner_Integration.integral_add[OF j1
            Bochner_Integration.integrable_add[OF j2
              Bochner_Integration.integrable_add[OF j3 j4]]]
          Bochner_Integration.integral_add[OF j2
            Bochner_Integration.integrable_add[OF j3 j4]]
          Bochner_Integration.integral_add[OF j3 j4]
        by simp
      finally show ?thesis .
    qed
    have zZ: "?Z j p' = ?Z i p'" using samev[OF i0 order_refl] samev[OF j0 ij]
      by simp
    have xc: "fst (p' (min j T)) $ c = fst (p' (min i T)) $ c"
      using samev[OF i0 order_refl] samev[OF j0 ij] by simp
    have xd: "fst (p' (min j T)) $ d = fst (p' (min i T)) $ d"
      using samev[OF i0 order_refl] samev[OF j0 ij] by simp
    have s1: "(\<integral>w. indicator C w * ?Z j p' \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * ?Z i p' \<partial>(\<kappa> p'))" unfolding zZ ..
    have s2: "(\<integral>w. indicator C w * ?Z j w \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * ?Z i w \<partial>(\<kappa> p'))"
      using KincC[OF sp Cf i0 ij jT]
      unfolding set_lebesgue_integral_def by simp
    have pull: "(\<integral>w. indicator C w * (a * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))
        = a * (\<integral>w. indicator C w * fst (w (min u T)) $ e \<partial>(\<kappa> p'))"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u a e
    proof -
      have ii: "integrable (\<kappa> p') (\<lambda>w. indicator C w * fst (w (min u T)) $ e)"
        using integrable_mult_indicator[OF CK Kint[OF sp u0 uT]] by simp
      have "(\<integral>w. indicator C w * (a * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))
          = (\<integral>w. a * (indicator C w * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: field_simps)
      also have "\<dots> = a * (\<integral>w. indicator C w * fst (w (min u T)) $ e \<partial>(\<kappa> p'))"
        using ii by simp
      finally show ?thesis .
    qed
    have ke: "(\<integral>w. indicator C w * fst (w (min j T)) $ e \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * fst (w (min i T)) $ e \<partial>(\<kappa> p'))" for e
      using Kinc[OF sp Cf i0 ij jT, of e]
      unfolding set_lebesgue_integral_def by simp
    have s3: "(\<integral>w. indicator C w
          * (fst (p' (min j T)) $ c * fst (w (min j T)) $ d) \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w
          * (fst (p' (min i T)) $ c * fst (w (min i T)) $ d) \<partial>(\<kappa> p'))"
      unfolding pull[OF j0 jT] pull[OF i0 iT] xc ke ..
    have s4: "(\<integral>w. indicator C w
          * (fst (w (min j T)) $ c * fst (p' (min j T)) $ d) \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w
          * (fst (w (min i T)) $ c * fst (p' (min i T)) $ d) \<partial>(\<kappa> p'))"
    proof -
      have r: "(\<integral>w. indicator C w * (fst (w (min u T)) $ c * a) \<partial>(\<kappa> p'))
          = a * (\<integral>w. indicator C w * fst (w (min u T)) $ c \<partial>(\<kappa> p'))"
        if "0 \<le> u" and "u \<le> T" for u a
      proof -
        have "(\<integral>w. indicator C w * (fst (w (min u T)) $ c * a) \<partial>(\<kappa> p'))
            = (\<integral>w. indicator C w * (a * fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
          by (rule Bochner_Integration.integral_cong[OF refl])
             (simp add: mult.commute)
        then show ?thesis unfolding pull[OF that] .
      qed
      show ?thesis unfolding r[OF j0 jT] r[OF i0 iT] xd ke ..
    qed
    show ?thesis
      unfolding dec[OF j0 jT] dec[OF i0 iT] s1 s2 s3 s4 ..
  qed

  \<comment> \<open>the outer split, exactly as in the \<open>X\<close> clause\<close>
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
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z u)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix x assume x: "x \<in> space Q"
      show "indicator ?E x *\<^sub>R ?g u x = indicator (?D \<inter> ?E) x *\<^sub>R ?Z u x"
      proof (cases "x \<in> ?E")
        case True
        then have lt: "i < \<theta> x" by simp
        have gv: "?g u x = indicator B (pcut i x) * ?Z u x"
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
    have Zcont: "continuous_on {0..T} (\<lambda>s. ?Z s p')"
      if sp: "p' \<in> space Q" for p'
    proof -
      have e: "(\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)
          = (\<lambda>s. fst (p' s) $ c * fst (p' s) $ d - snd (p' s) $ c $ d)"
        by (rule ext) (rule comp_entry_eq)
      have "continuous_on {0..T} (\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)"
        unfolding e using Qcont[OF sp] by (intro continuous_intros)
      moreover have "continuous_on {0..T} (\<lambda>s. ?Z s p')
          = continuous_on {0..T} (\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)"
        by (rule continuous_on_cong[OF refl]) simp
      ultimately show ?thesis by simp
    qed
    have samp: "set_lebesgue_integral Q (?D \<inter> ?E)
          (\<lambda>p'. ?Z (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min j (\<theta> p')) p')"
      by (rule stopped_increment_of_horizon_gen
          [OF T0 setsQ QHC Zcont sti sMi stj sMj lemin Cpre])
    have valE: "?Z (min u (\<theta> p')) p' = ?Z u p'"
      if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
        and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
      for p' u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u0])
      moreover have "min (min u (\<theta> p')) T = min (min u T) (\<theta> p')"
        using u0 uT th0[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have Dmeas: "?D \<in> sets Q"
      by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n).
        (outerp (fst z) - snd z) $ c $ d) \<in> borel_measurable borel"
    proof -
      have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
          \<in> borel_measurable borel"
        unfolding outerp_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have n1: "(\<lambda>v :: real^'n^'n. v $ c) \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_onI)
          (rule linear_continuous_on[OF bounded_linear_vec_nth])
      have n2: "(\<lambda>v :: real^'n. v $ d) \<in> borel_measurable borel"
        by (rule borel_measurable_nth)
      show ?thesis
        by (rule measurable_compose[OF measurable_compose[OF s n1] n2])
    qed
    have Zfix: "?Z v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule pair_law_eval_measurable[OF setsQ])
      then show ?thesis by (rule measurable_compose[OF _ fcB])
    qed
    have Zm: "(\<lambda>p' :: 'n pairpath. ?Z (min v (\<theta> p')) p') \<in> borel_measurable Q"
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
    have e1: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z i)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Zm[OF i0] Zfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Z (min i (\<theta> x)) x = ?Z i x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Z (min i (\<theta> x)) x = ?Z i x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Z (min i (\<theta> x)) x = ?Z i x"
            by (rule valE[OF sp idem lt i0 iT])
        qed
      qed
    qed
    have e2: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min j (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z j)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Zm[OF j0] Zfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Z (min j (\<theta> x)) x = ?Z j x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Z (min j (\<theta> x)) x = ?Z j x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Z (min j (\<theta> x)) x = ?Z j x"
            by (rule valE[OF sp idem lt j0 jT])
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

subsection \<open>Clause (iv): the compensated martingale for the glued law\<close>

lemma pfut_vimage_natural_filtration:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)) 0 (\<lambda>v w. w v) i)"
  shows "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  let ?Y = "(path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have sp: "space (pair_law_of (T - r) (pfut r T) P) = space ?Y"
    by (simp add: space_pair_law_of space_borel_of)
  have nfeq: "natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
        (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) i
      = natural_filtration ?Y 0 (\<lambda>v w. w v) i"
    by (rule natural_filtration_cong_space[OF sp])
  have AQ: "A' \<in> sets (natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
      (\<lambda>v w :: (real \<Rightarrow> 'a \<times> 'b). w v) i)"
    unfolding nfeq using A' .
  have m: "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) (r + min i (T - r))
        \<rightarrow>\<^sub>M natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
            (\<lambda>v w. w v) i"
    by (rule pfut_filtration_measurable[OF r rT setsP])
  have mm: "min i (T - r) = i" using iS by simp
  have "pfut r T -` A' \<inter> space (natural_filtration P 0
      (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) (r + i))
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
    using measurable_sets[OF m AQ] unfolding mm .
  then show ?thesis by simp
qed

lemma rect_vimage_natural_filtration:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A: "A \<in> sets (path_borel r :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)) 0 (\<lambda>v w. w v) i)"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  have c1: "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) r)"
    by (rule pcut_vimage_natural_filtration[OF r rT setsP A])
  have c1': "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) (r + i))"
    using c1 sets_natural_filtration_mono[of r "r + i"] i by auto
  have c2: "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) (r + i))"
    by (rule pfut_vimage_natural_filtration[OF r rT setsP i iS A'])
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      = (pcut r -` A \<inter> space P) \<inter> (pfut r T -` A' \<inter> space P)" by auto
  then show ?thesis using sets.Int[OF c1' c2] by simp
qed

subsection \<open>The martingale increment vanishes under the kernel\<close>

text \<open>The per-\<open>(i,j,A')\<close> statement, chained as follows:
  @{thm [source] AE_kernel_integral_zero} reduces the almost-sure vanishing
  of the kernel integral to the vanishing of every rectangle integral;
  @{thm [source] integral_ksemi_rect_of_set_integral} turns each rectangle
  integral into a set integral over \<open>P\<close>; @{thm [source]
  rect_vimage_natural_filtration} puts that set into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>; and there
  \<open>martingale.set_integral_eq\<close> closes it, with integrability
  from @{thm [source] integrable_ksemi_of_distr_rect} and
  @{thm [source] integrable_kernel_integral}.  The statement is componentwise,
  since the workhorse @{thm [source] AE_zero_of_set_integral_zero} is
  real-valued and \<open>'n\<close> is finite.\<close>

theorem aglue_law_comp_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and A: "A \<in> sets (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v) i)"
    and hi: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. indicator A \<omega>
          * ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d))"
    and msec: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gint: "\<And>u BB. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "set_lebesgue_integral (aglue_law T \<kappa> Q) A
        (\<lambda>\<omega>. (outerp (fst (\<omega> (min i T))) - snd (\<omega> (min i T))) $ c $ d)
      = set_lebesgue_integral (aglue_law T \<kappa> Q) A
        (\<lambda>\<omega>. (outerp (fst (\<omega> (min j T))) - snd (\<omega> (min j T))) $ c $ d)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Bi = "(path_borel i :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  obtain B where B: "B \<in> sets ?Bi" and Aeq: "A = pcut i -` B \<inter> space ?R"
    using A
    unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B" for u
    by (rule pair_law_eval_measurable[OF refl])
  have fem: "(\<lambda>w :: 'n pairpath. fst (w s) $ e) \<in> borel_measurable ?B" for s e
  proof -
    have "(\<lambda>w :: 'n pairpath. fst (w s) \<bullet> (axis e 1 :: real^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_fst_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have sem: "(\<lambda>w :: 'n pairpath. snd (w s) $ e $ f) \<in> borel_measurable ?B"
    for s e f
  proof -
    have "(\<lambda>w :: 'n pairpath. snd (w s) \<bullet> (axis e (axis f 1) :: real^'n^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_snd_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have Zm: "?Z u \<in> borel_measurable ?B" for u
  proof -
    have e: "?Z u = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c
        * fst (\<omega> (min u T)) $ d - snd (\<omega> (min u T)) $ c $ d)"
      by (rule ext) (rule comp_entry_eq)
    show ?thesis unfolding e
      by (intro borel_measurable_diff borel_measurable_times fem sem)
  qed
  have AR: "A \<in> sets ?R"
  proof -
    have "sets (natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) i)
        \<subseteq> sets ?R"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsR])
    then show ?thesis using A by blast
  qed
  have AB: "A \<in> sets ?B" using AR setsR by simp
  have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * ?Z u \<omega>) \<in> borel_measurable ?B"
    for u using AB Zm[of u] by measurable
  have tr: "set_lebesgue_integral ?R A (?Z u)
      = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have "set_lebesgue_integral ?R A (?Z u)
        = (\<integral>\<omega>. indicator A \<omega> * ?Z u \<omega> \<partial>?R)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
        * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
      by (rule integral_aglue_law
          [OF T0' PQ setsQ Kp hm hi[OF u0 uT] msec[OF u0 uT]])
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
        * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix p' assume sp: "p' \<in> space Q"
      have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sp spQ by (simp add: space_borel_of)
      have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
      have spK: "space (\<kappa> p') = space ?B"
        by (rule sets_eq_imp_space_eq[OF setsK])
      show "(\<integral>w. indicator A (padd T p' w) * ?Z u (padd T p' w) \<partial>(\<kappa> p'))
          = (\<integral>w. indicator B (pcut i (padd T p' w))
            * ?Z u (padd T p' w) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have inR: "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        have "indicator A (padd T p' w)
            = (indicator B (pcut i (padd T p' w)) :: real)"
          unfolding Aeq using inR by (simp add: indicator_def)
        then show "indicator A (padd T p' w) * ?Z u (padd T p' w)
            = indicator B (pcut i (padd T p' w)) * ?Z u (padd T p' w)"
          by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding tr[OF i0 iT] tr[OF j0 jT]
    by (rule aglue_inner_increment_comp
        [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint KintC
          Kinc KincC i0 ij iT jT B gint[OF _ _ B]])
qed

lemma pfut_rcd_X_increment_zero:
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
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ('n pairpath) measure)) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w * ((fst (w j) - fst (w i)) $ c) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?h = "\<lambda>w :: 'n pairpath. (fst (w j) - fst (w i)) $ c"
  have Tr: "0 \<le> ?S" using rT by simp
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
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
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y" for u
    by (rule pair_law_eval_measurable[OF refl])
  have hvec: "(\<lambda>w :: 'n pairpath. fst (w j) - fst (w i)) \<in> borel_measurable ?Y"
    by (intro borel_measurable_diff measurable_compose[OF ev pair_fst_borel])
  have hm: "?h \<in> borel_measurable ?Y"
  proof -
    have "(\<lambda>w :: 'n pairpath. (fst (w j) - fst (w i)) \<bullet> (axis c 1 :: real^'n))
        \<in> borel_measurable ?Y"
      by (intro borel_measurable_inner hvec borel_measurable_const)
    then show ?thesis by (simp add: inner_axis)
  qed
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)))"
    if u: "u \<in> {0..?S}" for u
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + u) T)))"
      by (rule Mg.integrable) (use r u in simp)
    moreover have "min (r + u) T = r + u" using u rT by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>stated as an equation of FUNCTIONS, and consumed by \<open>unfolding\<close>:
      \<open>simp\<close> distributes the \<open>$ c\<close> over the difference and then the rule's own
      left-hand side no longer matches anything\<close>
  have hP: "(\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))
      = (\<lambda>\<omega>. (fst (\<omega> (r + j)) - fst (\<omega> (r + i))) $ c)"
    by (rule ext) (simp add: pfut_fst[OF j0S] pfut_fst[OF i0S])
  have hi: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))"
    unfolding hP
    by (rule integrable_bounded_linear[OF bounded_linear_vec_nth
        Bochner_Integration.integrable_diff[OF Xint[OF j0S] Xint[OF i0S]]])
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?h (snd p))
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
  proof (rule integrable_ksemi_of_distr_rect)
    show "ksemi ?Q ?Y \<kappa> = distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>" by (rule eq'[symmetric])
    show "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y" by (rule mphi')
    show "?h \<in> borel_measurable ?Y" by (rule hm)
    show "A \<in> sets ?Q" by (rule A)
    show "A' \<in> sets ?Y" by (rule A'Y)
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))" by (rule hi)
  qed
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?\<phi> -` (A \<times> A') \<inter> space P
        \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
      by (rule rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'])
    have SP: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets P"
    proof -
      have "(0 :: real) \<le> r + i" using r i0 by simp
      then have "sets (natural_filtration P 0
          (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i)) \<subseteq> sets P"
        by (rule Mg.sets_F_subset)
      then show ?thesis using Sfilt by blast
    qed
    have mi: "min (r + i) T = r + i" using i0 iS rT by simp
    have mj: "min (r + j) T = r + j" using jS rT by simp
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + i) T)))
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (min (r + j) T)))"
      by (rule Mg.set_integral_eq[OF Sfilt]) (use r i0 ij in simp_all)
    then have vec: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + i)))
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (r + j)))"
      unfolding mi mj .
    have comp: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + i)) $ c)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (r + j)) $ c)"
      unfolding set_integral_vec_component[OF SP Xint[OF i0S]]
        set_integral_vec_component[OF SP Xint[OF j0S]]
      using vec by simp
    have si: "set_integrable P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)" if u: "u \<in> {0..?S}" for u
    proof -
      have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)"
        by (rule integrable_bounded_linear[OF bounded_linear_vec_nth Xint[OF u]])
      then show ?thesis
        unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP])
    qed
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> (r + j)) - fst (\<omega> (r + i))) $ c)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. fst (\<omega> (r + j)) $ c)
          - set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. fst (\<omega> (r + i)) $ c)"
      using set_integral_diff(2)[OF si[OF j0S] si[OF i0S]] by simp
    also have "\<dots> = 0" using comp by simp
    finally have zero: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>))) = 0"
      unfolding hP .
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

text \<open>The other hypothesis
  \<open>sigma_finite_filtered_measure.martingale_of_set_integral_eq\<close>
  wants: the coordinate process is \<open>\<kappa> p'\<close>-integrable at almost every \<open>p'\<close>.
  This needs no filtration at all --- only that the section of a
  \<open>ksemi\<close>-integrable function is almost surely integrable, which is
  @{thm [source] AE_integrable_ksemi_section} (generalised above from real
  to Banach values).\<close>

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
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have m: "min u T \<in> {0..u}" using u T0' by simp
    have Rb: "?G u = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
      by (rule natural_filtration_cong_space
          [OF sets_eq_imp_space_eq[OF setsR]])
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      unfolding Rb by (rule path_eval_measurable_natural_filtration'[OF m])
    have "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF evu measurable_compose
            [OF pair_fst_borel outerp_borel]])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (min u T)))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF evu pair_snd_borel])
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule RCint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    have v0: "0 \<le> v" using uv by simp
    have CR: "C \<in> sets ?R" using C SF.sets_F_subset[OF uv(1)] by blast
    have comp: "set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X u \<omega> $ c $ d)
        = set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X v \<omega> $ c $ d)" for c d
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      then have uT: "u \<le> T" by simp
      have vT: "min v T \<le> T" by simp
      have uvT: "u \<le> min v T" using uv uT by simp
      have hiA: "integrable ?R (\<lambda>\<omega>. indicator C \<omega>
          * ((outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d))"
        if s: "0 \<le> s" for s
      proof -
        have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
          by (rule bounded_linear_compose[OF bounded_linear_vec_nth
              bounded_linear_vec_nth])
        have ii: "integrable ?R (\<lambda>\<omega> :: 'n pairpath.
            (outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl RCint[OF s]])
        show ?thesis using integrable_mult_indicator[OF CR ii] by simp
      qed
      have "set_lebesgue_integral ?R C
            (\<lambda>\<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
          = set_lebesgue_integral ?R C
            (\<lambda>\<omega>. (outerp (fst (\<omega> (min (min v T) T)))
                  - snd (\<omega> (min (min v T) T))) $ c $ d)"
        by (rule aglue_law_comp_increment
            [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint
              KintC Kinc KincC uv(1) uvT uT vT C hiA msec[OF CR]
              gint[OF _ _ _ uv(1) uT]])
      then show ?thesis by simp
    qed
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof -
      have "set_lebesgue_integral ?R C (?X u) $ c $ d
          = set_lebesgue_integral ?R C (?X v) $ c $ d" for c d
        using comp[of c d]
        unfolding set_integral_mat_component[OF CR RCint[OF uv(1)]]
          set_integral_mat_component[OF CR RCint[OF v0]] .
      then show ?thesis by (simp add: vec_eq_iff)
    qed
  qed
qed

section \<open>The additive glue lands in the class\<close>

text \<open>All four clauses hold, with no martingale hypothesis left over.
  Clauses (i)--(iii) come from \<open>exit_class_aglue_law\<close>;
  the two martingale clauses are @{thm [source] aglue_law_X_martingale} and
  @{thm [source] aglue_law_comp_martingale}.  The remaining hypotheses
  concern only the two factors --- the stopped past \<open>Q\<close> and the
  continuation kernel \<open>\<kappa>\<close> --- read off the class and the r.c.d. by a caller.\<close>

lemma aglue_law_X_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
  shows "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?B \<kappa>"
  let ?t = "min u T"
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using padd_measurable_ksemi[OF T0 setsQ] measurable_cong_sets[OF setsS refl]
    by blast
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> ?t)) \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<omega> ?t) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      fst (padd T (fst p) (snd p) ?t)) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  interpret PQ': prob_space Q by (rule PQ)
  have hint: "integrable Q (\<lambda>p'. norm (fst (p' ?t)) + CX)"
    by (intro Bochner_Integration.integrable_add integrable_norm[OF QXint]
        PQ'.integrable_const)
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (fst (padd T (fst (p', w)) (snd (p', w)) ?t)))
        \<partial>(\<kappa> p')) \<le> ennreal (norm (fst (p' ?t)) + CX)"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have iN: "integrable (\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXint[OF sp]])
    have dom: "norm (fst (padd T p' w ?t)) \<le> norm (fst (p' ?t)) + norm (fst (w ?t))"
      for w :: "'n pairpath"
      unfolding padd_eval_split(1)[OF tm] by (rule norm_triangle_ineq)
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (fst (padd T p' w ?t)))"
    proof (rule Bochner_Integration.integrable_bound
        [OF Bochner_Integration.integrable_add[OF PK.integrable_const iN]])
      show "(\<lambda>w. norm (fst (padd T p' w ?t))) \<in> borel_measurable (\<kappa> p')"
      proof -
        have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
        have "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
          by (rule padd_measurable_left[OF T0])
             (use sp space_of_path_sets[OF setsQ] in simp)
        from measurable_compose[OF this hb]
        have mm: "(\<lambda>w :: 'n pairpath. fst (padd T p' w ?t)) \<in> borel_measurable ?B" .
        then have "(\<lambda>w :: 'n pairpath. fst (padd T p' w ?t))
            \<in> borel_measurable (\<kappa> p')"
          using measurable_cong_sets[OF sK refl] by blast
        then show ?thesis by measurable
      qed
      show "AE w in \<kappa> p'. norm (norm (fst (padd T p' w ?t)))
          \<le> norm (norm (fst (p' ?t)) + norm (fst (w ?t)))"
        using dom by (intro AE_I2) simp
    qed
    have "(\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))
        \<le> (\<integral>w. norm (fst (p' ?t)) + norm (fst (w ?t)) \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono
          [OF iP Bochner_Integration.integrable_add[OF PK.integrable_const iN]])
         (use dom in simp)
    also have "\<dots> = norm (fst (p' ?t)) + (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PK.integrable_const iN]
      by (simp add: PK.prob_space)
    also have "\<dots> \<le> norm (fst (p' ?t)) + CX" using KXbnd[OF sp] by simp
    finally have le: "(\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))
        \<le> norm (fst (p' ?t)) + CX" .
    have "(\<integral>\<^sup>+w. ennreal (norm (fst (padd T p' w ?t))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (norm (fst (p' ?t)) + CX)"
      using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. fst (padd T (fst p) (snd p) ?t))"
    by (rule integrable_ksemi_of_past_bound[OF Kp ne gm hint]) (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> ?t))
      = integrable ?S (\<lambda>p. fst (padd T (fst p) (snd p) ?t))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

text \<open>\<open>RCint\<close>.  \<^const>\<open>outerp\<close> is quadratic, so the glued compensated entry
  is not the sum of the two factors': @{thm [source] outerp_add} produces
  two cross terms, whose norms @{thm [source] norm_outer_prod} evaluates
  exactly.  The inner bound has the third shape
  @{thm [source] integrable_ksemi_of_past_bound} was written for.\<close>

lemma pfut_rcd_X_integrable:
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
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w u))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). fst (snd p u)"
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
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
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd
        measurable_compose[OF ev pair_fst_borel]])
  have gP: "(\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>)) = (\<lambda>\<omega>. fst (\<omega> (r + u)) - fst (\<omega> r))"
    by (rule ext) (simp add: pfut_fst[OF u])
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + v)))"
    if v: "v \<in> {0..?S}" for v
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + v) T)))"
      by (rule Mg.integrable) (use r v in simp)
    moreover have "min (r + v) T = r + v" using v rT by simp
    ultimately show ?thesis by simp
  qed
  have r0S: "(0::real) \<in> {0..?S}" using rT by simp
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>))"
      unfolding gP
      by (rule Bochner_Integration.integrable_diff[OF Xint[OF u]])
         (use Xint[OF r0S] r in simp)
    then have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] .
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

subsection \<open>From rational times to all times\<close>

text \<open>Only countably many conditions survive the passage from "for each,
  almost surely" to "almost surely, for all", so the martingale identity
  arrives at rational times only.  Extending it to every real time is not a
  matter of path continuity alone: pointwise convergence does not move a set
  integral, so uniform integrability is needed.  The family in question is a
  family of conditional expectations of the single terminal value, so
  \<open>prob_space.unif_integrable_of_averaging\<close> applies verbatim
  and \<open>finite_measure.vitali_convergence\<close> finishes, both from
  @{theory Continuous_Path_Spaces.Conditional_UI}.

  Larsson--Ruf's argument instead uses a regular conditional distribution
  citing Stroock--Varadhan, Thm 1.3.4; their classical conditioning theorem
  needs none of this because the martingale problem there is stated with
  test functions in \<open>C\<^sub>c\<^sup>\<infinity>\<close>, whose martingales are bounded, while the
  paper's class (1.7) makes \<open>X\<close> itself and \<open>outerp X - Y\<close> the martingales,
  and those are not.\<close>

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
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?B \<kappa>"
  let ?t = "min u T"
  let ?C = "\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> ?t)) - snd (\<omega> ?t)"
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  interpret PQ': prob_space Q by (rule PQ)
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using padd_measurable_ksemi[OF T0 setsQ] measurable_cong_sets[OF setsS refl]
    by blast
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have hb: "?C \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<omega> ?t) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      ?C (padd T (fst p) (snd p))) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  have hint: "integrable Q
      (\<lambda>p'. norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
    by (intro Bochner_Integration.integrable_add integrable_norm[OF QCint]
        PQ'.integrable_const Bochner_Integration.integrable_mult_right
        integrable_mult_left integrable_norm[OF QXint])
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (?C (padd T (fst (p', w)) (snd (p', w)))))
        \<partial>(\<kappa> p'))
      \<le> ennreal (norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have iNC: "integrable (\<kappa> p') (\<lambda>w. norm (?C w))"
      by (rule integrable_norm[OF KCint[OF sp]])
    have iNX: "integrable (\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXint[OF sp]])
    have iB: "integrable (\<kappa> p') (\<lambda>w. norm (?C p') + norm (?C w)
        + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))))"
      by (intro Bochner_Integration.integrable_add PK.integrable_const iNC
          Bochner_Integration.integrable_mult_right integrable_mult_left iNX)
    have dom: "norm (?C (padd T p' w))
        \<le> norm (?C p') + norm (?C w) + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t)))"
      for w :: "'n pairpath" by (rule padd_comp_norm_le[OF tm])
    have mP: "(\<lambda>w :: 'n pairpath. norm (?C (padd T p' w)))
        \<in> borel_measurable (\<kappa> p')"
    proof -
      have "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
        by (rule padd_measurable_left[OF T0])
           (use sp space_of_path_sets[OF setsQ] in simp)
      from measurable_compose[OF this hb]
      have "(\<lambda>w :: 'n pairpath. ?C (padd T p' w)) \<in> borel_measurable ?B" .
      then have "(\<lambda>w :: 'n pairpath. ?C (padd T p' w))
          \<in> borel_measurable (\<kappa> p')"
        using measurable_cong_sets[OF sK refl] by blast
      then show ?thesis by measurable
    qed
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (?C (padd T p' w)))"
      by (rule Bochner_Integration.integrable_bound[OF iB mP])
         (use dom in \<open>intro AE_I2, simp\<close>)
    have "(\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))
        \<le> (\<integral>w. norm (?C p') + norm (?C w)
            + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))) \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono[OF iP iB]) (use dom in simp)
    also have "\<dots> = norm (?C p') + (\<integral>w. norm (?C w) \<partial>(\<kappa> p'))
        + 2 * (norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p')))"
      using iNC iNX PK.integrable_const
      by (simp add: PK.prob_space algebra_simps)
    also have "\<dots> \<le> norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX))"
    proof -
      have b1: "(\<integral>w. norm (?C w) \<partial>(\<kappa> p')) \<le> CC" by (rule KCbnd[OF sp])
      have b2: "norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p'))
          \<le> norm (fst (p' ?t)) * CX"
        by (rule mult_left_mono[OF KXbnd[OF sp] norm_ge_zero])
      from b1 b2 show ?thesis by linarith
    qed
    finally have le: "(\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))
        \<le> norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX))" .
    have "(\<integral>\<^sup>+w. ennreal (norm (?C (padd T p' w))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
      using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. ?C (padd T (fst p) (snd p)))"
    by (rule integrable_ksemi_of_past_bound[OF Kp ne gm hint]) (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) ?C
      = integrable ?S (\<lambda>p. ?C (padd T (fst p) (snd p)))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

subsection \<open>\<open>msecX\<close> and \<open>msecC\<close>\<close>

text \<open>One generic lemma covers both, and \<open>gintX\<close>/\<open>gintC\<close> too: the
  conditioning factor enters only through being measurable and bounded by
  \<open>1\<close> --- an \<open>indicator\<close> for \<open>msec\<close>, an indicator composed with
  \<^const>\<open>pcut\<close> for \<open>gint\<close>.\<close>

lemma aglue_section_measurable:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
  shows "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      cc (padd T (fst p) (snd p)) * h (padd T (fst p) (snd p)))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    using measurable_compose[OF pmP cb] measurable_compose[OF pmP hb] by simp
  have gi: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
    if sp: "p' \<in> space Q" for p'
  proof (rule Bochner_Integration.integrable_bound[OF Kint[OF sp]])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pl: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
      by (rule padd_measurable_left[OF T0])
         (use sp space_of_path_sets[OF setsQ] in simp)
    have "(\<lambda>w :: 'n pairpath. cc (padd T p' w) * h (padd T p' w))
        \<in> borel_measurable ?B"
      using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
    then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
        \<in> borel_measurable (\<kappa> p')"
      using measurable_cong_sets[OF sK refl] by blast
  next
    show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
        \<le> norm (h (padd T p' w))"
    proof (intro AE_I2)
      fix w :: "'n pairpath"
      have "norm (cc (padd T p' w) * h (padd T p' w))
          = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>" by (simp add: abs_mult)
      also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
        by (rule mult_right_mono[OF c1]) simp
      finally show "norm (cc (padd T p' w) * h (padd T p' w))
          \<le> norm (h (padd T p' w))" by simp
    qed
  qed
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
  have AB: "A \<in> sets ?B" using A by (simp add: sets_aglue_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis
      by (rule measurable_compose
          [OF measurable_compose[OF ev f] borel_measurable_nth])
  qed
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

text \<open>\<open>gintX\<close>/\<open>gintC\<close>: the same section integral, now integrable in the
  past.  Bounded by \<open>1\<close>, the conditioning factor cannot enlarge the inner
  integral, so the past bound that already served \<open>RXint\<close>/\<open>RCint\<close> serves
  here too.\<close>

lemma aglue_section_int_at:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and sp: "p' \<in> space Q"
  shows "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
proof (rule Bochner_Integration.integrable_bound[OF Kint])
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
  have pl: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule padd_measurable_left[OF T0])
       (use sp space_of_path_sets[OF setsQ] in simp)
  have "(\<lambda>w :: 'n pairpath. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable ?B"
    using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
  then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable (\<kappa> p')"
    using measurable_cong_sets[OF sK refl] by blast
next
  show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
      \<le> norm (h (padd T p' w))"
  proof (intro AE_I2)
    fix w :: "'n pairpath"
    have "norm (cc (padd T p' w) * h (padd T p' w))
        = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>" by (simp add: abs_mult)
    also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
      by (rule mult_right_mono[OF c1]) simp
    finally show "norm (cc (padd T p' w) * h (padd T p' w))
        \<le> norm (h (padd T p' w))" by simp
  qed
qed

lemma aglue_section_integrable:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and hb: "h \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and cb: "cc \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
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
      fix p' :: "'n pairpath" assume sp: "p' \<in> space Q"
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
            \<le> \<bar>h (padd T p' w)\<bar>" for w :: "'n pairpath"
        proof -
          have "\<bar>cc (padd T p' w) * h (padd T p' w)\<bar>
              = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>"
            by (simp add: abs_mult)
          also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
            by (rule mult_right_mono[OF c1]) simp
          finally show ?thesis by simp
        qed
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
  have AB: "A \<in> sets ?B" using A by (simp add: sets_aglue_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (rule linear_continuous_on[OF bl])
    show ?thesis
      by (rule measurable_compose[OF measurable_compose[OF ev s] n])
  qed
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
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis
      by (rule measurable_compose
          [OF measurable_compose[OF ev f] borel_measurable_nth])
  qed
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
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (rule linear_continuous_on[OF bl])
    show ?thesis
      by (rule measurable_compose[OF measurable_compose[OF ev s] n])
  qed
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed


(*<*)

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
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: 'n pairpath. w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  \<comment> \<open>the countable \<open>\<pi>\<close>-system, one per time\<close>
  have exPi: "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    if q: "q \<in> {0..?S}" for q
  proof (rule countable_pi_system_natural_filtration_path
      [where Q = ?Y and T = ?S and s = q])
    show "sets ?Y = sets (path_borel ?S :: ('n pairpath) measure)" ..
    show "0 \<le> q" using q by simp
    show "q \<le> ?S" using q by simp
    fix E assume "countable E" "Int_stable E" "E \<subseteq> Pow (space ?Y)"
      "space ?Y \<in> E" "sets (?G q) = sigma_sets (space ?Y) E"
    then show "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
        \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
      by (intro exI[of _ E] conjI)
  qed
  have "\<forall>q \<in> {0..?S}. \<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    using exPi by blast
  from bchoice[OF this] obtain Eg where
    Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
        \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
        \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  have Espec: "countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    if q: "q \<in> {0..?S}" for q by (rule bspec[OF Espec0 q])

  \<comment> \<open>the countably many almost-sure conditions\<close>
  have step: "AE p' in ?Q.
      (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
    if q: "q \<in> {0..?S}" and A': "A' \<in> sets (?G q)" for q A' and c :: 'n
    by (rule pfut_rcd_X_increment_zero[OF r rT setsP PS K eq mg _ _ _ A'])
       (use q in auto)
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have cEg: "countable (Eg q)" using Espec[OF True] by blast
      have "AE p' in ?Q. \<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
          (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ cEg])
        fix A' assume A': "A' \<in> Eg q"
        have AG: "A' \<in> sets (?G q)"
          using A' Espec[OF True] by auto
        show "AE p' in ?Q. \<forall>c \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
          by (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
             (use step[OF True AG] in blast)
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_X_integrable[OF r rT setsP PS K eq mg True]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S))"
    by (rule pfut_rcd_X_integrable[OF r rT setsP PS K eq mg SS])

  \<comment> \<open>and the assembly at each good \<open>p'\<close>\<close>
  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A' c. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow>
          integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
      and SI: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: ('n pairpath) metric)"
      by (simp add: space_borel_of)

    show ?case
    proof (rule martingale_vecI)
      fix c :: 'n
      have Zint: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)"
        if qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}" for q
      proof -
        have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RI[OF qrat q]])
        moreover have "min q ?S = q" using q by simp
        ultimately show ?thesis by simp
      qed
      have ZintS: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. fst (w (min ?S ?S)) $ c)"
      proof -
        have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          by (rule integrable_bounded_linear[OF bounded_linear_vec_nth SI])
        then show ?thesis by simp
      qed
      show "martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
          (\<lambda>u w. fst (w (min u ?S)) $ c)"
      proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "u \<in> {0..?S}" for u
          by (rule eval_component_measurable_nf[OF Tr]) (use that in simp)
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "0 \<le> u" for u
          by (rule eval_component_measurable_nf[OF Tr that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)"
          if "q \<in> \<rat>" "q \<in> {0..?S}" for q by (rule Zint[OF that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w (min ?S ?S)) $ c)"
          by (rule ZintS)
        show "continuous_on {0..?S} (\<lambda>u. fst (w (min u ?S)) $ c)"
          if "w \<in> space (\<kappa> p')" for w :: "'n pairpath"
          using that spK spY by (intro eval_component_continuous) simp
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            = (\<lambda>w. fst (w (min ?S ?S)) $ c)" if "?S \<le> u" for u
          using that by simp
        \<comment> \<open>the \<open>\<pi>\<close>-system widens to \<open>\<F>\<^sub>q\<close> at this fixed \<open>p'\<close>\<close>
        fix q :: real and A
        assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
          and A: "A \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) q)"
        have AG: "A \<in> sets (?G q)" using A nfK by simp
        have EgS: "countable (Eg q)" "Int_stable (Eg q)"
          "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
          "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
          using Espec[OF q] by blast+
        have subG: "subalgebra (\<kappa> p') (?G q)"
          using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
        have iq: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RI[OF qrat q]])
        have iS: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          by (rule integrable_bounded_linear[OF bounded_linear_vec_nth SI])
        have gi: "integrable (\<kappa> p')
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c)"
          by (rule Bochner_Integration.integrable_diff[OF iS iq])
        have gz: "set_lebesgue_integral (\<kappa> p') B
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c) = 0"
          if B: "B \<in> Eg q" for B
        proof -
          have "set_lebesgue_integral (\<kappa> p') B
                (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c)
              = (\<integral>w. indicator B w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p'))"
            unfolding set_lebesgue_integral_def by simp
          also have "\<dots> = 0" by (rule Z0[OF qrat q B])
          finally show ?thesis .
        qed
        have zA: "set_lebesgue_integral (\<kappa> p') A
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c) = 0"
          by (rule set_integral_zero_of_generator
              [OF subG gi EgS(2) _ _ _ gz AG])
             (use EgS(3) EgS(4) EgS(5) spK in simp_all)
        have AQ: "A \<in> sets (\<kappa> p')"
          using AG subG by (auto simp: subalgebra_def)
        have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iS])
        have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iq])
        have "set_lebesgue_integral (\<kappa> p') A
              (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)
            - set_lebesgue_integral (\<kappa> p') A (\<lambda>w. fst (w q) $ c) = 0"
          using set_integral_diff(2)[OF s1 s2] zA by simp
        then show "set_lebesgue_integral (\<kappa> p') A
              (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)
            = set_lebesgue_integral (\<kappa> p') A (\<lambda>w. fst (w (min ?S ?S)) $ c)"
          using q by simp
      qed
    qed
  qed
qed

subsection \<open>Clause (iv) for the conditional law\<close>

text \<open>The clause-(iv) twin of
  @{thm [source] pfut_rcd_X_increment_zero}.  Two differences, both
  bookkeeping: the \<open>P\<close>-side martingale is
  \<open>exit_class_pfut_comp_martingale\<close>, which lives in the
  shifted filtration and is therefore read at times \<open>i, j\<close> rather than
  \<open>r+i, r+j\<close> (the two agree, since \<open>?FP i = \<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> for \<open>i \<le> T-r\<close>); and
  the component is a matrix entry, so the bounded-linear map is
  \<open>bounded_linear_vec_nth\<close> composed with itself.\<close>

lemma pfut_rcd_comp_increment_zero:
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
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration ((path_borel (T - r) :: ('n pairpath) measure)) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w
        * ((outerp (fst (w j)) - snd (w j)
            - (outerp (fst (w i)) - snd (w i))) $ c $ d) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  let ?Zf = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (pfut r T \<omega> (min u ?S)))
      - snd (pfut r T \<omega> (min u ?S))"
  let ?h = "\<lambda>w :: 'n pairpath. (outerp (fst (w j)) - snd (w j)
      - (outerp (fst (w i)) - snd (w i))) $ c $ d"
  have Tr: "0 \<le> ?S" using rT by simp
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  have mi: "min i ?S = i" using iS by simp
  have mj: "min j ?S = j" using jS by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P ?FP 0 ?Zf by (rule mg)
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have A'Y: "A' \<in> sets ?Y"
    using A' sets_natural_filtration_path_subset[of ?S i] by blast

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

  \<comment> \<open>the integrand\<close>
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y" for u
    by (rule pair_law_eval_measurable[OF refl])
  have compm: "(\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))
      \<in> borel_measurable ?Y" for u
  proof -
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w u))) \<in> borel_measurable ?Y"
      by (rule measurable_compose
          [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w u)) \<in> borel_measurable ?Y"
      by (rule measurable_compose[OF ev pair_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed
  have entm: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
  have hm: "?h \<in> borel_measurable ?Y"
  proof -
    have "(\<lambda>w :: 'n pairpath. (outerp (fst (w j)) - snd (w j))
        - (outerp (fst (w i)) - snd (w i))) \<in> borel_measurable ?Y"
      by (rule borel_measurable_diff[OF compm compm])
    from measurable_compose[OF this entm] show ?thesis by simp
  qed

  \<comment> \<open>the shifted compensated process, and its integrability under \<open>P\<close>\<close>
  have hP: "(\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))
      = (\<lambda>\<omega>. (?Zf j \<omega> - ?Zf i \<omega>) $ c $ d)"
    by (rule ext) (simp add: mi mj)
  have hi: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))"
    unfolding hP
    by (rule integrable_bounded_linear[OF bl
        Bochner_Integration.integrable_diff[OF Mg.integrable Mg.integrable]])
       (use i0 ij jS in simp_all)
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?h (snd p))
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
  proof (rule integrable_ksemi_of_distr_rect)
    show "ksemi ?Q ?Y \<kappa> = distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>" by (rule eq'[symmetric])
    show "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y" by (rule mphi')
    show "?h \<in> borel_measurable ?Y" by (rule hm)
    show "A \<in> sets ?Q" by (rule A)
    show "A' \<in> sets ?Y" by (rule A'Y)
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))" by (rule hi)
  qed
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets (?FP i)"
      using rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'] mi by simp
    have SP: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets P"
      using Mg.sets_F_subset[OF i0] Sfilt by blast
    have veq: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P) (?Zf i)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P) (?Zf j)"
      by (rule Mg.set_integral_eq[OF Sfilt i0 ij])
    have comp: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. ?Zf i \<omega> $ c $ d)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. ?Zf j \<omega> $ c $ d)"
      unfolding set_integral_mat_component[OF SP Mg.integrable[OF i0]]
        set_integral_mat_component[OF SP Mg.integrable[OF order_trans[OF i0 ij]]]
      using veq by simp
    have si: "set_integrable P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?Zf u \<omega> $ c $ d)" if u: "0 \<le> u" for u
    proof -
      have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?Zf u \<omega> $ c $ d)"
        by (rule integrable_bounded_linear[OF bl Mg.integrable[OF u]])
      then show ?thesis
        unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP])
    qed
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. ?Zf j \<omega> $ c $ d - ?Zf i \<omega> $ c $ d)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. ?Zf j \<omega> $ c $ d)
          - set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. ?Zf i \<omega> $ c $ d)"
      by (rule set_integral_diff(2)[OF si[OF order_trans[OF i0 ij]] si[OF i0]])
    also have "\<dots> = 0" using comp by simp
    finally have zero: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>))) = 0"
      unfolding hP by simp
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

lemma pfut_rcd_comp_integrable:
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
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  let ?Zf = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (pfut r T \<omega> (min u ?S)))
      - snd (pfut r T \<omega> (min u ?S))"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      outerp (fst (snd p u)) - snd (snd p u)"
  have u0: "0 \<le> u" using u by simp
  have mu: "min u ?S = u" using u by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P ?FP 0 ?Zf by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
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
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have compm: "(\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))
      \<in> borel_measurable ?Y"
  proof -
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w u))) \<in> borel_measurable ?Y"
      by (rule measurable_compose
          [OF measurable_compose[OF ev pair_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w u)) \<in> borel_measurable ?Y"
      by (rule measurable_compose[OF ev pair_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd compm])
  have gP: "(\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>)) = ?Zf u"
    by (rule ext) (simp add: mu)
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>))"
      unfolding gP by (rule Mg.integrable[OF u0])
    then have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] .
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

text \<open>The two pointwise facts for the compensated entry, as for the
  coordinate.  Continuity is read off the expanded entry
  \<open>X\<^sub>t\<^sup>c X\<^sub>t\<^sup>d - Y\<^sub>t\<^sup>c\<^sup>d\<close> rather than through \<^const>\<open>outerp\<close>, which keeps everything
  inside products and differences of real continuous functions.\<close>

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
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?S = "T - r"
  let ?Y = "(path_borel ?S :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: 'n pairpath. w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  have exPi: "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    if q: "q \<in> {0..?S}" for q
  proof (rule countable_pi_system_natural_filtration_path
      [where Q = ?Y and T = ?S and s = q])
    show "sets ?Y = sets (path_borel ?S :: ('n pairpath) measure)" ..
    show "0 \<le> q" using q by simp
    show "q \<le> ?S" using q by simp
    fix E assume "countable E" "Int_stable E" "E \<subseteq> Pow (space ?Y)"
      "space ?Y \<in> E" "sets (?G q) = sigma_sets (space ?Y) E"
    then show "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
        \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
      by (intro exI[of _ E] conjI)
  qed
  have "\<forall>q \<in> {0..?S}. \<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    using exPi by blast
  from bchoice[OF this] obtain Eg where
    Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
        \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
        \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  have Espec: "countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    if q: "q \<in> {0..?S}" for q by (rule bspec[OF Espec0 q])

  have step: "AE p' in ?Q. (\<integral>w. indicator A' w
      * ((outerp (fst (w ?S)) - snd (w ?S)
          - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
    if q: "q \<in> {0..?S}" and A': "A' \<in> sets (?G q)" for q A' and c d :: 'n
    by (rule pfut_rcd_comp_increment_zero
        [OF r rT setsP PS K eq mg _ _ _ A']) (use q in auto)
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
            - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
          (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
              - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have cEg: "countable (Eg q)" using Espec[OF True] by blast
      have "AE p' in ?Q. \<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
          \<forall>d \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ cEg])
        fix A' assume A': "A' \<in> Eg q"
        have AG: "A' \<in> sets (?G q)" using A' Espec[OF True] by auto
        show "AE p' in ?Q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
        proof (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
          fix c :: 'n assume "c \<in> (UNIV :: 'n set)"
          show "AE p' in ?Q. \<forall>d \<in> (UNIV :: 'n set).
              (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                  - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
            by (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
               (use step[OF True AG] in blast)
        qed
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p')
        (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> integrable (\<kappa> p')
        (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_comp_integrable[OF r rT setsP PS K eq mg True]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p')
      (\<lambda>w :: 'n pairpath. outerp (fst (w ?S)) - snd (w ?S))"
    by (rule pfut_rcd_comp_integrable[OF r rT setsP PS K eq mg SS])

  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A' c d. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
              - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
      and SI: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. outerp (fst (w ?S)) - snd (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: ('n pairpath) metric)"
      by (simp add: space_borel_of)

    show ?case
    proof (rule martingale_matI)
      fix c d :: 'n
      have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
        by (rule bounded_linear_compose[OF bounded_linear_vec_nth
            bounded_linear_vec_nth])
      show "martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
          (\<lambda>u w. (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)"
      proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "u \<in> {0..?S}" for u
          by (rule comp_entry_measurable_nf[OF Tr]) (use that in simp)
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "0 \<le> u" for u by (rule comp_entry_measurable_nf[OF Tr that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min q ?S))) - snd (w (min q ?S))) $ c $ d)"
          if q: "q \<in> \<rat>" "q \<in> {0..?S}" for q
        proof -
          have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w q)) - snd (w q)) $ c $ d)"
            by (rule integrable_bounded_linear[OF bl RI[OF q]])
          moreover have "min q ?S = q" using q by simp
          ultimately show ?thesis by simp
        qed
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
        proof -
          have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
            by (rule integrable_bounded_linear[OF bl SI])
          then show ?thesis by simp
        qed
        show "continuous_on {0..?S}
            (\<lambda>u. (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)"
          if "w \<in> space (\<kappa> p')" for w :: "'n pairpath"
          using that spK spY by (intro comp_entry_continuous) simp
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            = (\<lambda>w. (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
          if "?S \<le> u" for u using that by simp
        fix q :: real and A
        assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
          and A: "A \<in> sets (natural_filtration (\<kappa> p') 0
              (\<lambda>v w :: 'n pairpath. w v) q)"
        have AG: "A \<in> sets (?G q)" using A nfK by simp
        have EgS: "countable (Eg q)" "Int_stable (Eg q)"
          "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
          "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
          using Espec[OF q] by blast+
        have subG: "subalgebra (\<kappa> p') (?G q)"
          using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
        have iq: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl RI[OF qrat q]])
        have iS: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl SI])
        have gi: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          by (rule Bochner_Integration.integrable_diff[OF iS iq])
        have gz: "set_lebesgue_integral (\<kappa> p') B (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          if B: "B \<in> Eg q" for B
        proof -
          have "set_lebesgue_integral (\<kappa> p') B (\<lambda>w :: 'n pairpath.
                (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
                - (outerp (fst (w q)) - snd (w q)) $ c $ d)
              = (\<integral>w. indicator B w * ((outerp (fst (w ?S)) - snd (w ?S)
                  - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p'))"
            unfolding set_lebesgue_integral_def by simp
          also have "\<dots> = 0" by (rule Z0[OF qrat q B])
          finally show ?thesis .
        qed
        have zA: "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          by (rule set_integral_zero_of_generator
              [OF subG gi EgS(2) _ _ _ gz AG])
             (use EgS(3) EgS(4) EgS(5) spK in simp_all)
        have AQ: "A \<in> sets (\<kappa> p')" using AG subG by (auto simp: subalgebra_def)
        have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iS])
        have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iq])
        have "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
              (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)
            - set_lebesgue_integral (\<kappa> p') A (\<lambda>w.
              (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          using set_integral_diff(2)[OF s1 s2] zA by simp
        then show "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min q ?S))) - snd (w (min q ?S))) $ c $ d)
            = set_lebesgue_integral (\<kappa> p') A (\<lambda>w.
              (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
          using q by simp
      qed
    qed
  qed
qed

subsection \<open>The conditional law is in the class\<close>

text \<open>The regular conditional distribution of the rebased future given the
  past lies, at almost every \<open>p'\<close>, in the paper's class (1.7) at the origin,
  from the four clauses: (i) @{thm [source] pfut_rcd_start}, (ii)
  \<open>pfut_rcd_diffquot\<close>, (iii)
  @{thm [source] pfut_rcd_X_martingale}, (iv)
  @{thm [source] pfut_rcd_comp_martingale}.  Under \<open>\<kappa> p'\<close> the starting point
  is a constant, so the shifted law lies in the class at that point and its
  essential infimum is bounded by \<open>exit_val\<close> by definition, with no
  localization and no \<open>K\<^sub>\<epsilon>\<close>.\<close>

(*<*)
end
(*>*)
