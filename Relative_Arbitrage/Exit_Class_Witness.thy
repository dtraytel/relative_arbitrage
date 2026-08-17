section \<open>Concrete pair processes, and nonemptiness of the class\<close>

(*<*)
theory Exit_Class_Witness
  imports Exit_Class_Shift
begin

(*>*)

section \<open>Laws of concrete pair processes\<close>

text \<open>A pair process on some filtered probability space pushes forward to
  a pair law, and a martingale for the process's own filtration is a
  martingale for the law's natural filtration --- the tower property, in
  the set-integral form: the natural filtration of the law pulls back into
  the process's filtration, because the process is adapted, and the
  set-integral identity is then the one the process already satisfies over
  the pulled-back event.\<close>

definition pair_law_of ::
  "real \<Rightarrow> ('a \<Rightarrow> 'n::finite pairpath) \<Rightarrow> 'a measure \<Rightarrow> ('n pairpath) measure"
  where "pair_law_of T \<phi> M =
     distr M (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))) \<phi>"

lemma sets_pair_law_of[simp]:
  "sets (pair_law_of T \<phi> M)
     = sets (borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric)))"
  unfolding pair_law_of_def by simp

lemma space_pair_law_of:
  "space (pair_law_of T \<phi> M)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding pair_law_of_def by (simp add: space_borel_of)

lemma phi_filtration_measurable:
  fixes M :: "'a measure" and \<phi> :: "'a \<Rightarrow> 'n::finite pairpath"
  assumes phim: "\<phi> \<in> M \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
    and adap: "\<And>r. 0 \<le> r \<Longrightarrow> r \<le> u \<Longrightarrow> (\<lambda>\<omega>. \<phi> \<omega> r) \<in> borel_measurable (FF u)"
    and spF: "space (FF u) = space M"
  shows "\<phi> \<in> FF u \<rightarrow>\<^sub>M natural_filtration (pair_law_of T \<phi> M) 0 (\<lambda>v \<omega>. \<omega> v) u"
proof -
  let ?Q = "pair_law_of T \<phi> M"
  have into: "\<phi> \<omega> \<in> space ?Q" if "\<omega> \<in> space M" for \<omega>
    using measurable_space[OF phim that] by (simp add: pair_law_of_def)
  show ?thesis
  proof (rule measurable_sigma_sets[OF sets_natural_filtration])
    show "(\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?Q | A. A \<in> sets borel})
        \<subseteq> Pow (space ?Q)" by auto
    show "\<phi> \<in> space (FF u) \<rightarrow> space ?Q" using spF into by auto
    fix y
    assume "y \<in> (\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?Q | A. A \<in> sets borel})"
    then obtain i A where i: "i \<in> {0..u}" and A: "A \<in> sets borel"
      and y: "y = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?Q" by blast
    have e: "\<phi> -` y \<inter> space (FF u) = (\<lambda>\<omega>. \<phi> \<omega> i) -` A \<inter> space (FF u)"
      using y spF into by auto
    have "(\<lambda>\<omega>. \<phi> \<omega> i) -` A \<inter> space (FF u) \<in> sets (FF u)"
      using i A by (intro measurable_sets[OF adap]) auto
    then show "\<phi> -` y \<inter> space (FF u) \<in> sets (FF u)" unfolding e .
  qed
qed

theorem martingale_pair_law:
  fixes M :: "'a measure" and \<phi> :: "'a \<Rightarrow> 'n::finite pairpath"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes prob: "prob_space M"
    and phim: "\<phi> \<in> M \<rightarrow>\<^sub>M borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))"
    and adap: "\<And>u r. 0 \<le> r \<Longrightarrow> r \<le> u \<Longrightarrow>
        (\<lambda>\<omega>. \<phi> \<omega> r) \<in> borel_measurable (FF u)"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable
        (natural_filtration (pair_law_of T \<phi> M) 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and mg: "martingale M FF 0 (\<lambda>u \<omega>. Z u (\<phi> \<omega>))"
  shows "martingale (pair_law_of T \<phi> M)
      (natural_filtration (pair_law_of T \<phi> M) 0 (\<lambda>v \<omega>. \<omega> v)) 0 Z"
proof -
  let ?Q = "pair_law_of T \<phi> M"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret MG: martingale M FF 0 "\<lambda>u \<omega>. Z u (\<phi> \<omega>)" by (rule mg)
  interpret P: prob_space M by (rule prob)
  have spF: "space (FF u) = space M" if u: "0 \<le> u" for u
    using MG.subalgebras[OF u] by (simp add: subalgebra_def)
  have prob': "prob_space ?Q"
    unfolding pair_law_of_def by (rule P.prob_space_distr[OF phim])
  have fin': "finite_measure ?Q" using prob' by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF sets_pair_law_of])
  interpret SF: finite_filtered_measure ?Q ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP fin'])
  have ZB: "Z w \<in> borel_measurable ?B" if w: "0 \<le> w" for w
  proof -
    have "Z w \<in> borel_measurable ?Q"
      by (rule measurable_from_subalg[OF SF.subalgebras[OF w] Zm[OF w]])
    then show ?thesis using measurable_cong_sets[OF sets_pair_law_of refl] by blast
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?Q ?G 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?G u)" by (rule Zm[OF u])
    qed
    show "integrable ?Q (Z u)" if u: "0 \<le> u" for u
    proof -
      have "integrable ?Q (Z u) \<longleftrightarrow> integrable M (\<lambda>\<omega>. Z u (\<phi> \<omega>))"
        unfolding pair_law_of_def by (rule integrable_distr_eq[OF phim ZB[OF u]])
      then show ?thesis using MG.integrable[OF u] by simp
    qed
    fix A and u v :: real
    assume A: "A \<in> ?G u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have AB: "A \<in> sets ?B"
      using A SF.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
    \<comment> \<open>\<open>adap\<close> has TWO \<open>\<And>\<close>-bound variables, so an \<open>OF\<close> against it produces
        "multiple unifiers"; let the conclusion drive the instantiation.\<close>
    have phiFm: "\<phi> \<in> FF u \<rightarrow>\<^sub>M ?G u"
    proof (rule phi_filtration_measurable[where T = T])
      show "\<phi> \<in> M \<rightarrow>\<^sub>M ?B" by (rule phim)
      show "(\<lambda>\<omega>. \<phi> \<omega> r) \<in> borel_measurable (FF u)" if "0 \<le> r" "r \<le> u" for r
        by (rule adap[OF that])
      show "space (FF u) = space M" by (rule spF[OF uv(1)])
    qed
    have pA: "\<phi> -` A \<inter> space M \<in> FF u"
      using measurable_sets[OF phiFm A] spF[OF uv(1)] by simp
    have key: "set_lebesgue_integral ?Q A (Z w)
        = set_lebesgue_integral M (\<phi> -` A \<inter> space M) (\<lambda>\<omega>. Z w (\<phi> \<omega>))"
      if w: "0 \<le> w" for w
    proof -
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable ?B"
        using AB ZB[OF w] by measurable
      have "set_lebesgue_integral ?Q A (Z w)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>?Q)"
        unfolding set_lebesgue_integral_def ..
      also have "\<dots> = (\<integral>\<omega>. indicat_real A (\<phi> \<omega>) *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
        unfolding pair_law_of_def by (rule integral_distr[OF phim gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real (\<phi> -` A \<inter> space M) \<omega>
              *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def .
    qed
    show "set_lebesgue_integral ?Q A (Z u) = set_lebesgue_integral ?Q A (Z v)"
      unfolding key[OF uv(1)] key[OF v0]
      by (rule MG.set_integral_eq[OF pA uv(1) uv(2)])
  qed
qed

text \<open>The other plumbing piece the witness needs: the class stops its
  processes at the horizon, so a martingale must be stopped at the
  deterministic time \<open>T\<close>.  \<open>martingale_stopped_const\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

section \<open>The off-diagonal covariation of Brownian motion\<close>

text \<open>The market locale's \<open>coord_Z_martingale\<close> gives only the diagonal
  compensator, but the paper's class needs the whole matrix \<open>outerp X - Y\<close>;
  off the diagonal the compensator is \<open>0\<close>, so what is needed is that
  \<open>W\<^sub>i W\<^sub>j\<close> is a martingale for \<open>i \<noteq> j\<close>.  This follows from independence of
  the coordinates of \<open>bm_paths = Pi\<^sub>M UNIV (\<lambda>_. wiener_pre)\<close>, via
  \<open>Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate\<close>.\<close>

lemma bm_coordinates_indep:
  "prob_space.indep_vars (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>_. wiener_pre) (\<lambda>k \<omega>. \<omega> k) UNIV"
proof -
  \<comment> \<open>\<open>Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate\<close> is not in scope
      here, so its six-line argument is repeated: the identity distribution
      of a product is the product of its component distributions, which is
      exactly the criterion \<open>indep_vars_iff_distr_eq_PiM'\<close>.  \<open>BMC\<close> is the
      \<open>product_prob_space\<close> interpretation already present in
      @{theory Relative_Arbitrage.Brownian_Market}.\<close>
  let ?P = "Pi\<^sub>M (UNIV :: 'n set) (\<lambda>_ :: 'n. wiener_pre)"
  have rv: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> k) \<in> measurable ?P wiener_pre" for k
    by (rule measurable_component_singleton) simp
  have "distr ?P ?P (\<lambda>x. restrict x UNIV) = distr ?P ?P (\<lambda>x. x)"
    by (rule distr_cong) (simp_all add: space_PiM)
  also have "\<dots> = ?P" by simp
  also have "\<dots> = Pi\<^sub>M UNIV (\<lambda>i :: 'n. distr ?P wiener_pre (\<lambda>f. f i))"
    by (intro PiM_cong) (auto simp: BMC.PiM_component)
  finally have eq: "distr ?P (Pi\<^sub>M UNIV (\<lambda>_ :: 'n. wiener_pre))
      (\<lambda>x. \<lambda>i\<in>UNIV. x i)
      = Pi\<^sub>M UNIV (\<lambda>i :: 'n. distr ?P wiener_pre (\<lambda>f. f i))"
    by (simp add: restrict_def)
  have "prob_space.indep_vars ?P (\<lambda>_. wiener_pre) (\<lambda>k \<omega>. \<omega> k) UNIV"
    by (subst BMC.P.indep_vars_iff_distr_eq_PiM'[OF _ rv]) (use eq in auto)
  then show ?thesis unfolding bm_paths_def .
qed

lemma bm_increment_coord_indep:
  fixes i j :: "'n::finite"
  assumes ij: "i \<noteq> j" and s: "0 \<le> s" and st: "s \<le> t"
  shows "prob_space.indep_var (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      borel (\<lambda>\<omega>. \<omega> i t - \<omega> i s) borel (\<lambda>\<omega>. \<omega> j t - \<omega> j s)"
proof -
  \<comment> \<open>use the GLOBAL interpretation \<open>BMP\<close> of \<open>prob_space\<close> at \<open>bm_paths\<close>: an
      \<open>interpret\<close> against a \<open>let\<close>-bound \<open>?M\<close> yields "Undefined constant".\<close>
  have co: "BMP.indep_vars (\<lambda>_. wiener_pre) (\<lambda>k \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> k) UNIV"
    by (rule bm_coordinates_indep)
  have f: "(\<lambda>w. w t - w s) \<in> borel_measurable wiener_pre"
    using s st by (intro borel_measurable_diff measurable_coord) auto
  have co2: "BMP.indep_vars (\<lambda>_. borel)
      (\<lambda>k \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> k t - \<omega> k s) UNIV"
    by (rule BMP.indep_vars_compose2[OF co]) (use f in auto)
  have r: "BMP.indep_var
      (Pi\<^sub>M {i} (\<lambda>_. borel))
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict (\<lambda>k. \<omega> k t - \<omega> k s) {i})
      (Pi\<^sub>M {j} (\<lambda>_. borel))
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict (\<lambda>k. \<omega> k t - \<omega> k s) {j})"
    by (rule BMP.indep_var_restrict[OF co2]) (use ij in auto)
  have p: "(\<lambda>f. f i) \<in> Pi\<^sub>M {i} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
    by (rule measurable_component_singleton) simp
  have q: "(\<lambda>f. f j) \<in> Pi\<^sub>M {j} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
    by (rule measurable_component_singleton) simp
  from BMP.indep_var_compose[OF r p q] show ?thesis by (simp add: o_def)
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
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  have t0: "0 \<le> t" using s st by simp
  have ind: "BMP.indep_var borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i t - \<omega> i s)
      borel (\<lambda>\<omega>. \<omega> j t - \<omega> j s)"
    by (rule bm_increment_coord_indep[OF ij s st])
  show "integrable ?M (\<lambda>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))"
    by (rule BMP.indep_var_integrable[OF ind
        bm_increment_component_integrable[OF s t0]
        bm_increment_component_integrable[OF s t0]])
  have "(\<integral>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s) \<partial>?M)
      = (\<integral>\<omega>. \<omega> i t - \<omega> i s \<partial>?M) * (\<integral>\<omega>. \<omega> j t - \<omega> j s \<partial>?M)"
    by (rule BMP.indep_var_lebesgue_integral[OF ind
        bm_increment_component_integrable[OF s t0]
        bm_increment_component_integrable[OF s t0]])
  also have "\<dots> = 0"
    by (simp add: bm_increment_component_integral[OF s t0])
  finally show "(\<integral>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s) \<partial>?M) = 0" .
qed

text \<open>\<open>Brownian_Market.bm_meas_increment_indep_var\<close> generalises verbatim to
  any Borel function of the vector increment, since its argument only uses
  that --- and \<open>v \<mapsto> v$i \<sqdot> v$j\<close> is one.\<close>

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
  let ?V = "vimage_algebra (space ?M) ?D borel"
  have SP: "Stochastic_Process.stochastic_process ?M (0::real) (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration[OF SP])
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
    show ?thesis using sets.sigma_sets_subset[OF gen] by simp
  qed
  have R: "sigma_sets (space ?M)
      {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?V"
  proof -
    have gen: "{(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) -` B \<inter> space ?M
        |B. B \<in> sets borel} \<subseteq> sets ?V"
    proof safe
      fix B :: "real set" assume B: "B \<in> sets borel"
      have Ci: "h -` B \<in> sets borel"
        using measurable_sets[OF h B] by simp
      have veq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) -` B \<inter> space ?M
          = ?D -` (h -` B) \<inter> space ?M" by auto
      have "?D -` (h -` B) \<inter> space ?M
          \<in> {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        using Ci by blast
      then have "?D -` (h -` B) \<inter> space ?M
          \<in> sigma_sets (space ?M) {?D -` C \<inter> space ?M |C. C \<in> sets borel}"
        by (rule sigma_sets.Basic)
      then show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) -` B \<inter> space ?M
          \<in> sets ?V"
        unfolding veq sets_vimage_algebra .
    qed
    show ?thesis using sets.sigma_sets_subset[OF gen] by simp
  qed
  show ?thesis
    unfolding BMP.indep_var_eq
  proof (intro conjI)
    show "g \<in> borel_measurable ?M" by (rule g_M)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) \<in> borel_measurable ?M"
      using s st
      by (intro measurable_compose[OF _ h] borel_measurable_diff
          measurable_bmX) auto
    have "BMP.indep_sets (case_bool (sets ?F) (sets ?V)) UNIV"
      using base unfolding BMP.indep_set_def .
    then have "BMP.indep_sets (case_bool
        (sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) -` B \<inter> space ?M
            |B. B \<in> sets borel})) UNIV"
      by (rule BMP.indep_sets_mono_sets)
        (auto split: bool.split simp: L R)
    then show "BMP.indep_set
        (sigma_sets (space ?M) {g -` B \<inter> space ?M |B. B \<in> sets borel})
        (sigma_sets (space ?M)
          {(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. h (?D \<omega>)) -` B \<inter> space ?M
            |B. B \<in> sets borel})"
      unfolding BMP.indep_set_def .
  qed
qed

text \<open>Hence over a past event the cross increment has integral zero --- the
  off-diagonal analogue of \<open>Brownian_Market.bm_set_integral_coord_sq_eq\<close>,
  with compensator \<open>0\<close> rather than \<open>t - s\<close> because the coordinates are
  independent.\<close>

lemma bm_cross_set_integral_zero:
  fixes x0 :: "real^'n::finite" and i j :: 'n
  assumes ij: "i \<noteq> j" and s: "0 \<le> s" and st: "s \<le> t"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) s)"
  shows "(\<integral>\<omega>. indicat_real A \<omega> * ((\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))
       \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof (cases "s = t")
  case True
  then show ?thesis by simp
next
  case False
  with st have st': "s < t" by simp
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) s"
  have SP: "Stochastic_Process.stochastic_process ?M (0::real) (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration[OF SP])
  have AM: "A \<in> sets ?M" using A subalg by (auto simp: subalgebra_def)
  have hB: "(\<lambda>v :: real^'n. v $ i * v $ j) \<in> borel_measurable borel"
    by (intro borel_measurable_times borel_measurable_nth)
  have feq: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        (bmX x0 t \<omega> - bmX x0 s \<omega>) $ i * (bmX x0 t \<omega> - bmX x0 s \<omega>) $ j)
      = (\<lambda>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))"
    by (simp add: fun_eq_iff bmX_def)
  have ind: "BMP.indep_var borel (indicat_real A :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real)
      borel (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))"
    using bm_meas_increment_fun_indep_var[OF s st'
        borel_measurable_indicator[OF A] hB]
    unfolding feq .
  have int1: "integrable ?M (indicat_real A)"
    by (rule integrable_real_indicator[OF AM])
      (simp add: BMP.emeasure_eq_measure)
  have int2: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s))"
    by (rule bm_increment_cross_integrable[OF ij s st])
  have "(\<integral>\<omega>. indicat_real A \<omega> * ((\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s)) \<partial>?M)
      = (\<integral>\<omega>. indicat_real A \<omega> \<partial>?M)
        * (\<integral>\<omega>. (\<omega> i t - \<omega> i s) * (\<omega> j t - \<omega> j s) \<partial>?M)"
    by (rule BMP.indep_var_lebesgue_integral[OF ind int1 int2])
  also have "\<dots> = 0"
    by (simp add: bm_increment_cross_integral[OF ij s st])
  finally show ?thesis .
qed

text \<open>The martingale identity for the off-diagonal product.  Splitting
  \<open>X\<^sub>i(v)X\<^sub>j(v) - X\<^sub>i(u)X\<^sub>j(u) = X\<^sub>i(u)\<Delta>\<^sub>j + X\<^sub>j(u)\<Delta>\<^sub>i + \<Delta>\<^sub>i\<Delta>\<^sub>j\<close>, the first two
  terms vanish by \<open>Brownian_Market.bm_meas_increment_product_zero\<close> and the
  third by \<open>bm_cross_set_integral_zero\<close>.\<close>

lemma bm_cross_increment_set_integral_zero:
  fixes x0 :: "real^'n::finite" and i j :: 'n
  assumes ij: "i \<noteq> j" and u: "0 \<le> u" and uv: "u \<le> v"
    and A: "A \<in> sets (natural_filtration
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (bmX x0) u)"
  shows "(\<integral>\<omega>. indicat_real A \<omega> * (bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j
            - bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)
       \<partial>(bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0) u"
  have SP: "Stochastic_Process.stochastic_process ?M (0::real) (bmX x0)"
    by unfold_locales (intro measurable_bmX, simp)
  have subalg: "subalgebra ?M ?F"
    by (rule Stochastic_Process.stochastic_process.subalgebra_natural_filtration[OF SP])
  have AM: "A \<in> sets ?M" using A subalg by (auto simp: subalgebra_def)
  \<comment> \<open>the two past-measurable multipliers\<close>
  have cm: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 u \<omega> $ k) \<in> borel_measurable ?F"
    for k
  proof -
    have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. x0 $ k + \<omega> k u) \<in> borel_measurable ?F"
      by (intro borel_measurable_add borel_measurable_const
          bm_coordinate_measurable_F[OF u])
    then show ?thesis by (simp add: bmX_def)
  qed
  have gm: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. indicat_real A \<omega> * bmX x0 u \<omega> $ k)
      \<in> borel_measurable ?F" for k
    by (rule borel_measurable_times[OF borel_measurable_indicator[OF A] cm])
  have gi: "integrable ?M
      (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. indicat_real A \<omega> * bmX x0 u \<omega> $ k)" for k
  proof -
    have "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 u \<omega> $ k)"
      using BMP.integrable_const bm_coordinate_mean_integrable[OF u, of k]
      by (simp add: bmX_def)
    then have "integrable ?M
        (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. indicat_real A \<omega> *\<^sub>R bmX x0 u \<omega> $ k)"
      by (rule integrable_mult_indicator[OF AM])
    then show ?thesis by simp
  qed
  have z1: "(\<integral>\<omega>. (indicat_real A \<omega> * bmX x0 u \<omega> $ i) * (\<omega> j v - \<omega> j u) \<partial>?M) = 0"
    by (rule bm_meas_increment_product_zero[OF u uv gm gi])
  have z2: "(\<integral>\<omega>. (indicat_real A \<omega> * bmX x0 u \<omega> $ j) * (\<omega> i v - \<omega> i u) \<partial>?M) = 0"
    by (rule bm_meas_increment_product_zero[OF u uv gm gi])
  have z3: "(\<integral>\<omega>. indicat_real A \<omega> * ((\<omega> i v - \<omega> i u) * (\<omega> j v - \<omega> j u)) \<partial>?M) = 0"
    by (rule bm_cross_set_integral_zero[OF ij u uv A])
  have i1: "integrable ?M
      (\<lambda>\<omega>. (indicat_real A \<omega> * bmX x0 u \<omega> $ i) * (\<omega> j v - \<omega> j u))"
    by (rule bm_meas_increment_product_integrable[OF u uv gm gi])
  have i2: "integrable ?M
      (\<lambda>\<omega>. (indicat_real A \<omega> * bmX x0 u \<omega> $ j) * (\<omega> i v - \<omega> i u))"
    by (rule bm_meas_increment_product_integrable[OF u uv gm gi])
  have i3: "integrable ?M
      (\<lambda>\<omega>. indicat_real A \<omega> * ((\<omega> i v - \<omega> i u) * (\<omega> j v - \<omega> j u)))"
  proof -
    have "integrable ?M
        (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
           indicat_real A \<omega> *\<^sub>R ((\<omega> i v - \<omega> i u) * (\<omega> j v - \<omega> j u)))"
      by (rule integrable_mult_indicator[OF AM
          bm_increment_cross_integrable[OF ij u uv]])
    then show ?thesis by simp
  qed
  have decomp: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. indicat_real A \<omega>
        * (bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j - bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j))
      = (\<lambda>\<omega>. (indicat_real A \<omega> * bmX x0 u \<omega> $ i) * (\<omega> j v - \<omega> j u)
          + (indicat_real A \<omega> * bmX x0 u \<omega> $ j) * (\<omega> i v - \<omega> i u)
          + indicat_real A \<omega> * ((\<omega> i v - \<omega> i u) * (\<omega> j v - \<omega> j u)))"
    by (simp add: fun_eq_iff bmX_def algebra_simps)
  have "(\<integral>\<omega>. indicat_real A \<omega>
          * (bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j
             - bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j) \<partial>?M)
      = (\<integral>\<omega>. (indicat_real A \<omega> * bmX x0 u \<omega> $ i) * (\<omega> j v - \<omega> j u)
            + (indicat_real A \<omega> * bmX x0 u \<omega> $ j) * (\<omega> i v - \<omega> i u) \<partial>?M)
        + (\<integral>\<omega>. indicat_real A \<omega> * ((\<omega> i v - \<omega> i u) * (\<omega> j v - \<omega> j u)) \<partial>?M)"
    unfolding decomp
    by (rule Bochner_Integration.integral_add) (auto intro: i1 i2 i3)
  also have "\<dots> = 0"
    using z3 z1 z2 i1 i2 by simp
  finally show ?thesis .
qed

lemma bmX_coord_measurable_F:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 u \<omega> $ k) \<in> borel_measurable
      (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
        (bmX x0) u)"
proof -
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. x0 $ k + \<omega> k u) \<in> borel_measurable
      (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
        (bmX x0) u)"
    by (intro borel_measurable_add borel_measurable_const
        bm_coordinate_measurable_F[OF u])
  then show ?thesis by (simp add: bmX_def)
qed

lemma bmX_cross_integrable:
  fixes x0 :: "real^'n::finite"
  assumes u: "0 \<le> u"
  shows "integrable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>\<omega>. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  have sq: "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (bmX x0 u \<omega> $ k)\<^sup>2)"
    for k
    using bm_coordinate_sq_integrable[OF u, of "x0 $ k" k]
    by (simp add: bmX_def)
  \<comment> \<open>\<open>|ab| \<le> a\<^sup>2 + b\<^sup>2\<close>, from \<open>sum_squares_bound\<close> at \<open>|a|\<close>, \<open>|b|\<close>\<close>
  have abs_le: "\<bar>a * b\<bar> \<le> a\<^sup>2 + b\<^sup>2" for a b :: real
  proof -
    have s: "2 * \<bar>a\<bar> * \<bar>b\<bar> \<le> \<bar>a\<bar>\<^sup>2 + \<bar>b\<bar>\<^sup>2" by (rule sum_squares_bound)
    have s': "2 * (\<bar>a\<bar> * \<bar>b\<bar>) \<le> a\<^sup>2 + b\<^sup>2" using s by (simp add: mult.assoc)
    have nn: "0 \<le> \<bar>a\<bar> * \<bar>b\<bar>" by simp
    have "\<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>" by (simp add: abs_mult)
    also have "\<dots> \<le> a\<^sup>2 + b\<^sup>2" using s' nn by linarith
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound
      [where f = "\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (bmX x0 u \<omega> $ i)\<^sup>2 + (bmX x0 u \<omega> $ j)\<^sup>2"])
    show "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        (bmX x0 u \<omega> $ i)\<^sup>2 + (bmX x0 u \<omega> $ j)\<^sup>2)"
      by (intro Bochner_Integration.integrable_add sq)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)
        \<in> borel_measurable ?M"
      using u by (intro borel_measurable_times measurable_bm_coordinate
          borel_measurable_add borel_measurable_const) (auto simp: bmX_def)
    show "AE \<omega> in ?M. norm (bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)
        \<le> norm ((bmX x0 u \<omega> $ i)\<^sup>2 + (bmX x0 u \<omega> $ j)\<^sup>2)"
      by (intro always_eventually allI) (simp add: abs_le)
  qed
qed

theorem martingale_bm_cross:
  fixes x0 :: "real^'n::finite" and i j :: 'n
  assumes ij: "i \<noteq> j"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (bmX x0)) 0
      (\<lambda>u \<omega>. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (bmX x0)"
  interpret MX: martingale ?M ?F 0 "bmX x0" by (rule martingale_bmX)
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process ?M ?F 0 (\<lambda>u \<omega>. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "(\<lambda>\<omega>. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j) \<in> borel_measurable (?F u)"
        by (intro borel_measurable_times bmX_coord_measurable_F[OF u])
    qed
    show "integrable ?M (\<lambda>\<omega>. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)"
      if u: "0 \<le> u" for u by (rule bmX_cross_integrable[OF u])
    fix A and u v :: real
    assume A: "A \<in> ?F u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have Ai: "A \<in> sets ?M"
      using A MX.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
    have ii: "integrable ?M
        (\<lambda>\<omega>. indicat_real A \<omega> * (bmX x0 w \<omega> $ i * bmX x0 w \<omega> $ j))"
      if w: "0 \<le> w" for w
    proof -
      have "integrable ?M (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          indicat_real A \<omega> *\<^sub>R (bmX x0 w \<omega> $ i * bmX x0 w \<omega> $ j))"
        by (rule integrable_mult_indicator[OF Ai bmX_cross_integrable[OF w]])
      then show ?thesis by simp
    qed
    have eqv: "set_lebesgue_integral ?M A
          (\<lambda>\<omega>. bmX x0 w \<omega> $ i * bmX x0 w \<omega> $ j)
        = (\<integral>\<omega>. indicat_real A \<omega> * (bmX x0 w \<omega> $ i * bmX x0 w \<omega> $ j) \<partial>?M)"
      for w
      unfolding set_lebesgue_integral_def by simp
    have "(\<integral>\<omega>. indicat_real A \<omega> * (bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j) \<partial>?M)
        - (\<integral>\<omega>. indicat_real A \<omega> * (bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j) \<partial>?M)
        = (\<integral>\<omega>. indicat_real A \<omega> * (bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j)
              - indicat_real A \<omega> * (bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j) \<partial>?M)"
      by (rule Bochner_Integration.integral_diff[symmetric])
        (rule ii[OF v0], rule ii[OF uv(1)])
    also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega>
            * (bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j
               - bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j) \<partial>?M)"
      by (rule Bochner_Integration.integral_cong) (auto simp: algebra_simps)
    also have "\<dots> = 0"
      by (rule bm_cross_increment_set_integral_zero[OF ij uv A])
    finally show "set_lebesgue_integral ?M A
          (\<lambda>\<omega>. bmX x0 u \<omega> $ i * bmX x0 u \<omega> $ j)
        = set_lebesgue_integral ?M A
          (\<lambda>\<omega>. bmX x0 v \<omega> $ i * bmX x0 v \<omega> $ j)"
      unfolding eqv by simp
  qed
qed

text \<open>Transfer to the continuous modification via
  \<open>Modification_Transfer.martingale_of_modification_gen\<close>, as
  \<open>Brownian_Continuous.martingale_cbm_coord_square\<close> does for the diagonal.\<close>

lemma bm_prj_measurable: "(\<lambda>x :: real^'n::finite. x $ i) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI linear_continuous_on
      bounded_linear_vec_nth)

theorem martingale_cbm_cross:
  fixes x0 :: "real^'n::finite" and i j :: 'n
  assumes ij: "i \<noteq> j"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) 0
      (\<lambda>t \<omega>. cbmX x0 t \<omega> $ i * cbmX x0 t \<omega> $ j)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0)"
  let ?Y = "\<lambda>t \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmX x0 t \<omega> $ i * bmX x0 t \<omega> $ j"
  let ?Y' = "\<lambda>t \<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cbmX x0 t \<omega> $ i * cbmX x0 t \<omega> $ j"
  have measY': "?Y' u \<in> borel_measurable ?M" for u
    by (intro borel_measurable_times
        measurable_compose[OF measurable_cbmX bm_prj_measurable])
  have aeY: "AE \<omega> in ?M. ?Y' u \<omega> = ?Y u \<omega>" if u: "0 \<le> u" for u
  proof -
    have "AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      using u by (intro cbmX_ae_eq) simp
    then show ?thesis by eventually_elim simp
  qed
  show ?thesis
  proof (rule martingale_of_modification_gen[where X = "bmX x0" and Y = ?Y])
    show "prob_space ?M" by simp
    show "martingale ?M (natural_filtration ?M 0 (bmX x0)) 0 ?Y"
      by (rule martingale_bm_cross[OF ij])
    show "\<And>u. 0 \<le> u \<Longrightarrow> bmX x0 u \<in> borel_measurable ?M"
      by (intro measurable_bmX) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
      by (rule measurable_cbmX)
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. cbmX x0 u \<omega> = bmX x0 u \<omega>"
      by (intro cbmX_ae_eq) simp
    show "\<And>u. 0 \<le> u \<Longrightarrow> ?Y' u \<in> borel_measurable ?M" by (rule measY')
    show "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in ?M. ?Y' u \<omega> = ?Y u \<omega>" by (rule aeY)
    show "adapted_process ?M ?F 0 ?Y'"
    proof (rule adapted_of_natural_filtration
        [where f = "\<lambda>u y :: real^'n. (y $ i) * (y $ j)"])
      show "\<And>u. 0 \<le> u \<Longrightarrow> cbmX x0 u \<in> borel_measurable ?M"
        by (rule measurable_cbmX)
      show "\<And>u. (\<lambda>y :: real^'n. (y $ i) * (y $ j)) \<in> borel_measurable borel"
        by (intro borel_measurable_times bm_prj_measurable)
    qed
  qed
qed

text \<open>The whole matrix, assembled entrywise by \<open>martingale_matI\<close>: the
  diagonal from \<open>martingale_cbm_coord_square\<close> (compensator \<open>t\<close>, via
  \<open>martingale_cong_ge\<close>), the off-diagonal from \<open>martingale_cbm_cross\<close>
  (compensator \<open>0\<close>).\<close>

theorem martingale_cbm_outerp:
  fixes x0 :: "real^'n::finite"
  shows "martingale (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) 0
      (\<lambda>t \<omega>. outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1)"
proof (rule martingale_matI)
  fix i j :: 'n
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?F = "natural_filtration ?M 0 (cbmX x0)"
  have comp: "set_lebesgue_integral lborel {0..t}
      (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i) = t" if t: "0 \<le> t" for t
  proof -
    have "set_lebesgue_integral lborel {0..t}
        (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i)
        = t * ((mat 1 :: real^'n^'n) $ i $ i)"
      using t by (subst set_integral_const) auto
    then show ?thesis by (simp add: mat_def)
  qed
  show "martingale ?M ?F 0
      (\<lambda>t \<omega>. (outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1) $ i $ j)"
  proof (cases "i = j")
    case True
    show ?thesis
    proof (rule martingale_cong_ge[OF martingale_cbm_coord_square])
      fix t :: real assume t: "0 \<le> t"
      show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. (cbmX x0 t \<omega> $ i)\<^sup>2
            - set_lebesgue_integral lborel {0..t}
                (\<lambda>s. (mat 1 :: real^'n^'n) $ i $ i))
          = (\<lambda>\<omega>. (outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1) $ i $ j)"
        using True comp[OF t]
        by (simp add: outerp_def power2_eq_square mat_def)
    qed
  next
    case False
    show ?thesis
    proof (rule martingale_cong_ge[OF martingale_cbm_cross[OF False]])
      fix t :: real assume t: "0 \<le> t"
      show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cbmX x0 t \<omega> $ i * cbmX x0 t \<omega> $ j)
          = (\<lambda>\<omega>. (outerp (cbmX x0 t \<omega>) - t *\<^sub>R mat 1) $ i $ j)"
        using False by (simp add: outerp_def mat_def)
    qed
  qed
qed

section \<open>The paper's class is nonempty\<close>

text \<open>The witness: Brownian motion started at \<open>0\<close> paired with the
  deterministic covariation \<open>Y\<^sub>t = t \<sqdot> I\<close>, capped at the horizon.\<close>

definition bmpair :: "real \<Rightarrow> ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath"
  where "bmpair T \<omega> = restrict (\<lambda>t. (cbmX 0 t \<omega>, t *\<^sub>R mat 1)) {0..T}"

lemma bmpair_apply:
  "t \<in> {0..T} \<Longrightarrow> bmpair T \<omega> t = (cbmX 0 t \<omega>, t *\<^sub>R mat 1)"
  by (simp add: bmpair_def)

lemma continuous_on_bmpair_path:
  fixes \<omega> :: "'n::finite \<Rightarrow> real \<Rightarrow> real"
  shows "continuous_on {0..T}
      (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))"
proof (intro continuous_on_Pair)
  show "continuous_on {0..T} (\<lambda>t. cbmX (0 :: real^'n) t \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
  show "continuous_on {0..T} (\<lambda>t. t *\<^sub>R (mat 1 :: real^'n^'n))"
    by (rule linear_continuous_on[OF bounded_linear_scaleR_left])
qed

lemma bmpair_measurable:
  assumes T: "0 \<le> T"
  shows "(bmpair T :: ('n::finite \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      \<in> bm_paths \<rightarrow>\<^sub>M borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))"
proof -
  \<comment> \<open>the intermediate statement carries FULL type annotations; without them
      the obligations \<open>pathify_measurable\<close> generates elaborate at types the
      component lemmas no longer match.\<close>
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n))) {0..T})
      \<in> bm_paths \<rightarrow>\<^sub>M borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))"
  proof (rule pathify_measurable[OF T])
    fix t :: real assume "t \<in> {0..T}"
    have c: "(\<lambda>v :: real^'n. (v, t *\<^sub>R (mat 1 :: real^'n^'n)))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))
        \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
      by (rule measurable_compose[OF measurable_cbmX c])
  next
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    show "continuous_on {0..T}
        (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n)))"
      by (rule continuous_on_bmpair_path)
  qed
  moreover have "(bmpair T :: ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'n pairpath)
      = (\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. restrict
          (\<lambda>t. (cbmX (0 :: real^'n) t \<omega>, t *\<^sub>R (mat 1 :: real^'n^'n))) {0..T})"
    by (rule ext) (simp add: bmpair_def)
  ultimately show ?thesis by simp
qed

lemma prob_space_bmpair_law:
  assumes T: "0 \<le> T"
  shows "prob_space (pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))"
  unfolding pair_law_of_def
  by (rule BMP.prob_space_distr[OF bmpair_measurable[OF T]])

subsection \<open>The two almost-sure clauses for the witness\<close>

lemma bmpair_law_start:
  assumes T: "0 \<le> T"
  shows "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have phim: "bmpair T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule bmpair_measurable[OF T])
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
      \<in> sets ?B"
  proof -
    have "{\<omega> \<in> space ?B. fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(0, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have iff: "(AE \<omega> in pair_law_of T (bmpair T) ?M.
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0)
      = (AE \<omega> in ?M. fst (bmpair T \<omega> 0) = (0 :: real^'n)
          \<and> snd (bmpair T \<omega> 0) = 0)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
  have z: "(0::real) \<in> {0..T}" using T by simp
  have "AE \<omega> in ?M. cbmX (0 :: real^'n) 0 \<omega> = bmX 0 0 \<omega>"
    by (intro cbmX_ae_eq) simp
  moreover have "AE \<omega> in ?M. bmX (0 :: real^'n) 0 \<omega> = 0"
    by (rule bmX_start)
  ultimately have "AE \<omega> in ?M. fst (bmpair T \<omega> 0) = (0 :: real^'n)
      \<and> snd (bmpair T \<omega> 0) = 0"
    by eventually_elim (simp add: bmpair_apply[OF z])
  then show ?thesis unfolding iff .
qed

lemma bmpair_law_diffquot:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (bmpair T) ?M"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have phim: "bmpair T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule bmpair_measurable[OF T])
  have spQ: "space ?Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_pair_law_of)
  have one: "AE \<omega> in ?Q.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    if pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" for p q :: real
  proof -
    have mm: "{\<omega> \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L}
        \<in> sets ?B"
      using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
      by (simp add: space_borel_of)
    have iff: "(AE \<omega> in ?Q.
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L)
        = (AE \<omega> in ?M. (1 / (q - p))
            *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p)) \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in ?M. (1 / (q - p))
        *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p)) \<in> sconstraint k L"
    proof (intro AE_I2)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      have "(1 / (q - p)) *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p))
          = (1 / (q - p)) *\<^sub>R ((q - p) *\<^sub>R (mat 1 :: real^'n^'n))"
        using pq by (simp add: bmpair_apply scaleR_left_diff_distrib)
      also have "\<dots> = (mat 1 :: real^'n^'n)"
        using pq(3) by simp
      finally show "(1 / (q - p))
          *\<^sub>R (snd (bmpair T \<omega> q) - snd (bmpair T \<omega> p)) \<in> sconstraint k L"
        using mat_1_in_sconstraint[OF L] by simp
    qed
    then show ?thesis unfolding iff .
  qed
  \<comment> \<open>the rational reduction, exactly as in
      \<open>Exit_Class.exit_class_diffquot_limit\<close>\<close>
  have rat: "AE \<omega> in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in ?Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in ?Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      proof (cases "0 \<le> p \<and> p < q \<and> q \<le> T")
        case True
        then have "p \<in> {0..T}" "q \<in> {0..T}" "p < q" by auto
        from one[OF this] show ?thesis by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  from rat AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      and W: "\<omega> \<in> space ?Q" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spQ by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
        by (rule diffquot_all_of_rational
            [OF closed_sconstraint cont _ uv(1) uv(2) uv(3)]) (rule R)
    qed
  qed
qed

subsection \<open>The two martingale clauses for the witness\<close>

lemma bmpair_adapted:
  fixes r u :: real
  assumes r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n::finite \<Rightarrow> real \<Rightarrow> real. bmpair T \<omega> r) \<in> borel_measurable
      (natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
        (cbmX (0 :: real^'n)) u)"
proof (cases "r \<in> {0..T}")
  case True
  let ?F = "natural_filtration (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0
      (cbmX (0 :: real^'n))"
  interpret MC: martingale "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure" ?F 0
      "cbmX (0 :: real^'n)"
    by (rule martingale_cbmX)
  have cr: "cbmX (0 :: real^'n) r \<in> borel_measurable (?F r)"
    by (rule MC.adapted[OF r])
  have cu: "cbmX (0 :: real^'n) r \<in> borel_measurable (?F u)"
    using MC.borel_measurable_mono[OF r ru] cr by blast
  have c: "(\<lambda>v :: real^'n. (v, r *\<^sub>R (mat 1 :: real^'n^'n)))
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
        (cbmX (0 :: real^'n) r \<omega>, r *\<^sub>R (mat 1 :: real^'n^'n)))
      \<in> borel_measurable (?F u)"
    by (rule measurable_compose[OF cu c])
  then show ?thesis using True by (simp add: bmpair_apply)
next
  case False
  then have "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. bmpair T \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: bmpair_def)
  then show ?thesis by simp
qed

theorem bmpair_law_X_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (bmpair T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?G u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev fstB])
  qed
  have mg: "martingale ?M ?F 0 (\<lambda>u \<omega>. fst (bmpair T \<omega> (min u T)))"
  proof (rule martingale_cong_ge
      [OF martingale_stopped_const[OF T martingale_cbmX]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. cbmX (0 :: real^'n) (min u T) \<omega>)
        = (\<lambda>\<omega>. fst (bmpair T \<omega> (min u T)))"
      by (rule ext) (simp add: bmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        bmpair_measurable[OF T] bmpair_adapted Zm mg])
qed

theorem bmpair_law_comp_martingale:
  assumes T: "0 \<le> T"
  shows "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure"
  let ?Q = "pair_law_of T (bmpair T) ?M"
  let ?F = "natural_filtration ?M 0 (cbmX (0 :: real^'n))"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  \<comment> \<open>as in \<open>comp_entry_cont\<close>: rewrite to the ENTRYWISE form first, then
      \<open>continuous_on_vec_lambda\<close> twice.\<close>
  have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
      = (\<lambda>p. \<chi> i j. fst p $ i * fst p $ j - snd p $ i $ j)"
    by (rule ext) (simp add: outerp_def vec_eq_iff)
  have cB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
      \<in> borel_measurable borel"
    unfolding e
    by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
        continuous_intros)
  have Zm: "(\<lambda>\<omega> :: 'n pairpath.
        outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
      \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u T in auto)
    show ?thesis by (rule measurable_compose[OF ev cB])
  qed
  have mg: "martingale ?M ?F 0
      (\<lambda>u \<omega>. outerp (fst (bmpair T \<omega> (min u T))) - snd (bmpair T \<omega> (min u T)))"
  proof (rule martingale_cong_ge
      [OF martingale_stopped_const[OF T martingale_cbm_outerp]])
    fix u :: real assume u: "0 \<le> u"
    have mI: "min u T \<in> {0..T}" using u T by simp
    show "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real.
          outerp (cbmX (0 :: real^'n) (min u T) \<omega>) - (min u T) *\<^sub>R mat 1)
        = (\<lambda>\<omega>. outerp (fst (bmpair T \<omega> (min u T)))
             - snd (bmpair T \<omega> (min u T)))"
      by (rule ext) (simp add: bmpair_apply[OF mI])
  qed
  show ?thesis
    by (rule martingale_pair_law[OF prob_space_bm_paths
        bmpair_measurable[OF T] bmpair_adapted Zm mg])
qed

subsection \<open>The witness is a member, so the class is nonempty\<close>

theorem bmpair_law_in_paper_pair_class:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "pair_law_of T (bmpair T)
      (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
    \<in> exit_class k L T (0 :: real^'n)"
  unfolding exit_class_def
proof (intro CollectI conjI)
  show "prob_space (pair_law_of T (bmpair T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))"
    by (rule prob_space_bmpair_law[OF T])
  show "sets (pair_law_of T (bmpair T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      = sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    by simp
  show "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        fst (\<omega> 0) = (0 :: real^'n) \<and> snd (\<omega> 0) = 0"
    by (rule bmpair_law_start[OF T])
  show "AE \<omega> in pair_law_of T (bmpair T)
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule bmpair_law_diffquot[OF T L])
  show "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)) :: real^'n)"
    by (rule bmpair_law_X_martingale[OF T])
  show "martingale (pair_law_of T (bmpair T)
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure))
      (natural_filtration (pair_law_of T (bmpair T) bm_paths) 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T)) :: real^'n) - snd (\<omega> (min t T)))"
    by (rule bmpair_law_comp_martingale[OF T])
qed

corollary exit_class_nonempty:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "exit_class k L T (0 :: real^'n::finite) \<noteq> {}"
  using bmpair_law_in_paper_pair_class[OF T L] by blast

text \<open>Hence clause (1) of Theorem 1.1 for the paper's value function, under
  no hypothesis beyond the paper's own standing ones: \<open>0 < T\<close>, \<open>1 \<le> L\<close>
  (Eq. (1.5)), and \<open>K\<close> closed.\<close>

corollary exit_val_usc_unconditional:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and b :: ennreal
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
    and lt: "exit_val k L T K x < b"
  shows "eventually (\<lambda>y. exit_val k L T K y < b) (nhds x)"
proof (rule exit_val_usc[OF T _ K _ lt])
  show "0 \<le> L" using L by simp
  show "exit_class k L T (0 :: real^'n) \<noteq> {}"
    using T L by (intro exit_class_nonempty) simp_all
qed

section \<open>Consolidating the clauses onto the paper's value function\<close>

text \<open>Clause (0) for \<open>exit_val\<close>: the exit functional of Eq. (1.6) is capped
  at the horizon, so the value is bounded by it outright.  The sharp bound
  \<open>exit_val \<le> ball_v\<close>, giving also clause (3), needs the class-level
  expected-exit-time estimate below.\<close>

theorem exit_val_le_T:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T: "0 \<le> T"
  shows "exit_val k L T K x \<le> ennreal T"
  unfolding exit_val_def
proof (rule Sup_least)
  fix c :: ennreal
  assume "c \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      ` exit_class k L T x"
  then obtain Q :: "('n pairpath) measure"
    where Q: "Q \<in> exit_class k L T x"
      and c: "c = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
  show "c \<le> ennreal T"
    unfolding c
    by (rule ess_inf_time_le_const[OF exit_class_prob[OF Q]])
      (simp add: pexit_def etime_le_T[OF T])
qed

text \<open>The trace lower bound carried by the constraint set: the identity is a
  rank-\<open>n\<close> projection, so \<open>Pi_proj a n \<le> trace a\<close>, and the constraint's own
  bound at \<open>m = n\<close> is \<open>n - k\<close>.  This makes \<open>|X|\<^sup>2\<close> a submartingale with rate
  at least \<open>n - k\<close>, giving Lemma 2.1's exit-time estimate at the class
  level.\<close>

lemma sconstraint_trace_ge:
  fixes a :: "real^'n::finite^'n"
  assumes k: "k < CARD('n)" and a: "a \<in> sconstraint k L"
  shows "real (CARD('n) - k) \<le> trace a"
proof -
  have p: "psd a"
    and pi: "\<And>m. k < m \<Longrightarrow> m \<le> CARD('n) \<Longrightarrow> real (m - k) \<le> Pi_proj a m"
    using a unfolding sconstraint_def Pi_constraint_def by auto
  have "real (CARD('n) - k) \<le> Pi_proj a CARD('n)" using k by (intro pi) auto
  also have "\<dots> \<le> trace (a ** mat 1)"
    by (rule Pi_proj_le[OF p]) (simp_all add: is_proj_def trace_I)
  also have "\<dots> = trace a" by simp
  finally show ?thesis .
qed

text \<open>\<open>bounded_linear_trace\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma trace_outerp:
  fixes v :: "real^'n::finite"
  shows "trace (outerp v) = v \<bullet> v"
  by (simp add: outerp_def trace_def inner_vec_def)

theorem exit_class_trace_rate:
  fixes Q :: "('n::finite pairpath) measure"
  assumes k: "k < CARD('n)" and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      real (CARD('n) - k) * (t - s)
        \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  show ?thesis
  proof (rule eventually_mono[OF dq])
    fix \<omega> :: "'n pairpath"
    assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    show "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        real (CARD('n) - k) * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
    proof (intro allI impI)
      fix s t :: real
      assume s: "0 \<le> s" and st: "s < t" and tT: "t \<le> T"
      have mem: "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
        using q s st tT by blast
      have "real (CARD('n) - k)
          \<le> trace ((1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)))"
        by (rule sconstraint_trace_ge[OF k mem])
      also have "\<dots> = (trace (snd (\<omega> t)) - trace (snd (\<omega> s))) / (t - s)"
        by (simp add: trace_scaleR trace_diff_matrix)
      finally show "real (CARD('n) - k) * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
        using st by (simp add: pos_le_divide_eq)
    qed
  qed
qed

lemma exit_class_norm_sq_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
proof -
  have "integrable Q (\<lambda>\<omega> :: 'n pairpath. \<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2)"
    by (intro Bochner_Integration.integrable_sum
        exit_class_sq_integrable[OF T L Q t])
  then show ?thesis by (simp add: inner_vec_def power2_eq_square)
qed

text \<open>The class-level form of Lemma 2.1's estimate: the expected squared
  norm grows at rate at least \<open>n - k\<close>, using the compensated clause only at
  the fixed time \<open>t\<close> --- no stopping, no optional sampling.\<close>

theorem exit_class_sq_norm_mean_ge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes k: "k < CARD('n)" and T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and t: "t \<in> {0..T}"
  shows "x \<bullet> x + real (CARD('n) - k) * t
      \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by auto
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule exit_class_compensated_integrable[OF Q t])
  have ti: "integrable Q (\<lambda>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace ci])
  have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule exit_class_norm_sq_integrable[OF T L Q t])
  have mean: "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q) = x \<bullet> x"
  proof -
    have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
        = trace (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q)"
      by (rule integral_of_bounded_linear[OF bounded_linear_trace ci])
    also have "\<dots> = trace (outerp x)"
      by (simp add: exit_class_compensated_mean[OF Q t])
    finally show ?thesis by (simp add: trace_outerp)
  qed
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have tr: "AE \<omega> in Q. \<forall>s t'. 0 \<le> s \<longrightarrow> s < t' \<longrightarrow> t' \<le> T \<longrightarrow>
      real (CARD('n) - k) * (t' - s)
        \<le> trace (snd (\<omega> t')) - trace (snd (\<omega> s))"
    by (rule exit_class_trace_rate[OF k Q])
  have rate: "AE \<omega> in Q. real (CARD('n) - k) * t \<le> trace (snd (\<omega> t))"
    using st tr
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (cases "t = 0")
      case True
      then show ?thesis using elim by (simp add: trace_def)
    next
      case False
      with t0 have pos: "0 < t" by simp
      have "real (CARD('n) - k) * (t - 0)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> 0))"
        using elim pos tT by blast
      then show ?thesis using elim by (simp add: trace_def)
    qed
  qed
  have ptw: "AE \<omega> in Q. trace (outerp (fst (\<omega> t)) - snd (\<omega> t))
      + real (CARD('n) - k) * t \<le> fst (\<omega> t) \<bullet> fst (\<omega> t)"
    using rate by eventually_elim (simp add: trace_diff_matrix trace_outerp)
  have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      + real (CARD('n) - k) * t
      = (\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t))
            + real (CARD('n) - k) * t \<partial>Q)"
    using ti by (simp add: P.prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    by (rule integral_mono_AE) (use ti ni ptw in auto)
  finally show ?thesis unfolding mean .
qed

text \<open>Clause (3) on the ball: a member starting on the boundary that kept
  \<open>|X| \<le> r\<close> up to a positive time would have expected squared norm at most
  \<open>r\<^sup>2\<close> at an interior time, but \<open>exit_class_sq_norm_mean_ge\<close> forces
  it to be at least \<open>r\<^sup>2 + (n-k)t > r\<^sup>2\<close>.  So the exit time's essential
  infimum, and hence its supremum, is \<open>0\<close>.\<close>

theorem exit_val_boundary_zero:
  fixes r :: real and x :: "real^'n::finite"
  assumes k: "k < CARD('n)" and T: "0 < T" and L: "0 \<le> L"
    and x: "norm x = r"
  shows "exit_val k L T (cball 0 r) x = 0"
proof -
  have T0: "0 \<le> T" using T by simp
  have r0: "0 \<le> r" using x by (metis norm_ge_zero)
  have "exit_val k L T (cball 0 r) x \<le> 0"
    unfolding exit_val_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T (cball 0 r) (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and e: "e = ess_inf_time Q
            (\<lambda>\<omega>. pexit T (cball 0 r) (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule exit_class_prob[OF Q])
    show "e \<le> 0"
    proof (rule ccontr)
      assume "\<not> e \<le> 0"
      then have epos: "0 < e" by (simp add: zero_less_iff_neq_zero)
      have ele: "e \<le> ennreal T"
        unfolding e
        by (rule ess_inf_time_le_const[OF P.prob_space_axioms])
          (simp add: pexit_def etime_le_T[OF T0])
      have efin: "e < \<top>"
        using ele ennreal_less_top by (rule order_le_less_trans)
      define c where "c = enn2real e"
      have ec: "e = ennreal c" unfolding c_def using efin by simp
      have c0: "0 < c"
      proof (rule ccontr)
        assume "\<not> 0 < c"
        then have "ennreal c = 0" by (simp add: ennreal_neg)
        with ec epos show False by simp
      qed
      define t where "t = min (c/2) (T/2)"
      have t0: "0 < t" unfolding t_def using c0 T by simp
      have tc: "t < c" unfolding t_def using c0 by simp
      have tT: "t \<le> T" unfolding t_def using T by simp
      have tI: "t \<in> {0..T}" using t0 tT by simp
      have ae1: "AE \<omega> in Q. e \<le> ennreal (pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)))"
        unfolding e by (rule ess_inf_time_AE)
      have ae2: "AE \<omega> in Q. fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
      proof (rule eventually_mono[OF ae1])
        fix \<omega> :: "'n pairpath"
        assume "e \<le> ennreal (pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)))"
        then have "ennreal c \<le> ennreal (pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)))"
          using ec by simp
        moreover have nn: "0 \<le> pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s))"
          unfolding pexit_def by (rule etime_nonneg[OF T0])
        ultimately have ct: "c \<le> pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s))"
          by simp
        have inK: "fst (\<omega> t) \<in> cball 0 r"
        proof (rule ccontr)
          assume notin: "fst (\<omega> t) \<notin> cball 0 r"
          \<comment> \<open>let the CONCLUSION fix \<open>X\<close>, \<open>A\<close> and \<open>\<omega>\<close>; a pre-instantiated
              membership premise beta-reduces and no longer matches.\<close>
          have "pexit T (cball 0 r) (\<lambda>s. fst (\<omega> s)) \<le> t"
            unfolding pexit_def
            by (rule etime_le_of_mem[OF T0 less_imp_le[OF t0] tT])
              (use notin in simp)
          with ct tc show False by simp
        qed
        have "norm (fst (\<omega> t)) \<le> r" using inK by (simp add: dist_norm)
        then have "(norm (fst (\<omega> t)))\<^sup>2 \<le> r\<^sup>2"
          by (rule power_mono) simp
        then show "fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
          by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
      qed
      have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
        by (rule exit_class_norm_sq_integrable[OF T0 L Q tI])
      have lo: "x \<bullet> x + real (CARD('n) - k) * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule exit_class_sq_norm_mean_ge[OF k T0 L Q tI])
      have hi: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> r * r"
      proof -
        have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> (\<integral>\<omega>. r * r \<partial>Q)"
          by (rule integral_mono_AE) (use ni ae2 in auto)
        also have "\<dots> = r * r" by (simp add: P.prob_space)
        finally show ?thesis .
      qed
      have xx: "x \<bullet> x = r * r"
        using x by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
      \<comment> \<open>simp normalises \<open>real (CARD('n) - k)\<close> to \<open>real CARD('n) - real k\<close>
          inside \<open>lo\<close>, so state the factor in the SAME form or the atoms
          do not agree.\<close>
      have pos: "0 < (real CARD('n) - real k) * t"
      proof (rule mult_pos_pos)
        show "0 < real CARD('n) - real k" using k by simp
        show "0 < t" by (rule t0)
      qed
      have cast: "real (CARD('n) - k) = real CARD('n) - real k"
        using k by simp
      from lo hi pos show False unfolding xx cast by simp
    qed
  qed
  then show ?thesis by simp
qed

text \<open>Example 3.1, inequality (3.10): if the target set fits inside a ball
  of radius \<open>r\<close>, then \<open>v(x) \<le> (r\<^sup>2 - |x|\<^sup>2) / (n - k)\<close>, independent of the
  horizon \<open>T\<close> --- the quantitative form of clause (0), and why the horizon
  cap is eventually invisible.  \<open>exit_val_boundary_zero\<close> is the case
  \<open>|x| = r\<close>.  The paper derives (3.10) from It\<open>\<^bold>o\<close>'s formula; here it
  follows from \<open>exit_class_sq_norm_mean_ge\<close>, Lemma 2.1's estimate at
  a fixed time, with no stochastic calculus.\<close>

theorem exit_val_le_ball_bound:
  fixes r :: real and x :: "real^'n::finite" and K :: "(real^'n) set"
  assumes k: "k < CARD('n)" and T: "0 \<le> T" and L: "0 \<le> L"
    and KB: "K \<subseteq> cball 0 r"
  shows "exit_val k L T K x
      \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
proof -
  define B where "B = (r * r - x \<bullet> x) / real (CARD('n) - k)"
  have nk: "0 < real (CARD('n) - k)" using k by simp
  have main: "exit_val k L T K x \<le> ennreal B"
    unfolding exit_val_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` exit_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule exit_class_prob[OF Q])
    show "e \<le> ennreal B"
    proof (rule ccontr)
      assume "\<not> e \<le> ennreal B"
      then have gt: "ennreal B < e" by simp
      have ele: "e \<le> ennreal T"
        unfolding e
        by (rule ess_inf_time_le_const[OF P.prob_space_axioms])
          (simp add: pexit_def etime_le_T[OF T])
      have efin: "e < \<top>"
        using ele ennreal_less_top by (rule order_le_less_trans)
      define c where "c = enn2real e"
      have ec: "e = ennreal c" unfolding c_def using efin by simp
      have c0: "0 \<le> c" unfolding c_def by simp
      have cT: "c \<le> T" using ele T unfolding ec by simp
      define m where "m = max B 0"
      have m0: "0 \<le> m" and mB: "B \<le> m" unfolding m_def by auto
      have mc: "m < c"
      proof (cases "0 \<le> B")
        case True
        then have "B < c" using gt unfolding ec by (simp add: ennreal_less_iff)
        then show ?thesis using True unfolding m_def by simp
      next
        case False
        then have z: "ennreal B = 0" by (simp add: ennreal_neg)
        have "0 < c"
        proof (rule ccontr)
          assume "\<not> 0 < c"
          then have "ennreal c = 0" by (simp add: ennreal_neg)
          with gt z show False unfolding ec by simp
        qed
        then show ?thesis using False unfolding m_def by simp
      qed
      define t where "t = (m + c) / 2"
      have t0: "0 < t" unfolding t_def using m0 mc by simp
      have tc: "t < c" unfolding t_def using mc by simp
      have Bt: "B < t" unfolding t_def using mB mc by simp
      have tT: "t \<le> T" using tc cT by simp
      have tI: "t \<in> {0..T}" using t0 tT by simp
      have ae1: "AE \<omega> in Q. e \<le> ennreal (pexit T K (\<lambda>s. fst (\<omega> s)))"
        unfolding e by (rule ess_inf_time_AE)
      have ae2: "AE \<omega> in Q. fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
      proof (rule eventually_mono[OF ae1])
        fix \<omega> :: "'n pairpath"
        assume "e \<le> ennreal (pexit T K (\<lambda>s. fst (\<omega> s)))"
        then have "ennreal c \<le> ennreal (pexit T K (\<lambda>s. fst (\<omega> s)))"
          using ec by simp
        moreover have nn: "0 \<le> pexit T K (\<lambda>s. fst (\<omega> s))"
          unfolding pexit_def by (rule etime_nonneg[OF T])
        ultimately have ct: "c \<le> pexit T K (\<lambda>s. fst (\<omega> s))" by simp
        have inK: "fst (\<omega> t) \<in> K"
        proof (rule ccontr)
          assume notin: "fst (\<omega> t) \<notin> K"
          have "pexit T K (\<lambda>s. fst (\<omega> s)) \<le> t"
            unfolding pexit_def
            by (rule etime_le_of_mem[OF T less_imp_le[OF t0] tT])
              (use notin in simp)
          with ct tc show False by simp
        qed
        have "norm (fst (\<omega> t)) \<le> r" using inK KB by (auto simp: dist_norm)
        then have "(norm (fst (\<omega> t)))\<^sup>2 \<le> r\<^sup>2"
          by (rule power_mono) simp
        then show "fst (\<omega> t) \<bullet> fst (\<omega> t) \<le> r * r"
          by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
      qed
      have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
        by (rule exit_class_norm_sq_integrable[OF T L Q tI])
      have lo: "x \<bullet> x + real (CARD('n) - k) * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule exit_class_sq_norm_mean_ge[OF k T L Q tI])
      have hi: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> r * r"
      proof -
        have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q) \<le> (\<integral>\<omega>. r * r \<partial>Q)"
          by (rule integral_mono_AE) (use ni ae2 in auto)
        also have "\<dots> = r * r" by (simp add: P.prob_space)
        finally show ?thesis .
      qed
      from lo hi have "real (CARD('n) - k) * t \<le> r * r - x \<bullet> x" by simp
      then have "t \<le> B" unfolding B_def
        using nk by (simp add: pos_le_divide_eq mult.commute)
      with Bt show False by simp
    qed
  qed
  from main show ?thesis unfolding B_def .
qed


(*<*)
end
(*>*)
