section \<open>Clause (iv) at a stopping time\<close>

(*<*)
theory Dynamic_Programming_Stopping_Clauses
  imports Dynamic_Programming_Optional_Sampling
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Time_Martingales.Time_Discretisation"
begin

(*>*)

section \<open>The class's component martingale has a dominating function\<close>

text \<open>@{theory Continuous_Time_Martingales.Doob_Inequality}'s \<open>horizon_sq_int_martingale\<close> locale already builds
  the running supremum \<open>Dsup\<close>, proves it integrable, and proves it dominates
  the path (\<open>Dsup_dominates\<close>).  So the last hypothesis of
  @{thm [source] set_martingale_sampling} costs nothing more than an
  interpretation: the class supplies the martingale
  (@{thm [source] martingale_vec_component} for the component) and the
  square-integrability (@{thm [source] exit_class_sq_integrable}).\<close>

lemma exit_class_horizon_component:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
  shows "horizon_sq_int_martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v))
      (\<lambda>t \<omega>. fst (\<omega> (min t T)) $ c) T"
proof -
  have mgv: "martingale P (natural_filtration P 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    using P unfolding exit_class_def by blast
  have mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)) $ c)"
    by (rule martingale_vec_component[OF mgv])
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)" 0
    "\<lambda>t \<omega>. fst (\<omega> (min t T)) $ c" by (rule mg)
  interpret PS: prob_space P by (rule exit_class_prob[OF P])
  show ?thesis
  proof unfold_locales
    show "0 < T" by (rule T0)    fix s :: real assume s: "0 \<le> s"
    have m: "min s T \<in> {0..T}" using s T0 by simp
    show "integrable P (\<lambda>\<omega>. (fst (\<omega> (min s T)) $ c)\<^sup>2)"
      by (rule exit_class_sq_integrable
          [OF less_imp_le[OF T0] L0 P m])
  qed
qed

text \<open>The \<open>cont\<close> hypothesis of @{thm [source] set_martingale_sampling} for
  the class's component process: the dyadic times converge and the path is
  continuous, so the values do.\<close>

lemma exit_component_dyceil_tendsto:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>n. fst (\<omega> (min (dyceil n T s) T)) $ c)
      \<longlonglongrightarrow> fst (\<omega> (min s T)) $ c"
proof -
  have cont: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u) $ c)"
    using mspace_path_metricD[OF w] by (intro continuous_intros)
  have conv: "(\<lambda>n. dyceil n T s) \<longlonglongrightarrow> s" by (rule dyceil_tendsto[OF s0 sT])
  have mem: "dyceil n T s \<in> {0..T}" for n
    using dyceil_nonneg[OF s0 sT] dyceil_le_U[of n T s] by simp
  have "(\<lambda>n. fst (\<omega> (dyceil n T s)) $ c) \<longlonglongrightarrow> fst (\<omega> s) $ c"
  proof (rule continuous_on_tendsto_compose[OF cont conv])
    show "\<forall>\<^sub>F n in sequentially. dyceil n T s \<in> {0..T}" using mem by simp
    show "s \<in> {0..T}" using s0 sT by simp
  qed
  moreover have "min (dyceil n T s) T = dyceil n T s" for n
    using dyceil_le_U[of n T s] by simp
  moreover have "min s T = s" using sT by simp
  ultimately show ?thesis by simp
qed

text \<open>And the \<open>stops\<close> hypothesis at the shifted time.  Above the horizon the
  event is everything, since \<open>(\<theta>+i) \<and> T \<le> T\<close>; below it,
  @{thm [source] path_stopping_time_event_filtration} applies to the shifted
  stopping time.\<close>

lemma path_stopping_time_shift_event:
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric)))"
    and i: "0 \<le> i" and t: "0 \<le> t"
  shows "{\<omega> \<in> space (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))). min (\<theta> \<omega> + i) T \<le> t}
      \<in> sets (natural_filtration (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))) 0 (\<lambda>v \<omega>. \<omega> v) t)"
proof (cases "t \<le> T")
  case True
  have st': "path_stopping_time T (\<lambda>\<omega> :: 'n pairpath. min (\<theta> \<omega> + i) T)"
    by (rule path_stopping_time_shift[OF st i])
  have m': "(\<lambda>\<omega> :: 'n pairpath. min (\<theta> \<omega> + i) T) \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    using thM by measurable
  show ?thesis
    by (rule path_stopping_time_event_filtration[OF T0 st' m' t True])
next
  case False
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t"
  have "{\<omega> \<in> space ?B. min (\<theta> \<omega> + i) T \<le> t} = space ?B"
    using False by auto
  moreover have "space ?B \<in> sets ?F"
  proof -
    have "space ?F = space ?B" by simp
    then show ?thesis using sets.top[of ?F] by simp
  qed
  ultimately show ?thesis by simp
qed

section \<open>Clause (iv) at a stopping time: the increment identity\<close>

text \<open>The assembly.  Every hypothesis of
  @{thm [source] set_martingale_sampling_two} now has a supplier: the
  martingale from the class via @{thm [source] martingale_vec_component},
  the filtration facts from @{thm [source] sets_natural_filtration_mono} and
  the martingale locale, the stopping-time events from
  @{thm [source] path_stopping_time_shift_event}, the convergence from
  @{thm [source] exit_component_dyceil_tendsto}, and the domination from
  @{theory Continuous_Time_Martingales.Doob_Inequality}'s \<open>Dsup\<close> through
  @{thm [source] exit_class_horizon_component}.\<close>

text \<open>The same identity for an arbitrary real process that is a
  \<open>horizon_sq_int_martingale\<close> with continuous paths.  Both of the class's
  martingale clauses are of that shape --- the \<open>X\<close> one componentwise, the
  compensated one entrywise --- so this is the form clause (iv) uses twice.
  \<open>martingale_mat_component\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>Square-integrability of the compensated entry, from its
  nonnegative-integral bound.  This is the second half of what
  \<open>horizon_sq_int_martingale\<close> asks for.\<close>

lemma exit_class_comp_entry_sq_integrable:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and u: "u \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. ((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)"
proof (rule integrableI_bounded)
  have e: "integrable Q (\<lambda>\<omega>. (outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)"
    by (rule exit_class_compensated_entry_integrable[OF Q u])
  then have em: "(\<lambda>\<omega>. (outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)
      \<in> borel_measurable Q" by (rule borel_measurable_integrable)
  show "(\<lambda>\<omega>. ((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)
      \<in> borel_measurable Q" using em by measurable
next
  have "(\<integral>\<^sup>+\<omega>. ennreal (norm (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)) \<partial>Q)
      = (\<integral>\<^sup>+\<omega>. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2) \<partial>Q)"
    by simp
  also have "\<dots> \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
               + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
               + 2 * (real CARD('n) * L * T)\<^sup>2)"
    by (rule exit_class_comp_entry_sq_nn[OF T L Q u])
  also have "\<dots> < \<infinity>" by simp
  finally show "(\<integral>\<^sup>+\<omega>. ennreal (norm
      (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)) \<partial>Q) < \<infinity>" .
qed
text \<open>Hence the compensated clause is a \<open>horizon_sq_int_martingale\<close> too, and
  \<open>stopped_increment_of_horizon_gen\<close> applies to it verbatim.\<close>

lemma exit_class_horizon_compensated:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
  shows "horizon_sq_int_martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v))
      (\<lambda>t \<omega>. (outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T))) $ c $ d) T"
proof -
  have mgm: "martingale P (natural_filtration P 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule exit_class_compensated_martingale[OF P])
  have mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>t \<omega>. (outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T))) $ c $ d)"
    by (rule martingale_mat_component[OF mgm])
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)" 0
    "\<lambda>t \<omega>. (outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T))) $ c $ d"
    by (rule mg)
  interpret PS: prob_space P by (rule exit_class_prob[OF P])
  show ?thesis
  proof unfold_locales
    show "0 < T" by (rule T0)
    fix s :: real assume s: "0 \<le> s"
    have m: "min s T \<in> {0..T}" using s T0 by simp
    show "integrable P (\<lambda>\<omega>.
        ((outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d)\<^sup>2)"
      by (rule exit_class_comp_entry_sq_integrable[OF T0 L0 P m])
  qed
qed

section \<open>Clause (iv): the conditioning rectangle at a stopping time\<close>

text \<open>The deterministic case conditions on rectangles
  \<open>(pcut r, pfut r T) -` (A \<times> A')\<close>, which sit in \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> by
  @{thm [source] rect_vimage_natural_filtration}.  At a stopping time the
  split is \<open>(pstopped T \<theta>, pafter T \<theta>)\<close>; since \<^const>\<open>pafter\<close> is the delayed
  future, frozen until \<open>\<theta>\<close> and then running on the same clock, the time on
  the second factor is an absolute time \<open>u\<close>, not an offset, so the sampling
  time attached to it is \<open>u \<or> \<theta>\<close>, and this section is about that family.

  Everything rests on one pathwise observation: below a deterministic \<open>t\<close>
  both factors are read off the path stopped at \<open>t\<close>, an \<open>\<F>\<^sub>t\<close>-measurable
  function of \<open>\<omega>\<close>, the same device @{thm [source]
  path_stopping_time_event_filtration} uses for the event \<open>{\<theta> \<le> t}\<close> itself.\<close>

lemma path_stopping_time_cut_eq:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "path_stopping_time T \<theta>" and tT: "t \<le> T" and le: "\<theta> \<omega> \<le> t"
    and cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
  shows "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
proof (rule path_stopping_time_cong[OF st cw
      pstopped_fst_continuous[OF cw, of "\<lambda>_. t"]])
  show "0 \<le> t" using le path_stopping_time_nonneg[OF st, of \<omega>] by simp
  show "t \<le> T" by (rule tT)
  fix s assume s: "s \<in> {0..\<theta> \<omega>}"
  then have sT: "s \<in> {0..T}" using le tT by auto
  have "min s t = s" using s le by simp
  then show "\<omega> s = pstopped T (\<lambda>_. t) \<omega> s"
    by (simp add: pstopped_apply[OF sT])
qed

lemma pstopped_cut_compose:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "path_stopping_time T \<theta>" and tT: "t \<le> T" and le: "\<theta> \<omega> \<le> t"
    and cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
  shows "pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>) = pstopped T \<theta> \<omega>"
proof (rule ext)
  fix s :: real
  show "pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s = pstopped T \<theta> \<omega> s"
  proof (cases "s \<in> {0..T}")
    case True
    have th: "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
      by (rule path_stopping_time_cut_eq[OF st tT le cw])
    have th0: "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
    have m: "min s (\<theta> \<omega>) \<in> {0..T}" using True th0 by auto
    have "pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s
        = pstopped T (\<lambda>_. t) \<omega> (min s (\<theta> \<omega>))"
      unfolding pstopped_apply[OF True] th ..
    also have "\<dots> = \<omega> (min (min s (\<theta> \<omega>)) t)" by (rule pstopped_apply[OF m])
    also have "min (min s (\<theta> \<omega>)) t = min s (\<theta> \<omega>)" using le by simp
    finally show ?thesis by (simp add: pstopped_apply[OF True])
  next
    case False
    then show ?thesis by (simp add: pstopped_outside)
  qed
qed

text \<open>The second factor only agrees up to \<open>u\<close> --- exactly as far as an
  \<open>\<F>\<^sub>u\<close>-set can look, so composing with \<^const>\<open>pcut\<close> loses nothing.\<close>

lemma pcut_pafter_cut_compose:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "path_stopping_time T \<theta>" and tT: "t \<le> T"
    and u: "0 \<le> u" and ut: "u \<le> t" and le: "\<theta> \<omega> \<le> t"
    and cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
  shows "pcut u (pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>)) = pcut u (pafter T \<theta> \<omega>)"
proof (rule ext)
  fix s :: real
  show "pcut u (pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>)) s
      = pcut u (pafter T \<theta> \<omega>) s"
  proof (cases "s \<in> {0..u}")
    case True
    have th0: "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
    have sT: "s \<in> {0..T}" using True u ut tT by auto
    have th: "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
      by (rule path_stopping_time_cut_eq[OF st tT le cw])
    have m1: "max s (\<theta> \<omega>) \<in> {0..T}"
      using sT th0 path_stopping_time_le[OF st, of \<omega>] by auto
    have m2: "\<theta> \<omega> \<in> {0..T}"
      using th0 path_stopping_time_le[OF st, of \<omega>] by simp
    have mx: "max s (\<theta> \<omega>) \<le> t" using True ut le by simp
    have "pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s
        = pstopped T (\<lambda>_. t) \<omega> (max s (\<theta> \<omega>))
          - pstopped T (\<lambda>_. t) \<omega> (\<theta> \<omega>)"
      unfolding pafter_apply[OF sT] th ..
    also have "\<dots> = \<omega> (min (max s (\<theta> \<omega>)) t) - \<omega> (min (\<theta> \<omega>) t)"
      by (simp only: pstopped_apply[OF m1] pstopped_apply[OF m2])
    also have "\<dots> = \<omega> (max s (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)" using mx le by simp
    finally have "pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s = pafter T \<theta> \<omega> s"
      unfolding pafter_apply[OF sT] .
    then show ?thesis by (simp add: pcut_apply[OF True])
  next
    case False
    have out: "pcut u w s = undefined" for w :: "'n pairpath"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    show ?thesis unfolding out ..
  qed
qed

text \<open>\<open>u \<or> \<theta>\<close> is a stopping time for the same reason \<open>(\<theta>+i) \<and> T\<close> is
  (@{thm [source] path_stopping_time_shift}): it never looks back less far
  than \<open>\<theta>\<close> does.\<close>

lemma path_stopping_time_max:
  fixes \<theta> :: "'n::finite pairpath \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and u: "0 \<le> u" and uT: "u \<le> T"
  shows "path_stopping_time T (\<lambda>\<omega>. max u (\<theta> \<omega>))"
proof -
  have c1: "0 \<le> max u (\<theta> \<omega>) \<and> max u (\<theta> \<omega>) \<le> T" for \<omega> :: "'n pairpath"
    using u uT path_stopping_time_nonneg[OF st, of \<omega>]
      path_stopping_time_le[OF st, of \<omega>] by simp
  have c2: "max u (\<theta> \<omega>') = max u (\<theta> \<omega>)"
    if cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
      and cw': "continuous_on {0..T} (\<lambda>v. fst (\<omega>' v))"
      and ag: "\<forall>s \<in> {0..max u (\<theta> \<omega>)}. \<omega> s = \<omega>' s" for \<omega> \<omega>' :: "'n pairpath"
  proof -
    have "\<theta> \<omega>' = \<theta> \<omega>"
    proof (rule path_stopping_time_cong[OF st cw cw'])
      fix s assume "s \<in> {0..\<theta> \<omega>}"
      then have "s \<in> {0..max u (\<theta> \<omega>)}" by auto
      then show "\<omega> s = \<omega>' s" using ag by blast
    qed
    then show ?thesis by simp
  qed
  show ?thesis unfolding path_stopping_time_def using c1 c2 by blast
qed

text \<open>The event lemma with the horizon restriction removed: past \<open>T\<close> there is
  nothing left to decide.\<close>

lemma path_stopping_time_event_filtration_all:
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric)))"
    and t: "0 \<le> t"
  shows "{\<omega> \<in> space (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))). \<sigma> \<omega> \<le> t}
      \<in> sets (natural_filtration (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))) 0 (\<lambda>v \<omega>. \<omega> v) t)"
proof (cases "t \<le> T")
  case True
  show ?thesis by (rule path_stopping_time_event_filtration[OF T0 st sM t True])
next
  case False
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t"
  have lt: "\<sigma> \<omega> \<le> t" for \<omega> :: "'n pairpath"
    using path_stopping_time_le[OF st, of \<omega>] False by simp
  have "{\<omega> \<in> space ?B. \<sigma> \<omega> \<le> t} = space ?B" using lt by blast
  moreover have "space ?B \<in> sets ?F"
  proof -
    have "space ?F = space ?B" by simp
    then show ?thesis using sets.top[of ?F] by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open>A packaging lemma: for a stopping time bounded by \<open>T\<close> it is enough to
  check the \<open>\<F>\<^sub>\<sigma>\<close> condition at times below the horizon.\<close>

lemma pre_sigma_ofI_le:
  assumes T0: "0 \<le> T"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and bd: "\<And>\<omega>. \<sigma> \<omega> \<le> T"
    and S: "S \<in> sets M"
    and key: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T
      \<Longrightarrow> S \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  shows "S \<in> pre_sigma_of M F \<sigma>"
proof (rule pre_sigma_ofI[OF S])
  fix t :: real assume t: "0 \<le> t"
  show "S \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  proof (cases "t \<le> T")
    case True
    show ?thesis by (rule key[OF t True])
  next
    case False
    have lt: "\<sigma> \<omega> \<le> t" for \<omega> using bd[of \<omega>] False by simp
    have "{\<omega> \<in> space M. \<sigma> \<omega> \<le> t} = {\<omega> \<in> space M. \<sigma> \<omega> \<le> T}"
      using lt bd by blast
    then have "S \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F T)"
      using key[OF T0 order_refl] by simp
    moreover have "sets (F T) \<subseteq> sets (F t)" using mono[OF T0] False by simp
    ultimately show ?thesis by blast
  qed
qed

lemma pre_sigma_of_Int:
  assumes A: "A \<in> pre_sigma_of M F \<sigma>" and B: "B \<in> pre_sigma_of M F \<sigma>"
  shows "A \<inter> B \<in> pre_sigma_of M F \<sigma>"
proof (rule pre_sigma_ofI)
  show "A \<inter> B \<in> sets M"
    using pre_sigma_of_sets[OF A] pre_sigma_of_sets[OF B] by (rule sets.Int)
  fix t :: real assume t: "0 \<le> t"
  have "(A \<inter> B) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}
      = (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) \<inter> (B \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t})" by auto
  moreover have "\<dots> \<in> sets (F t)"
    using pre_sigma_of_cut[OF A t] pre_sigma_of_cut[OF B t] by (rule sets.Int)
  ultimately show "(A \<inter> B) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)" by simp
qed

text \<open>The first factor.  Below \<open>t\<close> the stopped path is read off the path
  stopped at \<open>t\<close> --- \<open>pstopped_cut_compose\<close> --- and that composite is
  \<open>\<F>\<^sub>t\<close>-measurable by \<open>pstopped_const_measurable_filtration\<close>.\<close>

lemma pstopped_vimage_pre_sigma:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and A: "A \<in> sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pstopped T \<theta> -` A \<inter> space P
      \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<theta>"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have mst: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have S: "pstopped T \<theta> -` A \<inter> space P \<in> sets P"
    by (rule measurable_sets[OF mst A])
  show ?thesis
  proof (rule pre_sigma_ofI_le[OF T0 mono thT S])
    fix t :: real assume t: "0 \<le> t" and tT: "t \<le> T"
    let ?g = "\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>)"
    have mg: "?g \<in> ?F t \<rightarrow>\<^sub>M ?B"
      unfolding FB
      by (rule measurable_compose
          [OF pstopped_const_measurable_filtration[OF T0 t tT]
             pstopped_measurable[OF T0 thM th0 thT]])
    have gm: "?g -` A \<inter> space P \<in> sets (?F t)"
      using measurable_sets[OF mg A] by simp
    have ev: "{\<omega> \<in> space P. \<theta> \<omega> \<le> t} \<in> sets (?F t)"
      unfolding FB spP
      by (rule path_stopping_time_event_filtration[OF T0 st thM t tT])
    have eqset: "(pstopped T \<theta> -` A \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}
        = (?g -` A \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}"
    proof -
      have "pstopped T \<theta> \<omega> = ?g \<omega>"
        if "\<theta> \<omega> \<le> t" and "\<omega> \<in> space P" for \<omega> :: "'n pairpath"
      proof -
        have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
          by (rule path_sets_fst_continuous[OF setsP that(2)])
        show ?thesis using pstopped_cut_compose[OF st tT that(1) cw] by simp
      qed
      then show ?thesis by auto
    qed
    show "(pstopped T \<theta> -` A \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}
        \<in> sets (?F t)"
      unfolding eqset using gm ev by (rule sets.Int)
  qed
qed

text \<open>The second factor.  An \<open>\<F>\<^sub>u\<close>-set of the path space is a
  \<open>pcut u\<close>-preimage --- @{thm [source] sets_natural_filtration_eq_pcut_vimage}
  --- so only the delayed future on \<open>[0,u]\<close> matters, and that is decided by
  the path stopped at \<open>t\<close> as soon as \<open>u \<or> \<theta> \<le> t\<close>.\<close>

lemma pafter_vimage_pre_sigma:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and u: "0 \<le> u" and uT: "u \<le> T"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) u)"
  shows "pafter T \<theta> -` A' \<inter> space P
      \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v))
          (\<lambda>\<omega>. max u (\<theta> \<omega>))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bu = "borel_of (mtopology_of (path_metric u :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have maxT: "max u (\<theta> \<omega>) \<le> T" for \<omega> :: "'n pairpath" using uT thT by simp
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have mafter: "pafter T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pafter_measurable[OF T0 thM th0 thT])
  obtain B where B: "B \<in> sets ?Bu" and A'eq: "A' = pcut u -` B \<inter> space ?B"
    using A' unfolding sets_natural_filtration_eq_pcut_vimage[OF refl u uT]
    by blast
  have h: "(\<lambda>\<omega> :: 'n pairpath. pcut u (pafter T \<theta> \<omega>)) \<in> P \<rightarrow>\<^sub>M ?Bu"
    by (rule measurable_compose[OF mafter pcut_measurable[OF u uT refl]])
  have vim: "pafter T \<theta> -` A' \<inter> space P
      = (\<lambda>\<omega> :: 'n pairpath. pcut u (pafter T \<theta> \<omega>)) -` B \<inter> space P"
    unfolding A'eq using measurable_space[OF mafter] by auto
  have S: "pafter T \<theta> -` A' \<inter> space P \<in> sets P"
    unfolding vim by (rule measurable_sets[OF h B])
  show ?thesis
  proof (rule pre_sigma_ofI_le[OF T0 mono maxT S])
    fix t :: real assume t: "0 \<le> t" and tT: "t \<le> T"
    show "(pafter T \<theta> -` A' \<inter> space P) \<inter> {\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t}
        \<in> sets (?F t)"
    proof (cases "u \<le> t")
      case False
      have e: "(pafter T \<theta> -` A' \<inter> space P)
          \<inter> {\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t} = {}"
        using False by auto
      show ?thesis unfolding e by simp
    next
      case True
      let ?g = "\<lambda>\<omega> :: 'n pairpath. pcut u (pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>))"
      have mg: "?g \<in> ?F t \<rightarrow>\<^sub>M ?Bu"
        unfolding FB
        by (rule measurable_compose
            [OF pstopped_const_measurable_filtration[OF T0 t tT]
               measurable_compose[OF pafter_measurable[OF T0 thM th0 thT]
                 pcut_measurable[OF u uT refl]]])
      have gm: "?g -` B \<inter> space P \<in> sets (?F t)"
        using measurable_sets[OF mg B] by simp
      have ev: "{\<omega> \<in> space P. \<theta> \<omega> \<le> t} \<in> sets (?F t)"
        unfolding FB spP
        by (rule path_stopping_time_event_filtration[OF T0 st thM t tT])
      have eqset: "(pafter T \<theta> -` A' \<inter> space P)
            \<inter> {\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t}
          = (?g -` B \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}"
      proof -
        have pt: "pcut u (pafter T \<theta> \<omega>) = ?g \<omega>"
          if mx: "max u (\<theta> \<omega>) \<le> t" and wsp: "\<omega> \<in> space P"
          for \<omega> :: "'n pairpath"
        proof -
          have le': "\<theta> \<omega> \<le> t" using mx by simp
          have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
            by (rule path_sets_fst_continuous[OF setsP wsp])
          show ?thesis
            using pcut_pafter_cut_compose[OF st tT u True le' cw] by simp
        qed
        show ?thesis unfolding vim using pt True by auto
      qed
      show ?thesis unfolding eqset using gm ev by (rule sets.Int)
    qed
  qed
qed

text \<open>The rectangle itself --- the stopping-time analogue of
  @{thm [source] rect_vimage_natural_filtration}.\<close>

lemma rect_vimage_pre_sigma_stopping:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and u: "0 \<le> u" and uT: "u \<le> T"
    and A: "A \<in> sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) u)"
  shows "(\<lambda>\<omega> :: 'n pairpath. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>)) -` (A \<times> A')
        \<inter> space P
      \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v))
          (\<lambda>\<omega>. max u (\<theta> \<omega>))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have maxM: "(\<lambda>\<omega> :: 'n pairpath. max u (\<theta> \<omega>)) \<in> borel_measurable ?B"
    using thM by measurable
  have stmax: "{\<omega> \<in> space P. max u (\<theta> \<omega>) \<le> t} \<in> sets (?F t)"
    if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all
        [OF T0 path_stopping_time_max[OF st u uT] maxM t])
  have le: "\<theta> \<omega> \<le> max u (\<theta> \<omega>)" for \<omega> :: "'n pairpath" by simp
  have c1: "pstopped T \<theta> -` A \<inter> space P \<in> pre_sigma_of P ?F \<theta>"
    by (rule pstopped_vimage_pre_sigma[OF T0 setsP st thM A])
  have c1': "pstopped T \<theta> -` A \<inter> space P
      \<in> pre_sigma_of P ?F (\<lambda>\<omega>. max u (\<theta> \<omega>))"
    using pre_sigma_of_mono[OF le stmax] c1 by blast
  have c2: "pafter T \<theta> -` A' \<inter> space P
      \<in> pre_sigma_of P ?F (\<lambda>\<omega>. max u (\<theta> \<omega>))"
    by (rule pafter_vimage_pre_sigma[OF T0 setsP st thM u uT A'])
  have "(\<lambda>\<omega> :: 'n pairpath. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>)) -` (A \<times> A')
        \<inter> space P
      = (pstopped T \<theta> -` A \<inter> space P) \<inter> (pafter T \<theta> -` A' \<inter> space P)"
    by auto
  then show ?thesis using pre_sigma_of_Int[OF c1' c2] by simp
qed

section \<open>Sampling at \<open>u \<or> \<theta>\<close>: the increment identity and its integrand\<close>

text \<open>\<open>stopped_increment_of_horizon_gen\<close> is stated for the offset
  family \<open>(\<theta>+i) \<and> T\<close>; the additive split instead uses the delayed family
  \<open>u \<or> \<theta>\<close>.  Both are instances of one statement about an arbitrary pair of
  ordered bounded path stopping times, proved here and already abstract in
  @{thm [source] set_martingale_sampling_two}.

  Integrability of the sampled process, free in the deterministic
  development from the martingale locale, is reconstructed here from the
  dyadic approximation and the same dominating function.\<close>

lemma integrable_at_bounded_stopping_time:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<sigma> :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Y"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U" and U0: "0 \<le> U"
    and cont: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<lambda>n. Y (dyceil n U (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    and Dbd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> U \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> D \<omega>"
    and Dint: "integrable M D"
  shows "integrable M (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
proof -
  interpret Mg: martingale M F 0 Y by (rule mg)
  define \<sigma>n where "\<sigma>n n \<omega> = dyceil n U (\<sigma> \<omega>)" for n :: nat and \<omega> :: 'a
  define Vn where "Vn n = (\<lambda>j. min U (real_of_int j / 2^n)) ` {0..\<lceil>2^n * U\<rceil>}"
    for n :: nat
  have Vfin: "finite (Vn n)" for n
    unfolding Vn_def by (rule finite_dyceil_range)
  have Vnn: "0 \<le> u" if "u \<in> Vn n" for u n
  proof -
    from that obtain j where j: "j \<in> {0..\<lceil>2^n * U\<rceil>}"
      and u: "u = min U (real_of_int j / 2^n)" unfolding Vn_def by blast
    show ?thesis using j u U0 by simp
  qed
  have vals: "\<sigma>n n \<omega> \<in> Vn n" for n \<omega>
    unfolding \<sigma>n_def Vn_def by (rule dyceil_range[OF U0 sig0 sigU])
  have stopn: "{\<omega> \<in> space M. \<sigma>n n \<omega> \<le> t} \<in> sets (F t)" if t: "0 \<le> t" for n t
    unfolding \<sigma>n_def by (rule dyceil_stopping[OF mono stop sub sig0 sigU t])
  have Ym: "Y u \<in> borel_measurable M" if "0 \<le> u" for u
    using Mg.integrable[OF that] by (rule borel_measurable_integrable)
  have gm: "(\<lambda>\<omega>. Y (\<sigma>n n \<omega>) \<omega>) \<in> borel_measurable M" for n
    by (rule borel_measurable_at_simple_time
        [OF sub mono stopn Vfin Vnn vals Ym])
  have lim: "(\<lambda>n. Y (\<sigma>n n \<omega>) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>" if w: "\<omega> \<in> space M" for \<omega>
    unfolding \<sigma>n_def by (rule cont[OF w])
  have glim: "(\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>) \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ_metric[OF gm lim])
  have bd: "AE \<omega> in M. norm (Y (\<sigma> \<omega>) \<omega>) \<le> norm \<bar>D \<omega>\<bar>"
    using Dbd
  proof eventually_elim
    case (elim \<omega>)
    have "\<bar>Y (\<sigma> \<omega>) \<omega>\<bar> \<le> D \<omega>" using elim sig0[of \<omega>] sigU[of \<omega>] by simp
    then show ?case by simp
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[where f = "\<lambda>\<omega>. \<bar>D \<omega>\<bar>"])
    show "integrable M (\<lambda>\<omega>. \<bar>D \<omega>\<bar>)" using Dint by simp
    show "(\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>) \<in> borel_measurable M" by (rule glim)
    show "AE \<omega> in M. norm (Y (\<sigma> \<omega>) \<omega>) \<le> norm \<bar>D \<omega>\<bar>" by (rule bd)
  qed
qed

theorem stopped_increment_of_horizon_gen:
  fixes P :: "('n::finite pairpath) measure"
    and Y :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real" and \<sigma> \<rho> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and H: "horizon_sq_int_martingale P
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) Y T"
    and Ycont: "\<And>\<omega>. \<omega> \<in> space P \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    and sts: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and str: "path_stopping_time T \<rho>"
    and rM: "\<rho> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and le: "\<And>\<omega> :: 'n pairpath. \<sigma> \<omega> \<le> \<rho> \<omega>"
    and A: "A \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<sigma>"
  shows "set_lebesgue_integral P A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
       = set_lebesgue_integral P A (\<lambda>\<omega>. Y (\<rho> \<omega>) \<omega>)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have T0': "0 \<le> T" using T0 by simp
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  interpret H: horizon_sq_int_martingale P ?F Y T by (rule H)

  have mg: "martingale P ?F 0 Y" by (rule H.martingale_axioms)
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have sub: "subalgebra P (?F t)" if "0 \<le> t" for t
    by (rule H.subalgebras[OF that])
  have sig0: "0 \<le> \<sigma> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF sts])
  have sigU: "\<sigma> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF sts])
  have rho0: "0 \<le> \<rho> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF str])
  have rhoU: "\<rho> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF str])
  have stops: "{\<omega> \<in> space P. \<sigma> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' sts sM t])
  have stopr: "{\<omega> \<in> space P. \<rho> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' str rM t])

  have conv: "(\<lambda>n. Y (dyceil n T s) \<omega>) \<longlonglongrightarrow> Y s \<omega>"
    if w: "\<omega> \<in> space P" and s0: "0 \<le> s" and sT: "s \<le> T" for \<omega> s
  proof (rule continuous_on_tendsto_compose
      [OF Ycont[OF w] dyceil_tendsto[OF s0 sT]])
    show "\<forall>\<^sub>F n in sequentially. dyceil n T s \<in> {0..T}"
      using dyceil_nonneg[OF s0 sT] dyceil_le_U[of _ T s] by simp
    show "s \<in> {0..T}" using s0 sT by simp
  qed
  have conts: "(\<lambda>n. Y (dyceil n T (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    if w: "\<omega> \<in> space P" for \<omega> :: "'n pairpath"
    by (rule conv[OF w sig0 sigU])
  have contr: "(\<lambda>n. Y (dyceil n T (\<rho> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<rho> \<omega>) \<omega>"
    if w: "\<omega> \<in> space P" for \<omega> :: "'n pairpath"
    by (rule conv[OF w rho0 rhoU])

  have pathcont: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    by (rule AE_I2) (rule Ycont)
  have Dbd: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates[OF pathcont])
  have Dint: "integrable P H.Dsup" by (rule H.Dsup_integrable)

  show ?thesis
    by (rule set_martingale_sampling_two
        [OF mg mono sub A stops stopr sig0 sigU rho0 rhoU T0' le
          conts contr Dbd Dint])
qed

lemma integrable_at_path_stopping_time:
  fixes P :: "('n::finite pairpath) measure"
    and Y :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real" and \<sigma> :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and H: "horizon_sq_int_martingale P
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) Y T"
    and Ycont: "\<And>\<omega>. \<omega> \<in> space P \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    and sts: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "integrable P (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have T0': "0 \<le> T" using T0 by simp
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  interpret H: horizon_sq_int_martingale P ?F Y T by (rule H)

  have mg: "martingale P ?F 0 Y" by (rule H.martingale_axioms)
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have sub: "subalgebra P (?F t)" if "0 \<le> t" for t
    by (rule H.subalgebras[OF that])
  have sig0: "0 \<le> \<sigma> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF sts])
  have sigU: "\<sigma> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF sts])
  have stops: "{\<omega> \<in> space P. \<sigma> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' sts sM t])
  have conts: "(\<lambda>n. Y (dyceil n T (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    if w: "\<omega> \<in> space P" for \<omega> :: "'n pairpath"
  proof (rule continuous_on_tendsto_compose
      [OF Ycont[OF w] dyceil_tendsto[OF sig0 sigU]])
    show "\<forall>\<^sub>F n in sequentially. dyceil n T (\<sigma> \<omega>) \<in> {0..T}"
      using dyceil_nonneg[OF sig0 sigU] dyceil_le_U[of _ T "\<sigma> \<omega>"] by simp
    show "\<sigma> \<omega> \<in> {0..T}" using sig0 sigU by simp
  qed
  have pathcont: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    by (rule AE_I2) (rule Ycont)
  have Dbd: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates[OF pathcont])
  have Dint: "integrable P H.Dsup" by (rule H.Dsup_integrable)

  show ?thesis
    by (rule integrable_at_bounded_stopping_time
        [OF mg mono sub stops sig0 sigU T0' conts Dbd Dint])
qed

section \<open>The increment identity moves to the kernel\<close>

text \<open>The stopping-time twin of @{thm [source] pfut_rcd_X_increment_zero},
  stated once for an arbitrary real integrand \<open>h\<close> on the future factor
  together with the identity \<open>hP\<close> pulling it back to an increment of a
  horizon martingale \<open>Y\<close> of \<open>P\<close>.  Every clause of the class surviving the
  additive split has this shape, so the disintegration is done once here
  and instantiated afterwards.

  The chain follows the deterministic one --- @{thm [source] AE_kernel_integral_zero}
  to rectangles, @{thm [source] integral_ksemi_rect_of_set_integral} to a set
  integral over \<open>P\<close> --- with the conditioning set landing in
  \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<or>\<^sub> \<^sub>\<theta>\<^sub>)\<close> via @{thm [source] rect_vimage_pre_sigma_stopping} instead of a
  deterministic \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>, closed by
  @{thm [source] stopped_increment_of_horizon_gen} instead of
  @{thm [source] martingale.set_integral_eq}.\<close>

text \<open>Clause (iv) for the \<open>X\<close> martingale: the additive split carries it
  across unchanged, since \<^term>\<open>pafter T \<theta> \<omega>\<close> is a difference of values of
  \<open>\<omega>\<close> and the constant \<^term>\<open>\<omega> (\<theta> \<omega>)\<close> cancels between the two times.\<close>

section \<open>The cross term: an increment against a known factor\<close>

text \<open>The compensated clause does not ride along on the additive split,
  because \<^const>\<open>outerp\<close> is quadratic.  Writing \<open>b = fst (\<omega> (\<theta> \<omega>))\<close>,

  \<open>outerp (X\<^sub>u - b) - (\<langle>X\<rangle>\<^sub>u - \<langle>X\<rangle>\<^sub>\<theta>)
     = (outerp X\<^sub>u - \<langle>X\<rangle>\<^sub>u) - X\<^sub>u bᵀ - b X\<^sub>uᵀ + outerp b + \<langle>X\<rangle>\<^sub>\<theta>\<close>

  and between two times the last two summands cancel, leaving a compensated
  increment plus two cross terms \<open>(\<Delta>X) bᵀ\<close> and \<open>b (\<Delta>X)ᵀ\<close>.  The factor \<open>b\<close> is
  \<open>\<F>\<^sub>\<theta>\<close>-measurable but not constant, so those terms need
  \<open>E[\<Delta>Y \<sqdot> Z] = 0\<close> for a square-integrable \<open>\<F>\<^sub>\<sigma>\<close>-measurable \<open>Z\<close>.

  With \<open>\<F>\<^sub>\<sigma>\<close> a genuine \<^const>\<open>sigma\<close> algebra the argument needs no
  approximation by simple functions: the conditional expectation of the
  increment vanishes (@{thm [source] AE_zero_of_set_integral_zero} against
  @{thm [source] stopped_increment_of_horizon_gen}), and \<open>Z\<close> pulls out of it
  (\<open>cond_exp_measurable_mult\<close>), using square-integrability of the
  increment from Doob's \<open>Dsup_sq_integrable\<close>.\<close>

lemma set_integral_increment_times_known:
  fixes P :: "('n::finite pairpath) measure"
    and Y :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real" and Z :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 < T" and PS: "prob_space P"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and H: "horizon_sq_int_martingale P
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) Y T"
    and Ycont: "\<And>\<omega>. \<omega> \<in> space P \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    and sts: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and str: "path_stopping_time T \<rho>"
    and rM: "\<rho> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and le: "\<And>\<omega> :: 'n pairpath. \<sigma> \<omega> \<le> \<rho> \<omega>"
    and Zpre: "\<And>B. B \<in> sets borel \<Longrightarrow> Z -` B \<inter> space P
        \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<sigma>"
    and Zsq: "integrable P (\<lambda>\<omega> :: 'n pairpath. (Z \<omega>)\<^sup>2)"
    and A: "A \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<sigma>"
  shows "integrable P (\<lambda>\<omega> :: 'n pairpath. (Y (\<rho> \<omega>) \<omega> - Y (\<sigma> \<omega>) \<omega>) * Z \<omega>)"
    and "set_lebesgue_integral P A
        (\<lambda>\<omega> :: 'n pairpath. (Y (\<rho> \<omega>) \<omega> - Y (\<sigma> \<omega>) \<omega>) * Z \<omega>) = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?D = "\<lambda>\<omega> :: 'n pairpath. Y (\<rho> \<omega>) \<omega> - Y (\<sigma> \<omega>) \<omega>"
  let ?G = "sigma (space P) (pre_sigma_of P ?F \<sigma>)"
  have T0': "0 \<le> T" using T0 by simp
  interpret PP: prob_space P by (rule PS)
  interpret H: horizon_sq_int_martingale P ?F Y T by (rule H)
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have subF: "subalgebra P (?F t)" if "0 \<le> t" for t
    by (rule H.subalgebras[OF that])
  have stops: "{\<omega> \<in> space P. \<sigma> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' sts sM t])

  \<comment> \<open>\<open>\<F>\<^sub>\<sigma>\<close> as a genuine sub-\<open>\<sigma>\<close>-algebra of \<open>P\<close>\<close>
  have sa: "sigma_algebra (space P) (pre_sigma_of P ?F \<sigma>)"
    by (rule sigma_algebra_pre_sigma_of[OF subF stops])
  have setsG: "sets ?G = pre_sigma_of P ?F \<sigma>"
    by (rule sigma_algebra.sets_measure_of_eq[OF sa])
  have spG: "space ?G = space P" by (simp add: space_measure_of_conv)
  have subG: "subalgebra P ?G"
    unfolding subalgebra_def using spG setsG pre_sigma_of_sets by auto
  have fm: "finite_measure P"
    by (rule finite_measureI) (simp add: PP.emeasure_space_1)
  interpret SF: sigma_finite_subalgebra P ?G
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fm subG)

  \<comment> \<open>the increment: integrable, and square integrable by Doob\<close>
  have intr: "integrable P (\<lambda>\<omega> :: 'n pairpath. Y (\<rho> \<omega>) \<omega>)"
    by (rule integrable_at_path_stopping_time[OF T0 setsP H Ycont str rM])
  have ints: "integrable P (\<lambda>\<omega> :: 'n pairpath. Y (\<sigma> \<omega>) \<omega>)"
    by (rule integrable_at_path_stopping_time[OF T0 setsP H Ycont sts sM])
  have intD: "integrable P ?D"
    by (rule Bochner_Integration.integrable_diff[OF intr ints])
  have pathcont: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    by (rule AE_I2) (rule Ycont)
  have Dbd: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates[OF pathcont])
  have Dsq: "integrable P (\<lambda>\<omega> :: 'n pairpath. (?D \<omega>)\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound
      [where f = "\<lambda>\<omega> :: 'n pairpath. 4 * (H.Dsup \<omega>)\<^sup>2"])
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. 4 * (H.Dsup \<omega>)\<^sup>2)"
      using H.Dsup_sq_integrable by simp
    show "(\<lambda>\<omega> :: 'n pairpath. (?D \<omega>)\<^sup>2) \<in> borel_measurable P"
      using intD by simp
    show "AE \<omega> in P. norm ((?D \<omega>)\<^sup>2) \<le> norm (4 * (H.Dsup \<omega>)\<^sup>2)"
      using Dbd
    proof eventually_elim
      case (elim \<omega>)
      have bs: "\<bar>Y (\<sigma> \<omega>) \<omega>\<bar> \<le> H.Dsup \<omega>"
        using elim path_stopping_time_nonneg[OF sts, of \<omega>]
          path_stopping_time_le[OF sts, of \<omega>] by simp
      have br: "\<bar>Y (\<rho> \<omega>) \<omega>\<bar> \<le> H.Dsup \<omega>"
        using elim path_stopping_time_nonneg[OF str, of \<omega>]
          path_stopping_time_le[OF str, of \<omega>] by simp
      have le2: "\<bar>?D \<omega>\<bar> \<le> 2 * H.Dsup \<omega>" using bs br by simp
      have "(?D \<omega>)\<^sup>2 = \<bar>?D \<omega>\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (2 * H.Dsup \<omega>)\<^sup>2"
        by (rule power_mono[OF le2 abs_ge_zero])
      finally show ?case by (simp add: power_mult_distrib)
    qed
  qed

  \<comment> \<open>the known factor\<close>
  have ZG: "Z \<in> borel_measurable ?G"
  proof (rule measurableI)
    show "Z \<omega> \<in> space borel" for \<omega> :: "'n pairpath" by simp
    fix B :: "real set" assume B: "B \<in> sets borel"
    show "Z -` B \<inter> space ?G \<in> sets ?G" using Zpre[OF B] setsG spG by simp
  qed
  have ZP: "Z \<in> borel_measurable P"
    using ZG measurable_from_subalg[OF subG] by blast
  have Dm: "?D \<in> borel_measurable P" using intD by simp
  have intZD: "integrable P (\<lambda>\<omega> :: 'n pairpath. Z \<omega> * ?D \<omega>)"
    by (rule integrable_mult_of_sq[OF ZP Dm Zsq Dsq])
  show int1: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?D \<omega> * Z \<omega>)"
    using intZD by (simp add: mult.commute)

  \<comment> \<open>the increment conditions to zero\<close>
  have ceD: "AE \<omega> in P. cond_exp P ?G ?D \<omega> = 0"
  proof (rule AE_zero_of_set_integral_zero[OF subG])
    show "integrable P (cond_exp P ?G ?D)" by (rule integrable_cond_exp)
    show "cond_exp P ?G ?D \<in> borel_measurable ?G"
      by (rule borel_measurable_cond_exp)
    fix C assume C: "C \<in> sets ?G"
    then have C': "C \<in> pre_sigma_of P ?F \<sigma>" using setsG by simp
    have CP: "C \<in> sets P" by (rule pre_sigma_of_sets[OF C'])
    have sii: "set_integrable P C (\<lambda>\<omega> :: 'n pairpath. Y (\<sigma> \<omega>) \<omega>)"
      unfolding set_integrable_def by (rule integrable_mult_indicator[OF CP ints])
    have sij: "set_integrable P C (\<lambda>\<omega> :: 'n pairpath. Y (\<rho> \<omega>) \<omega>)"
      unfolding set_integrable_def by (rule integrable_mult_indicator[OF CP intr])
    have "set_lebesgue_integral P C (cond_exp P ?G ?D)
        = set_lebesgue_integral P C ?D"
      by (rule SF.cond_exp_set_integral[OF intD C, symmetric])
    also have "\<dots> = set_lebesgue_integral P C (\<lambda>\<omega>. Y (\<rho> \<omega>) \<omega>)
        - set_lebesgue_integral P C (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
      using set_integral_diff(2)[OF sij sii] by simp
    also have "\<dots> = 0"
      using stopped_increment_of_horizon_gen
        [OF T0 setsP H Ycont sts sM str rM le C'] by simp
    finally show "set_lebesgue_integral P C (cond_exp P ?G ?D) = 0" .
  qed
  have ceZD: "AE \<omega> in P. cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>) \<omega>
      = Z \<omega> * cond_exp P ?G ?D \<omega>"
    by (rule SF.cond_exp_measurable_mult(2)[OF intZD intD ZG])
  have ae0: "AE \<omega> in P. cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>) \<omega> = 0"
    using ceZD ceD by eventually_elim simp

  have AP: "A \<in> sets P" by (rule pre_sigma_of_sets[OF A])
  have AG: "A \<in> sets ?G" using A setsG by simp
  have aeA: "AE \<omega>\<in>A in P. cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>) \<omega> = 0"
    using ae0 by (auto elim: eventually_mono)
  have "set_lebesgue_integral P A (\<lambda>\<omega> :: 'n pairpath. Z \<omega> * ?D \<omega>)
      = set_lebesgue_integral P A (cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>))"
    by (rule SF.cond_exp_set_integral[OF intZD AG])
  also have "\<dots> = set_lebesgue_integral P A (\<lambda>\<omega> :: 'n pairpath. 0)"
    by (rule set_lebesgue_integral_cong_AE
        [OF AP SF.borel_measurable_cond_exp' borel_measurable_const aeA])
  also have "\<dots> = 0" by (simp add: set_lebesgue_integral_def)
  finally show "set_lebesgue_integral P A
      (\<lambda>\<omega> :: 'n pairpath. ?D \<omega> * Z \<omega>) = 0"
    by (simp add: mult.commute)
qed

text \<open>The known factor is a function of the stopped path, hence \<open>\<F>\<^sub>\<theta>\<close>- and a
  fortiori \<open>\<F>\<^sub>(\<^sub>u\<^sub> \<^sub>\<or>\<^sub> \<^sub>\<theta>\<^sub>)\<close>-measurable.\<close>

section \<open>Clause (iv) for the compensated martingale\<close>

text \<open>The second, and last, clause-(iv) instance.  The pathwise identity is
  the \<^const>\<open>outerp\<close> expansion: with \<open>\<sigma> = i \<or> \<theta>\<close>, \<open>\<rho> = j \<or> \<theta>\<close> and
  \<open>b = fst (\<omega> (\<theta> \<omega>))\<close>,

  \<open>h (pafter T \<theta> \<omega>) = (Ym\<^sub>\<rho> - Ym\<^sub>\<sigma>) - (Yc\<^sub>\<rho> - Yc\<^sub>\<sigma>)\<sqdot>b$d - (Yd\<^sub>\<rho> - Yd\<^sub>\<sigma>)\<sqdot>b$c\<close>

  --- a compensated increment, which @{thm [source] stopped_increment_of_horizon_gen}
  kills, and two cross terms, which
  @{thm [source] set_integral_increment_times_known} kills.  The constants
  \<open>outerp b\<close> and \<open>\<langle>X\<rangle>\<^sub>\<theta>\<close> have already cancelled between the two times.\<close>


(*<*)
end
(*>*)
