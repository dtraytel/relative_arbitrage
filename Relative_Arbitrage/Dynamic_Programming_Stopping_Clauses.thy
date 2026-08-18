section \<open>Clause (iv) at a stopping time\<close>

(*<*)
theory Dynamic_Programming_Stopping_Clauses
  imports Dynamic_Programming_Optional_Sampling
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Time_Martingales.Time_Discretisation"
    Path_Law_Pasting
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














end
(*>*)
