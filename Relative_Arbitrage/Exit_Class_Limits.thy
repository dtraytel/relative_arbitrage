section \<open>Lemma 2.3: the class is closed under weak limits\<close>

(*<*)
theory Exit_Class_Limits
  imports
    "Levy_Prokhorov_Metric.Space_of_Finite_Measures" Exit_Class Path_Splicing
begin

(*>*)

section \<open>The martingale clauses of Lemma 2.3\<close>

text \<open>This section proves the martingale clauses of Lemma 2.3 for a weak
  limit of the paper's class, combining the class machinery of
  @{theory Relative_Arbitrage.Exit_Class} with the generic weak-limit
  martingale theorem @{thm [source] martingale_F_limit} of
  @{theory Relative_Arbitrage.Pair_Path_Laws}.

  Unlike the two closed path conditions of (1.7), which pass to a weak
  limit directly (\<open>Exit_Class.exit_class_start_limit\<close>,
  \<open>\<dots>_diffquot_limit\<close>), the martingale clauses are statements about
  integrals against past-measurable test functions, and only bounded
  continuous tests survive a weak limit.  @{thm [source] martingale_F_limit}
  carries the martingale property of a continuous functional \<open>F\<close> of the
  path through a weak limit, given a uniform \<open>L\<^sup>2\<close> bound on \<open>F\<close>; the
  coordinate clause is the case \<open>F = (\<lambda>p. fst p $ i)\<close>, and the compensated
  clause below is the case of an entry of \<open>outerp X - Y\<close>.  The paper's class
  admits no clamp: its processes are neither stopped nor bounded, so the
  test functional is continuous but unbounded, and the transfer runs through
  the uniform \<open>L\<^sup>2\<close> bound (\<open>Exit_Class.exit_class_sq_mean_le\<close>).\<close>

subsection \<open>The coordinate clause\<close>

lemma exit_class_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  using Q unfolding exit_class_def by blast

lemma exit_class_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)"
  by (rule martingale_vec_nth[OF exit_class_X_martingale[OF Q]])

lemma exit_class_sq_nn_bound:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q)
      \<le> ennreal ((x $ i)\<^sup>2 + real CARD('n) * L * T)"
  by (rule pair_law_coord_sq_nn_bound[OF exit_class_sets[OF Q] u
        exit_class_sq_integrable[OF T L Q u]
        exit_class_sq_mean_le[OF T L Q u]])

theorem exit_class_coord_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)"
proof (rule martingale_F_limit
    [where F = "\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p $ i"
       and C = "(x $ i)\<^sup>2 + real CARD('n) * L * T"])
  show "0 \<le> T" by (rule T)
  show "continuous_on UNIV (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p $ i)"
    by (intro continuous_intros)
  show "prob_space (Qm m)" for m by (rule exit_class_prob[OF mem])
  show "sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)" for m
    by (rule exit_class_sets[OF mem])
  show "martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)" for m
    by (rule exit_class_coord_martingale[OF mem])
  show "0 \<le> (x $ i)\<^sup>2 + real CARD('n) * L * T"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg) (use T L in auto)
  show "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>(Qm m))
      \<le> ennreal ((x $ i)\<^sup>2 + real CARD('n) * L * T)" if "u \<in> {0..T}" for m u
    by (rule exit_class_sq_nn_bound[OF T L mem that])
qed (use wc prob setsQ in auto)

corollary exit_class_X_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  by (rule martingale_vecI)
    (rule exit_class_coord_martingale_limit[OF T L mem wc prob setsQ])

subsection \<open>Lemma 2.3: three of the four clauses, at the limit\<close>

text \<open>A weak limit of class members satisfies the start clause, the
  covariation clause, and the \<open>X\<close>-martingale clause of (1.7).  What
  remains for \<open>Q \<in> exit_class k L T x\<close> is the compensated clause
  \<open>outerp X - Y\<close>: carrying it through the weak limit needs an \<open>L\<^sup>2\<close> bound
  on \<open>X\<^sub>i X\<^sub>j\<close>, i.e. a uniform fourth moment, which the paper obtains from
  Burkholder--Davis--Gundy -- not available in the AFP, and supplied
  instead in the next section.\<close>

theorem exit_class_limit_three_clauses:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    and "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    and "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
proof -
  show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule exit_class_start_limit[OF T mem wc prob setsQ])
  show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule exit_class_diffquot_limit[OF mem wc prob setsQ])
  show "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
    by (rule exit_class_X_martingale_limit[OF T L mem wc prob setsQ])
qed

section \<open>The uniform fourth moment of the class, by localization\<close>

text \<open>This bound supplies the compensated clause of Lemma 2.3.  The
  repo's estimate \<open>Increment_Moments.fourth_moment_bound_bounded\<close> wants a
  uniform sup bound on the process, which a class member does not have and
  which is structural to that estimate (it also fixes the constant of
  \<open>remainder_tendsto_zero\<close>).  The process stopped at
  \<open>\<tau>\<^sub>R = inf {t. R \<le> \<bar>X\<^sub>t\<bar>}\<close> does have a sup bound by construction; applying
  the estimate there gives a bound uniform in \<open>R\<close>, and path continuity on
  the compact \<open>[0,T]\<close> makes \<open>\<tau>\<^sub>R > T\<close> for large \<open>R\<close> pathwise, so Fatou
  removes the localization.  This avoids Burkholder--Davis--Gundy, using
  instead \<open>Stopping_Times.etime_stopping_time\<close> for \<open>\<tau>\<^sub>R\<close>,
  \<open>Doob_Inequality.horizon_sq_int_martingale\<close> for the integrable envelope
  that \<open>Optional_Sampling.optional_stopping\<close> asks for, and
  \<open>optional_stopping\<close> itself.\<close>

subsection \<open>The coordinate process, its compensator, and its paths\<close>

lemma exit_class_coord_adapted:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "adapted_process Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)"
proof -
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i"
    by (rule exit_class_coord_martingale[OF Q])
  show ?thesis by unfold_locales
qed

text \<open>Continuity holds on the whole half-line, not just on \<open>{0..T}\<close>: the
  stopped process is constant after the horizon.  That is the form
  \<open>Stopped_Adaptedness.stopped_adapted_of_cont\<close> asks for.\<close>




lemma exit_class_compensated_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. (fst (\<omega> (min u T)) $ i)\<^sup>2 - snd (\<omega> (min u T)) $ i $ i)"
proof -
  have mg: "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ i $ i)"
    by (rule martingale_mat_nth
        [OF exit_class_compensated_martingale[OF Q]])
  have eq: "(\<lambda>u \<omega> :: 'n pairpath.
        (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ i $ i)
      = (\<lambda>u \<omega> :: 'n pairpath.
        (fst (\<omega> (min u T)) $ i)\<^sup>2 - snd (\<omega> (min u T)) $ i $ i)"
    by (rule ext, rule ext) (simp add: outerp_def power2_eq_square)
  show ?thesis using mg unfolding eq .
qed

subsection \<open>The localizing stopping time\<close>

text \<open>\<open>ploc T i R\<close> is the first time the \<open>i\<close>-th coordinate reaches level
  \<open>R\<close> in absolute value, capped at the horizon.  It is a stopping time by
  \<open>Stopping_Times.etime_stopping_time\<close> --- the set \<open>{y. R \<le> \<bar>y\<bar>}\<close> is closed and
  nonempty and the paths are continuous --- and the process stopped at it
  is bounded, which is the whole point.\<close>





lemma exit_class_cont_adapted:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
  shows "cont_adapted_process Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u))
      (pcoord T i) T"
proof (intro cont_adapted_process.intro cont_adapted_process_axioms.intro)
  show "adapted_process Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (pcoord T i)"
    unfolding pcoord_def by (rule exit_class_coord_adapted[OF Q])
  show "0 \<le> T" by (rule T)
  show "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> continuous_on {0..T} (\<lambda>s. pcoord T i s \<omega>)"
    unfolding pcoord_def
    by (rule continuous_on_subset
        [OF exit_class_coord_paths_cont[OF T setsQ]]) auto
qed

lemma exit_class_ploc_stopping:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and t: "0 \<le> t"
  shows "{\<omega> \<in> space Q. ploc T i R \<omega> \<le> t}
      \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) t)"
proof -
  interpret CA: cont_adapted_process Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)"
      "pcoord T i" T
    by (rule exit_class_cont_adapted[OF T setsQ Q])
  show ?thesis
    unfolding ploc_def
    by (rule CA.etime_stopping_time[OF closed_abs_ge abs_ge_nonempty t])
qed

text \<open>The point of the localization: below the level the stopped path has
  not yet reached \<open>R\<close>, and at the level it is exactly \<open>R\<close> by continuity, so
  the stopped process never exceeds \<open>R\<close> in absolute value --- except
  possibly at time \<open>0\<close>, where it is the starting coordinate.\<close>

text \<open>At the stopping time itself the path has value exactly \<open>R\<close>, not more,
  which is why the bound needs continuity and not just the definition of an
  infimum.  \<open>Stopping_Times.etime_stays_in_cball\<close> is precisely that
  statement.\<close>


theorem exit_class_stopped_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>v \<omega>. pcoord T i (min v (ploc T i R \<omega>)) \<omega>)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have mg: "martingale Q ?F 0 (pcoord T i)"
    unfolding pcoord_def by (rule exit_class_coord_martingale[OF Q])
  have sq: "integrable Q (\<lambda>\<omega>. (pcoord T i s \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    unfolding pcoord_def
    using T0 s by (intro exit_class_sq_integrable[OF T0 L Q]) simp
  have adp: "adapted_process Q ?F 0 (pcoord T i)"
    unfolding pcoord_def by (rule exit_class_coord_adapted[OF Q])
  have cont0: "continuous_on {0..} (\<lambda>s. pcoord T i s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega>
    unfolding pcoord_def
    by (rule exit_class_coord_paths_cont[OF T0 setsQ w])
  have contu: "continuous_on {0..u} (\<lambda>s. pcoord T i s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    by (rule continuous_on_subset[OF cont0[OF w]]) auto
  have lnn: "0 \<le> ploc T i R \<omega>" for \<omega> by (rule ploc_nonneg[OF T0])
  interpret HM: horizon_sq_int_martingale Q ?F "pcoord T i" T
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mg T prob sq)
  have domT: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    by (rule HM.Dsup_dominates) (intro AE_I2 contu)
  \<comment> \<open>past the horizon the process no longer moves, so the envelope built at
      \<open>T\<close> dominates it at every later time as well.\<close>
  have domA: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    for u
    using domT
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    show "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s"
      have "pcoord T i s \<omega> = pcoord T i (min s T) \<omega>"
        unfolding pcoord_def by simp
      moreover have "\<bar>pcoord T i (min s T) \<omega>\<bar> \<le> HM.Dsup \<omega>"
        using h s T0 by simp
      ultimately show "\<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>" by simp
    qed
  qed
  show ?thesis
  proof (rule optional_stopping[where D = "\<lambda>_. HM.Dsup"])
    show "martingale Q ?F 0 (pcoord T i)" by (rule mg)
    show "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> 0 \<le> ploc T i R \<omega>" by (rule lnn)
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space Q. ploc T i R \<omega> \<le> s} \<in> sets (?F s)"
      by (rule exit_class_ploc_stopping[OF T0 setsQ Q])
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q. continuous_on {0..u} (\<lambda>s. pcoord T i s \<omega>)"
      by (intro AE_I2 contu)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q.
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
      by (rule domA)
    show "\<And>u. 0 < u \<Longrightarrow> integrable Q HM.Dsup" by (rule HM.Dsup_integrable)
    show "\<And>v. 0 \<le> v \<Longrightarrow> (\<lambda>\<omega>. pcoord T i (min v (ploc T i R \<omega>)) \<omega>)
        \<in> borel_measurable (?F v)"
      by (rule stopped_adapted_of_cont
          [OF adp lnn exit_class_ploc_stopping[OF T0 setsQ Q] cont0])
  qed
qed

text \<open>The compensated process is stopped by the same argument.  Its
  envelope is \<open>Dsup\<^sup>2 + n\<sqdot>L\<sqdot>T\<close>: the squared coordinate is dominated by the
  square of Doob's envelope (\<open>Dsup_sq_integrable\<close>) and the compensator by
  the class's Lipschitz bound on \<open>Y\<close>.\<close>

theorem exit_class_stopped_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>v \<omega>. (fst (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i)\<^sup>2
        - snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (fst (\<omega> (min u T)) $ i)\<^sup>2 - snd (\<omega> (min u T)) $ i $ i"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have mgZ: "martingale Q ?F 0 ?Z"
    by (rule exit_class_compensated_coord_martingale[OF Q])
  have adpZ: "adapted_process Q ?F 0 ?Z"
  proof -
    interpret MZ: martingale Q ?F 0 ?Z by (rule mgZ)
    show ?thesis by unfold_locales
  qed
  have contZ: "continuous_on {0..} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space Q" for \<omega>
    by (rule exit_class_comp_paths_cont[OF T0 setsQ w])
  have contZu: "continuous_on {0..u} (\<lambda>s. ?Z s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    by (rule continuous_on_subset[OF contZ[OF w]]) auto
  have lnn: "0 \<le> ploc T i R \<omega>" for \<omega> by (rule ploc_nonneg[OF T0])
  \<comment> \<open>the \<open>X\<close>-side envelope, from Doob, exactly as for the coordinate.\<close>
  have mg: "martingale Q ?F 0 (pcoord T i)"
    unfolding pcoord_def by (rule exit_class_coord_martingale[OF Q])
  have sq: "integrable Q (\<lambda>\<omega>. (pcoord T i s \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    unfolding pcoord_def
    using T0 s by (intro exit_class_sq_integrable[OF T0 L Q]) simp
  have contX: "continuous_on {0..u} (\<lambda>s. pcoord T i s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    unfolding pcoord_def
    by (rule continuous_on_subset
        [OF exit_class_coord_paths_cont[OF T0 setsQ w]]) auto
  interpret HM: horizon_sq_int_martingale Q ?F "pcoord T i" T
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mg T prob sq)
  have domT: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    by (rule HM.Dsup_dominates) (intro AE_I2 contX)
  \<comment> \<open>the \<open>Y\<close>-side envelope is the class's own Lipschitz bound.\<close>
  have ybnd: "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    by (rule exit_class_Y_bounded_ae[OF T0 L Q])
  have domZ: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
      \<bar>?Z s \<omega>\<bar> \<le> (HM.Dsup \<omega>)\<^sup>2 + real CARD('n) * L * T" for u
    using domT ybnd
  proof eventually_elim
    case (elim \<omega>)
    then have hX: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
      and hY: "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
      by blast+
    show ?case
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s"
      have mT: "min s T \<in> {0..T}" using s T0 by simp
      have bX: "\<bar>fst (\<omega> (min s T)) $ i\<bar> \<le> HM.Dsup \<omega>"
        using hX mT unfolding pcoord_def by simp
      have "\<bar>snd (\<omega> (min s T)) $ i $ i\<bar> \<le> norm (snd (\<omega> (min s T)) $ i)"
        using Finite_Cartesian_Product.norm_nth_le[of "snd (\<omega> (min s T)) $ i" i]
        by simp
      also have "\<dots> \<le> norm (snd (\<omega> (min s T)))"
        by (rule Finite_Cartesian_Product.norm_nth_le)
      also have "\<dots> \<le> real CARD('n) * L * T" using hY mT by blast
      finally have bY: "\<bar>snd (\<omega> (min s T)) $ i $ i\<bar> \<le> real CARD('n) * L * T" .
      have sqe: "(fst (\<omega> (min s T)) $ i)\<^sup>2 = \<bar>fst (\<omega> (min s T)) $ i\<bar>\<^sup>2"
        by simp
      have bX2: "(fst (\<omega> (min s T)) $ i)\<^sup>2 \<le> (HM.Dsup \<omega>)\<^sup>2"
        unfolding sqe by (rule power_mono[OF bX abs_ge_zero])
      have t1: "\<bar>?Z s \<omega>\<bar> \<le> (fst (\<omega> (min s T)) $ i)\<^sup>2
          + \<bar>snd (\<omega> (min s T)) $ i $ i\<bar>"
        using abs_triangle_ineq4[of "(fst (\<omega> (min s T)) $ i)\<^sup>2"
            "snd (\<omega> (min s T)) $ i $ i"]
        by simp
      show "\<bar>?Z s \<omega>\<bar> \<le> (HM.Dsup \<omega>)\<^sup>2 + real CARD('n) * L * T"
        using t1 bX2 bY by linarith
    qed
  qed
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have envint: "integrable Q (\<lambda>\<omega>. (HM.Dsup \<omega>)\<^sup>2 + real CARD('n) * L * T)"
    by (intro Bochner_Integration.integrable_add HM.Dsup_sq_integrable
        finite_measure.integrable_const[OF fmQ])
  show ?thesis
  proof (rule optional_stopping
      [where D = "\<lambda>_ \<omega>. (HM.Dsup \<omega>)\<^sup>2 + real CARD('n) * L * T"])
    show "martingale Q ?F 0 ?Z" by (rule mgZ)
    show "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> 0 \<le> ploc T i R \<omega>" by (rule lnn)
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space Q. ploc T i R \<omega> \<le> s} \<in> sets (?F s)"
      by (rule exit_class_ploc_stopping[OF T0 setsQ Q])
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q. continuous_on {0..u} (\<lambda>s. ?Z s \<omega>)"
      by (intro AE_I2 contZu)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>?Z s \<omega>\<bar> \<le> (HM.Dsup \<omega>)\<^sup>2 + real CARD('n) * L * T"
      by (rule domZ)
    show "\<And>u. 0 < u \<Longrightarrow>
        integrable Q (\<lambda>\<omega>. (HM.Dsup \<omega>)\<^sup>2 + real CARD('n) * L * T)"
      by (rule envint)
    show "\<And>v. 0 \<le> v \<Longrightarrow> (\<lambda>\<omega>. ?Z (min v (ploc T i R \<omega>)) \<omega>)
        \<in> borel_measurable (?F v)"
      by (rule stopped_adapted_of_cont
          [OF adpZ lnn exit_class_ploc_stopping[OF T0 setsQ Q] contZ])
  qed
qed

subsection \<open>The compensator rate at the stopped times\<close>

text \<open>Stopping can only shrink an interval --- \<open>w \<mapsto> min w c\<close> is
  nondecreasing and 1-Lipschitz --- so the class's diagonal rate bound
  survives it verbatim.\<close>

lemma exit_class_stopped_compensator_rate:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L" and Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
      0 \<le> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
        - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i
      \<and> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
        - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i \<le> L * (v - u)"
proof -
  have inc: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
      0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
      \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> L * (t - s)"
    by (rule exit_class_Y_diag_increment[OF L Q])
  from inc show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
        0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
        \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> L * (t - s)"
    show "\<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
          - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i
        \<and> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
          - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i \<le> L * (v - u)"
    proof (intro allI impI)
      fix u v :: real assume u: "0 \<le> u" and uv: "u \<le> v"
      have l0: "0 \<le> ploc T i R \<omega>" by (rule ploc_nonneg[OF T])
      have anz: "0 \<le> min (min u (ploc T i R \<omega>)) T" using u l0 T by simp
      have ab: "min (min u (ploc T i R \<omega>)) T
          \<le> min (min v (ploc T i R \<omega>)) T"
        by (intro min.mono uv order_refl)
      have bT: "min (min v (ploc T i R \<omega>)) T \<le> T" by simp
      have diff: "min (min v (ploc T i R \<omega>)) T
          - min (min u (ploc T i R \<omega>)) T \<le> v - u"
        using uv by (auto simp: min_def)
      have base: "0 \<le> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
            - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i
          \<and> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
            - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i
            \<le> L * (min (min v (ploc T i R \<omega>)) T
                - min (min u (ploc T i R \<omega>)) T)"
        using h anz ab bT by blast
      have "L * (min (min v (ploc T i R \<omega>)) T
          - min (min u (ploc T i R \<omega>)) T) \<le> L * (v - u)"
        by (rule mult_left_mono[OF diff L])
      then show "0 \<le> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
            - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i
          \<and> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
            - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i \<le> L * (v - u)"
        using base by linarith
    qed
  qed
qed

subsection \<open>The stopped process is bounded, hence integrable to any power\<close>

text \<open>On the stopped process every moment is free: the starting
  coordinate is \<open>x $ i\<close> almost surely, so the strict hypothesis of
  \<open>pcoord_stopped_bounded\<close> holds as soon as \<open>R\<close> exceeds it.\<close>

lemma exit_class_stopped_abs_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and R: "0 < R" and xR: "\<bar>x $ i\<bar> < R" and w: "0 \<le> w"
  shows "AE \<omega> in Q. \<bar>pcoord T i (min w (ploc T i R \<omega>)) \<omega>\<bar> \<le> R"
proof -
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  from st AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have s0: "fst (\<omega> 0) = x" and mem: "\<omega> \<in> space Q" by blast+
    have p0: "pcoord T i 0 \<omega> = x $ i"
      unfolding pcoord_def using T s0 by simp
    have c: "continuous_on {0..T} (\<lambda>s. pcoord T i s \<omega>)"
      unfolding pcoord_def
      by (rule continuous_on_subset
          [OF exit_class_coord_paths_cont[OF T setsQ mem]]) auto
    show ?case
      by (rule pcoord_stopped_bounded[OF T R _ c w]) (use p0 xR in simp)
  qed
qed

lemma exit_class_stopped_A_abs_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and w: "0 \<le> w"
  shows "AE \<omega> in Q. \<bar>snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i $ i\<bar>
      \<le> real CARD('n) * L * T"
proof -
  have yb: "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    by (rule exit_class_Y_bounded_ae[OF T L Q])
  from yb show ?thesis
  proof (rule eventually_mono)
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    have m: "min (min w (ploc T i R \<omega>)) T \<in> {0..T}"
      using w ploc_nonneg[OF T, of i R \<omega>] T by simp
    have "\<bar>snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i $ i\<bar>
        \<le> norm (snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i)"
      using Finite_Cartesian_Product.norm_nth_le
        [of "snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i" i] by simp
    also have "\<dots> \<le> norm (snd (\<omega> (min (min w (ploc T i R \<omega>)) T)))"
      by (rule Finite_Cartesian_Product.norm_nth_le)
    also have "\<dots> \<le> real CARD('n) * L * T" using h m by blast
    finally show "\<bar>snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i $ i\<bar>
        \<le> real CARD('n) * L * T" .
  qed
qed

subsection \<open>The conditional identity for the stopped pair\<close>

text \<open>\<open>E[(\<Delta>X\<^sup>\<tau>)\<^sup>2 | \<F>\<^sub>u] = E[\<Delta>A\<^sup>\<tau> | \<F>\<^sub>u]\<close>, the last hypothesis of
  \<open>Increment_Moments.fourth_moment_bound_bounded\<close> that is not immediate.
  It is the usual expansion --- the cross term is pulled out because
  \<open>X\<^sup>\<tau>\<^sub>u\<close> is \<open>\<F>\<^sub>u\<close>-measurable, and the compensated martingale converts
  \<open>E[(X\<^sup>\<tau>\<^sub>v)\<^sup>2 | \<F>\<^sub>u]\<close> into \<open>(X\<^sup>\<tau>\<^sub>u)\<^sup>2 - A\<^sup>\<tau>\<^sub>u + E[A\<^sup>\<tau>\<^sub>v | \<F>\<^sub>u]\<close>.  Every
  integrability side condition is free, because the stopped pair is
  bounded.\<close>

theorem exit_class_stopped_cond_exp:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and R: "0 < R" and xR: "\<bar>x $ i\<bar> < R"
    and uv: "0 \<le> u" "u \<le> v"
  shows "AE \<omega> in Q.
      cond_exp Q (natural_filtration Q 0 (\<lambda>w \<omega>. \<omega> w) u)
        (\<lambda>\<omega>. (pcoord T i (min v (ploc T i R \<omega>)) \<omega>
              - pcoord T i (min u (ploc T i R \<omega>)) \<omega>)\<^sup>2) \<omega>
      = cond_exp Q (natural_filtration Q 0 (\<lambda>w \<omega>. \<omega> w) u)
        (\<lambda>\<omega>. snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
              - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i) \<omega>"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>w \<omega> :: 'n pairpath. \<omega> w)"
  let ?X = "\<lambda>w \<omega> :: 'n pairpath. pcoord T i (min w (ploc T i R \<omega>)) \<omega>"
  let ?A = "\<lambda>w \<omega> :: 'n pairpath.
      snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i $ i"
  have T0: "0 \<le> T" using T by simp
  have v0: "0 \<le> v" using uv by simp
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  interpret MX: martingale Q ?F 0 ?X
    by (rule exit_class_stopped_coord_martingale[OF T L setsQ Q])
  have mgZ: "martingale Q ?F 0 (\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>)"
    using exit_class_stopped_comp_martingale[OF T L setsQ Q]
    unfolding pcoord_def by simp
  then interpret MZ: martingale Q ?F 0 "\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>" .
  interpret SFS: sigma_finite_subalgebra Q "?F u"
    by (rule MX.sigma_finite_subalgebra_F[OF uv(1)])
  \<comment> \<open>bounds and the integrability they buy\<close>
  have Xb: "AE \<omega> in Q. \<bar>?X w \<omega>\<bar> \<le> R" if w: "0 \<le> w" for w
    by (rule exit_class_stopped_abs_le[OF T0 setsQ Q R xR w])
  have Ab: "AE \<omega> in Q. \<bar>?A w \<omega>\<bar> \<le> real CARD('n) * L * T" if w: "0 \<le> w" for w
    by (rule exit_class_stopped_A_abs_le[OF T0 L Q w])
  have XQ: "?X w \<in> borel_measurable Q" if w: "0 \<le> w" for w
    by (rule borel_measurable_integrable[OF MX.integrable[OF w]])
  have AQ: "?A w \<in> borel_measurable Q" if w: "0 \<le> w" for w
  proof -
    have z: "(\<lambda>\<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>) \<in> borel_measurable Q"
      by (rule borel_measurable_integrable[OF MZ.integrable[OF w]])
    have "(\<lambda>\<omega>. (?X w \<omega>)\<^sup>2 - ((?X w \<omega>)\<^sup>2 - ?A w \<omega>)) \<in> borel_measurable Q"
      by (intro borel_measurable_diff borel_measurable_power XQ[OF w] z)
    then show ?thesis by simp
  qed
  have Ai: "integrable Q (?A w)" if w: "0 \<le> w" for w
  proof (rule finite_measure.integrable_const_bound
      [OF fmQ _ AQ[OF w], of "real CARD('n) * L * T"])
    show "AE \<omega> in Q. norm (?A w \<omega>) \<le> real CARD('n) * L * T"
      using Ab[OF w] by (rule eventually_mono) simp
  qed
  have prodb: "integrable Q (\<lambda>\<omega>. ?X a \<omega> * ?X b \<omega>)"
    if a: "0 \<le> a" and b: "0 \<le> b" for a b
  proof (rule finite_measure.integrable_const_bound[OF fmQ, of _ "R * R"])
    show "AE \<omega> in Q. norm (?X a \<omega> * ?X b \<omega>) \<le> R * R"
      using Xb[OF a] Xb[OF b]
    proof eventually_elim
      case (elim \<omega>)
      then show ?case
        using R by (simp add: abs_mult mult_mono)
    qed
    show "(\<lambda>\<omega>. ?X a \<omega> * ?X b \<omega>) \<in> borel_measurable Q"
      using XQ[OF a] XQ[OF b] by simp
  qed
  have Xsqi: "integrable Q (\<lambda>\<omega>. (?X w \<omega>)\<^sup>2)" if w: "0 \<le> w" for w
    using prodb[OF w w] by (simp add: power2_eq_square)
  \<comment> \<open>the cross term: pull out the \<open>\<F>\<^sub>u\<close>-measurable factor\<close>
  have Xum: "?X u \<in> borel_measurable (?F u)" by (rule MX.adapted[OF uv(1)])
  have cross: "AE \<omega> in Q.
      cond_exp Q (?F u) (\<lambda>\<omega>. ?X u \<omega> * ?X v \<omega>) \<omega> = (?X u \<omega>)\<^sup>2"
  proof -
    have "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. ?X u \<omega> * ?X v \<omega>) \<omega>
        = ?X u \<omega> * cond_exp Q (?F u) (?X v) \<omega>"
      by (rule SFS.cond_exp_measurable_mult(2)
          [OF prodb[OF uv(1) v0] MX.integrable[OF v0] Xum])
    moreover have "AE \<omega> in Q. ?X u \<omega> = cond_exp Q (?F u) (?X v) \<omega>"
      by (rule MX.martingale_property[OF uv])
    ultimately show ?thesis
      by eventually_elim (simp add: power2_eq_square)
  qed
  \<comment> \<open>the compensated martingale converts the square at \<open>v\<close>.\<close>
  have zsplit: "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2) \<omega>
      - cond_exp Q (?F u) (?A v) \<omega> = (?X u \<omega>)\<^sup>2 - ?A u \<omega>"
  proof -
    have "AE \<omega> in Q. (?X u \<omega>)\<^sup>2 - ?A u \<omega>
        = cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - ?A v \<omega>) \<omega>"
      by (rule MZ.martingale_property[OF uv])
    moreover have "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - ?A v \<omega>) \<omega>
        = cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2) \<omega> - cond_exp Q (?F u) (?A v) \<omega>"
      by (rule SFS.cond_exp_diff[OF Xsqi[OF v0] Ai[OF v0]])
    ultimately show ?thesis by eventually_elim simp
  qed
  \<comment> \<open>and the two terms that are already \<open>\<F>\<^sub>u\<close>-measurable.\<close>
  have Ameas: "AE \<omega> in Q. cond_exp Q (?F u) (?A u) \<omega> = ?A u \<omega>"
  proof -
    have "?A u \<in> borel_measurable (?F u)"
    proof -
      have z: "(\<lambda>\<omega>. (?X u \<omega>)\<^sup>2 - ?A u \<omega>) \<in> borel_measurable (?F u)"
        by (rule MZ.adapted[OF uv(1)])
      have "(\<lambda>\<omega>. (?X u \<omega>)\<^sup>2 - ((?X u \<omega>)\<^sup>2 - ?A u \<omega>))
          \<in> borel_measurable (?F u)"
        by (intro borel_measurable_diff borel_measurable_power Xum z)
      then show ?thesis by simp
    qed
    then show ?thesis by (rule SFS.cond_exp_F_meas[OF Ai[OF uv(1)]])
  qed
  have Xusq: "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. (?X u \<omega>)\<^sup>2) \<omega> = (?X u \<omega>)\<^sup>2"
    by (rule SFS.cond_exp_F_meas[OF Xsqi[OF uv(1)]])
      (use Xum in \<open>simp add: borel_measurable_power\<close>)
  \<comment> \<open>expand the square and assemble\<close>
  have expand: "(\<lambda>\<omega>. (?X v \<omega> - ?X u \<omega>)\<^sup>2)
      = (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - 2 * (?X u \<omega> * ?X v \<omega>) + (?X u \<omega>)\<^sup>2)"
    by (rule ext) (simp add: power2_diff mult.commute)
  have lhs: "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega> - ?X u \<omega>)\<^sup>2) \<omega>
      = cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2) \<omega>
        - 2 * (?X u \<omega>)\<^sup>2 + (?X u \<omega>)\<^sup>2"
  proof -
    have i1: "integrable Q (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - 2 * (?X u \<omega> * ?X v \<omega>))"
      by (intro Bochner_Integration.integrable_diff Xsqi[OF v0]
          integrable_mult_right prodb[OF uv(1) v0])
    have "AE \<omega> in Q. cond_exp Q (?F u)
        (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - 2 * (?X u \<omega> * ?X v \<omega>) + (?X u \<omega>)\<^sup>2) \<omega>
        = cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - 2 * (?X u \<omega> * ?X v \<omega>)) \<omega>
          + cond_exp Q (?F u) (\<lambda>\<omega>. (?X u \<omega>)\<^sup>2) \<omega>"
      by (rule SFS.cond_exp_add[OF i1 Xsqi[OF uv(1)]])
    moreover have "AE \<omega> in Q.
        cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2 - 2 * (?X u \<omega> * ?X v \<omega>)) \<omega>
        = cond_exp Q (?F u) (\<lambda>\<omega>. (?X v \<omega>)\<^sup>2) \<omega>
          - cond_exp Q (?F u) (\<lambda>\<omega>. 2 * (?X u \<omega> * ?X v \<omega>)) \<omega>"
      by (rule SFS.cond_exp_diff[OF Xsqi[OF v0]
            integrable_mult_right[OF prodb[OF uv(1) v0]]])
    moreover have "AE \<omega> in Q.
        cond_exp Q (?F u) (\<lambda>\<omega>. 2 * (?X u \<omega> * ?X v \<omega>)) \<omega>
        = 2 * cond_exp Q (?F u) (\<lambda>\<omega>. ?X u \<omega> * ?X v \<omega>) \<omega>"
      using SFS.cond_exp_scaleR_right
        [OF prodb[OF uv(1) v0], where c = 2] by simp
    ultimately show ?thesis using cross Xusq unfolding expand
      by eventually_elim simp
  qed
  have rhs: "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. ?A v \<omega> - ?A u \<omega>) \<omega>
      = cond_exp Q (?F u) (?A v) \<omega> - ?A u \<omega>"
  proof -
    have "AE \<omega> in Q. cond_exp Q (?F u) (\<lambda>\<omega>. ?A v \<omega> - ?A u \<omega>) \<omega>
        = cond_exp Q (?F u) (?A v) \<omega> - cond_exp Q (?F u) (?A u) \<omega>"
      by (rule SFS.cond_exp_diff[OF Ai[OF v0] Ai[OF uv(1)]])
    then show ?thesis using Ameas by eventually_elim simp
  qed
  from lhs zsplit rhs show ?thesis
    unfolding pcoord_def[symmetric] by eventually_elim simp
qed

subsection \<open>The bounded estimate at the stopped pair\<close>


theorem exit_class_stopped_fourth_moment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and R: "0 < R" and xR: "\<bar>x $ i\<bar> < R"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<omega>. (pcoord T i (min tt (ploc T i R \<omega>)) \<omega>
        - pcoord T i (min s (ploc T i R \<omega>)) \<omega>)^4 \<partial>Q)
      \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>w \<omega> :: 'n pairpath. \<omega> w)"
  let ?X = "\<lambda>w \<omega> :: 'n pairpath. pcoord T i (min w (ploc T i R \<omega>)) \<omega>"
  let ?A = "\<lambda>w \<omega> :: 'n pairpath.
      snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i $ i"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have mgX: "martingale Q ?F 0 ?X"
    by (rule exit_class_stopped_coord_martingale[OF T L setsQ Q])
  then interpret MX: martingale Q ?F 0 ?X .
  have mgZ: "martingale Q ?F 0 (\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>)"
    using exit_class_stopped_comp_martingale[OF T L setsQ Q]
    unfolding pcoord_def by simp
  then interpret MZ: martingale Q ?F 0 "\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>" .
  have Ab: "AE \<omega> in Q. \<bar>?A w \<omega>\<bar> \<le> real CARD('n) * L * T" if w: "0 \<le> w" for w
    by (rule exit_class_stopped_A_abs_le[OF T0 L Q w])
  have XQ: "?X w \<in> borel_measurable Q" if w: "0 \<le> w" for w
    by (rule borel_measurable_integrable[OF MX.integrable[OF w]])
  have AQ: "?A w \<in> borel_measurable Q" if w: "0 \<le> w" for w
  proof -
    have z: "(\<lambda>\<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>) \<in> borel_measurable Q"
      by (rule borel_measurable_integrable[OF MZ.integrable[OF w]])
    have "(\<lambda>\<omega>. (?X w \<omega>)\<^sup>2 - ((?X w \<omega>)\<^sup>2 - ?A w \<omega>)) \<in> borel_measurable Q"
      by (intro borel_measurable_diff borel_measurable_power XQ[OF w] z)
    then show ?thesis by simp
  qed
  have Ai: "integrable Q (?A w)" if w: "0 \<le> w" for w
  proof (rule finite_measure.integrable_const_bound
      [OF fmQ _ AQ[OF w], of "real CARD('n) * L * T"])
    show "AE \<omega> in Q. norm (?A w \<omega>) \<le> real CARD('n) * L * T"
      using Ab[OF w] by (rule eventually_mono) simp
  qed
  have cont: "AE \<omega> in Q. continuous_on {s..tt} (\<lambda>w. ?X w \<omega>)"
  proof (intro AE_I2)
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
    from pcoord_stopped_paths_cont[OF T0 setsQ this]
    show "continuous_on {s..tt} (\<lambda>w. ?X w \<omega>)"
      by (rule continuous_on_subset) (use st in auto)
  qed
  show ?thesis
  proof (rule fourth_moment_bound_bounded
      [OF prob mgX st stt Ai _ _ L _ _ cont])
    show "AE \<omega> in Q. \<forall>a b. 0 \<le> a \<longrightarrow> a \<le> b \<longrightarrow>
        0 \<le> ?A b \<omega> - ?A a \<omega> \<and> ?A b \<omega> - ?A a \<omega> \<le> L * (b - a)"
      by (rule exit_class_stopped_compensator_rate[OF T0 L Q])
    show "\<And>a b. 0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> AE \<omega> in Q.
        cond_exp Q (?F a) (\<lambda>\<omega>. (?X b \<omega> - ?X a \<omega>)\<^sup>2) \<omega>
          = cond_exp Q (?F a) (\<lambda>\<omega>. ?A b \<omega> - ?A a \<omega>) \<omega>"
      by (rule exit_class_stopped_cond_exp[OF T L setsQ Q R xR])
    show "0 \<le> R" using R by simp
    show "\<And>w. 0 \<le> w \<Longrightarrow> AE \<omega> in Q. \<bar>?X w \<omega>\<bar> \<le> R"
      by (rule exit_class_stopped_abs_le[OF T0 setsQ Q R xR])
  qed
qed

subsection \<open>Fatou removes the localization\<close>

text \<open>\<open>abs_diff_le_two\<close> lives in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>



theorem exit_class_fourth_moment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
      \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
proof -
  let ?RR = "\<lambda>m :: nat. \<bar>x $ i\<bar> + 1 + real m"
  let ?g = "\<lambda>m \<omega> :: 'n pairpath.
      (pcoord T i (min tt (ploc T i (?RR m) \<omega>)) \<omega>
        - pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>)^4"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule exit_class_prob[OF Q])
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have Rpos: "0 < ?RR m" for m by simp
  have Rgt: "\<bar>x $ i\<bar> < ?RR m" for m by simp
  have gint: "integrable Q (?g m)" for m
  proof -
    have mgX: "martingale Q (natural_filtration Q 0 (\<lambda>w \<omega>. \<omega> w)) 0
        (\<lambda>w \<omega>. pcoord T i (min w (ploc T i (?RR m) \<omega>)) \<omega>)"
      by (rule exit_class_stopped_coord_martingale[OF T L setsQ Q])
    then interpret MX: martingale Q "natural_filtration Q 0 (\<lambda>w \<omega>. \<omega> w)" 0
        "\<lambda>w \<omega>. pcoord T i (min w (ploc T i (?RR m) \<omega>)) \<omega>" .
    have tt0: "0 \<le> tt" using st stt by simp
    have m1: "(\<lambda>\<omega>. pcoord T i (min tt (ploc T i (?RR m) \<omega>)) \<omega>)
        \<in> borel_measurable Q"
      by (rule borel_measurable_integrable[OF MX.integrable[OF tt0]])
    have m2: "(\<lambda>\<omega>. pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>)
        \<in> borel_measurable Q"
      by (rule borel_measurable_integrable[OF MX.integrable[OF st]])
    have b1: "AE \<omega> in Q. \<bar>pcoord T i (min tt (ploc T i (?RR m) \<omega>)) \<omega>\<bar> \<le> ?RR m"
      by (rule exit_class_stopped_abs_le[OF T0 setsQ Q Rpos Rgt tt0])
    have b2: "AE \<omega> in Q. \<bar>pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>\<bar> \<le> ?RR m"
      by (rule exit_class_stopped_abs_le[OF T0 setsQ Q Rpos Rgt st])
    show ?thesis
    proof (rule finite_measure.integrable_const_bound
        [OF fmQ _ _, of _ "(2 * ?RR m)^4"])
      show "AE \<omega> in Q. norm (?g m \<omega>) \<le> (2 * ?RR m)^4"
        using b1 b2
      proof eventually_elim
        case (elim \<omega>)
        have le2: "\<bar>pcoord T i (min tt (ploc T i (?RR m) \<omega>)) \<omega>
              - pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>\<bar> \<le> 2 * ?RR m"
          using elim by (rule abs_diff_le_two)
        have "\<bar>pcoord T i (min tt (ploc T i (?RR m) \<omega>)) \<omega>
              - pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>\<bar>^4
            \<le> (2 * ?RR m)^4"
          by (rule power_mono[OF le2 abs_ge_zero])
        then show ?case by (simp add: power_abs)
      qed
      show "?g m \<in> borel_measurable Q" using m1 m2 by simp
    qed
  qed
  have gbound: "(\<integral>\<omega>. ?g m \<omega> \<partial>Q) \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2" for m
    by (rule exit_class_stopped_fourth_moment
        [OF T L setsQ Q Rpos Rgt st stt ttT])
  have gmeas: "(\<lambda>\<omega>. ennreal (?g m \<omega>)) \<in> borel_measurable Q" for m
    using borel_measurable_integrable[OF gint] by measurable
  have lim: "AE \<omega> in Q. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)
      = liminf (\<lambda>m. ennreal (?g m \<omega>))"
  proof (intro AE_I2)
    fix \<omega> :: "'n pairpath" assume mem: "\<omega> \<in> space Q"
    have c: "continuous_on {0..T} (\<lambda>r. pcoord T i r \<omega>)"
      unfolding pcoord_def
      by (rule continuous_on_subset
          [OF exit_class_coord_paths_cont[OF T0 setsQ mem]]) auto
    have "bounded ((\<lambda>r. pcoord T i r \<omega>) ` {0..T})"
      by (intro compact_imp_bounded compact_continuous_image c) simp
    then obtain B where B: "\<forall>r\<in>{0..T}. \<bar>pcoord T i r \<omega>\<bar> \<le> B"
      unfolding bounded_iff by auto
    obtain M0 :: nat where M0: "B - \<bar>x $ i\<bar> - 1 < real M0"
      using reals_Archimedean2 by blast
    have eq: "?g m \<omega> = (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4" if m: "M0 \<le> m" for m
    proof -
      have RB: "B < ?RR m" using M0 m by simp
      have "ploc T i (?RR m) \<omega> = T"
        by (rule ploc_eq_T_of_below) (use B RB in force)
      then show ?thesis
        unfolding pcoord_def using st stt ttT T0 by simp
    qed
    have ttd: "(\<lambda>m. ennreal (?g m \<omega>))
        \<longlonglongrightarrow> ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
      by (rule tendsto_eventually)
        (use eq in \<open>auto simp: eventually_sequentially\<close>)
    have "liminf (\<lambda>m. ennreal (?g m \<omega>))
        = ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
      by (rule lim_imp_Liminf[OF _ ttd]) simp
    then show "ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)
        = liminf (\<lambda>m. ennreal (?g m \<omega>))" by simp
  qed
  have bnd: "(\<integral>\<^sup>+\<omega>. ennreal (?g m \<omega>) \<partial>Q) \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
    for m
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (?g m \<omega>) \<partial>Q) = ennreal (\<integral>\<omega>. ?g m \<omega> \<partial>Q)"
      by (rule nn_integral_eq_integral[OF gint]) simp
    also have "\<dots> \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
      using gbound by (rule ennreal_leI)
    finally show ?thesis .
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
      = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>m. ennreal (?g m \<omega>)) \<partial>Q)"
    using lim by (rule nn_integral_cong_AE)
  also have "\<dots> \<le> liminf (\<lambda>m. \<integral>\<^sup>+\<omega>. ennreal (?g m \<omega>) \<partial>Q)"
    by (rule nn_integral_liminf[OF gmeas])
  also have "\<dots> \<le> limsup (\<lambda>m. \<integral>\<^sup>+\<omega>. ennreal (?g m \<omega>) \<partial>Q)"
    by (rule Liminf_le_Limsup) simp
  also have "\<dots> \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
    by (rule Limsup_bounded) (intro always_eventually allI bnd)
  finally show ?thesis .
qed

section \<open>The weak-limit machinery, parametric in a state functional\<close>

text \<open>The argument for the coordinate \<open>\<omega> \<mapsto> fst (\<omega> t) $ i\<close> also proves
  the compensated clause of (1.7) for
  \<open>\<omega> \<mapsto> (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ j\<close>: both are of the form
  \<open>\<omega> \<mapsto> F (\<omega> t)\<close> for a continuous \<open>F\<close> on the pair state, so this section
  redoes the chain once, parametric in \<open>F\<close>, and instantiates it twice.

  The hypotheses a caller must supply are exactly four: \<open>F\<close> continuous,
  the process \<open>\<lambda>u \<omega>. F (\<omega> (min u T))\<close> a martingale under every
  approximating law, a uniform \<open>L\<^sup>2\<close> bound on \<open>F (\<omega> u)\<close>, and the usual
  weak-convergence data.\<close>

subsection \<open>Continuity and measurability of the \<open>F\<close>-functionals\<close>

















lemma exit_class_fourth_moment_abs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4) \<partial>Q)
      \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4))"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have T0: "0 \<le> T" using T by simp
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  define d :: "'n pairpath \<Rightarrow> real"
    where "d = (\<lambda>\<omega>. (fst (\<omega> u) $ i - fst (\<omega> 0) $ i)^4)"
  define c :: real where "c = 8 * (x $ i)^4"
  have c0: "0 \<le> c" unfolding c_def using zero_le_fourth by simp
  have d0: "0 \<le> d \<omega>" for \<omega> unfolding d_def by (rule zero_le_fourth)
  have dm: "d \<in> borel_measurable Q"
    unfolding d_def
    by (intro borel_measurable_power borel_measurable_diff
        pair_law_coord_measurable[OF setsQ u] pair_law_coord_measurable[OF setsQ z])
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have ae: "AE \<omega> in Q. ennreal ((fst (\<omega> u) $ i)^4)
      \<le> ennreal (8 * d \<omega>) + ennreal c"
  proof (rule eventually_mono[OF st])
    fix \<omega> :: "'n pairpath"
    assume "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    then have zx: "fst (\<omega> 0) $ i = x $ i" by simp
    have "(fst (\<omega> u) $ i)^4
        = ((fst (\<omega> u) $ i - fst (\<omega> 0) $ i) + fst (\<omega> 0) $ i)^4" by simp
    also have "\<dots> \<le> 8 * ((fst (\<omega> u) $ i - fst (\<omega> 0) $ i)^4 + (fst (\<omega> 0) $ i)^4)"
      by (rule fourth_power_sum_bound)
    finally have "(fst (\<omega> u) $ i)^4 \<le> 8 * d \<omega> + c"
      using zx unfolding d_def c_def by (simp add: distrib_left)
    then have "ennreal ((fst (\<omega> u) $ i)^4) \<le> ennreal (8 * d \<omega> + c)"
      by (rule ennreal_leI)
    also have "\<dots> = ennreal (8 * d \<omega>) + ennreal c"
      by (rule ennreal_plus) (use c0 d0 in simp_all)
    finally show "ennreal ((fst (\<omega> u) $ i)^4)
        \<le> ennreal (8 * d \<omega>) + ennreal c" .
  qed
  have incr: "(\<integral>\<^sup>+\<omega>. ennreal (d \<omega>) \<partial>Q) \<le> ennreal (8 * L\<^sup>2 * T\<^sup>2)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (d \<omega>) \<partial>Q) \<le> ennreal (8 * L\<^sup>2 * (u - 0)\<^sup>2)"
      unfolding d_def
      by (rule exit_class_fourth_moment[OF T L setsQ Q order_refl])
        (use u in auto)
    also have "\<dots> \<le> ennreal (8 * L\<^sup>2 * T\<^sup>2)"
      using u by (intro ennreal_leI mult_left_mono power_mono) auto
    finally show ?thesis .
  qed
  have scal: "(\<integral>\<^sup>+\<omega>. ennreal (8 * d \<omega>) \<partial>Q) \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2))"
  proof -
    have e: "(\<lambda>\<omega>. ennreal (8 * d \<omega>)) = (\<lambda>\<omega>. 8 * ennreal (d \<omega>))"
      by (rule ext) (simp add: ennreal_mult d0)
    have "(\<integral>\<^sup>+\<omega>. ennreal (8 * d \<omega>) \<partial>Q) = 8 * (\<integral>\<^sup>+\<omega>. ennreal (d \<omega>) \<partial>Q)"
      unfolding e by (rule nn_integral_cmult) (use dm in measurable)
    also have "\<dots> \<le> 8 * ennreal (8 * L\<^sup>2 * T\<^sup>2)"
      using incr by (rule mult_left_mono) simp
    also have "\<dots> = ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2))"
      using L by (simp add: ennreal_mult ac_simps)
    finally show ?thesis .
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4) \<partial>Q)
      \<le> (\<integral>\<^sup>+\<omega>. ennreal (8 * d \<omega>) + ennreal c \<partial>Q)"
    by (rule nn_integral_mono_AE[OF ae])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (8 * d \<omega>) \<partial>Q) + (\<integral>\<^sup>+\<omega>. ennreal c \<partial>Q)"
    by (rule nn_integral_add) (use dm in measurable)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (8 * d \<omega>) \<partial>Q) + ennreal c"
    by (simp add: P.emeasure_space_1)
  also have "\<dots> \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2)) + ennreal c"
    using scal by (rule add_right_mono)
  also have "\<dots> = ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2) + c)"
    by (rule ennreal_plus[symmetric]) (use c0 L in simp_all)
  also have "\<dots> = ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4))"
    unfolding c_def by (simp add: distrib_left)
  finally show ?thesis .
qed

text \<open>The \<open>L\<^sup>2\<close> bound the generic chain asks for, at the compensated
  functional.  Pointwise \<open>(ab-c)\<^sup>2 \<le> a\<^sup>4 + b\<^sup>4 + 2c\<^sup>2\<close>: the two fourth
  moments come from the localization theorem, and \<open>c = Y\<^sub>i\<^sub>j\<close> is bounded
  outright because the covariation clause makes \<open>Y\<close> Lipschitz from \<open>0\<close>.
  The bound depends only on \<open>k, L, T, x\<close>, hence is uniform over the
  class.\<close>

lemma exit_class_comp_entry_sq_nn:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2) \<partial>Q)
      \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
               + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
               + 2 * (real CARD('n) * L * T)\<^sup>2)"
proof -
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have T0: "0 \<le> T" using T by simp
  have B0: "0 \<le> real CARD('n) * L * T" using L T0 by simp
  have m1: "(\<lambda>\<omega> :: 'n pairpath. ennreal ((fst (\<omega> u) $ i)^4))
      \<in> borel_measurable Q"
    using pair_law_coord_measurable[OF setsQ u, of i] by measurable
  have m2: "(\<lambda>\<omega> :: 'n pairpath. ennreal ((fst (\<omega> u) $ j)^4))
      \<in> borel_measurable Q"
    using pair_law_coord_measurable[OF setsQ u, of j] by measurable
  have m12: "(\<lambda>\<omega> :: 'n pairpath. ennreal ((fst (\<omega> u) $ i)^4)
        + ennreal ((fst (\<omega> u) $ j)^4)) \<in> borel_measurable Q"
    using m1 m2 by measurable
  have mc: "(\<lambda>\<omega> :: 'n pairpath. ennreal (2 * (real CARD('n) * L * T)\<^sup>2))
      \<in> borel_measurable Q"
    by simp
  have LT0: "0 \<le> 8 * L\<^sup>2 * T\<^sup>2" by (intro mult_nonneg_nonneg) auto
  have p0: "0 \<le> 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)"
    using LT0 zero_le_fourth[of "x $ i"] by simp
  have pj0: "0 \<le> 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)"
    using LT0 zero_le_fourth[of "x $ j"] by simp
  have Yb: "AE \<omega> in Q. norm (snd (\<omega> u) $ i $ j) \<le> real CARD('n) * L * T"
    by (rule exit_class_Y_entry_bound_ae[OF T0 L Q u])
  have ae: "AE \<omega> in Q. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)
      \<le> ennreal ((fst (\<omega> u) $ i)^4) + ennreal ((fst (\<omega> u) $ j)^4)
        + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)"
  proof (rule eventually_mono[OF Yb])
    fix \<omega> :: "'n pairpath"
    assume nb: "norm (snd (\<omega> u) $ i $ j) \<le> real CARD('n) * L * T"
    have c2: "(snd (\<omega> u) $ i $ j)\<^sup>2 \<le> (real CARD('n) * L * T)\<^sup>2"
    proof -
      have "(snd (\<omega> u) $ i $ j)\<^sup>2 = \<bar>snd (\<omega> u) $ i $ j\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (real CARD('n) * L * T)\<^sup>2"
        by (rule power_mono) (use nb in auto)
      finally show ?thesis .
    qed
    have "((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2
        = (fst (\<omega> u) $ i * fst (\<omega> u) $ j - snd (\<omega> u) $ i $ j)\<^sup>2"
      by (simp add: outerp_def)
    also have "\<dots> \<le> (fst (\<omega> u) $ i)^4 + (fst (\<omega> u) $ j)^4
        + 2 * (snd (\<omega> u) $ i $ j)\<^sup>2"
      by (rule prod_minus_sq_bound)
    also have "\<dots> \<le> (fst (\<omega> u) $ i)^4 + (fst (\<omega> u) $ j)^4
        + 2 * (real CARD('n) * L * T)\<^sup>2"
      using c2 by simp
    finally have le: "((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2
        \<le> (fst (\<omega> u) $ i)^4 + (fst (\<omega> u) $ j)^4
          + 2 * (real CARD('n) * L * T)\<^sup>2" .
    have "ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)
        \<le> ennreal ((fst (\<omega> u) $ i)^4 + (fst (\<omega> u) $ j)^4
            + 2 * (real CARD('n) * L * T)\<^sup>2)"
      using le by (rule ennreal_leI)
    also have "\<dots> = ennreal ((fst (\<omega> u) $ i)^4) + ennreal ((fst (\<omega> u) $ j)^4)
        + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)"
      by (simp add: zero_le_fourth)
    finally show "ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)
        \<le> ennreal ((fst (\<omega> u) $ i)^4) + ennreal ((fst (\<omega> u) $ j)^4)
          + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)" .
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2) \<partial>Q)
      \<le> (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4) + ennreal ((fst (\<omega> u) $ j)^4)
            + ennreal (2 * (real CARD('n) * L * T)\<^sup>2) \<partial>Q)"
    by (rule nn_integral_mono_AE[OF ae])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4)
                        + ennreal ((fst (\<omega> u) $ j)^4) \<partial>Q)
                 + (\<integral>\<^sup>+\<omega>. ennreal (2 * (real CARD('n) * L * T)\<^sup>2) \<partial>Q)"
    by (rule nn_integral_add[OF m12 mc])
  also have "\<dots> = ((\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4) \<partial>Q)
                  + (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ j)^4) \<partial>Q))
                 + (\<integral>\<^sup>+\<omega>. ennreal (2 * (real CARD('n) * L * T)\<^sup>2) \<partial>Q)"
    by (simp only: nn_integral_add[OF m1 m2])
  also have "\<dots> = ((\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4) \<partial>Q)
                  + (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ j)^4) \<partial>Q))
                 + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)"
    by (simp add: P.emeasure_space_1)
  also have "\<dots> \<le> (ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4))
                   + ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)))
                 + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)"
    by (intro add_mono order_refl exit_class_fourth_moment_abs[OF T L Q u])
  also have "\<dots> = ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
                         + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
                         + 2 * (real CARD('n) * L * T)\<^sup>2)"
  proof -
    \<comment> \<open>\<open>ennreal_plus\<close> is a DEFAULT simp rule in the SPLITTING direction, so
        neither it nor its symmetric form gets \<open>simp\<close> across this step
        (the latter loops); apply it as a rule, twice.\<close>
    have sum0: "0 \<le> 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
                  + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)"
      using p0 pj0 by simp
    have c30: "0 \<le> 2 * (real CARD('n) * L * T)\<^sup>2" by simp
    have "ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
                 + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
                 + 2 * (real CARD('n) * L * T)\<^sup>2)
        = ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
                 + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4))
          + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)"
      by (rule ennreal_plus[OF sum0 c30])
    also have "\<dots> = (ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4))
                    + ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)))
                   + ennreal (2 * (real CARD('n) * L * T)\<^sup>2)"
      by (simp only: ennreal_plus[OF p0 pj0])
    finally show ?thesis by (rule sym)
  qed
  finally show ?thesis .
qed

text \<open>\<open>mat_inner_axis\<close>, \<open>mat_Basis_cases\<close>, \<open>measurable_mat_entries\<close>,
  \<open>integrable_mat_entries\<close>, \<open>set_integral_mat_component\<close> and
  \<open>martingale_matI\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

subsection \<open>Lemma 2.3: the compensated clause, at the limit\<close>

theorem exit_class_comp_entry_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ i $ j)"
proof -
  let ?C = "8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
          + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
          + 2 * (real CARD('n) * L * T)\<^sup>2"
  have T0: "0 \<le> T" using T by simp
  have C0: "0 \<le> ?C"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg zero_le_fourth) auto
  show ?thesis
  proof (rule martingale_F_limit
      [where F = "\<lambda>p :: (real^'n) \<times> (real^'n^'n).
            (outerp (fst p) - snd p) $ i $ j"
         and C = "8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
                + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
                + 2 * (real CARD('n) * L * T)\<^sup>2"])
    show "0 \<le> T" by (rule T0)
    show "continuous_on UNIV
        (\<lambda>p :: (real^'n) \<times> (real^'n^'n). (outerp (fst p) - snd p) $ i $ j)"
      by (rule comp_entry_cont)
    show "prob_space (Qm m)" for m by (rule exit_class_prob[OF mem])
    show "sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)" for m
      by (rule exit_class_sets[OF mem])
    show "martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ i $ j)"
      for m
      by (rule martingale_mat_nth
          [OF exit_class_compensated_martingale[OF mem]])
    show "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))" by (rule wc)
    show "prob_space Q" by (rule prob)
    show "sets Q = sets (path_borel T :: ('n pairpath) measure)" by (rule setsQ)
    show "0 \<le> ?C" by (rule C0)
    show "(\<integral>\<^sup>+\<omega>. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)
            \<partial>(Qm m)) \<le> ennreal ?C" if "u \<in> {0..T}" for m u
      by (rule exit_class_comp_entry_sq_nn[OF T L mem that])
  qed
qed

corollary exit_class_comp_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
  by (rule martingale_matI)
    (rule exit_class_comp_entry_martingale_limit
      [OF T L mem wc prob setsQ])

section \<open>Lemma 2.3: the class is closed under weak limits\<close>

text \<open>All four clauses of (1.7) survive a weak limit, so the paper's
  class of pair laws is weakly closed; the compensated clause is the one
  that needed the uniform fourth moment.\<close>

theorem exit_class_weak_closed:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "Q \<in> exit_class k L T x"
proof -
  have T0: "0 \<le> T" using T by simp
  show ?thesis
    unfolding exit_class_def
  proof (intro CollectI conjI)
    show "prob_space Q" by (rule prob)
    show "sets Q = sets (path_borel T :: ('n pairpath) measure)" by (rule setsQ)
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule exit_class_limit_three_clauses(1)
          [OF T0 L mem wc prob setsQ])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule exit_class_limit_three_clauses(2)
          [OF T0 L mem wc prob setsQ])
    show "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
      by (rule exit_class_limit_three_clauses(3)
          [OF T0 L mem wc prob setsQ])
    show "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
      by (rule exit_class_comp_martingale_limit[OF T L mem wc prob setsQ])
  qed
qed


(*<*)
end
(*>*)
