section \<open>Lemma 2.3: the class is closed under weak limits\<close>

(*<*)
theory Exit_Class_Limits
  imports Exit_Class Exit_Time_Semicontinuity
    "Levy_Prokhorov_Metric.Space_of_Finite_Measures"
    "Semicontinuous_Analysis.Semicontinuous_Selection"
    "Continuous_Time_Martingales.Semidirect_Kernels"
    "Continuous_Time_Martingales.Martingale_Transfer"
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
    "Semicontinuous_Analysis.Semicontinuity"
    "Continuous_Path_Spaces.Path_Exit_Times"
begin

(*>*)

text \<open>
  The bridge from the market witnesses of this development to the
             class (1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close>, and the compactness theory of
             that class.

             By (1.7)-(1.8) the processes in \<open>P_x\<close> are never stopped: the
             covariation constraint holds for a.e. t >= 0, and \<open>tau_K\<close> is merely
             a functional of the path.  A \<open>stopped_market\<close> witness is therefore
             not a class member, its volatility vanishing after its stopping
             time.  The bridge continues the witness past the stopping time
             with an admissible volatility (\<open>Exit_Class\<close>.acont), the value being
             supplied by \<open>Exit_Class\<close>.\<open>mat_1_in_sconstraint\<close>, which is legitimate
             because the locale carries the paper's standing assumption L >= 1.

             This theory sits downstream of both \<open>Exit_Class\<close> and the market
             stack, so that neither has to import the other.\<close>
section \<open>Extracting the pointwise constraint from a market witness\<close>

text \<open>The locale's volatility hypotheses are stated as three separate
  almost-sure facts, each valid only up to the stopping time.  Combined
  and continued they give a single almost-sure statement holding for all
  times, which is the shape \<open>exit_class\<close> asks for.\<close>

text \<open>In particular the continued volatility of a market witness never
  leaves the constraint set, whereas the witness's own volatility does the
  moment it is stopped -- which is precisely the mismatch this theory
  exists to repair.\<close>

section \<open>Integrability of the continued volatility\<close>

text \<open>The continued volatility \<open>acov\<close> is integrable on bounded intervals.
  Boundedness follows on \<open>[0, tau \<omega>]\<close> from the locale's \<open>psd\<close> and
  \<open>eigen_ub L\<close> bounds via \<open>sconstraint_norm_le\<close>, and after \<open>tau \<omega>\<close> the
  continuation is the constant \<open>mat 1\<close>.  Measurability of \<open>acov\<close> in the
  time variable is the locale assumption \<open>acov_time_measurable\<close>, stated on
  the nonnegative axis --- faithful rather than a strengthening, since the
  paper's (1.7) constrains \<open>d\<langle>X\<^sub>i,X\<^sub>j\<rangle>(t)/dt\<close> and so presupposes the
  covariation density exists as a measurable object in \<open>t\<close>.
  \<open>Exit_Class.acont_set_borel_measurable\<close> transports this fact to the
  continuation, and \<open>set_borel_measurable_subset\<close> cuts it down to the
  interval at hand.\<close>

section \<open>The witness satisfies the class's covariation condition\<close>

text \<open>For a market witness, the continued running covariation
  \<open>Yint (acont \<dots>)\<close> has all its difference quotients in the constraint set
  almost surely, which is the covariation clause of \<open>exit_class\<close>
  with no stopping caveat, as (1.7) requires.  The witness's own
  covariation does not have this property
  (\<open>stopped_market_acov_leaves_sconstraint\<close>); the continuation repairs it
  at no cost by (1.8), since \<open>\<tau>\<^sub>K\<close> only sees the path up to the first exit
  from \<open>K\<close>.\<close>

corollary stopped_market_acov_leaves_sconstraint:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
    and s: "\<omega> \<in> space M" "tau \<omega> < s"
  shows "acov s \<omega> = 0"
  using SM s unfolding stopped_market_def by blast

section \<open>The martingale clauses of Lemma 2.3\<close>

text \<open>This section proves the martingale clauses of Lemma 2.3 for a weak
  limit of the paper's class, combining the class machinery of
  @{theory Relative_Arbitrage.Exit_Class} with the law machinery of @{theory Relative_Arbitrage.Exit_Time_Semicontinuity}
  (\<open>martingale_bounded_test\<close>, \<open>metric_measure_eqI_bounded_cts\<close>).

  Unlike the two closed path conditions of (1.7), which pass to a weak
  limit directly (\<open>Exit_Class.exit_class_start_limit\<close>,
  \<open>\<dots>_diffquot_limit\<close>), the martingale clauses are statements about
  integrals against past-measurable test functions, and only bounded
  continuous tests survive a weak limit.  The proof states the identity at
  a class member against a bounded continuous test, passes it through the
  weak limit using the uniform \<open>L\<^sup>2\<close> bound, upgrades from continuous tests
  to past events, and reassembles a martingale via the set-integral
  characterisation.

  The test function must be measurable for the natural filtration of the
  coordinate process, while it is naturally a function of the restricted
  path.  The two agree because \<open>\<sigma>(restriction) \<subseteq> \<F>\<^sub>s\<close>, which is exactly
  what \<open>Path_Space.pathify_measurable\<close> proves: the restriction map is the
  path map of the coordinate process on \<open>{0..s}\<close>, and that theorem reduces
  a ball of the path metric to countably many evaluation conditions.\<close>

subsection \<open>The restriction map is measurable for the natural filtration\<close>

lemma restrict_measurable_natural_filtration:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>\<omega>. restrict \<omega> {0..s})
      \<in> natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s
        \<rightarrow>\<^sub>M (path_borel s :: ('n pairpath) measure)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s"
  have spF: "space ?F = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_of_path_sets[OF setsQ])
  have evm: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> borel_measurable ?F"
    if u: "u \<in> {0..s}" for u
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use u in auto)
  have cont: "continuous_on {0..s} (\<lambda>u. \<omega> u)"
    if w: "\<omega> \<in> space ?F" for \<omega> :: "'n pairpath"
  proof -
    have "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w spF by simp
    from mspace_path_metricD[OF this] show ?thesis
      by (rule continuous_on_subset) (use sT s in auto)
  qed
  show ?thesis by (rule pathify_measurable[OF s evm cont])
qed

lemma past_test_measurable_natural_filtration:
  fixes Q :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and h: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}))
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  by (rule measurable_compose
      [OF restrict_measurable_natural_filtration[OF setsQ s sT] h])

subsection \<open>The identity at a class member, against a bounded test\<close>

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

theorem exit_class_martingale_test:
  fixes Q :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hm: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i) \<partial>Q) = 0"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)"
  \<comment> \<open>the class's martingale clause STOPS the process at \<open>T\<close> (it must ---
      see the note at \<open>exit_class\<close>), and on \<open>[0,T]\<close> the stopping is
      invisible, which is what the two \<open>min\<close> rewrites below record.\<close>
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ i"
  let ?Z = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s})"
  have sT: "s \<le> T" using ts tT by simp
  have t0: "0 \<le> t" using st ts by simp
  have mt: "min t T = t" using tT by simp
  have ms: "min s T = s" using sT by simp
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
  have MY: "martingale Q ?F 0 ?Y" by (rule exit_class_coord_martingale[OF Q])
  then interpret MY: martingale Q ?F 0 ?Y .
  have Zm: "?Z \<in> borel_measurable (?F s)"
    by (rule past_test_measurable_natural_filtration
        [OF exit_class_sets[OF Q] st sT hm])
  have ZM: "?Z \<in> borel_measurable Q"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st] Zm])
  have prod_int: "integrable Q (\<lambda>\<omega>. ?Z \<omega> * ?Y u \<omega>)" if u: "0 \<le> u" for u
  proof (rule Bochner_Integration.integrable_bound)
    show "integrable Q (\<lambda>\<omega>. \<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)"
      by (intro integrable_mult_right Bochner_Integration.integrable_abs
          MY.integrable[OF u])
    show "(\<lambda>\<omega>. ?Z \<omega> * ?Y u \<omega>) \<in> borel_measurable Q"
      using ZM borel_measurable_integrable[OF MY.integrable[OF u]]
      by measurable
    show "AE \<omega> in Q. norm (?Z \<omega> * ?Y u \<omega>) \<le> norm (\<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)"
    proof (intro AE_I2)
      fix \<omega> :: "'n pairpath"
      have "\<bar>?Z \<omega>\<bar> \<le> \<bar>B\<bar>" using hb[of "restrict \<omega> {0..s}"] by simp
      then have "\<bar>?Z \<omega> * ?Y u \<omega>\<bar> \<le> \<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>"
        by (simp add: abs_mult mult_right_mono)
      then show "norm (?Z \<omega> * ?Y u \<omega>) \<le> norm (\<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)" by simp
    qed
  qed
  have int_t: "integrable Q (\<lambda>\<omega>. ?Z \<omega> * ?Y t \<omega>)" by (rule prod_int[OF t0])
  have int_s: "integrable Q (\<lambda>\<omega>. ?Z \<omega> * ?Y s \<omega>)" by (rule prod_int[OF st])
  have eqts: "(\<integral>\<omega>. ?Z \<omega> * ?Y t \<omega> \<partial>Q) = (\<integral>\<omega>. ?Z \<omega> * ?Y s \<omega> \<partial>Q)"
    by (rule martingale_bounded_test[OF MY st ts Zm int_t int_s])
  have "(\<integral>\<omega>. ?Z \<omega> * (?Y t \<omega> - ?Y s \<omega>) \<partial>Q)
      = (\<integral>\<omega>. ?Z \<omega> * ?Y t \<omega> \<partial>Q) - (\<integral>\<omega>. ?Z \<omega> * ?Y s \<omega> \<partial>Q)"
    using Bochner_Integration.integral_diff[OF int_t int_s]
    by (simp add: right_diff_distrib)
  then show ?thesis using eqts mt ms by simp
qed

subsection \<open>The test functional is continuous on path space\<close>

text \<open>Unlike the confined market laws of @{theory Relative_Arbitrage.Exit_Time_Semicontinuity}, the paper's
  class admits no clamp: its processes are neither stopped nor bounded, so
  the test functional is continuous but unbounded, and the transfer runs
  through the uniform \<open>L\<^sup>2\<close> bound
  (\<open>Exit_Class.exit_class_sq_mean_le\<close>) rather than through
  boundedness.\<close>

lemma pair_eval_coord_cont:
  fixes t T :: real
  assumes t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      euclideanreal (\<lambda>\<omega>. fst (\<omega> t) $ i)"
proof -
  have ev: "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> t)"
    by (rule continuous_map_path_eval[OF t])
  have fstc: "continuous_map (euclidean :: ((real^'n) \<times> (real^'n^'n)) topology)
      euclidean fst"
    by (simp add: continuous_on_fst)
  have nthc: "continuous_map (euclidean :: (real^'n) topology) euclideanreal
      (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclideanreal (((\<lambda>v. v $ i) \<circ> fst) \<circ> (\<lambda>\<omega>. \<omega> t))"
    by (intro continuous_map_compose[OF ev] continuous_map_compose[OF fstc] nthc)
  then show ?thesis by (simp add: o_def)
qed

lemma pair_eval_coord_sq_cont:
  fixes t T :: real
  assumes t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      euclideanreal (\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)"
proof -
  have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclideanreal
      (\<lambda>\<omega>. fst (\<omega> t) $ i * fst (\<omega> t) $ i)"
    by (rule continuous_map_real_mult[OF pair_eval_coord_cont[OF t]
          pair_eval_coord_cont[OF t]])
  then show ?thesis by (simp add: power2_eq_square)
qed

lemma pair_test_functional_cont:
  fixes h :: "('n::finite pairpath) \<Rightarrow> real"
  assumes st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclideanreal
      (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))"
proof -
  let ?PT = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have part1: "continuous_map ?PT euclideanreal
      (\<lambda>\<omega>. fst (\<omega> t) $ i - fst (\<omega> s) $ i)"
    by (intro continuous_map_diff pair_eval_coord_cont tI sI)
  have rc: "continuous_map ?PT
      (mtopology_of (path_metric s :: ('n pairpath) metric))
      (\<lambda>\<omega>. restrict \<omega> {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have part2: "continuous_map ?PT euclideanreal (\<lambda>\<omega>. h (restrict \<omega> {0..s}))"
    using continuous_map_compose[OF rc hc] by (simp add: o_def)
  show ?thesis by (rule continuous_map_real_mult[OF part2 part1])
qed

subsection \<open>Integrability from the \<open>L\<^sup>2\<close> bound, for members and for limits\<close>

text \<open>\<open>integrable_of_sq_integrable\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


lemma pair_law_coord_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. fst (\<omega> u) $ i) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) $ i)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_coord_cont[OF u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_coord_sq_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> u) $ i)\<^sup>2)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_coord_sq_cont[OF u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_sq_integrable_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
    and bnd: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2)"
proof -
  have m: "(\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2) \<in> borel_measurable N"
    by (rule pair_law_coord_sq_measurable[OF setsN u])
  have lt: "(\<integral>\<^sup>+\<omega>. ennreal (norm ((fst (\<omega> u) $ i)\<^sup>2)) \<partial>N) < \<infinity>"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (norm ((fst (\<omega> u) $ i)\<^sup>2)) \<partial>N) \<le> ennreal C"
      using bnd by simp
    also have "ennreal C < \<infinity>" by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding integrable_iff_bounded using m lt by blast
qed

lemma pair_law_coord_sq_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
    and int: "integrable N (\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2)"
    and le: "(\<integral>\<omega>. (fst (\<omega> u) $ i)\<^sup>2 \<partial>N) \<le> C"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
proof -
  have "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N)
      = ennreal (\<integral>\<omega>. (fst (\<omega> u) $ i)\<^sup>2 \<partial>N)"
    by (rule nn_integral_eq_integral[OF int]) simp
  also have "\<dots> \<le> ennreal C" using le by (rule ennreal_leI)
  finally show ?thesis .
qed

subsection \<open>Generic integrability side conditions of the transfer theorem\<close>

text \<open>\<open>bounded_measurable_integrable\<close>, \<open>clamp_integrable\<close>, \<open>tail_indicator_measurable\<close>, \<open>tail_integrable\<close> live in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


subsection \<open>The test functional under a pair law with an \<open>L\<^sup>2\<close> bound\<close>

lemma pair_law_sq_mean_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
  assumes int: "integrable N (\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2)" and C0: "0 \<le> C"
    and bnd: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "(\<integral>\<omega>. (fst (\<omega> u) $ i)\<^sup>2 \<partial>N) \<le> C"
proof -
  have "ennreal (\<integral>\<omega>. (fst (\<omega> u) $ i)\<^sup>2 \<partial>N)
      = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>N)"
    by (rule nn_integral_eq_integral[OF int, symmetric]) simp
  also have "\<dots> \<le> ennreal C" by (rule bnd)
  finally show ?thesis using C0 by simp
qed

lemma pair_test_measurable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))
      \<in> borel_measurable N"
proof -
  have sT: "s \<le> T" using ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have "(\<lambda>\<omega> :: 'n pairpath.
        h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable
      [OF pair_test_functional_cont[OF st sT tI hc, of i]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_test_sq_bound:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> s) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> t) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. (h (restrict \<omega> {0..s})
        * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))\<^sup>2)"
    and "(\<integral>\<omega>. (h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))\<^sup>2 \<partial>N)
        \<le> 4 * B\<^sup>2 * C"
proof -
  let ?f = "\<lambda>\<omega> :: 'n pairpath.
      h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i)"
  let ?D = "\<lambda>\<omega> :: 'n pairpath.
      2 * B\<^sup>2 * ((fst (\<omega> t) $ i)\<^sup>2 + (fst (\<omega> s) $ i)\<^sup>2)"
  have sI: "s \<in> {0..T}" using st ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have B0: "0 \<le> B" by (rule order_trans[OF abs_ge_zero hb])
  have iss: "integrable N (\<lambda>\<omega>. (fst (\<omega> s) $ i)\<^sup>2)"
    by (rule pair_law_sq_integrable_of_nn_bound[OF setsN sI Cs])
  have itt: "integrable N (\<lambda>\<omega>. (fst (\<omega> t) $ i)\<^sup>2)"
    by (rule pair_law_sq_integrable_of_nn_bound[OF setsN tI Ct])
  have fm: "?f \<in> borel_measurable N"
    by (rule pair_test_measurable[OF setsN st ts tT hc])
  have fsqm: "(\<lambda>\<omega>. (?f \<omega>)\<^sup>2) \<in> borel_measurable N" using fm by measurable
  have dom_int: "integrable N ?D"
    by (intro integrable_mult_right Bochner_Integration.integrable_add itt iss)
  \<comment> \<open>pointwise: the test factor contributes at most \<open>B\<^sup>2\<close>, and the squared
      increment at most twice the sum of the two squared coordinates.\<close>
  have ptwise: "(?f \<omega>)\<^sup>2 \<le> ?D \<omega>" for \<omega>
  proof -
    have hsq: "(h (restrict \<omega> {0..s}))\<^sup>2 \<le> B\<^sup>2"
    proof -
      have "\<bar>h (restrict \<omega> {0..s})\<bar>\<^sup>2 \<le> B\<^sup>2"
        by (rule power_mono[OF hb abs_ge_zero])
      then show ?thesis by simp
    qed
    \<comment> \<open>\<open>2(a²+b²) - (a-b)² = (a+b)² \<ge> 0\<close>: stated as an EQUATION between
        squares so that \<open>linarith\<close> sees only linear atoms.\<close>
    have e1: "2 * ((fst (\<omega> t) $ i)\<^sup>2 + (fst (\<omega> s) $ i)\<^sup>2)
          - (fst (\<omega> t) $ i - fst (\<omega> s) $ i)\<^sup>2
        = (fst (\<omega> t) $ i + fst (\<omega> s) $ i)\<^sup>2"
      by (simp add: power2_diff power2_sum)
    have sq_le: "(fst (\<omega> t) $ i - fst (\<omega> s) $ i)\<^sup>2
        \<le> 2 * ((fst (\<omega> t) $ i)\<^sup>2 + (fst (\<omega> s) $ i)\<^sup>2)"
      using e1 zero_le_power2[of "fst (\<omega> t) $ i + fst (\<omega> s) $ i"] by linarith
    have "(?f \<omega>)\<^sup>2 = (h (restrict \<omega> {0..s}))\<^sup>2
        * (fst (\<omega> t) $ i - fst (\<omega> s) $ i)\<^sup>2"
      by (simp add: power_mult_distrib)
    also have "\<dots> \<le> B\<^sup>2 * (fst (\<omega> t) $ i - fst (\<omega> s) $ i)\<^sup>2"
      by (rule mult_right_mono[OF hsq zero_le_power2])
    also have "\<dots> \<le> B\<^sup>2 * (2 * ((fst (\<omega> t) $ i)\<^sup>2 + (fst (\<omega> s) $ i)\<^sup>2))"
      by (rule mult_left_mono[OF sq_le zero_le_power2])
    also have "\<dots> = ?D \<omega>" by simp
    finally show ?thesis .
  qed
  show fsq_int: "integrable N (\<lambda>\<omega>. (?f \<omega>)\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound[OF dom_int fsqm])
    show "AE \<omega> in N. norm ((?f \<omega>)\<^sup>2) \<le> norm (?D \<omega>)"
    proof (intro AE_I2)
      fix \<omega> :: "'n pairpath"
      have "0 \<le> ?D \<omega>" by simp
      then show "norm ((?f \<omega>)\<^sup>2) \<le> norm (?D \<omega>)" using ptwise[of \<omega>] by simp
    qed
  qed
  have Bs: "(\<integral>\<omega>. (fst (\<omega> s) $ i)\<^sup>2 \<partial>N) \<le> C"
    by (rule pair_law_sq_mean_of_nn_bound[OF iss C0 Cs])
  have Bt: "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>N) \<le> C"
    by (rule pair_law_sq_mean_of_nn_bound[OF itt C0 Ct])
  have "(\<integral>\<omega>. (?f \<omega>)\<^sup>2 \<partial>N) \<le> (\<integral>\<omega>. ?D \<omega> \<partial>N)"
    by (rule integral_mono[OF fsq_int dom_int]) (rule ptwise)
  also have "(\<integral>\<omega>. ?D \<omega> \<partial>N)
      = 2 * B\<^sup>2 * ((\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>N) + (\<integral>\<omega>. (fst (\<omega> s) $ i)\<^sup>2 \<partial>N))"
    by (simp add: Bochner_Integration.integral_add[OF itt iss])
  also have "\<dots> \<le> 2 * B\<^sup>2 * (2 * C)"
    by (rule mult_left_mono) (use Bs Bt zero_le_power2 in auto)
  also have "\<dots> = 4 * B\<^sup>2 * C" by simp
  finally show "(\<integral>\<omega>. (?f \<omega>)\<^sup>2 \<partial>N) \<le> 4 * B\<^sup>2 * C" .
qed

lemma pair_test_integrable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> s) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> t) $ i)\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N
      (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))"
proof -
  have fm: "finite_measure N" using P by (simp add: prob_space_def)
  show ?thesis
    by (rule integrable_of_sq_integrable[OF fm
          pair_test_measurable[OF setsN st ts tT hc]
          pair_test_sq_bound(1)[OF P setsN st ts tT hc hb C0 Cs Ct]])
qed

subsection \<open>The second moment bound of the class, in nn-integral form\<close>

lemma exit_class_sq_nn_bound:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x" and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q)
      \<le> ennreal ((x $ i)\<^sup>2 + real CARD('n) * L * T)"
  by (rule pair_law_coord_sq_nn_bound[OF exit_class_sets[OF Q] u
        exit_class_sq_integrable[OF T L Q u]
        exit_class_sq_mean_le[OF T L Q u]])

lemma pair_law_limit_sq_nn_bound:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes wc: "weak_conv_on Qm Q sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and u: "u \<in> {0..T}" and C0: "0 \<le> C"
    and bnd: "\<And>m. (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q) \<le> ennreal C"
  by (rule weak_conv_on_nn_integral_le
      [OF wc pair_eval_coord_sq_cont[OF u] _ C0 bnd]) simp

subsection \<open>The martingale identity passes to the weak limit\<close>

theorem exit_class_martingale_test_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i) \<partial>Q) = 0"
proof -
  let ?f = "\<lambda>\<omega> :: 'n pairpath.
      h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i)"
  let ?C = "(x $ i)\<^sup>2 + real CARD('n) * L * T"
  have sT: "s \<le> T" using ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have C0: "0 \<le> ?C" using L T by simp
  have B0: "0 \<le> B" by (rule order_trans[OF abs_ge_zero hb])
  have Pm: "prob_space (Qm m)" for m by (rule exit_class_prob[OF mem])
  have fmm: "finite_measure (Qm m)" for m
    using Pm by (simp add: prob_space_def)
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have setsm: "sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)" for m
    by (rule exit_class_sets[OF mem])
  have nnm: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>(Qm m)) \<le> ennreal ?C"
    if u: "u \<in> {0..T}" for u m
    by (rule exit_class_sq_nn_bound[OF T L mem u])
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q) \<le> ennreal ?C"
    if u: "u \<in> {0..T}" for u
    by (rule pair_law_limit_sq_nn_bound[OF wc u C0 nnm[OF u]])
  have intm: "integrable (Qm m) ?f" for m
    by (rule pair_test_integrable[OF Pm setsm st ts tT hc hb C0
          nnm[OF sI] nnm[OF tI]])
  have intQ: "integrable Q ?f"
    by (rule pair_test_integrable[OF prob setsQ st ts tT hc hb C0
          nnQ[OF sI] nnQ[OF tI]])
  have lim: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> (\<integral>\<omega>. ?f \<omega> \<partial>Q)"
  proof (rule weak_conv_integral_of_L2_bound)
    show "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))" by (rule wc)
    show "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
        euclideanreal ?f"
      by (rule pair_test_functional_cont[OF st sT tI hc])
    show "\<And>m. finite_measure (Qm m)" by (rule fmm)
    show "finite_measure Q" by (rule fmQ)
    show "\<And>m. integrable (Qm m) ?f" by (rule intm)
    show "integrable Q ?f" by (rule intQ)
    show "\<And>m R. integrable (Qm m) (\<lambda>w. max (- R) (min R (?f w)))"
      by (rule clamp_integrable[OF fmm borel_measurable_integrable[OF intm]])
    show "\<And>R. integrable Q (\<lambda>w. max (- R) (min R (?f w)))"
      by (rule clamp_integrable[OF fmQ borel_measurable_integrable[OF intQ]])
    show "\<And>m R. integrable (Qm m)
        (\<lambda>w. \<bar>?f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (?f w))"
      by (rule tail_integrable[OF intm])
    show "\<And>R. integrable Q (\<lambda>w. \<bar>?f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (?f w))"
      by (rule tail_integrable[OF intQ])
    show "0 \<le> 4 * B\<^sup>2 * ?C" using C0 by simp
    show "\<And>m. (\<integral>w. (?f w)\<^sup>2 \<partial>(Qm m)) \<le> 4 * B\<^sup>2 * ?C"
      by (rule pair_test_sq_bound(2)[OF Pm setsm st ts tT hc hb C0
            nnm[OF sI] nnm[OF tI]])
    show "(\<integral>w. (?f w)\<^sup>2 \<partial>Q) \<le> 4 * B\<^sup>2 * ?C"
      by (rule pair_test_sq_bound(2)[OF prob setsQ st ts tT hc hb C0
            nnQ[OF sI] nnQ[OF tI]])
    show "\<And>m. integrable (Qm m) (\<lambda>w. (?f w)\<^sup>2)"
      by (rule pair_test_sq_bound(1)[OF Pm setsm st ts tT hc hb C0
            nnm[OF sI] nnm[OF tI]])
    show "integrable Q (\<lambda>w. (?f w)\<^sup>2)"
      by (rule pair_test_sq_bound(1)[OF prob setsQ st ts tT hc hb C0
            nnQ[OF sI] nnQ[OF tI]])
  qed
  have hm: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
    using continuous_map_measurable[OF hc] by (simp add: borel_of_euclidean)
  have zero: "(\<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) = 0" for m
    by (rule exit_class_martingale_test[OF mem st ts tT hm hb])
  have z: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> 0" using zero by simp
  show ?thesis by (rule tendsto_unique[OF _ lim z]) simp
qed

subsection \<open>From continuous tests to past events\<close>

text \<open>The monotone-class step splits the increment into positive and
  negative parts, pushes each forward through the restriction map as a
  density, and uses that the limit identity says the two image measures
  integrate every bounded continuous function alike.
  \<open>Exit_Time_Semicontinuity.metric_measure_eqI_bounded_cts\<close> then makes the two
  measures equal, so they agree on every past event.

  That engine supplies tests bounded only on the topspace, whereas
  \<open>exit_class_martingale_test_limit\<close> asks for a global bound;
  composing with \<open>rclamp\<close> repairs it, since the clamp is invisible where
  the bound already holds.\<close>

lemma restrict_in_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "0 \<le> s" and sT: "s \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "restrict \<omega> {0..s} \<in> mspace (path_metric s :: ('n pairpath) metric)"
proof -
  have "(\<lambda>f :: 'n pairpath. restrict f {0..s})
      \<in> mspace (path_metric T :: ('n pairpath) metric)
        \<rightarrow> mspace (path_metric s :: ('n pairpath) metric)"
    using Lipschitz_restrict_path_metric[OF st sT]
    unfolding Lipschitz_continuous_map_def by blast
  then show ?thesis using w by blast
qed

lemma exit_class_limit_sq_nn:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q)
      \<le> ennreal ((x $ i)\<^sup>2 + real CARD('n) * L * T)"
proof -
  have C0: "0 \<le> (x $ i)\<^sup>2 + real CARD('n) * L * T" using L T by simp
  show ?thesis
    by (rule pair_law_limit_sq_nn_bound[OF wc u C0
          exit_class_sq_nn_bound[OF T L mem u]])
qed

lemma exit_class_limit_increment_integrable:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) $ i - fst (\<omega> s) $ i)"
proof -
  have sT: "s \<le> T" using ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have C0: "0 \<le> (x $ i)\<^sup>2 + real CARD('n) * L * T" using L T by simp
  have onec: "continuous_map
      (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal
      (\<lambda>_. 1 :: real)" by simp
  have one_b: "\<And>g :: 'n pairpath. \<bar>(\<lambda>_. 1 :: real) g\<bar> \<le> 1" by simp
  have "integrable Q (\<lambda>\<omega>. (\<lambda>_. 1 :: real) (restrict \<omega> {0..s})
      * (fst (\<omega> t) $ i - fst (\<omega> s) $ i))"
    by (rule pair_test_integrable[OF prob setsQ st ts tT onec one_b C0
          exit_class_limit_sq_nn[OF T L mem wc sI]
          exit_class_limit_sq_nn[OF T L mem wc tI]])
  then show ?thesis by simp
qed

theorem exit_class_martingale_event_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and Bs: "Bs \<in> sets (path_borel s :: ('n pairpath) measure)"
  shows "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..s})
      * (fst (\<omega> t) $ i - fst (\<omega> s) $ i) \<partial>Q) = 0"
proof -
  let ?PT = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?PS = "mtopology_of (path_metric s :: ('n pairpath) metric)"
  let ?g = "\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t) $ i - fst (\<omega> s) $ i"
  let ?p = "\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}"
  have sT: "s \<le> T" using ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have gint: "integrable Q ?g"
    by (rule exit_class_limit_increment_integrable
        [OF T L mem wc prob setsQ st ts tT])
  have gmeasQ: "?g \<in> borel_measurable Q"
    by (rule borel_measurable_integrable[OF gint])
  have rc: "continuous_map ?PT ?PS ?p"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pim: "?p \<in> borel_of ?PT \<rightarrow>\<^sub>M borel_of ?PS"
    by (rule continuous_map_measurable[OF rc])
  have pimQ: "?p \<in> Q \<rightarrow>\<^sub>M borel_of ?PS"
    using pim measurable_cong_sets[OF setsQ refl] by blast
  define gp where "gp = (\<lambda>\<omega> :: 'n pairpath. max (?g \<omega>) 0)"
  define gm where "gm = (\<lambda>\<omega> :: 'n pairpath. max (- ?g \<omega>) 0)"
  have gp0: "\<And>\<omega>. 0 \<le> gp \<omega>" and gm0: "\<And>\<omega>. 0 \<le> gm \<omega>"
    unfolding gp_def gm_def by simp_all
  have gdiff: "gp \<omega> - gm \<omega> = ?g \<omega>" for \<omega>
    unfolding gp_def gm_def by (simp add: max_def)
  have gpm: "gp \<in> borel_measurable Q" and gmm: "gm \<in> borel_measurable Q"
    unfolding gp_def gm_def
    by (intro borel_measurable_max gmeasQ borel_measurable_const
        borel_measurable_uminus)+
  have gpi: "integrable Q gp" and gmi: "integrable Q gm"
    unfolding gp_def gm_def
    by (rule Bochner_Integration.integrable_max
        [OF gint Bochner_Integration.integrable_zero],
        rule Bochner_Integration.integrable_max
        [OF Bochner_Integration.integrable_minus[OF gint]
            Bochner_Integration.integrable_zero])
  define N1 where "N1 = distr (density Q (\<lambda>\<omega>. ennreal (gp \<omega>))) (borel_of ?PS) ?p"
  define N2 where "N2 = distr (density Q (\<lambda>\<omega>. ennreal (gm \<omega>))) (borel_of ?PS) ?p"
  have sN1: "sets N1 = sets (borel_of ?PS)"
    and sN2: "sets N2 = sets (borel_of ?PS)"
    unfolding N1_def N2_def by simp_all
  have pdm: "?p \<in> density Q (\<lambda>\<omega>. ennreal (w \<omega>)) \<rightarrow>\<^sub>M borel_of ?PS" for w
    using pimQ measurable_cong_sets[OF sets_density refl] by blast
  have push: "(\<integral>y. u y \<partial>(distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>)))
        (borel_of ?PS) ?p)) = (\<integral>\<omega>. u (?p \<omega>) * w \<omega> \<partial>Q)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and wm: "w \<in> borel_measurable Q" and w0: "\<And>\<omega>. 0 \<le> w \<omega>" for u w
  proof -
    have cmp: "(\<lambda>\<omega>. u (?p \<omega>)) \<in> borel_measurable Q"
      using measurable_comp[OF pimQ um] by (simp add: o_def)
    have "(\<integral>y. u y \<partial>(distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>))) (borel_of ?PS) ?p))
        = (\<integral>\<omega>. u (?p \<omega>) \<partial>(density Q (\<lambda>\<omega>. ennreal (w \<omega>))))"
      by (rule Bochner_Integration.integral_distr[OF pdm um])
    also have "\<dots> = (\<integral>\<omega>. u (?p \<omega>) * w \<omega> \<partial>Q)"
      by (subst integral_density)
        (use cmp wm w0 in \<open>auto simp: mult.commute\<close>)
    finally show ?thesis .
  qed
  have finw: "finite_measure (distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>)))
      (borel_of ?PS) ?p)"
    if wm: "w \<in> borel_measurable Q" and w0: "\<And>\<omega>. 0 \<le> w \<omega>"
    and wi: "integrable Q w" for w
  proof (rule finite_measureI)
    let ?D = "density Q (\<lambda>\<omega>. ennreal (w \<omega>))"
    have sp: "space (distr ?D (borel_of ?PS) ?p) = space (borel_of ?PS)" by simp
    have pre: "?p -` space (borel_of ?PS) \<inter> space ?D = space Q"
      using measurable_space[OF pdm[of w]] by auto
    have "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p))
        = emeasure ?D (?p -` space (borel_of ?PS) \<inter> space ?D)"
      unfolding sp by (intro emeasure_distr pdm) (metis sets.top space_borel_of)
    also have "\<dots> = emeasure ?D (space Q)" unfolding pre ..
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (w \<omega>) * indicator (space Q) \<omega> \<partial>Q)"
      by (intro emeasure_density measurable_compose[OF wm measurable_ennreal]) auto
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (w \<omega>) \<partial>Q)"
      by (intro nn_integral_cong) (simp add: indicator_def)
    also have "\<dots> = ennreal (\<integral>\<omega>. w \<omega> \<partial>Q)"
      by (rule nn_integral_eq_integral[OF wi]) (use w0 in simp)
    also have "\<dots> < \<infinity>" by simp
    finally show "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p)) \<noteq> \<infinity>" by simp
  qed
  have finN1: "finite_measure N1" unfolding N1_def by (rule finw[OF gpm gp0 gpi])
  have finN2: "finite_measure N2" unfolding N2_def by (rule finw[OF gmm gm0 gmi])
  have NEQ: "N1 = N2"
  proof (rule metric_measure_eqI_bounded_cts[OF sN1 sN2 finN1 finN2])
    fix u :: "'n pairpath \<Rightarrow> real"
    assume uc: "continuous_map ?PS euclideanreal u"
    assume ub: "\<exists>B. \<forall>y\<in>topspace ?PS. \<bar>u y\<bar> \<le> B"
    then obtain B where B: "\<And>y. y \<in> topspace ?PS \<Longrightarrow> \<bar>u y\<bar> \<le> B" by blast
    define B' where "B' = max B 0"
    have B'0: "0 \<le> B'" unfolding B'_def by simp
    let ?u = "\<lambda>y. rclamp B' (u y)"
    have ucl: "continuous_map ?PS euclideanreal ?u"
      using continuous_map_compose[OF uc rclamp_cont] by (simp add: o_def)
    have ubd: "\<And>y. \<bar>?u y\<bar> \<le> B'" by (rule rclamp_bound[OF B'0])
    have uagree: "?u y = u y" if y: "y \<in> mspace (path_metric s :: ('n pairpath) metric)"
      for y
    proof (rule rclamp_id)
      have "\<bar>u y\<bar> \<le> B" using B y by simp
      then show "\<bar>u y\<bar> \<le> B'" unfolding B'_def by simp
    qed
    have um: "u \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF uc] by (simp add: borel_of_euclidean)
    have ucm: "?u \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF ucl] by (simp add: borel_of_euclidean)
    have same: "(\<integral>y. u y \<partial>Nj) = (\<integral>y. ?u y \<partial>Nj)"
      if sj: "sets Nj = sets (borel_of ?PS)" for Nj
    proof (rule integral_cong_AE)
      show "u \<in> borel_measurable Nj"
        using um measurable_cong_sets[OF sj refl] by blast
      show "?u \<in> borel_measurable Nj"
        using ucm measurable_cong_sets[OF sj refl] by blast
      have "space Nj = mspace (path_metric s :: ('n pairpath) metric)"
        using sets_eq_imp_space_eq[OF sj] by (simp add: space_borel_of)
      then show "AE y in Nj. u y = ?u y"
        by (intro AE_I2) (simp add: uagree)
    qed
    have zero: "(\<integral>\<omega>. ?u (?p \<omega>) * ?g \<omega> \<partial>Q) = 0"
      by (rule exit_class_martingale_test_limit
          [OF T L mem wc prob setsQ st ts tT ucl ubd])
    have i1: "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega>)"
      and i2: "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
    proof -
      have cmp: "(\<lambda>\<omega>. ?u (?p \<omega>)) \<in> borel_measurable Q"
        using measurable_comp[OF pimQ ucm] by (simp add: o_def)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gpi, of B'] _ ])
          (use cmp gpm ubd gp0 B'0 in
            \<open>auto intro!: borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gmi, of B'] _ ])
          (use cmp gmm ubd gm0 B'0 in
            \<open>auto intro!: borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
    qed
    have "(\<integral>y. ?u y \<partial>N1) - (\<integral>y. ?u y \<partial>N2)
        = (\<integral>\<omega>. ?u (?p \<omega>) * gp \<omega> \<partial>Q) - (\<integral>\<omega>. ?u (?p \<omega>) * gm \<omega> \<partial>Q)"
      unfolding N1_def N2_def
      by (simp add: push[OF ucm gpm gp0] push[OF ucm gmm gm0])
    also have "\<dots> = (\<integral>\<omega>. ?u (?p \<omega>) * gp \<omega> - ?u (?p \<omega>) * gm \<omega> \<partial>Q)"
      by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
    also have "\<dots> = (\<integral>\<omega>. ?u (?p \<omega>) * ?g \<omega> \<partial>Q)"
    proof -
      have fe: "(\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega> - ?u (?p \<omega>) * gm \<omega>)
          = (\<lambda>\<omega>. ?u (?p \<omega>) * ?g \<omega>)"
        by (rule ext) (simp add: gdiff[symmetric] right_diff_distrib)
      show ?thesis by (simp only: fe)
    qed
    also have "\<dots> = 0" by (rule zero)
    finally have "(\<integral>y. ?u y \<partial>N1) = (\<integral>y. ?u y \<partial>N2)" by simp
    then show "(\<integral>y. u y \<partial>N1) = (\<integral>y. u y \<partial>N2)"
      using same[OF sN1] same[OF sN2] by simp
  qed
  \<comment> \<open>the two measures agree, so they integrate the indicator alike; the
      difference of the two densities is the increment.\<close>
  have iB1: "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>)"
    and iB2: "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
  proof -
    have cmp: "(\<lambda>\<omega>. indicat_real Bs (?p \<omega>)) \<in> borel_measurable Q"
      using measurable_comp[OF pimQ borel_measurable_indicator[OF Bs]]
      by (simp add: o_def)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gpi _])
        (use cmp gpm gp0 in
          \<open>auto intro!: borel_measurable_times simp: indicator_def\<close>)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gmi _])
        (use cmp gmm gm0 in
          \<open>auto intro!: borel_measurable_times simp: indicator_def\<close>)
  qed
  have "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      = (\<integral>y. indicat_real Bs y \<partial>N1)"
    unfolding N1_def
    by (rule push[OF borel_measurable_indicator[OF Bs] gpm gp0, symmetric])
  also have "\<dots> = (\<integral>y. indicat_real Bs y \<partial>N2)" unfolding NEQ ..
  also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    unfolding N2_def
    by (rule push[OF borel_measurable_indicator[OF Bs] gmm gm0])
  finally have keq: "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)" .
  have feB: "(\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>
        - indicat_real Bs (?p \<omega>) * gm \<omega>)
      = (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * ?g \<omega>)"
    by (rule ext) (simp add: gdiff[symmetric] right_diff_distrib)
  have "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * ?g \<omega> \<partial>Q)
      = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> - indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    by (simp only: feB)
  also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      - (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    by (rule Bochner_Integration.integral_diff[OF iB1 iB2])
  also have "\<dots> = 0" using keq by simp
  finally show ?thesis .
qed

subsection \<open>The natural filtration is generated by the restriction map\<close>

text \<open>The converse of \<open>restrict_measurable_natural_filtration\<close>: for
  \<open>u \<le> s\<close> the evaluation \<open>\<omega> \<mapsto> \<omega> u\<close> factors through the restriction as
  \<open>ev\<^sub>u \<circ> restrict\<close>, and \<open>ev\<^sub>u\<close> is continuous on the \<open>s\<close>-path space.  So
  every event of \<open>\<FF>\<^sub>s\<close> is a past event, which turns
  \<open>exit_class_martingale_event_limit\<close> into the set-integral
  hypothesis of \<open>martingale_of_set_integral_eq\<close>.\<close>

lemma pair_law_eval_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
  shows "(\<lambda>\<omega>. \<omega> u) \<in> borel_measurable N"
proof (cases "u \<in> {0..T}")
  case True
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> u)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF continuous_map_path_eval[OF True]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
next
  case False
  \<comment> \<open>off the horizon the coordinate is the constant \<open>undefined\<close>: points of
      the capped path space are extensional on \<open>{0..T}\<close>.\<close>
  have spN: "space N = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsN])
  show ?thesis
  proof (rule measurableI)
    show "\<And>\<omega> :: 'n pairpath. \<omega> \<in> space N \<Longrightarrow> \<omega> u \<in> space borel" by simp
    fix C :: "((real^'n) \<times> (real^'n^'n)) set"
    assume "C \<in> sets borel"
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) -` C \<inter> space N
        = (if undefined \<in> C then space N else {})"
      using spN False by (auto simp: path_metric_def extensional_def)
    then show "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) -` C \<inter> space N \<in> sets N" by simp
  qed
qed

lemma natural_filtration_eq_restrict_vimage:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and A: "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  obtains Bs where
    "Bs \<in> sets (path_borel s :: ('n pairpath) measure)"
    and "A = (\<lambda>\<omega>. restrict \<omega> {0..s}) -` Bs \<inter> space Q"
proof -
  let ?PS = "mtopology_of (path_metric s :: ('n pairpath) metric)"
  let ?p = "\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}"
  let ?V = "vimage_algebra (space Q) ?p (borel_of ?PS)"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have pin: "?p \<in> space Q \<rightarrow> space (borel_of ?PS)"
    using restrict_in_mspace[OF s sT] spQ by (auto simp: space_borel_of)
  have pV: "?p \<in> ?V \<rightarrow>\<^sub>M borel_of ?PS"
    by (rule measurable_vimage_algebra1[OF pin])
  have evV: "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> ?V \<rightarrow>\<^sub>M borel" if u: "u \<in> {0..s}" for u
  proof -
    have "(\<lambda>g :: 'n pairpath. g u) \<in> borel_of ?PS \<rightarrow>\<^sub>M borel"
      using continuous_map_measurable[OF continuous_map_path_eval[OF u]]
      by (simp add: borel_of_euclidean)
    from measurable_compose[OF pV this]
    have "(\<lambda>\<omega> :: 'n pairpath. ?p \<omega> u) \<in> ?V \<rightarrow>\<^sub>M borel" .
    moreover have "(\<lambda>\<omega> :: 'n pairpath. ?p \<omega> u) = (\<lambda>\<omega> :: 'n pairpath. \<omega> u)"
      using u by (rule_tac ext) simp
    ultimately show ?thesis by simp
  qed
  have fam: "{(\<lambda>u \<omega> :: 'n pairpath. \<omega> u) i | i. i \<in> {0..s}}
      \<subseteq> ?V \<rightarrow>\<^sub>M (borel :: ((real^'n) \<times> (real^'n^'n)) measure)"
    using evV by blast
  have "family_vimage_algebra (space ?V)
      {(\<lambda>u \<omega> :: 'n pairpath. \<omega> u) i | i. i \<in> {0..s}}
      (borel :: ((real^'n) \<times> (real^'n^'n)) measure) \<subseteq> ?V"
    using fam measurable_family_iff_sets by blast
  then have inc: "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s) \<subseteq> sets ?V"
    unfolding natural_filtration_def by simp
  from A inc have "A \<in> sets ?V" by blast
  then obtain Bs where "Bs \<in> sets (borel_of ?PS)" and "A = ?p -` Bs \<inter> space Q"
    using sets_vimage_algebra2[OF pin] by blast
  then show thesis by (rule that)
qed

subsection \<open>The limit law's process is a martingale\<close>

text \<open>\<open>fst_coord_borel\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


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
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ i"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  \<comment> \<open>\<open>stochastic_process\<close> is shadowed by \<open>Kolmogorov_Chentsov's\<close> homonym;
      the Martingales one must be qualified by its theory name.\<close>
  have SP: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsQ])
  interpret SF: finite_filtered_measure Q ?F 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP finQ])
  have mI: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T by simp
  have iY: "integrable Q (?Y u)" if u: "0 \<le> u" for u
  proof (rule integrable_of_sq_integrable[OF finQ])
    show "?Y u \<in> borel_measurable Q"
      by (rule pair_law_coord_measurable[OF setsQ mI[OF u]])
    show "integrable Q (\<lambda>\<omega>. (?Y u \<omega>)\<^sup>2)"
      by (rule pair_law_sq_integrable_of_nn_bound[OF setsQ mI[OF u]
            exit_class_limit_sq_nn[OF T L mem wc mI[OF u]]])
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process Q ?F 0 ?Y"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?F u \<rightarrow>\<^sub>M borel"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use u T in auto)
      show "?Y u \<in> borel_measurable (?F u)"
        by (rule measurable_compose[OF ev fst_coord_borel])
    qed
    show "\<And>u. 0 \<le> u \<Longrightarrow> integrable Q (?Y u)" by (rule iY)
    fix A and u v :: real
    assume A: "A \<in> ?F u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have Ai: "A \<in> sets Q"
      using A SF.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
    have siY: "set_integrable Q A (?Y w)" if w: "0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai iY[OF w]])
    show "set_lebesgue_integral Q A (?Y u) = set_lebesgue_integral Q A (?Y v)"
    proof (cases "u \<le> T")
      case False
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case True
      have mu: "min u T = u" using True by simp
      have tI: "min v T \<in> {0..T}" by (rule mI[OF v0])
      have tT: "min v T \<le> T" using tI by simp
      have ut: "u \<le> min v T" using True uv by simp
      obtain Bs where Bs: "Bs \<in> sets (path_borel u :: ('n pairpath) measure)"
        and Aeq: "A = (\<lambda>\<omega>. restrict \<omega> {0..u}) -` Bs \<inter> space Q"
        using natural_filtration_eq_restrict_vimage[OF setsQ uv(1) True A]
        by blast
      have ind: "indicat_real A \<omega> = indicat_real Bs (restrict \<omega> {0..u})"
        if "\<omega> \<in> space Q" for \<omega> using Aeq that by (simp add: indicator_def)
      have zero: "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (fst (\<omega> (min v T)) $ i - fst (\<omega> u) $ i) \<partial>Q) = 0"
        by (rule exit_class_martingale_event_limit
            [OF T L mem wc prob setsQ uv(1) ut tT Bs])
      have mR: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u})
            * (fst (\<omega> (min v T)) $ i - fst (\<omega> u) $ i)) \<in> borel_measurable Q"
      proof -
        have rm: "(\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..u}) \<in> Q \<rightarrow>\<^sub>M
            (path_borel u :: ('n pairpath) measure)"
          using continuous_map_measurable
            [OF Lipschitz_continuous_imp_continuous_map
              [OF Lipschitz_restrict_path_metric[OF uv(1) True]]]
            measurable_cong_sets[OF setsQ refl] by blast
        have im: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u}))
            \<in> borel_measurable Q"
          by (rule measurable_compose[OF rm borel_measurable_indicator[OF Bs]])
        have c1: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min v T)) $ i)
            \<in> borel_measurable Q"
          by (rule pair_law_coord_measurable[OF setsQ tI])
        have c2: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) $ i) \<in> borel_measurable Q"
          using True uv(1) by (intro pair_law_coord_measurable[OF setsQ]) simp
        show ?thesis by (intro borel_measurable_times im
            borel_measurable_diff c1 c2)
      qed
      have mD: "(\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
          - indicat_real A \<omega> *\<^sub>R ?Y u \<omega>) \<in> borel_measurable Q"
        using siY[OF v0] siY[OF uv(1)]
        by (intro borel_measurable_diff)
          (auto simp: set_integrable_def dest: borel_measurable_integrable)
      have "(\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega> \<partial>Q)
          - (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y u \<omega> \<partial>Q)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
              - indicat_real A \<omega> *\<^sub>R ?Y u \<omega> \<partial>Q)"
        using siY[OF v0] siY[OF uv(1)]
        by (intro Bochner_Integration.integral_diff[symmetric])
          (auto simp: set_integrable_def)
      also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (fst (\<omega> (min v T)) $ i - fst (\<omega> u) $ i) \<partial>Q)"
      proof (rule integral_cong_AE[OF mD mR])
        show "AE \<omega> in Q. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
            - indicat_real A \<omega> *\<^sub>R ?Y u \<omega>
            = indicat_real Bs (restrict \<omega> {0..u})
              * (fst (\<omega> (min v T)) $ i - fst (\<omega> u) $ i)"
          by (intro AE_I2) (simp add: ind mu right_diff_distrib)
      qed
      also have "\<dots> = 0" by (rule zero)
      finally show ?thesis
        unfolding set_lebesgue_integral_def by simp
    qed
  qed
qed

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

lemma exit_class_path_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. \<omega> (min s T))"
proof -
  have "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    using w space_of_path_sets[OF setsQ] by simp
  from mspace_path_metricD[OF this] have c: "continuous_on {0..T} \<omega>" .
  have m: "continuous_on {0..} (\<lambda>s :: real. min s T)"
    by (intro continuous_intros)
  have mim: "(\<lambda>s :: real. min s T) ` {0..} \<subseteq> {0..T}" using T by auto
  show ?thesis by (rule continuous_on_compose2[OF c m mim])
qed

lemma exit_class_coord_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)) $ i)"
proof -
  have c2: "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)))"
    by (rule continuous_on_fst[OF exit_class_path_cont[OF T setsQ w]])
  have c3: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  show ?thesis by (rule continuous_on_compose2[OF c3 c2]) simp
qed

lemma exit_class_comp_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..}
      (\<lambda>s. (fst (\<omega> (min s T)) $ i)\<^sup>2 - snd (\<omega> (min s T)) $ i $ i)"
proof -
  have cx: "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)) $ i)"
    by (rule exit_class_coord_paths_cont[OF T setsQ w])
  have c2: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)))"
    by (rule continuous_on_snd[OF exit_class_path_cont[OF T setsQ w]])
  have c3: "continuous_on UNIV (\<lambda>v :: real^'n^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have c4: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)) $ i)"
    by (rule continuous_on_compose2[OF c3 c2]) simp
  have c5: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have cy: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)) $ i $ i)"
    by (rule continuous_on_compose2[OF c5 c4]) simp
  show ?thesis
    by (rule continuous_on_diff[OF continuous_on_power[OF cx] cy])
qed

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

definition pcoord :: "real \<Rightarrow> 'n::finite \<Rightarrow> real \<Rightarrow> ('n pairpath) \<Rightarrow> real"
  where "pcoord T i u \<omega> = fst (\<omega> (min u T)) $ i"

definition ploc :: "real \<Rightarrow> 'n::finite \<Rightarrow> real \<Rightarrow> ('n pairpath) \<Rightarrow> real"
  where "ploc T i R \<omega> = etime T {y. R \<le> \<bar>y\<bar>} (pcoord T i) \<omega>"

text \<open>\<open>closed_abs_ge\<close>, \<open>abs_ge_nonempty\<close> live in @{theory Semicontinuous_Analysis.Semicontinuity}.\<close>


lemma ploc_nonneg: "0 \<le> T \<Longrightarrow> 0 \<le> ploc T i R \<omega>"
  unfolding ploc_def by (rule etime_nonneg)

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

lemma pcoord_stopped_bounded:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T: "0 \<le> T" and R: "0 < R"
    and start: "\<bar>pcoord T i 0 \<omega>\<bar> < R"
    and cont: "continuous_on {0..T} (\<lambda>s. pcoord T i s \<omega>)"
    and v: "0 \<le> v"
  shows "\<bar>pcoord T i (min v (ploc T i R \<omega>)) \<omega>\<bar> \<le> R"
proof -
  have nrm: "{y :: real. R \<le> \<bar>y\<bar>} = {y. R \<le> norm y}" by simp
  have s0: "0 \<le> min v (ploc T i R \<omega>)"
    using v ploc_nonneg[OF T, of i R \<omega>] by simp
  have sle: "min v (ploc T i R \<omega>)
      \<le> etime T {y. R \<le> norm y} (pcoord T i) \<omega>"
    unfolding ploc_def[symmetric] nrm[symmetric] by simp
  have "pcoord T i (min v (ploc T i R \<omega>)) \<omega> \<in> cball 0 R"
    using start cont
    by (intro etime_stays_in_cball[OF T R _ _ s0 sle]) simp_all
  then show ?thesis by (simp add: dist_real_def)
qed

subsection \<open>Optional stopping at the localizing time\<close>

text \<open>\<open>Optional_Sampling.optional_stopping\<close> asks for an integrable
  envelope of the unstopped process, which the market locale could not
  supply but a class member has: \<open>Doob_Inequality.horizon_sq_int_martingale\<close>
  builds \<open>Dsup\<close> from Doob's \<open>L\<^sup>2\<close> inequality out of nothing but
  square-integrability, which \<open>exit_class_sq_integrable\<close>
  provides.\<close>

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

lemma pcoord_stopped_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. pcoord T i (min s (ploc T i R \<omega>)) \<omega>)"
proof -
  have c: "continuous_on {0..} (\<lambda>s. pcoord T i s \<omega>)"
    unfolding pcoord_def
    by (rule exit_class_coord_paths_cont[OF T setsQ w])
  have m: "continuous_on {0..} (\<lambda>s :: real. min s (ploc T i R \<omega>))"
    by (intro continuous_intros)
  have mim: "(\<lambda>s :: real. min s (ploc T i R \<omega>)) ` {0..} \<subseteq> {0..}"
    using ploc_nonneg[OF T, of i R \<omega>] by auto
  show ?thesis by (rule continuous_on_compose2[OF c m mim])
qed

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


lemma ploc_eq_T_of_below:
  fixes \<omega> :: "'n::finite pairpath"
  assumes h: "\<And>r. 0 \<le> r \<Longrightarrow> r \<le> T \<Longrightarrow> \<bar>pcoord T i r \<omega>\<bar> < R"
  shows "ploc T i R \<omega> = T"
proof -
  have e: "{r. 0 \<le> r \<and> r \<le> T \<and> pcoord T i r \<omega> \<in> {y :: real. R \<le> \<bar>y\<bar>}} \<union> {T}
      = {T}"
    using h by fastforce
  show ?thesis unfolding ploc_def etime_def e by simp
qed

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

lemma pair_eval_F_cont:
  fixes F :: "(real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F" and t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclideanreal (\<lambda>\<omega>. F (\<omega> t))"
proof -
  have ev: "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> t)"
    by (rule continuous_map_path_eval[OF t])
  have Fm: "continuous_map (euclidean :: ((real^'n) \<times> (real^'n^'n)) topology)
      euclideanreal F"
    using Fc by simp
  show ?thesis
    using continuous_map_compose[OF ev Fm] by (simp add: o_def)
qed

lemma pair_eval_F_sq_cont:
  fixes F :: "(real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F" and t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclideanreal (\<lambda>\<omega>. (F (\<omega> t))\<^sup>2)"
proof -
  have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclideanreal
      (\<lambda>\<omega>. F (\<omega> t) * F (\<omega> t))"
    by (rule continuous_map_real_mult[OF pair_eval_F_cont[OF Fc t]
          pair_eval_F_cont[OF Fc t]])
  then show ?thesis by (simp add: power2_eq_square)
qed

lemma pair_test_F_functional_cont:
  fixes F :: "(real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real"
    and h :: "('n pairpath) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclideanreal
      (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))"
proof -
  let ?PT = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have part1: "continuous_map ?PT euclideanreal (\<lambda>\<omega>. F (\<omega> t) - F (\<omega> s))"
    by (intro continuous_map_diff pair_eval_F_cont[OF Fc] tI sI)
  have rc: "continuous_map ?PT
      (mtopology_of (path_metric s :: ('n pairpath) metric))
      (\<lambda>\<omega>. restrict \<omega> {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have part2: "continuous_map ?PT euclideanreal (\<lambda>\<omega>. h (restrict \<omega> {0..s}))"
    using continuous_map_compose[OF rc hc] by (simp add: o_def)
  show ?thesis by (rule continuous_map_real_mult[OF part2 part1])
qed

lemma pair_law_F_measurable:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. F (\<omega> u)) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> u))
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_F_cont[OF Fc u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_F_sq_measurable:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. (F (\<omega> u))\<^sup>2) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. (F (\<omega> u))\<^sup>2)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_F_sq_cont[OF Fc u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_F_sq_integrable_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
    and bnd: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. (F (\<omega> u))\<^sup>2)"
proof -
  have m: "(\<lambda>\<omega>. (F (\<omega> u))\<^sup>2) \<in> borel_measurable N"
    by (rule pair_law_F_sq_measurable[OF Fc setsN u])
  have lt: "(\<integral>\<^sup>+\<omega>. ennreal (norm ((F (\<omega> u))\<^sup>2)) \<partial>N) < \<infinity>"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (norm ((F (\<omega> u))\<^sup>2)) \<partial>N) \<le> ennreal C"
      using bnd by simp
    also have "ennreal C < \<infinity>" by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding integrable_iff_bounded using m lt by blast
qed

lemma pair_law_F_sq_mean_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes int: "integrable N (\<lambda>\<omega>. (F (\<omega> u))\<^sup>2)" and C0: "0 \<le> C"
    and bnd: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "(\<integral>\<omega>. (F (\<omega> u))\<^sup>2 \<partial>N) \<le> C"
proof -
  have "ennreal (\<integral>\<omega>. (F (\<omega> u))\<^sup>2 \<partial>N) = (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>N)"
    by (rule nn_integral_eq_integral[OF int, symmetric]) simp
  also have "\<dots> \<le> ennreal C" by (rule bnd)
  finally show ?thesis using C0 by simp
qed

lemma pair_test_F_measurable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))
      \<in> borel_measurable N"
proof -
  have sT: "s \<le> T" using ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have "(\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable
      [OF pair_test_F_functional_cont[OF Fc st sT tI hc]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_test_F_sq_bound:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N" and Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> s))\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> t))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. (h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))\<^sup>2)"
    and "(\<integral>\<omega>. (h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))\<^sup>2 \<partial>N)
        \<le> 4 * B\<^sup>2 * C"
proof -
  let ?f = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s))"
  let ?D = "\<lambda>\<omega> :: 'n pairpath. 2 * B\<^sup>2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2)"
  have sI: "s \<in> {0..T}" using st ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have B0: "0 \<le> B" by (rule order_trans[OF abs_ge_zero hb])
  have iss: "integrable N (\<lambda>\<omega>. (F (\<omega> s))\<^sup>2)"
    by (rule pair_law_F_sq_integrable_of_nn_bound[OF Fc setsN sI Cs])
  have itt: "integrable N (\<lambda>\<omega>. (F (\<omega> t))\<^sup>2)"
    by (rule pair_law_F_sq_integrable_of_nn_bound[OF Fc setsN tI Ct])
  have fm: "?f \<in> borel_measurable N"
    by (rule pair_test_F_measurable[OF Fc setsN st ts tT hc])
  have fsqm: "(\<lambda>\<omega>. (?f \<omega>)\<^sup>2) \<in> borel_measurable N" using fm by measurable
  have dom_int: "integrable N ?D"
    by (intro integrable_mult_right Bochner_Integration.integrable_add itt iss)
  have ptwise: "(?f \<omega>)\<^sup>2 \<le> ?D \<omega>" for \<omega>
  proof -
    have hsq: "(h (restrict \<omega> {0..s}))\<^sup>2 \<le> B\<^sup>2"
    proof -
      have "\<bar>h (restrict \<omega> {0..s})\<bar>\<^sup>2 \<le> B\<^sup>2"
        by (rule power_mono[OF hb abs_ge_zero])
      then show ?thesis by simp
    qed
    have e1: "2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2) - (F (\<omega> t) - F (\<omega> s))\<^sup>2
        = (F (\<omega> t) + F (\<omega> s))\<^sup>2"
      by (simp add: power2_diff power2_sum)
    have sq_le: "(F (\<omega> t) - F (\<omega> s))\<^sup>2 \<le> 2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2)"
      using e1 zero_le_power2[of "F (\<omega> t) + F (\<omega> s)"] by linarith
    have "(?f \<omega>)\<^sup>2 = (h (restrict \<omega> {0..s}))\<^sup>2 * (F (\<omega> t) - F (\<omega> s))\<^sup>2"
      by (simp add: power_mult_distrib)
    also have "\<dots> \<le> B\<^sup>2 * (F (\<omega> t) - F (\<omega> s))\<^sup>2"
      by (rule mult_right_mono[OF hsq zero_le_power2])
    also have "\<dots> \<le> B\<^sup>2 * (2 * ((F (\<omega> t))\<^sup>2 + (F (\<omega> s))\<^sup>2))"
      by (rule mult_left_mono[OF sq_le zero_le_power2])
    also have "\<dots> = ?D \<omega>" by simp
    finally show ?thesis .
  qed
  show fsq_int: "integrable N (\<lambda>\<omega>. (?f \<omega>)\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound[OF dom_int fsqm])
    show "AE \<omega> in N. norm ((?f \<omega>)\<^sup>2) \<le> norm (?D \<omega>)"
    proof (intro AE_I2)
      fix \<omega> :: "'n pairpath"
      have "0 \<le> ?D \<omega>" by simp
      then show "norm ((?f \<omega>)\<^sup>2) \<le> norm (?D \<omega>)" using ptwise[of \<omega>] by simp
    qed
  qed
  have Bs: "(\<integral>\<omega>. (F (\<omega> s))\<^sup>2 \<partial>N) \<le> C"
    by (rule pair_law_F_sq_mean_of_nn_bound[OF iss C0 Cs])
  have Bt: "(\<integral>\<omega>. (F (\<omega> t))\<^sup>2 \<partial>N) \<le> C"
    by (rule pair_law_F_sq_mean_of_nn_bound[OF itt C0 Ct])
  have "(\<integral>\<omega>. (?f \<omega>)\<^sup>2 \<partial>N) \<le> (\<integral>\<omega>. ?D \<omega> \<partial>N)"
    by (rule integral_mono[OF fsq_int dom_int]) (rule ptwise)
  also have "(\<integral>\<omega>. ?D \<omega> \<partial>N)
      = 2 * B\<^sup>2 * ((\<integral>\<omega>. (F (\<omega> t))\<^sup>2 \<partial>N) + (\<integral>\<omega>. (F (\<omega> s))\<^sup>2 \<partial>N))"
    by (simp add: Bochner_Integration.integral_add[OF itt iss])
  also have "\<dots> \<le> 2 * B\<^sup>2 * (2 * C)"
    by (rule mult_left_mono) (use Bs Bt zero_le_power2 in auto)
  also have "\<dots> = 4 * B\<^sup>2 * C" by simp
  finally show "(\<integral>\<omega>. (?f \<omega>)\<^sup>2 \<partial>N) \<le> 4 * B\<^sup>2 * C" .
qed

lemma pair_test_F_integrable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N" and Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
    and C0: "0 \<le> C"
    and Cs: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> s))\<^sup>2) \<partial>N) \<le> ennreal C"
    and Ct: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> t))\<^sup>2) \<partial>N) \<le> ennreal C"
  shows "integrable N (\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))"
proof -
  have fmN: "finite_measure N" using P by (simp add: prob_space_def)
  show ?thesis
    by (rule integrable_of_sq_integrable[OF fmN
          pair_test_F_measurable[OF Fc setsN st ts tT hc]
          pair_test_F_sq_bound(1)[OF P Fc setsN st ts tT hc hb C0 Cs Ct]])
qed

subsection \<open>The test identity and its weak limit, generically\<close>

theorem martingale_test_F:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and mgF: "martingale N (natural_filtration N 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hm: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)) \<partial>N) = 0"
proof -
  let ?FF = "natural_filtration N 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. F (\<omega> (min u T))"
  let ?Z = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s})"
  have sT: "s \<le> T" using ts tT by simp
  have t0: "0 \<le> t" using st ts by simp
  have mt: "min t T = t" using tT by simp
  have ms: "min s T = s" using sT by simp
  interpret P: prob_space N by (rule P)
  interpret MY: martingale N ?FF 0 ?Y by (rule mgF)
  have Zm: "?Z \<in> borel_measurable (?FF s)"
    by (rule past_test_measurable_natural_filtration[OF setsN st sT hm])
  have ZM: "?Z \<in> borel_measurable N"
    by (rule measurable_from_subalg[OF MY.subalgebras[OF st] Zm])
  have prod_int: "integrable N (\<lambda>\<omega>. ?Z \<omega> * ?Y u \<omega>)" if u: "0 \<le> u" for u
  proof (rule Bochner_Integration.integrable_bound)
    show "integrable N (\<lambda>\<omega>. \<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)"
      by (intro integrable_mult_right Bochner_Integration.integrable_abs
          MY.integrable[OF u])
    show "(\<lambda>\<omega>. ?Z \<omega> * ?Y u \<omega>) \<in> borel_measurable N"
      using ZM borel_measurable_integrable[OF MY.integrable[OF u]]
      by measurable
    show "AE \<omega> in N. norm (?Z \<omega> * ?Y u \<omega>) \<le> norm (\<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)"
    proof (intro AE_I2)
      fix \<omega> :: "'n pairpath"
      have "\<bar>?Z \<omega>\<bar> \<le> \<bar>B\<bar>" using hb[of "restrict \<omega> {0..s}"] by simp
      then have "\<bar>?Z \<omega> * ?Y u \<omega>\<bar> \<le> \<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>"
        by (simp add: abs_mult mult_right_mono)
      then show "norm (?Z \<omega> * ?Y u \<omega>) \<le> norm (\<bar>B\<bar> * \<bar>?Y u \<omega>\<bar>)" by simp
    qed
  qed
  have int_t: "integrable N (\<lambda>\<omega>. ?Z \<omega> * ?Y t \<omega>)" by (rule prod_int[OF t0])
  have int_s: "integrable N (\<lambda>\<omega>. ?Z \<omega> * ?Y s \<omega>)" by (rule prod_int[OF st])
  have eqts: "(\<integral>\<omega>. ?Z \<omega> * ?Y t \<omega> \<partial>N) = (\<integral>\<omega>. ?Z \<omega> * ?Y s \<omega> \<partial>N)"
    by (rule martingale_bounded_test[OF mgF st ts Zm int_t int_s])
  have "(\<integral>\<omega>. ?Z \<omega> * (?Y t \<omega> - ?Y s \<omega>) \<partial>N)
      = (\<integral>\<omega>. ?Z \<omega> * ?Y t \<omega> \<partial>N) - (\<integral>\<omega>. ?Z \<omega> * ?Y s \<omega> \<partial>N)"
    using Bochner_Integration.integral_diff[OF int_t int_s]
    by (simp add: right_diff_distrib)
  then show ?thesis using eqts mt ms by simp
qed

theorem martingale_test_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)) \<partial>Q) = 0"
proof -
  let ?f = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s))"
  have sT: "s \<le> T" using ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have B0: "0 \<le> B" by (rule order_trans[OF abs_ge_zero hb])
  have fmm: "finite_measure (Qm m)" for m
    using Pm by (simp add: prob_space_def)
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>Q) \<le> ennreal C" if u: "u \<in> {0..T}"
    for u
    by (rule weak_conv_on_nn_integral_le
        [OF wc pair_eval_F_sq_cont[OF Fc u] _ C0 nnm[OF u]]) simp
  have intm: "integrable (Qm m) ?f" for m
    by (rule pair_test_F_integrable[OF Pm Fc setsm st ts tT hc hb C0
          nnm[OF sI] nnm[OF tI]])
  have intQ: "integrable Q ?f"
    by (rule pair_test_F_integrable[OF prob Fc setsQ st ts tT hc hb C0
          nnQ[OF sI] nnQ[OF tI]])
  have lim: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> (\<integral>\<omega>. ?f \<omega> \<partial>Q)"
  proof (rule weak_conv_integral_of_L2_bound)
    show "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))" by (rule wc)
    show "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
        euclideanreal ?f"
      by (rule pair_test_F_functional_cont[OF Fc st sT tI hc])
    show "\<And>m. finite_measure (Qm m)" by (rule fmm)
    show "finite_measure Q" by (rule fmQ)
    show "\<And>m. integrable (Qm m) ?f" by (rule intm)
    show "integrable Q ?f" by (rule intQ)
    show "\<And>m Rr. integrable (Qm m) (\<lambda>w. max (- Rr) (min Rr (?f w)))"
      by (rule clamp_integrable[OF fmm borel_measurable_integrable[OF intm]])
    show "\<And>Rr. integrable Q (\<lambda>w. max (- Rr) (min Rr (?f w)))"
      by (rule clamp_integrable[OF fmQ borel_measurable_integrable[OF intQ]])
    show "\<And>m Rr. integrable (Qm m)
        (\<lambda>w. \<bar>?f w\<bar> * indicat_real {z. Rr < \<bar>z\<bar>} (?f w))"
      by (rule tail_integrable[OF intm])
    show "\<And>Rr. integrable Q (\<lambda>w. \<bar>?f w\<bar> * indicat_real {z. Rr < \<bar>z\<bar>} (?f w))"
      by (rule tail_integrable[OF intQ])
    show "0 \<le> 4 * B\<^sup>2 * C" using C0 by simp
    show "\<And>m. (\<integral>w. (?f w)\<^sup>2 \<partial>(Qm m)) \<le> 4 * B\<^sup>2 * C"
      by (rule pair_test_F_sq_bound(2)[OF Pm Fc setsm st ts tT hc hb C0
            nnm[OF sI] nnm[OF tI]])
    show "(\<integral>w. (?f w)\<^sup>2 \<partial>Q) \<le> 4 * B\<^sup>2 * C"
      by (rule pair_test_F_sq_bound(2)[OF prob Fc setsQ st ts tT hc hb C0
            nnQ[OF sI] nnQ[OF tI]])
    show "\<And>m. integrable (Qm m) (\<lambda>w. (?f w)\<^sup>2)"
      by (rule pair_test_F_sq_bound(1)[OF Pm Fc setsm st ts tT hc hb C0
            nnm[OF sI] nnm[OF tI]])
    show "integrable Q (\<lambda>w. (?f w)\<^sup>2)"
      by (rule pair_test_F_sq_bound(1)[OF prob Fc setsQ st ts tT hc hb C0
            nnQ[OF sI] nnQ[OF tI]])
  qed
  have hm: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
    using continuous_map_measurable[OF hc] by (simp add: borel_of_euclidean)
  have zero: "(\<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) = 0" for m
    by (rule martingale_test_F[OF Pm setsm mgm st ts tT hm hb])
  have z: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> 0" using zero by simp
  show ?thesis by (rule tendsto_unique[OF _ lim z]) simp
qed

subsection \<open>The set-integral identity and martingale reassembly,
  generically\<close>

theorem martingale_event_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and Bs: "Bs \<in> sets (path_borel s :: ('n pairpath) measure)"
  shows "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)) \<partial>Q)
      = 0"
proof -
  let ?PS = "mtopology_of (path_metric s :: ('n pairpath) metric)"
  let ?g = "\<lambda>\<omega> :: 'n pairpath. F (\<omega> t) - F (\<omega> s)"
  let ?p = "\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}"
  have sT: "s \<le> T" using ts tT by simp
  have sI: "s \<in> {0..T}" using st sT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>Q) \<le> ennreal C" if u: "u \<in> {0..T}"
    for u
    by (rule weak_conv_on_nn_integral_le
        [OF wc pair_eval_F_sq_cont[OF Fc u] _ C0 nnm[OF u]]) simp
  have onec: "continuous_map ?PS euclideanreal (\<lambda>_. 1 :: real)" by simp
  have one_b: "\<And>g :: 'n pairpath. \<bar>(\<lambda>_. 1 :: real) g\<bar> \<le> 1" by simp
  have gint: "integrable Q ?g"
  proof -
    have "integrable Q (\<lambda>\<omega>. (\<lambda>_. 1 :: real) (?p \<omega>) * (F (\<omega> t) - F (\<omega> s)))"
      by (rule pair_test_F_integrable[OF prob Fc setsQ st ts tT onec one_b C0
            nnQ[OF sI] nnQ[OF tI]])
    then show ?thesis by simp
  qed
  have gmeasQ: "?g \<in> borel_measurable Q"
    by (rule borel_measurable_integrable[OF gint])
  have rc: "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) ?PS ?p"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have pimQ: "?p \<in> Q \<rightarrow>\<^sub>M borel_of ?PS"
    using continuous_map_measurable[OF rc] measurable_cong_sets[OF setsQ refl]
    by blast
  define gp where "gp = (\<lambda>\<omega> :: 'n pairpath. max (?g \<omega>) 0)"
  define gm where "gm = (\<lambda>\<omega> :: 'n pairpath. max (- ?g \<omega>) 0)"
  have gp0: "\<And>\<omega>. 0 \<le> gp \<omega>" and gm0: "\<And>\<omega>. 0 \<le> gm \<omega>"
    unfolding gp_def gm_def by simp_all
  have gdiff: "gp \<omega> - gm \<omega> = ?g \<omega>" for \<omega>
    unfolding gp_def gm_def by (simp add: max_def)
  have gpm: "gp \<in> borel_measurable Q" and gmm: "gm \<in> borel_measurable Q"
    unfolding gp_def gm_def
    by (intro borel_measurable_max gmeasQ borel_measurable_const
        borel_measurable_uminus)+
  have gpi: "integrable Q gp" and gmi: "integrable Q gm"
    unfolding gp_def gm_def
    by (rule Bochner_Integration.integrable_max
        [OF gint Bochner_Integration.integrable_zero],
        rule Bochner_Integration.integrable_max
        [OF Bochner_Integration.integrable_minus[OF gint]
            Bochner_Integration.integrable_zero])
  define N1 where "N1 = distr (density Q (\<lambda>\<omega>. ennreal (gp \<omega>))) (borel_of ?PS) ?p"
  define N2 where "N2 = distr (density Q (\<lambda>\<omega>. ennreal (gm \<omega>))) (borel_of ?PS) ?p"
  have sN1: "sets N1 = sets (borel_of ?PS)"
    and sN2: "sets N2 = sets (borel_of ?PS)"
    unfolding N1_def N2_def by simp_all
  have pdm: "?p \<in> density Q (\<lambda>\<omega>. ennreal (w \<omega>)) \<rightarrow>\<^sub>M borel_of ?PS" for w
    using pimQ measurable_cong_sets[OF sets_density refl] by blast
  have push: "(\<integral>y. u y \<partial>(distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>)))
        (borel_of ?PS) ?p)) = (\<integral>\<omega>. u (?p \<omega>) * w \<omega> \<partial>Q)"
    if um: "u \<in> borel_measurable (borel_of ?PS)"
    and wm: "w \<in> borel_measurable Q" and w0: "\<And>\<omega>. 0 \<le> w \<omega>" for u w
  proof -
    have cmp: "(\<lambda>\<omega>. u (?p \<omega>)) \<in> borel_measurable Q"
      using measurable_comp[OF pimQ um] by (simp add: o_def)
    have "(\<integral>y. u y \<partial>(distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>))) (borel_of ?PS) ?p))
        = (\<integral>\<omega>. u (?p \<omega>) \<partial>(density Q (\<lambda>\<omega>. ennreal (w \<omega>))))"
      by (rule Bochner_Integration.integral_distr[OF pdm um])
    also have "\<dots> = (\<integral>\<omega>. u (?p \<omega>) * w \<omega> \<partial>Q)"
      by (subst integral_density)
        (use cmp wm w0 in \<open>auto simp: mult.commute\<close>)
    finally show ?thesis .
  qed
  have finw: "finite_measure (distr (density Q (\<lambda>\<omega>. ennreal (w \<omega>)))
      (borel_of ?PS) ?p)"
    if wm: "w \<in> borel_measurable Q" and w0: "\<And>\<omega>. 0 \<le> w \<omega>"
    and wi: "integrable Q w" for w
  proof (rule finite_measureI)
    let ?D = "density Q (\<lambda>\<omega>. ennreal (w \<omega>))"
    have sp: "space (distr ?D (borel_of ?PS) ?p) = space (borel_of ?PS)" by simp
    have pre: "?p -` space (borel_of ?PS) \<inter> space ?D = space Q"
      using measurable_space[OF pdm[of w]] by auto
    have "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p))
        = emeasure ?D (?p -` space (borel_of ?PS) \<inter> space ?D)"
      unfolding sp by (intro emeasure_distr pdm) (metis sets.top space_borel_of)
    also have "\<dots> = emeasure ?D (space Q)" unfolding pre ..
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (w \<omega>) * indicator (space Q) \<omega> \<partial>Q)"
      by (intro emeasure_density measurable_compose[OF wm measurable_ennreal]) auto
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (w \<omega>) \<partial>Q)"
      by (intro nn_integral_cong) (simp add: indicator_def)
    also have "\<dots> = ennreal (\<integral>\<omega>. w \<omega> \<partial>Q)"
      by (rule nn_integral_eq_integral[OF wi]) (use w0 in simp)
    also have "\<dots> < \<infinity>" by simp
    finally show "emeasure (distr ?D (borel_of ?PS) ?p)
        (space (distr ?D (borel_of ?PS) ?p)) \<noteq> \<infinity>" by simp
  qed
  have finN1: "finite_measure N1" unfolding N1_def by (rule finw[OF gpm gp0 gpi])
  have finN2: "finite_measure N2" unfolding N2_def by (rule finw[OF gmm gm0 gmi])
  have NEQ: "N1 = N2"
  proof (rule metric_measure_eqI_bounded_cts[OF sN1 sN2 finN1 finN2])
    fix u :: "'n pairpath \<Rightarrow> real"
    assume uc: "continuous_map ?PS euclideanreal u"
    assume ub: "\<exists>B. \<forall>y\<in>topspace ?PS. \<bar>u y\<bar> \<le> B"
    then obtain B where B: "\<And>y. y \<in> topspace ?PS \<Longrightarrow> \<bar>u y\<bar> \<le> B" by blast
    define B' where "B' = max B 0"
    have B'0: "0 \<le> B'" unfolding B'_def by simp
    let ?u = "\<lambda>y. rclamp B' (u y)"
    have ucl: "continuous_map ?PS euclideanreal ?u"
      using continuous_map_compose[OF uc rclamp_cont] by (simp add: o_def)
    have ubd: "\<And>y. \<bar>?u y\<bar> \<le> B'" by (rule rclamp_bound[OF B'0])
    have uagree: "?u y = u y"
      if y: "y \<in> mspace (path_metric s :: ('n pairpath) metric)" for y
    proof (rule rclamp_id)
      have "\<bar>u y\<bar> \<le> B" using B y by simp
      then show "\<bar>u y\<bar> \<le> B'" unfolding B'_def by simp
    qed
    have um: "u \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF uc] by (simp add: borel_of_euclidean)
    have ucm: "?u \<in> borel_measurable (borel_of ?PS)"
      using continuous_map_measurable[OF ucl] by (simp add: borel_of_euclidean)
    have same: "(\<integral>y. u y \<partial>Nj) = (\<integral>y. ?u y \<partial>Nj)"
      if sj: "sets Nj = sets (borel_of ?PS)" for Nj
    proof (rule integral_cong_AE)
      show "u \<in> borel_measurable Nj"
        using um measurable_cong_sets[OF sj refl] by blast
      show "?u \<in> borel_measurable Nj"
        using ucm measurable_cong_sets[OF sj refl] by blast
      have "space Nj = mspace (path_metric s :: ('n pairpath) metric)"
        using sets_eq_imp_space_eq[OF sj] by (simp add: space_borel_of)
      then show "AE y in Nj. u y = ?u y"
        by (intro AE_I2) (simp add: uagree)
    qed
    have zero: "(\<integral>\<omega>. ?u (?p \<omega>) * ?g \<omega> \<partial>Q) = 0"
      by (rule martingale_test_F_limit
          [OF Fc Pm setsm mgm wc prob setsQ C0 nnm st ts tT ucl ubd])
    have i1: "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega>)"
      and i2: "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
    proof -
      have cmp: "(\<lambda>\<omega>. ?u (?p \<omega>)) \<in> borel_measurable Q"
        using measurable_comp[OF pimQ ucm] by (simp add: o_def)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gpi, of B'] _ ])
          (use cmp gpm ubd gp0 B'0 in
            \<open>auto intro!: borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gmi, of B'] _ ])
          (use cmp gmm ubd gm0 B'0 in
            \<open>auto intro!: borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
    qed
    have "(\<integral>y. ?u y \<partial>N1) - (\<integral>y. ?u y \<partial>N2)
        = (\<integral>\<omega>. ?u (?p \<omega>) * gp \<omega> \<partial>Q) - (\<integral>\<omega>. ?u (?p \<omega>) * gm \<omega> \<partial>Q)"
      unfolding N1_def N2_def
      by (simp add: push[OF ucm gpm gp0] push[OF ucm gmm gm0])
    also have "\<dots> = (\<integral>\<omega>. ?u (?p \<omega>) * gp \<omega> - ?u (?p \<omega>) * gm \<omega> \<partial>Q)"
      by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
    also have "\<dots> = (\<integral>\<omega>. ?u (?p \<omega>) * ?g \<omega> \<partial>Q)"
    proof -
      have fe: "(\<lambda>\<omega>. ?u (?p \<omega>) * gp \<omega> - ?u (?p \<omega>) * gm \<omega>)
          = (\<lambda>\<omega>. ?u (?p \<omega>) * ?g \<omega>)"
        by (rule ext) (simp add: gdiff[symmetric] right_diff_distrib)
      show ?thesis by (simp only: fe)
    qed
    also have "\<dots> = 0" by (rule zero)
    finally have "(\<integral>y. ?u y \<partial>N1) = (\<integral>y. ?u y \<partial>N2)" by simp
    then show "(\<integral>y. u y \<partial>N1) = (\<integral>y. u y \<partial>N2)"
      using same[OF sN1] same[OF sN2] by simp
  qed
  have iB1: "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>)"
    and iB2: "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
  proof -
    have cmp: "(\<lambda>\<omega>. indicat_real Bs (?p \<omega>)) \<in> borel_measurable Q"
      using measurable_comp[OF pimQ borel_measurable_indicator[OF Bs]]
      by (simp add: o_def)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gpi _])
        (use cmp gpm gp0 in
          \<open>auto intro!: borel_measurable_times simp: indicator_def\<close>)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gmi _])
        (use cmp gmm gm0 in
          \<open>auto intro!: borel_measurable_times simp: indicator_def\<close>)
  qed
  have "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q) = (\<integral>y. indicat_real Bs y \<partial>N1)"
    unfolding N1_def
    by (rule push[OF borel_measurable_indicator[OF Bs] gpm gp0, symmetric])
  also have "\<dots> = (\<integral>y. indicat_real Bs y \<partial>N2)" unfolding NEQ ..
  also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    unfolding N2_def
    by (rule push[OF borel_measurable_indicator[OF Bs] gmm gm0])
  finally have keq: "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)" .
  have feB: "(\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega>
        - indicat_real Bs (?p \<omega>) * gm \<omega>)
      = (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * ?g \<omega>)"
    by (rule ext) (simp add: gdiff[symmetric] right_diff_distrib)
  have "(\<integral>\<omega>. indicat_real Bs (?p \<omega>) * ?g \<omega> \<partial>Q)
      = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> - indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    by (simp only: feB)
  also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gp \<omega> \<partial>Q)
      - (\<integral>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega> \<partial>Q)"
    by (rule Bochner_Integration.integral_diff[OF iB1 iB2])
  also have "\<dots> = 0" using keq by simp
  finally show ?thesis .
qed

theorem martingale_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes T: "0 \<le> T" and Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (path_borel T :: ('n pairpath) measure)"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. F (\<omega> (min u T)))"
proof -
  let ?FF = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. F (\<omega> (min u T))"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsQ])
  interpret SF: finite_filtered_measure Q ?FF 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP finQ])
  have mI: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T by simp
  have nnQ: "(\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>Q) \<le> ennreal C" if u: "u \<in> {0..T}"
    for u
    by (rule weak_conv_on_nn_integral_le
        [OF wc pair_eval_F_sq_cont[OF Fc u] _ C0 nnm[OF u]]) simp
  have Fb: "F \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF Fc])
  have iY: "integrable Q (?Y u)" if u: "0 \<le> u" for u
  proof (rule integrable_of_sq_integrable[OF finQ])
    show "?Y u \<in> borel_measurable Q"
      by (rule pair_law_F_measurable[OF Fc setsQ mI[OF u]])
    show "integrable Q (\<lambda>\<omega>. (?Y u \<omega>)\<^sup>2)"
      by (rule pair_law_F_sq_integrable_of_nn_bound
          [OF Fc setsQ mI[OF u] nnQ[OF mI[OF u]]])
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process Q ?FF 0 ?Y"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> ?FF u \<rightarrow>\<^sub>M borel"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use u T in auto)
      show "?Y u \<in> borel_measurable (?FF u)"
        by (rule measurable_compose[OF ev Fb])
    qed
    show "\<And>u. 0 \<le> u \<Longrightarrow> integrable Q (?Y u)" by (rule iY)
    fix A and u v :: real
    assume A: "A \<in> ?FF u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have Ai: "A \<in> sets Q"
      using A SF.subalgebras[OF uv(1)] by (auto simp: subalgebra_def)
    have siY: "set_integrable Q A (?Y w)" if w: "0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai iY[OF w]])
    show "set_lebesgue_integral Q A (?Y u) = set_lebesgue_integral Q A (?Y v)"
    proof (cases "u \<le> T")
      case False
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case True
      have mu: "min u T = u" using True by simp
      have tI: "min v T \<in> {0..T}" by (rule mI[OF v0])
      have tT: "min v T \<le> T" using tI by simp
      have ut: "u \<le> min v T" using True uv by simp
      obtain Bs where Bs: "Bs \<in> sets (path_borel u :: ('n pairpath) measure)"
        and Aeq: "A = (\<lambda>\<omega>. restrict \<omega> {0..u}) -` Bs \<inter> space Q"
        using natural_filtration_eq_restrict_vimage[OF setsQ uv(1) True A]
        by blast
      have ind: "indicat_real A \<omega> = indicat_real Bs (restrict \<omega> {0..u})"
        if "\<omega> \<in> space Q" for \<omega> using Aeq that by (simp add: indicator_def)
      have zero: "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (F (\<omega> (min v T)) - F (\<omega> u)) \<partial>Q) = 0"
        by (rule martingale_event_F_limit
            [OF Fc Pm setsm mgm wc prob setsQ C0 nnm uv(1) ut tT Bs])
      have mR: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u})
            * (F (\<omega> (min v T)) - F (\<omega> u))) \<in> borel_measurable Q"
      proof -
        have rm: "(\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..u}) \<in> Q \<rightarrow>\<^sub>M
            (path_borel u :: ('n pairpath) measure)"
          using continuous_map_measurable
            [OF Lipschitz_continuous_imp_continuous_map
              [OF Lipschitz_restrict_path_metric[OF uv(1) True]]]
            measurable_cong_sets[OF setsQ refl] by blast
        have im: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u}))
            \<in> borel_measurable Q"
          by (rule measurable_compose[OF rm borel_measurable_indicator[OF Bs]])
        have c1: "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> (min v T))) \<in> borel_measurable Q"
          by (rule pair_law_F_measurable[OF Fc setsQ tI])
        have c2: "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> u)) \<in> borel_measurable Q"
          using True uv(1) by (intro pair_law_F_measurable[OF Fc setsQ]) simp
        show ?thesis by (intro borel_measurable_times im
            borel_measurable_diff c1 c2)
      qed
      have mD: "(\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
          - indicat_real A \<omega> *\<^sub>R ?Y u \<omega>) \<in> borel_measurable Q"
        using siY[OF v0] siY[OF uv(1)]
        by (intro borel_measurable_diff)
          (auto simp: set_integrable_def dest: borel_measurable_integrable)
      have "(\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega> \<partial>Q)
          - (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y u \<omega> \<partial>Q)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
              - indicat_real A \<omega> *\<^sub>R ?Y u \<omega> \<partial>Q)"
        using siY[OF v0] siY[OF uv(1)]
        by (intro Bochner_Integration.integral_diff[symmetric])
          (auto simp: set_integrable_def)
      also have "\<dots> = (\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (F (\<omega> (min v T)) - F (\<omega> u)) \<partial>Q)"
      proof (rule integral_cong_AE[OF mD mR])
        show "AE \<omega> in Q. indicat_real A \<omega> *\<^sub>R ?Y v \<omega>
            - indicat_real A \<omega> *\<^sub>R ?Y u \<omega>
            = indicat_real Bs (restrict \<omega> {0..u})
              * (F (\<omega> (min v T)) - F (\<omega> u))"
          by (intro AE_I2) (simp add: ind mu right_diff_distrib)
      qed
      also have "\<dots> = 0" by (rule zero)
      finally show ?thesis
        unfolding set_lebesgue_integral_def by simp
    qed
  qed
qed

section \<open>The compensated clause of Lemma 2.3\<close>

text \<open>\<open>prod_minus_sq_bound\<close>, \<open>fourth_power_sum_bound\<close>, \<open>zero_le_fourth\<close> live in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>


subsection \<open>The compensated functional\<close>

lemma comp_entry_eq:
  fixes p :: "(real^'n::finite) \<times> (real^'n^'n)"
  shows "(outerp (fst p) - snd p) $ i $ j = fst p $ i * fst p $ j - snd p $ i $ j"
  by (simp add: outerp_def)

lemma comp_entry_cont:
  shows "continuous_on UNIV
      (\<lambda>p :: (real^'n::finite) \<times> (real^'n^'n). (outerp (fst p) - snd p) $ i $ j)"
proof -
  have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). (outerp (fst p) - snd p) $ i $ j)
      = (\<lambda>p. fst p $ i * fst p $ j - snd p $ i $ j)"
    by (rule ext) (rule comp_entry_eq)
  show ?thesis unfolding e by (intro continuous_intros)
qed

text \<open>The fourth moment of the coordinate itself, not of an increment: the
  start clause pins \<open>X\<^sub>0 = x\<close>, so \<open>(a+b)\<^sup>4 \<le> 8(a\<^sup>4+b\<^sup>4)\<close> turns the increment
  bound into an absolute one, uniform over the whole class.\<close>

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
