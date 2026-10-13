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

section \<open>The uniform fourth moment of the class\<close>

text \<open>This bound supplies the compensated clause of Lemma 2.3.  A
  coordinate of a class member is an \<open>L\<^sup>2\<close> martingale whose square is
  compensated by a diagonal entry of \<open>Y\<close>, which grows at rate at most
  \<open>L\<close>; so the generic estimate @{thm [source] fourth_moment_L2} applies,
  once the start and rate conditions, which the class states only almost
  surely, are made pointwise by restricting to a full-measure event
  (@{thm [source] martingale_restrict_full}).\<close>

subsection \<open>The coordinate process, its compensator, and its paths\<close>

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

theorem exit_class_fourth_moment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
      \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ i"
  let ?A = "\<lambda>u \<omega> :: 'n pairpath. snd (\<omega> (min u T)) $ i $ i"
  have T0: "0 \<le> T" using T by simp
  interpret PQ: prob_space Q by (rule exit_class_prob[OF Q])
  have mgX: "martingale Q ?F 0 ?X" by (rule exit_class_coord_martingale[OF Q])
  have mgZ: "martingale Q ?F 0 (\<lambda>u \<omega>. (?X u \<omega>)\<^sup>2 - ?A u \<omega>)"
    by (rule exit_class_compensated_coord_martingale[OF Q])
  \<comment> \<open>a full-measure event on which the start and the rate hold pointwise\<close>
  have "AE \<omega> in Q. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
      \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L"
    using Q unfolding exit_class_def by blast
  with exit_class_start[OF Q]
  have "AE \<omega> in Q. (fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and> (\<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
      \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L)"
    by (rule eventually_conj)
  then obtain N where good: "\<And>\<omega>. \<omega> \<in> space Q - N \<Longrightarrow>
      (fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0) \<and> (\<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L)"
    and Nn: "N \<in> null_sets Q" by (rule AE_E3) blast
  define G where "G = space Q - N"
  have Gs: "G \<in> sets Q" unfolding G_def using Nn by auto
  have Gfull: "AE \<omega> in Q. \<omega> \<in> G"
    using AE_not_in[OF Nn] AE_space by eventually_elim (simp add: G_def)
  note RF = PQ.prob_space_axioms Gs Gfull
  have spM: "space (restrict_space Q G) = G" by (rule space_restrict_full[OF RF])
  \<comment> \<open>on that event the bound for an \<open>L\<^sup>2\<close> martingale with Lipschitz compensator applies\<close>
  have "(\<integral>\<^sup>+\<omega>. ennreal ((?X tt \<omega> - ?X s \<omega>)^4) \<partial>restrict_space Q G)
      \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
  proof (rule fourth_moment_L2[where B = "\<bar>x $ i\<bar>"])
    show "prob_space (restrict_space Q G)" by (rule prob_space_restrict_full[OF RF])
    show "martingale (restrict_space Q G) (\<lambda>u. restrict_space (?F u) G) 0 ?X"
      by (rule martingale_restrict_full[OF RF mgX])
    show "martingale (restrict_space Q G) (\<lambda>u. restrict_space (?F u) G) 0
        (\<lambda>u \<omega>. (?X u \<omega>)\<^sup>2 - ?A u \<omega>)"
      by (rule martingale_restrict_full[OF RF mgZ])
    show "integrable (restrict_space Q G) (\<lambda>\<omega>. (?X u \<omega>)\<^sup>2)" if "0 \<le> u" for u
      by (rule integrable_restrict_full[OF RF exit_class_sq_integrable[OF T0 L Q]])
        (use that T0 in simp)
    show "continuous_on {0..} (\<lambda>u. ?X u \<omega>)" if "\<omega> \<in> space (restrict_space Q G)" for \<omega>
      by (rule exit_class_coord_paths_cont[OF T0 setsQ]) (use that spM in \<open>simp add: G_def\<close>)
    show "AE \<omega> in restrict_space Q G. \<bar>?X 0 \<omega>\<bar> \<le> \<bar>x $ i\<bar>"
    proof (rule AE_I2)
      fix \<omega> assume "\<omega> \<in> space (restrict_space Q G)"
      then show "\<bar>?X 0 \<omega>\<bar> \<le> \<bar>x $ i\<bar>"
        using good[of \<omega>] spM T0 unfolding G_def by (simp add: min_absorb1)
    qed
    show "?A 0 \<omega> = 0" if "\<omega> \<in> space (restrict_space Q G)" for \<omega>
      using good[of \<omega>] that spM T0 unfolding G_def by (simp add: min_absorb1)
    show "\<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow> 0 \<le> ?A v \<omega> - ?A u \<omega> \<and> ?A v \<omega> - ?A u \<omega> \<le> L * (v - u)"
      if w: "\<omega> \<in> space (restrict_space Q G)" for \<omega>
    proof (intro allI impI)
      fix u v :: real assume uv: "0 \<le> u" "u \<le> v"
      let ?a = "min u T" and ?b = "min v T"
      have dq: "\<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
          \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L"
        using good[of \<omega>] w spM unfolding G_def by blast
      have ba: "?b - ?a \<le> v - u" using uv by (auto simp: min_def)
      show "0 \<le> ?A v \<omega> - ?A u \<omega> \<and> ?A v \<omega> - ?A u \<omega> \<le> L * (v - u)"
      proof (cases "?a < ?b")
        case False
        then have "?a = ?b" using uv by (auto simp: min_def)
        then show ?thesis using uv L by simp
      next
        case True
        have m: "(1 / (?b - ?a)) *\<^sub>R (snd (\<omega> ?b) - snd (\<omega> ?a)) \<in> sconstraint k L"
          by (rule dq[rule_format, OF _ True min.cobounded2]) (use uv T0 in simp)
        have d0: "0 \<le> (1 / (?b - ?a)) * (?A v \<omega> - ?A u \<omega>)"
          and dL: "(1 / (?b - ?a)) * (?A v \<omega> - ?A u \<omega>) \<le> L"
          using sconstraint_diag[OF m, of i] by simp_all
        have e: "?A v \<omega> - ?A u \<omega> = (?b - ?a) * ((1 / (?b - ?a)) * (?A v \<omega> - ?A u \<omega>))"
          using True by simp
        have y0: "0 \<le> ?A v \<omega> - ?A u \<omega>"
          by (subst e, rule mult_nonneg_nonneg[OF _ d0]) (use True in simp)
        have "?A v \<omega> - ?A u \<omega> \<le> (?b - ?a) * L"
          by (subst e, rule mult_left_mono[OF dL]) (use True in simp)
        also have "\<dots> \<le> (v - u) * L" by (rule mult_right_mono[OF ba L])
        finally show ?thesis using y0 by (simp add: mult.commute)
      qed
    qed
  qed (use L st stt in auto)
  \<comment> \<open>and the restriction to a full-measure event changes no integral\<close>
  moreover have "(\<integral>\<^sup>+\<omega>. ennreal ((?X tt \<omega> - ?X s \<omega>)^4) \<partial>restrict_space Q G)
      = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal ((?X tt \<omega> - ?X s \<omega>)^4) \<partial>restrict_space Q G)
        = (\<integral>\<^sup>+\<omega>. ennreal ((?X tt \<omega> - ?X s \<omega>)^4) * indicator G \<omega> \<partial>Q)"
      by (rule nn_integral_restrict_space[OF sets_restrict_full[OF RF]])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)"
    proof (rule nn_integral_cong_AE)
      have sT: "s \<le> T" using stt ttT by simp
      show "AE \<omega> in Q. ennreal ((?X tt \<omega> - ?X s \<omega>)^4) * indicator G \<omega>
          = ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
        using Gfull by eventually_elim (use sT ttT in \<open>simp add: min_absorb1\<close>)
    qed
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
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
  have c0: "0 \<le> c" unfolding c_def using pow4_nonneg by simp
  have d0: "0 \<le> d \<omega>" for \<omega> unfolding d_def by (rule pow4_nonneg)
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
  moments come from @{thm [source] exit_class_fourth_moment}, and \<open>c = Y\<^sub>i\<^sub>j\<close> is bounded
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
    using LT0 pow4_nonneg[of "x $ i"] by simp
  have pj0: "0 \<le> 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)"
    using LT0 pow4_nonneg[of "x $ j"] by simp
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
      by (simp add: pow4_nonneg)
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
    by (intro add_nonneg_nonneg mult_nonneg_nonneg pow4_nonneg) auto
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
