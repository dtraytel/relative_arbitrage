(*
  Title:   Paper_Bridge.thy
  Content: The bridge from the repo's market witnesses to the paper's
           class (1.7) of arXiv:2512.17702.

           Per the paper's (1.7)-(1.8) the processes in P_x are NEVER
           stopped: the covariation constraint holds for a.e. t >= 0 and
           tau_K is merely a functional of the path.  A `stopped_market'
           witness is therefore NOT a class member -- its volatility
           vanishes after its stopping time, and 0 is not admissible.
           The faithful bridge CONTINUES the witness past the stopping
           time with an admissible volatility; `Paper_Class.acont' does
           that, and `Paper_Class.mat_1_in_sconstraint' supplies the
           value (legitimate exactly because the locale carries the
           paper's standing assumption L >= 1).

           This theory sits downstream of BOTH Paper_Class and the
           market stack, so that neither has to import the other.

  STATUS:  PIDE-verified (359 commands, overall_status ok).  Since
           2026-08-05 the volatility side of the bridge is HYPOTHESIS-FREE:
           the time-measurability of `acov' that the two integrability
           results used to assume is now a locale assumption
           (`acov_time_measurable', on {0..}), transported to the
           continuation by `Paper_Class.acont_set_borel_measurable'.

           HISTORY: registering this NEW theory in ROOT wedged the
           running PIDE session -- the server snapshots ROOT at startup,
           so afterwards every theory reported "Malformed theory", and
           reverting the ROOT edit did NOT recover it.  A restart was
           required.  To add a theory mid-session, prefer adding an
           import to an existing theory instead.
*)

theory Paper_Bridge
  imports Paper_Class Section_2_Usc
    "Levy_Prokhorov_Metric.Space_of_Finite_Measures"
begin

section \<open>Extracting the pointwise constraint from a market witness\<close>

text \<open>The locale's volatility hypotheses are stated as three separate
  almost-sure facts, each valid only up to the stopping time.  Combined
  and continued they give a single almost-sure statement holding for ALL
  times, which is the shape \<open>paper_pair_class\<close> asks for.\<close>

theorem stopped_market_acont_in_sconstraint:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
  shows "AE \<omega> in M. \<forall>s. 0 \<le> s
      \<longrightarrow> acont (\<lambda>u. acov u \<omega>) (tau \<omega>) s \<in> sconstraint k L"
proof -
  from SM have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    unfolding stopped_market_def by blast
  interpret SV: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have L1: "1 \<le> L" by (rule SV.L_ge)
  show ?thesis
    using SV.acov_psd SV.acov_eigen_lb SV.acov_eigen_ub
  proof eventually_elim
    case (elim \<omega>)
    then have pd: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> psd (acov u \<omega>)"
      and lb: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega>
          \<Longrightarrow> eigen_lb (acov u \<omega>) (CARD('n) - k)"
      and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
      by blast+
    \<comment> \<open>\<open>pd\<close>, not \<open>psd\<close>: naming a local fact after the constant \<open>psd\<close>
        is legal (facts and constants live in separate namespaces) but
        invites misreading in the \<open>unfolding\<close> step just below.\<close>
    have sv: "acov u \<omega> \<in> suff_volatile k" if "0 \<le> u" "u \<le> tau \<omega>" for u
      unfolding suff_volatile_def using pd[OF that] lb[OF that] by simp
    show ?case
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s"
      show "acont (\<lambda>u. acov u \<omega>) (tau \<omega>) s \<in> sconstraint k L"
        by (rule acont_in_sconstraint[OF L1 sv ub s])
    qed
  qed
qed

text \<open>In particular the continued volatility of a market witness never
  leaves the constraint set, whereas the witness's own volatility does the
  moment it is stopped -- which is precisely the mismatch this theory
  exists to repair.\<close>

section \<open>Integrability of the continued volatility\<close>

text \<open>To build the running covariation \<open>Yint\<close> from a witness the continued
  volatility must be INTEGRABLE on bounded intervals.  Boundedness is free:
  on \<open>[0, tau \<omega>]\<close> the locale's \<open>psd\<close> + \<open>eigen_ub L\<close> bound every entry by \<open>L\<close>
  (via \<open>sconstraint_norm_le\<close>), and after \<open>tau \<omega>\<close> the continuation is the
  constant \<open>mat 1\<close>.  What the locale does NOT supply is MEASURABILITY of
  \<open>acov\<close> in the TIME variable: \<open>acov_trace_integrable\<close> covers only the
  trace, and \<open>coord_Z\<close> only the diagonal entries.

  That gap is now CLOSED IN THE LOCALE: \<open>sufficiently_volatile_market\<close>
  carries \<open>acov_time_measurable\<close>, stated on the nonnegative axis, which is
  faithful rather than a strengthening --- the paper's (1.7) constrains
  \<open>d\<langle>X\<^sub>i,X\<^sub>j\<rangle>(t)/dt\<close>, and that presupposes the covariation density exists
  as a measurable object in \<open>t\<close>.  So the theorem below no longer carries a
  measurability hypothesis; \<open>Paper_Class.acont_set_borel_measurable\<close>
  transports the locale's fact to the continuation, and
  \<open>set_borel_measurable_subset\<close> cuts it down to the interval at hand
  (legitimately, since \<open>0 \<le> s\<close> puts \<open>{s..t}\<close> inside \<open>{0..}\<close>).\<close>

lemma acont_bounded:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes L1: "1 \<le> L"
    and sv: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> acov u \<omega> \<in> suff_volatile k"
    and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tv \<Longrightarrow> eigen_ub (acov u \<omega>) L"
    and u: "0 \<le> u"
  shows "norm (acont (\<lambda>r. acov r \<omega>) tv u) \<le> real CARD('n) * L"
proof (rule sconstraint_norm_le)
  show "0 \<le> L" using L1 by simp
  show "acont (\<lambda>r. acov r \<omega>) tv u \<in> sconstraint k L"
    by (rule acont_in_sconstraint[OF L1 sv ub u])
qed

theorem stopped_market_acont_integrable:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
    and st: "0 \<le> s" "s \<le> t"
  shows "AE \<omega> in M.
      set_integrable lborel {s..t} (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)"
proof -
  from SM have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    unfolding stopped_market_def by blast
  interpret SV: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have L1: "1 \<le> L" by (rule SV.L_ge)
  have Bnn: "0 \<le> real CARD('n) * L" using L1 by simp
  show ?thesis
    using SV.acov_psd SV.acov_eigen_lb SV.acov_eigen_ub
      SV.acov_time_measurable
  proof eventually_elim
    case (elim \<omega>)
    then have pd: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> psd (acov u \<omega>)"
      and lb: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega>
          \<Longrightarrow> eigen_lb (acov u \<omega>) (CARD('n) - k)"
      and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
      and m0: "set_borel_measurable lborel {0..} (\<lambda>r. acov r \<omega>)"
      by blast+
    have m: "set_borel_measurable lborel {s..t}
        (acont (\<lambda>r. acov r \<omega>) (tau \<omega>))"
    proof (rule set_borel_measurable_subset)
      show "set_borel_measurable lborel {0..}
          (acont (\<lambda>r. acov r \<omega>) (tau \<omega>))"
        by (rule acont_set_borel_measurable[OF m0])
      show "{s..t} \<in> sets lborel" by simp
      show "{s..t} \<subseteq> {0..}" using st(1) by auto
    qed
    have sv: "acov u \<omega> \<in> suff_volatile k" if "0 \<le> u" "u \<le> tau \<omega>" for u
      unfolding suff_volatile_def using pd[OF that] lb[OF that] by simp
    \<comment> \<open>the conclusion must drive the unification here: an \<^verbatim>\<open>OF\<close> chain on
        \<^verbatim>\<open>acont_bounded\<close> reports "multiple unifiers".\<close>
    have bnd: "norm (acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u) \<le> real CARD('n) * L"
      if u0: "0 \<le> u" for u
    proof (rule acont_bounded)
      show "1 \<le> L" by (rule L1)
      show "\<And>v. 0 \<le> v \<Longrightarrow> v \<le> tau \<omega> \<Longrightarrow> acov v \<omega> \<in> suff_volatile k"
        by (rule sv)
      show "\<And>v. 0 \<le> v \<Longrightarrow> v \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov v \<omega>) L"
        by (rule ub)
      show "0 \<le> u" by (rule u0)
    qed
    have dom: "integrable lborel
        (\<lambda>u. indicat_real {s..t} u * (real CARD('n) * L))"
    proof -
      have "integrable lborel (indicat_real {s..t})"
        by (rule integrable_real_indicator)
          (use st in \<open>auto\<close>)
      then show ?thesis by simp
    qed
    show ?case
      unfolding set_integrable_def
    \<comment> \<open>\<^verbatim>\<open>Bochner_Integration.\<close> is required: the bare name resolves to the
        Henstock lemma about \<^verbatim>\<open>integrable_on cbox\<close>, exactly as for
        \<^verbatim>\<open>integrable_const\<close>.\<close>
    proof (rule Bochner_Integration.integrable_bound[OF dom])
      show "(\<lambda>u. indicat_real {s..t} u *\<^sub>R acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
          \<in> borel_measurable lborel"
        using m unfolding set_borel_measurable_def by simp
      show "AE u in lborel.
          norm (indicat_real {s..t} u *\<^sub>R acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
          \<le> norm (indicat_real {s..t} u * (real CARD('n) * L))"
      proof (intro AE_I2)
        fix u :: real
        show "norm (indicat_real {s..t} u *\<^sub>R acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)
            \<le> norm (indicat_real {s..t} u * (real CARD('n) * L))"
        proof (cases "u \<in> {s..t}")
          case True
          then have u0: "0 \<le> u" using st by simp
          show ?thesis using bnd[OF u0] True Bnn by simp
        next
          case False
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

section \<open>The witness satisfies the class's covariation condition\<close>

text \<open>The payoff of the volatility side of the bridge.  For a market
  witness, the CONTINUED running covariation \<open>Yint (acont \<dots>)\<close> has all its
  difference quotients in the constraint set, almost surely — which is
  verbatim the covariation clause of \<open>paper_pair_class\<close>, with no stopping
  caveat, exactly as (1.7) requires.  The witness's OWN covariation does
  not have this property (\<open>stopped_market_acov_leaves_sconstraint\<close>); the
  continuation is what repairs it, and by (1.8) it costs nothing, since
  \<open>\<tau>\<^sub>K\<close> only sees the path up to the first exit from \<open>K\<close>.\<close>

theorem stopped_market_Yint_diffquot_in_sconstraint:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
    and st: "0 \<le> s" "s < t"
  shows "AE \<omega> in M.
      (1 / (t - s)) *\<^sub>R (Yint (acont (\<lambda>r. acov r \<omega>) (tau \<omega>)) t
          - Yint (acont (\<lambda>r. acov r \<omega>) (tau \<omega>)) s) \<in> sconstraint k L"
proof -
  from SM have svm: "sufficiently_volatile_market M F X acov k L K x0 tau"
    unfolding stopped_market_def by blast
  interpret SV: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule svm)
  have L1: "1 \<le> L" by (rule SV.L_ge)
  have i1: "AE \<omega> in M.
      set_integrable lborel {0..s} (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)"
    by (rule stopped_market_acont_integrable[OF SM]) (use st in auto)
  have i2: "AE \<omega> in M.
      set_integrable lborel {s..t} (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)"
    using st by (intro stopped_market_acont_integrable[OF SM]) auto
  show ?thesis
    using SV.acov_psd SV.acov_eigen_lb SV.acov_eigen_ub i1 i2
  proof eventually_elim
    case (elim \<omega>)
    then have pd: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> psd (acov u \<omega>)"
      and lb: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega>
          \<Longrightarrow> eigen_lb (acov u \<omega>) (CARD('n) - k)"
      and ub: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
      and j1: "set_integrable lborel {0..s} (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)"
      and j2: "set_integrable lborel {s..t} (\<lambda>u. acont (\<lambda>r. acov r \<omega>) (tau \<omega>) u)"
      by blast+
    have sv: "acov u \<omega> \<in> suff_volatile k" if "0 \<le> u" "u \<le> tau \<omega>" for u
      unfolding suff_volatile_def using pd[OF that] lb[OF that] by simp
    show ?case
    proof (rule Yint_diffquot_in_sconstraint)
      show "1 \<le> L" by (rule L1)
      show "0 \<le> s" by (rule st(1))
      show "s < t" by (rule st(2))
      show "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> acov u \<omega> \<in> suff_volatile k"
        by (rule sv)
      show "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> tau \<omega> \<Longrightarrow> eigen_ub (acov u \<omega>) L"
        by (rule ub)
      show "set_integrable lborel {0..s} (acont (\<lambda>r. acov r \<omega>) (tau \<omega>))"
        by (rule j1)
      show "set_integrable lborel {s..t} (acont (\<lambda>r. acov r \<omega>) (tau \<omega>))"
        by (rule j2)
    qed
  qed
qed

corollary stopped_market_acov_leaves_sconstraint:
  fixes acov :: "real \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real^'n::finite^'n"
  assumes SM: "stopped_market k L K x0 M F X acov tau"
    and s: "\<omega> \<in> space M" "tau \<omega> < s"
  shows "acov s \<omega> = 0"
  using SM s unfolding stopped_market_def by blast

section \<open>NC-3: the martingale clauses of Lemma 2.3\<close>

text \<open>This section needs BOTH sides of the development --- the paper class
  from \<open>Paper_Class\<close> and the Section-2 law machinery from \<open>Section_2_Usc\<close>
  (\<open>martingale_bounded_test\<close>, \<open>metric_measure_eqI_bounded_cts\<close>) --- which is
  why it lives here rather than in \<open>Paper_Class\<close>.

  The two clauses of (1.7) that are CLOSED conditions on a single path
  already pass to a weak limit (\<open>Paper_Class.paper_pair_class_start_limit\<close>,
  \<open>\<dots>_diffquot_limit\<close>).  The martingale clauses are not of that kind: they
  are statements about integrals against past-measurable test functions, and
  only BOUNDED CONTINUOUS tests survive a weak limit.  So the route is
  (i) state the identity at a class member against a bounded continuous
  test, (ii) pass it through the weak limit using the uniform \<open>L\<^sup>2\<close> bound,
  (iii) upgrade from continuous tests to past events, (iv) reassemble a
  martingale through the set-integral characterisation.

  Step (i) needs the test function to be measurable for the NATURAL
  FILTRATION of the coordinate process, while it is naturally a function of
  the RESTRICTED path.  The two agree, and the non-trivial inclusion ---
  \<open>\<sigma>(restriction) \<subseteq> \<F>\<^sub>s\<close> --- is exactly what
  \<open>Path_Space.pathify_measurable\<close> proves: the restriction map is the
  "path map" of the coordinate process on \<open>{0..s}\<close>, and that theorem reduces
  a ball of the path metric to countably many evaluation conditions.\<close>

subsection \<open>The restriction map is measurable for the natural filtration\<close>

lemma restrict_measurable_natural_filtration:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>\<omega>. restrict \<omega> {0..s})
      \<in> natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric s :: ('n pairpath) metric))"
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
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and h: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric s :: ('n pairpath) metric)))"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}))
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  by (rule measurable_compose
      [OF restrict_measurable_natural_filtration[OF setsQ s sT] h])

subsection \<open>The identity at a class member, against a bounded test\<close>

lemma paper_pair_class_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  using Q unfolding paper_pair_class_def by blast

lemma paper_pair_class_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)"
  by (rule martingale_vec_nth[OF paper_pair_class_X_martingale[OF Q]])

theorem paper_pair_class_martingale_test:
  fixes Q :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes Q: "Q \<in> paper_pair_class k L T x"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hm: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric s :: ('n pairpath) metric)))"
    and hb: "\<And>g. \<bar>h g\<bar> \<le> B"
  shows "(\<integral>\<omega>. h (restrict \<omega> {0..s}) * (fst (\<omega> t) $ i - fst (\<omega> s) $ i) \<partial>Q) = 0"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)"
  \<comment> \<open>the class's martingale clause STOPS the process at \<open>T\<close> (it must ---
      see the note at \<open>paper_pair_class\<close>), and on \<open>[0,T]\<close> the stopping is
      invisible, which is what the two \<open>min\<close> rewrites below record.\<close>
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ i"
  let ?Z = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s})"
  have sT: "s \<le> T" using ts tT by simp
  have t0: "0 \<le> t" using st ts by simp
  have mt: "min t T = t" using tT by simp
  have ms: "min s T = s" using sT by simp
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have MY: "martingale Q ?F 0 ?Y" by (rule paper_pair_class_coord_martingale[OF Q])
  then interpret MY: martingale Q ?F 0 ?Y .
  have Zm: "?Z \<in> borel_measurable (?F s)"
    by (rule past_test_measurable_natural_filtration
        [OF paper_pair_class_sets[OF Q] st sT hm])
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

text \<open>What weak convergence sees.  Unlike the confined market laws of
  \<open>Section_2_Usc\<close>, the paper's class admits no clamp --- its processes are
  neither stopped nor bounded --- so the test functional is CONTINUOUS but
  UNBOUNDED, and the transfer runs through the uniform \<open>L\<^sup>2\<close> bound
  (\<open>Paper_Class.paper_pair_class_sq_mean_le\<close>) rather than through
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

text \<open>The transfer theorem \<open>weak_conv_integral_of_L2_bound\<close> asks for a
  battery of integrability facts under EVERY approximating law and under
  the limit.  All of them follow from one input: a bound on the second
  moment of the coordinate, which the members have by
  \<open>paper_pair_class_sq_mean_le\<close> and which the limit inherits because
  \<open>\<omega> \<mapsto> (X\<^sub>u $ i)\<^sup>2\<close> is continuous and nonnegative
  (\<open>Path_Space.weak_conv_on_nn_integral_le\<close>).  So this subsection works with
  a bare "pair law with an \<open>L\<^sup>2\<close> bound" and never mentions the class.\<close>

lemma integrable_of_sq_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes fm: "finite_measure N" and m: "f \<in> borel_measurable N"
    and sq: "integrable N (\<lambda>\<omega>. (f \<omega>)\<^sup>2)"
  shows "integrable N f"
proof (rule Bochner_Integration.integrable_bound)
  show "integrable N (\<lambda>\<omega>. 1 + (f \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add
        finite_measure.integrable_const[OF fm] sq)
  show "f \<in> borel_measurable N" by (rule m)
  show "AE \<omega> in N. norm (f \<omega>) \<le> norm (1 + (f \<omega>)\<^sup>2)"
  proof (intro AE_I2)
    fix \<omega>
    have nn: "(0::real) \<le> (1 - \<bar>f \<omega>\<bar>)\<^sup>2" by simp
    have exp: "(1 - \<bar>f \<omega>\<bar>)\<^sup>2 = 1 - 2 * \<bar>f \<omega>\<bar> + (f \<omega>)\<^sup>2"
      by (simp add: power2_diff)
    have "\<bar>f \<omega>\<bar> \<le> 1 + (f \<omega>)\<^sup>2"
      using nn abs_ge_zero[of "f \<omega>"] unfolding exp by linarith
    then show "norm (f \<omega>) \<le> norm (1 + (f \<omega>)\<^sup>2)" by simp
  qed
qed

lemma pair_law_coord_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. fst (\<omega> u) $ i) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) $ i)
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_coord_cont[OF u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_coord_sq_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> u) $ i)\<^sup>2)
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_coord_sq_cont[OF u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_sq_integrable_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
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
  assumes setsN: "sets N = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
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

text \<open>\<open>weak_conv_integral_of_L2_bound\<close> asks, besides the \<open>L\<^sup>2\<close> bound
  itself, for integrability of the CLAMPED and of the TAIL-TRUNCATED
  integrand under every law involved.  Neither depends on the path space:
  a clamp is bounded, and a tail truncation is dominated by \<open>\<bar>f\<bar>\<close>.\<close>

lemma bounded_measurable_integrable:
  fixes g :: "'a \<Rightarrow> real"
  assumes P: "finite_measure N" and m: "g \<in> borel_measurable N"
    and b: "\<And>w. \<bar>g w\<bar> \<le> D"
  shows "integrable N g"
  by (rule finite_measure.integrable_const_bound[OF P _ m]) (use b in auto)

lemma clamp_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "finite_measure N" and m: "f \<in> borel_measurable N"
  shows "integrable N (\<lambda>w. max (- R) (min R (f w)))"
proof (rule bounded_measurable_integrable[OF P])
  show "(\<lambda>w. max (- R) (min R (f w))) \<in> borel_measurable N"
    using m by measurable
  show "\<And>w. \<bar>max (- R) (min R (f w))\<bar> \<le> \<bar>R\<bar>" by auto
qed

lemma tail_indicator_measurable:
  fixes f :: "'a \<Rightarrow> real"
  assumes m: "f \<in> borel_measurable N"
  shows "(\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w)) \<in> borel_measurable N"
proof -
  have os: "open {z::real. R < \<bar>z\<bar>}"
    by (intro open_Collect_less continuous_intros)
  have "{z::real. R < \<bar>z\<bar>} \<in> sets borel" by (rule borel_open[OF os])
  note this[measurable] m[measurable]
  show ?thesis by measurable
qed

lemma tail_integrable:
  fixes f :: "'a \<Rightarrow> real"
  assumes int: "integrable N f"
  shows "integrable N (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
proof (rule Bochner_Integration.integrable_bound
    [OF Bochner_Integration.integrable_abs[OF int]])
  show "(\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w)) \<in> borel_measurable N"
    by (rule tail_indicator_measurable[OF borel_measurable_integrable[OF int]])
  show "AE w in N. norm (\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w)) \<le> norm \<bar>f w\<bar>"
    by (intro AE_I2) (auto simp: indicator_def)
qed

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
  assumes setsN: "sets N = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
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
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable
      [OF pair_test_functional_cont[OF st sT tI hc, of i]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_test_sq_bound:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
    \<comment> \<open>\<open>2(a²+b²) − (a−b)² = (a+b)² \<ge> 0\<close>: stated as an EQUATION between
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
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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

lemma paper_pair_class_sq_nn_bound:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q)
      \<le> ennreal ((x $ i)\<^sup>2 + real CARD('n) * L * T)"
  by (rule pair_law_coord_sq_nn_bound[OF paper_pair_class_sets[OF Q] u
        paper_pair_class_sq_integrable[OF T L Q u]
        paper_pair_class_sq_mean_le[OF T L Q u]])

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

theorem paper_pair_class_martingale_test_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
  have Pm: "prob_space (Qm m)" for m by (rule paper_pair_class_prob[OF mem])
  have fmm: "finite_measure (Qm m)" for m
    using Pm by (simp add: prob_space_def)
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have setsm: "sets (Qm m) = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" for m
    by (rule paper_pair_class_sets[OF mem])
  have nnm: "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>(Qm m)) \<le> ennreal ?C"
    if u: "u \<in> {0..T}" for u m
    by (rule paper_pair_class_sq_nn_bound[OF T L mem u])
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
  have hm: "h \<in> borel_measurable (borel_of (mtopology_of
      (path_metric s :: ('n pairpath) metric)))"
    using continuous_map_measurable[OF hc] by (simp add: borel_of_euclidean)
  have zero: "(\<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) = 0" for m
    by (rule paper_pair_class_martingale_test[OF mem st ts tT hm hb])
  have z: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> 0" using zero by simp
  show ?thesis by (rule tendsto_unique[OF _ lim z]) simp
qed

subsection \<open>From continuous tests to past events\<close>

text \<open>The monotone-class step, in the form the paper's class needs.  Split
  the increment into positive and negative parts, push each forward through
  the restriction map as a DENSITY, and observe that the limit identity says
  exactly that the two image measures integrate every bounded continuous
  function alike.  \<open>Section_2_Usc.metric_measure_eqI_bounded_cts\<close> then makes
  the two measures EQUAL, so they agree on every past event.

  One wrinkle: that engine supplies tests bounded only on the TOPSPACE,
  whereas \<open>paper_pair_class_martingale_test_limit\<close> asks for a global bound.
  Composing with \<open>rclamp\<close> repairs it --- the clamp is invisible where the
  bound already holds, hence on the whole space of the measures involved.\<close>

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

lemma paper_pair_class_limit_sq_nn:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)\<^sup>2) \<partial>Q)
      \<le> ennreal ((x $ i)\<^sup>2 + real CARD('n) * L * T)"
proof -
  have C0: "0 \<le> (x $ i)\<^sup>2 + real CARD('n) * L * T" using L T by simp
  show ?thesis
    by (rule pair_law_limit_sq_nn_bound[OF wc u C0
          paper_pair_class_sq_nn_bound[OF T L mem u]])
qed

lemma paper_pair_class_limit_increment_integrable:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
          paper_pair_class_limit_sq_nn[OF T L mem wc sI]
          paper_pair_class_limit_sq_nn[OF T L mem wc tI]])
  then show ?thesis by simp
qed

theorem paper_pair_class_martingale_event_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and Bs: "Bs \<in> sets (borel_of (mtopology_of
        (path_metric s :: ('n pairpath) metric)))"
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
    by (rule paper_pair_class_limit_increment_integrable
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
        (use cmp wm w0 in \<open>auto simp: mult.commute intro!: AE_I2\<close>)
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
      by (rule paper_pair_class_martingale_test_limit
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
            \<open>auto intro!: AE_I2 borel_measurable_times
              simp: abs_mult mult_right_mono\<close>)
      show "integrable Q (\<lambda>\<omega>. ?u (?p \<omega>) * gm \<omega>)"
        by (rule Bochner_Integration.integrable_bound
            [OF integrable_mult_right[OF gmi, of B'] _ ])
          (use cmp gmm ubd gm0 B'0 in
            \<open>auto intro!: AE_I2 borel_measurable_times
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
          \<open>auto intro!: AE_I2 borel_measurable_times simp: indicator_def\<close>)
    show "integrable Q (\<lambda>\<omega>. indicat_real Bs (?p \<omega>) * gm \<omega>)"
      by (rule Bochner_Integration.integrable_bound[OF gmi _])
        (use cmp gmm gm0 in
          \<open>auto intro!: AE_I2 borel_measurable_times simp: indicator_def\<close>)
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

text \<open>The converse of \<open>restrict_measurable_natural_filtration\<close>, and the
  EASY direction: for \<open>u \<le> s\<close> the evaluation \<open>\<omega> \<mapsto> \<omega> u\<close> factors through the
  restriction as \<open>ev\<^sub>u \<circ> restrict\<close>, and \<open>ev\<^sub>u\<close> is continuous on the
  \<open>s\<close>-path space.  So every event of \<open>\<FF>\<^sub>s\<close> IS a past event --- which is
  what turns \<open>paper_pair_class_martingale_event_limit\<close> into the
  set-integral hypothesis of \<open>martingale_of_set_integral_eq\<close>.\<close>

lemma pair_law_eval_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "(\<lambda>\<omega>. \<omega> u) \<in> borel_measurable N"
proof (cases "u \<in> {0..T}")
  case True
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> u)
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF continuous_map_path_eval[OF True]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
next
  case False
  \<comment> \<open>off the horizon the coordinate is the CONSTANT \<open>undefined\<close>: points of
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
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and A: "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  obtains Bs where
    "Bs \<in> sets (borel_of (mtopology_of
        (path_metric s :: ('n pairpath) metric)))"
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

subsection \<open>Step (iv): the limit law's process is a martingale\<close>

text \<open>The reassembly.  \<open>martingale_of_set_integral_eq\<close> is the right
  interface, because what the weak limit produced in step (iii) IS a
  set-integral identity: every event of \<open>\<FF>\<^sub>s\<close> is a past event
  (\<open>natural_filtration_eq_restrict_vimage\<close>), so the indicator of \<open>A\<close> is
  the indicator of a Borel set of restricted paths.  The two-case split is
  on \<open>u \<le> T\<close>: beyond the horizon the stopped process no longer moves and
  the identity is trivial.\<close>

lemma fst_coord_borel:
  "(\<lambda>p :: (real^'n::finite) \<times> (real^'n^'n). fst p $ i) \<in> borel_measurable borel"
proof -
  have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show ?thesis by (rule measurable_compose[OF f borel_measurable_nth])
qed

theorem paper_pair_class_coord_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ i"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  \<comment> \<open>\<open>stochastic_process\<close> is SHADOWED by Kolmogorov_Chentsov's homonym;
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
            paper_pair_class_limit_sq_nn[OF T L mem wc mI[OF u]]])
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
      obtain Bs where Bs: "Bs \<in> sets (borel_of (mtopology_of
            (path_metric u :: ('n pairpath) metric)))"
        and Aeq: "A = (\<lambda>\<omega>. restrict \<omega> {0..u}) -` Bs \<inter> space Q"
        using natural_filtration_eq_restrict_vimage[OF setsQ uv(1) True A]
        by blast
      have ind: "indicat_real A \<omega> = indicat_real Bs (restrict \<omega> {0..u})"
        if "\<omega> \<in> space Q" for \<omega> using Aeq that by (simp add: indicator_def)
      have zero: "(\<integral>\<omega>. indicat_real Bs (restrict \<omega> {0..u})
          * (fst (\<omega> (min v T)) $ i - fst (\<omega> u) $ i) \<partial>Q) = 0"
        by (rule paper_pair_class_martingale_event_limit
            [OF T L mem wc prob setsQ uv(1) ut tT Bs])
      have mR: "(\<lambda>\<omega> :: 'n pairpath. indicat_real Bs (restrict \<omega> {0..u})
            * (fst (\<omega> (min v T)) $ i - fst (\<omega> u) $ i)) \<in> borel_measurable Q"
      proof -
        have rm: "(\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..u}) \<in> Q \<rightarrow>\<^sub>M
            borel_of (mtopology_of (path_metric u :: ('n pairpath) metric))"
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

corollary paper_pair_class_X_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  by (rule martingale_vecI)
    (rule paper_pair_class_coord_martingale_limit[OF T L mem wc prob setsQ])

subsection \<open>Lemma 2.3: three of the four clauses, at the limit\<close>

text \<open>Where the closedness half of Lemma 2.3 stands.  A weak limit of
  class members satisfies the START clause, the COVARIATION clause and the
  \<open>X\<close>-MARTINGALE clause of (1.7); what is missing for
  \<open>Q \<in> paper_pair_class k L T x\<close> is exactly the compensated clause
  \<open>outerp X - Y\<close>, and only because carrying IT through the weak limit needs
  an \<open>L\<^sup>2\<close> bound on \<open>X\<^sub>i X\<^sub>j\<close>, i.e. a uniform FOURTH moment.  That is the
  same bound NC-2's tightness needs, and it is the one thing this route
  does not yet supply --- the paper gets it from Burkholder--Davis--Gundy,
  which the AFP does not have.  Stating the partial conclusion explicitly
  keeps the gap honest and machine-checked.\<close>

theorem paper_pair_class_limit_three_clauses:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    and "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    and "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
proof -
  show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule paper_pair_class_start_limit[OF T mem wc prob setsQ])
  show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule paper_pair_class_diffquot_limit[OF mem wc prob setsQ])
  show "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
    by (rule paper_pair_class_X_martingale_limit[OF T L mem wc prob setsQ])
qed

section \<open>The uniform fourth moment of the class, by localization\<close>

text \<open>The bound that unblocks BOTH the compensated clause of Lemma 2.3 and
  NC-2's tightness.  The repo's estimate
  \<open>Increment_Moments.fourth_moment_bound_bounded\<close> wants a UNIFORM SUP BOUND
  on the process, which a class member does not have --- and that bound is
  structural there, not incidental (it also fixes the constant of
  \<open>remainder_tendsto_zero\<close>), so generalising the estimate is the wrong
  move.  The process STOPPED at \<open>\<tau>\<^sub>R = inf {t. R \<le> \<bar>X\<^sub>t\<bar>}\<close> does have a sup
  bound, by construction.  Applying the estimate there gives a bound
  UNIFORM IN \<open>R\<close>; path continuity on the compact \<open>[0,T]\<close> makes
  \<open>\<tau>\<^sub>R > T\<close> for large \<open>R\<close> pathwise, so Fatou removes the localization.  No
  Burkholder--Davis--Gundy anywhere.

  Everything the argument needs is already in the repo:
  \<open>Exit_Time.etime_stopping_time\<close> for \<open>\<tau>\<^sub>R\<close>,
  \<open>Doob_Inequality.horizon_sq_int_martingale\<close> for the integrable envelope
  that \<open>Optional_Sampling.optional_stopping\<close> asks for, and
  \<open>optional_stopping\<close> itself.\<close>

subsection \<open>The coordinate process, its compensator, and its paths\<close>

lemma paper_pair_class_coord_adapted:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "adapted_process Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i)"
proof -
  interpret MG: martingale Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T)) $ i"
    by (rule paper_pair_class_coord_martingale[OF Q])
  show ?thesis by unfold_locales
qed

text \<open>Continuity holds on the WHOLE half-line, not just on \<open>{0..T}\<close>: the
  stopped process is constant after the horizon.  That is the form
  \<open>Stopped_Adaptedness.stopped_adapted_of_cont\<close> asks for.\<close>

lemma paper_pair_class_path_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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

lemma paper_pair_class_coord_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)) $ i)"
proof -
  have c2: "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)))"
    by (rule continuous_on_fst[OF paper_pair_class_path_cont[OF T setsQ w]])
  have c3: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)"
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  show ?thesis by (rule continuous_on_compose2[OF c3 c2]) simp
qed

lemma paper_pair_class_comp_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..}
      (\<lambda>s. (fst (\<omega> (min s T)) $ i)\<^sup>2 - snd (\<omega> (min s T)) $ i $ i)"
proof -
  have cx: "continuous_on {0..} (\<lambda>s. fst (\<omega> (min s T)) $ i)"
    by (rule paper_pair_class_coord_paths_cont[OF T setsQ w])
  have c2: "continuous_on {0..} (\<lambda>s. snd (\<omega> (min s T)))"
    by (rule continuous_on_snd[OF paper_pair_class_path_cont[OF T setsQ w]])
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

lemma paper_pair_class_compensated_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. (fst (\<omega> (min u T)) $ i)\<^sup>2 - snd (\<omega> (min u T)) $ i $ i)"
proof -
  have mg: "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ i $ i)"
    by (rule martingale_mat_nth
        [OF paper_pair_class_compensated_martingale[OF Q]])
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
  \<open>Exit_Time.etime_stopping_time\<close> --- the set \<open>{y. R \<le> \<bar>y\<bar>}\<close> is closed and
  nonempty and the paths are continuous --- and the process stopped at it
  is bounded, which is the whole point.\<close>

definition pcoord :: "real \<Rightarrow> 'n::finite \<Rightarrow> real \<Rightarrow> ('n pairpath) \<Rightarrow> real"
  where "pcoord T i u \<omega> = fst (\<omega> (min u T)) $ i"

definition ploc :: "real \<Rightarrow> 'n::finite \<Rightarrow> real \<Rightarrow> ('n pairpath) \<Rightarrow> real"
  where "ploc T i R \<omega> = etime T {y. R \<le> \<bar>y\<bar>} (pcoord T i) \<omega>"

lemma closed_abs_ge: "closed {y :: real. R \<le> \<bar>y\<bar>}"
  by (intro closed_Collect_le continuous_intros)

lemma abs_ge_nonempty: "{y :: real. R \<le> \<bar>y\<bar>} \<noteq> {}"
  by (rule notI) (use abs_ge_self[of R] in blast)

lemma ploc_nonneg: "0 \<le> T \<Longrightarrow> 0 \<le> ploc T i R \<omega>"
  unfolding ploc_def by (rule etime_nonneg)

lemma ploc_le_T: "0 \<le> T \<Longrightarrow> ploc T i R \<omega> \<le> T"
  unfolding ploc_def by (rule etime_le_T)

lemma paper_pair_class_cont_adapted:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "cont_adapted_process Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u))
      (pcoord T i) T"
proof (intro cont_adapted_process.intro cont_adapted_process_axioms.intro)
  show "adapted_process Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (pcoord T i)"
    unfolding pcoord_def by (rule paper_pair_class_coord_adapted[OF Q])
  show "0 \<le> T" by (rule T)
  show "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> continuous_on {0..T} (\<lambda>s. pcoord T i s \<omega>)"
    unfolding pcoord_def
    by (rule continuous_on_subset
        [OF paper_pair_class_coord_paths_cont[OF T setsQ]]) auto
qed

lemma paper_pair_class_ploc_stopping:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
    and t: "0 \<le> t"
  shows "{\<omega> \<in> space Q. ploc T i R \<omega> \<le> t}
      \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) t)"
proof -
  interpret CA: cont_adapted_process Q "natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)"
      "pcoord T i" T
    by (rule paper_pair_class_cont_adapted[OF T setsQ Q])
  show ?thesis
    unfolding ploc_def
    by (rule CA.etime_stopping_time[OF closed_abs_ge abs_ge_nonempty t])
qed

text \<open>The point of the localization: below the level the stopped path has
  not yet reached \<open>R\<close>, and at the level it is exactly \<open>R\<close> by continuity, so
  the stopped process never exceeds \<open>R\<close> in absolute value --- except
  possibly at time \<open>0\<close>, where it is the starting coordinate.\<close>

text \<open>At the stopping time itself the path has value exactly \<open>R\<close>, not more,
  which is why the bound needs CONTINUITY and not just the definition of an
  infimum.  \<open>Exit_Time.etime_stays_in_cball\<close> is precisely that statement,
  and it is why the theory exists.\<close>

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

text \<open>\<open>Optional_Sampling.optional_stopping\<close> asks for an INTEGRABLE ENVELOPE
  of the unstopped process --- the one thing the market locale could not
  supply, and the reason the plan long recorded optional stopping as out of
  reach here.  For a class member it IS available:
  \<open>Doob_Inequality.horizon_sq_int_martingale\<close> builds \<open>Dsup\<close> from Doob's
  \<open>L\<^sup>2\<close> inequality out of nothing but square-integrability, which
  \<open>paper_pair_class_sq_integrable\<close> provides.\<close>

theorem paper_pair_class_stopped_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>v \<omega>. pcoord T i (min v (ploc T i R \<omega>)) \<omega>)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have mg: "martingale Q ?F 0 (pcoord T i)"
    unfolding pcoord_def by (rule paper_pair_class_coord_martingale[OF Q])
  have sq: "integrable Q (\<lambda>\<omega>. (pcoord T i s \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    unfolding pcoord_def
    using T0 s by (intro paper_pair_class_sq_integrable[OF T0 L Q]) simp
  have adp: "adapted_process Q ?F 0 (pcoord T i)"
    unfolding pcoord_def by (rule paper_pair_class_coord_adapted[OF Q])
  have cont0: "continuous_on {0..} (\<lambda>s. pcoord T i s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega>
    unfolding pcoord_def
    by (rule paper_pair_class_coord_paths_cont[OF T0 setsQ w])
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
      by (rule paper_pair_class_ploc_stopping[OF T0 setsQ Q])
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q. continuous_on {0..u} (\<lambda>s. pcoord T i s \<omega>)"
      by (intro AE_I2 contu)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q.
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
      by (rule domA)
    show "\<And>u. 0 < u \<Longrightarrow> integrable Q HM.Dsup" by (rule HM.Dsup_integrable)
    show "\<And>v. 0 \<le> v \<Longrightarrow> (\<lambda>\<omega>. pcoord T i (min v (ploc T i R \<omega>)) \<omega>)
        \<in> borel_measurable (?F v)"
      by (rule stopped_adapted_of_cont
          [OF adp lnn paper_pair_class_ploc_stopping[OF T0 setsQ Q] cont0])
  qed
qed

text \<open>The compensated process is stopped by the same argument.  Its
  envelope is \<open>Dsup\<^sup>2 + n\<sqdot>L\<sqdot>T\<close>: the squared coordinate is dominated by the
  square of Doob's envelope (\<open>Dsup_sq_integrable\<close>) and the compensator by
  the class's Lipschitz bound on \<open>Y\<close>.\<close>

theorem paper_pair_class_stopped_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>v \<omega>. (fst (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i)\<^sup>2
        - snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (fst (\<omega> (min u T)) $ i)\<^sup>2 - snd (\<omega> (min u T)) $ i $ i"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have mgZ: "martingale Q ?F 0 ?Z"
    by (rule paper_pair_class_compensated_coord_martingale[OF Q])
  have adpZ: "adapted_process Q ?F 0 ?Z"
  proof -
    interpret MZ: martingale Q ?F 0 ?Z by (rule mgZ)
    show ?thesis by unfold_locales
  qed
  have contZ: "continuous_on {0..} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space Q" for \<omega>
    by (rule paper_pair_class_comp_paths_cont[OF T0 setsQ w])
  have contZu: "continuous_on {0..u} (\<lambda>s. ?Z s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    by (rule continuous_on_subset[OF contZ[OF w]]) auto
  have lnn: "0 \<le> ploc T i R \<omega>" for \<omega> by (rule ploc_nonneg[OF T0])
  \<comment> \<open>the \<open>X\<close>-side envelope, from Doob, exactly as for the coordinate.\<close>
  have mg: "martingale Q ?F 0 (pcoord T i)"
    unfolding pcoord_def by (rule paper_pair_class_coord_martingale[OF Q])
  have sq: "integrable Q (\<lambda>\<omega>. (pcoord T i s \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    unfolding pcoord_def
    using T0 s by (intro paper_pair_class_sq_integrable[OF T0 L Q]) simp
  have contX: "continuous_on {0..u} (\<lambda>s. pcoord T i s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    unfolding pcoord_def
    by (rule continuous_on_subset
        [OF paper_pair_class_coord_paths_cont[OF T0 setsQ w]]) auto
  interpret HM: horizon_sq_int_martingale Q ?F "pcoord T i" T
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mg T prob sq)
  have domT: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>pcoord T i s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    by (rule HM.Dsup_dominates) (intro AE_I2 contX)
  \<comment> \<open>the \<open>Y\<close>-side envelope is the class's own Lipschitz bound.\<close>
  have ybnd: "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    by (rule paper_pair_class_Y_bounded_ae[OF T0 L Q])
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
      by (rule paper_pair_class_ploc_stopping[OF T0 setsQ Q])
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
          [OF adpZ lnn paper_pair_class_ploc_stopping[OF T0 setsQ Q] contZ])
  qed
qed

subsection \<open>The compensator rate at the stopped times\<close>

text \<open>Step (a) of the four that remain.  Stopping can only shrink an
  interval --- \<open>w \<mapsto> min w c\<close> is nondecreasing and 1-Lipschitz --- so the
  class's diagonal rate bound survives it verbatim.\<close>

lemma paper_pair_class_stopped_compensator_rate:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L" and Q: "Q \<in> paper_pair_class k L T x"
  shows "AE \<omega> in Q. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
      0 \<le> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
        - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i
      \<and> snd (\<omega> (min (min v (ploc T i R \<omega>)) T)) $ i $ i
        - snd (\<omega> (min (min u (ploc T i R \<omega>)) T)) $ i $ i \<le> L * (v - u)"
proof -
  have inc: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> t \<le> T \<longrightarrow>
      0 \<le> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i
      \<and> snd (\<omega> t) $ i $ i - snd (\<omega> s) $ i $ i \<le> L * (t - s)"
    by (rule paper_pair_class_Y_diag_increment[OF L Q])
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

text \<open>The pay-off of localizing: on the stopped process every moment is
  free.  The starting coordinate is \<open>x $ i\<close> almost surely, so the strict
  hypothesis of \<open>pcoord_stopped_bounded\<close> holds as soon as \<open>R\<close> exceeds it.\<close>

lemma paper_pair_class_stopped_abs_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
    and R: "0 < R" and xR: "\<bar>x $ i\<bar> < R" and w: "0 \<le> w"
  shows "AE \<omega> in Q. \<bar>pcoord T i (min w (ploc T i R \<omega>)) \<omega>\<bar> \<le> R"
proof -
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding paper_pair_class_def by blast
  from st AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have s0: "fst (\<omega> 0) = x" and mem: "\<omega> \<in> space Q" by blast+
    have p0: "pcoord T i 0 \<omega> = x $ i"
      unfolding pcoord_def using T s0 by simp
    have c: "continuous_on {0..T} (\<lambda>s. pcoord T i s \<omega>)"
      unfolding pcoord_def
      by (rule continuous_on_subset
          [OF paper_pair_class_coord_paths_cont[OF T setsQ mem]]) auto
    show ?case
      by (rule pcoord_stopped_bounded[OF T R _ c w]) (use p0 xR in simp)
  qed
qed

lemma paper_pair_class_stopped_A_abs_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and w: "0 \<le> w"
  shows "AE \<omega> in Q. \<bar>snd (\<omega> (min (min w (ploc T i R \<omega>)) T)) $ i $ i\<bar>
      \<le> real CARD('n) * L * T"
proof -
  have yb: "AE \<omega> in Q. \<forall>u\<in>{0..T}. norm (snd (\<omega> u)) \<le> real CARD('n) * L * T"
    by (rule paper_pair_class_Y_bounded_ae[OF T L Q])
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

subsection \<open>Step (b): the conditional identity for the stopped pair\<close>

text \<open>\<open>E[(\<Delta>X\<^sup>\<tau>)\<^sup>2 | \<F>\<^sub>u] = E[\<Delta>A\<^sup>\<tau> | \<F>\<^sub>u]\<close>, the last hypothesis of
  \<open>Increment_Moments.fourth_moment_bound_bounded\<close> that is not immediate.
  It is the usual expansion --- the cross term is pulled out because
  \<open>X\<^sup>\<tau>\<^sub>u\<close> is \<open>\<F>\<^sub>u\<close>-measurable, and the compensated martingale converts
  \<open>E[(X\<^sup>\<tau>\<^sub>v)\<^sup>2 | \<F>\<^sub>u]\<close> into \<open>(X\<^sup>\<tau>\<^sub>u)\<^sup>2 - A\<^sup>\<tau>\<^sub>u + E[A\<^sup>\<tau>\<^sub>v | \<F>\<^sub>u]\<close>.  Every
  integrability side condition is free, because the stopped pair is
  BOUNDED.\<close>

theorem paper_pair_class_stopped_cond_exp:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
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
  have prob: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  interpret MX: martingale Q ?F 0 ?X
    by (rule paper_pair_class_stopped_coord_martingale[OF T L setsQ Q])
  have mgZ: "martingale Q ?F 0 (\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>)"
    using paper_pair_class_stopped_comp_martingale[OF T L setsQ Q]
    unfolding pcoord_def by simp
  then interpret MZ: martingale Q ?F 0 "\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>" .
  interpret SFS: sigma_finite_subalgebra Q "?F u"
    by (rule MX.sigma_finite_subalgebra_F[OF uv(1)])
  \<comment> \<open>bounds and the integrability they buy\<close>
  have Xb: "AE \<omega> in Q. \<bar>?X w \<omega>\<bar> \<le> R" if w: "0 \<le> w" for w
    by (rule paper_pair_class_stopped_abs_le[OF T0 setsQ Q R xR w])
  have Ab: "AE \<omega> in Q. \<bar>?A w \<omega>\<bar> \<le> real CARD('n) * L * T" if w: "0 \<le> w" for w
    by (rule paper_pair_class_stopped_A_abs_le[OF T0 L Q w])
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

subsection \<open>Step (c): the bounded estimate at the stopped pair\<close>

lemma pcoord_stopped_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. pcoord T i (min s (ploc T i R \<omega>)) \<omega>)"
proof -
  have c: "continuous_on {0..} (\<lambda>s. pcoord T i s \<omega>)"
    unfolding pcoord_def
    by (rule paper_pair_class_coord_paths_cont[OF T setsQ w])
  have m: "continuous_on {0..} (\<lambda>s :: real. min s (ploc T i R \<omega>))"
    by (intro continuous_intros)
  have mim: "(\<lambda>s :: real. min s (ploc T i R \<omega>)) ` {0..} \<subseteq> {0..}"
    using ploc_nonneg[OF T, of i R \<omega>] by auto
  show ?thesis by (rule continuous_on_compose2[OF c m mim])
qed

theorem paper_pair_class_stopped_fourth_moment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
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
  have prob: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have mgX: "martingale Q ?F 0 ?X"
    by (rule paper_pair_class_stopped_coord_martingale[OF T L setsQ Q])
  then interpret MX: martingale Q ?F 0 ?X .
  have mgZ: "martingale Q ?F 0 (\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>)"
    using paper_pair_class_stopped_comp_martingale[OF T L setsQ Q]
    unfolding pcoord_def by simp
  then interpret MZ: martingale Q ?F 0 "\<lambda>w \<omega>. (?X w \<omega>)\<^sup>2 - ?A w \<omega>" .
  have Ab: "AE \<omega> in Q. \<bar>?A w \<omega>\<bar> \<le> real CARD('n) * L * T" if w: "0 \<le> w" for w
    by (rule paper_pair_class_stopped_A_abs_le[OF T0 L Q w])
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
      by (rule paper_pair_class_stopped_compensator_rate[OF T0 L Q])
    show "\<And>a b. 0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> AE \<omega> in Q.
        cond_exp Q (?F a) (\<lambda>\<omega>. (?X b \<omega> - ?X a \<omega>)\<^sup>2) \<omega>
          = cond_exp Q (?F a) (\<lambda>\<omega>. ?A b \<omega> - ?A a \<omega>) \<omega>"
      by (rule paper_pair_class_stopped_cond_exp[OF T L setsQ Q R xR])
    show "0 \<le> R" using R by simp
    show "\<And>w. 0 \<le> w \<Longrightarrow> AE \<omega> in Q. \<bar>?X w \<omega>\<bar> \<le> R"
      by (rule paper_pair_class_stopped_abs_le[OF T0 setsQ Q R xR])
  qed
qed

subsection \<open>Step (d): Fatou removes the localization\<close>

text \<open>Pathwise the localization is eventually inactive: a path is
  continuous on the COMPACT \<open>{0..T}\<close>, hence bounded there, so once \<open>R\<close>
  exceeds that bound the level is never reached and \<open>\<tau>\<^sub>R = T\<close>.  The stopped
  increments are therefore eventually EQUAL to the unstopped ones, and
  Fatou turns the uniform bound of step (c) into the bound itself.\<close>

lemma abs_diff_le_two:
  fixes a b C :: real
  assumes "\<bar>a\<bar> \<le> C" and "\<bar>b\<bar> \<le> C"
  shows "\<bar>a - b\<bar> \<le> 2 * C"
  using assms by (simp add: abs_le_iff)

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

theorem paper_pair_class_fourth_moment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q: "Q \<in> paper_pair_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
      \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
proof -
  let ?RR = "\<lambda>m :: nat. \<bar>x $ i\<bar> + 1 + real m"
  let ?g = "\<lambda>m \<omega> :: 'n pairpath.
      (pcoord T i (min tt (ploc T i (?RR m) \<omega>)) \<omega>
        - pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>)^4"
  have T0: "0 \<le> T" using T by simp
  have prob: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have fmQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have Rpos: "0 < ?RR m" for m by simp
  have Rgt: "\<bar>x $ i\<bar> < ?RR m" for m by simp
  have gint: "integrable Q (?g m)" for m
  proof -
    have mgX: "martingale Q (natural_filtration Q 0 (\<lambda>w \<omega>. \<omega> w)) 0
        (\<lambda>w \<omega>. pcoord T i (min w (ploc T i (?RR m) \<omega>)) \<omega>)"
      by (rule paper_pair_class_stopped_coord_martingale[OF T L setsQ Q])
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
      by (rule paper_pair_class_stopped_abs_le[OF T0 setsQ Q Rpos Rgt tt0])
    have b2: "AE \<omega> in Q. \<bar>pcoord T i (min s (ploc T i (?RR m) \<omega>)) \<omega>\<bar> \<le> ?RR m"
      by (rule paper_pair_class_stopped_abs_le[OF T0 setsQ Q Rpos Rgt st])
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
    by (rule paper_pair_class_stopped_fourth_moment
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
          [OF paper_pair_class_coord_paths_cont[OF T0 setsQ mem]]) auto
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

text \<open>Steps (i)--(iv) of NC-3 were written for the coordinate
  \<open>\<omega> \<mapsto> fst (\<omega> t) $ i\<close>.  The COMPENSATED clause of (1.7) needs exactly the
  same four steps for \<open>\<omega> \<mapsto> (outerp (fst (\<omega> t)) - snd (\<omega> t)) $ i $ j\<close>.
  Both are of the form \<open>\<omega> \<mapsto> F (\<omega> t)\<close> for a CONTINUOUS \<open>F\<close> on the pair
  state, so the whole chain is redone here once, parametric in \<open>F\<close>, and
  instantiated twice.  Nothing is duplicated and nothing is lost: the
  coordinate instance of each generic statement is the old one.

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
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. F (\<omega> u)) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. F (\<omega> u))
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_F_cont[OF Fc u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_F_sq_measurable:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. (F (\<omega> u))\<^sup>2) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. (F (\<omega> u))\<^sup>2)
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_F_sq_cont[OF Fc u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma pair_law_F_sq_integrable_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hc: "continuous_map
        (mtopology_of (path_metric s :: ('n pairpath) metric)) euclideanreal h"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))
      \<in> borel_measurable N"
proof -
  have sT: "s \<le> T" using ts tT by simp
  have tI: "t \<in> {0..T}" using st ts tT by simp
  have "(\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s}) * (F (\<omega> t) - F (\<omega> s)))
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
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
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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

subsection \<open>Steps (i) and (ii), generically\<close>

theorem martingale_test_F:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and mgF: "martingale N (natural_filtration N 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and hm: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric s :: ('n pairpath) metric)))"
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
    and setsm: "\<And>m. sets (Qm m) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
  have hm: "h \<in> borel_measurable (borel_of (mtopology_of
      (path_metric s :: ('n pairpath) metric)))"
    using continuous_map_measurable[OF hc] by (simp add: borel_of_euclidean)
  have zero: "(\<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) = 0" for m
    by (rule martingale_test_F[OF Pm setsm mgm st ts tT hm hb])
  have z: "(\<lambda>m. \<integral>\<omega>. ?f \<omega> \<partial>(Qm m)) \<longlonglongrightarrow> 0" using zero by simp
  show ?thesis by (rule tendsto_unique[OF _ lim z]) simp
qed

subsection \<open>Steps (iii) and (iv), generically\<close>

theorem martingale_event_F_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
    and F :: "(real^'n) \<times> (real^'n^'n) \<Rightarrow> real"
  assumes Fc: "continuous_on UNIV F"
    and Pm: "\<And>m. prob_space (Qm m)"
    and setsm: "\<And>m. sets (Qm m) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and C0: "0 \<le> C"
    and nnm: "\<And>m u. u \<in> {0..T} \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((F (\<omega> u))\<^sup>2) \<partial>(Qm m)) \<le> ennreal C"
    and st: "0 \<le> s" and ts: "s \<le> t" and tT: "t \<le> T"
    and Bs: "Bs \<in> sets (borel_of (mtopology_of
        (path_metric s :: ('n pairpath) metric)))"
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
        (use cmp wm w0 in \<open>auto simp: mult.commute intro!: AE_I2\<close>)
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
    and setsm: "\<And>m. sets (Qm m) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and mgm: "\<And>m. martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. F (\<omega> (min u T)))"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
      obtain Bs where Bs: "Bs \<in> sets (borel_of (mtopology_of
            (path_metric u :: ('n pairpath) metric)))"
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
            borel_of (mtopology_of (path_metric u :: ('n pairpath) metric))"
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

text \<open>The instantiation of the generic chain at
  \<open>F\<^sub>2 p = (outerp (fst p) - snd p) $ i $ j\<close>.  The only new input is its
  \<open>L\<^sup>2\<close> bound, which is where the fourth moment is spent:
  \<open>(ab - c)\<^sup>2 \<le> a\<^sup>4 + b\<^sup>4 + 2c\<^sup>2\<close> pointwise, so a second moment of the
  compensated functional costs a FOURTH moment of the coordinates --- the
  reason this clause was blocked until now.\<close>

lemma prod_minus_sq_bound:
  fixes a b c :: real
  shows "(a * b - c)\<^sup>2 \<le> a^4 + b^4 + 2 * c\<^sup>2"
proof -
  have e1: "2 * (a*b)\<^sup>2 + 2 * c\<^sup>2 - (a*b - c)\<^sup>2 = (a*b + c)\<^sup>2"
    by (simp add: power2_diff power2_sum)
  have s1: "(a*b - c)\<^sup>2 \<le> 2 * (a*b)\<^sup>2 + 2 * c\<^sup>2"
    using e1 zero_le_power2[of "a*b + c"] by linarith
  have e2: "a^4 + b^4 - 2 * (a*b)\<^sup>2 = (a\<^sup>2 - b\<^sup>2)\<^sup>2"
    by (simp add: power2_diff power2_eq_square power4_eq_xxxx algebra_simps)
  have s2: "2 * (a*b)\<^sup>2 \<le> a^4 + b^4"
    using e2 zero_le_power2[of "a\<^sup>2 - b\<^sup>2"] by linarith
  from s1 s2 show ?thesis by linarith
qed

lemma fourth_power_sum_bound:
  fixes a b :: real
  shows "(a + b)^4 \<le> 8 * (a^4 + b^4)"
proof -
  have e1: "2 * (a\<^sup>2 + b\<^sup>2) - (a + b)\<^sup>2 = (a - b)\<^sup>2"
    by (simp add: power2_diff power2_sum)
  have s1: "(a + b)\<^sup>2 \<le> 2 * (a\<^sup>2 + b\<^sup>2)"
    using e1 zero_le_power2[of "a - b"] by linarith
  have nn: "0 \<le> (a + b)\<^sup>2" by simp
  have s2: "((a + b)\<^sup>2)\<^sup>2 \<le> (2 * (a\<^sup>2 + b\<^sup>2))\<^sup>2"
    by (rule power_mono[OF s1 nn])
  have e2: "a^4 + b^4 - 2 * (a\<^sup>2 * b\<^sup>2) = (a\<^sup>2 - b\<^sup>2)\<^sup>2"
    by (simp add: power2_diff power2_eq_square power4_eq_xxxx algebra_simps)
  have s3: "(a\<^sup>2 + b\<^sup>2)\<^sup>2 \<le> 2 * (a^4 + b^4)"
  proof -
    have s0: "2 * (a\<^sup>2 * b\<^sup>2) \<le> a^4 + b^4"
      using e2 zero_le_power2[of "a\<^sup>2 - b\<^sup>2"] by linarith
    have "(a\<^sup>2 + b\<^sup>2)\<^sup>2 = a^4 + 2 * (a\<^sup>2 * b\<^sup>2) + b^4"
      by (simp add: power2_sum power2_eq_square power4_eq_xxxx algebra_simps)
    \<comment> \<open>\<open>linarith\<close> balks here although the problem is linear in the atoms
        \<open>(a²+b²)²\<close>, \<open>a⁴\<close>, \<open>b⁴\<close>, \<open>a²b²\<close>; \<open>argo\<close> is the documented fix.\<close>
    then show ?thesis using s0 by argo
  qed
  have e3: "((a + b)\<^sup>2)\<^sup>2 = (a + b)^4"
    by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
  have e4: "(2 * (a\<^sup>2 + b\<^sup>2))\<^sup>2 = 4 * (a\<^sup>2 + b\<^sup>2)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  from s2 s3 show ?thesis unfolding e3 e4 by linarith
qed

lemma zero_le_fourth:
  fixes a :: real
  shows "0 \<le> a^4"
proof -
  have "a^4 = (a\<^sup>2)\<^sup>2"
    by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
  then show ?thesis by simp
qed

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

text \<open>The fourth moment of the coordinate ITSELF, not of an increment: the
  start clause pins \<open>X\<^sub>0 = x\<close>, so \<open>(a+b)\<^sup>4 \<le> 8(a\<^sup>4+b\<^sup>4)\<close> turns the increment
  bound into an absolute one, uniform over the whole class.\<close>

lemma paper_pair_class_fourth_moment_abs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> u) $ i)^4) \<partial>Q)
      \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4))"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
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
    using Q unfolding paper_pair_class_def by blast
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
      by (rule paper_pair_class_fourth_moment[OF T L setsQ Q order_refl])
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
  The bound depends only on \<open>k, L, T, x\<close>, hence is UNIFORM over the
  class --- which is exactly what a weak-limit argument needs.\<close>

lemma paper_pair_class_comp_entry_sq_nn:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and u: "u \<in> {0..T}"
  shows "(\<integral>\<^sup>+\<omega>. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2) \<partial>Q)
      \<le> ennreal (8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ i)^4)
               + 8 * (8 * L\<^sup>2 * T\<^sup>2 + (x $ j)^4)
               + 2 * (real CARD('n) * L * T)\<^sup>2)"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
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
    by (rule paper_pair_class_Y_entry_bound_ae[OF T0 L Q u])
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
    by (intro add_mono order_refl paper_pair_class_fourth_moment_abs[OF T L Q u])
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

subsection \<open>Assembling a matrix-valued martingale from its entries\<close>

text \<open>\<open>Ito_Market.martingale_vecI\<close> is stated for \<open>real^'n\<close>, and its three
  helpers (\<open>measurable_vec_components\<close>, \<open>integrable_vec_components\<close>,
  \<open>set_integral_vec_component\<close>) are all specific to REAL entries, so it does
  not iterate to \<open>real^'n^'n\<close>.  The three matrix analogues are proved here
  directly from the euclidean structure: \<open>Basis\<close> of a matrix consists of the
  \<open>axis i (axis j 1)\<close>, and \<open>A \<bullet> axis i (axis j 1) = A $ i $ j\<close>.\<close>

lemma mat_inner_axis:
  fixes A :: "real^'n::finite^'n"
  shows "A \<bullet> axis i (axis j 1) = A $ i $ j"
  by (simp add: inner_axis)

lemma mat_Basis_cases:
  fixes b :: "real^'n::finite^'n"
  assumes "b \<in> Basis"
  obtains i j where "b = axis i (axis j 1)"
  using assms by (auto simp: Basis_vec_def)

lemma measurable_mat_entries:
  fixes X :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes ent: "\<And>i j. (\<lambda>\<omega>. X \<omega> $ i $ j) \<in> borel_measurable M"
  shows "X \<in> borel_measurable M"
proof (subst borel_measurable_euclidean_space, safe)
  fix b :: "real^'n^'n" assume "b \<in> Basis"
  then obtain i j where b: "b = axis i (axis j 1)" by (rule mat_Basis_cases)
  show "(\<lambda>\<omega>. X \<omega> \<bullet> b) \<in> borel_measurable M"
    unfolding b by (simp add: mat_inner_axis ent)
qed

lemma integrable_mat_entries:
  fixes X :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes m: "X \<in> borel_measurable M"
    and ent: "\<And>i j. integrable M (\<lambda>\<omega>. X \<omega> $ i $ j)"
  shows "integrable M X"
proof (rule Bochner_Integration.integrable_bound
    [where f = "\<lambda>\<omega>. (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"])
  show "integrable M (\<lambda>\<omega>. (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>))"
  proof (intro Bochner_Integration.integrable_sum integrable_abs)
    fix b :: "real^'n^'n" assume "b \<in> Basis"
    then obtain i j where b: "b = axis i (axis j 1)" by (rule mat_Basis_cases)
    show "integrable M (\<lambda>\<omega>. X \<omega> \<bullet> b)"
      unfolding b by (simp add: mat_inner_axis ent)
  qed
  show "X \<in> borel_measurable M" by (rule m)
  show "AE \<omega> in M. norm (X \<omega>)
      \<le> norm (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"
  proof (intro always_eventually allI)
    fix \<omega> :: 'a
    have "norm (X \<omega>) \<le> (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"
      by (rule norm_le_l1)
    also have "\<dots> \<le> norm (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)"
      by simp
    finally show "norm (X \<omega>)
        \<le> norm (\<Sum>b\<in>(Basis :: (real^'n^'n) set). \<bar>X \<omega> \<bullet> b\<bar>)" .
  qed
qed

lemma set_integral_mat_component:
  fixes X :: "'a \<Rightarrow> real^'n::finite^'n"
  assumes A: "A \<in> sets M" and int: "integrable M X"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. X \<omega> $ i $ j)
      = set_lebesgue_integral M A X $ i $ j"
proof -
  have bl: "bounded_linear (\<lambda>A :: real^'n^'n. A $ i $ j)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth])
  have si: "integrable M (\<lambda>\<omega>. indicat_real A \<omega> *\<^sub>R X \<omega>)"
    by (intro integrable_mult_indicator A int)
  have "set_lebesgue_integral M A (\<lambda>\<omega>. X \<omega> $ i $ j)
      = (\<integral>\<omega>. (indicat_real A \<omega> *\<^sub>R X \<omega>) $ i $ j \<partial>M)"
    unfolding set_lebesgue_integral_def by simp
  also have "\<dots> = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R X \<omega> \<partial>M) $ i $ j"
    by (rule has_bochner_integral_integral_eq
        [OF has_bochner_integral_bounded_linear
          [OF bl has_bochner_integral_integrable[OF si]]])
  finally show ?thesis
    unfolding set_lebesgue_integral_def .
qed

lemma martingale_matI:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite^'n"
  assumes comp: "\<And>i j. martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ i $ j)"
  shows "martingale M F 0 X"
proof -
  interpret M0: martingale M F 0
      "\<lambda>t \<omega>. X t \<omega> $ (undefined :: 'n) $ (undefined :: 'n)"
    by (rule comp)
  have A_M: "A \<in> sets M" if u: "0 \<le> u" and A: "A \<in> sets (F u)" for A u
  proof -
    have "sets (F u) \<subseteq> sets M"
      using M0.subalgebras[OF u] by (simp add: subalgebra_def)
    then show ?thesis using A by blast
  qed
  have entmeas: "(\<lambda>\<omega>. X u \<omega> $ i $ j) \<in> borel_measurable (F u)"
    if u: "0 \<le> u" for u i j
  proof -
    interpret Mij: martingale M F 0 "\<lambda>t \<omega>. X t \<omega> $ i $ j" by (rule comp)
    show ?thesis by (rule Mij.adapted[OF u])
  qed
  have entint: "integrable M (\<lambda>\<omega>. X u \<omega> $ i $ j)" if u: "0 \<le> u" for u i j
    by (rule martingale.integrable[OF comp u])
  have Xm: "X u \<in> borel_measurable M" if u: "0 \<le> u" for u
    by (rule measurable_mat_entries)
      (rule borel_measurable_integrable[OF entint[OF u]])
  have vint: "integrable M (X u)" if u: "0 \<le> u" for u
    by (rule integrable_mat_entries[OF Xm[OF u]]) (rule entint[OF u])
  show ?thesis
  proof (rule M0.martingale_of_set_integral_eq)
    show "adapted_process M F 0 X"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure M F 0" by unfold_locales
      fix u :: real assume u: "0 \<le> u"
      show "X u \<in> borel_measurable (F u)"
        by (rule measurable_mat_entries) (rule entmeas[OF u])
    qed
    show "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (X u)" by (rule vint)
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u)"
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets M" by (rule A_M[OF u A])
    have "set_lebesgue_integral M A (X u) $ i $ j
        = set_lebesgue_integral M A (X v) $ i $ j" for i j
    proof -
      have "set_lebesgue_integral M A (X u) $ i $ j
          = set_lebesgue_integral M A (\<lambda>\<omega>. X u \<omega> $ i $ j)"
        by (rule set_integral_mat_component[OF AM vint[OF u], symmetric])
      also have "\<dots> = set_lebesgue_integral M A (\<lambda>\<omega>. X v \<omega> $ i $ j)"
        by (rule martingale.set_integral_eq[OF comp A u uv])
      also have "\<dots> = set_lebesgue_integral M A (X v) $ i $ j"
        by (rule set_integral_mat_component[OF AM vint[OF v]])
      finally show ?thesis .
    qed
    then show "set_lebesgue_integral M A (X u) = set_lebesgue_integral M A (X v)"
      by (simp add: vec_eq_iff)
  qed
qed

subsection \<open>Lemma 2.3: the compensated clause, at the limit\<close>

theorem paper_pair_class_comp_entry_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
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
    show "prob_space (Qm m)" for m by (rule paper_pair_class_prob[OF mem])
    show "sets (Qm m) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" for m
      by (rule paper_pair_class_sets[OF mem])
    show "martingale (Qm m) (natural_filtration (Qm m) 0 (\<lambda>u \<omega>. \<omega> u)) 0
        (\<lambda>u \<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ i $ j)"
      for m
      by (rule martingale_mat_nth
          [OF paper_pair_class_compensated_martingale[OF mem]])
    show "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))" by (rule wc)
    show "prob_space Q" by (rule prob)
    show "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" by (rule setsQ)
    show "0 \<le> ?C" by (rule C0)
    show "(\<integral>\<^sup>+\<omega>. ennreal (((outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)\<^sup>2)
            \<partial>(Qm m)) \<le> ennreal ?C" if "u \<in> {0..T}" for m u
      by (rule paper_pair_class_comp_entry_sq_nn[OF T L mem that])
  qed
qed

corollary paper_pair_class_comp_martingale_limit:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
  by (rule martingale_matI)
    (rule paper_pair_class_comp_entry_martingale_limit
      [OF T L mem wc prob setsQ])

section \<open>Lemma 2.3: the class is closed under weak limits\<close>

text \<open>All four clauses of (1.7) now survive a weak limit, so the paper's
  class of pair laws is weakly closed.  The compensated clause was the last
  one missing, and it is exactly the one that needed the uniform fourth
  moment.\<close>

theorem paper_pair_class_weak_closed:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "Q \<in> paper_pair_class k L T x"
proof -
  have T0: "0 \<le> T" using T by simp
  show ?thesis
    unfolding paper_pair_class_def
  proof (intro CollectI conjI)
    show "prob_space Q" by (rule prob)
    show "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" by (rule setsQ)
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule paper_pair_class_limit_three_clauses(1)
          [OF T0 L mem wc prob setsQ])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule paper_pair_class_limit_three_clauses(2)
          [OF T0 L mem wc prob setsQ])
    show "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
      by (rule paper_pair_class_limit_three_clauses(3)
          [OF T0 L mem wc prob setsQ])
    show "martingale Q (natural_filtration Q 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
      by (rule paper_pair_class_comp_martingale_limit[OF T L mem wc prob setsQ])
  qed
qed

section \<open>NC-2: the paper's class is tight\<close>

text \<open>The other consumer of the uniform fourth moment.  The Kolmogorov
  chain in \<open>Path_Tightness\<close> wants the moment as a BOCHNER integral, so the
  \<open>nn_integral\<close> bound is first converted; integrability is free, because a
  nonnegative function with a finite \<open>nn_integral\<close> is integrable.\<close>

lemma paper_pair_class_fourth_moment_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
proof -
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have sI: "s \<in> {0..T}" using st stt ttT by simp
  have tI: "tt \<in> {0..T}" using st stt ttT by simp
  have m: "(\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)
      \<in> borel_measurable Q"
    by (intro borel_measurable_power borel_measurable_diff
        pair_law_coord_measurable[OF setsQ tI]
        pair_law_coord_measurable[OF setsQ sI])
  show ?thesis
  proof (rule integrableI_nonneg[OF m])
    show "AE \<omega> in Q. 0 \<le> (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4"
      by (simp add: zero_le_fourth)
    have "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
        \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
      by (rule paper_pair_class_fourth_moment[OF T L setsQ Q st stt ttT])
    \<comment> \<open>\<open>\<infinity>\<close> and \<open>\<top>\<close> are DIFFERENT terms on \<open>ennreal\<close> (the former is a
        definition, only simp-identified with the latter), so the \<open>show\<close>
        must use the one the rule states.\<close>
    also have "\<dots> < \<infinity>" by simp
    finally show "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q) < \<infinity>" .
  qed
qed

lemma paper_pair_class_fourth_moment_bochner:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q) \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
proof -
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have int: "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
    by (rule paper_pair_class_fourth_moment_integrable[OF T L Q st stt ttT])
  have B0: "0 \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2" by (intro mult_nonneg_nonneg) auto
  have "ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
      = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)"
    by (rule nn_integral_eq_integral[symmetric, OF int])
      (simp add: zero_le_fourth)
  also have "\<dots> \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
    by (rule paper_pair_class_fourth_moment[OF T L setsQ Q st stt ttT])
  finally show ?thesis using B0 by simp
qed

lemma path_coord_cont_on:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "continuous_on {0..T} (\<lambda>t. fst (\<omega> t) $ i)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have c2: "continuous_on UNIV
      (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p $ i)"
    by (intro continuous_intros)
  show ?thesis by (rule continuous_on_compose2[OF c2 c]) simp
qed

text \<open>The mass a class member puts OUTSIDE a pair Hölder ball.  This is
  \<open>Path_Tightness.path_law_holder_ball_bound_vec\<close>'s argument, run natively
  on the pair path space.  Two things stop that theorem from being applied
  off the shelf: its conclusion is about the push-forward \<open>path_law M X T\<close>
  of an abstract process, whereas a class member IS already a law on paths;
  and it wants the start condition \<open>X\<^sub>0 = x\<close> POINTWISE, whereas a class
  member only has it almost surely.  Charging the failure of the
  start-and-Lipschitz event to a null set handles both --- and, as a
  bonus, removes the need for the \<open>Y\<close>-event of
  \<open>pair_holder_charge_split\<close> to be measurable, so the split lemma is not
  needed either.\<close>

theorem paper_pair_class_pair_holder_charge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and ga: "0 < ga" and ga4: "ga < 1/4"
    and Q: "Q \<in> paper_pair_class k L T x"
  shows "measure Q (space Q -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u)
                \<le> (real CARD('n) * holder_const ga T n
                    + real CARD('n) * L * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)})
    \<le> real CARD('n)
        * (8*L\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga))))"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  let ?B = "real CARD('n) * L"
  let ?c = "real CARD('n) * holder_const ga T n"
  let ?K = "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u)
             \<le> (?c + ?B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
  have T0: "0 \<le> T" using T by simp
  have ga1: "ga \<le> 1" using ga4 by simp
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have B0: "0 \<le> ?B" using L by simp
  have c0: "0 \<le> ?c"
    by (intro mult_nonneg_nonneg holder_const_nonneg[OF ga]) simp
  have cB0: "0 \<le> ?c + ?B * T powr (1 - ga)"
    using c0 B0 by simp
  \<comment> \<open>the ball is compact, hence closed, hence measurable\<close>
  have compK: "compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) ?K"
    by (rule compactin_pair_holder_ball[OF T0 ga cB0])
  have haus: "Hausdorff_space
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.Hausdorff_space_mtopology[OF Metric_space_mspace_mdist])
  have Ksets: "?K \<in> sets Q"
    using borel_of_closed[OF compactin_imp_closedin[OF haus compK]] setsQ by simp
  \<comment> \<open>the dyadic bad events, one per coordinate\<close>
  have coordm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) $ i) \<in> borel_measurable Q"
    for u i
    by (rule measurable_compose
        [OF pair_law_eval_measurable[OF setsQ] fst_coord_borel])
  define Bad where "Bad = (\<lambda>i. {\<omega> \<in> space Q. \<exists>j\<ge>n. \<exists>kk\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-ga*real j)
        \<le> \<bar>fst (\<omega> (real_of_int kk / 2^j)) $ i
            - fst (\<omega> (real_of_int (kk - 1) / 2^j)) $ i\<bar>})"
  have BadS: "Bad i \<in> sets Q" for i
    unfolding Bad_def
    by (intro dyadic_bad_event_sets[where X = "\<lambda>u \<omega>. fst (\<omega> u) $ i"] coordm)
  have badbnd: "measure Q (Bad i)
      \<le> 8*L\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga)))" for i
    unfolding Bad_def
    by (intro dyadic_bad_event_tail_mom
          [where X = "\<lambda>u \<omega>. fst (\<omega> u) $ i" and C = L]
        P.prob_space_axioms coordm
        paper_pair_class_fourth_moment_integrable[OF T L Q]
        paper_pair_class_fourth_moment_bochner[OF T L Q] T0 ga4)
  \<comment> \<open>the almost-sure start-and-Lipschitz event, and a null superset of its
      complement\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding paper_pair_class_def by blast
  have lip: "AE \<omega> in Q. ?B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    by (rule paper_pair_class_lipschitz_ae[OF T0 L Q])
  have ae: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0
      \<and> ?B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    using st lip by eventually_elim blast
  obtain N where
    Nsub: "{\<omega> \<in> space Q. \<not> (fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0
        \<and> ?B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t)))} \<subseteq> N"
    and Nzero: "emeasure Q N = 0" and Nsets: "N \<in> sets Q"
    by (rule AE_E[OF ae])
  have Nmeas: "measure Q N = 0" using Nzero by (simp add: measure_def)
  have sub: "space Q - ?K \<subseteq> (\<Union>i\<in>UNIV. Bad i) \<union> N"
  proof
    fix \<omega> :: "'n pairpath" assume w: "\<omega> \<in> space Q - ?K"
    have wQ: "\<omega> \<in> space Q" using w by blast
    have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using wQ spQ by simp
    show "\<omega> \<in> (\<Union>i\<in>UNIV. Bad i) \<union> N"
    proof (rule ccontr)
      assume nb: "\<omega> \<notin> (\<Union>i\<in>UNIV. Bad i) \<union> N"
      then have nBi: "\<omega> \<notin> Bad i" for i by blast
      have good: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0
          \<and> ?B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
        using nb Nsub wQ by blast
      have gi: "\<bar>fst (\<omega> (real_of_int kk / 2^j)) $ i
            - fst (\<omega> (real_of_int (kk - 1) / 2^j)) $ i\<bar>
          \<le> 2 powr (-ga*real j)"
        if jk: "n \<le> j" "kk \<in> {1..\<lfloor>2^j * T\<rfloor>}" for i j kk
      proof -
        have "\<not> 2 powr (-ga*real j)
            \<le> \<bar>fst (\<omega> (real_of_int kk / 2^j)) $ i
                - fst (\<omega> (real_of_int (kk - 1) / 2^j)) $ i\<bar>"
          using nBi[of i] wQ jk unfolding Bad_def by blast
        then show ?thesis by linarith
      qed
      have coordH: "\<bar>fst (\<omega> v) $ i - fst (\<omega> u) $ i\<bar>
          \<le> holder_const ga T n * \<bar>v - u\<bar> powr ga"
        if u: "u \<in> {0..T}" and v: "v \<in> {0..T}" for i and u v :: real
        by (rule holder_of_good_dyadics
            [OF T0 ga ga1 path_coord_cont_on[OF wm] gi v u])
      have XH: "norm (fst (\<omega> v) - fst (\<omega> u)) \<le> ?c * \<bar>v - u\<bar> powr ga"
        if u: "u \<in> {0..T}" and v: "v \<in> {0..T}" for u v :: real
      proof -
        have "norm (fst (\<omega> v) - fst (\<omega> u))
            \<le> (\<Sum>i\<in>UNIV. \<bar>(fst (\<omega> v) - fst (\<omega> u)) $ i\<bar>)"
          by (rule norm_le_l1_cart)
        also have "\<dots> = (\<Sum>i\<in>UNIV. \<bar>fst (\<omega> v) $ i - fst (\<omega> u) $ i\<bar>)"
          by simp
        also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'n set).
            holder_const ga T n * \<bar>v - u\<bar> powr ga)"
          by (intro sum_mono coordH[OF u v])
        also have "\<dots> = ?c * \<bar>v - u\<bar> powr ga" by simp
        finally show ?thesis .
      qed
      have YL: "norm (snd (\<omega> v) - snd (\<omega> u)) \<le> ?B * \<bar>v - u\<bar>"
        if u: "u \<in> {0..T}" and v: "v \<in> {0..T}" for u v :: real
      proof -
        have lipw: "?B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))" using good by blast
        have "dist (snd (\<omega> v)) (snd (\<omega> u)) \<le> ?B * dist v u"
          by (rule lipschitz_onD[OF lipw v u])
        then show ?thesis by (simp add: dist_norm dist_real_def)
      qed
      have start: "\<omega> 0 = (x, 0)" using good by (simp add: prod_eq_iff)
      have "\<omega> \<in> ?K"
        by (rule pair_holder_ball_mem[OF T0 ga ga1 c0 B0 wm start XH YL])
      with w show False by blast
    qed
  qed
  have UB: "(\<Union>i\<in>UNIV. Bad i) \<in> sets Q"
    by (intro sets.countable_UN'' BadS countableI_type)
  have "measure Q (space Q - ?K) \<le> measure Q ((\<Union>i\<in>UNIV. Bad i) \<union> N)"
    using Ksets UB Nsets by (intro P.finite_measure_mono[OF sub] sets.Un)
  also have "\<dots> \<le> measure Q (\<Union>i\<in>UNIV. Bad i) + measure Q N"
    by (rule measure_subadditive[OF UB Nsets])
      (simp_all add: P.emeasure_eq_measure)
  also have "\<dots> = measure Q (\<Union>i\<in>UNIV. Bad i)"
    using Nmeas by simp
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'n set). measure Q (Bad i))"
    by (rule P.finite_measure_subadditive_finite) (auto intro: BadS)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'n set).
      8*L\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga))))"
    by (intro sum_mono badbnd)
  also have "\<dots> = real CARD('n)
      * (8*L\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga))))"
    by simp
  finally show ?thesis .
qed

text \<open>Hence tightness.  The Hölder exponent may be any \<open>ga < 1/4\<close> --- the
  fourth moment is what caps it --- and \<open>1/8\<close> is taken; the RADIUS is what
  varies with \<open>e\<close>, through the dyadic level \<open>n\<close>, because
  \<open>2 powr (-(1-4\<sqdot>ga)) < 1\<close> makes the charge geometric in \<open>n\<close>.\<close>

theorem tight_on_set_paper_pair_class:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> N \<in> paper_pair_class k L T x"
  shows "tight_on_set (mtopology_of (path_metric T :: ('n pairpath) metric)) \<Gamma>"
proof -
  let ?ga = "1/8 :: real"
  let ?q = "2 powr (-(1-4*?ga)) :: real"
  have T0: "0 \<le> T" using T by simp
  have ga0: "0 < ?ga" by simp
  have ga4: "?ga < 1/4" by simp
  have q0: "0 < ?q" by simp
  have q1: "?q < 1" by (rule powr_ratio_lt_1[OF ga4])
  show ?thesis
  proof (rule tight_on_set_pair_holder_charge[OF T0 ga0])
    show "finite_measure N" if "N \<in> \<Gamma>" for N
      using paper_pair_class_prob[OF mem[OF that]]
      by (simp add: prob_space_def)
    show "sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))) = sets N" if "N \<in> \<Gamma>" for N
      by (rule paper_pair_class_sets[OF mem[OF that], symmetric])
    fix e :: real assume e: "0 < e"
    have lim: "(\<lambda>m :: nat. real CARD('n) * (8*L\<^sup>2*T * ?q^m / (1 - ?q)))
        \<longlonglongrightarrow> real CARD('n) * (8*L\<^sup>2*T * 0 / (1 - ?q))"
      by (intro tendsto_intros LIMSEQ_realpow_zero) (use q0 q1 in auto)
    have lim0: "(\<lambda>m :: nat. real CARD('n) * (8*L\<^sup>2*T * ?q^m / (1 - ?q)))
        \<longlonglongrightarrow> 0"
      using lim by simp
    have ev: "eventually
        (\<lambda>m. real CARD('n) * (8*L\<^sup>2*T * ?q^m / (1 - ?q)) < e) sequentially"
      by (rule order_tendstoD(2)[OF lim0 e])
    obtain n where n: "real CARD('n) * (8*L\<^sup>2*T * ?q^n / (1 - ?q)) < e"
      using ev unfolding eventually_sequentially by blast
    show "\<exists>c. 0 \<le> c \<and> (\<forall>N\<in>\<Gamma>. measure N (space N -
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
           \<omega> 0 = (x, 0)
           \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ?ga)}) < e)"
    proof (intro exI[of _ "real CARD('n) * holder_const ?ga T n
          + real CARD('n) * L * T powr (1 - ?ga)"] conjI ballI)
      show "0 \<le> real CARD('n) * holder_const ?ga T n
          + real CARD('n) * L * T powr (1 - ?ga)"
        using L holder_const_nonneg[OF ga0, of T n] by simp
      fix N :: "('n pairpath) measure" assume NG: "N \<in> \<Gamma>"
      have "measure N (space N -
          {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             \<omega> 0 = (x, 0)
             \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                  norm (\<omega> v - \<omega> u)
                    \<le> (real CARD('n) * holder_const ?ga T n
                        + real CARD('n) * L * T powr (1 - ?ga))
                      * \<bar>v - u\<bar> powr ?ga)})
          \<le> real CARD('n) * (8*L\<^sup>2*T * ?q^n / (1 - ?q))"
        by (rule paper_pair_class_pair_holder_charge
            [OF T L ga0 ga4 mem[OF NG]])
      then show "measure N (space N -
          {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             \<omega> 0 = (x, 0)
             \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                  norm (\<omega> v - \<omega> u)
                    \<le> (real CARD('n) * holder_const ?ga T n
                        + real CARD('n) * L * T powr (1 - ?ga))
                      * \<bar>v - u\<bar> powr ?ga)}) < e"
        using n by linarith
    qed
  qed
qed

section \<open>NC-2: the class is sequentially compact\<close>

text \<open>Tightness gives a convergent subsequence with mass at most one; that
  the LIMIT still has mass one is not automatic, and is where tightness is
  used a second time: a compact set carrying all but \<open>e\<close> of every
  approximating law is CLOSED, so portmanteau keeps at least \<open>1 - e\<close> of the
  mass in the limit, for every \<open>e\<close>.\<close>

theorem paper_pair_class_weak_limit_prob_space:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
    and wc: "weak_conv_on Qm Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    and fin: "finite_measure Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and le1: "emeasure Q (space Q) \<le> ennreal 1"
  shows "prob_space Q"
proof -
  interpret FQ: finite_measure Q by (rule fin)
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have haus: "Hausdorff_space
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.Hausdorff_space_mtopology[OF Metric_space_mspace_mdist])
  have tight: "tight_on_set
      (mtopology_of (path_metric T :: ('n pairpath) metric)) (range Qm)"
    by (rule tight_on_set_paper_pair_class[OF T L]) (use mem in auto)
  have ge: "1 \<le> measure Q (space Q) + e" if e: "0 < e" for e
  proof -
    obtain K where
      compK: "compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) K"
      and chK: "\<And>m. measure (Qm m) (space (Qm m) - K) < e"
      using tight e unfolding tight_on_set_def by auto
    have Kcl: "closedin (mtopology_of (path_metric T :: ('n pairpath) metric)) K"
      by (rule compactin_imp_closedin[OF haus compK])
    have Ksub: "K \<subseteq> space Q"
      using compactin_subset_topspace[OF compK] spQ by simp
    have mK: "1 - e < measure (Qm m) K" for m
    proof -
      interpret Pm: prob_space "Qm m" by (rule paper_pair_class_prob[OF mem])
      have setsm: "sets (Qm m) = sets (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
        by (rule paper_pair_class_sets[OF mem])
      have Km: "K \<in> sets (Qm m)"
        using borel_of_closed[OF Kcl] setsm by simp
      have "measure (Qm m) (space (Qm m) - K) = 1 - measure (Qm m) K"
        by (rule Pm.prob_compl[OF Km])
      then show ?thesis using chK[of m] by simp
    qed
    have step1: "ereal (1 - e) \<le> ereal (measure Q K)"
    proof -
      have "ereal (1 - e) = Limsup sequentially (\<lambda>m :: nat. ereal (1 - e))"
        by (simp add: Limsup_const)
      also have "\<dots> \<le> Limsup sequentially (\<lambda>m. ereal (measure (Qm m) K))"
      proof (rule Limsup_mono, rule always_eventually, rule allI)
        fix m :: nat
        show "ereal (1 - e) \<le> ereal (measure (Qm m) K)"
          using mK[of m] by simp
      qed
      also have "\<dots> \<le> ereal (measure Q K)"
        by (rule weak_conv_closed_limsup[OF wc Kcl])
      finally show ?thesis .
    qed
    have "measure Q K \<le> measure Q (space Q)"
      by (rule FQ.finite_measure_mono[OF Ksub]) simp
    with step1 show ?thesis by simp
  qed
  have ge1: "1 \<le> measure Q (space Q)"
    by (rule field_le_epsilon) (use ge in simp)
  have le: "measure Q (space Q) \<le> 1"
    using le1 by (simp add: FQ.emeasure_eq_measure)
  have "emeasure Q (space Q) = 1"
    using ge1 le by (simp add: FQ.emeasure_eq_measure)
  then show ?thesis by (rule prob_spaceI)
qed

text \<open>Sequential compactness of the paper's class: NC-2 and NC-3 together.
  Every sequence of members has a subsequence converging weakly to a
  MEMBER.  Tightness (NC-2) supplies the subsequence and the mass, weak
  closedness (NC-3) supplies membership of the limit.\<close>

corollary paper_pair_class_convergent_subsequence:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> paper_pair_class k L T x"
  shows "\<exists>a Q. strict_mono a \<and> Q \<in> paper_pair_class k L T x
      \<and> weak_conv_on (Qm \<circ> a) Q sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  have "\<exists>a N. strict_mono a \<and> finite_measure N \<and> sets N = sets (borel_of ?X)
      \<and> N (space N) \<le> ennreal 1 \<and> weak_conv_on (Qm \<circ> a) N sequentially ?X"
  proof (rule tight_on_set_imp_convergent_subsequence)
    show "metrizable_space ?X"
      unfolding mtopology_of_def
      by (rule Metric_space.metrizable_space_mtopology
          [OF Metric_space_mspace_mdist])
    show "separable_space ?X" by (rule separable_path_metric)
    show "tight_on_set ?X (range Qm)"
      by (rule tight_on_set_paper_pair_class[OF T L]) (use mem in auto)
    fix m :: nat
    show "Qm m (space (Qm m)) \<le> ennreal 1"
      using paper_pair_class_prob[OF mem]
      by (simp add: prob_space.emeasure_space_1)
  qed
  then obtain a N where sm: "strict_mono a" and finN: "finite_measure N"
    and setsN: "sets N = sets (borel_of ?X)"
    and leN: "N (space N) \<le> ennreal 1"
    and wcN: "weak_conv_on (Qm \<circ> a) N sequentially ?X"
    by blast
  have memA: "(Qm \<circ> a) m \<in> paper_pair_class k L T x" for m
    by (simp add: mem)
  have probN: "prob_space N"
    by (rule paper_pair_class_weak_limit_prob_space
        [OF T L memA wcN finN setsN leN])
  have "N \<in> paper_pair_class k L T x"
    by (rule paper_pair_class_weak_closed[OF T L memA wcN probN setsN])
  with sm wcN show ?thesis by blast
qed

section \<open>The shift structure of the class (Larsson--Ruf Prop. 2.2(ii))\<close>

text \<open>Every member started at \<open>x\<close> is the \<open>x\<close>-translate of a member started
  at \<open>0\<close>.  This is what turns the value function into a supremum over a
  FIXED family --- the shape Berge's theorem needs, and hence the last
  structural input of the NC headline.  The translation must \<open>restrict\<close>,
  because points of the capped path space are extensional on \<open>{0..T}\<close>.\<close>

definition pshift :: "real \<Rightarrow> real^'n::finite \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath"
  where "pshift T x \<omega> = restrict (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t))) {0..T}"

lemma pshift_apply: "t \<in> {0..T} \<Longrightarrow> pshift T x \<omega> t = (x + fst (\<omega> t), snd (\<omega> t))"
  by (simp add: pshift_def)

lemma pshift_fst: "t \<in> {0..T} \<Longrightarrow> fst (pshift T x \<omega> t) = x + fst (\<omega> t)"
  by (simp add: pshift_def)

lemma pshift_snd: "t \<in> {0..T} \<Longrightarrow> snd (pshift T x \<omega> t) = snd (\<omega> t)"
  by (simp add: pshift_def)

lemma pshift_outside: "t \<notin> {0..T} \<Longrightarrow> pshift T x \<omega> t = undefined"
  by (auto simp: pshift_def)

lemma mspace_path_restrict_self:
  fixes \<omega> :: "real \<Rightarrow> 'b::polish_space"
  assumes w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
  shows "restrict \<omega> {0..T} = \<omega>"
proof -
  \<comment> \<open>unfolding \<open>path_metric_def\<close> INSIDE a simp call does not terminate here;
      the extensionality has to be extracted by hand.\<close>
  have "\<omega> \<in> mspace (cfunspace (top_of_set {0..T}) (euclidean_metric :: 'b metric))"
    using w unfolding path_metric_def .
  then have "\<omega> \<in> extensional (topspace (top_of_set ({0..T} :: real set)))"
    unfolding mspace_cfunspace by blast
  then have e: "\<omega> \<in> extensional {0..T}" by simp
  show ?thesis
  proof (rule ext)
    fix t :: real
    show "restrict \<omega> {0..T} t = \<omega> t"
    proof (cases "t \<in> {0..T}")
      case True then show ?thesis by simp
    next
      case False
      then have "\<omega> t = undefined" using extensional_arb[OF e] by simp
      with False show ?thesis by simp
    qed
  qed
qed

lemma pshift_in_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T x \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have "continuous_on {0..T} (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t)))"
    by (intro continuous_intros c)
  then show ?thesis unfolding pshift_def by (rule mspace_path_metricI)
qed

lemma pshift_zero:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T 0 \<omega> = \<omega>"
proof -
  have "pshift T 0 \<omega> = restrict \<omega> {0..T}"
    unfolding pshift_def by simp
  also have "\<dots> = \<omega>" by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

lemma pshift_pshift:
  fixes \<omega> :: "'n::finite pairpath"
  shows "pshift T y (pshift T x \<omega>) = pshift T (y + x) \<omega>"
  by (rule ext) (simp add: pshift_def add.assoc)

lemma pshift_inverse:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T (- x) (pshift T x \<omega>) = \<omega>"
  using pshift_pshift[of T "- x" x \<omega>] pshift_zero[OF w] by simp

lemma Lipschitz_pshift:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n pairpath) metric)
      (path_metric T :: ('n pairpath) metric) (pshift T x)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pshift T x \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric T :: ('n pairpath) metric)"
    by (intro funcsetI pshift_in_mspace)
  have key: "mdist (path_metric T) (pshift T x f) (pshift T x g)
      \<le> 1 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and g: "g \<in> mspace (path_metric T :: ('n pairpath) metric)" for f g
  proof -
    have sf: "pshift T x f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (rule pshift_in_mspace[OF f])
    have sg: "pshift T x g \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (rule pshift_in_mspace[OF g])
    have pw: "\<forall>t\<in>{0..T}. dist (f t) (g t) \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T f g] by blast
    have pws: "dist (pshift T x f t) (pshift T x g t)
        \<le> mdist (path_metric T) f g" if t: "t \<in> {0..T}" for t
    proof -
      have "dist (pshift T x f t) (pshift T x g t)
          = dist (x + fst (f t), snd (f t)) (x + fst (g t), snd (g t))"
        using t by (simp add: pshift_def)
      also have "\<dots> = dist (f t) (g t)"
        by (simp add: dist_prod_def dist_norm)
      finally show ?thesis using bspec[OF pw t] by simp
    qed
    have "mdist (path_metric T) (pshift T x f) (pshift T x g)
        \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T sf sg] pws by blast
    then show ?thesis by simp
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>g\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric T) (pshift T x f) (pshift T x g)
          \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 1] ballI key)
qed

lemma pshift_measurable:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "pshift T x
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pshift[OF T])

text \<open>The shift is measurable for the NATURAL FILTRATION too, at every
  level: it changes values, not times.  This is what lets the martingale
  clauses be transported --- the past of the shifted path is the shifted
  past.\<close>

lemma pshift_filtration_measurable:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "pshift T x \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spF: "space ?F = space Q" by simp
  show ?thesis
  proof (rule measurable_sigma_sets[OF sets_natural_filtration])
    show "(\<Union>i\<in>{0..u}. {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})
        \<subseteq> Pow (space Q)"
      by auto
    show "pshift T x \<in> space ?F \<rightarrow> space Q"
      using spQ spF by (auto intro: pshift_in_mspace)
    fix y
    assume "y \<in> (\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})"
    then obtain i A where i: "i \<in> {0..u}" and A: "A \<in> sets borel"
      and y: "y = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q" by blast
    have shim: "pshift T x \<omega> \<in> space Q" if "\<omega> \<in> space Q" for \<omega>
      using that spQ by (simp add: pshift_in_mspace)
    show "pshift T x -` y \<inter> space ?F \<in> sets ?F"
    proof (cases "i \<in> {0..T}")
      case True
      define g where "g = (\<lambda>p :: (real^'n) \<times> (real^'n^'n). (x + fst p, snd p))"
      have gb: "g \<in> borel_measurable borel"
        unfolding g_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have gA: "g -` A \<in> sets borel"
        using measurable_sets[OF gb A] by simp
      have "pshift T x -` y \<inter> space ?F
          = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` (g -` A) \<inter> space Q"
        using True y spF shim by (auto simp: pshift_apply g_def)
      moreover have "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` (g -` A) \<inter> space Q \<in> sets ?F"
        unfolding sets_natural_filtration
        by (rule sigma_sets.Basic)
          (use i gA in \<open>auto intro!: bexI[of _ i] exI[of _ "g -` A"]\<close>)
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "undefined \<in> A")
        case inA: True
        have "pshift T x -` y \<inter> space ?F = space ?F"
        proof
          show "pshift T x -` y \<inter> space ?F \<subseteq> space ?F" by blast
          show "space ?F \<subseteq> pshift T x -` y \<inter> space ?F"
          proof
            fix \<omega> :: "'n pairpath" assume w: "\<omega> \<in> space ?F"
            then have wq: "\<omega> \<in> space Q" using spF by simp
            have "pshift T x \<omega> i = undefined"
              by (rule pshift_outside[OF False])
            then show "\<omega> \<in> pshift T x -` y \<inter> space ?F"
              using inA w shim[OF wq] spF y by auto
          qed
        qed
        then show ?thesis using sets.top[of ?F] by simp
      next
        case notinA: False
        have "pshift T x -` y \<inter> space ?F = {}"
        proof (rule ccontr)
          assume "pshift T x -` y \<inter> space ?F \<noteq> {}"
          then obtain \<omega> :: "'n pairpath" where "pshift T x \<omega> \<in> y" by blast
          then have "pshift T x \<omega> i \<in> A" using y by blast
          moreover have "pshift T x \<omega> i = undefined"
            by (rule pshift_outside[OF False])
          ultimately show False using notinA by simp
        qed
        then show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>The shifted law\<close>

definition pshift_law ::
  "real \<Rightarrow> real^'n::finite \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "pshift_law T x Q = distr Q
     (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))
     (pshift T x)"

lemma sets_pshift_law[simp]:
  "sets (pshift_law T x Q)
     = sets (borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric)))"
  unfolding pshift_law_def by simp

lemma space_pshift_law:
  "space (pshift_law T x Q)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding pshift_law_def by (simp add: space_borel_of)

lemma prob_space_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T" and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "prob_space (pshift_law T x Q)"
proof -
  interpret P: prob_space Q by (rule prob)
  have m: "pshift T x \<in> Q \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  show ?thesis unfolding pshift_law_def by (rule P.prob_space_distr[OF m])
qed

lemma natural_filtration_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)
       = natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)"
  unfolding natural_filtration_def
  using space_of_path_sets[OF setsQ] space_pshift_law[of T x Q] by simp

text \<open>The martingale property transports.  Everything is arranged so that
  the FILTRATION does not move (\<open>natural_filtration_pshift_law\<close>): only the
  measure and the process change, and they change by the same shift, so
  the set-integral identity is the one \<open>Q\<close> already satisfies over the
  shifted event.\<close>

lemma martingale_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes T: "0 \<le> T" and prob: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
    and mg: "martingale Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. Z u (pshift T x \<omega>))"
  shows "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0 Z"
proof -
  let ?Q' = "pshift_law T x Q"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret MG: martingale Q ?F 0 "\<lambda>u \<omega>. Z u (pshift T x \<omega>)" by (rule mg)
  have FF: "natural_filtration ?Q' 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) = ?F"
    by (rule natural_filtration_pshift_law[OF setsQ])
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spQ': "space ?Q' = space Q" using spQ by (simp add: space_pshift_law)
  have setsQ': "sets ?Q' = sets ?B" by simp
  have prob': "prob_space ?Q'" by (rule prob_space_pshift_law[OF T prob setsQ])
  have fin': "finite_measure ?Q'" using prob' by (simp add: prob_space_def)
  have shm: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have SP: "Stochastic_Process.stochastic_process ?Q' (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF sets_pshift_law])
  interpret SF: finite_filtered_measure ?Q' ?F 0
    using Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
      [OF SP fin'] unfolding FF .
  have ZB: "Z w \<in> borel_measurable ?B" if w: "0 \<le> w" for w
  proof -
    have "Z w \<in> borel_measurable ?Q'"
      by (rule measurable_from_subalg[OF SF.subalgebras[OF w] Zm[OF w]])
    then show ?thesis using measurable_cong_sets[OF setsQ' refl] by blast
  qed
  show ?thesis
    unfolding FF
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?Q' ?F 0 Z"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      show "Z u \<in> borel_measurable (?F u)" by (rule Zm[OF u])
    qed
    show "integrable ?Q' (Z u)" if u: "0 \<le> u" for u
    proof -
      have "integrable ?Q' (Z u) \<longleftrightarrow> integrable Q (\<lambda>\<omega>. Z u (pshift T x \<omega>))"
        unfolding pshift_law_def by (rule integrable_distr_eq[OF shm ZB[OF u]])
      then show ?thesis using MG.integrable[OF u] by simp
    qed
    fix A and u v :: real
    assume A: "A \<in> ?F u" and uv: "0 \<le> u" "u \<le> v"
    have v0: "0 \<le> v" using uv by simp
    have AB: "A \<in> sets ?B"
      using A SF.subalgebras[OF uv(1)] setsQ' by (auto simp: subalgebra_def)
    have pA: "pshift T x -` A \<inter> space Q \<in> ?F u"
      using measurable_sets[OF pshift_filtration_measurable[OF setsQ] A] by simp
    have key: "set_lebesgue_integral ?Q' A (Z w)
        = set_lebesgue_integral Q (pshift T x -` A \<inter> space Q)
            (\<lambda>\<omega>. Z w (pshift T x \<omega>))" if w: "0 \<le> w" for w
    proof -
      have gb: "(\<lambda>\<omega> :: 'n pairpath. indicat_real A \<omega> *\<^sub>R Z w \<omega>)
          \<in> borel_measurable ?B"
        using AB ZB[OF w] by measurable
      have "set_lebesgue_integral ?Q' A (Z w)
          = (\<integral>\<omega>. indicat_real A \<omega> *\<^sub>R Z w \<omega> \<partial>?Q')"
        unfolding set_lebesgue_integral_def ..
      also have "\<dots> = (\<integral>\<omega>. indicat_real A (pshift T x \<omega>)
              *\<^sub>R Z w (pshift T x \<omega>) \<partial>Q)"
        unfolding pshift_law_def by (rule integral_distr[OF shm gb])
      also have "\<dots> = (\<integral>\<omega>. indicat_real (pshift T x -` A \<inter> space Q) \<omega>
              *\<^sub>R Z w (pshift T x \<omega>) \<partial>Q)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis unfolding set_lebesgue_integral_def .
    qed
    show "set_lebesgue_integral ?Q' A (Z u) = set_lebesgue_integral ?Q' A (Z v)"
      unfolding key[OF uv(1)] key[OF v0]
      by (rule MG.set_integral_eq[OF pA uv(1) uv(2)])
  qed
qed

subsection \<open>Three pieces of martingale algebra the AFP does not have\<close>

lemma martingale_add:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes mX: "martingale M F t0 X" and mY: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>u \<omega>. X u \<omega> + Y u \<omega>)"
proof -
  interpret MX: martingale M F t0 X by (rule mX)
  interpret MY: martingale M F t0 Y by (rule mY)
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process M F t0 (\<lambda>u \<omega>. X u \<omega> + Y u \<omega>)"
    proof (unfold_locales)
      fix i :: real assume i: "t0 \<le> i"
      show "(\<lambda>\<omega>. X i \<omega> + Y i \<omega>) \<in> borel_measurable (F i)"
        using MX.adapted[OF i] MY.adapted[OF i] by simp
    qed
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. X i \<omega> + Y i \<omega>)"
      by (intro Bochner_Integration.integrable_add MX.integrable MY.integrable)
    fix A and i j :: real
    assume A: "A \<in> F i" and ij: "t0 \<le> i" "i \<le> j"
    have j: "t0 \<le> j" using ij by simp
    have Ai: "A \<in> sets M"
      using A MX.subalgebras[OF ij(1)] by (auto simp: subalgebra_def)
    have siX: "set_integrable M A (X w)" if w: "t0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai MX.integrable[OF w]])
    have siY: "set_integrable M A (Y w)" if w: "t0 \<le> w" for w
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF Ai MY.integrable[OF w]])
    have split: "set_lebesgue_integral M A (\<lambda>\<omega>. X w \<omega> + Y w \<omega>)
        = set_lebesgue_integral M A (X w) + set_lebesgue_integral M A (Y w)"
      if w: "t0 \<le> w" for w
      by (rule set_integral_add(2)[OF siX[OF w] siY[OF w]])
    show "set_lebesgue_integral M A (\<lambda>\<omega>. X i \<omega> + Y i \<omega>)
        = set_lebesgue_integral M A (\<lambda>\<omega>. X j \<omega> + Y j \<omega>)"
      unfolding split[OF ij(1)] split[OF j]
      using MX.set_integral_eq[OF A ij] MY.set_integral_eq[OF A ij] by simp
  qed
qed

lemma martingale_add_const:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes ffm: "finite_filtered_measure M F t0" and mg: "martingale M F t0 X"
  shows "martingale M F t0 (\<lambda>u \<omega>. c + X u \<omega>)"
proof -
  interpret FM: finite_filtered_measure M F t0 by (rule ffm)
  have "martingale M F t0 (\<lambda>_ _. c)" by (rule FM.martingale_const)
  from martingale_add[OF this mg] show ?thesis .
qed

text \<open>The processes below differ at NEGATIVE times --- the shifted
  evaluation is \<open>undefined\<close> there, the shifted value is not --- and the
  martingale locale never looks at those, so a congruence above \<open>t\<^sub>0\<close> is
  what is needed.\<close>

lemma martingale_cong_ge:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  assumes mg: "martingale M F t0 X"
    and eq: "\<And>u. t0 \<le> u \<Longrightarrow> X u = Y u"
  shows "martingale M F t0 Y"
proof -
  interpret MX: martingale M F t0 X by (rule mg)
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process M F t0 Y"
    proof (unfold_locales)
      fix i :: real assume i: "t0 \<le> i"
      show "Y i \<in> borel_measurable (F i)"
        using MX.adapted[OF i] eq[OF i] by simp
    qed
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (Y i)"
      using MX.integrable eq by simp
    fix A and i j :: real
    assume A: "A \<in> F i" and ij: "t0 \<le> i" "i \<le> j"
    have j: "t0 \<le> j" using ij by simp
    show "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (Y j)"
      using MX.set_integral_eq[OF A ij] eq[OF ij(1)] eq[OF j] by simp
  qed
qed

subsection \<open>Almost-sure statements transport through the shift\<close>

text \<open>The shift is a BIJECTION of the path space with measurable inverse,
  so a null set for \<open>Q\<close> has a null image --- which is what lets the two
  almost-sure clauses of (1.7) be transported without any measurability
  hypothesis on the property itself.\<close>

lemma AE_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and ae: "AE \<omega> in Q. P (pshift T x \<omega>)"
  shows "AE \<omega> in pshift_law T x Q. P \<omega>"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spQ': "space (pshift_law T x Q) = space Q"
    using spQ by (simp add: space_pshift_law)
  have shm: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have shmQ: "pshift T (- x) \<in> Q \<rightarrow>\<^sub>M Q"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ setsQ] by blast
  obtain N1 where N1: "{\<omega> \<in> space Q. \<not> P (pshift T x \<omega>)} \<subseteq> N1"
    and N1z: "emeasure Q N1 = 0" and N1s: "N1 \<in> sets Q"
    by (rule AE_E[OF ae])
  define B where "B = pshift T (- x) -` N1 \<inter> space Q"
  have Bs: "B \<in> sets Q" unfolding B_def by (rule measurable_sets[OF shmQ N1s])
  have pre: "pshift T x -` B \<inter> space Q = N1 \<inter> space Q"
  proof
    show "pshift T x -` B \<inter> space Q \<subseteq> N1 \<inter> space Q"
    proof
      fix \<omega> :: "'n pairpath"
      assume "\<omega> \<in> pshift T x -` B \<inter> space Q"
      then have w: "\<omega> \<in> space Q" and n: "pshift T (- x) (pshift T x \<omega>) \<in> N1"
        unfolding B_def by auto
      have "pshift T (- x) (pshift T x \<omega>) = \<omega>"
        using w spQ by (simp add: pshift_inverse)
      with n w show "\<omega> \<in> N1 \<inter> space Q" by simp
    qed
    show "N1 \<inter> space Q \<subseteq> pshift T x -` B \<inter> space Q"
    proof
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> N1 \<inter> space Q"
      then have n: "\<omega> \<in> N1" and w: "\<omega> \<in> space Q" by auto
      have e: "pshift T (- x) (pshift T x \<omega>) = \<omega>"
        using w spQ by (simp add: pshift_inverse)
      have "pshift T x \<omega> \<in> space Q" using w spQ by (simp add: pshift_in_mspace)
      then show "\<omega> \<in> pshift T x -` B \<inter> space Q"
        unfolding B_def using n w e by simp
    qed
  qed
  have "emeasure (pshift_law T x Q) B = emeasure Q (pshift T x -` B \<inter> space Q)"
    unfolding pshift_law_def
    by (rule emeasure_distr[OF shm]) (use Bs setsQ in simp)
  also have "\<dots> = emeasure Q (N1 \<inter> space Q)" using pre by simp
  also have "\<dots> = 0"
    using N1z sets.sets_into_space[OF N1s] by (simp add: Int_absorb2)
  finally have Bnull: "emeasure (pshift_law T x Q) B = 0" .
  have sub: "{\<omega> \<in> space (pshift_law T x Q). \<not> P \<omega>} \<subseteq> B"
  proof
    fix \<omega>' :: "'n pairpath"
    assume "\<omega>' \<in> {\<omega> \<in> space (pshift_law T x Q). \<not> P \<omega>}"
    then have w': "\<omega>' \<in> space Q" and nP: "\<not> P \<omega>'" using spQ' by auto
    have wm: "\<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w' spQ by simp
    have e: "pshift T x (pshift T (- x) \<omega>') = \<omega>'"
      using pshift_pshift[of T x "- x" \<omega>'] pshift_zero[OF wm] by simp
    have "pshift T (- x) \<omega>' \<in> space Q"
      using wm spQ by (simp add: pshift_in_mspace)
    then have "pshift T (- x) \<omega>' \<in> N1" using N1 nP e by auto
    then show "\<omega>' \<in> B" unfolding B_def using w' by simp
  qed
  have Bn: "B \<in> null_sets (pshift_law T x Q)"
    using Bs Bnull setsQ by (simp add: null_sets_def)
  show ?thesis
    unfolding eventually_ae_filter using sub Bn by blast
qed

subsection \<open>The class is shift-equivariant\<close>

text \<open>The one algebraic input: translating \<open>X\<close> splits the compensated
  process into ITSELF, a term LINEAR in \<open>X\<close>, and a constant --- so it stays
  a martingale.\<close>

lemma comp_shift_split:
  fixes x v :: "real^'n::finite" and w :: "real^'n^'n"
  shows "outerp x + ((outerp v - w) + (\<chi> i j. x $ i * v $ j + v $ i * x $ j))
       = outerp (x + v) - w"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma bounded_linear_cross:
  fixes x :: "real^'n::finite"
  shows "bounded_linear
      (\<lambda>v :: real^'n. (\<chi> i j. x $ i * v $ j + v $ i * x $ j) :: real^'n^'n)"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: vec_eq_iff algebra_simps)

theorem paper_pair_class_pshift:
  fixes Q :: "('n::finite pairpath) measure" and x x0 :: "real^'n"
  assumes T: "0 \<le> T" and Q: "Q \<in> paper_pair_class k L T x0"
  shows "pshift_law T x Q \<in> paper_pair_class k L T (x + x0)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?cross = "\<lambda>v :: real^'n. (\<chi> i j. x $ i * v $ j + v $ i * x $ j) :: real^'n^'n"
  have prob: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have finQ: "finite_measure Q" using prob by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsQ])
  have ffm: "finite_filtered_measure Q ?F 0"
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration
        [OF SP finQ])
  have minI: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T by simp
  have mX: "martingale Q ?F 0 (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule paper_pair_class_X_martingale[OF Q])
  interpret MX: martingale Q ?F 0 "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T))"
    by (rule mX)
  \<comment> \<open>the two almost-sure clauses\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x0 \<and> snd (\<omega> 0) = 0"
    using Q unfolding paper_pair_class_def by blast
  have st': "AE \<omega> in pshift_law T x Q. fst (\<omega> 0) = x + x0 \<and> snd (\<omega> 0) = 0"
  proof (rule AE_pshift_law[OF T setsQ])
    show "AE \<omega> in Q. fst (pshift T x \<omega> 0) = x + x0
        \<and> snd (pshift T x \<omega> 0) = 0"
    proof (rule eventually_mono[OF st])
      fix \<omega> :: "'n pairpath"
      assume "fst (\<omega> 0) = x0 \<and> snd (\<omega> 0) = 0"
      then show "fst (pshift T x \<omega> 0) = x + x0 \<and> snd (pshift T x \<omega> 0) = 0"
        using T by (simp add: pshift_fst pshift_snd)
    qed
  qed
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding paper_pair_class_def by blast
  have dq': "AE \<omega> in pshift_law T x Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  proof (rule AE_pshift_law[OF T setsQ])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
          \<in> sconstraint k L"
    proof (rule eventually_mono[OF dq])
      fix \<omega> :: "'n pairpath"
      assume q: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      show "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
            \<in> sconstraint k L"
      proof (intro allI impI)
        fix s t :: real
        assume s: "0 \<le> s" and stt: "s < t" and tT: "t \<le> T"
        have sI: "s \<in> {0..T}" using s stt tT by simp
        have tI: "t \<in> {0..T}" using s stt tT by simp
        show "(1 / (t - s)) *\<^sub>R (snd (pshift T x \<omega> t) - snd (pshift T x \<omega> s))
            \<in> sconstraint k L"
          using q s stt tT by (simp add: pshift_snd[OF sI] pshift_snd[OF tI])
      qed
    qed
  qed
  \<comment> \<open>the two martingale clauses\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T))) \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u by (rule MX.adapted[OF u])
  have mgX: "martingale Q ?F 0 (\<lambda>u \<omega>. fst (pshift T x \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_add_const[OF ffm mX, of x]])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. x + fst (\<omega> (min u T)))
        = (\<lambda>\<omega>. fst (pshift T x \<omega> (min u T)))"
      by (rule ext) (simp add: pshift_fst[OF minI[OF u]])
  qed
  have Xshift: "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule martingale_pshift_law[OF T prob setsQ Zm mgX])
  have mC: "martingale Q ?F 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule paper_pair_class_compensated_martingale[OF Q])
  interpret MC: martingale Q ?F 0
      "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
    by (rule mC)
  have mCross: "martingale Q ?F 0 (\<lambda>u \<omega>. ?cross (fst (\<omega> (min u T))))"
    by (rule martingale_bounded_linear_image[OF bounded_linear_cross mX])
  have sum2: "martingale Q ?F 0 (\<lambda>u \<omega>. outerp x
      + ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
         + ?cross (fst (\<omega> (min u T)))))"
    by (rule martingale_add_const[OF ffm martingale_add[OF mC mCross]])
  have ZmC: "(\<lambda>\<omega> :: 'n pairpath.
      outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
        \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u by (rule MC.adapted[OF u])
  have mgC: "martingale Q ?F 0 (\<lambda>u \<omega>.
      outerp (fst (pshift T x \<omega> (min u T))) - snd (pshift T x \<omega> (min u T)))"
  proof (rule martingale_cong_ge[OF sum2])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp x
        + ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))
           + ?cross (fst (\<omega> (min u T)))))
        = (\<lambda>\<omega>. outerp (fst (pshift T x \<omega> (min u T)))
           - snd (pshift T x \<omega> (min u T)))"
      by (rule ext)
        (simp add: pshift_fst[OF minI[OF u]] pshift_snd[OF minI[OF u]]
          comp_shift_split)
  qed
  have Cshift: "martingale (pshift_law T x Q)
      (natural_filtration (pshift_law T x Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule martingale_pshift_law[OF T prob setsQ ZmC mgC])
  show ?thesis
    unfolding paper_pair_class_def
  proof (intro CollectI conjI)
    show "prob_space (pshift_law T x Q)"
      by (rule prob_space_pshift_law[OF T prob setsQ])
    show "sets (pshift_law T x Q) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" by simp
    show "AE \<omega> in pshift_law T x Q. fst (\<omega> 0) = x + x0 \<and> snd (\<omega> 0) = 0"
      by (rule st')
    show "AE \<omega> in pshift_law T x Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule dq')
    show "martingale (pshift_law T x Q)
        (natural_filtration (pshift_law T x Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))" by (rule Xshift)
    show "martingale (pshift_law T x Q)
        (natural_filtration (pshift_law T x Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
      by (rule Cshift)
  qed
qed

text \<open>Larsson--Ruf Prop. 2.2(ii) for the paper's class, in the form the
  value function needs: the class at \<open>x\<close> is the \<open>x\<close>-translate of the class
  at \<open>0\<close>.  The reverse inclusion is the same theorem at \<open>-x\<close>, plus the fact
  that the two push-forwards compose to the identity.\<close>

corollary paper_pair_class_shift_image:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "paper_pair_class k L T x = pshift_law T x ` paper_pair_class k L T 0"
proof
  show "pshift_law T x ` paper_pair_class k L T 0 \<subseteq> paper_pair_class k L T x"
  proof
    fix R :: "('n pairpath) measure"
    assume "R \<in> pshift_law T x ` paper_pair_class k L T 0"
    then obtain Q0 where Q0: "Q0 \<in> paper_pair_class k L T 0"
      and R: "R = pshift_law T x Q0" by blast
    have "pshift_law T x Q0 \<in> paper_pair_class k L T (x + 0)"
      by (rule paper_pair_class_pshift[OF T Q0])
    then show "R \<in> paper_pair_class k L T x" using R by simp
  qed
  show "paper_pair_class k L T x \<subseteq> pshift_law T x ` paper_pair_class k L T 0"
  proof
    fix Q :: "('n pairpath) measure"
    assume Q: "Q \<in> paper_pair_class k L T x"
    let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
    have setsQ: "sets Q = sets ?B" by (rule paper_pair_class_sets[OF Q])
    have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
      by (rule space_of_path_sets[OF setsQ])
    have mem0: "pshift_law T (- x) Q \<in> paper_pair_class k L T 0"
      using paper_pair_class_pshift[OF T Q, of "- x"] by simp
    have shm: "pshift T (- x) \<in> Q \<rightarrow>\<^sub>M ?B"
      using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
    have shm2: "pshift T x \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule pshift_measurable[OF T])
    have "pshift_law T x (pshift_law T (- x) Q)
        = distr Q ?B (pshift T x \<circ> pshift T (- x))"
      unfolding pshift_law_def by (rule distr_distr[OF shm2 shm])
    also have "\<dots> = distr Q ?B (\<lambda>\<omega>. \<omega>)"
    proof (rule distr_cong)
      show "Q = Q" ..
      show "sets ?B = sets ?B" ..
      fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
      then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using spQ by simp
      show "(pshift T x \<circ> pshift T (- x)) \<omega> = \<omega>"
        using pshift_pshift[of T x "- x" \<omega>] pshift_zero[OF wm] by simp
    qed
    also have "\<dots> = Q" by (rule distr_id2[OF setsQ[symmetric]])
    finally have "pshift_law T x (pshift_law T (- x) Q) = Q" .
    with mem0 show "Q \<in> pshift_law T x ` paper_pair_class k L T 0" by force
  qed
qed

section \<open>NC: the value function of Eq. (1.6) is upper semicontinuous\<close>

subsection \<open>The shift is an involution on laws\<close>

lemma pshift_law_compose:
  fixes Q :: "('n::finite pairpath) measure" and x y :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pshift_law T y (pshift_law T x Q) = pshift_law T (y + x) Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have shx: "pshift T x \<in> Q \<rightarrow>\<^sub>M ?B"
    using pshift_measurable[OF T] measurable_cong_sets[OF setsQ refl] by blast
  have shy: "pshift T y \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule pshift_measurable[OF T])
  have "pshift_law T y (pshift_law T x Q) = distr Q ?B (pshift T y \<circ> pshift T x)"
    unfolding pshift_law_def by (rule distr_distr[OF shy shx])
  also have "\<dots> = distr Q ?B (pshift T (y + x))"
    by (rule distr_cong) (auto simp: pshift_pshift)
  finally show ?thesis unfolding pshift_law_def .
qed

lemma pshift_law_zero:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
  shows "pshift_law T 0 Q = Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have "pshift_law T 0 Q = distr Q ?B (\<lambda>\<omega>. \<omega>)"
    unfolding pshift_law_def
    by (rule distr_cong) (use spQ in \<open>auto simp: pshift_zero\<close>)
  also have "\<dots> = Q" by (rule distr_id2[OF setsQ[symmetric]])
  finally show ?thesis .
qed

text \<open>Hence the almost-sure transfer is an EQUIVALENCE, not just an
  implication: apply it at \<open>-x\<close> to the shifted law.\<close>

lemma AE_pshift_law_iff:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(AE \<omega> in pshift_law T x Q. P \<omega>)
       \<longleftrightarrow> (AE \<omega> in Q. P (pshift T x \<omega>))"
proof
  assume "AE \<omega> in Q. P (pshift T x \<omega>)"
  then show "AE \<omega> in pshift_law T x Q. P \<omega>"
    by (rule AE_pshift_law[OF T setsQ])
next
  let ?Q' = "pshift_law T x Q"
  assume h: "AE \<omega> in ?Q'. P \<omega>"
  have setsQ': "sets ?Q' = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" by simp
  have spQ': "space ?Q' = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_pshift_law)
  have id': "AE \<omega> in ?Q'. pshift T x (pshift T (- x) \<omega>) = \<omega>"
  proof (rule AE_I2)
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space ?Q'"
    then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using spQ' by simp
    show "pshift T x (pshift T (- x) \<omega>) = \<omega>"
      using pshift_pshift[of T x "- x" \<omega>] pshift_zero[OF wm] by simp
  qed
  have h2: "AE \<omega> in ?Q'. P (pshift T x (pshift T (- x) \<omega>))"
    using h id' by eventually_elim simp
  have step: "AE \<omega> in pshift_law T (- x) ?Q'. P (pshift T x \<omega>)"
    by (rule AE_pshift_law[OF T setsQ' h2])
  \<comment> \<open>the measure INSIDE an \<open>AE\<close> cannot be rewritten by simp; \<open>unfolding\<close>
      acts on the chained fact and does it.\<close>
  have eqQ: "pshift_law T (- x) ?Q' = Q"
    using pshift_law_compose[OF T setsQ, of "- x"] pshift_law_zero[OF setsQ]
    by simp
  show "AE \<omega> in Q. P (pshift T x \<omega>)" using step unfolding eqQ .
qed

lemma ess_inf_time_pshift_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "ess_inf_time (pshift_law T x Q) g
       = ess_inf_time Q (\<lambda>\<omega>. g (pshift T x \<omega>))"
proof -
  have "{c. AE \<omega> in pshift_law T x Q. c \<le> ennreal (g \<omega>)}
      = {c. AE \<omega> in Q. c \<le> ennreal (g (pshift T x \<omega>))}"
    by (intro Collect_cong) (rule AE_pshift_law_iff[OF T setsQ])
  then show ?thesis unfolding ess_inf_time_def by simp
qed

subsection \<open>The exit functional of (1.6) IS the shifted exit time\<close>

text \<open>Both sides are the same infimum: the times range over \<open>{0..T}\<close>, and
  there \<open>fst (pshift T x \<omega> r) = x + fst (\<omega> r) = fst ((x,0) + \<omega> r)\<close>.  No
  path-space membership is needed.\<close>

lemma pexit_pshift_eq_etime:
  fixes \<omega> :: "'n::finite pairpath" and K :: "(real^'n) set" and x :: "real^'n"
  shows "pexit T K (\<lambda>t. fst (pshift T x \<omega> t))
       = etime T {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}
           (\<lambda>s w. (x, 0) + w s) \<omega>"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> fst (pshift T x \<omega> r) \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> T
            \<and> (x, 0) + \<omega> r \<in> {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}}"
    by (auto simp: pshift_fst)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

subsection \<open>Turning a supremum of \<open>ennreal\<close>s into a supremum of reals\<close>

lemma ennreal_Sup_image:
  fixes S :: "real set" and B :: real
  assumes ne: "S \<noteq> {}" and bnd: "\<And>s. s \<in> S \<Longrightarrow> 0 \<le> s \<and> s \<le> B"
  shows "Sup (ennreal ` S) = ennreal (Sup S)"
proof -
  have bdd: "bdd_above S" using bnd by (intro bdd_aboveI[of _ B]) auto
  have le1: "Sup (ennreal ` S) \<le> ennreal (Sup S)"
  proof (rule Sup_least)
    fix e assume "e \<in> ennreal ` S"
    then obtain s where s: "s \<in> S" and e: "e = ennreal s" by blast
    have "s \<le> Sup S" using s bdd by (rule cSup_upper)
    then show "e \<le> ennreal (Sup S)" unfolding e by (rule ennreal_leI)
  qed
  have leB: "Sup (ennreal ` S) \<le> ennreal B"
    by (rule Sup_least) (use bnd in \<open>auto intro: ennreal_leI\<close>)
  have fin: "Sup (ennreal ` S) < \<top>"
    using leB ennreal_less_top by (rule order_le_less_trans)
  have "Sup S \<le> enn2real (Sup (ennreal ` S))"
  proof (rule cSup_least[OF ne])
    fix s assume s: "s \<in> S"
    have "ennreal s \<le> Sup (ennreal ` S)" using s by (intro Sup_upper) auto
    also have "\<dots> = ennreal (enn2real (Sup (ennreal ` S)))"
      using fin by simp
    finally show "s \<le> enn2real (Sup (ennreal ` S))" by simp
  qed
  then have "ennreal (Sup S) \<le> ennreal (enn2real (Sup (ennreal ` S)))"
    by (rule ennreal_leI)
  then have le2: "ennreal (Sup S) \<le> Sup (ennreal ` S)"
    using fin by simp
  from le1 le2 show ?thesis by simp
qed

subsection \<open>Eq. (1.6) as a shifted supremum over the class at \<open>0\<close>\<close>

theorem paper_v_eq_vshift_sup:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  \<comment> \<open>the \<open>0\<close> MUST be annotated: without it the class in the assumption
      elaborates at a fresh type variable and \<open>rule ne\<close> silently fails.\<close>
  assumes T: "0 \<le> T" and ne: "paper_pair_class k L T (0 :: real^'n) \<noteq> {}"
  shows "paper_v k L T K x
      = ennreal (Sup (vshift T {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K} (x, 0)
          ` paper_pair_class k L T 0))"
proof -
  let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
  let ?C = "paper_pair_class k L T 0"
  let ?g = "\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))"
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" if "Q \<in> ?C" for Q
    by (rule paper_pair_class_sets[OF that])
  have probQ: "prob_space Q" if "Q \<in> ?C" for Q :: "('n pairpath) measure"
    by (rule paper_pair_class_prob[OF that])
  have key: "ess_inf_time (pshift_law T x Q) ?g = ennreal (vshift T ?A (x, 0) Q)"
    if Q: "Q \<in> ?C" for Q
  proof -
    have "ess_inf_time (pshift_law T x Q) ?g
        = ess_inf_time Q (\<lambda>\<omega>. ?g (pshift T x \<omega>))"
      by (rule ess_inf_time_pshift_law[OF T setsQ[OF Q]])
    also have "\<dots> = ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s))"
      by (rule arg_cong[where f = "ess_inf_time Q"])
        (rule ext, rule pexit_pshift_eq_etime)
    finally have e: "ess_inf_time (pshift_law T x Q) ?g
        = ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s))" .
    have le: "ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s)) \<le> ennreal T"
      by (rule ess_inf_time_le_const[OF probQ[OF Q]]) (rule etime_le_T[OF T])
    have fin: "ess_inf_time Q (etime T ?A (\<lambda>s w. (x, 0) + w s)) < \<top>"
      using le ennreal_less_top by (rule order_le_less_trans)
    show ?thesis unfolding e vshift_def using fin by simp
  qed
  have img: "paper_pair_class k L T x = pshift_law T x ` ?C"
    by (rule paper_pair_class_shift_image[OF T])
  have "paper_v k L T K x
      = Sup ((\<lambda>Q. ess_inf_time Q ?g) ` (pshift_law T x ` ?C))"
    unfolding paper_v_def img ..
  also have "\<dots> = Sup ((\<lambda>Q. ess_inf_time (pshift_law T x Q) ?g) ` ?C)"
    by (simp add: image_image)
  also have "\<dots> = Sup ((\<lambda>Q. ennreal (vshift T ?A (x, 0) Q)) ` ?C)"
    using key by (intro arg_cong[where f = Sup] image_cong refl)
  also have "\<dots> = Sup (ennreal ` (vshift T ?A (x, 0) ` ?C))"
    by (simp add: image_image)
  also have "\<dots> = ennreal (Sup (vshift T ?A (x, 0) ` ?C))"
  proof (rule ennreal_Sup_image[where B = T])
    show "vshift T ?A (x, 0) ` ?C \<noteq> {}"
      unfolding image_is_empty by (rule ne)
    fix s :: real assume "s \<in> vshift T ?A (x, 0) ` ?C"
    then obtain Q where Q: "Q \<in> ?C" and s: "s = vshift T ?A (x, 0) Q" by blast
    have "0 \<le> s" unfolding s vshift_def by simp
    moreover have "s \<le> T" unfolding s by (rule vshift_le[OF T probQ[OF Q]])
    ultimately show "0 \<le> s \<and> s \<le> T" by blast
  qed
  finally show ?thesis .
qed

subsection \<open>Clause (1) of Theorem 1.1, for the paper's own value function\<close>

text \<open>\<open>paper_v\<close> IS Eq. (1.6): the supremum, over the class (1.7) started at
  \<open>x\<close>, of the essential infimum of the exit time from \<open>K\<close>.  Upper
  semicontinuity in \<open>x\<close> is exactly clause (1).  Every input is now proved:
  the class is sequentially compact (NC-2 + NC-3) and shift-equivariant
  (Prop. 2.2(ii)), so Berge applies through
  \<open>Section_2_Usc.vshift_sup_usc_of_seq_compact\<close>.  The only hypothesis left
  is NONEMPTINESS of the class at \<open>0\<close>, which is a separate construction.\<close>

theorem paper_v_usc:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and b :: ennreal
  assumes T: "0 < T" and L: "0 \<le> L" and K: "closed K"
    and ne: "paper_pair_class k L T (0 :: real^'n) \<noteq> {}"
    and lt: "paper_v k L T K x < b"
  shows "eventually (\<lambda>y. paper_v k L T K y < b) (nhds x)"
proof -
  let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
  let ?C = "paper_pair_class k L T (0 :: real^'n)"
  let ?S = "\<lambda>y :: real^'n. Sup (vshift T ?A (y, 0) ` ?C)"
  let ?e = "\<lambda>y :: real^'n. (y, 0 :: real^'n^'n)"
  have T0: "0 \<le> T" using T by simp
  have Aopen: "open ?A"
  proof -
    have e: "?A = (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) -` (- K)" by auto
    show ?thesis unfolding e by (rule open_vimage_fst[OF open_Compl[OF K]])
  qed
  have probQ: "prob_space Q" if "Q \<in> ?C" for Q :: "('n pairpath) measure"
    by (rule paper_pair_class_prob[OF that])
  have eqv: "paper_v k L T K y = ennreal (?S y)" for y :: "real^'n"
    by (rule paper_v_eq_vshift_sup[OF T0 ne])
  have bdd: "bdd_above (vshift T ?A (y, 0) ` ?C)" for y :: "real^'n"
    by (rule bdd_aboveI[of _ T]) (auto intro: vshift_le[OF T0] probQ)
  have S0: "0 \<le> ?S y" for y :: "real^'n"
  proof -
    from ne obtain Q0 :: "('n pairpath) measure" where Q0: "Q0 \<in> ?C" by auto
    have "0 \<le> vshift T ?A (y, 0) Q0" unfolding vshift_def by simp
    also have "\<dots> \<le> ?S y" using Q0 bdd by (intro cSup_upper) auto
    finally show ?thesis .
  qed
  have usc: "eventually (\<lambda>z. Sup (vshift T ?A z ` ?C) < c) (nhds (?e x))"
    if c: "?S x < c" for c :: real
  proof (rule vshift_sup_usc_of_seq_compact[OF T0 Aopen])
    show "?C \<noteq> {}" by (rule ne)
    show "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))" if "Q \<in> ?C" for Q
      by (rule paper_pair_class_sets[OF that])
    show "prob_space Q" if "Q \<in> ?C" for Q by (rule probQ[OF that])
    show "\<exists>Lm r. Lm \<in> ?C \<and> strict_mono r \<and> weak_conv_on (\<sigma> \<circ> r) Lm sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
      if "range \<sigma> \<subseteq> ?C" for \<sigma> :: "nat \<Rightarrow> ('n pairpath) measure"
    proof -
      have mem: "\<sigma> m \<in> ?C" for m using that by auto
      have ex: "\<exists>a Q. strict_mono a \<and> Q \<in> ?C \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
        by (rule paper_pair_class_convergent_subsequence[OF T L mem])
      obtain a where ea: "\<exists>Q. strict_mono a \<and> Q \<in> ?C
          \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
              (mtopology_of (path_metric T :: ('n pairpath) metric))"
        using ex by (rule exE)
      obtain Q where h: "strict_mono a \<and> Q \<in> ?C
          \<and> weak_conv_on (\<sigma> \<circ> a) Q sequentially
              (mtopology_of (path_metric T :: ('n pairpath) metric))"
        using ea by (rule exE)
      show ?thesis
        by (rule exI[of _ Q], rule exI[of _ a]) (use h in simp)
    qed
    show "?S x < c" by (rule c)
  qed
  obtain c :: real where cS: "?S x < c" and cb: "ennreal c \<le> b"
  proof (cases "b = \<top>")
    case True
    show thesis by (rule that[of "?S x + 1"]) (simp_all add: True)
  next
    case False
    then have blt: "b < \<top>" by (simp add: less_top)
    have bb: "b = ennreal (enn2real b)" using blt by simp
    have "ennreal (?S x) < b" using lt eqv by simp
    then have "ennreal (?S x) < ennreal (enn2real b)" using bb by simp
    \<comment> \<open>\<open>ennreal_less_iff\<close> carries its nonnegativity on the LEFT argument.\<close>
    then have "?S x < enn2real b"
      using S0[of x] by (simp add: ennreal_less_iff)
    then show thesis by (rule that) (use bb in simp)
  qed
  from usc[OF cS] obtain U where U: "open U" and xU: "?e x \<in> U"
    and UP: "\<And>z. z \<in> U \<Longrightarrow> Sup (vshift T ?A z ` ?C) < c"
    unfolding eventually_nhds by blast
  show ?thesis
    unfolding eventually_nhds
  proof (intro exI[of _ "?e -` U"] conjI ballI)
    show "open (?e -` U)"
      by (rule open_vimage[OF U]) (intro continuous_intros)
    show "x \<in> ?e -` U" using xU by simp
    fix y :: "real^'n" assume y: "y \<in> ?e -` U"
    have "?S y < c" using UP[of "?e y"] y by simp
    then have "ennreal (?S y) < ennreal c"
      using S0[of y] by (simp add: ennreal_less_iff)
    also have "\<dots> \<le> b" by (rule cb)
    finally show "paper_v k L T K y < b" using eqv[of y] by simp
  qed
qed

section \<open>Towards nonemptiness: laws of concrete pair processes\<close>

text \<open>The reusable core.  A pair PROCESS on some filtered probability
  space pushes forward to a pair LAW, and a martingale for the process's
  own filtration is a martingale for the law's NATURAL filtration --- the
  tower property, in the set-integral form: the natural filtration of the
  law pulls back INTO the process's filtration, because the process is
  adapted, and the set-integral identity is then the one the process
  already satisfies over the pulled-back event.\<close>

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
    \<comment> \<open>\<open>adap\<close> has TWO \<And>-bound variables, so an \<open>OF\<close> against it produces
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
  DETERMINISTIC time \<open>T\<close>.  (The repo's
  \<open>Deterministic_Radius_Market.martingale_stopped_deterministic\<close> is not
  reachable from here.)\<close>

lemma martingale_stopped_const:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes T: "0 \<le> T" and mg: "martingale M F 0 X"
  shows "martingale M F 0 (\<lambda>u \<omega>. X (min u T) \<omega>)"
proof -
  interpret MX: martingale M F 0 X by (rule mg)
  have mu: "0 \<le> min u T" if "0 \<le> u" for u using that T by simp
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>u \<omega>. X (min u T) \<omega>)"
    proof (unfold_locales)
      fix u :: real assume u: "0 \<le> u"
      have "X (min u T) \<in> borel_measurable (F (min u T))"
        by (rule MX.adapted[OF mu[OF u]])
      moreover have "borel_measurable (F (min u T)) \<subseteq> borel_measurable (F u)"
        by (rule MX.borel_measurable_mono[OF mu[OF u]]) simp
      ultimately show "X (min u T) \<in> borel_measurable (F u)" by blast
    qed
    show "integrable M (\<lambda>\<omega>. X (min u T) \<omega>)" if u: "0 \<le> u" for u
      using MX.integrable[OF mu[OF u]] by simp
    fix A and u v :: real
    assume A: "A \<in> F u" and uv: "0 \<le> u" "u \<le> v"
    show "set_lebesgue_integral M A (\<lambda>\<omega>. X (min u T) \<omega>)
        = set_lebesgue_integral M A (\<lambda>\<omega>. X (min v T) \<omega>)"
    proof (cases "u \<le> T")
      case True
      then have mu': "min u T = u" by simp
      show ?thesis
      proof (cases "v \<le> T")
        case True
        then have mv': "min v T = v" by simp
        show ?thesis unfolding mu' mv'
          using MX.set_integral_eq[OF A uv] by simp
      next
        case False
        then have mv': "min v T = T" by simp
        show ?thesis unfolding mu' mv'
          using MX.set_integral_eq[OF A uv(1) True] by simp
      qed
    next
      case False
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    qed
  qed
qed

section \<open>The off-diagonal covariation of Brownian motion\<close>

text \<open>The one input the nonemptiness witness needs that the market locale
  does not supply: it asserts only the DIAGONAL compensator
  (\<open>coord_Z_martingale\<close>), whereas the paper's class asks for the whole
  matrix \<open>outerp X - Y\<close>.  Off the diagonal the compensator is \<open>0\<close>, so what
  is needed is that \<open>W\<^sub>i W\<^sub>j\<close> is a martingale for \<open>i \<noteq> j\<close>.

  \<open>bm_paths = Pi\<^sub>M UNIV (\<lambda>_. wiener_pre)\<close>, so the coordinates are
  independent by construction --- that is
  \<open>Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate\<close>, and everything
  else here is bookkeeping on top of it.\<close>

lemma bm_coordinates_indep:
  "prob_space.indep_vars (bm_paths :: ('n::finite \<Rightarrow> real \<Rightarrow> real) measure)
      (\<lambda>_. wiener_pre) (\<lambda>k \<omega>. \<omega> k) UNIV"
proof -
  \<comment> \<open>\<open>Kolmogorov_Chentsov_Extras.indep_vars_PiM_coordinate\<close> is NOT in scope
      here, so its six-line argument is repeated: the identity distribution
      of a product IS the product of its component distributions, which is
      exactly the criterion \<open>indep_vars_iff_distr_eq_PiM'\<close>.  \<open>BMC\<close> is the
      \<open>product_prob_space\<close> interpretation already present in
      \<open>Brownian_Market\<close>.\<close>
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

text \<open>\<open>Brownian_Market.bm_meas_increment_indep_var\<close> makes the past
  independent of ONE COORDINATE of the increment.  Its argument never uses
  more than that the second function factors through the VECTOR increment,
  so it generalises verbatim to any Borel function of it --- and \<open>v \<mapsto> v$i
  \<sqdot> v$j\<close> is one.\<close>

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

text \<open>Hence the set-integral form: over a PAST event the cross increment
  has integral zero.  This is the off-diagonal analogue of
  \<open>Brownian_Market.bm_set_integral_coord_sq_eq\<close>, and the compensator is
  \<open>0\<close> rather than \<open>t - s\<close> precisely because the coordinates are
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

text \<open>The martingale identity for the off-diagonal product, in
  set-integral form.  Writing \<open>X\<^sub>i(v)X\<^sub>j(v) - X\<^sub>i(u)X\<^sub>j(u)
  = X\<^sub>i(u)\<Delta>\<^sub>j + X\<^sub>j(u)\<Delta>\<^sub>i + \<Delta>\<^sub>i\<Delta>\<^sub>j\<close>, the first two terms die by
  \<open>Brownian_Market.bm_meas_increment_product_zero\<close> (the multiplier is
  past-measurable) and the third by \<open>bm_cross_set_integral_zero\<close>.\<close>

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

text \<open>Transfer to the CONTINUOUS modification, which is the process the
  path space wants.  This is \<open>Modification_Transfer.martingale_of_modification_gen\<close>,
  exactly as \<open>Brownian_Continuous.martingale_cbm_coord_square\<close> does for the
  diagonal.\<close>

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

text \<open>The whole matrix, assembled from its entries by \<open>martingale_matI\<close>:
  the DIAGONAL is \<open>Brownian_Continuous.martingale_cbm_coord_square\<close> (whose
  compensator \<open>\<integral>\<^sub>0\<^sup>t (mat 1)\<^sub>i\<^sub>i\<close> is just \<open>t\<close>, so \<open>martingale_cong_ge\<close>
  rewrites it), the OFF-DIAGONAL is \<open>martingale_cbm_cross\<close> with compensator
  \<open>0\<close>.\<close>

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

section \<open>NC: the paper's class is NONEMPTY\<close>

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
      \<open>Paper_Class.paper_pair_class_diffquot_limit\<close>\<close>
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
    \<in> paper_pair_class k L T (0 :: real^'n)"
  unfolding paper_pair_class_def
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

corollary paper_pair_class_nonempty:
  assumes T: "0 \<le> T" and L: "1 \<le> L"
  shows "paper_pair_class k L T (0 :: real^'n::finite) \<noteq> {}"
  using bmpair_law_in_paper_pair_class[OF T L] by blast

text \<open>Hence clause (1) of Theorem 1.1 for the paper's own value function,
  with NO hypothesis left beyond the paper's own standing ones: \<open>0 < T\<close>,
  \<open>1 \<le> L\<close> (which is (1.5)) and \<open>K\<close> closed.\<close>

corollary paper_v_usc_unconditional:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and b :: ennreal
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
    and lt: "paper_v k L T K x < b"
  shows "eventually (\<lambda>y. paper_v k L T K y < b) (nhds x)"
proof (rule paper_v_usc[OF T _ K _ lt])
  show "0 \<le> L" using L by simp
  show "paper_pair_class k L T (0 :: real^'n) \<noteq> {}"
    using T L by (intro paper_pair_class_nonempty) simp_all
qed

section \<open>Consolidating the clauses onto the paper's value function\<close>

text \<open>Clause (0) for \<open>paper_v\<close>: the exit functional of Eq. (1.6) is capped
  at the horizon, so the value is bounded by it outright.  (The SHARP bound
  \<open>paper_v \<le> ball_v\<close>, which also gives clause (3), needs the class-level
  expected-exit-time estimate; \<open>sconstraint_trace_ge\<close> below is its first
  input.)\<close>

theorem paper_v_le_T:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T: "0 \<le> T"
  shows "paper_v k L T K x \<le> ennreal T"
  unfolding paper_v_def
proof (rule Sup_least)
  fix c :: ennreal
  assume "c \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      ` paper_pair_class k L T x"
  then obtain Q :: "('n pairpath) measure"
    where Q: "Q \<in> paper_pair_class k L T x"
      and c: "c = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
  show "c \<le> ennreal T"
    unfolding c
    by (rule ess_inf_time_le_const[OF paper_pair_class_prob[OF Q]])
      (simp add: pexit_def etime_le_T[OF T])
qed

text \<open>The trace lower bound carried by the constraint set: the identity is a
  rank-\<open>n\<close> projection, so \<open>Pi_proj a n \<le> trace a\<close>, and the constraint's
  own bound at \<open>m = n\<close> is \<open>n - k\<close>.  This is what makes \<open>|X|\<^sup>2\<close> a
  submartingale with rate at least \<open>n - k\<close>, hence the exit-time estimate
  of Lemma 2.1 at the CLASS level.\<close>

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

text \<open>Tracing the compensated clause turns it into the SUBMARTINGALE
  statement Lemma 2.1 runs on: \<open>|X|\<^sup>2 - trace Y\<close> is a martingale, and
  \<open>trace Y\<close> grows at rate at least \<open>n - k\<close>.  Together these give
  \<open>E[|X\<^sub>t|\<^sup>2] - |x|\<^sup>2 \<ge> (n-k)\<sqdot>t\<close>, which is what bounds the exit time.\<close>

lemma bounded_linear_trace:
  "bounded_linear (trace :: real^'n::finite^'n \<Rightarrow> real)"
  unfolding linear_conv_bounded_linear[symmetric]
  by (intro linearI) (simp_all add: trace_add trace_scaleR_matrix)

lemma trace_outerp:
  fixes v :: "real^'n::finite"
  shows "trace (outerp v) = v \<bullet> v"
  by (simp add: outerp_def trace_def inner_vec_def)

theorem paper_pair_class_trace_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) \<bullet> fst (\<omega> (min u T))
             - trace (snd (\<omega> (min u T))))"
proof -
  have "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. trace (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))))"
    by (rule martingale_bounded_linear_image[OF bounded_linear_trace
        paper_pair_class_compensated_martingale[OF Q]])
  then show ?thesis by (simp add: trace_diff_matrix trace_outerp)
qed

theorem paper_pair_class_trace_rate:
  fixes Q :: "('n::finite pairpath) measure"
  assumes k: "k < CARD('n)" and Q: "Q \<in> paper_pair_class k L T x"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      real (CARD('n) - k) * (t - s)
        \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
proof -
  have dq: "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using Q unfolding paper_pair_class_def by blast
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
        by (simp add: trace_scaleR_matrix trace_diff_matrix)
      finally show "real (CARD('n) - k) * (t - s)
          \<le> trace (snd (\<omega> t)) - trace (snd (\<omega> s))"
        using st by (simp add: pos_le_divide_eq)
    qed
  qed
qed

lemma paper_pair_class_norm_sq_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
proof -
  have "integrable Q (\<lambda>\<omega> :: 'n pairpath. \<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2)"
    by (intro Bochner_Integration.integrable_sum
        paper_pair_class_sq_integrable[OF T L Q t])
  then show ?thesis by (simp add: inner_vec_def power2_eq_square)
qed

text \<open>The class-level form of Lemma 2.1's estimate: the expected squared
  norm grows at rate at least \<open>n - k\<close>.  No stopping and no optional
  sampling --- the compensated clause is used at the FIXED time \<open>t\<close>.\<close>

theorem paper_pair_class_sq_norm_mean_ge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes k: "k < CARD('n)" and T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T x" and t: "t \<in> {0..T}"
  shows "x \<bullet> x + real (CARD('n) - k) * t
      \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by auto
  have ci: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule paper_pair_class_compensated_integrable[OF Q t])
  have ti: "integrable Q (\<lambda>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
    by (rule integrable_bounded_linear[OF bounded_linear_trace ci])
  have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule paper_pair_class_norm_sq_integrable[OF T L Q t])
  have mean: "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q) = x \<bullet> x"
  proof -
    have "(\<integral>\<omega>. trace (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
        = trace (\<integral>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t) \<partial>Q)"
      by (rule integral_of_bounded_linear[OF bounded_linear_trace ci])
    also have "\<dots> = trace (outerp x)"
      by (simp add: paper_pair_class_compensated_mean[OF Q t])
    finally show ?thesis by (simp add: trace_outerp)
  qed
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding paper_pair_class_def by blast
  have tr: "AE \<omega> in Q. \<forall>s t'. 0 \<le> s \<longrightarrow> s < t' \<longrightarrow> t' \<le> T \<longrightarrow>
      real (CARD('n) - k) * (t' - s)
        \<le> trace (snd (\<omega> t')) - trace (snd (\<omega> s))"
    by (rule paper_pair_class_trace_rate[OF k Q])
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

text \<open>Clause (3) for the paper's value function on the ball.  If a member
  kept \<open>|X| \<le> r\<close> up to a positive time from a boundary start, its expected
  squared norm at an interior time would be at most \<open>r\<^sup>2\<close> — but
  \<open>paper_pair_class_sq_norm_mean_ge\<close> says it is at least
  \<open>r\<^sup>2 + (n-k)t > r\<^sup>2\<close>.  So the essential infimum of the exit time is \<open>0\<close>
  for every member, hence so is the supremum.\<close>

theorem paper_v_boundary_zero:
  fixes r :: real and x :: "real^'n::finite"
  assumes k: "k < CARD('n)" and T: "0 < T" and L: "0 \<le> L"
    and x: "norm x = r"
  shows "paper_v k L T (cball 0 r) x = 0"
proof -
  have T0: "0 \<le> T" using T by simp
  have r0: "0 \<le> r" using x by (metis norm_ge_zero)
  have "paper_v k L T (cball 0 r) x \<le> 0"
    unfolding paper_v_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T (cball 0 r) (\<lambda>t. fst (\<omega> t))))
        ` paper_pair_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> paper_pair_class k L T x"
        and e: "e = ess_inf_time Q
            (\<lambda>\<omega>. pexit T (cball 0 r) (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
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
        by (rule paper_pair_class_norm_sq_integrable[OF T0 L Q tI])
      have lo: "x \<bullet> x + real (CARD('n) - k) * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule paper_pair_class_sq_norm_mean_ge[OF k T0 L Q tI])
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

text \<open>Example 3.1, inequality (3.10), for the paper's value function: if the
  target set fits inside a ball of radius \<open>r\<close>, then

    \<open>v(x) \<le> (r\<^sup>2 - |x|\<^sup>2) / (n - k)\<close>.

  The bound does NOT mention the horizon \<open>T\<close>, so it is the quantitative
  form of clause (0), and it is the reason the horizon cap of the capped
  path space is eventually invisible.  \<open>paper_v_boundary_zero\<close> is the case
  \<open>|x| = r\<close>.  The paper derives (3.10) from Ito's formula; here it comes
  from \<open>paper_pair_class_sq_norm_mean_ge\<close>, which is Lemma 2.1's estimate at
  a FIXED time and needs no stochastic calculus.\<close>

theorem paper_v_le_ball_bound:
  fixes r :: real and x :: "real^'n::finite" and K :: "(real^'n) set"
  assumes k: "k < CARD('n)" and T: "0 \<le> T" and L: "0 \<le> L"
    and KB: "K \<subseteq> cball 0 r"
  shows "paper_v k L T K x
      \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
proof -
  define B where "B = (r * r - x \<bullet> x) / real (CARD('n) - k)"
  have nk: "0 < real (CARD('n) - k)" using k by simp
  have main: "paper_v k L T K x \<le> ennreal B"
    unfolding paper_v_def
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` paper_pair_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> paper_pair_class k L T x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
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
        by (rule paper_pair_class_norm_sq_integrable[OF T L Q tI])
      have lo: "x \<bullet> x + real (CARD('n) - k) * t
          \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
        by (rule paper_pair_class_sq_norm_mean_ge[OF k T L Q tI])
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

section \<open>Towards the DPP: the class is closed under shortening the horizon\<close>

text \<open>The conditioning-free half of the closure the weak DPP needs.  A
  member on \<open>[0,T]\<close> restricted to \<open>[0,S]\<close> is a member on \<open>[0,S]\<close>.  Both
  martingale clauses come out of \<open>martingale_pair_law\<close> with the RESTRICTION
  as the path map: it is adapted for free, because \<open>pcut S \<omega> r = \<omega> r\<close> on
  \<open>{0..S}\<close>, and \<open>martingale_stopped_const\<close> turns the \<open>T\<close>-clause into the
  \<open>S\<close>-clause.\<close>

definition pcut :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "pcut S \<omega> = restrict \<omega> {0..S}"

lemma pcut_apply: "r \<in> {0..S} \<Longrightarrow> pcut S \<omega> r = \<omega> r"
  by (simp add: pcut_def)

lemma pcut_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pcut S \<in> Q \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric S :: ('n pairpath) metric))"
proof -
  have "(\<lambda>f :: 'n pairpath. restrict f {0..S})
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
    by (rule restrict_measurable_path_borel[OF S ST])
  then show ?thesis
    unfolding pcut_def using measurable_cong_sets[OF setsQ refl] by blast
qed

lemma pcut_adapted:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) \<in> borel_measurable
      (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<in> {0..S}")
  case True
  have "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M borel"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use r ru in auto)
  then show ?thesis using True by (simp add: pcut_apply)
next
  case False
  then have "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: pcut_def)
  then show ?thesis by simp
qed

text \<open>The rational reduction of the covariation clause, factored out: it is
  needed once per construction of a class member (the Brownian witness, the
  restricted law, and every later DPP construction), and the argument is
  always the same — countably many pairs by \<open>AE_ball_countable'\<close>, then
  \<open>diffquot_all_of_rational\<close> against path continuity.\<close>

lemma paper_pair_class_diffquot_of_pairs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and one: "\<And>p q :: real. p \<in> {0..T} \<Longrightarrow> q \<in> {0..T} \<Longrightarrow> p < q \<Longrightarrow>
      AE \<omega> in Q. (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have rat: "AE \<omega> in Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE \<omega> in Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE \<omega> in Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
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
      and W: "\<omega> \<in> space Q" by blast+
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

text \<open>Brick (a) of the DPP: a member of the class at horizon \<open>T\<close>, cut back
  to \<open>[0,S]\<close>, is a member of the class at horizon \<open>S\<close>.  All four clauses of
  (1.7) survive: the two \<open>AE\<close> clauses because \<open>pcut\<close> is the identity on
  \<open>[0,S]\<close>, and the two martingale clauses because stopping at \<open>S\<close> is
  harmless (\<open>martingale_stopped_const\<close>) and transports along \<open>pcut\<close>
  (\<open>martingale_pair_law\<close>).\<close>

theorem paper_pair_class_pcut:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and ST: "S \<le> T" and Q: "Q \<in> paper_pair_class k L T x"
  shows "pair_law_of S (pcut S) Q \<in> paper_pair_class k L S x"
proof -
  let ?Q = "pair_law_of S (pcut S) Q"
  let ?B = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have phim: "pcut S \<in> Q \<rightarrow>\<^sub>M ?B" by (rule pcut_measurable[OF S ST setsQ])
  have prob': "prob_space ?Q"
    unfolding pair_law_of_def by (rule P.prob_space_distr[OF phim])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pcut S \<omega> r) \<in> borel_measurable (?F u)"
    if "0 \<le> r" "r \<le> u" for r u
    by (rule pcut_adapted[OF S setsQ that])
  have mT: "min u S \<le> T" for u
    using min.cobounded2[of u S] ST by linarith

  \<comment> \<open>clause (i): the initial condition\<close>
  have start': "AE \<omega> in ?Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have mset: "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
          = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
        by (auto simp: prod_eq_iff)
      then show ?thesis using measurable_sets[OF ev] by simp
    qed
    have iff: "(AE \<omega> in ?Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0)
        = (AE \<omega> in Q. fst (pcut S \<omega> 0) = x \<and> snd (pcut S \<omega> 0) = 0)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
    have z: "(0::real) \<in> {0..S}" using S by simp
    have "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding paper_pair_class_def by blast
    then have "AE \<omega> in Q. fst (pcut S \<omega> 0) = x \<and> snd (pcut S \<omega> 0) = 0"
      by eventually_elim (simp add: pcut_apply[OF z])
    then show ?thesis unfolding iff .
  qed

  \<comment> \<open>clause (ii): the eigenvalue constraint on the covariation\<close>
  have cov': "AE \<omega> in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> S \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  proof (rule paper_pair_class_diffquot_of_pairs[OF sets_pair_law_of])
    fix p q :: real
    assume pq: "p \<in> {0..S}" "q \<in> {0..S}" "p < q"
    have mm: "{\<omega> \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
      using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
      by (simp add: space_borel_of)
    have iff: "(AE \<omega> in ?Q.
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L)
        = (AE \<omega> in Q. (1 / (q - p))
            *\<^sub>R (snd (pcut S \<omega> q) - snd (pcut S \<omega> p)) \<in> sconstraint k L)"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
    have "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding paper_pair_class_def by blast
    then have "AE \<omega> in Q. (1 / (q - p))
        *\<^sub>R (snd (pcut S \<omega> q) - snd (pcut S \<omega> p)) \<in> sconstraint k L"
    proof eventually_elim
      case (elim \<omega>)
      have "(1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
        using elim pq ST by auto
      then show ?case using pq by (simp add: pcut_apply)
    qed
    then show "AE \<omega> in ?Q.
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      unfolding iff .
  qed

  \<comment> \<open>clause (iii): \<open>X\<close> is a martingale\<close>
  have mgX': "martingale ?Q ?G 0 (\<lambda>u \<omega>. fst (\<omega> (min u S)) :: real^'n)"
  proof (rule martingale_pair_law[OF P.prob_space_axioms phim adap])
    fix u :: real assume u: "0 \<le> u"
    have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u S)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u S in auto)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u S))) \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF ev fstB])
  next
    show "martingale Q ?F 0 (\<lambda>u \<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)"
    proof (rule martingale_cong_ge
        [OF martingale_stopped_const[OF S paper_pair_class_X_martingale[OF Q]]])
      fix u :: real assume u: "0 \<le> u"
      have mI: "min u S \<in> {0..S}" using u S by simp
      have e1: "min (min u S) T = min u S" using mT by (rule min_absorb1)
      show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u S) T)))
          = (\<lambda>\<omega>. fst (pcut S \<omega> (min u S)) :: real^'n)"
        by (rule ext) (simp add: e1 pcut_apply[OF mI])
    qed
  qed

  \<comment> \<open>clause (iv): the compensated process is a martingale\<close>
  have mgC': "martingale ?Q ?G 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u S)) :: real^'n) - snd (\<omega> (min u S)))"
  proof (rule martingale_pair_law[OF P.prob_space_axioms phim adap])
    fix u :: real assume u: "0 \<le> u"
    have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        = (\<lambda>p. \<chi> i j. fst p $ i * fst p $ j - snd p $ i $ j)"
      by (rule ext) (simp add: outerp_def vec_eq_iff)
    have cB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        \<in> borel_measurable borel"
      unfolding e
      by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
          continuous_intros)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u S)) \<in> ?G u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u S in auto)
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u S))) - snd (\<omega> (min u S)))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF ev cB])
  next
    show "martingale Q ?F 0 (\<lambda>u \<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
        - snd (pcut S \<omega> (min u S)))"
    proof (rule martingale_cong_ge[OF martingale_stopped_const
          [OF S paper_pair_class_compensated_martingale[OF Q]]])
      fix u :: real assume u: "0 \<le> u"
      have mI: "min u S \<in> {0..S}" using u S by simp
      have e1: "min (min u S) T = min u S" using mT by (rule min_absorb1)
      show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min (min u S) T)))
            - snd (\<omega> (min (min u S) T)))
          = (\<lambda>\<omega>. outerp (fst (pcut S \<omega> (min u S)) :: real^'n)
              - snd (pcut S \<omega> (min u S)))"
        by (rule ext) (simp add: e1 pcut_apply[OF mI])
    qed
  qed

  show ?thesis
    unfolding paper_pair_class_def mem_Collect_eq
    using prob' sets_pair_law_of start' cov' mgX' mgC' by blast
qed

section \<open>Concatenation of pair paths\<close>

text \<open>The other half of the dynamic programming principle needs the class to
  be closed under PASTING: run \<open>\<omega>\<close> up to a time \<open>r\<close>, then continue with an
  independent path \<open>\<omega>'\<close> re-based at \<open>\<omega> r\<close>.  Both components of the pair
  concatenate additively --- for \<open>X\<close> because the increments do, for
  \<open>Y = \<langle>X\<rangle>\<close> because the covariation of a concatenation is the concatenation
  of the covariations.  We allow \<open>r\<close> to be an arbitrary real here; a
  stopping-time glue is obtained by instantiating \<open>r\<close> with \<open>\<theta> \<omega>\<close>.\<close>

definition pglue :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath
    \<Rightarrow> 'n pairpath"
  where "pglue r T \<omega> \<omega>' =
     restrict (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)) {0..T}"

lemma pglue_le: "t \<in> {0..T} \<Longrightarrow> t \<le> r \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> t"
  by (simp add: pglue_def)

lemma pglue_ge:
  "t \<in> {0..T} \<Longrightarrow> r \<le> t \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  by (cases "t = r") (auto simp: pglue_def)

lemma pglue_zero: "0 \<le> r \<Longrightarrow> 0 \<le> T \<Longrightarrow> pglue r T \<omega> \<omega>' 0 = \<omega> 0"
  by (rule pglue_le) auto

lemma continuous_on_pglue:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and c1: "continuous_on {0..r} \<omega>"
    and c2: "continuous_on {0..T - r} \<omega>'"
  shows "continuous_on {0..T}
      (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
proof -
  let ?f = "\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  have U: "{0..T} = {0..r} \<union> {r..T}" using r rT by auto
  have A: "continuous_on {0..r} ?f"
    by (rule continuous_on_eq[OF c1]) simp
  have B: "continuous_on {r..T} ?f"
  proof (rule continuous_on_eq)
    have "continuous_on {r..T} (\<lambda>t. \<omega>' (t - r))"
      by (rule continuous_on_compose2[OF c2 continuous_on_diff
            [OF continuous_on_id continuous_on_const]]) auto
    then show "continuous_on {r..T} (\<lambda>t. \<omega> r + (\<omega>' (t - r) - \<omega>' 0))"
      by (intro continuous_intros)
  next
    fix t :: real assume "t \<in> {r..T}"
    then show "\<omega> r + (\<omega>' (t - r) - \<omega>' 0) = ?f t" by (cases "t = r") auto
  qed
  show ?thesis unfolding U by (rule continuous_on_closed_Un[OF _ _ A B]) auto
qed

lemma pglue_in_mspace:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
    and w': "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
  shows "pglue r T \<omega> \<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)"
  unfolding pglue_def
  by (rule mspace_path_metricI[OF continuous_on_pglue[OF r rT
        mspace_path_metricD[OF w] mspace_path_metricD[OF w']]])

lemma pglue_measurable:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "sets R = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
  shows "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_snd
          pair_law_eval_measurable[OF setsR]])
  have Xm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" for t
    using eQ eR by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "'n pairpath \<times> 'n pairpath"
  proof (rule continuous_on_pglue[OF r rT])
    have "fst p \<in> space Q" "snd p \<in> space R"
      using p by (auto simp: space_pair_measure)
    then show "continuous_on {0..r} (fst p)" "continuous_on {0..T - r} (snd p)"
      using space_of_path_sets[OF setsQ] space_of_path_sets[OF setsR]
      by (auto intro: mspace_path_metricD)
  qed
  show ?thesis
    using pathify_measurable[OF T0 Xm cont] unfolding pglue_def by simp
qed

text \<open>The eigenvalue constraint (1.7) survives concatenation.  Across the
  glue point the difference quotient is a CONVEX COMBINATION of one quotient
  from each piece, which is why the constraint set had to be convexified
  (Lemma 2.1, \<open>sconstraint_convex\<close>) --- the unconvexified set of (1.4) would
  not do.\<close>

lemma pglue_diffquot:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and A: "\<And>p q :: real. 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> r \<Longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    and B: "\<And>p q :: real. 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T - r \<Longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega>' q) - snd (\<omega>' p)) \<in> sconstraint k L"
    and s: "0 \<le> s" and st: "s < t" and tT: "t \<le> T"
  shows "(1 / (t - s)) *\<^sub>R
      (snd (pglue r T \<omega> \<omega>' t) - snd (pglue r T \<omega> \<omega>' s)) \<in> sconstraint k L"
proof -
  have sT: "s \<in> {0..T}" and tI: "t \<in> {0..T}" using s st tT by auto
  consider (early) "t \<le> r" | (late) "r \<le> s" | (mid) "s < r" "r < t" by fastforce
  then show ?thesis
  proof cases
    case early
    then have "s \<le> r" using st by simp
    then show ?thesis
      using A[OF s st early] by (simp add: pglue_le[OF sT] pglue_le[OF tI early])
  next
    case late
    then have rt: "r \<le> t" using st by simp
    have "(1 / ((t - r) - (s - r))) *\<^sub>R (snd (\<omega>' (t - r)) - snd (\<omega>' (s - r)))
        \<in> sconstraint k L"
      using B[of "s - r" "t - r"] late st tT by simp
    then show ?thesis
      by (simp add: pglue_ge[OF sT late] pglue_ge[OF tI rt])
  next
    case mid
    let ?a = "(1 / (r - s)) *\<^sub>R (snd (\<omega> r) - snd (\<omega> s))"
    let ?b = "(1 / (t - r)) *\<^sub>R (snd (\<omega>' (t - r)) - snd (\<omega>' 0))"
    have aA: "?a \<in> sconstraint k L" by (rule A[OF s mid(1) order_refl])
    have bB: "?b \<in> sconstraint k L"
      using B[of 0 "t - r"] mid(2) tT by simp
    have pos: "0 < r - s" "0 < t - r" "0 < t - s" using mid st by auto
    have sum1: "(r - s) / (t - s) + (t - r) / (t - s) = 1"
      by (subst add_divide_distrib[symmetric]) (use pos(3) in simp)
    have cc: "((r - s) / (t - s)) *\<^sub>R ?a + ((t - r) / (t - s)) *\<^sub>R ?b
        \<in> sconstraint k L"
      using pos by (intro convexD[OF sconstraint_convex aA bB] sum1) auto
    have e1: "((r - s) / (t - s)) *\<^sub>R ?a
        = (1 / (t - s)) *\<^sub>R (snd (\<omega> r) - snd (\<omega> s))"
      using pos by simp
    have e2: "((t - r) / (t - s)) *\<^sub>R ?b
        = (1 / (t - s)) *\<^sub>R (snd (\<omega>' (t - r)) - snd (\<omega>' 0))"
      using pos by simp
    have "snd (pglue r T \<omega> \<omega>' t) - snd (pglue r T \<omega> \<omega>' s)
        = (snd (\<omega> r) - snd (\<omega> s)) + (snd (\<omega>' (t - r)) - snd (\<omega>' 0))"
      using mid(1) less_imp_le[OF mid(2)]
      by (simp add: pglue_le[OF sT] pglue_ge[OF tI])
    then show ?thesis
      using cc unfolding e1 e2 by (simp add: scaleR_right_distrib)
  qed
qed

subsection \<open>The pasted law\<close>

definition pglue_law :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath) measure
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "pglue_law r T Q R
     = pair_law_of T (\<lambda>p. pglue r T (fst p) (snd p)) (Q \<Otimes>\<^sub>M R)"

lemma sets_pglue_law[simp]:
  "sets (pglue_law r T Q R)
     = sets (borel_of (mtopology_of (path_metric T
         :: ('n::finite pairpath) metric)))"
  unfolding pglue_law_def by (rule sets_pair_law_of)

lemma space_pglue_law:
  "space (pglue_law r T Q R)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding pglue_law_def by (rule space_pair_law_of)

lemma prob_space_pair_measure:
  assumes M: "prob_space M" and N: "prob_space N"
  shows "prob_space (M \<Otimes>\<^sub>M N)"
proof -
  interpret M: prob_space M by (rule M)
  interpret N: prob_space N by (rule N)
  interpret PP: pair_prob_space M N by unfold_locales
  show ?thesis by (rule PP.P.prob_space_axioms)
qed

lemma prob_space_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "prob_space R"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "sets R = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
  shows "prob_space (pglue_law r T Q R)"
proof -
  interpret PP: prob_space "Q \<Otimes>\<^sub>M R"
    by (rule prob_space_pair_measure[OF PQ PR])
  show ?thesis
    unfolding pglue_law_def pair_law_of_def
    by (rule PP.prob_space_distr[OF pglue_measurable[OF r rT setsQ setsR]])
qed

text \<open>The transfer principle for almost-sure statements: a property of the
  glued path holds \<open>pglue_law\<close>-a.s. as soon as it follows from one
  \<open>Q\<close>-a.s. property of the first piece and one \<open>R\<close>-a.s. property of the
  second.  Both \<open>AE\<close> clauses of (1.7) are of this shape.\<close>

lemma AE_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "prob_space R"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "sets R = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and A: "AE \<omega> in Q. A \<omega>" and B: "AE \<omega>' in R. B \<omega>'"
    and imp: "\<And>\<omega> \<omega>' :: 'n pairpath.
        \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric) \<Longrightarrow>
        A \<omega> \<Longrightarrow> B \<omega>' \<Longrightarrow> P (pglue r T \<omega> \<omega>')"
  shows "AE \<omega> in pglue_law r T Q R. P \<omega>"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PR: prob_space R by (rule PR)
  interpret PP: pair_prob_space Q R by unfold_locales
  have phim: "?g \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pglue_measurable[OF r rT setsQ setsR])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in pglue_law r T Q R. P \<omega>) = (AE p in ?M. P (?g p))"
    unfolding pglue_law_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?M. P (?g p)} \<in> sets ?M"
  proof -
    have "{p \<in> space ?M. P (?g p)} = ?g -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?M"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have inner: "AE \<omega> in Q. AE \<omega>' in R. P (?g (\<omega>, \<omega>'))"
  proof -
    have RB: "AE \<omega>' in R. B \<omega>'
        \<and> \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      using B AE_space[of R] space_of_path_sets[OF setsR]
      by (auto intro: eventually_conj)
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      show "AE \<omega>' in R. P (?g (\<omega>, \<omega>'))"
      proof (rule eventually_mono[OF RB])
        fix \<omega>' :: "'n pairpath"
        assume "B \<omega>'
            \<and> \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
        with w show "P (?g (\<omega>, \<omega>'))" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?M. P (?g p)"
    using PP.AE_pair_measure[OF evm] inner by simp
  then show ?thesis unfolding iff .
qed

lemma pglue_law_start:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
  shows "AE \<omega> in pglue_law r T Q R. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff space_borel_of)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  show ?thesis
  proof (rule AE_pglue_law[OF r rT paper_pair_class_prob[OF Q]
        paper_pair_class_prob[OF R] paper_pair_class_sets[OF Q]
        paper_pair_class_sets[OF R] mset])
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding paper_pair_class_def by blast
    show "AE \<omega>' in R. True" by simp
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      and st: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0" and "True"
    from st show "fst (pglue r T \<omega> \<omega>' 0) = x \<and> snd (pglue r T \<omega> \<omega>' 0) = 0"
      using r rT by (simp add: pglue_zero)
  qed
qed

lemma pglue_law_diffquot:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
  shows "AE \<omega> in pglue_law r T Q R. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof (rule paper_pair_class_diffquot_of_pairs[OF sets_pglue_law])
  fix p q :: real
  assume pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
  show "AE \<omega> in pglue_law r T Q R.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_pglue_law[OF r rT paper_pair_class_prob[OF Q]
        paper_pair_class_prob[OF R] paper_pair_class_sets[OF Q]
        paper_pair_class_sets[OF R] mset])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding paper_pair_class_def by blast
    show "AE \<omega>' in R. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
      using R unfolding paper_pair_class_def by blast
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      and A: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      and B: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
    show "(1 / (q - p)) *\<^sub>R
        (snd (pglue r T \<omega> \<omega>' q) - snd (pglue r T \<omega> \<omega>' p)) \<in> sconstraint k L"
      using pq A B by (intro pglue_diffquot[OF r rT]) auto
  qed
qed

section \<open>The horizon cap does not bind\<close>

text \<open>\<open>paper_v\<close> caps the exit time at \<open>T\<close>, the paper's \<open>v\<close> does not.  Cutting
  a member back to \<open>[0,S]\<close> (\<open>paper_pair_class_pcut\<close>) can only shorten its exit
  time to \<open>min \<tau> S\<close>, so the value at horizon \<open>T\<close> is already visible at the
  shorter horizon \<open>S\<close> --- PROVIDED \<open>S\<close> is beyond the scale
  \<open>(r\<^sup>2 - |x|\<^sup>2)/(n-k)\<close> of \<open>paper_v_le_ball_bound\<close>, so that the cut does not
  truncate anything.  No pasting is needed for this direction.\<close>

definition pfst :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> (real \<Rightarrow> real^'n)"
  where "pfst S \<omega> = restrict (\<lambda>t. fst (\<omega> t)) {0..S}"

lemma pexit_pfst: "pexit S K (pfst S \<omega>) = pexit S K (\<lambda>t. fst (\<omega> t))"
proof -
  have "{r. 0 \<le> r \<and> r \<le> S \<and> pfst S \<omega> r \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> S \<and> fst (\<omega> r) \<in> - K}"
    by (auto simp: pfst_def)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma pfst_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
  shows "pfst S \<in> N \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric S :: ((real \<Rightarrow> real^'n)) metric))"
  unfolding pfst_def
proof (rule pathify_measurable[OF S])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  fix t :: real assume "t \<in> {0..S}"
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsN] fstB])
next
  fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space N"
  then have "\<omega> \<in> mspace (path_metric S :: ('n pairpath) metric)"
    using space_of_path_sets[OF setsN] by simp
  then have "continuous_on {0..S} \<omega>" by (rule mspace_path_metricD)
  then show "continuous_on {0..S} (\<lambda>t. fst (\<omega> t))"
    by (intro continuous_intros)
qed

lemma ennreal_min_eq: "ennreal (min a b) = min (ennreal a) (ennreal b)"
proof (cases "a \<le> b")
  case True
  then have "ennreal a \<le> ennreal b" by (rule ennreal_leI)
  with True show ?thesis by (simp add: min_def)
next
  case False
  then have "ennreal b \<le> ennreal a" by (simp add: ennreal_leI)
  with False show ?thesis by (simp add: min_def)
qed

lemma pexit_pcut_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> :: "'n pairpath"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "min (pexit T K (\<lambda>t. fst (\<omega> t))) S
      \<le> pexit S K (\<lambda>t. fst (pcut S \<omega> t))"
proof -
  have T0: "0 \<le> T" using S ST by simp
  have lb: "min (pexit T K (\<lambda>t. fst (\<omega> t))) S \<le> z"
    if z: "z \<in> {r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S}"
    for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> S" "fst (pcut S \<omega> z) \<in> - K" | (cap) "z = S"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zT: "z \<le> T" using ST by simp
      have notin: "fst (\<omega> z) \<in> - K"
        using hit by (simp add: pcut_apply)
      have "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> z"
        unfolding pexit_def
        by (rule etime_le_of_mem[OF T0 hit(1) zT]) (use notin in simp)
      then show ?thesis using hit(2) by simp
    next
      case cap
      then show ?thesis by simp
    qed
  qed
  have "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
      = Inf ({r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S})"
    unfolding pexit_def etime_def ..
  moreover have "min (pexit T K (\<lambda>t. fst (\<omega> t)))  S
      \<le> Inf ({r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

theorem paper_v_horizon_stable:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and r :: real
  assumes k: "k < CARD('n)" and L: "0 \<le> L" and S: "0 \<le> S" and ST: "S \<le> T"
    and K: "closed K" and KB: "K \<subseteq> cball 0 r"
    and big: "(r * r - x \<bullet> x) / real (CARD('n) - k) \<le> S"
  shows "paper_v k L T K x \<le> paper_v k L S K x"
proof -
  have T0: "0 \<le> T" using S ST by simp
  let ?B = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  let ?tau = "\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t))"
  have taum: "?tau \<in> borel_measurable ?B"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable ?B"
      by (rule measurable_compose[OF pfst_measurable[OF S refl]
            pexit_measurable[OF S K]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  have "paper_v k L T K x
      = Sup ((\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
          ` paper_pair_class k L T x)"
    unfolding paper_v_def ..
  also have "\<dots> \<le> paper_v k L S K x"
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        ` paper_pair_class k L T x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> paper_pair_class k L T x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))" by blast
    have eS: "e \<le> ennreal S"
    proof -
      have "e \<le> paper_v k L T K x"
        unfolding paper_v_def e using Q by (intro Sup_upper imageI)
      also have "\<dots> \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
        by (rule paper_v_le_ball_bound[OF k T0 L KB])
      also have "\<dots> \<le> ennreal S" using big by (rule ennreal_leI)
      finally show ?thesis .
    qed
    have Q': "pair_law_of S (pcut S) Q \<in> paper_pair_class k L S x"
      by (rule paper_pair_class_pcut[OF S ST Q])
    have m1: "pcut S \<in> Q \<rightarrow>\<^sub>M ?B"
      by (rule pcut_measurable[OF S ST paper_pair_class_sets[OF Q]])
    have mset: "{\<omega> \<in> space ?B. e \<le> ennreal (?tau \<omega>)} \<in> sets ?B"
      using taum by measurable
    have iff: "(AE \<omega> in pair_law_of S (pcut S) Q. e \<le> ennreal (?tau \<omega>))
        = (AE \<omega> in Q. e \<le> ennreal (?tau (pcut S \<omega>)))"
      unfolding pair_law_of_def by (rule AE_distr_iff[OF m1 mset])
    have ae1: "AE \<omega> in Q. e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      unfolding e by (rule ess_inf_time_AE)
    have "AE \<omega> in Q. e \<le> ennreal (?tau (pcut S \<omega>))"
    proof (rule eventually_mono[OF ae1])
      fix \<omega> :: "'n pairpath"
      assume "e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      with eS have "e \<le> ennreal (min (pexit T K (\<lambda>t. fst (\<omega> t))) S)"
        unfolding ennreal_min_eq by simp
      also have "\<dots> \<le> ennreal (pexit S K (\<lambda>t. fst (pcut S \<omega> t)))"
        by (intro ennreal_leI pexit_pcut_ge[OF S ST])
      finally show "e \<le> ennreal (?tau (pcut S \<omega>))" by simp
    qed
    then have ae: "AE \<omega> in pair_law_of S (pcut S) Q. e \<le> ennreal (?tau \<omega>)"
      unfolding iff .
    have "e \<le> ess_inf_time (pair_law_of S (pcut S) Q) ?tau"
      unfolding ess_inf_time_def using ae by (intro Sup_upper) simp
    also have "\<dots> \<le> paper_v k L S K x"
      unfolding paper_v_def using Q' by (intro Sup_upper imageI)
    finally show "e \<le> paper_v k L S K x" .
  qed
  finally show ?thesis .
qed

section \<open>Martingales on a product of two filtered measures\<close>

text \<open>The pasting theorem needs three transfer results: a martingale of the
  FIRST factor, read as a process on the product, is a martingale for the
  PRODUCT filtration; likewise for the second factor; and so is the product
  of a first-factor variable with a second-factor martingale.  All three come
  out of Fubini plus a SECTIONWISE use of the factor's set-integral identity:
  a section of a set of \<open>F u \<Otimes>\<^sub>M G u\<close> is a set of \<open>F u\<close> (resp. \<open>G u\<close>), so
  the factor's martingale property applies to it directly.  No conditional
  expectation on the product, and no \<open>\<pi>\<close>-\<open>\<lambda>\<close> argument, is needed.\<close>

lemma sets_pair_measure_mono:
  assumes A: "sets A \<subseteq> sets M" "space A = space M"
    and B: "sets B \<subseteq> sets N" "space B = space N"
  shows "sets (A \<Otimes>\<^sub>M B) \<subseteq> sets (M \<Otimes>\<^sub>M N)"
proof -
  have "{a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B} \<subseteq> sets (M \<Otimes>\<^sub>M N)"
    using A(1) B(1) by auto
  then have "sigma_sets (space (M \<Otimes>\<^sub>M N))
      {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B} \<subseteq> sets (M \<Otimes>\<^sub>M N)"
    by (rule sets.sigma_sets_subset)
  then show ?thesis
    using A(2) B(2) by (simp add: sets_pair_measure space_pair_measure)
qed

lemma filtered_measure_pair:
  fixes F :: "real \<Rightarrow> 'a measure" and G :: "real \<Rightarrow> 'b measure"
  assumes MF: "filtered_measure M F (0::real)"
    and NG: "filtered_measure N G (0::real)"
  shows "filtered_measure (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) (0::real)"
proof -
  interpret MF: filtered_measure M F "0::real" by (rule MF)
  interpret NG: filtered_measure N G "0::real" by (rule NG)
  show ?thesis
  proof (unfold_locales)
    fix i :: real assume i: "0 \<le> i"
    have "sets (F i \<Otimes>\<^sub>M G i) \<subseteq> sets (M \<Otimes>\<^sub>M N)"
      using MF.sets_F_subset[OF i] NG.sets_F_subset[OF i]
        MF.space_F[OF i] NG.space_F[OF i]
      by (intro sets_pair_measure_mono)
    moreover have "space (F i \<Otimes>\<^sub>M G i) = space (M \<Otimes>\<^sub>M N)"
      using MF.space_F[OF i] NG.space_F[OF i] by (simp add: space_pair_measure)
    ultimately show "subalgebra (M \<Otimes>\<^sub>M N) (F i \<Otimes>\<^sub>M G i)"
      by (simp add: subalgebra_def)
  next
    fix i j :: real assume ij: "0 \<le> i" "i \<le> j"
    then have j: "0 \<le> j" by simp
    show "sets (F i \<Otimes>\<^sub>M G i) \<le> sets (F j \<Otimes>\<^sub>M G j)"
      using MF.sets_F_mono[OF ij] NG.sets_F_mono[OF ij]
        MF.space_F[OF ij(1)] MF.space_F[OF j]
        NG.space_F[OF ij(1)] NG.space_F[OF j]
      by (intro sets_pair_measure_mono) simp_all
  qed
qed

theorem martingale_pair_fst:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes M: "prob_space M" and N: "prob_space N"
    and mg: "martingale M F (0::real) X"
    and NG: "filtered_measure N G (0::real)"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 (\<lambda>u p. X u (fst p))"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret MG: martingale M F "0::real" X by (rule mg)
  interpret PP: prob_space "M \<Otimes>\<^sub>M N" by (rule prob_space_pair_measure[OF M N])
  interpret PS: pair_sigma_finite M N by unfold_locales
  have FMF: "filtered_measure M F (0::real)" by unfold_locales
  interpret FP: finite_filtered_measure "M \<Otimes>\<^sub>M N" "\<lambda>u. F u \<Otimes>\<^sub>M G u" "0::real"
    unfolding finite_filtered_measure_def
    using filtered_measure_pair[OF FMF NG] PP.finite_measure_axioms by blast
  have Xm: "X u \<in> borel_measurable M" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MG.subalgebras[OF u] MG.adapted[OF u]])
  have int: "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X u (fst p))" if u: "0 \<le> u" for u
  proof -
    have e: "integrable (distr (M \<Otimes>\<^sub>M N) M fst) (X u)
        = integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X u (fst p))"
      by (rule integrable_distr_eq[OF measurable_fst Xm[OF u]])
    have "integrable (distr (M \<Otimes>\<^sub>M N) M fst) (X u)"
      using MG.integrable[OF u] by (simp add: PN.distr_pair_fst)
    then show ?thesis unfolding e .
  qed
  have si: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p))
      = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X v (fst p))"
    if u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u \<Otimes>\<^sub>M G u)" for A u v
  proof -
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets (M \<Otimes>\<^sub>M N)" using A FP.sets_F_subset[OF u] by auto
    have key: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X w (fst p))
        = (\<integral>\<omega>'. set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X w) \<partial>N)"
      if w: "0 \<le> w" for w
    proof -
      have ii: "integrable (M \<Otimes>\<^sub>M N)
          (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R X w \<omega>))"
        using integrable_mult_indicator[OF AM int[OF w]]
        by (simp add: case_prod_unfold)
      have "(\<integral>\<omega>'. (\<integral>\<omega>. indicator A (\<omega>, \<omega>') *\<^sub>R X w \<omega> \<partial>M) \<partial>N)
          = (\<integral>p. indicator A p *\<^sub>R X w (fst p) \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_snd[OF ii] by (simp add: case_prod_unfold)
      then show ?thesis
        by (simp add: set_lebesgue_integral_def indicator_def)
    qed
    have sec: "(\<lambda>\<omega>. (\<omega>, \<omega>')) -` A \<in> sets (F u)" for \<omega>'
      by (rule sets_Pair2[OF A])
    have "(\<integral>\<omega>'. set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X u) \<partial>N)
        = (\<integral>\<omega>'. set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X v) \<partial>N)"
      using MG.set_integral_eq[OF sec u uv] by simp
    then show ?thesis unfolding key[OF u] key[OF v] .
  qed
  show ?thesis
  proof (rule FP.martingale_of_set_integral_eq)
    show "adapted_process (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 (\<lambda>u p. X u (fst p))"
    proof (unfold_locales)
      fix i :: real assume i: "0 \<le> i"
      show "(\<lambda>p. X i (fst p)) \<in> borel_measurable (F i \<Otimes>\<^sub>M G i)"
        by (rule measurable_compose[OF measurable_fst MG.adapted[OF i]])
    qed
    show "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X i (fst p))" if "0 \<le> i" for i
      by (rule int[OF that])
    show "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X i (fst p))
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X j (fst p))"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F i \<Otimes>\<^sub>M G i)" for A i j
      by (rule si[OF that])
  qed
qed

lemma distr_pair_snd:
  assumes M: "prob_space M" and N: "sigma_finite_measure N"
  shows "distr (M \<Otimes>\<^sub>M N) N snd = N"
proof (intro measure_eqI)
  interpret PM: prob_space M by (rule M)
  interpret SN: sigma_finite_measure N by (rule N)
  fix A assume "A \<in> sets (distr (M \<Otimes>\<^sub>M N) N snd)"
  then have A: "A \<in> sets N" by simp
  have "emeasure (distr (M \<Otimes>\<^sub>M N) N snd) A = emeasure (M \<Otimes>\<^sub>M N) (space M \<times> A)"
    using A by (auto simp add: emeasure_distr space_pair_measure
        dest: sets.sets_into_space intro!: arg_cong2[where f = emeasure])
  also have "\<dots> = emeasure N A"
    using A by (simp add: SN.emeasure_pair_measure_Times PM.emeasure_space_1)
  finally show "emeasure (distr (M \<Otimes>\<^sub>M N) N snd) A = emeasure N A" .
qed simp

text \<open>The second-factor lift in the form the DPP will need: the process may
  depend on the FIRST coordinate too, as long as it is a second-factor
  martingale for each frozen value of it.  That is exactly what an
  endpoint-dependent continuation looks like once the endpoint is frozen.
  The section argument is unchanged --- for fixed \<open>\<omega>\<close> the section of \<open>A\<close> is a
  set of \<open>G u\<close> and the frozen process is a martingale on it.\<close>

theorem martingale_pair_snd_param:
  fixes Z :: "real \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes M: "prob_space M" and N: "prob_space N"
    and MF: "filtered_measure M F (0::real)"
    and NG: "filtered_measure N G (0::real)"
    and adap: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable (F u \<Otimes>\<^sub>M G u)"
    and int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable (M \<Otimes>\<^sub>M N) (Z u)"
    and sec: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> martingale N G 0 (\<lambda>u \<omega>'. Z u (\<omega>, \<omega>'))"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 Z"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret PP: prob_space "M \<Otimes>\<^sub>M N" by (rule prob_space_pair_measure[OF M N])
  interpret PS: pair_sigma_finite M N by unfold_locales
  interpret FP: finite_filtered_measure "M \<Otimes>\<^sub>M N" "\<lambda>u. F u \<Otimes>\<^sub>M G u" "0::real"
    unfolding finite_filtered_measure_def
    using filtered_measure_pair[OF MF NG] PP.finite_measure_axioms by blast
  have si: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z u)
      = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z v)"
    if u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u \<Otimes>\<^sub>M G u)" for A u v
  proof -
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets (M \<Otimes>\<^sub>M N)" using A FP.sets_F_subset[OF u] by auto
    have ii: "integrable (M \<Otimes>\<^sub>M N)
        (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z w (\<omega>, \<omega>')))"
      if w: "0 \<le> w" for w
      using integrable_mult_indicator[OF AM int[OF w]]
      by (simp add: case_prod_unfold)
    have key: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z w)
        = (\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z w (\<omega>, \<omega>') \<partial>N) \<partial>M)"
      if w: "0 \<le> w" for w
    proof -
      have "(\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z w (\<omega>, \<omega>') \<partial>N) \<partial>M)
          = (\<integral>p. indicator A p *\<^sub>R Z w p \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_fst[OF ii[OF w]] by (simp add: case_prod_unfold)
      then show ?thesis by (simp add: set_lebesgue_integral_def)
    qed
    have inner_eq: "(\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z u (\<omega>, \<omega>') \<partial>N)
        = (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z v (\<omega>, \<omega>') \<partial>N)"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      interpret MW: martingale N G "0::real" "\<lambda>u \<omega>'. Z u (\<omega>, \<omega>')"
        by (rule sec[OF w])
      have "set_lebesgue_integral N (Pair \<omega> -` A) (\<lambda>\<omega>'. Z u (\<omega>, \<omega>'))
          = set_lebesgue_integral N (Pair \<omega> -` A) (\<lambda>\<omega>'. Z v (\<omega>, \<omega>'))"
        by (rule MW.set_integral_eq[OF sets_Pair1[OF A] u uv])
      then show ?thesis
        by (simp add: set_lebesgue_integral_def indicator_def)
    qed
    have "(\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z u (\<omega>, \<omega>') \<partial>N) \<partial>M)
        = (\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') *\<^sub>R Z v (\<omega>, \<omega>') \<partial>N) \<partial>M)"
      using AE_space inner_eq
      by (intro Bochner_Integration.integral_cong_AE
          borel_measurable_integrable PS.integrable_fst[OF ii[OF u]]
          PS.integrable_fst[OF ii[OF v]]) auto
    then show ?thesis unfolding key[OF u] key[OF v] .
  qed
  show ?thesis
  proof (rule FP.martingale_of_set_integral_eq)
    show "adapted_process (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 Z"
      unfolding adapted_process_def adapted_process_axioms_def
      using filtered_measure_pair[OF MF NG] adap by blast
    show "integrable (M \<Otimes>\<^sub>M N) (Z i)" if "0 \<le> i" for i by (rule int[OF that])
    show "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z i)
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (Z j)"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F i \<Otimes>\<^sub>M G i)" for A i j
      by (rule si[OF that])
  qed
qed

theorem martingale_pair_snd:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes M: "prob_space M" and N: "prob_space N"
    and MF: "filtered_measure M F (0::real)"
    and mg: "martingale N G (0::real) Y"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0 (\<lambda>u p. Y u (snd p))"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret MG: martingale N G "0::real" Y by (rule mg)
  have FMG: "filtered_measure N G (0::real)" by unfold_locales
  have Ym: "Y u \<in> borel_measurable N" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MG.subalgebras[OF u] MG.adapted[OF u]])
  show ?thesis
  proof (rule martingale_pair_snd_param[OF M N MF FMG])
    show "(\<lambda>p. Y u (snd p)) \<in> borel_measurable (F u \<Otimes>\<^sub>M G u)" if "0 \<le> u" for u
      by (rule measurable_compose[OF measurable_snd MG.adapted[OF that]])
    show "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. Y u (snd p))" if u: "0 \<le> u" for u
    proof -
      have e: "integrable (distr (M \<Otimes>\<^sub>M N) N snd) (Y u)
          = integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. Y u (snd p))"
        by (rule integrable_distr_eq[OF measurable_snd Ym[OF u]])
      have "integrable (distr (M \<Otimes>\<^sub>M N) N snd) (Y u)"
        using MG.integrable[OF u]
        by (simp add: distr_pair_snd[OF M PN.sigma_finite_measure_axioms])
      then show ?thesis unfolding e .
    qed
    show "martingale N G 0 (\<lambda>u \<omega>'. Y u (snd (\<omega>, \<omega>')))"
      if "\<omega> \<in> space M" for \<omega> by (simp add: mg)
  qed
qed

text \<open>Two more pieces of martingale algebra the assembly needs: passing to an
  almost-everywhere equal (still adapted) process --- which is how the
  \<open>\<omega>' 0 = 0\<close> clause of the second factor gets used --- and reparametrising
  time by a nondecreasing map, which is how the second factor's clock
  \<open>u \<mapsto> (u - r)\<^sup>+\<close> is installed.\<close>

lemma martingale_cong_AE:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
    and adap: "adapted_process M F (0::real) Y"
    and eq: "\<And>i. 0 \<le> i \<Longrightarrow> AE \<omega> in M. X i \<omega> = Y i \<omega>"
  shows "martingale M F 0 Y"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  interpret AY: adapted_process M F "0::real" Y by (rule adap)
  have Xm: "X i \<in> borel_measurable M" if i: "0 \<le> i" for i
    by (rule measurable_from_subalg[OF MG.subalgebras[OF i] MG.adapted[OF i]])
  have Ym: "Y i \<in> borel_measurable M" if i: "0 \<le> i" for i
    by (rule measurable_from_subalg[OF MG.subalgebras[OF i] AY.adapted[OF i]])
  have iY: "integrable M (Y i)" if i: "0 \<le> i" for i
    using MG.integrable[OF i] integrable_cong_AE[OF Xm[OF i] Ym[OF i] eq[OF i]]
    by simp
  show ?thesis
  proof (rule MG.martingale_of_set_integral_eq[OF adap iY])
    fix A and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and A: "A \<in> sets (F i)"
    then have j: "0 \<le> j" by simp
    have AM: "A \<in> sets M" using A MG.sets_F_subset[OF ij(1)] by auto
    have "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (X i)"
      using eq[OF ij(1)]
      by (intro set_lebesgue_integral_cong_AE[OF AM Ym[OF ij(1)] Xm[OF ij(1)]])
        auto
    also have "\<dots> = set_lebesgue_integral M A (X j)"
      by (rule MG.set_integral_eq[OF A ij])
    also have "\<dots> = set_lebesgue_integral M A (Y j)"
      using eq[OF j]
      by (intro set_lebesgue_integral_cong_AE[OF AM Xm[OF j] Ym[OF j]]) auto
    finally show "set_lebesgue_integral M A (Y i) = set_lebesgue_integral M A (Y j)" .
  qed
qed

lemma martingale_time_change:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
    and s0: "\<And>u :: real. 0 \<le> u \<Longrightarrow> 0 \<le> s u"
    and smono: "\<And>u v :: real. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> s u \<le> s v"
  shows "martingale M (\<lambda>u. F (s u)) 0 (\<lambda>u. X (s u))"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have FMs: "filtered_measure M (\<lambda>u. F (s u)) (0::real)"
  proof (unfold_locales)
    show "subalgebra M (F (s i))" if "0 \<le> i" for i :: real
      by (rule MG.subalgebras[OF s0[OF that]])
    show "sets (F (s i)) \<le> sets (F (s j))" if "0 \<le> i" "i \<le> j" for i j :: real
      by (rule MG.sets_F_mono[OF s0[OF that(1)] smono[OF that]])
  qed
  interpret SF: sigma_finite_filtered_measure M "\<lambda>u. F (s u)" "0::real"
    unfolding sigma_finite_filtered_measure_def
      sigma_finite_filtered_measure_axioms_def
    using FMs MG.sigma_finite_subalgebra_F[OF s0[OF order_refl]] by blast
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process M (\<lambda>u. F (s u)) 0 (\<lambda>u. X (s u))"
      unfolding adapted_process_def adapted_process_axioms_def
      using FMs MG.adapted[OF s0] by blast
    show "integrable M (X (s i))" if "0 \<le> i" for i :: real
      by (rule MG.integrable[OF s0[OF that]])
    show "set_lebesgue_integral M A (X (s i))
        = set_lebesgue_integral M A (X (s j))"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F (s i))" for A and i j :: real
      by (rule MG.set_integral_eq[OF that(3) s0[OF that(1)] smono[OF that(1,2)]])
  qed
qed

text \<open>The third transfer result, and the one the COMPENSATED clause needs: the
  product of a first-factor martingale with a second-factor martingale is a
  martingale for the product filtration.  This is where independence of the
  two pieces is genuinely used --- it is what makes the cross term
  \<open>X\<^sub>r \<otimes> W + W \<otimes> X\<^sub>r\<close> of \<open>outerp (X\<^sub>r + W)\<close> a martingale.  Again the proof is
  Fubini twice: once in each variable, moving one factor's time index at a
  time, using the OTHER factor's set-integral identity on the section.\<close>

theorem martingale_pair_mult:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and Y :: "real \<Rightarrow> 'b \<Rightarrow> real"
  assumes M: "prob_space M" and N: "prob_space N"
    and mgX: "martingale M F (0::real) X"
    and mgY: "martingale N G (0::real) Y"
  shows "martingale (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0
      (\<lambda>u p. X u (fst p) * Y u (snd p))"
proof -
  interpret PM: prob_space M by (rule M)
  interpret PN: prob_space N by (rule N)
  interpret MX: martingale M F "0::real" X by (rule mgX)
  interpret MY: martingale N G "0::real" Y by (rule mgY)
  interpret PP: prob_space "M \<Otimes>\<^sub>M N" by (rule prob_space_pair_measure[OF M N])
  interpret PS: pair_sigma_finite M N by unfold_locales
  have FMF: "filtered_measure M F (0::real)" by unfold_locales
  have FMG: "filtered_measure N G (0::real)" by unfold_locales
  interpret FP: finite_filtered_measure "M \<Otimes>\<^sub>M N" "\<lambda>u. F u \<Otimes>\<^sub>M G u" "0::real"
    unfolding finite_filtered_measure_def
    using filtered_measure_pair[OF FMF FMG] PP.finite_measure_axioms by blast
  have Xm: "X u \<in> borel_measurable M" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MX.subalgebras[OF u] MX.adapted[OF u]])
  have Ym: "Y u \<in> borel_measurable N" if u: "0 \<le> u" for u
    by (rule measurable_from_subalg[OF MY.subalgebras[OF u] MY.adapted[OF u]])
  have prodm: "(\<lambda>p. X w (fst p) * Y z (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    if w: "0 \<le> w" and z: "0 \<le> z" for w z
    by (rule borel_measurable_times
        [OF measurable_compose[OF measurable_fst Xm[OF w]]
            measurable_compose[OF measurable_snd Ym[OF z]]])
  have pint: "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X w (fst p) * Y z (snd p))"
    if w: "0 \<le> w" and z: "0 \<le> z" for w z
  proof (rule PS.Fubini_integrable[OF prodm[OF w z]])
    have "integrable M (\<lambda>\<omega>. \<bar>X w \<omega>\<bar> * (\<integral>\<omega>'. \<bar>Y z \<omega>'\<bar> \<partial>N))"
      using MX.integrable[OF w] by simp
    then show "integrable M
        (\<lambda>\<omega>. \<integral>\<omega>'. norm (X w (fst (\<omega>, \<omega>')) * Y z (snd (\<omega>, \<omega>'))) \<partial>N)"
      by (simp add: abs_mult)
  next
    show "AE \<omega> in M. integrable N
        (\<lambda>\<omega>'. X w (fst (\<omega>, \<omega>')) * Y z (snd (\<omega>, \<omega>')))"
      using MY.integrable[OF z] by simp
  qed
  have si: "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p) * Y u (snd p))
      = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X v (fst p) * Y v (snd p))"
    if u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> sets (F u \<Otimes>\<^sub>M G u)" for A u v
  proof -
    have v: "0 \<le> v" using u uv by simp
    have AM: "A \<in> sets (M \<Otimes>\<^sub>M N)" using A FP.sets_F_subset[OF u] by auto
    have key1: "set_lebesgue_integral (M \<Otimes>\<^sub>M N)
          A (\<lambda>p. X w (fst p) * Y z (snd p))
        = (\<integral>\<omega>. X w \<omega> * set_lebesgue_integral N (Pair \<omega> -` A) (Y z) \<partial>M)"
      if w: "0 \<le> w" and z: "0 \<le> z" for w z
    proof -
      have ii: "integrable (M \<Otimes>\<^sub>M N)
          (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>')))"
        using integrable_mult_indicator[OF AM pint[OF w z]]
        by (simp add: case_prod_unfold)
      have inner: "(\<integral>\<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>N)
          = X w \<omega> * set_lebesgue_integral N (Pair \<omega> -` A) (Y z)" for \<omega>
      proof -
        have "(\<integral>\<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>N)
            = (\<integral>\<omega>'. X w \<omega> * (indicator (Pair \<omega> -` A) \<omega>' * Y z \<omega>') \<partial>N)"
          by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
        also have "\<dots>
            = X w \<omega> * (\<integral>\<omega>'. indicator (Pair \<omega> -` A) \<omega>' * Y z \<omega>' \<partial>N)"
          by simp
        finally show ?thesis by (simp add: set_lebesgue_integral_def)
      qed
      have "(\<integral>\<omega>. (\<integral>\<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>N) \<partial>M)
          = (\<integral>p. indicator A p * (X w (fst p) * Y z (snd p)) \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_fst[OF ii] by (simp add: case_prod_unfold)
      then show ?thesis
        unfolding inner by (simp add: set_lebesgue_integral_def)
    qed
    have key2: "set_lebesgue_integral (M \<Otimes>\<^sub>M N)
          A (\<lambda>p. X w (fst p) * Y z (snd p))
        = (\<integral>\<omega>'. Y z \<omega>'
            * set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X w) \<partial>N)"
      if w: "0 \<le> w" and z: "0 \<le> z" for w z
    proof -
      have ii: "integrable (M \<Otimes>\<^sub>M N)
          (case_prod (\<lambda>\<omega> \<omega>'. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>')))"
        using integrable_mult_indicator[OF AM pint[OF w z]]
        by (simp add: case_prod_unfold)
      have inner: "(\<integral>\<omega>. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>M)
          = Y z \<omega>' * set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X w)" for \<omega>'
      proof -
        have "(\<integral>\<omega>. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>M)
            = (\<integral>\<omega>. Y z \<omega>'
                * (indicator ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) \<omega> * X w \<omega>) \<partial>M)"
          by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
        also have "\<dots> = Y z \<omega>'
            * (\<integral>\<omega>. indicator ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) \<omega> * X w \<omega> \<partial>M)"
          by simp
        finally show ?thesis by (simp add: set_lebesgue_integral_def)
      qed
      have "(\<integral>\<omega>'. (\<integral>\<omega>. indicator A (\<omega>, \<omega>') * (X w \<omega> * Y z \<omega>') \<partial>M) \<partial>N)
          = (\<integral>p. indicator A p * (X w (fst p) * Y z (snd p)) \<partial>(M \<Otimes>\<^sub>M N))"
        using PS.integral_snd[OF ii] by (simp add: case_prod_unfold)
      then show ?thesis
        unfolding inner by (simp add: set_lebesgue_integral_def)
    qed
    have eqY: "set_lebesgue_integral N (Pair \<omega> -` A) (Y u)
        = set_lebesgue_integral N (Pair \<omega> -` A) (Y v)" for \<omega>
      by (rule MY.set_integral_eq[OF sets_Pair1[OF A] u uv])
    have eqX: "set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X u)
        = set_lebesgue_integral M ((\<lambda>\<omega>. (\<omega>, \<omega>')) -` A) (X v)" for \<omega>'
      by (rule MX.set_integral_eq[OF sets_Pair2[OF A] u uv])
    have "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p) * Y u (snd p))
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X u (fst p) * Y v (snd p))"
      unfolding key1[OF u u] key1[OF u v] using eqY by simp
    also have "\<dots>
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X v (fst p) * Y v (snd p))"
      unfolding key2[OF u v] key2[OF v v] using eqX by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule FP.martingale_of_set_integral_eq)
    show "adapted_process (M \<Otimes>\<^sub>M N) (\<lambda>u. F u \<Otimes>\<^sub>M G u) 0
        (\<lambda>u p. X u (fst p) * Y u (snd p))"
    proof (unfold_locales)
      fix i :: real assume i: "0 \<le> i"
      show "(\<lambda>p. X i (fst p) * Y i (snd p))
          \<in> borel_measurable (F i \<Otimes>\<^sub>M G i)"
        by (rule borel_measurable_times
            [OF measurable_compose[OF measurable_fst MX.adapted[OF i]]
                measurable_compose[OF measurable_snd MY.adapted[OF i]]])
    qed
    show "integrable (M \<Otimes>\<^sub>M N) (\<lambda>p. X i (fst p) * Y i (snd p))"
      if "0 \<le> i" for i
      by (rule pint[OF that that])
    show "set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X i (fst p) * Y i (snd p))
        = set_lebesgue_integral (M \<Otimes>\<^sub>M N) A (\<lambda>p. X j (fst p) * Y j (snd p))"
      if "0 \<le> i" "i \<le> j" "A \<in> sets (F i \<Otimes>\<^sub>M G i)" for A i j
      by (rule si[OF that])
  qed
qed

section \<open>The pasted law is a member of the class\<close>

text \<open>The glued process splits as a first-factor martingale plus a
  second-factor martingale run on the shifted clock \<open>u \<mapsto> (u - r)\<^sup>+\<close>: on
  \<open>[0,r]\<close> only the first piece moves, after \<open>r\<close> the first piece is frozen at
  \<open>X\<^sub>r\<close> and the second runs.  The identity is only ALMOST everywhere ---
  it uses \<open>X'(0) = 0\<close> from the second factor's clause (i) --- which is what
  \<open>martingale_cong_AE\<close> is for.\<close>

lemma nat_filt_eval:
  fixes Q :: "('n::finite pairpath) measure"
  assumes b: "0 \<le> b" and ba: "b \<le> a"
  shows "(\<lambda>\<omega> :: 'n pairpath. \<omega> b)
      \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) a \<rightarrow>\<^sub>M borel"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use b ba in auto)

theorem pglue_law_X_martingale:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
  shows "martingale (pglue_law r T Q R)
      (natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?FR = "natural_filtration R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?FR (?s u)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using r rT by simp
  have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have PR: "prob_space R" by (rule paper_pair_class_prob[OF R])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have setsR: "sets R = sets (borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF R])
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have s2_0: "0 \<le> ?s u" if "0 \<le> u" for u :: real by simp
  have s2_mono: "?s u \<le> ?s v" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp

  \<comment> \<open>the two factor martingales, on their own clocks\<close>
  have mQ0: "martingale Q ?FQ 0 (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
    by (rule paper_pair_class_X_martingale[OF Q])
  have mQ1: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (min u r) r)) :: real^'n)"
    by (rule martingale_time_change[OF mQ0 s1_0 s1_mono])
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge[OF mQ1])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have mR0: "martingale R ?FR 0 (\<lambda>u \<omega>. fst (\<omega> (min u (T - r))) :: real^'n)"
    by (rule paper_pair_class_X_martingale[OF R])
  have mR: "martingale R (\<lambda>u. ?FR (?s u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (?s u) (T - r))) :: real^'n)"
    by (rule martingale_time_change[OF mR0 s2_0 s2_mono])
  have FQ: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have FR: "filtered_measure R (\<lambda>u. ?FR (?s u)) (0::real)"
  proof -
    interpret MR: martingale R "\<lambda>u. ?FR (?s u)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min (?s u) (T - r))) :: real^'n" by (rule mR)
    show ?thesis by unfold_locales
  qed

  \<comment> \<open>lift both to the product and add\<close>
  have msum: "martingale ?M ?FF 0
      (\<lambda>u p. fst (fst p (min u r)) + fst (snd p (min (?s u) (T - r))) :: real^'n)"
    by (rule martingale_add[OF martingale_pair_fst[OF PQ PR mQ FR]
          martingale_pair_snd[OF PQ PR FQ mR]])

  \<comment> \<open>evaluation measurability on the product filtration\<close>
  have evQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have evR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> ?s u" for b u
    by (rule measurable_compose[OF measurable_snd nat_filt_eval[OF that]])
  have gadap: "(\<lambda>p. ?g p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. undefined)"
      by (auto simp: pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. fst p v)"
        by (simp add: pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have mur: "min u r = r" using rv vu r False by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v)
          = (\<lambda>p. fst p r + (snd p (v - r) - snd p 0))"
        by (simp add: pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p r)
          \<in> borel_measurable (?FF u)"
        using evQ[of r u] r mur by simp
      have m2: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p (v - r))
          \<in> borel_measurable (?FF u)"
        using evR[of "v - r" u] rv vu by simp
      have m3: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
          \<in> borel_measurable (?FF u)" using evR[of 0 u] by simp
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed

  \<comment> \<open>the glued process agrees with the sum almost everywhere\<close>
  have start: "AE p in ?M. fst (snd p 0) = (0::real^'n)"
  proof -
    interpret PP: pair_prob_space Q R
      by (simp add: pair_prob_space_def pair_sigma_finite_def PQ PR
          prob_space_imp_sigma_finite)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable R"
      by (rule pair_law_eval_measurable[OF setsR])
    have sm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd ev])
    have "{q :: (real^'n) \<times> (real^'n^'n). fst q = 0}
        = {0::real^'n} \<times> (UNIV :: (real^'n^'n) set)" by auto
    then have cl: "{q :: (real^'n) \<times> (real^'n^'n). fst q = 0} \<in> sets borel"
      by (simp add: borel_closed closed_Times)
    have "{p \<in> space ?M. fst (snd p 0) = (0::real^'n)}
        = (\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
            -` {q. fst q = (0::real^'n)} \<inter> space ?M" by auto
    then have mset: "{p \<in> space ?M. fst (snd p 0) = (0::real^'n)} \<in> sets ?M"
      using measurable_sets[OF sm cl] by simp
    have "AE \<omega> in Q. AE \<omega>' in R. fst (snd (\<omega>, \<omega>') 0) = (0::real^'n)"
      using R unfolding paper_pair_class_def by auto
    then show ?thesis by (rule PP.AE_pair_measure[OF mset])
  qed
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have FFm: "filtered_measure ?M ?FF (0::real)"
    by (rule filtered_measure_pair[OF FQ FR])
  have gfst: "(\<lambda>p. fst (?g p (min i T)) :: real^'n) \<in> borel_measurable (?FF i)"
    if i: "0 \<le> i" for i
  proof -
    have a1: "0 \<le> min i T" using i T0 by simp
    have a2: "min i T \<le> i" by simp
    show ?thesis by (rule measurable_compose[OF gadap[OF a1 a2] fstB])
  qed
  have mgl: "martingale ?M ?FF 0 (\<lambda>u p. fst (?g p (min u T)) :: real^'n)"
  proof (rule martingale_cong_AE[OF msum])
    show "adapted_process ?M ?FF 0 (\<lambda>u p. fst (?g p (min u T)) :: real^'n)"
      unfolding adapted_process_def adapted_process_axioms_def
      using FFm gfst by blast
  next
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "AE p in ?M. fst (fst p (min u r)) + fst (snd p (min (?s u) (T - r)))
        = fst (?g p (min u T))"
    proof (rule eventually_mono[OF start])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume z: "fst (snd p 0) = (0::real^'n)"
      show "fst (fst p (min u r)) + fst (snd p (min (?s u) (T - r)))
          = fst (?g p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "min (?s u) (T - r) = 0" using True rT by simp
        have g0: "fst (?g p (min u T)) = fst (fst p (min u r))"
          unfolding e1[symmetric] by (simp add: pglue_le[OF muI le])
        show ?thesis using z e2 g0 by simp
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "min (?s u) (T - r) = min u T - r"
          using ru by (simp add: min_def)
        show ?thesis
          using z by (simp add: pglue_ge[OF muI rv] e1 e2)
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) :: real^'n)
      \<in> borel_measurable (natural_filtration (pglue_law r T Q R) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v) u \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ fstB])
  qed
  show ?thesis
    unfolding pglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PR]
        pglue_measurable[OF r rT setsQ setsR] gadap Zm[unfolded pglue_law_def]
        mgl])
qed

lemma outerp_add:
  fixes a b :: "real^'n::finite"
  shows "outerp (a + b) = outerp a + outerp b
      + ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma outerp_zero: "outerp (0 :: real^'n::finite) = 0"
  by (simp add: outerp_def vec_eq_iff)

text \<open>Clause (iv).  Beyond \<open>r\<close> the glued pair is
  \<open>(X\<^sub>r + W, Y\<^sub>r + \<langle>W\<rangle>)\<close>, so its compensated process expands as

    \<open>(outerp X\<^sub>r - Y\<^sub>r) + (outerp W - \<langle>W\<rangle>) + (X\<^sub>r \<otimes> W + W \<otimes> X\<^sub>r)\<close>:

  one compensated martingale from each factor, plus the CROSS term, which is
  a martingale only because the two factors are independent
  (\<open>martingale_pair_mult\<close>, entrywise through \<open>martingale_matI\<close>).\<close>

theorem pglue_law_comp_martingale:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
  shows "martingale (pglue_law r T Q R)
      (natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?M = "Q \<Otimes>\<^sub>M R"
  let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue r T (fst p) (snd p)"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?FR = "natural_filtration R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?FR (?s u)"
  let ?A = "\<lambda>u p. fst (fst p (min u r)) :: real^'n"
  let ?Bp = "\<lambda>u p. fst (snd p (?t u)) :: real^'n"
  have T0: "0 \<le> T" using r rT by simp
  have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have PR: "prob_space R" by (rule paper_pair_class_prob[OF R])
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have setsR: "sets R = sets (borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF R])
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have s2_0: "0 \<le> ?s u" if "0 \<le> u" for u :: real by simp
  have s2_mono: "?s u \<le> ?s v" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp

  \<comment> \<open>the four factor martingales, on the two clocks\<close>
  have mQ1: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (min u r) r)) :: real^'n)"
    by (rule martingale_time_change
        [OF paper_pair_class_X_martingale[OF Q] s1_0 s1_mono])
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge[OF mQ1])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have mR: "martingale R (\<lambda>u. ?FR (?s u)) 0
      (\<lambda>u \<omega>. fst (\<omega> (?t u)) :: real^'n)"
    by (rule martingale_time_change
        [OF paper_pair_class_X_martingale[OF R] s2_0 s2_mono])
  have cQ1: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min (min u r) r)) :: real^'n)
          - snd (\<omega> (min (min u r) r)))"
    by (rule martingale_time_change
        [OF paper_pair_class_compensated_martingale[OF Q] s1_0 s1_mono])
  have cQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u r)) :: real^'n) - snd (\<omega> (min u r)))"
  proof (rule martingale_cong_ge[OF cQ1])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min (min u r) r)) :: real^'n)
          - snd (\<omega> (min (min u r) r)))
        = (\<lambda>\<omega>. outerp (fst (\<omega> (min u r))) - snd (\<omega> (min u r)))" by simp
  qed
  have cR: "martingale R (\<lambda>u. ?FR (?s u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (?t u)) :: real^'n) - snd (\<omega> (?t u)))"
    by (rule martingale_time_change
        [OF paper_pair_class_compensated_martingale[OF R] s2_0 s2_mono])
  have FQ: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have FR: "filtered_measure R (\<lambda>u. ?FR (?s u)) (0::real)"
  proof -
    interpret MR: martingale R "\<lambda>u. ?FR (?s u)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (?t u)) :: real^'n" by (rule mR)
    show ?thesis by unfold_locales
  qed
  have FFm: "filtered_measure ?M ?FF (0::real)"
    by (rule filtered_measure_pair[OF FQ FR])

  \<comment> \<open>the two cross terms\<close>
  have mA: "martingale ?M ?FF 0 ?A" by (rule martingale_pair_fst[OF PQ PR mQ FR])
  have mB: "martingale ?M ?FF 0 ?Bp" by (rule martingale_pair_snd[OF PQ PR FQ mR])
  have cross1: "martingale ?M ?FF 0 (\<lambda>u p. (\<chi> i j. ?A u p $ i * ?Bp u p $ j))"
  proof (rule martingale_matI)
    fix i j :: 'n
    have "martingale ?M ?FF 0 (\<lambda>u p. ?A u p $ i * ?Bp u p $ j)"
      by (rule martingale_pair_mult[OF PQ PR martingale_vec_nth[OF mQ]
            martingale_vec_nth[OF mR]])
    then show "martingale ?M ?FF 0
        (\<lambda>u p. (\<chi> i j. ?A u p $ i * ?Bp u p $ j) $ i $ j)" by simp
  qed
  have cross2: "martingale ?M ?FF 0 (\<lambda>u p. (\<chi> i j. ?Bp u p $ i * ?A u p $ j))"
  proof (rule martingale_matI)
    fix i j :: 'n
    have "martingale ?M ?FF 0 (\<lambda>u p. ?A u p $ j * ?Bp u p $ i)"
      by (rule martingale_pair_mult[OF PQ PR martingale_vec_nth[OF mQ]
            martingale_vec_nth[OF mR]])
    then show "martingale ?M ?FF 0
        (\<lambda>u p. (\<chi> i j. ?Bp u p $ i * ?A u p $ j) $ i $ j)"
      by (simp add: mult.commute)
  qed
  have csum: "martingale ?M ?FF 0
      (\<lambda>u p. ((outerp (?A u p) - snd (fst p (min u r)))
            + (outerp (?Bp u p) - snd (snd p (?t u))))
          + ((\<chi> i j. ?A u p $ i * ?Bp u p $ j)
            + (\<chi> i j. ?Bp u p $ i * ?A u p $ j)))"
    by (rule martingale_add[OF martingale_add
          [OF martingale_pair_fst[OF PQ PR cQ FR]
              martingale_pair_snd[OF PQ PR FQ cR]]
          martingale_add[OF cross1 cross2]])

  \<comment> \<open>adaptedness of the glued compensated process\<close>
  have cB: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n). outerp (fst q) - snd q)
      \<in> borel_measurable borel"
  proof -
    have e: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n). outerp (fst q) - snd q)
        = (\<lambda>q. \<chi> i j. fst q $ i * fst q $ j - snd q $ i $ j)"
      by (rule ext) (simp add: outerp_def vec_eq_iff)
    show ?thesis unfolding e
      by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
          continuous_intros)
  qed
  have evQ: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have evR: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> ?s u" for b u
    by (rule measurable_compose[OF measurable_snd nat_filt_eval[OF that]])
  have gadap: "(\<lambda>p. ?g p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. undefined)"
      by (auto simp: pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v) = (\<lambda>p. fst p v)"
        by (simp add: pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have mur: "min u r = r" using rv vu r False by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. ?g p v)
          = (\<lambda>p. fst p r + (snd p (v - r) - snd p 0))"
        by (simp add: pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. fst p r)
          \<in> borel_measurable (?FF u)" using evQ[of r u] r mur by simp
      have m2: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p (v - r))
          \<in> borel_measurable (?FF u)" using evR[of "v - r" u] rv vu by simp
      have m3: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0)
          \<in> borel_measurable (?FF u)" using evR[of 0 u] by simp
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed
  have gcomp: "(\<lambda>p. outerp (fst (?g p (min i T)) :: real^'n)
      - snd (?g p (min i T))) \<in> borel_measurable (?FF i)" if i: "0 \<le> i" for i
  proof -
    have a1: "0 \<le> min i T" using i T0 by simp
    have a2: "min i T \<le> i" by simp
    show ?thesis by (rule measurable_compose[OF gadap[OF a1 a2] cB])
  qed

  \<comment> \<open>the glued compensated process agrees with the sum almost everywhere\<close>
  have start: "AE p in ?M. snd p 0 = ((0::real^'n), (0::real^'n^'n))"
  proof -
    interpret PP: pair_prob_space Q R
      by (simp add: pair_prob_space_def pair_sigma_finite_def PQ PR
          prob_space_imp_sigma_finite)
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable R"
      by (rule pair_law_eval_measurable[OF setsR])
    have sm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd ev])
    have "{p \<in> space ?M. snd p 0 = ((0::real^'n), (0::real^'n^'n))}
        = (\<lambda>p :: 'n pairpath \<times> 'n pairpath. snd p 0) -` {(0, 0)} \<inter> space ?M"
      by auto
    then have mset: "{p \<in> space ?M. snd p 0 = ((0::real^'n), (0::real^'n^'n))}
        \<in> sets ?M" using measurable_sets[OF sm] by simp
    have "AE \<omega> in Q. AE \<omega>' in R.
        snd (\<omega>, \<omega>') 0 = ((0::real^'n), (0::real^'n^'n))"
      using R unfolding paper_pair_class_def by (auto simp: prod_eq_iff)
    then show ?thesis by (rule PP.AE_pair_measure[OF mset])
  qed
  have mgl: "martingale ?M ?FF 0
      (\<lambda>u p. outerp (fst (?g p (min u T)) :: real^'n) - snd (?g p (min u T)))"
  proof (rule martingale_cong_AE[OF csum])
    show "adapted_process ?M ?FF 0
        (\<lambda>u p. outerp (fst (?g p (min u T)) :: real^'n) - snd (?g p (min u T)))"
      unfolding adapted_process_def adapted_process_axioms_def
      using FFm gcomp by blast
  next
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "AE p in ?M. ((outerp (?A u p) - snd (fst p (min u r)))
            + (outerp (?Bp u p) - snd (snd p (?t u))))
          + ((\<chi> i j. ?A u p $ i * ?Bp u p $ j)
            + (\<chi> i j. ?Bp u p $ i * ?A u p $ j))
        = outerp (fst (?g p (min u T))) - snd (?g p (min u T))"
    proof (rule eventually_mono[OF start])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume z: "snd p 0 = ((0::real^'n), (0::real^'n^'n))"
      show "((outerp (?A u p) - snd (fst p (min u r)))
              + (outerp (?Bp u p) - snd (snd p (?t u))))
            + ((\<chi> i j. ?A u p $ i * ?Bp u p $ j)
              + (\<chi> i j. ?Bp u p $ i * ?A u p $ j))
          = outerp (fst (?g p (min u T))) - snd (?g p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "?t u = 0" using True rT by simp
        have g0: "?g p (min u T) = fst p (min u r)"
          unfolding e1[symmetric] by (simp add: pglue_le[OF muI le])
        show ?thesis
          using z by (simp add: g0 e2 outerp_zero vec_eq_iff)
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "?t u = min u T - r" using ru by (simp add: min_def)
        have g0: "?g p (min u T)
            = fst p r + (snd p (min u T - r) - snd p 0)"
          by (simp add: pglue_ge[OF muI rv])
        have gX: "fst (?g p (min u T)) = ?A u p + ?Bp u p"
          using z by (simp add: g0 e1 e2)
        have gY: "snd (?g p (min u T)) = snd (fst p (min u r)) + snd (snd p (?t u))"
          using z by (simp add: g0 e1 e2)
        show ?thesis by (simp add: gX gY outerp_add)
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T)) :: real^'n)
        - snd (\<omega> (min u T)))
      \<in> borel_measurable (natural_filtration (pglue_law r T Q R) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (pglue_law r T Q R) 0 (\<lambda>v \<omega>. \<omega> v) u \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ cB])
  qed
  show ?thesis
    unfolding pglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PR]
        pglue_measurable[OF r rT setsQ setsR] gadap Zm[unfolded pglue_law_def]
        mgl])
qed

text \<open>Brick (b) of the DPP, complete: the class is closed under INDEPENDENT
  CONCATENATION.  This is the constructive half of the pasting the weak
  dynamic programming principle needs; with a countable Borel partition of
  the endpoint it will give the \<open>\<ge>\<close> inequality of (2.9).\<close>

theorem paper_pair_class_pglue_law:
  fixes Q R :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
  shows "pglue_law r T Q R \<in> paper_pair_class k L T x"
  unfolding paper_pair_class_def mem_Collect_eq
  using prob_space_pglue_law[OF r rT paper_pair_class_prob[OF Q]
      paper_pair_class_prob[OF R] paper_pair_class_sets[OF Q]
      paper_pair_class_sets[OF R]]
    sets_pglue_law pglue_law_start[OF r rT Q R]
    pglue_law_diffquot[OF r rT Q R] pglue_law_X_martingale[OF r rT Q R]
    pglue_law_comp_martingale[OF r rT Q R]
  by blast

text \<open>The immediate payoff: \<open>paper_v\<close> is NONDECREASING in the horizon.  Paste
  the Brownian witness onto the tail of a horizon-\<open>S\<close> member; the glued path
  agrees with the original on \<open>[0,S]\<close>, so it cannot exit earlier.  Together
  with \<open>paper_v_horizon_stable\<close> this makes \<open>paper_v k L T K x\<close> CONSTANT for
  \<open>T\<close> beyond the scale \<open>(r\<^sup>2 - |x|\<^sup>2)/(n-k)\<close> --- the horizon cap of the capped
  path space is invisible, and \<open>paper_v\<close> is the paper's uncapped \<open>v\<close>.\<close>

lemma pexit_pglue_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))"
proof -
  have lb: "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue S T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      show ?thesis
      proof (cases "z \<le> S")
        case True
        have zI: "z \<in> {0..T}" using hit by simp
        have notin: "fst (\<omega> z) \<in> - K"
          using hit True by (simp add: pglue_le[OF zI])
        show ?thesis
          unfolding pexit_def
          by (rule etime_le_of_mem[OF S hit(1) True]) (use notin in simp)
      next
        case False
        then show ?thesis
          using pexit_le_T[OF S, of K "\<lambda>t. fst (\<omega> t)"] by linarith
      qed
    next
      case cap
      then show ?thesis
        using pexit_le_T[OF S, of K "\<lambda>t. fst (\<omega> t)"] ST by linarith
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "pexit S K (\<lambda>t. fst (\<omega> t))
      \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

theorem paper_v_horizon_mono:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes S: "0 \<le> S" and ST: "S \<le> T" and L: "1 \<le> L" and K: "closed K"
  shows "paper_v k L S K x \<le> paper_v k L T K x"
proof -
  have T0: "0 \<le> T" using S ST by simp
  have TS: "0 \<le> T - S" using ST by simp
  have "paper_v k L S K x = Sup ((\<lambda>Q. ess_inf_time Q
      (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))) ` paper_pair_class k L S x)"
    unfolding paper_v_def ..
  also have "\<dots> \<le> paper_v k L T K x"
  proof (rule Sup_least)
    fix e :: ennreal
    assume "e \<in> (\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t))))
        ` paper_pair_class k L S x"
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> paper_pair_class k L S x"
        and e: "e = ess_inf_time Q (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))" by blast
    define R where "R = pair_law_of (T - S) (bmpair (T - S))
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    have R: "R \<in> paper_pair_class k L (T - S) (0 :: real^'n)"
      unfolding R_def by (rule bmpair_law_in_paper_pair_class[OF TS L])
    have G: "pglue_law S T Q R \<in> paper_pair_class k L T x"
      by (rule paper_pair_class_pglue_law[OF S ST Q R])
    let ?M = "Q \<Otimes>\<^sub>M R"
    let ?g = "\<lambda>p :: 'n pairpath \<times> 'n pairpath. pglue S T (fst p) (snd p)"
    let ?BT = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
    have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
    have PR: "prob_space R" by (rule paper_pair_class_prob[OF R])
    interpret PP: pair_prob_space Q R
      by (simp add: pair_prob_space_def pair_sigma_finite_def PQ PR
          prob_space_imp_sigma_finite)
    have setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
      by (rule paper_pair_class_sets[OF Q])
    have setsR: "sets R = sets (borel_of (mtopology_of
        (path_metric (T - S) :: ('n pairpath) metric)))"
      by (rule paper_pair_class_sets[OF R])
    have tauS: "(\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable Q"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable Q"
        by (rule measurable_compose[OF pfst_measurable[OF S setsQ]
              pexit_measurable[OF S K]])
      then show ?thesis by (simp add: pexit_pfst)
    qed
    have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable ?BT"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. pexit T K (pfst T \<omega>)) \<in> borel_measurable ?BT"
        by (rule measurable_compose[OF pfst_measurable[OF T0 refl]
              pexit_measurable[OF T0 K]])
      then show ?thesis by (simp add: pexit_pfst)
    qed
    have aeQ: "AE \<omega> in Q. e \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))"
      unfolding e by (rule ess_inf_time_AE)
    have aeM: "AE p in ?M. e \<le> ennreal (pexit S K (\<lambda>t. fst (fst p t)))"
    proof (rule PP.AE_pair_measure)
      have m1: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath. pexit S K (\<lambda>t. fst (fst p t)))
          \<in> borel_measurable ?M"
        by (rule measurable_compose[OF measurable_fst tauS])
      show "{p \<in> space ?M. e \<le> ennreal (pexit S K (\<lambda>t. fst (fst p t)))}
          \<in> sets ?M" using m1 by measurable
      show "AE \<omega> in Q. AE \<omega>' in R.
          e \<le> ennreal (pexit S K (\<lambda>t. fst (fst (\<omega>, \<omega>') t)))"
        using aeQ by simp
    qed
    have aeG: "AE p in ?M. e \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t)))"
    proof (rule eventually_mono[OF aeM])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume "e \<le> ennreal (pexit S K (\<lambda>t. fst (fst p t)))"
      also have "\<dots> \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t)))"
        by (intro ennreal_leI pexit_pglue_ge[OF S ST])
      finally show "e \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t)))" .
    qed
    have iff: "(AE \<omega> in pglue_law S T Q R.
          e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))
        = (AE p in ?M. e \<le> ennreal (pexit T K (\<lambda>t. fst (?g p t))))"
    proof -
      have mset: "{\<omega> \<in> space ?BT.
          e \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?BT"
        using tauT by measurable
      show ?thesis
        unfolding pglue_law_def pair_law_of_def
        by (rule AE_distr_iff[OF pglue_measurable[OF S ST setsQ setsR] mset])
    qed
    have "e \<le> ess_inf_time (pglue_law S T Q R)
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      unfolding ess_inf_time_def using aeG unfolding iff[symmetric]
      by (intro Sup_upper) simp
    also have "\<dots> \<le> paper_v k L T K x"
      unfolding paper_v_def using G by (intro Sup_upper imageI)
    finally show "e \<le> paper_v k L T K x" .
  qed
  finally show ?thesis .
qed

text \<open>Horizon-cap invisibility, both halves.  Past the natural scale of
  Example 3.1 the horizon does not matter at all, so \<open>paper_v\<close> --- defined
  on the CAPPED path space --- computes the paper's uncapped \<open>v\<close> of (1.6).\<close>

corollary paper_v_horizon_eq:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and r :: real
  assumes k: "k < CARD('n)" and L: "1 \<le> L" and K: "closed K"
    and KB: "K \<subseteq> cball 0 r" and S0: "0 \<le> S" and ST: "S \<le> T"
    and big: "(r * r - x \<bullet> x) / real (CARD('n) - k) \<le> S"
  shows "paper_v k L T K x = paper_v k L S K x"
proof (rule order.antisym)
  show "paper_v k L T K x \<le> paper_v k L S K x"
    using L by (intro paper_v_horizon_stable[OF k _ S0 ST K KB big]) simp
  show "paper_v k L S K x \<le> paper_v k L T K x"
    by (rule paper_v_horizon_mono[OF S0 ST L K])
qed

section \<open>Towards Proposition 2.4: the pasting lower bound\<close>

text \<open>The mechanism behind the \<open>\<ge>\<close> half of the dynamic programming principle
  (2.9).  Pasting produces a member of the class, so the essential infimum of
  ITS exit time is a lower bound for \<open>v(x)\<close>; and the exit time of a glued path
  is at least \<open>r + c\<close> as soon as the first piece stays in \<open>K\<close> up to \<open>r\<close> and
  the re-based continuation stays in \<open>K\<close> for a further \<open>c\<close>.  Note the
  continuation is automatically re-based at the endpoint by \<open>pglue\<close>, so a
  SINGLE law \<open>R\<close> started at \<open>0\<close> supplies a continuation from every endpoint;
  what the full (2.9) needs on top is to choose that law depending on the
  endpoint.\<close>

lemma pexit_path_measurable:
  fixes K :: "(real^'n::finite) set" and N :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. pexit T K (pfst T \<omega>)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pfst_measurable[OF T setsN]
          pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

theorem paper_v_paste_ge:
  fixes Q R :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and K: "closed K"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
    and stay: "AE p in Q \<Otimes>\<^sub>M R.
        c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  shows "ennreal c \<le> paper_v k L T K x"
proof -
  have T0: "0 \<le> T" using r rT by simp
  let ?BT = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have G: "pglue_law r T Q R \<in> paper_pair_class k L T x"
    by (rule paper_pair_class_pglue_law[OF r rT Q R])
  have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BT"
    by (rule pexit_path_measurable[OF T0 K refl])
  have mset: "{\<omega> \<in> space ?BT.
      ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?BT"
    using tauT by measurable
  have iff: "(AE \<omega> in pglue_law r T Q R.
        ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))
      = (AE p in Q \<Otimes>\<^sub>M R. ennreal c
          \<le> ennreal (pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))))"
    unfolding pglue_law_def pair_law_of_def
    by (rule AE_distr_iff[OF pglue_measurable[OF r rT
          paper_pair_class_sets[OF Q] paper_pair_class_sets[OF R]] mset])
  have "AE p in Q \<Otimes>\<^sub>M R. ennreal c
      \<le> ennreal (pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))"
    using stay by (auto intro: ennreal_leI elim: eventually_mono)
  then have ae: "AE \<omega> in pglue_law r T Q R.
      ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding iff .
  have "ennreal c
      \<le> ess_inf_time (pglue_law r T Q R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding ess_inf_time_def using ae by (intro Sup_upper) simp
  also have "\<dots> \<le> paper_v k L T K x"
    unfolding paper_v_def using G by (intro Sup_upper imageI)
  finally show ?thesis .
qed

lemma pexit_pglue_split:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and c: "0 \<le> c" and cT: "r + c \<le> T"
    and stay: "\<And>t. t \<in> {0..r} \<Longrightarrow> fst (\<omega> t) \<in> K"
    and cont: "\<And>s. s \<in> {0..c} \<Longrightarrow> fst (\<omega> r + (\<omega>' s - \<omega>' 0)) \<in> K"
  shows "r + c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
proof -
  have lb: "r + c \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue r T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zI: "z \<in> {0..T}" by simp
      show ?thesis
      proof (rule ccontr)
        assume "\<not> r + c \<le> z"
        then have zc: "z < r + c" by simp
        show False
        proof (cases "z \<le> r")
          case True
          have "fst (\<omega> z) \<in> K" using hit(1) True by (intro stay) simp
          then show False using hit(3) by (simp add: pglue_le[OF zI True])
        next
          case False
          then have rz: "r \<le> z" by simp
          have "z - r \<in> {0..c}" using rz zc by simp
          then have "fst (\<omega> r + (\<omega>' (z - r) - \<omega>' 0)) \<in> K" by (rule cont)
          then show False using hit(3) by (simp add: pglue_ge[OF zI rz])
        qed
      qed
    next
      case cap
      then show ?thesis using cT by simp
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "r + c \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
      \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

corollary paper_v_paste_lower:
  fixes Q R :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes r: "0 \<le> r" and c: "0 \<le> c" and cT: "r + c \<le> T" and K: "closed K"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "R \<in> paper_pair_class k L (T - r) 0"
    and ae: "AE p in Q \<Otimes>\<^sub>M R. (\<forall>t\<in>{0..r}. fst (fst p t) \<in> K)
        \<and> (\<forall>s\<in>{0..c}. fst (fst p r + (snd p s - snd p 0)) \<in> K)"
  shows "ennreal (r + c) \<le> paper_v k L T K x"
proof -
  have rT: "r \<le> T" using c cT by simp
  show ?thesis
  proof (rule paper_v_paste_ge[OF r rT K Q R])
    show "AE p in Q \<Otimes>\<^sub>M R.
        r + c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
    proof (rule eventually_mono[OF ae])
      fix p :: "'n pairpath \<times> 'n pairpath"
      assume "(\<forall>t\<in>{0..r}. fst (fst p t) \<in> K)
          \<and> (\<forall>s\<in>{0..c}. fst (fst p r + (snd p s - snd p 0)) \<in> K)"
      then show "r + c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
        by (intro pexit_pglue_split[OF r rT c cT]) auto
    qed
  qed
qed

section \<open>Lifting a martingale to an infinite product\<close>

text \<open>Pasting with a KERNEL --- a continuation chosen per endpoint --- uses as
  its second factor the product \<open>\<Pi>\<^sub>M i. R i\<close> of all the candidate
  continuations, from which the glue map picks the one the endpoint selects.
  For that, the \<open>i\<close>-th coordinate process must be a martingale for the
  product filtration.  The route is: split the coordinate off with the
  library's \<open>distr_pair_PiM_eq_PiM\<close>, use \<open>martingale_pair_fst\<close> on the
  resulting pair, and transport back along the \<open>distr\<close>.\<close>

lemma sets_PiM_mono:
  assumes S: "\<And>i. i \<in> I \<Longrightarrow> sets (A i) \<subseteq> sets (B i)"
    and SP: "\<And>i. i \<in> I \<Longrightarrow> space (A i) = space (B i)"
  shows "sets (Pi\<^sub>M I A) \<subseteq> sets (Pi\<^sub>M I B)"
proof -
  have sp: "(\<Pi>\<^sub>E i\<in>I. space (A i)) = (\<Pi>\<^sub>E i\<in>I. space (B i))"
    using SP by (intro PiE_cong) simp
  have gen: "{{f \<in> \<Pi>\<^sub>E i\<in>I. space (A i). f i \<in> X} | i X. i \<in> I \<and> X \<in> sets (A i)}
      \<subseteq> sets (Pi\<^sub>M I B)"
  proof safe
    fix i X assume iX: "i \<in> I" "X \<in> sets (A i)"
    then have "X \<in> sets (B i)" using S by blast
    then have "{f \<in> \<Pi>\<^sub>E i\<in>I. space (B i). f i \<in> X} \<in> sets (Pi\<^sub>M I B)"
      using iX(1) unfolding sets_PiM_single by (intro sigma_sets.Basic) blast
    then show "{f \<in> \<Pi>\<^sub>E i\<in>I. space (A i). f i \<in> X} \<in> sets (Pi\<^sub>M I B)"
      unfolding sp .
  qed
  have "sigma_sets (space (Pi\<^sub>M I B))
      {{f \<in> \<Pi>\<^sub>E i\<in>I. space (A i). f i \<in> X} | i X. i \<in> I \<and> X \<in> sets (A i)}
      \<subseteq> sets (Pi\<^sub>M I B)"
    by (rule sets.sigma_sets_subset[OF gen])
  then show ?thesis
    unfolding sets_PiM_single using sp by (simp add: space_PiM)
qed

lemma filtered_measure_PiM:
  fixes G :: "'i \<Rightarrow> real \<Rightarrow> 'a measure"
  assumes F: "\<And>i. i \<in> I \<Longrightarrow> filtered_measure (R i) (G i) (0::real)"
  shows "filtered_measure (Pi\<^sub>M I R) (\<lambda>u. Pi\<^sub>M I (\<lambda>i. G i u)) (0::real)"
proof (unfold_locales)
  fix u :: real assume u: "0 \<le> u"
  have spu: "space (G i u) = space (R i)" if "i \<in> I" for i
    by (rule filtered_measure.space_F[OF F[OF that] u])
  have "space (Pi\<^sub>M I (\<lambda>i. G i u)) = space (Pi\<^sub>M I R)"
    using spu by (simp add: space_PiM cong: PiE_cong)
  moreover have "sets (Pi\<^sub>M I (\<lambda>i. G i u)) \<subseteq> sets (Pi\<^sub>M I R)"
  proof (rule sets_PiM_mono)
    show "sets (G i u) \<subseteq> sets (R i)" if "i \<in> I" for i
      by (rule filtered_measure.sets_F_subset[OF F[OF that] u])
    show "space (G i u) = space (R i)" if "i \<in> I" for i by (rule spu[OF that])
  qed
  ultimately show "subalgebra (Pi\<^sub>M I R) (Pi\<^sub>M I (\<lambda>i. G i u))"
    by (simp add: subalgebra_def)
next
  fix u v :: real assume uv: "0 \<le> u" "u \<le> v"
  then have v: "0 \<le> v" by simp
  have spu: "space (G i u) = space (R i)" if "i \<in> I" for i
    by (rule filtered_measure.space_F[OF F[OF that] uv(1)])
  have spv: "space (G i v) = space (R i)" if "i \<in> I" for i
    by (rule filtered_measure.space_F[OF F[OF that] v])
  show "sets (Pi\<^sub>M I (\<lambda>i. G i u)) \<le> sets (Pi\<^sub>M I (\<lambda>i. G i v))"
  proof (rule sets_PiM_mono)
    show "sets (G i u) \<subseteq> sets (G i v)" if "i \<in> I" for i
      by (rule filtered_measure.sets_F_mono[OF F[OF that] uv(1) uv(2)])
    show "space (G i u) = space (G i v)" if "i \<in> I" for i
      using spu[OF that] spv[OF that] by simp
  qed
qed

text \<open>Transport of the martingale property along a pushforward.  This is the
  general form of what \<open>martingale_pair_law\<close> does for path spaces: if \<open>\<phi>\<close>
  pulls the target filtration back into the source one, a source martingale
  of the composed process is a target martingale.\<close>

theorem martingale_distr:
  fixes Z :: "real \<Rightarrow> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes prob: "prob_space M"
    and phim: "\<phi> \<in> M \<rightarrow>\<^sub>M N"
    and GG: "filtered_measure (distr M N \<phi>) GG (0::real)"
    and pull: "\<And>u. 0 \<le> u \<Longrightarrow> \<phi> \<in> FF u \<rightarrow>\<^sub>M GG u"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable (GG u)"
    and mg: "martingale M FF 0 (\<lambda>u \<omega>. Z u (\<phi> \<omega>))"
  shows "martingale (distr M N \<phi>) GG 0 Z"
proof -
  interpret PM: prob_space M by (rule prob)
  interpret MG: martingale M FF "0::real" "\<lambda>u \<omega>. Z u (\<phi> \<omega>)" by (rule mg)
  interpret PD: prob_space "distr M N \<phi>" by (rule PM.prob_space_distr[OF phim])
  interpret FD: finite_filtered_measure "distr M N \<phi>" GG "0::real"
    unfolding finite_filtered_measure_def
    using GG PD.finite_measure_axioms by blast
  have ZM: "Z u \<in> borel_measurable N" if u: "0 \<le> u" for u
  proof -
    have "Z u \<in> borel_measurable (distr M N \<phi>)"
      by (rule measurable_from_subalg[OF FD.subalgebras[OF u] Zm[OF u]])
    then show ?thesis by simp
  qed
  have int: "integrable (distr M N \<phi>) (Z u)" if u: "0 \<le> u" for u
  proof -
    have e: "integrable (distr M N \<phi>) (Z u) = integrable M (\<lambda>\<omega>. Z u (\<phi> \<omega>))"
      by (rule integrable_distr_eq[OF phim ZM[OF u]])
    show ?thesis unfolding e by (rule MG.integrable[OF u])
  qed
  show ?thesis
  proof (rule FD.martingale_of_set_integral_eq)
    show "adapted_process (distr M N \<phi>) GG 0 Z"
      unfolding adapted_process_def adapted_process_axioms_def
      using GG Zm by blast
    show "integrable (distr M N \<phi>) (Z i)" if "0 \<le> i" for i by (rule int[OF that])
    fix A and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and A: "A \<in> sets (GG i)"
    then have j: "0 \<le> j" by simp
    have AN: "A \<in> sets N" using A FD.sets_F_subset[OF ij(1)] by auto
    have pre: "\<phi> -` A \<inter> space M \<in> sets (FF i)"
      using measurable_sets[OF pull[OF ij(1)] A] MG.space_F[OF ij(1)] by simp
    have key: "set_lebesgue_integral (distr M N \<phi>) A (Z w)
        = set_lebesgue_integral M (\<phi> -` A \<inter> space M) (\<lambda>\<omega>. Z w (\<phi> \<omega>))"
      if w: "0 \<le> w" for w
    proof -
      have "set_lebesgue_integral (distr M N \<phi>) A (Z w)
          = (\<integral>y. indicator A y *\<^sub>R Z w y \<partial>(distr M N \<phi>))"
        by (simp add: set_lebesgue_integral_def)
      also have "\<dots> = (\<integral>\<omega>. indicator A (\<phi> \<omega>) *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
      proof (rule integral_distr[OF phim])
        show "(\<lambda>y. indicator A y *\<^sub>R Z w y) \<in> borel_measurable N"
          using ZM[OF w] AN by measurable
      qed
      also have "\<dots> = (\<integral>\<omega>. indicator (\<phi> -` A \<inter> space M) \<omega> *\<^sub>R Z w (\<phi> \<omega>) \<partial>M)"
        by (rule Bochner_Integration.integral_cong) (auto simp: indicator_def)
      finally show ?thesis by (simp add: set_lebesgue_integral_def)
    qed
    show "set_lebesgue_integral (distr M N \<phi>) A (Z i)
        = set_lebesgue_integral (distr M N \<phi>) A (Z j)"
      unfolding key[OF ij(1)] key[OF j] by (rule MG.set_integral_eq[OF pre ij])
  qed
qed

theorem martingale_PiM_component:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> 'c::{banach,second_countable_topology}"
    and R :: "'i \<Rightarrow> 'a measure" and G :: "'i \<Rightarrow> real \<Rightarrow> 'a measure"
  assumes R: "\<And>j. prob_space (R j)"
    and F: "\<And>j. filtered_measure (R j) (G j) (0::real)"
    and mg: "martingale (R i) (G i) 0 Y"
  shows "martingale (Pi\<^sub>M UNIV R) (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. G j u)) 0 (\<lambda>u f. Y u (f i))"
proof -
  let ?I = "UNIV - {i}"
  let ?S = "Pi\<^sub>M ?I R"
  let ?P = "R i \<Otimes>\<^sub>M ?S"
  let ?\<phi> = "\<lambda>(x, X). X(i := x)"
  let ?GG = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. G j u)"
  let ?FF = "\<lambda>u. G i u \<Otimes>\<^sub>M Pi\<^sub>M ?I (\<lambda>j. G j u)"
  interpret MG: martingale "R i" "G i" "0::real" Y by (rule mg)
  have ins: "insert i ?I = (UNIV :: 'i set)" by auto
  have PS: "prob_space ?S" by (rule prob_space_PiM) (rule R)
  have PP: "prob_space ?P" by (rule prob_space_pair_measure[OF R PS])
  have GI: "filtered_measure ?S (\<lambda>u. Pi\<^sub>M ?I (\<lambda>j. G j u)) (0::real)"
    by (rule filtered_measure_PiM) (rule F)
  have GU: "filtered_measure (Pi\<^sub>M UNIV R) ?GG (0::real)"
    by (rule filtered_measure_PiM) (rule F)

  \<comment> \<open>the coordinate-insertion map, uniformly in the family of factors\<close>
  have phim: "(\<lambda>(x, X). X(i := x)) \<in> (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow>\<^sub>M Pi\<^sub>M UNIV H"
    for H :: "'i \<Rightarrow> 'a measure"
  proof -
    have e: "(\<lambda>(x, X). X(i := x))
        = (\<lambda>p :: 'a \<times> ('i \<Rightarrow> 'a). \<lambda>j. if j = i then fst p else snd p j)"
      by (rule ext) (auto simp: fun_upd_def case_prod_unfold)
    show ?thesis
      unfolding e
    proof (rule measurable_PiM_single')
      fix j :: 'i assume "j \<in> (UNIV :: 'i set)"
      show "(\<lambda>p. if j = i then fst p else snd p j)
          \<in> (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow>\<^sub>M H j"
      proof (cases "j = i")
        case True
        then show ?thesis using measurable_fst by simp
      next
        case False
        then have jI: "j \<in> ?I" by simp
        have "(\<lambda>p :: 'a \<times> ('i \<Rightarrow> 'a). snd p j) \<in> (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow>\<^sub>M H j"
          by (rule measurable_compose[OF measurable_snd
                measurable_component_singleton[OF jI]])
        then show ?thesis using False by simp
      qed
    next
      show "(\<lambda>p j. if j = i then fst p else snd p j)
          \<in> space (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H) \<rightarrow> (\<Pi>\<^sub>E j\<in>UNIV. space (H j))"
      proof (rule Pi_I)
        fix p :: "'a \<times> ('i \<Rightarrow> 'a)"
        assume p: "p \<in> space (H i \<Otimes>\<^sub>M Pi\<^sub>M ?I H)"
        then have p1: "fst p \<in> space (H i)"
          and p2: "snd p \<in> (\<Pi>\<^sub>E j\<in>?I. space (H j))"
          by (simp_all add: space_pair_measure space_PiM mem_Times_iff)
        have "(if j = i then fst p else snd p j) \<in> space (H j)" for j :: 'i
        proof (cases "j = i")
          case True
          then show ?thesis using p1 by simp
        next
          case False
          then have "j \<in> ?I" by simp
          then show ?thesis using p2 False by (simp add: PiE_iff)
        qed
        then show "(\<lambda>j. if j = i then fst p else snd p j)
            \<in> (\<Pi>\<^sub>E j\<in>UNIV. space (H j))" by (simp add: PiE_iff)
      qed
    qed
  qed

  \<comment> \<open>the product is the pushforward of the split product\<close>
  have D: "distr ?P (Pi\<^sub>M UNIV R) ?\<phi> = Pi\<^sub>M UNIV R"
  proof -
    have "distr (R i \<Otimes>\<^sub>M Pi\<^sub>M ?I R) (Pi\<^sub>M (insert i ?I) R) (\<lambda>(x, X). X(i := x))
        = Pi\<^sub>M (insert i ?I) R"
      by (rule distr_pair_PiM_eq_PiM) (auto simp: R)
    then show ?thesis unfolding ins .
  qed

  have Zm: "(\<lambda>f. Y u (f i)) \<in> borel_measurable (?GG u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>f :: 'i \<Rightarrow> 'a. f i) \<in> ?GG u \<rightarrow>\<^sub>M G i u"
      by (rule measurable_component_singleton) simp
    then show ?thesis by (rule measurable_compose[OF _ MG.adapted[OF u]])
  qed
  have mgP: "martingale ?P ?FF 0 (\<lambda>u p. Y u ((case p of (x, X) \<Rightarrow> X(i := x)) i))"
  proof (rule martingale_cong_ge[OF martingale_pair_fst[OF R PS mg GI]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>p :: 'a \<times> ('i \<Rightarrow> 'a). Y u (fst p))
        = (\<lambda>p. Y u ((case p of (x, X) \<Rightarrow> X(i := x)) i))"
      by (rule ext) (simp add: case_prod_unfold)
  qed
  have "martingale (distr ?P (Pi\<^sub>M UNIV R) ?\<phi>) ?GG 0 (\<lambda>u f. Y u (f i))"
  proof (rule martingale_distr[OF PP phim[of R]])
    show "filtered_measure (distr ?P (Pi\<^sub>M UNIV R) ?\<phi>) ?GG (0::real)"
      unfolding D by (rule GU)
    show "?\<phi> \<in> ?FF u \<rightarrow>\<^sub>M ?GG u" if "0 \<le> u" for u by (rule phim)
    show "(\<lambda>f. Y u (f i)) \<in> borel_measurable (?GG u)" if "0 \<le> u" for u
      by (rule Zm[OF that])
    show "martingale ?P ?FF 0
        (\<lambda>u \<omega>. Y u ((case \<omega> of (x, X) \<Rightarrow> X(i := x)) i))"
      by (rule mgP)
  qed
  then show ?thesis unfolding D .
qed

section \<open>Kernel pasting: a continuation chosen by the endpoint\<close>

text \<open>The step from \<open>pglue_law\<close> (one continuation for every endpoint) to what
  (2.9) needs: a countable family \<open>RR\<close> of candidate continuations and a
  past-measurable index \<open>N\<close> selecting one of them.  The second factor is the
  product \<open>\<Pi>\<^sub>M i. RR i\<close> of all candidates --- a probability space, from which
  the glue picks the \<open>N \<omega>\<close>-th.  For a FROZEN first coordinate the index is a
  constant, which is why \<open>martingale_pair_snd_param\<close> and
  \<open>martingale_PiM_component\<close> are the two lemmas this construction rests on.\<close>

definition kglue :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> nat)
    \<Rightarrow> ('n pairpath \<times> (nat \<Rightarrow> 'n pairpath)) \<Rightarrow> 'n pairpath"
  where "kglue r T N p = pglue r T (fst p) (snd p (N (fst p)))"

definition kglue_law :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> nat)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> (nat \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure"
  where "kglue_law r T N Q RR
     = pair_law_of T (kglue r T N) (Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR)"

lemma sets_kglue_law[simp]:
  "sets (kglue_law r T N Q RR)
     = sets (borel_of (mtopology_of (path_metric T
         :: ('n::finite pairpath) metric)))"
  unfolding kglue_law_def by (rule sets_pair_law_of)

lemma space_kglue_law:
  "space (kglue_law r T N Q RR)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding kglue_law_def by (rule space_pair_law_of)

lemma kglue_measurable:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "\<And>j. sets (RR j) = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "kglue r T N \<in> Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M
      borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?M = "Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR"
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p v)
      \<in> borel_measurable ?M" for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have Nfst: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?M \<rightarrow>\<^sub>M count_space UNIV"
    by (rule measurable_compose[OF measurable_fst Nm])
  have eS: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) v)
      \<in> borel_measurable ?M" for v
  proof (rule measurable_compose_countable[OF _ Nfst])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M RR j"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j) \<in> ?M \<rightarrow>\<^sub>M RR j" .
    from measurable_compose[OF this pair_law_eval_measurable[OF setsR]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j v)
        \<in> borel_measurable ?M" .
  qed
  have Xm: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). if t \<le> r then fst p t
        else fst p r + (snd p (N (fst p)) (t - r) - snd p (N (fst p)) 0))
      \<in> borel_measurable ?M" for t
    using eQ eS by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (N (fst p)) (t - r) - snd p (N (fst p)) 0))"
    if p: "p \<in> space ?M" for p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
  proof (rule continuous_on_pglue[OF r rT])
    have "fst p \<in> space Q" and sp: "snd p \<in> space (Pi\<^sub>M UNIV RR)"
      using p by (auto simp: space_pair_measure)
    then show "continuous_on {0..r} (fst p)"
      using space_of_path_sets[OF setsQ] by (auto intro: mspace_path_metricD)
    have "snd p (N (fst p)) \<in> space (RR (N (fst p)))"
      using sp by (simp add: space_PiM PiE_iff)
    then show "continuous_on {0..T - r} (snd p (N (fst p)))"
      using space_of_path_sets[OF setsR] by (auto intro: mspace_path_metricD)
  qed
  show ?thesis
    using pathify_measurable[OF T0 Xm cont]
    unfolding kglue_def pglue_def by simp
qed

lemma prob_space_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "\<And>j. sets (RR j) = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "prob_space (kglue_law r T N Q RR)"
proof -
  interpret PP: prob_space "Q \<Otimes>\<^sub>M Pi\<^sub>M UNIV RR"
    by (rule prob_space_pair_measure[OF PQ prob_space_PiM]) (rule PR)
  show ?thesis
    unfolding kglue_law_def pair_law_of_def
    by (rule PP.prob_space_distr
        [OF kglue_measurable[OF r rT setsQ setsR Nm]])
qed

lemma AE_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "\<And>j. sets (RR j) = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and A: "AE \<omega> in Q. A \<omega>" and B: "AE f in Pi\<^sub>M UNIV RR. B f"
    and imp: "\<And>\<omega> f. \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        f \<in> space (Pi\<^sub>M UNIV RR) \<Longrightarrow> A \<omega> \<Longrightarrow> B f \<Longrightarrow> P (kglue r T N (\<omega>, f))"
  shows "AE \<omega> in kglue_law r T N Q RR. P \<omega>"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PS: prob_space ?S by (rule prob_space_PiM) (rule PR)
  interpret PP: pair_prob_space Q ?S by unfold_locales
  have phim: "kglue r T N \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule kglue_measurable[OF r rT setsQ setsR Nm])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in kglue_law r T N Q RR. P \<omega>)
      = (AE p in ?M. P (kglue r T N p))"
    unfolding kglue_law_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?M. P (kglue r T N p)} \<in> sets ?M"
  proof -
    have "{p \<in> space ?M. P (kglue r T N p)}
        = kglue r T N -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?M"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have inner: "AE \<omega> in Q. AE f in ?S. P (kglue r T N (\<omega>, f))"
  proof -
    have SB: "AE f in ?S. B f \<and> f \<in> space ?S"
      using B AE_space[of ?S] by (auto intro: eventually_conj)
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      show "AE f in ?S. P (kglue r T N (\<omega>, f))"
      proof (rule eventually_mono[OF SB])
        fix f :: "nat \<Rightarrow> 'n pairpath"
        assume "B f \<and> f \<in> space ?S"
        with w show "P (kglue r T N (\<omega>, f))" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?M. P (kglue r T N p)"
    using PP.AE_pair_measure[OF evm] inner by simp
  then show ?thesis unfolding iff .
qed

lemma kglue_law_start:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "\<And>j. RR j \<in> paper_pair_class k L (T - r) 0"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "AE \<omega> in kglue_law r T N Q RR. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff space_borel_of)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  show ?thesis
  proof (rule AE_kglue_law[OF r rT paper_pair_class_prob[OF Q]
        paper_pair_class_prob[OF R] paper_pair_class_sets[OF Q]
        paper_pair_class_sets[OF R] Nm mset])
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding paper_pair_class_def by blast
    show "AE f in Pi\<^sub>M UNIV RR. True" by simp
    fix \<omega> :: "'n pairpath" and f :: "nat \<Rightarrow> 'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "f \<in> space (Pi\<^sub>M UNIV RR)"
      and st: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0" and "True"
    from st show "fst (kglue r T N (\<omega>, f) 0) = x
        \<and> snd (kglue r T N (\<omega>, f) 0) = 0"
      using r rT by (simp add: kglue_def pglue_zero)
  qed
qed

lemma kglue_law_diffquot:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "\<And>j. RR j \<in> paper_pair_class k L (T - r) 0"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  shows "AE \<omega> in kglue_law r T N Q RR. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof (rule paper_pair_class_diffquot_of_pairs[OF sets_kglue_law])
  fix p q :: real
  assume pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
  show "AE \<omega> in kglue_law r T N Q RR.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_kglue_law[OF r rT paper_pair_class_prob[OF Q]
        paper_pair_class_prob[OF R] paper_pair_class_sets[OF Q]
        paper_pair_class_sets[OF R] Nm mset])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding paper_pair_class_def by blast
    show "AE f in Pi\<^sub>M UNIV RR. \<forall>j. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (f j t) - snd (f j s)) \<in> sconstraint k L"
      unfolding AE_all_countable
    proof
      fix j :: nat
      have Pj: "prob_space (RR i)" if "i \<in> (UNIV :: nat set)" for i
        by (rule paper_pair_class_prob[OF R])
      have dj: "distr (Pi\<^sub>M UNIV RR) (RR j) (\<lambda>f. f j) = RR j"
        by (rule distr_PiM_component[OF Pj UNIV_I])
      have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> Pi\<^sub>M UNIV RR \<rightarrow>\<^sub>M RR j"
        by (rule measurable_component_singleton) simp
      have "AE \<omega>' in RR j. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
        using R unfolding paper_pair_class_def by blast
      then have "AE \<omega>' in distr (Pi\<^sub>M UNIV RR) (RR j) (\<lambda>f. f j).
          \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
            (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
        unfolding dj .
      from AE_distrD[OF mj this]
      show "AE f in Pi\<^sub>M UNIV RR. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (f j t) - snd (f j s)) \<in> sconstraint k L" .
    qed
    fix \<omega> :: "'n pairpath" and f :: "nat \<Rightarrow> 'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "f \<in> space (Pi\<^sub>M UNIV RR)"
      and Aw: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      and Bf: "\<forall>j. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (f j t) - snd (f j s)) \<in> sconstraint k L"
    show "(1 / (q - p)) *\<^sub>R (snd (kglue r T N (\<omega>, f) q)
        - snd (kglue r T N (\<omega>, f) p)) \<in> sconstraint k L"
      using pq Aw Bf unfolding kglue_def
      by (intro pglue_diffquot[OF r rT]) auto
  qed
qed

text \<open>Clauses (iii) and (iv) for the kernel glue.  The decomposition is now
  POINTWISE, because the second summand explicitly subtracts the
  continuation's initial value and is therefore literally \<open>0\<close> before \<open>r\<close> ---
  which is what makes it adapted there, since the index \<open>N\<close> is only
  \<open>\<FF>\<^sub>r\<close>-measurable.  Freezing the first coordinate turns \<open>X\<^sub>r\<close> into a CONSTANT,
  so even the cross term of clause (iv) is a second-factor martingale (a
  bounded-linear image of one), and \<open>martingale_pair_snd_param\<close> carries
  everything.\<close>

lemma martingale_sub_initial:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes mg: "martingale M F (0::real) X"
  shows "martingale M F 0 (\<lambda>u \<omega>. X u \<omega> - X 0 \<omega>)"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have c: "martingale M F 0 (\<lambda>_ \<omega>. - X 0 \<omega>)"
  proof (rule MG.martingale_const_fun)
    show "integrable M (\<lambda>\<omega>. - X 0 \<omega>)" using MG.integrable[of 0] by simp
    show "(\<lambda>\<omega>. - X 0 \<omega>) \<in> borel_measurable (F 0)" using MG.adapted[of 0] by simp
  qed
  have "martingale M F 0 (\<lambda>u \<omega>. X u \<omega> + (- X 0 \<omega>))"
    by (rule martingale_add[OF mg c])
  then show ?thesis by simp
qed

lemma kglue_param_martingale:
  fixes RR :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Z :: "nat \<Rightarrow> real \<Rightarrow> ('n pairpath)
        \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes rT: "r \<le> T"
    and mg: "\<And>j. martingale (RR j) (natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v)) 0 (Z j)"
    and PR: "\<And>j. prob_space (RR j)"
  shows "martingale (Pi\<^sub>M UNIV RR)
      (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v) (max (u - r) 0)))
      0 (\<lambda>u f. Z i (max (u - r) 0) (f i))"
proof -
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  have FR: "filtered_measure (RR j) (?GR j) (0::real)" for j
  proof -
    interpret MJ: martingale "RR j" "?GR j" "0::real" "Z j" by (rule mg)
    show ?thesis by unfold_locales
  qed
  have s0: "0 \<le> max (u - r) 0" for u :: real by simp
  have smono: "max (u - r) 0 \<le> max (v - r) 0" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have "martingale (Pi\<^sub>M UNIV RR) (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j u)) 0
      (\<lambda>u f. Z i u (f i))"
    by (rule martingale_PiM_component[OF PR FR mg])
  from martingale_time_change[OF this s0 smono] show ?thesis .
qed

text \<open>The UNIFORM first-moment bound the kernel glue's integrability needs:
  the bound depends only on \<open>k\<close>, \<open>L\<close> and the horizon, not on the member --- so
  it holds simultaneously for every candidate continuation in the family.
  \<open>a \<le> 1 + a\<^sup>2\<close> avoids a square root, so no Cauchy--Schwarz is needed.\<close>

lemma paper_pair_class_norm_mean_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T (0 :: real^'n)" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. norm (fst (\<omega> t)) \<partial>Q)
      \<le> 1 + real CARD('n) * (real CARD('n) * L * T)"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have key: "a \<le> 1 + a * a" for a :: real
  proof -
    have "0 \<le> (a - 1/2) * (a - 1/2)" by simp
    then have "0 \<le> a * a - a + 1/4" by (simp add: algebra_simps)
    then show ?thesis by linarith
  qed
  have ni: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule paper_pair_class_norm_sq_integrable[OF T L Q t])
  have i1: "integrable Q (\<lambda>\<omega>. 1 + fst (\<omega> t) \<bullet> fst (\<omega> t))"
    using ni by simp
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have nm: "(\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> t))) \<in> borel_measurable Q"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable Q"
      by (rule measurable_compose
          [OF paper_pair_class_eval_measurable[OF Q t] fstB])
    then show ?thesis by measurable
  qed
  have le: "norm (fst (\<omega> t)) \<le> 1 + fst (\<omega> t) \<bullet> fst (\<omega> t)" for \<omega> :: "'n pairpath"
    using key[of "norm (fst (\<omega> t))"]
    by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  have i0: "integrable Q (\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> t)))"
  proof (rule Bochner_Integration.integrable_bound[OF i1 nm])
    show "AE \<omega> in Q. norm (norm (fst (\<omega> t)))
        \<le> norm (1 + fst (\<omega> t) \<bullet> fst (\<omega> t))"
      using le by (intro AE_I2) auto
  qed
  have "(\<integral>\<omega>. norm (fst (\<omega> t)) \<partial>Q) \<le> (\<integral>\<omega>. 1 + fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    by (rule integral_mono[OF i0 i1]) (rule le)
  also have "\<dots> = 1 + (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)"
    using ni by (simp add: P.prob_space)
  also have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
  proof -
    have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
        = (\<integral>\<omega>. (\<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2) \<partial>Q)"
      by (rule Bochner_Integration.integral_cong)
        (simp_all add: inner_vec_def power2_eq_square)
    also have "\<dots> = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
      by (rule Bochner_Integration.integral_sum)
        (rule paper_pair_class_sq_integrable[OF T L Q t])
    finally show ?thesis .
  qed
  also have "(\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))
      \<le> (\<Sum>i\<in>(UNIV :: 'n set). real CARD('n) * L * T)"
  proof (rule sum_mono)
    fix i :: 'n
    have "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q)
        \<le> ((0 :: real^'n) $ i)\<^sup>2 + real CARD('n) * L * T"
      by (rule paper_pair_class_sq_mean_le[OF T L Q t])
    then show "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> real CARD('n) * L * T" by simp
  qed
  finally show ?thesis by simp
qed

theorem kglue_law_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "\<And>j. RR j \<in> paper_pair_class k L (T - r) 0"
    and Nm: "N \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M count_space UNIV"
  shows "martingale (kglue_law r T N Q RR)
      (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?GS = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j (?s u))"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?GS u"
  let ?B = "\<lambda>u p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
      fst (snd p (N (fst p)) (?t u)) - fst (snd p (N (fst p)) 0) :: real^'n"
  have T0: "0 \<le> T" using r rT by simp
  have TR: "0 \<le> T - r" using rT by simp
  have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have PRj: "prob_space (RR j)" for j by (rule paper_pair_class_prob[OF R])
  have PS: "prob_space ?S" by (rule prob_space_PiM) (rule PRj)
  interpret PQi: prob_space Q by (rule PQ)
  interpret PS': pair_sigma_finite Q ?S
    by (simp add: pair_sigma_finite_def PQ PS prob_space_imp_sigma_finite)
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have setsR: "sets (RR j) = sets (borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric)))" for j
    by (rule paper_pair_class_sets[OF R])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)

  \<comment> \<open>the first factor's martingale, on the clock \<open>min u r\<close>\<close>
  have mQ0: "martingale Q ?FQ 0 (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
    by (rule paper_pair_class_X_martingale[OF Q])
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge
      [OF martingale_time_change[OF mQ0 s1_0 s1_mono]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have FQf: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have NmQ: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  proof -
    interpret MQ0: martingale Q ?FQ "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ0)
    show ?thesis
      by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nm])
  qed

  \<comment> \<open>the second factor's martingale, per index, on the clock \<open>(u-r)\<^sup>+\<close>\<close>
  have mZ: "martingale (RR j) (?GR j) 0
      (\<lambda>v \<omega>'. fst (\<omega>' (min v (T - r))) - fst (\<omega>' 0) :: real^'n)" for j
  proof -
    have "martingale (RR j) (?GR j) 0 (\<lambda>v \<omega>'.
        (fst (\<omega>' (min v (T - r))) :: real^'n)
          - (\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n) 0 \<omega>')"
      by (rule martingale_sub_initial[OF paper_pair_class_X_martingale[OF R]])
    then show ?thesis using TR by simp
  qed
  have mBj: "martingale ?S ?GS 0
      (\<lambda>u f. fst (f i (?t u)) - fst (f i 0) :: real^'n)" for i
    by (rule kglue_param_martingale[OF rT mZ PRj])
  have FSf: "filtered_measure ?S ?GS (0::real)"
  proof -
    interpret MS: martingale ?S ?GS "0::real"
      "\<lambda>u f. fst (f 0 (?t u)) - fst (f 0 0) :: real^'n" by (rule mBj)
    show ?thesis by unfold_locales
  qed

  \<comment> \<open>evaluation measurability on the product filtration\<close>
  have evQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have Nidx: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?FF u \<rightarrow>\<^sub>M count_space UNIV" if u: "r \<le> u" for u
  proof -
    have "min u r = r" using u by simp
    then show ?thesis using measurable_compose[OF measurable_fst Nm] by simp
  qed
  have evK: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) w)
      \<in> borel_measurable (?FF u)" if u: "r \<le> u" and w: "0 \<le> w" "w \<le> ?s u"
    for u w
  proof (rule measurable_compose_countable[OF _ Nidx[OF u]])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?GS u \<rightarrow>\<^sub>M ?GR j (?s u)"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j)
        \<in> ?FF u \<rightarrow>\<^sub>M ?GR j (?s u)" .
    from measurable_compose[OF this nat_filt_eval[OF w]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j w)
        \<in> borel_measurable (?FF u)" .
  qed
  have adapB: "?B u \<in> borel_measurable (?FF u)" if u: "0 \<le> u" for u
  proof (cases "u \<le> r")
    case True
    then have "?t u = 0" using TR by simp
    then have "?B u = (\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). 0)" by simp
    then show ?thesis by simp
  next
    case False
    then have ru: "r \<le> u" by simp
    have m1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) (?t u)) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) (use TR in auto)
    have m2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) auto
    show ?thesis
      using measurable_compose[OF m1 fstB] measurable_compose[OF m2 fstB]
      by (rule borel_measurable_diff)
  qed
  have BM: "?B u \<in> borel_measurable ?M" if u: "0 \<le> u" for u
  proof -
    interpret FP: filtered_measure ?M ?FF "0::real"
      by (rule filtered_measure_pair[OF FQf FSf])
    show ?thesis
      by (rule measurable_from_subalg[OF FP.subalgebras[OF u] adapB[OF u]])
  qed
  \<comment> \<open>integrability, uniformly over the family of continuations\<close>
  define C where "C = 1 + real CARD('n) * (real CARD('n) * L * (T - r))"
  have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?S \<rightarrow>\<^sub>M RR j" for j
    by (rule measurable_component_singleton) simp
  have dj: "distr ?S (RR j) (\<lambda>f. f j) = RR j" for j
    by (rule distr_PiM_component) (rule PRj, simp)
  have hX: "(\<lambda>\<omega>' :: 'n pairpath. fst (\<omega>' v) :: real^'n)
      \<in> borel_measurable (RR j)" for j v
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsR] fstB])
  have intRj: "integrable (RR j) (\<lambda>\<omega>' :: 'n pairpath. fst (\<omega>' v) :: real^'n)"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    interpret MJ: martingale "RR j" "?GR j" "0::real"
      "\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n"
      by (rule paper_pair_class_X_martingale[OF R])
    have "integrable (RR j) (\<lambda>\<omega>'. fst (\<omega>' (min v (T - r))) :: real^'n)"
      using MJ.integrable[of v] v by simp
    then show ?thesis using v by simp
  qed
  have intSj: "integrable ?S (\<lambda>f. fst (f j v) :: real^'n)"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have "integrable (distr ?S (RR j) (\<lambda>f. f j))
        (\<lambda>\<omega>'. fst (\<omega>' v) :: real^'n)"
      unfolding dj by (rule intRj[OF v])
    then show ?thesis using integrable_distr_eq[OF mj hX] by simp
  qed
  have bndSj: "(\<integral>f. norm (fst (f j v)) \<partial>?S) \<le> C"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have hn: "(\<lambda>\<omega>' :: 'n pairpath. norm (fst (\<omega>' v)))
        \<in> borel_measurable (RR j)" using hX by measurable
    have "(\<integral>f. norm (fst (f j v)) \<partial>?S) = (\<integral>\<omega>'. norm (fst (\<omega>' v)) \<partial>(RR j))"
      by (rule integral_distr[OF mj hn, unfolded dj, symmetric])
    also have "\<dots> \<le> C" unfolding C_def
      by (rule paper_pair_class_norm_mean_le[OF TR L0 R v])
    finally show ?thesis .
  qed
  have tI: "?t u \<in> {0..T - r}" for u using TR by auto
  have zI: "(0::real) \<in> {0..T - r}" using TR by simp
  have secInt: "integrable ?S
      (\<lambda>f. fst (f i (?t u)) - fst (f i 0) :: real^'n)" for i u
    using intSj[OF tI] intSj[OF zI] by simp
  have secBnd: "(\<integral>f. norm (fst (f i (?t u)) - fst (f i 0)) \<partial>?S) \<le> 2 * C"
    for i u
  proof -
    have i1: "integrable ?S (\<lambda>f. norm (fst (f i (?t u))))"
      by (rule integrable_norm[OF intSj[OF tI]])
    have i2: "integrable ?S (\<lambda>f. norm (fst (f i 0)))"
      by (rule integrable_norm[OF intSj[OF zI]])
    have "(\<integral>f. norm (fst (f i (?t u)) - fst (f i 0)) \<partial>?S)
        \<le> (\<integral>f. norm (fst (f i (?t u))) + norm (fst (f i 0)) \<partial>?S)"
      using integrable_norm[OF secInt] i1 i2
      by (intro integral_mono) (auto simp: norm_triangle_ineq4)
    also have "\<dots> = (\<integral>f. norm (fst (f i (?t u))) \<partial>?S)
        + (\<integral>f. norm (fst (f i 0)) \<partial>?S)"
      using i1 i2 by simp
    also have "\<dots> \<le> C + C"
    proof -
      have b1: "(\<integral>f. norm (fst (f i (?t u))) \<partial>?S) \<le> C" by (rule bndSj[OF tI])
      have b2: "(\<integral>f. norm (fst (f i 0)) \<partial>?S) \<le> C" by (rule bndSj[OF zI])
      show ?thesis using b1 b2 by simp
    qed
    finally show ?thesis by simp
  qed
  have intB: "integrable ?M (?B u)" if u: "0 \<le> u" for u
  proof (rule PS'.Fubini_integrable[OF BM[OF u]])
    have e: "(\<lambda>\<omega>. \<integral>f. norm (?B u (\<omega>, f)) \<partial>?S)
        = (\<lambda>\<omega>. \<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)) \<partial>?S)"
      by simp
    have meas: "(\<lambda>\<omega> :: 'n pairpath.
          (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)) \<partial>?S))
        \<in> borel_measurable Q"
    proof (rule measurable_compose_countable
        [where f = "\<lambda>j (_ :: 'n pairpath).
            (\<integral>f. norm (fst (f j (?t u)) - fst (f j 0)) \<partial>?S)"])
      show "(\<lambda>_ :: 'n pairpath.
          (\<integral>f. norm (fst (f j (?t u)) - fst (f j 0)) \<partial>?S))
          \<in> borel_measurable Q" for j by simp
      show "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
    qed
    show "integrable Q (\<lambda>\<omega>. \<integral>f. norm (?B u (\<omega>, f)) \<partial>?S)"
      unfolding e
    proof (rule PQi.integrable_const_bound[where B = "2 * C"])
      show "AE \<omega> in Q. norm (\<integral>f. norm (fst (f (N \<omega>) (?t u))
          - fst (f (N \<omega>) 0)) \<partial>?S) \<le> 2 * C"
      proof (intro AE_I2)
        fix \<omega> :: "'n pairpath"
        have nn: "0 \<le> (\<integral>f. norm (fst (f (N \<omega>) (?t u))
            - fst (f (N \<omega>) 0)) \<partial>?S)"
          by (rule integral_nonneg_AE) simp
        show "norm (\<integral>f. norm (fst (f (N \<omega>) (?t u))
            - fst (f (N \<omega>) 0)) \<partial>?S) \<le> 2 * C"
          using nn secBnd[of "N \<omega>" u] by simp
      qed
    qed (rule meas)
    show "AE \<omega> in Q. integrable ?S (\<lambda>f. ?B u (\<omega>, f))"
      using secInt by simp
  qed

  \<comment> \<open>the two halves, added and matched to the glued process\<close>
  have mB: "martingale ?M ?FF 0 ?B"
  proof (rule martingale_pair_snd_param[OF PQ PS FQf FSf adapB intB])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
    show "martingale ?S ?GS 0 (\<lambda>u f. ?B u (\<omega>, f))"
      using mBj[of "N \<omega>"] by simp
  qed
  have mA: "martingale ?M ?FF 0
      (\<lambda>u p. fst (fst p (min u r)) :: real^'n)"
    by (rule martingale_pair_fst[OF PQ PS mQ FSf])
  have mgl: "martingale ?M ?FF 0
      (\<lambda>u p. fst (kglue r T N p (min u T)) :: real^'n)"
  proof (rule martingale_cong_ge[OF martingale_add[OF mA mB]])
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          fst (fst p (min u r)) + ?B u p)
        = (\<lambda>p. fst (kglue r T N p (min u T)) :: real^'n)"
    proof (rule ext)
      fix p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
      show "fst (fst p (min u r)) + ?B u p
          = fst (kglue r T N p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "?t u = 0" using True TR by simp
        have g0: "kglue r T N p (min u T) = fst p (min u r)"
          unfolding kglue_def e1[symmetric]
          by (simp add: pglue_le[OF muI le])
        show ?thesis by (simp add: g0 e2)
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "?t u = min u T - r" using ru by (simp add: min_def)
        have g0: "kglue r T N p (min u T)
            = fst p r + (snd p (N (fst p)) (min u T - r)
                - snd p (N (fst p)) 0)"
          unfolding kglue_def by (simp add: pglue_ge[OF muI rv])
        show ?thesis by (simp add: g0 e1 e2)
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have gadap: "(\<lambda>p. kglue r T N p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
        = (\<lambda>p. undefined)" by (auto simp: kglue_def pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p v)" by (simp add: kglue_def pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have ru: "r \<le> u" using rv vu by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p r + (snd p (N (fst p)) (v - r)
              - snd p (N (fst p)) 0))"
        by (simp add: kglue_def pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p r)
          \<in> borel_measurable (?FF u)"
        by (rule evQ) (use r ru in auto)
      have m2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) (v - r)) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) (use rv vu in auto)
      have m3: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) auto
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) :: real^'n)
      \<in> borel_measurable (natural_filtration (kglue_law r T N Q RR) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v) u
          \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ fstB])
  qed
  show ?thesis
    unfolding kglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PS]
        kglue_measurable[OF r rT setsQ setsR NmQ] gadap
        Zm[unfolded kglue_law_def] mgl])
qed

text \<open>Material for clause (iv).  The cross term of \<open>outerp (X\<^sub>r + W)\<close> is
  \<open>X\<^sub>r \<otimes> W + W \<otimes> X\<^sub>r\<close>; once the first coordinate is FROZEN, \<open>X\<^sub>r\<close> is a
  constant and the map \<open>v \<mapsto> c \<otimes> v + v \<otimes> c\<close> is linear --- hence bounded,
  the space being finite-dimensional --- so the cross term is a
  bounded-linear image of the second factor's martingale, not a product of
  two martingales.\<close>

lemma norm_outer_prod:
  fixes a b :: "real^'n::finite"
  shows "norm (\<chi> i j. a $ i * b $ j) = norm a * norm b"
proof -
  have "(\<chi> i j. a $ i * b $ j) \<bullet> (\<chi> i j. a $ i * b $ j)
      = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (a $ i * b $ j) * (a $ i * b $ j))"
    by (simp add: inner_vec_def)
  also have "\<dots> = (\<Sum>i\<in>UNIV. (a $ i * a $ i) * (\<Sum>j\<in>UNIV. b $ j * b $ j))"
    by (simp add: sum_distrib_left) (simp add: algebra_simps)
  also have "\<dots> = (a \<bullet> a) * (b \<bullet> b)"
    by (simp add: inner_vec_def sum_distrib_right)
  finally have e: "(\<chi> i j. a $ i * b $ j) \<bullet> (\<chi> i j. a $ i * b $ j)
      = (a \<bullet> a) * (b \<bullet> b)" .
  show ?thesis
    unfolding norm_eq_sqrt_inner e
    by (simp add: real_sqrt_mult)
qed

lemma norm_outerp: "norm (outerp (v :: real^'n::finite)) = norm v * norm v"
proof -
  have "outerp v = (\<chi> i j. v $ i * v $ j)" by (simp add: outerp_def)
  then show ?thesis by (simp add: norm_outer_prod)
qed

lemma bounded_linear_cross_pair:
  fixes c :: "real^'n::finite"
  shows "bounded_linear
      (\<lambda>v :: real^'n. (\<chi> i j. c $ i * v $ j) + (\<chi> i j. v $ i * c $ j))"
proof -
  have "linear (\<lambda>v :: real^'n. (\<chi> i j. c $ i * v $ j) + (\<chi> i j. v $ i * c $ j))"
    by (rule linearI) (auto simp: vec_eq_iff algebra_simps)
  then show ?thesis by (simp add: linear_conv_bounded_linear)
qed

lemma pair_fst_borel:
  "(fst :: (real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma pair_snd_borel:
  "(snd :: (real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)
     \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_intros)

lemma outerp_borel:
  "(outerp :: real^'n::finite \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
proof -
  have e: "(outerp :: real^'n \<Rightarrow> real^'n^'n) = (\<lambda>v. \<chi> i j. v $ i * v $ j)"
    by (rule ext) (simp add: outerp_def)
  show ?thesis unfolding e
    by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
        continuous_intros)
qed

lemma cross_borel:
  fixes c :: "real^'n::finite"
  shows "(\<lambda>v :: real^'n. (\<chi> i j. c $ i * v $ j) + (\<chi> i j. v $ i * c $ j))
      \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
      continuous_intros)

lemma kglue_param_comp_martingale:
  fixes RR :: "nat \<Rightarrow> ('n::finite pairpath) measure"
  assumes rT: "r \<le> T"
    and R: "\<And>j. RR j \<in> paper_pair_class k L (T - r) 0"
  shows "martingale (Pi\<^sub>M UNIV RR)
      (\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega>. \<omega> v) (max (u - r) 0)))
      0 (\<lambda>u f. outerp (fst (f i (min (max (u - r) 0) (T - r)))
              - fst (f i 0) :: real^'n)
          - (snd (f i (min (max (u - r) 0) (T - r))) - snd (f i 0)))"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?GS = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j (?s u))"
  have TR: "0 \<le> T - r" using rT by simp
  have PRj: "prob_space (RR j)" for j by (rule paper_pair_class_prob[OF R])
  have m0: "martingale ?S ?GS 0
      (\<lambda>u f. outerp (fst (f i (?t u)) :: real^'n) - snd (f i (?t u)))"
    by (rule kglue_param_martingale
        [OF rT paper_pair_class_compensated_martingale[OF R] PRj])
  have FSf: "filtered_measure ?S ?GS (0::real)"
  proof -
    interpret MS: martingale ?S ?GS "0::real"
      "\<lambda>u f. outerp (fst (f i (?t u)) :: real^'n) - snd (f i (?t u))"
      by (rule m0)
    show ?thesis by unfold_locales
  qed
  have start: "AE f in ?S. fst (f i 0) = (0::real^'n) \<and> snd (f i 0) = 0"
  proof -
    have Pj: "prob_space (RR j)" if "j \<in> (UNIV::nat set)" for j by (rule PRj)
    have dj: "distr ?S (RR i) (\<lambda>f. f i) = RR i"
      by (rule distr_PiM_component[OF Pj UNIV_I])
    have mi: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i) \<in> ?S \<rightarrow>\<^sub>M RR i"
      by (rule measurable_component_singleton) simp
    have "AE \<omega>' in RR i. fst (\<omega>' 0) = (0::real^'n) \<and> snd (\<omega>' 0) = 0"
      using R unfolding paper_pair_class_def by blast
    then have "AE \<omega>' in distr ?S (RR i) (\<lambda>f. f i).
        fst (\<omega>' 0) = (0::real^'n) \<and> snd (\<omega>' 0) = 0" unfolding dj .
    from AE_distrD[OF mi this] show ?thesis .
  qed
  have adap: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath.
      outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
        - (snd (f i (?t u)) - snd (f i 0))) \<in> borel_measurable (?GS u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i v) \<in> borel_measurable (?GS u)"
      if "0 \<le> v" "v \<le> ?s u" for v
    proof -
      have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i) \<in> ?GS u \<rightarrow>\<^sub>M ?GR i (?s u)"
        by (rule measurable_component_singleton) simp
      from measurable_compose[OF this nat_filt_eval[OF that]] show ?thesis .
    qed
    have e1: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i (?t u)) \<in> borel_measurable (?GS u)"
      by (rule ev) (use TR in auto)
    have e2: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f i 0) \<in> borel_measurable (?GS u)"
      by (rule ev) auto
    have a1: "(\<lambda>f. fst (f i (?t u)) :: real^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e1 pair_fst_borel])
    have a2: "(\<lambda>f. fst (f i 0) :: real^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e2 pair_fst_borel])
    have b1: "(\<lambda>f. snd (f i (?t u)) :: real^'n^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e1 pair_snd_borel])
    have b2: "(\<lambda>f. snd (f i 0) :: real^'n^'n) \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF e2 pair_snd_borel])
    have d1: "(\<lambda>f. fst (f i (?t u)) - fst (f i 0) :: real^'n)
        \<in> borel_measurable (?GS u)" using a1 a2 by (rule borel_measurable_diff)
    have o1: "(\<lambda>f. outerp (fst (f i (?t u)) - fst (f i 0)) :: real^'n^'n)
        \<in> borel_measurable (?GS u)"
      by (rule measurable_compose[OF d1 outerp_borel])
    have d2: "(\<lambda>f. snd (f i (?t u)) - snd (f i 0) :: real^'n^'n)
        \<in> borel_measurable (?GS u)" using b1 b2 by (rule borel_measurable_diff)
    show ?thesis using o1 d2 by (rule borel_measurable_diff)
  qed
  show ?thesis
  proof (rule martingale_cong_AE[OF m0])
    show "adapted_process ?S ?GS 0 (\<lambda>u f.
        outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
          - (snd (f i (?t u)) - snd (f i 0)))"
      unfolding adapted_process_def adapted_process_axioms_def
      using FSf adap by blast
  next
    fix u :: real assume "0 \<le> u"
    show "AE f in ?S. outerp (fst (f i (?t u)) :: real^'n) - snd (f i (?t u))
        = outerp (fst (f i (?t u)) - fst (f i 0)) - (snd (f i (?t u)) - snd (f i 0))"
      by (rule eventually_mono[OF start]) simp
  qed
qed

lemma paper_pair_class_inner_mean_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T (0 :: real^'n)" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      \<le> real CARD('n) * (real CARD('n) * L * T)"
proof -
  have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
  proof -
    have "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
        = (\<integral>\<omega>. (\<Sum>i\<in>UNIV. (fst (\<omega> t) $ i)\<^sup>2) \<partial>Q)"
      by (rule Bochner_Integration.integral_cong)
        (simp_all add: inner_vec_def power2_eq_square)
    also have "\<dots> = (\<Sum>i\<in>UNIV. (\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q))"
      by (rule Bochner_Integration.integral_sum)
        (rule paper_pair_class_sq_integrable[OF T L Q t])
    finally show ?thesis .
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV :: 'n set). real CARD('n) * L * T)"
  proof (rule sum_mono)
    fix i :: 'n
    have "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q)
        \<le> ((0 :: real^'n) $ i)\<^sup>2 + real CARD('n) * L * T"
      by (rule paper_pair_class_sq_mean_le[OF T L Q t])
    then show "(\<integral>\<omega>. (fst (\<omega> t) $ i)\<^sup>2 \<partial>Q) \<le> real CARD('n) * L * T" by simp
  qed
  finally show ?thesis by simp
qed

lemma paper_pair_class_comp_norm_mean_le:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T" and L: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L T (0 :: real^'n)" and t: "t \<in> {0..T}"
  shows "(\<integral>\<omega>. norm (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      \<le> real CARD('n) * (real CARD('n) * L * T) + real CARD('n) * L * T"
proof -
  interpret P: prob_space Q by (rule paper_pair_class_prob[OF Q])
  have iC: "integrable Q (\<lambda>\<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    by (rule paper_pair_class_compensated_integrable[OF Q t])
  have iN: "integrable Q (\<lambda>\<omega>. norm (outerp (fst (\<omega> t)) - snd (\<omega> t)))"
    by (rule integrable_norm[OF iC])
  have iX: "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t))"
    by (rule paper_pair_class_norm_sq_integrable[OF T L Q t])
  have Ym: "(\<lambda>\<omega> :: 'n pairpath. norm (snd (\<omega> t))) \<in> borel_measurable Q"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> t)) \<in> borel_measurable Q"
      by (rule measurable_compose
          [OF paper_pair_class_eval_measurable[OF Q t] pair_snd_borel])
    then show ?thesis by measurable
  qed
  have Yb: "AE \<omega> in Q. norm (snd (\<omega> t)) \<le> real CARD('n) * L * T"
    using paper_pair_class_Y_bounded_ae[OF T L Q] t by (auto elim: eventually_mono)
  have iY: "integrable Q (\<lambda>\<omega> :: 'n pairpath. norm (snd (\<omega> t)))"
  proof (rule P.integrable_const_bound[where B = "real CARD('n) * L * T"])
    show "AE \<omega> in Q. norm (norm (snd (\<omega> t))) \<le> real CARD('n) * L * T"
      using Yb by simp
  qed (rule Ym)
  have "(\<integral>\<omega>. norm (outerp (fst (\<omega> t)) - snd (\<omega> t)) \<partial>Q)
      \<le> (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) + norm (snd (\<omega> t)) \<partial>Q)"
  proof (rule integral_mono[OF iN])
    show "integrable Q (\<lambda>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) + norm (snd (\<omega> t)))"
      using iX iY by simp
    fix \<omega> :: "'n pairpath"
    have "norm (outerp (fst (\<omega> t)) - snd (\<omega> t))
        \<le> norm (outerp (fst (\<omega> t))) + norm (snd (\<omega> t))"
      by (rule norm_triangle_ineq4)
    then show "norm (outerp (fst (\<omega> t)) - snd (\<omega> t))
        \<le> fst (\<omega> t) \<bullet> fst (\<omega> t) + norm (snd (\<omega> t))"
      by (simp add: norm_outerp power2_norm_eq_inner[symmetric] power2_eq_square)
  qed
  also have "\<dots> = (\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
      + (\<integral>\<omega>. norm (snd (\<omega> t)) \<partial>Q)" using iX iY by simp
  also have "\<dots> \<le> real CARD('n) * (real CARD('n) * L * T)
      + real CARD('n) * L * T"
  proof -
    have b1: "(\<integral>\<omega>. fst (\<omega> t) \<bullet> fst (\<omega> t) \<partial>Q)
        \<le> real CARD('n) * (real CARD('n) * L * T)"
      by (rule paper_pair_class_inner_mean_le[OF T L Q t])
    have b2: "(\<integral>\<omega>. norm (snd (\<omega> t)) \<partial>Q) \<le> real CARD('n) * L * T"
    proof -
      have "(\<integral>\<omega>. norm (snd (\<omega> t)) \<partial>Q)
          \<le> (\<integral>\<omega>. real CARD('n) * L * T \<partial>Q)"
        using iY Yb by (intro integral_mono_AE) auto
      also have "\<dots> = real CARD('n) * L * T" by (simp add: P.prob_space)
      finally show ?thesis .
    qed
    from b1 b2 show ?thesis by simp
  qed
  finally show ?thesis .
qed

theorem kglue_law_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "\<And>j. RR j \<in> paper_pair_class k L (T - r) 0"
    and Nm: "N \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M count_space UNIV"
  shows "martingale (kglue_law r T N Q RR)
      (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
proof -
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?M = "Q \<Otimes>\<^sub>M ?S"
  let ?FQ = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?GR = "\<lambda>j. natural_filtration (RR j) 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?s = "\<lambda>u :: real. max (u - r) 0"
  let ?t = "\<lambda>u :: real. min (max (u - r) 0) (T - r)"
  let ?GS = "\<lambda>u. Pi\<^sub>M UNIV (\<lambda>j. ?GR j (?s u))"
  let ?FF = "\<lambda>u. ?FQ (min u r) \<Otimes>\<^sub>M ?GS u"
  let ?Ap = "\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst (fst p r) :: real^'n"
  let ?bb = "\<lambda>u p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
      fst (snd p (N (fst p)) (?t u)) - fst (snd p (N (fst p)) 0) :: real^'n"
  let ?YY = "\<lambda>u p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
      snd (snd p (N (fst p)) (?t u)) - snd (snd p (N (fst p)) 0) :: real^'n^'n"
  let ?P1 = "\<lambda>u p. outerp (?bb u p) - ?YY u p"
  let ?P2 = "\<lambda>u p. (\<chi> i j. ?Ap p $ i * ?bb u p $ j)
      + (\<chi> i j. ?bb u p $ i * ?Ap p $ j)"
  let ?D = "\<lambda>u p. ?P1 u p + ?P2 u p"
  define KK where "KK = real CARD('n) * (real CARD('n) * L * (T - r))
      + real CARD('n) * L * (T - r)"
  define C where "C = 1 + real CARD('n) * (real CARD('n) * L * (T - r))"
  have T0: "0 \<le> T" using r rT by simp
  have TR: "0 \<le> T - r" using rT by simp
  have Cnn: "0 \<le> C" unfolding C_def using L0 TR by simp
  have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  have PRj: "prob_space (RR j)" for j by (rule paper_pair_class_prob[OF R])
  have PS: "prob_space ?S" by (rule prob_space_PiM) (rule PRj)
  interpret PQi: prob_space Q by (rule PQ)
  interpret PS': pair_sigma_finite Q ?S
    by (simp add: pair_sigma_finite_def PQ PS prob_space_imp_sigma_finite)
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have setsR: "sets (RR j) = sets (borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric)))" for j
    by (rule paper_pair_class_sets[OF R])
  have cB: "(\<lambda>q :: (real^'n) \<times> (real^'n^'n). outerp (fst q) - snd q)
      \<in> borel_measurable borel"
    using measurable_compose[OF pair_fst_borel outerp_borel] pair_snd_borel
    by (rule borel_measurable_diff)

  \<comment> \<open>the first factor, on the clock \<open>min u r\<close>\<close>
  have s1_0: "0 \<le> min u r" if "0 \<le> u" for u :: real using that r by simp
  have s1_mono: "min u r \<le> min v r" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mQ0: "martingale Q ?FQ 0 (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
    by (rule paper_pair_class_X_martingale[OF Q])
  have mQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n)"
  proof (rule martingale_cong_ge
      [OF martingale_time_change[OF mQ0 s1_0 s1_mono]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (min u r) r)) :: real^'n)
        = (\<lambda>\<omega>. fst (\<omega> (min u r)))" by simp
  qed
  have FQf: "filtered_measure Q (\<lambda>u. ?FQ (min u r)) (0::real)"
  proof -
    interpret MQ: martingale Q "\<lambda>u. ?FQ (min u r)" "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ)
    show ?thesis by unfold_locales
  qed
  have NmQ: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  proof -
    interpret MQ0: martingale Q ?FQ "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ0)
    show ?thesis
      by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nm])
  qed
  have iAQ: "integrable Q (\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> r) :: real^'n))"
  proof -
    interpret MQ0: martingale Q ?FQ "0::real"
      "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n" by (rule mQ0)
    have "integrable Q (\<lambda>\<omega>. fst (\<omega> (min r r)) :: real^'n)"
      by (rule MQ0.integrable[OF r])
    then show ?thesis by simp
  qed
  have cQ: "martingale Q (\<lambda>u. ?FQ (min u r)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u r)) :: real^'n) - snd (\<omega> (min u r)))"
  proof (rule martingale_cong_ge[OF martingale_time_change
        [OF paper_pair_class_compensated_martingale[OF Q] s1_0 s1_mono]])
    fix u :: real assume "0 \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min (min u r) r)) :: real^'n)
          - snd (\<omega> (min (min u r) r)))
        = (\<lambda>\<omega>. outerp (fst (\<omega> (min u r))) - snd (\<omega> (min u r)))" by simp
  qed

  \<comment> \<open>the second factor, per index\<close>
  have mZ: "martingale (RR j) (?GR j) 0
      (\<lambda>v \<omega>'. fst (\<omega>' (min v (T - r))) - fst (\<omega>' 0) :: real^'n)" for j
  proof -
    have "martingale (RR j) (?GR j) 0 (\<lambda>v \<omega>'.
        (fst (\<omega>' (min v (T - r))) :: real^'n)
          - (\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n) 0 \<omega>')"
      by (rule martingale_sub_initial[OF paper_pair_class_X_martingale[OF R]])
    then show ?thesis using TR by simp
  qed
  have mBj: "martingale ?S ?GS 0
      (\<lambda>u f. fst (f i (?t u)) - fst (f i 0) :: real^'n)" for i
    by (rule kglue_param_martingale[OF rT mZ PRj])
  have mCi: "martingale ?S ?GS 0
      (\<lambda>u f. outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
          - (snd (f i (?t u)) - snd (f i 0)))" for i
    by (rule kglue_param_comp_martingale[OF rT R])
  have FSf: "filtered_measure ?S ?GS (0::real)"
  proof -
    interpret MS: martingale ?S ?GS "0::real"
      "\<lambda>u f. fst (f 0 (?t u)) - fst (f 0 0) :: real^'n" by (rule mBj)
    show ?thesis by unfold_locales
  qed
  have Dfroz: "martingale ?S ?GS 0 (\<lambda>u f.
      (outerp (fst (f i (?t u)) - fst (f i 0) :: real^'n)
          - (snd (f i (?t u)) - snd (f i 0)))
      + ((\<chi> p q. c $ p * (fst (f i (?t u)) - fst (f i 0)) $ q)
          + (\<chi> p q. (fst (f i (?t u)) - fst (f i 0)) $ p * c $ q)))"
    for i and c :: "real^'n"
    by (rule martingale_add[OF mCi martingale_bounded_linear_image
          [OF bounded_linear_cross_pair mBj]])

  \<comment> \<open>evaluation measurability on the product filtration\<close>
  have evQ: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p b)
      \<in> borel_measurable (?FF u)" if "0 \<le> b" "b \<le> min u r" for b u
    by (rule measurable_compose[OF measurable_fst nat_filt_eval[OF that]])
  have Nidx: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). N (fst p))
      \<in> ?FF u \<rightarrow>\<^sub>M count_space UNIV" if u: "r \<le> u" for u
  proof -
    have "min u r = r" using u by simp
    then show ?thesis using measurable_compose[OF measurable_fst Nm] by simp
  qed
  have evK: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p (N (fst p)) w)
      \<in> borel_measurable (?FF u)" if u: "r \<le> u" and w: "0 \<le> w" "w \<le> ?s u"
    for u w
  proof (rule measurable_compose_countable[OF _ Nidx[OF u]])
    fix j :: nat
    have "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?GS u \<rightarrow>\<^sub>M ?GR j (?s u)"
      by (rule measurable_component_singleton) simp
    from measurable_compose[OF measurable_snd this]
    have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j)
        \<in> ?FF u \<rightarrow>\<^sub>M ?GR j (?s u)" .
    from measurable_compose[OF this nat_filt_eval[OF w]]
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). snd p j w)
        \<in> borel_measurable (?FF u)" .
  qed
  have crB: "(\<lambda>ab :: (real^'n) \<times> (real^'n).
      (\<chi> i j. fst ab $ i * snd ab $ j) + (\<chi> i j. snd ab $ i * fst ab $ j))
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
        continuous_intros)
  have adapP: "?P1 u \<in> borel_measurable (?FF u)
      \<and> ?P2 u \<in> borel_measurable (?FF u)
      \<and> (\<lambda>p. 2 * norm (?Ap p) * norm (?bb u p)) \<in> borel_measurable (?FF u)"
    if u: "0 \<le> u" for u
  proof (cases "u \<le> r")
    case True
    then have z: "?t u = 0" using TR by simp
    have e1: "?P1 u = (\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). 0)"
      by (rule ext) (simp add: z outerp_zero)
    have e2: "?P2 u = (\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). 0)"
      by (rule ext) (simp add: z vec_eq_iff)
    have e3: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        2 * norm (?Ap p) * norm (?bb u p)) = (\<lambda>p. 0)"
      by (rule ext) (simp add: z)
    show ?thesis unfolding e1 e2 e3 by simp
  next
    case False
    then have ru: "r \<le> u" by simp
    have k1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) (?t u)) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) (use TR in auto)
    have k2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
        snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
      by (rule evK[OF ru]) auto
    have a0: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p r)
        \<in> borel_measurable (?FF u)" by (rule evQ) (use r ru in auto)
    have mA: "?Ap \<in> borel_measurable (?FF u)"
      by (rule measurable_compose[OF a0 pair_fst_borel])
    have mb: "?bb u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF k1 pair_fst_borel]
        measurable_compose[OF k2 pair_fst_borel]
      by (rule borel_measurable_diff)
    have my: "?YY u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF k1 pair_snd_borel]
        measurable_compose[OF k2 pair_snd_borel]
      by (rule borel_measurable_diff)
    have m1: "?P1 u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF mb outerp_borel] my
      by (rule borel_measurable_diff)
    have mp: "(\<lambda>p. (?Ap p, ?bb u p)) \<in> ?FF u \<rightarrow>\<^sub>M borel"
      using measurable_Pair[OF mA mb] by (simp add: borel_prod)
    have m2: "?P2 u \<in> borel_measurable (?FF u)"
      using measurable_compose[OF mp crB] by simp
    have m3: "(\<lambda>p. 2 * norm (?Ap p) * norm (?bb u p))
        \<in> borel_measurable (?FF u)" using mA mb by measurable
    show ?thesis using m1 m2 m3 by blast
  qed
  have adapD: "?D u \<in> borel_measurable (?FF u)" if u: "0 \<le> u" for u
    using adapP[OF u, THEN conjunct1]
      adapP[OF u, THEN conjunct2, THEN conjunct1]
    by (rule borel_measurable_add)
  have FPf: "filtered_measure ?M ?FF (0::real)"
    by (rule filtered_measure_pair[OF FQf FSf])
  have subM: "h \<in> borel_measurable ?M"
    if u: "0 \<le> u" and h: "h \<in> borel_measurable (?FF u)"
    for u :: real and h :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)
        \<Rightarrow> 'b::{banach,second_countable_topology}"
  proof -
    interpret FP: filtered_measure ?M ?FF "0::real" by (rule FPf)
    show ?thesis
      by (rule measurable_from_subalg[OF FP.subalgebras[OF u] h])
  qed

  \<comment> \<open>uniform bounds on the family, transferred to the product\<close>
  have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f j) \<in> ?S \<rightarrow>\<^sub>M RR j" for j
    by (rule measurable_component_singleton) simp
  have dj: "distr ?S (RR j) (\<lambda>f. f j) = RR j" for j
    by (rule distr_PiM_component) (rule PRj, simp)
  have tI: "?t u \<in> {0..T - r}" for u using TR by auto
  have zI: "(0::real) \<in> {0..T - r}" using TR by simp
  have startj: "AE \<omega>' in RR j. fst (\<omega>' 0) = (0::real^'n) \<and> snd (\<omega>' 0) = 0" for j
    using R unfolding paper_pair_class_def by blast
  have evR: "(\<lambda>\<omega>' :: 'n pairpath. \<omega>' v) \<in> borel_measurable (RR j)" for j v
    by (rule pair_law_eval_measurable[OF setsR])
  have iCS: "integrable ?S (\<lambda>f. outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
      - (snd (f j (?t u)) - snd (f j 0)))" if u: "0 \<le> u" for j u
  proof -
    interpret MC: martingale ?S ?GS "0::real"
      "\<lambda>u f. outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
          - (snd (f j (?t u)) - snd (f j 0))" by (rule mCi)
    show ?thesis by (rule MC.integrable[OF u])
  qed
  have iBS: "integrable ?S (\<lambda>f. fst (f j (?t u)) - fst (f j 0) :: real^'n)"
    if u: "0 \<le> u" for j u
  proof -
    interpret MB: martingale ?S ?GS "0::real"
      "\<lambda>u f. fst (f j (?t u)) - fst (f j 0) :: real^'n" by (rule mBj)
    show ?thesis by (rule MB.integrable[OF u])
  qed
  have bCS: "(\<integral>f. norm (outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
      - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S) \<le> KK" if u: "0 \<le> u" for j u
  proof -
    have h1: "(\<lambda>\<omega>' :: 'n pairpath.
        norm (outerp (fst (\<omega>' (?t u)) - fst (\<omega>' 0) :: real^'n)
          - (snd (\<omega>' (?t u)) - snd (\<omega>' 0)))) \<in> borel_measurable (RR j)"
      using measurable_compose[OF evR pair_fst_borel]
        measurable_compose[OF evR pair_snd_borel] outerp_borel by measurable
    have h2: "(\<lambda>\<omega>' :: 'n pairpath.
        norm (outerp (fst (\<omega>' (?t u)) :: real^'n) - snd (\<omega>' (?t u))))
        \<in> borel_measurable (RR j)"
      using measurable_compose[OF evR pair_fst_borel]
        measurable_compose[OF evR pair_snd_borel] outerp_borel by measurable
    have "(\<integral>f. norm (outerp (fst (f j (?t u)) - fst (f j 0) :: real^'n)
          - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S)
        = (\<integral>\<omega>'. norm (outerp (fst (\<omega>' (?t u)) - fst (\<omega>' 0) :: real^'n)
            - (snd (\<omega>' (?t u)) - snd (\<omega>' 0))) \<partial>(RR j))"
      by (rule integral_distr[OF mj h1, unfolded dj, symmetric])
    also have "\<dots> = (\<integral>\<omega>'. norm (outerp (fst (\<omega>' (?t u)) :: real^'n)
        - snd (\<omega>' (?t u))) \<partial>(RR j))"
      by (rule integral_cong_AE[OF h1 h2])
        (rule eventually_mono[OF startj], simp)
    also have "\<dots> \<le> KK" unfolding KK_def
      by (rule paper_pair_class_comp_norm_mean_le[OF TR L0 R tI])
    finally show ?thesis .
  qed
  have hX: "(\<lambda>\<omega>' :: 'n pairpath. fst (\<omega>' v) :: real^'n)
      \<in> borel_measurable (RR j)" for j v
    by (rule measurable_compose[OF evR pair_fst_borel])
  have istep: "integrable ?S (\<lambda>f. fst (f j v) :: real^'n)"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have "integrable (distr ?S (RR j) (\<lambda>f. f j)) (\<lambda>\<omega>'. fst (\<omega>' v) :: real^'n)"
      unfolding dj
    proof -
      interpret MJ: martingale "RR j" "?GR j" "0::real"
        "\<lambda>w \<omega>'. fst (\<omega>' (min w (T - r))) :: real^'n"
        by (rule paper_pair_class_X_martingale[OF R])
      have "integrable (RR j) (\<lambda>\<omega>'. fst (\<omega>' (min v (T - r))) :: real^'n)"
        using MJ.integrable[of v] v by simp
      then show "integrable (RR j) (\<lambda>\<omega>'. fst (\<omega>' v) :: real^'n)"
        using v by simp
    qed
    then show ?thesis using integrable_distr_eq[OF mj hX] by simp
  qed
  have bstep: "(\<integral>f. norm (fst (f j v) :: real^'n) \<partial>?S) \<le> C"
    if v: "v \<in> {0..T - r}" for j v
  proof -
    have hn: "(\<lambda>\<omega>' :: 'n pairpath. norm (fst (\<omega>' v) :: real^'n))
        \<in> borel_measurable (RR j)" using hX by measurable
    have "(\<integral>f. norm (fst (f j v) :: real^'n) \<partial>?S)
        = (\<integral>\<omega>'. norm (fst (\<omega>' v) :: real^'n) \<partial>(RR j))"
      by (rule integral_distr[OF mj hn, unfolded dj, symmetric])
    also have "\<dots> \<le> C" unfolding C_def
      by (rule paper_pair_class_norm_mean_le[OF TR L0 R v])
    finally show ?thesis .
  qed
  have bBS: "(\<integral>f. norm (fst (f j (?t u)) - fst (f j 0) :: real^'n) \<partial>?S)
      \<le> 2 * C" if u: "0 \<le> u" for j u
  proof -
    have i1: "integrable ?S (\<lambda>f. norm (fst (f j (?t u)) :: real^'n))"
      by (rule integrable_norm[OF istep[OF tI]])
    have i2: "integrable ?S (\<lambda>f. norm (fst (f j 0) :: real^'n))"
      by (rule integrable_norm[OF istep[OF zI]])
    have "(\<integral>f. norm (fst (f j (?t u)) - fst (f j 0) :: real^'n) \<partial>?S)
        \<le> (\<integral>f. norm (fst (f j (?t u)) :: real^'n)
            + norm (fst (f j 0) :: real^'n) \<partial>?S)"
      using integrable_norm[OF iBS[OF u]] i1 i2
      by (intro integral_mono) (auto simp: norm_triangle_ineq4)
    also have "\<dots> = (\<integral>f. norm (fst (f j (?t u)) :: real^'n) \<partial>?S)
        + (\<integral>f. norm (fst (f j 0) :: real^'n) \<partial>?S)" using i1 i2 by simp
    also have "\<dots> \<le> C + C"
    proof -
      have "(\<integral>f. norm (fst (f j (?t u)) :: real^'n) \<partial>?S) \<le> C"
        by (rule bstep[OF tI])
      moreover have "(\<integral>f. norm (fst (f j 0) :: real^'n) \<partial>?S) \<le> C"
        by (rule bstep[OF zI])
      ultimately show ?thesis by simp
    qed
    finally show ?thesis by simp
  qed
  have bBnn: "0 \<le> (\<integral>f. norm (fst (f j (?t u)) - fst (f j 0) :: real^'n) \<partial>?S)"
    for j u by (rule integral_nonneg_AE) simp

  \<comment> \<open>integrability of the two summands on the product\<close>
  have intP1: "integrable ?M (?P1 u)" if u: "0 \<le> u" for u
  proof (rule PS'.Fubini_integrable[OF subM[OF u adapP[OF u, THEN conjunct1]]])
    have meas: "(\<lambda>\<omega> :: 'n pairpath. (\<integral>f. norm (outerp
          (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
            - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S))
        \<in> borel_measurable Q"
    proof (rule measurable_compose_countable
        [where f = "\<lambda>j (_ :: 'n pairpath). (\<integral>f. norm (outerp
            (fst (f j (?t u)) - fst (f j 0) :: real^'n)
              - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S)"])
      show "(\<lambda>_ :: 'n pairpath. (\<integral>f. norm (outerp
          (fst (f j (?t u)) - fst (f j 0) :: real^'n)
            - (snd (f j (?t u)) - snd (f j 0))) \<partial>?S))
          \<in> borel_measurable Q" for j by simp
      show "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
    qed
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<integral>f. norm (?P1 u (\<omega>, f)) \<partial>?S)
        = (\<lambda>\<omega>. \<integral>f. norm (outerp
            (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
              - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S)" by simp
    show "integrable Q (\<lambda>\<omega>. \<integral>f. norm (?P1 u (\<omega>, f)) \<partial>?S)"
      unfolding e
    proof (rule PQi.integrable_const_bound[where B = KK])
      show "AE \<omega> in Q. norm (\<integral>f. norm (outerp
          (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
            - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S) \<le> KK"
      proof (intro AE_I2)
        fix \<omega> :: "'n pairpath"
        have nn: "0 \<le> (\<integral>f. norm (outerp
            (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
              - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S)"
          by (rule integral_nonneg_AE) simp
        show "norm (\<integral>f. norm (outerp
            (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)
              - (snd (f (N \<omega>) (?t u)) - snd (f (N \<omega>) 0))) \<partial>?S) \<le> KK"
          using nn bCS[OF u, of "N \<omega>"] by simp
      qed
    qed (rule meas)
    show "AE \<omega> in Q. integrable ?S (\<lambda>f. ?P1 u (\<omega>, f))"
      using iCS[OF u] by simp
  qed
  have intG: "integrable ?M (\<lambda>p. 2 * norm (?Ap p) * norm (?bb u p))"
    if u: "0 \<le> u" for u
  proof (rule PS'.Fubini_integrable
      [OF subM[OF u adapP[OF u, THEN conjunct2, THEN conjunct2]]])
    have pull: "(\<integral>f. 2 * norm (fst (\<omega> r) :: real^'n)
          * norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n) \<partial>?S)
        = 2 * norm (fst (\<omega> r) :: real^'n)
          * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
              :: real^'n) \<partial>?S)" for \<omega> :: "'n pairpath" by simp
    have meas: "(\<lambda>\<omega> :: 'n pairpath. 2 * norm (fst (\<omega> r) :: real^'n)
          * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
              :: real^'n) \<partial>?S)) \<in> borel_measurable Q"
    proof -
      have m1: "(\<lambda>\<omega> :: 'n pairpath. norm (fst (\<omega> r) :: real^'n))
          \<in> borel_measurable Q" using iAQ by (rule borel_measurable_integrable)
      have m2: "(\<lambda>\<omega> :: 'n pairpath. (\<integral>f. norm (fst (f (N \<omega>) (?t u))
            - fst (f (N \<omega>) 0) :: real^'n) \<partial>?S)) \<in> borel_measurable Q"
      proof (rule measurable_compose_countable
          [where f = "\<lambda>j (_ :: 'n pairpath). (\<integral>f. norm (fst (f j (?t u))
              - fst (f j 0) :: real^'n) \<partial>?S)"])
        show "(\<lambda>_ :: 'n pairpath. (\<integral>f. norm (fst (f j (?t u))
            - fst (f j 0) :: real^'n) \<partial>?S)) \<in> borel_measurable Q" for j
          by simp
        show "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
      qed
      show ?thesis using m1 m2 by measurable
    qed
    show "integrable Q (\<lambda>\<omega>. \<integral>f. norm (2 * norm (?Ap (\<omega>, f))
        * norm (?bb u (\<omega>, f))) \<partial>?S)"
    proof (rule Bochner_Integration.integrable_bound
        [where f = "\<lambda>\<omega> :: 'n pairpath. 4 * C * norm (fst (\<omega> r) :: real^'n)"])
      show "integrable Q (\<lambda>\<omega> :: 'n pairpath.
          4 * C * norm (fst (\<omega> r) :: real^'n))" using iAQ by simp
      show "(\<lambda>\<omega>. \<integral>f. norm (2 * norm (?Ap (\<omega>, f))
          * norm (?bb u (\<omega>, f))) \<partial>?S) \<in> borel_measurable Q"
        using meas by simp
      show "AE \<omega> in Q. norm (\<integral>f. norm (2 * norm (?Ap (\<omega>, f))
          * norm (?bb u (\<omega>, f))) \<partial>?S)
          \<le> norm (4 * C * norm (fst (\<omega> r) :: real^'n))"
      proof (intro AE_I2)
        fix \<omega> :: "'n pairpath"
        have "(\<integral>f. norm (2 * norm (fst (\<omega> r) :: real^'n)
              * norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0) :: real^'n)) \<partial>?S)
            = 2 * norm (fst (\<omega> r) :: real^'n)
              * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
                  :: real^'n) \<partial>?S)" by simp
        moreover have "2 * norm (fst (\<omega> r) :: real^'n)
              * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
                  :: real^'n) \<partial>?S)
            \<le> 2 * norm (fst (\<omega> r) :: real^'n) * (2 * C)"
          using bBS[OF u, of "N \<omega>"] by (intro mult_left_mono) auto
        moreover have "0 \<le> 2 * norm (fst (\<omega> r) :: real^'n)
              * (\<integral>f. norm (fst (f (N \<omega>) (?t u)) - fst (f (N \<omega>) 0)
                  :: real^'n) \<partial>?S)"
          using bBnn[of "N \<omega>" u] by simp
        ultimately show "norm (\<integral>f. norm (2 * norm (?Ap (\<omega>, f))
            * norm (?bb u (\<omega>, f))) \<partial>?S)
            \<le> norm (4 * C * norm (fst (\<omega> r) :: real^'n))"
          using Cnn by simp
      qed
    qed
    show "AE \<omega> in Q. integrable ?S
        (\<lambda>f. 2 * norm (?Ap (\<omega>, f)) * norm (?bb u (\<omega>, f)))"
      using integrable_norm[OF iBS[OF u]] by simp
  qed
  have intD: "integrable ?M (?D u)" if u: "0 \<le> u" for u
  proof -
    have iP2: "integrable ?M (?P2 u)"
    proof (rule Bochner_Integration.integrable_bound[OF intG[OF u]])
      show "?P2 u \<in> borel_measurable ?M"
        by (rule subM[OF u adapP[OF u, THEN conjunct2, THEN conjunct1]])
      show "AE p in ?M. norm (?P2 u p)
          \<le> norm (2 * norm (?Ap p) * norm (?bb u p))"
      proof (intro AE_I2)
        fix p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
        have key: "norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
            \<le> norm (2 * norm a * norm b)" for a b :: "real^'n"
        proof -
          have "norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
              \<le> norm (\<chi> i j. a $ i * b $ j) + norm (\<chi> i j. b $ i * a $ j)"
            by (rule norm_triangle_ineq)
          also have "\<dots> = 2 * norm a * norm b"
          proof -
            have n1: "norm (\<chi> i j. a $ i * b $ j) = norm a * norm b"
              by (rule norm_outer_prod)
            have n2: "norm (\<chi> i j. b $ i * a $ j) = norm b * norm a"
              by (rule norm_outer_prod)
            show ?thesis unfolding n1 n2 by simp
          qed
          finally show ?thesis by simp
        qed
        show "norm (?P2 u p)
            \<le> norm (2 * norm (?Ap p) * norm (?bb u p))" by (rule key)
      qed
    qed
    show ?thesis using intP1[OF u] iP2 by simp
  qed
  have mD: "martingale ?M ?FF 0 ?D"
  proof (rule martingale_pair_snd_param[OF PQ PS FQf FSf adapD intD])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space Q"
    show "martingale ?S ?GS 0 (\<lambda>u f. ?D u (\<omega>, f))"
      using Dfroz[of "N \<omega>" "fst (\<omega> r)"] by simp
  qed
  have mCQ: "martingale ?M ?FF 0
      (\<lambda>u p. outerp (fst (fst p (min u r)) :: real^'n) - snd (fst p (min u r)))"
    by (rule martingale_pair_fst[OF PQ PS cQ FSf])
  have mgl: "martingale ?M ?FF 0
      (\<lambda>u p. outerp (fst (kglue r T N p (min u T)) :: real^'n)
          - snd (kglue r T N p (min u T)))"
  proof (rule martingale_cong_ge[OF martingale_add[OF mCQ mD]])
    fix u :: real assume u: "0 \<le> u"
    have muI: "min u T \<in> {0..T}" using u T0 by simp
    show "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          (outerp (fst (fst p (min u r)) :: real^'n) - snd (fst p (min u r)))
            + ?D u p)
        = (\<lambda>p. outerp (fst (kglue r T N p (min u T)) :: real^'n)
            - snd (kglue r T N p (min u T)))"
    proof (rule ext)
      fix p :: "'n pairpath \<times> (nat \<Rightarrow> 'n pairpath)"
      show "(outerp (fst (fst p (min u r)) :: real^'n) - snd (fst p (min u r)))
            + ?D u p
          = outerp (fst (kglue r T N p (min u T)) :: real^'n)
            - snd (kglue r T N p (min u T))"
      proof (cases "u \<le> r")
        case True
        then have uT: "u \<le> T" using rT by simp
        then have le: "min u T \<le> r" using True by simp
        have e1: "min u T = min u r" using True uT by simp
        have e2: "?t u = 0" using True TR by simp
        have g0: "kglue r T N p (min u T) = fst p (min u r)"
          unfolding kglue_def e1[symmetric]
          by (simp add: pglue_le[OF muI le])
        show ?thesis by (simp add: g0 e2 outerp_zero vec_eq_iff)
      next
        case False
        then have ru: "r < u" by simp
        have rv: "r \<le> min u T" using ru rT by simp
        have e1: "min u r = r" using ru by simp
        have e2: "?t u = min u T - r" using ru by (simp add: min_def)
        have g0: "kglue r T N p (min u T)
            = fst p r + (snd p (N (fst p)) (min u T - r)
                - snd p (N (fst p)) 0)"
          unfolding kglue_def by (simp add: pglue_ge[OF muI rv])
        have gX: "fst (kglue r T N p (min u T)) = ?Ap p + ?bb u p"
          by (simp add: g0 e2)
        have gY: "snd (kglue r T N p (min u T)) = snd (fst p r) + ?YY u p"
          by (simp add: g0 e2)
        have "outerp (fst (kglue r T N p (min u T)) :: real^'n)
              - snd (kglue r T N p (min u T))
            = (outerp (?Ap p) + outerp (?bb u p)
                + ((\<chi> i j. ?Ap p $ i * ?bb u p $ j)
                    + (\<chi> i j. ?bb u p $ i * ?Ap p $ j)))
              - (snd (fst p r) + ?YY u p)"
          unfolding gX gY by (simp only: outerp_add)
        also have "\<dots> = (outerp (?Ap p) - snd (fst p r)) + ?D u p"
          by (simp add: algebra_simps)
        finally show ?thesis using e1 by simp
      qed
    qed
  qed

  \<comment> \<open>transport to the pasted law\<close>
  have gadap: "(\<lambda>p. kglue r T N p v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (cases "v \<le> T")
    case False
    then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
        = (\<lambda>p. undefined)" by (auto simp: kglue_def pglue_def)
    then show ?thesis by simp
  next
    case True
    then have vI: "v \<in> {0..T}" using v by simp
    show ?thesis
    proof (cases "v \<le> r")
      case True
      then have "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p v)" by (simp add: kglue_def pglue_le[OF vI])
      then show ?thesis using evQ[of v u] v vu True by simp
    next
      case False
      then have rv: "r \<le> v" by simp
      have ru: "r \<le> u" using rv vu by simp
      have e: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). kglue r T N p v)
          = (\<lambda>p. fst p r + (snd p (N (fst p)) (v - r)
              - snd p (N (fst p)) 0))"
        by (simp add: kglue_def pglue_ge[OF vI rv])
      have m1: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath). fst p r)
          \<in> borel_measurable (?FF u)" by (rule evQ) (use r ru in auto)
      have m2: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) (v - r)) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) (use rv vu in auto)
      have m3: "(\<lambda>p :: 'n pairpath \<times> (nat \<Rightarrow> 'n pairpath).
          snd p (N (fst p)) 0) \<in> borel_measurable (?FF u)"
        by (rule evK[OF ru]) auto
      show ?thesis unfolding e using m1 m2 m3 by simp
    qed
  qed
  have Zm: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T)) :: real^'n)
        - snd (\<omega> (min u T)))
      \<in> borel_measurable (natural_filtration (kglue_law r T N Q RR) 0
          (\<lambda>v \<omega>. \<omega> v) u)" if u: "0 \<le> u" for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T))
        \<in> natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v) u
          \<rightarrow>\<^sub>M borel"
      by (rule nat_filt_eval) (use u T0 in auto)
    then show ?thesis by (rule measurable_compose[OF _ cB])
  qed
  show ?thesis
    unfolding kglue_law_def
    by (rule martingale_pair_law[OF prob_space_pair_measure[OF PQ PS]
        kglue_measurable[OF r rT setsQ setsR NmQ] gadap
        Zm[unfolded kglue_law_def] mgl])
qed

text \<open>Kernel pasting, complete: the class is closed under concatenation with a
  continuation CHOSEN BY THE ENDPOINT, along any countable past-measurable
  selector.  This is what Proposition 2.4's \<open>\<ge>\<close> inequality needs on top of
  \<open>paper_pair_class_pglue_law\<close>: with an \<open>\<epsilon>\<close>-optimal continuation attached to
  each cell of a countable Borel partition of \<open>X(r)\<close>, the pasted law realises
  \<open>r + v(X(r))\<close> up to \<open>\<epsilon>\<close>.\<close>

theorem paper_pair_class_kglue_law:
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and Q: "Q \<in> paper_pair_class k L r x"
    and R: "\<And>j. RR j \<in> paper_pair_class k L (T - r) 0"
    and Nm: "N \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M count_space UNIV"
  shows "kglue_law r T N Q RR \<in> paper_pair_class k L T x"
proof -
  have NmQ: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
  proof -
    interpret MQ0: martingale Q "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      "0::real" "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n"
      by (rule paper_pair_class_X_martingale[OF Q])
    show ?thesis
      by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nm])
  qed
  show ?thesis
    unfolding paper_pair_class_def mem_Collect_eq
  proof (intro conjI)
    show "prob_space (kglue_law r T N Q RR)"
      by (rule prob_space_kglue_law[OF r rT paper_pair_class_prob[OF Q]
            paper_pair_class_prob[OF R] paper_pair_class_sets[OF Q]
            paper_pair_class_sets[OF R] NmQ])
    show "sets (kglue_law r T N Q RR)
        = sets (borel_of (mtopology_of (path_metric T
            :: ('n pairpath) metric)))" by (rule sets_kglue_law)
    show "AE \<omega> in kglue_law r T N Q RR. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      by (rule kglue_law_start[OF r rT Q R NmQ])
    show "AE \<omega> in kglue_law r T N Q RR. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      by (rule kglue_law_diffquot[OF r rT Q R NmQ])
    show "martingale (kglue_law r T N Q RR)
        (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)) :: real^'n)"
      by (rule kglue_law_X_martingale[OF r rT L0 Q R Nm])
    show "martingale (kglue_law r T N Q RR)
        (natural_filtration (kglue_law r T N Q RR) 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T)) :: real^'n) - snd (\<omega> (min u T)))"
      by (rule kglue_law_comp_martingale[OF r rT L0 Q R Nm])
  qed
qed

section \<open>What Theorem 1.1 currently asserts about the paper's own \<open>v\<close>\<close>

text \<open>The clauses of Theorem 1.1 that are proved for \<open>paper_v\<close> --- the
  faithful rendering of Eq. (1.6) --- collected in one place, so that the
  state of the formalisation is a single citable fact.

  Clause (2), the viscosity property, is NOT here: it needs the dynamic
  programming principle of Proposition 2.4 and, on top of that, Section 3's
  It\<open>\<^bold>o\<close>/SDE layer.  Clause (3) is here only for the ball; the interior value
  for \<open>n - k \<ge> 2\<close> is open.  Clause (4), uniqueness, is
  \<open>Theorem_1_1.theorem_1_1_uniqueness_general\<close> and is a statement about
  viscosity solutions rather than about \<open>paper_v\<close>.\<close>

theorem theorem_1_1_paper_v_fragment:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and r :: real
  assumes k: "k < CARD('n)" and T: "0 < T" and L: "1 \<le> L"
    and K: "closed K" and KB: "K \<subseteq> cball 0 r"
  shows
    \<comment> \<open>clause (0), in Example 3.1's sharp horizon-free form (3.10)\<close>
    "paper_v k L T K x \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
    \<comment> \<open>clause (1): upper semicontinuity in the starting point\<close>
    and "paper_v k L T K x < b \<Longrightarrow>
        eventually (\<lambda>y. paper_v k L T K y < b) (nhds x)"
    \<comment> \<open>clause (3) on the ball: \<open>v\<close> vanishes on the boundary\<close>
    and "K = cball 0 r \<Longrightarrow> norm x = r \<Longrightarrow> paper_v k L T K x = 0"
    \<comment> \<open>and the horizon cap is invisible past the scale of (3.10), so this
        IS the paper's uncapped \<open>v\<close>\<close>
    and "(r * r - x \<bullet> x) / real (CARD('n) - k) \<le> S \<Longrightarrow> 0 \<le> S \<Longrightarrow> S \<le> T
        \<Longrightarrow> paper_v k L T K x = paper_v k L S K x"
proof -
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L by simp
  show "paper_v k L T K x \<le> ennreal ((r * r - x \<bullet> x) / real (CARD('n) - k))"
    by (rule paper_v_le_ball_bound[OF k T0 L0 KB])
  show "paper_v k L T K x < b \<Longrightarrow>
      eventually (\<lambda>y. paper_v k L T K y < b) (nhds x)"
    by (rule paper_v_usc_unconditional[OF T L K])
  show "K = cball 0 r \<Longrightarrow> norm x = r \<Longrightarrow> paper_v k L T K x = 0"
    by (simp add: paper_v_boundary_zero[OF k T L0])
  show "(r * r - x \<bullet> x) / real (CARD('n) - k) \<le> S \<Longrightarrow> 0 \<le> S \<Longrightarrow> S \<le> T
      \<Longrightarrow> paper_v k L T K x = paper_v k L S K x"
    by (rule paper_v_horizon_eq[OF k L K KB])
qed

section \<open>The supremum in (1.6) is attained\<close>

text \<open>The pointwise half of Larsson--Ruf's Proposition 2.2(ii): the class is
  sequentially compact and the essential infimum of the exit time is upper
  semicontinuous along weak convergence, so the supremum defining \<open>paper_v\<close>
  is a maximum.  The paper's Section 3.1 opens by fixing an optimizer, so
  this is needed there independently of the dynamic programming principle.

  The usc input (\<open>Exit_Semicontinuity.ess_inf_pexit_usc\<close>) lives on the
  VECTOR path space, so the functional is first transported along the
  \<open>X\<close>-component map \<open>pfst\<close>, which is \<open>1\<close>-Lipschitz between the two path
  metrics --- weak convergence then pushes forward.\<close>

lemma pfst_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
proof -
  have "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))" by (intro continuous_intros)
  then show ?thesis unfolding pfst_def by (rule mspace_path_metricI)
qed

lemma Lipschitz_pfst:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n::finite pairpath) metric)
      (path_metric T :: (real \<Rightarrow> real^'n) metric) (pfst T)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pfst T \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
    by (intro funcsetI pfst_mspace[OF T])
  have key: "mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
        (pfst T \<omega>) (pfst T \<omega>')
      \<le> 1 * mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
    if w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and w': "\<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)" for \<omega> \<omega>'
  proof -
    have rw: "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
      by (rule pfst_mspace[OF T w])
    have rw': "pfst T \<omega>' \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
      by (rule pfst_mspace[OF T w'])
    have pw: "\<forall>t\<in>{0..T}. dist (\<omega> t) (\<omega>' t)
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      using path_mdist_le_iff_all[OF T w w'] by blast
    have pwr: "dist (pfst T \<omega> t) (pfst T \<omega>' t)
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      if t: "t \<in> {0..T}" for t
    proof -
      have "dist (fst (\<omega> t)) (fst (\<omega>' t)) \<le> dist (\<omega> t) (\<omega>' t)"
        by (rule dist_fst_le)
      then show ?thesis using bspec[OF pw t] t by (simp add: pfst_def)
    qed
    have "mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
          (pfst T \<omega>) (pfst T \<omega>')
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      using path_mdist_le_iff_all[OF T rw rw'] pwr by blast
    then show ?thesis by simp
  qed
  show "\<exists>B. \<forall>\<omega>\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>\<omega>'\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
            (pfst T \<omega>) (pfst T \<omega>')
          \<le> B * mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
    by (intro exI[of _ 1] ballI key)
qed

lemma ess_inf_time_pfst:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "ess_inf_time (distr Q (borel_of (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'n) metric))) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  have "ess_inf_time (distr Q (borel_of (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'n) metric))) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (pfst T \<omega>))"
    by (rule Value_Function.ess_inf_time_distr
        [OF pfst_measurable[OF T setsQ] pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

theorem paper_v_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  shows "\<exists>Q \<in> paper_pair_class k L T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = paper_v k L T K x"
proof -
  let ?C = "paper_pair_class k L T x"
  let ?S = "\<lambda>Q :: ('n pairpath) measure.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
  let ?Y = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'n) metric)"
  let ?p = "\<lambda>Q :: ('n pairpath) measure. distr Q (borel_of ?Y) (pfst T)"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L by simp
  have ne: "?C \<noteq> {}"
    using paper_pair_class_shift_image[OF T0, of k L x]
      paper_pair_class_nonempty[OF T0 L] by auto
  have imne: "?S ` ?C \<noteq> {}" using ne by simp
  obtain f :: "nat \<Rightarrow> ennreal" where finc: "incseq f"
    and frange: "range f \<subseteq> ?S ` ?C"
    and fsup: "Sup (?S ` ?C) = (SUP i. f i)"
    using ennreal_Sup_countable_SUP[OF imne] by blast
  have "\<forall>i. \<exists>Q. Q \<in> ?C \<and> f i = ?S Q" using frange by blast
  then obtain Qm :: "nat \<Rightarrow> ('n pairpath) measure"
    where Qm: "\<And>i. Qm i \<in> ?C" and fQ: "\<And>i. f i = ?S (Qm i)" by metis
  have sub: "\<exists>a Q. strict_mono a \<and> Q \<in> ?C
      \<and> weak_conv_on (Qm \<circ> a) Q sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule paper_pair_class_convergent_subsequence[OF T L0]) (rule Qm)
  obtain a Q where sm: "strict_mono a" and Qc: "Q \<in> ?C"
    and wc: "weak_conv_on (Qm \<circ> a) Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    using sub by blast
  have pQ: "prob_space (Qm i)" for i by (rule paper_pair_class_prob[OF Qm])
  have pQc: "prob_space Q" by (rule paper_pair_class_prob[OF Qc])
  have wcY: "weak_conv_on (\<lambda>i. ?p (Qm (a i))) (?p Q) sequentially ?Y"
  proof -
    have "weak_conv_on (\<lambda>i. distr ((Qm \<circ> a) i) (borel_of ?Y) (pfst T))
        (distr Q (borel_of ?Y) (pfst T)) sequentially ?Y"
      by (rule weak_conv_on_pushforward
          [OF Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pfst[OF T0]] wc])
    then show ?thesis by simp
  qed
  have lim: "Limsup sequentially (\<lambda>i. ess_inf_time (?p (Qm (a i))) (pexit T K))
      \<le> ess_inf_time (?p Q) (pexit T K)"
  proof (rule ess_inf_pexit_usc[OF T K wcY])
    show "prob_space (?p (Qm (a i)))" for i
      by (rule prob_space.prob_space_distr[OF pQ pfst_measurable[OF T0]])
        (rule paper_pair_class_sets[OF Qm])
    show "prob_space (?p Q)"
      by (rule prob_space.prob_space_distr[OF pQc pfst_measurable[OF T0]])
        (rule paper_pair_class_sets[OF Qc])
  qed
  have eqS: "ess_inf_time (?p R) (pexit T K) = ?S R" if "R \<in> ?C" for R
    by (rule ess_inf_time_pfst[OF T0 K paper_pair_class_sets[OF that]])
  have lim': "Limsup sequentially (\<lambda>i. ?S (Qm (a i))) \<le> ?S Q"
    using lim by (simp add: eqS[OF Qm] eqS[OF Qc])
  have "f \<longlonglongrightarrow> (SUP i. f i)" using finc by (rule LIMSEQ_SUP)
  then have "(f \<circ> a) \<longlonglongrightarrow> (SUP i. f i)"
    by (rule LIMSEQ_subseq_LIMSEQ[OF _ sm])
  then have "Limsup sequentially (\<lambda>i. ?S (Qm (a i))) = (SUP i. f i)"
    using fQ by (simp add: lim_imp_Limsup o_def)
  with lim' fsup have ge: "Sup (?S ` ?C) \<le> ?S Q" by simp
  have le: "?S Q \<le> Sup (?S ` ?C)" using Qc by (intro Sup_upper imageI)
  from ge le have "?S Q = Sup (?S ` ?C)" by simp
  then show ?thesis using Qc unfolding paper_v_def by blast
qed

section \<open>A measurable selection theorem for upper semicontinuous payoffs\<close>

text \<open>Larsson--Ruf's Proposition 2.2(ii) asserts more than @{thm [source]
  paper_v_attained}: the optimizer can be chosen MEASURABLY in the starting
  point.  Their reference is Bertsekas--Shreve (1978), Proposition 7.33, a
  measurable selection theorem for upper semicontinuous payoffs on compact
  sets.  Nothing of the kind is in the AFP, so it is built here.

  The construction is a greedy nested bisection.  Fix a countable dense
  sequence \<open>z\<close> in the compact metric space \<open>Y\<close>.  Starting from \<open>Y\<close> itself,
  at stage \<open>n\<close> intersect the current compact set with the closed ball of
  radius \<open>2\<^sup>-\<^sup>n\<^sup>-\<^sup>1\<close> around \<open>z j\<close> for the LEAST \<open>j\<close> that keeps the set
  nonempty and does not lower the supremum.  Such a \<open>j\<close> exists because the
  balls of that radius cover the current compact set, so finitely many of
  them do, and a supremum over a finite union is the maximum of the pieces'
  suprema.  The nested compact sets shrink to a point, which is the
  selected one; upper semicontinuity is what makes its value the supremum.

  Measurability is where the greedy recipe pays off.  The sequence of
  chosen indices --- the CODE --- is a countably valued function of the
  parameter, so on each cell of a countable measurable partition the whole
  nested family is a FIXED compact set.  For an open \<open>U\<close> the preimage
  \<open>{x. s x \<in> U}\<close> is then the countable union of those cells whose set is
  contained in \<open>U\<close>.  No limits and no analytic sets are involved.

  Note that an \<epsilon>-version with a COUNTABLY VALUED selector does not exist:
  the supremum of an upper semicontinuous function over a countable dense
  subset can be strictly smaller than its supremum, so no fixed countable
  family of candidates is \<epsilon>-optimal at every parameter.  This is why
  \<open>paper_pair_class_kglue_law\<close>, whose index is countably valued, cannot be
  the final form of the pasting step.\<close>

text \<open>A helper: @{typ ennreal} is densely ordered.  The instance is
  declared for @{typ ereal} but not for @{typ ennreal}.\<close>

lemma ennreal_strict_between:
  fixes a b :: ennreal
  assumes ab: "a < b"
  shows "\<exists>c. a < c \<and> c < b"
proof -
  have "enn2ereal a < enn2ereal b" using ab by (simp add: less_ennreal.rep_eq)
  then obtain e where e1: "enn2ereal a < e" and e2: "e < enn2ereal b"
    using dense by blast
  have "(0::ereal) \<le> enn2ereal a" by simp
  then have e0: "0 \<le> e" using order.strict_implies_order[OF e1] by (rule order_trans)
  have re: "enn2ereal (e2ennreal e) = e" by (rule enn2ereal_e2ennreal[OF e0])
  show ?thesis
  proof (intro exI[of _ "e2ennreal e"] conjI)
    show "a < e2ennreal e" using e1 by (simp add: less_ennreal.rep_eq re)
    show "e2ennreal e < b" using e2 by (simp add: less_ennreal.rep_eq re)
  qed
qed

text \<open>A compact metric space carries a dense SEQUENCE (it is nonempty, so
  the countable dense set can be enumerated).\<close>

lemma (in Metric_space) compact_space_dense_seq:
  assumes cpt: "compact_space mtopology" and ne: "M \<noteq> {}"
  shows "\<exists>z :: nat \<Rightarrow> 'a. (\<forall>j. z j \<in> M)
      \<and> (\<forall>y \<in> M. \<forall>e > 0. \<exists>j. d (z j) y < e)"
proof -
  have cover: "\<exists>K. finite K \<and> K \<subseteq> M \<and> M \<subseteq> (\<Union>x\<in>K. mball x e)" if e: "0 < e" for e
  proof -
    have "M \<subseteq> \<Union> ((\<lambda>x. mball x e) ` M)" using e by auto
    moreover have "openin mtopology U" if "U \<in> (\<lambda>x. mball x e) ` M" for U
      using that by auto
    ultimately obtain F where F: "finite F" "F \<subseteq> (\<lambda>x. mball x e) ` M"
        "M \<subseteq> \<Union>F"
      using cpt unfolding compact_space_alt by (metis topspace_mtopology)
    from F(2) obtain K where K: "K \<subseteq> M" "finite K" "F = (\<lambda>x. mball x e) ` K"
      by (meson finite_subset_image F(1))
    show ?thesis using K F(3) by auto
  qed
  have "\<forall>n::nat. \<exists>K. finite K \<and> K \<subseteq> M \<and> M \<subseteq> (\<Union>x\<in>K. mball x ((1/2)^n))"
    by (intro allI cover) simp
  then obtain KK where KK: "\<And>n::nat. finite (KK n)" "\<And>n::nat. KK n \<subseteq> M"
      "\<And>n::nat. M \<subseteq> (\<Union>x\<in>KK n. mball x ((1/2)^n))"
    by metis
  define D where "D = (\<Union>n::nat. KK n)"
  have Dc: "countable D" unfolding D_def using KK(1) by (blast intro: countable_UN countable_finite)
  have DM: "D \<subseteq> M" unfolding D_def using KK(2) by blast
  have Dne: "D \<noteq> {}"
  proof -
    from ne obtain y where y: "y \<in> M" by blast
    then obtain x where "x \<in> KK 0" using KK(3)[of 0] by auto
    then show ?thesis unfolding D_def by blast
  qed
  define z where "z = from_nat_into D"
  have zr: "range z = D" unfolding z_def by (rule range_from_nat_into[OF Dne Dc])
  have zM: "z j \<in> M" for j using zr DM by blast
  have zd: "\<exists>j. d (z j) y < e" if y: "y \<in> M" and e: "0 < e" for y e
  proof -
    have "(\<lambda>n. (1/2::real)^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) auto
    then have "\<forall>\<^sub>F n in sequentially. (1/2::real)^n < e"
      using e by (rule order_tendstoD(2))
    then obtain n :: nat where n: "(1/2::real)^n < e"
      by (auto simp: eventually_sequentially)
    from KK(3)[of n] y obtain x where x: "x \<in> KK n" "y \<in> mball x ((1/2)^n)" by auto
    then have "d x y < (1/2)^n" by simp
    with n have "d x y < e" by simp
    moreover have "x \<in> D" unfolding D_def using x(1) by blast
    ultimately show ?thesis using zr by (metis rangeE)
  qed
  show ?thesis using zM zd by blast
qed

text \<open>The greedy construction.  \<open>usc_sel_set Y dd z js\<close> is the set reached
  by the index sequence \<open>js\<close> (most recent index first), \<open>usc_sel_good\<close> the
  greedy criterion, \<open>usc_sel_code\<close> the index sequence chosen for the payoff
  \<open>g\<close>, and \<open>usc_sel\<close> the point the nested sets shrink to.  Everything is
  parametrized by the carrier, the distance and the dense sequence, so no
  new locale is needed.\<close>

definition usc_sel_set ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat list \<Rightarrow> 'a set" where
  "usc_sel_set Y dd z
     = rec_list Y (\<lambda>j js S. {y \<in> S. dd (z j) y \<le> (1/2)^(Suc (length js))})"

lemma usc_sel_set_Nil [simp]: "usc_sel_set Y dd z [] = Y"
  by (simp add: usc_sel_set_def)

lemma usc_sel_set_Cons [simp]:
  "usc_sel_set Y dd z (j # js)
     = {y \<in> usc_sel_set Y dd z js. dd (z j) y \<le> (1/2)^(Suc (length js))}"
  by (simp add: usc_sel_set_def)

lemma usc_sel_set_subset: "usc_sel_set Y dd z js \<subseteq> Y"
  by (induct js) auto

lemma usc_sel_set_mono: "usc_sel_set Y dd z (j # js) \<subseteq> usc_sel_set Y dd z js"
  by auto

definition usc_sel_good ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "usc_sel_good Y dd z g js j \<longleftrightarrow>
     usc_sel_set Y dd z (j # js) \<noteq> {}
       \<and> Sup (g ` usc_sel_set Y dd z (j # js)) = Sup (g ` usc_sel_set Y dd z js)"

definition usc_sel_code ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow> nat list"
  where "usc_sel_code Y dd z g
     = rec_nat [] (\<lambda>n js. (LEAST j. usc_sel_good Y dd z g js j) # js)"

lemma usc_sel_code_0 [simp]: "usc_sel_code Y dd z g 0 = []"
  by (simp add: usc_sel_code_def)

lemma usc_sel_code_Suc [simp]:
  "usc_sel_code Y dd z g (Suc n)
     = (LEAST j. usc_sel_good Y dd z g (usc_sel_code Y dd z g n) j)
        # usc_sel_code Y dd z g n"
  by (simp add: usc_sel_code_def)

lemma length_usc_sel_code [simp]: "length (usc_sel_code Y dd z g n) = n"
  by (induct n) simp_all

definition usc_sel ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a" where
  "usc_sel Y dd z g
     = (SOME y. y \<in> (\<Inter>n. usc_sel_set Y dd z (usc_sel_code Y dd z g n)))"

context Metric_space
begin

lemma usc_sel_set_closedin:
  assumes z: "\<And>j. z j \<in> M"
  shows "closedin mtopology (usc_sel_set M d z js)"
proof (induct js)
  case Nil
  show ?case by simp
next
  case (Cons j js)
  have eq: "usc_sel_set M d z (j # js)
      = usc_sel_set M d z js \<inter> mcball (z j) ((1/2)^(Suc (length js)))"
    using usc_sel_set_subset[of M d z js] z by auto
  show ?case unfolding eq by (rule closedin_Int[OF Cons closedin_mcball])
qed

lemma usc_sel_set_compactin:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
  shows "compactin mtopology (usc_sel_set M d z js)"
  by (rule closedin_compact_space[OF cpt usc_sel_set_closedin[OF z]])

text \<open>The greedy step always succeeds: the balls of the current radius
  cover the current compact set, so finitely many of them do, and the
  supremum over a finite union is the maximum of the pieces' suprema.  No
  semicontinuity is used here --- this holds for an ARBITRARY payoff \<open>g\<close>,
  which is what makes \<open>usc_sel\<close> total.\<close>

lemma usc_sel_good_ex:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "usc_sel_set M d z js \<noteq> {}"
  shows "\<exists>j. usc_sel_good M d z g js j"
proof -
  define S where "S = usc_sel_set M d z js"
  define r where "r = (1/2::real)^(Suc (length js))"
  have r0: "0 < r" unfolding r_def by simp
  have SM: "S \<subseteq> M" unfolding S_def by (rule usc_sel_set_subset)
  have Sne: "S \<noteq> {}" using ne unfolding S_def .
  have Scpt: "compactin mtopology S"
    unfolding S_def by (rule usc_sel_set_compactin[OF cpt z])
  have cov: "S \<subseteq> \<Union> (range (\<lambda>j. mball (z j) r))"
  proof
    fix y assume yS: "y \<in> S"
    then have yM: "y \<in> M" using SM by blast
    from dns[OF yM r0] obtain j where "d (z j) y < r" by blast
    then have "y \<in> mball (z j) r" using yM z by simp
    then show "y \<in> \<Union> (range (\<lambda>j. mball (z j) r))" by blast
  qed
  have opn: "openin mtopology U" if "U \<in> range (\<lambda>j. mball (z j) r)" for U
    using that by auto
  have "\<exists>F. finite F \<and> F \<subseteq> range (\<lambda>j. mball (z j) r) \<and> S \<subseteq> \<Union>F"
    using Scpt cov opn unfolding compactin_def by blast
  then obtain F where F: "finite F" "F \<subseteq> range (\<lambda>j. mball (z j) r)" "S \<subseteq> \<Union>F"
    by blast
  from F(1,2) obtain J0 :: "nat set" where J0: "finite J0"
      "F = (\<lambda>j. mball (z j) r) ` J0"
    by (meson finite_subset_image subset_UNIV)
  define J where "J = {j \<in> J0. S \<inter> mball (z j) r \<noteq> {}}"
  have Jfin: "finite J" unfolding J_def using J0(1) by simp
  have Scov: "S = (\<Union>j\<in>J. S \<inter> mball (z j) r)"
  proof
    show "S \<subseteq> (\<Union>j\<in>J. S \<inter> mball (z j) r)"
    proof
      fix y assume yS: "y \<in> S"
      with F(3) J0(2) obtain j where j: "j \<in> J0" "y \<in> mball (z j) r" by auto
      with yS have yj: "y \<in> S \<inter> mball (z j) r" by blast
      with j(1) have "j \<in> J" unfolding J_def by blast
      with yj show "y \<in> (\<Union>j\<in>J. S \<inter> mball (z j) r)" by blast
    qed
  qed blast
  have Jne: "J \<noteq> {}" using Scov Sne by auto
  define h where "h = (\<lambda>j. Sup (g ` (S \<inter> mball (z j) r)))"
  have supS: "Sup (g ` S) = Sup (h ` J)"
  proof (rule antisym)
    show "Sup (g ` S) \<le> Sup (h ` J)"
    proof (rule Sup_least)
      fix v assume "v \<in> g ` S"
      then obtain y where y: "y \<in> S" "v = g y" by blast
      then obtain j where j: "j \<in> J" "y \<in> S \<inter> mball (z j) r" using Scov by blast
      have "v \<le> h j" unfolding h_def using y j by (auto intro: Sup_upper)
      also have "\<dots> \<le> Sup (h ` J)" using j by (auto intro: Sup_upper)
      finally show "v \<le> Sup (h ` J)" .
    qed
    show "Sup (h ` J) \<le> Sup (g ` S)"
    proof (rule Sup_least)
      fix v assume "v \<in> h ` J"
      then obtain j where j: "j \<in> J" "v = h j" by blast
      have "h j \<le> Sup (g ` S)" unfolding h_def
        by (intro Sup_subset_mono image_mono) auto
      then show "v \<le> Sup (g ` S)" using j by simp
    qed
  qed
  have maxin: "Max (h ` J) \<in> h ` J" using Jne Jfin by simp
  have supmax: "Sup (h ` J) = Max (h ` J)"
  proof (rule antisym)
    show "Sup (h ` J) \<le> Max (h ` J)"
      using Jfin by (intro Sup_least) simp
    show "Max (h ` J) \<le> Sup (h ` J)" using maxin by (rule Sup_upper)
  qed
  from maxin obtain j0 where j0eq: "Max (h ` J) = h j0" and j0J: "j0 \<in> J"
    by (rule imageE)
  have j0: "j0 \<in> J" "h j0 = Max (h ` J)" using j0J j0eq by simp_all
  have sub: "S \<inter> mball (z j0) r \<subseteq> usc_sel_set M d z (j0 # js)"
    unfolding S_def r_def by auto
  have "usc_sel_good M d z g js j0"
    unfolding usc_sel_good_def
  proof
    from j0(1) have "S \<inter> mball (z j0) r \<noteq> {}" unfolding J_def by blast
    with sub show "usc_sel_set M d z (j0 # js) \<noteq> {}" by blast
  next
    show "Sup (g ` usc_sel_set M d z (j0 # js))
        = Sup (g ` usc_sel_set M d z js)"
    proof (rule antisym)
      show "Sup (g ` usc_sel_set M d z (j0 # js))
          \<le> Sup (g ` usc_sel_set M d z js)"
        by (intro Sup_subset_mono image_mono usc_sel_set_mono)
      have "Sup (g ` usc_sel_set M d z js) = h j0"
        using supS supmax j0 unfolding S_def by simp
      also have "\<dots> \<le> Sup (g ` usc_sel_set M d z (j0 # js))"
        unfolding h_def using sub by (intro Sup_subset_mono image_mono)
      finally show "Sup (g ` usc_sel_set M d z js)
          \<le> Sup (g ` usc_sel_set M d z (j0 # js))" .
    qed
  qed
  then show ?thesis ..
qed

text \<open>Along the code every set is nonempty and carries the FULL supremum:
  that is the whole point of the greedy criterion.\<close>

lemma usc_sel_code_set:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel_set M d z (usc_sel_code M d z g n) \<noteq> {}
       \<and> Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n)) = Sup (g ` M)"
proof (induct n)
  case 0
  show ?case using ne by simp
next
  case (Suc n)
  then have ne': "usc_sel_set M d z (usc_sel_code M d z g n) \<noteq> {}" by blast
  have "usc_sel_good M d z g (usc_sel_code M d z g n)
      (LEAST j. usc_sel_good M d z g (usc_sel_code M d z g n) j)"
    by (rule LeastI_ex[OF usc_sel_good_ex[OF cpt z dns ne']])
  then show ?case using Suc by (simp add: usc_sel_good_def)
qed

lemma usc_sel_code_set_ne:
  assumes "compact_space mtopology" "\<And>j. z j \<in> M"
    "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e" "M \<noteq> {}"
  shows "usc_sel_set M d z (usc_sel_code M d z g n) \<noteq> {}"
  using usc_sel_code_set[OF assms] by blast

lemma usc_sel_code_set_sup:
  assumes "compact_space mtopology" "\<And>j. z j \<in> M"
    "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e" "M \<noteq> {}"
  shows "Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n)) = Sup (g ` M)"
  using usc_sel_code_set[OF assms] by blast

lemma usc_sel_code_mono:
  assumes mn: "m \<le> n"
  shows "usc_sel_set M d z (usc_sel_code M d z g n)
       \<subseteq> usc_sel_set M d z (usc_sel_code M d z g m)"
  using mn
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m \<le> n")
    case True
    have "usc_sel_set M d z (usc_sel_code M d z g (Suc n))
        \<subseteq> usc_sel_set M d z (usc_sel_code M d z g n)" by auto
    with Suc.hyps[OF True] show ?thesis by blast
  next
    case False
    with Suc.prems have "m = Suc n" by simp
    then show ?thesis by simp
  qed
qed

lemma usc_sel_code_decseq:
  "decseq (\<lambda>n. usc_sel_set M d z (usc_sel_code M d z g n))"
  unfolding decseq_def using usc_sel_code_mono by blast

text \<open>The nested compact sets have a common point, and \<open>usc_sel\<close> is one.\<close>

lemma usc_sel_in_code_set:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel M d z g \<in> usc_sel_set M d z (usc_sel_code M d z g n)"
proof -
  have "(\<Inter>n. usc_sel_set M d z (usc_sel_code M d z g n)) \<noteq> {}"
  proof (rule compact_space_imp_nest[OF cpt])
    show "closedin mtopology (usc_sel_set M d z (usc_sel_code M d z g k))" for k
      by (rule usc_sel_set_closedin[OF z])
    show "usc_sel_set M d z (usc_sel_code M d z g k) \<noteq> {}" for k
      by (rule usc_sel_code_set_ne[OF cpt z dns ne])
    show "decseq (\<lambda>n. usc_sel_set M d z (usc_sel_code M d z g n))"
      by (rule usc_sel_code_decseq)
  qed
  then obtain y0 where "y0 \<in> (\<Inter>n. usc_sel_set M d z (usc_sel_code M d z g n))"
    by blast
  then have "usc_sel M d z g \<in> (\<Inter>n. usc_sel_set M d z (usc_sel_code M d z g n))"
    unfolding usc_sel_def by (rule someI)
  then show ?thesis by blast
qed

lemma usc_sel_in_M:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel M d z g \<in> M"
  using usc_sel_in_code_set[OF cpt z dns ne, of g 0] by simp

text \<open>The sets shrink: at stage \<open>Suc n\<close> everything is within \<open>2\<^sup>-\<^sup>n\<close> of the
  selected point, by the triangle inequality through the chosen centre.\<close>

lemma usc_sel_code_set_small:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
  shows "usc_sel_set M d z (usc_sel_code M d z g (Suc n))
      \<subseteq> mcball (usc_sel M d z g) ((1/2)^n)"
proof -
  define jn where "jn = (LEAST j. usc_sel_good M d z g (usc_sel_code M d z g n) j)"
  have code: "usc_sel_code M d z g (Suc n) = jn # usc_sel_code M d z g n"
    unfolding jn_def by simp
  have zjn: "z jn \<in> M" by (rule z)
  have half: "d (z jn) w \<le> (1/2)^(Suc n)"
    if "w \<in> usc_sel_set M d z (usc_sel_code M d z g (Suc n))" for w
    using that unfolding code by simp
  have sel: "usc_sel M d z g \<in> usc_sel_set M d z (usc_sel_code M d z g (Suc n))"
    by (rule usc_sel_in_code_set[OF cpt z dns ne])
  have sM: "usc_sel M d z g \<in> M" by (rule usc_sel_in_M[OF cpt z dns ne])
  show ?thesis
  proof
    fix y assume y: "y \<in> usc_sel_set M d z (usc_sel_code M d z g (Suc n))"
    have yM: "y \<in> M"
      using usc_sel_set_subset[of M d z "usc_sel_code M d z g (Suc n)"] y by blast
    have "d (usc_sel M d z g) y \<le> d (usc_sel M d z g) (z jn) + d (z jn) y"
      by (rule triangle[OF sM zjn yM])
    also have "\<dots> \<le> (1/2)^(Suc n) + (1/2)^(Suc n)"
      using half[OF sel] half[OF y] by (simp add: commute)
    also have "\<dots> = (1/2::real)^n" by simp
    finally show "y \<in> mcball (usc_sel M d z g) ((1/2)^n)"
      using sM yM by simp
  qed
qed

lemma usc_sel_code_set_in_open:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
    and U: "openin mtopology U" and mem: "usc_sel M d z g \<in> U"
  shows "\<exists>n. usc_sel_set M d z (usc_sel_code M d z g n) \<subseteq> U"
proof -
  from U mem obtain r where r: "0 < r" "mball (usc_sel M d z g) r \<subseteq> U"
    unfolding openin_mtopology by blast
  have "(\<lambda>n. (1/2::real)^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) auto
  then have "\<forall>\<^sub>F n in sequentially. (1/2::real)^n < r"
    using r(1) by (rule order_tendstoD(2))
  then obtain n :: nat where n: "(1/2::real)^n < r"
    by (auto simp: eventually_sequentially)
  have "usc_sel_set M d z (usc_sel_code M d z g (Suc n))
      \<subseteq> mcball (usc_sel M d z g) ((1/2)^n)"
    by (rule usc_sel_code_set_small[OF cpt z dns ne])
  also have "\<dots> \<subseteq> mball (usc_sel M d z g) r" using n by auto
  also have "\<dots> \<subseteq> U" by (rule r(2))
  finally show ?thesis by blast
qed

text \<open>Upper semicontinuity turns the shrinking into optimality.\<close>

lemma usc_sel_optimal:
  assumes cpt: "compact_space mtopology" and z: "\<And>j. z j \<in> M"
    and dns: "\<And>y e. y \<in> M \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>j. d (z j) y < e"
    and ne: "M \<noteq> {}"
    and usc: "\<And>c. openin mtopology {y \<in> M. g y < c}"
  shows "g (usc_sel M d z g) = Sup (g ` M)"
proof (rule antisym)
  show "g (usc_sel M d z g) \<le> Sup (g ` M)"
    using usc_sel_in_M[OF cpt z dns ne] by (auto intro: Sup_upper)
  show "Sup (g ` M) \<le> g (usc_sel M d z g)"
  proof (rule ccontr)
    assume "\<not> Sup (g ` M) \<le> g (usc_sel M d z g)"
    then have lt: "g (usc_sel M d z g) < Sup (g ` M)" by simp
    then obtain c where c1: "g (usc_sel M d z g) < c" and c2: "c < Sup (g ` M)"
      using ennreal_strict_between by blast
    have Uopen: "openin mtopology {y \<in> M. g y < c}" by (rule usc)
    have Umem: "usc_sel M d z g \<in> {y \<in> M. g y < c}"
      using usc_sel_in_M[OF cpt z dns ne] c1 by simp
    from usc_sel_code_set_in_open[OF cpt z dns ne Uopen Umem]
    obtain n where n: "usc_sel_set M d z (usc_sel_code M d z g n)
        \<subseteq> {y \<in> M. g y < c}" by blast
    have "Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n)) \<le> c"
    proof (rule Sup_least)
      fix v assume "v \<in> g ` usc_sel_set M d z (usc_sel_code M d z g n)"
      then obtain y where y: "y \<in> usc_sel_set M d z (usc_sel_code M d z g n)"
          "v = g y" by blast
      then have "g y < c" using n by blast
      then show "v \<le> c" using y by simp
    qed
    moreover have "Sup (g ` usc_sel_set M d z (usc_sel_code M d z g n))
        = Sup (g ` M)"
      by (rule usc_sel_code_set_sup[OF cpt z dns ne])
    ultimately show False using c2 by simp
  qed
qed

text \<open>A characterisation of @{term Least} on @{typ nat} that turns the
  greedy choice into a Boolean combination of countably many conditions.\<close>

lemma Least_nat_eq_iff:
  fixes Q :: "nat \<Rightarrow> bool"
  assumes ex: "\<exists>i. Q i"
  shows "((LEAST i. Q i) = j) \<longleftrightarrow> (Q j \<and> (\<forall>i<j. \<not> Q i))"
proof
  assume L: "(LEAST i. Q i) = j"
  have "Q (LEAST i. Q i)" using ex by (rule LeastI_ex)
  with L have Qj: "Q j" by simp
  have "\<not> Q i" if ij: "i < j" for i
  proof
    assume "Q i"
    then have "(LEAST i. Q i) \<le> i" by (rule Least_le)
    with L ij show False by simp
  qed
  with Qj show "Q j \<and> (\<forall>i<j. \<not> Q i)" by blast
next
  assume R: "Q j \<and> (\<forall>i<j. \<not> Q i)"
  show "(LEAST i. Q i) = j"
  proof (rule Least_equality)
    show "Q j" using R by blast
    show "j \<le> i" if "Q i" for i
    proof (rule ccontr)
      assume "\<not> j \<le> i"
      then have "i < j" by simp
      with R have "\<not> Q i" by blast
      with that show False by blast
    qed
  qed
qed

text \<open>The measurable selection theorem.  The payoff is upper semicontinuous
  in the second argument for every parameter, and its supremum over every
  closed set is measurable in the parameter --- the latter is what joint
  upper semicontinuity supplies in the intended application.\<close>

theorem usc_measurable_selection:
  fixes P :: "'b measure" and f :: "'b \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes cpt: "compact_space mtopology" and ne: "M \<noteq> {}"
    and usc: "\<And>x c. x \<in> space P \<Longrightarrow> openin mtopology {y \<in> M. f x y < c}"
    and meas: "\<And>C. closedin mtopology C
        \<Longrightarrow> (\<lambda>x. Sup (f x ` C)) \<in> borel_measurable P"
  obtains s where "s \<in> P \<rightarrow>\<^sub>M borel_of mtopology" and "\<And>x. s x \<in> M"
    and "\<And>x. x \<in> space P \<Longrightarrow> f x (s x) = Sup (f x ` M)"
proof -
  obtain z :: "nat \<Rightarrow> 'a" where z0: "\<forall>j. z j \<in> M"
    and dns0: "\<forall>y \<in> M. \<forall>e > 0. \<exists>j. d (z j) y < e"
    using compact_space_dense_seq[OF cpt ne] by blast
  have z: "z j \<in> M" for j using z0 by blast
  have dns: "\<exists>j. d (z j) y < e" if "y \<in> M" and "0 < e" for y e
    using dns0 that by blast
  define s where "s = (\<lambda>x. usc_sel M d z (f x))"
  have sM: "s x \<in> M" for x
    unfolding s_def by (rule usc_sel_in_M[OF cpt z dns ne])
  have sopt: "f x (s x) = Sup (f x ` M)" if x: "x \<in> space P" for x
    unfolding s_def by (rule usc_sel_optimal[OF cpt z dns ne usc[OF x]])
  define A where "A = (\<lambda>n js. {x \<in> space P. usc_sel_code M d z (f x) n = js})"
  have Gmeas: "{x \<in> space P. usc_sel_good M d z (f x) js i} \<in> sets P" for js i
  proof (cases "usc_sel_set M d z (i # js) = {}")
    case True
    have empty: "{x \<in> space P. usc_sel_good M d z (f x) js i} = {}"
      using True unfolding usc_sel_good_def by auto
    show ?thesis unfolding empty by simp
  next
    case False
    have eq: "{x \<in> space P. usc_sel_good M d z (f x) js i}
        = {x \<in> space P. Sup (f x ` usc_sel_set M d z (i # js))
             = Sup (f x ` usc_sel_set M d z js)}"
      using False unfolding usc_sel_good_def by auto
    have m1: "(\<lambda>x. Sup (f x ` usc_sel_set M d z (i # js))) \<in> borel_measurable P"
      by (rule meas[OF usc_sel_set_closedin[OF z]])
    have m2: "(\<lambda>x. Sup (f x ` usc_sel_set M d z js)) \<in> borel_measurable P"
      by (rule meas[OF usc_sel_set_closedin[OF z]])
    show ?thesis unfolding eq by (rule borel_measurable_eq[OF m1 m2])
  qed
  have Ameas: "A n js \<in> sets P" for n js
  proof (induct n arbitrary: js)
    case 0
    have "A 0 js = (if js = [] then space P else {})"
      unfolding A_def by auto
    then show ?case by simp
  next
    case (Suc n)
    show ?case
    proof (cases js)
      case Nil
      have "A (Suc n) [] = {}" unfolding A_def by auto
      with Nil show ?thesis by simp
    next
      case (Cons j js')
      have split: "A (Suc n) (j # js')
          = A n js'
            \<inter> {x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}"
      proof (intro set_eqI iffI)
        fix x assume "x \<in> A (Suc n) (j # js')"
        then have xP: "x \<in> space P"
          and e: "usc_sel_code M d z (f x) (Suc n) = j # js'"
          unfolding A_def by auto
        from e have c1: "usc_sel_code M d z (f x) n = js'" by simp
        from e have "(LEAST i. usc_sel_good M d z (f x) js' i) # js' = j # js'"
          by (simp only: usc_sel_code_Suc c1)
        then have c2: "(LEAST i. usc_sel_good M d z (f x) js' i) = j" by simp
        show "x \<in> A n js'
            \<inter> {x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}"
          using xP c1 c2 unfolding A_def by simp
      next
        fix x assume "x \<in> A n js'
            \<inter> {x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}"
        then have xP: "x \<in> space P" and c1: "usc_sel_code M d z (f x) n = js'"
          and c2: "(LEAST i. usc_sel_good M d z (f x) js' i) = j"
          unfolding A_def by auto
        have "usc_sel_code M d z (f x) (Suc n) = j # js'"
        proof -
          have "usc_sel_code M d z (f x) (Suc n)
              = (LEAST i. usc_sel_good M d z (f x)
                  (usc_sel_code M d z (f x) n) i) # usc_sel_code M d z (f x) n"
            by simp
          also have "\<dots> = (LEAST i. usc_sel_good M d z (f x) js' i) # js'"
            unfolding c1 by (rule refl)
          also have "\<dots> = j # js'" unfolding c2 by (rule refl)
          finally show ?thesis .
        qed
        with xP show "x \<in> A (Suc n) (j # js')"
          unfolding A_def by (simp del: usc_sel_code_Suc)
      qed
      show ?thesis
      proof (cases "usc_sel_set M d z js' = {}")
        case True
        have "A n js' = {}"
        proof -
          have "usc_sel_set M d z (usc_sel_code M d z (f x) n) \<noteq> {}" for x
            by (rule usc_sel_code_set_ne[OF cpt z dns ne])
          with True show ?thesis unfolding A_def by auto
        qed
        with split Cons show ?thesis by simp
      next
        case False
        have exg: "\<exists>i. usc_sel_good M d z (f x) js' i" for x
          by (rule usc_sel_good_ex[OF cpt z dns False])
        have leasteq: "((LEAST i. usc_sel_good M d z (f x) js' i) = j)
            \<longleftrightarrow> (usc_sel_good M d z (f x) js' j
                \<and> (\<forall>i<j. \<not> usc_sel_good M d z (f x) js' i))" for x
          by (rule Least_nat_eq_iff) (rule exg)
        have setD: "{x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}
            = {x \<in> space P. usc_sel_good M d z (f x) js' j}
              - (\<Union>i\<in>{..<j}. {x \<in> space P. usc_sel_good M d z (f x) js' i})"
          using leasteq by auto
        have "(\<Union>i\<in>{..<j}. {x \<in> space P. usc_sel_good M d z (f x) js' i}) \<in> sets P"
          using Gmeas by (intro sets.finite_UN) auto
        then have "{x \<in> space P. (LEAST i. usc_sel_good M d z (f x) js' i) = j}
            \<in> sets P"
          unfolding setD by (rule sets.Diff[OF Gmeas])
        with Suc[of js'] split Cons show ?thesis by simp
      qed
    qed
  qed
  have preim: "s -` U \<inter> space P
      = (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
    if U: "openin mtopology U" for U
  proof (intro set_eqI iffI)
    fix x assume "x \<in> s -` U \<inter> space P"
    then have xP: "x \<in> space P" and xU: "usc_sel M d z (f x) \<in> U"
      unfolding s_def by auto
    from usc_sel_code_set_in_open[OF cpt z dns ne U xU]
    obtain n where n: "usc_sel_set M d z (usc_sel_code M d z (f x) n) \<subseteq> U"
      by blast
    have "x \<in> A (length (usc_sel_code M d z (f x) n))
        (usc_sel_code M d z (f x) n)"
      using xP unfolding A_def by simp
    with n show "x \<in> (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
      by blast
  next
    fix x assume "x \<in> (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
    then obtain js where js: "usc_sel_set M d z js \<subseteq> U" "x \<in> A (length js) js"
      by blast
    from js(2) have xP: "x \<in> space P"
      and c: "usc_sel_code M d z (f x) (length js) = js"
      unfolding A_def by auto
    have inset: "usc_sel M d z (f x)
        \<in> usc_sel_set M d z (usc_sel_code M d z (f x) (length js))"
      by (rule usc_sel_in_code_set[OF cpt z dns ne])
    from inset c have "usc_sel M d z (f x) \<in> usc_sel_set M d z js" by simp
    with js(1) have "s x \<in> U" unfolding s_def by blast
    with xP show "x \<in> s -` U \<inter> space P" by simp
  qed
  have smeas: "s \<in> P \<rightarrow>\<^sub>M borel_of mtopology"
  proof (rule measurable_sigma_sets)
    show "sets (borel_of mtopology)
        = sigma_sets (topspace mtopology) {U. openin mtopology U}"
      by (rule sets_borel_of)
    have "U \<subseteq> topspace mtopology" if "openin mtopology U" for U
      by (rule openin_subset[OF that])
    then show "{U. openin mtopology U} \<subseteq> Pow (topspace mtopology)" by auto
    show "s \<in> space P \<rightarrow> topspace mtopology" using sM by auto
    show "s -` U \<inter> space P \<in> sets P" if "U \<in> {U. openin mtopology U}" for U
    proof -
      have cnt: "countable {js :: nat list. usc_sel_set M d z js \<subseteq> U}"
        by (rule countableI_type)
      have "s -` U \<inter> space P
          = (\<Union>js \<in> {js. usc_sel_set M d z js \<subseteq> U}. A (length js) js)"
        using that by (intro preim) simp
      also have "\<dots> \<in> sets P"
        by (rule sets.countable_UN''[OF cnt]) (rule Ameas)
      finally show ?thesis .
    qed
  qed
  show ?thesis by (rule that[OF smeas sM sopt])
qed

end

section \<open>The paper's class is a compact metric space of measures\<close>

text \<open>Step (i) of applying the selection theorem.  The AFP entry
  \<open>Levy_Prokhorov_Metric\<close> --- already a session dependency --- makes the
  space of finite Borel measures on a separable metric space a metric
  space for the L\'evy--Prokhorov distance, whose topology IS
  \<open>weak_conv_topology\<close>, the topology our \<open>weak_conv_on\<close> is a \<open>limitin\<close> of.
  Prokhorov's theorem turns tightness (NC-2) into relative compactness,
  and weak closedness (NC-3) collapses the closure.  The result is that
  the paper's class is a COMPACT subset of a metric space --- exactly the
  input @{thm [source] Metric_space.usc_measurable_selection} wants.\<close>

theorem paper_pair_class_compactin_weak:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (paper_pair_class k L T x)"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?C = "paper_pair_class k L T x"
  interpret LP: Levy_Prokhorov "mspace (path_metric T :: ('n pairpath) metric)"
      "mdist (path_metric T :: ('n pairpath) metric)"
    by (simp add: Levy_Prokhorov_def)
  have Xeq: "LP.mtopology = ?X" by (simp add: mtopology_of_def)
  have sep: "separable_space ?X" by (rule separable_path_metric)
  have met: "metrizable_space ?X"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  have sepLP: "separable_space LP.mtopology" using sep Xeq by simp
  have LPtop: "LP.LPm.mtopology = ?W"
    using LP.LPmtopology_eq_weak_conv_topology[OF sepLP] Xeq by simp
  have bound: "?C \<subseteq> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> ?C"
    have "prob_space N" by (rule paper_pair_class_prob[OF N])
    then have "N (space N) \<le> ennreal 1" by (simp add: prob_space.emeasure_space_1)
    moreover have "sets N = sets (borel_of ?X)" by (rule paper_pair_class_sets[OF N])
    ultimately show "N \<in> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
      by simp
  qed
  have topC: "?C \<subseteq> topspace ?W"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> ?C"
    have p: "prob_space N" by (rule paper_pair_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with paper_pair_class_sets[OF N] show "N \<in> topspace ?W" by simp
  qed
  have tight: "tight_on_set ?X ?C"
    by (rule tight_on_set_paper_pair_class[OF T L]) simp
  have rc: "compactin ?W (?W closure_of ?C)"
    by (rule tight_imp_relatively_compact[OF met sep bound tight])
  have cl: "?W closure_of ?C \<subseteq> ?C"
  proof
    fix Q :: "('n pairpath) measure"
    assume Qc: "Q \<in> ?W closure_of ?C"
    then have QL: "Q \<in> LP.LPm.mtopology closure_of ?C" using LPtop by simp
    then obtain sq :: "nat \<Rightarrow> ('n pairpath) measure"
      where sq: "range sq \<subseteq> ?C \<inter> LP.\<P>"
        and lim: "limitin LP.LPm.mtopology sq Q sequentially"
      by (auto simp: LP.LPm.closure_of_sequentially)
    have QP: "Q \<in> LP.\<P>" using QL by (auto simp: LP.LPm.closure_of_sequentially)
    have mem: "sq i \<in> ?C" for i using sq by blast
    have wc: "weak_conv_on sq Q sequentially ?X" using lim LPtop by simp
    have prob: "prob_space Q"
      by (rule weak_conv_on_prob_space[OF wc]) (rule paper_pair_class_prob[OF mem])
    have setsQ: "sets Q = sets (borel_of ?X)"
      using QP Xeq by (simp add: LP.inP_iff)
    show "Q \<in> ?C" by (rule paper_pair_class_weak_closed[OF T L mem wc prob setsQ])
  qed
  have sub: "?C \<subseteq> ?W closure_of ?C" by (rule closure_of_subset[OF topC])
  from cl sub have "?W closure_of ?C = ?C" by blast
  with rc show ?thesis by simp
qed

section \<open>Joint continuity of the shift\<close>

text \<open>Step (ii) of applying the selection theorem.  After @{thm [source]
  paper_pair_class_shift_image} the functional whose supremum is
  @{term paper_v} is a function of the STARTING POINT and of a member of
  the FIXED class at the origin.  The selection theorem's measurability
  hypothesis --- that the supremum over each closed set be measurable in
  the parameter --- comes from JOINT upper semicontinuity, and that in
  turn from joint continuity of the shift.

  The estimate is uniform: shifting a path by a constant vector moves it
  by exactly that vector in the sup metric, so a UNIFORMLY continuous
  test function is displaced uniformly over the whole path space.  Weak
  convergence may be tested against bounded uniformly continuous
  functions (@{thm [source] mweak_conv_fin.mweak_conv_eq1}), so no
  tightness is needed here.\<close>

lemma mdist_pshift_pshift:
  fixes z y :: "real^'n::finite"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "mdist (path_metric T :: ('n pairpath) metric)
      (pshift T z \<omega>) (pshift T y \<omega>) \<le> dist z y"
proof -
  have sz: "pshift T z \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pshift_in_mspace[OF w])
  have sy: "pshift T y \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pshift_in_mspace[OF w])
  have pw: "dist (pshift T z \<omega> t) (pshift T y \<omega> t) \<le> dist z y" if t: "t \<in> {0..T}" for t
  proof -
    have "dist (pshift T z \<omega> t) (pshift T y \<omega> t)
        = dist (z + fst (\<omega> t), snd (\<omega> t)) (y + fst (\<omega> t), snd (\<omega> t))"
      using t by (simp add: pshift_apply)
    also have "\<dots> = dist (z + fst (\<omega> t)) (y + fst (\<omega> t))"
      by (simp add: dist_Pair_Pair)
    also have "\<dots> = dist z y" by (simp add: dist_norm)
    finally show ?thesis by simp
  qed
  show ?thesis using path_mdist_le_iff_all[OF T sz sy] pw by blast
qed

lemma pshift_law_weak_conv_joint:
  fixes ym :: "nat \<Rightarrow> real^'n::finite" and Rm :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes T: "0 \<le> T"
    and yc: "ym \<longlonglongrightarrow> y"
    and prR: "\<And>m. prob_space (Rm m)"
    and setsR: "\<And>m. sets (Rm m) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and prR': "prob_space R"
    and setsR': "sets R = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and wc: "weak_conv_on Rm R sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
  shows "weak_conv_on (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?S = "mspace (path_metric T :: ('n pairpath) metric)"
  have prS: "prob_space (pshift_law T z (Rm m))" for z m
    by (rule prob_space_pshift_law[OF T prR setsR])
  have fmS: "finite_measure (pshift_law T z (Rm m))" for z m
    using prS[of z m] by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmS': "finite_measure (pshift_law T y R)"
    using prob_space_pshift_law[OF T prR' setsR']
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have MWfin: "mweak_conv_fin ?S (mdist (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R) sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using fmS fmS' by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin ?S "mdist (path_metric T :: ('n pairpath) metric)"
      "\<lambda>m. pshift_law T (ym m) (Rm m)" "pshift_law T y R" sequentially
    by (rule MWfin)
  show ?thesis
    unfolding mtopology_of_def
  proof (rule MW.mweak_conv_eq1[THEN iffD2], intro allI impI)
    fix f :: "'n pairpath \<Rightarrow> real"
    assume uc: "uniformly_continuous_map MW.Self euclidean_metric f"
    assume bnd: "\<exists>B. \<forall>x \<in> ?S. \<bar>f x\<bar> \<le> B"
    from bnd obtain B where B: "\<And>x. x \<in> ?S \<Longrightarrow> \<bar>f x\<bar> \<le> B" by blast
    have cf: "continuous_map ?X euclideanreal f"
      using uniformly_continuous_imp_continuous_map[OF uc]
      by (simp add: mtopology_of_def)
    have fm: "f \<in> borel_measurable ?B"
      using continuous_map_measurable[OF cf] by (simp add: borel_of_euclidean)
    have shiftm: "pshift T z \<in> Rm m \<rightarrow>\<^sub>M ?B" for z m
      using pshift_measurable[OF T] measurable_cong_sets[OF setsR refl] by blast
    have spRm: "space (Rm m) = ?S" for m by (rule space_of_path_sets[OF setsR])
    have hmeas: "(\<lambda>\<omega>. f (pshift T z \<omega>)) \<in> borel_measurable (Rm m)" for z m
      using fm shiftm by simp
    have hbnd: "\<bar>f (pshift T z \<omega>)\<bar> \<le> B" if "\<omega> \<in> space (Rm m)" for z m \<omega>
    proof -
      have "\<omega> \<in> ?S" using that spRm by simp
      then have "pshift T z \<omega> \<in> ?S" by (rule pshift_in_mspace)
      then show ?thesis by (rule B)
    qed
    have intg: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T z \<omega>))" for z m
    proof -
      interpret PR: prob_space "Rm m" by (rule prR)
      have ae: "AE \<omega> in Rm m. norm (f (pshift T z \<omega>)) \<le> \<bar>B\<bar>"
      proof (intro AE_I2)
        fix \<omega> assume "\<omega> \<in> space (Rm m)"
        then have "\<bar>f (pshift T z \<omega>)\<bar> \<le> B" by (rule hbnd)
        then show "norm (f (pshift T z \<omega>)) \<le> \<bar>B\<bar>" by simp
      qed
      from PR.integrable_const_bound[OF ae hmeas] show ?thesis .
    qed
    have distr_int: "(\<integral>\<omega>. f \<omega> \<partial>(pshift_law T z S)) = (\<integral>\<omega>. f (pshift T z \<omega>) \<partial>S)"
      if "sets S = sets ?B" for z and S :: "('n pairpath) measure"
    proof -
      have m: "pshift T z \<in> S \<rightarrow>\<^sub>M ?B"
        using pshift_measurable[OF T] measurable_cong_sets[OF that refl] by blast
      show ?thesis unfolding pshift_law_def by (rule integral_distr[OF m fm])
    qed
    have lim2: "(\<lambda>m. \<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) \<longlonglongrightarrow> (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)"
    proof -
      have cshift: "continuous_map ?X ?X (pshift T y)"
        by (rule Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pshift[OF T]])
      have cg: "continuous_map ?X euclideanreal (\<lambda>\<omega>. f (pshift T y \<omega>))"
        using continuous_map_compose[OF cshift cf] by (simp add: comp_def)
      have bg: "\<exists>B'. \<forall>x \<in> topspace ?X. \<bar>f (pshift T y x)\<bar> \<le> B'"
      proof (intro exI[of _ B] ballI)
        fix x assume "x \<in> topspace ?X"
        then have "x \<in> ?S" by simp
        then show "\<bar>f (pshift T y x)\<bar> \<le> B" using B pshift_in_mspace by blast
      qed
      show ?thesis using wc[unfolded weak_conv_on_def] cg bg by blast
    qed
    have lim1: "(\<lambda>m. (\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))) \<longlonglongrightarrow> 0"
    proof (rule LIMSEQ_I)
      fix e :: real assume e: "0 < e"
      then have e2: "0 < e/2" by simp
      have ucd: "\<forall>ep>0. \<exists>dl>0. \<forall>u\<in>?S. \<forall>v\<in>?S.
          mdist (path_metric T :: ('n pairpath) metric) v u < dl \<longrightarrow> \<bar>f v - f u\<bar> < ep"
        using uc unfolding uniformly_continuous_map_def by (simp add: dist_real_def)
      from ucd e2 obtain del where d0: "0 < del"
        and dd0: "\<forall>u\<in>?S. \<forall>v\<in>?S.
            mdist (path_metric T :: ('n pairpath) metric) v u < del
              \<longrightarrow> \<bar>f v - f u\<bar> < e/2"
        by blast
      have dd: "\<bar>f v - f u\<bar> < e/2" if "u \<in> ?S" and "v \<in> ?S"
        and "mdist (path_metric T :: ('n pairpath) metric) v u < del" for u v
        using dd0 that by blast
      from LIMSEQ_D[OF yc d0] obtain M0
        where M0: "\<And>m. M0 \<le> m \<Longrightarrow> norm (ym m - y) < del" by blast
      have main: "norm ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
          - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) - 0) < e" if mM: "M0 \<le> m" for m
      proof -
        interpret PRm: prob_space "Rm m" by (rule prR)
        have cint: "(\<integral>\<omega>. (c::real) \<partial>(Rm m)) = c" for c
          by (simp add: PRm.prob_space)
        have i1: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T (ym m) \<omega>))" by (rule intg)
        have i2: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T y \<omega>))" by (rule intg)
        have idiff: "integrable (Rm m)
            (\<lambda>\<omega>. f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>))"
          using i1 i2 by (rule Bochner_Integration.integrable_diff)
        have icu: "integrable (Rm m) (\<lambda>\<omega>. e/2 :: real)" by (rule PRm.integrable_const)
        have icl: "integrable (Rm m) (\<lambda>\<omega>. - (e/2) :: real)"
          by (rule PRm.integrable_const)
        have key: "\<bar>f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)\<bar> \<le> e/2"
          if w: "\<omega> \<in> space (Rm m)" for \<omega>
        proof -
          have wm: "\<omega> \<in> ?S" using w spRm by simp
          have m1: "pshift T (ym m) \<omega> \<in> ?S" by (rule pshift_in_mspace[OF wm])
          have m2: "pshift T y \<omega> \<in> ?S" by (rule pshift_in_mspace[OF wm])
          have "mdist (path_metric T :: ('n pairpath) metric)
              (pshift T (ym m) \<omega>) (pshift T y \<omega>) \<le> dist (ym m) y"
            by (rule mdist_pshift_pshift[OF T wm])
          also have "\<dots> < del" using M0[OF mM] by (simp add: dist_norm)
          finally have "mdist (path_metric T :: ('n pairpath) metric)
              (pshift T (ym m) \<omega>) (pshift T y \<omega>) < del" .
          from dd[OF m2 m1 this] show ?thesis by simp
        qed
        have ptu: "f (pshift T (ym m) x) - f (pshift T y x) \<le> e/2"
          if "x \<in> space (Rm m)" for x using key[OF that] by linarith
        have ptl: "- (e/2) \<le> f (pshift T (ym m) x) - f (pshift T y x)"
          if "x \<in> space (Rm m)" for x using key[OF that] by linarith
        have eq: "(\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
            - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))
            = (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
          by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
        have up: "(\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m)) \<le> e/2"
        proof -
          have "(\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))
              \<le> (\<integral>\<omega>. e/2 \<partial>(Rm m))"
            by (rule integral_mono[OF idiff icu ptu])
          also have "\<dots> = e/2" by (rule cint)
          finally show ?thesis .
        qed
        have lo: "- (e/2) \<le> (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
        proof -
          have "- (e/2) = (\<integral>\<omega>. - (e/2) \<partial>(Rm m))" by (rule cint[symmetric])
          also have "\<dots> \<le> (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
            by (rule integral_mono[OF icl idiff ptl])
          finally show ?thesis .
        qed
        from up lo have "\<bar>(\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
            - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))\<bar> \<le> e/2"
          unfolding eq by simp
        then show ?thesis using e by simp
      qed
      then show "\<exists>no. \<forall>m\<ge>no. norm ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
          - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) - 0) < e" by blast
    qed
    have "(\<lambda>m. ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)))
        + (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)))
        \<longlonglongrightarrow> 0 + (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)"
      by (rule tendsto_add[OF lim1 lim2])
    then have "(\<lambda>m. \<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        \<longlonglongrightarrow> (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)" by simp
    then show "(\<lambda>m. \<integral>\<omega>. f \<omega> \<partial>(pshift_law T (ym m) (Rm m)))
        \<longlonglongrightarrow> (\<integral>\<omega>. f \<omega> \<partial>(pshift_law T y R))"
      by (simp add: distr_int[OF setsR] distr_int[OF setsR'])
  qed
qed

text \<open>Joint upper semicontinuity of the payoff, in sequential form.  The
  parameter and the law move TOGETHER; joint continuity of the shift
  carries the pair to a weakly convergent sequence of laws, and
  @{thm [source] ess_inf_pexit_usc} --- which lives on the VECTOR path
  space --- is reached through @{thm [source] Lipschitz_pfst} exactly as
  in @{thm [source] paper_v_attained}.\<close>

lemma ess_inf_pexit_pshift_usc:
  fixes ym :: "nat \<Rightarrow> real^'n::finite" and Rm :: "nat \<Rightarrow> ('n pairpath) measure"
    and K :: "(real^'n) set"
  assumes T: "0 < T" and K: "closed K"
    and yc: "ym \<longlonglongrightarrow> y"
    and prR: "\<And>m. prob_space (Rm m)"
    and setsR: "\<And>m. sets (Rm m) = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and prR': "prob_space R"
    and setsR': "sets R = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and wc: "weak_conv_on Rm R sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
  shows "Limsup sequentially (\<lambda>m. ess_inf_time (pshift_law T (ym m) (Rm m))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      \<le> ess_inf_time (pshift_law T y R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  let ?Y = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'n) metric)"
  let ?p = "\<lambda>Q :: ('n pairpath) measure. distr Q (borel_of ?Y) (pfst T)"
  have T0: "0 \<le> T" using T by simp
  have wcs: "weak_conv_on (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule pshift_law_weak_conv_joint[OF T0 yc prR setsR prR' setsR' wc])
  have prS: "prob_space (pshift_law T (ym m) (Rm m))" for m
    by (rule prob_space_pshift_law[OF T0 prR setsR])
  have prS': "prob_space (pshift_law T y R)"
    by (rule prob_space_pshift_law[OF T0 prR' setsR'])
  have wcY: "weak_conv_on (\<lambda>m. ?p (pshift_law T (ym m) (Rm m)))
      (?p (pshift_law T y R)) sequentially ?Y"
    by (rule weak_conv_on_pushforward
        [OF Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pfst[OF T0]] wcs])
  have lim: "Limsup sequentially
        (\<lambda>m. ess_inf_time (?p (pshift_law T (ym m) (Rm m))) (pexit T K))
      \<le> ess_inf_time (?p (pshift_law T y R)) (pexit T K)"
  proof (rule ess_inf_pexit_usc[OF T K wcY])
    show "prob_space (?p (pshift_law T (ym m) (Rm m)))" for m
      by (rule prob_space.prob_space_distr[OF prS pfst_measurable[OF T0]]) simp
    show "prob_space (?p (pshift_law T y R))"
      by (rule prob_space.prob_space_distr[OF prS' pfst_measurable[OF T0]]) simp
  qed
  have eqS: "ess_inf_time (?p S) (pexit T K)
      = ess_inf_time S (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    if "sets S = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    for S :: "('n pairpath) measure"
    by (rule ess_inf_time_pfst[OF T0 K that])
  show ?thesis using lim by (simp add: eqS)
qed

text \<open>The class packaged exactly as @{thm [source]
  Metric_space.usc_measurable_selection} consumes it: a compact metric
  space, the metric being L\'evy--Prokhorov restricted to the class, and
  its topology the subspace topology of weak convergence.\<close>

theorem paper_pair_class_compact_metric_space:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "Metric_space (paper_pair_class k L T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))"
    and "Metric_space.mtopology (paper_pair_class k L T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))
      = subtopology (weak_conv_topology
          (mtopology_of (path_metric T :: ('n pairpath) metric)))
          (paper_pair_class k L T x)"
    and "compact_space (Metric_space.mtopology (paper_pair_class k L T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))))"
proof -
  interpret LP: Levy_Prokhorov "mspace (path_metric T :: ('n pairpath) metric)"
      "mdist (path_metric T :: ('n pairpath) metric)"
    by (simp add: Levy_Prokhorov_def)
  have Xeq: "LP.mtopology = mtopology_of (path_metric T :: ('n pairpath) metric)"
    by (simp add: mtopology_of_def)
  have sepLP: "separable_space LP.mtopology"
    using separable_path_metric Xeq by simp
  have LPtop: "LP.LPm.mtopology
      = weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
    using LP.LPmtopology_eq_weak_conv_topology[OF sepLP] Xeq by simp
  have subC: "paper_pair_class k L T x \<subseteq> LP.\<P>"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> paper_pair_class k L T x"
    have p: "prob_space N" by (rule paper_pair_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with paper_pair_class_sets[OF N] Xeq show "N \<in> LP.\<P>" by (simp add: LP.inP_iff)
  qed
  have SMloc: "Submetric LP.\<P> LP.LPm (paper_pair_class k L T x)"
    unfolding Submetric_def Submetric_axioms_def
    using LP.LPm.Metric_space_axioms subC by blast
  interpret SM: Submetric "LP.\<P>" "LP.LPm" "paper_pair_class k L T x"
    by (rule SMloc)
  show ms: "Metric_space (paper_pair_class k L T x) LP.LPm"
    by (rule SM.sub.Metric_space_axioms)
  show top: "SM.sub.mtopology
      = subtopology (weak_conv_topology
          (mtopology_of (path_metric T :: ('n pairpath) metric)))
          (paper_pair_class k L T x)"
    using SM.mtopology_submetric LPtop by simp
  show "compact_space SM.sub.mtopology"
    unfolding top
    by (rule compact_space_subtopology[OF paper_pair_class_compactin_weak[OF T L]])
qed

section \<open>A measurable optimizer: Larsson--Ruf Proposition 2.2(ii)\<close>

text \<open>The optimizer of @{thm [source] paper_v_attained} can be chosen
  MEASURABLY in the starting point.  Everything is now in place: the class
  at the origin is a compact metric space
  (@{thm [source] paper_pair_class_compact_metric_space}), the payoff is
  jointly upper semicontinuous
  (@{thm [source] ess_inf_pexit_pshift_usc}), and
  @{thm [source] Metric_space.usc_measurable_selection} does the rest.

  Only two pieces of bookkeeping stand between those and the theorem.
  First, upper semicontinuity IN THE LAW is the joint statement along a
  constant parameter sequence, and closedness in a metric topology is
  sequential closedness (@{thm [source] Metric_space.closure_of_sequentially}).
  Second, the supremum over a closed --- hence compact --- subset is upper
  semicontinuous in the parameter: pick, for each parameter and each
  \<open>b < c\<close>, a law beating \<open>b\<close>, extract a convergent subsequence by
  @{thm [source] Metric_space.compactin_sequentially}, and let the joint
  statement close the gap.  Attainment of the supremum is NOT needed for
  that, only \<open>b < c\<close> for every \<open>b\<close> below \<open>c\<close>, which is where
  @{thm [source] ennreal_strict_between} is used again.\<close>

theorem paper_v_measurable_selector:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains S where
    "S \<in> borel \<rightarrow>\<^sub>M borel_of (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and "\<And>y. S y \<in> paper_pair_class k L T 0"
    and "\<And>y. pshift_law T y (S y) \<in> paper_pair_class k L T y"
    and "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = paper_v k L T K y"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?C = "paper_pair_class k L T (0 :: real^'n)"
  let ?g = "\<lambda>(y :: real^'n) (R :: ('n pairpath) measure).
      ess_inf_time (pshift_law T y R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L by simp
  interpret MC: Metric_space "paper_pair_class k L T (0 :: real^'n)"
      "Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))"
    by (rule paper_pair_class_compact_metric_space(1)[OF T L0])
  have Ctop: "MC.mtopology = subtopology ?W ?C"
    by (rule paper_pair_class_compact_metric_space(2)[OF T L0])
  have Ccpt: "compact_space MC.mtopology"
    by (rule paper_pair_class_compact_metric_space(3)[OF T L0])
  have Cne: "?C \<noteq> {}" by (rule paper_pair_class_nonempty[OF T0 L])
  have prC: "prob_space R" if "R \<in> ?C" for R by (rule paper_pair_class_prob[OF that])
  have stC: "sets R = sets ?B" if "R \<in> ?C" for R
    by (rule paper_pair_class_sets[OF that])
  have convC: "weak_conv_on sq Rl sequentially ?X"
    if "limitin MC.mtopology sq Rl sequentially" for sq Rl
    using that unfolding Ctop by (simp add: limitin_subtopology)
  have limC: "Rl \<in> ?C" if "limitin MC.mtopology sq Rl sequentially" for sq Rl
    using that unfolding Ctop by (simp add: limitin_subtopology)
  \<comment> \<open>the first hypothesis: upper semicontinuity in the law\<close>
  have hypA: "openin MC.mtopology {R \<in> ?C. ?g y R < c}" for y c
  proof -
    let ?A = "{R \<in> ?C. c \<le> ?g y R}"
    have Asub: "?A \<subseteq> ?C" by blast
    have Acl: "MC.mtopology closure_of ?A \<subseteq> ?A"
    proof
      fix Rl assume "Rl \<in> MC.mtopology closure_of ?A"
      then obtain sq where sq: "range sq \<subseteq> ?A \<inter> ?C"
        and lim: "limitin MC.mtopology sq Rl sequentially"
        by (auto simp: MC.closure_of_sequentially)
      have memC: "sq m \<in> ?C" for m using sq by blast
      have memA: "c \<le> ?g y (sq m)" for m using sq by blast
      have RlC: "Rl \<in> ?C" by (rule limC[OF lim])
      have wc: "weak_conv_on sq Rl sequentially ?X" by (rule convC[OF lim])
      have "Limsup sequentially (\<lambda>m. ?g y (sq m)) \<le> ?g y Rl"
        by (rule ess_inf_pexit_pshift_usc
            [OF T K tendsto_const prC[OF memC] stC[OF memC]
                prC[OF RlC] stC[OF RlC] wc])
      moreover have "c \<le> Liminf sequentially (\<lambda>m. ?g y (sq m))"
        using memA by (intro Liminf_bounded always_eventually) blast
      moreover have "Liminf sequentially (\<lambda>m. ?g y (sq m))
          \<le> Limsup sequentially (\<lambda>m. ?g y (sq m))"
        by (rule Liminf_le_Limsup) simp
      ultimately have "c \<le> ?g y Rl" by simp
      with RlC show "Rl \<in> ?A" by blast
    qed
    have Asub': "?A \<subseteq> topspace MC.mtopology" using Asub by simp
    have "MC.mtopology closure_of ?A = ?A"
      using Acl closure_of_subset[OF Asub'] by blast
    then have "closedin MC.mtopology ?A" by (simp add: closure_of_eq)
    then have "openin MC.mtopology (topspace MC.mtopology - ?A)"
      by (rule openin_diff[OF openin_topspace])
    moreover have "topspace MC.mtopology - ?A = {R \<in> ?C. ?g y R < c}"
      by (auto simp: not_le)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>the second hypothesis: the supremum over a compact set is measurable\<close>
  have hypB: "(\<lambda>y. Sup (?g y ` Cs)) \<in> borel_measurable (borel :: (real^'n) measure)"
    if Cl: "closedin MC.mtopology Cs" for Cs
  proof (rule borel_measurableI_ge)
    fix c :: ennreal
    have CsC: "Cs \<subseteq> ?C" using Cl by (metis closedin_subset MC.topspace_mtopology)
    have Cscpt: "compactin MC.mtopology Cs"
      by (rule closedin_compact_space[OF Ccpt Cl])
    have "closed {y :: real^'n. c \<le> Sup (?g y ` Cs)}"
    proof (subst closed_sequential_limits, intro allI impI)
      fix ym :: "nat \<Rightarrow> real^'n" and y :: "real^'n"
      assume h: "(\<forall>m. ym m \<in> {y. c \<le> Sup (?g y ` Cs)}) \<and> ym \<longlonglongrightarrow> y"
      then have cs: "c \<le> Sup (?g (ym m) ` Cs)" for m by blast
      have yc: "ym \<longlonglongrightarrow> y" using h by blast
      have below: "b \<le> Sup (?g y ` Cs)" if b: "b < c" for b
      proof -
        have "\<exists>R. R \<in> Cs \<and> b < ?g (ym m) R" for m
        proof -
          have "b < Sup (?g (ym m) ` Cs)" using b cs[of m] by simp
          then show ?thesis by (auto simp: less_Sup_iff)
        qed
        then obtain Rm where Rm: "\<And>m. Rm m \<in> Cs"
          and bR: "\<And>m. b < ?g (ym m) (Rm m)" by metis
        from Cscpt Rm obtain Rl a where Rl: "Rl \<in> Cs" and sm: "strict_mono a"
          and lim: "limitin MC.mtopology (Rm \<circ> a) Rl sequentially"
          unfolding MC.compactin_sequentially by (metis image_subsetI)
        have RlC: "Rl \<in> ?C" using Rl CsC by blast
        have RmC: "(Rm \<circ> a) m \<in> ?C" for m using Rm CsC by auto
        have wc: "weak_conv_on (Rm \<circ> a) Rl sequentially ?X" by (rule convC[OF lim])
        have yca: "(\<lambda>m. ym (a m)) \<longlonglongrightarrow> y"
          using LIMSEQ_subseq_LIMSEQ[OF yc sm] by (simp add: o_def)
        have "Limsup sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m)) \<le> ?g y Rl"
          by (rule ess_inf_pexit_pshift_usc
              [OF T K yca prC[OF RmC] stC[OF RmC] prC[OF RlC] stC[OF RlC] wc])
        moreover have "b \<le> Liminf sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m))"
          using bR by (intro Liminf_bounded always_eventually) (auto simp: less_imp_le)
        moreover have "Liminf sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m))
            \<le> Limsup sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m))"
          by (rule Liminf_le_Limsup) simp
        ultimately have "b \<le> ?g y Rl" by simp
        also have "\<dots> \<le> Sup (?g y ` Cs)" using Rl by (intro Sup_upper imageI)
        finally show ?thesis .
      qed
      have "c \<le> Sup (?g y ` Cs)"
      proof (rule ccontr)
        assume "\<not> c \<le> Sup (?g y ` Cs)"
        then have "Sup (?g y ` Cs) < c" by simp
        then obtain b where "Sup (?g y ` Cs) < b" and "b < c"
          using ennreal_strict_between by blast
        with below[of b] show False by simp
      qed
      then show "y \<in> {y. c \<le> Sup (?g y ` Cs)}" by blast
    qed
    then show "{y \<in> space (borel :: (real^'n) measure). c \<le> Sup (?g y ` Cs)}
        \<in> sets (borel :: (real^'n) measure)" by simp
  qed
  \<comment> \<open>the selection theorem, and the transfer back to the value function\<close>
  obtain s where sm: "s \<in> (borel :: (real^'n) measure) \<rightarrow>\<^sub>M borel_of MC.mtopology"
    and sC: "\<And>y. s y \<in> ?C"
    and sopt: "\<And>y. y \<in> space (borel :: (real^'n) measure)
        \<Longrightarrow> ?g y (s y) = Sup (?g y ` ?C)"
    by (rule MC.usc_measurable_selection
        [where P = "borel :: (real^'n) measure" and f = ?g, OF Ccpt Cne]) (use hypA hypB in blast)+
  have topC: "?C \<subseteq> topspace ?W"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> ?C"
    have p: "prob_space N" by (rule paper_pair_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with paper_pair_class_sets[OF N] show "N \<in> topspace ?W" by simp
  qed
  have smW: "s \<in> (borel :: (real^'n) measure) \<rightarrow>\<^sub>M borel_of ?W"
  proof (rule measurable_sigma_sets)
    show "sets (borel_of ?W) = sigma_sets (topspace ?W) {U. openin ?W U}"
      by (rule sets_borel_of)
    have "U \<subseteq> topspace ?W" if "openin ?W U" for U by (rule openin_subset[OF that])
    then show "{U. openin ?W U} \<subseteq> Pow (topspace ?W)" by auto
    show "s \<in> space (borel :: (real^'n) measure) \<rightarrow> topspace ?W"
      using sC topC by auto
    show "s -` U \<inter> space (borel :: (real^'n) measure)
        \<in> sets (borel :: (real^'n) measure)" if "U \<in> {U. openin ?W U}" for U
    proof -
      have "openin MC.mtopology (U \<inter> ?C)"
        unfolding Ctop using that by (auto simp: openin_subtopology)
      then have "U \<inter> ?C \<in> sets (borel_of MC.mtopology)" by (rule borel_of_open)
      then have "s -` (U \<inter> ?C) \<inter> space (borel :: (real^'n) measure)
          \<in> sets (borel :: (real^'n) measure)" by (rule measurable_sets[OF sm])
      moreover have "s -` (U \<inter> ?C) = s -` U" using sC by auto
      ultimately show ?thesis by simp
    qed
  qed
  have shiftmem: "pshift_law T y (s y) \<in> paper_pair_class k L T y" for y
    using paper_pair_class_pshift[OF T0 sC, of y] by simp
  have supeq: "Sup (?g y ` ?C) = paper_v k L T K y" for y
  proof -
    have "paper_pair_class k L T y = pshift_law T y ` ?C"
      by (rule paper_pair_class_shift_image[OF T0])
    then have "(\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
          ` paper_pair_class k L T y = ?g y ` ?C"
      by (simp add: image_image)
    then show ?thesis unfolding paper_v_def by simp
  qed
  have sval: "ess_inf_time (pshift_law T y (s y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      = paper_v k L T K y" for y
    using sopt[of y] supeq[of y] by simp
  show ?thesis by (rule that[OF smW sC shiftmem sval])
qed

section \<open>The optimizer as a Giry-monad kernel\<close>

text \<open>Step (iii)'s prerequisite.  Kernel pasting glues with the Giry
  monad's @{term bind}, which wants the continuation as a measurable map
  into @{term prob_algebra} --- the measurable space of probability
  measures --- not merely into the Borel algebra of the weak topology.
  The AFP supplies the bridge: on a POLISH space the two agree once one
  restricts to probability measures with the right \<open>sets\<close>
  (@{thm [source] weak_conv_topology_eq_prob_algebra}), and that is where
  the selector lands anyway.\<close>

lemma Polish_space_path_metric:
  "Polish_space (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))"
  unfolding mtopology_of_def
  by (rule Metric_space.Polish_space_mtopology
      [OF Metric_space_mspace_mdist path_metric_polish(1) path_metric_polish(2)])

theorem paper_v_measurable_selector_kernel:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains S where
    "S \<in> borel \<rightarrow>\<^sub>M prob_algebra (borel_of
        (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and "\<And>y. S y \<in> paper_pair_class k L T 0"
    and "\<And>y. pshift_law T y (S y) \<in> paper_pair_class k L T y"
    and "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = paper_v k L T K y"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?P = "{N :: ('n pairpath) measure. prob_space N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))}"
  obtain S where Sm: "S \<in> borel \<rightarrow>\<^sub>M borel_of ?W"
    and SC: "\<And>y. S y \<in> paper_pair_class k L T 0"
    and Sshift: "\<And>y. pshift_law T y (S y) \<in> paper_pair_class k L T y"
    and Sval: "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = paper_v k L T K y"
    by (rule paper_v_measurable_selector[where k = k, OF T L K]) blast
  have SP: "S y \<in> ?P" for y
    using paper_pair_class_prob[OF SC] paper_pair_class_sets[OF SC] by simp
  have polish: "Polish_space (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule Polish_space_path_metric)
  have setsPA: "sets (borel_of (subtopology ?W ?P)) = sets (prob_algebra ?B)"
    by (rule weak_conv_topology_eq_prob_algebra[OF polish])
  have r1: "S \<in> borel \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?P"
    by (rule measurable_restrict_space2[OF _ Sm]) (use SP in auto)
  have r2: "S \<in> borel \<rightarrow>\<^sub>M borel_of (subtopology ?W ?P)"
    using r1 by (simp add: borel_of_subtopology)
  have Sk: "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
    using r2 measurable_cong_sets[OF refl setsPA] by blast
  show ?thesis
  proof (rule that)
    show "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B" by (rule Sk)
    show "S y \<in> paper_pair_class k L T 0" for y by (rule SC)
    show "pshift_law T y (S y) \<in> paper_pair_class k L T y" for y by (rule Sshift)
    show "ess_inf_time (pshift_law T y (S y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = paper_v k L T K y" for y by (rule Sval)
  qed
qed

section \<open>Kernel pasting: the semidirect product\<close>

text \<open>Step (iii) proper.  @{thm [source] paper_pair_class_kglue_law} glues
  with a COUNTABLY valued index, which
  @{thm [source] Metric_space.usc_measurable_selection} cannot supply ---
  see the note there.  The replacement is the Giry monad's semidirect
  product: run \<open>Q\<close>, then continue with the law the kernel picks at the
  endpoint reached.

  \<open>ksemi M N Kr\<close> is that product on \<open>'a \<times> 'b\<close>.  Everything the pasting
  argument needs about it is here: its \<open>sets\<close> agree with the ordinary
  product (so all the measurability already proved for \<open>Q \<Otimes>\<^sub>M R\<close>
  transfers verbatim by @{thm [source] measurable_cong_sets}), it is a
  probability space, and its almost-sure and nonnegative integrals
  disintegrate.  What it does NOT satisfy is Fubini --- the order of
  integration cannot be swapped --- which is exactly why the product
  martingale machinery has to be redone rather than reused.\<close>

definition ksemi :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b measure) \<Rightarrow> ('a \<times> 'b) measure"
  where "ksemi M N Kr = M \<bind> (\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"

lemma ksemi_sets_kernel:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and w: "\<omega> \<in> space M"
  shows "sets (Kr \<omega>) = sets N" and "prob_space (Kr \<omega>)"
  using measurable_space[OF K w] by (auto simp: space_prob_algebra)

lemma ksemi_Pair_measurable:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and w: "\<omega> \<in> space M"
  shows "Pair \<omega> \<in> Kr \<omega> \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
  using measurable_Pair1'[OF w, of N]
    measurable_cong_sets[OF ksemi_sets_kernel(1)[OF K w] refl] by blast

lemma ksemi_kernel_measurable:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
  shows "(\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) \<in> M \<rightarrow>\<^sub>M subprob_algebra (M \<Otimes>\<^sub>M N)"
proof (rule measurable_distr2[where M = N])
  show "case_prod Pair \<in> M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N" by simp
  show "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N" by (rule measurable_prob_algebraD[OF K])
qed

lemma sets_ksemi[measurable_cong]:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
  shows "sets (ksemi M N Kr) = sets (M \<Otimes>\<^sub>M N)"
  unfolding ksemi_def
  by (rule sets_bind[OF _ ne]) (simp add: ksemi_sets_kernel(1)[OF K])

lemma space_ksemi:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
  shows "space (ksemi M N Kr) = space (M \<Otimes>\<^sub>M N)"
  by (rule sets_eq_imp_space_eq[OF sets_ksemi[OF K ne]])

lemma prob_space_ksemi:
  assumes P: "prob_space M" and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
  shows "prob_space (ksemi M N Kr)"
proof -
  interpret PM: prob_space M by (rule P)
  have "AE \<omega> in M. prob_space (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"
  proof (rule AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    show "prob_space (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"
      by (rule prob_space.prob_space_distr
          [OF ksemi_sets_kernel(2)[OF K w] ksemi_Pair_measurable[OF K w]])
  qed
  from PM.prob_space_bind[OF this ksemi_kernel_measurable[OF K]]
  show ?thesis unfolding ksemi_def .
qed

lemma AE_ksemi:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and P: "{p \<in> space (M \<Otimes>\<^sub>M N). P p} \<in> sets (M \<Otimes>\<^sub>M N)"
  shows "(AE p in ksemi M N Kr. P p) \<longleftrightarrow> (AE \<omega> in M. AE \<omega>' in Kr \<omega>. P (\<omega>, \<omega>'))"
proof -
  have Pp: "Measurable.pred (M \<Otimes>\<^sub>M N) P" using P by (simp add: pred_def)
  have inner: "(AE p in distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>). P p)
      \<longleftrightarrow> (AE \<omega>' in Kr \<omega>. P (\<omega>, \<omega>'))" if w: "\<omega> \<in> space M" for \<omega>
    using AE_distr_iff[OF ksemi_Pair_measurable[OF K w] P] by simp
  have "(AE p in ksemi M N Kr. P p)
      \<longleftrightarrow> (AE \<omega> in M. AE p in distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>). P p)"
    unfolding ksemi_def by (rule AE_bind[OF ksemi_kernel_measurable[OF K] Pp])
  also have "\<dots> \<longleftrightarrow> (AE \<omega> in M. AE \<omega>' in Kr \<omega>. P (\<omega>, \<omega>'))"
    by (rule AE_cong) (simp add: inner)
  finally show ?thesis .
qed

lemma nn_integral_ksemi:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and g: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  shows "(\<integral>\<^sup>+p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  have inner: "(\<integral>\<^sup>+p. g p \<partial>(distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)))
      = (\<integral>\<^sup>+\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))" if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have gm: "g \<in> borel_measurable (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))"
      using g by simp
    show ?thesis
      by (rule nn_integral_distr[OF ksemi_Pair_measurable[OF K w] gm])
  qed
  have "(\<integral>\<^sup>+p. g p \<partial>(ksemi M N Kr))
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+p. g p \<partial>(distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>))) \<partial>M)"
    unfolding ksemi_def
    by (rule nn_integral_bind[OF g ksemi_kernel_measurable[OF K]])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_cong) (simp add: inner)
  finally show ?thesis .
qed

subsection \<open>The glued law, and the two almost-sure clauses of (1.7)\<close>

definition kglue_law' :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "kglue_law' r T Kr Q
     = pair_law_of T (\<lambda>p. pglue r T (fst p) (snd p))
         (ksemi Q (borel_of (mtopology_of
             (path_metric (T - r) :: ('n pairpath) metric))) Kr)"

lemma sets_kglue_law'[simp]:
  "sets (kglue_law' r T Kr Q)
     = sets (borel_of (mtopology_of (path_metric T
         :: ('n::finite pairpath) metric)))"
  unfolding kglue_law'_def by (rule sets_pair_law_of)

lemma space_kglue_law':
  "space (kglue_law' r T Kr Q)
     = mspace (path_metric T :: ('n::finite pairpath) metric)"
  unfolding kglue_law'_def by (rule space_pair_law_of)

lemma kglue_law'_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and ne: "space Q \<noteq> {}"
  shows "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> ksemi Q (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric))) Kr
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  have "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule pglue_measurable[OF r rT setsQ refl])
  then show ?thesis
    using measurable_cong_sets[OF sets_ksemi[OF K ne] refl] by blast
qed

lemma prob_space_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
  shows "prob_space (kglue_law' r T Kr Q)"
proof -
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  interpret PK: prob_space "ksemi Q (borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))) Kr"
    by (rule prob_space_ksemi[OF PQ K])
  show ?thesis
    unfolding kglue_law'_def pair_law_of_def
    by (rule PK.prob_space_distr[OF kglue_law'_measurable[OF r rT setsQ K ne]])
qed

text \<open>The almost-sure transfer.  Note that the second-coordinate property
  \<open>B\<close> may depend on the first coordinate --- it has to, since the kernel
  does.  That is the only difference from
  @{thm [source] AE_kglue_law}; the proof is the same, with
  @{thm [source] AE_ksemi} in place of the product space's
  \<open>AE_pair_measure\<close>.\<close>

lemma AE_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and A: "AE \<omega> in Q. A \<omega>"
    and B: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> AE \<omega>' in Kr \<omega>. B \<omega> \<omega>'"
    and imp: "\<And>\<omega> \<omega>'. \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric) \<Longrightarrow>
        A \<omega> \<Longrightarrow> B \<omega> \<omega>' \<Longrightarrow> P (pglue r T \<omega> \<omega>')"
  shows "AE \<omega> in kglue_law' r T Kr Q. P \<omega>"
proof -
  let ?MR = "borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))"
  let ?S = "ksemi Q ?MR Kr"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have phim: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ?S \<rightarrow>\<^sub>M ?B"
    by (rule kglue_law'_measurable[OF r rT setsQ K ne])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in kglue_law' r T Kr Q. P \<omega>)
      = (AE p in ?S. P (pglue r T (fst p) (snd p)))"
    unfolding kglue_law'_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?S. P (pglue r T (fst p) (snd p))} \<in> sets ?S"
  proof -
    have "{p \<in> space ?S. P (pglue r T (fst p) (snd p))}
        = (\<lambda>p. pglue r T (fst p) (snd p)) -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?S"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have evm': "{p \<in> space (Q \<Otimes>\<^sub>M ?MR). P (pglue r T (fst p) (snd p))}
      \<in> sets (Q \<Otimes>\<^sub>M ?MR)"
    using evm sets_ksemi[OF K ne] space_ksemi[OF K ne] by simp
  have inner: "AE \<omega> in Q. AE \<omega>' in Kr \<omega>. P (pglue r T \<omega> \<omega>')"
  proof -
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<and> \<omega> \<in> space Q"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)
          \<and> \<omega> \<in> space Q"
      then have wQ: "\<omega> \<in> space Q" by blast
      have sk: "sets (Kr \<omega>) = sets ?MR" by (rule ksemi_sets_kernel(1)[OF K wQ])
      have KB: "AE \<omega>' in Kr \<omega>. B \<omega> \<omega>' \<and> \<omega>' \<in> space (Kr \<omega>)"
        using B[OF wQ] AE_space[of "Kr \<omega>"] by (auto intro: eventually_conj)
      show "AE \<omega>' in Kr \<omega>. P (pglue r T \<omega> \<omega>')"
      proof (rule eventually_mono[OF KB])
        fix \<omega>' :: "'n pairpath"
        assume "B \<omega> \<omega>' \<and> \<omega>' \<in> space (Kr \<omega>)"
        then have "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
          and "B \<omega> \<omega>'"
          using sk by (auto simp: space_of_path_sets sets_eq_imp_space_eq
              space_borel_of)
        with w show "P (pglue r T \<omega> \<omega>')" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?S. P (pglue r T (fst p) (snd p))"
    using AE_ksemi[OF K evm'] inner by simp
  then show ?thesis unfolding iff .
qed

text \<open>Clause (i) of (1.7) for the kernel glue.\<close>

lemma kglue_law'_start:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
  shows "AE \<omega> in kglue_law' r T Kr Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
        fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff space_borel_of)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  show ?thesis
  proof (rule AE_kglue_law'[OF r rT paper_pair_class_prob[OF Q]
        paper_pair_class_sets[OF Q] K mset])
    show "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
      using Q unfolding paper_pair_class_def by blast
    show "AE \<omega>' in Kr \<omega>. True" if "\<omega> \<in> space Q" for \<omega> by simp
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      and st: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0" and "True"
    from st show "fst (pglue r T \<omega> \<omega>' 0) = x \<and> snd (pglue r T \<omega> \<omega>' 0) = 0"
      using r rT by (simp add: pglue_zero)
  qed
qed

text \<open>Clause (ii): the covariation difference quotient.  The kernel's
  values have to lie in the class at the origin --- this is the first
  place where that is used, and it is where the almost-sure statement of
  the CONTINUATION enters, one \<open>\<omega>\<close> at a time.\<close>

lemma kglue_law'_diffquot:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Kc: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> Kr \<omega> \<in> paper_pair_class k L (T - r) 0"
  shows "AE \<omega> in kglue_law' r T Kr Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof (rule paper_pair_class_diffquot_of_pairs[OF sets_kglue_law'])
  fix p q :: real
  assume pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
  show "AE \<omega> in kglue_law' r T Kr Q.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_kglue_law'[OF r rT paper_pair_class_prob[OF Q]
        paper_pair_class_sets[OF Q] K mset])
    show "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      using Q unfolding paper_pair_class_def by blast
    show "AE \<omega>' in Kr \<omega>. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
      if w: "\<omega> \<in> space Q" for \<omega>
      using Kc[OF w] unfolding paper_pair_class_def by blast
    fix \<omega> \<omega>' :: "'n pairpath"
    assume "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      and Aw: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      and Bf: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
          (1 / (t - s)) *\<^sub>R (snd (\<omega>' t) - snd (\<omega>' s)) \<in> sconstraint k L"
    show "(1 / (q - p)) *\<^sub>R (snd (pglue r T \<omega> \<omega>' q) - snd (pglue r T \<omega> \<omega>' p))
        \<in> sconstraint k L"
      using pq Aw Bf by (intro pglue_diffquot[OF r rT]) auto
  qed
qed

subsection \<open>The glue is continuous, and the product is a Polish product\<close>

text \<open>A change of route for clauses (iii) and (iv), decided 2026-08-07.
  Proving them directly for @{const ksemi} runs into two obstructions: the
  distribution's \<open>integral_bind\<close> is only for BOUNDED REAL integrands, and
  the FIRST-factor martingale property is FALSE for a semidirect product
  (the weight \<open>(Kr \<omega>)(A\<^sub>\<omega>)\<close> in the disintegrated set integral is only
  \<open>\<F>\<^sub>r\<close>-measurable).

  Neither has to be faced.  The class is WEAKLY CLOSED
  (@{thm [source] paper_pair_class_weak_closed}), the glue with a COUNTABLY
  valued index is already in it
  (@{thm [source] paper_pair_class_kglue_law}), and the class at the origin
  is a COMPACT metric space
  (@{thm [source] paper_pair_class_compact_metric_space}) --- so it is
  separable, and any kernel into it is a pointwise limit of countably
  valued ones.  If the semidirect products converge weakly, the glued laws
  do too, and weak closedness finishes.  What that needs is exactly what
  the martingale route did not: continuity of the glue, and the identity
  of the two \<sigma>-algebras on the product.\<close>

lemma second_countable_path_metric:
  "second_countable (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))"
  unfolding mtopology_of_def
  by (rule Metric_space.separable_space_imp_second_countable
      [OF Metric_space_mspace_mdist path_metric_polish(2)])

lemma borel_of_path_prod:
  "borel_of (mtopology_of (path_metric r :: ('n::finite pairpath) metric))
     \<Otimes>\<^sub>M borel_of (mtopology_of (path_metric s :: ('n pairpath) metric))
   = borel_of (mtopology_of (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric s :: ('n pairpath) metric)))"
  by (simp add: borel_of_prod second_countable_path_metric)

lemma mdist_pglue_le:
  fixes w wt w' wt' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "w \<in> mspace (path_metric r :: ('n pairpath) metric)"
    and wt: "wt \<in> mspace (path_metric r :: ('n pairpath) metric)"
    and w': "w' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
    and wt': "wt' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
  shows "mdist (path_metric T :: ('n pairpath) metric)
        (pglue r T w w') (pglue r T wt wt')
      \<le> mdist (path_metric r :: ('n pairpath) metric) w wt
        + 2 * mdist (path_metric (T - r) :: ('n pairpath) metric) w' wt'"
proof -
  let ?d1 = "mdist (path_metric r :: ('n pairpath) metric) w wt"
  let ?d2 = "mdist (path_metric (T - r) :: ('n pairpath) metric) w' wt'"
  have T0: "0 \<le> T" using r rT by simp
  have Tr0: "0 \<le> T - r" using rT by simp
  have g1: "pglue r T w w' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pglue_in_mspace[OF r rT w w'])
  have g2: "pglue r T wt wt' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pglue_in_mspace[OF r rT wt wt'])
  have pw1: "dist (w t) (wt t) \<le> ?d1" if "t \<in> {0..r}" for t
    using path_mdist_le_iff_all[OF r w wt] that by blast
  have pw2: "dist (w' t) (wt' t) \<le> ?d2" if "t \<in> {0..T - r}" for t
    using path_mdist_le_iff_all[OF Tr0 w' wt'] that by blast
  have pw: "dist (pglue r T w w' t) (pglue r T wt wt' t) \<le> ?d1 + 2 * ?d2"
    if t: "t \<in> {0..T}" for t
  proof (cases "t \<le> r")
    case True
    then have tr: "t \<in> {0..r}" using t by simp
    have "dist (pglue r T w w' t) (pglue r T wt wt' t) = dist (w t) (wt t)"
      using t True by (simp add: pglue_le)
    also have "\<dots> \<le> ?d1" by (rule pw1[OF tr])
    also have "\<dots> \<le> ?d1 + 2 * ?d2" by simp
    finally show ?thesis .
  next
    case False
    then have tr: "r \<le> t" by simp
    have t1: "t - r \<in> {0..T - r}" using t tr by simp
    have t2: "(0::real) \<in> {0..T - r}" using Tr0 by simp
    have alg: "(w r + (w' (t - r) - w' 0)) - (wt r + (wt' (t - r) - wt' 0))
        = (w r - wt r) + ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0))"
      by (simp add: algebra_simps)
    have "dist (pglue r T w w' t) (pglue r T wt wt' t)
        = norm ((w r - wt r) + ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0)))"
      using t tr by (simp add: pglue_ge dist_norm alg)
    also have "\<dots> \<le> norm (w r - wt r)
        + norm ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0))"
      by (rule norm_triangle_ineq)
    also have "\<dots> \<le> norm (w r - wt r)
        + (norm (w' (t - r) - wt' (t - r)) + norm (w' 0 - wt' 0))"
      by (simp add: norm_triangle_ineq4)
    also have "\<dots> \<le> ?d1 + (?d2 + ?d2)"
      using pw1[of r] pw2[OF t1] pw2[OF t2] r by (simp add: dist_norm)
    finally show ?thesis by simp
  qed
  show ?thesis using path_mdist_le_iff_all[OF T0 g1 g2] pw by blast
qed

lemma Lipschitz_pglue:
  fixes r T :: real
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map
      (prod_metric (path_metric r :: ('n::finite pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric))
      (path_metric T :: ('n pairpath) metric)
      (\<lambda>p. pglue r T (fst p) (snd p))"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
          (path_metric (T - r) :: ('n pairpath) metric))
        \<rightarrow> mspace (path_metric T :: ('n pairpath) metric)"
    using pglue_in_mspace[OF r rT] by (intro funcsetI) auto
  show "\<exists>B. \<forall>p \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
          (path_metric (T - r) :: ('n pairpath) metric)).
      \<forall>q \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
          (path_metric (T - r) :: ('n pairpath) metric)).
        mdist (path_metric T :: ('n pairpath) metric)
            ((\<lambda>p. pglue r T (fst p) (snd p)) p) ((\<lambda>p. pglue r T (fst p) (snd p)) q)
          \<le> B * mdist (prod_metric (path_metric r :: ('n pairpath) metric)
              (path_metric (T - r) :: ('n pairpath) metric)) p q"
  proof (intro exI[of _ 3] ballI)
    fix p q :: "'n pairpath \<times> 'n pairpath"
    assume p: "p \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric))"
      and q: "q \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric))"
    from p have p1: "fst p \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and p2: "snd p \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by auto
    from q have q1: "fst q \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and q2: "snd q \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by auto
    let ?a = "mdist (path_metric r :: ('n pairpath) metric) (fst p) (fst q)"
    let ?b = "mdist (path_metric (T - r) :: ('n pairpath) metric) (snd p) (snd q)"
    let ?pd = "mdist (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric)) p q"
    have pdeq: "?pd = sqrt (?a\<^sup>2 + ?b\<^sup>2)"
      by (simp add: prod_dist_def case_prod_unfold)
    have c1: "?a \<le> ?pd"
    proof -
      have "?a = sqrt (?a\<^sup>2)" by simp
      also have "\<dots> \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2)" by (simp add: real_sqrt_le_mono)
      finally show ?thesis using pdeq by simp
    qed
    have c2: "?b \<le> ?pd"
    proof -
      have "?b = sqrt (?b\<^sup>2)" by simp
      also have "\<dots> \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2)" by (simp add: real_sqrt_le_mono)
      finally show ?thesis using pdeq by simp
    qed
    have "mdist (path_metric T :: ('n pairpath) metric)
        (pglue r T (fst p) (snd p)) (pglue r T (fst q) (snd q)) \<le> ?a + 2 * ?b"
      by (rule mdist_pglue_le[OF r rT p1 q1 p2 q2])
    also have "\<dots> \<le> 3 * ?pd" using c1 c2 by simp
    finally show "mdist (path_metric T :: ('n pairpath) metric)
        ((\<lambda>p. pglue r T (fst p) (snd p)) p) ((\<lambda>p. pglue r T (fst p) (snd p)) q)
        \<le> 3 * ?pd" by simp
  qed
qed

subsection \<open>Weak convergence of the semidirect products\<close>

text \<open>The bounded disintegration.  This is the case the distribution's
  \<open>integral_bind\<close> does cover, and it is all the weak-convergence route
  needs --- test functions for weak convergence are bounded and real by
  definition.\<close>

lemma integral_ksemi_bounded:
  fixes g :: "'a \<times> 'b \<Rightarrow> real"
  assumes PM: "prob_space M"
    and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gb: "\<And>p. p \<in> space (M \<Otimes>\<^sub>M N) \<Longrightarrow> \<bar>g p\<bar> \<le> B"
  shows "(\<integral>p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  interpret PM: prob_space M by (rule PM)
  let ?f = "\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)"
  have fm: "?f \<in> M \<rightarrow>\<^sub>M subprob_algebra (M \<Otimes>\<^sub>M N)"
    by (rule ksemi_kernel_measurable[OF K])
  have gb': "\<bar>g p\<bar> \<le> B" if "p \<in> space (M \<Otimes>\<^sub>M N)" for p by (rule gb[OF that])
  have ae: "AE \<omega> in M. emeasure (?f \<omega>) (space (?f \<omega>)) \<le> ennreal 1"
  proof (rule AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have "prob_space (?f \<omega>)"
      by (rule prob_space.prob_space_distr
          [OF ksemi_sets_kernel(2)[OF K w] ksemi_Pair_measurable[OF K w]])
    then have "emeasure (?f \<omega>) (space (?f \<omega>)) = 1"
      by (rule prob_space.emeasure_space_1)
    then show "emeasure (?f \<omega>) (space (?f \<omega>)) \<le> ennreal 1" by simp
  qed
  have "(\<integral>p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<omega>. (\<integral>p. g p \<partial>(?f \<omega>)) \<partial>M)"
    unfolding ksemi_def
    by (rule integral_bind[OF gm gb' fm PM.finite_measure_axioms ae])
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix \<omega> assume w: "\<omega> \<in> space M"
    show "(\<integral>p. g p \<partial>(?f \<omega>)) = (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
      by (rule integral_distr[OF ksemi_Pair_measurable[OF K w] gm])
  qed
  finally show ?thesis .
qed

lemma integral_ksemi_measurable:
  fixes g :: "'a \<times> 'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  shows "(\<lambda>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))) \<in> borel_measurable M"
proof -
  let ?f = "\<lambda>\<omega>. distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)"
  have "(\<lambda>\<omega>. (\<integral>p. g p \<partial>(?f \<omega>))) \<in> borel_measurable M"
    using measurable_compose[OF ksemi_kernel_measurable[OF K]
        integral_measurable_subprob_algebra[OF gm]] .
  moreover have "(\<integral>p. g p \<partial>(?f \<omega>)) = (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    show ?thesis by (rule integral_distr[OF ksemi_Pair_measurable[OF K w] gm])
  qed
  ultimately show ?thesis by (simp cong: measurable_cong)
qed

text \<open>Pointwise weak convergence of the KERNELS gives weak convergence of
  the semidirect products.  The proof is dominated convergence over the
  first coordinate: a bounded continuous test function on the product is,
  at each fixed first coordinate, a bounded continuous test function on
  the second, so the inner integrals converge pointwise, and they are all
  bounded by the same constant.\<close>

lemma ksemi_weak_conv:
  fixes Krm :: "nat \<Rightarrow> 'a \<Rightarrow> 'b measure" and X :: "'a topology" and Y :: "'b topology"
  assumes PM: "prob_space M"
    and setsM: "sets M = sets (borel_of X)"
    and scX: "second_countable X" and scY: "second_countable Y"
    and Km: "\<And>m. Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of Y)"
    and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of Y)"
    and conv: "\<And>\<omega>. \<omega> \<in> space M
        \<Longrightarrow> weak_conv_on (\<lambda>m. Krm m \<omega>) (Kr \<omega>) sequentially Y"
  shows "weak_conv_on (\<lambda>m. ksemi M (borel_of Y) (Krm m))
      (ksemi M (borel_of Y) Kr) sequentially (prod_topology X Y)"
proof -
  let ?N = "borel_of Y"
  let ?Z = "prod_topology X Y"
  interpret PM: prob_space M by (rule PM)
  have ne: "space M \<noteq> {}" by (rule PM.not_empty)
  have spX: "space M = topspace X"
    using setsM by (simp add: sets_eq_imp_space_eq space_borel_of)
  have bprod: "sets (M \<Otimes>\<^sub>M ?N) = sets (borel_of ?Z)"
  proof -
    have "sets (M \<Otimes>\<^sub>M ?N) = sets (borel_of X \<Otimes>\<^sub>M borel_of Y)"
      by (rule sets_pair_measure_cong[OF setsM refl])
    also have "\<dots> = sets (borel_of ?Z)"
      by (rule arg_cong[where f = sets, OF borel_of_prod[OF scX scY]])
    finally show ?thesis .
  qed
  have setsK: "sets (ksemi M ?N Kr) = sets (borel_of ?Z)"
    using sets_ksemi[OF K ne] bprod by simp
  have setsKm: "sets (ksemi M ?N (Krm m)) = sets (borel_of ?Z)" for m
  proof -
    have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
    show ?thesis using sets_ksemi[OF Kmm ne] bprod by simp
  qed
  have fmK: "finite_measure (ksemi M ?N Kr)"
    using prob_space_ksemi[OF PM K]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmKm: "finite_measure (ksemi M ?N (Krm m))" for m
  proof -
    have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
    show ?thesis using prob_space_ksemi[OF PM Kmm]
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
  qed
  show ?thesis
    unfolding weak_conv_on_def
  proof (intro conjI allI impI)
    show "\<forall>\<^sub>F m in sequentially. sets (ksemi M ?N (Krm m)) = sets (borel_of ?Z)
        \<and> finite_measure (ksemi M ?N (Krm m))"
      by (intro always_eventually allI conjI setsKm fmKm)
    show "sets (ksemi M ?N Kr) = sets (borel_of ?Z)" by (rule setsK)
    show "finite_measure (ksemi M ?N Kr)" by (rule fmK)
    fix f :: "'a \<times> 'b \<Rightarrow> real"
    assume cf: "continuous_map ?Z euclideanreal f"
    assume bf: "\<exists>B. \<forall>p \<in> topspace ?Z. \<bar>f p\<bar> \<le> B"
    from bf obtain B where B: "\<And>p. p \<in> topspace ?Z \<Longrightarrow> \<bar>f p\<bar> \<le> B" by blast
    have fm: "f \<in> borel_measurable (M \<Otimes>\<^sub>M ?N)"
    proof -
      have "f \<in> borel_of ?Z \<rightarrow>\<^sub>M borel_of euclideanreal"
        by (rule continuous_map_measurable[OF cf])
      then have "f \<in> borel_measurable (borel_of ?Z)"
        by (simp add: borel_of_euclidean)
      then show ?thesis unfolding measurable_cong_sets[OF bprod refl] .
    qed
    have spZ: "space (M \<Otimes>\<^sub>M ?N) = topspace ?Z"
    proof -
      have "space (M \<Otimes>\<^sub>M ?N) = space (borel_of ?Z)"
        by (rule sets_eq_imp_space_eq[OF bprod])
      then show ?thesis by (simp add: space_borel_of)
    qed
    have fb: "\<bar>f p\<bar> \<le> B" if "p \<in> space (M \<Otimes>\<^sub>M ?N)" for p
      using that spZ by (simp add: B)
    \<comment> \<open>the two disintegrations\<close>
    have dK: "(\<integral>p. f p \<partial>(ksemi M ?N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
      by (rule integral_ksemi_bounded[OF PM K fm fb])
    have dKm: "(\<integral>p. f p \<partial>(ksemi M ?N (Krm m)))
        = (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<partial>M)" for m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      show ?thesis by (rule integral_ksemi_bounded[OF PM Kmm fm fb])
    qed
    \<comment> \<open>the inner integrals converge pointwise and are uniformly bounded\<close>
    have inner_lim: "(\<lambda>m. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<longlonglongrightarrow> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have wX: "\<omega> \<in> topspace X" using w spX by simp
      have cpair: "continuous_map Y ?Z (Pair \<omega>)"
        unfolding continuous_map_pairwise using wX by (simp add: o_def)
      have cg: "continuous_map Y euclideanreal (\<lambda>\<omega>'. f (\<omega>, \<omega>'))"
        using continuous_map_compose[OF cpair cf] by (simp add: comp_def)
      have bg: "\<exists>B'. \<forall>y \<in> topspace Y. \<bar>f (\<omega>, y)\<bar> \<le> B'"
        using B wX by (intro exI[of _ B]) auto
      show ?thesis using conv[OF w, unfolded weak_conv_on_def] cg bg by blast
    qed
    have inner_meas: "(\<lambda>\<omega>. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<in> borel_measurable M" for m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      show ?thesis by (rule integral_ksemi_measurable[OF Kmm fm])
    qed
    have inner_meas': "(\<lambda>\<omega>. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
      by (rule integral_ksemi_measurable[OF K fm])
    have inner_bnd: "\<bar>\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)\<bar> \<le> \<bar>B\<bar>" if w: "\<omega> \<in> space M" for \<omega> m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      interpret PK: prob_space "Krm m \<omega>" by (rule ksemi_sets_kernel(2)[OF Kmm w])
      have sk: "sets (Krm m \<omega>) = sets ?N" by (rule ksemi_sets_kernel(1)[OF Kmm w])
      have gm: "(\<lambda>\<omega>'. f (\<omega>, \<omega>')) \<in> borel_measurable (Krm m \<omega>)"
      proof -
        have "Pair \<omega> \<in> Krm m \<omega> \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M ?N"
          by (rule ksemi_Pair_measurable[OF Kmm w])
        from measurable_compose[OF this fm] show ?thesis by simp
      qed
      have spk: "space (Krm m \<omega>) = space ?N" by (rule sets_eq_imp_space_eq[OF sk])
      have gb: "\<bar>f (\<omega>, \<omega>')\<bar> \<le> \<bar>B\<bar>" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
      proof -
        have "\<omega>' \<in> space ?N" using that spk by simp
        then have "(\<omega>, \<omega>') \<in> space (M \<Otimes>\<^sub>M ?N)"
          using w by (simp add: space_pair_measure)
        then show ?thesis using fb[of "(\<omega>, \<omega>')"] by simp
      qed
      have gbu: "f (\<omega>, \<omega>') \<le> \<bar>B\<bar>" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
        using gb[OF that] by (simp add: abs_le_iff)
      have gbl: "- \<bar>B\<bar> \<le> f (\<omega>, \<omega>')" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
        using gb[OF that] by (simp add: abs_le_iff)
      have cint: "(\<integral>\<omega>'. (c::real) \<partial>(Krm m \<omega>)) = c" for c
        by (simp add: PK.prob_space)
      have ig: "integrable (Krm m \<omega>) (\<lambda>\<omega>'. f (\<omega>, \<omega>'))"
        by (rule PK.integrable_const_bound[of _ "\<bar>B\<bar>"])
          (use gb gm in \<open>auto intro: AE_I2\<close>)
      have ic: "integrable (Krm m \<omega>) (\<lambda>\<omega>'. \<bar>B\<bar>)" by (rule PK.integrable_const)
      have ic': "integrable (Krm m \<omega>) (\<lambda>\<omega>'. - \<bar>B\<bar>)" by (rule PK.integrable_const)
      have up: "(\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> \<bar>B\<bar>"
      proof -
        have "(\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> (\<integral>\<omega>'. \<bar>B\<bar> \<partial>(Krm m \<omega>))"
          by (rule integral_mono[OF ig ic gbu])
        also have "\<dots> = \<bar>B\<bar>" by (rule cint)
        finally show ?thesis .
      qed
      have lo: "- \<bar>B\<bar> \<le> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))"
      proof -
        have "- \<bar>B\<bar> = (\<integral>\<omega>'. - \<bar>B\<bar> \<partial>(Krm m \<omega>))" by (rule cint[symmetric])
        also have "\<dots> \<le> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))"
          by (rule integral_mono[OF ic' ig gbl])
        finally show ?thesis .
      qed
      from up lo show ?thesis by simp
    qed
    have "(\<lambda>m. \<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<partial>M)
        \<longlonglongrightarrow> (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    proof (rule integral_dominated_convergence
        [where w = "\<lambda>_. \<bar>B\<bar>", OF inner_meas' inner_meas])
      show "integrable M (\<lambda>_. \<bar>B\<bar>)" by simp
      show "AE \<omega> in M. (\<lambda>m. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))
          \<longlonglongrightarrow> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
        using inner_lim by (intro AE_I2) blast
      show "AE \<omega> in M. norm (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> \<bar>B\<bar>" for m
        using inner_bnd by (intro AE_I2) simp
    qed
    then show "(\<lambda>m. \<integral>p. f p \<partial>(ksemi M ?N (Krm m)))
        \<longlonglongrightarrow> (\<integral>p. f p \<partial>(ksemi M ?N Kr))"
      by (simp add: dK dKm)
  qed
qed

subsection \<open>Countably valued approximation of a kernel\<close>

text \<open>A measurable map into a COMPACT metric space is a uniform limit of
  countably valued measurable maps: round to the nearest point of a dense
  sequence, taking the least admissible index so that the choice is
  measurable.  The rounding is measurable for a cheap reason --- the set
  where the distance to a fixed centre is small is an OPEN BALL, so its
  preimage is measurable with no continuity argument at all.\<close>

lemma (in Metric_space) countably_valued_approx:
  fixes g :: "'b \<Rightarrow> 'a" and P :: "'b measure"
  assumes cpt: "compact_space mtopology" and ne: "M \<noteq> {}"
    and gm: "g \<in> P \<rightarrow>\<^sub>M borel_of mtopology" and rng: "\<And>x. g x \<in> M"
  obtains z :: "nat \<Rightarrow> 'a" and Nx :: "nat \<Rightarrow> 'b \<Rightarrow> nat"
    where "\<And>j. z j \<in> M"
      and "\<And>m. Nx m \<in> P \<rightarrow>\<^sub>M count_space UNIV"
      and "\<And>m x. d (z (Nx m x)) (g x) < (1/2)^m"
proof -
  obtain z :: "nat \<Rightarrow> 'a" where z0: "\<forall>j. z j \<in> M"
    and zd0: "\<forall>y \<in> M. \<forall>e > 0. \<exists>j. d (z j) y < e"
    using compact_space_dense_seq[OF cpt ne] by blast
  have zM: "z j \<in> M" for j using z0 by blast
  have ex: "\<exists>j. d (z j) (g x) < (1/2::real)^m" for m x
    using zd0 rng[of x] by simp
  define Nx :: "nat \<Rightarrow> 'b \<Rightarrow> nat"
    where "Nx = (\<lambda>m x. LEAST j. d (z j) (g x) < (1/2::real)^m)"
  have lt: "d (z (Nx m x)) (g x) < (1/2::real)^m" for m x
    unfolding Nx_def by (rule LeastI_ex) (rule ex)
  have fib: "(Nx m x = j) \<longleftrightarrow> (d (z j) (g x) < (1/2::real)^m
      \<and> (\<forall>i<j. \<not> d (z i) (g x) < (1/2::real)^m))" for m x j
    unfolding Nx_def by (rule Least_nat_eq_iff) (rule ex)
  have ball: "{x \<in> space P. d (z i) (g x) < c} \<in> sets P" for i c
  proof -
    have "{x \<in> space P. d (z i) (g x) < c} = g -` mball (z i) c \<inter> space P"
      using zM rng by auto
    moreover have "mball (z i) c \<in> sets (borel_of mtopology)"
      by (rule borel_of_open) simp
    ultimately show ?thesis using measurable_sets[OF gm] by simp
  qed
  have Nm: "Nx m \<in> P \<rightarrow>\<^sub>M count_space UNIV" for m
  proof -
    have fibm: "Nx m -` {j} \<inter> space P \<in> sets P" for j
    proof -
      have "Nx m -` {j} \<inter> space P
          = {x \<in> space P. d (z j) (g x) < (1/2::real)^m}
            - (\<Union>i\<in>{..<j}. {x \<in> space P. d (z i) (g x) < (1/2::real)^m})"
        using fib by auto
      moreover have "(\<Union>i\<in>{..<j}. {x \<in> space P. d (z i) (g x)
          < (1/2::real)^m}) \<in> sets P"
        using ball by (intro sets.finite_UN) auto
      ultimately show ?thesis using ball by (simp add: sets.Diff)
    qed
    show ?thesis
      using fibm by (auto simp: measurable_count_space_eq2_countable)
  qed
  show ?thesis by (rule that[OF zM Nm lt])
qed

lemma (in Metric_space) limitin_of_dist_half:
  assumes zz: "\<And>m. zz m \<in> M" and y: "y \<in> M"
    and lt: "\<And>m. d (zz m) y < (1/2::real)^m"
  shows "limitin mtopology zz y sequentially"
  unfolding limitin_metric
proof (intro conjI y allI impI)
  fix e :: real assume e: "0 < e"
  have "(\<lambda>m. (1/2::real)^m) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) auto
  then have "\<forall>\<^sub>F m in sequentially. (1/2::real)^m < e"
    using e by (rule order_tendstoD(2))
  then show "\<forall>\<^sub>F m in sequentially. zz m \<in> M \<and> d (zz m) y < e"
  proof (rule eventually_mono)
    fix m assume "(1/2::real)^m < e"
    with lt[of m] zz[of m] show "zz m \<in> M \<and> d (zz m) y < e" by simp
  qed
qed

subsection \<open>The two constructions agree at a countably valued kernel\<close>

text \<open>The last structural step.  With a countably valued index the
  product-of-all-candidates construction and the Giry semidirect product
  give the SAME law, because the second coordinate of the product,
  evaluated at a first-coordinate-measurable index, has exactly the
  kernel's law.  Both sides reduce to
  \<open>\<integral>\<^sup>+\<omega>. (RR (N \<omega>)) {\<omega>'. pglue r T \<omega> \<omega>' \<in> A} \<partial>Q\<close>: on the left by Fubini and
  @{thm [source] distr_PiM_component}, on the right by @{thm [source]
  emeasure_bind} and @{thm [source] emeasure_distr}.\<close>

lemma kglue_law_eq_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and setsR: "\<And>j. sets (RR j) = sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
    and K: "(\<lambda>\<omega>. RR (N \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
  shows "kglue_law r T N Q RR = kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q"
proof (rule measure_eqI)
  let ?MR = "borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?P = "Q \<Otimes>\<^sub>M ?S"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PS: prob_space ?S by (rule prob_space_PiM) (rule PR)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have gm: "kglue r T N \<in> ?P \<rightarrow>\<^sub>M ?B"
    by (rule kglue_measurable[OF r rT setsQ setsR Nm])
  have pm: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)) \<rightarrow>\<^sub>M ?B"
    by (rule kglue_law'_measurable[OF r rT setsQ K ne])
  show "sets (kglue_law r T N Q RR) = sets (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q)"
    by simp
  fix A :: "('n pairpath) set"
  assume A: "A \<in> sets (kglue_law r T N Q RR)"
  then have AB: "A \<in> sets ?B" by simp
  \<comment> \<open>the section of the pulled-back set, one \<omega> at a time\<close>
  have sec: "emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
      = emeasure ?S (Pair \<omega> -` (kglue r T N -` A \<inter> space ?P))"
    if w: "\<omega> \<in> space Q" for \<omega>
  proof -
    have Pj: "prob_space (RR i)" if "i \<in> (UNIV :: nat set)" for i by (rule PR)
    have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f (N \<omega>)) \<in> ?S \<rightarrow>\<^sub>M RR (N \<omega>)"
      by (rule measurable_component_singleton) simp
    have dj: "distr ?S (RR (N \<omega>)) (\<lambda>f. f (N \<omega>)) = RR (N \<omega>)"
      by (rule distr_PiM_component[OF Pj UNIV_I])
    have pglm: "pglue r T \<omega> \<in> RR (N \<omega>) \<rightarrow>\<^sub>M ?B"
    proof -
      have p1: "Pair \<omega> \<in> RR (N \<omega>) \<rightarrow>\<^sub>M Q \<Otimes>\<^sub>M ?MR"
        using measurable_Pair1'[OF w, of ?MR]
          measurable_cong_sets[OF setsR refl] by blast
      have p2: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?MR \<rightarrow>\<^sub>M ?B"
        by (rule pglue_measurable[OF r rT setsQ refl])
      from measurable_compose[OF p1 p2] show ?thesis by (simp add: comp_def)
    qed
    have Am: "{\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<in> sets (RR (N \<omega>))"
    proof -
      have "{\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
          = pglue r T \<omega> -` A \<inter> space (RR (N \<omega>))" by auto
      then show ?thesis using measurable_sets[OF pglm AB] by simp
    qed
    have "emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
        = emeasure (distr ?S (RR (N \<omega>)) (\<lambda>f. f (N \<omega>)))
            {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}"
      unfolding dj ..
    also have "\<dots> = emeasure ?S
        ((\<lambda>f. f (N \<omega>)) -` {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<inter> space ?S)"
      by (rule emeasure_distr[OF mj Am])
    also have "(\<lambda>f. f (N \<omega>)) -` {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
          \<inter> space ?S
        = Pair \<omega> -` (kglue r T N -` A \<inter> space ?P)"
      using w measurable_space[OF mj] by (auto simp: space_pair_measure kglue_def)
    finally show ?thesis .
  qed
  \<comment> \<open>the left-hand side by Fubini\<close>
  have lhs: "emeasure (kglue_law r T N Q RR) A
      = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
  proof -
    have "emeasure (kglue_law r T N Q RR) A
        = emeasure ?P (kglue r T N -` A \<inter> space ?P)"
      unfolding kglue_law_def pair_law_of_def by (rule emeasure_distr[OF gm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure ?S (Pair \<omega> -` (kglue r T N -` A \<inter> space ?P)) \<partial>Q)"
      by (rule PS.emeasure_pair_measure_alt) (rule measurable_sets[OF gm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>))
        {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
      by (rule nn_integral_cong) (simp add: sec)
    finally show ?thesis .
  qed
  \<comment> \<open>the right-hand side by the semidirect product's disintegration\<close>
  have rhs: "emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A
      = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
  proof -
    define C where "C = (\<lambda>p. pglue r T (fst p) (snd p)) -` A
        \<inter> space (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)))"
    have Cs: "C \<in> sets (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)))"
      unfolding C_def by (rule measurable_sets[OF pm AB])
    have Csp: "C \<in> sets (Q \<Otimes>\<^sub>M ?MR)" using Cs sets_ksemi[OF K ne] by simp
    have "emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A
        = emeasure (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>))) C"
      unfolding kglue_law'_def pair_law_of_def C_def
      by (rule emeasure_distr[OF pm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C \<partial>Q)"
      unfolding ksemi_def
      by (rule emeasure_bind[OF ne ksemi_kernel_measurable[OF K] Csp])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>))
        {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
    proof (rule nn_integral_cong)
      fix \<omega> assume w: "\<omega> \<in> space Q"
      have spR: "space (RR (N \<omega>)) = space ?MR"
        by (rule sets_eq_imp_space_eq[OF setsR])
      have "emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C
          = emeasure (RR (N \<omega>)) (Pair \<omega> -` C \<inter> space (RR (N \<omega>)))"
        by (rule emeasure_distr[OF ksemi_Pair_measurable[OF K w] Csp])
      also have "Pair \<omega> -` C \<inter> space (RR (N \<omega>))
          = {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}"
        unfolding C_def
        using w spR space_ksemi[OF K ne] by (auto simp: space_pair_measure)
      finally show "emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C
          = emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}" .
    qed
    finally show ?thesis .
  qed
  show "emeasure (kglue_law r T N Q RR) A
      = emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A"
    using lhs rhs by simp
qed

subsection \<open>Kernel pasting: clauses (iii) and (iv), by weak closedness\<close>

text \<open>The headline of the new route.  The class is closed under
  concatenation with a continuation chosen by an ARBITRARY measurable
  kernel, not just a countably valued index --- and the two martingale
  clauses never have to be proved for the semidirect product.

  Round the kernel to the dense sequence of the compact class
  (@{thm [source] Metric_space.countably_valued_approx}); each rounded
  glue is a legitimate pasting
  (@{thm [source] paper_pair_class_kglue_law}) and, by
  @{thm [source] kglue_law_eq_kglue_law'}, is the kernel glue at the
  rounded kernel; the semidirect products converge weakly
  (@{thm [source] ksemi_weak_conv}), the glue is continuous
  (@{thm [source] Lipschitz_pglue}), so the glued laws converge; and the
  class is weakly closed
  (@{thm [source] paper_pair_class_weak_closed}).\<close>

theorem paper_pair_class_kglue_law':
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L"
    and T0: "0 < T"
    and Q: "Q \<in> paper_pair_class k L r x"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Kb: "Kr \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
            (paper_pair_class k L (T - r) (0::real^'n))
            (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
              (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and Kc: "\<And>\<omega>. Kr \<omega> \<in> paper_pair_class k L (T - r) 0"
  shows "kglue_law' r T Kr Q \<in> paper_pair_class k L T x"
proof -
  let ?s = "T - r"
  let ?C0 = "paper_pair_class k L ?s (0::real^'n)"
  let ?dd = "Levy_Prokhorov.LPm (mspace (path_metric ?s :: ('n pairpath) metric))
      (mdist (path_metric ?s :: ('n pairpath) metric))"
  let ?MR = "borel_of (mtopology_of (path_metric ?s :: ('n pairpath) metric))"
  let ?X = "mtopology_of (path_metric r :: ('n pairpath) metric)"
  let ?Y = "mtopology_of (path_metric ?s :: ('n pairpath) metric)"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have s0: "0 < ?s" using rT by simp
  have s0': "0 \<le> ?s" using s0 by simp
  have L0: "0 \<le> L" using L1 by simp
  have rT': "r \<le> T" using rT by simp
  have setsQ: "sets Q = sets (borel_of ?X)" by (rule paper_pair_class_sets[OF Q])
  have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  interpret MC: Metric_space "paper_pair_class k L ?s (0::real^'n)" ?dd
    by (rule paper_pair_class_compact_metric_space(1)[OF s0 L0])
  have Ctop: "MC.mtopology = subtopology (weak_conv_topology ?Y) ?C0"
    by (rule paper_pair_class_compact_metric_space(2)[OF s0 L0])
  have Ccpt: "compact_space MC.mtopology"
    by (rule paper_pair_class_compact_metric_space(3)[OF s0 L0])
  have Cne: "?C0 \<noteq> {}" by (rule paper_pair_class_nonempty[OF s0' L1])
  \<comment> \<open>round the kernel to a dense sequence of the compact class\<close>
  obtain z :: "nat \<Rightarrow> ('n pairpath) measure"
    and Nm :: "nat \<Rightarrow> 'n pairpath \<Rightarrow> nat"
    where zC: "\<And>j. z j \<in> ?C0"
    and Nmeas: "\<And>m. Nm m \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M count_space UNIV"
    and zclose: "\<And>m \<omega>. ?dd (z (Nm m \<omega>)) (Kr \<omega>) < (1/2)^m"
    by (rule MC.countably_valued_approx[OF Ccpt Cne Kb Kc]) blast
  have NmQ: "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" for m
  proof -
    interpret MQ0: martingale Q "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      "0::real" "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n"
      by (rule paper_pair_class_X_martingale[OF Q])
    show ?thesis by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nmeas])
  qed
  \<comment> \<open>each rounded glue is in the class, and IS the kernel glue at the rounding\<close>
  have memm: "kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q \<in> paper_pair_class k L T x" for m
  proof -
    have "kglue_law r T (Nm m) Q z \<in> paper_pair_class k L T x"
      by (rule paper_pair_class_kglue_law[OF r rT' L0 Q zC Nmeas])
    moreover have "kglue_law r T (Nm m) Q z = kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q"
    proof (rule kglue_law_eq_kglue_law'[OF r rT' PQ _ setsQ _ NmQ])
      show "prob_space (z j)" for j by (rule paper_pair_class_prob[OF zC])
      show "sets (z j) = sets ?MR" for j by (rule paper_pair_class_sets[OF zC])
      show "(\<lambda>\<omega>. z (Nm m \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR"
      proof (rule measurable_compose_countable[where f = "\<lambda>j (_ :: 'n pairpath). z j"])
        show "(\<lambda>\<omega>. z j) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for j
          using paper_pair_class_prob[OF zC] paper_pair_class_sets[OF zC]
          by (simp add: measurable_const space_prob_algebra)
        show "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
      qed
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>the kernels converge pointwise, hence the semidirect products do\<close>
  have Kpm: "(\<lambda>\<omega>. z (Nm m \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for m
  proof (rule measurable_compose_countable[where f = "\<lambda>j (_ :: 'n pairpath). z j"])
    show "(\<lambda>\<omega>. z j) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for j
      using paper_pair_class_prob[OF zC] paper_pair_class_sets[OF zC]
      by (simp add: measurable_const space_prob_algebra)
    show "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
  qed
  have kconv: "weak_conv_on (\<lambda>m. z (Nm m \<omega>)) (Kr \<omega>) sequentially ?Y" for \<omega>
  proof -
    have "limitin MC.mtopology (\<lambda>m. z (Nm m \<omega>)) (Kr \<omega>) sequentially"
      by (rule MC.limitin_of_dist_half[OF zC Kc zclose])
    then show ?thesis unfolding Ctop by (simp add: limitin_subtopology)
  qed
  have swc: "weak_conv_on (\<lambda>m. ksemi Q ?MR (\<lambda>\<omega>. z (Nm m \<omega>)))
      (ksemi Q ?MR Kr) sequentially (prod_topology ?X ?Y)"
    by (rule ksemi_weak_conv[OF PQ setsQ second_countable_path_metric
          second_countable_path_metric Kpm Kp]) (rule kconv)
  \<comment> \<open>push forward along the continuous glue\<close>
  have cglue: "continuous_map (prod_topology ?X ?Y)
      (mtopology_of (path_metric T :: ('n pairpath) metric))
      (\<lambda>p. pglue r T (fst p) (snd p))"
    using Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pglue[OF r rT']]
    by simp
  have gconv: "weak_conv_on (\<lambda>m. kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q)
      (kglue_law' r T Kr Q) sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    using weak_conv_on_pushforward[OF cglue swc]
    unfolding kglue_law'_def pair_law_of_def by simp
  \<comment> \<open>weak closedness finishes\<close>
  have pl: "prob_space (kglue_law' r T Kr Q)"
    by (rule prob_space_kglue_law'[OF r rT' PQ setsQ Kp])
  show ?thesis
    by (rule paper_pair_class_weak_closed[OF T0 L0 memm gconv pl]) simp
qed

end
