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
          (use st in \<open>auto simp: emeasure_lborel_Icc\<close>)
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
      using measurable_space[OF pdm[of w]] by (auto simp: space_density)
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
      have "\<bar>u y\<bar> \<le> B" using B y by (simp add: topspace_mtopology_of)
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
    using Fc by (simp add: continuous_map_iff_continuous2)
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
      using measurable_space[OF pdm[of w]] by (auto simp: space_density)
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
      have "\<bar>u y\<bar> \<le> B" using B y by (simp add: topspace_mtopology_of)
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

end
