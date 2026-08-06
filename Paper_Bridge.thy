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

end
