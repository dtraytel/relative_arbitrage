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

lemma paper_pair_class_coord_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. fst (\<omega> u) $ i)"
proof (rule martingale_vec_nth)
  show "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0 (\<lambda>u \<omega>. fst (\<omega> u))"
    using Q unfolding paper_pair_class_def by blast
qed

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
  let ?Y = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> u) $ i"
  let ?Z = "\<lambda>\<omega> :: 'n pairpath. h (restrict \<omega> {0..s})"
  have sT: "s \<le> T" using ts tT by simp
  have t0: "0 \<le> t" using st ts by simp
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
  then show ?thesis using eqts by simp
qed

end
