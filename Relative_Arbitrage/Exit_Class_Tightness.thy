section \<open>Tightness and sequential compactness\<close>

(*<*)
theory Exit_Class_Tightness
  imports Exit_Class_Limits
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
begin

(*>*)

section \<open>The paper's class is tight\<close>

text \<open>The other consumer of the uniform fourth moment.  The Kolmogorov
  chain in @{theory Continuous_Path_Spaces.Path_Tightness} wants the moment as a Bochner integral, so the
  \<open>nn_integral\<close> bound is first converted; integrability is free, because a
  nonnegative function with a finite \<open>nn_integral\<close> is integrable.\<close>

lemma exit_class_fourth_moment_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
proof -
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF Q])
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
      by (rule exit_class_fourth_moment[OF T L setsQ Q st stt ttT])
    \<comment> \<open>\<open>\<infinity>\<close> and \<open>\<top>\<close> are DIFFERENT terms on \<open>ennreal\<close> (the former is a
        definition, only simp-identified with the latter), so the \<open>show\<close>
        must use the one the rule states.\<close>
    also have "\<dots> < \<infinity>" by simp
    finally show "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q) < \<infinity>" .
  qed
qed

lemma exit_class_fourth_moment_bochner:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and Q: "Q \<in> exit_class k L T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q) \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2"
proof -
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF Q])
  have int: "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
    by (rule exit_class_fourth_moment_integrable[OF T L Q st stt ttT])
  have B0: "0 \<le> 8 * L\<^sup>2 * (tt - s)\<^sup>2" by (intro mult_nonneg_nonneg) auto
  have "ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
      = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)"
    by (rule nn_integral_eq_integral[symmetric, OF int])
      (simp add: zero_le_fourth)
  also have "\<dots> \<le> ennreal (8 * L\<^sup>2 * (tt - s)\<^sup>2)"
    by (rule exit_class_fourth_moment[OF T L setsQ Q st stt ttT])
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

text \<open>The mass a class member puts outside a pair Hoelder ball.  This is
  \<open>Path_Tightness.path_law_holder_ball_bound_vec\<close>'s argument, run natively
  on the pair path space.  Two things stop that theorem from being applied
  off the shelf: its conclusion is about the push-forward \<open>path_law M X T\<close>
  of an abstract process, whereas a class member is already a law on paths;
  and it wants the start condition \<open>X\<^sub>0 = x\<close> pointwise, whereas a class
  member only has it almost surely.  Charging the failure of the
  start-and-Lipschitz event to a null set handles both, and also removes
  the need for the \<open>Y\<close>-event of \<open>pair_holder_charge_split\<close> to be
  measurable, so the split lemma is not needed either.\<close>

theorem exit_class_pair_holder_charge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and ga: "0 < ga" and ga4: "ga < 1/4"
    and Q: "Q \<in> exit_class k L T x"
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
  interpret P: prob_space Q by (rule exit_class_prob[OF Q])
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
    by (rule exit_class_sets[OF Q])
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
        exit_class_fourth_moment_integrable[OF T L Q]
        exit_class_fourth_moment_bochner[OF T L Q] T0 ga4)
  \<comment> \<open>the almost-sure start-and-Lipschitz event, and a null superset of its
      complement\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    using Q unfolding exit_class_def by blast
  have lip: "AE \<omega> in Q. ?B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    by (rule exit_class_lipschitz_ae[OF T0 L Q])
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

text \<open>Hence tightness.  The Hoelder exponent may be any \<open>ga < 1/4\<close> --- the
  fourth moment is what caps it --- and \<open>1/8\<close> is taken; the radius is what
  varies with \<open>e\<close>, through the dyadic level \<open>n\<close>, because
  \<open>2 powr (-(1-4\<sqdot>ga)) < 1\<close> makes the charge geometric in \<open>n\<close>.\<close>

theorem tight_on_set_paper_pair_class:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> N \<in> exit_class k L T x"
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
      using exit_class_prob[OF mem[OF that]]
      by (simp add: prob_space_def)
    show "sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))) = sets N" if "N \<in> \<Gamma>" for N
      by (rule exit_class_sets[OF mem[OF that], symmetric])
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
        by (rule exit_class_pair_holder_charge
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

section \<open>The class is sequentially compact\<close>

text \<open>Tightness gives a convergent subsequence with mass at most one; that
  the limit still has mass one is not automatic, and is where tightness is
  used a second time: a compact set carrying all but \<open>e\<close> of every
  approximating law is closed, so portmanteau keeps at least \<open>1 - e\<close> of the
  mass in the limit, for every \<open>e\<close>.\<close>

theorem exit_class_weak_limit_prob_space:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
    and Q :: "('n pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
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
      interpret Pm: prob_space "Qm m" by (rule exit_class_prob[OF mem])
      have setsm: "sets (Qm m) = sets (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
        by (rule exit_class_sets[OF mem])
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

text \<open>Sequential compactness of the paper's class: every sequence of
  members has a subsequence converging weakly to a member.  Tightness
  supplies the subsequence and the mass, weak closedness supplies
  membership of the limit.\<close>

corollary exit_class_convergent_subsequence:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "0 \<le> L"
    and mem: "\<And>m. Qm m \<in> exit_class k L T x"
  shows "\<exists>a Q. strict_mono a \<and> Q \<in> exit_class k L T x
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
      using exit_class_prob[OF mem]
      by (simp add: prob_space.emeasure_space_1)
  qed
  then obtain a N where sm: "strict_mono a" and finN: "finite_measure N"
    and setsN: "sets N = sets (borel_of ?X)"
    and leN: "N (space N) \<le> ennreal 1"
    and wcN: "weak_conv_on (Qm \<circ> a) N sequentially ?X"
    by blast
  have memA: "(Qm \<circ> a) m \<in> exit_class k L T x" for m
    by (simp add: mem)
  have probN: "prob_space N"
    by (rule exit_class_weak_limit_prob_space
        [OF T L memA wcN finN setsN leN])
  have "N \<in> exit_class k L T x"
    by (rule exit_class_weak_closed[OF T L memA wcN probN setsN])
  with sm wcN show ?thesis by blast
qed


(*<*)
end
(*>*)
