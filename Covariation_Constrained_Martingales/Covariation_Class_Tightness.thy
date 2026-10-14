section \<open>Tightness and sequential compactness\<close>

(*<*)
theory Covariation_Class_Tightness
  imports
    Covariation_Class_Limits
begin

(*>*)

section \<open>The class is tight\<close>

text \<open>The other consumer of the uniform fourth moment.  The Kolmogorov
  chain in @{theory Continuous_Path_Spaces.Path_Tightness} wants the moment as a Bochner integral, so the
  \<open>nn_integral\<close> bound is first converted; integrability is free, because a
  nonnegative function with a finite \<open>nn_integral\<close> is integrable.\<close>

lemma covariation_class_fourth_moment_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Q: "Q \<in> covariation_class S T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
proof -
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule covariation_class_sets[OF Q])
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
      by (simp add: pow4_nonneg)
    have "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)
        \<le> ennreal (8 * D\<^sup>2 * (tt - s)\<^sup>2)"
      by (rule covariation_class_fourth_moment[OF T B0 B D0 D setsQ Q st stt ttT])
    \<comment> \<open>\<open>\<infinity>\<close> and \<open>\<top>\<close> are DIFFERENT terms on \<open>ennreal\<close> (the former is a
        definition, only simp-identified with the latter), so the \<open>show\<close>
        must use the one the rule states.\<close>
    also have "\<dots> < \<infinity>" by simp
    finally show "(\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q) < \<infinity>" .
  qed
qed

lemma covariation_class_fourth_moment_bochner:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Q: "Q \<in> covariation_class S T x"
    and st: "0 \<le> s" and stt: "s \<le> tt" and ttT: "tt \<le> T"
  shows "(\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q) \<le> 8 * D\<^sup>2 * (tt - s)\<^sup>2"
proof -
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule covariation_class_sets[OF Q])
  have int: "integrable Q (\<lambda>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4)"
    by (rule covariation_class_fourth_moment_integrable[OF T B0 B D0 D Q st stt ttT])
  have C0: "0 \<le> 8 * D\<^sup>2 * (tt - s)\<^sup>2" by (intro mult_nonneg_nonneg) auto
  have "ennreal (\<integral>\<omega>. (fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4 \<partial>Q)
      = (\<integral>\<^sup>+\<omega>. ennreal ((fst (\<omega> tt) $ i - fst (\<omega> s) $ i)^4) \<partial>Q)"
    by (rule nn_integral_eq_integral[symmetric, OF int])
      (simp add: pow4_nonneg)
  also have "\<dots> \<le> ennreal (8 * D\<^sup>2 * (tt - s)\<^sup>2)"
    by (rule covariation_class_fourth_moment[OF T B0 B D0 D setsQ Q st stt ttT])
  finally show ?thesis using C0 by simp
qed


theorem covariation_class_pair_holder_charge:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and ga: "0 < ga" and ga4: "ga < 1/4"
    and Q: "Q \<in> covariation_class S T x"
  shows "measure Q (space Q -
      {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
         \<omega> 0 = (x, 0)
         \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
              norm (\<omega> v - \<omega> u)
                \<le> (real CARD('n) * holder_const ga T n
                    + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)})
    \<le> real CARD('n)
        * (8*D\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga))))"
proof -
  interpret P: prob_space Q by (rule covariation_class_prob[OF Q])
  let ?c = "real CARD('n) * holder_const ga T n"
  let ?K = "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
      \<omega> 0 = (x, 0)
      \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
           norm (\<omega> v - \<omega> u)
             \<le> (?c + B * T powr (1 - ga)) * \<bar>v - u\<bar> powr ga)}"
  have T0: "0 \<le> T" using T by simp
  have ga1: "ga \<le> 1" using ga4 by simp
  have setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    by (rule covariation_class_sets[OF Q])
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have c0: "0 \<le> ?c"
    by (intro mult_nonneg_nonneg holder_const_nonneg[OF ga]) simp
  have cB0: "0 \<le> ?c + B * T powr (1 - ga)"
    using c0 B0 by simp
  \<comment> \<open>the ball is compact, hence closed, hence measurable\<close>
  have compK: "compactin (mtopology_of (path_metric T :: ('n pairpath) metric)) ?K"
    by (rule compactin_path_holder_ball[OF T0 ga cB0])
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
      \<le> 8*D\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga)))" for i
    unfolding Bad_def
    by (intro dyadic_bad_event_tail_mom
          [where X = "\<lambda>u \<omega>. fst (\<omega> u) $ i" and C = D]
        P.prob_space_axioms coordm
        covariation_class_fourth_moment_integrable[OF T B0 B D0 D Q]
        covariation_class_fourth_moment_bochner[OF T B0 B D0 D Q] T0 ga4)
  \<comment> \<open>the almost-sure start-and-Lipschitz event, and a null superset of its
      complement\<close>
  have st: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule covariation_class_start[OF Q])
  have lip: "AE \<omega> in Q. B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    by (rule covariation_class_lipschitz_ae[OF T0 B0 B Q])
  have ae: "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0
      \<and> B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
    using st lip by eventually_elim blast
  obtain N where
    Nsub: "{\<omega> \<in> space Q. \<not> (fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0
        \<and> B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t)))} \<subseteq> N"
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
          \<and> B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))"
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
      have YL: "norm (snd (\<omega> v) - snd (\<omega> u)) \<le> B * \<bar>v - u\<bar>"
        if u: "u \<in> {0..T}" and v: "v \<in> {0..T}" for u v :: real
      proof -
        have lipw: "B-lipschitz_on {0..T} (\<lambda>t. snd (\<omega> t))" using good by blast
        have "dist (snd (\<omega> v)) (snd (\<omega> u)) \<le> B * dist v u"
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
      8*D\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga))))"
    by (intro sum_mono badbnd)
  also have "\<dots> = real CARD('n)
      * (8*D\<^sup>2*T * (2 powr (-(1-4*ga)))^n / (1 - 2 powr (-(1-4*ga))))"
    by simp
  finally show ?thesis .
qed

text \<open>Hence tightness.  The Hoelder exponent may be any \<open>ga < 1/4\<close> --- the
  fourth moment is what caps it --- and \<open>1/8\<close> is taken; the radius is what
  varies with \<open>e\<close>, through the dyadic level \<open>n\<close>, because
  \<open>2 powr (-(1-4\<sqdot>ga)) < 1\<close> makes the charge geometric in \<open>n\<close>.\<close>

theorem covariation_class_tight_on_set:
  fixes \<Gamma> :: "(('n::finite) pairpath) measure set" and x :: "real^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and mem: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> N \<in> covariation_class S T x"
  shows "tight_on_set (mtopology_of (path_metric T :: ('n pairpath) metric)) \<Gamma>"
proof -
  let ?ga = "1/8 :: real"
  let ?q = "2 powr (-(1-4*?ga)) :: real"
  have T0: "0 \<le> T" using T by simp
  have ga0: "0 < ?ga" by simp
  have ga4: "?ga < 1/4" by simp
  have q0: "0 < ?q" by simp
  have q1: "?q < 1" by (rule powr_less_one) (use ga4 in simp_all)
  show ?thesis
  proof (rule tight_on_set_of_holder_charge[OF T0 ga0, where x = "(x, 0)"])
    show "finite_measure N" if "N \<in> \<Gamma>" for N
      using covariation_class_prob[OF mem[OF that]]
      by (simp add: prob_space_def)
    show "sets (path_borel T :: ('n pairpath) measure) = sets N" if "N \<in> \<Gamma>" for N
      by (rule covariation_class_sets[OF mem[OF that], symmetric])
    fix e :: real assume e: "0 < e"
    have lim: "(\<lambda>m :: nat. real CARD('n) * (8*D\<^sup>2*T * ?q^m / (1 - ?q)))
        \<longlonglongrightarrow> real CARD('n) * (8*D\<^sup>2*T * 0 / (1 - ?q))"
      by (intro tendsto_intros LIMSEQ_realpow_zero) (use q0 q1 in auto)
    have lim0: "(\<lambda>m :: nat. real CARD('n) * (8*D\<^sup>2*T * ?q^m / (1 - ?q)))
        \<longlonglongrightarrow> 0"
      using lim by simp
    have ev: "eventually
        (\<lambda>m. real CARD('n) * (8*D\<^sup>2*T * ?q^m / (1 - ?q)) < e) sequentially"
      by (rule order_tendstoD(2)[OF lim0 e])
    obtain n where n: "real CARD('n) * (8*D\<^sup>2*T * ?q^n / (1 - ?q)) < e"
      using ev unfolding eventually_sequentially by blast
    show "\<exists>c. 0 \<le> c \<and> (\<forall>N\<in>\<Gamma>. measure N (space N -
        {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
           \<omega> 0 = (x, 0)
           \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                norm (\<omega> v - \<omega> u) \<le> c * \<bar>v - u\<bar> powr ?ga)}) < e)"
    proof (intro exI[of _ "real CARD('n) * holder_const ?ga T n
          + B * T powr (1 - ?ga)"] conjI ballI)
      show "0 \<le> real CARD('n) * holder_const ?ga T n
          + B * T powr (1 - ?ga)"
        using B0 holder_const_nonneg[OF ga0, of T n] by simp
      fix N :: "('n pairpath) measure" assume NG: "N \<in> \<Gamma>"
      have "measure N (space N -
          {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             \<omega> 0 = (x, 0)
             \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                  norm (\<omega> v - \<omega> u)
                    \<le> (real CARD('n) * holder_const ?ga T n
                        + B * T powr (1 - ?ga))
                      * \<bar>v - u\<bar> powr ?ga)})
          \<le> real CARD('n) * (8*D\<^sup>2*T * ?q^n / (1 - ?q))"
        by (rule covariation_class_pair_holder_charge
            [OF T B0 B D0 D ga0 ga4 mem[OF NG]])
      then show "measure N (space N -
          {\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric).
             \<omega> 0 = (x, 0)
             \<and> (\<forall>u\<in>{0..T}. \<forall>v\<in>{0..T}.
                  norm (\<omega> v - \<omega> u)
                    \<le> (real CARD('n) * holder_const ?ga T n
                        + B * T powr (1 - ?ga))
                      * \<bar>v - u\<bar> powr ?ga)}) < e"
        using n by linarith
    qed
  qed
qed

section \<open>The class is sequentially compact\<close>

text \<open>Sequential compactness of the class: every sequence of
  members has a subsequence converging weakly to a member.  Tightness
  supplies the subsequence, weak convergence keeps the mass
  (@{thm [source] weak_conv_on_prob_space}), and weak closedness supplies
  membership of the limit.\<close>

corollary covariation_class_convergent_subsequence:
  fixes Qm :: "nat \<Rightarrow> ('n::finite pairpath) measure"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and S: "closed S"
    and mem: "\<And>m. Qm m \<in> covariation_class S T x"
  shows "\<exists>a Q. strict_mono a \<and> Q \<in> covariation_class S T x
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
      by (rule covariation_class_tight_on_set[OF T B0 B D0 D]) (use mem in auto)
    fix m :: nat
    show "Qm m (space (Qm m)) \<le> ennreal 1"
      using covariation_class_prob[OF mem]
      by (simp add: prob_space.emeasure_space_1)
  qed
  then obtain a N where sm: "strict_mono a"
    and setsN: "sets N = sets (borel_of ?X)"
    and wcN: "weak_conv_on (Qm \<circ> a) N sequentially ?X"
    by blast
  have memA: "(Qm \<circ> a) m \<in> covariation_class S T x" for m
    by (simp add: mem)
  have probN: "prob_space N"
    by (rule weak_conv_on_prob_space[OF wcN covariation_class_prob[OF memA]])
  have "N \<in> covariation_class S T x"
    by (rule covariation_class_weak_closed[OF T B0 B D0 D S memA wcN probN setsN])
  with sm wcN show ?thesis by blast
qed


(*<*)
end
(*>*)
