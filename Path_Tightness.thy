section \<open>Tightness of the path laws\<close>

text \<open>
  Plan step A5c (STATUS.md 25h), second half: the laws of processes satisfying
  the uniform fourth-moment package of Eq. (2.7) form a tight family on the
  path space \<open>C({0..T})\<close>. The chain: \<open>dyadic_bad_event_tail_mom\<close>
  (Modulus\_Tails) bounds the probability that some dyadic increment at some
  level \<open>j \<ge> n\<close> is large; on the complement, \<open>modulus_of_good_path\<close> plus
  \<open>holder_of_dyadic_moduli\<close> (Holder\_Interpolation) place the path in an
  explicit H\"older ball, which \<open>compactin_path_holder_ball\<close> (Path\_Space)
  makes compact. Large levels \<open>n\<close> make the exceptional mass small, uniformly
  over the family — which is exactly \<open>tight_on_set\<close>, the hypothesis of the
  AFP's \<open>Prokhorov_theorem_LP\<close>.
\<close>

theory Path_Tightness
  imports Path_Space Holder_Interpolation
begin

subsection \<open>Measurability of the bad event\<close>

lemma dyadic_bad_event_sets:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
  shows "{\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
            2 powr (-\<gamma>*real j)
              \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
         \<in> sets M"
proof -
  define E where "E j = {\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}" for j
  have Esets: "E j \<in> sets M" for j
  proof -
    have "{\<omega> \<in> space M. 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>} \<in> sets M"
      if k: "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    proof -
      have "0 \<le> real_of_int (k - 1) / 2^j" "0 \<le> real_of_int k / 2^j"
        using k by simp_all
      from Xm[OF this(1)] Xm[OF this(2)] show ?thesis by measurable
    qed
    moreover have "E j = (\<Union>k\<in>{1..\<lfloor>2^j * T\<rfloor>}. {\<omega> \<in> space M. 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>})"
      unfolding E_def by auto
    ultimately show ?thesis
      by (metis (lifting) countable_Un_Int(1))
  qed
  have s1: "{\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
      = (\<Union>j\<in>{n..}. E j)"
    unfolding E_def by auto
  show ?thesis unfolding s1
    by (intro sets.countable_UN'' Esets countableI_type)
qed

subsection \<open>Good dyadics put the path in an explicit H\"older ball\<close>

lemma powr_neg_lt_1:
  assumes g0: "0 < \<gamma>"
  shows "2 powr (-\<gamma>) < (1::real)"
proof -
  have "(-\<gamma>) < 0" using g0 by simp
  hence "2 powr (-\<gamma>) < 2 powr 0" by (intro powr_less_mono) simp_all
  thus ?thesis by simp
qed

text \<open>
  The H\"older constant produced by the level-\<open>n\<close> modulus: explicit in
  \<open>(\<gamma>, T, n)\<close> only, so the resulting compact ball is COMMON to every law
  satisfying the moment package.
\<close>

definition holder_const :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "holder_const \<gamma> T n =
     3 / (1 - 2 powr (-\<gamma>)) * 2 powr \<gamma>
     + 2 * (3 / (1 - 2 powr (-\<gamma>))) * 2 ^ n * 2 powr (-\<gamma> * real n)
       * max 1 (T powr (1 - \<gamma>))"

lemma holder_const_nonneg:
  assumes g0: "0 < \<gamma>"
  shows "0 \<le> holder_const \<gamma> T n"
proof -
  have pos: "0 < 1 - 2 powr (-\<gamma>)" using powr_neg_lt_1[OF g0] by simp
  have E0: "0 \<le> 3 / (1 - 2 powr (-\<gamma>))" using pos by simp
  show ?thesis unfolding holder_const_def
    by (intro add_nonneg_nonneg mult_nonneg_nonneg E0) simp_all
qed

lemma holder_of_good_dyadics:
  fixes f :: "real \<Rightarrow> real" and \<gamma> T :: real and n :: nat
  assumes T: "0 \<le> T" and g0: "0 < \<gamma>" and g1: "\<gamma> \<le> 1"
    and cont: "continuous_on {0..T} f"
    and good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
        \<bar>f (real_of_int k / 2^j) - f (real_of_int (k - 1) / 2^j)\<bar> \<le> 2 powr (-\<gamma>*real j)"
    and u: "u \<in> {0..T}" and v: "v \<in> {0..T}"
  shows "\<bar>f u - f v\<bar> \<le> holder_const \<gamma> T n * \<bar>u - v\<bar> powr \<gamma>"
proof -
  define E where "E = 3 / (1 - 2 powr (-\<gamma>))"
  have pos: "0 < 1 - 2 powr (-\<gamma>)" using powr_neg_lt_1[OF g0] by simp
  have E0: "0 \<le> E" unfolding E_def using pos by simp
  have H: "\<bar>f u' - f v'\<bar> \<le> E * 2 powr (- \<gamma> * real m)"
    if m: "n \<le> m" and u': "u' \<in> {0..T}" and v': "v' \<in> {0..T}"
      and gap: "\<bar>u' - v'\<bar> < 1 / 2 ^ m" for m and u' v' :: real
  proof -
    have goodm: "\<bar>f (real_of_int k / 2^j) - f (real_of_int (k - 1) / 2^j)\<bar>
        \<le> 2 powr (-\<gamma>*real j)" if "m \<le> j" "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
      by (rule good[OF order.trans[OF m that(1)] that(2)])
    have "\<bar>f u' - f v'\<bar> \<le> 3 * 2 powr (-\<gamma>*real m) / (1 - 2 powr (-\<gamma>))"
      by (rule modulus_of_good_path[OF cont goodm g0 u' v' gap])
    also have "\<dots> = E * 2 powr (- \<gamma> * real m)"
      unfolding E_def by simp
    finally show ?thesis .
  qed
  have "\<bar>f u - f v\<bar>
      \<le> (E * 2 powr \<gamma>
          + 2 * E * 2 ^ n * 2 powr (- \<gamma> * real n) * max 1 (T powr (1 - \<gamma>)))
        * \<bar>u - v\<bar> powr \<gamma>"
    by (rule holder_of_dyadic_moduli[OF T g0 g1 E0 H u v])
  thus ?thesis unfolding holder_const_def E_def .
qed

subsection \<open>The per-law bound: mass outside the H\"older ball\<close>

theorem path_law_holder_ball_bound:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and M :: "'a measure" and T C \<gamma> x :: real and n :: nat
  assumes P: "prob_space M"
    and T0: "0 \<le> T"
    and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
    and start: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> X 0 \<omega> = x"
    and int4: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
    and mom: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "measure (path_law M X T)
      (space (path_law M X T)
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> real) metric).
             f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
               norm (f t - f s) \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)})
    \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))"
proof -
  interpret P: prob_space M by (rule P)
  let ?PS = "borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
  define K where "K = {f \<in> mspace (path_metric T :: (real \<Rightarrow> real) metric).
      f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
        norm (f t - f s) \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)}"
  define pf where "pf = (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})"
  have g1': "\<gamma> \<le> 1" using g2 by linarith
  have Xm': "X t \<in> borel_measurable M" if "t \<in> {0..T}" for t
    using that by (intro Xm) simp
  have pfm: "pf \<in> M \<rightarrow>\<^sub>M ?PS"
    unfolding pf_def by (rule pathify_measurable[OF T0 Xm' cont])
  have cK: "compactin (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)) K"
    unfolding K_def
    by (rule compactin_path_holder_ball[OF T0 g0 holder_const_nonneg[OF g0]])
  have haus: "Hausdorff_space (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.Hausdorff_space_mtopology[OF Metric_space_mspace_mdist])
  have Ksets: "K \<in> sets ?PS"
    by (rule borel_of_closed[OF compactin_imp_closedin[OF haus cK]])
  have KD: "space ?PS - K \<in> sets ?PS"
    by (rule sets.compl_sets[OF Ksets])
  have spN: "space (path_law M X T) = space ?PS"
    unfolding path_law_def by simp
  define Bad where "Bad = {\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}"
  have BadS: "Bad \<in> sets M"
    unfolding Bad_def by (rule dyadic_bad_event_sets[OF Xm])
  have sub: "pf -` (space ?PS - K) \<inter> space M \<subseteq> Bad"
  proof
    fix \<omega> assume A: "\<omega> \<in> pf -` (space ?PS - K) \<inter> space M"
    have w: "\<omega> \<in> space M" using A by blast
    have notK: "pf \<omega> \<notin> K" using A by blast
    show "\<omega> \<in> Bad"
    proof (rule ccontr)
      assume nB: "\<omega> \<notin> Bad"
      have good: "\<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
        if jk: "n \<le> j" "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
      proof -
        have "\<not> 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>"
          using nB w jk unfolding Bad_def by blast
        thus ?thesis by linarith
      qed
      have k0: "0 \<le> real_of_int (k - 1) / 2^j" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
        using that by simp
      have kk: "real_of_int (k - 1) / 2^j \<le> real_of_int k / 2^j" for j k
        by (intro divide_right_mono) simp_all
      have kT: "real_of_int k / 2^j \<le> T" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
      proof -
        from that have "real_of_int k \<le> real_of_int \<lfloor>2^j * T\<rfloor>" by simp
        also have "\<dots> \<le> 2^j * T" by (rule of_int_floor_le)
        finally show ?thesis by (simp add: field_simps)
      qed
      have m1: "real_of_int k / 2^j \<in> {0..T}" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
        using k0[OF that] kk[of k j] kT[OF that] by auto
      have m2: "real_of_int (k - 1) / 2^j \<in> {0..T}" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
        using k0[OF that] kk[of k j] kT[OF that] by auto
      have contf: "continuous_on {0..T} (pf \<omega>)"
        unfolding pf_def
        by (rule continuous_on_cong[OF refl, THEN iffD2, OF _ cont[OF w]]) simp
      have f0: "pf \<omega> 0 = x"
        unfolding pf_def using T0 start[OF w] by simp
      have goodf: "\<bar>pf \<omega> (real_of_int k / 2^j) - pf \<omega> (real_of_int (k - 1) / 2^j)\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
        if jk: "n \<le> j" "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
        using good[OF jk] m1[OF jk(2)] m2[OF jk(2)] unfolding pf_def by simp
      have holderf: "norm (pf \<omega> t - pf \<omega> s)
          \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>"
        if s: "s \<in> {0..T}" and t: "t \<in> {0..T}" for s t
      proof -
        have "\<bar>pf \<omega> t - pf \<omega> s\<bar> \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>"
          by (rule holder_of_good_dyadics[OF T0 g0 g1' contf goodf t s])
        thus ?thesis by simp
      qed
      have pfin: "pf \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real) metric)"
        unfolding pf_def by (rule mspace_path_metricI[OF cont[OF w]])
      have inK: "pf \<omega> \<in> K"
        unfolding K_def using pfin f0 holderf by auto
      with notK show False by contradiction
    qed
  qed
  have pl: "path_law M X T = distr M ?PS pf"
    unfolding path_law_def pf_def by (rule refl)
  have "measure (path_law M X T) (space (path_law M X T) - K)
      = measure (distr M ?PS pf) (space ?PS - K)"
    unfolding pl by simp
  also have "\<dots> = measure M (pf -` (space ?PS - K) \<inter> space M)"
    by (rule measure_distr[OF pfm KD])
  also have "\<dots> \<le> measure M Bad"
    by (rule P.finite_measure_mono[OF sub BadS])
  also have "\<dots> \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))"
    unfolding Bad_def
    by (rule dyadic_bad_event_tail_mom[OF P Xm int4 mom T0 g2])
  finally have res: "measure (path_law M X T) (space (path_law M X T) - K)
      \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))" .
  show ?thesis by (rule res[unfolded K_def])
qed

subsection \<open>Tightness of a family of path laws\<close>

theorem tight_on_set_path_laws:
  fixes MM :: "'i \<Rightarrow> 'a measure" and XX :: "'i \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
    and I :: "'i set" and T C \<gamma> x :: real
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. i \<in> I \<Longrightarrow> prob_space (MM i)"
    and Xm: "\<And>i u. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<omega> \<in> space (MM i) \<Longrightarrow>
        continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i u v. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> - XX i u \<omega>)^4)"
    and mom: "\<And>i u v. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> - XX i u \<omega>)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))
      ((\<lambda>i. path_law (MM i) (XX i) T) ` I)"
proof -
  have part1: "\<forall>N\<in>(\<lambda>i. path_law (MM i) (XX i) T) ` I.
      finite_measure N
      \<and> sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)))
        = sets N"
  proof
    fix N assume "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I"
    then obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T" by blast
    have Xm': "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
      using that by (intro Xm[OF i]) simp
    have PN: "prob_space N"
      unfolding Ni by (rule prob_space_path_law[OF P[OF i] T0 Xm' cont[OF i]])
    have fN: "finite_measure N" by (rule prob_space.axioms(1)[OF PN])
    have sN: "sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)))
        = sets N"
      unfolding Ni by (rule sets_path_law[symmetric])
    show "finite_measure N
        \<and> sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)))
          = sets N"
      using fN sN by blast
  qed
  have part2: "\<exists>K. compactin (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)) K
      \<and> (\<forall>N\<in>(\<lambda>i. path_law (MM i) (XX i) T) ` I. measure N (space N - K) < e)"
    if e: "0 < e" for e :: real
  proof -
    define q where "q = 2 powr (-(1-4*\<gamma>))"
    have q0: "0 \<le> q" unfolding q_def by simp
    have q1: "q < 1" unfolding q_def by (rule powr_ratio_lt_1[OF g2])
    have lim: "(\<lambda>n. 8*C\<^sup>2*T * q^n / (1 - q)) \<longlonglongrightarrow> 0"
    proof -
      have e1: "(\<lambda>n. q^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero[OF q0 q1])
      have e2: "(\<lambda>n. (8*C\<^sup>2*T/(1 - q)) * q^n) \<longlonglongrightarrow> 0"
        by (rule tendsto_mult_right_zero[OF e1])
      have e3: "(8*C\<^sup>2*T/(1 - q)) * q^n = 8*C\<^sup>2*T * q^n / (1 - q)" for n
        by simp
      show ?thesis using e2 unfolding e3 .
    qed
    obtain n where nn: "8*C\<^sup>2*T * q^n / (1 - q) < e"
      using order_tendstoD(2)[OF lim e] by (auto simp: eventually_sequentially)
    define K where "K = {f \<in> mspace (path_metric T :: (real \<Rightarrow> real) metric).
        f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
          norm (f t - f s) \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)}"
    have cK: "compactin (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)) K"
      unfolding K_def
      by (rule compactin_path_holder_ball[OF T0 g0 holder_const_nonneg[OF g0]])
    have bnd: "measure N (space N - K) < e"
      if N: "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I" for N
    proof -
      obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T"
        using N by blast
      have "measure N (space N - K) \<le> 8*C\<^sup>2*T * q^n / (1 - q)"
        unfolding Ni K_def q_def
        by (rule path_law_holder_ball_bound[OF P[OF i] T0 g0 g2 Xm[OF i]
              cont[OF i] start[OF i] int4[OF i] mom[OF i]])
      with nn show ?thesis by linarith
    qed
    show ?thesis using cK bnd by blast
  qed
  show ?thesis
    unfolding tight_on_set_def using part1 part2 by blast
qed

subsection \<open>The subsequence extraction of Lemma 2.2, per horizon\<close>

text \<open>
  Combining the tightness theorem with the AFP's
  \<open>tight_on_set_imp_convergent_subsequence\<close>: every sequence of laws whose
  processes satisfy the uniform Eq. (2.7) package has a weakly convergent
  subsequence on \<open>C({0..T})\<close>. This is the relative-compactness content of
  Lemma 2.2 at a fixed horizon; the \<open>C([0,\<infinity>))\<close> statement is the remaining
  architecture step (STATUS.md 25h, A5d).
\<close>

corollary path_laws_convergent_subsequence:
  fixes MM :: "nat \<Rightarrow> 'a measure" and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
    and T C \<gamma> x :: real
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> - XX i u \<omega>)^4)"
    and mom: "\<And>i u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> - XX i u \<omega>)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
proof (rule tight_on_set_imp_convergent_subsequence)
  show "metrizable_space (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  show "separable_space (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
    by (rule separable_path_metric)
  show "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))
      (range (\<lambda>i. path_law (MM i) (XX i) T))"
    by (intro tight_on_set_path_laws[OF T0 g0 g2, where x = x and C = C]
          P Xm cont start int4 mom)
  fix i :: nat
  have Xm': "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
    using that by (intro Xm) simp
  have "prob_space (path_law (MM i) (XX i) T)"
    by (rule prob_space_path_law[OF P T0 Xm' cont])
  thus "path_law (MM i) (XX i) T (space (path_law (MM i) (XX i) T)) \<le> ennreal 1"
    by (simp add: prob_space.emeasure_space_1)
qed

subsection \<open>The vector-valued layer\<close>

text \<open>
  The paper's paths are \<open>R^n\<close>-valued while the moment machinery above is
  real-valued; this layer closes the gap by working per coordinate. The bad
  event is the union of the coordinate bad events (a factor \<open>CARD('m)\<close> in the
  probability by the union bound), and on its complement every coordinate is
  H\"older, so the vector path is H\"older with constant
  \<open>CARD('m) * holder_const \<gamma> T n\<close> via \<open>norm_le_l1_cart\<close>. The compact ball
  comes from \<open>compactin_path_holder_ball\<close> at \<open>'b = real^'m\<close>.
\<close>

theorem path_law_holder_ball_bound_vec:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'m::finite" and M :: "'a measure" and T C \<gamma> :: real
    and x :: "real^'m" and n :: nat
  assumes P: "prob_space M"
    and T0: "0 \<le> T"
    and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
    and start: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> X 0 \<omega> = x"
    and int4: "\<And>i u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable M (\<lambda>\<omega>. (X v \<omega> $ i - X u \<omega> $ i)^4)"
    and mom: "\<And>i u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (X v \<omega> $ i - X u \<omega> $ i)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "measure (path_law M X T)
      (space (path_law M X T)
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric).
             f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
               norm (f t - f s)
                 \<le> real CARD('m) * holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)})
    \<le> real CARD('m)
        * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
proof -
  interpret P: prob_space M by (rule P)
  let ?PS = "borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
  define c where "c = real CARD('m) * holder_const \<gamma> T n"
  define K where "K = {f \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric).
      f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
        norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr \<gamma>)}"
  define pf where "pf = (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})"
  have g1': "\<gamma> \<le> 1" using g2 by linarith
  have c0: "0 \<le> c"
    unfolding c_def
    by (intro mult_nonneg_nonneg holder_const_nonneg[OF g0]) simp
  have Xmi: "(\<lambda>\<omega>. X u \<omega> $ i) \<in> borel_measurable M" if "0 \<le> u" for u i
    by (rule measurable_compose[OF Xm[OF that] borel_measurable_nth])
  have Xm': "X t \<in> borel_measurable M" if "t \<in> {0..T}" for t
    using that by (intro Xm) simp
  have pfm: "pf \<in> M \<rightarrow>\<^sub>M ?PS"
    unfolding pf_def by (rule pathify_measurable[OF T0 Xm' cont])
  have cK: "compactin (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)) K"
    unfolding K_def by (rule compactin_path_holder_ball[OF T0 g0 c0])
  have haus: "Hausdorff_space (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.Hausdorff_space_mtopology[OF Metric_space_mspace_mdist])
  have Ksets: "K \<in> sets ?PS"
    by (rule borel_of_closed[OF compactin_imp_closedin[OF haus cK]])
  have KD: "space ?PS - K \<in> sets ?PS"
    by (rule sets.compl_sets[OF Ksets])
  have spN: "space (path_law M X T) = space ?PS"
    unfolding path_law_def by simp
  define Bad where "Bad = (\<lambda>i. {\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> $ i - X (real_of_int (k - 1) / 2^j) \<omega> $ i\<bar>})"
  have BadS: "Bad i \<in> sets M" for i
    unfolding Bad_def
    by (intro dyadic_bad_event_sets[where X = "\<lambda>u \<omega>. X u \<omega> $ i"] Xmi)
  have sub: "pf -` (space ?PS - K) \<inter> space M \<subseteq> (\<Union>i\<in>UNIV. Bad i)"
  proof
    fix \<omega> assume A: "\<omega> \<in> pf -` (space ?PS - K) \<inter> space M"
    have w: "\<omega> \<in> space M" using A by blast
    have notK: "pf \<omega> \<notin> K" using A by blast
    show "\<omega> \<in> (\<Union>i\<in>UNIV. Bad i)"
    proof (rule ccontr)
      assume nB: "\<omega> \<notin> (\<Union>i\<in>UNIV. Bad i)"
      have nBi: "\<omega> \<notin> Bad i" for i using nB by blast
      have good: "\<bar>X (real_of_int k / 2^j) \<omega> $ i - X (real_of_int (k - 1) / 2^j) \<omega> $ i\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
        if jk: "n \<le> j" "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for i j k
      proof -
        have "\<not> 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> $ i - X (real_of_int (k - 1) / 2^j) \<omega> $ i\<bar>"
          using nBi[of i] w jk unfolding Bad_def by blast
        thus ?thesis by linarith
      qed
      have coordH: "\<bar>X t \<omega> $ i - X s \<omega> $ i\<bar> \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>"
        if s: "s \<in> {0..T}" and t: "t \<in> {0..T}" for i and s t :: real
      proof -
        have c1: "continuous_on {0..T} (\<lambda>t. X t \<omega> $ i)"
          by (rule continuous_on_component[OF cont[OF w]])
        have gi: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
            \<bar>X (real_of_int k / 2^j) \<omega> $ i - X (real_of_int (k - 1) / 2^j) \<omega> $ i\<bar>
              \<le> 2 powr (-\<gamma>*real j)"
          by (rule good)
        show ?thesis
          by (rule holder_of_good_dyadics[OF T0 g0 g1' c1 gi t s])
      qed
      have vecH: "norm (pf \<omega> t - pf \<omega> s) \<le> c * \<bar>t - s\<bar> powr \<gamma>"
        if s: "s \<in> {0..T}" and t: "t \<in> {0..T}" for s t
      proof -
        have pft: "pf \<omega> t = X t \<omega>" unfolding pf_def using t by simp
        have pfs: "pf \<omega> s = X s \<omega>" unfolding pf_def using s by simp
        have "norm (X t \<omega> - X s \<omega>) \<le> (\<Sum>i\<in>UNIV. \<bar>(X t \<omega> - X s \<omega>) $ i\<bar>)"
          by (rule norm_le_l1_cart)
        also have "\<dots> = (\<Sum>i\<in>UNIV. \<bar>X t \<omega> $ i - X s \<omega> $ i\<bar>)"
          by simp
        also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'m set). holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)"
          by (intro sum_mono coordH[OF s t])
        also have "\<dots> = c * \<bar>t - s\<bar> powr \<gamma>"
          unfolding c_def by simp
        finally show ?thesis unfolding pft pfs .
      qed
      have f0: "pf \<omega> 0 = x"
        unfolding pf_def using T0 start[OF w] by simp
      have pfin: "pf \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric)"
        unfolding pf_def by (rule mspace_path_metricI[OF cont[OF w]])
      have inK: "pf \<omega> \<in> K"
        unfolding K_def using pfin f0 vecH by auto
      with notK show False by contradiction
    qed
  qed
  have UB: "(\<Union>i\<in>UNIV. Bad i) \<in> sets M"
    by (intro sets.countable_UN'' BadS countableI_type)
  have bnd_i: "measure M (Bad i)
      \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))" for i
    unfolding Bad_def
    by (intro dyadic_bad_event_tail_mom[where X = "\<lambda>u \<omega>. X u \<omega> $ i" and C = C]
          P Xmi int4 mom T0 g2)
  have "measure M (\<Union>i\<in>UNIV. Bad i) \<le> (\<Sum>i\<in>(UNIV::'m set). measure M (Bad i))"
    by (rule P.finite_measure_subadditive_finite) (auto intro: BadS)
  also have "\<dots> \<le> (\<Sum>i\<in>(UNIV::'m set).
      8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
    by (intro sum_mono bnd_i)
  also have "\<dots> = real CARD('m)
      * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
    by simp
  finally have Ubnd: "measure M (\<Union>i\<in>UNIV. Bad i)
      \<le> real CARD('m)
        * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))" .
  have pl: "path_law M X T = distr M ?PS pf"
    unfolding path_law_def pf_def by (rule refl)
  have "measure (path_law M X T) (space (path_law M X T) - K)
      = measure (distr M ?PS pf) (space ?PS - K)"
    unfolding pl by simp
  also have "\<dots> = measure M (pf -` (space ?PS - K) \<inter> space M)"
    by (rule measure_distr[OF pfm KD])
  also have "\<dots> \<le> measure M (\<Union>i\<in>UNIV. Bad i)"
    by (rule P.finite_measure_mono[OF sub UB])
  also have "\<dots> \<le> real CARD('m)
      * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
    by (rule Ubnd)
  finally have res: "measure (path_law M X T) (space (path_law M X T) - K)
      \<le> real CARD('m)
        * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))" .
  show ?thesis by (rule res[unfolded K_def c_def])
qed

theorem tight_on_set_path_laws_vec:
  fixes MM :: "'i \<Rightarrow> 'a measure" and XX :: "'i \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and I :: "'i set" and T C \<gamma> :: real and x :: "real^'m"
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. i \<in> I \<Longrightarrow> prob_space (MM i)"
    and Xm: "\<And>i u. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<omega> \<in> space (MM i) \<Longrightarrow>
        continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i l u v. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    and mom: "\<And>i l u v. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      ((\<lambda>i. path_law (MM i) (XX i) T) ` I)"
proof -
  have part1: "\<forall>N\<in>(\<lambda>i. path_law (MM i) (XX i) T) ` I.
      finite_measure N
      \<and> sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
        = sets N"
  proof
    fix N assume "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I"
    then obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T" by blast
    have Xm': "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
      using that by (intro Xm[OF i]) simp
    have PN: "prob_space N"
      unfolding Ni by (rule prob_space_path_law[OF P[OF i] T0 Xm' cont[OF i]])
    have fN: "finite_measure N" by (rule prob_space.axioms(1)[OF PN])
    have sN: "sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
        = sets N"
      unfolding Ni by (rule sets_path_law[symmetric])
    show "finite_measure N
        \<and> sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
          = sets N"
      using fN sN by blast
  qed
  have part2: "\<exists>K. compactin (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)) K
      \<and> (\<forall>N\<in>(\<lambda>i. path_law (MM i) (XX i) T) ` I. measure N (space N - K) < e)"
    if e: "0 < e" for e :: real
  proof -
    define q where "q = 2 powr (-(1-4*\<gamma>))"
    have q0: "0 \<le> q" unfolding q_def by simp
    have q1: "q < 1" unfolding q_def by (rule powr_ratio_lt_1[OF g2])
    have lim: "(\<lambda>n. real CARD('m) * (8*C\<^sup>2*T * q^n / (1 - q))) \<longlonglongrightarrow> 0"
    proof -
      have e1: "(\<lambda>n. q^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero[OF q0 q1])
      have e2: "(\<lambda>n. (8*C\<^sup>2*T/(1 - q)) * q^n) \<longlonglongrightarrow> 0"
        by (rule tendsto_mult_right_zero[OF e1])
      have e3: "(8*C\<^sup>2*T/(1 - q)) * q^n = 8*C\<^sup>2*T * q^n / (1 - q)" for n
        by simp
      have e4: "(\<lambda>n. 8*C\<^sup>2*T * q^n / (1 - q)) \<longlonglongrightarrow> 0"
        using e2 unfolding e3 .
      show ?thesis by (rule tendsto_mult_right_zero[OF e4])
    qed
    obtain n where nn: "real CARD('m) * (8*C\<^sup>2*T * q^n / (1 - q)) < e"
      using order_tendstoD(2)[OF lim e] by (auto simp: eventually_sequentially)
    define K where "K = {f \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric).
        f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
          norm (f t - f s)
            \<le> real CARD('m) * holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)}"
    have c0: "0 \<le> real CARD('m) * holder_const \<gamma> T n"
      by (intro mult_nonneg_nonneg holder_const_nonneg[OF g0]) simp
    have cK: "compactin (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)) K"
      unfolding K_def by (rule compactin_path_holder_ball[OF T0 g0 c0])
    have bnd: "measure N (space N - K) < e"
      if N: "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I" for N
    proof -
      obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T"
        using N by blast
      have "measure N (space N - K) \<le> real CARD('m) * (8*C\<^sup>2*T * q^n / (1 - q))"
        unfolding Ni K_def q_def
        by (rule path_law_holder_ball_bound_vec[OF P[OF i] T0 g0 g2 Xm[OF i]
              cont[OF i] start[OF i] int4[OF i] mom[OF i]])
      with nn show ?thesis by linarith
    qed
    show ?thesis using cK bnd by blast
  qed
  show ?thesis
    unfolding tight_on_set_def using part1 part2 by blast
qed

corollary path_laws_convergent_subsequence_vec:
  fixes MM :: "nat \<Rightarrow> 'a measure" and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and T C \<gamma> :: real and x :: "real^'m"
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    and mom: "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
proof (rule tight_on_set_imp_convergent_subsequence)
  show "metrizable_space (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  show "separable_space (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by (rule separable_path_metric)
  show "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      (range (\<lambda>i. path_law (MM i) (XX i) T))"
    by (intro tight_on_set_path_laws_vec[OF T0 g0 g2, where x = x and C = C]
          P Xm cont start int4 mom)
  fix i :: nat
  have Xm': "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
    using that by (intro Xm) simp
  have "prob_space (path_law (MM i) (XX i) T)"
    by (rule prob_space_path_law[OF P T0 Xm' cont])
  thus "path_law (MM i) (XX i) T (space (path_law (MM i) (XX i) T)) \<le> ennreal 1"
    by (simp add: prob_space.emeasure_space_1)
qed

subsection \<open>The diagonal extraction over integer horizons\<close>

text \<open>
  Step (ii) of the A5d plan (STATUS.md 25m): from a horizon-uniform moment
  package, ONE subsequence along which the path laws converge weakly at EVERY
  integer horizon simultaneously. Built on HOL-Library's
  \<open>Diagonal_Subsequence\<close> (locale \<open>subseqs\<close>, reachable through
  HOL-Probability); subsequence-stability of weak convergence is
  \<open>limitin_subsequence\<close>, and the tail shift is absorbed by
  \<open>limitin_sequentially_offset_rev\<close>.
\<close>

theorem path_laws_diagonal_subsequence:
  fixes MM :: "nat \<Rightarrow> 'a measure" and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and C \<gamma> :: real and x :: "real^'m"
  assumes g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    and mom: "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "\<exists>a. strict_mono a \<and> (\<forall>m::nat. \<exists>N.
      finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) N sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
proof -
  define Q where "Q = (\<lambda>(m::nat) (s::nat \<Rightarrow> nat). \<exists>N.
      finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> s) N sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
  have ex: "\<exists>r'. strict_mono r' \<and> Q m (s \<circ> r')"
    if s: "strict_mono s" for m and s :: "nat \<Rightarrow> nat"
  proof -
    have inst: "\<exists>a N. strict_mono a \<and> finite_measure N
        \<and> sets N = sets (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
        \<and> N (space N) \<le> ennreal 1
        \<and> weak_conv_on ((\<lambda>i. path_law (MM (s i)) (XX (s i)) (real m)) \<circ> a) N
            sequentially
            (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
    proof (rule path_laws_convergent_subsequence_vec[where x = x and C = C])
      show "0 \<le> real m" by simp
      show "0 < \<gamma>" by (rule g0)
      show "\<gamma> < 1/4" by (rule g2)
      show "\<And>i. prob_space (MM (s i))" by (rule P)
      show "\<And>i u. 0 \<le> u \<Longrightarrow> XX (s i) u \<in> borel_measurable (MM (s i))"
        by (rule Xm)
      show "continuous_on {0..real m} (\<lambda>t. XX (s i) t \<omega>)"
        if "\<omega> \<in> space (MM (s i))" for i \<omega>
        by (rule continuous_on_subset[OF cont[OF that]]) auto
      show "\<And>i \<omega>. \<omega> \<in> space (MM (s i)) \<Longrightarrow> XX (s i) 0 \<omega> = x" by (rule start)
      show "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> real m \<Longrightarrow>
          integrable (MM (s i)) (\<lambda>\<omega>. (XX (s i) v \<omega> $ l - XX (s i) u \<omega> $ l)^4)"
        by (rule int4)
      show "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> real m \<Longrightarrow>
          (\<integral>\<omega>. (XX (s i) v \<omega> $ l - XX (s i) u \<omega> $ l)^4 \<partial>(MM (s i)))
            \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
        by (rule mom)
    qed
    then obtain a N where a: "strict_mono a" and N1: "finite_measure N"
      and N2: "sets N = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
      and N3: "N (space N) \<le> ennreal 1"
      and N4: "weak_conv_on ((\<lambda>i. path_law (MM (s i)) (XX (s i)) (real m)) \<circ> a) N
          sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      by blast
    have eq: "(\<lambda>i. path_law (MM (s i)) (XX (s i)) (real m)) \<circ> a
        = (\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> (s \<circ> a)"
      by (simp add: o_def)
    have "Q m (s \<circ> a)"
      unfolding Q_def using N1 N2 N3 N4[unfolded eq] by blast
    thus ?thesis using a by blast
  qed
  interpret S: subseqs Q
    by unfold_locales (rule ex)
  have stable: "Q n (v \<circ> r)"
    if r: "strict_mono r" and Qv: "Q n v" for r v :: "nat \<Rightarrow> nat" and n
  proof -
    from Qv obtain N where N1: "finite_measure N"
      and N2: "sets N = sets (borel_of (mtopology_of
          (path_metric (real n) :: (real \<Rightarrow> real^'m) metric)))"
      and N3: "N (space N) \<le> ennreal 1"
      and N4: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real n)) \<circ> v) N
          sequentially
          (mtopology_of (path_metric (real n) :: (real \<Rightarrow> real^'m) metric))"
      unfolding Q_def by blast
    have "weak_conv_on (((\<lambda>i. path_law (MM i) (XX i) (real n)) \<circ> v) \<circ> r) N
        sequentially
        (mtopology_of (path_metric (real n) :: (real \<Rightarrow> real^'m) metric))"
      by (rule limitin_subsequence[OF r N4])
    hence N4': "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real n)) \<circ> (v \<circ> r)) N
        sequentially
        (mtopology_of (path_metric (real n) :: (real \<Rightarrow> real^'m) metric))"
      by (simp add: o_def)
    show ?thesis unfolding Q_def using N1 N2 N3 N4' by blast
  qed
  have final: "\<exists>N. finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> S.diagseq) N
          sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))" for m
  proof -
    have "Q m (S.diagseq \<circ> ((+) (Suc m)))"
      by (rule S.diagseq_holds) (rule stable)
    then obtain N where N1: "finite_measure N"
      and N2: "sets N = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
      and N3: "N (space N) \<le> ennreal 1"
      and N4: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m))
            \<circ> (S.diagseq \<circ> ((+) (Suc m)))) N sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      unfolding Q_def by blast
    have eq: "((\<lambda>i. path_law (MM i) (XX i) (real m))
          \<circ> (S.diagseq \<circ> ((+) (Suc m))))
        = (\<lambda>i. ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> S.diagseq) (i + Suc m))"
      by (simp add: o_def add.commute)
    have N4': "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> S.diagseq) N
        sequentially
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      by (rule limitin_sequentially_offset_rev[OF N4[unfolded eq]])
    show ?thesis using N1 N2 N3 N4' by blast
  qed
  show ?thesis using S.subseq_diagseq final by blast
qed

subsection \<open>Consistency of the diagonal limits across horizons\<close>

text \<open>
  The per-horizon limit laws of the diagonal subsequence form a PROJECTIVE
  family: restricting the horizon-\<open>m'\<close> limit to \<open>{0..m}\<close> gives the
  horizon-\<open>m\<close> limit. Proof: the restriction map is continuous
  (\<open>Lipschitz_restrict_path_metric\<close>), so \<open>weak_conv_on_pushforward\<close> sends
  the horizon-\<open>m'\<close> convergence to convergence of the restricted laws, which
  by \<open>path_law_restrict\<close> ARE the horizon-\<open>m\<close> laws; uniqueness of weak limits
  (the weak topology is metrizable by \<open>metrizable_weak_conv_topology\<close>, hence
  Hausdorff) identifies the two candidate limits. This is the input for the
  projective-limit assembly (step (iii) of STATUS.md 25m).
\<close>

theorem path_laws_diagonal_consistent:
  fixes MM :: "nat \<Rightarrow> 'a measure" and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and C \<gamma> :: real and x :: "real^'m"
  assumes g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    and mom: "\<And>i l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "\<exists>a N. strict_mono a
      \<and> (\<forall>m::nat. finite_measure (N m)
          \<and> sets (N m) = sets (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          \<and> N m (space (N m)) \<le> ennreal 1
          \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) (N m)
              sequentially
              (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> (\<forall>m m'::nat. m \<le> m' \<longrightarrow>
          distr (N m') (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
            (\<lambda>f. restrict f {0..real m}) = N m)"
proof -
  obtain a where aa: "strict_mono a \<and> (\<forall>m::nat. \<exists>Nm.
      finite_measure Nm
      \<and> sets Nm = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> Nm (space Nm) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) Nm sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
    using path_laws_diagonal_subsequence[OF g0 g2 P Xm cont start int4 mom]
    by (rule exE)
  have a: "strict_mono a" by (rule conjunct1[OF aa])
  have all: "\<forall>m::nat. \<exists>Nm.
      finite_measure Nm
      \<and> sets Nm = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> Nm (space Nm) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) Nm sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
    by (rule conjunct2[OF aa])
  define N where "N = (\<lambda>m::nat. SOME Nm.
      finite_measure Nm
      \<and> sets Nm = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> Nm (space Nm) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) Nm sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
  have Nm: "finite_measure (N m)
      \<and> sets (N m) = sets (borel_of (mtopology_of
          (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      \<and> N m (space (N m)) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) (N m)
          sequentially
          (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))" for m
    unfolding N_def by (rule someI_ex) (use all in blast)
  have consist: "distr (N m') (borel_of (mtopology_of
        (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
      (\<lambda>f. restrict f {0..real m}) = N m" if mm: "m \<le> m'" for m m' :: nat
  proof -
    have m0: "0 \<le> real m" by simp
    have mmr: "real m \<le> real m'" using mm by simp
    have rc: "continuous_map
        (mtopology_of (path_metric (real m') :: (real \<Rightarrow> real^'m) metric))
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))
        (\<lambda>f. restrict f {0..real m})"
      by (rule Lipschitz_continuous_imp_continuous_map
            [OF Lipschitz_restrict_path_metric[OF m0 mmr]])
    have wc': "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m')) \<circ> a) (N m')
        sequentially
        (mtopology_of (path_metric (real m') :: (real \<Rightarrow> real^'m) metric))"
      using Nm[of m'] by blast
    have push: "weak_conv_on
        (\<lambda>i. distr (((\<lambda>i. path_law (MM i) (XX i) (real m')) \<circ> a) i)
            (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
            (\<lambda>f. restrict f {0..real m}))
        (distr (N m') (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          (\<lambda>f. restrict f {0..real m}))
        sequentially
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      by (rule weak_conv_on_pushforward[OF rc wc'])
    have eq: "(\<lambda>i. distr (((\<lambda>i. path_law (MM i) (XX i) (real m')) \<circ> a) i)
            (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
            (\<lambda>f. restrict f {0..real m}))
        = ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a)"
    proof (rule ext)
      fix i
      have Xmi: "XX (a i) t \<in> borel_measurable (MM (a i))"
        if "t \<in> {0..real m'}" for t
        using that by (intro Xm) simp
      have conti: "continuous_on {0..real m'} (\<lambda>t. XX (a i) t \<omega>)"
        if "\<omega> \<in> space (MM (a i))" for \<omega>
        by (rule continuous_on_subset[OF cont[OF that]]) auto
      show "(\<lambda>i. distr (((\<lambda>i. path_law (MM i) (XX i) (real m')) \<circ> a) i)
            (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
            (\<lambda>f. restrict f {0..real m})) i
          = ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) i"
        using path_law_restrict[OF m0 mmr Xmi conti] by (simp add: o_def)
    qed
    have lim1: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a)
        (distr (N m') (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          (\<lambda>f. restrict f {0..real m}))
        sequentially
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      using push unfolding eq .
    have lim2: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) (N m)
        sequentially
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      using Nm[of m] by blast
    have pmm: "metrizable_space
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      unfolding mtopology_of_def
      by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
    have met: "metrizable_space (weak_conv_topology
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
      by (rule metrizable_weak_conv_topology[OF pmm separable_path_metric])
    have haus: "Hausdorff_space (weak_conv_topology
        (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
      by (rule metrizable_imp_Hausdorff_space[OF met])
    show ?thesis
      by (rule limitin_Hausdorff_unique[OF lim1 lim2 trivial_limit_sequentially haus])
  qed
  show ?thesis
  proof (intro exI[of _ a] exI[of _ N] conjI)
    show "strict_mono a" by (rule a)
    show "\<forall>m::nat. finite_measure (N m)
        \<and> sets (N m) = sets (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
        \<and> N m (space (N m)) \<le> ennreal 1
        \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) (real m)) \<circ> a) (N m)
            sequentially
            (mtopology_of (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
      using Nm by blast
    show "\<forall>m m'::nat. m \<le> m' \<longrightarrow>
        distr (N m') (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          (\<lambda>f. restrict f {0..real m}) = N m"
      using consist by blast
  qed
qed

subsection \<open>The moment bound passes to the limit laws (plan item A1)\<close>

text \<open>
  Coordinate increments of paths are continuous test functions
  (\<open>continuous_map_path_eval_nth\<close>, composed through the missing-in-library
  \<open>continuous_map_real_diff\<close>), so \<open>weak_conv_on_nn_integral_le\<close> transfers the
  Eq. (2.7) fourth-moment package from the approximating processes to any
  weak limit of their path laws. Applied to the diagonal limits of
  \<open>path_laws_diagonal_consistent\<close>, this is what lets the dyadic modulus
  machinery run on the limit (plan item A3).
\<close>

lemma continuous_map_real_diff:
  assumes f: "continuous_map X euclideanreal f"
    and g: "continuous_map X euclideanreal g"
  shows "continuous_map X euclideanreal (\<lambda>x. f x - g x)"
  using assms unfolding continuous_map_atin
  by (auto intro!: tendsto_diff)

lemma continuous_map_path_eval_nth:
  fixes t T :: real
  assumes t: "t \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m::finite) metric))
      euclideanreal (\<lambda>g. g t $ l)"
proof -
  have e1: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclidean (\<lambda>g. g t)"
    by (rule continuous_map_path_eval[OF t])
  have "continuous_on UNIV (\<lambda>y :: real^'m. y $ l)"
    by (intro continuous_on_component continuous_on_id)
  hence e2: "continuous_map (euclidean :: (real^'m) topology) euclideanreal
      (\<lambda>y. y $ l)"
    by simp
  show ?thesis
    using continuous_map_compose[OF e1 e2] by (simp add: o_def)
qed

lemma continuous_map_path_moment:
  fixes u v T :: real
  assumes u: "u \<in> {0..T}" and v: "v \<in> {0..T}"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m::finite) metric))
      euclideanreal (\<lambda>g. (g v $ l - g u $ l)^4)"
  by (intro continuous_map_real_pow continuous_map_real_diff
        continuous_map_path_eval_nth u v)

theorem path_law_limit_moment_bound:
  fixes MM :: "nat \<Rightarrow> 'a measure" and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and N :: "(real \<Rightarrow> real^'m) measure" and T C u v :: real
  assumes wc: "weak_conv_on (\<lambda>i. path_law (MM i) (XX i) T) N sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    and Xm: "\<And>i t. t \<in> {0..T} \<Longrightarrow> XX i t \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and int4: "\<And>i. integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    and mom: "\<And>i. (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i))
        \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    and uv: "0 \<le> u" "u \<le> v" "v \<le> T"
  shows "(\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4) \<partial>N)
      \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
proof (rule weak_conv_on_nn_integral_le[OF wc])
  have um: "u \<in> {0..T}" and vm: "v \<in> {0..T}" using uv by auto
  show "continuous_map (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal (\<lambda>g. (g v $ l - g u $ l)^4)"
    by (rule continuous_map_path_moment[OF um vm])
  show "\<And>g. g \<in> topspace (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      \<Longrightarrow> 0 \<le> (g v $ l - g u $ l)^4"
    by (rule pow4_nonneg)
  show "0 \<le> 8*C\<^sup>2*(v - u)\<^sup>2" by simp
  fix i
  have T0: "0 \<le> T" using uv by linarith
  have pfm: "(\<lambda>\<omega>. restrict (\<lambda>t. XX i t \<omega>) {0..T})
      \<in> MM i \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by (rule pathify_measurable[OF T0 Xm cont])
  have hm: "(\<lambda>g. (g v $ l - g u $ l)^4) \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    using continuous_map_measurable[OF continuous_map_path_moment[OF um vm]]
    by (simp add: borel_of_euclidean)
  note hm[measurable]
  have fm: "(\<lambda>g. ennreal ((g v $ l - g u $ l)^4)) \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    by measurable
  have "(\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4) \<partial>(path_law (MM i) (XX i) T))
      = (\<integral>\<^sup>+\<omega>. ennreal ((restrict (\<lambda>t. XX i t \<omega>) {0..T} v $ l
          - restrict (\<lambda>t. XX i t \<omega>) {0..T} u $ l)^4) \<partial>(MM i))"
    unfolding path_law_def
    by (rule nn_integral_distr[OF pfm]) (use fm in simp)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal ((XX i v \<omega> $ l - XX i u \<omega> $ l)^4) \<partial>(MM i))"
    using um vm by simp
  also have "\<dots> = ennreal (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i))"
    by (rule nn_integral_eq_integral[OF int4])
       (intro AE_I2 pow4_nonneg)
  also have "\<dots> \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by (intro ennreal_leI mom)
  finally show "(\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4)
      \<partial>((\<lambda>i. path_law (MM i) (XX i) T) i)) \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by simp
qed

subsection \<open>The projective-limit assembly (plan item A2)\<close>

text \<open>
  From the horizon-consistent family of limit laws
  (\<open>path_laws_diagonal_consistent\<close>) to ONE probability measure on the
  full-time function space with the product sigma-algebra, via the
  Daniell-Kolmogorov theorem (\<open>HOL-Probability.Projective_Limit\<close>,
  locale \<open>polish_projective\<close>). The finite-dimensional marginals are the
  pushforwards of the \<open>N m\<close> under the (measurable, by evaluation continuity)
  restriction maps; the horizon choice is immaterial by the consistency
  identity, and the projective property is the restrict-restrict collapse.
  NOTE: \<open>unfold_locales\<close> on \<open>polish_projective\<close> decomposes the
  \<open>prob_space (P J)\<close> axiom into its three RAW ancestor axioms
  (sigma-finite cover, finiteness, total mass one) — discharge those, not
  the locale predicate.
\<close>

lemma marginal_map_measurable:
  fixes T :: real
  assumes J: "finite J" "J \<subseteq> {0..T}"
  shows "(\<lambda>g. restrict g J)
      \<in> borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m::finite) metric))
        \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel :: (real^'m) measure)"
proof -
  have ev: "(\<lambda>g. g t) \<in> borel_of (mtopology_of
      (path_metric T :: (real \<Rightarrow> real^'m) metric)) \<rightarrow>\<^sub>M borel"
    if t: "t \<in> J" for t
    using continuous_map_measurable[OF continuous_map_path_eval[OF subsetD[OF J(2) t]]]
    by (simp add: borel_of_euclidean)
  show ?thesis
    by (rule measurable_restrict) (rule ev)
qed

theorem projective_limit_of_consistent_path_laws:
  fixes N :: "nat \<Rightarrow> (real \<Rightarrow> real^'m::finite) measure"
  assumes PN: "\<And>m. prob_space (N m)"
    and sN: "\<And>m. sets (N m) = sets (borel_of (mtopology_of
        (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
    and consist: "\<And>m m'. m \<le> m' \<Longrightarrow>
        distr (N m') (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          (\<lambda>f. restrict f {0..real m}) = N m"
  shows "\<exists>L :: (real \<Rightarrow> real^'m) measure. prob_space L
      \<and> sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))
      \<and> (\<forall>m J. finite J \<longrightarrow> J \<subseteq> {0..real m} \<longrightarrow>
          distr L (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)
            = distr (N m) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J))"
proof -
  have exm: "\<exists>m :: nat. J \<subseteq> {0..real m}"
    if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
  proof (cases "J = {}")
    case True thus ?thesis by simp
  next
    case False
    obtain m :: nat where m: "Max J \<le> real m" using real_arch_simple by blast
    have "J \<subseteq> {0..real m}"
    proof
      fix t assume tJ: "t \<in> J"
      have "t \<le> Max J" by (rule Max_ge[OF J(1) tJ])
      also have "\<dots> \<le> real m" by (rule m)
      finally show "t \<in> {0..real m}" using subsetD[OF J(2) tJ] by auto
    qed
    thus ?thesis by blast
  qed
  define mm where "mm = (\<lambda>J :: real set. LEAST m :: nat. J \<subseteq> {0..real m})"
  have mmJ: "J \<subseteq> {0..real (mm J)}"
    if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
    unfolding mm_def using exm[OF J] by (rule LeastI_ex)
  have margNm: "(\<lambda>g. restrict g J) \<in> N m \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel :: (real^'m) measure)"
    if J: "finite J" "J \<subseteq> {0..real m}" for J m
  proof -
    have e: "measurable (N m) (PiM J (\<lambda>_. borel :: (real^'m) measure))
        = measurable (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          (PiM J (\<lambda>_. borel))"
      by (rule measurable_cong_sets[OF sN refl])
    show ?thesis unfolding e by (rule marginal_map_measurable[OF J])
  qed
  have indep: "distr (N m) (PiM J (\<lambda>_. borel :: (real^'m) measure)) (\<lambda>g. restrict g J)
      = distr (N m') (PiM J (\<lambda>_. borel)) (\<lambda>g. restrict g J)"
    if J: "finite J" "J \<subseteq> {0..real m}" and mle: "m \<le> m'" for J m m'
  proof -
    have m0: "0 \<le> real m" by simp
    have mr: "real m \<le> real m'" using mle by simp
    have rm: "(\<lambda>f. restrict f {0..real m})
        \<in> N m' \<rightarrow>\<^sub>M borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric))"
    proof -
      have e: "measurable (N m') (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          = measurable (borel_of (mtopology_of
              (path_metric (real m') :: (real \<Rightarrow> real^'m) metric)))
            (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
        by (rule measurable_cong_sets[OF sN refl])
      show ?thesis
        unfolding e by (rule restrict_measurable_path_borel[OF m0 mr])
    qed
    have "distr (N m) (PiM J (\<lambda>_. borel :: (real^'m) measure)) (\<lambda>g. restrict g J)
        = distr (distr (N m') (borel_of (mtopology_of
              (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
            (\<lambda>f. restrict f {0..real m}))
          (PiM J (\<lambda>_. borel)) (\<lambda>g. restrict g J)"
      unfolding consist[OF mle] by (rule refl)
    also have "\<dots> = distr (N m') (PiM J (\<lambda>_. borel))
        ((\<lambda>g. restrict g J) \<circ> (\<lambda>f. restrict f {0..real m}))"
      by (rule distr_distr[OF marginal_map_measurable[OF J] rm])
    also have "((\<lambda>g. restrict g J) \<circ> (\<lambda>f. restrict f {0..real m}))
        = (\<lambda>g. restrict g J)"
      using J(2) by (auto simp: restrict_def fun_eq_iff o_def)
    finally show ?thesis .
  qed
  have indep2: "distr (N m) (PiM J (\<lambda>_. borel :: (real^'m) measure)) (\<lambda>g. restrict g J)
      = distr (N m') (PiM J (\<lambda>_. borel)) (\<lambda>g. restrict g J)"
    if J: "finite J" "J \<subseteq> {0..real m}" "J \<subseteq> {0..real m'}" for J m m'
  proof (cases "m \<le> m'")
    case True show ?thesis by (rule indep[OF J(1) J(2) True])
  next
    case False
    hence "m' \<le> m" by simp
    show ?thesis by (rule indep[OF J(1) J(3) \<open>m' \<le> m\<close>, symmetric])
  qed
  define P where "P = (\<lambda>J :: real set.
      distr (N (mm J)) (PiM J (\<lambda>_. borel :: (real^'m) measure)) (\<lambda>g. restrict g J))"
  have PJ_eq: "P J = distr (N m) (PiM J (\<lambda>_. borel)) (\<lambda>g. restrict g J)"
    if J: "finite J" "J \<subseteq> ({0..} :: real set)" and Jm: "J \<subseteq> {0..real m}" for J m
    unfolding P_def by (rule indep2[OF J(1) mmJ[OF J] Jm])
  have prob_P: "prob_space (P J)" if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
    unfolding P_def
    by (rule prob_space.prob_space_distr[OF PN margNm[OF J(1) mmJ[OF J]]])
  have proj: "P J = distr (P H) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
    if JH: "J \<subseteq> H" and H: "finite H" and HI: "H \<subseteq> ({0..} :: real set)" for J H
  proof -
    have J: "finite J" "J \<subseteq> ({0..} :: real set)"
      using JH H HI finite_subset by auto
    have JmH: "J \<subseteq> {0..real (mm H)}" using JH mmJ[OF H HI] by auto
    have rJH: "(\<lambda>f. restrict f J) \<in> PiM H (\<lambda>_. borel :: (real^'m) measure)
        \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel)"
    proof (rule measurable_restrict)
      fix i assume "i \<in> J"
      thus "(\<lambda>x. x i) \<in> PiM H (\<lambda>_. borel :: (real^'m) measure) \<rightarrow>\<^sub>M borel"
        by (intro measurable_component_singleton) (use JH in blast)
    qed
    have "distr (P H) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)
        = distr (distr (N (mm H)) (PiM H (\<lambda>_. borel)) (\<lambda>g. restrict g H))
            (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
      unfolding P_def by (rule refl)
    also have "\<dots> = distr (N (mm H)) (PiM J (\<lambda>_. borel))
        ((\<lambda>f. restrict f J) \<circ> (\<lambda>g. restrict g H))"
      by (rule distr_distr[OF rJH margNm[OF H mmJ[OF H HI]]])
    also have "((\<lambda>f. restrict f J) \<circ> (\<lambda>g. restrict g H)) = (\<lambda>g. restrict g J)"
      using JH by (auto simp: restrict_def fun_eq_iff o_def)
    also have "distr (N (mm H)) (PiM J (\<lambda>_. borel)) (\<lambda>g. restrict g J) = P J"
      by (rule PJ_eq[OF J JmH, symmetric])
    finally show ?thesis by (rule sym)
  qed
  interpret PP: polish_projective "{0..} :: real set" P
  proof (unfold_locales)
    show "\<And>J H. J \<subseteq> H \<Longrightarrow> finite H \<Longrightarrow> H \<subseteq> ({0..} :: real set) \<Longrightarrow>
        P J = distr (P H) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
      by (rule proj)
    show "\<exists>A. countable A \<and> A \<subseteq> sets (P J) \<and> \<Union> A = space (P J)
        \<and> (\<forall>a\<in>A. emeasure (P J) a \<noteq> \<infinity>)"
      if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
    proof -
      interpret PJ: prob_space "P J" by (rule prob_P[OF J])
      show ?thesis
        by (intro exI[of _ "{space (P J)}"])
           (auto simp: PJ.emeasure_space_1)
    qed
    show "emeasure (P J) (space (P J)) \<noteq> \<top>"
      if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
      using prob_space.emeasure_space_1[OF prob_P[OF J]] by simp
    show "emeasure (P J) (space (P J)) = 1"
      if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
      by (rule prob_space.emeasure_space_1[OF prob_P[OF J]])
  qed
  have PL: "prob_space PP.lim"
    by (rule prob_spaceI) (rule PP.P.emeasure_space_1)
  have limmarg: "distr PP.lim (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J) = P J"
    if J: "finite J" "J \<subseteq> ({0..} :: real set)" for J
  proof (rule measure_eqI)
    show "sets (distr PP.lim (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)) = sets (P J)"
      by (simp add: PP.sets_P[OF J])
    fix A assume "A \<in> sets (distr PP.lim (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J))"
    hence A: "A \<in> sets (PiM J (\<lambda>_. borel :: (real^'m) measure))" by simp
    have rlim: "(\<lambda>f. restrict f J) \<in> PP.lim \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel)"
    proof -
      have e: "measurable PP.lim (PiM J (\<lambda>_. borel :: (real^'m) measure))
          = measurable (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))
            (PiM J (\<lambda>_. borel))"
        by (rule measurable_cong_sets[OF PP.sets_lim refl])
      have "(\<lambda>f. restrict f J) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
          \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel)"
      proof (rule measurable_restrict)
        fix i assume "i \<in> J"
        thus "(\<lambda>x. x i) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
            \<rightarrow>\<^sub>M borel"
          by (intro measurable_component_singleton) (use J(2) in blast)
      qed
      thus ?thesis unfolding e .
    qed
    have "emeasure (distr PP.lim (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)) A
        = emeasure PP.lim ((\<lambda>f. restrict f J) -` A \<inter> space PP.lim)"
      by (rule emeasure_distr[OF rlim A])
    also have "(\<lambda>f. restrict f J) -` A \<inter> space PP.lim
        = prod_emb {0..} (\<lambda>_. borel) J A"
      by (simp add: prod_emb_def space_PiM)
    also have "emeasure PP.lim (prod_emb {0..} (\<lambda>_. borel) J A) = emeasure (P J) A"
      by (rule PP.emeasure_lim_emb[OF J(2) J(1) A])
    finally show "emeasure (distr PP.lim (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)) A
        = emeasure (P J) A" .
  qed
  show ?thesis
  proof (intro exI[of _ PP.lim] conjI allI impI)
    show "prob_space PP.lim" by (rule PL)
    show "sets PP.lim = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
      by (rule PP.sets_lim)
    fix m :: nat and J :: "real set"
    assume Jf: "finite J" and Jm: "J \<subseteq> {0..real m}"
    have J: "finite J" "J \<subseteq> ({0..} :: real set)" using Jf Jm by auto
    show "distr PP.lim (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)
        = distr (N m) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
      using limmarg[OF J] PJ_eq[OF J Jm] by simp
  qed
qed

text \<open>First brick of plan item A3: the Eq. (2.7) package holds for the
  COORDINATES of the projective limit — the increment moment is a function of
  a two-point marginal, and marginals are inherited from the \<open>N m\<close>. This is
  the input for running the dyadic modulus machinery on \<open>L\<close> and building the
  continuous modification.\<close>

lemma lim_coordinate_moment_bound:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure"
    and N :: "nat \<Rightarrow> (real \<Rightarrow> real^'m) measure" and C u v :: real
  assumes sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and marg: "\<And>m J. finite J \<Longrightarrow> J \<subseteq> {0..real m} \<Longrightarrow>
        distr L (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)
          = distr (N m) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
    and sN: "\<And>m. sets (N m) = sets (borel_of (mtopology_of
        (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))"
    and momN: "\<And>m. v \<le> real m \<Longrightarrow>
        (\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4) \<partial>(N m))
          \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    and uv: "0 \<le> u" "u \<le> v"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
      \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
proof -
  obtain m :: nat where m: "v \<le> real m" using real_arch_simple by blast
  define J where "J = {u, v}"
  have Jf: "finite J" unfolding J_def by simp
  have Jm: "J \<subseteq> {0..real m}" unfolding J_def using uv m by auto
  have uJ: "u \<in> J" and vJ: "v \<in> J" unfolding J_def by auto
  have hmJ: "(\<lambda>g. ennreal ((g v $ l - g u $ l)^4))
      \<in> borel_measurable (PiM J (\<lambda>_. borel :: (real^'m) measure))"
  proof -
    have mu: "(\<lambda>g. g u) \<in> PiM J (\<lambda>_. borel :: (real^'m) measure) \<rightarrow>\<^sub>M borel"
      by (rule measurable_component_singleton[OF uJ])
    have mv: "(\<lambda>g. g v) \<in> PiM J (\<lambda>_. borel :: (real^'m) measure) \<rightarrow>\<^sub>M borel"
      by (rule measurable_component_singleton[OF vJ])
    have mul: "(\<lambda>g. g u $ l) \<in> PiM J (\<lambda>_. borel :: (real^'m) measure) \<rightarrow>\<^sub>M borel"
      by (rule measurable_compose[OF mu borel_measurable_nth])
    have mvl: "(\<lambda>g. g v $ l) \<in> PiM J (\<lambda>_. borel :: (real^'m) measure) \<rightarrow>\<^sub>M borel"
      by (rule measurable_compose[OF mv borel_measurable_nth])
    note mul[measurable] mvl[measurable]
    show ?thesis by measurable
  qed
  have hmJL: "(\<lambda>g. ennreal ((g v $ l - g u $ l)^4))
      \<in> borel_measurable (distr L (PiM J (\<lambda>_. borel :: (real^'m) measure))
          (\<lambda>f. restrict f J))"
    using hmJ measurable_cong_sets[OF sets_distr refl] by blast
  have hmJN: "(\<lambda>g. ennreal ((g v $ l - g u $ l)^4))
      \<in> borel_measurable (distr (N m) (PiM J (\<lambda>_. borel :: (real^'m) measure))
          (\<lambda>f. restrict f J))"
    using hmJ measurable_cong_sets[OF sets_distr refl] by blast
  have rL: "(\<lambda>f. restrict f J) \<in> L \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel :: (real^'m) measure)"
  proof -
    have e: "measurable L (PiM J (\<lambda>_. borel :: (real^'m) measure))
        = measurable (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))
          (PiM J (\<lambda>_. borel))"
      by (rule measurable_cong_sets[OF sL refl])
    have "(\<lambda>f. restrict f J) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
        \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel)"
    proof (rule measurable_restrict)
      fix i assume "i \<in> J"
      hence "i \<in> ({0..} :: real set)" using Jm by auto
      thus "(\<lambda>x. x i) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
          \<rightarrow>\<^sub>M borel"
        by (rule measurable_component_singleton)
    qed
    thus ?thesis unfolding e .
  qed
  have rN: "(\<lambda>f. restrict f J) \<in> N m \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel :: (real^'m) measure)"
  proof -
    have e: "measurable (N m) (PiM J (\<lambda>_. borel :: (real^'m) measure))
        = measurable (borel_of (mtopology_of
            (path_metric (real m) :: (real \<Rightarrow> real^'m) metric)))
          (PiM J (\<lambda>_. borel))"
      by (rule measurable_cong_sets[OF sN refl])
    show ?thesis unfolding e by (rule marginal_map_measurable[OF Jf Jm])
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
      = (\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4)
          \<partial>(distr L (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)))"
    by (subst nn_integral_distr[OF rL hmJL]) (simp add: uJ vJ)
  also have "\<dots> = (\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4)
      \<partial>(distr (N m) (PiM J (\<lambda>_. borel)) (\<lambda>f. restrict f J)))"
    unfolding marg[OF Jf Jm] by (rule refl)
  also have "\<dots> = (\<integral>\<^sup>+g. ennreal ((g v $ l - g u $ l)^4) \<partial>(N m))"
    by (subst nn_integral_distr[OF rN hmJN]) (simp add: uJ vJ)
  also have "\<dots> \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by (rule momN[OF m])
  finally show ?thesis .
qed

subsection \<open>The dyadic extension operator (plan item A3, deterministic core)\<close>

text \<open>
  A path controlled only ON THE DYADICS extends to a continuous function:
  \<open>dyadic_pair_modulus\<close> is the continuity-free chaining bound for pairs of
  dyadics (any metric space, via \<open>dyadic_chaining\<close>); the anchor sequences
  \<open>danchor k t\<close> are then Cauchy, and \<open>dyadic_ext\<close> takes their limit. It
  agrees with the original path at dyadic points, satisfies the same modulus
  at every level, and is continuous on \<open>{0..T}\<close>. Applied \<omega>-wise on the good
  event of the projective limit, this builds the continuous modification.
\<close>

lemma dyadic_pair_modulus:
  fixes f :: "real \<Rightarrow> 'b::metric_space" and \<gamma> T E :: real
  assumes good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
      dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>" and E0: "0 \<le> E"
    and w: "w \<in> dyadic_interval_step m 0 T" and z: "z \<in> dyadic_interval_step m 0 T"
    and wz: "\<bar>w - z\<bar> \<le> 1 / 2 ^ n'"
    and nn': "n \<le> n'"
  shows "dist (f w) (f z) \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))"
proof -
  let ?r = "2 powr (-\<gamma>)"
  have r0: "0 < ?r" by simp
  have r1: "?r < 1" using powr_neg_lt_1[OF g0] by simp
  have pos: "0 < 1 - ?r" using r1 by simp
  have cj: "2 powr (-\<gamma>*real j) = ?r^j" for j
    by (subst powr_realpow[symmetric]) (simp_all add: powr_powr)
  define m' where "m' = max m n'"
  have mm: "m \<le> m'" and nm: "n' \<le> m'" unfolding m'_def by simp_all
  have w': "w \<in> dyadic_interval_step m' 0 T"
    by (rule dyadic_interval_step_mono[OF w mm])
  have z': "z \<in> dyadic_interval_step m' 0 T"
    by (rule dyadic_interval_step_mono[OF z mm])
  have H: "dist (f (real_of_int (k - 1) / 2 ^ j)) (f (real_of_int k / 2 ^ j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    if "n' \<le> j" "j \<le> m'" "k \<in> {1..\<lfloor>2 ^ j * T\<rfloor>}" for j k
    using good[OF order.trans[OF nn' that(1)] that(3)] .
  have c0: "\<And>j. 0 \<le> E * 2 powr (-\<gamma>*real j)"
    using E0 by simp
  have S1: "(\<Sum>j\<in>{n'<..m'}. E * 2 powr (-\<gamma>*real j)) \<le> E * (?r^Suc n' / (1 - ?r))"
  proof -
    have "(\<Sum>j\<in>{n'<..m'}. E * 2 powr (-\<gamma>*real j)) = E * (\<Sum>j\<in>{n'<..m'}. ?r^j)"
      unfolding cj by (rule sum_distrib_left[symmetric])
    also have "\<dots> \<le> E * (?r^Suc n' / (1 - ?r))"
      by (intro mult_left_mono geometric_tail_sum_le E0) (use r0 r1 in simp_all)
    finally show ?thesis .
  qed
  have "dist (f w) (f z)
      \<le> E * 2 powr (-\<gamma>*real n') + 2 * (\<Sum>j\<in>{n'<..m'}. E * 2 powr (-\<gamma>*real j))"
    by (rule dyadic_chaining[where f=f, OF w' z' wz nm H c0])
  also have "\<dots> \<le> E * ?r^n' + 2 * (E * (?r^Suc n' / (1 - ?r)))"
    using S1 cj[of n'] by (simp add: mult_left_mono)
  also have "\<dots> = E * (?r^n' + 2 * (?r^Suc n' / (1 - ?r)))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> E * (3 * ?r^n' / (1 - ?r))"
  proof (rule mult_left_mono[OF _ E0])
    have ne: "1 - ?r \<noteq> 0" using pos by linarith
    have e1: "(?r^n' * (1 - ?r) + 2 * ?r^Suc n') / (1 - ?r)
        = ?r^n' + 2 * (?r^Suc n' / (1 - ?r))"
    proof -
      have "(?r^n' * (1 - ?r) + 2 * ?r^Suc n') / (1 - ?r)
          = ?r^n' * (1 - ?r) / (1 - ?r) + 2 * ?r^Suc n' / (1 - ?r)"
        by (rule add_divide_distrib)
      also have "?r^n' * (1 - ?r) / (1 - ?r) = ?r^n'"
        by (rule nonzero_mult_div_cancel_right[OF ne])
      finally show ?thesis by simp
    qed
    have e2: "?r^n' * (1 - ?r) + 2 * ?r^Suc n' = ?r^n' + ?r^Suc n'"
      by (simp add: algebra_simps)
    have le1: "?r^Suc n' \<le> ?r^n'"
      by (intro power_decreasing) (use r0 r1 in simp_all)
    have rn0: "0 \<le> ?r^n'"
      by (rule zero_le_power[OF less_imp_le[OF r0]])
    have e3: "?r^n' + ?r^Suc n' \<le> 3 * ?r^n'"
      using le1 rn0 by linarith
    have "(?r^n' + ?r^Suc n') / (1 - ?r) \<le> (3 * ?r^n') / (1 - ?r)"
      by (rule divide_right_mono[OF e3]) (use pos in simp)
    thus "?r^n' + 2 * (?r^Suc n' / (1 - ?r)) \<le> 3 * ?r^n' / (1 - ?r)"
      unfolding e1[symmetric] e2 by simp
  qed
  also have "E * (3 * ?r^n' / (1 - ?r)) = 3 * E * 2 powr (-\<gamma>*real n') / (1 - ?r)"
    unfolding cj[of n'] by simp
  finally show ?thesis .
qed

definition dyadic_ext :: "(real \<Rightarrow> 'b) \<Rightarrow> real \<Rightarrow> 'b::complete_space" where
  "dyadic_ext f t = lim (\<lambda>k. f (danchor k t))"

lemma modulus_level_choice:
  fixes \<gamma> E e :: real
  assumes g0: "0 < \<gamma>" and E0: "0 \<le> E" and e: "0 < e"
  shows "\<exists>n' \<ge> N. 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>)) < e"
proof -
  let ?r = "2 powr (-\<gamma>)"
  have r0: "0 \<le> ?r" by simp
  have r1: "?r < 1" using powr_neg_lt_1[OF g0] by simp
  have cj: "\<And>j. 2 powr (-\<gamma>*real j) = ?r^j"
    by (subst powr_realpow[symmetric]) (simp_all add: powr_powr)
  have lim0: "(\<lambda>n'. (3 * E / (1 - ?r)) * ?r^n') \<longlonglongrightarrow> 0"
    by (rule tendsto_mult_right_zero[OF LIMSEQ_realpow_zero[OF r0 r1]])
  from order_tendstoD(2)[OF lim0 e] obtain M where
    M: "\<And>k. M \<le> k \<Longrightarrow> (3 * E / (1 - ?r)) * ?r^k < e"
    by (auto simp: eventually_sequentially)
  have ee: "3 * E * 2 powr (-\<gamma>*real k) / (1 - ?r) = (3 * E / (1 - ?r)) * ?r^k" for k
    unfolding cj by simp
  have "3 * E * 2 powr (-\<gamma>*real (max N M)) / (1 - ?r) < e"
    unfolding ee by (rule M) simp
  thus ?thesis by (intro exI[of _ "max N M"]) simp
qed

lemma dyadic_ext_tendsto:
  fixes f :: "real \<Rightarrow> 'b::complete_space" and \<gamma> T E :: real
  assumes good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
      dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>" and E0: "0 \<le> E"
    and t: "t \<in> {0..T}"
  shows "(\<lambda>k. f (danchor k t)) \<longlonglongrightarrow> dyadic_ext f t"
proof -
  have t0: "0 \<le> t" and tT: "t \<le> T" using t by auto
  have anch: "danchor k t \<in> dyadic_interval_step k 0 T" for k
    by (rule danchor_mem[OF t0 tT])
  have C: "Cauchy (\<lambda>k. f (danchor k t))"
  proof (rule metric_CauchyI)
    fix e :: real assume e: "0 < e"
    obtain n' where n': "n \<le> n'"
      and lt: "3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>)) < e"
      using modulus_level_choice[OF g0 E0 e] by blast
    show "\<exists>M. \<forall>k\<ge>M. \<forall>k'\<ge>M. dist (f (danchor k t)) (f (danchor k' t)) < e"
    proof (intro exI[of _ "Suc n'"] allI impI)
      fix k k' assume k: "Suc n' \<le> k" and k': "Suc n' \<le> k'"
      have m1: "danchor k t \<in> dyadic_interval_step (max k k') 0 T"
        by (rule dyadic_interval_step_mono[OF anch]) simp
      have m2: "danchor k' t \<in> dyadic_interval_step (max k k') 0 T"
        by (rule dyadic_interval_step_mono[OF anch]) simp
      have le1: "danchor k t \<le> t" by (rule danchor_le)
      have gt1: "t - 1 / 2 ^ k < danchor k t" by (rule danchor_gt)
      have le2: "danchor k' t \<le> t" by (rule danchor_le)
      have gt2: "t - 1 / 2 ^ k' < danchor k' t" by (rule danchor_gt)
      have h1: "(2::real) ^ Suc n' \<le> 2 ^ k"
        by (intro power_increasing k) simp
      have half1: "(1::real) / 2 ^ k \<le> 1 / 2 ^ Suc n'"
        using h1 by (intro divide_left_mono) simp_all
      have h2: "(2::real) ^ Suc n' \<le> 2 ^ k'"
        by (intro power_increasing k') simp
      have half2: "(1::real) / 2 ^ k' \<le> 1 / 2 ^ Suc n'"
        using h2 by (intro divide_left_mono) simp_all
      have twice: "(1::real) / 2 ^ Suc n' + 1 / 2 ^ Suc n' = 1 / 2 ^ n'"
        by (simp add: field_simps)
      have gap: "\<bar>danchor k t - danchor k' t\<bar> \<le> 1 / 2 ^ n'"
        using le1 gt1 le2 gt2 half1 half2 twice by (auto simp: abs_le_iff)
      have "dist (f (danchor k t)) (f (danchor k' t))
          \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))"
        by (rule dyadic_pair_modulus[OF good g0 E0 m1 m2 gap n'])
      with lt show "dist (f (danchor k t)) (f (danchor k' t)) < e" by linarith
    qed
  qed
  hence "convergent (\<lambda>k. f (danchor k t))" by (rule Cauchy_convergent)
  thus ?thesis unfolding dyadic_ext_def by (rule convergent_LIMSEQ_iff[THEN iffD1])
qed

lemma dyadic_ext_dyadic:
  fixes f :: "real \<Rightarrow> 'b::complete_space" and \<gamma> T E :: real
  assumes good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
      dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>" and E0: "0 \<le> E"
    and t: "t \<in> dyadic_interval_step m 0 T"
  shows "dyadic_ext f t = f t"
proof -
  have tmem: "t \<in> {0..T}"
    using dyadic_step_geq[OF t] dyadic_step_leq[OF t] by auto
  have l1: "(\<lambda>k. f (danchor k t)) \<longlonglongrightarrow> dyadic_ext f t"
    by (rule dyadic_ext_tendsto[OF good g0 E0 tmem])
  have const: "danchor k t = t" if "m \<le> k" for k
    by (rule danchor_self[OF dyadic_interval_step_mono[OF t that]])
  have l2: "(\<lambda>k. f (danchor k t)) \<longlonglongrightarrow> f t"
    by (rule tendsto_eventually)
       (auto simp: eventually_sequentially const intro: exI[of _ m])
  show ?thesis
    by (rule LIMSEQ_unique[OF l1 l2])
qed

lemma dyadic_ext_dist_le:
  fixes f :: "real \<Rightarrow> 'b::complete_space" and \<gamma> T E :: real
  assumes good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
      dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>" and E0: "0 \<le> E"
    and u: "u \<in> {0..T}" and v: "v \<in> {0..T}"
    and gap: "\<bar>u - v\<bar> < 1 / 2 ^ n'"
    and nn': "n \<le> n'"
  shows "dist (dyadic_ext f u) (dyadic_ext f v)
      \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))"
proof -
  have u0: "0 \<le> u" and uT: "u \<le> T" using u by auto
  have v0: "0 \<le> v" and vT: "v \<le> T" using v by auto
  have lu: "(\<lambda>k. f (danchor k u)) \<longlonglongrightarrow> dyadic_ext f u"
    by (rule dyadic_ext_tendsto[OF good g0 E0 u])
  have lv: "(\<lambda>k. f (danchor k v)) \<longlonglongrightarrow> dyadic_ext f v"
    by (rule dyadic_ext_tendsto[OF good g0 E0 v])
  have ld: "(\<lambda>k. dist (f (danchor k u)) (f (danchor k v)))
      \<longlonglongrightarrow> dist (dyadic_ext f u) (dyadic_ext f v)"
    by (rule tendsto_dist[OF lu lv])
  have small: "(\<lambda>k. (2::real) / 2 ^ k) \<longlonglongrightarrow> 0"
    by (intro tendsto_divide_0[OF tendsto_const] LIMSEQ_ignore_initial_segment)
       (auto intro!: filterlim_realpow_sequentially_gt1)
  have gap': "0 < 1 / 2 ^ n' - \<bar>u - v\<bar>" using gap by simp
  from order_tendstoD(2)[OF small gap'] obtain K where
    K: "\<And>k. K \<le> k \<Longrightarrow> (2::real) / 2 ^ k < 1 / 2 ^ n' - \<bar>u - v\<bar>"
    by (auto simp: eventually_sequentially)
  have bnd: "dist (f (danchor k u)) (f (danchor k v))
      \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))" if kK: "K \<le> k" for k
  proof -
    have m1: "danchor k u \<in> dyadic_interval_step k 0 T"
      by (rule danchor_mem[OF u0 uT])
    have m2: "danchor k v \<in> dyadic_interval_step k 0 T"
      by (rule danchor_mem[OF v0 vT])
    have a1: "danchor k u \<le> u" by (rule danchor_le)
    have a2: "u - 1 / 2 ^ k < danchor k u" by (rule danchor_gt)
    have a3: "danchor k v \<le> v" by (rule danchor_le)
    have a4: "v - 1 / 2 ^ k < danchor k v" by (rule danchor_gt)
    have "\<bar>danchor k u - danchor k v\<bar> \<le> \<bar>u - v\<bar> + 2 / 2 ^ k"
      using a1 a2 a3 a4 by (auto simp: abs_le_iff abs_less_iff)
    also have "\<dots> \<le> 1 / 2 ^ n'"
      using K[OF kK] by linarith
    finally have gapk: "\<bar>danchor k u - danchor k v\<bar> \<le> 1 / 2 ^ n'" .
    show ?thesis
      by (rule dyadic_pair_modulus[OF good g0 E0 m1 m2 gapk nn'])
  qed
  have ev: "\<forall>\<^sub>F k in sequentially. dist (f (danchor k u)) (f (danchor k v))
      \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))"
    by (rule eventually_sequentiallyI[of K]) (rule bnd)
  show ?thesis
    by (rule tendsto_upperbound[OF ld ev trivial_limit_sequentially])
qed

lemma dyadic_ext_continuous_on:
  fixes f :: "real \<Rightarrow> 'b::complete_space" and \<gamma> T E :: real
  assumes good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
      dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>" and E0: "0 \<le> E"
  shows "continuous_on {0..T} (dyadic_ext f)"
proof (rule continuous_on_iff[THEN iffD2], intro ballI allI impI)
  fix t :: real and e :: real
  assume t: "t \<in> {0..T}" and e: "0 < e"
  obtain n' where n': "n \<le> n'"
    and lt: "3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>)) < e"
    using modulus_level_choice[OF g0 E0 e] by blast
  show "\<exists>d>0. \<forall>t'\<in>{0..T}. dist t' t < d \<longrightarrow>
      dist (dyadic_ext f t') (dyadic_ext f t) < e"
  proof (intro exI[of _ "1 / 2 ^ n'"] conjI ballI impI)
    show "(0::real) < 1 / 2 ^ n'" by simp
    fix t' assume t': "t' \<in> {0..T}" and dt: "dist t' t < 1 / 2 ^ n'"
    have gp: "\<bar>t' - t\<bar> < 1 / 2 ^ n'" using dt by (simp add: dist_real_def)
    have "dist (dyadic_ext f t') (dyadic_ext f t)
        \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))"
      by (rule dyadic_ext_dist_le[OF good g0 E0 t' t gp n'])
    with lt show "dist (dyadic_ext f t') (dyadic_ext f t) < e" by linarith
  qed
qed

subsection \<open>The good-dyadics event of the projective limit is almost sure\<close>

text \<open>
  Plan item A3, probabilistic half, first pieces: the coordinates of the
  projective limit are measurable, carry the Bochner form of the Eq. (2.7)
  package (adapter from the \<open>nn_integral\<close> bound), and — via
  \<open>dyadic_bad_event_tail_mom\<close> at every integer horizon and coordinate, with
  the geometric level bounds forcing the intersection over levels to be null
  — almost every \<open>\<omega>\<close> satisfies the dyadic moduli from some level on, at every
  horizon and coordinate simultaneously. On this event \<open>dyadic_ext\<close> builds
  the continuous modification.
\<close>

lemma lim_coordinate_measurable:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and u: "0 \<le> u"
  shows "(\<lambda>\<omega>. \<omega> u $ l) \<in> borel_measurable L"
proof -
  have e: "measurable L (borel :: real measure)
      = measurable (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)) borel"
    by (rule measurable_cong_sets[OF sL refl])
  have c: "(\<lambda>\<omega>. \<omega> u) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
      \<rightarrow>\<^sub>M borel"
    using u by (intro measurable_component_singleton) simp
  have "(\<lambda>\<omega>. \<omega> u $ l) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
      \<rightarrow>\<^sub>M borel"
    by (rule measurable_compose[OF c borel_measurable_nth])
  thus ?thesis unfolding e .
qed

lemma lim_coordinate_moment_package:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure" and C u v :: real
  assumes sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and mom: "(\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
        \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    and uv: "0 \<le> u" "u \<le> v"
  shows "integrable L (\<lambda>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4)"
    and "(\<integral>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4 \<partial>L) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
proof -
  have v0: "0 \<le> v" using uv by linarith
  have m: "(\<lambda>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4) \<in> borel_measurable L"
    using lim_coordinate_measurable[OF sL uv(1), of l]
      lim_coordinate_measurable[OF sL v0, of l]
    by measurable
  have ae: "AE \<omega> in L. 0 \<le> (\<omega> v $ l - \<omega> u $ l)^4"
    by (intro AE_I2 pow4_nonneg)
  show intg: "integrable L (\<lambda>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4)"
  proof (rule integrableI_nonneg[OF m ae])
    have "(\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L) \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
      by (rule mom)
    also have "\<dots> < \<infinity>" by simp
    finally show "(\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L) < \<infinity>" .
  qed
  have "ennreal (\<integral>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4 \<partial>L)
      = (\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)"
    by (rule nn_integral_eq_integral[symmetric, OF intg ae])
  also have "\<dots> \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by (rule mom)
  finally show "(\<integral>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4 \<partial>L) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    by simp
qed

theorem lim_dyadic_good_AE:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure" and C \<gamma> :: real
  assumes PL: "prob_space L"
    and sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and mom: "\<And>l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
          \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
  shows "AE \<omega> in L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
        \<le> 2 powr (-\<gamma>*real j)"
proof -
  interpret P: prob_space L by (rule PL)
  have good_Tl: "AE \<omega> in L. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
        \<le> 2 powr (-\<gamma>*real j)" for T :: nat and l
  proof -
    define E where "E = (\<lambda>n. {\<omega> \<in> space L. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        2 powr (-\<gamma>*real j)
          \<le> \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>})"
    have Xm: "(\<lambda>\<omega>. \<omega> u $ l) \<in> borel_measurable L" if "0 \<le> u" for u
      by (rule lim_coordinate_measurable[OF sL that])
    have ES: "E n \<in> sets L" for n
      unfolding E_def
      by (intro dyadic_bad_event_sets[where X = "\<lambda>u \<omega>. \<omega> u $ l"] Xm)
    have Ebnd: "measure L (E n)
        \<le> 8*C\<^sup>2*(real T) * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))" for n
      unfolding E_def
    proof (intro dyadic_bad_event_tail_mom[where X = "\<lambda>u \<omega>. \<omega> u $ l" and C = C]
          PL g2)
      show "\<And>u. 0 \<le> u \<Longrightarrow> (\<lambda>\<omega>. \<omega> u $ l) \<in> borel_measurable L" by (rule Xm)
      show "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> real T \<Longrightarrow>
          integrable L (\<lambda>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4)"
        by (rule lim_coordinate_moment_package(1)[OF sL mom])
      show "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> real T \<Longrightarrow>
          (\<integral>\<omega>. (\<omega> v $ l - \<omega> u $ l)^4 \<partial>L) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
        by (rule lim_coordinate_moment_package(2)[OF sL mom])
      show "0 \<le> real T" by simp
    qed
    define q where "q = 2 powr (-(1-4*\<gamma>))"
    have q0: "0 \<le> q" unfolding q_def by simp
    have q1: "q < 1" unfolding q_def by (rule powr_ratio_lt_1[OF g2])
    have limq: "(\<lambda>n. 8*C\<^sup>2*(real T) * q^n / (1 - q)) \<longlonglongrightarrow> 0"
    proof -
      have e1: "(\<lambda>n. (8*C\<^sup>2*(real T)/(1 - q)) * q^n) \<longlonglongrightarrow> 0"
        by (rule tendsto_mult_right_zero[OF LIMSEQ_realpow_zero[OF q0 q1]])
      have e2: "(8*C\<^sup>2*(real T)/(1 - q)) * q^n = 8*C\<^sup>2*(real T) * q^n / (1 - q)" for n
        by simp
      show ?thesis using e1 unfolding e2 .
    qed
    have Iset: "(\<Inter>n. E n) \<in> sets L"
    proof (rule sets.countable_INT'[OF countableI_type])
      show "(UNIV :: nat set) \<noteq> {}" by simp
      show "E ` UNIV \<subseteq> sets L" using ES by auto
    qed
    have Ibnd: "measure L (\<Inter>n. E n) \<le> 8*C\<^sup>2*(real T) * q^n / (1 - q)" for n
    proof -
      have "measure L (\<Inter>n. E n) \<le> measure L (E n)"
        by (intro P.finite_measure_mono ES) auto
      also have "\<dots> \<le> 8*C\<^sup>2*(real T) * q^n / (1 - q)"
        unfolding q_def by (rule Ebnd)
      finally show ?thesis .
    qed
    have I0: "measure L (\<Inter>n. E n) = 0"
    proof (rule ccontr)
      assume ne: "measure L (\<Inter>n. E n) \<noteq> 0"
      have pos: "0 < measure L (\<Inter>n. E n)"
        using ne measure_nonneg[of L "\<Inter>n. E n"] by linarith
      from order_tendstoD(2)[OF limq pos] obtain n where
        "8*C\<^sup>2*(real T) * q^n / (1 - q) < measure L (\<Inter>n. E n)"
        by (auto simp: eventually_sequentially)
      with Ibnd[of n] show False by linarith
    qed
    have ae1: "AE \<omega> in L. \<omega> \<notin> (\<Inter>n. E n)"
      by (rule AE_I[where N = "\<Inter>n. E n"])
         (use I0 Iset in \<open>auto simp: P.emeasure_eq_measure\<close>)
    have main: "\<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
      if w: "\<omega> \<in> space L" and nI: "\<omega> \<notin> (\<Inter>n. E n)" for \<omega>
    proof -
      from nI obtain n where nE: "\<omega> \<notin> E n" by blast
      have le: "\<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
        if jk: "n \<le> j" "k \<in> {1..\<lfloor>2^j * real T\<rfloor>}" for j k
      proof -
        have "\<not> 2 powr (-\<gamma>*real j)
            \<le> \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>"
          using nE w jk unfolding E_def by blast
        thus ?thesis by linarith
      qed
      show ?thesis
        by (intro exI[of _ n] allI impI ballI le)
    qed
    have ae2: "AE \<omega> in L. \<omega> \<notin> (\<Inter>n. E n) \<longrightarrow> (\<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j))"
      by (rule AE_I2) (use main in blast)
    show ?thesis by (rule AE_mp[OF ae1 ae2])
  qed
  have "AE \<omega> in L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
        \<le> 2 powr (-\<gamma>*real j)"
    by (intro AE_all_countable[THEN iffD2] allI good_Tl)
  thus ?thesis .
qed

text \<open>Continuity of the extension on all of \<open>{0..}\<close> from PER-HORIZON good
  bounds (each point sits inside some integer horizon, and \<open>dyadic_ext\<close> is
  horizon-free), plus the measurable good set of the projective limit —
  the strict-threshold bad events have the same countable-union structure,
  and the good set is the complement assembled by \<open>countable_INT'\<close>/UN.\<close>

lemma dyadic_ext_continuous_on_all:
  fixes f :: "real \<Rightarrow> 'b::complete_space" and \<gamma> E :: real
  assumes goodT: "\<And>T::nat. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
        \<le> E * 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>" and E0: "0 \<le> E"
  shows "continuous_on {0..} (dyadic_ext f)"
proof (rule continuous_on_iff[THEN iffD2], intro ballI allI impI)
  fix t :: real and e :: real
  assume t: "t \<in> {0..}" and e: "0 < e"
  have t0: "0 \<le> t" using t by simp
  define T where "T = nat \<lfloor>t\<rfloor> + 1"
  have tT: "t < real T"
    unfolding T_def using t0 by linarith
  from goodT[of T] obtain n where
    good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * real T\<rfloor>} \<Longrightarrow>
        dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
          \<le> E * 2 powr (-\<gamma>*real j)"
    by blast
  obtain n' where n': "n \<le> n'"
    and lt: "3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>)) < e"
    using modulus_level_choice[OF g0 E0 e] by blast
  define d where "d = min (1 / 2 ^ n') (real T - t)"
  have d0: "0 < d" unfolding d_def using tT by simp
  show "\<exists>d>0. \<forall>t'\<in>{0..}. dist t' t < d \<longrightarrow>
      dist (dyadic_ext f t') (dyadic_ext f t) < e"
  proof (intro exI[of _ d] conjI ballI impI)
    show "0 < d" by (rule d0)
    fix t' assume t': "t' \<in> {0..}" and dt: "dist t' t < d"
    have t'0: "0 \<le> t'" using t' by simp
    have t'T: "t' \<le> real T"
      using dt unfolding d_def by (simp add: dist_real_def) linarith
    have tmem: "t \<in> {0..real T}" using t0 tT by simp
    have t'mem: "t' \<in> {0..real T}" using t'0 t'T by simp
    have gp: "\<bar>t' - t\<bar> < 1 / 2 ^ n'"
      using dt unfolding d_def by (simp add: dist_real_def)
    have "dist (dyadic_ext f t') (dyadic_ext f t)
        \<le> 3 * E * 2 powr (-\<gamma>*real n') / (1 - 2 powr (-\<gamma>))"
      by (rule dyadic_ext_dist_le[OF good g0 E0 t'mem tmem gp n'])
    with lt show "dist (dyadic_ext f t') (dyadic_ext f t) < e" by linarith
  qed
qed

lemma dyadic_bad_event_sets_strict:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
  shows "{\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
            2 powr (-\<gamma>*real j)
              < \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
         \<in> sets M"
proof -
  define E where "E j = {\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        < \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}" for j
  have Esets: "E j \<in> sets M" for j
  proof -
    have "{\<omega> \<in> space M. 2 powr (-\<gamma>*real j)
            < \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>} \<in> sets M"
      if k: "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    proof -
      have "0 \<le> real_of_int (k - 1) / 2^j" "0 \<le> real_of_int k / 2^j"
        using k by simp_all
      from Xm[OF this(1)] Xm[OF this(2)] show ?thesis by measurable
    qed
    moreover have "E j = (\<Union>k\<in>{1..\<lfloor>2^j * T\<rfloor>}. {\<omega> \<in> space M. 2 powr (-\<gamma>*real j)
            < \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>})"
      unfolding E_def by auto
    ultimately show ?thesis
      by (metis (lifting) countable_Un_Int(1))
  qed
  have s1: "{\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        < \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
      = (\<Union>j\<in>{n..}. E j)"
    unfolding E_def by auto
  show ?thesis unfolding s1
    by (intro sets.countable_UN'' Esets countableI_type)
qed

lemma lim_good_set:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure" and \<gamma> :: real
  assumes sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
  shows "{\<omega> \<in> space L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
        \<le> 2 powr (-\<gamma>*real j)} \<in> sets L"
proof -
  define B where "B = (\<lambda>(T::nat) l n. {\<omega> \<in> space L. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        < \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>})"
  have Xm: "(\<lambda>\<omega>. \<omega> u $ l) \<in> borel_measurable L" if "0 \<le> u" for u l
    by (rule lim_coordinate_measurable[OF sL that])
  have BS: "B T l n \<in> sets L" for T l n
    unfolding B_def
    by (intro dyadic_bad_event_sets_strict[where X = "\<lambda>u \<omega>. \<omega> u $ l"] Xm)
  have inner: "space L - B T l n \<in> sets L" for T l n
    by (intro sets.compl_sets BS)
  have un: "(\<Union>n. space L - B T l n) \<in> sets L" for T l
    by (intro sets.countable_UN'' countableI_type) (use inner in auto)
  have il: "(\<Inter>l. \<Union>n. space L - B T l n) \<in> sets L" for T
  proof (rule sets.countable_INT'[OF countableI_type])
    show "(UNIV :: 'm set) \<noteq> {}" by simp
    show "(\<lambda>l. \<Union>n. space L - B T l n) ` UNIV \<subseteq> sets L" using un by auto
  qed
  have iT: "(\<Inter>T::nat. \<Inter>l. \<Union>n. space L - B T l n) \<in> sets L"
  proof (rule sets.countable_INT'[OF countableI_type])
    show "(UNIV :: nat set) \<noteq> {}" by simp
    show "(\<lambda>T::nat. \<Inter>l. \<Union>n. space L - B T l n) ` UNIV \<subseteq> sets L"
      using il by auto
  qed
  have eq: "{\<omega> \<in> space L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
        \<le> 2 powr (-\<gamma>*real j)}
      = space L \<inter> (\<Inter>T::nat. \<Inter>l. \<Union>n. space L - B T l n)"
  proof (intro subset_antisym subsetI)
    fix \<omega> assume A: "\<omega> \<in> {\<omega> \<in> space L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n.
        \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)}"
    have w: "\<omega> \<in> space L" using A by blast
    have P: "\<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
      using A by blast
    have inU: "\<omega> \<in> (\<Union>n. space L - B T l n)" for T l
    proof -
      from P obtain n where g: "\<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
          \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
            \<le> 2 powr (-\<gamma>*real j)"
        by blast
      have "\<omega> \<notin> B T l n"
      proof
        assume "\<omega> \<in> B T l n"
        then obtain j k where jn: "n \<le> j" and kk: "k \<in> {1..\<lfloor>2^j * real T\<rfloor>}"
          and lt: "2 powr (-\<gamma>*real j)
            < \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>"
          unfolding B_def by blast
        from g jn kk have "\<bar>\<omega> (real_of_int k / 2^j) $ l
            - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar> \<le> 2 powr (-\<gamma>*real j)" by blast
        with lt show False by linarith
      qed
      with w show ?thesis by (intro UN_I[of n]) auto
    qed
    show "\<omega> \<in> space L \<inter> (\<Inter>T::nat. \<Inter>l. \<Union>n. space L - B T l n)"
      using w inU by blast
  next
    fix \<omega> assume A: "\<omega> \<in> space L \<inter> (\<Inter>T::nat. \<Inter>l. \<Union>n. space L - B T l n)"
    have w: "\<omega> \<in> space L" using A by blast
    have P: "\<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)" for T l
    proof -
      have "\<omega> \<in> (\<Union>n. space L - B T l n)" using A by blast
      then obtain n where nB: "\<omega> \<notin> B T l n" by blast
      have le: "\<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
        if jn: "n \<le> j" and kk: "k \<in> {1..\<lfloor>2^j * real T\<rfloor>}" for j k
      proof -
        have "\<not> 2 powr (-\<gamma>*real j)
            < \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>"
          using nB w jn kk unfolding B_def by blast
        thus ?thesis by linarith
      qed
      show ?thesis by (intro exI[of _ n] allI impI ballI le)
    qed
    show "\<omega> \<in> {\<omega> \<in> space L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)}"
      using w P by blast
  qed
  show ?thesis unfolding eq
    by (intro sets.Int sets.top iT)
qed

text \<open>Per-time measurability of the extension: \<open>dyadic_ext\<close> is
  DEFINITIONALLY a \<open>lim\<close> along the (nonnegative, by \<open>danchor_nonneg\<close>) anchor
  sequence, so \<open>borel_measurable_lim_metric\<close> applies directly.\<close>

lemma lim_vector_coordinate_measurable:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and u: "0 \<le> u"
  shows "(\<lambda>\<omega>. \<omega> u) \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)"
proof -
  have e: "measurable L (borel :: (real^'m) measure)
      = measurable (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)) borel"
    by (rule measurable_cong_sets[OF sL refl])
  have "(\<lambda>\<omega>. \<omega> u) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
      \<rightarrow>\<^sub>M borel"
    using u by (intro measurable_component_singleton) simp
  thus ?thesis unfolding e .
qed

lemma dyadic_ext_measurable:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure"
  assumes sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and t0: "0 \<le> t"
  shows "(\<lambda>\<omega>. dyadic_ext \<omega> t) \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)"
proof -
  have comp: "(\<lambda>\<omega>. \<omega> (danchor k t)) \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)" for k
    by (rule lim_vector_coordinate_measurable[OF sL danchor_nonneg[OF t0]])
  have "(\<lambda>\<omega>. lim (\<lambda>k. \<omega> (danchor k t))) \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)"
    by (rule borel_measurable_lim_metric[OF comp])
  thus ?thesis unfolding dyadic_ext_def .
qed

subsection \<open>The modification identity (plan item A3, final piece)\<close>

text \<open>
  The extension agrees with the sample almost surely at every fixed time:
  the anchors converge to the extension almost surely (on the good event, by
  \<open>dyadic_ext_tendsto\<close> with the vector bound assembled from per-coordinate
  levels), and to the sample in probability (Chebyshev at the fourth moment,
  \<open>lim_vector_increment_tail\<close>); the truncated-distance Fatou argument glues
  the two. This makes \<open>dyadic_ext\<close> a CONTINUOUS MODIFICATION of the
  projective limit's coordinate process.
\<close>

lemma lim_vector_increment_tail:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure" and C s t e :: real
  assumes PL: "prob_space L"
    and sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and mom: "\<And>l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
          \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    and st: "0 \<le> s" "s \<le> t"
    and e: "0 < e"
  shows "measure L {\<omega> \<in> space L. e \<le> dist (\<omega> s) (\<omega> t)}
      \<le> real (CARD('m)) * (8*C\<^sup>2*(t - s)\<^sup>2 * (real (CARD('m)))^4 / e^4)"
proof -
  interpret P: prob_space L by (rule PL)
  have t0: "0 \<le> t" using st by linarith
  define ec where "ec = e / real (CARD('m))"
  have ec0: "0 < ec" unfolding ec_def using e by (simp add: card_gt_0_iff)
  have coordm: "(\<lambda>\<omega>. \<omega> t $ l - \<omega> s $ l) \<in> borel_measurable L" for l
    using lim_coordinate_measurable[OF sL st(1), of l]
      lim_coordinate_measurable[OF sL t0, of l]
    by measurable
  have int4: "integrable L (\<lambda>\<omega>. (\<omega> t $ l - \<omega> s $ l)^4)" for l
    using st by (intro lim_coordinate_moment_package(1)[OF sL mom])
  have momB: "(\<integral>\<omega>. (\<omega> t $ l - \<omega> s $ l)^4 \<partial>L) \<le> 8*C\<^sup>2*(t - s)\<^sup>2" for l
    using st by (intro lim_coordinate_moment_package(2)[OF sL mom])
  have coord_tail: "measure L {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>}
      \<le> 8*C\<^sup>2*(t - s)\<^sup>2 / ec^4" for l
  proof -
    have "measure L {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>}
        \<le> (\<integral>\<omega>. (\<omega> t $ l - \<omega> s $ l)^4 \<partial>L) / ec^4"
      by (rule fourth_moment_tail[OF PL coordm int4 ec0])
    also have "\<dots> \<le> 8*C\<^sup>2*(t - s)\<^sup>2 / ec^4"
      by (intro divide_right_mono momB) (use ec0 in simp)
    finally show ?thesis .
  qed
  have coordS: "{\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>} \<in> sets L" for l
    using coordm by measurable
  have sub: "{\<omega> \<in> space L. e \<le> dist (\<omega> s) (\<omega> t)}
      \<subseteq> (\<Union>l\<in>UNIV. {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>})"
  proof
    fix \<omega> assume A: "\<omega> \<in> {\<omega> \<in> space L. e \<le> dist (\<omega> s) (\<omega> t)}"
    have w: "\<omega> \<in> space L" and de: "e \<le> dist (\<omega> s) (\<omega> t)" using A by auto
    have "\<exists>l. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>"
    proof (rule ccontr)
      assume "\<not> (\<exists>l. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>)"
      hence lt: "\<And>l. \<bar>\<omega> t $ l - \<omega> s $ l\<bar> < ec" by (auto simp: not_le)
      have "dist (\<omega> s) (\<omega> t) = norm (\<omega> t - \<omega> s)"
        by (simp add: dist_norm norm_minus_commute)
      also have "\<dots> \<le> (\<Sum>l\<in>UNIV. \<bar>(\<omega> t - \<omega> s) $ l\<bar>)"
        by (rule norm_le_l1_cart)
      also have "\<dots> = (\<Sum>l\<in>UNIV. \<bar>\<omega> t $ l - \<omega> s $ l\<bar>)"
        by simp
      also have "\<dots> < (\<Sum>l\<in>(UNIV::'m set). ec)"
        by (intro sum_strict_mono finite lt) simp_all
      also have "\<dots> = e"
        unfolding ec_def by (simp add: card_gt_0_iff)
      finally show False using de by linarith
    qed
    thus "\<omega> \<in> (\<Union>l\<in>UNIV. {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>})"
      using w by blast
  qed
  have US: "(\<Union>l\<in>UNIV. {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>}) \<in> sets L"
    by (intro sets.finite_UN) (use coordS in auto)
  have "measure L {\<omega> \<in> space L. e \<le> dist (\<omega> s) (\<omega> t)}
      \<le> measure L (\<Union>l\<in>UNIV. {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>})"
    by (rule P.finite_measure_mono[OF sub US])
  also have "\<dots> \<le> (\<Sum>l\<in>(UNIV::'m set).
      measure L {\<omega> \<in> space L. ec \<le> \<bar>\<omega> t $ l - \<omega> s $ l\<bar>})"
    by (rule P.finite_measure_subadditive_finite) (use coordS in auto)
  also have "\<dots> \<le> (\<Sum>l\<in>(UNIV::'m set). 8*C\<^sup>2*(t - s)\<^sup>2 / ec^4)"
    by (intro sum_mono coord_tail)
  also have "\<dots> = real (CARD('m)) * (8*C\<^sup>2*(t - s)\<^sup>2 / ec^4)"
    by simp
  also have "\<dots> = real (CARD('m)) * (8*C\<^sup>2*(t - s)\<^sup>2 * (real (CARD('m)))^4 / e^4)"
    unfolding ec_def by (simp add: power_divide)
  finally show ?thesis .
qed

theorem dyadic_ext_modification:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure" and C \<gamma> t :: real
  assumes PL: "prob_space L"
    and sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and mom: "\<And>l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
          \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and t0: "0 \<le> t"
  shows "AE \<omega> in L. dyadic_ext \<omega> t = \<omega> t"
proof -
  interpret P: prob_space L by (rule PL)
  define s where "s = (\<lambda>k. danchor k t)"
  have sk0: "0 \<le> s k" for k unfolding s_def by (rule danchor_nonneg[OF t0])
  have skt: "s k \<le> t" for k unfolding s_def by (rule danchor_le)
  have skgt: "t - 1/2^k < s k" for k unfolding s_def by (rule danchor_gt)
  define u where "u = (\<lambda>k (\<omega> :: real \<Rightarrow> real^'m).
      ennreal (min (dist (\<omega> (s k)) (\<omega> t)) 1))"
  have vm: "(\<lambda>\<omega>. \<omega> r) \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)" if "0 \<le> r" for r
    by (rule lim_vector_coordinate_measurable[OF sL that])
  have um: "u k \<in> borel_measurable L" for k
    unfolding u_def using vm[OF sk0[of k]] vm[OF t0] by measurable
  have ubnd: "(\<integral>\<^sup>+\<omega>. u k \<omega> \<partial>L) \<le> ennreal e
      + ennreal (real (CARD('m)) * (8*C\<^sup>2*(t - s k)\<^sup>2 * (real (CARD('m)))^4 / e^4))"
    if e: "0 < e" for k e
  proof -
    define A where "A = {\<omega> \<in> space L. e \<le> dist (\<omega> (s k)) (\<omega> t)}"
    have Am: "A \<in> sets L"
      unfolding A_def using vm[OF sk0[of k]] vm[OF t0] by measurable
    have ple: "u k \<omega> \<le> ennreal e + indicator A \<omega>" if w: "\<omega> \<in> space L" for \<omega>
    proof (cases "\<omega> \<in> A")
      case True
      hence i1: "indicator A \<omega> = (1::ennreal)" by simp
      have "u k \<omega> \<le> ennreal 1"
        unfolding u_def by (intro ennreal_leI) simp
      also have "ennreal 1 \<le> ennreal e + 1"
        by (simp add: add_increasing)
      finally show ?thesis unfolding i1 .
    next
      case False
      hence dlt: "dist (\<omega> (s k)) (\<omega> t) < e"
        unfolding A_def using w by (auto simp: not_le)
      have "u k \<omega> \<le> ennreal e"
        unfolding u_def
        by (intro ennreal_leI order_trans[OF min.cobounded1]) (use dlt in linarith)
      thus ?thesis by (simp add: indicator_def False)
    qed
    have "(\<integral>\<^sup>+\<omega>. u k \<omega> \<partial>L) \<le> (\<integral>\<^sup>+\<omega>. ennreal e + indicator A \<omega> \<partial>L)"
      by (rule nn_integral_mono) (rule ple)
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal e \<partial>L) + (\<integral>\<^sup>+\<omega>. indicator A \<omega> \<partial>L)"
      by (rule nn_integral_add) (use Am in auto)
    also have "\<dots> = ennreal e + emeasure L A"
      by (simp add: P.emeasure_space_1 nn_integral_indicator[OF Am])
    also have "\<dots> \<le> ennreal e
        + ennreal (real (CARD('m)) * (8*C\<^sup>2*(t - s k)\<^sup>2 * (real (CARD('m)))^4 / e^4))"
    proof -
      have "emeasure L A = ennreal (measure L A)"
        by (rule P.emeasure_eq_measure)
      also have "\<dots> \<le> ennreal (real (CARD('m))
          * (8*C\<^sup>2*(t - s k)\<^sup>2 * (real (CARD('m)))^4 / e^4))"
        unfolding A_def
        by (intro ennreal_leI lim_vector_increment_tail[OF PL sL mom sk0 skt e])
      finally show ?thesis by (rule add_left_mono)
    qed
    finally show ?thesis .
  qed
  have mainc: "(\<lambda>k. u k \<omega>) \<longlonglongrightarrow> ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1)"
    if good: "\<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
    for \<omega> :: "real \<Rightarrow> real^'m"
  proof -
    define TT where "TT = nat \<lfloor>t\<rfloor> + 1"
    have e1: "real (nat \<lfloor>t\<rfloor>) = of_int \<lfloor>t\<rfloor>" using t0 by simp
    have t2: "t \<le> 1 + real_of_int \<lfloor>t\<rfloor>" by linarith
    have tmem: "t \<in> {0..real TT}"
      unfolding TT_def using t0 t2 e1 by simp
    have gTT: "\<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real TT\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
      using good by blast
    obtain nl where nl: "\<forall>l. \<forall>j\<ge>nl l. \<forall>k\<in>{1..\<lfloor>2^j * real TT\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
      using choice[OF gTT] by blast
    define n0 where "n0 = Max (range nl)"
    have vecgood: "dist (\<omega> (real_of_int (k - 1) / 2^j)) (\<omega> (real_of_int k / 2^j))
        \<le> real (CARD('m)) * 2 powr (-\<gamma>*real j)"
      if jk: "n0 \<le> j" "k \<in> {1..\<lfloor>2^j * real TT\<rfloor>}" for j k
    proof -
      have coord: "\<bar>\<omega> (real_of_int k / 2^j) $ l
          - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar> \<le> 2 powr (-\<gamma>*real j)" for l
      proof -
        have "nl l \<le> n0"
          unfolding n0_def by (intro Max_ge finite_imageI) auto
        hence "nl l \<le> j" using jk(1) by linarith
        thus ?thesis using nl jk(2) by blast
      qed
      have "dist (\<omega> (real_of_int (k - 1) / 2^j)) (\<omega> (real_of_int k / 2^j))
          = norm (\<omega> (real_of_int (k - 1) / 2^j) - \<omega> (real_of_int k / 2^j))"
        by (rule dist_norm)
      also have "\<dots> \<le> (\<Sum>l\<in>UNIV. \<bar>(\<omega> (real_of_int (k - 1) / 2^j)
          - \<omega> (real_of_int k / 2^j)) $ l\<bar>)"
        by (rule norm_le_l1_cart)
      also have "\<dots> = (\<Sum>l\<in>UNIV. \<bar>\<omega> (real_of_int k / 2^j) $ l
          - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>)"
        by (intro sum.cong refl) (simp add: abs_minus_commute)
      also have "\<dots> \<le> (\<Sum>l\<in>(UNIV::'m set). 2 powr (-\<gamma>*real j))"
        by (rule sum_mono) (rule coord)
      also have "\<dots> = real (CARD('m)) * 2 powr (-\<gamma>*real j)"
        by simp
      finally show ?thesis .
    qed
    have E0: "0 \<le> real (CARD('m))" by simp
    have conv: "(\<lambda>k. \<omega> (s k)) \<longlonglongrightarrow> dyadic_ext \<omega> t"
      unfolding s_def
      by (rule dyadic_ext_tendsto[OF vecgood g0 E0 tmem])
    have "(\<lambda>k. dist (\<omega> (s k)) (\<omega> t)) \<longlonglongrightarrow> dist (dyadic_ext \<omega> t) (\<omega> t)"
      by (rule tendsto_dist[OF conv tendsto_const])
    hence "(\<lambda>k. min (dist (\<omega> (s k)) (\<omega> t)) 1)
        \<longlonglongrightarrow> min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1"
      by (intro tendsto_min tendsto_const)
    thus ?thesis
      unfolding u_def by (intro tendsto_ennrealI)
  qed
  have aeconv: "AE \<omega> in L. (\<lambda>k. u k \<omega>)
      \<longlonglongrightarrow> ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1)"
  proof (rule AE_mp[OF lim_dyadic_good_AE[OF PL sL mom g0 g2]])
    show "AE \<omega> in L. (\<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j))
        \<longrightarrow> (\<lambda>k. u k \<omega>) \<longlonglongrightarrow> ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1)"
      by (rule AE_I2) (use mainc in blast)
  qed
  have key: "(\<integral>\<^sup>+\<omega>. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1) \<partial>L) \<le> ennreal e"
    if e: "0 < e" for e
  proof -
    define c where "c = real (CARD('m)) * (8*C\<^sup>2 * (real (CARD('m)))^4 / e^4)"
    have beq: "real (CARD('m)) * (8*C\<^sup>2*(t - s k)\<^sup>2 * (real (CARD('m)))^4 / e^4)
        = c * (t - s k)\<^sup>2" for k
      unfolding c_def by (simp add: algebra_simps)
    have half0: "(\<lambda>k. (1::real)/2^k) \<longlonglongrightarrow> 0"
    proof -
      have "(\<lambda>k. ((1::real)/2)^k) \<longlonglongrightarrow> 0"
        by (rule LIMSEQ_realpow_zero) simp_all
      thus ?thesis by (simp add: power_one_over)
    qed
    have ts0: "(\<lambda>k. t - s k) \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich[OF _ _ tendsto_const half0])
      show "\<forall>\<^sub>F k in sequentially. 0 \<le> t - s k"
      proof (intro always_eventually allI)
        fix k show "0 \<le> t - s k" using skt[of k] by linarith
      qed
      show "\<forall>\<^sub>F k in sequentially. t - s k \<le> 1/2^k"
      proof (intro always_eventually allI)
        fix k show "t - s k \<le> 1/2^k" using skgt[of k] by linarith
      qed
    qed
    have sq0: "(\<lambda>k. (t - s k)\<^sup>2) \<longlonglongrightarrow> 0"
      using tendsto_power[OF ts0, of 2] by simp
    have b0: "(\<lambda>k. c * (t - s k)\<^sup>2) \<longlonglongrightarrow> 0"
      by (rule tendsto_mult_right_zero[OF sq0])
    have blim: "(\<lambda>k. ennreal e + ennreal (c * (t - s k)\<^sup>2)) \<longlonglongrightarrow> ennreal e"
    proof -
      have "(\<lambda>k. ennreal (c * (t - s k)\<^sup>2)) \<longlonglongrightarrow> ennreal 0"
        by (intro tendsto_ennrealI b0)
      hence "(\<lambda>k. ennreal e + ennreal (c * (t - s k)\<^sup>2))
          \<longlonglongrightarrow> ennreal e + ennreal 0"
        by (intro tendsto_add tendsto_const)
      thus ?thesis by simp
    qed
    have aeL: "AE \<omega> in L. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1)
        = liminf (\<lambda>k. u k \<omega>)"
      by (rule eventually_mono[OF aeconv])
         (simp add: lim_imp_Liminf[OF trivial_limit_sequentially])
    have "(\<integral>\<^sup>+\<omega>. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1) \<partial>L)
        = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>k. u k \<omega>) \<partial>L)"
      by (rule nn_integral_cong_AE[OF aeL])
    also have "\<dots> \<le> liminf (\<lambda>k. \<integral>\<^sup>+\<omega>. u k \<omega> \<partial>L)"
      by (rule nn_integral_liminf[OF um])
    also have "\<dots> \<le> liminf (\<lambda>k. ennreal e + ennreal (c * (t - s k)\<^sup>2))"
      by (intro Liminf_mono always_eventually allI)
         (use ubnd[OF e] beq in simp)
    also have "\<dots> = ennreal e"
      by (rule lim_imp_Liminf[OF trivial_limit_sequentially blim])
    finally show ?thesis .
  qed
  have zero: "(\<integral>\<^sup>+\<omega>. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1) \<partial>L) = 0"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1) \<partial>L) \<le> 0"
      by (rule ennreal_le_epsilon) (use key in simp)
    thus ?thesis by simp
  qed
  have msble: "(\<lambda>\<omega>. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1))
      \<in> borel_measurable L"
    using dyadic_ext_measurable[OF sL t0] vm[OF t0] by measurable
  have ae0: "AE \<omega> in L. ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1) = 0"
    using nn_integral_0_iff_AE[OF msble] zero by simp
  show ?thesis
  proof (rule eventually_mono[OF ae0])
    fix \<omega> :: "real \<Rightarrow> real^'m"
    assume z: "ennreal (min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1) = 0"
    have mnn: "0 \<le> min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1"
      by (auto simp: min_def)
    have le0: "min (dist (dyadic_ext \<omega> t) (\<omega> t)) 1 = 0"
      using z mnn by simp
    have d0: "dist (dyadic_ext \<omega> t) (\<omega> t) = 0"
      using le0 by (auto simp: min_def split: if_split_asm)
    show "dyadic_ext \<omega> t = \<omega> t"
      using d0 by simp
  qed
qed

subsection \<open>The continuous modification, assembled (plan item A3 complete)\<close>

text \<open>
  The bundle: from the moment package alone, the projective limit carries a
  process \<open>Y\<close> with measurable time sections, EVERYWHERE-continuous paths on
  \<open>{0..}\<close>, and \<open>Y t = \<omega> t\<close> almost surely at every time — a continuous
  modification of the coordinate process. \<open>Y\<close> is \<open>dyadic_ext\<close> gated on the
  measurable almost-sure good set.
\<close>

theorem lim_continuous_modification:
  fixes L :: "(real \<Rightarrow> real^'m::finite) measure" and C \<gamma> :: real
  assumes PL: "prob_space L"
    and sL: "sets L = sets (PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure))"
    and mom: "\<And>l u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow>
        (\<integral>\<^sup>+\<omega>. ennreal ((\<omega> v $ l - \<omega> u $ l)^4) \<partial>L)
          \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
  shows "\<exists>Y :: real \<Rightarrow> (real \<Rightarrow> real^'m) \<Rightarrow> real^'m.
      (\<forall>t\<ge>0. Y t \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure))
      \<and> (\<forall>\<omega>. continuous_on {0..} (\<lambda>t. Y t \<omega>))
      \<and> (\<forall>t\<ge>0. AE \<omega> in L. Y t \<omega> = \<omega> t)"
proof -
  define G where "G = {\<omega> \<in> space L. \<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n.
      \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
        \<le> 2 powr (-\<gamma>*real j)}"
  have GS: "G \<in> sets L"
    unfolding G_def by (rule lim_good_set[OF sL])
  define Y where "Y = (\<lambda>t (\<omega> :: real \<Rightarrow> real^'m).
      if \<omega> \<in> G then dyadic_ext \<omega> t else 0)"
  have vecT: "\<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
      dist (\<omega> (real_of_int (k - 1) / 2^j)) (\<omega> (real_of_int k / 2^j))
        \<le> real (CARD('m)) * 2 powr (-\<gamma>*real j)"
    if wG: "\<omega> \<in> G" for \<omega> :: "real \<Rightarrow> real^'m" and T :: nat
  proof -
    have gTT: "\<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
      using wG unfolding G_def by blast
    obtain nl where nl: "\<forall>l. \<forall>j\<ge>nl l. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
        \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
          \<le> 2 powr (-\<gamma>*real j)"
      using choice[OF gTT] by blast
    define n0 where "n0 = Max (range nl)"
    have vg: "dist (\<omega> (real_of_int (k - 1) / 2^j)) (\<omega> (real_of_int k / 2^j))
        \<le> real (CARD('m)) * 2 powr (-\<gamma>*real j)"
      if jk: "n0 \<le> j" "k \<in> {1..\<lfloor>2^j * real T\<rfloor>}" for j k
    proof -
      have coord: "\<bar>\<omega> (real_of_int k / 2^j) $ l
          - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar> \<le> 2 powr (-\<gamma>*real j)" for l
      proof -
        have "nl l \<le> n0"
          unfolding n0_def by (intro Max_ge finite_imageI) auto
        hence "nl l \<le> j" using jk(1) by linarith
        thus ?thesis using nl jk(2) by blast
      qed
      have "dist (\<omega> (real_of_int (k - 1) / 2^j)) (\<omega> (real_of_int k / 2^j))
          = norm (\<omega> (real_of_int (k - 1) / 2^j) - \<omega> (real_of_int k / 2^j))"
        by (rule dist_norm)
      also have "\<dots> \<le> (\<Sum>l\<in>UNIV. \<bar>(\<omega> (real_of_int (k - 1) / 2^j)
          - \<omega> (real_of_int k / 2^j)) $ l\<bar>)"
        by (rule norm_le_l1_cart)
      also have "\<dots> = (\<Sum>l\<in>UNIV. \<bar>\<omega> (real_of_int k / 2^j) $ l
          - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>)"
        by (intro sum.cong refl) (simp add: abs_minus_commute)
      also have "\<dots> \<le> (\<Sum>l\<in>(UNIV::'m set). 2 powr (-\<gamma>*real j))"
        by (rule sum_mono) (rule coord)
      also have "\<dots> = real (CARD('m)) * 2 powr (-\<gamma>*real j)"
        by simp
      finally show ?thesis .
    qed
    show ?thesis
      by (intro exI[of _ n0] allI impI ballI vg)
  qed
  have E0: "0 \<le> real (CARD('m))" by simp
  show ?thesis
  proof (intro exI[of _ Y] conjI allI impI)
    show "\<And>t. 0 \<le> t \<Longrightarrow> Y t \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)"
    proof -
      fix t :: real assume t0: "0 \<le> t"
      have m1: "(\<lambda>\<omega>. dyadic_ext \<omega> t) \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)"
        by (rule dyadic_ext_measurable[OF sL t0])
      show "Y t \<in> L \<rightarrow>\<^sub>M (borel :: (real^'m) measure)"
        unfolding Y_def using m1 GS by measurable
    qed
    show "\<And>\<omega>. continuous_on {0..} (\<lambda>t. Y t \<omega>)"
    proof -
      fix \<omega> :: "real \<Rightarrow> real^'m"
      show "continuous_on {0..} (\<lambda>t. Y t \<omega>)"
      proof (cases "\<omega> \<in> G")
        case True
        have "continuous_on {0..} (dyadic_ext \<omega>)"
          by (rule dyadic_ext_continuous_on_all[OF vecT[OF True] g0 E0])
        thus ?thesis unfolding Y_def using True by simp
      next
        case False
        show ?thesis unfolding Y_def using False by simp
      qed
    qed
    show "\<And>t. 0 \<le> t \<Longrightarrow> AE \<omega> in L. Y t \<omega> = \<omega> t"
    proof -
      fix t :: real assume t0: "0 \<le> t"
      have aeG: "AE \<omega> in L. \<omega> \<in> G"
      proof (rule AE_mp[OF lim_dyadic_good_AE[OF PL sL mom g0 g2] AE_I2])
        fix \<omega> assume w: "\<omega> \<in> space L"
        show "(\<forall>T::nat. \<forall>l. \<exists>n. \<forall>j\<ge>n. \<forall>k\<in>{1..\<lfloor>2^j * real T\<rfloor>}.
            \<bar>\<omega> (real_of_int k / 2^j) $ l - \<omega> (real_of_int (k - 1) / 2^j) $ l\<bar>
              \<le> 2 powr (-\<gamma>*real j)) \<longrightarrow> \<omega> \<in> G"
          unfolding G_def using w by blast
      qed
      have aeE: "AE \<omega> in L. dyadic_ext \<omega> t = \<omega> t"
        by (rule dyadic_ext_modification[OF PL sL mom g0 g2 t0])
      show "AE \<omega> in L. Y t \<omega> = \<omega> t"
        using aeG aeE by eventually_elim (simp add: Y_def)
    qed
  qed
qed

subsection \<open>Currying toward the \<open>P_x\<close> sample type (plan item A4, first piece)\<close>

text \<open>
  The flip map from time-indexed vector paths to coordinate-indexed real
  paths — the direction along which the limit law will be transported to the
  \<open>('n \<Rightarrow> real \<Rightarrow> real) measure\<close> sample type that \<open>mkt_exit_vals\<close> fixes.
\<close>

lemma flip_measurable:
  "(\<lambda>\<omega> :: real \<Rightarrow> real^'m::finite. \<lambda>l\<in>(UNIV::'m set). \<lambda>t\<in>({0..}::real set). \<omega> t $ l)
      \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
        \<rightarrow>\<^sub>M PiM (UNIV :: 'm set) (\<lambda>_. PiM ({0..} :: real set) (\<lambda>_. borel :: real measure))"
proof (rule measurable_restrict)
  fix l assume "l \<in> (UNIV :: 'm set)"
  show "(\<lambda>\<omega> :: real \<Rightarrow> real^'m. \<lambda>t\<in>({0..}::real set). \<omega> t $ l)
      \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
        \<rightarrow>\<^sub>M PiM ({0..} :: real set) (\<lambda>_. borel :: real measure)"
  proof (rule measurable_restrict)
    fix t assume t: "t \<in> ({0..} :: real set)"
    have c: "(\<lambda>\<omega>. \<omega> t) \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure)
        \<rightarrow>\<^sub>M borel"
      using t by (intro measurable_component_singleton) simp
    show "(\<lambda>\<omega> :: real \<Rightarrow> real^'m. \<omega> t $ l)
        \<in> PiM ({0..} :: real set) (\<lambda>_. borel :: (real^'m) measure) \<rightarrow>\<^sub>M borel"
      by (rule measurable_compose[OF c borel_measurable_nth])
  qed
qed


text \<open>RQ-A's final piece: weak convergence UPGRADED by uniform integrability.

  \<open>weak_conv_on_nn_integral_le\<close> below handles a non-negative integrand and gives
  an UPPER bound on the limit, by truncating at \<open>K\<close> and letting monotone
  convergence do the work --- no integrability hypothesis at all.  That covers
  exactly the \<open>\<preceq> L\<cdot>I\<close> half of the covariation constraint.

  It does NOT cover the other half.  The constraint set also carries LOWER
  bounds (\<open>\<Pi>\<^sub>m(a) \<ge> m-k\<close>), and for those the inequality runs the other way, where
  weak convergence gives only the Fatou direction \<open>liminf \<ge> lim\<close>.  Recovering
  \<open>limsup \<le>\<close> is exactly what uniform integrability buys, and this is the lemma
  that buys it.

  The argument is the \<open>3\<epsilon>\<close> one: truncate \<open>f\<close> at height \<open>R\<close> --- the truncation is
  bounded and continuous, so weak convergence applies to it directly --- and
  control both truncation errors by the tail hypothesis.  All three pieces are
  already proved: \<open>Increment_Moments.clamp_integral_error\<close> for the errors,
  \<open>Increment_Moments.tendsto_real_of_approximants\<close> for the limit passage, and
  \<open>Increment_Moments.sq_tail_bound_of_fourth_moment\<close> supplies \<open>ui\<close> in the
  application from the fourth-moment bound of Eq. (2.7).

  The integrability side conditions are hypotheses rather than derived: in the
  application they all come from the moment bounds, and deriving them here would
  obscure the one idea.\<close>

lemma weak_conv_on_integral_unif_integrable:
  fixes f :: "'b \<Rightarrow> real" and Ni :: "nat \<Rightarrow> 'b measure"
  assumes wc: "weak_conv_on Ni N sequentially X"
    and f: "continuous_map X euclideanreal f"
    and fmi: "\<And>i. finite_measure (Ni i)" and fmN: "finite_measure N"
    and iNi: "\<And>i. integrable (Ni i) f" and iN: "integrable N f"
    and iCi: "\<And>i R. integrable (Ni i) (\<lambda>x. max (- R) (min R (f x)))"
    and iCN: "\<And>R. integrable N (\<lambda>x. max (- R) (min R (f x)))"
    and iTi: "\<And>i R. integrable (Ni i)
        (\<lambda>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x))"
    and iTN: "\<And>R. integrable N
        (\<lambda>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x))"
    and ui: "\<And>e. 0 < e \<Longrightarrow> \<exists>R. 0 \<le> R
        \<and> (\<forall>i. (\<integral>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x) \<partial>(Ni i)) \<le> e)
        \<and> (\<integral>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x) \<partial>N) \<le> e"
  shows "(\<lambda>i. \<integral>x. f x \<partial>(Ni i)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>N)"
proof (rule tendsto_real_of_approximants)
  fix e :: real assume e: "0 < e"
  obtain R where R0: "0 \<le> R"
    and tNi: "\<And>i. (\<integral>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x) \<partial>(Ni i)) \<le> e"
    and tN: "(\<integral>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x) \<partial>N) \<le> e"
    using ui[OF e] by blast
  \<comment> \<open>the truncation is bounded and continuous, so weak convergence applies\<close>
  have cc: "continuous_map X euclideanreal (\<lambda>x. max (- R) (min R (f x)))"
    by (intro continuous_map_real_max continuous_map_real_min f) simp_all
  have cb: "\<exists>B. \<forall>x\<in>topspace X. \<bar>max (- R) (min R (f x))\<bar> \<le> B"
  proof -
    have "\<bar>max (- R) (min R (f x))\<bar> \<le> R" for x using R0 by simp
    thus ?thesis by blast
  qed
  have lim: "(\<lambda>i. \<integral>x. max (- R) (min R (f x)) \<partial>(Ni i))
      \<longlonglongrightarrow> (\<integral>x. max (- R) (min R (f x)) \<partial>N)"
    using wc[unfolded weak_conv_on_def] cc cb by blast
  \<comment> \<open>and the two truncation errors are the tails\<close>
  have errNi: "\<bar>(\<integral>x. f x \<partial>(Ni i)) - (\<integral>x. max (- R) (min R (f x)) \<partial>(Ni i))\<bar> \<le> e"
    for i
  proof -
    have "\<bar>(\<integral>x. f x \<partial>(Ni i)) - (\<integral>x. max (- R) (min R (f x)) \<partial>(Ni i))\<bar>
        \<le> (\<integral>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x) \<partial>(Ni i))"
      by (rule clamp_integral_error[OF fmi R0 iNi iCi iTi])
    also have "\<dots> \<le> e" by (rule tNi)
    finally show ?thesis .
  qed
  have errN: "\<bar>(\<integral>x. max (- R) (min R (f x)) \<partial>N) - (\<integral>x. f x \<partial>N)\<bar> \<le> e"
  proof -
    have "\<bar>(\<integral>x. f x \<partial>N) - (\<integral>x. max (- R) (min R (f x)) \<partial>N)\<bar>
        \<le> (\<integral>x. \<bar>f x\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f x) \<partial>N)"
      by (rule clamp_integral_error[OF fmN R0 iN iCN iTN])
    with tN show ?thesis by (simp add: abs_minus_commute)
  qed
  show "\<exists>y w. (\<forall>m. \<bar>(\<integral>x. f x \<partial>(Ni m)) - y m\<bar> \<le> e)
      \<and> (y \<longlonglongrightarrow> w) \<and> \<bar>w - (\<integral>x. f x \<partial>N)\<bar> \<le> e"
    by (intro exI[of _ "\<lambda>m. \<integral>x. max (- R) (min R (f x)) \<partial>(Ni m)"]
               exI[of _ "\<integral>x. max (- R) (min R (f x)) \<partial>N"]
               conjI allI errNi lim errN)
qed

end
