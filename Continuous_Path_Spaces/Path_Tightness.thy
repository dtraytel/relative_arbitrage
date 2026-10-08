section \<open>Tightness of the path laws\<close>

(*<*)
theory Path_Tightness
  imports Path_Space Holder_Interpolation
begin

(*>*)

text \<open>
  Laws of processes satisfying the uniform fourth-moment package of
  Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> form a tight family on \<open>C({0..T})\<close>: \<open>dyadic_bad_event_tail_mom\<close>
  (@{theory Continuous_Path_Spaces.Modulus_Tails}) bounds the probability some dyadic increment at level
  \<open>j \<ge> n\<close> is large; on the complement, \<open>modulus_of_good_path\<close> and
  \<open>holder_of_dyadic_moduli\<close> (@{theory Continuous_Path_Spaces.Holder_Interpolation}) place the path in an
  explicit H\"older ball, compact by \<open>compactin_path_holder_ball\<close>
  (@{theory Continuous_Path_Spaces.Path_Space}). Large \<open>n\<close> makes the exceptional mass uniformly small --
  exactly \<open>tight_on_set\<close>, the hypothesis of the AFP's
  \<open>Prokhorov_theorem_LP\<close>.
\<close>
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
  \<open>(\<gamma>, T, n)\<close> only, so the resulting compact ball is common to every law
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
  let ?PS = "(path_borel T :: (real \<Rightarrow> real) measure)"
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
      \<and> sets (path_borel T :: (real \<Rightarrow> real) measure)
        = sets N"
  proof
    fix N assume "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I"
    then obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T" by blast
    have Xm': "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
      using that by (intro Xm[OF i]) simp
    have PN: "prob_space N"
      unfolding Ni by (rule prob_space_path_law[OF P[OF i] T0 Xm' cont[OF i]])
    have fN: "finite_measure N" by (rule prob_space.axioms(1)[OF PN])
    have sN: "sets (path_borel T :: (real \<Rightarrow> real) measure)
        = sets N"
      unfolding Ni by (rule sets_path_law[symmetric])
    show "finite_measure N
        \<and> sets (path_borel T :: (real \<Rightarrow> real) measure)
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

subsection \<open>The subsequence extraction of Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close>, per horizon\<close>

text \<open>
  Combining the tightness theorem with the AFP's
  \<open>tight_on_set_imp_convergent_subsequence\<close>: every sequence of laws whose
  processes satisfy the uniform Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> package has a weakly convergent
  subsequence on \<open>C({0..T})\<close>. This is the relative-compactness content of
  Lemma 2.2 at a fixed horizon; the \<open>C([0,\<infinity>))\<close> statement extends it to
  unbounded time.
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
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> real) measure)
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
  The paths of \<^cite>\<open>LaiShkolnikovSoner\<close> are \<open>\<real>\<^sup>n\<close>-valued while the moment machinery above
  is real-valued; this layer closes the gap coordinatewise. The bad event
  is the union of the coordinate bad events (factor \<open>CARD('m)\<close> by the union
  bound); on its complement every coordinate is H\"older, so the vector path
  is H\"older with constant \<open>CARD('m) * holder_const \<gamma> T n\<close> via
  \<open>norm_le_l1_cart\<close>, and the compact ball comes from
  \<open>compactin_path_holder_ball\<close> at \<open>'b = real^'m\<close>.
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
  let ?PS = "(path_borel T :: (real \<Rightarrow> real^'m) measure)"
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
      \<and> sets (path_borel T :: (real \<Rightarrow> real^'m) measure)
        = sets N"
  proof
    fix N assume "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I"
    then obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T" by blast
    have Xm': "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
      using that by (intro Xm[OF i]) simp
    have PN: "prob_space N"
      unfolding Ni by (rule prob_space_path_law[OF P[OF i] T0 Xm' cont[OF i]])
    have fN: "finite_measure N" by (rule prob_space.axioms(1)[OF PN])
    have sN: "sets (path_borel T :: (real \<Rightarrow> real^'m) measure)
        = sets N"
      unfolding Ni by (rule sets_path_law[symmetric])
    show "finite_measure N
        \<and> sets (path_borel T :: (real \<Rightarrow> real^'m) measure)
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
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> real^'m) measure)
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
  From a horizon-uniform moment package, a single subsequence along which the
  path laws converge weakly at every integer horizon simultaneously. Built on
  HOL-Library's \<open>Diagonal_Subsequence\<close> (locale \<open>subseqs\<close>, reachable through
  HOL-Probability); subsequence-stability of weak convergence is
  \<open>limitin_subsequence\<close>, and the tail shift is absorbed by
  \<open>limitin_sequentially_offset_rev\<close>.
\<close>

subsection \<open>Consistency of the diagonal limits across horizons\<close>

text \<open>
  The per-horizon limit laws of the diagonal subsequence form a projective
  family: restricting the horizon-\<open>m'\<close> limit to \<open>{0..m}\<close> gives the
  horizon-\<open>m\<close> limit. The restriction map is continuous
  (\<open>Lipschitz_restrict_path_metric\<close>), so \<open>weak_conv_on_pushforward\<close>
  carries the horizon-\<open>m'\<close> convergence to the restricted laws, identified
  with the horizon-\<open>m\<close> limit by uniqueness of weak limits (the weak
  topology is metrizable, hence Hausdorff).
\<close>

subsection \<open>The projective-limit assembly\<close>

text \<open>
  From the horizon-consistent family of limit laws
  (\<open>path_laws_diagonal_consistent\<close>) to a single probability measure on the
  full-time function space with the product sigma-algebra, via the
  Daniell--Kolmogorov theorem (\<open>HOL-Probability.Projective_Limit\<close>, locale
  \<open>polish_projective\<close>). The finite-dimensional marginals are pushforwards
  of the \<open>N m\<close> under the (measurable) restriction maps, immaterial to
  horizon choice by the consistency identity. \<open>unfold_locales\<close> on
  \<open>polish_projective\<close> decomposes \<open>prob_space (P J)\<close> into its three
  ancestor axioms (sigma-finite cover, finiteness, total mass one) --
  discharge those, not the locale predicate.
\<close>

lemma marginal_map_measurable:
  fixes T :: real
  assumes J: "finite J" "J \<subseteq> {0..T}"
  shows "(\<lambda>g. restrict g J)
      \<in> (path_borel T :: (real \<Rightarrow> real^'m::finite) measure)
        \<rightarrow>\<^sub>M PiM J (\<lambda>_. borel :: (real^'m) measure)"
proof -
  have ev: "(\<lambda>g. g t) \<in> (path_borel T :: (real \<Rightarrow> real^'m) measure) \<rightarrow>\<^sub>M borel"
    if t: "t \<in> J" for t
    using continuous_map_measurable[OF continuous_map_path_eval[OF subsetD[OF J(2) t]]]
    by (simp add: borel_of_euclidean)
  show ?thesis
    by (rule measurable_restrict) (rule ev)
qed

text \<open>The Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> package holds for the coordinates of the projective
  limit --- the increment moment is a function of a two-point marginal, and
  marginals are inherited from the \<open>N m\<close>. This is the input for running the
  dyadic modulus machinery on \<open>L\<close> and building the continuous
  modification.\<close>

subsection \<open>The dyadic extension operator\<close>

text \<open>
  A path controlled only on the dyadics extends to a continuous function:
  \<open>dyadic_pair_modulus\<close> is the continuity-free chaining bound for pairs of
  dyadics (\<open>dyadic_chaining\<close>, any metric space); the anchor sequences
  \<open>danchor k t\<close> are then Cauchy, and \<open>dyadic_ext\<close> takes their limit,
  agreeing with the original path at dyadic points, with the same modulus
  at every level, continuous on \<open>{0..T}\<close>. Applied pathwise on the good
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

subsection \<open>The good-dyadics event of the projective limit is almost sure\<close>

text \<open>
  The coordinates of the projective limit are measurable and carry the
  Bochner form of the Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> package (adapted from the \<open>nn_integral\<close>
  bound). Via \<open>dyadic_bad_event_tail_mom\<close> at every integer horizon and
  coordinate, with geometric level bounds forcing the intersection over
  levels to be null, almost every \<open>\<omega>\<close> satisfies the dyadic moduli from
  some level on, everywhere simultaneously; on this event \<open>dyadic_ext\<close>
  builds the continuous modification.
\<close>

text \<open>Continuity of the extension on all of \<open>{0..}\<close> from per-horizon good
  bounds (each point sits inside some integer horizon, and \<open>dyadic_ext\<close> is
  horizon-free), plus the measurable good set of the projective limit ---
  the strict-threshold bad events have the same countable-union structure,
  and the good set is the complement assembled by \<open>countable_INT'\<close>/UN.\<close>

text \<open>Per-time measurability of the extension: \<open>dyadic_ext\<close> is definitionally
  a \<open>lim\<close> along the (nonnegative, by \<open>danchor_nonneg\<close>) anchor sequence, so
  \<open>borel_measurable_lim_metric\<close> applies directly.\<close>

subsection \<open>The continuous modification, assembled\<close>

text \<open>
  The bundle: from the moment package alone, the projective limit carries a
  process \<open>Y\<close> with measurable time sections, everywhere-continuous paths on
  \<open>{0..}\<close>, and \<open>Y t = \<omega> t\<close> almost surely at every time --- a continuous
  modification of the coordinate process. \<open>Y\<close> is \<open>dyadic_ext\<close> gated on the
  measurable almost-sure good set.
\<close>

subsection \<open>Currying toward the \<open>P_x\<close> sample type\<close>

text \<open>
  The flip map from time-indexed vector paths to coordinate-indexed real
  paths --- the direction along which the limit law will be transported to the
  \<open>('n \<Rightarrow> real \<Rightarrow> real) measure\<close> sample type that the application's sample type fixes.
\<close>

text \<open>Weak convergence upgraded by uniform integrability.  \<open>weak_conv_on_nn_integral_le\<close>
  handles a non-negative integrand and bounds the limit above by truncating
  at \<open>K\<close> and using monotone convergence, with no integrability hypothesis --
  covering the \<open>\<preceq> L \<cdot> I\<close> half of the covariation constraint.

  The lower bounds \<open>\<Pi>\<^sub>m(a) \<ge> m-k\<close> run the other way, where weak
  convergence only gives the Fatou direction \<open>liminf \<ge> lim\<close>; recovering
  \<open>limsup \<le>\<close> is what uniform integrability buys, via the \<open>3\<epsilon>\<close> argument:
  truncate \<open>f\<close> at height \<open>R\<close> (bounded and continuous, so weak convergence
  applies directly) and control both truncation errors by the tail
  hypothesis, using \<open>Increment_Moments.clamp_integral_error\<close>,
  \<open>Increment_Moments.tendsto_real_of_approximants\<close>, and
  \<open>Increment_Moments.sq_tail_bound_of_fourth_moment\<close> for uniform
  integrability from the fourth-moment bound of Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close>.

  The integrability side conditions are kept as hypotheses, since in the
  application they all come from the moment bounds.\<close>

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


subsection \<open>Transfer along weak convergence, and equality of metric measures\<close>

text \<open>Passing an integral to a weak limit when the family is uniformly
  integrable --- which an \<open>L\<^sup>2\<close> bound supplies --- and recognising two
  measures on a metric space as equal, or ordered, from their integrals
  against bounded continuous functions alone.\<close>

text \<open>Total mass survives a weak limit: test against the constant \<open>1\<close>.\<close>

text \<open>A finite Borel measure on a metric space is determined by its
  integrals against bounded continuous functions: apply the closed-set
  Portmanteau bound to the constant sequence both ways, then extend from
  closed sets (\<open>sets_borel_of_closed\<close>) by \<open>measure_eqI_generator_eq\<close>.
  This monotone-class engine upgrades the integrated identities on
  closure points from continuous past functionals to arbitrary past
  events.\<close>

lemma metric_measure_eqI_bounded_cts:
  fixes m :: "'a metric" and M1 M2 :: "'a measure"
  assumes s1: "sets M1 = sets (borel_of (mtopology_of m))"
    and s2: "sets M2 = sets (borel_of (mtopology_of m))"
    and f1: "finite_measure M1" and f2: "finite_measure M2"
    and eq: "\<And>g. continuous_map (mtopology_of m) euclideanreal g \<Longrightarrow>
        \<exists>B. \<forall>x\<in>topspace (mtopology_of m). \<bar>g x\<bar> \<le> B \<Longrightarrow>
        (\<integral>x. g x \<partial>M1) = (\<integral>x. g x \<partial>M2)"
  shows "M1 = M2"
proof -
  interpret PM: Metric_space "mspace m" "mdist m"
    by (rule Metric_space_mspace_mdist)
  have top: "PM.mtopology = mtopology_of m"
    by (simp add: mtopology_of_def)
  have tsp: "topspace (mtopology_of m) = mspace m"
    using top PM.topspace_mtopology by simp
  have le: "measure Ma A \<le> measure Mb A"
    if sa: "sets Ma = sets (borel_of (mtopology_of m))"
    and sb: "sets Mb = sets (borel_of (mtopology_of m))"
    and fa: "finite_measure Ma" and fb: "finite_measure Mb"
    and eqab: "\<And>g. continuous_map (mtopology_of m) euclideanreal g \<Longrightarrow>
        \<exists>B. \<forall>x\<in>topspace (mtopology_of m). \<bar>g x\<bar> \<le> B \<Longrightarrow>
        (\<integral>x. g x \<partial>Ma) = (\<integral>x. g x \<partial>Mb)"
    and clA: "closedin (mtopology_of m) A"
    for Ma Mb :: "'a measure" and A
  proof -
    interpret MW: mweak_conv_fin "mspace m" "mdist m" "\<lambda>_ :: nat. Ma"
        Mb sequentially
    proof
      show "\<forall>\<^sub>F i in sequentially.
          sets ((\<lambda>_ :: nat. Ma) i) = sets (borel_of PM.mtopology)"
        using sa top by simp
      show "sets Mb = sets (borel_of PM.mtopology)"
        using sb top by simp
      show "\<forall>\<^sub>F i in sequentially. finite_measure ((\<lambda>_ :: nat. Ma) i)"
        using fa by simp
      show "\<exists>A. countable A \<and> A \<subseteq> sets Mb \<and> \<Union> A = space Mb
          \<and> (\<forall>a\<in>A. emeasure Mb a \<noteq> \<infinity>)"
        by (intro exI[of _ "{space Mb}"])
          (auto simp: finite_measure.emeasure_eq_measure[OF fb])
      show "emeasure Mb (space Mb) \<noteq> \<top>"
        by (simp add: finite_measure.emeasure_eq_measure[OF fb])
    qed
    have key: "Limsup sequentially (\<lambda>x. ereal (measure Ma A))
        \<le> ereal (measure Mb A)"
    proof (rule MW.mweak_conv2)
      fix g :: "'a \<Rightarrow> real"
      assume u: "uniformly_continuous_map PM.Self euclidean_metric g"
        and b: "\<exists>B. \<forall>x\<in>mspace m. \<bar>g x\<bar> \<le> B"
      have cg: "continuous_map (mtopology_of m) euclideanreal g"
        using uniformly_continuous_imp_continuous_map[OF u]
        by (simp add: mtopology_of_def)
      have "(\<integral>x. g x \<partial>Ma) = (\<integral>x. g x \<partial>Mb)"
        by (rule eqab[OF cg]) (use b in \<open>simp add: tsp\<close>)
      then show "((\<lambda>i. \<integral>x. g x \<partial>((\<lambda>_ :: nat. Ma) i))
          \<longlongrightarrow> (\<integral>x. g x \<partial>Mb)) sequentially"
        by simp
    next
      show "closedin PM.mtopology A" using clA top by simp
    qed
    have "Limsup sequentially (\<lambda>x. ereal (measure Ma A))
        = ereal (measure Ma A)"
      by (simp add: Limsup_const)
    with key show ?thesis by simp
  qed
  have eqC: "emeasure M1 C = emeasure M2 C"
    if C: "closedin (mtopology_of m) C" for C
  proof -
    have "measure M1 C \<le> measure M2 C"
      by (rule le[OF s1 s2 f1 f2 eq C])
    moreover have "measure M2 C \<le> measure M1 C"
      by (rule le[OF s2 s1 f2 f1 eq[symmetric] C])
    ultimately have "measure M1 C = measure M2 C" by linarith
    then show ?thesis
      by (simp add: finite_measure.emeasure_eq_measure[OF f1]
          finite_measure.emeasure_eq_measure[OF f2])
  qed
  show ?thesis
  proof (rule measure_eqI_generator_eq[of "{C. closedin (mtopology_of m) C}"
      "topspace (mtopology_of m)" M1 M2
      "\<lambda>_ :: nat. topspace (mtopology_of m)"])
    show "Int_stable {C. closedin (mtopology_of m) C}"
      by (auto simp: Int_stable_def closedin_Int)
    show "{C. closedin (mtopology_of m) C} \<subseteq> Pow (topspace (mtopology_of m))"
      by (fastforce dest: closedin_subset)
    show "\<And>X. X \<in> {C. closedin (mtopology_of m) C}
        \<Longrightarrow> emeasure M1 X = emeasure M2 X"
      using eqC by auto
    show "sets M1 = sigma_sets (topspace (mtopology_of m))
        {C. closedin (mtopology_of m) C}"
      unfolding s1 by (rule sets_borel_of_closed)
    show "sets M2 = sigma_sets (topspace (mtopology_of m))
        {C. closedin (mtopology_of m) C}"
      unfolding s2 by (rule sets_borel_of_closed)
    show "range (\<lambda>_ :: nat. topspace (mtopology_of m))
        \<subseteq> {C. closedin (mtopology_of m) C}"
      using closedin_topspace[of "mtopology_of m"] by auto
    show "(\<Union>i :: nat. topspace (mtopology_of m)) = topspace (mtopology_of m)"
      by simp
    show "\<And>i :: nat. emeasure M1 (topspace (mtopology_of m)) \<noteq> \<infinity>"
      by (simp add: finite_measure.emeasure_eq_measure[OF f1])
  qed
qed

text \<open>The one-sided companion of \<open>metric_measure_eqI_bounded_cts\<close>: if one
  finite Borel measure integrates every continuous \<open>[0,1]\<close>-valued
  function below another, it is dominated on every Borel set. Closed sets
  first, via the Urysohn sandwich \<open>1\<^sub>C \<le> f\<^sub>m \<le> 1\<^bsub>U\<^sub>m\<^esub>\<close> with
  \<open>U\<^sub>m \<down> C\<close>; general Borel sets by inner regularity
  (\<open>finite_measure.inner_regular'\<close>, AFP Riesz--Representation), since a
  one-sided bound cannot be extended from a generator by a Dynkin
  argument.\<close>

lemma metric_measure_mono_bounded_cts:
  fixes m :: "'a metric" and M1 M2 :: "'a measure"
  assumes s1: "sets M1 = sets (borel_of (mtopology_of m))"
    and s2: "sets M2 = sets (borel_of (mtopology_of m))"
    and f1: "finite_measure M1" and f2: "finite_measure M2"
    and le: "\<And>g. continuous_map (mtopology_of m) euclideanreal g \<Longrightarrow>
        (\<And>x. 0 \<le> g x) \<Longrightarrow> (\<And>x. g x \<le> 1) \<Longrightarrow>
        (\<integral>x. g x \<partial>M1) \<le> (\<integral>x. g x \<partial>M2)"
    and A: "A \<in> sets M1"
  shows "measure M1 A \<le> measure M2 A"
proof -
  interpret PM: Metric_space "mspace m" "mdist m"
    by (rule Metric_space_mspace_mdist)
  have top: "PM.mtopology = mtopology_of m"
    by (simp add: mtopology_of_def)
  have tsp: "topspace (mtopology_of m) = mspace m"
    using top PM.topspace_mtopology by simp
  have leC: "measure M1 C \<le> measure M2 C"
    if Ccl: "closedin (mtopology_of m) C" for C
  proof (cases "C = {}")
    case True
    then show ?thesis by simp
  next
    case False
    have CM: "C \<subseteq> mspace m"
      using closedin_subset[OF Ccl] tsp by simp
    have Csets1: "C \<in> sets M1" and Csets2: "C \<in> sets M2"
      using borel_of_closed[OF Ccl] s1 s2 by simp_all
    define Um where "Um = (\<lambda>mm :: nat. \<Union>a\<in>C. PM.mball a (1 / Suc mm))"
    have Um_open: "openin (mtopology_of m) (Um mm)" for mm
      unfolding Um_def top[symmetric] by auto
    have Um_sets2: "Um mm \<in> sets M2" for mm
      using borel_of_open[OF Um_open] s2 by simp
    have C_Um: "C \<subseteq> Um mm" for mm
      unfolding Um_def using CM
      by (auto intro!: PM.centre_in_mball_iff[THEN iffD2])
    have Um_dec: "decseq Um"
    proof (rule decseq_SucI)
      fix mm :: nat
      have "1 / Suc (Suc mm) \<le> 1 / Suc mm"
        by (simp add: frac_le)
      then show "Um (Suc mm) \<subseteq> Um mm"
        unfolding Um_def by auto
    qed
    have Um_Int: "(\<Inter>mm. Um mm) = C"
    proof
      show "C \<subseteq> (\<Inter>mm. Um mm)" using C_Um by blast
      show "(\<Inter>mm. Um mm) \<subseteq> C"
      proof
        fix x assume x: "x \<in> (\<Inter>mm. Um mm)"
        then have xM: "x \<in> mspace m"
          unfolding Um_def by auto
        show "x \<in> C"
        proof (rule ccontr)
          assume xC: "x \<notin> C"
          have op: "openin (mtopology_of m) (topspace (mtopology_of m) - C)"
            using Ccl unfolding closedin_def by blast
          have xin: "x \<in> topspace (mtopology_of m) - C"
            using xM xC tsp by simp
          obtain r where r0: "0 < r"
            and rsub: "PM.mball x r \<subseteq> topspace (mtopology_of m) - C"
            using op[unfolded top[symmetric] PM.openin_mtopology] xin
              top by auto
          obtain mm where mm: "1 / Suc mm < r"
            using reals_Archimedean[OF r0] by (auto simp: inverse_eq_divide)
          obtain a where a: "a \<in> C" "x \<in> PM.mball a (1 / Suc mm)"
            using x unfolding Um_def by blast
          have "mdist m a x < 1 / Suc mm" and aM: "a \<in> mspace m"
            using a by auto
          then have "a \<in> PM.mball x r"
            using mm xM by (auto simp: PM.commute)
          then have "a \<notin> C" using rsub by auto
          with a show False by simp
        qed
      qed
    qed
    have bound: "measure M1 C \<le> measure M2 (Um mm)" for mm
    proof -
      have cl2: "closedin (mtopology_of m)
          (topspace (mtopology_of m) - Um mm)"
        using Um_open[of mm] openin_subset[OF Um_open[of mm]]
        by (auto simp: closedin_def Diff_Diff_Int Int_absorb1 tsp)
      have disj: "C \<inter> (topspace (mtopology_of m) - Um mm) = {}"
        using C_Um[of mm] by blast
      have sep: "1 / Suc mm \<le> mdist m x y"
        if xy: "x \<in> C" "y \<in> topspace (mtopology_of m) - Um mm" for x y
      proof (rule ccontr)
        assume "\<not> 1 / Suc mm \<le> mdist m x y"
        then have "mdist m x y < 1 / Suc mm" by simp
        then have "y \<in> PM.mball x (1 / Suc mm)"
          using xy CM tsp by auto
        then have "y \<in> Um mm"
          unfolding Um_def using xy by blast
        with xy show False by simp
      qed
      obtain fm :: "'a \<Rightarrow> real"
        where fmU: "uniformly_continuous_map m euclidean_metric fm"
        and fm0: "\<And>x. 0 \<le> fm x" and fm1: "\<And>x. fm x \<le> 1"
        and fmC: "\<And>x. x \<in> C \<Longrightarrow> fm x = 1"
        and fmZ: "\<And>x. x \<in> topspace (mtopology_of m) - Um mm \<Longrightarrow> fm x = 0"
        using Urysohn_lemma_uniform[OF Ccl cl2 disj sep] by auto
      have fmc: "continuous_map (mtopology_of m) euclideanreal fm"
        using uniformly_continuous_imp_continuous_map[OF fmU]
        by (simp add: mtopology_of_def)
      have fmmeas: "fm \<in> borel_measurable (borel_of (mtopology_of m))"
        using continuous_map_measurable[OF fmc]
        by (simp add: borel_of_euclidean)
      have fmm1: "fm \<in> borel_measurable M1"
        using fmmeas measurable_cong_sets[OF s1 refl] by blast
      have fmm2: "fm \<in> borel_measurable M2"
        using fmmeas measurable_cong_sets[OF s2 refl] by blast
      have int_fm1: "integrable M1 fm"
        by (rule finite_measure.integrable_const_bound[OF f1, of _ 1])
          (use fm0 fm1 fmm1 in auto)
      have int_fm2: "integrable M2 fm"
        by (rule finite_measure.integrable_const_bound[OF f2, of _ 1])
          (use fm0 fm1 fmm2 in auto)
      have int_indC: "integrable M1 (indicat_real C)"
        by (intro integrable_real_indicator Csets1)
          (simp add: finite_measure.emeasure_eq_measure[OF f1])
      have "measure M1 C = (\<integral>x. indicat_real C x \<partial>M1)"
        using Csets1 by simp
      also have "\<dots> \<le> (\<integral>x. fm x \<partial>M1)"
        by (intro integral_mono int_indC int_fm1)
          (use fm0 fmC in \<open>auto simp: indicator_def\<close>)
      also have "\<dots> \<le> (\<integral>x. fm x \<partial>M2)"
        by (rule le[OF fmc fm0 fm1])
      also have "\<dots> \<le> (\<integral>x. indicat_real (Um mm) x \<partial>M2)"
      proof (rule integral_mono_AE[OF int_fm2])
        show "integrable M2 (indicat_real (Um mm))"
          by (intro integrable_real_indicator Um_sets2)
            (simp add: finite_measure.emeasure_eq_measure[OF f2])
        show "AE x in M2. fm x \<le> indicat_real (Um mm) x"
        proof (intro AE_I2)
          fix x assume x: "x \<in> space M2"
          have xtop: "x \<in> topspace (mtopology_of m)"
            using x
            by (simp add: sets_eq_imp_space_eq[OF s2] space_borel_of)
          show "fm x \<le> indicat_real (Um mm) x"
          proof (cases "x \<in> Um mm")
            case True then show ?thesis
              using fm1 by (simp add: indicator_def)
          next
            case False then show ?thesis
              using fmZ xtop by (simp add: indicator_def)
          qed
        qed
      qed
      also have "\<dots> = measure M2 (Um mm)"
        using Um_sets2 by simp
      finally show ?thesis .
    qed
    have lim: "(\<lambda>mm. measure M2 (Um mm)) \<longlonglongrightarrow> measure M2 C"
      using finite_measure.finite_Lim_measure_decseq[OF f2 _ Um_dec]
        Um_sets2 Um_Int by auto
    show ?thesis
      by (rule LIMSEQ_le_const[OF lim]) (use bound in auto)
  qed
  have mtz: "metrizable_space (mtopology_of m)"
    using PM.metrizable_space_mtopology top by simp
  have ir: "inner_regular (mtopology_of m) M1"
    by (rule finite_measure.inner_regular'[OF f1 mtz s1[symmetric]])
  have "measure M1 A
      = (\<Squnion>C\<in>{C. closedin (mtopology_of m) C \<and> C \<subseteq> A}. measure M1 C)"
    by (rule finite_measure.inner_regularD[OF f1 ir A])
  also have "\<dots> \<le> measure M2 A"
  proof (rule cSUP_least)
    show "{C. closedin (mtopology_of m) C \<and> C \<subseteq> A} \<noteq> {}"
      by (auto intro!: exI[of _ "{}"])
    fix C assume "C \<in> {C. closedin (mtopology_of m) C \<and> C \<subseteq> A}"
    then have Ccl: "closedin (mtopology_of m) C" and CA: "C \<subseteq> A" by auto
    have "measure M1 C \<le> measure M2 C" by (rule leC[OF Ccl])
    also have "\<dots> \<le> measure M2 A"
      by (intro finite_measure.finite_measure_mono[OF f2 CA])
        (use A s1 s2 in simp)
    finally show "measure M1 C \<le> measure M2 A" .
  qed
  finally show ?thesis .
qed

text \<open>The class's integrated identities --- \<open>E[Z\<sqdot>(X\<^sub>t - X\<^sub>s)] = 0\<close> for a
  bounded continuous test \<open>Z\<close> of the past, and its covariation analogue ---
  are integrals of continuous but unbounded path functionals, so weak
  convergence alone does not transfer them. \<open>Path_Tightness\<close>'s
  \<open>weak_conv_on_integral_unif_integrable\<close> closes the gap given uniform
  integrability, which a uniform \<open>L\<^sup>2\<close> bound supplies via
  Chebyshev--Markov: \<open>\<integral>\<bar>f\<bar>\<sqdot>1\<^bsub>{\<bar>f\<bar>>R}\<^esub> \<le> (1/R)\<sqdot>\<integral>f\<^sup>2 \<le> C/R\<close>.\<close>

lemma unif_integrable_of_L2_bound:
  fixes f :: "'b \<Rightarrow> real" and Ni :: "nat \<Rightarrow> 'b measure"
  assumes C: "0 \<le> C"
    and iTi: "\<And>i R. integrable (Ni i)
        (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and iTN: "\<And>R. integrable N (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and sqi: "\<And>i. (\<integral>w. (f w)\<^sup>2 \<partial>(Ni i)) \<le> C"
    and sqN: "(\<integral>w. (f w)\<^sup>2 \<partial>N) \<le> C"
    and sqiI: "\<And>i. integrable (Ni i) (\<lambda>w. (f w)\<^sup>2)"
    and sqNI: "integrable N (\<lambda>w. (f w)\<^sup>2)"
    and e: "0 < e"
  shows "\<exists>R. 0 \<le> R
      \<and> (\<forall>i. (\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>(Ni i)) \<le> e)
      \<and> (\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>N) \<le> e"
proof -
  define R where "R = (C + 1) / e"
  have R0: "0 < R" using C e unfolding R_def by simp
  have key: "(\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>M) \<le> e"
    if int: "integrable M (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
      and sq: "(\<integral>w. (f w)\<^sup>2 \<partial>M) \<le> C"
      and sqI: "integrable M (\<lambda>w. (f w)\<^sup>2)"
    for M :: "'b measure"
  proof -
    have pt: "\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<le> (1 / R) * (f w)\<^sup>2"
      for w
    proof (cases "R < \<bar>f w\<bar>")
      case True
      have "\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) = \<bar>f w\<bar>"
        using True by (simp add: indicator_def)
      also have "\<dots> = (1 / R) * (R * \<bar>f w\<bar>)" using R0 by simp
      also have "\<dots> \<le> (1 / R) * (\<bar>f w\<bar> * \<bar>f w\<bar>)"
        using True R0 by (intro mult_left_mono mult_right_mono) auto
      also have "\<dots> = (1 / R) * (f w)\<^sup>2"
        by (simp add: power2_eq_square flip: power2_abs)
      finally show ?thesis .
    next
      case False
      have "\<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) = 0"
        using False by (simp add: indicator_def)
      also have "\<dots> \<le> (1 / R) * (f w)\<^sup>2"
        using R0 by simp
      finally show ?thesis .
    qed
    have "(\<integral>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w) \<partial>M)
        \<le> (\<integral>w. (1 / R) * (f w)\<^sup>2 \<partial>M)"
      using pt int sqI by (intro Bochner_Integration.integral_mono) auto
    also have "\<dots> = (1 / R) * (\<integral>w. (f w)\<^sup>2 \<partial>M)" by simp
    also have "\<dots> \<le> (1 / R) * C"
      using sq R0 by (intro mult_left_mono) auto
    also have "\<dots> \<le> e"
      using C e R0 unfolding R_def by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis
    using R0 key[OF iTi sqi sqiI] key[OF iTN sqN sqNI]
    by (intro exI[of _ R]) auto
qed

text \<open>The transfer the canonical-market construction uses: a continuous
  path functional with a uniform second-moment bound has its integral
  pass to the weak limit. Applied with
  \<open>f \<omega> = Z \<omega> \<sqdot> ((X\<^sub>t - X\<^sub>s) \<bullet> e\<^sub>j)\<close> this carries the martingale
  identity to the limit law, and with the squared increment the
  covariation identity.\<close>

theorem weak_conv_integral_of_L2_bound:
  fixes f :: "'b \<Rightarrow> real" and Ni :: "nat \<Rightarrow> 'b measure"
  assumes wc: "weak_conv_on Ni N sequentially X"
    and f: "continuous_map X euclideanreal f"
    and fmi: "\<And>i. finite_measure (Ni i)" and fmN: "finite_measure N"
    and iNi: "\<And>i. integrable (Ni i) f" and iN: "integrable N f"
    and iCi: "\<And>i R. integrable (Ni i) (\<lambda>w. max (- R) (min R (f w)))"
    and iCN: "\<And>R. integrable N (\<lambda>w. max (- R) (min R (f w)))"
    and iTi: "\<And>i R. integrable (Ni i)
        (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and iTN: "\<And>R. integrable N (\<lambda>w. \<bar>f w\<bar> * indicat_real {z. R < \<bar>z\<bar>} (f w))"
    and C: "0 \<le> C"
    and sqi: "\<And>i. (\<integral>w. (f w)\<^sup>2 \<partial>(Ni i)) \<le> C" and sqN: "(\<integral>w. (f w)\<^sup>2 \<partial>N) \<le> C"
    and sqiI: "\<And>i. integrable (Ni i) (\<lambda>w. (f w)\<^sup>2)"
    and sqNI: "integrable N (\<lambda>w. (f w)\<^sup>2)"
  shows "(\<lambda>i. \<integral>w. f w \<partial>(Ni i)) \<longlonglongrightarrow> (\<integral>w. f w \<partial>N)"
  by (rule weak_conv_on_integral_unif_integrable
      [OF wc f fmi fmN iNi iN iCi iCN iTi iTN])
    (rule unif_integrable_of_L2_bound
      [OF C iTi iTN sqi sqN sqiI sqNI])


subsection \<open>A convergent subsequence of path laws, in the vector case\<close>

text \<open>
  The adapter between the stochastic layer (\<open>Stopped_Localization\<close>) and the
  topological layer (\<open>Path_Tightness\<close>): the moment hypotheses of
  \<open>path_laws_convergent_subsequence_vec\<close> are discharged per coordinate by
  \<open>fourth_moment_L2_integrable\<close> / \<open>fourth_moment_L2_bochner\<close>, so the
  subsequence extraction of Lemma 2.2 holds for any sequence of laws carrying,
  per coordinate, an \<open>L\<^sup>2\<close> martingale with a compensated square whose adapted
  compensator grows at rate at most \<open>C\<close> --- the formal content of the paper's
  admissibility conditions Eqs. (1.7)-(1.8).
\<close>

(*<*)
end
(*>*)
