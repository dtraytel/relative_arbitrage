section \<open>Tightness of the path laws\<close>

(*<*)
theory Path_Tightness
  imports
    Holder_Interpolation Path_Space "Continuous_Time_Martingales.Stopped_Localization"
begin

(*>*)

text \<open>
  Laws of processes satisfying a uniform fourth-moment bound
  \<open>E (X v - X u)\<^sup>4 \<le> 8 C\<^sup>2 (v - u)\<^sup>2\<close> form a tight family on \<open>C({0..T})\<close>: \<open>dyadic_bad_event_tail_mom\<close>
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
  have pos: "0 < 1 - 2 powr (-\<gamma>)" using g0 by (simp add: powr_less_one)
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
  have pos: "0 < 1 - 2 powr (-\<gamma>)" using g0 by (simp add: powr_less_one)
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

text \<open>
  The bound is proved once for paths in a Euclidean space and read
  componentwise along the basis. The bad event is the union of the
  component bad events (factor \<open>DIM('b)\<close> by the union bound); on its
  complement every component is H\"older, so the path is H\"older with
  constant \<open>DIM('b) * holder_const \<gamma> T n\<close> via \<open>norm_le_l1\<close>, and the
  compact ball comes from \<open>compactin_path_holder_ball\<close>. The real-valued
  and the \<open>\<real>\<^sup>n\<close>-valued forms are its instances.
\<close>

theorem path_law_holder_ball_bound_basis:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::euclidean_space" and M :: "'a measure" and T C \<gamma> :: real
    and x :: 'b and n :: nat
  assumes P: "prob_space M"
    and T0: "0 \<le> T"
    and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
    and start: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> X 0 \<omega> = x"
    and int4: "\<And>b u v. b \<in> Basis \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable M (\<lambda>\<omega>. (X v \<omega> \<bullet> b - X u \<omega> \<bullet> b)^4)"
    and mom: "\<And>b u v. b \<in> Basis \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (X v \<omega> \<bullet> b - X u \<omega> \<bullet> b)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "measure (path_law M X T)
      (space (path_law M X T)
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
             f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
               norm (f t - f s)
                 \<le> real DIM('b) * holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)})
    \<le> real DIM('b)
        * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
proof -
  interpret P: prob_space M by (rule P)
  let ?PS = "(path_borel T :: (real \<Rightarrow> 'b) measure)"
  define c where "c = real DIM('b) * holder_const \<gamma> T n"
  define K where "K = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
        norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr \<gamma>)}"
  define pf where "pf = (\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})"
  have g1': "\<gamma> \<le> 1" using g2 by linarith
  have c0: "0 \<le> c"
    unfolding c_def
    by (intro mult_nonneg_nonneg holder_const_nonneg[OF g0]) simp
  have Xmi: "(\<lambda>\<omega>. X u \<omega> \<bullet> b) \<in> borel_measurable M" if "0 \<le> u" for u b
    by (intro borel_measurable_inner Xm[OF that] borel_measurable_const)
  have Xm': "X t \<in> borel_measurable M" if "t \<in> {0..T}" for t
    using that by (intro Xm) simp
  have pfm: "pf \<in> M \<rightarrow>\<^sub>M ?PS"
    unfolding pf_def by (rule pathify_measurable[OF T0 Xm' cont])
  have cK: "compactin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) K"
    unfolding K_def by (rule compactin_path_holder_ball[OF T0 g0 c0])
  have haus: "Hausdorff_space (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    unfolding mtopology_of_def
    by (rule Metric_space.Hausdorff_space_mtopology[OF Metric_space_mspace_mdist])
  have KD: "space ?PS - K \<in> sets ?PS"
    by (rule sets.compl_sets[OF borel_of_closed[OF compactin_imp_closedin[OF haus cK]]])
  define Bad where "Bad = (\<lambda>b. {\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> \<bullet> b - X (real_of_int (k - 1) / 2^j) \<omega> \<bullet> b\<bar>})"
  have BadS: "Bad b \<in> sets M" for b
    unfolding Bad_def
    by (intro dyadic_bad_event_sets[where X = "\<lambda>u \<omega>. X u \<omega> \<bullet> b"] Xmi)
  have sub: "pf -` (space ?PS - K) \<inter> space M \<subseteq> (\<Union>b\<in>Basis. Bad b)"
  proof
    fix \<omega> assume A: "\<omega> \<in> pf -` (space ?PS - K) \<inter> space M"
    have w: "\<omega> \<in> space M" using A by blast
    have notK: "pf \<omega> \<notin> K" using A by blast
    show "\<omega> \<in> (\<Union>b\<in>Basis. Bad b)"
    proof (rule ccontr)
      assume nB: "\<omega> \<notin> (\<Union>b\<in>Basis. Bad b)"
      have coordH: "\<bar>X t \<omega> \<bullet> b - X s \<omega> \<bullet> b\<bar> \<le> holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>"
        if b: "b \<in> Basis" and s: "s \<in> {0..T}" and t: "t \<in> {0..T}" for b and s t :: real
      proof (rule holder_of_good_dyadics[where f = "\<lambda>t. X t \<omega> \<bullet> b", OF T0 g0 g1' _ _ t s])
        show "continuous_on {0..T} (\<lambda>t. X t \<omega> \<bullet> b)"
          by (intro continuous_on_inner cont[OF w] continuous_on_const)
        fix j k assume "n \<le> j" "k \<in> {1..\<lfloor>2^j * T\<rfloor>}"
        then have "\<not> 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> \<bullet> b - X (real_of_int (k - 1) / 2^j) \<omega> \<bullet> b\<bar>"
          using nB w b unfolding Bad_def by blast
        then show "\<bar>X (real_of_int k / 2^j) \<omega> \<bullet> b - X (real_of_int (k - 1) / 2^j) \<omega> \<bullet> b\<bar>
            \<le> 2 powr (-\<gamma>*real j)" by linarith
      qed
      have vecH: "norm (pf \<omega> t - pf \<omega> s) \<le> c * \<bar>t - s\<bar> powr \<gamma>"
        if s: "s \<in> {0..T}" and t: "t \<in> {0..T}" for s t
      proof -
        have "norm (X t \<omega> - X s \<omega>) \<le> (\<Sum>b\<in>Basis. \<bar>(X t \<omega> - X s \<omega>) \<bullet> b\<bar>)"
          by (rule norm_le_l1)
        also have "\<dots> = (\<Sum>b\<in>Basis. \<bar>X t \<omega> \<bullet> b - X s \<omega> \<bullet> b\<bar>)"
          by (simp add: inner_diff_left)
        also have "\<dots> \<le> (\<Sum>b\<in>(Basis::'b set). holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)"
          by (intro sum_mono coordH[OF _ s t])
        also have "\<dots> = c * \<bar>t - s\<bar> powr \<gamma>"
          unfolding c_def by simp
        finally show ?thesis using s t unfolding pf_def by simp
      qed
      have f0: "pf \<omega> 0 = x"
        unfolding pf_def using T0 start[OF w] by simp
      have pfin: "pf \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
        unfolding pf_def by (rule mspace_path_metricI[OF cont[OF w]])
      have "pf \<omega> \<in> K"
        unfolding K_def using pfin f0 vecH by auto
      with notK show False by contradiction
    qed
  qed
  have UB: "(\<Union>b\<in>Basis. Bad b) \<in> sets M"
    by (intro sets.countable_UN'' BadS countable_finite[OF finite_Basis])
  have pl: "path_law M X T = distr M ?PS pf"
    unfolding path_law_def pf_def by (rule refl)
  have "measure (path_law M X T) (space (path_law M X T) - K)
      = measure (distr M ?PS pf) (space ?PS - K)"
    unfolding pl by simp
  also have "\<dots> = measure M (pf -` (space ?PS - K) \<inter> space M)"
    by (rule measure_distr[OF pfm KD])
  also have "\<dots> \<le> measure M (\<Union>b\<in>Basis. Bad b)"
    by (rule P.finite_measure_mono[OF sub UB])
  also have "\<dots> \<le> (\<Sum>b\<in>(Basis::'b set). measure M (Bad b))"
    by (rule P.finite_measure_subadditive_finite) (auto intro: BadS)
  also have "\<dots> \<le> (\<Sum>b\<in>(Basis::'b set).
      8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
  proof (rule sum_mono)
    fix b :: 'b assume b: "b \<in> Basis"
    show "measure M (Bad b)
        \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))"
      unfolding Bad_def
      by (rule dyadic_bad_event_tail_mom[where X = "\<lambda>u \<omega>. X u \<omega> \<bullet> b",
            OF P Xmi int4[OF b] mom[OF b] T0 g2])
  qed
  also have "\<dots> = real DIM('b)
      * (8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>))))"
    by simp
  finally show ?thesis unfolding K_def c_def .
qed

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
  by (rule path_law_holder_ball_bound_basis[where C = C, OF P T0 g0 g2 Xm cont start,
        unfolded DIM_real of_nat_1 mult_1_left])
    (auto simp: int4 mom)

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
  by (rule path_law_holder_ball_bound_basis[where C = C, OF P T0 g0 g2 Xm cont start,
        unfolded DIM_cart DIM_real mult_1_right])
    (auto simp: Basis_vec_def inner_axis int4 mom)

subsection \<open>Tightness of a family of path laws\<close>

text \<open>A family of path laws is tight as soon as, for every \<open>e\<close>, some
  H\"older ball --- compact by @{thm [source] compactin_path_holder_ball} ---
  carries all but \<open>e\<close> of every law's mass.\<close>

theorem tight_on_set_of_holder_charge:
  fixes \<Gamma> :: "(real \<Rightarrow> 'b::{polish_space, real_normed_vector, heine_borel}) measure set"
    and x :: 'b
  assumes T: "0 \<le> T" and ga: "0 < ga"
    and fm: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> finite_measure N"
    and st: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> sets (path_borel T :: (real \<Rightarrow> 'b) measure) = sets N"
    and charge: "\<And>e. 0 < e \<Longrightarrow> \<exists>c. 0 \<le> c \<and> (\<forall>N\<in>\<Gamma>. measure N (space N -
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
              norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr ga)}) < e)"
  shows "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) \<Gamma>"
  unfolding tight_on_set_def
proof (intro conjI allI impI)
  show "\<forall>M\<in>\<Gamma>. finite_measure M \<and> sets (path_borel T :: (real \<Rightarrow> 'b) measure) = sets M"
    using fm st by blast
  fix e :: real assume e: "0 < e"
  obtain c where c: "0 \<le> c"
    and ch: "\<And>N. N \<in> \<Gamma> \<Longrightarrow> measure N (space N -
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
              norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr ga)}) < e"
    using charge[OF e] by blast
  show "\<exists>K. compactin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) K
      \<and> (\<forall>M\<in>\<Gamma>. measure M (space M - K) < e)"
    by (intro exI[of _ "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
              norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr ga)}"]
        conjI ballI compactin_path_holder_ball[OF T ga c] ch)
qed

theorem tight_on_set_path_laws_basis:
  fixes MM :: "'i \<Rightarrow> 'a measure" and XX :: "'i \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'b::euclidean_space"
    and I :: "'i set" and T C \<gamma> :: real and x :: 'b
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. i \<in> I \<Longrightarrow> prob_space (MM i)"
    and Xm: "\<And>i u. i \<in> I \<Longrightarrow> 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<omega> \<in> space (MM i) \<Longrightarrow>
        continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. i \<in> I \<Longrightarrow> \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i b u v. i \<in> I \<Longrightarrow> b \<in> Basis \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> \<bullet> b - XX i u \<omega> \<bullet> b)^4)"
    and mom: "\<And>i b u v. i \<in> I \<Longrightarrow> b \<in> Basis \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> \<bullet> b - XX i u \<omega> \<bullet> b)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      ((\<lambda>i. path_law (MM i) (XX i) T) ` I)"
proof (rule tight_on_set_of_holder_charge[OF T0 g0, where x = x])
  fix N assume "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I"
  then obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T" by blast
  have "prob_space N"
    unfolding Ni by (rule prob_space_path_law[OF P[OF i] T0]) (use Xm[OF i] cont[OF i] in auto)
  then show "finite_measure N" by (rule prob_space.axioms(1))
  show "sets (path_borel T :: (real \<Rightarrow> 'b) measure) = sets N" unfolding Ni by simp
next
  fix e :: real assume e: "0 < e"
  define q where "q = 2 powr (-(1-4*\<gamma>))"
  have q0: "0 \<le> q" unfolding q_def by simp
  have q1: "q < 1" unfolding q_def by (rule powr_less_one) (use g2 in simp_all)
  have "(\<lambda>n. real DIM('b) * (8*C\<^sup>2*T * q^n / (1 - q)))
      \<longlonglongrightarrow> real DIM('b) * (8*C\<^sup>2*T * 0 / (1 - q))"
    by (intro tendsto_intros LIMSEQ_realpow_zero) (use q0 q1 in auto)
  then have "(\<lambda>n. real DIM('b) * (8*C\<^sup>2*T * q^n / (1 - q))) \<longlonglongrightarrow> 0" by simp
  then have "eventually (\<lambda>n. real DIM('b) * (8*C\<^sup>2*T * q^n / (1 - q)) < e) sequentially"
    by (rule order_tendstoD(2)[OF _ e])
  then obtain n where n: "real DIM('b) * (8*C\<^sup>2*T * q^n / (1 - q)) < e"
    unfolding eventually_sequentially by blast
  show "\<exists>c. 0 \<le> c \<and> (\<forall>N\<in>(\<lambda>i. path_law (MM i) (XX i) T) ` I. measure N (space N -
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
              norm (f t - f s) \<le> c * \<bar>t - s\<bar> powr \<gamma>)}) < e)"
  proof (intro exI[of _ "real DIM('b) * holder_const \<gamma> T n"] conjI ballI)
    show "0 \<le> real DIM('b) * holder_const \<gamma> T n"
      using holder_const_nonneg[OF g0, of T n] by simp
    fix N assume "N \<in> (\<lambda>i. path_law (MM i) (XX i) T) ` I"
    then obtain i where i: "i \<in> I" and Ni: "N = path_law (MM i) (XX i) T" by blast
    have "measure N (space N -
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
              norm (f t - f s) \<le> real DIM('b) * holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)})
        \<le> real DIM('b) * (8*C\<^sup>2*T * q^n / (1 - q))"
      unfolding Ni q_def
      by (rule path_law_holder_ball_bound_basis[OF P[OF i] T0 g0 g2 Xm[OF i]
            cont[OF i] start[OF i] int4[OF i] mom[OF i]])
    with n show "measure N (space N -
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         f 0 = x \<and> (\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}.
              norm (f t - f s) \<le> real DIM('b) * holder_const \<gamma> T n * \<bar>t - s\<bar> powr \<gamma>)}) < e"
      by linarith
  qed
qed

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
  by (rule tight_on_set_path_laws_basis[where C = C, OF T0 g0 g2 P Xm cont start])
    (auto simp: int4 mom)

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
  by (rule tight_on_set_path_laws_basis[where C = C, OF T0 g0 g2 P Xm cont start])
    (auto simp: Basis_vec_def inner_axis int4 mom)

subsection \<open>Subsequence extraction at a fixed horizon\<close>

text \<open>
  Combining the tightness theorem with the AFP's
  \<open>tight_on_set_imp_convergent_subsequence\<close>: every sequence of laws whose
  processes satisfy the uniform fourth-moment bound has a weakly convergent
  subsequence on \<open>C({0..T})\<close>: relative compactness at a fixed horizon. The
  \<open>C([0,\<infinity>))\<close> statement extends it to unbounded time.
\<close>

corollary path_laws_convergent_subsequence_basis:
  fixes MM :: "nat \<Rightarrow> 'a measure" and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'b::euclidean_space"
    and T C \<gamma> :: real and x :: 'b
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and cont: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and int4: "\<And>i b u v. b \<in> Basis \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> \<bullet> b - XX i u \<omega> \<bullet> b)^4)"
    and mom: "\<And>i b u v. b \<in> Basis \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (XX i v \<omega> \<bullet> b - XX i u \<omega> \<bullet> b)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> 'b) measure)
      \<and> prob_space N
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
proof -
  have Pl: "prob_space (path_law (MM i) (XX i) T)" for i
    by (rule prob_space_path_law[OF P T0]) (use Xm cont in auto)
  have "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> 'b) measure)
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
  proof (rule tight_on_set_imp_convergent_subsequence)
    show "metrizable_space (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
      unfolding mtopology_of_def
      by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
    show "separable_space (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
      by (rule separable_path_metric)
    show "tight_on_set (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        (range (\<lambda>i. path_law (MM i) (XX i) T))"
      by (intro tight_on_set_path_laws_basis[OF T0 g0 g2, where x = x and C = C]
            P Xm cont start int4 mom)
    show "path_law (MM i) (XX i) T (space (path_law (MM i) (XX i) T)) \<le> ennreal 1" for i
      using Pl[of i] by (simp add: prob_space.emeasure_space_1)
  qed
  then obtain a N where "strict_mono a" "finite_measure N"
      "sets N = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
      and wc: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))" by blast
  moreover have "prob_space N" by (rule weak_conv_on_prob_space[OF wc]) (simp add: Pl)
  ultimately show ?thesis by blast
qed

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
proof -
  have "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> real) measure)
      \<and> prob_space N
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
    by (rule path_laws_convergent_subsequence_basis[where C = C, OF T0 g0 g2 P Xm cont start])
      (auto simp: int4 mom)
  then obtain a N where a: "strict_mono a" and N: "finite_measure N"
      "sets N = sets (path_borel T :: (real \<Rightarrow> real) measure)" "prob_space N"
    and wc: "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real) metric))"
    by blast
  have "N (space N) \<le> ennreal 1" using prob_space.emeasure_space_1[OF N(3)] by simp
  with a N wc show ?thesis by blast
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
      \<and> prob_space N
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
  by (rule path_laws_convergent_subsequence_basis[where C = C, OF T0 g0 g2 P Xm cont start])
    (auto simp: Basis_vec_def inner_axis int4 mom)

subsection \<open>The finite-dimensional marginal maps\<close>

text \<open>
  Restricting a path to a finite set of times \<open>J \<subseteq> {0..T}\<close> is
  measurable from \<open>path_borel T\<close> to the product space on \<open>J\<close>; the
  finite-dimensional marginals of a path law are its pushforwards under
  these maps.
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

subsection \<open>The dyadic extension operator\<close>

text \<open>
  \<open>dyadic_ext\<close> extends a function from the dyadics by taking the limit
  along the anchor sequences \<open>danchor k t\<close>.
\<close>

definition dyadic_ext :: "(real \<Rightarrow> 'b) \<Rightarrow> real \<Rightarrow> 'b::complete_space" where
  "dyadic_ext f t = lim (\<lambda>k. f (danchor k t))"

subsection \<open>Truncation: the other half of the \<open>3\<epsilon>\<close> argument\<close>

text \<open>Uniform integrability of the squared increments is what passes the
  covariation constraint's linear inequalities

    \<open>E[(X\<^sub>t - X\<^sub>s)\<^sup>T M (X\<^sub>t - X\<^sub>s) g] \<le> (t-s) h\<^sub>S(M) E[g]\<close>

  to weak limits without a Skorokhod representation, so that the class of
  laws with covariation rates in a closed set \<open>S\<close> is closed under weak
  convergence. Quantifying only
  over \<open>M \<succeq> 0\<close> does not work: the set \<open>{a : tr(M a) \<le> h\<^sub>S(M) \<forall> M \<succeq> 0}\<close> is
  the downward closure of \<open>S\<close> in the psd order, whereas \<open>S\<close> may carry lower
  bounds (on its eigenvalues, say) and then is not downward closed. Weak convergence
  alone gives only the Fatou direction \<open>liminf \<ge> lim\<close>, which runs the
  wrong way for the lower constraints.

  The fourth-moment bound (\<open>fourth_moment_bound_bounded\<close>
  in \<open>Increment_Moments\<close>, free of Ito and BDG) controls the tail of the
  squared increment uniformly over the family, the hypothesis
  \<open>unif_integrable\<close> of \<open>Vitali_Convergence.vitali_convergence\<close>. The
  estimate is pointwise and elementary: on \<open>{Z\<^sup>2 > R}\<close>,
  \<open>Z\<^sup>2 = Z\<^sup>4/Z\<^sup>2 < Z\<^sup>4/R\<close>, and off that set the left side vanishes.\<close>

text \<open>Weak convergence upgrades to convergence of unbounded continuous
  integrals \<open>\<integral>f dP\<^sub>m \<rightarrow> \<integral>f dP\<close> when \<open>f\<close> has uniformly integrable tails:
  truncate \<open>f\<close> at height \<open>R\<close> --- bounded and continuous, so weak
  convergence applies directly --- and control the two truncation errors
  by the tail integral of \<open>|f|\<close> over \<open>{|f| > R}\<close>.

  The error estimate: pointwise the clamped function differs from \<open>f\<close>
  only where \<open>|f| > R\<close>, and there by at most \<open>|f|\<close> itself, so the error
  is dominated by that tail integral (\<open>clamp_integral_error\<close>), which
  \<open>unif_integrable_of_L2_bound\<close> makes uniformly small
  under an \<open>L\<^sup>2\<close> bound.\<close>

text \<open>The abstract shape of the \<open>3\<epsilon>\<close> argument, with the measure theory
  removed: a sequence uniformly within \<open>e\<close> of some convergent sequence,
  whose limit is itself within \<open>e\<close> of \<open>z\<close> for every \<open>e\<close>, converges to
  \<open>z\<close> -- what truncating the integrand at height \<open>R\<close> and bounding the two
  errors by the tail integral leaves to prove.

  The margin is \<open>e = \<epsilon>/4\<close> rather than \<open>\<epsilon>/3\<close> so the three terms sum to
  \<open>3\<epsilon>/4 < \<epsilon>\<close> strictly, as \<open>LIMSEQ_I\<close> wants.\<close>

lemma tendsto_real_of_approximants:
  fixes x :: "nat \<Rightarrow> real" and z :: real
  assumes approx: "\<And>e. 0 < e \<Longrightarrow>
      \<exists>y w. (\<forall>m. \<bar>x m - y m\<bar> \<le> e) \<and> (y \<longlonglongrightarrow> w) \<and> \<bar>w - z\<bar> \<le> e"
  shows "x \<longlonglongrightarrow> z"
proof (rule LIMSEQ_I)
  fix r :: real assume r: "0 < r"
  have q: "0 < r/4" using r by simp
  obtain y w where near: "\<And>m. \<bar>x m - y m\<bar> \<le> r/4"
    and lim: "y \<longlonglongrightarrow> w" and wz: "\<bar>w - z\<bar> \<le> r/4"
    using approx[OF q] by blast
  obtain no where no: "\<And>m. no \<le> m \<Longrightarrow> norm (y m - w) < r/4"
    using LIMSEQ_D[OF lim q] by blast
  have "norm (x m - z) < r" if m: "no \<le> m" for m
  proof -
    have "\<bar>x m - z\<bar> \<le> \<bar>x m - y m\<bar> + \<bar>y m - w\<bar> + \<bar>w - z\<bar>" by simp
    moreover have "\<bar>y m - w\<bar> < r/4" using no[OF m] by simp
    ultimately have "\<bar>x m - z\<bar> < r/4 + r/4 + r/4"
      using near[of m] wz by linarith
    moreover have "r/4 + r/4 + r/4 < r" using r by simp
    ultimately show ?thesis by simp
  qed
  then show "\<exists>no. \<forall>m\<ge>no. norm (x m - z) < r" by blast
qed

lemma clamp_diff_le_tail_pointwise:
  fixes z R :: real
  assumes Rnn: "0 \<le> R"
  shows "\<bar>z - max (- R) (min R z)\<bar> \<le> \<bar>z\<bar> * indicat_real {w. R < \<bar>w\<bar>} z"
  using Rnn by (auto simp: indicator_def abs_if max_def min_def)

lemma clamp_integral_error:
  fixes f :: "'a \<Rightarrow> real"
  assumes M: "finite_measure M"
    and R: "0 \<le> R"
    and iF: "integrable M f"
    and iC: "integrable M (\<lambda>\<omega>. max (- R) (min R (f \<omega>)))"
    and iT: "integrable M (\<lambda>\<omega>. \<bar>f \<omega>\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f \<omega>))"
  shows "\<bar>(\<integral>\<omega>. f \<omega> \<partial>M) - (\<integral>\<omega>. max (- R) (min R (f \<omega>)) \<partial>M)\<bar>
      \<le> (\<integral>\<omega>. \<bar>f \<omega>\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f \<omega>) \<partial>M)"
proof -
  have diff: "(\<integral>\<omega>. f \<omega> \<partial>M) - (\<integral>\<omega>. max (- R) (min R (f \<omega>)) \<partial>M)
      = (\<integral>\<omega>. f \<omega> - max (- R) (min R (f \<omega>)) \<partial>M)"
    by (rule Bochner_Integration.integral_diff[symmetric, OF iF iC])
  have idiff: "integrable M (\<lambda>\<omega>. f \<omega> - max (- R) (min R (f \<omega>)))"
    by (rule Bochner_Integration.integrable_diff[OF iF iC])
  have "\<bar>(\<integral>\<omega>. f \<omega> - max (- R) (min R (f \<omega>)) \<partial>M)\<bar>
      \<le> (\<integral>\<omega>. \<bar>f \<omega> - max (- R) (min R (f \<omega>))\<bar> \<partial>M)"
    by (rule integral_abs_bound)
  also have "\<dots> \<le> (\<integral>\<omega>. \<bar>f \<omega>\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f \<omega>) \<partial>M)"
    by (rule integral_mono[OF integrable_abs[OF idiff] iT])
       (rule clamp_diff_le_tail_pointwise[OF R])
  finally show ?thesis unfolding diff .
qed

subsection \<open>Weak convergence upgraded by uniform integrability\<close>

text \<open>\<open>weak_conv_on_nn_integral_le\<close> handles a non-negative integrand and
  bounds the limit above by truncating at \<open>K\<close> and using monotone
  convergence, with no integrability hypothesis --
  covering the \<open>\<preceq> L \<cdot> I\<close> half of the covariation constraint.

  The lower bounds \<open>\<Pi>\<^sub>m(a) \<ge> m-k\<close> run the other way, where weak
  convergence only gives the Fatou direction \<open>liminf \<ge> lim\<close>; recovering
  \<open>limsup \<le>\<close> is what uniform integrability buys, via the \<open>3\<epsilon>\<close> argument:
  truncate \<open>f\<close> at height \<open>R\<close> (bounded and continuous, so weak convergence
  applies directly) and control both truncation errors by the tail
  hypothesis, using \<open>clamp_integral_error\<close> and
  \<open>tendsto_real_of_approximants\<close> above;
  \<open>unif_integrable_of_L2_bound\<close> supplies the tail hypothesis from an
  \<open>L\<^sup>2\<close> bound on \<open>f\<close>, which for the squared increment is the
  fourth-moment bound.

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

text \<open>A finite Borel measure on a metric space is determined by its
  integrals against bounded continuous functions: apply the closed-set
  Portmanteau bound (@{thm [source] weak_conv_closedin_limsup}) to the
  constant sequence both ways, then extend from
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
    have "weak_conv_on (\<lambda>_ :: nat. Ma) Mb sequentially (mtopology_of m)"
      unfolding weak_conv_on_def
    proof (intro conjI allI impI)
      show "\<forall>\<^sub>F i in sequentially. sets Ma = sets (borel_of (mtopology_of m))
          \<and> finite_measure Ma" using sa fa by simp
      fix g assume "continuous_map (mtopology_of m) euclideanreal g"
        "\<exists>B. \<forall>x\<in>topspace (mtopology_of m). \<bar>g x\<bar> \<le> B"
      then show "(\<lambda>i. \<integral>x. g x \<partial>Ma) \<longlonglongrightarrow> (\<integral>x. g x \<partial>Mb)" by (simp add: eqab)
    qed (use sb fb in auto)
    from weak_conv_closedin_limsup[OF this clA] show ?thesis by (simp add: Limsup_const)
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

text \<open>Integrated identities such as \<open>E[Z\<sqdot>(X\<^sub>t - X\<^sub>s)] = 0\<close> for a
  bounded continuous test \<open>Z\<close> of the past, and its covariation analogue,
  are integrals of continuous but unbounded path functionals, so weak
  convergence alone does not transfer them.
  \<open>weak_conv_on_integral_unif_integrable\<close> above closes the gap given uniform
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

text \<open>The transfer itself: a continuous path functional with a uniform second-moment bound has its integral
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
  The moment hypotheses of \<open>path_laws_convergent_subsequence_vec\<close>,
  discharged per coordinate by the martingale estimate
  \<open>fourth_moment_L2_bochner\<close>: the path laws of any sequence of processes
  carrying, per coordinate, a continuous \<open>L\<^sup>2\<close> martingale from a common start
  with a compensated square whose compensator grows at rate at most \<open>C\<close> have
  a weakly convergent subsequence.
\<close>

corollary path_laws_convergent_subsequence_martingale:
  fixes MM :: "nat \<Rightarrow> 'a measure" and FF :: "nat \<Rightarrow> real \<Rightarrow> 'a measure"
    and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and AA :: "nat \<Rightarrow> 'm \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real"
    and T C \<gamma> :: real and x :: "real^'m"
  assumes T0: "0 \<le> T" and g0: "0 < \<gamma>" and g2: "\<gamma> < 1/4" and C0: "0 \<le> C"
    and P: "\<And>i. prob_space (MM i)"
    and Xm: "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)"
    and mgX: "\<And>i l. martingale (MM i) (FF i) 0 (\<lambda>s \<omega>. XX i s \<omega> $ l)"
    and sqX: "\<And>i l s. 0 \<le> s \<Longrightarrow> integrable (MM i) (\<lambda>\<omega>. (XX i s \<omega> $ l)\<^sup>2)"
    and contX: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> continuous_on {0..} (\<lambda>s. XX i s \<omega>)"
    and start: "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x"
    and mgZ: "\<And>i l. martingale (MM i) (FF i) 0
        (\<lambda>t \<omega>. (XX i t \<omega> $ l)\<^sup>2 - AA i l t \<omega>)"
    and A0: "\<And>i l \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> AA i l 0 \<omega> = 0"
    and A_rate: "\<And>i l \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> AA i l v \<omega> - AA i l u \<omega> \<and> AA i l v \<omega> - AA i l u \<omega> \<le> C * (v - u)"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> real^'m) measure)
      \<and> prob_space N
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
proof (rule path_laws_convergent_subsequence_vec[where C = C and x = x, OF T0 g0 g2])
  show "\<And>i. prob_space (MM i)" by (rule P)
  show "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)" by (rule Xm)
  show "continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    if w: "\<omega> \<in> space (MM i)" for i \<omega>
    by (rule continuous_on_subset[OF contX[OF w]]) auto
  show "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x" by (rule start)
  have bochner: "integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)
      \<and> (\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    if u0: "0 \<le> u" and uv: "u \<le> v" for i l u v
  proof -
    have contl: "continuous_on {0..} (\<lambda>s. XX i s \<omega> $ l)"
      if w: "\<omega> \<in> space (MM i)" for \<omega>
      by (rule continuous_on_component[OF contX[OF w]])
    have startl: "AE \<omega> in MM i. \<bar>XX i 0 \<omega> $ l\<bar> \<le> \<bar>x $ l\<bar>"
      by (intro AE_I2) (simp add: start)
    show ?thesis
      using fourth_moment_L2_bochner[OF P mgX sqX contl startl mgZ A0 A_rate C0 u0 uv]
      by blast
  qed
  show "integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    if "0 \<le> u" and "u \<le> v" and "v \<le> T" for i l u v
    using bochner[OF that(1,2)] by blast
  show "(\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    if "0 \<le> u" and "u \<le> v" and "v \<le> T" for i l u v
    using bochner[OF that(1,2)] by blast
qed

(*<*)
end
(*>*)
