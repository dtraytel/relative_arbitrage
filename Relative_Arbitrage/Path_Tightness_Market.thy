section \<open>Lemma 2.2, market form: subsequence extraction from the martingale package\<close>

(*<*)
theory Path_Tightness_Market
  imports "Path_Space_Tightness.Path_Tightness" Stopped_Localization
begin

(*>*)

text \<open>
  The adapter between the stochastic layer (@{theory Relative_Arbitrage.Stopped_Localization}) and the
  topological layer (@{theory Path_Space_Tightness.Path_Tightness}): the moment hypotheses of
  \<open>path_laws_convergent_subsequence_vec\<close> are discharged per coordinate by
  \<open>fourth_moment_L2_integrable\<close> / \<open>fourth_moment_L2_bochner\<close>, so the
  subsequence extraction of Lemma 2.2 holds for any sequence of laws carrying,
  per coordinate, an \<open>L\<^sup>2\<close> martingale with a compensated square whose adapted
  compensator grows at rate at most \<open>C\<close> --- the formal content of the paper's
  admissibility conditions Eqs. (1.7)-(1.8).
\<close>
corollary path_laws_convergent_subsequence_market:
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
    and Aad: "\<And>i l. adapted_process (MM i) (FF i) 0 (AA i l)"
    and A0: "\<And>i l \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> AA i l 0 \<omega> = 0"
    and A_rate: "\<And>i l \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> AA i l v \<omega> - AA i l u \<omega> \<and> AA i l v \<omega> - AA i l u \<omega> \<le> C * (v - u)"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
proof (rule path_laws_convergent_subsequence_vec[where C = C and x = x, OF T0 g0 g2])
  show "\<And>i. prob_space (MM i)" by (rule P)
  show "\<And>i u. 0 \<le> u \<Longrightarrow> XX i u \<in> borel_measurable (MM i)" by (rule Xm)
  show "continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
    if w: "\<omega> \<in> space (MM i)" for i \<omega>
    by (rule continuous_on_subset[OF contX[OF w]]) auto
  show "\<And>i \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i 0 \<omega> = x" by (rule start)
  show "integrable (MM i) (\<lambda>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4)"
    if u0: "0 \<le> u" and uv: "u \<le> v" and vT: "v \<le> T" for i l u v
  proof -
    have contl: "continuous_on {0..} (\<lambda>s. XX i s \<omega> $ l)"
      if w: "\<omega> \<in> space (MM i)" for \<omega>
      by (rule continuous_on_component[OF contX[OF w]])
    have startl: "XX i 0 \<omega> $ l = x $ l" if w: "\<omega> \<in> space (MM i)" for \<omega>
      using start[OF w] by simp
    show ?thesis
      by (rule fourth_moment_L2_integrable[OF P mgX sqX contl startl mgZ Aad A0
            A_rate C0 u0 uv])
  qed
  show "(\<integral>\<omega>. (XX i v \<omega> $ l - XX i u \<omega> $ l)^4 \<partial>(MM i)) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    if u0: "0 \<le> u" and uv: "u \<le> v" and vT: "v \<le> T" for i l u v
  proof -
    have contl: "continuous_on {0..} (\<lambda>s. XX i s \<omega> $ l)"
      if w: "\<omega> \<in> space (MM i)" for \<omega>
      by (rule continuous_on_component[OF contX[OF w]])
    have startl: "XX i 0 \<omega> $ l = x $ l" if w: "\<omega> \<in> space (MM i)" for \<omega>
      using start[OF w] by simp
    show ?thesis
      by (rule fourth_moment_L2_bochner[OF P mgX sqX contl startl mgZ Aad A0
            A_rate C0 u0 uv])
  qed
qed


section \<open>The exit time is upper semicontinuous\<close>

text \<open>The join.  \<open>Exit_Time.etime_less_iff\<close> says being strictly below \<open>c\<close>
  is witnessed by a single time \<open>r < c\<close> at which the path is already in
  \<open>A\<close>; \<open>Path_Space.open_hit_strictly_before\<close> says the witnessed condition
  is open in the path topology.  Together they give upper semicontinuity of
  the exit time, which is what Larsson--Ruf's Lemma 2.1 needs.

  This is the only theory in the development that sees both halves:
  @{theory Relative_Arbitrage.Exit_Time} sits under @{theory Relative_Arbitrage.Ito_Market} while @{theory Path_Space_Tightness.Path_Space} sits under the AFP
  Prokhorov entry, and the two branches meet nowhere else.

  The degenerate branch \<open>T < c\<close> is not a special case of the witnessed one:
  a path that never enters \<open>A\<close> still has exit time \<open>T\<close>, so when \<open>T < c\<close>
  every path qualifies and the set is the whole space.\<close>

lemma etime_usc_on_paths:
  fixes T c :: real and A :: "'b::polish_space set"
  assumes T: "0 \<le> T" and A: "open A"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         etime T A (\<lambda>s w. w s) f < c}"
proof (cases "T < c")
  case True
  have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
        etime T A (\<lambda>s w. w s) f < c}
      = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
  proof -
    have "etime T A (\<lambda>s w. w s) f < c" for f :: "real \<Rightarrow> 'b"
      using etime_le_T[OF T, of A "\<lambda>s w. w s" f] True by linarith
    thus ?thesis by blast
  qed
  then show ?thesis
    using openin_topspace[of
        "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)"]
    by simp
next
  case False
  have eq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
        etime T A (\<lambda>s w. w s) f < c}
      = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         \<exists>r. 0 \<le> r \<and> r \<le> T \<and> r < c \<and> f r \<in> A}"
  proof -
    have "etime T A (\<lambda>s w. w s) f < c
        \<longleftrightarrow> (\<exists>r. 0 \<le> r \<and> r \<le> T \<and> r < c \<and> f r \<in> A)"
      for f :: "real \<Rightarrow> 'b"
      using etime_less_iff[OF T, of A "\<lambda>s w. w s" f c] False by auto
    thus ?thesis by blast
  qed
  show ?thesis unfolding eq by (rule open_hit_strictly_before[OF A])
qed

text \<open>Lemma 2.2 of arXiv:2512.17702, at the market class itself: for any
  sequence of sufficiently volatile markets that are stopped at their horizon
  and confined to a ball, the path laws admit a weakly convergent
  subsequence.  The almost-sure hypotheses of the locale become the pointwise
  hypotheses of the adapter above by restricting each market to a
  full-measure good event (the transfer package of @{theory Relative_Arbitrage.Stopped_Localization});
  the restriction is invisible to the path laws.  The per-coordinate
  compensator is the entrywise integral of \<open>acov\<close>, whose rate bound \<open>L\<close> comes
  from the eigenvalue constraint through the diagonal entries.\<close>

section \<open>Diagonal entries under the eigenvalue constraints\<close>

lemma diag_entry_quadform:
  fixes a :: "real^'m::finite^'m"
  shows "axis l 1 \<bullet> (a *v axis l 1) = a $ l $ l"
proof -
  have col: "(a *v axis l 1) $ l = a $ l $ l"
    by (simp add: matrix_vector_mult_def axis_def if_distrib
        cong: if_cong)
  have "axis l 1 \<bullet> (a *v axis l 1) = (a *v axis l 1) $ l"
    by (metis cart_eq_inner_axis inner_commute)
  with col show ?thesis by simp
qed

lemma psd_diag_nonneg:
  fixes a :: "real^'m::finite^'m"
  assumes "psd a"
  shows "0 \<le> a $ l $ l"
  using assms diag_entry_quadform[where a = a and l = l]
  by (auto simp: psd_def dest: spec[of _ "axis l 1"])

lemma eigen_ub_diag:
  fixes a :: "real^'m::finite^'m"
  assumes "eigen_ub a L"
  shows "a $ l $ l \<le> L"
proof -
  have ax: "axis l 1 \<bullet> (axis l 1 :: real^'m) = 1"
    by (simp add: inner_vec_def axis_def if_distrib cong: if_cong)
  show ?thesis
    using assms diag_entry_quadform[where a = a and l = l] ax
    by (auto simp: eigen_ub_def dest: spec[of _ "axis l 1"])
qed

section \<open>Lemma 2.2 at the market class\<close>

theorem market_path_laws_convergent_subsequence:
  fixes MM :: "nat \<Rightarrow> 'a measure" and FF :: "nat \<Rightarrow> real \<Rightarrow> 'a measure"
    and XX :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m::finite"
    and aa :: "nat \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> real^'m^'m"
    and tt :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and k :: nat and L r T :: real
    and K :: "(real^'m) set" and x0 :: "real^'m"
  assumes svm: "\<And>i. sufficiently_volatile_market (MM i) (FF i) (XX i) (aa i)
      k L K x0 (tt i)"
    and stp: "\<And>i s \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> XX i s \<omega> = XX i (min s (tt i \<omega>)) \<omega>"
    and astop: "\<And>i s \<omega>. \<omega> \<in> space (MM i) \<Longrightarrow> tt i \<omega> < s \<Longrightarrow> aa i s \<omega> = 0"
    and Kball: "K \<subseteq> cball 0 r"
    and aint: "\<And>i. AE \<omega> in MM i. \<forall>l t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. aa i s \<omega> $ l $ l)"
    and T0: "0 \<le> T"
  shows "\<exists>a N. strict_mono a \<and> finite_measure N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric T :: (real \<Rightarrow> real^'m) metric)))
      \<and> N (space N) \<le> ennreal 1
      \<and> weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
proof -
  define good where "good = (\<lambda>i \<omega>.
      0 \<le> tt i \<omega> \<and> XX i 0 \<omega> = x0
      \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tt i \<omega> \<longrightarrow> XX i s \<omega> \<in> K)
      \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tt i \<omega> \<longrightarrow> psd (aa i s \<omega>))
      \<and> (\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tt i \<omega> \<longrightarrow> eigen_ub (aa i s \<omega>) L)
      \<and> (\<forall>l t. 0 \<le> t \<longrightarrow> set_integrable lborel {0..t}
            (\<lambda>s. aa i s \<omega> $ l $ l)))"
  have exG: "\<exists>G. G \<in> sets (MM i) \<and> (AE \<omega> in MM i. \<omega> \<in> G)
      \<and> (\<forall>\<omega>\<in>G. \<omega> \<in> space (MM i) \<and> good i \<omega>)" for i
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    have ae: "AE \<omega> in MM i. good i \<omega>"
      unfolding good_def
      using sv.tau_nonneg sv.X_start sv.X_in_K sv.acov_psd
        sv.acov_eigen_ub aint[of i]
      by eventually_elim blast
    then obtain N where N1: "{\<omega> \<in> space (MM i). \<not> good i \<omega>} \<subseteq> N"
      and N2: "N \<in> sets (MM i)" and N3: "emeasure (MM i) N = 0"
      by (rule AE_E)
    have GN: "space (MM i) - N \<in> sets (MM i)"
      by (intro sets.Diff sets.top N2)
    have aeG: "AE \<omega> in MM i. \<omega> \<in> space (MM i) - N"
    proof -
      have "AE \<omega> in MM i. \<omega> \<notin> N"
        by (rule AE_not_in) (use N2 N3 in \<open>auto simp: null_sets_def\<close>)
      then show ?thesis by auto
    qed
    have gd: "\<omega> \<in> space (MM i) \<and> good i \<omega>"
      if "\<omega> \<in> space (MM i) - N" for \<omega>
      using that N1 by auto
    show ?thesis
      by (intro exI[of _ "space (MM i) - N"] conjI GN aeG ballI gd)
  qed
  define GG where "GG = (\<lambda>i. SOME G. G \<in> sets (MM i)
      \<and> (AE \<omega> in MM i. \<omega> \<in> G)
      \<and> (\<forall>\<omega>\<in>G. \<omega> \<in> space (MM i) \<and> good i \<omega>))"
  \<comment> \<open>Extract the defining property once, then project: unfolding
      \<^verbatim>\<open>GG_def\<close> afresh for each conjunct would force the simplifier to
      search under the \<^verbatim>\<open>SOME\<close>-term three times, so \<^verbatim>\<open>someI_ex\<close> is
      applied once instead.\<close>
  have GGspec: "GG i \<in> sets (MM i)
      \<and> (AE \<omega> in MM i. \<omega> \<in> GG i)
      \<and> (\<forall>\<omega>\<in>GG i. \<omega> \<in> space (MM i) \<and> good i \<omega>)" for i
    unfolding GG_def by (rule someI_ex[OF exG[of i]])
  have GG1: "GG i \<in> sets (MM i)" for i
    using GGspec[of i] by (rule conjunct1)
  have GG2: "AE \<omega> in MM i. \<omega> \<in> GG i" for i
    using GGspec[of i] by (rule conjunct2[THEN conjunct1])
  have GG3: "\<omega> \<in> space (MM i) \<and> good i \<omega>" if "\<omega> \<in> GG i" for i \<omega>
    using GGspec[of i, THEN conjunct2, THEN conjunct2] that by (rule bspec)
  let ?M' = "\<lambda>i. restrict_space (MM i) (GG i)"
  let ?F' = "\<lambda>i t. restrict_space (FF i t) (GG i)"
  let ?A = "\<lambda>i l t \<omega>. set_lebesgue_integral lborel {0..t}
      (\<lambda>s. aa i s \<omega> $ l $ l)"
  have prj: "(\<lambda>x :: real^'m. x $ l) \<in> borel_measurable borel" for l
    by (intro borel_measurable_continuous_onI linear_continuous_on
        bounded_linear_vec_nth)
  have P': "prob_space (?M' i)" for i
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    show ?thesis
      by (rule prob_space_restrict_full[OF sv.prob_space_M GG1 GG2])
  qed
  have sp': "space (?M' i) = GG i" for i
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    show ?thesis
      by (rule space_restrict_full[OF sv.prob_space_M GG1 GG2])
  qed
  have Xm': "XX i u \<in> borel_measurable (?M' i)" if "0 \<le> u" for i u
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    show ?thesis
      by (intro measurable_restrict_space1 sv.random_variable that)
  qed
  have mgX': "martingale (?M' i) (?F' i) 0 (\<lambda>s \<omega>. XX i s \<omega> $ l)" for i l
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    have "martingale (?M' i) (?F' i) 0 (XX i)"
      by (rule martingale_restrict_full
          [OF sv.prob_space_M GG1 GG2 sv.martingale_axioms])
    then show ?thesis by (rule martingale_vec_component)
  qed
  have bnd: "norm (XX i s \<omega>) \<le> r" if w: "\<omega> \<in> GG i" and s: "0 \<le> s" for i s \<omega>
  proof -
    from GG3[OF w] have wsp: "\<omega> \<in> space (MM i)" and g: "good i \<omega>" by auto
    have t0: "0 \<le> tt i \<omega>" using g by (simp add: good_def)
    have m0: "0 \<le> min s (tt i \<omega>)" using s t0 by simp
    have mle: "min s (tt i \<omega>) \<le> tt i \<omega>" by simp
    from g have inK: "\<forall>s'. 0 \<le> s' \<longrightarrow> s' \<le> tt i \<omega> \<longrightarrow> XX i s' \<omega> \<in> K"
      by (simp add: good_def)
    have "XX i s \<omega> = XX i (min s (tt i \<omega>)) \<omega>" by (rule stp[OF wsp])
    also have "\<dots> \<in> K" using inK m0 mle by blast
    finally have "XX i s \<omega> \<in> K" .
    then show ?thesis using Kball by (auto simp: dist_norm)
  qed
  have sqX': "integrable (?M' i) (\<lambda>\<omega>. (XX i s \<omega> $ l)\<^sup>2)"
    if s: "0 \<le> s" for i l s
  proof -
    have fm: "finite_measure (?M' i)"
      by (rule prob_space.finite_measure[OF P'])
    show ?thesis
    proof (rule finite_measure.integrable_const_bound[OF fm, of _ "r\<^sup>2"])
      show "(\<lambda>\<omega>. (XX i s \<omega> $ l)\<^sup>2) \<in> borel_measurable (?M' i)"
        by (intro borel_measurable_power
            measurable_compose[OF Xm'[OF s] prj])
      show "AE \<omega> in ?M' i. norm ((XX i s \<omega> $ l)\<^sup>2) \<le> r\<^sup>2"
      proof (rule AE_I2)
        fix \<omega> assume "\<omega> \<in> space (?M' i)"
        then have w: "\<omega> \<in> GG i" by (simp add: sp')
        have "\<bar>XX i s \<omega> $ l\<bar> \<le> norm (XX i s \<omega>)"
          by (rule component_le_norm_cart)
        also have "\<dots> \<le> r" by (rule bnd[OF w s])
        finally have "\<bar>XX i s \<omega> $ l\<bar>\<^sup>2 \<le> r\<^sup>2"
          by (intro power_mono) auto
        then show "norm ((XX i s \<omega> $ l)\<^sup>2) \<le> r\<^sup>2" by simp
      qed
    qed
  qed
  have contX': "continuous_on {0..} (\<lambda>s. XX i s \<omega>)"
    if "\<omega> \<in> space (?M' i)" for i \<omega>
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    from that sp' GG3 have "\<omega> \<in> space (MM i)" by blast
    then show ?thesis by (rule sv.X_paths_cont)
  qed
  have start': "XX i 0 \<omega> = x0" if "\<omega> \<in> space (?M' i)" for i \<omega>
    using GG3 that by (auto simp: sp' good_def)
  have mgZ': "martingale (?M' i) (?F' i) 0
      (\<lambda>t \<omega>. (XX i t \<omega> $ l)\<^sup>2 - ?A i l t \<omega>)" for i l
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    have "martingale (?M' i) (?F' i) 0 (coord_Z (XX i) (aa i) l)"
      by (rule martingale_restrict_full
          [OF sv.prob_space_M GG1 GG2 sv.coord_Z_martingale])
    moreover have "coord_Z (XX i) (aa i) l
        = (\<lambda>t \<omega>. (XX i t \<omega> $ l)\<^sup>2 - ?A i l t \<omega>)"
      by (simp add: coord_Z_def fun_eq_iff)
    ultimately show ?thesis by simp
  qed
  have Aad': "adapted_process (?M' i) (?F' i) 0 (?A i l)" for i l
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    interpret CZ: martingale "MM i" "FF i" 0 "coord_Z (XX i) (aa i) l"
      by (rule sv.coord_Z_martingale)
    have ap: "adapted_process (MM i) (FF i) 0 (?A i l)"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure (MM i) (FF i) 0"
        by (rule sv.filtered_measure_axioms)
      fix u :: real assume u: "0 \<le> u"
      have m1: "(\<lambda>\<omega>. (XX i u \<omega> $ l)\<^sup>2) \<in> borel_measurable (FF i u)"
        by (intro borel_measurable_power
            measurable_compose[OF sv.adapted[OF u] prj])
      have m2: "coord_Z (XX i) (aa i) l u \<in> borel_measurable (FF i u)"
        by (rule CZ.adapted[OF u])
      have "(\<lambda>\<omega>. (XX i u \<omega> $ l)\<^sup>2 - coord_Z (XX i) (aa i) l u \<omega>)
          \<in> borel_measurable (FF i u)"
        by (intro borel_measurable_diff m1 m2)
      moreover have "?A i l u
          = (\<lambda>\<omega>. (XX i u \<omega> $ l)\<^sup>2 - coord_Z (XX i) (aa i) l u \<omega>)"
        by (simp add: coord_Z_def fun_eq_iff)
      ultimately show "?A i l u \<in> borel_measurable (FF i u)" by simp
    qed
    show ?thesis
      by (rule adapted_process_restrict_full
          [OF sv.prob_space_M GG1 GG2 ap])
  qed
  have A0': "?A i l 0 \<omega> = 0" if "\<omega> \<in> space (?M' i)" for i l \<omega>
    by simp
  have Arate': "\<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
      0 \<le> ?A i l v \<omega> - ?A i l u \<omega> \<and> ?A i l v \<omega> - ?A i l u \<omega> \<le> L * (v - u)"
    if w: "\<omega> \<in> space (?M' i)" for i l \<omega>
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    from w sp' have wG: "\<omega> \<in> GG i" by blast
    from GG3[OF wG] have wsp: "\<omega> \<in> space (MM i)" and g: "good i \<omega>" by auto
    have ent_int: "\<forall>t. 0 \<le> t \<longrightarrow> set_integrable lborel {0..t}
        (\<lambda>s. aa i s \<omega> $ l $ l)"
      and psdg: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tt i \<omega> \<longrightarrow> psd (aa i s \<omega>)"
      and ubg: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> tt i \<omega> \<longrightarrow> eigen_ub (aa i s \<omega>) L"
      using g by (auto simp add: good_def)
    have L0: "0 \<le> L" using sv.L_ge by simp
    show ?thesis
    proof (intro allI impI conjI)
      fix u v :: real assume u: "0 \<le> u" and uv: "u \<le> v"
      have v: "0 \<le> v" using u uv by simp
      have pt: "0 \<le> aa i \<sigma> \<omega> $ l $ l \<and> aa i \<sigma> \<omega> $ l $ l \<le> L"
        if \<sigma>: "\<sigma> \<in> {u<..v}" for \<sigma>
      proof (cases "\<sigma> \<le> tt i \<omega>")
        case True
        have s0: "0 \<le> \<sigma>" using \<sigma> u by auto
        with True psdg ubg have "psd (aa i \<sigma> \<omega>)" "eigen_ub (aa i \<sigma> \<omega>) L"
          by blast+
        then show ?thesis
          by (auto intro: psd_diag_nonneg eigen_ub_diag)
      next
        case False
        then have "aa i \<sigma> \<omega> = 0" by (intro astop[OF wsp]) simp
        then show ?thesis using L0 by simp
      qed
      have splitset: "{0..v} = {0..u} \<union> {u<..v}" using u uv by auto
      have int_v: "set_integrable lborel {0..v} (\<lambda>s. aa i s \<omega> $ l $ l)"
        using ent_int v by blast
      have int_u: "set_integrable lborel {0..u} (\<lambda>s. aa i s \<omega> $ l $ l)"
        using ent_int u by blast
      have int_uv: "set_integrable lborel {u<..v} (\<lambda>s. aa i s \<omega> $ l $ l)"
        by (rule set_integrable_subset[OF int_v]) (use u in auto)
      have add: "?A i l v \<omega> = ?A i l u \<omega>
          + set_lebesgue_integral lborel {u<..v} (\<lambda>s. aa i s \<omega> $ l $ l)"
        unfolding splitset
        by (rule set_integral_Un) (auto intro: int_u int_uv)
      have zero_int: "set_integrable lborel {u<..v} (\<lambda>_. 0 :: real)"
        by (simp add: set_integrable_def)
      have lower: "0 \<le> set_lebesgue_integral lborel {u<..v}
          (\<lambda>s. aa i s \<omega> $ l $ l)"
      proof -
        have "set_lebesgue_integral lborel {u<..v} (\<lambda>_. 0 :: real)
            \<le> set_lebesgue_integral lborel {u<..v} (\<lambda>s. aa i s \<omega> $ l $ l)"
          by (rule set_integral_mono[OF zero_int int_uv]) (use pt in blast)
        then show ?thesis by simp
      qed
      have Lint: "set_integrable lborel {u<..v} (\<lambda>_. L)"
        unfolding set_integrable_def
        by (intro integrable_scaleR_left integrable_real_indicator)
          (use uv in \<open>auto\<close>)
      have upper: "set_lebesgue_integral lborel {u<..v}
          (\<lambda>s. aa i s \<omega> $ l $ l) \<le> L * (v - u)"
      proof -
        have "set_lebesgue_integral lborel {u<..v} (\<lambda>s. aa i s \<omega> $ l $ l)
            \<le> set_lebesgue_integral lborel {u<..v} (\<lambda>_. L)"
          by (rule set_integral_mono[OF int_uv Lint]) (use pt in blast)
        also have "set_lebesgue_integral lborel {u<..v} (\<lambda>_. L)
            = measure lborel {u<..v} *\<^sub>R L"
          by (intro set_integral_const)
            (use uv in \<open>auto\<close>)
        also have "measure lborel {u<..v} = v - u"
          using uv by simp
        finally show ?thesis by (simp add: mult.commute)
      qed
      show "0 \<le> ?A i l v \<omega> - ?A i l u \<omega>" using add lower by simp
      show "?A i l v \<omega> - ?A i l u \<omega> \<le> L * (v - u)" using add upper by simp
    qed
  qed
  have L0: "0 \<le> L"
  proof -
    interpret sv: sufficiently_volatile_market "MM 0" "FF 0" "XX 0" "aa 0"
        k L K x0 "tt 0" by (rule svm)
    show ?thesis using sv.L_ge by simp
  qed
  have g0: "0 < (1/8 :: real)" by simp
  have g2: "(1/8 :: real) < 1/4" by simp
  obtain a N where aN1: "strict_mono a" and aN2: "finite_measure N"
    and aN3: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
    and aN4: "N (space N) \<le> ennreal 1"
    and aN5: "weak_conv_on ((\<lambda>i. path_law (?M' i) (XX i) T) \<circ> a) N
        sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    using path_laws_convergent_subsequence_market[where MM = ?M'
        and FF = ?F' and XX = XX and AA = ?A and T = T and C = L
        and \<gamma> = "1/8" and x = x0,
        OF T0 g0 g2 L0 P' Xm' mgX' sqX' contX' start' mgZ' Aad' A0' Arate']
    by blast
  have pl_eq: "path_law (?M' i) (XX i) T = path_law (MM i) (XX i) T" for i
  proof -
    interpret sv: sufficiently_volatile_market "MM i" "FF i" "XX i" "aa i"
        k L K x0 "tt i" by (rule svm)
    have Xm0: "XX i t \<in> borel_measurable (MM i)" if "t \<in> {0..T}" for t
      using that by (intro sv.random_variable) simp
    have cont0: "continuous_on {0..T} (\<lambda>t. XX i t \<omega>)"
      if "\<omega> \<in> space (MM i)" for \<omega>
      by (rule continuous_on_subset[OF sv.X_paths_cont[OF that]]) auto
    have pm: "(\<lambda>\<omega>. restrict (\<lambda>t. XX i t \<omega>) {0..T}) \<in> measurable (MM i)
        (borel_of (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)))"
      by (rule pathify_measurable[OF T0 Xm0 cont0])
    show ?thesis
      unfolding path_law_def
      by (rule distr_restrict_full[OF sv.prob_space_M GG1 GG2 pm])
  qed
  have "(\<lambda>i. path_law (?M' i) (XX i) T) \<circ> a
      = (\<lambda>i. path_law (MM i) (XX i) T) \<circ> a"
    by (simp add: pl_eq fun_eq_iff)
  with aN5 have "weak_conv_on ((\<lambda>i. path_law (MM i) (XX i) T) \<circ> a) N
      sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))"
    by simp
  then show ?thesis
    using aN1 aN2 aN3 aN4 by blast
qed


(*<*)
end
(*>*)
