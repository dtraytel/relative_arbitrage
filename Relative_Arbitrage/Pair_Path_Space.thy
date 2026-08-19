section \<open>The pair path space\<close>

(*<*)
theory Pair_Path_Space
  imports
    "Continuous_Path_Spaces.Path_Space" "Continuous_Path_Spaces.Path_Space_Infinite"
    "Continuous_Path_Spaces.Path_Exit_Times" "Continuous_Path_Spaces.Path_Tightness"
    "Continuous_Path_Spaces.Pathwise_Quadratic_Variation"
    "Continuous_Path_Spaces.Adapted_Quadratic_Variation"
    "Continuous_Path_Spaces.Stopped_Localization"
    "Continuous_Path_Spaces.Increment_Moments" "Continuous_Path_Spaces.Holder_Interpolation"
    "Continuous_Path_Spaces.Conditional_UI"
    "Continuous_Time_Martingales.Doob_Inequality" "Continuous_Time_Martingales.Optional_Sampling"
    "Continuous_Time_Martingales.Stopping_Times" "Continuous_Time_Martingales.Natural_Filtration"
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Time_Martingales.Semidirect_Kernels"
    "Continuous_Time_Martingales.Martingale_Algebra"
    "Continuous_Time_Martingales.Martingale_Transfer"
    "Continuous_Time_Martingales.Modification_Transfer"
    "Continuous_Time_Martingales.Time_Discretisation"
    "Continuous_Time_Martingales.Vitali_Convergence"
    "Continuous_Time_Martingales.Stopped_Adaptedness"
    "Symmetric_Matrix_Spectra.Matrix_Algebra" "Symmetric_Matrix_Spectra.Ky_Fan"
    "Symmetric_Matrix_Spectra.Orthonormal_Families" "Symmetric_Matrix_Spectra.Outer_Products"
    "Symmetric_Matrix_Spectra.Poincare_Separation" "Symmetric_Matrix_Spectra.Symmetric_Spectral"
    "Symmetric_Matrix_Spectra.Householder_Rotation"
    "Semicontinuous_Analysis.Semicontinuity" "Semicontinuous_Analysis.Berge"
    "Semicontinuous_Analysis.Semicontinuous_Selection"
    "Second_Order_Viscosity_Analysis.Sup_Convolution"
    "Second_Order_Viscosity_Analysis.Doubling_Of_Variables"
    "Wiener_Measure.Brownian_Finite_Dimensional_Distributions"
    "Disintegration.Disintegration"
begin

(*>*)

text \<open>The state and its covariation, carried as one path.\<close>

type_synonym 'n pairpath = "real \<Rightarrow> (real^'n) \<times> (real^'n^'n)"

text \<open>The path space this development works on carries a pair: the state
  and its covariation, \<open>real \<Rightarrow> (real^'n) \<times> (real^'n^'n)\<close>.  This theory fixes
  that type and collects what is true of paths, and of laws of paths, before
  any constraint on the covariation is imposed -- measurability of the
  coordinates, continuity of evaluation, martingale clauses for a general
  law, and the localisation facts the tightness argument runs on.\<close>

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
      \<and> sets N = sets (path_borel T :: (real \<Rightarrow> real^'m) measure)
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

text \<open>The join.  \<open>Stopping_Times.etime_less_iff\<close> says being strictly below \<open>c\<close>
  is witnessed by a single time \<open>r < c\<close> at which the path is already in
  \<open>A\<close>; \<open>Path_Space.open_hit_strictly_before\<close> says the witnessed condition
  is open in the path topology.  Together they give upper semicontinuity of
  the exit time, which is what Larsson--Ruf's Lemma 2.1 needs.

  The degenerate branch \<open>T < c\<close> is not a special case of the witnessed one:
  a path that never enters \<open>A\<close> still has exit time \<open>T\<close>, so when \<open>T < c\<close>
  every path qualifies and the set is the whole space.\<close>

text \<open>Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close>, at the market class itself: for any
  sequence of sufficiently volatile markets that are stopped at their horizon
  and confined to a ball, the path laws admit a weakly convergent
  subsequence.  The almost-sure hypotheses of the locale become the pointwise
  hypotheses of the adapter above by restricting each market to a
  full-measure good event (the transfer package of \<open>Stopped_Localization\<close>);
  the restriction is invisible to the path laws.  The per-coordinate
  compensator is the entrywise integral of \<open>acov\<close>, whose rate bound \<open>L\<close> comes
  from the eigenvalue constraint through the diagonal entries.\<close>

section \<open>Diagonal entries under the eigenvalue constraints\<close>

text \<open>\<open>diag_entry_quadform\<close> lives in \<open>Matrix_Algebra\<close>.\<close>

(*<*)
(*<*)

text \<open>\<open>radial_sq_upto\<close> transports the growth identity to the
  endpoint of a half-open confinement interval.  Nothing in its proof is
  specific to \<open>\<lambda>w. (norm (w - y\<^sub>0))\<^sup>2\<close> --- any continuous functional of the
  position does --- and the sharp bound below needs it for the projected
  square as well.\<close>

lemma radial_sq_upto_gen:
  fixes \<omega> :: "'n::finite pairpath" and TT e c0 cn :: real
    and RO :: "(real^'n) set" and F :: "real^'n \<Rightarrow> real"
  assumes wm: "\<omega> \<in> mspace (path_metric TT :: ('n pairpath) metric)"
    and Fc: "continuous_on UNIV F"
    and grow: "\<And>t. 0 < t \<Longrightarrow> t \<le> TT \<Longrightarrow>
      (\<forall>s\<in>{0..t}. fst (\<omega> s) \<in> RO) \<Longrightarrow> F (fst (\<omega> t)) = c0 + t * cn"
    and e0: "0 < e" and eT: "e \<le> TT"
    and inside: "\<And>s. 0 \<le> s \<Longrightarrow> s < e \<Longrightarrow> fst (\<omega> s) \<in> RO"
  shows "F (fst (\<omega> e)) = c0 + e * cn"
proof -
  define g where "g = (\<lambda>s. F (fst (\<omega> s)))"
  have gc: "continuous_on {0..TT} g"
  proof -
    have wc: "continuous_on {0..TT} \<omega>"
      by (rule mspace_path_metricD[OF wm])
    have fc: "continuous_on {0..TT} (\<lambda>s. fst (\<omega> s))"
      by (rule continuous_on_fst[OF wc])
    show ?thesis
      unfolding g_def by (rule continuous_on_compose2[OF Fc fc]) auto
  qed
  define tj where "tj = (\<lambda>j. e - e / (2 * real (Suc j)))"
  have tjl: "0 < tj j" for j
  proof -
    have "e / (2 * real (Suc j)) \<le> e / 2"
    proof (rule divide_left_mono)
      show "2 \<le> 2 * real (Suc j)" by simp
      show "0 \<le> e" using e0 by linarith
      show "0 < 2 * real (Suc j) * 2" by simp
    qed
    then show ?thesis unfolding tj_def using e0 by linarith
  qed
  have tju: "tj j < e" for j
  proof -
    have "0 < e / (2 * real (Suc j))" using e0 by simp
    then show ?thesis unfolding tj_def by linarith
  qed
  have tjT: "tj j \<le> TT" for j using tju[of j] eT by linarith
  have glow: "g (tj j) = c0 + tj j * cn" for j
    unfolding g_def
  proof (rule grow)
    show "0 < tj j" by (rule tjl)
    show "tj j \<le> TT" by (rule tjT)
    show "\<forall>s\<in>{0..tj j}. fst (\<omega> s) \<in> RO"
    proof
      fix s assume s: "s \<in> {0..tj j}"
      then have "0 \<le> s" and "s < e" using tju[of j] by auto
      then show "fst (\<omega> s) \<in> RO" by (rule inside)
    qed
  qed
  have tjlim: "tj \<longlonglongrightarrow> e"
  proof -
    have eq: "(\<lambda>j. (e / 2) * inverse (real (Suc j)))
        = (\<lambda>j. e / (2 * real (Suc j)))"
      by (rule ext) (simp add: field_simps)
    have "(\<lambda>j. (e / 2) * inverse (real (Suc j))) \<longlonglongrightarrow> (e / 2) * 0"
      by (intro tendsto_mult tendsto_const LIMSEQ_inverse_real_of_nat)
    then have "(\<lambda>j. e / (2 * real (Suc j))) \<longlonglongrightarrow> 0"
      unfolding eq by simp
    then have "(\<lambda>j. e - e / (2 * real (Suc j))) \<longlonglongrightarrow> e - 0"
      by (intro tendsto_diff tendsto_const)
    then show ?thesis unfolding tj_def by simp
  qed
  have gcomp: "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> g e"
  proof -
    have inS: "\<forall>n. tj n \<in> {0..TT}"
      using tjl tjT by (auto intro: less_imp_le)
    have eS: "e \<in> {0..TT}" using e0 eT by auto
    have "(g \<circ> tj) \<longlonglongrightarrow> g e"
      using continuous_on_sequentially[THEN iffD1, OF gc] inS eS tjlim
      by blast
    then show ?thesis by (simp add: o_def)
  qed
  have vlim: "(\<lambda>j. c0 + tj j * cn) \<longlonglongrightarrow> c0 + e * cn"
    by (intro tendsto_add tendsto_const tendsto_mult tjlim)
  have "(\<lambda>j. g (tj j)) \<longlonglongrightarrow> c0 + e * cn"
    using vlim unfolding glow by simp
  then have "g e = c0 + e * cn"
    using gcomp LIMSEQ_unique by blast
  then show ?thesis unfolding g_def .
qed

text \<open>The subspace-tangential member confines the path to
  \<open>cball 0 rB \<subseteq> K\<close> for any deterministic time \<open>cc\<close> strictly below
  \<open>\<delta> = (rB\<^sup>2 - |x|\<^sup>2)/(m-1)\<close>.  The inner barrier is unreachable because the
  projected square only grows, and the outer sphere pins the time exactly
  because the full square grows at the same rate --- that is what the
  upgraded \<open>subspace_tangential_exact_growth\<close> delivers.
  Feeding the constant-time DPP gives \<open>cc \<le> v(x)\<close>, and \<open>cc\<close> is a free
  parameter, so no factor \<open>2\<close> and no \<open>T/2\<close> cap survive: letting
  \<open>cc \<longrightarrow> min T \<delta>\<close> is the corollary below.\<close>

text \<open>Stopping at the exit time from a ball of radius \<open>r\<close> makes the process
  bounded, which is the one hypothesis of the scalar theory that a class member fails.
  Everything else survives stopping: the martingale property by
  \<open>stopped_martingale_L2\<close>, the compensator relation by
  \<open>stopped_compensated_square\<close>, and the rate because \<open>min u tau \<le> min v tau\<close> with
  \<open>min v tau - min u tau \<le> v - u\<close>.\<close>

lemma qvps_eq_A_stopped:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and T0: "0 < T" and r0: "0 < r"
    and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<bar>X 0 \<omega>\<bar> < r"
  defines "tau \<equiv> etime T {y :: real. r \<le> norm y} X"
  shows "AE \<omega> in M. qvp_good C (\<lambda>s. X (min s (tau \<omega>)) \<omega>)
           \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
                qvps (\<lambda>s. X (min s (tau \<omega>)) \<omega>) t = A (min t (tau \<omega>)) \<omega>)"proof -
  interpret MX: martingale M F "0::real" X by (rule mgX)
  have Tnn: "0 \<le> T" using T0 by simp
  have Acl: "closed {y :: real. r \<le> norm y}"
    by (intro closed_Collect_le continuous_intros)
  have Ane: "{y :: real. r \<le> norm y} \<noteq> {}" using r0 by (auto intro!: exI[of _ r])
  have contT: "continuous_on {0..T} (\<lambda>s. X s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF contX[OF w]]) auto

  text \<open>The exit time is a stopping time.\<close>
  interpret CA: cont_adapted_process M F X T
  proof (intro cont_adapted_process.intro cont_adapted_process_axioms.intro)
    show "adapted_process M F 0 X" by (rule MX.adapted_process_axioms)
    show "0 \<le> T" by (rule Tnn)
    show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>s. X s \<omega>)" by (rule contT)
  qed
  have tau_stop: "{\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)" if s: "0 \<le> s" for s
    unfolding tau_def by (rule CA.etime_stopping_time[OF Acl Ane s])
  have tau_nn: "0 \<le> tau \<omega>" for \<omega> unfolding tau_def by (rule etime_nonneg[OF Tnn])
  have tau_le: "tau \<omega> \<le> T" for \<omega> unfolding tau_def by (rule etime_le_T[OF Tnn])

  text \<open>The stopped process is bounded by the radius.\<close>
  have bndS: "\<bar>X (min v (tau \<omega>)) \<omega>\<bar> \<le> r" if w: "\<omega> \<in> space M" and v: "0 \<le> v" for v \<omega>
  proof -
    have s1: "0 \<le> min v (tau \<omega>)" using v tau_nn[of \<omega>] by simp
    have s2: "min v (tau \<omega>) \<le> etime T {y :: real. r \<le> norm y} X \<omega>"
      unfolding tau_def[symmetric] by simp
    have "X (min v (tau \<omega>)) \<omega> \<in> cball 0 r"
      by (rule etime_stays_in_cball[where T = T and r = r and X = X and \<omega> = \<omega>
            and s = "min v (tau \<omega>)"])
         (use X0[OF w] contT[OF w] s1 s2 r0 Tnn in simp_all)
    then show ?thesis by (simp add: dist_norm)
  qed

  text \<open>The stopped compensator keeps the rate.\<close>
  have rateS: "0 \<le> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>
      \<and> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega> \<le> C * (v - u)"
    if w: "\<omega> \<in> space M" and u: "0 \<le> u" and uv: "u \<le> v" for u v \<omega>
  proof -
    have m1: "0 \<le> min u (tau \<omega>)" using u tau_nn[of \<omega>] by simp
    have m2: "min u (tau \<omega>) \<le> min v (tau \<omega>)" using uv by simp
    have le: "min v (tau \<omega>) - min u (tau \<omega>) \<le> v - u" using uv by simp
    from A_rate[OF w, rule_format, OF m1 m2] have
      nn: "0 \<le> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>"
      and ub: "A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>
                 \<le> C * (min v (tau \<omega>) - min u (tau \<omega>))" by simp_all
    have "C * (min v (tau \<omega>) - min u (tau \<omega>)) \<le> C * (v - u)"
      using C0 le by (rule mult_left_mono[rotated])
    with nn ub show ?thesis by simp
  qed

  text \<open>The stopped pair satisfies the hypotheses of the scalar theory.\<close>
  interpret S: bounded_martingale_compensator M F
      "\<lambda>v \<omega>. X (min v (tau \<omega>)) \<omega>" "\<lambda>v \<omega>. A (min v (tau \<omega>)) \<omega>" C r
  proof (rule bounded_martingale_compensator.intro)
    show "prob_space M" by (rule P)
    show "0 \<le> C" by (rule C0)
    show "0 \<le> r" using r0 by simp
    show "martingale M F 0 (\<lambda>v \<omega>. X (min v (tau \<omega>)) \<omega>)"
      by (rule stopped_martingale_L2[OF P mgX sqX contX tau_nn tau_stop])
    show "martingale M F 0 (\<lambda>v \<omega>. (X (min v (tau \<omega>)) \<omega>)\<^sup>2 - A (min v (tau \<omega>)) \<omega>)"
      by (rule stopped_compensated_square
            [OF P mgX sqX contX mgZ A0 A_rate C0 tau_nn tau_stop])
    show "AE \<omega> in M. \<bar>X (min v (tau \<omega>)) \<omega>\<bar> \<le> r" if "0 \<le> v" for v
      using bndS[OF _ that] by (intro AE_I2) blast
    show "AE \<omega> in M. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>
        \<and> A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega> \<le> C * (v - u)"
      using rateS by (intro AE_I2) blast
    show "AE \<omega> in M. A (min 0 (tau \<omega>)) \<omega> = 0"
      using A0 tau_nn by (intro AE_I2) simp
    show "AE \<omega> in M. continuous_on {0..} (\<lambda>p. X (min p (tau \<omega>)) \<omega>)"
    proof (intro AE_I2)
      fix \<omega> assume w: "\<omega> \<in> space M"
      have "continuous_on {0..} (\<lambda>p. min p (tau \<omega>))" by (intro continuous_intros)
      moreover have "(\<lambda>p. min p (tau \<omega>)) ` {0..} \<subseteq> {0..}"
        using tau_nn[of \<omega>] by auto
      ultimately show "continuous_on {0..} (\<lambda>p. X (min p (tau \<omega>)) \<omega>)"
        by (rule continuous_on_compose2[OF contX[OF w], unfolded o_def])
    qed
  qed
  show ?thesis using S.qvp_good_ae S.qvps_eq_A by eventually_elim blast
qed

subsection \<open>The scalar identification without the boundedness hypothesis\<close>

text \<open>Letting the radius and the horizon grow together.  For a fixed time the
  path is bounded on \<open>{0..t}\<close> by continuity, so some level is never reached
  before \<open>t\<close>; there the stopped process agrees with \<open>X\<close> and the stopped
  compensator with \<open>A\<close>, and the congruence carries the identification across.
  The levels are indexed by naturals, so one countable intersection serves all
  of them.\<close>

lemma etime_shift_le_of_eroded:
  fixes A :: "'b::{polish_space,real_normed_vector} set"
  assumes T: "0 \<le> T" and rr: "0 \<le> r" "r \<le> T"
    and mem: "x + \<omega> r \<in> eroded \<delta> A"
    and near: "dist x y < \<delta>"
  shows "etime T A (\<lambda>s w. y + w s) \<omega> \<le> r"
proof -
  have "dist (x + \<omega> r) (y + \<omega> r) < \<delta>" using near by simp
  from eroded_shift[OF mem this] have inA: "y + \<omega> r \<in> A" .
  text \<open>The conclusion drives the unification here: chaining \<open>inA\<close> into the
    rule instead leaves \<open>?X r \<omega> \<in> A\<close> to be solved higher-order, with
    several solutions, so the step fails.\<close>
  show ?thesis
  proof (rule etime_le_of_mem)
    show "0 \<le> T" by (rule T)
    show "0 \<le> r" by (rule rr(1))
    show "r \<le> T" by (rule rr(2))
    show "y + \<omega> r \<in> A" by (rule inA)
  qed
qed

text \<open>From a witness time \<open>r\<close> carrying positive mass, extract an open set of
  paths, still of positive mass, on which the exit time stays below \<open>d\<close>
  for every nearby starting point; openness lets the measure-moving half
  of Berge's \<open>box\<close> go through by Portmanteau.\<close>

lemma etime_shift_uniform_margin:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and r: "0 \<le> r" "r \<le> T" "r < d"
    and pos: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
  shows "\<exists>\<delta>>0. \<exists>G. openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G
      \<and> emeasure P G \<noteq> 0
      \<and> (\<forall>y. dist x y < \<delta> \<longrightarrow> (\<forall>\<omega> \<in> G. etime T A (\<lambda>s w. y + w s) \<omega> < d))"
proof -
  have spP: "space P = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sP] by (simp add: space_borel_of)
  have rT: "r \<in> {0..T}" using r by simp
  have opn: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         x + f r \<in> eroded (1 / Suc n) A}" for n :: nat
    by (rule open_shifted_eval_preimage[OF rT open_eroded])
  have meas: "{\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A} \<in> sets P" for n :: nat
    using borel_of_open[OF opn[of n]] unfolding sP spP by simp
  obtain n :: nat where
    posn: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A} \<noteq> 0"
    by (rule positive_mass_at_some_erosion[OF A meas pos, THEN exE])
  define G where "G = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      x + f r \<in> eroded (1 / Suc n) A}"
  have Gspace: "G = {\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A}"
    unfolding G_def spP by simp
  have "(0::real) < 1 / Suc n" by simp
  moreover have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G"
    unfolding G_def by (rule opn)
  moreover have "emeasure P G \<noteq> 0" unfolding Gspace by (rule posn)
  moreover have "etime T A (\<lambda>s w. y + w s) \<omega> < d"
    if near: "dist x y < 1 / Suc n" and \<omega>: "\<omega> \<in> G" for y \<omega>
  proof -
    have le: "etime T A (\<lambda>s w. y + w s) \<omega> \<le> r"
    proof (rule etime_shift_le_of_eroded)
      show "0 \<le> T" by (rule T)
      show "0 \<le> r" by (rule r(1))
      show "r \<le> T" by (rule r(2))
      show "x + \<omega> r \<in> eroded (1 / Suc n) A" using \<omega> unfolding G_def by simp
      show "dist x y < 1 / Suc n" by (rule near)
    qed
    from le r(3) show ?thesis by linarith
  qed
  ultimately show ?thesis by blast
qed

text \<open>The countable reduction, at the level of measures: \<open>etime_less_iff_qtimes_open\<close>
  turns the event into a union over the countable \<open>qtimes T\<close>, so
  \<open>positive_of_countable_UN\<close> extracts a single witness time of positive
  mass --- needed before erosion, which requires a fixed time to erode
  around.\<close>

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

lemma psd_diag_nonneg:
  fixes a :: "real^'m::finite^'m"
  assumes "psd a"
  shows "0 \<le> a $ l $ l"
  using assms diag_entry_quadform[where a = a and l = l]
  by (auto simp: psd_def dest: spec[of _ "axis l 1"])

theorem etime_shift_box_half:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pos: "emeasure P
        {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "\<exists>\<delta>>0. \<exists>G. openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G
      \<and> emeasure P G \<noteq> 0
      \<and> (\<forall>y. dist x y < \<delta> \<longrightarrow> (\<forall>\<omega> \<in> G. etime T A (\<lambda>s w. y + w s) \<omega> < d))"
proof -
  obtain r where r: "r \<in> qtimes T" "r < d"
    and posr: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
    using positive_mass_at_some_qtime[OF T A dT sP pos] by blast
  have rT: "r \<in> {0..T}" using qtimes_subset[OF T] r(1) by blast
  show ?thesis
  proof (rule etime_shift_uniform_margin[OF T A sP])
    show "0 \<le> r" using rT by simp
    show "r \<le> T" using rT by simp
    show "r < d" by (rule r(2))
    show "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0" by (rule posr)
  qed
qed

text \<open>The same decomposition, used for measurability rather than for extraction:
  the event \<open>{\<tau>\<^sub>K(y + \<cdot>) < d}\<close> is a countable union of open sets, hence open, hence
  Borel; the final monotonicity step below needs this set to be Borel.\<close>

theorem qvps_eq_A_localised:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and B0: "0 \<le> B" and X0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<bar>X 0 \<omega>\<bar> \<le> B"
  shows "AE \<omega> in M. qvp_good C (\<lambda>s. X s \<omega>)
           \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega>) t = A t \<omega>)"
proof -
  define lev where "lev = (\<lambda>R::nat. B + real (Suc R))"
  define tau where
    "tau = (\<lambda>R::nat. etime (real (Suc R)) {y :: real. lev R \<le> norm y} X)"
  have lev_pos: "0 < lev R" for R using B0 by (simp add: lev_def)
  have T_pos: "(0::real) < real (Suc R)" for R by simp
  have X0lt: "\<bar>X 0 \<omega>\<bar> < lev R" if "\<omega> \<in> space M" for \<omega> R
    using X0[OF that] by (simp add: lev_def)
  have step: "AE \<omega> in M. qvp_good C (\<lambda>s. X (min s (tau R \<omega>)) \<omega>)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>)" for R
    unfolding tau_def
    by (rule qvps_eq_A_stopped
          [OF P mgX sqX contX mgZ A0 A_rate C0 T_pos lev_pos X0lt])
  have all: "AE \<omega> in M. \<forall>R::nat. qvp_good C (\<lambda>s. X (min s (tau R \<omega>)) \<omega>)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>)"
    by (subst AE_all_countable) (rule allI, rule step)
  have sp: "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  from all sp show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have key: "\<And>R t. 0 \<le> t \<Longrightarrow>
        qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>"
      and keyg: "\<And>R. qvp_good C (\<lambda>s. X (min s (tau R \<omega>)) \<omega>)"
      and w: "\<omega> \<in> space M" by blast+

    text \<open>Some level is not reached before a given time, because the path is
      bounded on the compact interval.\<close>
    have esc: "\<exists>n :: nat. t < tau n \<omega>" if t: "0 \<le> t" for t
    proof -
      have contt: "continuous_on {0..t} (\<lambda>s. X s \<omega>)"
        by (rule continuous_on_subset[OF contX[OF w]]) auto
      have "compact ((\<lambda>s. X s \<omega>) ` {0..t})"
        by (rule compact_continuous_image[OF contt compact_Icc])
      then have "bounded ((\<lambda>s. X s \<omega>) ` {0..t})" by (rule compact_imp_bounded)
      then obtain Bd where Bd: "\<And>y. y \<in> (\<lambda>s. X s \<omega>) ` {0..t} \<Longrightarrow> norm y \<le> Bd"
        by (auto simp: bounded_iff)
      obtain n :: nat where n: "max t Bd < real n" using reals_Archimedean2 by blast
      have nt: "t < real (Suc n)" using n by simp
      have nB: "Bd < lev n" using n B0 by (simp add: lev_def)
      have "t < tau n \<omega>"
      proof (rule ccontr)
        assume "\<not> t < tau n \<omega>"
        then have le: "tau n \<omega> \<le> t" by simp
        have "tau n \<omega> \<le> t \<longleftrightarrow> (\<exists>s\<in>{0..t}. X s \<omega> \<in> {y :: real. lev n \<le> norm y})"
          unfolding tau_def
        proof (rule etime_le_iff[OF _ t nt])
          show "(0::real) \<le> real (Suc n)" by simp
          show "closed {y :: real. lev n \<le> norm y}"
            by (intro closed_Collect_le continuous_intros)
          show "continuous_on {0..real (Suc n)} (\<lambda>s. X s \<omega>)"
            by (rule continuous_on_subset[OF contX[OF w]]) auto
        qed
        with le obtain s where s: "s \<in> {0..t}" and hit: "lev n \<le> \<bar>X s \<omega>\<bar>" by auto
        have "\<bar>X s \<omega>\<bar> \<le> Bd" using Bd[of "X s \<omega>"] s by auto
        with hit nB show False by simp
      qed
      then show ?thesis by blast
    qed

    show ?case
    proof
      show "\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega>) t = A t \<omega>"
      proof (intro allI impI)
        fix t :: real assume t: "0 \<le> t"
        obtain n :: nat where taut: "t < tau n \<omega>" using esc[OF t] by blast
        have "qvps (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) t = qvps (\<lambda>s. X s \<omega>) t"
          by (rule qvps_cong) (use taut in simp)
        moreover have "A (min t (tau n \<omega>)) \<omega> = A t \<omega>" using taut by simp
        ultimately show "qvps (\<lambda>s. X s \<omega>) t = A t \<omega>" using key[OF t, of n] by simp
      qed
    next
      show "qvp_good C (\<lambda>s. X s \<omega>)"
        unfolding qvp_good_def
      proof (intro conjI)
        show "qvp (\<lambda>s. X s \<omega>) 0 = 0" by simp
        show "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
            0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
            \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
                \<le> C * (real_of_rat q - real_of_rat p)"
        proof (intro allI impI)
        fix p q :: rat assume p: "0 \<le> p" and pq: "p \<le> q"
        then have q: "0 \<le> q" by simp
        have pq': "real_of_rat p \<le> real_of_rat q" using pq by (simp add: of_rat_less_eq)
        have q': "(0::real) \<le> real_of_rat q" using q by simp
        obtain n :: nat where taut: "real_of_rat q < tau n \<omega>" using esc[OF q'] by blast
        have ep: "qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat p)
            = qvp (\<lambda>s. X s \<omega>) (real_of_rat p)"
          by (rule qvp_cong) (use taut pq' p in auto)
        have eq: "qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat q)
            = qvp (\<lambda>s. X s \<omega>) (real_of_rat q)"
          by (rule qvp_cong) (use taut q in auto)
        from keyg[of n] p pq have
          "0 \<le> qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat q)
                 - qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat p)
           \<and> qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat q)
                 - qvp (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) (real_of_rat p)
               \<le> C * (real_of_rat q - real_of_rat p)"
          unfolding qvp_good_def by blast
        then show "0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
            \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
                \<le> C * (real_of_rat q - real_of_rat p)"
          using ep eq by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>The matrix identification without the boundedness hypothesis\<close>

text \<open>The polarisation, run through the localised scalar theorem.  The
  hypotheses are pointwise on \<open>space M\<close> rather than almost everywhere, which is
  what the stopping arguments need; the intended application reaches that form
  through the \<open>restrict_full\<close> package of
  @{theory Continuous_Path_Spaces.Stopped_Localization}.\<close>

theorem etime_shift_box:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and Qi :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
    and x :: 'b and yi :: "nat \<Rightarrow> 'b"
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and wc: "weak_conv_on Qi P sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and sQ: "\<And>i. sets (Qi i) = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pQ: "\<And>i. prob_space (Qi i)" and pP: "prob_space P"
    and yconv: "yi \<longlonglongrightarrow> x"
    and pos: "emeasure P {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "eventually (\<lambda>i. emeasure (Qi i)
      {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0) sequentially"
proof -
  interpret PP: prob_space P by (rule pP)
  have sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    using wc[unfolded weak_conv_on_def] by blast
  obtain \<delta> G where d0: "0 < \<delta>"
    and Gopen: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G"
    and Gpos: "emeasure P G \<noteq> 0"
    and marg: "\<And>y \<omega>. dist x y < \<delta> \<Longrightarrow> \<omega> \<in> G
        \<Longrightarrow> etime T A (\<lambda>s w. y + w s) \<omega> < d"
    using etime_shift_box_half[OF T A dT sP pos] by blast
  have GP: "0 < measure P G"
  proof (rule ccontr)
    assume "\<not> 0 < measure P G"
    hence "measure P G = 0" using measure_nonneg[of P G] by linarith
    hence "ennreal (measure P G) = 0" by simp
    thus False using Gpos PP.emeasure_eq_measure by simp
  qed
  have ev1: "eventually (\<lambda>i. 0 < measure (Qi i) G) sequentially"
    by (rule weak_conv_open_positive_eventually[OF wc Gopen GP sQ pQ pP])
  have ev2: "eventually (\<lambda>i. dist x (yi i) < \<delta>) sequentially"
    using tendstoD[OF yconv d0] by (simp add: dist_commute)
  show ?thesis
  proof (rule eventually_mono[OF eventually_conj[OF ev1 ev2]])
    fix i
    assume h: "0 < measure (Qi i) G \<and> dist x (yi i) < \<delta>"
    interpret QQ: prob_space "Qi i" by (rule pQ)
    have spQ: "space (Qi i) = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using sets_eq_imp_space_eq[OF sQ[of i]] by (simp add: space_borel_of)
    have Gsub: "G \<subseteq> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using openin_subset[OF Gopen] by simp
    have sub: "G \<subseteq> {\<omega> \<in> space (Qi i).
        etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
    proof
      fix \<omega> assume w: "\<omega> \<in> G"
      have "etime T A (\<lambda>s w. yi i + w s) \<omega> < d"
        using marg[OF _ w] h by simp
      thus "\<omega> \<in> {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
        using w Gsub spQ by auto
    qed
    have meas: "{\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d}
        \<in> sets (Qi i)"
      using borel_of_open[OF open_etime_shift_less[OF T A dT]]
      unfolding sQ spQ by simp
    have "emeasure (Qi i) G \<noteq> 0"
      using h QQ.emeasure_eq_measure by simp
    moreover have "emeasure (Qi i) G
        \<le> emeasure (Qi i) {\<omega> \<in> space (Qi i).
             etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
      by (rule emeasure_mono[OF sub meas])
    ultimately show "emeasure (Qi i) {\<omega> \<in> space (Qi i).
        etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0" by auto
  qed
qed

subsection \<open>Upper semicontinuity of the supremum over a compact family\<close>

text \<open>
  The value functional, real-valued: \<open>ess_inf_time\<close> is
  \<open>ennreal\<close>-valued but Berge's supremum needs a real number; the
  conversion is faithful since the exit time is capped at \<open>T\<close>, so the
  essential infimum is never \<open>\<top>\<close>.
\<close>

lemma rot_col_cont:
  fixes q x c :: "real^'n::finite" and M :: "real^'n^'n" and A :: "(real^'n) set"
  assumes q0: "q \<noteq> 0"
    and ok: "\<And>y. y \<in> A \<Longrightarrow>
      0 < norm q * norm (q + M *v (y - x)) + q \<bullet> (q + M *v (y - x))"
  shows "continuous_on A (\<lambda>y. rotm q (q + M *v (y - x)) *v c)"
proof -
  have gradc: "continuous_on A (\<lambda>y::real^'n. q + M *v (y - x))"
  proof -
    have d: "continuous_on A (\<lambda>y :: real^'n. y - x)"
      by (intro continuous_intros)
    have mv: "continuous_on A (\<lambda>y :: real^'n. M *v (y - x))"
      by (rule continuous_on_compose2[OF
          linear_continuous_on[OF matvec_blin] d]) auto
    show ?thesis by (intro continuous_intros mv)
  qed
  show ?thesis
  proof (rule continuous_on_compose2[OF _ gradc])
    show "continuous_on {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}
        (\<lambda>w. rotm q w *v c)"
      by (rule rotm_vec_cont[OF q0]) simp
    show "(\<lambda>y::real^'n. q + M *v (y - x)) ` A
        \<subseteq> {w :: real^'n. 0 < norm q * norm w + q \<bullet> w}"
      using ok by blast
  qed
qed

definition outerp :: "real^'n::finite \<Rightarrow> real^'n^'n" where
  "outerp x = (\<chi> i j. x $ i * x $ j)"

text \<open>\<open>outerp\<close> is the rank-one projector \<open>x x\<^sup>T\<close> of the compensated
  martingale clause.  It is HOL's own \<open>outer_prod\<close> at equal arguments
  (\<open>outerp_eq_outer_prod\<close> below); it stays a definition of its own because
  making it an abbreviation unfolds it in every simp set that mentions it,
  and two proofs of the subsolution half then diverge.\<close>

lemma outerp_matvec_image:
  fixes S :: "real^'n::finite^'n" and w :: "real^'n"
  shows "outerp (S *v w) = S ** outerp w ** transpose S"
proof -
  have "outerp (S *v w) $ i $ j
      = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l)"
    for i j
  proof -
    have "outerp (S *v w) $ i $ j
        = (\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (\<Sum>l\<in>UNIV. S $ j $ l * w $ l)"
      by (simp add: outerp_def matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * w $ k)
        * (S $ j $ l * w $ l))"
      by (rule sum_distrib_left)
    also have "\<dots> = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l))
        * S $ j $ l)"
    proof (rule sum.cong[OF refl])
      fix l :: 'n
      have "(\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (S $ j $ l * w $ l)
          = (\<Sum>k\<in>UNIV. S $ i $ k * w $ k * (S $ j $ l * w $ l))"
        by (rule sum_distrib_right)
      also have "\<dots> = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l) * S $ j $ l)"
        by (rule sum.cong[OF refl]) (simp only: mult_ac)
      also have "\<dots> = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l"
        by (rule sum_distrib_right[symmetric])
      finally show "(\<Sum>k\<in>UNIV. S $ i $ k * w $ k) * (S $ j $ l * w $ l)
          = (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l" .
    qed
    finally show ?thesis .
  qed
  moreover have "(S ** outerp w ** transpose S) $ i $ j
      = (\<Sum>l\<in>UNIV. (\<Sum>k\<in>UNIV. S $ i $ k * (w $ k * w $ l)) * S $ j $ l)"
    for i j
    by (simp add: matrix_matrix_mult_def transpose_def outerp_def)
  ultimately show ?thesis by (simp add: vec_eq_iff)
qed

text \<open>\<open>matmul_scaleR_right\<close>, \<open>sandwich_mat1\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>

lemma outerp_scale_self:
  fixes u :: "real^'n::finite"
  shows "outerp (c *\<^sub>R u) = (c * c) *\<^sub>R outer_prod u u"
  by (simp add: vec_eq_iff outerp_def outer_prod_def)

lemma outerp_eq_outer_prod:
  fixes v :: "real^'n::finite"
  shows "outerp v = outer_prod v v"
  by (simp add: outerp_def outer_prod_def)

lemma trace_mult_outerp:
  fixes M :: "real^'n::finite^'n" and v :: "real^'n"
  shows "trace (M ** outerp v) = v \<bullet> (M *v v)"
  by (simp add: outerp_eq_outer_prod mult_outer_prod inner_commute)

text \<open>\<open>trace_mult_sum\<close>, \<open>bounded_linear_trace_mult_left\<close>, \<open>bounded_linear_trace_mult_right\<close>, \<open>bounded_linear_quadform\<close>, \<open>trace_mult_diff\<close>, \<open>trace_mult_scaleR\<close>, \<open>bounded_linear_transpose\<close> live in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


subsection \<open>The averaged covariation stays in the constraint set\<close>

text \<open>Every condition defining \<open>sconstraint\<close> is a linear (in)equality in
  the matrix: \<^const>\<open>psd\<close> and \<open>eigen_ub\<close> are conditions on the
  quadratic form \<open>z \<bullet> (a *v z)\<close>, linear in \<open>a\<close>, and \<open>c \<le> Pi_proj a m\<close> is by
  \<open>Pi_proj_ge\<close> an intersection of the half-spaces
  \<open>c \<le> trace (a ** P)\<close>, again linear in \<open>a\<close>.  The set is an intersection of
  closed half-spaces and passes through the integral.\<close>

text \<open>\<open>trace_mult_zero_right\<close> lives in @{theory Symmetric_Matrix_Spectra.Matrix_Algebra}.\<close>


lemma trace_mult_outerp_sum:
  fixes M :: "real^'n::finite^'n" and w :: "'b \<Rightarrow> real^'n" and F :: "'b set"
  assumes finF: "finite F"
  shows "trace (M ** (\<Sum>u\<in>F. outerp (w u))) = (\<Sum>u\<in>F. w u \<bullet> (M *v w u))"
  using finF
proof (induction F)
  case empty
  show ?case by (simp add: trace_mult_zero_right trace_def)
next
  case (insert u F)
  have "trace (M ** (\<Sum>v\<in>insert u F. outerp (w v)))
      = trace (M ** (outerp (w u) + (\<Sum>v\<in>F. outerp (w v))))"
    using insert.hyps by simp
  also have "\<dots> = trace (M ** outerp (w u))
      + trace (M ** (\<Sum>v\<in>F. outerp (w v)))"
    by (rule trace_mult_add)
  finally show ?case
    using insert by (simp add: trace_mult_outerp)
qed

subsection \<open>The constant-volatility Gaussian member\<close>

text \<open>The Euler kernels freeze the covariance at the step's left endpoint,
  so the building block is Brownian motion pushed through a constant
  matrix \<open>S\<close>: the pair \<open>(S \<cdot> W\<^sub>t, t \<cdot> S S\<^sup>T)\<close>, started at \<open>0\<close>.  Class
  membership mirrors \<open>bmpair_law_in_paper_pair_class\<close>: the
  martingale clauses are bounded-linear images of the Brownian ones
  (@{thm [source] martingale_bounded_linear_image}), the covariation
  clause is deterministic, and an arbitrary start comes free from
  \<open>exit_class_pshift\<close>.  The only hypothesis is
  \<open>S S\<^sup>T \<in> sconstraint k L\<close>.\<close>

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

abbreviation pairX :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> 'a"
  where "pairX t \<omega> \<equiv> fst (\<omega> t)"

theorem vshift_sup_usc:
  fixes T c :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and C :: "(real \<Rightarrow> 'b) measure set" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and cC: "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    and neC: "C \<noteq> {}"
    and sC: "\<And>Q. Q \<in> C \<Longrightarrow> sets Q = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pC: "\<And>Q. Q \<in> C \<Longrightarrow> prob_space Q"
    and lt: "Sup (vshift T A x ` C) < c"
  shows "eventually (\<lambda>y. Sup (vshift T A y ` C) < c) (nhds x)"
proof (rule usc_sup_over_compactin)
  show "compactin (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    by (rule cC)
  show "C \<noteq> {}" by (rule neC)
  show "bdd_above (vshift T A y ` C)" for y
    by (rule bdd_aboveI2[of _ _ T]) (use vshift_le[OF T] pC in blast)
  show "Sup (vshift T A x ` C) < c" by (rule lt)
next
  fix P :: "(real \<Rightarrow> 'b) measure" and d :: real
  assume P: "P \<in> C" and small: "vshift T A x P < d"
  have d0: "0 \<le> d"
  proof -
    have "0 \<le> vshift T A x P" unfolding vshift_def by simp
    with small show ?thesis by linarith
  qed
  show "\<exists>U V. open U \<and> openin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) V
      \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> C. vshift T A y Q < d)"
  proof (cases "T < d")
    text \<open>Berge quantifies \<open>box\<close> over every threshold above \<open>vshift T A x P\<close>,
      including thresholds beyond \<open>T\<close> --- that branch is trivial since the
      exit time never exceeds \<open>T\<close>, so the whole space works, and is split
      off because the witness machinery above assumes \<open>\<not> T < d\<close>.\<close>
    case True
    have allQ: "vshift T A y Q < d" if "Q \<in> C" for y Q
    proof -
      have "vshift T A y Q \<le> T" by (rule vshift_le[OF T pC[OF that]])
      with True show ?thesis by linarith
    qed
    have oT: "openin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        (topspace (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))))"
      by (rule openin_topspace)
    have Ptop: "P \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      using sC[OF P] prob_space.finite_measure[OF pC[OF P]] by simp
    text \<open>The witnesses \<open>U = UNIV\<close> and \<open>V = topspace\<close> must be handed over
      explicitly: left to invent them itself, \<open>blast\<close> does not terminate.\<close>
    have inst: "open (UNIV :: 'b set)
        \<and> openin (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
           (topspace (weak_conv_topology
              (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))))
        \<and> x \<in> (UNIV :: 'b set)
        \<and> P \<in> topspace (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> (\<forall>y \<in> (UNIV :: 'b set).
             \<forall>Q \<in> topspace (weak_conv_topology
                 (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) \<inter> C.
               vshift T A y Q < d)"
      using oT Ptop allQ by simp
    thus ?thesis by blast
  next
    case False
    hence dT: "\<not> T < d" by simp
    have posP: "emeasure P {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
      using small
      unfolding vshift_less_iff_positive_mass[OF T A dT d0 sC[OF P] pC[OF P]] .
    show ?thesis
    proof (rule box_of_sequential_euclidean)
      show "metrizable_space (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
        by (rule metrizable_weak_conv_path_topology)
      show "P \<in> topspace (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
        using sC[OF P] prob_space.finite_measure[OF pC[OF P]] by simp
    next
      fix yi :: "nat \<Rightarrow> 'b" and Qi :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
      assume yconv: "yi \<longlonglongrightarrow> x"
        and lQ: "limitin (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) Qi P sequentially"
        and inC: "\<And>i. Qi i \<in> C"
      text \<open>\<open>weak_conv_on\<close> is \<open>limitin (weak_conv_topology \<dots>)\<close> by definition.
        The membership \<open>Qi i \<in> C\<close> cannot be dropped: \<open>etime_shift_box\<close>
        needs each \<open>Qi i\<close> to be a probability measure, while an arbitrary
        measure near \<open>P\<close> in the weak topology is only finite.\<close>
      have wc: "weak_conv_on Qi P sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
        using lQ .
      have sQi: "sets (Qi i) = sets (path_borel T :: (real \<Rightarrow> 'b) measure)" for i
        by (rule sC[OF inC])
      have pQi: "prob_space (Qi i)" for i by (rule pC[OF inC])
      have ev: "eventually (\<lambda>i. emeasure (Qi i)
          {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0) sequentially"
        by (rule etime_shift_box[OF T A dT wc sQi pQi pC[OF P] yconv posP])
      show "eventually (\<lambda>i. vshift T A (yi i) (Qi i) < d) sequentially"
      proof (rule eventually_mono[OF ev])
        fix i
        assume "emeasure (Qi i)
            {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0"
        thus "vshift T A (yi i) (Qi i) < d"
          unfolding vshift_less_iff_positive_mass[OF T A dT d0
              sC[OF inC] pC[OF inC]] .
      qed
    qed
  qed
qed

text \<open>
  The interface to Lemma 2.3, with exactly one obligation. Lemmas 2.2
  and 2.3 together say that \<open>\<P>\<^sub>0\<close> is sequentially compact for weak
  convergence: 2.2 extracts a convergent subsequence, 2.3 puts the limit
  back into the set --- the \<open>seq\<close> hypothesis below verbatim, and nothing
  else about \<open>\<P>\<^sub>0\<close> is used.
\<close>

abbreviation pairY :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> 'b"
  where "pairY t \<omega> \<equiv> snd (\<omega> t)"

section \<open>Laws on the capped path space\<close>

text \<open>Operational reading of (1.7), equivalent by compensator uniqueness: a
  law of \<open>(X, Y)\<close> where \<open>X\<close> is a martingale from \<open>x\<close>, \<open>Y\<close> starts at \<open>0\<close>
  with difference quotients in the constraint set (so \<open>Y\<close> is Lipschitz and
  a.e. differentiable into \<open>S\<close>), and \<open>X X\<^sup>T - Y\<close> is a martingale, making
  \<open>Y\<close> the quadratic covariation. The cap at \<open>T\<close> is invisible once \<open>T\<close>
  exceeds the uniform exit-time bound (Lemma 1.9 / Eq. (3.10)).

  The martingale clauses must stop the process at \<open>T\<close>: points of
  \<^term>\<open>mspace (path_metric T)\<close> are extensional on \<open>{0..T}\<close>, so an
  unstopped clause would force the coordinate process to be almost surely
  constant, emptying the class for every \<open>T > 0\<close>. Stopping at \<open>T\<close>
  captures exactly (1.7) on \<open>[0,T]\<close>.\<close>

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

text \<open>\<open>integrable_of_sq_integrable\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>

theorem qvmat_eq_A_localised:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" and A :: "real \<Rightarrow> 'a \<Rightarrow> real^'n^'n"
  assumes P: "prob_space M"
    and Xcomp: "\<And>i. martingale M F (0::real) (\<lambda>v \<omega>. X v \<omega> $ i)"
    and XAcomp: "\<And>i j. martingale M F (0::real)
                    (\<lambda>v \<omega>. X v \<omega> $ i * X v \<omega> $ j - A v \<omega> $ i $ j)"
    and contX: "\<And>\<omega> i. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega> $ i)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and Apsd: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
                  (\<forall>y. 0 \<le> y \<bullet> ((A q \<omega> - A p \<omega>) *v y))"
    and Arate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
                  \<bar>A q \<omega> $ i $ j - A p \<omega> $ i $ j\<bar> \<le> C * (q - p)"
    and C0: "0 \<le> C"
    and B0: "0 \<le> B" and X0: "\<And>\<omega> i. \<omega> \<in> space M \<Longrightarrow> \<bar>X 0 \<omega> $ i\<bar> \<le> B"
  shows "AE \<omega> in M.
     (\<forall>i j. qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j)
          \<and> qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j))
     \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
          qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2))"
proof -
  interpret P: prob_space M by (rule P)
  have pol: "AE \<omega> in M. qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + c * (X s \<omega> $ j))
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X s \<omega> $ i + c * (X s \<omega> $ j)) t
             = A t \<omega> $ i $ i + c * (A t \<omega> $ i $ j + A t \<omega> $ j $ i)
               + c\<^sup>2 * (A t \<omega> $ j $ j))"
    if c: "\<bar>c\<bar> \<le> 1" for c i j
  proof -
    define Y where "Y = (\<lambda>v \<omega>. X v \<omega> $ i + c * (X v \<omega> $ j))"
    define G where "G = (\<lambda>v \<omega>. A v \<omega> $ i $ i
        + c * (A v \<omega> $ i $ j + A v \<omega> $ j $ i) + c\<^sup>2 * (A v \<omega> $ j $ j))"
    have c2: "c\<^sup>2 \<le> 1" using sq_mono_abs[OF c] by simp

    have mgY: "martingale M F 0 Y"
    proof -
      have "martingale M F 0 (\<lambda>v \<omega>. X v \<omega> $ i + c *\<^sub>R (X v \<omega> $ j))"
        by (intro martingale.add[OF Xcomp] martingale.scaleR_const[OF Xcomp])
      then show ?thesis unfolding Y_def by simp
    qed
    have mgZ: "martingale M F 0 (\<lambda>v \<omega>. (Y v \<omega>)\<^sup>2 - G v \<omega>)"
    proof -
      have eq: "(\<lambda>v \<omega>. (Y v \<omega>)\<^sup>2 - G v \<omega>)
          = (\<lambda>v \<omega>. ((X v \<omega> $ i * X v \<omega> $ i - A v \<omega> $ i $ i)
                      + c *\<^sub>R (X v \<omega> $ i * X v \<omega> $ j - A v \<omega> $ i $ j))
                   + (c *\<^sub>R (X v \<omega> $ j * X v \<omega> $ i - A v \<omega> $ j $ i)
                      + c\<^sup>2 *\<^sub>R (X v \<omega> $ j * X v \<omega> $ j - A v \<omega> $ j $ j)))"
        unfolding Y_def G_def
        by (rule ext)+ (simp add: power2_eq_square algebra_simps)
      have m1: "martingale M F 0 (\<lambda>v \<omega>. X v \<omega> $ i * X v \<omega> $ i - A v \<omega> $ i $ i)"
        by (rule XAcomp)
      have m2: "martingale M F 0 (\<lambda>v \<omega>. c *\<^sub>R (X v \<omega> $ i * X v \<omega> $ j - A v \<omega> $ i $ j))"
        by (rule martingale.scaleR_const[OF XAcomp])
      have m3: "martingale M F 0 (\<lambda>v \<omega>. c *\<^sub>R (X v \<omega> $ j * X v \<omega> $ i - A v \<omega> $ j $ i))"
        by (rule martingale.scaleR_const[OF XAcomp])
      have m4: "martingale M F 0 (\<lambda>v \<omega>. c\<^sup>2 *\<^sub>R (X v \<omega> $ j * X v \<omega> $ j - A v \<omega> $ j $ j))"
        by (rule martingale.scaleR_const[OF XAcomp])
      show ?thesis unfolding eq
        by (rule martingale.add[OF martingale.add[OF m1 m2] martingale.add[OF m3 m4]])
    qed

    text \<open>The polarised compensator inherits monotonicity from positive
      semidefiniteness and the upper bound from the entrywise rate.\<close>
    have Grate: "\<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
        0 \<le> G v \<omega> - G u \<omega> \<and> G v \<omega> - G u \<omega> \<le> (4 * C) * (v - u)"
      if w: "\<omega> \<in> space M" for \<omega>
    proof (intro allI impI)
      fix u v :: real assume uv: "0 \<le> u" "u \<le> v"
      have diff: "G v \<omega> - G u \<omega>
          = (axis i 1 + c *\<^sub>R axis j 1) \<bullet> ((A v \<omega> - A u \<omega>) *v (axis i 1 + c *\<^sub>R axis j 1))"
      proof -
        have "(axis i 1 + c *\<^sub>R axis j 1)
                \<bullet> ((A v \<omega> - A u \<omega>) *v (axis i 1 + c *\<^sub>R axis j 1))
            = (A v \<omega> - A u \<omega>) $ i $ i
              + c * ((A v \<omega> - A u \<omega>) $ i $ j + (A v \<omega> - A u \<omega>) $ j $ i)
              + c\<^sup>2 * ((A v \<omega> - A u \<omega>) $ j $ j)"
          by (rule inner_mv_axis)
        then show ?thesis unfolding G_def by (simp add: algebra_simps)
      qed
      have nn: "0 \<le> G v \<omega> - G u \<omega>"
        unfolding diff using Apsd[OF w] uv by blast
      have e: "\<And>a b. \<bar>A v \<omega> $ a $ b - A u \<omega> $ a $ b\<bar> \<le> C * (v - u)"
        using Arate[OF w] uv by blast
      have "G v \<omega> - G u \<omega>
          = (A v \<omega> $ i $ i - A u \<omega> $ i $ i)
            + c * ((A v \<omega> $ i $ j - A u \<omega> $ i $ j) + (A v \<omega> $ j $ i - A u \<omega> $ j $ i))
            + c\<^sup>2 * (A v \<omega> $ j $ j - A u \<omega> $ j $ j)"
        unfolding G_def by (simp add: algebra_simps)
      also have "\<dots> \<le> C * (v - u) + 1 * (C * (v - u) + C * (v - u)) + 1 * (C * (v - u))"
      proof (intro add_mono)
        show "A v \<omega> $ i $ i - A u \<omega> $ i $ i \<le> C * (v - u)"
          using e by (simp add: abs_le_iff)
        have "c * ((A v \<omega> $ i $ j - A u \<omega> $ i $ j) + (A v \<omega> $ j $ i - A u \<omega> $ j $ i))
            \<le> \<bar>c\<bar> * \<bar>(A v \<omega> $ i $ j - A u \<omega> $ i $ j) + (A v \<omega> $ j $ i - A u \<omega> $ j $ i)\<bar>"
          by (simp add: abs_mult flip: abs_mult)
        also have "\<dots> \<le> 1 * (C * (v - u) + C * (v - u))"
          using c e[of i j] e[of j i] C0 uv
          by (intro mult_mono) (auto intro: order_trans[OF abs_triangle_ineq] add_mono)
        finally show "c * ((A v \<omega> $ i $ j - A u \<omega> $ i $ j)
                             + (A v \<omega> $ j $ i - A u \<omega> $ j $ i))
            \<le> 1 * (C * (v - u) + C * (v - u))" .
        have "0 \<le> A v \<omega> $ j $ j - A u \<omega> $ j $ j"
        proof -
          have ax: "axis j (1::real) \<bullet> ((A v \<omega> - A u \<omega>) *v axis j 1)
              = (A v \<omega> - A u \<omega>) $ j $ j"
            using inner_mv_axis[of j 0 j "A v \<omega> - A u \<omega>"] by simp
          have "0 \<le> axis j (1::real) \<bullet> ((A v \<omega> - A u \<omega>) *v axis j 1)"
            using Apsd[OF w] uv by blast
          then show ?thesis using ax by simp
        qed
        moreover have "A v \<omega> $ j $ j - A u \<omega> $ j $ j \<le> C * (v - u)"
          using e by (simp add: abs_le_iff)
        ultimately show "c\<^sup>2 * (A v \<omega> $ j $ j - A u \<omega> $ j $ j) \<le> 1 * (C * (v - u))"
          using c2 C0 uv by (intro mult_mono) auto
      qed
      also have "\<dots> = (4 * C) * (v - u)" by simp
      finally show "0 \<le> G v \<omega> - G u \<omega> \<and> G v \<omega> - G u \<omega> \<le> (4 * C) * (v - u)"
        using nn by simp
    qed

    text \<open>Square integrability, from the compensated square and the bound on
      \<open>G\<close> --- there is no uniform bound on \<open>Y\<close> to appeal to.\<close>
    have G0: "G 0 \<omega> = 0" if w: "\<omega> \<in> space M" for \<omega>
      unfolding G_def using A0[OF w] by simp
    have Gbnd: "\<bar>G s \<omega>\<bar> \<le> (4 * C) * s" if w: "\<omega> \<in> space M" and s: "0 \<le> s" for s \<omega>
      using Grate[OF w] s G0[OF w] by (metis order_refl abs_of_nonneg diff_zero)
    have Ymeas: "Y s \<in> borel_measurable M" if s: "0 \<le> s" for s
      by (rule borel_measurable_integrable[OF martingale.integrable[OF mgY s]])
    have Gmeas: "G s \<in> borel_measurable M" if s: "0 \<le> s" for s
    proof -
      have m: "(\<lambda>\<omega>. (Y s \<omega>)\<^sup>2 - G s \<omega>) \<in> borel_measurable M"
        by (rule borel_measurable_integrable[OF martingale.integrable[OF mgZ s]])
      have f1: "(\<lambda>\<omega>. (Y s \<omega>)\<^sup>2) \<in> borel_measurable M" using Ymeas[OF s] by simp
      have "(\<lambda>\<omega>. (Y s \<omega>)\<^sup>2 - ((Y s \<omega>)\<^sup>2 - G s \<omega>)) \<in> borel_measurable M"
        by (rule borel_measurable_diff[OF f1 m])
      moreover have "(\<lambda>\<omega>. (Y s \<omega>)\<^sup>2 - ((Y s \<omega>)\<^sup>2 - G s \<omega>)) = G s" by (rule ext) simp
      ultimately show ?thesis by simp
    qed
    have Gint: "integrable M (G s)" if s: "0 \<le> s" for s
    proof (rule P.integrable_const_bound[of _ "(4 * C) * s"])
      show "AE \<omega> in M. norm (G s \<omega>) \<le> (4 * C) * s"
        using Gbnd[OF _ s] by (intro AE_I2) simp
      show "G s \<in> borel_measurable M" by (rule Gmeas[OF s])
    qed
    have sqY: "integrable M (\<lambda>\<omega>. (Y s \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    proof -
      have "integrable M (\<lambda>\<omega>. ((Y s \<omega>)\<^sup>2 - G s \<omega>) + G s \<omega>)"
        by (intro Bochner_Integration.integrable_add
            martingale.integrable[OF mgZ s] Gint[OF s])
      then show ?thesis by simp
    qed
    have contY: "continuous_on {0..} (\<lambda>s. Y s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
      unfolding Y_def
      by (intro continuous_on_add continuous_on_mult_left contX[OF w])
    have Y0: "\<bar>Y 0 \<omega>\<bar> \<le> 2 * B" if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have "\<bar>Y 0 \<omega>\<bar> \<le> \<bar>X 0 \<omega> $ i\<bar> + \<bar>c * (X 0 \<omega> $ j)\<bar>"
        unfolding Y_def by (rule abs_triangle_ineq)
      also have "\<dots> = \<bar>X 0 \<omega> $ i\<bar> + \<bar>c\<bar> * \<bar>X 0 \<omega> $ j\<bar>" by (simp add: abs_mult)
      also have "\<dots> \<le> B + 1 * B"
        using X0[OF w] c B0 by (intro add_mono mult_mono) auto
      finally show ?thesis by simp
    qed
    have "AE \<omega> in M. qvp_good (4 * C) (\<lambda>s. Y s \<omega>)
        \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. Y s \<omega>) t = G t \<omega>)"
      by (rule qvps_eq_A_localised
            [OF P mgY sqY contY mgZ G0 Grate _ _ Y0]) (use C0 B0 in auto)
    then show ?thesis unfolding Y_def G_def .
  qed
  have c1: "\<bar>(1::real)\<bar> \<le> 1" by simp
  have cm1: "\<bar>(- 1::real)\<bar> \<le> 1" by simp
  have all1: "AE \<omega> in M. \<forall>i \<in> (UNIV :: 'n set). \<forall>j \<in> (UNIV :: 'n set).
      qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j) t
           = A t \<omega> $ i $ i + (A t \<omega> $ i $ j + A t \<omega> $ j $ i) + A t \<omega> $ j $ j)"
    by (intro AE_finite_allI; use pol[OF c1] in simp)
  have all2: "AE \<omega> in M. \<forall>i \<in> (UNIV :: 'n set). \<forall>j \<in> (UNIV :: 'n set).
      qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j)
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j) t
           = A t \<omega> $ i $ i + (- A t \<omega> $ i $ j - A t \<omega> $ j $ i) + A t \<omega> $ j $ j)"
    by (intro AE_finite_allI; use pol[OF cm1] in simp)
  from all1 all2 show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    have e1: "qvps (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j) t
        = A t \<omega> $ i $ i + (A t \<omega> $ i $ j + A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
      if "0 \<le> t" for i j t using elim(1) that by blast
    have e2: "qvps (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j) t
        = A t \<omega> $ i $ i + (- A t \<omega> $ i $ j - A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
      if "0 \<le> t" for i j t using elim(2) that by blast
    show ?case
    proof
      show "\<forall>i j. qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j)
          \<and> qvp_good (4 * C) (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j)"
        using elim(1) elim(2) by blast
    next
      show "\<forall>t. 0 \<le> t \<longrightarrow>
          qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2)"
      proof (intro allI impI)
        fix t :: real assume t: "0 \<le> t"
        have ent: "qvmat (\<lambda>s. X s \<omega>) t $ i $ j = (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2"
          for i j by (simp add: qvmat_def e1[OF t] e2[OF t])
        show "qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2)"
          by (simp add: vec_eq_iff ent)
      qed
    qed
  qed
qed

subsection \<open>The value functional of a family of laws\<close>

text \<open>
  Eq. (1.6)--(1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> as the paper states them: laws of
  the \<open>R\<^sup>n\<close>-valued path alone.  The covariation enters existentially, through a
  compensator \<open>A\<close> whose difference quotients lie in the constraint set --- which
  is what \<open>d\<langle>X\<rangle>(t)/dt \<in> S\<^sub>k\<^sup>L\<close> says once \<open>\<langle>X\<rangle>\<close> is read as the compensator of
  \<open>X X\<^sup>T\<close>.
\<close>

lemma space_of_path_sets:
  fixes Q :: "(('n::finite) pairpath) measure"
  assumes "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "space Q = mspace (path_metric T :: ('n pairpath) metric)"
  using sets_eq_imp_space_eq[OF assms] by (simp add: space_borel_of)

section \<open>The constraint passes to weak limits, without Skorokhod\<close>

text \<open>The paper passes the covariation constraint to the limit law via
  Skorokhod's representation theorem; this instead uses the closed-set half
  of the portmanteau theorem (\<open>weak_conv_closed_full_mass\<close>). For fixed
  times \<open>s < t\<close> the difference quotient is a continuous function of the
  path and the constraint set is closed, so
  \<open>{\<omega>. (Y t \<omega> - Y s \<omega>)/(t - s) \<in> S}\<close> is closed and has full mass under
  every approximating law, hence under the limit.\<close>

lemma restrict_measurable_natural_filtration:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>\<omega>. restrict \<omega> {0..s})
      \<in> natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s
        \<rightarrow>\<^sub>M (path_borel s :: ('n pairpath) measure)"
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
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and s: "0 \<le> s" and sT: "s \<le> T"
    and h: "h \<in> borel_measurable (path_borel s :: ('n pairpath) measure)"
  shows "(\<lambda>\<omega>. h (restrict \<omega> {0..s}))
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)"
  by (rule measurable_compose
      [OF restrict_measurable_natural_filtration[OF setsQ s sT] h])

subsection \<open>The identity at a law, against a bounded test\<close>

lemma pair_law_coord_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. fst (\<omega> u) $ i) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) $ i)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_coord_cont[OF u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF setsN refl] by blast
qed

lemma continuous_on_pglue:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'a::real_normed_vector \<times> 'b::real_normed_vector)"
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

lemma continuous_map_diffquot:
  fixes s t :: real
  assumes s: "s \<in> {0..T}" and t: "t \<in> {0..T}"
  shows "continuous_map (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
      euclidean (\<lambda>\<omega>. (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)))"
proof -
  have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> t)"
    by (rule continuous_map_path_eval[OF t])
  moreover have "continuous_map (mtopology_of (path_metric T :: ('n pairpath) metric))
      euclidean (\<lambda>\<omega>. \<omega> s)"
    by (rule continuous_map_path_eval[OF s])
  moreover have sndc:
    "continuous_map euclidean euclidean
       (snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)"
    by (simp add: continuous_on_snd)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s))"
    by (intro continuous_map_diff)
      (auto intro: continuous_map_compose[OF _ sndc, unfolded o_def])
  moreover have scl: "continuous_map euclidean euclidean
      (\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)"
    by (simp add:
        continuous_on_scaleR)
  ultimately have "continuous_map
      (mtopology_of (path_metric T :: ('n pairpath) metric)) euclidean
      ((\<lambda>v :: real^'n^'n. (1 / (t - s)) *\<^sub>R v)
        \<circ> (\<lambda>\<omega>. snd (\<omega> t) - snd (\<omega> s)))"
    by (intro continuous_map_compose)
  then show ?thesis by (simp add: o_def)
qed

lemma pair_law_coord_sq_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and u: "u \<in> {0..T}"
  shows "(\<lambda>\<omega>. (fst (\<omega> u) $ i)\<^sup>2) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> u) $ i)\<^sup>2)
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable[OF pair_eval_coord_sq_cont[OF u]]
    by (simp add: borel_of_euclidean)
  then show ?thesis
    using measurable_cong_sets[OF setsN refl] by blast
qed

lemma ess_inf_time_min_const:
  fixes c :: real
  assumes M: "prob_space M"
  shows "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) = min (ess_inf_time M g) (ennreal c)"
proof (rule order.antisym)
  show "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) \<le> min (ess_inf_time M g) (ennreal c)"
  proof (intro min.boundedI)
    show "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) \<le> ess_inf_time M g"
      by (rule ess_inf_time_mono) simp
    show "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) \<le> ennreal c"
      by (rule ess_inf_time_le_const[OF M]) simp
  qed
  show "min (ess_inf_time M g) (ennreal c) \<le> ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)"
  proof (rule ccontr)
    assume "\<not> min (ess_inf_time M g) (ennreal c)
        \<le> ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)"
    then have "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)
        < min (ess_inf_time M g) (ennreal c)" by (rule not_le_imp_less)
    then obtain b where b1: "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) < b"
      and b2: "b < min (ess_inf_time M g) (ennreal c)"
      using ennreal_strict_between by blast
    from b2 have bg: "b < ess_inf_time M g"
      by (rule order.strict_trans2[OF _ min.cobounded1])
    from b2 have bc: "b < ennreal c"
      by (rule order.strict_trans2[OF _ min.cobounded2])
    from bg have "b < Sup {e. AE \<omega> in M. e \<le> ennreal (g \<omega>)}"
      unfolding ess_inf_time_def .
    then obtain e where eA: "e \<in> {e. AE \<omega> in M. e \<le> ennreal (g \<omega>)}"
      and be: "b < e" by (auto simp: less_Sup_iff)
    from eA have e: "AE \<omega> in M. e \<le> ennreal (g \<omega>)" by simp
    then have "AE \<omega> in M. b \<le> ennreal (min (g \<omega>) c)"
    proof (rule eventually_mono)
      fix \<omega> assume "e \<le> ennreal (g \<omega>)"
      with be have "b \<le> ennreal (g \<omega>)" by simp
      with bc have "b \<le> min (ennreal (g \<omega>)) (ennreal c)" by simp
      then show "b \<le> ennreal (min (g \<omega>) c)" by (simp add: ennreal_min_eq)
    qed
    then have "b \<le> ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)"
      unfolding ess_inf_time_def by (intro Sup_upper) simp
    with b1 show False by simp
  qed
qed

text \<open>The value function at a shorter horizon is the value function at the
  longer one, capped.  The \<open>\<le>\<close> half is \<open>exit_val_horizon_mono\<close>
  together with \<open>exit_val_le_T\<close>; the \<open>\<ge>\<close> half cuts a
  competitor at the longer horizon back to the shorter one
  (\<open>exit_class_pcut\<close>), where the two lemmas above turn
  its value into the capped value.  No pasting is needed in either
  direction --- the pasting is already inside
  \<open>exit_val_horizon_mono\<close>.\<close>

lemma pair_law_sq_integrable_of_nn_bound:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
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
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
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

text \<open>\<open>bounded_measurable_integrable\<close>, \<open>clamp_integrable\<close>, \<open>tail_indicator_measurable\<close>, \<open>tail_integrable\<close> live in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


subsection \<open>The test functional under a pair law with an \<open>L\<^sup>2\<close> bound\<close>

corollary vshift_sup_usc_of_seq_compact:
  fixes T c :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and C :: "(real \<Rightarrow> 'b) measure set" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and neC: "C \<noteq> {}"
    and sC: "\<And>Q. Q \<in> C \<Longrightarrow> sets Q = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pC: "\<And>Q. Q \<in> C \<Longrightarrow> prob_space Q"
    and seq: "\<And>\<sigma> :: nat \<Rightarrow> (real \<Rightarrow> 'b) measure. range \<sigma> \<subseteq> C \<Longrightarrow>
        \<exists>L r. L \<in> C \<and> strict_mono r \<and> weak_conv_on (\<sigma> \<circ> r) L sequentially
              (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and lt: "Sup (vshift T A x ` C) < c"
  shows "eventually (\<lambda>y. Sup (vshift T A y ` C) < c) (nhds x)"
proof -
  have sub: "C \<subseteq> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
  proof
    fix Q assume Q: "Q \<in> C"
    show "Q \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      using sC[OF Q] prob_space.finite_measure[OF pC[OF Q]] by simp
  qed
  have cC: "compactin (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    by (rule compactin_of_seq_compact[OF metrizable_weak_conv_path_topology sub])
       (use seq in blast)
  show ?thesis by (rule vshift_sup_usc[OF T A cC neC sC pC lt])
qed

subsection \<open>From a market to its law: transferring the exit time\<close>

text \<open>
  \<open>vshift\<close> speaks about laws on the path space, while
  \<open>Value_Function_Market.val_fn\<close> is a supremum over markets --- a measure,
  filtration, process and covariation. \<open>Path_Space.path_law\<close> bridges the
  two, and these lemmas carry the essential infimum of the exit time
  across it, connecting the semicontinuity results above to \<open>\<P>\<^sub>x\<close>.
\<close>

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

lemma outerp_diff:
  fixes a b :: "real^'n::finite"
  shows "outerp (a - b) = outerp a - ((\<chi> i j. a $ i * b $ j)
      + (\<chi> i j. b $ i * a $ j)) + outerp b"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma pair_test_measurable:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
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
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M borel"
    using continuous_map_measurable
      [OF pair_test_functional_cont[OF st sT tI hc, of i]]
    by (simp add: borel_of_euclidean)
  then show ?thesis using measurable_cong_sets[OF setsN refl] by blast
qed

lemma outerp_diff_compensated:
  fixes a b :: "real^'n::finite" and Ya Yb :: "real^'n^'n"
  shows "outerp (a - b) - (Ya - Yb)
      = (outerp a - Ya) - ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
        + (outerp b + Yb)"
  by (simp add: outerp_diff)

text \<open>The martingale-level form of "pulling out what is known": the AFP's
  conditional-expectation lemma \<open>cond_exp_measurable_mult\<close> feeds the
  cross term of @{thm [source] outerp_diff_compensated}.  The factor must be
  measurable for the filtration at the initial time, not merely somewhere
  along it, or it is not adapted.  \<open>martingale_mult_measurable\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>\<open>integrable_mult_of_sq\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


text \<open>\<open>martingale_cross_measurable\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>\<open>martingale_diff\<close>, the subtractive companion to \<open>martingale_add\<close>,
  lives in @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

subsection \<open>The shifted processes of a law\<close>

text \<open>\<open>pair_snd_borel\<close> lives in \<open>Exit_Class_Pasting\<close>.\<close>

lemma etime_shift_of_restrict:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{polish_space,real_normed_vector}" and y :: 'b
  shows "etime T A (\<lambda>s w. y + w s) (restrict (\<lambda>t. X t \<omega>) {0..T})
       = etime T A (\<lambda>s \<omega>'. y + X s \<omega>') \<omega>"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> y + restrict (\<lambda>t. X t \<omega>) {0..T} r \<in> A}
      = {r. 0 \<le> r \<and> r \<le> T \<and> y + X r \<omega> \<in> A}"
    by (auto simp: restrict_def)
  thus ?thesis unfolding etime_def by simp
qed

lemma pair_test_sq_bound:
  fixes N :: "('n::finite pairpath) measure" and h :: "('n pairpath) \<Rightarrow> real"
  assumes P: "prob_space N"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
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
    \<comment> \<open>\<open>2(a²+b²) - (a-b)² = (a+b)² \<ge> 0\<close>: stated as an EQUATION between
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

theorem vshift_path_law:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{polish_space,real_normed_vector}" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and Xm: "\<And>t. t \<in> {0..T} \<Longrightarrow> X t \<in> borel_measurable M"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..T} (\<lambda>t. X t \<omega>)"
  shows "vshift T A y (path_law M X T)
       = enn2real (ess_inf_time M (etime T A (\<lambda>s \<omega>'. y + X s \<omega>')))"
proof -
  have pm: "(\<lambda>\<omega>. restrict (\<lambda>t. X t \<omega>) {0..T})
      \<in> M \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'b) measure)"
    by (rule pathify_measurable[OF T Xm cont])
  have meas: "{\<omega> \<in> space (path_borel T :: (real \<Rightarrow> 'b) measure).
        c \<le> ennreal (etime T A (\<lambda>s w. y + w s) \<omega>)}
      \<in> sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    for c :: ennreal
    using borel_of_closed[OF etime_shift_superlevel_closed[OF T A, of c y]]
    by (simp add: space_borel_of)
  have "ess_inf_time (path_law M X T) (etime T A (\<lambda>s w. y + w s))
      = ess_inf_time M
          (\<lambda>\<omega>. etime T A (\<lambda>s w. y + w s) (restrict (\<lambda>t. X t \<omega>) {0..T}))"
    unfolding path_law_def by (rule ess_inf_time_distr[OF pm meas])
  also have "\<dots> = ess_inf_time M (etime T A (\<lambda>s \<omega>'. y + X s \<omega>'))"
    by (simp add: etime_shift_of_restrict)
  finally show ?thesis unfolding vshift_def by simp
qed

(*<*)
end
(*>*)
