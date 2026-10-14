section \<open>Localization: stopping an \<open>L\<^sup>2\<close> martingale needs no domination hypothesis\<close>

(*<*)
theory Stopped_Localization
  imports
    Increment_Moments "Continuous_Time_Martingales.Doob_Inequality"
    "Continuous_Time_Martingales.Martingale_Transfer"
    "Continuous_Time_Martingales.Optional_Sampling"
    "Continuous_Time_Martingales.Stopped_Adaptedness"
    "Continuous_Time_Martingales.Stopping_Times"
begin

(*>*)

text \<open>
  The repository's continuous-time \<open>optional_stopping\<close>
  (@{theory Continuous_Time_Martingales.Optional_Sampling}) carries an integrable running-domination
  hypothesis. For an \<open>L\<^sup>2\<close> martingale that hypothesis is dischargeable: the
  \<open>horizon_sq_int_martingale\<close> locale of @{theory Continuous_Time_Martingales.Doob_Inequality} produces, per
  horizon, an integrable function \<open>Dsup\<close> dominating \<open>\<bar>X s\<bar>\<close> on the whole
  interval (Doob's \<open>L\<^sup>2\<close> inequality along dyadic grids + monotone
  convergence + path continuity). This theory packages that discharge:
  stopping an \<open>L\<^sup>2\<close> martingale with continuous paths at any stopping time
  yields a martingale, unconditionally.

  First the two ingredients: \<open>optional_stopping\<close> for a process with
  continuous paths on \<open>{0..}\<close> and some integrable envelope per horizon, and
  the envelope of an \<open>L\<^sup>2\<close> martingale, square-integrable as well.
\<close>

lemma optional_stopping_cont:
  fixes Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Z"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. Z s \<omega>)"
    and dom: "\<And>u. 0 < u \<Longrightarrow> \<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D \<omega>)
                \<and> integrable M D"
  shows "martingale M F 0 (\<lambda>v \<omega>. Z (min v (tau \<omega>)) \<omega>)"
proof -
  have "\<exists>D. \<forall>u. 0 < u \<longrightarrow> (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D u \<omega>)
      \<and> integrable M (D u)"
    using dom by (intro choice) blast
  then obtain D where D: "\<And>u. 0 < u \<Longrightarrow> (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D u \<omega>)
      \<and> integrable M (D u)"
    by blast
  show ?thesis
  proof (rule optional_stopping[OF mg tau_nonneg tau_stop _ conjunct1[OF D] conjunct2[OF D]])
    show "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. Z s \<omega>)" for u
      by (intro AE_I2 continuous_on_subset[OF cont]) auto
    show "(\<lambda>\<omega>. Z (min v (tau \<omega>)) \<omega>) \<in> borel_measurable (F v)" if "0 \<le> v" for v
      by (rule stopped_adapted_of_cont[OF martingale.axioms(2)[OF mg]
            tau_nonneg tau_stop cont that])
  qed
qed

lemma L2_martingale_envelope:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mg: "martingale M F (0::real) X"
    and sq: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and u: "0 < u"
  shows "\<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D \<omega>)
      \<and> integrable M D \<and> integrable M (\<lambda>\<omega>. (D \<omega>)\<^sup>2)"
proof -
  interpret H: horizon_sq_int_martingale M F X u
    by (intro horizon_sq_int_martingale.intro[OF mg]
        horizon_sq_int_martingale_axioms.intro u P sq)
  have "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. X s \<omega>)"
    by (intro AE_I2 continuous_on_subset[OF cont]) auto
  then show ?thesis
    by (intro exI[of _ H.Dsup] conjI H.Dsup_dominates H.Dsup_integrable
        H.Dsup_sq_integrable)
qed

text \<open>The stopped process stays square-integrable: on \<open>[0,s]\<close> it is
  dominated by the envelope at horizon \<open>s + 1\<close>.\<close>

lemma stopped_L2_sq_integrable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mg: "martingale M F (0::real) X"
    and sq: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and s: "0 \<le> s"
  shows "integrable M (\<lambda>\<omega>. (X (min s (tau \<omega>)) \<omega>)\<^sup>2)"
proof -
  interpret MX: martingale M F "0::real" X by (rule mg)
  obtain D where D: "AE \<omega> in M. \<forall>v. 0 \<le> v \<longrightarrow> v \<le> s + 1 \<longrightarrow> \<bar>X v \<omega>\<bar> \<le> D \<omega>"
    and D2: "integrable M (\<lambda>\<omega>. (D \<omega>)\<^sup>2)"
    using L2_martingale_envelope[OF P mg sq cont, of "s + 1"] s by auto
  have "(\<lambda>\<omega>. X (min s (tau \<omega>)) \<omega>) \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF MX.subalgebras[OF s]
          stopped_adapted_of_cont[OF martingale.axioms(2)[OF mg] tau_nonneg tau_stop cont s]])
  moreover have "AE \<omega> in M. norm ((X (min s (tau \<omega>)) \<omega>)\<^sup>2) \<le> norm ((D \<omega>)\<^sup>2)"
    using D AE_space
  proof eventually_elim
    case (elim \<omega>)
    then have "\<bar>X (min s (tau \<omega>)) \<omega>\<bar> \<le> D \<omega>" using s tau_nonneg by simp
    then have "\<bar>X (min s (tau \<omega>)) \<omega>\<bar>\<^sup>2 \<le> (D \<omega>)\<^sup>2" by (intro power_mono) auto
    then show ?case by simp
  qed
  ultimately show ?thesis
    by (intro Bochner_Integration.integrable_bound[OF D2]) measurable
qed

theorem stopped_martingale_L2:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mg: "martingale M F (0::real) X"
    and sq: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
  shows "martingale M F 0 (\<lambda>v \<omega>. X (min v (tau \<omega>)) \<omega>)"
proof (rule optional_stopping_cont[OF mg tau_nonneg tau_stop cont])
  fix u :: real assume u: "0 < u"
  then obtain D where "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D \<omega>"
    and "integrable M D"
    using L2_martingale_envelope[OF P mg sq cont u] by blast
  then show "\<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D \<omega>)
      \<and> integrable M D" by blast
qed

section \<open>Stopping the compensated square\<close>

text \<open>
  A compensator with a rate \<open>0 \<le> A v - A u \<le> C (v - u)\<close> is \<open>C\<close>-Lipschitz,
  hence continuous; stopped, it is bounded by \<open>C s\<close> at time \<open>s\<close>, hence
  integrable.
\<close>

lemma rate_continuous_on:
  fixes f :: "real \<Rightarrow> real"
  assumes C0: "0 \<le> C"
    and rate: "\<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow> 0 \<le> f v - f u \<and> f v - f u \<le> C * (v - u)"
  shows "continuous_on {0..} f"
proof -
  have "C-lipschitz_on {0..} f"
  proof (rule lipschitz_onI)
    show "0 \<le> C" by (rule C0)
    fix x y :: real assume x: "x \<in> {0..}" and y: "y \<in> {0..}"
    show "dist (f x) (f y) \<le> C * dist x y"
    proof (cases "x \<le> y")
      case True
      with rate[rule_format, of x y] x show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff)
    next
      case False
      with rate[rule_format, of y x] y show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff)
    qed
  qed
  thus ?thesis by (rule lipschitz_on_continuous_on)
qed

lemma stopped_compensator_integrable:
  fixes A :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real" and C :: real
  assumes P: "prob_space M"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and meas: "(\<lambda>\<omega>. A (min s (tau \<omega>)) \<omega>) \<in> borel_measurable M"
    and s: "0 \<le> s"
  shows "integrable M (\<lambda>\<omega>. A (min s (tau \<omega>)) \<omega>)"
proof (rule Bochner_Integration.integrable_bound
    [OF finite_measure.integrable_const[OF prob_space.finite_measure[OF P], of "C * s"]
      meas AE_I2])
  fix \<omega> assume w: "\<omega> \<in> space M"
  have "0 \<le> A (min s (tau \<omega>)) \<omega> \<and> A (min s (tau \<omega>)) \<omega> \<le> C * min s (tau \<omega>)"
    using A_rate[OF w, rule_format, of 0 "min s (tau \<omega>)"] s tau_nonneg[OF w] A0[OF w]
    by simp
  moreover have "C * min s (tau \<omega>) \<le> C * s"
    using C0 s by (intro mult_left_mono) simp_all
  ultimately show "norm (A (min s (tau \<omega>)) \<omega>) \<le> norm (C * s)"
    using C0 s by simp
qed

text \<open>
  The compensated square \<open>Z = X\<^sup>2 - A\<close> of an \<open>L\<^sup>2\<close> martingale with a
  Lipschitz-rate compensator is generally not \<open>L\<^sup>2\<close>, so
  @{thm [source] stopped_martingale_L2} does not apply to it directly. But it
  is dominated on \<open>[0,u]\<close>: \<open>\<bar>Z s\<bar> \<le> D\<^sup>2 + C u\<close> where \<open>D\<close> is the
  envelope of @{thm [source] L2_martingale_envelope}, whose square is
  integrable by Doob's \<open>L\<^sup>2\<close> inequality. So the domination hypothesis of
  \<open>optional_stopping\<close> is again dischargeable. Stopping \<open>Z\<close> is what transfers
  the covariation package to the stopped process: the martingale property of
  \<open>Z\<^sup>\<tau>\<close> is the statement that \<open>A(\<cdot> \<and> \<tau>)\<close> compensates \<open>(X\<^sup>\<tau>)\<^sup>2\<close>.
\<close>

theorem stopped_compensated_square:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real" and C :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
  shows "martingale M F 0
      (\<lambda>v \<omega>. (X (min v (tau \<omega>)) \<omega>)\<^sup>2 - A (min v (tau \<omega>)) \<omega>)"
proof (rule optional_stopping_cont[OF mgZ tau_nonneg tau_stop])
  show "continuous_on {0..} (\<lambda>s. (X s \<omega>)\<^sup>2 - A s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
    by (intro continuous_on_diff continuous_on_power contX[OF w]
        rate_continuous_on[OF C0 A_rate[OF w]])
  fix u :: real assume u: "0 < u"
  obtain D where D: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D \<omega>"
    and D2: "integrable M (\<lambda>\<omega>. (D \<omega>)\<^sup>2)"
    using L2_martingale_envelope[OF P mgX sqX contX u] by blast
  have "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>(X s \<omega>)\<^sup>2 - A s \<omega>\<bar> \<le> (D \<omega>)\<^sup>2 + C * u"
    using D AE_space
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s" and su: "s \<le> u"
      have "\<bar>X s \<omega>\<bar>\<^sup>2 \<le> (D \<omega>)\<^sup>2" using elim s su by (intro power_mono) auto
      then have x2: "(X s \<omega>)\<^sup>2 \<le> (D \<omega>)\<^sup>2" by simp
      have a: "0 \<le> A s \<omega>" "A s \<omega> \<le> C * s"
        using A_rate[OF elim(2), rule_format, of 0 s] s A0[OF elim(2)] by simp_all
      have cu: "C * s \<le> C * u" using su C0 by (intro mult_left_mono)
      have x0: "0 \<le> (X s \<omega>)\<^sup>2" by simp
      show "\<bar>(X s \<omega>)\<^sup>2 - A s \<omega>\<bar> \<le> (D \<omega>)\<^sup>2 + C * u"
      proof (rule abs_leI)
        show "(X s \<omega>)\<^sup>2 - A s \<omega> \<le> (D \<omega>)\<^sup>2 + C * u" using x2 a cu by linarith
        show "- ((X s \<omega>)\<^sup>2 - A s \<omega>) \<le> (D \<omega>)\<^sup>2 + C * u" using x2 a cu x0 by linarith
      qed
    qed
  qed
  moreover have "integrable M (\<lambda>\<omega>. (D \<omega>)\<^sup>2 + C * u)"
    by (rule Bochner_Integration.integrable_add[OF D2
          finite_measure.integrable_const[OF prob_space.finite_measure[OF P]]])
  ultimately show "\<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>(X s \<omega>)\<^sup>2 - A s \<omega>\<bar> \<le> D \<omega>)
      \<and> integrable M D"
    by (intro exI[of _ "\<lambda>\<omega>. (D \<omega>)\<^sup>2 + C * u"] conjI)
qed

section \<open>The covariation package transfers to the stopped process\<close>

text \<open>
  The martingale property of the stopped compensated square, rewritten as the
  conditional covariation identity for the stopped process: this is what feeds
  \<open>fourth_moment_bound_bounded\<close> at compensator \<open>A(\<cdot> \<and> \<tau>)\<close>.  It is
  \<open>compensator_cond_increment\<close> for the stopped pair, whose two martingale
  properties are @{thm [source] stopped_martingale_L2} and
  @{thm [source] stopped_compensated_square}; the stopped compensator is adapted
  because it is a compensator (\<open>compensator_adapted\<close>), so no adaptedness of
  \<open>A\<close> is assumed.
\<close>

theorem stopped_covariation:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real" and C :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and uv: "0 \<le> u" "u \<le> v"
  shows "AE \<omega> in M.
      cond_exp M (F u) (\<lambda>\<omega>. (X (min v (tau \<omega>)) \<omega> - X (min u (tau \<omega>)) \<omega>)\<^sup>2) \<omega>
    = cond_exp M (F u) (\<lambda>\<omega>. A (min v (tau \<omega>)) \<omega> - A (min u (tau \<omega>)) \<omega>) \<omega>"
proof -
  interpret MX: martingale M F "0::real" X by (rule mgX)
  let ?XS = "\<lambda>t \<omega>. X (min t (tau \<omega>)) \<omega>"
  let ?AS = "\<lambda>t \<omega>. A (min t (tau \<omega>)) \<omega>"
  have mgXS: "martingale M F 0 ?XS"
    by (rule stopped_martingale_L2[OF P mgX sqX contX tau_nonneg tau_stop])
  have mgZS: "martingale M F 0 (\<lambda>t \<omega>. (?XS t \<omega>)\<^sup>2 - ?AS t \<omega>)"
    by (rule stopped_compensated_square[OF P mgX sqX contX mgZ A0 A_rate C0
          tau_nonneg tau_stop])
  have iAS: "integrable M (?AS s)" if s: "0 \<le> s" for s
    by (rule stopped_compensator_integrable[OF P A0 A_rate C0 tau_nonneg
          measurable_from_subalg[OF MX.subalgebras[OF s]
            adapted_process.adapted[OF compensator_adapted[OF mgXS mgZS] s]] s])
  show ?thesis
    by (rule compensator_cond_increment[OF mgXS mgZS
          stopped_L2_sq_integrable[OF P mgX sqX contX tau_nonneg tau_stop] iAS uv])
qed

section \<open>Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> for unbounded \<open>L\<^sup>2\<close> martingales, by localization and Fatou\<close>

lemma etime_eq_T_of_no_hit:
  assumes T: "0 \<le> T" and nh: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> X s \<omega> \<notin> A"
  shows "etime T A X \<omega> = T"
proof -
  have e: "{s. 0 \<le> s \<and> s \<le> T \<and> X s \<omega> \<in> A} = {}" using nh by auto
  show ?thesis unfolding etime_def e by simp
qed

text \<open>
  The paper's Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> with constant \<open>8 C\<^sup>2\<close> for an unbounded \<open>L\<^sup>2\<close>
  martingale with an almost surely bounded start, \<open>\<bar>X\<^sub>0\<bar> \<le> B\<close>, and a
  Lipschitz-rate compensator for its square (adapted, being a compensator:
  \<open>compensator_adapted\<close>). Localize at the exit times of the balls of radius
  \<open>\<bar>B\<bar> + n + 1\<close>, apply the bounded estimate to each stopped process --- its
  martingale property, covariation package and boundedness come from the
  three theorems above and the exit-time theory --- and pass to the limit by
  Fatou: continuous paths are bounded on compact intervals, so for every
  \<open>\<omega>\<close> the stopped increments are eventually equal to the plain ones.
\<close>

theorem fourth_moment_L2:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and C B :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and start: "AE \<omega> in M. \<bar>X 0 \<omega>\<bar> \<le> B"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and uv: "0 \<le> u" "u \<le> v"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M) \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule mgX)
  have Aad: "adapted_process M F (0::real) A" by (rule compensator_adapted[OF mgX mgZ])
  have v0: "0 \<le> v" using uv by linarith
  define r where "r = (\<lambda>n::nat. \<bar>B\<bar> + real n + 1)"
  have r_gt: "\<bar>B\<bar> < r n" for n unfolding r_def by simp
  have r_pos: "0 < r n" for n unfolding r_def by simp
  define tau where "tau = (\<lambda>n \<omega>. etime v {y::real. r n \<le> norm y} X \<omega>)"
  have closedA: "closed {y::real. r n \<le> norm y}" for n
    by (intro closed_Collect_le continuous_on_const continuous_on_norm
        continuous_on_id)
  have neA: "{y::real. r n \<le> norm y} \<noteq> {}" for n
  proof -
    have "r n \<in> {y::real. r n \<le> norm y}" using r_pos[of n] by simp
    thus ?thesis by blast
  qed
  have contXv: "continuous_on {0..v} (\<lambda>s. X s \<omega>)" if "\<omega> \<in> space M" for \<omega>
    by (rule continuous_on_subset[OF contX[OF that]]) auto
  have CA: "cont_adapted_process M F X v"
    by (intro cont_adapted_process.intro martingale.axioms(2)[OF mgX]
        cont_adapted_process_axioms.intro v0 contXv)
  have tau_nn: "0 \<le> tau n \<omega>" for n \<omega>
    unfolding tau_def by (rule etime_nonneg[OF v0])
  have tau_le: "tau n \<omega> \<le> v" for n \<omega>
    unfolding tau_def by (rule etime_le_T[OF v0])
  have tau_stop: "{\<omega> \<in> space M. tau n \<omega> \<le> s} \<in> sets (F s)" if s: "0 \<le> s" for n s
    unfolding tau_def
    by (rule cont_adapted_process.etime_stopping_time[OF CA closedA neA s])
  have tau_nn': "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau n \<omega>" for n by (rule tau_nn)
  let ?XS = "\<lambda>n t \<omega>. X (min t (tau n \<omega>)) \<omega>"
  let ?AS = "\<lambda>n t \<omega>. A (min t (tau n \<omega>)) \<omega>"
  have bndS: "AE \<omega> in M. \<bar>?XS n s \<omega>\<bar> \<le> r n" if s: "0 \<le> s" for n s
    using start AE_space
  proof eventually_elim
    case (elim \<omega>)
    then have w: "\<omega> \<in> space M" by simp
    have m0: "0 \<le> min s (tau n \<omega>)" using s tau_nn by simp
    have st: "norm (X 0 \<omega>) < r n" using elim(1) r_gt[of n] by simp
    have sle: "min s (tau n \<omega>) \<le> etime v {y. r n \<le> norm y} X \<omega>"
      unfolding tau_def by simp
    have "X (min s (tau n \<omega>)) \<omega> \<in> cball 0 (r n)"
      by (rule etime_stays_in_cball[OF v0 r_pos st contXv[OF w] m0 sle])
    thus ?case by simp
  qed
  have contA: "continuous_on {0..} (\<lambda>s. A s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
    by (rule rate_continuous_on[OF C0 A_rate[OF w]])
  have ASad: "?AS n s \<in> borel_measurable (F s)" if "0 \<le> s" for n s
    by (rule stopped_adapted_of_cont[OF Aad tau_nn' tau_stop contA that])
  have ASm: "?AS n s \<in> borel_measurable M" if "0 \<le> s" for n s
    by (rule measurable_from_subalg[OF MX.subalgebras[OF that] ASad[OF that]])
  have XSad: "?XS n s \<in> borel_measurable (F s)" if "0 \<le> s" for n s
    by (rule stopped_adapted_of_cont[OF martingale.axioms(2)[OF mgX]
          tau_nn' tau_stop contX that])
  have XSm: "?XS n s \<in> borel_measurable M" if "0 \<le> s" for n s
    by (rule measurable_from_subalg[OF MX.subalgebras[OF that] XSad[OF that]])
  have A_intS: "integrable M (?AS n s)" if s: "0 \<le> s" for n s
    by (rule stopped_compensator_integrable[OF P A0 A_rate C0 tau_nn' ASm[OF s] s])
  have A_rateS: "AE \<omega> in M. \<forall>u' v'. 0 \<le> u' \<longrightarrow> u' \<le> v' \<longrightarrow>
      0 \<le> ?AS n v' \<omega> - ?AS n u' \<omega> \<and> ?AS n v' \<omega> - ?AS n u' \<omega> \<le> C * (v' - u')"
    for n
  proof (intro AE_I2 allI impI)
    fix \<omega> and u' v' :: real
    assume w: "\<omega> \<in> space M" and u': "0 \<le> u'" and u'v': "u' \<le> v'"
    have m0: "0 \<le> min u' (tau n \<omega>)" using u' tau_nn by simp
    have mm: "min u' (tau n \<omega>) \<le> min v' (tau n \<omega>)" using u'v' by simp
    have md: "min v' (tau n \<omega>) - min u' (tau n \<omega>) \<le> v' - u'"
      using u'v' by (simp add: min_def)
    from A_rate[OF w, rule_format, OF m0 mm]
    have "0 \<le> ?AS n v' \<omega> - ?AS n u' \<omega>"
      and "?AS n v' \<omega> - ?AS n u' \<omega> \<le> C * (min v' (tau n \<omega>) - min u' (tau n \<omega>))"
      by simp_all
    moreover have "C * (min v' (tau n \<omega>) - min u' (tau n \<omega>)) \<le> C * (v' - u')"
      using C0 md by (intro mult_left_mono)
    ultimately show "0 \<le> ?AS n v' \<omega> - ?AS n u' \<omega>
        \<and> ?AS n v' \<omega> - ?AS n u' \<omega> \<le> C * (v' - u')" by linarith
  qed
  have contS: "AE \<omega> in M. continuous_on {u..v} (\<lambda>t. ?XS n t \<omega>)" for n
  proof (intro AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have "continuous_on {u..v} ((\<lambda>s. X s \<omega>) \<circ> (\<lambda>t. min t (tau n \<omega>)))"
    proof (rule continuous_on_compose)
      show "continuous_on {u..v} (\<lambda>t. min t (tau n \<omega>))"
        by (intro continuous_on_min continuous_on_id continuous_on_const)
      show "continuous_on ((\<lambda>t. min t (tau n \<omega>)) ` {u..v}) (\<lambda>s. X s \<omega>)"
        by (rule continuous_on_subset[OF contX[OF w]])
           (use uv tau_nn in \<open>auto simp: min_def\<close>)
    qed
    thus "continuous_on {u..v} (\<lambda>t. ?XS n t \<omega>)" by (simp add: o_def)
  qed
  have mgXS: "martingale M F 0 (?XS n)" for n
    by (rule stopped_martingale_L2[OF P mgX sqX contX tau_nn' tau_stop])
  have covAS: "AE \<omega> in M. cond_exp M (F u') (\<lambda>\<omega>. (?XS n v' \<omega> - ?XS n u' \<omega>)\<^sup>2) \<omega>
      = cond_exp M (F u') (\<lambda>\<omega>. ?AS n v' \<omega> - ?AS n u' \<omega>) \<omega>"
    if "0 \<le> u'" "u' \<le> v'" for n u' v'
    by (rule stopped_covariation[OF P mgX sqX contX mgZ A0 A_rate C0
          tau_nn' tau_stop that])
  have bound_n: "(\<integral>\<omega>. (?XS n v \<omega> - ?XS n u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2" for n
    by (rule fourth_moment_bound_bounded[OF P mgXS uv A_intS A_rateS covAS C0
          less_imp_le[OF r_pos] bndS contS])
  have int4_n: "integrable M (\<lambda>\<omega>. (?XS n v \<omega> - ?XS n u \<omega>)^4)" for n
  proof (rule integrable_pow4_of_bounded[OF P _ _ _])
    show "(\<lambda>\<omega>. ?XS n v \<omega> - ?XS n u \<omega>) \<in> borel_measurable M"
      using XSm[OF v0, of n] XSm[OF uv(1), of n] by measurable
    show "0 \<le> 2 * r n" using r_pos[of n] by simp
    show "AE \<omega> in M. \<bar>?XS n v \<omega> - ?XS n u \<omega>\<bar> \<le> 2 * r n"
      using bndS[OF v0, of n] bndS[OF uv(1), of n]
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>?XS n v \<omega> - ?XS n u \<omega>\<bar> \<le> \<bar>?XS n v \<omega>\<bar> + \<bar>?XS n u \<omega>\<bar>"
        by (rule abs_triangle_ineq4)
      with elim show ?case by linarith
    qed
  qed
  have ptw: "\<forall>\<^sub>F n in sequentially.
      (?XS n v \<omega> - ?XS n u \<omega>)^4 = (X v \<omega> - X u \<omega>)^4"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have "compact ((\<lambda>s. X s \<omega>) ` {0..v})"
      by (intro compact_continuous_image contXv[OF w] compact_Icc)
    then have "bounded ((\<lambda>s. X s \<omega>) ` {0..v})" by (rule compact_imp_bounded)
    then obtain b where b: "\<And>y. y \<in> (\<lambda>s. X s \<omega>) ` {0..v} \<Longrightarrow> norm y \<le> b"
      unfolding bounded_iff by blast
    obtain N where N: "b \<le> real N" using real_arch_simple by blast
    have eq: "(?XS n v \<omega> - ?XS n u \<omega>)^4 = (X v \<omega> - X u \<omega>)^4" if nN: "N \<le> n" for n
    proof -
      have taueq: "tau n \<omega> = v"
        unfolding tau_def
      proof (rule etime_eq_T_of_no_hit[OF v0])
        fix s :: real assume s: "0 \<le> s" "s \<le> v"
        have "norm (X s \<omega>) \<le> b" using b s by auto
        also have "b \<le> real N" by (rule N)
        also have "real N \<le> real n" using nN by simp
        also have "real n < r n" unfolding r_def by simp
        finally show "X s \<omega> \<notin> {y. r n \<le> norm y}" by auto
      qed
      have "min v (tau n \<omega>) = v" and "min u (tau n \<omega>) = u"
        unfolding taueq using uv by simp_all
      thus ?thesis by simp
    qed
    show ?thesis unfolding eventually_sequentially
      by (intro exI[of _ N] allI impI) (rule eq, assumption)
  qed
  have gm: "(\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4) \<in> borel_measurable M"
    using borel_measurable_integrable[OF MX.integrable[OF v0]]
      borel_measurable_integrable[OF MX.integrable[OF uv(1)]] by measurable
  have fm: "(\<lambda>\<omega>. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4)) \<in> borel_measurable M" for n
    using XSm[OF v0, of n] XSm[OF uv(1), of n] by measurable
  have "AE \<omega> in M. ennreal ((X v \<omega> - X u \<omega>)^4)
      = liminf (\<lambda>n. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4))"
  proof (intro AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have "(\<lambda>n. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4))
        \<longlonglongrightarrow> ennreal ((X v \<omega> - X u \<omega>)^4)"
      by (rule tendsto_eventually) (use ptw[OF w] in \<open>auto elim: eventually_mono\<close>)
    thus "ennreal ((X v \<omega> - X u \<omega>)^4)
        = liminf (\<lambda>n. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4))"
      by (intro lim_imp_Liminf[symmetric]) simp
  qed
  hence "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M)
      = (\<integral>\<^sup>+\<omega>. liminf (\<lambda>n. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4)) \<partial>M)"
    by (rule nn_integral_cong_AE)
  also have "\<dots> \<le> liminf (\<lambda>n. \<integral>\<^sup>+\<omega>. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4) \<partial>M)"
    by (intro nn_integral_liminf fm)
  also have "\<dots> \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
  proof (rule order_trans[OF Liminf_le_Limsup])
    show "sequentially \<noteq> bot" by simp
    show "Limsup sequentially
        (\<lambda>n. \<integral>\<^sup>+\<omega>. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4) \<partial>M)
        \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    proof (intro Limsup_bounded always_eventually allI)
      fix n
      have "(\<integral>\<^sup>+\<omega>. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4) \<partial>M)
          = ennreal (\<integral>\<omega>. (?XS n v \<omega> - ?XS n u \<omega>)^4 \<partial>M)"
        by (intro nn_integral_eq_integral int4_n AE_I2 pow4_nonneg)
      also have "\<dots> \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
        by (rule ennreal_leI[OF bound_n])
      finally show "(\<integral>\<^sup>+\<omega>. ennreal ((?XS n v \<omega> - ?XS n u \<omega>)^4) \<partial>M)
          \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)" .
    qed
  qed
  finally show ?thesis .
qed

text \<open>The Bochner forms: integrability of the fourth power and the bound
  itself, ready for the dyadic tail bounds of a tightness argument.\<close>

corollary fourth_moment_L2_bochner:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and C B :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and start: "AE \<omega> in M. \<bar>X 0 \<omega>\<bar> \<le> B"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and uv: "0 \<le> u" "u \<le> v"
  shows "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
    and "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
proof -
  interpret MX: martingale M F "0::real" X by (rule mgX)
  have v0: "0 \<le> v" using uv by linarith
  have nn: "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M) \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by (rule fourth_moment_L2[OF P mgX sqX contX start mgZ A0 A_rate C0 uv])
  show int: "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
  proof (rule integrableI_nonneg)
    show "(\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4) \<in> borel_measurable M"
      using borel_measurable_integrable[OF MX.integrable[OF v0]]
        borel_measurable_integrable[OF MX.integrable[OF uv(1)]] by measurable
    show "AE \<omega> in M. 0 \<le> (X v \<omega> - X u \<omega>)^4"
      by (intro AE_I2 pow4_nonneg)
    show "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M) < \<infinity>"
      using nn by (rule order.strict_trans1) simp
  qed
  have "ennreal (\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M)
      = (\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M)"
    by (rule nn_integral_eq_integral[symmetric, OF int]) (intro AE_I2 pow4_nonneg)
  also note nn
  finally show "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    using zero_le_power2[of C] zero_le_power2[of "v - u"] by simp
qed

text \<open>Restricting a filtered probability space to a full-measure event turns
  every almost-sure hypothesis into a pointwise one while changing nothing
  visible to the laws: the restricted measure is again a probability space,
  integrals and integrability are unchanged, pushforwards are unchanged, and
  adaptedness and the martingale property descend to the restricted
  filtration.  \<open>space_restrict_full\<close>, \<open>sets_restrict_full\<close>,
  \<open>emeasure_restrict_full\<close>, \<open>prob_space_restrict_full\<close>,
  \<open>integrable_restrict_full\<close>, \<open>integral_restrict_full\<close>,
  \<open>distr_restrict_full\<close>, \<open>set_integral_restrict_full\<close>,
  \<open>filtered_measure_restrict_full\<close>,
  \<open>sigma_finite_filtered_measure_restrict_full\<close>,
  \<open>adapted_process_restrict_full\<close> and \<open>martingale_restrict_full\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

(*<*)
end
(*>*)
