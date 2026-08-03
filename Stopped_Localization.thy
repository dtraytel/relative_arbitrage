section \<open>Localization: stopping an \<open>L\<^sup>2\<close> martingale needs no domination hypothesis\<close>

text \<open>
  Plan step A3 (STATUS.md 25h), part (c'). The repository's continuous-time
  \<open>optional_stopping\<close> (Optional\_Sampling.thy) carries an integrable
  running-domination hypothesis. For an \<open>L\<^sup>2\<close> martingale that hypothesis is
  DISCHARGEABLE: the \<open>horizon_sq_int_martingale\<close> locale of Doob\_Inequality.thy
  produces, per horizon, an integrable function \<open>Dsup\<close> dominating \<open>\<bar>X s\<bar>\<close> on the
  whole interval (Doob's \<open>L\<^sup>2\<close> inequality along dyadic grids + monotone
  convergence + path continuity). This theory packages that discharge: stopping
  an \<open>L\<^sup>2\<close> martingale with continuous paths at any stopping time yields a
  martingale, unconditionally.
\<close>

theory Stopped_Localization
  imports Stopped_Adaptedness Increment_Moments Exit_Time
begin

theorem stopped_martingale_L2:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mg: "martingale M F (0::real) X"
    and sq: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
  shows "martingale M F 0 (\<lambda>v \<omega>. X (min v (tau \<omega>)) \<omega>)"
proof -
  interpret MX: martingale M F "0::real" X by (rule mg)
  have contu: "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. X s \<omega>)" if "0 < u" for u
  proof (intro AE_I2)
    fix \<omega> assume "\<omega> \<in> space M"
    from cont[OF this] show "continuous_on {0..u} (\<lambda>s. X s \<omega>)"
      by (rule continuous_on_subset) auto
  qed
  have hsim: "horizon_sq_int_martingale M F X u" if "0 < u" for u
    by (intro horizon_sq_int_martingale.intro[OF mg]
        horizon_sq_int_martingale_axioms.intro that P sq)
  have Dex: "\<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D \<omega>)
              \<and> integrable M D" if u: "0 < u" for u
  proof -
    interpret H: horizon_sq_int_martingale M F X u by (rule hsim[OF u])
    show ?thesis
      by (intro exI[of _ H.Dsup] conjI H.Dsup_dominates[OF contu[OF u]]
          H.Dsup_integrable)
  qed
  define D where "D = (\<lambda>u. SOME Dv.
      (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> Dv \<omega>) \<and> integrable M Dv)"
  have DP: "(AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D u \<omega>)
              \<and> integrable M (D u)" if u: "0 < u" for u
    unfolding D_def by (rule someI_ex[OF Dex[OF u]])
  show ?thesis
  proof (rule optional_stopping[OF mg tau_nonneg tau_stop])
    show "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. X s \<omega>)" if "0 < u" for u
      by (rule contu[OF that])
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> D u \<omega>" if "0 < u" for u
      using DP[OF that] by blast
    show "integrable M (D u)" if "0 < u" for u
      using DP[OF that] by blast
    show "(\<lambda>\<omega>. X (min v (tau \<omega>)) \<omega>) \<in> borel_measurable (F v)" if "0 \<le> v" for v
      by (rule stopped_adapted_of_cont[OF martingale.axioms(2)[OF mg]
            tau_nonneg tau_stop cont that])
  qed
qed

section \<open>Stopping the compensated square\<close>

text \<open>
  Plan step A3 (c''). The compensated square \<open>Z = X\<^sup>2 - A\<close> of an \<open>L\<^sup>2\<close> martingale
  with a Lipschitz-rate compensator is generally NOT \<open>L\<^sup>2\<close>, so
  @{thm [source] stopped_martingale_L2} does not apply to it directly. But it IS
  dominated on \<open>[0,u]\<close>: \<open>\<bar>Z s\<bar> \<le> Dsup\<^sup>2 + C u\<close> where \<open>Dsup\<close> is the running-maximum
  bound for \<open>X\<close>, and \<open>Dsup\<^sup>2\<close> is integrable by Doob's \<open>L\<^sup>2\<close> inequality
  (\<open>Dsup_sq_integrable\<close>). So the domination hypothesis of \<open>optional_stopping\<close> is
  again dischargeable. Stopping \<open>Z\<close> is what transfers the covariation package to
  the stopped process: the martingale property of \<open>Z\<^sup>\<tau>\<close> IS the statement that
  \<open>A(\<cdot> \<and> \<tau>)\<close> compensates \<open>(X\<^sup>\<tau>)\<^sup>2\<close>.
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
proof -
  interpret P: prob_space M by (rule P)
  let ?Z = "\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>"
  have Abnd: "0 \<le> A s \<omega> \<and> A s \<omega> \<le> C * s"
    if w: "\<omega> \<in> space M" and s: "0 \<le> s" for s \<omega>
    using A_rate[OF w, rule_format, of 0 s] s A0[OF w] by simp
  have contA: "continuous_on {0..} (\<lambda>s. A s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have "C-lipschitz_on {0..} (\<lambda>s. A s \<omega>)"
    proof (rule lipschitz_onI)
      show "0 \<le> C" by (rule C0)
      fix x y :: real assume x: "x \<in> {0..}" and y: "y \<in> {0..}"
      show "dist (A x \<omega>) (A y \<omega>) \<le> C * dist x y"
      proof (cases "x \<le> y")
        case True
        with A_rate[OF w, rule_format, of x y] x show ?thesis
          by (simp add: dist_real_def abs_diff_le_iff) linarith?
      next
        case False
        with A_rate[OF w, rule_format, of y x] y show ?thesis
          by (simp add: dist_real_def abs_diff_le_iff) linarith?
      qed
    qed
    thus ?thesis by (rule lipschitz_on_continuous_on)
  qed
  have contZ: "continuous_on {0..} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
    by (intro continuous_on_diff continuous_on_power contX[OF w] contA[OF w])
  have contZu: "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. ?Z s \<omega>)" if "0 < u" for u
  proof (intro AE_I2)
    fix \<omega> assume "\<omega> \<in> space M"
    from contZ[OF this] show "continuous_on {0..u} (\<lambda>s. ?Z s \<omega>)"
      by (rule continuous_on_subset) auto
  qed
  have contXu: "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. X s \<omega>)" if "0 < u" for u
  proof (intro AE_I2)
    fix \<omega> assume "\<omega> \<in> space M"
    from contX[OF this] show "continuous_on {0..u} (\<lambda>s. X s \<omega>)"
      by (rule continuous_on_subset) auto
  qed
  have Dex: "\<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>?Z s \<omega>\<bar> \<le> D \<omega>)
              \<and> integrable M D" if u: "0 < u" for u
  proof -
    interpret H: horizon_sq_int_martingale M F X u
      by (intro horizon_sq_int_martingale.intro[OF mgX]
          horizon_sq_int_martingale_axioms.intro u P sqX)
    have dom: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow>
        \<bar>?Z s \<omega>\<bar> \<le> (H.Dsup \<omega>)\<^sup>2 + C * u"
      using H.Dsup_dominates[OF contXu[OF u]] AE_space
    proof eventually_elim
      case (elim \<omega>)
      show ?case
      proof (intro allI impI)
        fix s :: real assume s: "0 \<le> s" and su: "s \<le> u"
        have xb: "\<bar>X s \<omega>\<bar> \<le> H.Dsup \<omega>" using elim s su by blast
        have "(X s \<omega>)\<^sup>2 = \<bar>X s \<omega>\<bar>\<^sup>2" by simp
        also have "\<dots> \<le> (H.Dsup \<omega>)\<^sup>2"
          by (rule power_mono[OF xb abs_ge_zero])
        finally have x2: "(X s \<omega>)\<^sup>2 \<le> (H.Dsup \<omega>)\<^sup>2" .
        have "0 \<le> A s \<omega> \<and> A s \<omega> \<le> C * s"
          using Abnd elim s by blast
        moreover have "C * s \<le> C * u"
          using su C0 by (intro mult_left_mono)
        moreover have "0 \<le> (X s \<omega>)\<^sup>2" by simp
        ultimately show "\<bar>?Z s \<omega>\<bar> \<le> (H.Dsup \<omega>)\<^sup>2 + C * u"
          using x2 zero_le_power2[of "X s \<omega>"] zero_le_power2[of "H.Dsup \<omega>"]
          unfolding abs_diff_le_iff by (intro conjI) linarith+
      qed
    qed
    have int: "integrable M (\<lambda>\<omega>. (H.Dsup \<omega>)\<^sup>2 + C * u)"
      by (intro Bochner_Integration.integrable_add H.Dsup_sq_integrable
          P.integrable_const)
    show ?thesis
      by (intro exI[of _ "\<lambda>\<omega>. (H.Dsup \<omega>)\<^sup>2 + C * u"] conjI dom int)
  qed
  define D where "D = (\<lambda>u. SOME Dv.
      (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>?Z s \<omega>\<bar> \<le> Dv \<omega>) \<and> integrable M Dv)"
  have DP: "(AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>?Z s \<omega>\<bar> \<le> D u \<omega>)
              \<and> integrable M (D u)" if u: "0 < u" for u
    unfolding D_def by (rule someI_ex[OF Dex[OF u]])
  show ?thesis
  proof (rule optional_stopping[OF mgZ tau_nonneg tau_stop])
    show "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. ?Z s \<omega>)" if "0 < u" for u
      by (rule contZu[OF that])
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>?Z s \<omega>\<bar> \<le> D u \<omega>" if "0 < u" for u
      using DP[OF that] by blast
    show "integrable M (D u)" if "0 < u" for u
      using DP[OF that] by blast
    show "(\<lambda>\<omega>. ?Z (min v (tau \<omega>)) \<omega>) \<in> borel_measurable (F v)" if "0 \<le> v" for v
      by (rule stopped_adapted_of_cont[OF martingale.axioms(2)[OF mgZ]
            tau_nonneg tau_stop contZ that])
  qed
qed

section \<open>The covariation package transfers to the stopped process\<close>

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

text \<open>
  The martingale property of the stopped compensated square, rewritten as the
  conditional covariation identity for the stopped process: this is what feeds
  \<open>fourth_moment_bound_bounded\<close> at compensator \<open>A(\<cdot> \<and> \<tau>)\<close>. The conditional
  variance identity \<open>cond_exp_increment_sq\<close> converts squared increments into
  differences of squares, and adaptedness of the stopped compensator collapses
  its conditional expectation.
\<close>

theorem stopped_covariation:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real" and C :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and Aad: "adapted_process M F (0::real) A"
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
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule mgX)
  let ?XS = "\<lambda>t \<omega>. X (min t (tau \<omega>)) \<omega>"
  let ?AS = "\<lambda>t \<omega>. A (min t (tau \<omega>)) \<omega>"
  have v0: "0 \<le> v" using uv by linarith
  have contA: "continuous_on {0..} (\<lambda>s. A s \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
    by (rule rate_continuous_on[OF C0 A_rate[OF w]])
  have contXu: "AE \<omega> in M. continuous_on {0..w} (\<lambda>s. X s \<omega>)" if "0 < w" for w
  proof (intro AE_I2)
    fix \<omega> assume "\<omega> \<in> space M"
    from contX[OF this] show "continuous_on {0..w} (\<lambda>s. X s \<omega>)"
      by (rule continuous_on_subset) auto
  qed
  have mgXS: "martingale M F 0 ?XS"
    by (rule stopped_martingale_L2[OF P mgX sqX contX tau_nonneg tau_stop])
  have XSad: "?XS s \<in> borel_measurable (F s)" if "0 \<le> s" for s
    by (rule stopped_adapted_of_cont[OF martingale.axioms(2)[OF mgX]
          tau_nonneg tau_stop contX that])
  have XSm: "?XS s \<in> borel_measurable M" if "0 \<le> s" for s
    by (rule measurable_from_subalg[OF MX.subalgebras[OF that] XSad[OF that]])
  have ASad: "?AS s \<in> borel_measurable (F s)" if "0 \<le> s" for s
    by (rule stopped_adapted_of_cont[OF Aad tau_nonneg tau_stop contA that])
  have ASm: "?AS s \<in> borel_measurable M" if "0 \<le> s" for s
    by (rule measurable_from_subalg[OF MX.subalgebras[OF that] ASad[OF that]])
  have sqXS: "integrable M (\<lambda>\<omega>. (?XS s \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have s1: "0 < s + 1" using s by simp
    interpret H: horizon_sq_int_martingale M F X "s + 1"
      by (intro horizon_sq_int_martingale.intro[OF mgX]
          horizon_sq_int_martingale_axioms.intro s1 P sqX)
    have bnd: "AE \<omega> in M. norm ((?XS s \<omega>)\<^sup>2) \<le> norm ((H.Dsup \<omega>)\<^sup>2)"
      using H.Dsup_dominates[OF contXu[OF s1]] AE_space
    proof eventually_elim
      case (elim \<omega>)
      have m0: "0 \<le> min s (tau \<omega>)" using s tau_nonneg elim by simp
      have m1: "min s (tau \<omega>) \<le> s + 1" using s by simp
      have xb: "\<bar>?XS s \<omega>\<bar> \<le> H.Dsup \<omega>" using elim m0 m1 by blast
      have "(?XS s \<omega>)\<^sup>2 = \<bar>?XS s \<omega>\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (H.Dsup \<omega>)\<^sup>2" by (rule power_mono[OF xb abs_ge_zero])
      finally show ?case by simp
    qed
    show ?thesis
      by (rule Bochner_Integration.integrable_bound
            [OF H.Dsup_sq_integrable _ bnd]) (use XSm[OF s] in measurable)
  qed
  have iAS: "integrable M (?AS s)" if s: "0 \<le> s" for s
  proof (rule Bochner_Integration.integrable_bound[OF P.integrable_const[of "C * s"]])
    show "?AS s \<in> borel_measurable M" by (rule ASm[OF s])
    show "AE \<omega> in M. norm (?AS s \<omega>) \<le> norm (C * s)"
    proof (intro AE_I2)
      fix \<omega> assume w: "\<omega> \<in> space M"
      have m0: "0 \<le> min s (tau \<omega>)" using s tau_nonneg w by simp
      have "0 \<le> ?AS s \<omega> \<and> ?AS s \<omega> \<le> C * min s (tau \<omega>)"
        using A_rate[OF w, rule_format, of 0 "min s (tau \<omega>)"] m0 A0[OF w] by simp
      moreover have "C * min s (tau \<omega>) \<le> C * s"
        using C0 s by (intro mult_left_mono) simp_all
      moreover have "0 \<le> C * s" using C0 s by simp
      ultimately show "norm (?AS s \<omega>) \<le> norm (C * s)" by simp
    qed
  qed
  have mgZS: "martingale M F 0 (\<lambda>t \<omega>. (?XS t \<omega>)\<^sup>2 - ?AS t \<omega>)"
    by (rule stopped_compensated_square[OF P mgX sqX contX mgZ A0 A_rate C0
          tau_nonneg tau_stop])
  have sfs: "sigma_finite_subalgebra M (F u)"
    using uv(1) by (rule MX.sigma_finite_subalgebra_F)
  have inc: "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. (?XS v \<omega> - ?XS u \<omega>)\<^sup>2) \<omega>
      = cond_exp M (F u) (\<lambda>\<omega>. (?XS v \<omega>)\<^sup>2) \<omega> - (?XS u \<omega>)\<^sup>2"
    by (rule cond_exp_increment_sq[OF mgXS sqXS uv])
  have zmp: "AE \<omega> in M. (?XS u \<omega>)\<^sup>2 - ?AS u \<omega>
      = cond_exp M (F u) (\<lambda>\<omega>. (?XS v \<omega>)\<^sup>2 - ?AS v \<omega>) \<omega>"
    by (rule martingale.martingale_property[OF mgZS uv(1) uv(2)])
  have d1: "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. (?XS v \<omega>)\<^sup>2 - ?AS v \<omega>) \<omega>
      = cond_exp M (F u) (\<lambda>\<omega>. (?XS v \<omega>)\<^sup>2) \<omega> - cond_exp M (F u) (?AS v) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff[OF sfs sqXS[OF v0] iAS[OF v0]])
  have d2: "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. ?AS v \<omega> - ?AS u \<omega>) \<omega>
      = cond_exp M (F u) (?AS v) \<omega> - cond_exp M (F u) (?AS u) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff[OF sfs iAS[OF v0] iAS[OF uv(1)]])
  have fm: "AE \<omega> in M. cond_exp M (F u) (?AS u) \<omega> = ?AS u \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_F_meas[OF sfs iAS[OF uv(1)]
          ASad[OF uv(1)]])
  from inc zmp d1 d2 fm show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    from elim show ?case by linarith
  qed
qed

section \<open>Eq. (2.7) for unbounded \<open>L\<^sup>2\<close> martingales, by localization and Fatou\<close>

lemma etime_eq_T_of_no_hit:
  assumes T: "0 \<le> T" and nh: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> X s \<omega> \<notin> A"
  shows "etime T A X \<omega> = T"
proof -
  have e: "{s. 0 \<le> s \<and> s \<le> T \<and> X s \<omega> \<in> A} = {}" using nh by auto
  have "etime T A X \<omega> = Inf ({s. 0 \<le> s \<and> s \<le> T \<and> X s \<omega> \<in> A} \<union> {T})"
    unfolding etime_def by (rule refl)
  also have "\<dots> = Inf {T}" unfolding e by simp
  also have "\<dots> = T" by (rule cInf_singleton)
  finally show ?thesis .
qed

text \<open>
  The A3 deliverable (STATUS.md 25h): the paper's Eq. (2.7) with constant
  \<open>8 C\<^sup>2\<close> for an UNBOUNDED \<open>L\<^sup>2\<close> martingale with deterministic start and a
  Lipschitz-rate compensator for its square. Localize at the exit times of the
  balls of radius \<open>\<bar>x\<^sub>0\<bar> + n + 1\<close>, apply the bounded estimate to each stopped
  process — its martingale property, covariation package and boundedness come
  from the three theorems above and the exit-time theory — and pass to the
  limit by Fatou: continuous paths are bounded on compact intervals, so for
  every \<open>\<omega>\<close> the stopped increments are EVENTUALLY EQUAL to the plain ones.
\<close>

theorem fourth_moment_L2:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and C x0 :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and start: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> X 0 \<omega> = x0"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and Aad: "adapted_process M F (0::real) A"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and uv: "0 \<le> u" "u \<le> v"
  shows "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M) \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule mgX)
  have v0: "0 \<le> v" using uv by linarith
  define r where "r = (\<lambda>n::nat. \<bar>x0\<bar> + real n + 1)"
  have r_gt: "\<bar>x0\<bar> < r n" for n unfolding r_def by simp
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
  proof (intro AE_I2)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have m0: "0 \<le> min s (tau n \<omega>)" using s tau_nn by simp
    have st: "norm (X 0 \<omega>) < r n" using start[OF w] r_gt by simp
    have sle: "min s (tau n \<omega>) \<le> etime v {y. r n \<le> norm y} X \<omega>"
      unfolding tau_def by simp
    have "X (min s (tau n \<omega>)) \<omega> \<in> cball 0 (r n)"
      by (rule etime_stays_in_cball[OF v0 r_pos st contXv[OF w] m0 sle])
    thus "\<bar>?XS n s \<omega>\<bar> \<le> r n" by simp
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
  proof (rule Bochner_Integration.integrable_bound[OF P.integrable_const[of "C * s"]])
    show "?AS n s \<in> borel_measurable M" by (rule ASm[OF s])
    show "AE \<omega> in M. norm (?AS n s \<omega>) \<le> norm (C * s)"
    proof (intro AE_I2)
      fix \<omega> assume w: "\<omega> \<in> space M"
      have m0: "0 \<le> min s (tau n \<omega>)" using s tau_nn by simp
      have "0 \<le> ?AS n s \<omega> \<and> ?AS n s \<omega> \<le> C * min s (tau n \<omega>)"
        using A_rate[OF w, rule_format, of 0 "min s (tau n \<omega>)"] m0 A0[OF w] by simp
      moreover have "C * min s (tau n \<omega>) \<le> C * s"
        using C0 s by (intro mult_left_mono) simp_all
      moreover have "0 \<le> C * s" by (rule mult_nonneg_nonneg[OF C0 s])
      ultimately show "norm (?AS n s \<omega>) \<le> norm (C * s)" by simp
    qed
  qed
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
    by (rule stopped_covariation[OF P mgX sqX contX mgZ Aad A0 A_rate C0
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
  itself, ready for \<open>dyadic_bad_event_tail_mom\<close>.\<close>

corollary fourth_moment_L2_integrable:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and C x0 :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and start: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> X 0 \<omega> = x0"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and Aad: "adapted_process M F (0::real) A"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and uv: "0 \<le> u" "u \<le> v"
  shows "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
proof (rule integrableI_nonneg)
  interpret MX: martingale M F "0::real" X by (rule mgX)
  have v0: "0 \<le> v" using uv by linarith
  show "(\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4) \<in> borel_measurable M"
    using borel_measurable_integrable[OF MX.integrable[OF v0]]
      borel_measurable_integrable[OF MX.integrable[OF uv(1)]] by measurable
  show "AE \<omega> in M. 0 \<le> (X v \<omega> - X u \<omega>)^4"
    by (intro AE_I2 pow4_nonneg)
  have "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M) \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by (rule fourth_moment_L2[OF P mgX sqX contX start mgZ Aad A0 A_rate C0 uv])
  also have "\<dots> < \<infinity>" by simp
  finally show "(\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M) < \<infinity>" .
qed

corollary fourth_moment_L2_bochner:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and C x0 :: real
  assumes P: "prob_space M"
    and mgX: "martingale M F (0::real) X"
    and sqX: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and contX: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and start: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> X 0 \<omega> = x0"
    and mgZ: "martingale M F 0 (\<lambda>t \<omega>. (X t \<omega>)\<^sup>2 - A t \<omega>)"
    and Aad: "adapted_process M F (0::real) A"
    and A0: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> A 0 \<omega> = 0"
    and A_rate: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and C0: "0 \<le> C"
    and uv: "0 \<le> u" "u \<le> v"
  shows "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
proof -
  have int: "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
    by (rule fourth_moment_L2_integrable[OF P mgX sqX contX start mgZ Aad A0
          A_rate C0 uv])
  have B0: "0 \<le> 8*C\<^sup>2*(v - u)\<^sup>2" by simp
  have "ennreal (\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M)
      = (\<integral>\<^sup>+\<omega>. ennreal ((X v \<omega> - X u \<omega>)^4) \<partial>M)"
    by (rule nn_integral_eq_integral[symmetric, OF int])
       (intro AE_I2 pow4_nonneg)
  also have "\<dots> \<le> ennreal (8*C\<^sup>2*(v - u)\<^sup>2)"
    by (rule fourth_moment_L2[OF P mgX sqX contX start mgZ Aad A0 A_rate C0 uv])
  finally show ?thesis
    using B0 by simp
qed

text \<open>Restricting a filtered probability space to a full-measure event turns
  every almost-sure hypothesis into a pointwise one while changing nothing
  visible to the laws: the restricted measure is again a probability space,
  integrals and integrability are unchanged, pushforwards are unchanged, and
  adaptedness and the martingale property descend to the restricted
  filtration.  This is the bridge from the AE-phrased market class to the
  pointwise hypotheses of the tightness package.\<close>

section \<open>Restriction of a filtered probability space to a full-measure event\<close>

context
  fixes M :: "'a measure" and G :: "'a set"
  assumes P: "prob_space M"
      and G: "G \<in> sets M"
      and full: "AE \<omega> in M. \<omega> \<in> G"
begin

lemma space_restrict_full: "space (restrict_space M G) = G"
  using sets.sets_into_space[OF G] by (auto simp: space_restrict_space)

lemma sets_restrict_full: "G \<inter> space M \<in> sets M"
  using G by (simp add: sets.sets_into_space Int_absorb2)

lemma AE_restrict_full:
  assumes "AE \<omega> in M. \<phi> \<omega>"
  shows "AE \<omega> in restrict_space M G. \<phi> \<omega>"
  by (subst AE_restrict_space_iff[OF sets_restrict_full])
    (use assms in auto)

lemma emeasure_restrict_full:
  assumes S: "S \<in> sets M"
  shows "emeasure (restrict_space M G) (S \<inter> G) = emeasure M S"
proof -
  have "emeasure (restrict_space M G) (S \<inter> G) = emeasure M (S \<inter> G)"
    by (rule emeasure_restrict_space[OF sets_restrict_full]) auto
  also have "\<dots> = emeasure M S"
    using full S G by (intro emeasure_eq_AE) auto
  finally show ?thesis .
qed

lemma prob_space_restrict_full: "prob_space (restrict_space M G)"
proof -
  interpret prob_space M by (rule P)
  have sG: "space M \<inter> G = G"
    using sets.sets_into_space[OF G] by auto
  have "emeasure (restrict_space M G) (space (restrict_space M G))
      = emeasure M (space M)"
    using emeasure_restrict_full[OF sets.top] space_restrict_full
    unfolding sG by simp
  then show ?thesis
    by (intro prob_spaceI) (simp add: emeasure_space_1)
qed

lemma integrable_restrict_full:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes "integrable M f"
  shows "integrable (restrict_space M G) f"
proof -
  have "integrable M (\<lambda>x. indicator G x *\<^sub>R f x)"
    by (rule integrable_mult_indicator[OF G assms])
  then show ?thesis
    by (subst integrable_restrict_space[OF sets_restrict_full])
qed

lemma integral_restrict_full:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<integral>\<omega>. f \<omega> \<partial>restrict_space M G) = (\<integral>\<omega>. f \<omega> \<partial>M)"
proof -
  have "(\<integral>\<omega>. f \<omega> \<partial>restrict_space M G) = (\<integral>\<omega>. indicator G \<omega> *\<^sub>R f \<omega> \<partial>M)"
    by (rule integral_restrict_space[OF sets_restrict_full])
  also have "\<dots> = (\<integral>\<omega>. f \<omega> \<partial>M)"
  proof -
    have m: "(\<lambda>\<omega>. indicator G \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable M"
      by (intro borel_measurable_scaleR borel_measurable_indicator G f)
    show ?thesis
      using full by (intro integral_cong_AE[OF m f]) auto
  qed
  finally show ?thesis .
qed

lemma distr_restrict_full:
  assumes f: "f \<in> measurable M N"
  shows "distr (restrict_space M G) N f = distr M N f"
proof (rule measure_eqI)
  show "sets (distr (restrict_space M G) N f) = sets (distr M N f)"
    by simp
  fix B assume "B \<in> sets (distr (restrict_space M G) N f)"
  then have B: "B \<in> sets N" by simp
  have f': "f \<in> measurable (restrict_space M G) N"
    by (rule measurable_restrict_space1[OF f])
  have vim: "f -` B \<inter> space M \<in> sets M"
    by (rule measurable_sets[OF f B])
  have "emeasure (distr (restrict_space M G) N f) B
      = emeasure (restrict_space M G) (f -` B \<inter> space (restrict_space M G))"
    by (rule emeasure_distr[OF f' B])
  also have "f -` B \<inter> space (restrict_space M G) = (f -` B \<inter> space M) \<inter> G"
    unfolding space_restrict_full using sets.sets_into_space[OF G] by auto
  also have "emeasure (restrict_space M G) ((f -` B \<inter> space M) \<inter> G)
      = emeasure M (f -` B \<inter> space M)"
    by (rule emeasure_restrict_full[OF vim])
  also have "\<dots> = emeasure (distr M N f) B"
    by (rule emeasure_distr[symmetric, OF f B])
  finally show "emeasure (distr (restrict_space M G) N f) B
      = emeasure (distr M N f) B" .
qed

lemma set_integral_restrict_full:
  fixes f :: "'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes f: "f \<in> borel_measurable M" and S: "S \<in> sets M"
  shows "set_lebesgue_integral (restrict_space M G) (G \<inter> S) f
       = set_lebesgue_integral M S f"
proof -
  have GS: "G \<inter> S \<in> sets M"
    using G S by blast
  have m: "(\<lambda>\<omega>. indicator (G \<inter> S) \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_scaleR borel_measurable_indicator GS f)
  have m': "(\<lambda>\<omega>. indicator S \<omega> *\<^sub>R f \<omega>) \<in> borel_measurable M"
    by (intro borel_measurable_scaleR borel_measurable_indicator S f)
  have "set_lebesgue_integral (restrict_space M G) (G \<inter> S) f
      = (\<integral>\<omega>. indicator (G \<inter> S) \<omega> *\<^sub>R f \<omega> \<partial>restrict_space M G)"
    by (simp add: set_lebesgue_integral_def)
  also have "\<dots> = (\<integral>\<omega>. indicator (G \<inter> S) \<omega> *\<^sub>R f \<omega> \<partial>M)"
    by (rule integral_restrict_full[OF m])
  also have "\<dots> = (\<integral>\<omega>. indicator S \<omega> *\<^sub>R f \<omega> \<partial>M)"
    using full by (intro integral_cong_AE[OF m m']) (auto simp: indicator_def)
  also have "\<dots> = set_lebesgue_integral M S f"
    by (simp add: set_lebesgue_integral_def)
  finally show ?thesis .
qed

lemma filtered_measure_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
  assumes fm: "filtered_measure M F (0::real)"
  shows "filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
proof -
  interpret FM: filtered_measure M F 0 by (rule fm)
  show ?thesis
  proof (unfold_locales)
    fix i :: real assume i: "0 \<le> i"
    have "sets (restrict_space (F i) G) = (\<inter>) G ` sets (F i)"
      by (rule sets_restrict_space)
    also have "\<dots> \<subseteq> (\<inter>) G ` sets M"
      using FM.subalgebras[OF i] by (auto simp: subalgebra_def)
    also have "\<dots> = sets (restrict_space M G)"
      by (rule sets_restrict_space[symmetric])
    finally have 1: "sets (restrict_space (F i) G)
        \<subseteq> sets (restrict_space M G)" .
    have 2: "space (restrict_space (F i) G) = space (restrict_space M G)"
      by (simp add: space_restrict_space FM.space_F[OF i])
    show "subalgebra (restrict_space M G) (restrict_space (F i) G)"
      using 1 2 by (simp add: subalgebra_def)
  next
    fix i j :: real assume "0 \<le> i" "i \<le> j"
    then show "sets (restrict_space (F i) G)
        \<subseteq> sets (restrict_space (F j) G)"
      using FM.sets_F_mono by (auto simp: sets_restrict_space)
  qed
qed

lemma sigma_finite_filtered_measure_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
  assumes fm: "filtered_measure M F (0::real)"
  shows "sigma_finite_filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
proof -
  have fm': "filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
    by (rule filtered_measure_restrict_full[OF fm])
  have fin: "finite_measure (restrict_space M G)"
    by (rule prob_space.finite_measure[OF prob_space_restrict_full])
  have sub0: "subalgebra (restrict_space M G) (restrict_space (F 0) G)"
    by (rule filtered_measure.subalgebras[OF fm']) simp
  show ?thesis
    by (intro sigma_finite_filtered_measure.intro fm'
        sigma_finite_filtered_measure_axioms.intro
        finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fin sub0)
qed

lemma adapted_process_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
    and A :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes ap: "adapted_process M F (0::real) A"
  shows "adapted_process (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0 A"
proof -
  interpret AP: adapted_process M F 0 A by (rule ap)
  have fm: "filtered_measure (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0"
    by (rule filtered_measure_restrict_full[OF AP.filtered_measure_axioms])
  show ?thesis
    by (intro adapted_process.intro fm adapted_process_axioms.intro
        measurable_restrict_space1 AP.adapted)
qed

theorem martingale_restrict_full:
  fixes F :: "real \<Rightarrow> 'a measure"
    and X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology, banach}"
  assumes mg: "martingale M F (0::real) X"
  shows "martingale (restrict_space M G)
      (\<lambda>t. restrict_space (F t) G) 0 X"
proof -
  interpret MX: martingale M F 0 X by (rule mg)
  let ?M' = "restrict_space M G"
  let ?F' = "\<lambda>t. restrict_space (F t) G"
  interpret SFF: sigma_finite_filtered_measure ?M' ?F' 0
    by (rule sigma_finite_filtered_measure_restrict_full
        [OF MX.filtered_measure_axioms])
  have ap: "adapted_process ?M' ?F' 0 X"
    by (rule adapted_process_restrict_full[OF MX.adapted_process_axioms])
  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq[OF ap])
    show "\<And>i. 0 \<le> i \<Longrightarrow> integrable ?M' (X i)"
      by (intro integrable_restrict_full MX.integrable)
    fix A and i j :: real
    assume i: "0 \<le> i" and ij: "i \<le> j" and A: "A \<in> sets (?F' i)"
    have j: "0 \<le> j" using i ij by linarith
    from A obtain S where S: "S \<in> sets (F i)" and AS: "A = G \<inter> S"
      by (auto simp: sets_restrict_space)
    have SM: "S \<in> sets M"
      using MX.subalgebras[OF i] S by (auto simp: subalgebra_def)
    have Xi: "X i \<in> borel_measurable M"
      by (rule borel_measurable_integrable[OF MX.integrable[OF i]])
    have Xj: "X j \<in> borel_measurable M"
      by (rule borel_measurable_integrable[OF MX.integrable[OF j]])
    have "set_lebesgue_integral ?M' A (X i)
        = set_lebesgue_integral M S (X i)"
      unfolding AS by (rule set_integral_restrict_full[OF Xi SM])
    also have "\<dots> = set_lebesgue_integral M S (X j)"
      using S i ij by (rule MX.set_integral_eq)
    also have "\<dots> = set_lebesgue_integral ?M' A (X j)"
      unfolding AS by (rule set_integral_restrict_full[symmetric, OF Xj SM])
    finally show "set_lebesgue_integral ?M' A (X i)
        = set_lebesgue_integral ?M' A (X j)" .
  qed
qed

end

end
