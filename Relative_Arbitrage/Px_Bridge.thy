section \<open>The paper's class \<open>P\<^sub>x\<close> and the bridge to the pair class\<close>

(*<*)
theory Px_Bridge
  imports Exit_Class_Infinite Continuous_QV
begin
(*>*)

text \<open>
  \<open>iexit_class k L x\<close> is a set of laws of the PAIR \<open>(X, \<langle>X\<rangle>)\<close>; the paper's \<open>P\<^sub>x\<close>
  is a set of laws of \<open>X\<close> alone, constrained through \<open>d\<langle>X\<rangle>(t)/dt\<close>.  This theory
  states the paper's class and identifies the two.

  The covariation is phrased EXISTENTIALLY: a law belongs to the class when
  SOME continuous adapted \<open>A\<close> compensates \<open>X X\<^sup>T\<close> and has the required rate.
  That is faithful --- the paper's \<open>d\<langle>X\<rangle>/dt \<in> S\<close> says exactly that \<open>\<langle>X\<rangle>\<close> is such
  an \<open>A\<close>, and the compensator is unique up to indistinguishability --- and it is
  what makes both inclusions fall out of \<open>qvmat_eq_A_sym\<close>: such an \<open>A\<close> is forced
  to agree with \<open>qvmat\<close>, which is a functional of the path alone.
\<close>

subsection \<open>The functional reads the path only up to the current time\<close>

text \<open>
  T1--T4 assume \<open>X\<close> uniformly bounded, because Eq. (2.7)
  (\<open>fourth_moment_bound_bounded\<close>) does.  A member of the class is not bounded,
  so the identification has to be localised --- which is what
  @{theory Relative_Arbitrage.Stopped_Localization} was built for: stopping an
  \<open>L\<^sup>2\<close> martingale with continuous paths at any stopping time yields a
  martingale, unconditionally, and the same holds for the compensated square.

  The functional cooperates: \<open>qvps w t\<close> reads \<open>w\<close> only on \<open>{0..t}\<close> --- the
  dyadic grid of \<open>{0..q}\<close> for rational \<open>q < t\<close> --- so on the event that the
  stopping time exceeds \<open>t\<close>, stopping does not change it.  These three
  congruences are what make that precise.
\<close>

lemma dyadic_qsum_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> w s = w' s" and T: "0 \<le> T"
  shows "dyadic_qsum w T n = dyadic_qsum w' T n"
  unfolding dyadic_qsum_def
proof (rule sum.cong[OF refl])
  fix k :: nat assume "k \<in> {..<2 ^ n}"
  then have k: "Suc k \<le> 2 ^ n" by simp
  then have k': "k \<le> 2 ^ n" by simp
  show "(w (T * real (Suc k) / 2 ^ n) - w (T * real k / 2 ^ n))\<^sup>2
      = (w' (T * real (Suc k) / 2 ^ n) - w' (T * real k / 2 ^ n))\<^sup>2"
    using eq[OF grid_bounds(1)[OF T k] grid_bounds(2)[OF T k]]
      eq[OF grid_bounds(1)[OF T k'] grid_bounds(2)[OF T k']]
    by simp
qed

lemma qvp_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> w s = w' s" and T: "0 \<le> T"
  shows "qvp w T = qvp w' T"
  unfolding qvp_def by (simp add: dyadic_qsum_cong[OF eq T])

lemma qvps_cong:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> w s = w' s"
  shows "qvps w t = qvps w' t"
  unfolding qvps_def
proof (intro arg_cong[where f = real_of_ereal] SUP_cong refl)
  fix q :: rat assume "q \<in> {q :: rat. 0 \<le> q \<and> real_of_rat q < t}"
  then have q: "0 \<le> real_of_rat q" and qt: "real_of_rat q < t" by auto
  have "qvp w (real_of_rat q) = qvp w' (real_of_rat q)"
    by (rule qvp_cong[OF _ q]) (use eq qt in auto)
  then show "ereal (qvp w (real_of_rat q)) = ereal (qvp w' (real_of_rat q))"
    by simp
qed

subsection \<open>The identification at one localisation level\<close>

text \<open>Stopping at the exit time from a ball of radius \<open>r\<close> makes the process
  bounded, which is the one hypothesis of T1--T4 that a class member fails.
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
  shows "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
           qvps (\<lambda>s. X (min s (tau \<omega>)) \<omega>) t = A (min t (tau \<omega>)) \<omega>"
proof -
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

  text \<open>The stopped pair satisfies the hypotheses of T1--T4.\<close>
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
  show ?thesis by (rule S.qvps_eq_A)
qed

subsection \<open>T4 without the boundedness hypothesis\<close>

text \<open>Letting the radius and the horizon grow together.  For a fixed time the
  path is bounded on \<open>{0..t}\<close> by continuity, so some level is never reached
  before \<open>t\<close>; there the stopped process agrees with \<open>X\<close> and the stopped
  compensator with \<open>A\<close>, and the congruence carries the identification across.
  The levels are indexed by naturals, so one countable intersection serves all
  of them.\<close>

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
  shows "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega>) t = A t \<omega>"
proof -
  define lev where "lev = (\<lambda>R::nat. B + real (Suc R))"
  define tau where
    "tau = (\<lambda>R::nat. etime (real (Suc R)) {y :: real. lev R \<le> norm y} X)"
  have lev_pos: "0 < lev R" for R using B0 by (simp add: lev_def)
  have T_pos: "(0::real) < real (Suc R)" for R by simp
  have X0lt: "\<bar>X 0 \<omega>\<bar> < lev R" if "\<omega> \<in> space M" for \<omega> R
    using X0[OF that] by (simp add: lev_def)
  have step: "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
      qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>" for R
    unfolding tau_def
    by (rule qvps_eq_A_stopped
          [OF P mgX sqX contX mgZ A0 A_rate C0 T_pos lev_pos X0lt])
  have all: "AE \<omega> in M. \<forall>R::nat. \<forall>t. 0 \<le> t \<longrightarrow>
      qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>"
    by (subst AE_all_countable) (rule allI, rule step)
  have sp: "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  from all sp show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have key: "\<And>R t. 0 \<le> t \<Longrightarrow>
        qvps (\<lambda>s. X (min s (tau R \<omega>)) \<omega>) t = A (min t (tau R \<omega>)) \<omega>"
      and w: "\<omega> \<in> space M" by blast+
    show ?case
    proof (intro allI impI)
      fix t :: real assume t: "0 \<le> t"
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
      have taut: "t < tau n \<omega>"
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
      have "qvps (\<lambda>s. X (min s (tau n \<omega>)) \<omega>) t = qvps (\<lambda>s. X s \<omega>) t"
        by (rule qvps_cong) (use taut in simp)
      moreover have "A (min t (tau n \<omega>)) \<omega> = A t \<omega>" using taut by simp
      ultimately show "qvps (\<lambda>s. X s \<omega>) t = A t \<omega>" using key[OF t, of n] by simp
    qed
  qed
qed

subsection \<open>T3 without the boundedness hypothesis\<close>

text \<open>The polarisation of T3, run through the localised scalar theorem.  The
  hypotheses are pointwise on \<open>space M\<close> rather than almost everywhere, which is
  what the stopping arguments need; the intended application reaches that form
  through the \<open>restrict_full\<close> package of
  @{theory Relative_Arbitrage.Stopped_Localization}.\<close>

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
  shows "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
     qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2)"
proof -
  interpret P: prob_space M by (rule P)
  have pol: "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
      qvps (\<lambda>s. X s \<omega> $ i + c * (X s \<omega> $ j)) t
        = A t \<omega> $ i $ i + c * (A t \<omega> $ i $ j + A t \<omega> $ j $ i)
          + c\<^sup>2 * (A t \<omega> $ j $ j)"
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
    have "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow> qvps (\<lambda>s. Y s \<omega>) t = G t \<omega>"
      by (rule qvps_eq_A_localised
            [OF P mgY sqY contY mgZ G0 Grate _ _ Y0]) (use C0 B0 in auto)
    then show ?thesis unfolding Y_def G_def .
  qed
  have c1: "\<bar>(1::real)\<bar> \<le> 1" by simp
  have cm1: "\<bar>(- 1::real)\<bar> \<le> 1" by simp
  have all1: "AE \<omega> in M. \<forall>i \<in> (UNIV :: 'n set). \<forall>j \<in> (UNIV :: 'n set). \<forall>t.
      0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j) t
        = A t \<omega> $ i $ i + (A t \<omega> $ i $ j + A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
    by (intro AE_finite_allI; use pol[OF c1] in simp)
  have all2: "AE \<omega> in M. \<forall>i \<in> (UNIV :: 'n set). \<forall>j \<in> (UNIV :: 'n set). \<forall>t.
      0 \<le> t \<longrightarrow> qvps (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j) t
        = A t \<omega> $ i $ i + (- A t \<omega> $ i $ j - A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
    by (intro AE_finite_allI; use pol[OF cm1] in simp)
  from all1 all2 show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix t :: real assume t: "0 \<le> t"
      have e1: "qvps (\<lambda>s. X s \<omega> $ i + X s \<omega> $ j) t
          = A t \<omega> $ i $ i + (A t \<omega> $ i $ j + A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
        for i j using elim(1) t by blast
      have e2: "qvps (\<lambda>s. X s \<omega> $ i - X s \<omega> $ j) t
          = A t \<omega> $ i $ i + (- A t \<omega> $ i $ j - A t \<omega> $ j $ i) + A t \<omega> $ j $ j"
        for i j using elim(2) t by blast
      have ent: "qvmat (\<lambda>s. X s \<omega>) t $ i $ j = (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2"
        for i j by (simp add: qvmat_def e1 e2)
      show "qvmat (\<lambda>s. X s \<omega>) t = (\<chi> i. \<chi> j. (A t \<omega> $ i $ j + A t \<omega> $ j $ i) / 2)"
        by (simp add: vec_eq_iff ent)
    qed
  qed
qed

subsection \<open>T5: the paper's class and value function\<close>

text \<open>
  Eq. (1.6)--(1.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> as the paper states them: laws of
  the \<open>R\<^sup>n\<close>-valued path alone.  The covariation enters existentially, through a
  compensator \<open>A\<close> whose difference quotients lie in the constraint set --- which
  is what \<open>d\<langle>X\<rangle>(t)/dt \<in> S\<^sub>k\<^sup>L\<close> says once \<open>\<langle>X\<rangle>\<close> is read as the compensator of
  \<open>X X\<^sup>T\<close>.
\<close>

definition xclass ::
  "nat \<Rightarrow> real \<Rightarrow> real^'n::finite \<Rightarrow> ((real \<Rightarrow> real^'n) measure) set"
  where
  "xclass k L x = {Q.
     prob_space Q \<and>
     sets Q = sets (ipath_space :: ((real \<Rightarrow> real^'n) measure)) \<and>
     (AE w in Q. w 0 = x) \<and>
     martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0 (\<lambda>t w. w t) \<and>
     (\<exists>A. (AE w in Q. A 0 w = 0) \<and>
          martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
            (\<lambda>t w. outerp (w t) - A t w) \<and>
          (AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
             (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L))}"

definition xval ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "xval k L K x = Sup ((\<lambda>Q. ess_inf_enn Q (iexit K)) ` xclass k L x)"

lemma xclass_prob: "Q \<in> xclass k L x \<Longrightarrow> prob_space Q"
  unfolding xclass_def by blast

lemma xclass_sets:
  "Q \<in> xclass k L x \<Longrightarrow> sets Q = sets (ipath_space :: ((real \<Rightarrow> real^'n::finite) measure))"
  unfolding xclass_def by blast

lemma xclass_start: "Q \<in> xclass k L x \<Longrightarrow> AE w in Q. w 0 = x"
  unfolding xclass_def by blast

lemma xclass_martingale:
  "Q \<in> xclass k L x \<Longrightarrow>
     martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0 (\<lambda>t w. w t)"
  unfolding xclass_def by blast

lemma xclass_compensator:
  assumes "Q \<in> xclass k L x"
  obtains A where "AE w in Q. A 0 w = 0"
    and "martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
           (\<lambda>t w. outerp (w t) - A t w)"
    and "AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
           (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L"
  using assms unfolding xclass_def by blast

text \<open>The constraint set supplies exactly the two hypotheses the matrix locale
  of @{theory Relative_Arbitrage.Continuous_QV} needs and the plan never named:
  the increments of \<open>A\<close> are positive semidefinite, and their entries are
  Lipschitz in time.\<close>

lemma sconstraint_psd_quadform:
  assumes a: "a \<in> sconstraint k L"
  shows "0 \<le> y \<bullet> (a *v y)"
  using a by (simp add: sconstraint_def Pi_constraint_def psd_def)

subsection \<open>T6: pulling a natural filtration back along a pushforward\<close>

text \<open>The \<open>pull\<close> hypothesis of \<open>martingale_distr\<close> in the case that matters here:
  the target filtration is the natural one of the coordinate process.  Then it
  is enough that each coordinate of the composed map is measurable at the right
  level --- the generator of a natural filtration is exactly the family of
  preimages of the coordinates.\<close>

lemma natural_filtration_pull:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> 'c :: {second_countable_topology, banach}"
  assumes into: "\<And>\<omega>. \<omega> \<in> space (FF u) \<Longrightarrow> \<phi> \<omega> \<in> space N"
    and comp: "\<And>v. 0 \<le> v \<Longrightarrow> v \<le> u \<Longrightarrow> (\<lambda>\<omega>. Y v (\<phi> \<omega>)) \<in> borel_measurable (FF u)"
  shows "\<phi> \<in> FF u \<rightarrow>\<^sub>M natural_filtration N (0::real) Y u"
proof (rule measurable_sigma_sets)
  show "sets (natural_filtration N 0 Y u)
      = sigma_sets (space N) (\<Union>v\<in>{0..u}. {Y v -` A \<inter> space N | A. A \<in> borel})"
    by (rule sets_natural_filtration)
  show "(\<Union>v\<in>{0..u}. {Y v -` A \<inter> space N | A. A \<in> borel}) \<subseteq> Pow (space N)" by blast
  show "\<phi> \<in> space (FF u) \<rightarrow> space N" using into by blast
  fix S assume "S \<in> (\<Union>v\<in>{0..u}. {Y v -` A \<inter> space N | A. A \<in> borel})"
  then obtain v A where v: "0 \<le> v" "v \<le> u" and A: "A \<in> sets borel"
    and S: "S = Y v -` A \<inter> space N" by auto
  have "\<phi> -` S \<inter> space (FF u) = (\<lambda>\<omega>. Y v (\<phi> \<omega>)) -` A \<inter> space (FF u)"
    unfolding S using into by auto
  also have "\<dots> \<in> sets (FF u)"
    using comp[OF v] A by (rule measurable_sets)
  finally show "\<phi> -` S \<inter> space (FF u) \<in> sets (FF u)" .
qed

subsection \<open>What the constraint set gives the matrix hypotheses\<close>

text \<open>Positive semidefiniteness of the difference quotients is the
  monotonicity hypothesis, the eigenvalue upper bound is the Lipschitz one, and
  symmetry --- part of \<open>psd\<close> --- is what turns the symmetric part delivered by
  polarisation back into \<open>A\<close> itself.\<close>

lemma diffquot_psd:
  fixes A :: "real \<Rightarrow> real^'n::finite^'n"
  assumes dq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (A t - A s) \<in> sconstraint k L"
    and p: "0 \<le> p" and pq: "p \<le> q"
  shows "0 \<le> y \<bullet> ((A q - A p) *v y)"
proof (cases "p < q")
  case True
  then have "(1 / (q - p)) *\<^sub>R (A q - A p) \<in> sconstraint k L" using dq p by blast
  then have "psd ((1 / (q - p)) *\<^sub>R (A q - A p))"
    by (simp add: sconstraint_def Pi_constraint_def)
  then have nn: "0 \<le> y \<bullet> (((1 / (q - p)) *\<^sub>R (A q - A p)) *v y)" by (simp add: psd_def)
  have eq: "y \<bullet> (((1 / (q - p)) *\<^sub>R (A q - A p)) *v y)
      = (y \<bullet> ((A q - A p) *v y)) / (q - p)"
    by (simp add: scaleR_matrix_vector_assoc[symmetric])
  from nn have "0 \<le> (y \<bullet> ((A q - A p) *v y)) / (q - p)" unfolding eq .
  then show ?thesis using True by (simp add: zero_le_divide_iff)
next
  case False
  then have "p = q" using pq by simp
  then show ?thesis by simp
qed

lemma diffquot_entry:
  fixes A :: "real \<Rightarrow> real^'n::finite^'n"
  assumes dq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (A t - A s) \<in> sconstraint k L"
    and p: "0 \<le> p" and pq: "p \<le> q"
  shows "\<bar>A q $ i $ j - A p $ i $ j\<bar> \<le> L * (q - p)"
proof (cases "p < q")
  case True
  then have mem: "(1 / (q - p)) *\<^sub>R (A q - A p) \<in> sconstraint k L" using dq p by blast
  then have "psd ((1 / (q - p)) *\<^sub>R (A q - A p))"
    and "eigen_ub ((1 / (q - p)) *\<^sub>R (A q - A p)) L"
    by (auto simp: sconstraint_def Pi_constraint_def)
  from psd_eigen_ub_entry_abs_le[OF this, of i j]
  have "\<bar>(1 / (q - p)) * (A q $ i $ j - A p $ i $ j)\<bar> \<le> L" by simp
  then have "(1 / (q - p)) * \<bar>A q $ i $ j - A p $ i $ j\<bar> \<le> L"
    using True by (simp add: abs_mult)
  then show ?thesis using True by (simp add: field_simps)
next
  case False
  then have "p = q" using pq by simp
  then show ?thesis by simp
qed

lemma diffquot_sym:
  fixes A :: "real \<Rightarrow> real^'n::finite^'n"
  assumes dq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> (1 / (t - s)) *\<^sub>R (A t - A s) \<in> sconstraint k L"
    and A0: "A 0 = 0" and t: "0 \<le> t"
  shows "A t $ i $ j = A t $ j $ i"
proof (cases "0 < t")
  case True
  then have "(1 / (t - 0)) *\<^sub>R (A t - A 0) \<in> sconstraint k L" using dq by blast
  then have "psd ((1 / t) *\<^sub>R A t)" using A0 by (simp add: sconstraint_def Pi_constraint_def)
  then have tr: "transpose ((1 / t) *\<^sub>R A t) = (1 / t) *\<^sub>R A t" by (simp add: psd_def)
  have "transpose ((1 / t) *\<^sub>R A t) $ i $ j = ((1 / t) *\<^sub>R A t) $ i $ j"
    by (simp add: tr)
  then have "(1 / t) * (A t $ j $ i) = (1 / t) * (A t $ i $ j)"
    by (simp add: transpose_def)
  then show ?thesis using True by simp
next
  case False
  then have "t = 0" using t by simp
  then show ?thesis using A0 by simp
qed

subsection \<open>The second coordinate of a class member IS the quadratic variation\<close>

text \<open>Obligation (b) of the bridge.  The class states its side conditions almost
  everywhere, while the localised identification wants them pointwise; the two
  are reconciled by restricting to a full-measure event, which is what the
  \<open>restrict_full\<close> package of @{theory Relative_Arbitrage.Stopped_Localization}
  is for.  The event is built from null sets rather than from the conditions
  themselves, so nothing has to be shown measurable --- in particular not the
  difference-quotient condition, which quantifies over all real pairs.\<close>

theorem iexit_class_qvmat:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x" and L: "0 \<le> L"
  shows "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow> qvmat (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
proof -
  interpret PP: prob_space P by (rule iexit_class_prob[OF P])
  let ?F = "natural_filtration P 0 (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
  have spP: "space P = (ipath :: ('n pairpath) set)"
    using iexit_class_sets[OF P] by (simp add: sets_eq_imp_space_eq)
  have mgX: "martingale P ?F 0 (\<lambda>t \<omega>. fst (\<omega> t) :: real^'n)"
    by (rule iexit_class_X_martingale[OF P])
  have mgXA: "martingale P ?F 0 (\<lambda>t \<omega>. outerp (fst (\<omega> t)) - snd (\<omega> t))"
    using P unfolding iexit_class_def by blast

  text \<open>A full-measure event on which the side conditions hold pointwise.\<close>
  from iexit_class_start[OF P] obtain N1 where
    N1: "{\<omega> \<in> space P. \<not> (fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0)} \<subseteq> N1"
    and N1e: "emeasure P N1 = 0" and N1s: "N1 \<in> sets P" by (rule AE_E)
  from iexit_class_diffquot[OF P] obtain N2 where
    N2: "{\<omega> \<in> space P. \<not> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
            (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L)} \<subseteq> N2"
    and N2e: "emeasure P N2 = 0" and N2s: "N2 \<in> sets P" by (rule AE_E)
  have N1n: "N1 \<in> null_sets P" using N1e N1s by (simp add: null_sets_def)
  have N2n: "N2 \<in> null_sets P" using N2e N2s by (simp add: null_sets_def)
  define G where "G = space P - (N1 \<union> N2)"
  have Nsets: "N1 \<union> N2 \<in> sets P" using N1s N2s by simp
  have Gsets: "G \<in> sets P" unfolding G_def using Nsets by simp
  have Gfull: "AE \<omega> in P. \<omega> \<in> G"
  proof (rule AE_I[where N = "N1 \<union> N2"])
    show "{\<omega> \<in> space P. \<omega> \<notin> G} \<subseteq> N1 \<union> N2" unfolding G_def by blast
    show "emeasure P (N1 \<union> N2) = 0"
      using N1n N2n by (simp add: null_sets_def emeasure_Un_null_set)
    show "N1 \<union> N2 \<in> sets P" by (rule Nsets)
  qed
  have Gspace: "G \<subseteq> space P" unfolding G_def by blast
  have Gstart: "fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0" if "\<omega> \<in> G" for \<omega>
    using N1 that unfolding G_def by blast
  have Gdq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L" if "\<omega> \<in> G" for \<omega>
    using N2 that unfolding G_def by blast

  text \<open>On the restricted space every hypothesis of the localised matrix
    identification holds pointwise.\<close>
  let ?M = "restrict_space P G"
  let ?FF = "\<lambda>t. restrict_space (?F t) G"
  have spM: "space ?M = G"
    by (rule space_restrict_full[OF PP.prob_space_axioms Gsets Gfull])
  have Xc: "martingale ?M ?FF 0 (\<lambda>v \<omega>. fst (\<omega> v) $ i)" for i
    by (rule martingale_restrict_full[OF PP.prob_space_axioms Gsets Gfull
          martingale_vec_nth[OF mgX]])
  have XAc: "martingale ?M ?FF 0 (\<lambda>v \<omega>. fst (\<omega> v) $ i * fst (\<omega> v) $ j
      - snd (\<omega> v) $ i $ j)" for i j
  proof -
    have "martingale P ?F 0 (\<lambda>v \<omega>. (outerp (fst (\<omega> v)) - snd (\<omega> v)) $ i $ j)"
      by (rule martingale_mat_nth[OF mgXA])
    then have "martingale P ?F 0
        (\<lambda>v \<omega>. fst (\<omega> v) $ i * fst (\<omega> v) $ j - snd (\<omega> v) $ i $ j)"
      by (simp add: outerp_def)
    then show ?thesis
      by (rule martingale_restrict_full[OF PP.prob_space_axioms Gsets Gfull])
  qed
  have contc: "continuous_on {0..} (\<lambda>s. fst (\<omega> s) $ i)" if w: "\<omega> \<in> space ?M" for \<omega> i
  proof -
    have "\<omega> \<in> ipath" using w Gspace spM spP by auto
    then have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
    have g: "continuous_on UNIV (\<lambda>p :: (real^'n) \<times> (real^'n^'n). fst p $ i)"
      by (intro continuous_intros)
    show ?thesis by (rule continuous_on_compose2[OF g c]) auto
  qed
  have A0c: "snd (\<omega> 0) = 0" if "\<omega> \<in> space ?M" for \<omega>
    using Gstart that spM by simp
  have psdc: "\<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
      (\<forall>y. 0 \<le> y \<bullet> ((snd (\<omega> q) - snd (\<omega> p)) *v y))" if w: "\<omega> \<in> space ?M" for \<omega>
  proof (intro allI impI)
    fix p q :: real and y :: "real^'n"
    assume pq: "0 \<le> p" "p \<le> q"
    show "0 \<le> y \<bullet> ((snd (\<omega> q) - snd (\<omega> p)) *v y)"
      using diffquot_psd[where A = "\<lambda>t. snd (\<omega> t)" and k = k and L = L
              and p = p and q = q and y = y] Gdq[of \<omega>] w spM pq by simp
  qed
  have ratec: "\<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
      \<bar>snd (\<omega> q) $ i $ j - snd (\<omega> p) $ i $ j\<bar> \<le> L * (q - p)"
    if w: "\<omega> \<in> space ?M" for \<omega>
  proof (intro allI impI)
    fix p q :: real and i j assume pq: "0 \<le> p" "p \<le> q"
    show "\<bar>snd (\<omega> q) $ i $ j - snd (\<omega> p) $ i $ j\<bar> \<le> L * (q - p)"
      using diffquot_entry[where A = "\<lambda>t. snd (\<omega> t)" and k = k and L = L
              and p = p and q = q and i = i and j = j] Gdq[of \<omega>] w spM pq by simp
  qed
  have X0c: "\<bar>fst (\<omega> 0) $ i\<bar> \<le> norm x" if "\<omega> \<in> space ?M" for \<omega> i
    using Gstart that spM by (simp add: component_le_norm_cart)

  have key: "AE \<omega> in ?M. \<forall>t. 0 \<le> t \<longrightarrow>
      qvmat (\<lambda>s. fst (\<omega> s)) t
        = (\<chi> i. \<chi> j. (snd (\<omega> t) $ i $ j + snd (\<omega> t) $ j $ i) / 2)"
  proof (rule qvmat_eq_A_localised[where M = ?M and F = ?FF
           and X = "\<lambda>v \<omega>. fst (\<omega> v)" and A = "\<lambda>v \<omega>. snd (\<omega> v)"
           and C = L and B = "norm x"])
    show "prob_space ?M"
      by (rule prob_space_restrict_full[OF PP.prob_space_axioms Gsets Gfull])
    show "\<And>i. martingale ?M ?FF 0 (\<lambda>v \<omega>. fst (\<omega> v) $ i)" by (rule Xc)
    show "\<And>i j. martingale ?M ?FF 0
        (\<lambda>v \<omega>. fst (\<omega> v) $ i * fst (\<omega> v) $ j - snd (\<omega> v) $ i $ j)" by (rule XAc)
    show "\<And>\<omega> i. \<omega> \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. fst (\<omega> s) $ i)"
      by (rule contc)
    show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> snd (\<omega> 0) = 0" by (rule A0c)
    show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        (\<forall>y. 0 \<le> y \<bullet> ((snd (\<omega> q) - snd (\<omega> p)) *v y))" by (rule psdc)
    show "\<And>\<omega>. \<omega> \<in> space ?M \<Longrightarrow> \<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        \<bar>snd (\<omega> q) $ i $ j - snd (\<omega> p) $ i $ j\<bar> \<le> L * (q - p)" by (rule ratec)
    show "0 \<le> L" by (rule L)
    show "0 \<le> norm x" by simp
    show "\<And>\<omega> i. \<omega> \<in> space ?M \<Longrightarrow> \<bar>fst (\<omega> 0) $ i\<bar> \<le> norm x" by (rule X0c)
  qed

  text \<open>Symmetry collapses the symmetric part back to \<open>A\<close> itself.\<close>
  have spAE: "AE \<omega> in ?M. \<omega> \<in> space ?M" by (rule AE_I2) simp
  have sym: "AE \<omega> in ?M. \<forall>t. 0 \<le> t \<longrightarrow> qvmat (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
    using key spAE
  proof eventually_elim
    case (elim \<omega>)
    then have "\<omega> \<in> G" using spM by simp
    then have s: "snd (\<omega> t) $ i $ j = snd (\<omega> t) $ j $ i" if "0 \<le> t" for t i j
      using diffquot_sym[where A = "\<lambda>u. snd (\<omega> u)" and k = k and L = L
              and t = t and i = i and j = j] Gdq[of \<omega>] Gstart[of \<omega>] that by simp
    show ?case
    proof (intro allI impI)
      fix t :: real assume t: "0 \<le> t"
      have "(\<chi> i. \<chi> j. (snd (\<omega> t) $ i $ j + snd (\<omega> t) $ j $ i) / 2) = snd (\<omega> t)"
        by (simp add: vec_eq_iff s[OF t])
      then show "qvmat (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)" using elim t by simp
    qed
  qed

  have "AE \<omega> in P. \<omega> \<in> G \<longrightarrow> (\<forall>t. 0 \<le> t \<longrightarrow> qvmat (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t))"
    using sym Gsets Gspace
    by (subst (asm) AE_restrict_space_iff) (auto simp: Int_absorb2)
  with Gfull show ?thesis by eventually_elim blast
qed

subsection \<open>A continuous version of the scalar functional\<close>

text \<open>
  The pushforward into the pair space needs the second coordinate to be a
  CONTINUOUS path for EVERY path, not merely almost every one, and transferring
  an almost-everywhere statement along a pushforward needs the exceptional set
  to be measurable.  Both are settled at once by cutting the functional down to
  the event where its rational-time data is nondecreasing and Lipschitz.  That
  event is a countable condition, hence measurable; and on it the \<open>limsup\<close>
  extension --- a supremum over rationals below \<open>t\<close> --- inherits the two
  properties, so it is Lipschitz on \<open>{0..}\<close> and therefore continuous.
\<close>

definition qvp_good :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "qvp_good C w \<longleftrightarrow> qvp w 0 = 0 \<and>
     (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        0 \<le> qvp w (real_of_rat q) - qvp w (real_of_rat p) \<and>
        qvp w (real_of_rat q) - qvp w (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))"

lemma qvp_good_nonneg:
  assumes g: "qvp_good C w" and q: "0 \<le> (q :: rat)"
  shows "0 \<le> qvp w (real_of_rat q)"
  using g q unfolding qvp_good_def by (metis diff_ge_0_iff_ge of_rat_0 order_refl)

lemma qvp_good_ub:
  assumes g: "qvp_good C w" and q: "0 \<le> (q :: rat)"
  shows "qvp w (real_of_rat q) \<le> C * real_of_rat q"
proof -
  have "qvp w (real_of_rat q) - qvp w (real_of_rat 0)
      \<le> C * (real_of_rat q - real_of_rat 0)"
    using g q unfolding qvp_good_def by blast
  then show ?thesis using g unfolding qvp_good_def by simp
qed

lemma qvps_as_Sup:
  assumes g: "qvp_good C w" and C: "0 \<le> C" and t: "0 < t"
  shows "qvps w t
       = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t})"
proof -
  define Q where "Q = {q :: rat. 0 \<le> q \<and> real_of_rat q < t}"
  have ne: "Q \<noteq> {}"
  proof -
    obtain q :: rat where "0 < real_of_rat q" "real_of_rat q < t"
      using t of_rat_dense[of 0 t] by auto
    then show ?thesis unfolding Q_def by (auto simp: less_le)
  qed
  have ub: "qvp w (real_of_rat q) \<le> C * t" if "q \<in> Q" for q
  proof -
    have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
      using that qvp_good_ub[OF g] unfolding Q_def by simp
    also have "\<dots> \<le> C * t" using that C unfolding Q_def by (intro mult_left_mono) auto
    finally show ?thesis .
  qed
  have bdd: "bdd_above ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` Q)"
    using ub by (intro bdd_aboveI2) blast
  have fin: "\<bar>SUP q \<in> Q. ereal (qvp w (real_of_rat q))\<bar> \<noteq> \<infinity>"
  proof -
    have le: "(SUP q \<in> Q. ereal (qvp w (real_of_rat q))) \<le> ereal (C * t)"
      using ub by (intro SUP_least) simp
    obtain q0 where q0: "q0 \<in> Q" using ne by blast
    have ge: "ereal (qvp w (real_of_rat q0))
        \<le> (SUP q \<in> Q. ereal (qvp w (real_of_rat q)))"
      using q0 by (rule SUP_upper)
    show ?thesis
    proof (cases "SUP q \<in> Q. ereal (qvp w (real_of_rat q))" rule: ereal_cases)
      case (real r) then show ?thesis by simp
    next
      case PInf then show ?thesis using le by simp
    next
      case MInf then show ?thesis using ge by simp
    qed
  qed
  have E: "ereal (Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` Q))
      = (SUP q \<in> Q. ereal (qvp w (real_of_rat q)))"
    by (rule ereal_SUP[OF fin])
  show ?thesis unfolding qvps_def Q_def[symmetric] by (simp add: E[symmetric])
qed

lemma qvps_mono_lip:
  assumes g: "qvp_good C w" and C: "0 \<le> C" and s: "0 \<le> s" and st: "s \<le> t"
  shows "0 \<le> qvps w t - qvps w s \<and> qvps w t - qvps w s \<le> C * (t - s)"
proof (cases "0 < s")
  case False
  then have s0: "s = 0" using s by simp
  then have qs: "qvps w s = 0" by simp
  show ?thesis
  proof (cases "0 < t")
    case True
    have img: "qvps w t
        = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t})"
      by (rule qvps_as_Sup[OF g C True])
    have ne: "{q :: rat. 0 \<le> q \<and> real_of_rat q < t} \<noteq> {}"
    proof -
      obtain q :: rat where "0 < real_of_rat q" "real_of_rat q < t"
        using True of_rat_dense[of 0 t] by auto
      then show ?thesis by (auto simp: less_le)
    qed
    have le: "qvp w (real_of_rat q) \<le> C * t"
      if "q \<in> {q :: rat. 0 \<le> q \<and> real_of_rat q < t}" for q
    proof -
      have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
        using that qvp_good_ub[OF g] by simp
      also have "\<dots> \<le> C * t" using that C by (intro mult_left_mono) auto
      finally show ?thesis .
    qed
    have nn: "0 \<le> qvps w t"
    proof -
      obtain q0 :: rat where q0: "q0 \<in> {q. 0 \<le> q \<and> real_of_rat q < t}"
        using ne by blast
      have a: "0 \<le> qvp w (real_of_rat q0)"
        using q0 qvp_good_nonneg[OF g] by simp
      have b: "qvp w (real_of_rat q0) \<le> qvps w t"
        unfolding img
        by (rule cSup_upper[OF imageI[OF q0]]) (use le in \<open>auto intro!: bdd_aboveI2\<close>)
      show ?thesis using a b by simp
    qed
    have ub: "qvps w t \<le> C * t"
      unfolding img using ne le by (intro cSup_least) auto
    show ?thesis using qs nn ub s0 by simp
  next
    case False
    then show ?thesis using qs st s0 by simp
  qed
next
  case True
  then have t: "0 < t" using st by simp
  have imgs: "qvps w s
      = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < s})"
    by (rule qvps_as_Sup[OF g C True])
  have imgt: "qvps w t
      = Sup ((\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t})"
    by (rule qvps_as_Sup[OF g C t])
  have bddt: "bdd_above ((\<lambda>q :: rat. qvp w (real_of_rat q))
      ` {q. 0 \<le> q \<and> real_of_rat q < t})"
  proof (intro bdd_aboveI2)
    fix q :: rat assume "q \<in> {q. 0 \<le> q \<and> real_of_rat q < t}"
    then have "qvp w (real_of_rat q) \<le> C * real_of_rat q"
      using qvp_good_ub[OF g] by simp
    also have "\<dots> \<le> C * t"
      using \<open>q \<in> _\<close> C by (intro mult_left_mono) auto
    finally show "qvp w (real_of_rat q) \<le> C * t" .
  qed
  have nes: "{q :: rat. 0 \<le> q \<and> real_of_rat q < s} \<noteq> {}"
  proof -
    obtain q :: rat where "0 < real_of_rat q" "real_of_rat q < s"
      using True of_rat_dense[of 0 s] by auto
    then show ?thesis by (auto simp: less_le)
  qed
  have mono: "qvps w s \<le> qvps w t"
    unfolding imgs imgt
  proof (rule cSup_subset_mono)
    show "(\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < s} \<noteq> {}"
      using nes by blast
    show "bdd_above ((\<lambda>q :: rat. qvp w (real_of_rat q))
        ` {q. 0 \<le> q \<and> real_of_rat q < t})" by (rule bddt)
    show "(\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < s}
        \<subseteq> (\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t}"
      using st by auto
  qed
  have lip: "qvps w t \<le> qvps w s + C * (t - s)"
    unfolding imgt
  proof (intro cSup_least)
    show "(\<lambda>q :: rat. qvp w (real_of_rat q)) ` {q. 0 \<le> q \<and> real_of_rat q < t} \<noteq> {}"
      using t of_rat_dense[of 0 t] by (auto simp: less_le)
    fix y assume "y \<in> (\<lambda>q :: rat. qvp w (real_of_rat q))
        ` {q. 0 \<le> q \<and> real_of_rat q < t}"
    then obtain q :: rat where q: "0 \<le> q" "real_of_rat q < t"
      and y: "y = qvp w (real_of_rat q)" by auto
    show "y \<le> qvps w s + C * (t - s)"
    proof (cases "real_of_rat q < s")
      case True
      then have "q \<in> {q :: rat. 0 \<le> q \<and> real_of_rat q < s}" using q by simp
      then have "y \<le> qvps w s"
        unfolding y imgs
        by (intro cSup_upper bdd_above_mono[OF bddt]) (use st in auto)
      moreover have "0 \<le> C * (t - s)" using C st by simp
      ultimately show ?thesis by simp
    next
      case False
      then have sq: "s \<le> real_of_rat q" by simp
      show ?thesis
      proof (rule field_le_epsilon)
        fix e :: real assume e: "0 < e"
        have pos: "0 < e / (C + 1)" using e C by simp
        obtain p :: rat where p1: "max 0 (s - e / (C + 1)) < real_of_rat p"
          and p2: "real_of_rat p < s"
          using of_rat_dense[of "max 0 (s - e / (C + 1))" s] pos \<open>0 < s\<close> by auto
        have p0: "0 \<le> p"
        proof -
          have "0 < real_of_rat p" using p1 by simp
          then show ?thesis by simp
        qed
        have pq: "p \<le> q"
        proof -
          have "real_of_rat p \<le> real_of_rat q" using p2 sq by simp
          then show ?thesis by (simp add: of_rat_less_eq)
        qed
        have d1: "y - qvp w (real_of_rat p) \<le> C * (real_of_rat q - real_of_rat p)"
          using g p0 pq unfolding qvp_good_def y by blast
        have d2: "qvp w (real_of_rat p) \<le> qvps w s"
          using p0 p2 unfolding imgs
          by (intro cSup_upper bdd_above_mono[OF bddt]) (use st in auto)
        have d3: "real_of_rat q - real_of_rat p \<le> (t - s) + e / (C + 1)"
          using q p1 by simp
        have d4: "C * (real_of_rat q - real_of_rat p) \<le> C * ((t - s) + e / (C + 1))"
          by (rule mult_left_mono[OF d3 C])
        have "y \<le> qvps w s + C * ((t - s) + e / (C + 1))"
          using d1 d2 d4 by simp
        moreover have "C * ((t - s) + e / (C + 1)) \<le> C * (t - s) + e"
        proof -
          have "C * (e / (C + 1)) \<le> (C + 1) * (e / (C + 1))"
            using pos by (intro mult_right_mono) auto
          also have "\<dots> = e" using C by simp
          finally show ?thesis by (simp add: algebra_simps)
        qed
        ultimately show "y \<le> qvps w s + C * (t - s) + e" by simp
      qed
    qed
  qed
  show ?thesis using mono lip by simp
qed

lemma qvps_continuous:
  assumes g: "qvp_good C w" and C: "0 \<le> C"
  shows "continuous_on {0..} (qvps w)"
proof -
  have "C-lipschitz_on {0..} (qvps w)"
  proof (rule lipschitz_onI)
    show "0 \<le> C" by (rule C)
    fix a b :: real assume ab: "a \<in> {0..}" "b \<in> {0..}"
    show "dist (qvps w a) (qvps w b) \<le> C * dist a b"
    proof (cases "a \<le> b")
      case True
      with qvps_mono_lip[OF g C, of a b] ab show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff) linarith?
    next
      case False
      with qvps_mono_lip[OF g C, of b a] ab show ?thesis
        by (simp add: dist_real_def abs_diff_le_iff) linarith?
    qed
  qed
  then show ?thesis by (rule lipschitz_on_continuous_on)
qed

subsection \<open>The cut-down functional, scalar and matrix\<close>

text \<open>Off the good event the functional is set to \<open>0\<close>, which is continuous; on
  it, \<open>qvps_continuous\<close> applies.  So \<open>qvsc\<close> is continuous in \<open>t\<close> for EVERY path,
  which is what the pushforward into the pair space needs, and it stays Borel
  because the good event is measurable.\<close>

definition qvsc :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "qvsc C w t = (if qvp_good C w then qvps w t else 0)"

lemma qvsc_continuous:
  assumes C: "0 \<le> C"
  shows "continuous_on {0..} (qvsc C w)"
proof (cases "qvp_good C w")
  case True
  then have "qvsc C w = qvps w" by (simp add: qvsc_def fun_eq_iff)
  then show ?thesis using qvps_continuous[OF True C] by simp
next
  case False
  then have "qvsc C w = (\<lambda>t. 0)" by (simp add: qvsc_def fun_eq_iff)
  then show ?thesis by simp
qed

lemma qvp_good_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real" and N :: "'b measure"
  assumes Y: "\<And>s. 0 \<le> s \<Longrightarrow> Y s \<in> borel_measurable N"
  shows "Measurable.pred N (\<lambda>\<omega>. qvp_good C (\<lambda>s. Y s \<omega>))"
proof -
  have m: "(\<lambda>\<omega>. qvp (\<lambda>s. Y s \<omega>) (real_of_rat r)) \<in> borel_measurable N"
    if r: "0 \<le> (r :: rat)" for r
  proof (rule qvp_measurable)
    show "0 \<le> real_of_rat r" using r by simp
    fix s assume s: "0 \<le> s" and "s \<le> real_of_rat r"
    show "Y s \<in> borel_measurable N" by (rule Y[OF s])
  qed
  have m0 [measurable]: "(\<lambda>\<omega>. qvp (\<lambda>s. Y s \<omega>) 0) \<in> borel_measurable N"
    using m[of 0] by simp
  have inner: "Measurable.pred N (\<lambda>\<omega>. \<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
      0 \<le> qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p) \<and>
      qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p)
        \<le> C * (real_of_rat q - real_of_rat p))"
  proof (intro pred_intros_countable)
    fix p q :: rat
    show "Measurable.pred N (\<lambda>\<omega>. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        0 \<le> qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p) \<and>
        qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p)
          \<le> C * (real_of_rat q - real_of_rat p))"
    proof (cases "0 \<le> p \<and> p \<le> q")
      case True
      then have p: "0 \<le> p" and pq: "p \<le> q" by auto
      then have q: "0 \<le> q" by simp
      note [measurable] = m[OF p] m[OF q]
      show ?thesis by measurable
    next
      case False
      then show ?thesis by simp
    qed
  qed
  have "Measurable.pred N (\<lambda>\<omega>. qvp (\<lambda>s. Y s \<omega>) 0 = 0 \<and>
      (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
         0 \<le> qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p) \<and>
         qvp (\<lambda>s. Y s \<omega>) (real_of_rat q) - qvp (\<lambda>s. Y s \<omega>) (real_of_rat p)
           \<le> C * (real_of_rat q - real_of_rat p)))"
    using inner by measurable
  then show ?thesis unfolding qvp_good_def by simp
qed

lemma qvsc_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real" and N :: "'b measure"
  assumes Y: "\<And>s. 0 \<le> s \<Longrightarrow> Y s \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. qvsc C (\<lambda>s. Y s \<omega>) t) \<in> borel_measurable N"
proof -
  have g: "Measurable.pred N (\<lambda>\<omega>. qvp_good C (\<lambda>s. Y s \<omega>))"
    by (rule qvp_good_measurable[OF Y])
  have p: "(\<lambda>\<omega>. qvps (\<lambda>s. Y s \<omega>) t) \<in> borel_measurable N"
    by (rule qvps_measurable) (use Y in simp)
  show ?thesis unfolding qvsc_def using g p by simp
qed

text \<open>The matrix version, assembled by polarisation from the scalar one.  The
  order matters: the SCALAR functionals are the monotone ones, so they are what
  the regularisation of the previous subsection applies to.\<close>

definition qvmatc ::
  "real \<Rightarrow> (real \<Rightarrow> real^'n::finite) \<Rightarrow> real \<Rightarrow> real^'n^'n"
  where
  "qvmatc C w t = (\<chi> i. \<chi> j. (qvsc C (\<lambda>s. w s $ i + w s $ j) t
                              - qvsc C (\<lambda>s. w s $ i + (- 1) * (w s $ j)) t) / 4)"

lemma qvmatc_continuous:
  assumes C: "0 \<le> C"
  shows "continuous_on {0..} (qvmatc C w)"
  unfolding qvmatc_def
  by (intro continuous_on_vec_lambda continuous_intros qvsc_continuous[OF C]) simp

lemma qvmatc_measurable:
  fixes Y :: "real \<Rightarrow> 'b \<Rightarrow> real^'n::finite" and N :: "'b measure"
  assumes Y: "\<And>s i. 0 \<le> s \<Longrightarrow> (\<lambda>\<omega>. Y s \<omega> $ i) \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. qvmatc C (\<lambda>s. Y s \<omega>) t) \<in> borel_measurable N"
proof (rule measurable_mat_entries)
  fix i j :: 'n
  have p: "(\<lambda>\<omega>. qvsc C (\<lambda>s. Y s \<omega> $ i + c * (Y s \<omega> $ j)) t) \<in> borel_measurable N"
    for c by (rule qvsc_measurable) (use Y in simp)
  have "(\<lambda>\<omega>. qvmatc C (\<lambda>s. Y s \<omega>) t $ i $ j)
      = (\<lambda>\<omega>. (qvsc C (\<lambda>s. Y s \<omega> $ i + 1 * (Y s \<omega> $ j)) t
              - qvsc C (\<lambda>s. Y s \<omega> $ i + (- 1) * (Y s \<omega> $ j)) t) / 4)"
    by (simp add: qvmatc_def)
  then show "(\<lambda>\<omega>. qvmatc C (\<lambda>s. Y s \<omega>) t $ i $ j) \<in> borel_measurable N"
    using p[of 1] p[of "- 1"] by simp
qed

text \<open>On the event where every polarised scalar is good, the cut-down matrix
  functional agrees with the original one.\<close>

lemma qvmatc_eq_qvmat:
  assumes "\<And>i j. qvp_good C (\<lambda>s. w s $ i + w s $ j)"
    and "\<And>i j. qvp_good C (\<lambda>s. w s $ i + (- 1) * (w s $ j))"
  shows "qvmatc C w t = qvmat w t"
  using assms by (simp add: qvmatc_def qvmat_def qvsc_def)

subsection \<open>The good event has full measure\<close>

text \<open>The cut-down functional is only useful if the cut discards nothing: under
  the hypotheses of T1--T4 the rational-time data of \<open>qvp\<close> IS the compensator,
  so it is nondecreasing and Lipschitz almost surely.  Stated inside the locale,
  where \<open>qvp_eq_A\<close> identifies \<open>qvp\<close> at each fixed time; the rationals are
  countable, so one intersection covers them all.\<close>

lemma (in bounded_martingale_compensator) qvp_good_ae:
  "AE \<omega> in M. qvp_good C (\<lambda>s. X s \<omega>)"
proof -
  have rat: "AE \<omega> in M. \<forall>q :: rat. 0 \<le> q \<longrightarrow>
      qvp (\<lambda>s. X s \<omega>) (real_of_rat q) = A (real_of_rat q) \<omega>"
  proof (subst AE_all_countable, intro allI)
    fix q :: rat
    show "AE \<omega> in M. 0 \<le> q \<longrightarrow>
        qvp (\<lambda>s. X s \<omega>) (real_of_rat q) = A (real_of_rat q) \<omega>"
    proof (cases "0 \<le> q")
      case True
      then have "(0::real) \<le> real_of_rat q" by simp
      from qvp_eq_A[OF this] show ?thesis by eventually_elim simp
    qed simp
  qed
  from rat A0 Arate show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have qeq: "\<And>q :: rat. 0 \<le> q \<Longrightarrow>
        qvp (\<lambda>s. X s \<omega>) (real_of_rat q) = A (real_of_rat q) \<omega>"
      and z: "A 0 \<omega> = 0"
      and rate: "\<And>p r. 0 \<le> p \<Longrightarrow> p \<le> r \<Longrightarrow>
          0 \<le> A r \<omega> - A p \<omega> \<and> A r \<omega> - A p \<omega> \<le> C * (r - p)" by blast+
    show ?case unfolding qvp_good_def
    proof (intro conjI)
      show "qvp (\<lambda>s. X s \<omega>) 0 = 0" using qeq[of 0] z by simp
      show "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
          0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
          \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
              \<le> C * (real_of_rat q - real_of_rat p)"
      proof (intro allI impI)
      fix p q :: rat assume p: "0 \<le> p" and pq: "p \<le> q"
      then have q: "0 \<le> q" by simp
      have pr: "real_of_rat p \<le> real_of_rat q" using pq by (simp add: of_rat_less_eq)
      have p0: "(0::real) \<le> real_of_rat p" using p by simp
      show "0 \<le> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
          \<and> qvp (\<lambda>s. X s \<omega>) (real_of_rat q) - qvp (\<lambda>s. X s \<omega>) (real_of_rat p)
              \<le> C * (real_of_rat q - real_of_rat p)"
        using rate[OF p0 pr] qeq[OF p] qeq[OF q] by simp
      qed
    qed
  qed
qed

(*<*)
end
(*>*)
