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

(*<*)
end
(*>*)
