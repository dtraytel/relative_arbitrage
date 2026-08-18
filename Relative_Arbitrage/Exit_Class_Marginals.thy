section \<open>The \<open>X\<close>-marginals of the exit class\<close>

(*<*)
theory Exit_Class_Marginals
  imports Exit_Class_Infinite "Continuous_Path_Spaces.Adapted_Quadratic_Variation"
    "Continuous_Path_Spaces.Increment_Moments"
    "Continuous_Time_Martingales.Essential_Infimum"
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

text \<open>The adapted continuous version of the quadratic-variation functional
  --- \<open>qvp_good\<close>, \<open>qvp_goodupto\<close>, \<open>qvpc\<close>, \<open>qvsa\<close> and \<open>qvmata\<close> ---
  lives in @{theory Continuous_Path_Spaces.Adapted_Quadratic_Variation}.\<close>

subsection \<open>The identification at one localisation level\<close>

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

subsection \<open>The class \<open>P\<^sub>x\<close> and its value function\<close>

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
  "xval k L K x = Sup ((\<lambda>Q. ess_inf Q (iexit K)) ` xclass k L x)"

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

text \<open>The constraint set supplies exactly the two hypotheses the matrix locale
  of @{theory Continuous_Path_Spaces.Pathwise_Quadratic_Variation} needs and the plan never named:
  the increments of \<open>A\<close> are positive semidefinite, and their entries are
  Lipschitz in time.\<close>

text \<open>\<open>natural_filtration_pull\<close> lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}: the \<open>pull\<close>
  hypothesis of \<open>martingale_distr\<close> in the case that matters here, since the
  target filtration is the natural one of the coordinate process.\<close>

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
  \<open>restrict_full\<close> package of @{theory Continuous_Path_Spaces.Stopped_Localization}
  is for.  The event is built from null sets rather than from the conditions
  themselves, so nothing has to be shown measurable --- in particular not the
  difference-quotient condition, which quantifies over all real pairs.\<close>

theorem iexit_class_qvmat:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x" and L: "0 \<le> L"
  shows "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow>
      qvmata (4 * L) (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
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

  have key: "AE \<omega> in ?M.
      (\<forall>i j. qvp_good (4 * L) (\<lambda>s. fst (\<omega> s) $ i + fst (\<omega> s) $ j)
           \<and> qvp_good (4 * L) (\<lambda>s. fst (\<omega> s) $ i - fst (\<omega> s) $ j))
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvmat (\<lambda>s. fst (\<omega> s)) t
           = (\<chi> i. \<chi> j. (snd (\<omega> t) $ i $ j + snd (\<omega> t) $ j $ i) / 2))"
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
  have L4: "0 \<le> 4 * L" using L by simp
  have sym: "AE \<omega> in ?M. \<forall>t. 0 \<le> t \<longrightarrow>
      qvmata (4 * L) (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
    using key spAE
  proof eventually_elim
    case (elim \<omega>)
    then have gp: "\<And>i j. qvp_good (4 * L) (\<lambda>s. fst (\<omega> s) $ i + fst (\<omega> s) $ j)"
      and gm: "\<And>i j. qvp_good (4 * L) (\<lambda>s. fst (\<omega> s) $ i - fst (\<omega> s) $ j)"
      and ke: "\<And>t. 0 \<le> t \<Longrightarrow> qvmat (\<lambda>s. fst (\<omega> s)) t
          = (\<chi> i. \<chi> j. (snd (\<omega> t) $ i $ j + snd (\<omega> t) $ j $ i) / 2)" by blast+
    from elim have "\<omega> \<in> G" using spM by simp
    then have s: "snd (\<omega> t) $ i $ j = snd (\<omega> t) $ j $ i" if "0 \<le> t" for t i j
      using diffquot_sym[where A = "\<lambda>u. snd (\<omega> u)" and k = k and L = L
              and t = t and i = i and j = j] Gdq[of \<omega>] Gstart[of \<omega>] that by simp
    show ?case
    proof (intro allI impI)
      fix t :: real assume t: "0 \<le> t"
      have "(\<chi> i. \<chi> j. (snd (\<omega> t) $ i $ j + snd (\<omega> t) $ j $ i) / 2) = snd (\<omega> t)"
        by (simp add: vec_eq_iff s[OF t])
      then have "qvmat (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)" using ke[OF t] by simp
      then show "qvmata (4 * L) (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
        using qvmata_eq_qvmat[OF gp gm L4] by simp
    qed
  qed

  have "AE \<omega> in P. \<omega> \<in> G \<longrightarrow>
      (\<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * L) (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t))"
    using sym Gsets Gspace
    by (subst (asm) AE_restrict_space_iff) (auto simp: Int_absorb2)
  with Gfull show ?thesis by eventually_elim blast
qed

subsection \<open>First inclusion: the \<open>X\<close>-marginal of a pair law is a \<open>P\<^sub>x\<close>-law\<close>

text \<open>
  Push a member of the pair class forward along \<open>\<omega> \<mapsto> fst \<circ> \<omega>\<close>.  The compensator
  witnessing membership of the paper's class cannot be the second coordinate ---
  that is not a functional of the \<open>X\<close>-path --- so it has to be \<^const>\<open>qvmata\<close>,
  which the identification says agrees with it almost surely.  This is where
  being ADAPTED earns its keep: \<open>martingale_distr\<close> pulls the natural filtration
  of the image back along the map, and the second component of the map is
  \<^const>\<open>qvmata\<close>.
\<close>

text \<open>\<open>outerp_borel\<close> lives in @{theory Relative_Arbitrage.Exit_Class_Pasting}.\<close>

text \<open>\<open>natural_filtration_eval\<close>, the evaluations of a natural filtration in
  the two shapes the pushforward needs them, lives in
  @{theory Continuous_Time_Martingales.Natural_Filtration}.\<close>

lemma ipath_eval_measurable_sets:
  fixes Q :: "(real \<Rightarrow> 'b::polish_space) measure"
  assumes setsQ: "sets Q = sets (ipath_space :: ((real \<Rightarrow> 'b) measure))" and v: "0 \<le> v"
  shows "(\<lambda>w. w v) \<in> borel_measurable Q"
  unfolding measurable_cong_sets[OF setsQ refl] by (rule ipath_eval_measurable[OF v])

theorem iexit_class_marginal_in_xclass:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x" and L: "0 \<le> L"
  shows "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t)) \<in> xclass k L x"
proof -
  interpret PP: prob_space P by (rule iexit_class_prob[OF P])
  define C where "C = 4 * L"
  have C0: "0 \<le> C" using L by (simp add: C_def)
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. restrict (\<lambda>t. fst (\<omega> t)) {0..}"
  let ?Q = "distr P (ipath_space :: ((real \<Rightarrow> real^'n) measure)) ?\<phi>"
  let ?F = "natural_filtration P 0 (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"

  have spP: "space P = (ipath :: ('n pairpath) set)"
    using iexit_class_sets[OF P] by (simp add: sets_eq_imp_space_eq)
  have evP: "(\<lambda>\<omega> :: 'n pairpath. \<omega> v) \<in> borel_measurable P" if v: "0 \<le> v" for v
    unfolding measurable_cong_sets[OF iexit_class_sets[OF P] refl]
    by (rule ipath_eval_measurable[OF v])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have XmP: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> v)) \<in> borel_measurable P" if v: "0 \<le> v" for v
    by (rule measurable_compose[OF evP[OF v] fstB])
  have contP: "continuous_on {0..} (\<lambda>t. fst (\<omega> t))" if w: "\<omega> \<in> space P" for \<omega>
  proof -
    have "\<omega> \<in> ipath" using w spP by simp
    then have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
    show ?thesis by (rule continuous_on_compose2[OF _ c]) (auto intro: fstB
        continuous_on_fst continuous_on_id)
  qed
  have phim: "?\<phi> \<in> P \<rightarrow>\<^sub>M (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
    by (rule ipathify_measurable[OF XmP contP])
  have into: "?\<phi> \<omega> \<in> ipath" if "\<omega> \<in> space P" for \<omega>
    using measurable_space[OF phim that] by simp

  text \<open>The identification, and the two consequences it has for the image.\<close>
  have keyq: "AE \<omega> in P. \<forall>t. 0 \<le> t \<longrightarrow> qvmata C (\<lambda>s. fst (\<omega> s)) t = snd (\<omega> t)"
    unfolding C_def by (rule iexit_class_qvmat[OF P L])
  have phicong: "qvmata C (?\<phi> \<omega>) t = qvmata C (\<lambda>s. fst (\<omega> s)) t" for \<omega> t
    by (rule qvmata_cong) simp

  text \<open>The two filtration facts that both martingale clauses need.\<close>
  interpret MF: martingale P ?F 0 "\<lambda>t \<omega>. fst (\<omega> t) :: real^'n"
    by (rule iexit_class_X_martingale[OF P])
  have spF: "space (?F u) = space P" if "0 \<le> u" for u by (rule MF.space_F[OF that])
  have GG: "filtered_measure ?Q ?G (0::real)"
  proof -
    interpret PQ: prob_space ?Q by (rule PP.prob_space_distr[OF phim])
    have SQ: "Stochastic_Process.stochastic_process ?Q (0::real)
        (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
      by (unfold_locales) (rule ipath_eval_measurable_sets[OF sets_distr])
    show ?thesis
      by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SQ])
  qed
  have pull: "?\<phi> \<in> ?F u \<rightarrow>\<^sub>M ?G u" if u: "0 \<le> u" for u
  proof (rule natural_filtration_pull)
    fix \<omega> assume "\<omega> \<in> space (?F u)"
    then have "\<omega> \<in> space P" using spF[OF u] by simp
    then show "?\<phi> \<omega> \<in> space ?Q" using into by (simp add: space_distr)
  next
    fix v :: real assume v: "0 \<le> v" and vu: "v \<le> u"
    have e: "(\<lambda>\<omega> :: 'n pairpath. ?\<phi> \<omega> v) = (\<lambda>\<omega>. fst (\<omega> v))" using v by simp
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> v) \<in> borel_measurable (?F u)"
      by (rule natural_filtration_eval[OF v vu])
    then show "(\<lambda>\<omega> :: 'n pairpath. ?\<phi> \<omega> v) \<in> borel_measurable (?F u)"
      unfolding e by (rule measurable_compose[OF _ fstB])
  qed
  have SP: "Stochastic_Process.stochastic_process P (0::real)
      (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
    by (unfold_locales) (rule evP)
  have FM: "filtered_measure P ?F (0::real)"
    by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SP])
  have projB: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI continuous_intros)
  have entB: "(\<lambda>Z :: real^'n^'n. Z $ i $ j) \<in> borel_measurable borel" for i j
    by (intro borel_measurable_continuous_onI continuous_intros)
  have evF: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> v) $ i) \<in> borel_measurable (?F u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v i
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> v) \<in> borel_measurable (?F u)"
      by (rule natural_filtration_eval[OF v vu])
    from measurable_compose[OF this fstB] show ?thesis
      by (rule measurable_compose[OF _ projB])
  qed
  have evG: "(\<lambda>w :: real \<Rightarrow> real^'n. w v $ i) \<in> borel_measurable (?G u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v i
    by (rule measurable_compose[OF natural_filtration_eval[OF v vu] projB])

  text \<open>Clause (i): the initial condition.\<close>
  have predx: "Measurable.pred (ipath_space :: ((real \<Rightarrow> real^'n) measure))
      (\<lambda>w. w 0 = x)"
  proof -
    have m: "(\<lambda>w :: real \<Rightarrow> real^'n. w 0) \<in> borel_measurable ipath_space"
      by (rule ipath_eval_measurable) simp
    have "{w \<in> space (ipath_space :: ((real \<Rightarrow> real^'n) measure)). w 0 = x}
        = (\<lambda>w :: real \<Rightarrow> real^'n. w 0) -` {x} \<inter> space ipath_space" by auto
    also have "\<dots> \<in> sets (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
      by (rule measurable_sets[OF m]) simp
    finally show ?thesis unfolding pred_def by simp
  qed
  have startQ: "AE w in ?Q. w 0 = x"
  proof (subst AE_distr_iff[OF phim predx[unfolded pred_def]])
    show "AE \<omega> in P. ?\<phi> \<omega> 0 = x"
      using iexit_class_start[OF P] by eventually_elim simp
  qed

  text \<open>Clause (ii): the coordinate process is a martingale.\<close>
  have mgX: "martingale P ?F 0 (\<lambda>t \<omega>. fst (\<omega> t) :: real^'n)"
    by (rule iexit_class_X_martingale[OF P])
  have XmgQ: "martingale ?Q ?G 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
  proof (rule martingale_distr[OF PP.prob_space_axioms phim GG pull])
    show "(\<lambda>w :: real \<Rightarrow> real^'n. w u) \<in> borel_measurable (?G u)" if "0 \<le> u" for u
      by (rule natural_filtration_eval[OF that order_refl])
    show "martingale P ?F 0 (\<lambda>u \<omega> :: 'n pairpath. ?\<phi> \<omega> u)"
      by (rule martingale_cong_ge[OF mgX]) simp
  qed

  text \<open>Clause (iii): the compensator vanishes at \<open>0\<close>, for every path.\<close>
  have A0Q: "AE w in ?Q. qvmata C (w :: real \<Rightarrow> real^'n) 0 = 0"
    using C0 by simp

  text \<open>Clause (iv): the compensated process is a martingale.  The composite is
    a modification of the class's own compensated process, and it is adapted
    because \<^const>\<open>qvmata\<close> is.\<close>
  have mgXA: "martingale P ?F 0 (\<lambda>t \<omega>. outerp (fst (\<omega> t) :: real^'n) - snd (\<omega> t))"
    by (rule iexit_class_comp_martingale[OF P])
  have qmP: "(\<lambda>\<omega> :: 'n pairpath. qvmata C (\<lambda>s. fst (\<omega> s)) u) \<in> borel_measurable P"
    if u: "0 \<le> u" for u
    by (rule qvmata_measurable[OF _ C0])
       (use XmP measurable_compose[OF _ projB] in blast)
  have qmF: "(\<lambda>\<omega> :: 'n pairpath. qvmata C (\<lambda>s. fst (\<omega> s)) u) \<in> borel_measurable (?F u)"
    if u: "0 \<le> u" for u
    by (rule qvmata_measurable[OF _ C0]) (use evF in auto)
  have mgcomp: "martingale P ?F 0
      (\<lambda>u \<omega> :: 'n pairpath. outerp (?\<phi> \<omega> u) - qvmata C (?\<phi> \<omega>) u)"
  proof -
    have tgt: "martingale P ?F 0
        (\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u)"
    proof (rule martingale_matI)
      fix i j :: 'n
      show "martingale P ?F 0 (\<lambda>u \<omega> :: 'n pairpath.
          (outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u) $ i $ j)"
      proof (rule martingale_of_modification_gen
               [where X = "\<lambda>t \<omega> :: 'n pairpath. \<omega> t" and X' = "\<lambda>t \<omega> :: 'n pairpath. \<omega> t"
                and Y = "\<lambda>u \<omega> :: 'n pairpath. (outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j"])
        show "prob_space P" by (rule PP.prob_space_axioms)
        show "martingale P ?F 0
            (\<lambda>u \<omega> :: 'n pairpath. (outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j)"
          by (rule martingale_mat_nth[OF mgXA])
        show "\<And>u. 0 \<le> u \<Longrightarrow> (\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> borel_measurable P"
          by (rule evP)
        show "\<And>u. 0 \<le> u \<Longrightarrow> (\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> borel_measurable P"
          by (rule evP)
        show "AE \<omega> in P. \<omega> u = \<omega> u" for u by simp
        show "(\<lambda>\<omega> :: 'n pairpath.
            (outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u) $ i $ j)
            \<in> borel_measurable P" if u: "0 \<le> u" for u
        proof -
          have "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u)) :: real^'n^'n)
              \<in> borel_measurable P"
            by (rule measurable_compose[OF XmP[OF u] outerp_borel])
          then have "(\<lambda>\<omega> :: 'n pairpath.
              outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u) \<in> borel_measurable P"
            using qmP[OF u] by simp
          then show ?thesis by (rule measurable_compose[OF _ entB])
        qed
        show "AE \<omega> in P.
            (outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u) $ i $ j
              = (outerp (fst (\<omega> u)) - snd (\<omega> u)) $ i $ j" if u: "0 \<le> u" for u
          using keyq by eventually_elim (use u in simp)
        show "adapted_process P ?F 0 (\<lambda>u \<omega> :: 'n pairpath.
            (outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u) $ i $ j)"
        proof -
          have ad: "(\<lambda>\<omega> :: 'n pairpath.
              (outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u) $ i $ j)
              \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
          proof -
            have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) :: real^'n) \<in> borel_measurable (?F u)"
            proof -
              have "(\<lambda>\<omega> :: 'n pairpath. \<omega> u) \<in> borel_measurable (?F u)"
                by (rule natural_filtration_eval[OF u order_refl])
              then show ?thesis by (rule measurable_compose[OF _ fstB])
            qed
            then have "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u)) :: real^'n^'n)
                \<in> borel_measurable (?F u)"
              by (rule measurable_compose[OF _ outerp_borel])
            then have "(\<lambda>\<omega> :: 'n pairpath.
                outerp (fst (\<omega> u)) - qvmata C (\<lambda>s. fst (\<omega> s)) u)
                \<in> borel_measurable (?F u)" using qmF[OF u] by simp
            then show ?thesis by (rule measurable_compose[OF _ entB])
          qed
          show ?thesis
            unfolding adapted_process_def adapted_process_axioms_def
            using FM ad by blast
        qed
      qed
    qed
    show ?thesis by (rule martingale_cong_ge[OF tgt]) (simp add: phicong)
  qed
  have CmgQ: "martingale ?Q ?G 0
      (\<lambda>t w :: real \<Rightarrow> real^'n. outerp (w t) - qvmata C w t)"
  proof (rule martingale_distr[OF PP.prob_space_axioms phim GG pull])
    show "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)
        \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
    proof -
      have "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) :: real^'n^'n)
          \<in> borel_measurable (?G u)"
        by (rule measurable_compose
              [OF natural_filtration_eval[OF u order_refl] outerp_borel])
      moreover have "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w u) \<in> borel_measurable (?G u)"
        by (rule qvmata_measurable[OF _ C0]) (use evG in auto)
      ultimately show ?thesis by simp
    qed
    show "martingale P ?F 0
        (\<lambda>u \<omega> :: 'n pairpath. outerp (?\<phi> \<omega> u) - qvmata C (?\<phi> \<omega>) u)"
      by (rule mgcomp)
  qed

  text \<open>Clause (v): the difference quotients.  The cut-down functional is
    continuous for EVERY path, so the condition over all real pairs is the
    condition over the rational ones, which is countable, hence measurable ---
    and that is what lets it be transferred along the pushforward.\<close>
  have equiv: "(\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> sconstraint k L)
      \<longleftrightarrow> (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (qvmata C w (real_of_rat q) - qvmata C w (real_of_rat p)) \<in> sconstraint k L)"
    for w :: "real \<Rightarrow> real^'n"
  proof
    assume A: "\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> sconstraint k L"
    show "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (qvmata C w (real_of_rat q) - qvmata C w (real_of_rat p)) \<in> sconstraint k L"
    proof (intro allI impI)
      fix p q :: rat assume pq: "0 \<le> p" "p < q"
      then have "(0 :: real) \<le> real_of_rat p" and "real_of_rat p < real_of_rat q"
        by (simp_all add: of_rat_less)
      with A show "(1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (qvmata C w (real_of_rat q) - qvmata C w (real_of_rat p)) \<in> sconstraint k L"
        by blast
    qed
  next
    assume R: "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (qvmata C w (real_of_rat q) - qvmata C w (real_of_rat p)) \<in> sconstraint k L"
    show "\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> sconstraint k L"
    proof (intro allI impI)
      fix s t :: real assume st: "0 \<le> s" "s < t"
      show "(1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> sconstraint k L"
      proof (rule diffquot_all_of_rational[OF closed_sconstraint _ _ st order_refl])
        show "continuous_on {0..t} (qvmata C w)"
          by (rule continuous_on_subset[OF qvmata_continuous[OF C0]]) auto
        fix p q :: real
        assume pQ: "p \<in> \<rat>" and qQ: "q \<in> \<rat>" and p0: "0 \<le> p" and pq: "p < q"
          and qt: "q \<le> t"
        obtain p' :: rat where p': "p = real_of_rat p'" using pQ by (auto simp: Rats_def)
        obtain q' :: rat where q': "q = real_of_rat q'" using qQ by (auto simp: Rats_def)
        have "real_of_rat 0 \<le> real_of_rat p'" using p0 p' by simp
        then have "0 \<le> p'" by (simp add: of_rat_less_eq)
        moreover have "p' < q'" using pq p' q' by (simp add: of_rat_less)
        ultimately show "(1 / (q - p)) *\<^sub>R (qvmata C w q - qvmata C w p)
            \<in> sconstraint k L" using R p' q' by blast
      qed
    qed
  qed
  have predD: "Measurable.pred (ipath_space :: ((real \<Rightarrow> real^'n) measure))
      (\<lambda>w. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> sconstraint k L)"
  proof (subst equiv, intro pred_intros_countable)
    fix p q :: rat
    show "Measurable.pred (ipath_space :: ((real \<Rightarrow> real^'n) measure))
        (\<lambda>w. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
          (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
            (qvmata C w (real_of_rat q) - qvmata C w (real_of_rat p))
              \<in> sconstraint k L)"
    proof (cases "0 \<le> p \<and> p < q")
      case False
      then show ?thesis by simp
    next
      case True
      have qm: "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w r)
          \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> real^'n) measure))" for r
      proof (rule qvmata_measurable[OF _ C0])
        fix s :: real and i assume s: "0 \<le> s"
        show "(\<lambda>w :: real \<Rightarrow> real^'n. w s $ i)
            \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
          by (rule measurable_compose[OF ipath_eval_measurable[OF s] projB])
      qed
      let ?g = "\<lambda>w :: real \<Rightarrow> real^'n. (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (qvmata C w (real_of_rat q) - qvmata C w (real_of_rat p))"
      have gm: "?g \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
        using qm by simp
      have "{w \<in> space (ipath_space :: ((real \<Rightarrow> real^'n) measure)). ?g w \<in> sconstraint k L}
          = ?g -` (sconstraint k L) \<inter> space ipath_space" by auto
      also have "\<dots> \<in> sets (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
        by (rule measurable_sets[OF gm]) (simp add: borel_closed closed_sconstraint)
      finally have "Measurable.pred (ipath_space :: ((real \<Rightarrow> real^'n) measure))
          (\<lambda>w. ?g w \<in> sconstraint k L)" unfolding pred_def by simp
      then show ?thesis using True by simp
    qed
  qed
  have dqP: "AE \<omega> in P. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (qvmata C (?\<phi> \<omega>) t - qvmata C (?\<phi> \<omega>) s) \<in> sconstraint k L"
    using keyq iexit_class_diffquot[OF P]
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix s t :: real assume st: "0 \<le> s" "s < t"
      have es: "qvmata C (?\<phi> \<omega>) s = snd (\<omega> s)" using phicong elim(1) st by simp
      have et: "qvmata C (?\<phi> \<omega>) t = snd (\<omega> t)" using phicong elim(1) st by simp
      show "(1 / (t - s)) *\<^sub>R (qvmata C (?\<phi> \<omega>) t - qvmata C (?\<phi> \<omega>) s)
          \<in> sconstraint k L" unfolding es et using elim(2) st by blast
    qed
  qed
  have dqQ: "AE w in ?Q. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (qvmata C w t - qvmata C w s) \<in> sconstraint k L"
    by (subst AE_distr_iff[OF phim predD[unfolded pred_def]]) (rule dqP)

  text \<open>Assembling the five clauses.\<close>
  have "?Q \<in> xclass k L x"
    unfolding xclass_def mem_Collect_eq
  proof (intro conjI)
    show "prob_space ?Q" by (rule PP.prob_space_distr[OF phim])
    show "sets ?Q = sets (ipath_space :: ((real \<Rightarrow> real^'n) measure))" by simp
    show "AE w in ?Q. w 0 = x" by (rule startQ)
    show "martingale ?Q ?G 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)" by (rule XmgQ)
    show "\<exists>A. (AE w in ?Q. A 0 w = 0)
        \<and> martingale ?Q ?G 0 (\<lambda>t w :: real \<Rightarrow> real^'n. outerp (w t) - A t w)
        \<and> (AE w in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
             (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L)"
      by (intro exI[of _ "\<lambda>t w :: real \<Rightarrow> real^'n. qvmata C w t"] conjI)
         (rule A0Q, rule CmgQ, rule dqQ)
  qed
  then show ?thesis unfolding ipath_law_def .
qed

subsection \<open>Second inclusion: a \<open>P\<^sub>x\<close>-law lifts to a pair law\<close>

text \<open>
  The converse pushforward, along \<open>w \<mapsto> (w, qvmata w)\<close>.  The pair space is a
  space of CONTINUOUS paths, so the second component must be continuous for
  every path, not merely almost every one --- which is what \<^const>\<open>qvmata\<close> is,
  and what a cut at the global good event would not have given while staying
  adapted.
\<close>

lemma xclass_qvmata:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes Q: "Q \<in> xclass k L x" and L: "0 \<le> L"
    and A0: "AE w in Q. A 0 w = 0"
    and mgA: "martingale Q (natural_filtration Q 0 (\<lambda>t w. w t)) 0
                (\<lambda>t w. outerp (w t) - A t w)"
    and dqA: "AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
                (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L"
  shows "AE w in Q. \<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * L) w t = A t w"
proof -
  interpret PQ: prob_space Q by (rule xclass_prob[OF Q])
  let ?F = "natural_filtration Q 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
  have spQ: "space Q = (ipath :: ((real \<Rightarrow> real^'n) set))"
    using xclass_sets[OF Q] by (simp add: sets_eq_imp_space_eq)
  have mgX: "martingale Q ?F 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
    by (rule xclass_martingale[OF Q])

  text \<open>A full-measure event carrying the three almost-everywhere clauses
    pointwise.\<close>
  from xclass_start[OF Q] obtain N1 where
    N1: "{w \<in> space Q. \<not> (w 0 = x)} \<subseteq> N1"
    and N1e: "emeasure Q N1 = 0" and N1s: "N1 \<in> sets Q" by (rule AE_E)
  from dqA obtain N2 where
    N2: "{w \<in> space Q. \<not> (\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
            (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L)} \<subseteq> N2"
    and N2e: "emeasure Q N2 = 0" and N2s: "N2 \<in> sets Q" by (rule AE_E)
  from A0 obtain N3 where
    N3: "{w \<in> space Q. \<not> (A 0 w = 0)} \<subseteq> N3"
    and N3e: "emeasure Q N3 = 0" and N3s: "N3 \<in> sets Q" by (rule AE_E)
  have Nn: "N1 \<in> null_sets Q" "N2 \<in> null_sets Q" "N3 \<in> null_sets Q"
    using N1e N1s N2e N2s N3e N3s by (simp_all add: null_sets_def)
  define G where "G = space Q - (N1 \<union> N2 \<union> N3)"
  have Nsets: "N1 \<union> N2 \<union> N3 \<in> sets Q" using N1s N2s N3s by simp
  have Gsets: "G \<in> sets Q" unfolding G_def using Nsets by simp
  have Gfull: "AE w in Q. w \<in> G"
  proof (rule AE_I[where N = "N1 \<union> N2 \<union> N3"])
    show "{w \<in> space Q. w \<notin> G} \<subseteq> N1 \<union> N2 \<union> N3" unfolding G_def by blast
    show "emeasure Q (N1 \<union> N2 \<union> N3) = 0"
    proof -
      have "N1 \<union> N2 \<in> null_sets Q" using Nn(1) Nn(2) by (rule null_sets.Un)
      then have "N1 \<union> N2 \<union> N3 \<in> null_sets Q" using Nn(3) by (rule null_sets.Un)
      then show ?thesis by (simp add: null_sets_def)
    qed
    show "N1 \<union> N2 \<union> N3 \<in> sets Q" by (rule Nsets)
  qed
  have Gspace: "G \<subseteq> space Q" unfolding G_def by blast
  have Gstart: "w 0 = x" if "w \<in> G" for w using N1 that unfolding G_def by blast
  have GA0: "A 0 w = 0" if "w \<in> G" for w using N3 that unfolding G_def by blast
  have Gdq: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L" if "w \<in> G" for w
    using N2 that unfolding G_def by blast

  let ?M = "restrict_space Q G"
  let ?FF = "\<lambda>t. restrict_space (?F t) G"
  have spM: "space ?M = G"
    by (rule space_restrict_full[OF PQ.prob_space_axioms Gsets Gfull])
  have Xc: "martingale ?M ?FF 0 (\<lambda>v w :: real \<Rightarrow> real^'n. w v $ i)" for i
    by (rule martingale_restrict_full[OF PQ.prob_space_axioms Gsets Gfull
          martingale_vec_nth[OF mgX]])
  have XAc: "martingale ?M ?FF 0
      (\<lambda>v w :: real \<Rightarrow> real^'n. w v $ i * w v $ j - A v w $ i $ j)" for i j
  proof -
    have "martingale Q ?F 0 (\<lambda>v w :: real \<Rightarrow> real^'n. (outerp (w v) - A v w) $ i $ j)"
      by (rule martingale_mat_nth[OF mgA])
    then have "martingale Q ?F 0
        (\<lambda>v w :: real \<Rightarrow> real^'n. w v $ i * w v $ j - A v w $ i $ j)"
      by (simp add: outerp_def)
    then show ?thesis
      by (rule martingale_restrict_full[OF PQ.prob_space_axioms Gsets Gfull])
  qed
  have contc: "continuous_on {0..} (\<lambda>s. w s $ i)" if w: "w \<in> space ?M" for w i
  proof -
    have "w \<in> ipath" using w Gspace spM spQ by auto
    then have c: "continuous_on {0..} w" by (rule ipath_continuous_on) simp
    have g: "continuous_on UNIV (\<lambda>v :: real^'n. v $ i)" by (intro continuous_intros)
    show ?thesis by (rule continuous_on_compose2[OF g c]) auto
  qed
  have A0c: "A 0 w = 0" if "w \<in> space ?M" for w using GA0 that spM by simp
  have psdc: "\<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow> (\<forall>y. 0 \<le> y \<bullet> ((A q w - A p w) *v y))"
    if w: "w \<in> space ?M" for w
  proof (intro allI impI)
    fix p q :: real and y :: "real^'n"
    assume pq: "0 \<le> p" "p \<le> q"
    show "0 \<le> y \<bullet> ((A q w - A p w) *v y)"
      using diffquot_psd[where A = "\<lambda>t. A t w" and k = k and L = L
              and p = p and q = q and y = y] Gdq[of w] w spM pq by simp
  qed
  have ratec: "\<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
      \<bar>A q w $ i $ j - A p w $ i $ j\<bar> \<le> L * (q - p)" if w: "w \<in> space ?M" for w
  proof (intro allI impI)
    fix p q :: real and i j assume pq: "0 \<le> p" "p \<le> q"
    show "\<bar>A q w $ i $ j - A p w $ i $ j\<bar> \<le> L * (q - p)"
      using diffquot_entry[where A = "\<lambda>t. A t w" and k = k and L = L
              and p = p and q = q and i = i and j = j] Gdq[of w] w spM pq by simp
  qed
  have X0c: "\<bar>w 0 $ i\<bar> \<le> norm x" if "w \<in> space ?M" for w i
    using Gstart that spM by (simp add: component_le_norm_cart)

  have key: "AE w in ?M.
      (\<forall>i j. qvp_good (4 * L) (\<lambda>s. w s $ i + w s $ j)
           \<and> qvp_good (4 * L) (\<lambda>s. w s $ i - w s $ j))
      \<and> (\<forall>t. 0 \<le> t \<longrightarrow> qvmat (\<lambda>s. w s) t
           = (\<chi> i. \<chi> j. (A t w $ i $ j + A t w $ j $ i) / 2))"
  proof (rule qvmat_eq_A_localised[where M = ?M and F = ?FF
           and X = "\<lambda>v w :: real \<Rightarrow> real^'n. w v" and A = "\<lambda>v w. A v w"
           and C = L and B = "norm x"])
    show "prob_space ?M"
      by (rule prob_space_restrict_full[OF PQ.prob_space_axioms Gsets Gfull])
    show "\<And>i. martingale ?M ?FF 0 (\<lambda>v w :: real \<Rightarrow> real^'n. w v $ i)" by (rule Xc)
    show "\<And>i j. martingale ?M ?FF 0
        (\<lambda>v w :: real \<Rightarrow> real^'n. w v $ i * w v $ j - A v w $ i $ j)" by (rule XAc)
    show "\<And>w i. w \<in> space ?M \<Longrightarrow> continuous_on {0..} (\<lambda>s. w s $ i)" by (rule contc)
    show "\<And>w. w \<in> space ?M \<Longrightarrow> A 0 w = 0" by (rule A0c)
    show "\<And>w. w \<in> space ?M \<Longrightarrow> \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        (\<forall>y. 0 \<le> y \<bullet> ((A q w - A p w) *v y))" by (rule psdc)
    show "\<And>w. w \<in> space ?M \<Longrightarrow> \<forall>p q i j. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
        \<bar>A q w $ i $ j - A p w $ i $ j\<bar> \<le> L * (q - p)" by (rule ratec)
    show "0 \<le> L" by (rule L)
    show "0 \<le> norm x" by simp
    show "\<And>w i. w \<in> space ?M \<Longrightarrow> \<bar>w 0 $ i\<bar> \<le> norm x" by (rule X0c)
  qed
  have L4: "0 \<le> 4 * L" using L by simp
  have spAE: "AE w in ?M. w \<in> space ?M" by (rule AE_I2) simp
  have sym: "AE w in ?M. \<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * L) w t = A t w"
    using key spAE
  proof eventually_elim
    case (elim w)
    then have gp: "\<And>i j. qvp_good (4 * L) (\<lambda>s. w s $ i + w s $ j)"
      and gm: "\<And>i j. qvp_good (4 * L) (\<lambda>s. w s $ i - w s $ j)"
      and ke: "\<And>t. 0 \<le> t \<Longrightarrow> qvmat (\<lambda>s. w s) t
          = (\<chi> i. \<chi> j. (A t w $ i $ j + A t w $ j $ i) / 2)" by blast+
    from elim have "w \<in> G" using spM by simp
    then have s: "A t w $ i $ j = A t w $ j $ i" if "0 \<le> t" for t i j
      using diffquot_sym[where A = "\<lambda>u. A u w" and k = k and L = L
              and t = t and i = i and j = j] Gdq[of w] GA0[of w] that by simp
    show ?case
    proof (intro allI impI)
      fix t :: real assume t: "0 \<le> t"
      have "(\<chi> i. \<chi> j. (A t w $ i $ j + A t w $ j $ i) / 2) = A t w"
        by (simp add: vec_eq_iff s[OF t])
      then have "qvmat (\<lambda>s. w s) t = A t w" using ke[OF t] by simp
      then show "qvmata (4 * L) w t = A t w"
        using qvmata_eq_qvmat[OF gp gm L4] by simp
    qed
  qed
  have "AE w in Q. w \<in> G \<longrightarrow> (\<forall>t. 0 \<le> t \<longrightarrow> qvmata (4 * L) w t = A t w)"
    using sym Gsets Gspace
    by (subst (asm) AE_restrict_space_iff) (auto simp: Int_absorb2)
  with Gfull show ?thesis by eventually_elim blast
qed

text \<open>The two events of the pair path space that the lift has to hit: the
  initial condition, and the constraint on the difference quotients.  Both are
  measurable, the second because every point of the path space IS a continuous
  path, so the condition over all real pairs is the countable condition over the
  rational ones.\<close>

lemma pairpath_start_sets:
  fixes x :: "real^'n::finite"
  shows "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ipath_space"
proof -
  have m: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ipath_space"
    by (rule ipath_eval_measurable) simp
  have "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
      = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ipath_space"
    by (auto simp: prod_eq_iff)
  also have "\<dots> \<in> sets (ipath_space :: (('n pairpath) measure))"
    by (rule measurable_sets[OF m]) simp
  finally show ?thesis .
qed

lemma pairpath_diffquot_sets:
  shows "{\<omega> \<in> space (ipath_space :: (('n::finite pairpath) measure)).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L}
    \<in> sets ipath_space"
proof -
  have sndB: "(snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have ev: "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> v)) \<in> borel_measurable ipath_space"
    if v: "0 \<le> v" for v
    by (rule measurable_compose[OF ipath_eval_measurable[OF v] sndB])
  have cont: "continuous_on {0..} (\<lambda>t. snd (\<omega> t))"
    if w: "\<omega> \<in> (ipath :: (('n pairpath) set))" for \<omega>
  proof -
    have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on[OF w]) simp
    have g: "continuous_on UNIV (snd :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n)"
      by (intro continuous_intros)
    show ?thesis by (rule continuous_on_compose2[OF g c]) auto
  qed
  have equiv: "(\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L)
      \<longleftrightarrow> (\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L)"
    if w: "\<omega> \<in> (ipath :: (('n pairpath) set))" for \<omega>
  proof
    assume A: "\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    show "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L"
    proof (intro allI impI)
      fix p q :: rat assume pq: "0 \<le> p" "p < q"
      then have "(0 :: real) \<le> real_of_rat p" and "real_of_rat p < real_of_rat q"
        by (simp_all add: of_rat_less)
      with A show "(1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L"
        by blast
    qed
  next
    assume R: "\<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L"
    show "\<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    proof (intro allI impI)
      fix s t :: real assume st: "0 \<le> s" "s < t"
      show "(1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
      proof (rule diffquot_all_of_rational[OF closed_sconstraint _ _ st order_refl])
        show "continuous_on {0..t} (\<lambda>u. snd (\<omega> u))"
          by (rule continuous_on_subset[OF cont[OF w]]) auto
        fix p q :: real
        assume pQ: "p \<in> \<rat>" and qQ: "q \<in> \<rat>" and p0: "0 \<le> p" and pq: "p < q"
          and qt: "q \<le> t"
        obtain p' :: rat where p': "p = real_of_rat p'" using pQ by (auto simp: Rats_def)
        obtain q' :: rat where q': "q = real_of_rat q'" using qQ by (auto simp: Rats_def)
        have "real_of_rat 0 \<le> real_of_rat p'" using p0 p' by simp
        then have "0 \<le> p'" by (simp add: of_rat_less_eq)
        moreover have "p' < q'" using pq p' q' by (simp add: of_rat_less)
        ultimately show "(1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
          using R p' q' by blast
      qed
    qed
  qed
  have "Measurable.pred (ipath_space :: (('n pairpath) measure))
      (\<lambda>\<omega>. \<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L)"
  proof (intro pred_intros_countable)
    fix p q :: rat
    show "Measurable.pred (ipath_space :: (('n pairpath) measure))
        (\<lambda>\<omega>. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
          (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
            (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L)"
    proof (cases "0 \<le> p \<and> p < q")
      case False
      then show ?thesis by simp
    next
      case True
      then have p0: "(0 :: real) \<le> real_of_rat p" and q0: "(0 :: real) \<le> real_of_rat q"
        by (auto simp: of_rat_less)
      let ?g = "\<lambda>\<omega> :: 'n pairpath. (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p)))"
      have gm: "?g \<in> borel_measurable (ipath_space :: (('n pairpath) measure))"
        using ev[OF p0] ev[OF q0] by simp
      have "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)). ?g \<omega> \<in> sconstraint k L}
          = ?g -` (sconstraint k L) \<inter> space ipath_space" by auto
      also have "\<dots> \<in> sets (ipath_space :: (('n pairpath) measure))"
        by (rule measurable_sets[OF gm]) (simp add: borel_closed closed_sconstraint)
      finally have "Measurable.pred (ipath_space :: (('n pairpath) measure))
          (\<lambda>\<omega>. ?g \<omega> \<in> sconstraint k L)" unfolding pred_def by simp
      then show ?thesis using True by simp
    qed
  qed
  then have "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      \<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L}
      \<in> sets ipath_space" unfolding pred_def by simp
  moreover have "{\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L}
      = {\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      \<forall>p q :: rat. 0 \<le> p \<longrightarrow> p < q \<longrightarrow>
        (1 / (real_of_rat q - real_of_rat p)) *\<^sub>R
          (snd (\<omega> (real_of_rat q)) - snd (\<omega> (real_of_rat p))) \<in> sconstraint k L}"
    using equiv by auto
  ultimately show ?thesis by simp
qed

theorem xclass_lift_in_iexit_class:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes Q: "Q \<in> xclass k L x" and L: "0 \<le> L"
  shows "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * L) w t)) \<in> iexit_class k L x"
proof -
  interpret PQ: prob_space Q by (rule xclass_prob[OF Q])
  define C where "C = 4 * L"
  have C0: "0 \<le> C" using L by (simp add: C_def)
  let ?\<psi> = "\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata C w t)) {0..}"
  let ?P = "distr Q (ipath_space :: (('n pairpath) measure)) ?\<psi>"
  let ?F = "natural_filtration Q 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
  let ?G = "natural_filtration ?P 0 (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"

  from Q obtain A where A0: "AE w in Q. A 0 w = 0"
    and mgA: "martingale Q ?F 0 (\<lambda>t w. outerp (w t) - A t w)"
    and dqA: "AE w in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
                (1 / (t - s)) *\<^sub>R (A t w - A s w) \<in> sconstraint k L"
    unfolding xclass_def by blast
  have keyq: "AE w in Q. \<forall>t. 0 \<le> t \<longrightarrow> qvmata C w t = A t w"
    unfolding C_def by (rule xclass_qvmata[OF Q L A0 mgA dqA])

  have spQ: "space Q = (ipath :: ((real \<Rightarrow> real^'n) set))"
    using xclass_sets[OF Q] by (simp add: sets_eq_imp_space_eq)
  have mgX: "martingale Q ?F 0 (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
    by (rule xclass_martingale[OF Q])
  have evQ: "(\<lambda>w :: real \<Rightarrow> real^'n. w v) \<in> borel_measurable Q" if v: "0 \<le> v" for v
    by (rule ipath_eval_measurable_sets[OF xclass_sets[OF Q] v])
  have projB: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI continuous_intros)
  have qmQ: "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w v) \<in> borel_measurable Q"
    if v: "0 \<le> v" for v
    by (rule qvmata_measurable[OF _ C0])
       (use evQ measurable_compose[OF _ projB] in blast)
  have Xm: "(\<lambda>w :: real \<Rightarrow> real^'n. (w v, qvmata C w v)) \<in> borel_measurable Q"
    if v: "0 \<le> v" for v
    by (rule borel_measurable_Pair[OF evQ[OF v] qmQ[OF v]])
  have contQ: "continuous_on {0..} (\<lambda>t. (w t, qvmata C w t))" if w: "w \<in> space Q" for w
  proof -
    have "w \<in> ipath" using w spQ by simp
    then have c: "continuous_on {0..} w" by (rule ipath_continuous_on) simp
    show ?thesis
      by (intro continuous_on_Pair c qvmata_continuous[OF C0])
  qed
  have psim: "?\<psi> \<in> Q \<rightarrow>\<^sub>M (ipath_space :: (('n pairpath) measure))"
    by (rule ipathify_measurable[OF Xm contQ])
  have into: "?\<psi> w \<in> (ipath :: (('n pairpath) set))" if "w \<in> space Q" for w
    using measurable_space[OF psim that] by simp
  have probP: "prob_space ?P" by (rule PQ.prob_space_distr[OF psim])

  text \<open>The filtration facts, as in the first inclusion.\<close>
  interpret MX: martingale Q ?F 0 "\<lambda>t w :: real \<Rightarrow> real^'n. w t" by (rule mgX)
  have spF: "space (?F u) = space Q" if "0 \<le> u" for u by (rule MX.space_F[OF that])
  have GG: "filtered_measure ?P ?G (0::real)"
  proof -
    interpret PP: prob_space ?P by (rule probP)
    have SP: "Stochastic_Process.stochastic_process ?P (0::real)
        (\<lambda>t \<omega> :: 'n pairpath. \<omega> t)"
      by (unfold_locales) (rule ipath_eval_measurable_sets[OF sets_distr])
    show ?thesis
      by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SP])
  qed
  have evF: "(\<lambda>w :: real \<Rightarrow> real^'n. w v) \<in> borel_measurable (?F u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
    by (rule natural_filtration_eval[OF v vu])
  have qmF: "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w v) \<in> borel_measurable (?F u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for u v
  proof (rule qvmata_measurable[OF _ C0])
    fix s :: real and i assume s: "0 \<le> s" and sv: "s < v"
    show "(\<lambda>w :: real \<Rightarrow> real^'n. w s $ i) \<in> borel_measurable (?F u)"
      by (rule measurable_compose[OF evF[OF s] projB]) (use sv vu in simp)
  qed
  have pull: "?\<psi> \<in> ?F u \<rightarrow>\<^sub>M ?G u" if u: "0 \<le> u" for u
  proof (rule natural_filtration_pull)
    fix w assume "w \<in> space (?F u)"
    then have "w \<in> space Q" using spF[OF u] by simp
    then show "?\<psi> w \<in> space ?P" using into by (simp add: space_distr)
  next
    fix v :: real assume v: "0 \<le> v" and vu: "v \<le> u"
    have e: "(\<lambda>w :: real \<Rightarrow> real^'n. ?\<psi> w v) = (\<lambda>w. (w v, qvmata C w v))"
      using v by simp
    show "(\<lambda>w :: real \<Rightarrow> real^'n. ?\<psi> w v) \<in> borel_measurable (?F u)"
      unfolding e by (rule borel_measurable_Pair[OF evF[OF v vu] qmF[OF v vu]])
  qed

  text \<open>Clause (i): the initial condition.  The second coordinate vanishes at
    \<open>0\<close> for EVERY path.\<close>
  have start: "AE \<omega> in ?P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  proof (subst AE_distr_iff[OF psim pairpath_start_sets])
    show "AE w in Q. fst (?\<psi> w 0) = x \<and> snd (?\<psi> w 0) = 0"
      using xclass_start[OF Q] by eventually_elim (simp add: C0)
  qed

  text \<open>Clause (ii): the difference quotients.\<close>
  have dqQ: "AE w in Q. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (?\<psi> w t) - snd (?\<psi> w s)) \<in> sconstraint k L"
    using keyq dqA
  proof eventually_elim
    case (elim w)
    show ?case
    proof (intro allI impI)
      fix s t :: real assume st: "0 \<le> s" "s < t"
      have es: "snd (?\<psi> w s) = A s w" using elim(1) st by simp
      have et: "snd (?\<psi> w t) = A t w" using elim(1) st by simp
      show "(1 / (t - s)) *\<^sub>R (snd (?\<psi> w t) - snd (?\<psi> w s)) \<in> sconstraint k L"
        unfolding es et using elim(2) st by blast
    qed
  qed
  have dq: "AE \<omega> in ?P. \<forall>s t :: real. 0 \<le> s \<longrightarrow> s < t \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (subst AE_distr_iff[OF psim pairpath_diffquot_sets]) (rule dqQ)

  text \<open>Clause (iii): the first coordinate is a martingale.\<close>
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have Xmg: "martingale ?P ?G 0 (\<lambda>t \<omega> :: 'n pairpath. fst (\<omega> t) :: real^'n)"
  proof (rule martingale_distr[OF PQ.prob_space_axioms psim GG pull])
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> u) :: real^'n) \<in> borel_measurable (?G u)"
      if u: "0 \<le> u" for u
      by (rule measurable_compose[OF natural_filtration_eval[OF u order_refl] fstB])
    show "martingale Q ?F 0 (\<lambda>u w :: real \<Rightarrow> real^'n. fst (?\<psi> w u) :: real^'n)"
      by (rule martingale_cong_ge[OF mgX]) simp
  qed

  text \<open>Clause (iv): the compensated process is a martingale, again a
    modification of the one the paper's class supplies.\<close>
  have cB: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
      \<in> borel_measurable borel"
  proof -
    have e: "(\<lambda>p :: (real^'n) \<times> (real^'n^'n). outerp (fst p) - snd p)
        = (\<lambda>p. \<chi> i j. fst p $ i * fst p $ j - snd p $ i $ j)"
      by (rule ext) (simp add: outerp_def vec_eq_iff)
    show ?thesis unfolding e
      by (intro borel_measurable_continuous_onI continuous_on_vec_lambda
          continuous_intros)
  qed
  have entB: "(\<lambda>Z :: real^'n^'n. Z $ i $ j) \<in> borel_measurable borel" for i j
    by (intro borel_measurable_continuous_onI continuous_intros)
  have SQ: "Stochastic_Process.stochastic_process Q (0::real)
      (\<lambda>t w :: real \<Rightarrow> real^'n. w t)"
    by (unfold_locales) (rule evQ)
  have FM: "filtered_measure Q ?F (0::real)"
    by (rule Stochastic_Process.stochastic_process.filtered_measure_natural_filtration[OF SQ])
  have mgcomp: "martingale Q ?F 0
      (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (fst (?\<psi> w u)) - snd (?\<psi> w u))"
  proof -
    have tgt: "martingale Q ?F 0
        (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)"
    proof (rule martingale_matI)
      fix i j :: 'n
      show "martingale Q ?F 0
          (\<lambda>u w :: real \<Rightarrow> real^'n. (outerp (w u) - qvmata C w u) $ i $ j)"
      proof (rule martingale_of_modification_gen
               [where X = "\<lambda>t w :: real \<Rightarrow> real^'n. w t"
                and X' = "\<lambda>t w :: real \<Rightarrow> real^'n. w t"
                and Y = "\<lambda>u w :: real \<Rightarrow> real^'n. (outerp (w u) - A u w) $ i $ j"])
        show "prob_space Q" by (rule PQ.prob_space_axioms)
        show "martingale Q ?F 0
            (\<lambda>u w :: real \<Rightarrow> real^'n. (outerp (w u) - A u w) $ i $ j)"
          by (rule martingale_mat_nth[OF mgA])
        show "\<And>u. 0 \<le> u \<Longrightarrow> (\<lambda>w :: real \<Rightarrow> real^'n. w u) \<in> borel_measurable Q"
          by (rule evQ)
        show "\<And>u. 0 \<le> u \<Longrightarrow> (\<lambda>w :: real \<Rightarrow> real^'n. w u) \<in> borel_measurable Q"
          by (rule evQ)
        show "AE w in Q. w u = w u" for u by simp
        show "(\<lambda>w :: real \<Rightarrow> real^'n. (outerp (w u) - qvmata C w u) $ i $ j)
            \<in> borel_measurable Q" if u: "0 \<le> u" for u
        proof -
          have "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) :: real^'n^'n)
              \<in> borel_measurable Q"
            by (rule measurable_compose[OF evQ[OF u] outerp_borel])
          then have "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)
              \<in> borel_measurable Q" using qmQ[OF u] by simp
          then show ?thesis by (rule measurable_compose[OF _ entB])
        qed
        show "AE w in Q. (outerp (w u) - qvmata C w u) $ i $ j
            = (outerp (w u) - A u w) $ i $ j" if u: "0 \<le> u" for u
          using keyq by eventually_elim (use u in simp)
        show "adapted_process Q ?F 0
            (\<lambda>u w :: real \<Rightarrow> real^'n. (outerp (w u) - qvmata C w u) $ i $ j)"
        proof -
          have ad: "(\<lambda>w :: real \<Rightarrow> real^'n. (outerp (w u) - qvmata C w u) $ i $ j)
              \<in> borel_measurable (?F u)" if u: "0 \<le> u" for u
          proof -
            have "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) :: real^'n^'n)
                \<in> borel_measurable (?F u)"
              by (rule measurable_compose[OF evF[OF u order_refl] outerp_borel])
            then have "(\<lambda>w :: real \<Rightarrow> real^'n. outerp (w u) - qvmata C w u)
                \<in> borel_measurable (?F u)" using qmF[OF u order_refl] by simp
            then show ?thesis by (rule measurable_compose[OF _ entB])
          qed
          show ?thesis
            unfolding adapted_process_def adapted_process_axioms_def
            using FM ad by blast
        qed
      qed
    qed
    show ?thesis by (rule martingale_cong_ge[OF tgt]) simp
  qed
  have Cmg: "martingale ?P ?G 0
      (\<lambda>t \<omega> :: 'n pairpath. outerp (fst (\<omega> t) :: real^'n) - snd (\<omega> t))"
  proof (rule martingale_distr[OF PQ.prob_space_axioms psim GG pull])
    show "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> u) :: real^'n) - snd (\<omega> u))
        \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
      by (rule measurable_compose[OF natural_filtration_eval[OF u order_refl] cB])
    show "martingale Q ?F 0
        (\<lambda>u w :: real \<Rightarrow> real^'n. outerp (fst (?\<psi> w u) :: real^'n) - snd (?\<psi> w u))"
      by (rule mgcomp)
  qed

  have "?P \<in> iexit_class k L x"
    unfolding iexit_class_def mem_Collect_eq
    using probP sets_distr start dq Xmg Cmg by blast
  then show ?thesis unfolding ipath_law_def C_def .
qed

subsection \<open>The two value functions coincide\<close>

text \<open>
  The exit functional reads the path only on \<open>{0..}\<close> and is measurable there, so
  the essential infimum transports along both pushforwards.  Together with the
  two inclusions this identifies @{const iexit_val} with @{const xval} ---
  and hence every clause of Theorem 1.1 with a statement about the paper's own
  value function (1.6).
\<close>

lemma pexit_cong_nonneg:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> f s = g s" and T: "0 \<le> T"
  shows "pexit T K f = pexit T K g"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K} = {r. 0 \<le> r \<and> r \<le> T \<and> g r \<in> - K}"
    using eq by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma iexit_cong_nonneg:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> f s = g s"
  shows "iexit K f = iexit K g"
  unfolding iexit_def by (intro SUP_cong refl) (use pexit_cong_nonneg[OF eq] in auto)

lemma pexit_restrict [simp]: "pexit T K (restrict f {0..T}) = pexit T K f"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> restrict f {0..T} r \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K}" by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma iexit_nat_sup: "iexit K f = (SUP n :: nat. ennreal (pexit (real n) K f))"
proof (rule antisym)
  show "iexit K f \<le> (SUP n :: nat. ennreal (pexit (real n) K f))"
    unfolding iexit_def
  proof (rule SUP_least)
    fix T :: real assume "T \<in> {0..}"
    then have T: "0 \<le> T" by simp
    obtain n :: nat where n: "T < real n" using reals_Archimedean2 by blast
    have "pexit T K f \<le> pexit (real n) K f"
      by (rule pexit_mono_T[OF T]) (use n in simp)
    then have "ennreal (pexit T K f) \<le> ennreal (pexit (real n) K f)"
      by (rule ennreal_leI)
    also have "\<dots> \<le> (SUP n :: nat. ennreal (pexit (real n) K f))"
      by (rule SUP_upper) simp
    finally show "ennreal (pexit T K f) \<le> (SUP n :: nat. ennreal (pexit (real n) K f))" .
  qed
  show "(SUP n :: nat. ennreal (pexit (real n) K f)) \<le> iexit K f"
    by (rule SUP_least) (auto intro: pexit_le_iexit)
qed

lemma iexit_measurable_gen:
  fixes K :: "('b::polish_space) set" and N :: "'a measure"
  assumes K: "closed K"
    and Ym: "\<And>t. 0 \<le> t \<Longrightarrow> Y t \<in> borel_measurable N"
    and cont: "\<And>\<omega>. \<omega> \<in> space N \<Longrightarrow> continuous_on {0..} (\<lambda>t. Y t \<omega>)"
  shows "(\<lambda>\<omega>. iexit K (\<lambda>t. Y t \<omega>)) \<in> borel_measurable N"
proof -
  have step: "(\<lambda>\<omega>. ennreal (pexit T K (\<lambda>t. Y t \<omega>))) \<in> borel_measurable N"
    if T: "0 \<le> T" for T
  proof -
    have p: "(\<lambda>\<omega>. restrict (\<lambda>t. Y t \<omega>) {0..T})
        \<in> N \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'b) measure)"
    proof (rule pathify_measurable[OF T])
      fix t assume "t \<in> {0..T}"
      then show "Y t \<in> borel_measurable N" by (intro Ym) simp
    next
      fix \<omega> assume "\<omega> \<in> space N"
      from cont[OF this] show "continuous_on {0..T} (\<lambda>t. Y t \<omega>)"
        by (rule continuous_on_subset) auto
    qed
    have "(\<lambda>\<omega>. pexit T K (restrict (\<lambda>t. Y t \<omega>) {0..T})) \<in> borel_measurable N"
      by (rule measurable_compose[OF p pexit_measurable[OF T K]])
    then show ?thesis by simp
  qed
  have "(\<lambda>\<omega>. SUP n :: nat. ennreal (pexit (real n) K (\<lambda>t. Y t \<omega>)))
      \<in> borel_measurable N"
    by (intro borel_measurable_SUP[where I = UNIV]) (use step in auto)
  then show ?thesis by (simp add: iexit_nat_sup)
qed

lemma iexit_measurable_ipath:
  fixes K :: "('b::polish_space) set"
  assumes K: "closed K"
  shows "iexit K \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
proof -
  have "(\<lambda>w :: real \<Rightarrow> 'b. iexit K (\<lambda>t. w t))
      \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
  proof (rule iexit_measurable_gen[OF K])
    show "\<And>t. 0 \<le> t \<Longrightarrow> (\<lambda>w :: real \<Rightarrow> 'b. w t)
        \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
      by (rule ipath_eval_measurable)
  next
    fix w :: "real \<Rightarrow> 'b" assume "w \<in> space (ipath_space :: ((real \<Rightarrow> 'b) measure))"
    then show "continuous_on {0..} (\<lambda>t. w t)"
      by (intro ipath_continuous_on) auto
  qed
  then show ?thesis by simp
qed

lemma iexit_fst_measurable_ipath:
  fixes K :: "(real^'n::finite) set"
  assumes K: "closed K"
  shows "(\<lambda>\<omega> :: 'n pairpath. iexit K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable (ipath_space :: (('n pairpath) measure))"
proof (rule iexit_measurable_gen[OF K])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable ipath_space"
    if "0 \<le> t" for t
    by (rule measurable_compose[OF ipath_eval_measurable[OF that] fstB])
next
  fix \<omega> :: "'n pairpath"
  assume "\<omega> \<in> space (ipath_space :: (('n pairpath) measure))"
  then have "\<omega> \<in> ipath" by simp
  then have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
  have g: "continuous_on UNIV (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)"
    by (intro continuous_intros)
  show "continuous_on {0..} (\<lambda>t. fst (\<omega> t))"
    by (rule continuous_on_compose2[OF g c]) auto
qed


lemma iexit_class_fstify_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes P: "P \<in> iexit_class k L x"
  shows "(\<lambda>\<omega> :: 'n pairpath. restrict (\<lambda>t. fst (\<omega> t)) {0..})
      \<in> P \<rightarrow>\<^sub>M (ipath_space :: ((real \<Rightarrow> real^'n) measure))"
proof (rule ipathify_measurable)
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable P" if "0 \<le> t" for t
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> t) \<in> borel_measurable P"
      unfolding measurable_cong_sets[OF iexit_class_sets[OF P] refl]
      by (rule ipath_eval_measurable[OF that])
    then show ?thesis by (rule measurable_compose[OF _ fstB])
  qed
next
  fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
  then have "\<omega> \<in> ipath"
    using iexit_class_sets[OF P] by (simp add: sets_eq_imp_space_eq)
  then have c: "continuous_on {0..} \<omega>" by (rule ipath_continuous_on) simp
  have g: "continuous_on UNIV (fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)"
    by (intro continuous_intros)
  show "continuous_on {0..} (\<lambda>t. fst (\<omega> t))"
    by (rule continuous_on_compose2[OF g c]) auto
qed

lemma xclass_liftify_measurable:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)"
  assumes Q: "Q \<in> xclass k L x" and C: "0 \<le> C"
  shows "(\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata C w t)) {0..})
      \<in> Q \<rightarrow>\<^sub>M (ipath_space :: (('n pairpath) measure))"
proof (rule ipathify_measurable)
  have projB: "(\<lambda>v :: real^'n. v $ i) \<in> borel_measurable borel" for i
    by (intro borel_measurable_continuous_onI continuous_intros)
  have evQ: "(\<lambda>w :: real \<Rightarrow> real^'n. w v) \<in> borel_measurable Q" if "0 \<le> v" for v
    by (rule ipath_eval_measurable_sets[OF xclass_sets[OF Q] that])
  show "(\<lambda>w :: real \<Rightarrow> real^'n. (w t, qvmata C w t)) \<in> borel_measurable Q"
    if t: "0 \<le> t" for t
  proof (rule borel_measurable_Pair[OF evQ[OF t]])
    show "(\<lambda>w :: real \<Rightarrow> real^'n. qvmata C w t) \<in> borel_measurable Q"
      by (rule qvmata_measurable[OF _ C])
         (use evQ measurable_compose[OF _ projB] in blast)
  qed
next
  fix w :: "real \<Rightarrow> real^'n" assume "w \<in> space Q"
  then have "w \<in> ipath" using xclass_sets[OF Q] by (simp add: sets_eq_imp_space_eq)
  then have c: "continuous_on {0..} w" by (rule ipath_continuous_on) simp
  show "continuous_on {0..} (\<lambda>t. (w t, qvmata C w t))"
    by (intro continuous_on_Pair c qvmata_continuous[OF C])
qed

text \<open>The essential infimum of the exit time is the same on a pair law and on
  its \<open>X\<close>-marginal, and on a \<open>P\<^sub>x\<close>-law and on its lift.\<close>

lemma ess_inf_fstify:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes P: "P \<in> iexit_class k L x" and K: "closed K"
  shows "ess_inf (ipath_law P (\<lambda>t \<omega>. fst (\<omega> t))) (iexit K)
       = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
proof -
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. restrict (\<lambda>t. fst (\<omega> t)) {0..}"
  have m: "\<And>c :: ennreal.
      {w \<in> space (ipath_space :: ((real \<Rightarrow> real^'n) measure)). c \<le> iexit K w}
        \<in> sets ipath_space"
    using iexit_measurable_ipath[OF K] by measurable
  have "ess_inf (distr P (ipath_space :: ((real \<Rightarrow> real^'n) measure)) ?\<phi>) (iexit K)
      = ess_inf P (\<lambda>\<omega>. iexit K (?\<phi> \<omega>))"
    by (rule ess_inf_distr[OF iexit_class_fstify_measurable[OF P] m])
  also have "\<dots> = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
    by (intro arg_cong[where f = "ess_inf P"] ext iexit_cong_nonneg) simp
  finally show ?thesis unfolding ipath_law_def .
qed

lemma ess_inf_liftify:
  fixes Q :: "((real \<Rightarrow> real^'n::finite) measure)" and K :: "(real^'n) set"
  assumes Q: "Q \<in> xclass k L x" and K: "closed K" and C: "0 \<le> C"
  shows "ess_inf (ipath_law Q (\<lambda>t w. (w t, qvmata C w t)))
           (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))
       = ess_inf Q (iexit K)"
proof -
  let ?\<psi> = "\<lambda>w :: real \<Rightarrow> real^'n. restrict (\<lambda>t. (w t, qvmata C w t)) {0..}"
  have m: "\<And>c :: ennreal. {\<omega> \<in> space (ipath_space :: (('n pairpath) measure)).
      c \<le> iexit K (\<lambda>t. fst (\<omega> t))} \<in> sets ipath_space"
    using iexit_fst_measurable_ipath[OF K] by measurable
  have "ess_inf (distr Q (ipath_space :: (('n pairpath) measure)) ?\<psi>)
        (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))
      = ess_inf Q (\<lambda>w. iexit K (\<lambda>t. fst (?\<psi> w t)))"
    by (rule ess_inf_distr[OF xclass_liftify_measurable[OF Q C] m])
  also have "\<dots> = ess_inf Q (iexit K)"
    by (intro arg_cong[where f = "ess_inf Q"] ext iexit_cong_nonneg) simp
  finally show ?thesis unfolding ipath_law_def .
qed

theorem iexit_val_eq_xval:
  fixes K :: "(real^'n::finite) set"
  assumes K: "closed K" and L: "0 \<le> L"
  shows "iexit_val k L K x = (xval k L K x :: ennreal)"
proof (rule antisym)
  show "iexit_val k L K x \<le> xval k L K x"
    unfolding iexit_val_def
  proof (rule Sup_least)
    fix v assume "v \<in> (\<lambda>Q. ess_inf Q (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t))))
        ` iexit_class k L x"
    then obtain P :: "('n pairpath) measure"
      where P: "P \<in> iexit_class k L x"
        and v: "v = ess_inf P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))" by blast
    let ?Q = "ipath_law P (\<lambda>t \<omega>. fst (\<omega> t))"
    have Qx: "?Q \<in> xclass k L x" by (rule iexit_class_marginal_in_xclass[OF P L])
    have "v = ess_inf ?Q (iexit K)" using v ess_inf_fstify[OF P K] by simp
    also have "\<dots> \<le> xval k L K x"
      unfolding xval_def using Qx by (intro Sup_upper) blast
    finally show "v \<le> xval k L K x" .
  qed
next
  show "xval k L K x \<le> iexit_val k L K x"
    unfolding xval_def
  proof (rule Sup_least)
    fix v assume "v \<in> (\<lambda>Q. ess_inf Q (iexit K)) ` xclass k L x"
    then obtain Q :: "((real \<Rightarrow> real^'n) measure)"
      where Q: "Q \<in> xclass k L x" and v: "v = ess_inf Q (iexit K)" by blast
    have L4: "0 \<le> 4 * L" using L by simp
    let ?P = "ipath_law Q (\<lambda>t w. (w t, qvmata (4 * L) w t))"
    have Pi: "?P \<in> iexit_class k L x" by (rule xclass_lift_in_iexit_class[OF Q L])
    have "v = ess_inf ?P (\<lambda>\<omega>. iexit K (\<lambda>t. fst (\<omega> t)))"
      using v ess_inf_liftify[OF Q K L4] by simp
    also have "\<dots> \<le> iexit_val k L K x"
      unfolding iexit_val_def using Pi by (intro Sup_upper) blast
    finally show "v \<le> iexit_val k L K x" .
  qed
qed

(*<*)
end
(*>*)
