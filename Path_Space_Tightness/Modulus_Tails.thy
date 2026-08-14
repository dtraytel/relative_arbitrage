section \<open>The uniform modulus-of-continuity tail bound\<close>

(*<*)
theory Modulus_Tails
  imports Increment_Tails Dyadic_Chaining
begin

(*>*)

text \<open>
  Combine the per-level dyadic tail bounds (from Eq. (2.7) via
  @{theory Path_Space_Tightness.Increment_Tails}) with the deterministic chaining of @{theory Path_Space_Tightness.Dyadic_Chaining}
  into the quantitative tail bound on the modulus of continuity. Both the
  modulus threshold and the exceptional probability are explicit in
  \<open>(C, T, \<gamma>, n)\<close> only --- uniformity over the family of admissible laws is
  exactly what tightness in Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close> consumes.
\<close>
subsection \<open>The bad event at one dyadic level\<close>

text \<open>
  The level bound in its abstract form: only measurability, integrability of
  the fourth powers and the Eq. (2.7) moment bound itself are consumed. The
  Lemma 2.2 there needs this for unbounded martingale laws, where (2.7)
  will be obtained by localization + Fatou; the bounded package is a
  corollary below.
\<close>

lemma dyadic_level_tail_mom:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and int4: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
    and mom: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    and T0: "0 \<le> T"
    and l: "0 < l"
  shows "measure M {\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
            l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
           \<le> 8*C\<^sup>2*T*(1/2^j) / l^4"
proof -
  interpret P: prob_space M by (rule P)
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule Xm[OF that])
  have k0: "0 \<le> real_of_int (k - 1) / 2^j" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    using that by simp
  have kk: "real_of_int (k - 1) / 2^j \<le> real_of_int k / 2^j" for k
    by (intro divide_right_mono) simp_all
  have kT: "real_of_int k / 2^j \<le> T" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
  proof -
    from that have "real_of_int k \<le> real_of_int \<lfloor>2^j * T\<rfloor>" by simp
    also have "\<dots> \<le> 2^j * T" by (rule of_int_floor_le)
    finally show ?thesis by (simp add: field_simps)
  qed
  have k0': "0 \<le> real_of_int k / 2^j" if "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    using k0[OF that] kk[of k] by linarith
  have iY4: "integrable M (\<lambda>\<omega>. (X (real_of_int k / 2^j) \<omega>
                               - X (real_of_int (k - 1) / 2^j) \<omega>)^4)"
    if k: "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    by (rule int4[OF k0[OF k] kk kT[OF k]])
  have Ak: "{\<omega> \<in> space M. l \<le> \<bar>X (real_of_int k / 2^j) \<omega>
                              - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>} \<in> sets M"
    if k: "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    using Xmeas[OF k0'[OF k]] Xmeas[OF k0[OF k]] by measurable
  have perk: "measure M {\<omega> \<in> space M. l \<le> \<bar>X (real_of_int k / 2^j) \<omega>
                  - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
        \<le> 8*C\<^sup>2*(1/2^j)\<^sup>2 / l^4"
    if k: "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
  proof -
    have "measure M {\<omega> \<in> space M. l \<le> \<bar>X (real_of_int k / 2^j) \<omega>
              - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
          \<le> (\<integral>\<omega>. (X (real_of_int k / 2^j) \<omega>
                    - X (real_of_int (k - 1) / 2^j) \<omega>)^4 \<partial>M) / l^4"
      by (intro fourth_moment_tail[OF P _ iY4[OF k] l]
            borel_measurable_diff Xmeas k0[OF k] k0'[OF k])
    also have "\<dots> \<le> 8*C\<^sup>2*(real_of_int k / 2^j - real_of_int (k - 1) / 2^j)\<^sup>2 / l^4"
      by (intro divide_right_mono mom[OF k0[OF k] kk kT[OF k]] pow4_nonneg)
    also have "real_of_int k / 2^j - real_of_int (k - 1) / 2^j = 1/2^j"
      by (simp add: diff_divide_distrib[symmetric])
    finally show ?thesis .
  qed
  have seteq: "{\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
        l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
      = (\<Union>k\<in>{1..\<lfloor>2^j * T\<rfloor>}. {\<omega> \<in> space M.
          l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>})"
    by auto
  have Asub: "(\<lambda>k. {\<omega> \<in> space M.
        l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>})
      ` {1..\<lfloor>2^j * T\<rfloor>} \<subseteq> sets M"
    by (intro image_subsetI Ak)
  have "measure M {\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
        l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
      \<le> (\<Sum>k\<in>{1..\<lfloor>2^j * T\<rfloor>}. measure M {\<omega> \<in> space M.
          l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>})"
    unfolding seteq
    by (rule P.finite_measure_subadditive_finite[OF _ Asub]) simp
  also have "\<dots> \<le> (\<Sum>k\<in>{1..\<lfloor>2^j * T\<rfloor>}. 8*C\<^sup>2*(1/2^j)\<^sup>2 / l^4)"
    by (rule sum_mono[OF perk])
  also have "\<dots> = real (nat \<lfloor>2^j * T\<rfloor>) * (8*C\<^sup>2*(1/2^j)\<^sup>2 / l^4)"
    by simp
  also have "\<dots> \<le> (2^j * T) * (8*C\<^sup>2*(1/2^j)\<^sup>2 / l^4)"
  proof (rule mult_right_mono)
    have nn: "0 \<le> \<lfloor>2^j * T\<rfloor>" using T0 by simp
    have "real (nat \<lfloor>2^j * T\<rfloor>) = real_of_int \<lfloor>2^j * T\<rfloor>" using nn by simp
    also have "\<dots> \<le> 2^j * T" by (rule of_int_floor_le)
    finally show "real (nat \<lfloor>2^j * T\<rfloor>) \<le> 2^j * T" .
    show "0 \<le> 8*C\<^sup>2*(1/2^j)\<^sup>2 / l^4" using l by simp
  qed
  also have "\<dots> = 8*C\<^sup>2*T*(1/2^j) / l^4"
  proof -
    have twoj: "(2::real)^j * ((1/2^j) * (1/2^j)) = 1/2^j"
      by simp
    have "(2^j * T) * (8*C\<^sup>2*(1/2^j)\<^sup>2 / l^4)
        = (8*C\<^sup>2*(2^j * ((1/2^j) * (1/2^j)))*T) / l^4"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = (8*C\<^sup>2*(1/2^j)*T) / l^4"
      unfolding twoj by (rule refl)
    also have "\<dots> = 8*C\<^sup>2*T*(1/2^j) / l^4"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

text \<open>The bounded package discharges the abstract hypotheses.\<close>

lemma dyadic_level_tail:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and T0: "0 \<le> T"
    and A_int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (A u)"
    and A_rate: "AE \<omega> in M. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and covA: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> AE \<omega> in M.
        cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F u) (\<lambda>\<omega>. A v \<omega> - A u \<omega>) \<omega>"
    and C: "0 \<le> C" and R: "0 \<le> R"
    and bnd: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. \<bar>X u \<omega>\<bar> \<le> R"
    and cont: "AE \<omega> in M. continuous_on {0..T} (\<lambda>u. X u \<omega>)"
    and l: "0 < l"
  shows "measure M {\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
            l \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
           \<le> 8*C\<^sup>2*T*(1/2^j) / l^4"
proof -
  interpret MX: martingale M F "0::real" X by (rule X)
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule borel_measurable_integrable[OF MX.integrable[OF that]])
  have q4: "integrable M (\<lambda>\<omega>. (X u \<omega>)^4)" if "0 \<le> u" for u
    by (rule integrable_pow4_of_bounded[OF P Xmeas[OF that] R bnd[OF that]])
  show ?thesis
  proof (rule dyadic_level_tail_mom[OF P Xmeas _ _ T0 l])
    fix u v :: real assume uv: "0 \<le> u" "u \<le> v" "v \<le> T"
    have v0: "0 \<le> v" using uv by linarith
    show "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
      by (rule integrable_pow4_diff[OF q4[OF v0] q4[OF uv(1)]
            Xmeas[OF v0] Xmeas[OF uv(1)]])
    show "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
      by (rule fourth_moment_bound_subinterval[OF P X order.refl T0
            A_int A_rate covA C R bnd cont uv])
  qed
qed

subsection \<open>The geometric form of the level bound\<close>

lemma powr_level_calc:
  fixes \<gamma> B :: real and j :: nat
  shows "B*(1/2^j) / (2 powr (-\<gamma>*real j))^4 = B * (2 powr (-(1-4*\<gamma>)))^j"
proof -
  have p4: "(2 powr (-\<gamma>*real j))^4 = 2 powr (-\<gamma>*real j*4)"
    by (subst powr_realpow[symmetric]) (simp_all add: powr_powr)
  have p1: "(1::real)/2^j = 2 powr (- real j)"
    by (subst powr_realpow[symmetric]) (simp_all add: powr_minus_divide)
  have pq: "(2 powr (-(1-4*\<gamma>)))^j = 2 powr (-(1-4*\<gamma>)*real j)"
    by (subst powr_realpow[symmetric]) (simp_all add: powr_powr)
  have "B*(1/2^j) / (2 powr (-\<gamma>*real j))^4
      = B * (2 powr (- real j) / 2 powr (-\<gamma>*real j*4))"
    unfolding p4 p1 by simp
  also have "2 powr (- real j) / 2 powr (-\<gamma>*real j*4)
      = 2 powr (- real j - -\<gamma>*real j*4)"
    by (rule powr_diff[symmetric])
  also have "- real j - -\<gamma>*real j*4 = -(1-4*\<gamma>)*real j"
    by algebra
  finally show ?thesis unfolding pq by simp
qed

lemma powr_ratio_lt_1:
  fixes \<gamma> :: real
  assumes "\<gamma> < 1/4"
  shows "2 powr (-(1-4*\<gamma>)) < 1"
proof -
  have "(-(1-4*\<gamma>)) < 0" using assms by simp
  hence "2 powr (-(1-4*\<gamma>)) < 2 powr 0"
    by (intro powr_less_mono) simp_all
  thus ?thesis by simp
qed

subsection \<open>The bad event over all levels at once\<close>

text \<open>
  The union over levels \<open>j \<ge> n\<close> of the level-\<open>j\<close> bad events, with the geometric
  thresholds \<open>2 powr (-\<gamma> j)\<close>. For \<open>\<gamma> < 1/4\<close> the level bounds are geometric with
  ratio \<open>q = 2 powr (-(1-4\<gamma>)) < 1\<close>, so the tail sum is \<open>q^n/(1-q)\<close> --- decaying
  in \<open>n\<close>, uniformly over every law satisfying the hypotheses.
\<close>

theorem dyadic_bad_event_tail_mom:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and Xm: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and int4: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
    and mom: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T \<Longrightarrow>
        (\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
    and T0: "0 \<le> T"
    and g2: "\<gamma> < 1/4"
  shows "measure M {\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
            2 powr (-\<gamma>*real j)
              \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
         \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))"
proof -
  interpret P: prob_space M by (rule P)
  let ?q = "2 powr (-(1-4*\<gamma>))"
  define E where "E j = {\<omega> \<in> space M. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}" for j
  have q0: "0 < ?q" by simp
  have q1: "?q < 1" by (rule powr_ratio_lt_1[OF g2])
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule Xm[OF that])
  have Esets: "E j \<in> sets M" for j
  proof -
    have "{\<omega> \<in> space M. 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>} \<in> sets M"
      if k: "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for k
    proof -
      have "0 \<le> real_of_int (k - 1) / 2^j" "0 \<le> real_of_int k / 2^j"
        using k by simp_all
      from Xmeas[OF this(1)] Xmeas[OF this(2)] show ?thesis by measurable
    qed
    moreover have "E j = (\<Union>k\<in>{1..\<lfloor>2^j * T\<rfloor>}. {\<omega> \<in> space M. 2 powr (-\<gamma>*real j)
            \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>})"
      unfolding E_def by auto
    ultimately show ?thesis
      by (metis (lifting) countable_Un_Int(1))
  qed
  have lvl: "measure M (E j) \<le> 8*C\<^sup>2*T * ?q^j" for j
  proof -
    have "measure M (E j) \<le> 8*C\<^sup>2*T*(1/2^j) / (2 powr (-\<gamma>*real j))^4"
      unfolding E_def
      by (rule dyadic_level_tail_mom[OF P Xm int4 mom T0]) simp_all
    also have "\<dots> = 8*C\<^sup>2*T * ?q^j"
      by (rule powr_level_calc)
    finally show ?thesis .
  qed
  have shifted: "measure M (E (n + m)) \<le> 8*C\<^sup>2*T * ?q^n * ?q^m" for m
    using lvl[of "n + m"] by (simp add: power_add mult.assoc)
  have geo: "summable (\<lambda>m. 8*C\<^sup>2*T * ?q^n * ?q^m)"
    by (intro summable_mult summable_geometric) (use q0 q1 in auto)
  have msum: "summable (\<lambda>m. measure M (E (n + m)))"
  proof (rule summable_comparison_test'[OF geo])
    fix m :: nat
    show "norm (measure M (E (n + m))) \<le> 8*C\<^sup>2*T * ?q^n * ?q^m"
      using shifted[of m] by simp
  qed
  have s1: "{\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
      2 powr (-\<gamma>*real j)
        \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
      = (\<Union>j\<in>{n..}. E j)"
    unfolding E_def by auto
  have s2: "(\<Union>j\<in>{n..}. E j) = (\<Union>m. E (n + m))"
  proof -
    have "(\<Union>j\<in>{n..}. E j) \<subseteq> (\<Union>m. E (n + m))"
    proof
      fix x assume "x \<in> (\<Union>j\<in>{n..}. E j)"
      then obtain j where j: "n \<le> j" "x \<in> E j" by auto
      from j(1) obtain m where "j = n + m" using le_Suc_ex by blast
      with j(2) show "x \<in> (\<Union>m. E (n + m))" by auto
    qed
    moreover have "(\<Union>m. E (n + m)) \<subseteq> (\<Union>j\<in>{n..}. E j)"
    proof
      fix x assume "x \<in> (\<Union>m. E (n + m))"
      then obtain m where "x \<in> E (n + m)" by auto
      thus "x \<in> (\<Union>j\<in>{n..}. E j)" by (intro UN_I[of "n + m"]) simp_all
    qed
    ultimately show ?thesis by blast
  qed
  have "measure M (\<Union>m. E (n + m)) \<le> (\<Sum>m. measure M (E (n + m)))"
    by (rule P.finite_measure_subadditive_countably) (use Esets msum in auto)
  also have "\<dots> \<le> (\<Sum>m. 8*C\<^sup>2*T * ?q^n * ?q^m)"
    by (rule suminf_le[OF shifted msum geo])
  also have "\<dots> = 8*C\<^sup>2*T * ?q^n * (\<Sum>m. ?q^m)"
    by (rule suminf_mult)
       (intro summable_geometric, use q0 q1 in auto)
  also have "(\<Sum>m. ?q^m) = 1 / (1 - ?q)"
    using q0 q1 by (simp add: suminf_geometric)
  also have "8*C\<^sup>2*T * ?q^n * (1 / (1 - ?q)) = 8*C\<^sup>2*T * ?q^n / (1 - ?q)"
    by simp
  finally have res: "measure M (\<Union>m. E (n + m))
      \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))" .
  show ?thesis unfolding s1 s2 by (rule res)
qed

corollary dyadic_bad_event_tail:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and T0: "0 \<le> T"
    and A_int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (A u)"
    and A_rate: "AE \<omega> in M. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and covA: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> AE \<omega> in M.
        cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F u) (\<lambda>\<omega>. A v \<omega> - A u \<omega>) \<omega>"
    and C: "0 \<le> C" and R: "0 \<le> R"
    and bnd: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. \<bar>X u \<omega>\<bar> \<le> R"
    and cont: "AE \<omega> in M. continuous_on {0..T} (\<lambda>u. X u \<omega>)"
    and g2: "\<gamma> < 1/4"
  shows "measure M {\<omega> \<in> space M. \<exists>j\<ge>n. \<exists>k\<in>{1..\<lfloor>2^j * T\<rfloor>}.
            2 powr (-\<gamma>*real j)
              \<le> \<bar>X (real_of_int k / 2^j) \<omega> - X (real_of_int (k - 1) / 2^j) \<omega>\<bar>}
         \<le> 8*C\<^sup>2*T * (2 powr (-(1-4*\<gamma>)))^n / (1 - 2 powr (-(1-4*\<gamma>)))"
proof -
  interpret MX: martingale M F "0::real" X by (rule X)
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule borel_measurable_integrable[OF MX.integrable[OF that]])
  have q4: "integrable M (\<lambda>\<omega>. (X u \<omega>)^4)" if "0 \<le> u" for u
    by (rule integrable_pow4_of_bounded[OF P Xmeas[OF that] R bnd[OF that]])
  show ?thesis
  proof (rule dyadic_bad_event_tail_mom[OF P Xmeas _ _ T0 g2])
    fix u v :: real assume uv: "0 \<le> u" "u \<le> v" "v \<le> T"
    have v0: "0 \<le> v" using uv by linarith
    show "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
      by (rule integrable_pow4_diff[OF q4[OF v0] q4[OF uv(1)]
            Xmeas[OF v0] Xmeas[OF uv(1)]])
    show "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
      by (rule fourth_moment_bound_subinterval[OF P X order.refl T0
            A_int A_rate covA C R bnd cont uv])
  qed
qed

subsection \<open>The modulus bound on the complement of the bad event\<close>

lemma geometric_tail_sum_le:
  fixes r :: real
  assumes r0: "0 \<le> r" and r1: "r < 1"
  shows "(\<Sum>j\<in>{n<..m}. r^j) \<le> r^Suc n / (1 - r)"
proof (cases "n \<le> m")
  case True
  have iv: "{n<..m} = {Suc n..<Suc m}" by auto
  have "(\<Sum>j\<in>{Suc n..<Suc m}. r^j) = (\<Sum>i\<in>{0..<Suc m - Suc n}. r^(i + Suc n))"
    using sum.shift_bounds_nat_ivl[of "\<lambda>j. r^j" 0 "Suc n" "Suc m - Suc n"] True
    by simp
  also have "\<dots> = r^Suc n * (\<Sum>i\<in>{0..<Suc m - Suc n}. r^i)"
    by (simp add: power_add sum_distrib_left mult_ac)
  also have "\<dots> \<le> r^Suc n * (1 / (1 - r))"
  proof (rule mult_left_mono)
    have "(\<Sum>i\<in>{0..<Suc m - Suc n}. r^i) \<le> (\<Sum>i. r^i)"
      by (rule sum_le_suminf)
         (use r0 r1 summable_geometric[of r] in auto)
    also have "\<dots> = 1 / (1 - r)"
      using r0 r1 by (simp add: suminf_geometric)
    finally show "(\<Sum>i\<in>{0..<Suc m - Suc n}. r^i) \<le> 1 / (1 - r)" .
    show "0 \<le> r^Suc n" using r0 by simp
  qed
  finally show ?thesis unfolding iv by simp
next
  case False
  hence "{n<..m} = {}" by auto
  moreover have "0 \<le> r^Suc n / (1 - r)"
    using r0 r1 by (intro divide_nonneg_pos) simp_all
  ultimately show ?thesis by simp
qed

text \<open>
  The deterministic conclusion: a continuous path whose level-\<open>j\<close> dyadic
  increments stay below \<open>2 powr (-\<gamma> j)\<close> for every level \<open>j \<ge> n\<close> has modulus
  of continuity at most \<open>3 \<cdot> 2 powr (-\<gamma> n) / (1 - 2 powr (-\<gamma>))\<close> at scale
  \<open>1/2^n\<close>, on all of \<open>{0..T}\<close>. Together with \<open>dyadic_bad_event_tail\<close> this is
  the quantitative Kolmogorov tail estimate: both the threshold and the
  exceptional probability are explicit in \<open>(C, T, \<gamma>, n)\<close> and decay
  geometrically in \<open>n\<close>.
\<close>

theorem modulus_of_good_path:
  fixes f :: "real \<Rightarrow> real" and \<gamma> T :: real
  assumes cont: "continuous_on {0..T} f"
    and good: "\<And>j k. n \<le> j \<Longrightarrow> k \<in> {1..\<lfloor>2^j * T\<rfloor>} \<Longrightarrow>
        \<bar>f (real_of_int k / 2^j) - f (real_of_int (k - 1) / 2^j)\<bar> \<le> 2 powr (-\<gamma>*real j)"
    and g0: "0 < \<gamma>"
    and u: "u \<in> {0..T}" and v: "v \<in> {0..T}"
    and gap: "\<bar>u - v\<bar> < 1 / 2 ^ n"
  shows "\<bar>f u - f v\<bar> \<le> 3 * 2 powr (-\<gamma>*real n) / (1 - 2 powr (-\<gamma>))"
proof -
  let ?r = "2 powr (-\<gamma>)"
  have r0: "0 < ?r" by simp
  have r1: "?r < 1"
  proof -
    have "(-\<gamma>) < 0" using g0 by simp
    hence "2 powr (-\<gamma>) < 2 powr 0" by (intro powr_less_mono) simp_all
    thus ?thesis by simp
  qed
  have pos: "0 < 1 - ?r" using r1 by simp
  have cj: "2 powr (-\<gamma>*real j) = ?r^j" for j
    by (subst powr_realpow[symmetric]) (simp_all add: powr_powr)
  have K: "dist (f w) (f z) \<le> 3 * 2 powr (-\<gamma>*real n) / (1 - ?r)"
    if w: "w \<in> dyadic_interval_step m 0 T" and z: "z \<in> dyadic_interval_step m 0 T"
      and wz: "\<bar>w - z\<bar> \<le> 1 / 2 ^ n" for m w z
  proof -
    define m' where "m' = max m n"
    have mm: "m \<le> m'" and nm: "n \<le> m'" unfolding m'_def by simp_all
    have w': "w \<in> dyadic_interval_step m' 0 T"
      by (rule dyadic_interval_step_mono[OF w mm])
    have z': "z \<in> dyadic_interval_step m' 0 T"
      by (rule dyadic_interval_step_mono[OF z mm])
    have H: "dist (f (real_of_int (k - 1) / 2 ^ j)) (f (real_of_int k / 2 ^ j))
              \<le> 2 powr (-\<gamma>*real j)"
      if "n \<le> j" "j \<le> m'" "k \<in> {1..\<lfloor>2 ^ j * T\<rfloor>}" for j k
      using good[OF that(1) that(3)] by (simp add: dist_real_def abs_minus_commute)
    have S1: "(\<Sum>j\<in>{n<..m'}. 2 powr (-\<gamma>*real j)) \<le> ?r^Suc n / (1 - ?r)"
      unfolding cj by (rule geometric_tail_sum_le) (use r0 r1 in simp_all)
    have "dist (f w) (f z)
        \<le> 2 powr (-\<gamma>*real n) + 2 * (\<Sum>j\<in>{n<..m'}. 2 powr (-\<gamma>*real j))"
      by (rule dyadic_chaining[where f=f, OF w' z' wz nm H]) simp_all
    also have "\<dots> \<le> ?r^n + 2 * (?r^Suc n / (1 - ?r))"
      using S1 cj[of n] by linarith
    also have "\<dots> \<le> 3 * ?r^n / (1 - ?r)"
    proof -
      have ne: "1 - ?r \<noteq> 0" using pos by linarith
      have e1: "(?r^n * (1 - ?r) + 2 * ?r^Suc n) / (1 - ?r)
          = ?r^n + 2 * (?r^Suc n / (1 - ?r))"
      proof -
        have "(?r^n * (1 - ?r) + 2 * ?r^Suc n) / (1 - ?r)
            = ?r^n * (1 - ?r) / (1 - ?r) + 2 * ?r^Suc n / (1 - ?r)"
          by (rule add_divide_distrib)
        also have "?r^n * (1 - ?r) / (1 - ?r) = ?r^n"
          by (rule nonzero_mult_div_cancel_right[OF ne])
        finally show ?thesis by simp
      qed
      have e2: "?r^n * (1 - ?r) + 2 * ?r^Suc n = ?r^n + ?r^Suc n"
        by (simp add: algebra_simps)
      have le1: "?r^Suc n \<le> ?r^n"
        by (intro power_decreasing) (use r0 r1 in simp_all)
      have rn0: "0 \<le> ?r^n"
        by (rule zero_le_power[OF less_imp_le[OF r0]])
      have e3: "?r^n + ?r^Suc n \<le> 3 * ?r^n"
        using le1 rn0 by linarith
      have "(?r^n + ?r^Suc n) / (1 - ?r) \<le> (3 * ?r^n) / (1 - ?r)"
        by (rule divide_right_mono[OF e3]) (use pos in simp)
      thus ?thesis unfolding e1[symmetric] e2 by simp
    qed
    also have "3 * ?r^n / (1 - ?r) = 3 * 2 powr (-\<gamma>*real n) / (1 - ?r)"
      unfolding cj[of n] by (rule refl)
    finally show ?thesis .
  qed
  have "dist (f u) (f v) \<le> 3 * 2 powr (-\<gamma>*real n) / (1 - ?r)"
    by (rule dyadic_modulus_extension[OF cont K u v gap])
  thus ?thesis by (simp add: dist_real_def)
qed


(*<*)
end
(*>*)
