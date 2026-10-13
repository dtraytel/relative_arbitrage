section \<open>The uniform modulus-of-continuity tail bound\<close>

(*<*)
theory Modulus_Tails
  imports Increment_Tails Dyadic_Chaining
begin

(*>*)

text \<open>
  Combine the per-level dyadic tail bounds (from Eq. (2.7) via
  @{theory Continuous_Path_Spaces.Increment_Tails}) with the deterministic chaining of @{theory Continuous_Path_Spaces.Dyadic_Chaining}
  into the quantitative tail bound on the modulus of continuity. Both the
  modulus threshold and the exceptional probability are explicit in
  \<open>(C, T, \<gamma>, n)\<close> only --- uniformity over the family of admissible laws is
  exactly what tightness in Lemma 2.2 of \<^cite>\<open>LaiShkolnikovSoner\<close> consumes.
\<close>
subsection \<open>The bad event at one dyadic level\<close>

text \<open>
  The level bound in its abstract form: only measurability, integrability of
  the fourth powers and the Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> moment bound itself are consumed. The
  Lemma 2.2 there needs this for unbounded martingale laws, where (2.7)
  will be obtained by localization + Fatou.
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
  have q1: "?q < 1" by (rule powr_less_one) (use g2 in simp_all)
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
    by (auto dest: le_Suc_ex intro!: bexI[of _ "n + _"])
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

subsection \<open>The modulus bound on the complement of the bad event\<close>

lemma geometric_tail_sum_le:
  fixes r :: real
  assumes r0: "0 \<le> r" and r1: "r < 1"
  shows "(\<Sum>j\<in>{n<..m}. r^j) \<le> r^Suc n / (1 - r)"
proof (cases "n < m")
  case True
  have "{n<..m} = {Suc n..m}" by auto
  then show ?thesis
    using True r0 r1 by (simp add: sum_gp divide_right_mono)
next
  case False
  then show ?thesis using r0 r1 by simp
qed

text \<open>
  The chaining bound for pairs of dyadics, with no continuity hypothesis and in
  any metric space (\<open>dyadic_chaining\<close>): if every level-\<open>j\<close> dyadic increment,
  \<open>j \<ge> n\<close>, is at most \<open>E \<cdot> 2 powr (-\<gamma> j)\<close>, then two dyadics at distance at
  most \<open>1/2^n'\<close>, \<open>n' \<ge> n\<close>, are mapped at most
  \<open>3 E \<cdot> 2 powr (-\<gamma> n') / (1 - 2 powr (-\<gamma>))\<close> apart.
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
  have r1: "?r < 1" by (rule powr_less_one) (use g0 in simp_all)
  have cj: "2 powr (-\<gamma>*real j) = ?r^j" for j
    by (subst powr_realpow[symmetric]) (simp_all add: powr_powr)
  define m' where "m' = max m n'"
  have nm: "n' \<le> m'" unfolding m'_def by simp
  have w': "w \<in> dyadic_interval_step m' 0 T" and z': "z \<in> dyadic_interval_step m' 0 T"
    using dyadic_interval_step_mono[OF w] dyadic_interval_step_mono[OF z]
    unfolding m'_def by simp_all
  have "dist (f w) (f z)
      \<le> E * 2 powr (-\<gamma>*real n') + 2 * (\<Sum>j\<in>{n'<..m'}. E * 2 powr (-\<gamma>*real j))"
    by (rule dyadic_chaining[where f=f, OF w' z' wz nm])
       (use good[OF order.trans[OF nn']] E0 in simp_all)
  also have "\<dots> \<le> E * ?r^n' + 2 * (E * (?r^Suc n' / (1 - ?r)))"
    unfolding cj sum_distrib_left[symmetric]
    by (intro add_mono order_refl mult_left_mono geometric_tail_sum_le E0) (use r0 r1 in simp_all)
  also have "\<dots> = (E * ?r^n' * (1 - ?r) + 2 * (E * ?r^Suc n')) / (1 - ?r)"
    using r1 g0 by (simp add: add_divide_distrib)
  also have "\<dots> \<le> 3 * (E * ?r^n') / (1 - ?r)"
  proof (rule divide_right_mono)
    have "E * ?r^n' * (1 - ?r) \<le> E * ?r^n'"
      by (rule mult_left_le) (use E0 r0 r1 in simp_all)
    moreover have "E * ?r^Suc n' \<le> E * ?r^n'"
      by (intro mult_left_mono power_decreasing) (use E0 r0 r1 in simp_all)
    ultimately show "E * ?r^n' * (1 - ?r) + 2 * (E * ?r^Suc n') \<le> 3 * (E * ?r^n')"
      by linarith
  qed (use r1 in simp)
  finally show ?thesis unfolding cj by (simp only: mult.assoc)
qed

text \<open>
  The deterministic conclusion: a continuous path whose level-\<open>j\<close> dyadic
  increments stay below \<open>2 powr (-\<gamma> j)\<close> for every level \<open>j \<ge> n\<close> has modulus
  of continuity at most \<open>3 \<cdot> 2 powr (-\<gamma> n) / (1 - 2 powr (-\<gamma>))\<close> at scale
  \<open>1/2^n\<close>, on all of \<open>{0..T}\<close>. Together with \<open>dyadic_bad_event_tail_mom\<close> this is
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
  have good': "dist (f (real_of_int (k - 1) / 2^j)) (f (real_of_int k / 2^j))
      \<le> 1 * 2 powr (-\<gamma>*real j)" if "n \<le> j" "k \<in> {1..\<lfloor>2^j * T\<rfloor>}" for j k
    using good[OF that] by (simp add: dist_real_def abs_minus_commute)
  have "dist (f u) (f v) \<le> 3 * 1 * 2 powr (-\<gamma>*real n) / (1 - 2 powr (-\<gamma>))"
    by (rule dyadic_modulus_extension[OF cont
          dyadic_pair_modulus[OF good' g0 zero_le_one _ _ _ order_refl] u v gap])
  thus ?thesis by (simp add: dist_real_def)
qed


(*<*)
end
(*>*)
