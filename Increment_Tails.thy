section \<open>Tail bounds from the fourth-moment estimate\<close>

text \<open>
  Plan step A4 (STATUS.md 25h), first tranche: the quantitative tail estimates
  that turn Eq. (2.7) into tightness. The AFP's Kolmogorov-Chentsov theorem
  produces a continuous MODIFICATION but not the tail bound on the modulus of
  continuity that Lemma 2.2 of arXiv:2512.17702 needs; that bound is assembled
  here from Markov's inequality and a union bound over one partition level.
  The chaining over dyadic levels is the following step.
\<close>

theory Increment_Tails
  imports Increment_Moments
begin

subsection \<open>Markov's inequality at the fourth power\<close>

lemma abs_pow4: "\<bar>x::real\<bar>^4 = x^4"
proof -
  have "\<bar>x\<bar>^4 = (\<bar>x\<bar>\<^sup>2)\<^sup>2" by algebra
  also have "\<dots> = (x\<^sup>2)\<^sup>2" by simp
  also have "\<dots> = x^4" by algebra
  finally show ?thesis .
qed

lemma fourth_moment_tail:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and fm[measurable]: "f \<in> borel_measurable M"
    and f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)"
    and l: "0 < l"
  shows "measure M {\<omega> \<in> space M. l \<le> \<bar>f \<omega>\<bar>} \<le> (\<integral>\<omega>. (f \<omega>)^4 \<partial>M) / l^4"
proof -
  have seteq: "{\<omega> \<in> space M. l \<le> \<bar>f \<omega>\<bar>} = {\<omega> \<in> space M. l^4 \<le> (f \<omega>)^4}"
  proof (intro Collect_cong conj_cong refl iffI)
    fix \<omega>
    assume "l \<le> \<bar>f \<omega>\<bar>"
    hence "l^4 \<le> \<bar>f \<omega>\<bar>^4" using l by (intro power_mono) simp_all
    thus "l^4 \<le> (f \<omega>)^4" by (simp add: abs_pow4)
  next
    fix \<omega>
    assume "l^4 \<le> (f \<omega>)^4"
    hence h4: "l ^ Suc 3 \<le> \<bar>f \<omega>\<bar> ^ Suc 3"
      by (simp add: abs_pow4 eval_nat_numeral)
    show "l \<le> \<bar>f \<omega>\<bar>" by (rule power_le_imp_le_base[OF h4 abs_ge_zero])
  qed
  have l4: "0 < l^4" using l by simp
  have "measure M {\<omega> \<in> space M. l^4 \<le> (f \<omega>)^4} \<le> (\<integral>\<omega>. (f \<omega>)^4 \<partial>M) / l^4"
  proof (rule integral_Markov_inequality_measure)
    show "integrable M (\<lambda>\<omega>. (f \<omega>)^4)" by (rule f4)
    show "space M \<in> sets M" by (rule sets.top)
    show "AE \<omega> in M. 0 \<le> (f \<omega>)^4" by (intro AE_I2 pow4_nonneg)
    show "0 < l^4" by (rule l4)
  qed
  thus ?thesis by (simp add: seteq)
qed

subsection \<open>Eq. (2.7) on subintervals\<close>

corollary fourth_moment_bound_subinterval:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and s0: "0 \<le> s" and sT: "s \<le> T"
    and A_int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (A u)"
    and A_rate: "AE \<omega> in M. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and covA: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> AE \<omega> in M.
        cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F u) (\<lambda>\<omega>. A v \<omega> - A u \<omega>) \<omega>"
    and C: "0 \<le> C" and R: "0 \<le> R"
    and bnd: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. \<bar>X u \<omega>\<bar> \<le> R"
    and cont: "AE \<omega> in M. continuous_on {s..T} (\<lambda>u. X u \<omega>)"
    and uv: "s \<le> u" "u \<le> v" "v \<le> T"
  shows "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(v - u)\<^sup>2"
proof (rule fourth_moment_bound_bounded[OF P X _ _ A_int A_rate covA C R bnd])
  show "0 \<le> u" using s0 uv(1) by linarith
  show "u \<le> v" by (rule uv(2))
  show "AE \<omega> in M. continuous_on {u..v} (\<lambda>w. X w \<omega>)"
    using cont
  proof eventually_elim
    case (elim \<omega>)
    have "{u..v} \<subseteq> {s..T}" using uv by auto
    thus "continuous_on {u..v} (\<lambda>w. X w \<omega>)"
      by (rule continuous_on_subset[OF elim])
  qed
qed

subsection \<open>The tail bound at one partition level\<close>

text \<open>
  The union bound over the increments of the \<open>m\<close>-th uniform partition. The bound
  DECAYS like \<open>1 / Suc m\<close>: refining the partition by a factor halves the tail,
  which is what makes the dyadic chaining sum converge.
\<close>

theorem partition_max_tail_bound:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and s0: "0 \<le> s" and sT: "s \<le> T"
    and A_int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (A u)"
    and A_rate: "AE \<omega> in M. \<forall>u v. 0 \<le> u \<longrightarrow> u \<le> v \<longrightarrow>
                    0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
    and covA: "\<And>u v. 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> AE \<omega> in M.
        cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F u) (\<lambda>\<omega>. A v \<omega> - A u \<omega>) \<omega>"
    and C: "0 \<le> C" and R: "0 \<le> R"
    and bnd: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. \<bar>X u \<omega>\<bar> \<le> R"
    and cont: "AE \<omega> in M. continuous_on {s..T} (\<lambda>u. X u \<omega>)"
    and l: "0 < l"
  shows "measure M {\<omega> \<in> space M. \<exists>k<Suc m.
            l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>}
           \<le> 8*C\<^sup>2*(T - s)\<^sup>2 / (real (Suc m) * l^4)"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule borel_measurable_integrable[OF MX.integrable[OF that]])
  have upt_nn: "0 \<le> upart s T m k" for k by (rule upart_nonneg[OF s0 sT])
  have XmM[measurable]: "X (upart s T m k) \<in> borel_measurable M" for k
    by (rule Xmeas[OF upt_nn])
  have q4: "integrable M (\<lambda>\<omega>. (X u \<omega>)^4)" if "0 \<le> u" for u
    by (rule integrable_pow4_of_bounded[OF P Xmeas[OF that] R bnd[OF that]])
  have iY4: "integrable M (\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)^4)" for k
    by (rule integrable_pow4_diff[OF q4[OF upt_nn] q4[OF upt_nn] XmM XmM])
  have Ak: "{\<omega> \<in> space M. l \<le> \<bar>X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>\<bar>} \<in> sets M" for k
    by measurable
  have seteq: "{\<omega> \<in> space M. \<exists>k<Suc m.
        l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>}
      = (\<Union>k\<in>{..<Suc m}. {\<omega> \<in> space M.
          l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>})"
    by auto
  have perk: "measure M {\<omega> \<in> space M.
        l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>}
      \<le> 8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2 / l^4" for k
  proof -
    have "measure M {\<omega> \<in> space M.
          l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>}
        \<le> (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)^4 \<partial>M) / l^4"
      by (rule fourth_moment_tail[OF P _ iY4 l]) measurable
    also have "\<dots> \<le> 8*C\<^sup>2*(upart s T m (Suc k) - upart s T m k)\<^sup>2 / l^4"
    proof (rule divide_right_mono)
      have kk: "upart s T m k \<le> upart s T m (Suc k)"
        using monoD[OF upart_mono[OF sT], of k "Suc k"] by simp
      show "(\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)^4 \<partial>M)
              \<le> 8*C\<^sup>2*(upart s T m (Suc k) - upart s T m k)\<^sup>2"
        by (rule fourth_moment_bound_subinterval[OF P X s0 sT A_int A_rate
              covA C R bnd cont upart_ge_s[OF sT] kk upart_le_T[OF sT]])
           simp_all
      show "0 \<le> l^4" using l by simp
    qed
    also have "\<dots> \<le> 8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2 / l^4"
    proof (rule divide_right_mono)
      have d1: "upart s T m (Suc k) - upart s T m k \<le> (T - s)/real (Suc m)"
        by (rule upart_diff_le[OF sT])
      have d2: "0 \<le> upart s T m (Suc k) - upart s T m k"
        using monoD[OF upart_mono[OF sT], of k "Suc k"] by simp
      have "(upart s T m (Suc k) - upart s T m k)\<^sup>2 \<le> ((T - s)/real (Suc m))\<^sup>2"
        by (rule power_mono[OF d1 d2])
      thus "8*C\<^sup>2*(upart s T m (Suc k) - upart s T m k)\<^sup>2
              \<le> 8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2"
        by (intro mult_left_mono) simp_all
      show "0 \<le> l^4" using l by simp
    qed
    finally show ?thesis .
  qed
  have "measure M {\<omega> \<in> space M. \<exists>k<Suc m.
        l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>}
      = measure M (\<Union>k\<in>{..<Suc m}. {\<omega> \<in> space M.
          l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>})"
    by (simp add: seteq)
  also have "\<dots> \<le> (\<Sum>k<Suc m. measure M {\<omega> \<in> space M.
          l \<le> \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>})"
    by (rule P.finite_measure_subadditive_finite) (auto intro: Ak)
  also have "\<dots> \<le> (\<Sum>k<Suc m. 8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2 / l^4)"
    by (rule sum_mono[OF perk])
  also have "\<dots> = real (Suc m) * (8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2 / l^4)"
    by simp
  also have "\<dots> = 8*C\<^sup>2*(T - s)\<^sup>2 / (real (Suc m) * l^4)"
  proof -
    have n0: "real (Suc m) \<noteq> 0" by simp
    have Ts: "real (Suc m) * ((T - s)/real (Suc m)) = T - s" by simp
    have num: "real (Suc m) * (real (Suc m) * (8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2))
        = 8*C\<^sup>2*(T - s)\<^sup>2"
    proof -
      have "real (Suc m) * (real (Suc m) * (8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2))
          = 8*C\<^sup>2*((real (Suc m) * ((T - s)/real (Suc m)))
                   * (real (Suc m) * ((T - s)/real (Suc m))))"
        by (simp add: power2_eq_square algebra_simps)
      thus ?thesis unfolding Ts power2_eq_square .
    qed
    have "real (Suc m) * (8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2 / l^4)
        = (real (Suc m) * (real (Suc m) * (8*C\<^sup>2*((T - s)/real (Suc m))\<^sup>2)))
            / (real (Suc m) * l^4)"
      by (subst mult_divide_mult_cancel_left[OF n0]) simp
    also have "\<dots> = 8*C\<^sup>2*(T - s)\<^sup>2 / (real (Suc m) * l^4)"
      unfolding num by (rule refl)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

end
