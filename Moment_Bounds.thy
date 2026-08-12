section \<open>The fourth-moment bound of Eq. (2.7)\<close>

text \<open>
  Lemma 2.2 of arXiv:2512.17702 rests on the estimate of Eq. (2.7),
  \<open>E |X t - X s| ^ 4 <= 66 * C ^ 2 * (t - s) ^ 2\<close>, which the paper derives by
  applying Ito's formula to the auxiliary process
  \<open>Z t = |X t - X s| ^ 2 - tr (qvar X t) + tr (qvar X s)\<close>
  -- a martingale, because \<open>X\<close> is -- and then bounding its second moment.

  The test function is quadratic. Lemma 2.2 does not need Ito's formula for
  general \<open>C ^ 2\<close> functions, only for \<open>|x| ^ 2\<close>, which is exactly the shape
  of the \<open>Z_martingale\<close> assumption of the locale \<open>ito_volatile_market\<close>.

  This theory isolates the assembly step, which is pure integration theory
  and needs no stochastic calculus: given a second-moment bound on the
  compensated martingale and the rate bound on the trace of the covariation,
  the fourth moment of the increment follows; everything from those two
  inputs to Eq. (2.7) is proved here.
\<close>

theory Moment_Bounds
  imports "HOL-Probability.Probability"
begin

subsection \<open>An elementary square inequality\<close>

lemma square_add_le_two:
  fixes a b :: real
  shows "(a + b)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * b\<^sup>2"
proof -
  have "0 \<le> (a - b)\<^sup>2" by simp
  thus ?thesis by (simp add: power2_eq_square algebra_simps)
qed

subsection \<open>A bounded function has a bounded second moment\<close>

lemma (in prob_space) integral_square_le_of_bound:
  fixes T :: "'a \<Rightarrow> real"
  assumes Tint: "integrable M (\<lambda>w. (T w)\<^sup>2)" and B: "0 \<le> B"
    and bnd: "\<And>w. w \<in> space M \<Longrightarrow> \<bar>T w\<bar> \<le> B"
  shows "(\<integral> w. (T w)\<^sup>2 \<partial>M) \<le> B\<^sup>2"
proof -
  have "(\<integral> w. (T w)\<^sup>2 \<partial>M) \<le> (\<integral> w. B\<^sup>2 \<partial>M)"
  proof (rule integral_mono)
    show "integrable M (\<lambda>w. (T w)\<^sup>2)" by (rule Tint)
    show "integrable M (\<lambda>w. B\<^sup>2)" by simp
    show "(T w)\<^sup>2 \<le> B\<^sup>2" if "w \<in> space M" for w
    proof -
      have "(T w)\<^sup>2 = \<bar>T w\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> B\<^sup>2" using bnd[OF that] by (intro power_mono) auto
      finally show ?thesis .
    qed
  qed
  also have "(\<integral> w. B\<^sup>2 \<partial>M) = B\<^sup>2" by (simp add: prob_space)  finally show ?thesis .
qed

subsection \<open>Assembling Eq. (2.7)\<close>

text \<open>
  Here @{term D} is the squared increment \<open>|X t - X s| ^ 2\<close>, split by Ito's
  formula as a compensated martingale @{term Z} plus the increment @{term T} of
  the trace of the covariation. The conclusion is the fourth-moment bound, since
  @{term "(D w)\<^sup>2"} is \<open>|X t - X s| ^ 4\<close>.
\<close>

theorem (in prob_space) fourth_moment_of_compensated:
  fixes Z T D :: "'a \<Rightarrow> real"
  assumes split: "\<And>w. w \<in> space M \<Longrightarrow> D w = Z w + T w"
    and Zint: "integrable M (\<lambda>w. (Z w)\<^sup>2)"
    and Tint: "integrable M (\<lambda>w. (T w)\<^sup>2)"
    and Dint: "integrable M (\<lambda>w. (D w)\<^sup>2)"
    and Zbnd: "(\<integral> w. (Z w)\<^sup>2 \<partial>M) \<le> K * (t - s)\<^sup>2"
    and Tbnd: "\<And>w. w \<in> space M \<Longrightarrow> \<bar>T w\<bar> \<le> C * (t - s)"
    and C: "0 \<le> C" and ts: "s \<le> t"
  shows "(\<integral> w. (D w)\<^sup>2 \<partial>M) \<le> (2 * K + 2 * C\<^sup>2) * (t - s)\<^sup>2"
proof -
  have B: "0 \<le> C * (t - s)" using C ts by simp
  have "(\<integral> w. (D w)\<^sup>2 \<partial>M) \<le> (\<integral> w. 2 * (Z w)\<^sup>2 + 2 * (T w)\<^sup>2 \<partial>M)"
  proof (rule integral_mono)
    show "integrable M (\<lambda>w. (D w)\<^sup>2)" by (rule Dint)
    show "integrable M (\<lambda>w. 2 * (Z w)\<^sup>2 + 2 * (T w)\<^sup>2)"
      using Zint Tint by simp
    show "(D w)\<^sup>2 \<le> 2 * (Z w)\<^sup>2 + 2 * (T w)\<^sup>2" if "w \<in> space M" for w
      using split[OF that] square_add_le_two[of "Z w" "T w"] by simp
  qed
  also have "(\<integral> w. 2 * (Z w)\<^sup>2 + 2 * (T w)\<^sup>2 \<partial>M)
             = 2 * (\<integral> w. (Z w)\<^sup>2 \<partial>M) + 2 * (\<integral> w. (T w)\<^sup>2 \<partial>M)"
    using Zint Tint by simp
  also have "\<dots> \<le> 2 * (K * (t - s)\<^sup>2) + 2 * (C * (t - s))\<^sup>2"
  proof (intro add_mono mult_left_mono Zbnd)
    show "(\<integral> w. (T w)\<^sup>2 \<partial>M) \<le> (C * (t - s))\<^sup>2"
      by (rule integral_square_le_of_bound[OF Tint B Tbnd])
  qed auto
  also have "\<dots> = (2 * K + 2 * C\<^sup>2) * (t - s)\<^sup>2"
    unfolding power_mult_distrib by (simp add: algebra_simps)
  finally show ?thesis .
qed

end
