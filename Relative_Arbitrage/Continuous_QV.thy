section \<open>Quadratic variation in continuous time, along dyadic partitions\<close>

(*<*)
theory Continuous_QV
  imports "Path_Space_Tightness.Increment_Moments"
begin
(*>*)

text \<open>
  Towards the \<open>P\<^sub>x\<close> bridge of \<open>OPEN_ITEMS.md\<close>: the covariation of a continuous
  martingale, obtained not from Doob--Meyer but as the limit of sums of squared
  increments along dyadic partitions.  Two payoffs over the abstract
  construction: the limit is a Borel functional of the path, so it can be used
  to build a law on the pair space, and it is adapted to the filtration of \<open>X\<close>
  alone.

  This theory is step T1 of that plan: the \<open>L\<^sup>2\<close> estimate with a rate.  The rate
  is what matters --- it is summable, so the full dyadic sequence converges
  almost surely and no subsequence is needed.
\<close>

subsection \<open>Martingales form a vector space\<close>

text \<open>The AFP entry does not record the difference; both integrability side
  conditions of \<open>cond_exp_diff\<close> come straight from the two locales.\<close>

lemma martingale_diff:
  fixes X Y :: "'b :: {second_countable_topology, order_topology, t2_space}
    \<Rightarrow> 'a \<Rightarrow> 'c :: {second_countable_topology, banach}"
  assumes MX: "martingale M F t0 X" and MY: "martingale M F t0 Y"
  shows "martingale M F t0 (\<lambda>i \<omega>. X i \<omega> - Y i \<omega>)"
proof -
  interpret MX: martingale M F t0 X by (rule MX)
  interpret MY: martingale M F t0 Y by (rule MY)
  show ?thesis
  proof (unfold_locales)
    show "\<And>i. t0 \<le> i \<Longrightarrow> (\<lambda>\<omega>. X i \<omega> - Y i \<omega>) \<in> borel_measurable (F i)"
      using MX.adapted MY.adapted by simp
    show "\<And>i. t0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<omega>. X i \<omega> - Y i \<omega>)"
      using MX.integrable MY.integrable by simp
    fix i j assume ij: "t0 \<le> i" "i \<le> j"
    then have j: "t0 \<le> j" by simp
    have "AE \<omega> in M. cond_exp M (F i) (\<lambda>\<omega>. X j \<omega> - Y j \<omega>) \<omega>
        = cond_exp M (F i) (X j) \<omega> - cond_exp M (F i) (Y j) \<omega>"
      by (rule sigma_finite_subalgebra.cond_exp_diff
            [OF MX.sigma_finite_subalgebra_F[OF ij(1)]
                MX.integrable[OF j] MY.integrable[OF j]])
    then show "AE \<omega> in M. X i \<omega> - Y i \<omega>
        = cond_exp M (F i) (\<lambda>\<omega>. X j \<omega> - Y j \<omega>) \<omega>"
      using MX.martingale_property[OF ij] MY.martingale_property[OF ij] by force
  qed
qed

subsection \<open>The compensator relation, conditionally\<close>

text \<open>\<open>fourth_moment_bound_bounded\<close> takes the compensator relation in
  conditional form (its \<open>covA\<close> hypothesis), while everything here says instead
  that \<open>X\<^sup>2 - A\<close> is a martingale.  This bridges the two, so both halves of T1
  run off one bundle of assumptions.\<close>

lemma compensator_cond_increment:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and XA: "martingale M F (0::real) (\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>)"
    and sq: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (\<lambda>\<omega>. (X v \<omega>)\<^sup>2)"
    and Aint: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (A v)"
    and u: "0 \<le> u" and uv: "u \<le> v"
  shows "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)\<^sup>2) \<omega>
                      = cond_exp M (F u) (\<lambda>\<omega>. A v \<omega> - A u \<omega>) \<omega>"
proof -
  interpret MX: martingale M F "0::real" X by (rule X)
  interpret MXA: martingale M F "0::real" "\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>" by (rule XA)
  have v: "0 \<le> v" using u uv by simp
  have sfs: "sigma_finite_subalgebra M (F u)"
    by (rule MX.sigma_finite_subalgebra_F[OF u])
  have Aadapt: "A u \<in> borel_measurable (F u)"
  proof -
    have Aeq: "(\<lambda>\<omega>. (X u \<omega>)\<^sup>2 - ((X u \<omega>)\<^sup>2 - A u \<omega>)) = A u" by (rule ext) simp
    have f1: "(\<lambda>\<omega>. (X u \<omega>)\<^sup>2) \<in> borel_measurable (F u)"
      using MX.adapted[OF u] by simp
    have f2: "(\<lambda>\<omega>. (X u \<omega>)\<^sup>2 - A u \<omega>) \<in> borel_measurable (F u)"
      using MXA.adapted[OF u] by simp
    have "(\<lambda>\<omega>. (X u \<omega>)\<^sup>2 - ((X u \<omega>)\<^sup>2 - A u \<omega>)) \<in> borel_measurable (F u)"
      by (rule borel_measurable_diff[OF f1 f2])
    then show ?thesis unfolding Aeq .
  qed
  have e1: "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)\<^sup>2) \<omega>
      = cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega>)\<^sup>2) \<omega> - (X u \<omega>)\<^sup>2"
    by (rule cond_exp_increment_sq[OF X sq u uv])
  have e2: "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>) \<omega>
      = cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega>)\<^sup>2) \<omega> - cond_exp M (F u) (A v) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff[OF sfs sq[OF v] Aint[OF v]])
  have e3: "AE \<omega> in M. (X u \<omega>)\<^sup>2 - A u \<omega>
      = cond_exp M (F u) (\<lambda>\<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>) \<omega>"
    by (rule MXA.martingale_property[OF u uv])
  have e4: "AE \<omega> in M. cond_exp M (F u) (\<lambda>\<omega>. A v \<omega> - A u \<omega>) \<omega>
      = cond_exp M (F u) (A v) \<omega> - cond_exp M (F u) (A u) \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_diff[OF sfs Aint[OF v] Aint[OF u]])
  have e5: "AE \<omega> in M. cond_exp M (F u) (A u) \<omega> = A u \<omega>"
    by (rule sigma_finite_subalgebra.cond_exp_F_meas[OF sfs Aint[OF u] Aadapt])
  from e1 e2 e3 e4 e5 show ?thesis by eventually_elim simp
qed

subsection \<open>T1a: the compensated sums, and the vanishing of the cross terms\<close>

text \<open>Along a partition \<open>t\<close>, the sum of squared increments minus the
  compensator is a martingale.  Nothing here is quantitative --- no Lipschitz
  bound, no moment bound --- so this step stands on its own.\<close>

lemma qv_minus_compensator_martingale:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and XA: "martingale M F (0::real) (\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>)"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
  shows "martingale M (\<lambda>k. F (t k)) 0
           (\<lambda>n \<omega>. qvar (\<lambda>k. X (t k)) n \<omega> - A (t n) \<omega>)"
proof -
  have m1: "martingale M (\<lambda>k. F (t k)) 0
      (\<lambda>n \<omega>. (X (t n) \<omega>)\<^sup>2 - (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2))"
    by (rule qvar_compensates_sampled[OF X t0 tmono sq])
  have m2: "martingale M (\<lambda>k. F (t k)) 0 (\<lambda>n \<omega>. (X (t n) \<omega>)\<^sup>2 - A (t n) \<omega>)"
    by (rule martingale_sampled[OF XA t0 tmono])
  have "martingale M (\<lambda>k. F (t k)) 0
      (\<lambda>n \<omega>. ((X (t n) \<omega>)\<^sup>2 - A (t n) \<omega>)
             - ((X (t n) \<omega>)\<^sup>2 - (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)))"
    by (rule martingale_diff[OF m2 m1])
  moreover have "(\<lambda>n \<omega>. ((X (t n) \<omega>)\<^sup>2 - A (t n) \<omega>)
             - ((X (t n) \<omega>)\<^sup>2 - (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)))
      = (\<lambda>n \<omega>. qvar (\<lambda>k. X (t k)) n \<omega> - A (t n) \<omega>)"
    by (simp add: qvar_sampled_eq)
  ultimately show ?thesis by simp
qed

text \<open>T1a proper: the compensated increments \<open>(dX)\<^sup>2 - dA\<close> are martingale
  differences, so the second moment of their sum is the sum of their second
  moments.  This is \<open>expectation_sq_qvar\<close> applied to the martingale above.\<close>

lemma qv_orthogonality:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and XA: "martingale M F (0::real) (\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>)"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and A0: "AE \<omega> in M. A (t 0) \<omega> = 0"
    and Dsq: "\<And>m. integrable M (\<lambda>\<omega>. (qvar (\<lambda>k. X (t k)) m \<omega> - A (t m) \<omega>)\<^sup>2)"
    and incsq: "\<And>k. integrable M (\<lambda>\<omega>. ((X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                    - (A (t (Suc k)) \<omega> - A (t k) \<omega>))\<^sup>2)"
  shows "(\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) n \<omega> - A (t n) \<omega>)\<^sup>2 \<partial>M)
       = (\<Sum>k<n. \<integral>\<omega>. ((X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                       - (A (t (Suc k)) \<omega> - A (t k) \<omega>))\<^sup>2 \<partial>M)"
proof -
  define D where "D = (\<lambda>n \<omega>. qvar (\<lambda>k. X (t k)) n \<omega> - A (t n) \<omega>)"
  have mD: "martingale M (\<lambda>k. F (t k)) 0 D"
    unfolding D_def by (rule qv_minus_compensator_martingale[OF X XA t0 tmono sq])
  interpret D: sq_int_martingale M "\<lambda>k. F (t k)" D
  proof (intro sq_int_martingale.intro sq_int_martingale_axioms.intro)
    show "nat_sigma_finite_filtered_measure M (\<lambda>k. F (t k))"
      by (rule nat_filtered_of_sampled[OF X t0 tmono])
    show "martingale M (\<lambda>k. F (t k)) 0 D" by (rule mD)
    show "integrable M (\<lambda>\<omega>. (D m \<omega>)\<^sup>2)" for m
      unfolding D_def by (rule Dsq)
  qed
  have D0: "AE \<omega> in M. D 0 \<omega> = 0"
    using A0 unfolding D_def by simp
  have incD: "D (Suc k) \<omega> - D k \<omega>
      = (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 - (A (t (Suc k)) \<omega> - A (t k) \<omega>)" for k \<omega>
    unfolding D_def by (simp add: qvar_Suc)
  have "(\<integral>\<omega>. (D n \<omega>)\<^sup>2 \<partial>M) = (\<integral>\<omega>. (D 0 \<omega>)\<^sup>2 \<partial>M) + (\<integral>\<omega>. qvar D n \<omega> \<partial>M)"
    by (rule D.expectation_sq_qvar)
  also have "(\<integral>\<omega>. (D 0 \<omega>)\<^sup>2 \<partial>M) = 0"
    using D0 by (intro integral_eq_zero_AE) simp
  also have "(\<integral>\<omega>. qvar D n \<omega> \<partial>M)
      = (\<Sum>k<n. \<integral>\<omega>. ((X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                      - (A (t (Suc k)) \<omega> - A (t k) \<omega>))\<^sup>2 \<partial>M)"
    unfolding qvar_def by (simp add: incD incsq)
  finally show ?thesis unfolding D_def by simp
qed

subsection \<open>T1b: the per-increment bound\<close>

text \<open>Each compensated increment has second moment at most \<open>18 C\<^sup>2 (dt)\<^sup>2\<close>: the
  fourth moment contributes \<open>8 C\<^sup>2 (dt)\<^sup>2\<close> by Eq. (2.7) and the compensator
  increment \<open>C\<^sup>2 (dt)\<^sup>2\<close> by the Lipschitz rate, through \<open>(a - b)\<^sup>2 \<le> 2a\<^sup>2 + 2b\<^sup>2\<close>.\<close>

lemma sq_diff_le_two:
  fixes a b :: real
  shows "(a - b)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * b\<^sup>2"
proof -
  have "0 \<le> (a + b)\<^sup>2" by simp
  then show ?thesis by (simp add: power2_eq_square algebra_simps)
qed

text \<open>The same, with the first square already folded into a fourth power ---
  the form the two integral bounds are stated in.\<close>

text \<open>Monotonicity of the even powers under an absolute bound; both directions of
  the rewriting between \<open>x^4\<close> and \<open>(x\<^sup>2)\<^sup>2\<close> are needed downstream.\<close>

lemma sq_mono_abs:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "x\<^sup>2 \<le> b\<^sup>2"
  using power_mono[OF assms abs_ge_zero, of 2] by simp

lemma fourth_mono_abs:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "x^4 \<le> b^4"
proof -
  have "(x\<^sup>2)\<^sup>2 \<le> (b\<^sup>2)\<^sup>2" by (rule power_mono[OF sq_mono_abs[OF assms]]) simp
  moreover have "(x\<^sup>2)\<^sup>2 = x^4" and "(b\<^sup>2)\<^sup>2 = b^4" by algebra+
  ultimately show ?thesis by simp
qed

lemma sq_abs_mono:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "\<bar>x\<^sup>2\<bar> \<le> b\<^sup>2"
  using sq_mono_abs[OF assms] by simp

lemma fourth_abs_mono:
  fixes x b :: real
  assumes "\<bar>x\<bar> \<le> b"
  shows "\<bar>x^4\<bar> \<le> b^4"
  using power_mono[OF assms abs_ge_zero, of 4] by (simp add: power_abs)

lemma sq_diff_le_fourth:
  fixes x a :: real
  shows "(x\<^sup>2 - a)\<^sup>2 \<le> 2 * x^4 + 2 * a\<^sup>2"
proof -
  have "(x\<^sup>2 - a)\<^sup>2 \<le> 2 * (x\<^sup>2)\<^sup>2 + 2 * a\<^sup>2" by (rule sq_diff_le_two)
  moreover have "(x\<^sup>2)\<^sup>2 = x^4" by algebra
  ultimately show ?thesis by simp
qed

lemma compensated_increment_second_moment:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and XA: "martingale M F (0::real) (\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>)"
    and sq: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (\<lambda>\<omega>. (X v \<omega>)\<^sup>2)"
    and Aint: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (A v)"
    and Arate: "AE \<omega> in M. \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
                   0 \<le> A q \<omega> - A p \<omega> \<and> A q \<omega> - A p \<omega> \<le> C * (q - p)"
    and C: "0 \<le> C" and R: "0 \<le> R"
    and bnd: "\<And>v. 0 \<le> v \<Longrightarrow> AE \<omega> in M. \<bar>X v \<omega>\<bar> \<le> R"
    and cont: "AE \<omega> in M. continuous_on {u..v} (\<lambda>p. X p \<omega>)"
    and fourth: "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
    and dAsq: "integrable M (\<lambda>\<omega>. (A v \<omega> - A u \<omega>)\<^sup>2)"
    and sqint: "integrable M (\<lambda>\<omega>. ((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2)"
    and u: "0 \<le> u" and uv: "u \<le> v"
  shows "(\<integral>\<omega>. ((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2 \<partial>M)
           \<le> 18 * C\<^sup>2 * (v - u)\<^sup>2"
proof -
  interpret P: prob_space M by (rule P)
  have covA: "\<And>p q. 0 \<le> p \<Longrightarrow> p \<le> q \<Longrightarrow> AE \<omega> in M.
      cond_exp M (F p) (\<lambda>\<omega>. (X q \<omega> - X p \<omega>)\<^sup>2) \<omega>
        = cond_exp M (F p) (\<lambda>\<omega>. A q \<omega> - A p \<omega>) \<omega>"
    by (rule compensator_cond_increment[OF X XA sq Aint])
  have m4: "(\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) \<le> 8 * C\<^sup>2 * (v - u)\<^sup>2"
    by (rule fourth_moment_bound_bounded
          [OF P X u uv Aint Arate covA C R bnd cont])
  have dAle: "AE \<omega> in M. (A v \<omega> - A u \<omega>)\<^sup>2 \<le> C\<^sup>2 * (v - u)\<^sup>2"
    using Arate
  proof eventually_elim
    case (elim \<omega>)
    then have nn: "0 \<le> A v \<omega> - A u \<omega>" and le: "A v \<omega> - A u \<omega> \<le> C * (v - u)"
      using u uv by blast+
    have "(A v \<omega> - A u \<omega>)\<^sup>2 \<le> (C * (v - u))\<^sup>2" by (rule power_mono[OF le nn])
    then show ?case by (simp add: power_mult_distrib)
  qed
  have dA: "(\<integral>\<omega>. (A v \<omega> - A u \<omega>)\<^sup>2 \<partial>M) \<le> C\<^sup>2 * (v - u)\<^sup>2"
  proof -
    have "(\<integral>\<omega>. (A v \<omega> - A u \<omega>)\<^sup>2 \<partial>M) \<le> (\<integral>\<omega>. C\<^sup>2 * (v - u)\<^sup>2 \<partial>M)"
      by (rule integral_mono_AE[OF dAsq _ dAle]) simp
    then show ?thesis by (simp add: P.prob_space)
  qed
  have int1: "integrable M (\<lambda>\<omega>. 2 * (X v \<omega> - X u \<omega>)^4 + 2 * (A v \<omega> - A u \<omega>)\<^sup>2)"
    using fourth dAsq by simp
  have "(\<integral>\<omega>. ((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2 \<partial>M)
      \<le> (\<integral>\<omega>. 2 * (X v \<omega> - X u \<omega>)^4 + 2 * (A v \<omega> - A u \<omega>)\<^sup>2 \<partial>M)"
    by (rule integral_mono_AE[OF sqint int1])
       (intro AE_I2 sq_diff_le_fourth)
  also have "\<dots> = 2 * (\<integral>\<omega>. (X v \<omega> - X u \<omega>)^4 \<partial>M) + 2 * (\<integral>\<omega>. (A v \<omega> - A u \<omega>)\<^sup>2 \<partial>M)"
    using fourth dAsq by simp
  also have "\<dots> \<le> 2 * (8 * C\<^sup>2 * (v - u)\<^sup>2) + 2 * (C\<^sup>2 * (v - u)\<^sup>2)"
    using m4 dA by simp
  finally show ?thesis by simp
qed

subsection \<open>From a summable \<open>L\<^sup>2\<close> rate to almost sure convergence\<close>

text \<open>The rate of T1 is summable, so the whole sequence converges almost surely
  --- Borel--Cantelli is not needed, the sum of the second moments being finite
  already forces the summands to vanish pointwise.\<close>

lemma AE_tendsto_zero_of_summable_sq:
  fixes Z :: "nat \<Rightarrow> 'a \<Rightarrow> real" and c :: "nat \<Rightarrow> real"
  assumes m: "\<And>n. Z n \<in> borel_measurable M"
    and b: "\<And>n. (\<integral>\<^sup>+\<omega>. ennreal ((Z n \<omega>)\<^sup>2) \<partial>M) \<le> ennreal (c n)"
    and cn: "\<And>n. 0 \<le> c n" and s: "summable c"
  shows "AE \<omega> in M. (\<lambda>n. Z n \<omega>) \<longlonglongrightarrow> 0"
proof -
  have mm [measurable]: "(\<lambda>\<omega>. ennreal ((Z n \<omega>)\<^sup>2)) \<in> borel_measurable M" for n
    using m[of n] by simp
  have "(\<integral>\<^sup>+\<omega>. (\<Sum>n. ennreal ((Z n \<omega>)\<^sup>2)) \<partial>M) = (\<Sum>n. \<integral>\<^sup>+\<omega>. ennreal ((Z n \<omega>)\<^sup>2) \<partial>M)"
    by (rule nn_integral_suminf) (rule mm)
  also have "\<dots> \<le> (\<Sum>n. ennreal (c n))" by (intro suminf_le b) auto
  also have "\<dots> = ennreal (\<Sum>n. c n)" using s cn by (simp add: suminf_ennreal2)
  finally have "(\<integral>\<^sup>+\<omega>. (\<Sum>n. ennreal ((Z n \<omega>)\<^sup>2)) \<partial>M) < \<top>"
    by (rule le_less_trans) (rule ennreal_less_top)
  then have fin: "(\<integral>\<^sup>+\<omega>. (\<Sum>n. ennreal ((Z n \<omega>)\<^sup>2)) \<partial>M) \<noteq> \<infinity>" by simp
  have "AE \<omega> in M. (\<Sum>n. ennreal ((Z n \<omega>)\<^sup>2)) \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF _ fin]) measurable
  then show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have "summable (\<lambda>n. (Z n \<omega>)\<^sup>2)" by (intro summable_suminf_not_top) auto
    then have "(\<lambda>n. (Z n \<omega>)\<^sup>2) \<longlonglongrightarrow> 0" by (rule summable_LIMSEQ_zero)
    then have "(\<lambda>n. sqrt ((Z n \<omega>)\<^sup>2)) \<longlonglongrightarrow> sqrt 0" by (rule tendsto_real_sqrt)
    then have "(\<lambda>n. \<bar>Z n \<omega>\<bar>) \<longlonglongrightarrow> 0" by simp
    then show ?case by (rule tendsto_rabs_zero_cancel)
  qed
qed

subsection \<open>T2: the quadratic variation as a path functional\<close>

text \<open>The point of defining \<open>qvp\<close> as a \<open>limsup\<close> rather than by Doob--Meyer:
  each dyadic sum is a Borel function of the path by composition of evaluations,
  so measurability is free, and the grid of \<open>{0..T}\<close> uses only times \<open>\<le> T\<close>, so
  the functional is adapted to the filtration of the path alone.\<close>

definition dyadic_qsum :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "dyadic_qsum w T n =
     (\<Sum>k<2 ^ n. (w (T * real (Suc k) / 2 ^ n) - w (T * real k / 2 ^ n))\<^sup>2)"

definition qvp :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "qvp w T = real_of_ereal (limsup (\<lambda>n. ereal (dyadic_qsum w T n)))"

lemma dyadic_qsum_eq_qvar:
  "dyadic_qsum (\<lambda>s. Y s \<omega>) T n = qvar (\<lambda>k \<omega>. Y (T * real k / 2 ^ n) \<omega>) (2 ^ n) \<omega>"
  by (simp add: dyadic_qsum_def qvar_def)

text \<open>Every grid point of \<open>{0..T}\<close> lies in \<open>{0..T}\<close>.\<close>

lemma grid_bounds:
  fixes T :: real
  assumes T: "0 \<le> T" and k: "k \<le> 2 ^ n"
  shows "0 \<le> T * real k / 2 ^ n" and "T * real k / 2 ^ n \<le> T"
proof -
  show "0 \<le> T * real k / 2 ^ n" using T by simp
  have "T * real k \<le> T * 2 ^ n" using T k by (intro mult_left_mono) auto
  then show "T * real k / 2 ^ n \<le> T" by (simp add: divide_le_eq)
qed

lemma dyadic_qsum_measurable:
  assumes T: "0 \<le> T"
    and Y: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> Y s \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. dyadic_qsum (\<lambda>s. Y s \<omega>) T n) \<in> borel_measurable N"
  unfolding dyadic_qsum_def
proof (intro borel_measurable_sum borel_measurable_power borel_measurable_diff)
  fix k :: nat assume "k \<in> {..<2 ^ n}"
  then have k: "Suc k \<le> 2 ^ n" by simp
  then have k': "k \<le> 2 ^ n" by simp
  show "(\<lambda>\<omega>. Y (T * real (Suc k) / 2 ^ n) \<omega>) \<in> borel_measurable N"
    by (rule Y[OF grid_bounds(1)[OF T k] grid_bounds(2)[OF T k]])
  show "(\<lambda>\<omega>. Y (T * real k / 2 ^ n) \<omega>) \<in> borel_measurable N"
    by (rule Y[OF grid_bounds(1)[OF T k'] grid_bounds(2)[OF T k']])
qed

lemma qvp_measurable:
  assumes T: "0 \<le> T"
    and Y: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> Y s \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. qvp (\<lambda>s. Y s \<omega>) T) \<in> borel_measurable N"
  unfolding qvp_def
  by (intro borel_measurable_real_of_ereal borel_measurable_limsup
        borel_measurable_ereal dyadic_qsum_measurable[OF T Y])

text \<open>If the dyadic sums converge, the \<open>limsup\<close> is the limit.\<close>

lemma qvp_eq_limI:
  assumes "(\<lambda>n. dyadic_qsum w T n) \<longlonglongrightarrow> L"
  shows "qvp w T = L"
proof -
  have "(\<lambda>n. ereal (dyadic_qsum w T n)) \<longlonglongrightarrow> ereal L"
    using assms by (rule tendsto_ereal)
  then have "limsup (\<lambda>n. ereal (dyadic_qsum w T n)) = ereal L"
    by (rule lim_imp_Limsup[OF sequentially_bot])
  then show ?thesis by (simp add: qvp_def)
qed

subsection \<open>A locale for the standing hypotheses\<close>

text \<open>Both halves of T1 run off the same bundle: a bounded continuous martingale
  with a Lipschitz compensator on a probability space.  Every integrability side
  condition either half needs is derivable from boundedness, so the locale states
  none of them.\<close>

locale bounded_martingale_compensator =
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and C R :: real
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and XA: "martingale M F (0::real) (\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>)"
    and C: "0 \<le> C" and R: "0 \<le> R"
    and bnd: "\<And>v. 0 \<le> v \<Longrightarrow> AE \<omega> in M. \<bar>X v \<omega>\<bar> \<le> R"
    and Arate: "AE \<omega> in M. \<forall>p q. 0 \<le> p \<longrightarrow> p \<le> q \<longrightarrow>
                   0 \<le> A q \<omega> - A p \<omega> \<and> A q \<omega> - A p \<omega> \<le> C * (q - p)"
    and A0: "AE \<omega> in M. A 0 \<omega> = 0"
    and cont: "AE \<omega> in M. continuous_on {0..} (\<lambda>p. X p \<omega>)"
begin

sublocale P: prob_space M by (rule P)
sublocale MX: martingale M F "0::real" X by (rule X)
sublocale MXA: martingale M F "0::real" "\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>" by (rule XA)

lemma Xmeas: "0 \<le> v \<Longrightarrow> X v \<in> borel_measurable M"
  by (rule MX.random_variable)

lemma Ameas: "0 \<le> v \<Longrightarrow> A v \<in> borel_measurable M"
proof -
  assume v: "0 \<le> v"
  have m1: "(\<lambda>\<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>) \<in> borel_measurable M"
    by (rule MXA.random_variable[OF v])
  have f1: "(\<lambda>\<omega>. (X v \<omega>)\<^sup>2) \<in> borel_measurable M" using Xmeas[OF v] by simp
  have "(\<lambda>\<omega>. (X v \<omega>)\<^sup>2 - ((X v \<omega>)\<^sup>2 - A v \<omega>)) \<in> borel_measurable M"
    by (rule borel_measurable_diff[OF f1 m1])
  moreover have "(\<lambda>\<omega>. (X v \<omega>)\<^sup>2 - ((X v \<omega>)\<^sup>2 - A v \<omega>)) = A v" by (rule ext) simp
  ultimately show ?thesis by simp
qed

lemma integrable_bounded:
  fixes B :: real
  assumes f: "f \<in> borel_measurable M" and b: "AE \<omega> in M. \<bar>f \<omega>\<bar> \<le> B"
  shows "integrable M f"
  using b by (intro P.integrable_const_bound[of _ B] f) simp

text \<open>The compensator increments, read off the Lipschitz rate.\<close>

lemma Ainc:
  assumes "0 \<le> u" and "u \<le> v"
  shows "AE \<omega> in M. 0 \<le> A v \<omega> - A u \<omega> \<and> A v \<omega> - A u \<omega> \<le> C * (v - u)"
  using Arate by eventually_elim (use assms in blast)

lemma Abnd:
  assumes v: "0 \<le> v"
  shows "AE \<omega> in M. \<bar>A v \<omega>\<bar> \<le> C * v"
  using Ainc[OF order_refl v] A0 by eventually_elim simp

lemma Aint:
  assumes v: "0 \<le> v"
  shows "integrable M (A v)"
  by (rule integrable_bounded[OF Ameas[OF v] Abnd[OF v]])

text \<open>The martingale increments, read off the uniform bound on \<open>X\<close>.\<close>

lemma Xinc:
  assumes u: "0 \<le> u" and v: "0 \<le> v"
  shows "AE \<omega> in M. \<bar>X v \<omega> - X u \<omega>\<bar> \<le> 2 * R"
  using bnd[OF u] bnd[OF v] by eventually_elim simp

lemma sqint_X:
  assumes v: "0 \<le> v"
  shows "integrable M (\<lambda>\<omega>. (X v \<omega>)\<^sup>2)"
proof (rule integrable_bounded[where B = "R\<^sup>2"])
  show "(\<lambda>\<omega>. (X v \<omega>)\<^sup>2) \<in> borel_measurable M" using Xmeas[OF v] by simp
  show "AE \<omega> in M. \<bar>(X v \<omega>)\<^sup>2\<bar> \<le> R\<^sup>2"
    using bnd[OF v] by eventually_elim (simp add: sq_mono_abs)
qed

lemma fourth_int:
  assumes u: "0 \<le> u" and v: "0 \<le> v"
  shows "integrable M (\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4)"
proof (rule integrable_bounded[where B = "(2 * R)^4"])
  show "(\<lambda>\<omega>. (X v \<omega> - X u \<omega>)^4) \<in> borel_measurable M"
    using Xmeas[OF u] Xmeas[OF v] by simp
  show "AE \<omega> in M. \<bar>(X v \<omega> - X u \<omega>)^4\<bar> \<le> (2 * R)^4"
    using Xinc[OF u v] by eventually_elim (rule fourth_abs_mono)
qed

lemma dAsq_int:
  assumes u: "0 \<le> u" and uv: "u \<le> v"
  shows "integrable M (\<lambda>\<omega>. (A v \<omega> - A u \<omega>)\<^sup>2)"
proof (rule integrable_bounded[where B = "C\<^sup>2 * (v - u)\<^sup>2"])
  from u uv have v: "0 \<le> v" by simp
  show "(\<lambda>\<omega>. (A v \<omega> - A u \<omega>)\<^sup>2) \<in> borel_measurable M"
    using Ameas[OF u] Ameas[OF v] by simp
  show "AE \<omega> in M. \<bar>(A v \<omega> - A u \<omega>)\<^sup>2\<bar> \<le> C\<^sup>2 * (v - u)\<^sup>2"
    using Ainc[OF u uv]
  proof eventually_elim
    case (elim \<omega>)
    then have "(A v \<omega> - A u \<omega>)\<^sup>2 \<le> (C * (v - u))\<^sup>2" by (intro power_mono) auto
    then show ?case using elim by (simp add: power_mult_distrib)
  qed
qed

lemma compsq_int:
  assumes u: "0 \<le> u" and uv: "u \<le> v"
  shows "integrable M (\<lambda>\<omega>. ((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2)"
proof -
  from u uv have v: "0 \<le> v" by simp
  have m: "(\<lambda>\<omega>. ((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2) \<in> borel_measurable M"
    using Xmeas[OF u] Xmeas[OF v] Ameas[OF u] Ameas[OF v] by simp
  show ?thesis
  proof (rule integrable_bounded[OF m, where B = "2 * (2 * R)^4 + 2 * (C * (v - u))\<^sup>2"])
    show "AE \<omega> in M. \<bar>((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2\<bar>
            \<le> 2 * (2 * R)^4 + 2 * (C * (v - u))\<^sup>2"
      using Xinc[OF u v] Ainc[OF u uv]
    proof eventually_elim
      case (elim \<omega>)
      have "((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2
              \<le> 2 * (X v \<omega> - X u \<omega>)^4 + 2 * (A v \<omega> - A u \<omega>)\<^sup>2"
        by (rule sq_diff_le_fourth)
      moreover have "(X v \<omega> - X u \<omega>)^4 \<le> (2 * R)^4"
        using elim by (intro fourth_mono_abs) simp
      moreover have "(A v \<omega> - A u \<omega>)\<^sup>2 \<le> (C * (v - u))\<^sup>2"
        using elim by (intro power_mono) auto
      ultimately show ?case by simp
    qed
  qed
qed

text \<open>Continuity on any subinterval of \<open>{0..}\<close>.\<close>

lemma cont_on:
  assumes u: "0 \<le> u"
  shows "AE \<omega> in M. continuous_on {u..v} (\<lambda>p. X p \<omega>)"
  using cont
proof eventually_elim
  case (elim \<omega>)
  have "{u..v} \<subseteq> {0..}" using u by auto
  then show ?case by (rule continuous_on_subset[OF elim])
qed

subsection \<open>T1a and T1b inside the locale\<close>

text \<open>The two halves again, now with every side condition discharged.\<close>

lemma increment_second_moment:
  assumes u: "0 \<le> u" and uv: "u \<le> v"
  shows "(\<integral>\<omega>. ((X v \<omega> - X u \<omega>)\<^sup>2 - (A v \<omega> - A u \<omega>))\<^sup>2 \<partial>M) \<le> 18 * C\<^sup>2 * (v - u)\<^sup>2"
proof -
  from u uv have v: "0 \<le> v" by simp
  show ?thesis
    by (rule compensated_increment_second_moment
          [OF P X XA sqint_X Aint Arate C R bnd cont_on[OF u] fourth_int[OF u v]
              dAsq_int[OF u uv] compsq_int[OF u uv] u uv])
qed

text \<open>The compensated sum along a grid is square integrable: \<open>qvar\<close> is a sum of
  \<open>m\<close> squared increments, each bounded by \<open>(2R)\<^sup>2\<close>, and the compensator by \<open>C t\<^sub>m\<close>.\<close>

lemma qvar_grid_sq_int:
  assumes t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
  shows "integrable M (\<lambda>\<omega>. (qvar (\<lambda>k. X (t k)) m \<omega> - A (t m) \<omega>)\<^sup>2)"
proof -
  have meas: "(\<lambda>\<omega>. (qvar (\<lambda>k. X (t k)) m \<omega> - A (t m) \<omega>)\<^sup>2) \<in> borel_measurable M"
    unfolding qvar_def using Xmeas[OF t0] Ameas[OF t0] by simp
  have qb: "AE \<omega> in M. \<bar>qvar (\<lambda>k. X (t k)) m \<omega>\<bar> \<le> real m * (2 * R)\<^sup>2"
  proof -
    have "AE \<omega> in M. \<forall>k<m. \<bar>X (t (Suc k)) \<omega> - X (t k) \<omega>\<bar> \<le> 2 * R"
    proof (subst AE_all_countable, intro allI)
      fix k show "AE \<omega> in M. k < m \<longrightarrow> \<bar>X (t (Suc k)) \<omega> - X (t k) \<omega>\<bar> \<le> 2 * R"
        using Xinc[of "t k" "t (Suc k)", OF t0 t0] by eventually_elim simp
    qed
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>qvar (\<lambda>k. X (t k)) m \<omega>\<bar> = (\<Sum>k<m. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
        unfolding qvar_def by (simp add: sum_nonneg)
      also have "\<dots> \<le> (\<Sum>k<m. (2 * R)\<^sup>2)"
        using elim by (intro sum_mono sq_mono_abs) simp
      finally show ?case by simp
    qed
  qed
  have ab: "AE \<omega> in M. \<bar>A (t m) \<omega>\<bar> \<le> C * t m" by (rule Abnd[OF t0])
  show ?thesis
  proof (rule integrable_bounded[OF meas,
           where B = "(real m * (2 * R)\<^sup>2 + C * t m)\<^sup>2"])
    show "AE \<omega> in M. \<bar>(qvar (\<lambda>k. X (t k)) m \<omega> - A (t m) \<omega>)\<^sup>2\<bar>
            \<le> (real m * (2 * R)\<^sup>2 + C * t m)\<^sup>2"
      using qb ab
    proof eventually_elim
      case (elim \<omega>)
      have "\<bar>qvar (\<lambda>k. X (t k)) m \<omega> - A (t m) \<omega>\<bar> \<le> real m * (2 * R)\<^sup>2 + C * t m"
        using elim by simp
      then show ?case by (rule sq_abs_mono)
    qed
  qed
qed

subsection \<open>T1: the \<open>L\<^sup>2\<close> rate along a grid\<close>

text \<open>Orthogonality turns the \<open>L\<^sup>2\<close> error into a sum of per-increment second
  moments, and each of those is quadratic in the mesh.  So the total is the mesh
  times the length of the interval --- summable along the dyadics.\<close>

lemma qv_grid_L2:
  assumes tz: "t 0 = 0" and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
  shows "(\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) n \<omega> - A (t n) \<omega>)\<^sup>2 \<partial>M)
       \<le> (\<Sum>k<n. 18 * C\<^sup>2 * (t (Suc k) - t k)\<^sup>2)"
proof -
  have le: "t k \<le> t (Suc k)" for k using tmono by (simp add: mono_def)
  have "(\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) n \<omega> - A (t n) \<omega>)\<^sup>2 \<partial>M)
      = (\<Sum>k<n. \<integral>\<omega>. ((X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                      - (A (t (Suc k)) \<omega> - A (t k) \<omega>))\<^sup>2 \<partial>M)"
  proof (rule qv_orthogonality[OF X XA t0 tmono sqint_X])
    show "AE \<omega> in M. A (t 0) \<omega> = 0" using A0 by (simp add: tz)
    show "integrable M (\<lambda>\<omega>. (qvar (\<lambda>k. X (t k)) m \<omega> - A (t m) \<omega>)\<^sup>2)" for m
      by (rule qvar_grid_sq_int[OF t0 tmono])
    show "integrable M (\<lambda>\<omega>. ((X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
             - (A (t (Suc k)) \<omega> - A (t k) \<omega>))\<^sup>2)" for k
      by (rule compsq_int[OF t0 le])
  qed
  also have "\<dots> \<le> (\<Sum>k<n. 18 * C\<^sup>2 * (t (Suc k) - t k)\<^sup>2)"
    by (intro sum_mono increment_second_moment[OF t0 le])
  finally show ?thesis .
qed

text \<open>On the uniform grid of mesh \<open>T / 2\<^sup>n\<close> the bound telescopes to \<open>18 C\<^sup>2 T\<^sup>2 / 2\<^sup>n\<close>:
  the rate is summable, so the whole dyadic sequence converges almost surely and
  no subsequence has to be extracted.\<close>

lemma qv_dyadic_L2:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "(\<integral>\<omega>. (qvar (\<lambda>k. X (T * real k / 2 ^ n)) (2 ^ n) \<omega> - A T \<omega>)\<^sup>2 \<partial>M)
       \<le> 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n"
proof -
  define t where "t = (\<lambda>k::nat. T * real k / 2 ^ n)"
  have tz: "t 0 = 0" by (simp add: t_def)
  have t0: "0 \<le> t k" for k using T by (simp add: t_def)
  have tmono: "mono t" using T by (simp add: t_def mono_def divide_right_mono mult_left_mono)
  have tend: "t (2 ^ n) = T" by (simp add: t_def)
  have inc: "t (Suc k) - t k = T / 2 ^ n" for k
    by (simp add: t_def field_simps)
  have "(\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) (2 ^ n) \<omega> - A T \<omega>)\<^sup>2 \<partial>M)
      = (\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) (2 ^ n) \<omega> - A (t (2 ^ n)) \<omega>)\<^sup>2 \<partial>M)"
    by (simp add: tend)
  also have "\<dots> \<le> (\<Sum>k<(2::nat) ^ n. 18 * C\<^sup>2 * (t (Suc k) - t k)\<^sup>2)"
    by (rule qv_grid_L2[OF tz t0 tmono])
  also have "\<dots> = 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n"
    by (simp add: inc power_divide power2_eq_square)
  finally show ?thesis by (simp add: t_def)
qed

subsection \<open>T2 at a fixed time: the path functional computes the compensator\<close>

text \<open>The rate \<open>18 C\<^sup>2 T\<^sup>2 / 2\<^sup>n\<close> is summable, so the dyadic sums converge to
  \<open>A T\<close> almost surely, and \<open>qvp\<close> --- their \<open>limsup\<close> --- agrees with \<open>A T\<close>.\<close>

lemma dyadic_qsum_eq_grid:
  "dyadic_qsum (\<lambda>s. X s \<omega>) T n = qvar (\<lambda>k. X (T * real k / 2 ^ n)) (2 ^ n) \<omega>"
  by (simp add: dyadic_qsum_def qvar_def)

lemma qvp_tendsto:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "AE \<omega> in M. (\<lambda>n. dyadic_qsum (\<lambda>s. X s \<omega>) T n - A T \<omega>) \<longlonglongrightarrow> 0"
proof (rule AE_tendsto_zero_of_summable_sq[where c = "\<lambda>n. 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n"])
  fix n :: nat
  define t where "t = (\<lambda>k::nat. T * real k / 2 ^ n)"
  have t0: "0 \<le> t k" for k using T by (simp add: t_def)
  have tmono: "mono t"
    using T by (simp add: t_def mono_def divide_right_mono mult_left_mono)
  have eq: "dyadic_qsum (\<lambda>s. X s \<omega>) T n = qvar (\<lambda>k. X (t k)) (2 ^ n) \<omega>" for \<omega>
    by (simp add: dyadic_qsum_eq_grid t_def)
  show "(\<lambda>\<omega>. dyadic_qsum (\<lambda>s. X s \<omega>) T n - A T \<omega>) \<in> borel_measurable M"
    unfolding eq qvar_def using Xmeas[OF t0] Ameas[OF T] by simp
  have int: "integrable M (\<lambda>\<omega>. (qvar (\<lambda>k. X (t k)) (2 ^ n) \<omega> - A T \<omega>)\<^sup>2)"
  proof -
    have "t (2 ^ n) = T" by (simp add: t_def)
    then show ?thesis using qvar_grid_sq_int[OF t0 tmono, of "2 ^ n"] by simp
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal ((dyadic_qsum (\<lambda>s. X s \<omega>) T n - A T \<omega>)\<^sup>2) \<partial>M)
      = ennreal (\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) (2 ^ n) \<omega> - A T \<omega>)\<^sup>2 \<partial>M)"
    unfolding eq by (rule nn_integral_eq_integral[OF int]) simp
  also have "\<dots> \<le> ennreal (18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n)"
  proof (rule ennreal_leI)
    have "t (2 ^ n) = T" by (simp add: t_def)
    then show "(\<integral>\<omega>. (qvar (\<lambda>k. X (t k)) (2 ^ n) \<omega> - A T \<omega>)\<^sup>2 \<partial>M)
                 \<le> 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n"
      using qv_dyadic_L2[OF T, of n] by (simp add: t_def)
  qed
  finally show "(\<integral>\<^sup>+\<omega>. ennreal ((dyadic_qsum (\<lambda>s. X s \<omega>) T n - A T \<omega>)\<^sup>2) \<partial>M)
                  \<le> ennreal (18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n)" .
next
  show "0 \<le> 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n" for n :: nat by simp
  have "summable (\<lambda>n::nat. 18 * C\<^sup>2 * T\<^sup>2 * (1 / 2) ^ n)"
    by (intro summable_mult summable_geometric) simp
  moreover have "(\<lambda>n::nat. 18 * C\<^sup>2 * T\<^sup>2 * (1 / 2) ^ n)
      = (\<lambda>n. 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n)"
    by (simp add: power_one_over)
  ultimately show "summable (\<lambda>n::nat. 18 * C\<^sup>2 * T\<^sup>2 / 2 ^ n)" by simp
qed

theorem qvp_eq_A:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "AE \<omega> in M. qvp (\<lambda>s. X s \<omega>) T = A T \<omega>"
  using qvp_tendsto[OF T]
proof eventually_elim
  case (elim \<omega>)
  have "(\<lambda>n. (dyadic_qsum (\<lambda>s. X s \<omega>) T n - A T \<omega>) + A T \<omega>) \<longlonglongrightarrow> 0 + A T \<omega>"
    by (intro tendsto_add elim tendsto_const)
  then have "(\<lambda>n. dyadic_qsum (\<lambda>s. X s \<omega>) T n) \<longlonglongrightarrow> A T \<omega>" by simp
  then show ?case by (rule qvp_eq_limI)
qed

end

(*<*)
end
(*>*)
