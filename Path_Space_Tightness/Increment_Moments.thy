section \<open>The second-moment bound on increments\<close>

(*<*)
theory Increment_Moments
  imports "Martingale_Sampling.Sampled_Quadratic_Variation" "Martingale_Sampling.Moment_Bounds"
begin

(*>*)

text \<open>
  This theory proves the second-moment bound on increments used in Lemma 2.2 of
  \<^cite>\<open>LaiShkolnikovSoner\<close>:

    \<open>E[(X u - X s)\<^sup>2] \<le> C * (u - s)\<close>

  whenever the compensator of the square grows at rate at most \<open>C\<close> --
  for the admissible family there the hypothesis \<open>trace (acov) \<le> C\<close>,
  since the compensator is \<open>integral (trace o acov)\<close>.

  The proof needs no stochastic integral: it combines the energy identity along a
  two-point partition (\<open>expectation_sq_sampled\<close>) with a martingale's constant
  expectation, applied to the compensated square.
\<close>
subsection \<open>A martingale has constant expectation\<close>

lemma martingale_expectation_eq:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes Y: "martingale M F (0::real) Y" and ij: "0 \<le> i" "i \<le> j"
  shows "(\<integral>\<omega>. Y i \<omega> \<partial>M) = (\<integral>\<omega>. Y j \<omega> \<partial>M)"
proof -
  interpret Q: martingale M F "0::real" Y by (rule Y)
  have j: "0 \<le> j" using ij by simp
  have sp: "space M \<in> sets (F i)"
    using sets.top[of "F i"] Q.space_F[OF ij(1)] by simp
  have eq: "set_lebesgue_integral M (space M) (Y i)
            = set_lebesgue_integral M (space M) (Y j)"
    by (rule Q.set_integral_eq[OF sp ij])
  have li: "set_lebesgue_integral M (space M) (Y i) = (\<integral>\<omega>. Y i \<omega> \<partial>M)"
    by (rule set_integral_space[OF Q.integrable[OF ij(1)]])
  have lj: "set_lebesgue_integral M (space M) (Y j) = (\<integral>\<omega>. Y j \<omega> \<partial>M)"
    by (rule set_integral_space[OF Q.integrable[OF j]])
  from eq li lj show ?thesis by simp
qed

subsection \<open>The increment identity\<close>

text \<open>
  The energy identity at a two-point partition: the second moment of an increment
  is the increment of the second moment.
\<close>

lemma expectation_increment_sq:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and sq: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (\<lambda>\<omega>. (X v \<omega>)\<^sup>2)"
    and s: "0 \<le> s" and su: "s \<le> u"
  shows "(\<integral>\<omega>. (X u \<omega> - X s \<omega>)\<^sup>2 \<partial>M)
           = (\<integral>\<omega>. (X u \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. (X s \<omega>)\<^sup>2 \<partial>M)"
proof -
  define t where "t = (\<lambda>k::nat. if k = 0 then s else u)"
  have t0: "0 \<le> t k" for k unfolding t_def using s su by simp
  have tmono: "mono t"
  proof (rule monoI)
    fix k l :: nat assume "k \<le> l"
    thus "t k \<le> t l" unfolding t_def using su
      by (cases "k = 0"; cases "l = 0") auto
  qed
  have t_0: "t 0 = s" and t_1: "t (Suc 0) = u" unfolding t_def by simp_all
  have "(\<integral>\<omega>. (X (t (Suc 0)) \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. (X (t 0) \<omega>)\<^sup>2 \<partial>M)
            + (\<integral>\<omega>. (\<Sum>k<Suc 0. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<partial>M)"
    by (rule expectation_sq_sampled[OF X t0 tmono sq])
  thus ?thesis by (simp add: t_0 t_1)
qed

subsection \<open>The bound\<close>

theorem increment_second_moment_bound:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and sq: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (\<lambda>\<omega>. (X v \<omega>)\<^sup>2)"
    and Zmart: "martingale M F (0::real) (\<lambda>v \<omega>. (X v \<omega>)\<^sup>2 - A v \<omega>)"
    and Aint: "\<And>v. 0 \<le> v \<Longrightarrow> integrable M (A v)"
    and Arate: "AE \<omega> in M. A u \<omega> - A s \<omega> \<le> C * (u - s)"
    and s: "0 \<le> s" and su: "s \<le> u"
  shows "(\<integral>\<omega>. (X u \<omega> - X s \<omega>)\<^sup>2 \<partial>M) \<le> C * (u - s)"
proof -
  interpret P: prob_space M by (rule P)
  have u: "0 \<le> u" using s su by simp

  text \<open>The compensated square has equal expectations at @{term s} and @{term u}.\<close>
  have "(\<integral>\<omega>. (X s \<omega>)\<^sup>2 - A s \<omega> \<partial>M) = (\<integral>\<omega>. (X u \<omega>)\<^sup>2 - A u \<omega> \<partial>M)"
    by (rule martingale_expectation_eq[OF Zmart s su])
  moreover have "(\<integral>\<omega>. (X v \<omega>)\<^sup>2 - A v \<omega> \<partial>M)
      = (\<integral>\<omega>. (X v \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. A v \<omega> \<partial>M)" if "0 \<le> v" for v
    by (rule Bochner_Integration.integral_diff[OF sq[OF that] Aint[OF that]])
  ultimately have split:
      "(\<integral>\<omega>. (X u \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. (X s \<omega>)\<^sup>2 \<partial>M)
         = (\<integral>\<omega>. A u \<omega> \<partial>M) - (\<integral>\<omega>. A s \<omega> \<partial>M)"
    using s u by simp

  text \<open>And the compensator increment is bounded by hypothesis.\<close>
  have "(\<integral>\<omega>. A u \<omega> \<partial>M) - (\<integral>\<omega>. A s \<omega> \<partial>M) = (\<integral>\<omega>. A u \<omega> - A s \<omega> \<partial>M)"
    by (rule Bochner_Integration.integral_diff[OF Aint[OF u] Aint[OF s], symmetric])
  also have "\<dots> \<le> (\<integral>\<omega>. C * (u - s) \<partial>M)"
  proof (rule integral_mono_AE)
    show "integrable M (\<lambda>\<omega>. A u \<omega> - A s \<omega>)" using Aint[OF u] Aint[OF s] by simp
    show "integrable M (\<lambda>\<omega>. C * (u - s))" by simp
    show "AE \<omega> in M. A u \<omega> - A s \<omega> \<le> C * (u - s)" by (rule Arate)
  qed
  also have "(\<integral>\<omega>. C * (u - s) \<partial>M) = C * (u - s)" by (simp add: P.prob_space)
  finally have Abound: "(\<integral>\<omega>. A u \<omega> \<partial>M) - (\<integral>\<omega>. A s \<omega> \<partial>M) \<le> C * (u - s)" .

  have "(\<integral>\<omega>. (X u \<omega> - X s \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. (X u \<omega>)\<^sup>2 \<partial>M) - (\<integral>\<omega>. (X s \<omega>)\<^sup>2 \<partial>M)"
    by (rule expectation_increment_sq[OF X sq s su])
  also have "\<dots> = (\<integral>\<omega>. A u \<omega> \<partial>M) - (\<integral>\<omega>. A s \<omega> \<partial>M)" by (rule split)
  also note Abound
  finally show ?thesis .
qed

subsection \<open>Pointwise inequalities for the fourth-moment recursion\<close>

text \<open>
  Everything below reduces to the two-square bound \<open>2 \<bar>a\<bar> \<bar>b\<bar> \<le> a\<^sup>2 + b\<^sup>2\<close>
  (@{thm [source] sum_squares_bound}); no Cauchy-Schwarz or Young machinery is
  needed. Polynomial identities are discharged with \<open>algebra\<close> and the linear
  assembly with \<open>linarith\<close>, keeping every nonlinear term as a shared atom.
\<close>

lemma two_abs_prod_le_squares: "2 * \<bar>a\<bar> * \<bar>b\<bar> \<le> a\<^sup>2 + b\<^sup>2" for a b :: real
  using sum_squares_bound[of "\<bar>a\<bar>" "\<bar>b\<bar>"] by simp

lemma abs_prod_le_half_squares: "\<bar>a * b\<bar> \<le> a\<^sup>2 / 2 + b\<^sup>2 / 2" for a b :: real
proof -
  have "2 * \<bar>a * b\<bar> \<le> a\<^sup>2 + b\<^sup>2"
    using two_abs_prod_le_squares[of a b] by (simp add: abs_mult)
  thus ?thesis by linarith
qed

lemma sq_le_half_add_half_pow4: "x\<^sup>2 \<le> 1/2 + x^4/2" for x :: real
proof -
  have "0 \<le> (x\<^sup>2 - 1)\<^sup>2" by simp
  moreover have "(x\<^sup>2 - 1)\<^sup>2 = x^4 - 2*x\<^sup>2 + 1" by algebra
  ultimately show ?thesis by linarith
qed

lemma prod_sq_le_half_pow4: "a\<^sup>2 * b\<^sup>2 \<le> a^4/2 + b^4/2" for a b :: real
proof -
  have "0 \<le> (a\<^sup>2 - b\<^sup>2)\<^sup>2" by simp
  moreover have "(a\<^sup>2 - b\<^sup>2)\<^sup>2 = a^4 - 2*(a\<^sup>2*b\<^sup>2) + b^4" by algebra
  ultimately show ?thesis by linarith
qed

lemma pow4_nonneg: "0 \<le> (x::real)^4"
proof -
  have "(x::real)^4 = (x\<^sup>2)\<^sup>2" by algebra
  then show ?thesis by simp
qed

lemma pow4_diff_le: "(a - b)^4 \<le> 8*a^4 + 8*b^4" for a b :: real
proof -
  have 1: "(a - b)\<^sup>2 \<le> 2*a\<^sup>2 + 2*b\<^sup>2"
    using square_add_le_two[of a "-b"] by simp
  have 2: "((a - b)\<^sup>2)\<^sup>2 \<le> (2*a\<^sup>2 + 2*b\<^sup>2)\<^sup>2"
    by (rule power_mono[OF 1 zero_le_power2])
  have 3: "((a - b)\<^sup>2)\<^sup>2 = (a - b)^4" by algebra
  have 4: "(2*a\<^sup>2 + 2*b\<^sup>2)\<^sup>2 = 4*a^4 + 8*(a\<^sup>2*b\<^sup>2) + 4*b^4" by algebra
  have 5: "a\<^sup>2*b\<^sup>2 \<le> a^4/2 + b^4/2" by (rule prod_sq_le_half_pow4)
  from 2 3 4 5 show ?thesis by linarith
qed

lemma abs_cube_prod_le_pow4: "\<bar>a^3 * b\<bar> \<le> 3/4*a^4 + 1/4*b^4" for a b :: real
proof -
  have e: "a^3 * b = a\<^sup>2 * (a * b)" by algebra
  have 1: "\<bar>a^3 * b\<bar> = a\<^sup>2 * \<bar>a * b\<bar>"
    unfolding e by (simp add: abs_mult)
  have 2: "\<bar>a * b\<bar> \<le> a\<^sup>2/2 + b\<^sup>2/2" by (rule abs_prod_le_half_squares)
  have 3: "a\<^sup>2 * \<bar>a * b\<bar> \<le> a\<^sup>2 * (a\<^sup>2/2 + b\<^sup>2/2)"
    by (rule mult_left_mono[OF 2]) simp
  have 4: "a\<^sup>2 * (a\<^sup>2/2 + b\<^sup>2/2) = a^4/2 + (a\<^sup>2*b\<^sup>2)/2" by algebra
  have 5: "a\<^sup>2*b\<^sup>2 \<le> a^4/2 + b^4/2" by (rule prod_sq_le_half_pow4)
  from 1 3 4 5 show ?thesis by linarith
qed

lemma abs_prod_cube_le_pow4: "\<bar>a * b^3\<bar> \<le> 1/4*a^4 + 3/4*b^4" for a b :: real
proof -
  have e: "a * b^3 = b^3 * a" by algebra
  show ?thesis
    unfolding e using abs_cube_prod_le_pow4[of b a] by linarith
qed

lemma four_prod_cube_le: "4*(y*d^3) \<le> 2*(y\<^sup>2*d\<^sup>2) + 2*d^4" for y d :: real
proof -
  have a: "4*(y*d^3) \<le> 4*(\<bar>y*d\<bar>*d\<^sup>2)"
  proof -
    have e: "y*d^3 = (y*d)*d\<^sup>2" by algebra
    have "(y*d)*d\<^sup>2 \<le> \<bar>(y*d)*d\<^sup>2\<bar>" by (rule abs_ge_self)
    also have "\<bar>(y*d)*d\<^sup>2\<bar> = \<bar>y*d\<bar>*d\<^sup>2" by (simp add: abs_mult)
    finally show ?thesis unfolding e by linarith
  qed
  have b: "2*\<bar>y*d\<bar> \<le> y\<^sup>2 + d\<^sup>2"
    using two_abs_prod_le_squares[of y d] by (simp add: abs_mult)
  have c: "4*(\<bar>y*d\<bar>*d\<^sup>2) = (2*\<bar>y*d\<bar>) * (2*d\<^sup>2)" by algebra
  have d': "(2*\<bar>y*d\<bar>)*(2*d\<^sup>2) \<le> (y\<^sup>2+d\<^sup>2)*(2*d\<^sup>2)"
    by (rule mult_right_mono[OF b]) simp
  have e': "(y\<^sup>2+d\<^sup>2)*(2*d\<^sup>2) = 2*(y\<^sup>2*d\<^sup>2) + 2*d^4" by algebra
  from a c d' e' show ?thesis by linarith
qed

lemma pow4_binomial:
  "(y + d)^4 = y^4 + 4*(y^3*d) + 6*(y\<^sup>2*d\<^sup>2) + 4*(y*d^3) + d^4" for y d :: real
  by algebra

subsection \<open>Integrability from fourth moments\<close>

lemma integrable_sq_diff':
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2)" and g: "integrable M (\<lambda>\<omega>. (g \<omega>)\<^sup>2)"
    and fm[measurable]: "f \<in> borel_measurable M"
    and gm[measurable]: "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. (f \<omega> - g \<omega>)\<^sup>2)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. 2*(f \<omega>)\<^sup>2 + 2*(g \<omega>)\<^sup>2"])
  show "integrable M (\<lambda>\<omega>. 2*(f \<omega>)\<^sup>2 + 2*(g \<omega>)\<^sup>2)" using f g by simp
  show "(\<lambda>\<omega>. (f \<omega> - g \<omega>)\<^sup>2) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm ((f \<omega> - g \<omega>)\<^sup>2) \<le> norm (2*(f \<omega>)\<^sup>2 + 2*(g \<omega>)\<^sup>2)"
  proof (intro always_eventually allI)
    fix \<omega>
    have "(f \<omega> - g \<omega>)\<^sup>2 \<le> 2*(f \<omega>)\<^sup>2 + 2*(g \<omega>)\<^sup>2"
      using square_add_le_two[of "f \<omega>" "- g \<omega>"] by simp
    thus "norm ((f \<omega> - g \<omega>)\<^sup>2) \<le> norm (2*(f \<omega>)\<^sup>2 + 2*(g \<omega>)\<^sup>2)" by simp
  qed
qed

lemma integrable_pow4_diff:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)" and g4: "integrable M (\<lambda>\<omega>. (g \<omega>)^4)"
    and fm[measurable]: "f \<in> borel_measurable M"
    and gm[measurable]: "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. (f \<omega> - g \<omega>)^4)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. 8*(f \<omega>)^4 + 8*(g \<omega>)^4"])
  show "integrable M (\<lambda>\<omega>. 8*(f \<omega>)^4 + 8*(g \<omega>)^4)" using f4 g4 by simp
  show "(\<lambda>\<omega>. (f \<omega> - g \<omega>)^4) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm ((f \<omega> - g \<omega>)^4) \<le> norm (8*(f \<omega>)^4 + 8*(g \<omega>)^4)"
  proof (intro always_eventually allI)
    fix \<omega>
    have le: "(f \<omega> - g \<omega>)^4 \<le> 8*(f \<omega>)^4 + 8*(g \<omega>)^4" by (rule pow4_diff_le)
    have nn: "0 \<le> (f \<omega> - g \<omega>)^4" by (rule pow4_nonneg)
    have nn2: "0 \<le> 8*(f \<omega>)^4 + 8*(g \<omega>)^4"
      using pow4_nonneg[of "f \<omega>"] pow4_nonneg[of "g \<omega>"] by linarith
    show "norm ((f \<omega> - g \<omega>)^4) \<le> norm (8*(f \<omega>)^4 + 8*(g \<omega>)^4)"
      using le nn nn2 by simp
  qed
qed

lemma integrable_sq_of_pow4:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)"
    and fm[measurable]: "f \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. 1/2 + (f \<omega>)^4/2"])
  interpret P: prob_space M by (rule P)
  show "integrable M (\<lambda>\<omega>. 1/2 + (f \<omega>)^4/2)" using f4 by simp
  show "(\<lambda>\<omega>. (f \<omega>)\<^sup>2) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm ((f \<omega>)\<^sup>2) \<le> norm (1/2 + (f \<omega>)^4/2)"
  proof (intro always_eventually allI)
    fix \<omega>
    have le: "(f \<omega>)\<^sup>2 \<le> 1/2 + (f \<omega>)^4/2" by (rule sq_le_half_add_half_pow4)
    have nn2: "0 \<le> 1/2 + (f \<omega>)^4/2" using pow4_nonneg[of "f \<omega>"] by linarith
    show "norm ((f \<omega>)\<^sup>2) \<le> norm (1/2 + (f \<omega>)^4/2)" using le nn2 by simp
  qed
qed

lemma integrable_prod_sq_sq:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)" and g4: "integrable M (\<lambda>\<omega>. (g \<omega>)^4)"
    and fm[measurable]: "f \<in> borel_measurable M"
    and gm[measurable]: "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * (g \<omega>)\<^sup>2)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. (f \<omega>)^4/2 + (g \<omega>)^4/2"])
  show "integrable M (\<lambda>\<omega>. (f \<omega>)^4/2 + (g \<omega>)^4/2)" using f4 g4 by simp
  show "(\<lambda>\<omega>. (f \<omega>)\<^sup>2 * (g \<omega>)\<^sup>2) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm ((f \<omega>)\<^sup>2 * (g \<omega>)\<^sup>2) \<le> norm ((f \<omega>)^4/2 + (g \<omega>)^4/2)"
  proof (intro always_eventually allI)
    fix \<omega>
    have le: "(f \<omega>)\<^sup>2 * (g \<omega>)\<^sup>2 \<le> (f \<omega>)^4/2 + (g \<omega>)^4/2"
      by (rule prod_sq_le_half_pow4)
    have nn: "0 \<le> (f \<omega>)\<^sup>2 * (g \<omega>)\<^sup>2" by simp
    have nn2: "0 \<le> (f \<omega>)^4/2 + (g \<omega>)^4/2"
      using pow4_nonneg[of "f \<omega>"] pow4_nonneg[of "g \<omega>"] by linarith
    show "norm ((f \<omega>)\<^sup>2 * (g \<omega>)\<^sup>2) \<le> norm ((f \<omega>)^4/2 + (g \<omega>)^4/2)"
      using le nn nn2 by simp
  qed
qed

lemma integrable_cube_prod:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)" and g4: "integrable M (\<lambda>\<omega>. (g \<omega>)^4)"
    and fm[measurable]: "f \<in> borel_measurable M"
    and gm[measurable]: "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. (f \<omega>)^3 * g \<omega>)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. 3/4*(f \<omega>)^4 + 1/4*(g \<omega>)^4"])
  show "integrable M (\<lambda>\<omega>. 3/4*(f \<omega>)^4 + 1/4*(g \<omega>)^4)" using f4 g4 by simp
  show "(\<lambda>\<omega>. (f \<omega>)^3 * g \<omega>) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm ((f \<omega>)^3 * g \<omega>) \<le> norm (3/4*(f \<omega>)^4 + 1/4*(g \<omega>)^4)"
  proof (intro always_eventually allI)
    fix \<omega>
    have le: "\<bar>(f \<omega>)^3 * g \<omega>\<bar> \<le> 3/4*(f \<omega>)^4 + 1/4*(g \<omega>)^4"
      by (rule abs_cube_prod_le_pow4)
    have nn2: "0 \<le> 3/4*(f \<omega>)^4 + 1/4*(g \<omega>)^4"
      using pow4_nonneg[of "f \<omega>"] pow4_nonneg[of "g \<omega>"] by linarith
    show "norm ((f \<omega>)^3 * g \<omega>) \<le> norm (3/4*(f \<omega>)^4 + 1/4*(g \<omega>)^4)"
      using le nn2 by simp
  qed
qed

lemma integrable_prod_cube:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)" and g4: "integrable M (\<lambda>\<omega>. (g \<omega>)^4)"
    and fm[measurable]: "f \<in> borel_measurable M"
    and gm[measurable]: "g \<in> borel_measurable M"
  shows "integrable M (\<lambda>\<omega>. f \<omega> * (g \<omega>)^3)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. 1/4*(f \<omega>)^4 + 3/4*(g \<omega>)^4"])
  show "integrable M (\<lambda>\<omega>. 1/4*(f \<omega>)^4 + 3/4*(g \<omega>)^4)" using f4 g4 by simp
  show "(\<lambda>\<omega>. f \<omega> * (g \<omega>)^3) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm (f \<omega> * (g \<omega>)^3) \<le> norm (1/4*(f \<omega>)^4 + 3/4*(g \<omega>)^4)"
  proof (intro always_eventually allI)
    fix \<omega>
    have le: "\<bar>f \<omega> * (g \<omega>)^3\<bar> \<le> 1/4*(f \<omega>)^4 + 3/4*(g \<omega>)^4"
      by (rule abs_prod_cube_le_pow4)
    have nn2: "0 \<le> 1/4*(f \<omega>)^4 + 3/4*(g \<omega>)^4"
      using pow4_nonneg[of "f \<omega>"] pow4_nonneg[of "g \<omega>"] by linarith
    show "norm (f \<omega> * (g \<omega>)^3) \<le> norm (1/4*(f \<omega>)^4 + 3/4*(g \<omega>)^4)"
      using le nn2 by simp
  qed
qed

subsection \<open>The expectation of a conditional expectation\<close>

lemma expectation_cond_exp:
  assumes sfs: "sigma_finite_subalgebra M G"
    and sp: "space M \<in> sets G"
    and f: "integrable M f"
  shows "(\<integral>\<omega>. cond_exp M G f \<omega> \<partial>M) = (\<integral>\<omega>. f \<omega> \<partial>M)"
proof -
  have "set_lebesgue_integral M (space M) f
          = set_lebesgue_integral M (space M) (cond_exp M G f)"
    by (rule sigma_finite_subalgebra.cond_exp_set_integral[OF sfs f sp])
  moreover have "set_lebesgue_integral M (space M) f = (\<integral>\<omega>. f \<omega> \<partial>M)"
    by (rule set_integral_space[OF f])
  moreover have "set_lebesgue_integral M (space M) (cond_exp M G f)
          = (\<integral>\<omega>. cond_exp M G f \<omega> \<partial>M)"
    by (rule set_integral_space[OF integrable_cond_exp])
  ultimately show ?thesis by simp
qed

subsection \<open>Second moments along a partition, from per-interval covariation data\<close>

text \<open>
  A localised variant of @{thm [source] increment_second_moment_bound}: the
  conditional expectation of the squared increment over \<open>[t k, t (Suc k)]\<close>
  agrees with that of the compensator increment \<open>dA k\<close>, growing at rate at
  most @{term C} -- the form in which the admissible laws of \<^cite>\<open>LaiShkolnikovSoner\<close>
  supply their covariation constraint.
\<close>

theorem second_moment_partition_bound:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and dA_bounds: "\<And>k. AE \<omega> in M. 0 \<le> dA k \<omega> \<and> dA k \<omega> \<le> C * (t (Suc k) - t k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
  shows "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M) \<le> C * (t n - t 0)"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have XmM[measurable]: "X (t k) \<in> borel_measurable M" for k
    by (rule borel_measurable_integrable[OF MX.integrable[OF t0]])
  have sqk: "integrable M (\<lambda>\<omega>. (X (t k) \<omega>)\<^sup>2)" for k by (rule sq[OF t0])
  have tles: "t 0 \<le> t k" for k by (rule monoD[OF tmono]) simp
  have sfs: "sigma_finite_subalgebra M (F (t k))" for k
    by (rule MX.sigma_finite_subalgebra_F[OF t0])
  have spF: "space M \<in> sets (F (t k))" for k
    using sets.top[of "F (t k)"] MX.space_F[OF t0] by simp
  have iY2: "integrable M (\<lambda>\<omega>. (X (t j) \<omega> - X (t k) \<omega>)\<^sup>2)" for j k
    by (rule integrable_sq_diff'[OF sqk sqk XmM XmM])
  have iYd: "integrable M (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
                              * (X (t (Suc n)) \<omega> - X (t n) \<omega>))" for n
    by (intro integrable_prod_of_squares[OF iY2 iY2]
              borel_measurable_diff XmM)

  have EYd: "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>) \<partial>M) = 0" for n
  proof -
    have dint: "integrable M (\<lambda>\<omega>. X (t (Suc n)) \<omega> - X (t n) \<omega>)"
      by (intro Bochner_Integration.integrable_diff MX.integrable t0)
    have Ymeas: "(\<lambda>\<omega>. X (t n) \<omega> - X (t 0) \<omega>) \<in> borel_measurable (F (t n))"
      by (intro borel_measurable_diff MX.adaptedD[OF t0 order.refl]
                MX.adaptedD[OF t0 tles])
    have pull: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<omega>
          = (X (t n) \<omega> - X (t 0) \<omega>)
            * cond_exp M (F (t n)) (\<lambda>\<omega>. X (t (Suc n)) \<omega> - X (t n) \<omega>) \<omega>"
      by (intro sigma_finite_subalgebra.cond_exp_measurable_mult(2)[OF sfs]
                iYd dint Ymeas)
    have zero: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. X (t (Suc n)) \<omega> - X (t n) \<omega>) \<omega> = 0"
      by (rule MX.cond_exp_diff_eq_zero[OF t0 monoD[OF tmono]]) simp
    have z2: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<omega> = 0"
      using pull zero by eventually_elim simp
    have "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
               * (X (t (Suc n)) \<omega> - X (t n) \<omega>) \<partial>M)
            = (\<integral>\<omega>. cond_exp M (F (t n))
                     (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
                          * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<omega> \<partial>M)"
      by (rule expectation_cond_exp[OF sfs spF iYd, symmetric])
    also have "\<dots> = (\<integral>\<omega>. (0::real) \<partial>M)"
      by (intro integral_cong_AE
                sigma_finite_subalgebra.borel_measurable_cond_exp'[OF sfs]
                borel_measurable_const z2)
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed

  have Ed2: "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)
               \<le> C * (t (Suc n) - t n)" for n
  proof -
    have "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)
            = (\<integral>\<omega>. cond_exp M (F (t n))
                     (\<lambda>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<omega> \<partial>M)"
      by (rule expectation_cond_exp[OF sfs spF iY2, symmetric])
    also have "\<dots> = (\<integral>\<omega>. cond_exp M (F (t n)) (dA n) \<omega> \<partial>M)"
      by (intro integral_cong_AE
                sigma_finite_subalgebra.borel_measurable_cond_exp'[OF sfs] cov)
    also have "\<dots> = (\<integral>\<omega>. dA n \<omega> \<partial>M)"
      by (rule expectation_cond_exp[OF sfs spF dA_int])
    also have "\<dots> \<le> (\<integral>\<omega>. C * (t (Suc n) - t n) \<partial>M)"
    proof (rule integral_mono_AE)
      show "integrable M (dA n)" by (rule dA_int)
      show "integrable M (\<lambda>\<omega>. C * (t (Suc n) - t n))" by simp
      show "AE \<omega> in M. dA n \<omega> \<le> C * (t (Suc n) - t n)"
        using dA_bounds[of n] by eventually_elim linarith
    qed
    also have "(\<integral>\<omega>. C * (t (Suc n) - t n) \<partial>M) = C * (t (Suc n) - t n)"
      by (simp add: P.prob_space)
    finally show ?thesis .
  qed

  show ?thesis
  proof (induction n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have expand: "(X (t (Suc n)) \<omega> - X (t 0) \<omega>)\<^sup>2
        = (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
          + (2 * ((X (t n) \<omega> - X (t 0) \<omega>) * (X (t (Suc n)) \<omega> - X (t n) \<omega>))
             + (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)" for \<omega>
      by algebra
    have i2: "integrable M
        (\<lambda>\<omega>. 2 * ((X (t n) \<omega> - X (t 0) \<omega>) * (X (t (Suc n)) \<omega> - X (t n) \<omega>))
             + (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)"
      using iYd[of n] iY2[of "Suc n" n] by simp
    have split: "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M)
        = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M)
          + ((\<integral>\<omega>. 2 * ((X (t n) \<omega> - X (t 0) \<omega>)
                        * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<partial>M)
             + (\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M))"
    proof -
      have "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
              + (2 * ((X (t n) \<omega> - X (t 0) \<omega>)
                      * (X (t (Suc n)) \<omega> - X (t n) \<omega>))
                 + (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<partial>M)"
        by (simp add: expand)
      also have "\<dots> = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M)
          + ((\<integral>\<omega>. 2 * ((X (t n) \<omega> - X (t 0) \<omega>)
                        * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<partial>M)
             + (\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M))"
        using Bochner_Integration.integral_add[OF iY2 i2]
              Bochner_Integration.integral_add[OF _ iY2]
        by (simp add: iYd iY2)
      finally show ?thesis .
    qed
    have E2Yd: "(\<integral>\<omega>. 2 * ((X (t n) \<omega> - X (t 0) \<omega>)
                          * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<partial>M) = 0"
      using EYd[of n] by simp
    have arith: "C*(t n - t 0) + C*(t (Suc n) - t n) = C*(t (Suc n) - t 0)"
      by algebra
    from split E2Yd Ed2[of n] Suc.IH arith show ?case by linarith
  qed
qed

subsection \<open>Fourth moments along a partition: Eq. (2.7) with an explicit remainder\<close>

text \<open>
  Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close> is derived there through the Burkholder-Davis-Gundy
  inequality, which
  is absent from Isabelle and the AFP. The theorem below reaches the same bound by
  expanding \<open>(Y + d)^4\<close> directly along the partition using only conditional
  pull-outs: with a common constant \<open>8 C\<^sup>2\<close> (that route gives \<open>66 C\<^sup>2\<close>), the
  fourth moment of the increment is bounded by \<open>8 C\<^sup>2 (t-s)\<^sup>2\<close> plus three times the
  accumulated fourth moments of the partition increments, an explicit remainder
  vanishing in the mesh limit for continuous paths.

  The fourth-moment integrability hypothesis is discharged in the intended
  application by localisation: up to the exit time the paths live in the compact
  @{term K}, so all moments exist.
\<close>

theorem fourth_moment_partition_bound:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and q4: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)^4)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and dA_bounds: "\<And>k. AE \<omega> in M. 0 \<le> dA k \<omega> \<and> dA k \<omega> \<le> C * (t (Suc k) - t k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
    and C: "0 \<le> C"
  shows "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
           \<le> 8 * C\<^sup>2 * (t n - t 0)\<^sup>2
             + 3 * (\<Sum>k<n. (\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4 \<partial>M))"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have XmM[measurable]: "X (t k) \<in> borel_measurable M" for k
    by (rule borel_measurable_integrable[OF MX.integrable[OF t0]])
  have sq: "integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)" if u: "0 \<le> u" for u
    by (rule integrable_sq_of_pow4[OF P q4[OF u]
          borel_measurable_integrable[OF MX.integrable[OF u]]])
  have tles: "t 0 \<le> t k" for k by (rule monoD[OF tmono]) simp
  have tSk: "t k \<le> t (Suc k)" for k by (rule monoD[OF tmono]) simp
  have dt_nn: "0 \<le> t (Suc k) - t k" for k using tSk[of k] by simp
  have t0k_nn: "0 \<le> t k - t 0" for k using tles[of k] by simp
  have sfs: "sigma_finite_subalgebra M (F (t k))" for k
    by (rule MX.sigma_finite_subalgebra_F[OF t0])
  have spF: "space M \<in> sets (F (t k))" for k
    using sets.top[of "F (t k)"] MX.space_F[OF t0] by simp
  have q4k: "integrable M (\<lambda>\<omega>. (X (t k) \<omega>)^4)" for k by (rule q4[OF t0])
  have iY4: "integrable M (\<lambda>\<omega>. (X (t j) \<omega> - X (t k) \<omega>)^4)" for j k
    by (rule integrable_pow4_diff[OF q4k q4k XmM XmM])
  have Ymeas: "(\<lambda>\<omega>. X (t j) \<omega> - X (t k) \<omega>) \<in> borel_measurable M" for j k
    by measurable
  have iY2: "integrable M (\<lambda>\<omega>. (X (t j) \<omega> - X (t k) \<omega>)\<^sup>2)" for j k
    by (rule integrable_sq_of_pow4[OF P iY4 Ymeas])
  have iY2d2: "integrable M (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                                * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)" for n
    by (rule integrable_prod_sq_sq[OF iY4 iY4 Ymeas Ymeas])
  have iY3d: "integrable M (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3
                               * (X (t (Suc n)) \<omega> - X (t n) \<omega>))" for n
    by (rule integrable_cube_prod[OF iY4 iY4 Ymeas Ymeas])
  have iYd3: "integrable M (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)
                               * (X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)" for n
    by (rule integrable_prod_cube[OF iY4 iY4 Ymeas Ymeas])

  text \<open>The cubic cross term has vanishing expectation.\<close>
  have EY3d: "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3
                    * (X (t (Suc n)) \<omega> - X (t n) \<omega>) \<partial>M) = 0" for n
  proof -
    have dint: "integrable M (\<lambda>\<omega>. X (t (Suc n)) \<omega> - X (t n) \<omega>)"
      by (intro Bochner_Integration.integrable_diff MX.integrable t0)
    have Y3meas: "(\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3) \<in> borel_measurable (F (t n))"
      by (intro borel_measurable_power borel_measurable_diff
                MX.adaptedD[OF t0 order.refl] MX.adaptedD[OF t0 tles])
    have pull: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<omega>
          = (X (t n) \<omega> - X (t 0) \<omega>)^3
            * cond_exp M (F (t n)) (\<lambda>\<omega>. X (t (Suc n)) \<omega> - X (t n) \<omega>) \<omega>"
      by (intro sigma_finite_subalgebra.cond_exp_measurable_mult(2)[OF sfs]
                iY3d dint Y3meas)
    have zero: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. X (t (Suc n)) \<omega> - X (t n) \<omega>) \<omega> = 0"
      by (rule MX.cond_exp_diff_eq_zero[OF t0 monoD[OF tmono]]) simp
    have z2: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<omega> = 0"
      using pull zero by eventually_elim simp
    have "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3
               * (X (t (Suc n)) \<omega> - X (t n) \<omega>) \<partial>M)
            = (\<integral>\<omega>. cond_exp M (F (t n))
                     (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^3
                          * (X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<omega> \<partial>M)"
      by (rule expectation_cond_exp[OF sfs spF iY3d, symmetric])
    also have "\<dots> = (\<integral>\<omega>. (0::real) \<partial>M)"
      by (intro integral_cong_AE
                sigma_finite_subalgebra.borel_measurable_cond_exp'[OF sfs]
                borel_measurable_const z2)
    also have "\<dots> = 0" by simp
    finally show ?thesis .
  qed

  text \<open>The mixed square term is controlled by the covariation rate and the
    second-moment bound.\<close>
  have EY2d2: "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                    * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)
                 \<le> C\<^sup>2 * ((t (Suc n) - t n) * (t n - t 0))" for n
  proof -
    have Y2meas: "(\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2) \<in> borel_measurable (F (t n))"
      by (intro borel_measurable_power borel_measurable_diff
                MX.adaptedD[OF t0 order.refl] MX.adaptedD[OF t0 tles])
    have iY2dA: "integrable M (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>)"
    proof (rule Bochner_Integration.integrable_bound
             [of _ "\<lambda>\<omega>. (C * (t (Suc n) - t n)) * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2"])
      show "integrable M (\<lambda>\<omega>. (C * (t (Suc n) - t n))
                              * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2)"
        using iY2 by simp
      show "(\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>) \<in> borel_measurable M"
        using borel_measurable_integrable[OF dA_int[of n]] by measurable
      show "AE \<omega> in M. norm ((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>)
              \<le> norm ((C * (t (Suc n) - t n)) * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2)"
        using dA_bounds[of n]
      proof eventually_elim
        case (elim \<omega>)
        have nn: "0 \<le> (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>"
          using elim by simp
        have le: "(X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>
                    \<le> (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * (C * (t (Suc n) - t n))"
          using elim by (intro mult_left_mono) simp_all
        have nn2: "0 \<le> (C * (t (Suc n) - t n)) * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2"
          using C dt_nn[of n] by simp
        show ?case using nn le nn2 by (simp add: mult.commute)
      qed
    qed
    have pull1: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<omega>
          = (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
            * cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<omega>"
      by (intro sigma_finite_subalgebra.cond_exp_measurable_mult(2)[OF sfs]
                iY2d2 iY2 Y2meas)
    have pull2: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>) \<omega>
          = (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
            * cond_exp M (F (t n)) (dA n) \<omega>"
      by (intro sigma_finite_subalgebra.cond_exp_measurable_mult(2)[OF sfs]
                iY2dA dA_int Y2meas)
    have chain: "AE \<omega> in M.
        cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t n)) (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>) \<omega>"
      using pull1 pull2 cov[of n] by eventually_elim simp
    have "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
               * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)
            = (\<integral>\<omega>. cond_exp M (F (t n))
                     (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                          * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<omega> \<partial>M)"
      by (rule expectation_cond_exp[OF sfs spF iY2d2, symmetric])
    also have "\<dots> = (\<integral>\<omega>. cond_exp M (F (t n))
                          (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>) \<omega> \<partial>M)"
      by (intro integral_cong_AE
                sigma_finite_subalgebra.borel_measurable_cond_exp'[OF sfs] chain)
    also have "\<dots> = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega> \<partial>M)"
      by (rule expectation_cond_exp[OF sfs spF iY2dA])
    also have "\<dots> \<le> (\<integral>\<omega>. (C * (t (Suc n) - t n))
                          * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M)"
    proof (rule integral_mono_AE)
      show "integrable M (\<lambda>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>)"
        by (rule iY2dA)
      show "integrable M (\<lambda>\<omega>. (C * (t (Suc n) - t n))
                              * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2)"
        using iY2 by simp
      show "AE \<omega> in M. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>
              \<le> (C * (t (Suc n) - t n)) * (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2"
        using dA_bounds[of n]
      proof eventually_elim
        case (elim \<omega>)
        have "(X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * dA n \<omega>
                \<le> (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 * (C * (t (Suc n) - t n))"
          using elim by (intro mult_left_mono) simp_all
        thus ?case by (simp add: mult.commute)
      qed
    qed
    also have "\<dots> = (C * (t (Suc n) - t n))
                    * (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M)"
      by simp
    also have "\<dots> \<le> (C * (t (Suc n) - t n)) * (C * (t n - t 0))"
    proof (rule mult_left_mono)
      show "(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 \<partial>M) \<le> C * (t n - t 0)"
        by (rule second_moment_partition_bound[of M _ X t, OF P X t0 tmono sq dA_int
              dA_bounds cov])
      show "0 \<le> C * (t (Suc n) - t n)" using C dt_nn[of n] by simp
    qed
    also have "(C * (t (Suc n) - t n)) * (C * (t n - t 0))
                 = C\<^sup>2 * ((t (Suc n) - t n) * (t n - t 0))" by algebra
    finally show ?thesis .
  qed

  text \<open>The odd cross term is absorbed into the mixed square and the remainder.\<close>
  have EYd3: "(\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                      * (X (t (Suc n)) \<omega> - X (t n) \<omega>)^3) \<partial>M)
                \<le> 2*(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                          * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)
                  + 2*(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)" for n
  proof -
    have iA: "integrable M (\<lambda>\<omega>. 2*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2))"
      using iY2d2 by simp
    have iB: "integrable M (\<lambda>\<omega>. 2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)"
      using iY4 by simp
    have "(\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                  * (X (t (Suc n)) \<omega> - X (t n) \<omega>)^3) \<partial>M)
            \<le> (\<integral>\<omega>. 2*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                       * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                    + 2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)"
    proof (rule integral_mono)
      show "integrable M (\<lambda>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                                 * (X (t (Suc n)) \<omega> - X (t n) \<omega>)^3))"
        using iYd3 by simp
      show "integrable M (\<lambda>\<omega>. 2*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                                 * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                              + 2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)"
        using iA iB by simp
      show "\<And>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                   * (X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
              \<le> 2*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                    * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                + 2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^4"
        by (rule four_prod_cube_le)
    qed
    also have "\<dots> = (\<integral>\<omega>. 2*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                            * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<partial>M)
                    + (\<integral>\<omega>. 2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)"
      by (rule Bochner_Integration.integral_add[OF iA iB])
    also have "\<dots> = 2*(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                          * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)
                    + 2*(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)"
      by simp
    finally show ?thesis .
  qed
  text \<open>The per-interval recursion, from the binomial expansion of \<open>(Y + d)^4\<close>.\<close>
  have step: "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
                \<le> (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
                  + 8*(C\<^sup>2*((t (Suc n) - t n)*(t n - t 0)))
                  + 3*(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)" for n
  proof -
    have i_r3: "integrable M
        (\<lambda>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
             + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)"
      using iYd3[of n] iY4 by simp
    have i_r2: "integrable M
        (\<lambda>\<omega>. 6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
             + (4*((X (t n) \<omega> - X (t 0) \<omega>)*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4))"
      using iY2d2[of n] i_r3 by simp
    have i_r1: "integrable M
        (\<lambda>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>))
             + (6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                + (4*((X (t n) \<omega> - X (t 0) \<omega>)*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                   + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)))"
      using iY3d[of n] i_r2 by simp
    have i4Y3d: "integrable M
        (\<lambda>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>)))"
      using iY3d[of n] by simp
    have i6Y2d2: "integrable M
        (\<lambda>\<omega>. 6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2))"
      using iY2d2[of n] by simp
    have i4Yd3: "integrable M
        (\<lambda>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)*(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3))"
      using iYd3[of n] by simp
    have expand: "(X (t (Suc n)) \<omega> - X (t 0) \<omega>)^4
        = (X (t n) \<omega> - X (t 0) \<omega>)^4
          + (4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>))
             + (6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2*(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                      *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                   + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)))" for \<omega>
      by algebra
    have calc: "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
        = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
          + (\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>))
                 + (6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                       *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                    + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                          *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                       + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)) \<partial>M)"
    proof -
      have "(\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
          = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^4
              + (4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>))
                 + (6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                       *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                    + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                          *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                       + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4))) \<partial>M)"
        by (rule Bochner_Integration.integral_cong[OF refl]) (rule expand)
      also have "\<dots> = (\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)^4 \<partial>M)
          + (\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>))
                 + (6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                       *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                    + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                          *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                       + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)) \<partial>M)"
        by (rule Bochner_Integration.integral_add[OF iY4 i_r1])
      finally show ?thesis .
    qed
    have sr1: "(\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3*(X (t (Suc n)) \<omega> - X (t n) \<omega>))
                    + (6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                          *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                       + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                             *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                          + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4)) \<partial>M)
        = (\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3
                   *(X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<partial>M)
          + (\<integral>\<omega>. 6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                     *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                 + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                       *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                    + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4) \<partial>M)"
      by (rule Bochner_Integration.integral_add[OF i4Y3d i_r2])
    have sr2: "(\<integral>\<omega>. 6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                       *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)
                    + (4*((X (t n) \<omega> - X (t 0) \<omega>)
                          *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                       + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4) \<partial>M)
        = (\<integral>\<omega>. 6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                   *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<partial>M)
          + (\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                     *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                 + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)"
      by (rule Bochner_Integration.integral_add[OF i6Y2d2 i_r3])
    have sr3: "(\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                       *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3)
                    + (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)
        = (\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)
                   *(X (t (Suc n)) \<omega> - X (t n) \<omega>)^3) \<partial>M)
          + (\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)"
      by (rule Bochner_Integration.integral_add[OF i4Yd3 iY4])
    have v1: "(\<integral>\<omega>. 4*((X (t n) \<omega> - X (t 0) \<omega>)^3
                      *(X (t (Suc n)) \<omega> - X (t n) \<omega>)) \<partial>M) = 0"
      using EY3d[of n] by simp
    have v2: "(\<integral>\<omega>. 6*((X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                      *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2) \<partial>M)
        = 6*(\<integral>\<omega>. (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
                 *(X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2 \<partial>M)"
      by simp
    show ?thesis
      using calc sr1 sr2 sr3 v1 v2 EY2d2[of n] EYd3[of n] by linarith
  qed

  show ?thesis
  proof (induction n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have e1: "8*C\<^sup>2*(t n - t 0)\<^sup>2 + 8*(C\<^sup>2*((t (Suc n) - t n)*(t n - t 0)))
                = 8*C\<^sup>2*((t (Suc n) - t 0)*(t n - t 0))" by algebra
    have bnn: "0 \<le> t (Suc n) - t 0" using t0k_nn[of "Suc n"] .
    have ab: "t n - t 0 \<le> t (Suc n) - t 0" using tSk[of n] by linarith
    have e3: "8*C\<^sup>2*((t (Suc n) - t 0)*(t n - t 0)) \<le> 8*C\<^sup>2*(t (Suc n) - t 0)\<^sup>2"
    proof -
      have h: "(t (Suc n) - t 0)*(t n - t 0) \<le> (t (Suc n) - t 0)\<^sup>2"
      proof -
        have "(t (Suc n) - t 0)*(t n - t 0)
                \<le> (t (Suc n) - t 0)*(t (Suc n) - t 0)"
          by (rule mult_left_mono[OF ab bnn])
        thus ?thesis by (simp add: power2_eq_square)
      qed
      show ?thesis by (rule mult_left_mono[OF h]) simp
    qed
    have ssum: "(\<Sum>k<Suc n. (\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4 \<partial>M))
                  = (\<Sum>k<n. (\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4 \<partial>M))
                    + (\<integral>\<omega>. (X (t (Suc n)) \<omega> - X (t n) \<omega>)^4 \<partial>M)"
      by simp
    from step[of n] Suc.IH e1 e3 ssum show ?case by linarith
  qed
qed

subsection \<open>Per-interval energy, standalone\<close>

text \<open>
  The mesh limit of the remainder \<open>SUM E[d_k^4]\<close> rests on the uniform bound
  \<open>E[(SUM d_k\<^sup>2)\<^sup>2] \<le> 4 R\<^sup>2 C (t-s) + C\<^sup>2 (t-s)\<^sup>2\<close>, which makes \<open>SUM d_k\<^sup>2\<close> bounded
  in \<open>L\<^sup>2\<close> uniformly over partitions. This subsection isolates the per-interval
  facts it needs.
\<close>

lemma sq_times_sq: "(x::real)\<^sup>2 * x\<^sup>2 = x^4"
  by algebra

lemma interval_sq_eq_dA:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
  shows "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M) = (\<integral>\<omega>. dA k \<omega> \<partial>M)"
proof -
  interpret MX: martingale M F "0::real" X by (rule X)
  have XmM[measurable]: "X (t k) \<in> borel_measurable M" for k
    by (rule borel_measurable_integrable[OF MX.integrable[OF t0]])
  have sfs: "sigma_finite_subalgebra M (F (t k))" for k
    by (rule MX.sigma_finite_subalgebra_F[OF t0])
  have spF: "space M \<in> sets (F (t k))" for k
    using sets.top[of "F (t k)"] MX.space_F[OF t0] by simp
  have iY2: "integrable M (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
    by (rule integrable_sq_diff'[OF sq[OF t0] sq[OF t0] XmM XmM])
  have "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. cond_exp M (F (t k))
                   (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega> \<partial>M)"
    by (rule expectation_cond_exp[OF sfs spF iY2, symmetric])
  also have "\<dots> = (\<integral>\<omega>. cond_exp M (F (t k)) (dA k) \<omega> \<partial>M)"
    by (intro integral_cong_AE
              sigma_finite_subalgebra.borel_measurable_cond_exp'[OF sfs] cov)
  also have "\<dots> = (\<integral>\<omega>. dA k \<omega> \<partial>M)"
    by (rule expectation_cond_exp[OF sfs spF dA_int])
  finally show ?thesis .
qed

lemma interval_sq_le:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and dA_bounds: "\<And>k. AE \<omega> in M. 0 \<le> dA k \<omega> \<and> dA k \<omega> \<le> C * (t (Suc k) - t k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
  shows "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M) \<le> C * (t (Suc k) - t k)"
proof -
  interpret P: prob_space M by (rule P)
  have "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M) = (\<integral>\<omega>. dA k \<omega> \<partial>M)"
    by (rule interval_sq_eq_dA[of M _ X t, OF P X t0 tmono sq dA_int cov])
  also have "\<dots> \<le> (\<integral>\<omega>. C * (t (Suc k) - t k) \<partial>M)"
  proof (rule integral_mono_AE)
    show "integrable M (dA k)" by (rule dA_int)
    show "integrable M (\<lambda>\<omega>. C * (t (Suc k) - t k))" by simp
    show "AE \<omega> in M. dA k \<omega> \<le> C * (t (Suc k) - t k)"
      using dA_bounds[of k] by eventually_elim linarith
  qed
  also have "\<dots> = C * (t (Suc k) - t k)" by (simp add: P.prob_space)
  finally show ?thesis .
qed

text \<open>
  The mixed-term estimate with an arbitrary weight measurable at the left end
  of the interval: \<open>E[f\<^sup>2 d_k\<^sup>2] \<le> C \<Delta>t_k E[f\<^sup>2]\<close>. Taking \<open>f\<close> to be an earlier
  increment gives the off-diagonal terms of \<open>E[(SUM d\<^sup>2)\<^sup>2]\<close>.
\<close>

lemma weighted_interval_bound:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
    and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real" and f :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and q4: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)^4)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and dA_bounds: "\<And>k. AE \<omega> in M. 0 \<le> dA k \<omega> \<and> dA k \<omega> \<le> C * (t (Suc k) - t k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
    and C: "0 \<le> C"
    and f4: "integrable M (\<lambda>\<omega>. (f \<omega>)^4)"
    and fF: "f \<in> borel_measurable (F (t k))"
  shows "(\<integral>\<omega>. (f \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
           \<le> (C * (t (Suc k) - t k)) * (\<integral>\<omega>. (f \<omega>)\<^sup>2 \<partial>M)"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have XmM[measurable]: "X (t k) \<in> borel_measurable M" for k
    by (rule borel_measurable_integrable[OF MX.integrable[OF t0]])
  have tSk: "t k \<le> t (Suc k)" by (rule monoD[OF tmono]) simp
  have dt_nn: "0 \<le> t (Suc k) - t k" using tSk by simp
  have sfs: "sigma_finite_subalgebra M (F (t k))"
    by (rule MX.sigma_finite_subalgebra_F[OF t0])
  have spF: "space M \<in> sets (F (t k))"
    using sets.top[of "F (t k)"] MX.space_F[OF t0] by simp
  have fmM[measurable]: "f \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF sigma_finite_subalgebra.subalg[OF sfs] fF])
  have if2: "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2)"
    by (rule integrable_sq_of_pow4[OF P f4 fmM])
  have iY4k: "integrable M (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4)"
    by (rule integrable_pow4_diff[OF q4[OF t0] q4[OF t0] XmM XmM])
  have dmeasM: "(\<lambda>\<omega>. X (t (Suc k)) \<omega> - X (t k) \<omega>) \<in> borel_measurable M"
    by measurable
  have id2: "integrable M (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
    by (rule integrable_sq_of_pow4[OF P iY4k dmeasM])
  have if2d2: "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
    by (rule integrable_prod_sq_sq[OF f4 iY4k fmM dmeasM])
  have f2F: "(\<lambda>\<omega>. (f \<omega>)\<^sup>2) \<in> borel_measurable (F (t k))"
    using fF by measurable
  have if2dA: "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega>)"
  proof (rule Bochner_Integration.integrable_bound
           [of _ "\<lambda>\<omega>. (C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2"])
    show "integrable M (\<lambda>\<omega>. (C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2)"
      using if2 by simp
    show "(\<lambda>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega>) \<in> borel_measurable M"
      using borel_measurable_integrable[OF dA_int[of k]] by measurable
    show "AE \<omega> in M. norm ((f \<omega>)\<^sup>2 * dA k \<omega>)
            \<le> norm ((C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2)"
      using dA_bounds[of k]
    proof eventually_elim
      case (elim \<omega>)
      have nn: "0 \<le> (f \<omega>)\<^sup>2 * dA k \<omega>" using elim by simp
      have le: "(f \<omega>)\<^sup>2 * dA k \<omega> \<le> (f \<omega>)\<^sup>2 * (C * (t (Suc k) - t k))"
        using elim by (intro mult_left_mono) simp_all
      have nn2: "0 \<le> (C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2"
        using C dt_nn by simp
      show ?case using nn le nn2 by (simp add: mult.commute)
    qed
  qed
  have pull1: "AE \<omega> in M.
      cond_exp M (F (t k)) (\<lambda>\<omega>. (f \<omega>)\<^sup>2
                                 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
        = (f \<omega>)\<^sup>2
          * cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>"
    by (intro sigma_finite_subalgebra.cond_exp_measurable_mult(2)[OF sfs]
              if2d2 id2 f2F)
  have pull2: "AE \<omega> in M.
      cond_exp M (F (t k)) (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega>) \<omega>
        = (f \<omega>)\<^sup>2 * cond_exp M (F (t k)) (dA k) \<omega>"
    by (intro sigma_finite_subalgebra.cond_exp_measurable_mult(2)[OF sfs]
              if2dA dA_int f2F)
  have chain: "AE \<omega> in M.
      cond_exp M (F (t k)) (\<lambda>\<omega>. (f \<omega>)\<^sup>2
                                 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
        = cond_exp M (F (t k)) (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega>) \<omega>"
    using pull1 pull2 cov[of k] by eventually_elim simp
  have "(\<integral>\<omega>. (f \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. cond_exp M (F (t k))
                   (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega> \<partial>M)"
    by (rule expectation_cond_exp[OF sfs spF if2d2, symmetric])
  also have "\<dots> = (\<integral>\<omega>. cond_exp M (F (t k))
                        (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega>) \<omega> \<partial>M)"
    by (intro integral_cong_AE
              sigma_finite_subalgebra.borel_measurable_cond_exp'[OF sfs] chain)
  also have "\<dots> = (\<integral>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega> \<partial>M)"
    by (rule expectation_cond_exp[OF sfs spF if2dA])
  also have "\<dots> \<le> (\<integral>\<omega>. (C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2 \<partial>M)"
  proof (rule integral_mono_AE)
    show "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2 * dA k \<omega>)" by (rule if2dA)
    show "integrable M (\<lambda>\<omega>. (C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2)"
      using if2 by simp
    show "AE \<omega> in M. (f \<omega>)\<^sup>2 * dA k \<omega>
            \<le> (C * (t (Suc k) - t k)) * (f \<omega>)\<^sup>2"
      using dA_bounds[of k]
    proof eventually_elim
      case (elim \<omega>)
      have "(f \<omega>)\<^sup>2 * dA k \<omega> \<le> (f \<omega>)\<^sup>2 * (C * (t (Suc k) - t k))"
        using elim by (intro mult_left_mono) simp_all
      thus ?case by (simp add: mult.commute)
    qed
  qed
  also have "\<dots> = (C * (t (Suc k) - t k)) * (\<integral>\<omega>. (f \<omega>)\<^sup>2 \<partial>M)"
    by simp
  finally show ?thesis .
qed

text \<open>The diagonal terms, for a martingale bounded by @{term R}: the fourth
  moment of one increment is at most \<open>4 R\<^sup>2\<close> times its second moment.\<close>

lemma interval_pow4_le:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and q4: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)^4)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and dA_bounds: "\<And>k. AE \<omega> in M. 0 \<le> dA k \<omega> \<and> dA k \<omega> \<le> C * (t (Suc k) - t k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
    and R: "0 \<le> R"
    and bnd: "\<And>k. AE \<omega> in M. \<bar>X (t k) \<omega>\<bar> \<le> R"
  shows "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4 \<partial>M)
           \<le> 4*R\<^sup>2*(C*(t (Suc k) - t k))"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have XmM[measurable]: "X (t k) \<in> borel_measurable M" for k
    by (rule borel_measurable_integrable[OF MX.integrable[OF t0]])
  have sq: "integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)" if u: "0 \<le> u" for u
    by (rule integrable_sq_of_pow4[OF P q4[OF u]
          borel_measurable_integrable[OF MX.integrable[OF u]]])
  have iY4k: "integrable M (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4)"
    by (rule integrable_pow4_diff[OF q4[OF t0] q4[OF t0] XmM XmM])
  have id2: "integrable M (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
    by (rule integrable_sq_diff'[OF sq[OF t0] sq[OF t0] XmM XmM])
  have ae: "AE \<omega> in M. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4
              \<le> 4*R\<^sup>2*(X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2"
    using bnd[of k] bnd[of "Suc k"]
  proof eventually_elim
    case (elim \<omega>)
    have tri: "\<bar>X (t (Suc k)) \<omega> - X (t k) \<omega>\<bar>
                 \<le> \<bar>X (t (Suc k)) \<omega>\<bar> + \<bar>X (t k) \<omega>\<bar>"
      by (rule abs_triangle_ineq4)
    have habs: "\<bar>X (t (Suc k)) \<omega> - X (t k) \<omega>\<bar> \<le> 2*R"
      using tri elim by linarith
    have hsq: "(X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<le> (2*R)\<^sup>2"
    proof -
      have "\<bar>X (t (Suc k)) \<omega> - X (t k) \<omega>\<bar>\<^sup>2 \<le> (2*R)\<^sup>2"
        by (rule power_mono[OF habs abs_ge_zero])
      thus ?thesis by simp
    qed
    have e1: "(X (t (Suc k)) \<omega> - X (t k) \<omega>)^4
        = (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2"
      by (simp add: sq_times_sq)
    have e2: "(X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
        \<le> (2*R)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2"
      by (rule mult_right_mono[OF hsq zero_le_power2])
    have e3: "(2*R)\<^sup>2 = 4*R\<^sup>2" by algebra
    have "(X (t (Suc k)) \<omega> - X (t k) \<omega>)^4
        \<le> (2*R)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2"
      using e1 e2 by linarith
    thus ?case using e3 by simp
  qed
  have "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4 \<partial>M)
          \<le> (\<integral>\<omega>. 4*R\<^sup>2*(X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)"
  proof (rule integral_mono_AE)
    show "integrable M (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4)" by (rule iY4k)
    show "integrable M (\<lambda>\<omega>. 4*R\<^sup>2*(X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)"
      using id2 by simp
    show "AE \<omega> in M. (X (t (Suc k)) \<omega> - X (t k) \<omega>)^4
            \<le> 4*R\<^sup>2*(X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2" by (rule ae)
  qed
  also have "\<dots> = 4*R\<^sup>2*(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)"
    by simp
  also have "\<dots> \<le> 4*R\<^sup>2*(C*(t (Suc k) - t k))"
  proof (rule mult_left_mono)
    show "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M) \<le> C*(t (Suc k) - t k)"
      by (rule interval_sq_le[of M _ X t, OF P X t0 tmono sq dA_int dA_bounds cov])
    show "0 \<le> 4*R\<^sup>2" by simp
  qed
  finally show ?thesis .
qed

subsection \<open>The sum of squared increments is bounded in \<open>L\<^sup>2\<close>, uniformly in the partition\<close>

text \<open>
  For a martingale bounded by @{term R} with covariation rate at most @{term C},

    \<open>E[(SUM_{k<n} d_k\<^sup>2)\<^sup>2] \<le> 4 R\<^sup>2 C (t n - t 0) + C\<^sup>2 (t n - t 0)\<^sup>2\<close>

  holds for every partition, the diagonal controlled by @{thm [source]
  interval_pow4_le} and each off-diagonal term by @{thm [source]
  weighted_interval_bound}. This bounds \<open>SUM d\<^sup>2\<close> in \<open>L\<^sup>2\<close> uniformly over
  partitions, letting the mesh limit of the remainder be taken by the
  \<open>K\<close>-split \<open>W S \<le> K W + 4 R\<^sup>2 S\<^sup>2 / K\<close>.
\<close>

theorem sum_sq_squared_bound:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real" and dA :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and q4: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)^4)"
    and dA_int: "\<And>k. integrable M (dA k)"
    and dA_bounds: "\<And>k. AE \<omega> in M. 0 \<le> dA k \<omega> \<and> dA k \<omega> \<le> C * (t (Suc k) - t k)"
    and cov: "\<And>k. AE \<omega> in M.
        cond_exp M (F (t k)) (\<lambda>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<omega>
          = cond_exp M (F (t k)) (dA k) \<omega>"
    and C: "0 \<le> C"
    and R: "0 \<le> R"
    and bnd: "\<And>k. AE \<omega> in M. \<bar>X (t k) \<omega>\<bar> \<le> R"
  shows "(\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
           \<le> 4*R\<^sup>2*C*(t n - t 0) + C\<^sup>2*(t n - t 0)\<^sup>2"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have XmM[measurable]: "X (t k) \<in> borel_measurable M" for k
    by (rule borel_measurable_integrable[OF MX.integrable[OF t0]])
  have sq: "integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)" if u: "0 \<le> u" for u
    by (rule integrable_sq_of_pow4[OF P q4[OF u]
          borel_measurable_integrable[OF MX.integrable[OF u]]])
  have dt_nn: "0 \<le> t (Suc k) - t k" for k
    using monoD[OF tmono, of k "Suc k"] by simp
  have iY4: "integrable M (\<lambda>\<omega>. (X (t j) \<omega> - X (t k) \<omega>)^4)" for j k
    by (rule integrable_pow4_diff[OF q4[OF t0] q4[OF t0] XmM XmM])
  have dmeasM: "(\<lambda>\<omega>. X (t j) \<omega> - X (t k) \<omega>) \<in> borel_measurable M" for j k
    by measurable
  have ipair: "integrable M (\<lambda>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                                 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)" for j k
    by (rule integrable_prod_sq_sq[OF iY4 iY4 dmeasM dmeasM])

  have offdiag: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                      * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
                   \<le> C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))"
    if jk: "Suc j \<le> k" for j k
  proof -
    have jle: "j \<le> k" using jk by linarith
    have fF: "(\<lambda>\<omega>. X (t (Suc j)) \<omega> - X (t j) \<omega>) \<in> borel_measurable (F (t k))"
      by (intro borel_measurable_diff
                MX.adaptedD[OF t0 monoD[OF tmono jk]]
                MX.adaptedD[OF t0 monoD[OF tmono jle]])
    have w: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                  * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
               \<le> (C * (t (Suc k) - t k))
                 * (\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)"
      by (rule weighted_interval_bound[OF P X t0 tmono q4 dA_int dA_bounds
            cov C iY4 fF])
    have s: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)
               \<le> C * (t (Suc j) - t j)"
      by (rule interval_sq_le[of M _ X t, OF P X t0 tmono sq dA_int dA_bounds cov])
    have cd: "0 \<le> C * (t (Suc k) - t k)"
      by (rule mult_nonneg_nonneg[OF C dt_nn])
    have m: "(C * (t (Suc k) - t k))
             * (\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)
               \<le> (C * (t (Suc k) - t k)) * (C * (t (Suc j) - t j))"
      by (rule mult_left_mono[OF s cd])
    have alg: "(C * (t (Suc k) - t k)) * (C * (t (Suc j) - t j))
                 = C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))" by algebra
    from w m alg show ?thesis by linarith
  qed

  have per_pair: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                       * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
                    \<le> C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))
                      + (if k = j then 4*R\<^sup>2*(C*(t (Suc j) - t j)) else 0)" for j k
  proof (cases "k = j")
    case True
    have e: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                  * (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)
               = (\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)^4 \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl) (simp add: sq_times_sq)
    have b: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)^4 \<partial>M)
               \<le> 4*R\<^sup>2*(C*(t (Suc j) - t j))"
      by (rule interval_pow4_le[of M _ X t, OF P X t0 tmono q4 dA_int dA_bounds cov R bnd])
    have nn: "0 \<le> C\<^sup>2*((t (Suc j) - t j)*(t (Suc j) - t j))"
      by (intro mult_nonneg_nonneg zero_le_power2 dt_nn)
    have goal': "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                      * (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)
                   \<le> C\<^sup>2*((t (Suc j) - t j)*(t (Suc j) - t j))
                     + 4*R\<^sup>2*(C*(t (Suc j) - t j))"
      using e b nn by linarith
    show ?thesis using True goal' by simp
  next
    case False
    then have "Suc j \<le> k \<or> Suc k \<le> j" by linarith
    then have main: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                          * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
                       \<le> C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))"
    proof
      assume "Suc j \<le> k"
      thus ?thesis by (rule offdiag)
    next
      assume kj: "Suc k \<le> j"
      have comm: "(\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                       * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M)
                    = (\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                           * (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)"
        by (intro Bochner_Integration.integral_cong refl) (simp add: mult.commute)
      have o: "(\<integral>\<omega>. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                    * (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2 \<partial>M)
                 \<le> C\<^sup>2*((t (Suc k) - t k)*(t (Suc j) - t j))"
        by (rule offdiag[OF kj])
      have alg: "C\<^sup>2*((t (Suc k) - t k)*(t (Suc j) - t j))
                   = C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))" by algebra
      from comm o alg show ?thesis by linarith
    qed
    show ?thesis using False main by simp
  qed

  have pw: "(\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)\<^sup>2
      = (\<Sum>j<n. \<Sum>k<n. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                       * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)" for \<omega>
    by (simp add: power2_eq_square sum_product)
  have isum_inner: "integrable M
      (\<lambda>\<omega>. \<Sum>k<n. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                  * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)" for j
    by (intro Bochner_Integration.integrable_sum ipair)
  have split1: "(\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
      = (\<Sum>j<n. (\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                             * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<partial>M))"
  proof -
    have "(\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
        = (\<integral>\<omega>. (\<Sum>j<n. \<Sum>k<n. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                              * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<partial>M)"
      by (intro Bochner_Integration.integral_cong refl) (rule pw)
    also have "\<dots> = (\<Sum>j<n. (\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                                        * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<partial>M))"
      by (rule Bochner_Integration.integral_sum[OF isum_inner])
    finally show ?thesis .
  qed
  have split2: "(\<Sum>j<n. (\<integral>\<omega>. (\<Sum>k<n. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                                    * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2) \<partial>M))
      = (\<Sum>j<n. \<Sum>k<n. (\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                            * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M))"
    by (intro sum.cong refl Bochner_Integration.integral_sum ipair)
  have bound: "(\<Sum>j<n. \<Sum>k<n. (\<integral>\<omega>. (X (t (Suc j)) \<omega> - X (t j) \<omega>)\<^sup>2
                                   * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2 \<partial>M))
      \<le> (\<Sum>j<n. \<Sum>k<n. (C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))
                        + (if k = j then 4*R\<^sup>2*(C*(t (Suc j) - t j)) else 0)))"
    by (intro sum_mono per_pair)
  have rhs1: "(\<Sum>j<n. \<Sum>k<n. (C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k))
                             + (if k = j then 4*R\<^sup>2*(C*(t (Suc j) - t j)) else 0)))
      = (\<Sum>j<n. \<Sum>k<n. C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k)))
        + (\<Sum>j<n. \<Sum>k<n. (if k = j then 4*R\<^sup>2*(C*(t (Suc j) - t j)) else 0))"
    by (simp add: sum.distrib)
  have rhs2: "(\<Sum>j<n. \<Sum>k<n. C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k)))
      = C\<^sup>2*((\<Sum>j<n. (t (Suc j) - t j)) * (\<Sum>k<n. (t (Suc k) - t k)))"
  proof -
    have "(\<Sum>j<n. \<Sum>k<n. C\<^sup>2*((t (Suc j) - t j)*(t (Suc k) - t k)))
        = C\<^sup>2*(\<Sum>j<n. \<Sum>k<n. (t (Suc j) - t j)*(t (Suc k) - t k))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = C\<^sup>2*((\<Sum>j<n. (t (Suc j) - t j)) * (\<Sum>k<n. (t (Suc k) - t k)))"
      by (simp add: sum_product[symmetric])
    finally show ?thesis .
  qed
  have rhs3: "(\<Sum>j<n. \<Sum>k<n. (if k = j then 4*R\<^sup>2*(C*(t (Suc j) - t j)) else 0))
      = (\<Sum>j<n. 4*R\<^sup>2*(C*(t (Suc j) - t j)))"
    by simp
  have rhs4: "(\<Sum>j<n. 4*R\<^sup>2*(C*(t (Suc j) - t j)))
      = 4*R\<^sup>2*(C*(\<Sum>j<n. (t (Suc j) - t j)))"
    by (simp add: sum_distrib_left)
  have tel: "(\<Sum>j<n. (t (Suc j) - t j)) = t n - t 0"
    by (rule sum_lessThan_telescope)
  have shape1: "C\<^sup>2*((t n - t 0) * (t n - t 0)) = C\<^sup>2*(t n - t 0)\<^sup>2" by algebra
  have shape2: "4*R\<^sup>2*(C*(t n - t 0)) = 4*R\<^sup>2*C*(t n - t 0)" by algebra
  have bridge1: "C\<^sup>2*((\<Sum>j<n. (t (Suc j) - t j)) * (\<Sum>k<n. (t (Suc k) - t k)))
                   = C\<^sup>2*((t n - t 0)*(t n - t 0))"
    using tel by simp
  have bridge2: "4*R\<^sup>2*(C*(\<Sum>j<n. (t (Suc j) - t j))) = 4*R\<^sup>2*(C*(t n - t 0))"
    using tel by simp
  show ?thesis
    using split1 split2 bound rhs1 rhs2 rhs3 rhs4 bridge1 bridge2
          shape1 shape2 by linarith
qed

subsection \<open>The uniform partitions of \<open>[s, T]\<close>\<close>

text \<open>
  The \<open>m\<close>-th uniform partition of \<open>[s,T]\<close> has \<open>Suc m\<close> intervals (never zero, so
  maxima over the increments are well defined) and is capped at \<open>T\<close>, so it is
  defined and monotone on all of @{typ nat}, which is the shape the partition
  theorems above expect.
\<close>

definition upart :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "upart s T m k = s + (T - s) * real (min k (Suc m)) / real (Suc m)"

lemma upart_zero [simp]: "upart s T m 0 = s"
  by (simp add: upart_def)

lemma upart_top: "Suc m \<le> k \<Longrightarrow> upart s T m k = T"
  by (simp add: upart_def min_absorb2)

lemma upart_mono: assumes sT: "s \<le> T" shows "mono (upart s T m)"
proof (rule monoI)
  fix j k :: nat assume jk: "j \<le> k"
  have "real (min j (Suc m)) \<le> real (min k (Suc m))"
    using min.mono[OF jk order_refl] by simp
  hence "(T - s) * real (min j (Suc m)) / real (Suc m)
           \<le> (T - s) * real (min k (Suc m)) / real (Suc m)"
    using sT by (intro divide_right_mono mult_left_mono) simp_all
  thus "upart s T m j \<le> upart s T m k" by (simp add: upart_def)
qed

lemma upart_ge_s: assumes sT: "s \<le> T" shows "s \<le> upart s T m k"
proof -
  have "0 \<le> (T - s) * real (min k (Suc m)) / real (Suc m)"
    using sT by (intro divide_nonneg_nonneg mult_nonneg_nonneg) simp_all
  thus ?thesis by (simp add: upart_def)
qed

lemma upart_nonneg: "0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> 0 \<le> upart s T m k"
  using upart_ge_s[of s T m k] by linarith

lemma upart_le_T: assumes sT: "s \<le> T" shows "upart s T m k \<le> T"
proof -
  have "real (min k (Suc m)) / real (Suc m) \<le> 1"
    by (simp add: divide_le_eq_1)
  hence "(T - s) * (real (min k (Suc m)) / real (Suc m)) \<le> (T - s) * 1"
    using sT by (intro mult_left_mono) simp_all
  thus ?thesis by (simp add: upart_def)
qed

lemma upart_mem: "s \<le> T \<Longrightarrow> upart s T m k \<in> {s..T}"
  using upart_ge_s upart_le_T by simp

lemma upart_diff_le:
  assumes sT: "s \<le> T"
  shows "upart s T m (Suc k) - upart s T m k \<le> (T - s) / real (Suc m)"
proof -
  have h: "min (Suc k) (Suc m) \<le> Suc (min k (Suc m))"
    by (simp add: min_def)
  have hr: "real (min (Suc k) (Suc m)) - real (min k (Suc m)) \<le> 1"
    using h by simp
  have "upart s T m (Suc k) - upart s T m k
          = (T - s) * real (min (Suc k) (Suc m)) / real (Suc m)
            - (T - s) * real (min k (Suc m)) / real (Suc m)"
    by (simp add: upart_def)
  also have "\<dots> = ((T - s) * real (min (Suc k) (Suc m))
                   - (T - s) * real (min k (Suc m))) / real (Suc m)"
    by (simp add: diff_divide_distrib)
  also have "\<dots> = (T - s) * (real (min (Suc k) (Suc m))
                             - real (min k (Suc m))) / real (Suc m)"
    by (simp add: right_diff_distrib)  also have "\<dots> \<le> (T - s) * 1 / real (Suc m)"
    using sT hr by (intro divide_right_mono mult_left_mono) simp_all
  finally show ?thesis by simp
qed

subsection \<open>The two pointwise steps of the mesh limit\<close>

lemma sum_pow4_le_max_times_sum:
  fixes d :: "nat \<Rightarrow> real"
  shows "(\<Sum>k<Suc m. (d k)^4)
           \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (\<Sum>k<Suc m. (d k)\<^sup>2)"
proof -
  have fin: "finite ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m})" by simp
  have per: "(d k)^4 \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (d k)\<^sup>2"
    if k: "k \<in> {..<Suc m}" for k
  proof -
    have mem: "(d k)\<^sup>2 \<in> (\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}" using k by auto
    have le: "(d k)\<^sup>2 \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m})"
      by (rule Max_ge[OF fin mem])
    have "(d k)^4 = (d k)\<^sup>2 * (d k)\<^sup>2" by (simp add: sq_times_sq)
    also have "\<dots> \<le> Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (d k)\<^sup>2"
      by (rule mult_right_mono[OF le zero_le_power2])
    finally show ?thesis .
  qed
  have "(\<Sum>k<Suc m. (d k)^4)
          \<le> (\<Sum>k<Suc m. Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (d k)\<^sup>2)"
    by (rule sum_mono[OF per])
  also have "\<dots> = Max ((\<lambda>k. (d k)\<^sup>2) ` {..<Suc m}) * (\<Sum>k<Suc m. (d k)\<^sup>2)"
    by (rule sum_distrib_left[symmetric])
  finally show ?thesis .
qed

lemma prod_le_K_split:
  fixes Wv Sv K B :: real
  assumes W0: "0 \<le> Wv" and WB: "Wv \<le> B" and S0: "0 \<le> Sv" and K: "0 < K"
  shows "Wv * Sv \<le> K * Wv + (B/K) * Sv\<^sup>2"
proof -
  have B0: "0 \<le> B" using W0 WB by linarith
  show ?thesis
  proof (cases "Sv \<le> K")
    case True
    have 1: "Wv * Sv \<le> Wv * K" by (rule mult_left_mono[OF True W0])
    have 2: "Wv * K = K * Wv" by (simp add: mult.commute)
    have 3: "0 \<le> (B/K) * Sv\<^sup>2"
      by (rule mult_nonneg_nonneg[OF divide_nonneg_pos[OF B0 K] zero_le_power2])
    from 1 2 3 show ?thesis by linarith
  next
    case False
    hence KS: "K \<le> Sv" by linarith
    have 1: "Wv * Sv \<le> B * Sv" by (rule mult_right_mono[OF WB S0])
    have "Sv * K \<le> Sv\<^sup>2"
      using mult_left_mono[OF KS S0] by (simp add: power2_eq_square)
    hence "Sv \<le> Sv\<^sup>2 / K" using K by (simp add: pos_le_divide_eq)
    hence 2: "B * Sv \<le> B * (Sv\<^sup>2 / K)" by (rule mult_left_mono[OF _ B0])
    have 3: "B * (Sv\<^sup>2 / K) = (B/K) * Sv\<^sup>2" by simp
    have 4: "0 \<le> K * Wv" using K W0 by (intro mult_nonneg_nonneg) simp_all
    from 1 2 3 4 show ?thesis by linarith
  qed
qed

subsection \<open>The maximal squared increment vanishes in expectation\<close>

text \<open>
  For a bounded process with almost-surely continuous paths on \<open>[s,T]\<close>, the
  expectation of the largest squared increment along the \<open>m\<close>-th uniform
  partition tends to zero. The pointwise limit is uniform continuity on the
  compact; the passage to expectations is dominated convergence with the
  constant dominator \<open>4 R\<^sup>2\<close>. No martingale structure is used.
\<close>

lemma expectation_max_sq_tendsto_zero:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and Xmeas: "\<And>u. 0 \<le> u \<Longrightarrow> X u \<in> borel_measurable M"
    and s0: "0 \<le> s" and sT: "s \<le> T"
    and R: "0 \<le> R"
    and bnd: "\<And>u. 0 \<le> u \<Longrightarrow> AE \<omega> in M. \<bar>X u \<omega>\<bar> \<le> R"
    and cont: "AE \<omega> in M. continuous_on {s..T} (\<lambda>u. X u \<omega>)"
  shows "(\<lambda>m. \<integral>\<omega>. Max ((\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}) \<partial>M) \<longlonglongrightarrow> 0"
proof -
  interpret P: prob_space M by (rule P)
  define W where "W = (\<lambda>m \<omega>. Max ((\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}))"
  have upt_nonneg: "0 \<le> upart s T m k" for m k
    by (rule upart_nonneg[OF s0 sT])
  have upt_mem: "upart s T m k \<in> {s..T}" for m k
    by (rule upart_mem[OF sT])
  have XmM: "X (upart s T m k) \<in> borel_measurable M" for m k
    by (rule Xmeas[OF upt_nonneg])
  have dk_meas: "(\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2)
                   \<in> borel_measurable M" for m k
    using XmM by measurable
  have Wmeas: "W m \<in> borel_measurable M" for m
    unfolding W_def by (intro borel_measurable_Max) (auto intro: dk_meas)
  have Wnn: "0 \<le> W m \<omega>" for m \<omega>
  proof -
    have mem: "(X (upart s T m (Suc 0)) \<omega> - X (upart s T m 0) \<omega>)\<^sup>2
        \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}"
      by (rule imageI) simp
    have "(X (upart s T m (Suc 0)) \<omega> - X (upart s T m 0) \<omega>)\<^sup>2 \<le> W m \<omega>"
      unfolding W_def by (intro Max_ge finite_imageI finite_lessThan mem)    thus ?thesis
      using zero_le_power2[of "X (upart s T m (Suc 0)) \<omega> - X (upart s T m 0) \<omega>"]
      by linarith
  qed
  have bnd_all: "AE \<omega> in M. \<forall>m k. \<bar>X (upart s T m k) \<omega>\<bar> \<le> R"
  proof (subst AE_all_countable, intro allI)
    fix m show "AE \<omega> in M. \<forall>k. \<bar>X (upart s T m k) \<omega>\<bar> \<le> R"
      by (subst AE_all_countable) (intro allI bnd upt_nonneg)
  qed
  have Wbnd: "AE \<omega> in M. \<forall>m. W m \<omega> \<le> 4*R\<^sup>2"
    using bnd_all
  proof eventually_elim
    case (elim \<omega>)
    show "\<forall>m. W m \<omega> \<le> 4*R\<^sup>2"
    proof
      fix m
      show "W m \<omega> \<le> 4*R\<^sup>2"
        unfolding W_def
      proof (subst Max_le_iff)
        show "finite ((\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                            - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m})" by simp
        show "(\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                    - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m} \<noteq> {}" by auto
        show "\<forall>x \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                         - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}. x \<le> 4*R\<^sup>2"
        proof
          fix x assume "x \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                                  - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}"
          then obtain k where xk:
              "x = (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2"
            by auto
          have b1: "\<bar>X (upart s T m (Suc k)) \<omega>\<bar> \<le> R" using elim by blast
          have b2: "\<bar>X (upart s T m k) \<omega>\<bar> \<le> R" using elim by blast
          have tri: "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>
                       \<le> \<bar>X (upart s T m (Suc k)) \<omega>\<bar> + \<bar>X (upart s T m k) \<omega>\<bar>"
            by (rule abs_triangle_ineq4)
          have habs: "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar> \<le> 2*R"
            using tri b1 b2 by linarith
          have "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>\<^sup>2 \<le> (2*R)\<^sup>2"
            by (rule power_mono[OF habs abs_ge_zero])
          hence "x \<le> (2*R)\<^sup>2" using xk by simp
          also have "(2*R)\<^sup>2 = 4*R\<^sup>2" by algebra
          finally show "x \<le> 4*R\<^sup>2" .
        qed
      qed
    qed
  qed
  have Wconv: "AE \<omega> in M. (\<lambda>m. W m \<omega>) \<longlonglongrightarrow> 0"
    using cont
  proof eventually_elim
    case (elim \<omega>)
    show "(\<lambda>m. W m \<omega>) \<longlonglongrightarrow> 0"
      unfolding LIMSEQ_iff
    proof (intro allI impI)
      fix r :: real assume r: "0 < r"
      define e where "e = min 1 r"
      have e0: "0 < e" unfolding e_def using r by simp
      have e1: "e \<le> 1" and er: "e \<le> r" unfolding e_def by simp_all
      have e2r: "e\<^sup>2 \<le> r"
      proof -
        have "e\<^sup>2 \<le> e * 1"
          unfolding power2_eq_square using e0 e1 by (intro mult_left_mono) simp_all
        thus ?thesis using er by simp
      qed
      have uc: "uniformly_continuous_on {s..T} (\<lambda>u. X u \<omega>)"
        by (rule compact_uniformly_continuous[OF elim compact_Icc])
      obtain \<delta> where \<delta>0: "\<delta> > 0"
        and \<delta>prop: "\<And>u v. u \<in> {s..T} \<Longrightarrow> v \<in> {s..T} \<Longrightarrow> dist v u < \<delta>
                       \<Longrightarrow> dist (X v \<omega>) (X u \<omega>) < e"
        using uc e0 unfolding uniformly_continuous_on_def by blast
      obtain N where N: "(T - s)/\<delta> < real N"
        using reals_Archimedean2 by blast
      show "\<exists>no. \<forall>m\<ge>no. norm (W m \<omega> - 0) < r"
      proof (intro exI[of _ N] allI impI)
        fix m assume mN: "N \<le> m"
        have "(T - s)/\<delta> < real (Suc m)" using N mN by simp
        hence "T - s < real (Suc m) * \<delta>"
          using \<delta>0 by (simp add: pos_divide_less_eq)
        hence mesh: "(T - s)/real (Suc m) < \<delta>"
          by (simp add: pos_divide_less_eq mult.commute)
        have Wlt: "W m \<omega> < r"
          unfolding W_def
        proof (subst Max_less_iff)
          show "finite ((\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m})" by simp
          show "(\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                      - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m} \<noteq> {}" by auto
          show "\<forall>x \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                           - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}. x < r"
          proof
            fix x assume "x \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                                    - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}"
            then obtain k where xk:
                "x = (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2"
              by auto
            have d1: "upart s T m (Suc k) - upart s T m k \<le> (T - s)/real (Suc m)"
              by (rule upart_diff_le[OF sT])
            have d2: "0 \<le> upart s T m (Suc k) - upart s T m k"
              using monoD[OF upart_mono[OF sT], of k "Suc k"] by simp
            have du: "dist (X (upart s T m (Suc k)) \<omega>) (X (upart s T m k) \<omega>) < e"
            proof (rule \<delta>prop[OF upt_mem upt_mem])
              show "dist (upart s T m (Suc k)) (upart s T m k) < \<delta>"
                using d1 d2 mesh by (simp add: dist_real_def)
            qed
            have dabs: "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar> < e"
              using du by (simp add: dist_real_def)
            have "x = \<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>\<^sup>2"
              using xk by simp
            also have "\<dots> < e\<^sup>2"
              by (rule power_strict_mono[OF dabs abs_ge_zero]) simp
            also have "e\<^sup>2 \<le> r" by (rule e2r)
            finally show "x < r" .
          qed
        qed
        show "norm (W m \<omega> - 0) < r" using Wlt Wnn[of m \<omega>] by simp
      qed
    qed
  qed
  have "(\<lambda>m. \<integral>\<omega>. W m \<omega> \<partial>M) \<longlonglongrightarrow> (\<integral>\<omega>. (0::real) \<partial>M)"
  proof (rule integral_dominated_convergence[where w = "\<lambda>_. 4*R\<^sup>2"])
    show "(\<lambda>\<omega>. (0::real)) \<in> borel_measurable M" by simp
    show "\<And>m. W m \<in> borel_measurable M" by (rule Wmeas)
    show "integrable M (\<lambda>_. 4*R\<^sup>2)" by (rule P.integrable_const)
    show "AE \<omega> in M. (\<lambda>m. W m \<omega>) \<longlonglongrightarrow> 0" by (rule Wconv)
    show "AE \<omega> in M. norm (W m \<omega>) \<le> 4*R\<^sup>2" for m
      using Wbnd by eventually_elim (simp add: Wnn)
  qed
  thus ?thesis unfolding W_def by simp
qed

subsection \<open>Fourth moments are free for a bounded process\<close>

lemma integrable_pow4_of_bounded:
  fixes f :: "'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and fm[measurable]: "f \<in> borel_measurable M"
    and R: "0 \<le> R"
    and b: "AE \<omega> in M. \<bar>f \<omega>\<bar> \<le> R"
  shows "integrable M (\<lambda>\<omega>. (f \<omega>)^4)"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>_. R^4"])
  interpret P: prob_space M by (rule P)
  show "integrable M (\<lambda>_. R^4)" by (rule P.integrable_const)
  show "(\<lambda>\<omega>. (f \<omega>)^4) \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. norm ((f \<omega>)^4) \<le> norm (R^4)"
    using b
  proof eventually_elim
    case (elim \<omega>)
    have le4: "\<bar>f \<omega>\<bar>^4 \<le> R^4" by (rule power_mono[OF elim abs_ge_zero])
    have e1: "\<bar>f \<omega>\<bar>^4 = (\<bar>f \<omega>\<bar>\<^sup>2)\<^sup>2" by algebra
    have e2: "(\<bar>f \<omega>\<bar>\<^sup>2)\<^sup>2 = ((f \<omega>)\<^sup>2)\<^sup>2" by simp
    have e3: "((f \<omega>)\<^sup>2)\<^sup>2 = (f \<omega>)^4" by algebra
    have le: "(f \<omega>)^4 \<le> R^4" using le4 e1 e2 e3 by linarith
    have nn: "0 \<le> (f \<omega>)^4" by (rule pow4_nonneg)
    have nn2: "0 \<le> R^4" using R by simp
    show ?case using le nn nn2 by simp
  qed
qed


subsection \<open>The remainder vanishes along the uniform partitions\<close>

text \<open>
  The hypotheses package the setting of \<^cite>\<open>LaiShkolnikovSoner\<close>: a global compensator @{term A}
  with rate at most @{term C} (in the application, \<open>A u = \<integral> trace (acov)\<close>
  over \<open>[0,u]\<close>), the conditional covariation identity per pair of times,
  boundedness by @{term R}, and almost-surely continuous paths on \<open>[s,T]\<close>.
  Fourth-moment integrability is not assumed -- it follows from boundedness.
\<close>

theorem remainder_tendsto_zero:
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
  shows "(\<lambda>m. \<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)^4 \<partial>M)) \<longlonglongrightarrow> 0"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule borel_measurable_integrable[OF MX.integrable[OF that]])
  have upt_nn: "0 \<le> upart s T m k" for m k by (rule upart_nonneg[OF s0 sT])
  have upt_mono: "mono (upart s T m)" for m by (rule upart_mono[OF sT])
  have upt_le: "upart s T m k \<le> upart s T m (Suc k)" for m k
    by (rule monoD[OF upt_mono]) simp
  have XmM[measurable]: "X (upart s T m k) \<in> borel_measurable M" for m k
    by (rule Xmeas[OF upt_nn])
  have q4: "integrable M (\<lambda>\<omega>. (X u \<omega>)^4)" if "0 \<le> u" for u
    by (rule integrable_pow4_of_bounded[OF P Xmeas[OF that] R bnd[OF that]])
  have dAint: "integrable M (\<lambda>\<omega>. A (upart s T m (Suc k)) \<omega>
                                - A (upart s T m k) \<omega>)" for m k
    by (intro Bochner_Integration.integrable_diff A_int upt_nn)
  have dAbnd: "AE \<omega> in M. 0 \<le> A (upart s T m (Suc k)) \<omega> - A (upart s T m k) \<omega>
                 \<and> A (upart s T m (Suc k)) \<omega> - A (upart s T m k) \<omega>
                   \<le> C * (upart s T m (Suc k) - upart s T m k)" for m k
    using A_rate
  proof eventually_elim
    case (elim \<omega>)
    show ?case using elim upt_nn[of m k] upt_le[of m k] by blast
  qed
  have covm: "AE \<omega> in M. cond_exp M (F (upart s T m k))
                 (\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2) \<omega>
               = cond_exp M (F (upart s T m k))
                 (\<lambda>\<omega>. A (upart s T m (Suc k)) \<omega> - A (upart s T m k) \<omega>) \<omega>" for m k
    by (rule covA[OF upt_nn upt_le])
  have bndm: "AE \<omega> in M. \<bar>X (upart s T m k) \<omega>\<bar> \<le> R" for m k
    by (rule bnd[OF upt_nn])

  define B where "B = 4*R\<^sup>2*C*(T - s) + C\<^sup>2*(T - s)\<^sup>2"
  have B0: "0 \<le> B"
  proof -
    have "0 \<le> 4*R\<^sup>2*C*(T - s)" using C sT by (intro mult_nonneg_nonneg) simp_all
    moreover have "0 \<le> C\<^sup>2*(T - s)\<^sup>2" by (intro mult_nonneg_nonneg zero_le_power2)
    ultimately show ?thesis unfolding B_def by linarith
  qed
  have SSB: "(\<integral>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M) \<le> B" for m
  proof -
    have "(\<integral>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                            - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
            \<le> 4*R\<^sup>2*C*(upart s T m (Suc m) - upart s T m 0)
              + C\<^sup>2*(upart s T m (Suc m) - upart s T m 0)\<^sup>2"
      by (rule sum_sq_squared_bound[of M _ X "upart s T m", OF P X upt_nn upt_mono q4 dAint dAbnd
            covm C R bndm])
    also have "\<dots> = B" unfolding B_def by (simp add: upart_top)
    finally show ?thesis .
  qed

  have iY4: "integrable M (\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)^4)" for m k
    by (rule integrable_pow4_diff[OF q4[OF upt_nn] q4[OF upt_nn] XmM XmM])
  have dmeas: "(\<lambda>\<omega>. X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)
                 \<in> borel_measurable M" for m k
    by measurable
  have dk2meas: "(\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2)
                   \<in> borel_measurable M" for m k
    by measurable
  have iY2: "integrable M (\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)\<^sup>2)" for m k
    by (rule integrable_sq_of_pow4[OF P iY4 dmeas])
  have iS: "integrable M (\<lambda>\<omega>. \<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                         - X (upart s T m k) \<omega>)\<^sup>2)" for m
    by (intro Bochner_Integration.integrable_sum iY2)
  have iSd4: "integrable M (\<lambda>\<omega>. \<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                           - X (upart s T m k) \<omega>)^4)" for m
    by (intro Bochner_Integration.integrable_sum iY4)
  have Smeas: "(\<lambda>\<omega>. \<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)\<^sup>2) \<in> borel_measurable M" for m
    by measurable
  have Snn: "0 \<le> (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)\<^sup>2)" for m \<omega>
    by (intro sum_nonneg) simp
  have ipair: "integrable M (\<lambda>\<omega>. (X (upart s T m (Suc j)) \<omega>
                                 - X (upart s T m j) \<omega>)\<^sup>2
                                * (X (upart s T m (Suc k)) \<omega>
                                   - X (upart s T m k) \<omega>)\<^sup>2)" for m j k
    by (rule integrable_prod_sq_sq[OF iY4 iY4 dmeas dmeas])
  have pw: "(\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                        - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2
      = (\<Sum>j<Suc m. \<Sum>k<Suc m. (X (upart s T m (Suc j)) \<omega>
                               - X (upart s T m j) \<omega>)\<^sup>2
                              * (X (upart s T m (Suc k)) \<omega>
                                 - X (upart s T m k) \<omega>)\<^sup>2)" for m \<omega>
    by (simp only: power2_eq_square sum_product)
  have iS2: "integrable M (\<lambda>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                           - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2)" for m
  proof -
    have "integrable M (\<lambda>\<omega>. \<Sum>j<Suc m. \<Sum>k<Suc m.
            (X (upart s T m (Suc j)) \<omega> - X (upart s T m j) \<omega>)\<^sup>2
            * (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2)"
      by (intro Bochner_Integration.integrable_sum ipair)
    thus ?thesis unfolding pw .
  qed

  define W where "W = (\<lambda>m \<omega>. Max ((\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}))"
  have Wmeas: "W m \<in> borel_measurable M" for m
    unfolding W_def by (intro borel_measurable_Max) (auto intro: dk2meas)
  have Wnn: "0 \<le> W m \<omega>" for m \<omega>
  proof -
    have mem: "(X (upart s T m (Suc 0)) \<omega> - X (upart s T m 0) \<omega>)\<^sup>2
        \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}"
      by (rule imageI) simp
    have "(X (upart s T m (Suc 0)) \<omega> - X (upart s T m 0) \<omega>)\<^sup>2 \<le> W m \<omega>"
      unfolding W_def by (intro Max_ge finite_imageI finite_lessThan mem)
    thus ?thesis
      using zero_le_power2[of "X (upart s T m (Suc 0)) \<omega> - X (upart s T m 0) \<omega>"]
      by linarith
  qed
  have Wub: "AE \<omega> in M. W m \<omega> \<le> 4*R\<^sup>2" for m
  proof -
    have allk: "AE \<omega> in M. \<forall>k. \<bar>X (upart s T m k) \<omega>\<bar> \<le> R"
      by (subst AE_all_countable) (intro allI bndm)
    show ?thesis using allk
    proof eventually_elim
      case (elim \<omega>)
      show "W m \<omega> \<le> 4*R\<^sup>2"
        unfolding W_def
      proof (subst Max_le_iff)
        show "finite ((\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                            - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m})" by simp
        show "(\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                    - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m} \<noteq> {}" by auto
        show "\<forall>x \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                         - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}. x \<le> 4*R\<^sup>2"
        proof
          fix x assume "x \<in> (\<lambda>k. (X (upart s T m (Suc k)) \<omega>
                                  - X (upart s T m k) \<omega>)\<^sup>2) ` {..<Suc m}"
          then obtain k where xk:
              "x = (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2"
            by auto
          have b1: "\<bar>X (upart s T m (Suc k)) \<omega>\<bar> \<le> R" using elim by blast
          have b2: "\<bar>X (upart s T m k) \<omega>\<bar> \<le> R" using elim by blast
          have tri: "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>
                       \<le> \<bar>X (upart s T m (Suc k)) \<omega>\<bar> + \<bar>X (upart s T m k) \<omega>\<bar>"
            by (rule abs_triangle_ineq4)
          have habs: "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar> \<le> 2*R"
            using tri b1 b2 by linarith
          have "\<bar>X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>\<bar>\<^sup>2 \<le> (2*R)\<^sup>2"
            by (rule power_mono[OF habs abs_ge_zero])
          hence "x \<le> (2*R)\<^sup>2" using xk by simp
          also have "(2*R)\<^sup>2 = 4*R\<^sup>2" by algebra
          finally show "x \<le> 4*R\<^sup>2" .
        qed
      qed
    qed
  qed
  have iW: "integrable M (W m)" for m
  proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>_. 4*R\<^sup>2"])
    show "integrable M (\<lambda>_. 4*R\<^sup>2)" by (rule P.integrable_const)
    show "W m \<in> borel_measurable M" by (rule Wmeas)
    show "AE \<omega> in M. norm (W m \<omega>) \<le> norm (4*R\<^sup>2)"
      using Wub[of m] by eventually_elim (simp add: Wnn)
  qed
  have iWS: "integrable M (\<lambda>\<omega>. W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                       - X (upart s T m k) \<omega>)\<^sup>2))" for m
  proof (rule Bochner_Integration.integrable_bound
           [of _ "\<lambda>\<omega>. 4*R\<^sup>2 * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                          - X (upart s T m k) \<omega>)\<^sup>2)"])
    show "integrable M (\<lambda>\<omega>. 4*R\<^sup>2 * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                               - X (upart s T m k) \<omega>)\<^sup>2))"
      using iS by simp
    show "(\<lambda>\<omega>. W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                    - X (upart s T m k) \<omega>)\<^sup>2))
            \<in> borel_measurable M"
      by (intro borel_measurable_times Wmeas Smeas)
    show "AE \<omega> in M. norm (W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                    - X (upart s T m k) \<omega>)\<^sup>2))
            \<le> norm (4*R\<^sup>2 * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2))"
      using Wub[of m]
    proof eventually_elim
      case (elim \<omega>)
      have le: "W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                    - X (upart s T m k) \<omega>)\<^sup>2)
                  \<le> 4*R\<^sup>2 * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2)"
        by (rule mult_right_mono[OF elim Snn])
      have nn: "0 \<le> W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2)"
        by (rule mult_nonneg_nonneg[OF Wnn Snn])
      have nn2: "0 \<le> 4*R\<^sup>2 * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2)"
        by (intro mult_nonneg_nonneg Snn) simp_all
      show ?case using le nn nn2 by simp
    qed
  qed

  have keybound: "(\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                                   - X (upart s T m k) \<omega>)^4 \<partial>M))
        \<le> K * (\<integral>\<omega>. W m \<omega> \<partial>M) + (4*R\<^sup>2/K) * B" if K0: "0 < K" for m K
  proof -
    have e1: "(\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)^4 \<partial>M))
        = (\<integral>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                            - X (upart s T m k) \<omega>)^4) \<partial>M)"
      by (rule Bochner_Integration.integral_sum[OF iY4, symmetric])
    have e2: "(\<integral>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                               - X (upart s T m k) \<omega>)^4) \<partial>M)
        \<le> (\<integral>\<omega>. W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                     - X (upart s T m k) \<omega>)\<^sup>2) \<partial>M)"
    proof (rule integral_mono[OF iSd4 iWS])
      fix \<omega>
      show "(\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                        - X (upart s T m k) \<omega>)^4)
              \<le> W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                     - X (upart s T m k) \<omega>)\<^sup>2)"
        unfolding W_def by (rule sum_pow4_le_max_times_sum)
    qed
    have e3: "(\<integral>\<omega>. W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                        - X (upart s T m k) \<omega>)\<^sup>2) \<partial>M)
        \<le> (\<integral>\<omega>. K * W m \<omega>
               + (4*R\<^sup>2/K) * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                         - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)"
    proof (rule integral_mono_AE)
      show "integrable M (\<lambda>\<omega>. W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                       - X (upart s T m k) \<omega>)\<^sup>2))"
        by (rule iWS)
      show "integrable M (\<lambda>\<omega>. K * W m \<omega>
               + (4*R\<^sup>2/K) * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                         - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2)"
        using iW[of m] iS2[of m] by simp
      show "AE \<omega> in M. W m \<omega> * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                            - X (upart s T m k) \<omega>)\<^sup>2)
              \<le> K * W m \<omega>
                + (4*R\<^sup>2/K) * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                          - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2"
        using Wub[of m]
      proof eventually_elim
        case (elim \<omega>)
        show ?case by (rule prod_le_K_split[OF Wnn elim Snn K0])
      qed
    qed
    have e4: "(\<integral>\<omega>. K * W m \<omega>
               + (4*R\<^sup>2/K) * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                         - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
        = K * (\<integral>\<omega>. W m \<omega> \<partial>M)
          + (4*R\<^sup>2/K) * (\<integral>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                          - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)"
    proof -
      have iKW: "integrable M (\<lambda>\<omega>. K * W m \<omega>)" using iW by simp
      have iBS: "integrable M (\<lambda>\<omega>. (4*R\<^sup>2/K)
                   * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                 - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2)"
        using iS2 by simp
      have "(\<integral>\<omega>. K * W m \<omega>
               + (4*R\<^sup>2/K) * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                         - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. K * W m \<omega> \<partial>M)
            + (\<integral>\<omega>. (4*R\<^sup>2/K) * (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                           - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)"
        by (rule Bochner_Integration.integral_add[OF iKW iBS])
      thus ?thesis by simp
    qed
    have e5: "(4*R\<^sup>2/K) * (\<integral>\<omega>. (\<Sum>k<Suc m. (X (upart s T m (Suc k)) \<omega>
                                          - X (upart s T m k) \<omega>)\<^sup>2)\<^sup>2 \<partial>M)
        \<le> (4*R\<^sup>2/K) * B"
    proof (rule mult_left_mono[OF SSB])
      show "0 \<le> 4*R\<^sup>2/K" using K0 by (intro divide_nonneg_pos) simp_all
    qed
    from e1 e2 e3 e4 e5 show ?thesis by linarith
  qed

  have W3: "(\<lambda>m. \<integral>\<omega>. W m \<omega> \<partial>M) \<longlonglongrightarrow> 0"
    unfolding W_def
    by (rule expectation_max_sq_tendsto_zero[OF P Xmeas s0 sT R bnd cont])
  have EWnn: "0 \<le> (\<integral>\<omega>. W m \<omega> \<partial>M)" for m
    by (simp add: Wnn)
  have int4nn: "0 \<le> (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                          - X (upart s T m k) \<omega>)^4 \<partial>M)" for m k
    by (simp add: pow4_nonneg)
  have E4nn: "0 \<le> (\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                                   - X (upart s T m k) \<omega>)^4 \<partial>M))" for m
    by (intro sum_nonneg int4nn)
  show ?thesis
    unfolding LIMSEQ_iff
  proof (intro allI impI)
    fix r :: real assume r: "0 < r"
    define K where "K = (8*R\<^sup>2*B + r)/r"
    have num0: "0 \<le> 8*R\<^sup>2*B" using B0 by (intro mult_nonneg_nonneg) simp_all
    have K0: "0 < K" unfolding K_def using r num0
      by (intro divide_pos_pos) linarith+
    have Keq: "(r/2)*K = 4*R\<^sup>2*B + r/2"
      unfolding K_def using r by (simp add: field_simps)
    have keyB: "(4*R\<^sup>2*B)/K \<le> r/2"
    proof -
      have "4*R\<^sup>2*B \<le> (r/2)*K" using Keq r by linarith
      thus ?thesis using K0 by (simp add: pos_divide_le_eq)
    qed
    have rK0: "0 < r/(2*K)" using r K0 by (intro divide_pos_pos) simp_all
    obtain N where N: "\<forall>m\<ge>N. norm ((\<integral>\<omega>. W m \<omega> \<partial>M) - 0) < r/(2*K)"
      using W3[unfolded LIMSEQ_iff, rule_format, OF rK0] by blast
    show "\<exists>no. \<forall>m\<ge>no. norm ((\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                                             - X (upart s T m k) \<omega>)^4 \<partial>M)) - 0) < r"
    proof (intro exI[of _ N] allI impI)
      fix m assume mN: "N \<le> m"
      have EW: "(\<integral>\<omega>. W m \<omega> \<partial>M) < r/(2*K)"
        using N mN EWnn[of m] by auto
      have t1: "K * (\<integral>\<omega>. W m \<omega> \<partial>M) < K * (r/(2*K))"
        by (rule mult_strict_left_mono[OF EW K0])
      have t2: "K * (r/(2*K)) = r/2" using K0 by (simp add: field_simps)
      have t3: "(4*R\<^sup>2/K) * B = (4*R\<^sup>2*B)/K" by simp
      have lt: "(\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                                 - X (upart s T m k) \<omega>)^4 \<partial>M)) < r"
        using keybound[OF K0, of m] t1 t2 t3 keyB by linarith
      show "norm ((\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                                   - X (upart s T m k) \<omega>)^4 \<partial>M)) - 0) < r"
        using lt E4nn[of m] by simp
    qed
  qed
qed

subsection \<open>Eq. (2.7) for bounded continuous martingales\<close>

text \<open>
  The fourth-moment bound of Eq. (2.7) of \<^cite>\<open>LaiShkolnikovSoner\<close>, for a martingale
  that is bounded and has almost-surely continuous paths on \<open>[s,T]\<close>, with
  covariation compensator of rate at most @{term C}. The constant is \<open>8 C\<^sup>2\<close>,
  against the \<open>66 C\<^sup>2\<close> obtained through the Burkholder-Davis-Gundy
  inequality; no BDG and no stochastic integral is used anywhere in the proof.
\<close>

theorem fourth_moment_bound_bounded:
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
  shows "(\<integral>\<omega>. (X T \<omega> - X s \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(T - s)\<^sup>2"
proof -
  interpret P: prob_space M by (rule P)
  interpret MX: martingale M F "0::real" X by (rule X)
  have Xmeas: "X u \<in> borel_measurable M" if "0 \<le> u" for u
    by (rule borel_measurable_integrable[OF MX.integrable[OF that]])
  have upt_nn: "0 \<le> upart s T m k" for m k by (rule upart_nonneg[OF s0 sT])
  have upt_mono: "mono (upart s T m)" for m by (rule upart_mono[OF sT])
  have upt_le: "upart s T m k \<le> upart s T m (Suc k)" for m k
    by (rule monoD[OF upt_mono]) simp
  have XmM[measurable]: "X (upart s T m k) \<in> borel_measurable M" for m k
    by (rule Xmeas[OF upt_nn])
  have q4: "integrable M (\<lambda>\<omega>. (X u \<omega>)^4)" if "0 \<le> u" for u
    by (rule integrable_pow4_of_bounded[OF P Xmeas[OF that] R bnd[OF that]])
  have dAint: "integrable M (\<lambda>\<omega>. A (upart s T m (Suc k)) \<omega>
                                - A (upart s T m k) \<omega>)" for m k
    by (intro Bochner_Integration.integrable_diff A_int upt_nn)
  have dAbnd: "AE \<omega> in M. 0 \<le> A (upart s T m (Suc k)) \<omega> - A (upart s T m k) \<omega>
                 \<and> A (upart s T m (Suc k)) \<omega> - A (upart s T m k) \<omega>
                   \<le> C * (upart s T m (Suc k) - upart s T m k)" for m k
    using A_rate
  proof eventually_elim
    case (elim \<omega>)
    show ?case using elim upt_nn[of m k] upt_le[of m k] by blast
  qed
  have covm: "AE \<omega> in M. cond_exp M (F (upart s T m k))
                 (\<lambda>\<omega>. (X (upart s T m (Suc k)) \<omega> - X (upart s T m k) \<omega>)\<^sup>2) \<omega>
               = cond_exp M (F (upart s T m k))
                 (\<lambda>\<omega>. A (upart s T m (Suc k)) \<omega> - A (upart s T m k) \<omega>) \<omega>" for m k
    by (rule covA[OF upt_nn upt_le])

  have per: "(\<integral>\<omega>. (X T \<omega> - X s \<omega>)^4 \<partial>M)
       \<le> 8*C\<^sup>2*(T - s)\<^sup>2
         + 3*(\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)^4 \<partial>M))" for m
  proof -
    have "(\<integral>\<omega>. (X (upart s T m (Suc m)) \<omega> - X (upart s T m 0) \<omega>)^4 \<partial>M)
       \<le> 8*C\<^sup>2*(upart s T m (Suc m) - upart s T m 0)\<^sup>2
         + 3*(\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)^4 \<partial>M))"
      by (rule fourth_moment_partition_bound[of M _ X "upart s T m", OF P X upt_nn upt_mono q4 dAint
            dAbnd covm C])
    thus ?thesis by (simp add: upart_top)
  qed
  have lim: "(\<lambda>m. 8*C\<^sup>2*(T - s)\<^sup>2
         + 3*(\<Sum>k<Suc m. (\<integral>\<omega>. (X (upart s T m (Suc k)) \<omega>
                              - X (upart s T m k) \<omega>)^4 \<partial>M)))
       \<longlonglongrightarrow> 8*C\<^sup>2*(T - s)\<^sup>2 + 3*0"
    by (intro tendsto_add tendsto_const tendsto_mult_left
              remainder_tendsto_zero[OF P X s0 sT A_int A_rate covA C R bnd cont])
  have "(\<integral>\<omega>. (X T \<omega> - X s \<omega>)^4 \<partial>M) \<le> 8*C\<^sup>2*(T - s)\<^sup>2 + 3*0"
  proof (rule LIMSEQ_le_const[OF lim])
    show "\<exists>N. \<forall>n\<ge>N. (\<integral>\<omega>. (X T \<omega> - X s \<omega>)^4 \<partial>M)
            \<le> 8*C\<^sup>2*(T - s)\<^sup>2
              + 3*(\<Sum>k<Suc n. (\<integral>\<omega>. (X (upart s T n (Suc k)) \<omega>
                                   - X (upart s T n k) \<omega>)^4 \<partial>M))"
      using per by blast
  qed
  thus ?thesis by simp
qed


section \<open>Uniform integrability of the squared increments\<close>

text \<open>The closedness half of Lemma 2.3 needs to pass the covariation
  constraint's linear inequalities

    \<open>E[(X\<^sub>t - X\<^sub>s)\<^sup>T M (X\<^sub>t - X\<^sub>s) g] \<le> (t-s) h\<^sub>S(M) E[g]\<close>

  to weak limits, avoiding a Skorokhod representation. Quantifying only
  over \<open>M \<succeq> 0\<close> does not work: the set \<open>{a : tr(M a) \<le> h\<^sub>S(M) \<forall> M \<succeq> 0}\<close> is
  the downward closure of \<open>S\<close> in the psd order, whereas \<open>S\<close> carries lower
  bounds (\<open>\<Pi>\<^sub>m(a) \<ge> m-k\<close>) and is not downward closed. Weak convergence
  alone gives only the Fatou direction \<open>liminf \<ge> lim\<close>, which runs the
  wrong way for the lower constraints.

  Uniform integrability supplies what is needed: the fourth-moment bound
  of Eq. (2.7) (\<open>fourth_moment_bound_bounded\<close>, free of Ito and BDG)
  controls the tail of the squared increment uniformly over the family,
  the hypothesis \<open>unif_integrable\<close> of \<open>Vitali_Convergence.vitali_convergence\<close>.

  The estimate is pointwise and elementary: on \<open>{Z\<^sup>2 > R}\<close>,
  \<open>Z\<^sup>2 = Z\<^sup>4/Z\<^sup>2 < Z\<^sup>4/R\<close>, and off that set the left side vanishes.\<close>

lemma sq_tail_le_fourth_moment_pointwise:
  fixes z R :: real
  assumes R: "0 < R"
  shows "z\<^sup>2 * indicat_real {w. R < w\<^sup>2} z \<le> z^4 / R"
proof (cases "R < z\<^sup>2")
  case True
  have z2: "0 < z\<^sup>2" using True R by linarith
  have "z\<^sup>2 * R \<le> z\<^sup>2 * z\<^sup>2"
    by (rule mult_left_mono) (use True z2 in linarith)+
  also have "z\<^sup>2 * z\<^sup>2 = z^4" by (simp add: power2_eq_square power4_eq_xxxx)
  finally have "z\<^sup>2 * R \<le> z^4" .
  then have "z\<^sup>2 \<le> z^4 / R" using R by (simp add: field_simps)
  then show ?thesis using True by simp
next
  case False
  have "0 \<le> z^4 / R" using R by simp
  then show ?thesis using False by simp
qed

lemma sq_tail_bound_of_fourth_moment:
  fixes Z :: "'a \<Rightarrow> real"
  assumes M: "finite_measure M"
    and i4: "integrable M (\<lambda>\<omega>. (Z \<omega>)^4)"
    and i2: "integrable M (\<lambda>\<omega>. (Z \<omega>)\<^sup>2 * indicat_real {w. R < w\<^sup>2} (Z \<omega>))"
    and B: "(\<integral>\<omega>. (Z \<omega>)^4 \<partial>M) \<le> B"
    and R: "0 < R"
  shows "(\<integral>\<omega>. (Z \<omega>)\<^sup>2 * indicat_real {w. R < w\<^sup>2} (Z \<omega>) \<partial>M) \<le> B / R"
proof -
  have ptw: "(Z \<omega>)\<^sup>2 * indicat_real {w. R < w\<^sup>2} (Z \<omega>) \<le> (Z \<omega>)^4 / R" for \<omega>
    by (rule sq_tail_le_fourth_moment_pointwise[OF R])
  have idiv: "integrable M (\<lambda>\<omega>. (Z \<omega>)^4 / R)"
    by (rule integrable_divide_zero[OF i4])
  have "(\<integral>\<omega>. (Z \<omega>)\<^sup>2 * indicat_real {w. R < w\<^sup>2} (Z \<omega>) \<partial>M)
      \<le> (\<integral>\<omega>. (Z \<omega>)^4 / R \<partial>M)"
    by (rule integral_mono[OF i2 idiv]) (rule ptw)
  also have "(\<integral>\<omega>. (Z \<omega>)^4 / R \<partial>M) = (\<integral>\<omega>. (Z \<omega>)^4 \<partial>M) / R"
    by simp
  also have "\<dots> \<le> B / R"
    by (rule divide_right_mono[OF B]) (use R in linarith)
  finally show ?thesis .
qed


subsection \<open>Truncation: the other half of the \<open>3\<epsilon>\<close> argument\<close>

text \<open>Weak convergence upgrades to convergence of unbounded continuous
  integrals \<open>\<integral>f dP\<^sub>m \<rightarrow> \<integral>f dP\<close> when \<open>f\<close> has uniformly integrable tails:
  truncate \<open>f\<close> at height \<open>R\<close> --- bounded and continuous, so weak
  convergence applies directly --- and control the two truncation errors
  by the tail bound above.

  The error estimate: pointwise the clamped function differs from \<open>f\<close>
  only where \<open>|f| > R\<close>, and there by at most \<open>|f|\<close> itself, so the error
  is dominated by the tail integral that \<open>sq_tail_bound_of_fourth_moment\<close>
  bounds.\<close>

text \<open>The abstract shape of the \<open>3\<epsilon>\<close> argument, with the measure theory
  removed: a sequence uniformly within \<open>e\<close> of some convergent sequence,
  whose limit is itself within \<open>e\<close> of \<open>z\<close> for every \<open>e\<close>, converges to
  \<open>z\<close> -- what truncating the integrand at height \<open>R\<close> and bounding the two
  errors via \<open>sq_tail_bound_of_fourth_moment\<close> leaves to prove.

  The margin is \<open>e = \<epsilon>/4\<close> rather than \<open>\<epsilon>/3\<close> so the three terms sum to
  \<open>3\<epsilon>/4 < \<epsilon>\<close> strictly, as \<open>LIMSEQ_I\<close> wants.\<close>

lemma tendsto_real_of_approximants:
  fixes x :: "nat \<Rightarrow> real" and z :: real
  assumes approx: "\<And>e. 0 < e \<Longrightarrow>
      \<exists>y w. (\<forall>m. \<bar>x m - y m\<bar> \<le> e) \<and> (y \<longlonglongrightarrow> w) \<and> \<bar>w - z\<bar> \<le> e"
  shows "x \<longlonglongrightarrow> z"
proof (rule LIMSEQ_I)
  fix r :: real assume r: "0 < r"
  have q: "0 < r/4" using r by simp
  obtain y w where near: "\<And>m. \<bar>x m - y m\<bar> \<le> r/4"
    and lim: "y \<longlonglongrightarrow> w" and wz: "\<bar>w - z\<bar> \<le> r/4"
    using approx[OF q] by blast
  obtain no where no: "\<And>m. no \<le> m \<Longrightarrow> norm (y m - w) < r/4"
    using LIMSEQ_D[OF lim q] by blast
  have "norm (x m - z) < r" if m: "no \<le> m" for m
  proof -
    have "\<bar>x m - z\<bar> \<le> \<bar>x m - y m\<bar> + \<bar>y m - w\<bar> + \<bar>w - z\<bar>" by simp
    moreover have "\<bar>y m - w\<bar> < r/4" using no[OF m] by simp
    ultimately have "\<bar>x m - z\<bar> < r/4 + r/4 + r/4"
      using near[of m] wz by linarith
    moreover have "r/4 + r/4 + r/4 < r" using r by simp
    ultimately show ?thesis by simp
  qed
  then show "\<exists>no. \<forall>m\<ge>no. norm (x m - z) < r" by blast
qed

lemma clamp_diff_le_tail_pointwise:
  fixes z R :: real
  assumes Rnn: "0 \<le> R"
  shows "\<bar>z - max (- R) (min R z)\<bar> \<le> \<bar>z\<bar> * indicat_real {w. R < \<bar>w\<bar>} z"
proof (cases "R < \<bar>z\<bar>")
  case False
  then have zR: "\<bar>z\<bar> \<le> R" by linarith
  then have "min R z = z" by (simp add: abs_le_iff)
  moreover have "max (- R) z = z" using zR by (simp add: abs_le_iff)
  ultimately show ?thesis by simp
next
  case True
  have ind: "indicat_real {w. R < \<bar>w\<bar>} z = 1" using True by simp
  show ?thesis
  proof (cases "0 \<le> z")
    case True
    then have zgt: "R < z" using \<open>R < \<bar>z\<bar>\<close> by simp
    have "min R z = R" using zgt by simp
    moreover have "max (- R) R = R" using Rnn by simp
    ultimately have "max (- R) (min R z) = R" by simp
    then show ?thesis unfolding ind using zgt True Rnn by simp
  next
    case False
    then have zlt: "z < - R" using \<open>R < \<bar>z\<bar>\<close> by simp
    have zleR: "z \<le> R" using zlt Rnn by linarith
    have "min R z = z" by (rule min_absorb2[OF zleR])
    moreover have "max (- R) z = - R" using zlt by simp
    ultimately have "max (- R) (min R z) = - R" by simp
    then show ?thesis unfolding ind using zlt False Rnn by simp
  qed
qed

lemma clamp_integral_error:
  fixes f :: "'a \<Rightarrow> real"
  assumes M: "finite_measure M"
    and R: "0 \<le> R"
    and iF: "integrable M f"
    and iC: "integrable M (\<lambda>\<omega>. max (- R) (min R (f \<omega>)))"
    and iT: "integrable M (\<lambda>\<omega>. \<bar>f \<omega>\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f \<omega>))"
  shows "\<bar>(\<integral>\<omega>. f \<omega> \<partial>M) - (\<integral>\<omega>. max (- R) (min R (f \<omega>)) \<partial>M)\<bar>
      \<le> (\<integral>\<omega>. \<bar>f \<omega>\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f \<omega>) \<partial>M)"
proof -
  have diff: "(\<integral>\<omega>. f \<omega> \<partial>M) - (\<integral>\<omega>. max (- R) (min R (f \<omega>)) \<partial>M)
      = (\<integral>\<omega>. f \<omega> - max (- R) (min R (f \<omega>)) \<partial>M)"
    by (rule Bochner_Integration.integral_diff[symmetric, OF iF iC])
  have idiff: "integrable M (\<lambda>\<omega>. f \<omega> - max (- R) (min R (f \<omega>)))"
    by (rule Bochner_Integration.integrable_diff[OF iF iC])
  have "\<bar>(\<integral>\<omega>. f \<omega> - max (- R) (min R (f \<omega>)) \<partial>M)\<bar>
      \<le> (\<integral>\<omega>. \<bar>f \<omega> - max (- R) (min R (f \<omega>))\<bar> \<partial>M)"
    by (rule integral_abs_bound)
  also have "\<dots> \<le> (\<integral>\<omega>. \<bar>f \<omega>\<bar> * indicat_real {w. R < \<bar>w\<bar>} (f \<omega>) \<partial>M)"
    by (rule integral_mono[OF integrable_abs[OF idiff] iT])
       (rule clamp_diff_le_tail_pointwise[OF R])
  finally show ?thesis unfolding diff .
qed


(*<*)
end
(*>*)
