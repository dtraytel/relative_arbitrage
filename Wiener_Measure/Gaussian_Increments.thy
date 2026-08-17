

(*<*)
theory Gaussian_Increments
  imports Sorted_Lists
begin

(*>*)

text \<open>
  Construction of Brownian motion in Isabelle/HOL.

    Strategy (maximal reuse):
    \<^item> finite-dimensional distributions are pushforwards of finite products of
      independent Gaussian increment measures under cumulative-sum maps;
    \<^item> projectivity reduces to merging two adjacent increments, i.e. to the
      convolution law for Gaussians (HOL-Probability's
      \<open>conv_normal_density_zero_mean\<close>);
    \<^item> the projective limit is Immler's Daniell--Kolmogorov theorem
      (HOL-Probability, locale \<open>polish_projective\<close>);
    \<^item> the continuous modification comes from the AFP entry
      \<open>Kolmogorov_Chentsov\<close> (theorem \<open>Kolmogorov_Chentsov\<close>), whose moment
      hypothesis is discharged by the Gaussian fourth moment
      \<open>E \<bar>B t - B s\<bar>\<^sup>4 = 3 * \<bar>t - s\<bar>\<^sup>2\<close>
      (HOL-Probability's \<open>normal_moment_even\<close>).

    This part provides the Gaussian increment measure \<open>gauss_measure\<close>,
    parameterized by its variance (variance 0 degenerating to a point
    mass), its moments, and the convolution law both in pushforward and in
    iterated-integral form.\<close>
section \<open>The Gaussian increment measure\<close>

definition gauss_measure :: "real \<Rightarrow> real measure" where
  "gauss_measure v =
     (if v \<le> 0 then return borel 0
      else density lborel (normal_density 0 (sqrt v)))"

lemma gauss_measure_zero: "gauss_measure 0 = return borel 0"
  by (simp add: gauss_measure_def)

lemma gauss_measure_pos:
  "0 < v \<Longrightarrow> gauss_measure v = density lborel (normal_density 0 (sqrt v))"
  by (simp add: gauss_measure_def)

lemma sets_gauss_measure [simp, measurable_cong]:
  "sets (gauss_measure v) = sets borel"
  by (simp add: gauss_measure_def)

lemma space_gauss_measure [simp]:
  "space (gauss_measure v) = UNIV"
  by (simp add: gauss_measure_def)

lemma prob_space_gauss_measure [intro, simp]:
  "prob_space (gauss_measure v)"
proof (cases "v \<le> 0")
  case True
  then show ?thesis
    by (simp add: gauss_measure_def prob_space_return)
next
  case False
  then have "0 < sqrt v"
    by simp
  then show ?thesis
    using False by (simp add: gauss_measure_def prob_space_normal_density)
qed

lemma sigma_finite_gauss_measure [intro, simp]:
  "sigma_finite_measure (gauss_measure v)"
  by (intro prob_space_imp_sigma_finite prob_space_gauss_measure)

subsection \<open>Moments\<close>

lemma gauss_measure_moment_even:
  assumes v: "0 < v"
  shows "has_bochner_integral (gauss_measure v) (\<lambda>x. x ^ (2 * k))
           (fact (2 * k) / (2 ^ k * fact k) * v ^ k)"
proof -
  have veq: "fact (2 * k) / ((2 / v) ^ k * fact k)
      = fact (2 * k) / (2 ^ k * fact k) * (v ^ k :: real)"
    using v by (simp add: field_simps)
  have "has_bochner_integral lborel
          (\<lambda>x. normal_density 0 (sqrt v) x * x ^ (2 * k))
          (fact (2 * k) / ((2 / v) ^ k * fact k))"
    using normal_moment_even[of "sqrt v" 0 k] v by simp
  then have "has_bochner_integral lborel
          (\<lambda>x. normal_density 0 (sqrt v) x * x ^ (2 * k))
          (fact (2 * k) / (2 ^ k * fact k) * v ^ k)"
    by (simp add: veq)
  then have "has_bochner_integral
      (density lborel (normal_density 0 (sqrt v))) (\<lambda>x. x ^ (2 * k))
      (fact (2 * k) / (2 ^ k * fact k) * v ^ k)"
    by (subst has_bochner_integral_density)
      (auto simp: mult_ac)
  then show ?thesis
    using v by (simp add: gauss_measure_pos)
qed

lemma gauss_measure_fourth_moment:
  assumes v: "0 \<le> v"
  shows "(\<integral>x. x ^ 4 \<partial>gauss_measure v) = 3 * v\<^sup>2"
proof (cases "v = 0")
  case True
  then show ?thesis
    by (simp add: gauss_measure_zero integral_return)
next
  case False
  with v have v': "0 < v"
    by simp
  have "has_bochner_integral (gauss_measure v) (\<lambda>x. x ^ (2 * 2))
          (fact (2 * 2) / (2 ^ 2 * fact 2) * v ^ 2)"
    by (rule gauss_measure_moment_even[OF v'])
  moreover have "(fact (2 * 2) / (2 ^ 2 * fact 2) :: real) = 3"
    by (simp add: fact_numeral)
  ultimately have "has_bochner_integral (gauss_measure v) (\<lambda>x. x ^ 4) (3 * v\<^sup>2)"
    by (simp add: power2_eq_square)
  then show ?thesis
    by (rule has_bochner_integral_integral_eq)
qed

lemma gauss_measure_fourth_moment_nn:
  assumes v: "0 \<le> v"
  shows "(\<integral>\<^sup>+x. x ^ 4 \<partial>gauss_measure v) = ennreal (3 * v\<^sup>2)"
proof (cases "v = 0")
  case True
  then show ?thesis
    by (simp add: gauss_measure_zero nn_integral_return)
next
  case False
  with v have v': "0 < v"
    by simp
  have integrable: "integrable (gauss_measure v) (\<lambda>x. x ^ 4)"
    using gauss_measure_moment_even[OF v', of 2]
    by (auto intro: integrable.intros)
  have nonneg: "AE x in gauss_measure v. 0 \<le> x ^ 4"
    by (auto intro!: zero_le_even_power)
  have "(\<integral>\<^sup>+x. x ^ 4 \<partial>gauss_measure v) = ennreal (\<integral>x. x ^ 4 \<partial>gauss_measure v)"
    by (rule nn_integral_eq_integral[OF integrable nonneg])
  then show ?thesis
    by (simp add: gauss_measure_fourth_moment[OF v])
qed

subsection \<open>Translation invariance of \<open>lborel\<close>\<close>

lemma nn_integral_lborel_shift:
  fixes c :: real
  assumes [measurable]: "f \<in> borel_measurable borel"
  shows "(\<integral>\<^sup>+y. f (c + y) \<partial>lborel) = (\<integral>\<^sup>+y. f y \<partial>lborel)"
  using nn_integral_real_affine[OF assms, of 1 c] by simp

subsection \<open>The convolution law\<close>

text \<open>Adding two independent Gaussian increments produces a Gaussian
  increment with summed variance --- including the degenerate cases.  This
  single lemma carries the projectivity of the Brownian finite-dimensional
  distributions.\<close>

lemma gauss_measure_conv_nn:
  assumes a: "0 \<le> a" and b: "0 \<le> b"
    and f [measurable]: "f \<in> borel_measurable (borel :: real measure)"
  shows "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x + y) \<partial>gauss_measure b) \<partial>gauss_measure a)
       = (\<integral>\<^sup>+z. f z \<partial>gauss_measure (a + b))"
proof (cases "a = 0")
  case True
  have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x + y) \<partial>gauss_measure b) \<partial>return borel 0)
      = (\<integral>\<^sup>+y. f ((0::real) + y) \<partial>gauss_measure b)"
  proof (rule nn_integral_return)
    interpret Gb: sigma_finite_measure "gauss_measure b"
      by simp
    show "(\<lambda>x. \<integral>\<^sup>+y. f (x + y) \<partial>gauss_measure b) \<in> borel_measurable borel"
      by measurable
  qed simp
  then show ?thesis
    using True by (simp add: gauss_measure_zero)
next
  case False
  with a have a': "0 < a" by simp
  show ?thesis
  proof (cases "b = 0")
    case True
    have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x + y) \<partial>return borel 0) \<partial>gauss_measure a)
        = (\<integral>\<^sup>+x. f (x + (0::real)) \<partial>gauss_measure a)"
      by (intro nn_integral_cong nn_integral_return) auto
    then show ?thesis
      using True by (simp add: gauss_measure_zero)
  next
    case False
    with b have b': "0 < b" by simp
    let ?ga = "\<lambda>x. ennreal (normal_density 0 (sqrt a) x)"
    let ?gb = "\<lambda>x. ennreal (normal_density 0 (sqrt b) x)"
    have "(\<integral>\<^sup>+x. (\<integral>\<^sup>+y. f (x + y) \<partial>gauss_measure b) \<partial>gauss_measure a)
        = (\<integral>\<^sup>+x. ?ga x * (\<integral>\<^sup>+y. f (x + y) \<partial>gauss_measure b) \<partial>lborel)"
      unfolding gauss_measure_pos[OF a']
    proof (rule nn_integral_density)
      interpret Gb: sigma_finite_measure "gauss_measure b"
        by simp
      show "(\<lambda>x. \<integral>\<^sup>+y. f (x + y) \<partial>gauss_measure b) \<in> borel_measurable lborel"
        by measurable
    qed auto
    also have "\<dots> = (\<integral>\<^sup>+x. ?ga x * (\<integral>\<^sup>+y. ?gb y * f (x + y) \<partial>lborel) \<partial>lborel)"
      unfolding gauss_measure_pos[OF b']
      by (intro nn_integral_cong arg_cong2[where f = "(*)"] refl
          nn_integral_density)
        auto
    also have "\<dots> = (\<integral>\<^sup>+x. ?ga x * (\<integral>\<^sup>+z. ?gb (z - x) * f z \<partial>lborel) \<partial>lborel)"
    proof (rule nn_integral_cong)
      fix x :: real
      have "(\<integral>\<^sup>+y. ?gb y * f (x + y) \<partial>lborel)
          = (\<integral>\<^sup>+y. (\<lambda>z. ?gb (z - x) * f z) (x + y) \<partial>lborel)"
        by (intro nn_integral_cong) simp
      also have "\<dots> = (\<integral>\<^sup>+z. ?gb (z - x) * f z \<partial>lborel)"
        by (rule nn_integral_lborel_shift) measurable
      finally show "?ga x * (\<integral>\<^sup>+y. ?gb y * f (x + y) \<partial>lborel)
          = ?ga x * (\<integral>\<^sup>+z. ?gb (z - x) * f z \<partial>lborel)" by simp
    qed
    also have "\<dots> = (\<integral>\<^sup>+x. (\<integral>\<^sup>+z. ?ga x * (?gb (z - x) * f z) \<partial>lborel) \<partial>lborel)"
    proof (rule nn_integral_cong)
      fix x :: real
      show "?ga x * (\<integral>\<^sup>+z. ?gb (z - x) * f z \<partial>lborel)
          = (\<integral>\<^sup>+z. ?ga x * (?gb (z - x) * f z) \<partial>lborel)"
        by (rule nn_integral_cmult[symmetric]) measurable
    qed
    also have "\<dots> = (\<integral>\<^sup>+z. (\<integral>\<^sup>+x. ?ga x * (?gb (z - x) * f z) \<partial>lborel) \<partial>lborel)"
      by (rule lborel_pair.Fubini') measurable
    also have "\<dots> = (\<integral>\<^sup>+z. (\<integral>\<^sup>+x. ennreal (normal_density 0 (sqrt b) (z - x)
        * normal_density 0 (sqrt a) x) \<partial>lborel) * f z \<partial>lborel)"
    proof (rule nn_integral_cong)
      fix z :: real
      have "(\<integral>\<^sup>+x. ?ga x * (?gb (z - x) * f z) \<partial>lborel)
          = (\<integral>\<^sup>+x. ennreal (normal_density 0 (sqrt b) (z - x)
              * normal_density 0 (sqrt a) x) * f z \<partial>lborel)"
        by (intro nn_integral_cong)
          (simp add: ennreal_mult mult_ac)
      also have "\<dots> = (\<integral>\<^sup>+x. ennreal (normal_density 0 (sqrt b) (z - x)
              * normal_density 0 (sqrt a) x) \<partial>lborel) * f z"
        by (rule nn_integral_multc) measurable
      finally show "(\<integral>\<^sup>+x. ?ga x * (?gb (z - x) * f z) \<partial>lborel)
          = (\<integral>\<^sup>+x. ennreal (normal_density 0 (sqrt b) (z - x)
              * normal_density 0 (sqrt a) x) \<partial>lborel) * f z" .
    qed
    also have "\<dots> = (\<integral>\<^sup>+z. ennreal (normal_density 0 (sqrt (a + b)) z) * f z
        \<partial>lborel)"
    proof (intro nn_integral_cong arg_cong2[where f = "(*)"] refl)
      fix z :: real
      have "(\<integral>\<^sup>+x. ennreal (normal_density 0 (sqrt b) (z - x)
          * normal_density 0 (sqrt a) x) \<partial>lborel)
          = ennreal (normal_density 0 (sqrt ((sqrt b)\<^sup>2 + (sqrt a)\<^sup>2)) z)"
        using fun_cong[OF conv_normal_density_zero_mean[of "sqrt b" "sqrt a"],
            of z] a' b'
        by simp
      also have "sqrt ((sqrt b)\<^sup>2 + (sqrt a)\<^sup>2) = sqrt (a + b)"
        using a b by (simp add: add.commute)
      finally show "(\<integral>\<^sup>+x. ennreal (normal_density 0 (sqrt b) (z - x)
          * normal_density 0 (sqrt a) x) \<partial>lborel)
          = ennreal (normal_density 0 (sqrt (a + b)) z)" .
    qed
    also have "\<dots> = (\<integral>\<^sup>+z. f z \<partial>gauss_measure (a + b))"
      unfolding gauss_measure_pos[OF add_pos_nonneg[OF a' b]]
      by (rule nn_integral_density[symmetric])
        auto
    finally show ?thesis .
  qed
qed

text \<open>The pushforward form of the convolution law.\<close>

lemma gauss_measure_conv:
  assumes a: "0 \<le> a" and b: "0 \<le> b"
  shows "distr (gauss_measure a \<Otimes>\<^sub>M gauss_measure b) borel (\<lambda>(x, y). x + y)
       = gauss_measure (a + b)"
proof (rule measure_eqI)
  show "sets (distr (gauss_measure a \<Otimes>\<^sub>M gauss_measure b) borel
      (\<lambda>(x, y). x + y)) = sets (gauss_measure (a + b))"
    by simp
next
  interpret Gb: sigma_finite_measure "gauss_measure b"
    by simp
  fix X :: "real set"
  assume "X \<in> sets (distr (gauss_measure a \<Otimes>\<^sub>M gauss_measure b) borel
      (\<lambda>(x, y). x + y))"
  then have X [measurable]: "X \<in> sets borel"
    by simp
  have meas_add: "(\<lambda>(x, y). x + y)
      \<in> (gauss_measure a \<Otimes>\<^sub>M gauss_measure b) \<rightarrow>\<^sub>M (borel :: real measure)"
    by measurable
  have pre: "(\<lambda>(x, y). x + y) -` X \<inter>
        space (gauss_measure a \<Otimes>\<^sub>M gauss_measure b)
      \<in> sets (gauss_measure a \<Otimes>\<^sub>M gauss_measure b)"
    by (rule measurable_sets[OF meas_add X])
  have "emeasure (distr (gauss_measure a \<Otimes>\<^sub>M gauss_measure b) borel
        (\<lambda>(x, y). x + y)) X
      = emeasure (gauss_measure a \<Otimes>\<^sub>M gauss_measure b)
        ((\<lambda>(x, y). x + y) -` X \<inter> space (gauss_measure a \<Otimes>\<^sub>M gauss_measure b))"
    by (rule emeasure_distr[OF meas_add X])
  also have "\<dots> = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator ((\<lambda>(x, y). x + y) -` X \<inter>
        space (gauss_measure a \<Otimes>\<^sub>M gauss_measure b)) (x, y)
        \<partial>gauss_measure b) \<partial>gauss_measure a)"
    by (rule Gb.emeasure_pair_measure[OF pre])
  also have "\<dots> = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator X (x + y) \<partial>gauss_measure b)
      \<partial>gauss_measure a)"
    by (intro nn_integral_cong)
      (auto simp: space_pair_measure split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+z. indicator X z \<partial>gauss_measure (a + b))"
    by (rule gauss_measure_conv_nn[OF a b]) measurable
  also have "\<dots> = emeasure (gauss_measure (a + b)) X"
    by simp
  finally show "emeasure (distr (gauss_measure a \<Otimes>\<^sub>M gauss_measure b) borel
      (\<lambda>(x, y). x + y)) X = emeasure (gauss_measure (a + b)) X" .
qed


(*<*)
end
(*>*)
