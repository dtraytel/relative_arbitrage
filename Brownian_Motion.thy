(*
  Title:   Brownian_Motion.thy
  Content: Construction of Brownian motion in Isabelle/HOL.

  Strategy (maximal reuse):
  \<^item> finite-dimensional distributions are pushforwards of finite products of
    independent Gaussian increment measures under cumulative-sum maps;
  \<^item> projectivity reduces to merging two adjacent increments, i.e. to the
    convolution law for Gaussians (HOL-Probability's
    conv_normal_density_zero_mean);
  \<^item> the projective limit is Immler's Daniell--Kolmogorov theorem
    (HOL-Probability, locale polish_projective);
  \<^item> the continuous modification comes from the AFP entry
    Kolmogorov_Chentsov (theorem Kolmogorov_Chentsov), whose moment
    hypothesis is discharged by the Gaussian fourth moment
    E|B_t - B_s|^4 = 3 |t-s|^2  (HOL-Probability's normal_moment_even).

  This part provides the Gaussian increment measure gauss_measure,
  parameterized by its VARIANCE (variance 0 degenerating to a point
  mass), its moments, and the convolution law both in pushforward and in
  iterated-integral form.
*)

theory Brownian_Motion
  imports
    "HOL-Probability.Probability"
begin

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
    by (auto intro!: AE_I2 zero_le_even_power)
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

section \<open>Finite-dimensional distributions\<close>

text \<open>For a finite set \<open>J\<close> of times, the Brownian finite-dimensional
  distribution is the pushforward of the product of independent Gaussian
  increment measures (one per time, with variance the gap to the previous
  time) under the cumulative-sum map.  Indexing the increment product by the
  times themselves avoids all list/index bookkeeping in the product measure.\<close>

definition prevt :: "real \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real" where
  "prevt t J s = Max (insert t {u \<in> J. u < s})"

definition inc_prod :: "real \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> real) measure" where
  "inc_prod t J = Pi\<^sub>M J (\<lambda>s. gauss_measure (s - prevt t J s))"

definition csum :: "real set \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "csum J \<omega> = (\<lambda>t\<in>J. \<Sum>u\<in>{u \<in> J. u \<le> t}. \<omega> u)"

definition bm_fdd :: "real set \<Rightarrow> (real \<Rightarrow> real) measure" where
  "bm_fdd J = distr (inc_prod 0 J) (Pi\<^sub>M J (\<lambda>_. borel)) (csum J)"

lemma sets_inc_prod [simp, measurable_cong]:
  "sets (inc_prod t J) = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
  unfolding inc_prod_def by (rule sets_PiM_cong) simp_all

lemma prob_space_inc_prod [intro, simp]: "prob_space (inc_prod t J)"
  unfolding inc_prod_def by (intro prob_space_PiM prob_space_gauss_measure)

lemma measurable_csum [measurable]:
  "csum J \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
  unfolding csum_def
  by (intro measurable_restrict borel_measurable_sum
      measurable_component_singleton) auto

lemma measurable_csum_inc_prod [measurable]:
  "csum J \<in> inc_prod t J \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
  by (subst measurable_cong_sets[OF sets_inc_prod refl])
    (rule measurable_csum)

lemma sets_bm_fdd [simp]:
  "sets (bm_fdd J) = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
  by (simp add: bm_fdd_def)

lemma space_bm_fdd:
  "space (bm_fdd J) = space (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
  by (rule sets_eq_imp_space_eq) simp

lemma prob_space_bm_fdd [intro, simp]: "prob_space (bm_fdd J)"
  unfolding bm_fdd_def
  by (intro prob_space.prob_space_distr prob_space_inc_prod
      measurable_csum_inc_prod)

subsection \<open>The nested-integral kernel of the FDDs\<close>

text \<open>\<open>wr t x ps\<close> is the probability that a Brownian path started at time
  \<open>t\<close> in position \<open>x\<close> passes through the window \<open>A\<close> at each time \<open>s\<close>, for
  \<open>(s, A)\<close> in the list \<open>ps\<close> --- written as iterated Gaussian integrals.\<close>

fun wr :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real set) list \<Rightarrow> ennreal" where
  "wr t x [] = 1"
| "wr t x ((s, A) # ps) =
    (\<integral>\<^sup>+z. indicator A (x + z) * wr s (x + z) ps
     \<partial>gauss_measure (s - t))"

lemma wr_measurable:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> snd p \<in> sets borel"
  shows "(\<lambda>x. wr t x ps) \<in> borel_measurable (borel :: real measure)"
  using assms
proof (induction ps arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain s A where p [simp]: "p = (s, A)" by (cases p)
  from Cons.prems have A [measurable]: "A \<in> sets borel" by force
  have rec [measurable]: "(\<lambda>x. wr s x ps) \<in> borel_measurable borel"
    using Cons.prems by (intro Cons.IH) auto
  interpret G: sigma_finite_measure "gauss_measure (s - t)"
    by simp
  have "(\<lambda>(x, z). indicator A (x + z) * wr s (x + z) ps)
      \<in> borel_measurable (borel \<Otimes>\<^sub>M gauss_measure (s - t))"
    by measurable
  then have "(\<lambda>x. \<integral>\<^sup>+z. indicator A (x + z) * wr s (x + z) ps
      \<partial>gauss_measure (s - t)) \<in> borel_measurable borel"
    by (rule G.borel_measurable_nn_integral)
  then show ?case by simp
qed

subsection \<open>Marginalization: inserting an unconstrained time\<close>

fun ins :: "real \<Rightarrow> (real \<times> real set) list \<Rightarrow> (real \<times> real set) list" where
  "ins s [] = [(s, UNIV)]"
| "ins s (p # ps) = (if s < fst p then (s, UNIV) # p # ps else p # ins s ps)"

text \<open>The heart of projectivity: integrating out an unconstrained time
  merges two adjacent Gaussian increments, which is the convolution law.\<close>

lemma wr_ins:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> snd p \<in> sets borel"
    and "t \<le> s"
  shows "wr t x (ins s ps) = wr t x ps"
  using assms
proof (induction ps arbitrary: t x)
  case Nil
  interpret G: prob_space "gauss_measure (s - t)" by simp
  show ?case
    using G.emeasure_space_1
    by (simp add: indicator_def)
next
  case (Cons p ps)
  obtain u A where p [simp]: "p = (u, A)" by (cases p)
  from Cons.prems have A [measurable]: "A \<in> sets borel" by force
  have ps_sets: "\<And>q. q \<in> set ps \<Longrightarrow> snd q \<in> sets borel"
    using Cons.prems by auto
  show ?case
  proof (cases "s < u")
    case True
    have wrm [measurable]: "(\<lambda>y. wr u y ps) \<in> borel_measurable borel"
      by (rule wr_measurable) fact
    have fmeas: "(\<lambda>y. indicator A (x + y) * wr u (x + y) ps)
        \<in> borel_measurable (borel :: real measure)"
      by measurable
    have "wr t x (ins s (p # ps))
        = (\<integral>\<^sup>+z. indicator (UNIV :: real set) (x + z) * wr s (x + z) (p # ps)
           \<partial>gauss_measure (s - t))"
      using True by simp
    also have "\<dots> = (\<integral>\<^sup>+z. \<integral>\<^sup>+w. indicator A (x + (z + w)) * wr u (x + (z + w)) ps
        \<partial>gauss_measure (u - s) \<partial>gauss_measure (s - t))"
      by (simp add: indicator_def add_ac)
    also have "\<dots> = (\<integral>\<^sup>+y. indicator A (x + y) * wr u (x + y) ps
        \<partial>gauss_measure ((s - t) + (u - s)))"
      by (rule gauss_measure_conv_nn
          [where f = "\<lambda>y. indicator A (x + y) * wr u (x + y) ps"])
        (use True \<open>t \<le> s\<close> fmeas in auto)
    also have "\<dots> = wr t x (p # ps)"
      by simp
    finally show ?thesis .
  next
    case False
    then have us: "u \<le> s" by simp
    have IH': "\<And>y. wr u y (ins s ps) = wr u y ps"
      using ps_sets us by (intro Cons.IH) auto
    have "wr t x (ins s (p # ps))
        = (\<integral>\<^sup>+z. indicator A (x + z) * wr u (x + z) (ins s ps)
           \<partial>gauss_measure (u - t))"
      using False by simp
    also have "\<dots> = (\<integral>\<^sup>+z. indicator A (x + z) * wr u (x + z) ps
        \<partial>gauss_measure (u - t))"
      by (intro nn_integral_cong) (simp add: IH')
    also have "\<dots> = wr t x (p # ps)"
      by simp
    finally show ?thesis .
  qed
qed

subsection \<open>Rectangle emeasure formula\<close>

lemma prod_indicator_conj:
  "finite J \<Longrightarrow> (\<Prod>s\<in>J. (indicator (A s) (g s) :: ennreal))
     = (if \<forall>s\<in>J. g s \<in> A s then 1 else 0)"
  by (induction J rule: finite_induct) (auto simp: indicator_def)

lemma sumprod_measurable:
  fixes Mm :: "real \<Rightarrow> real measure"
  assumes Mm: "\<And>s. sets (Mm s) = sets borel"
    and A: "\<And>s. s \<in> J \<Longrightarrow> A s \<in> sets borel"
  shows "(\<lambda>\<omega>. \<Prod>s\<in>J. (indicator (A s) (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u))
          :: ennreal)) \<in> borel_measurable (Pi\<^sub>M J Mm)"
proof (rule borel_measurable_prod_ennreal)
  fix s assume s: "s \<in> J"
  have comp: "(\<lambda>\<omega>. \<omega> u) \<in> borel_measurable (Pi\<^sub>M J Mm)"
    if u: "u \<in> {u \<in> J. u \<le> s}" for u
  proof -
    from u have "u \<in> J" by blast
    then have "(\<lambda>\<omega>. \<omega> u) \<in> Pi\<^sub>M J Mm \<rightarrow>\<^sub>M Mm u"
      by (rule measurable_component_singleton)
    then show ?thesis
      by (simp add: measurable_cong_sets[OF refl Mm])
  qed
  have inner: "(\<lambda>\<omega>. x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u))
      \<in> borel_measurable (Pi\<^sub>M J Mm)"
    by (intro borel_measurable_add borel_measurable_const
        borel_measurable_sum comp)
  show "(\<lambda>\<omega>. (indicator (A s) (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)) :: ennreal))
      \<in> borel_measurable (Pi\<^sub>M J Mm)"
    by (rule measurable_compose[OF inner borel_measurable_indicator])
      (rule A[OF s])
qed

lemma inc_prod_rect:
  "finite J \<Longrightarrow> \<forall>s\<in>J. t \<le> s \<Longrightarrow> \<forall>s\<in>J. A s \<in> sets borel \<Longrightarrow>
   (\<integral>\<^sup>+\<omega>. (\<Prod>s\<in>J. indicator (A s) (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)))
     \<partial>inc_prod t J)
   = wr t x (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
proof (induction J arbitrary: t x rule: finite_psubset_induct)
  case (psubset J)
  note finJ = psubset.hyps
  note lower = psubset.prems(1)
  note Asets = psubset.prems(2)
  show ?case
  proof (cases "J = {}")
    case True
    interpret E: prob_space "inc_prod t J" by simp
    show ?thesis
      using E.emeasure_space_1
      by (simp add: True)
  next
    case False
    define t0 where "t0 = Min J"
    define J' where "J' = J - {t0}"
    have t0J: "t0 \<in> J"
      using False finJ by (simp add: t0_def)
    have t0min: "\<And>s. s \<in> J \<Longrightarrow> t0 \<le> s"
      using finJ by (simp add: t0_def)
    have Jins: "J = insert t0 J'"
      using t0J by (auto simp: J'_def)
    have finJ': "finite J'" and t0J': "t0 \<notin> J'"
      using finJ by (auto simp: J'_def)
    have J'less: "\<And>s. s \<in> J' \<Longrightarrow> t0 < s"
      using t0min by (auto simp: J'_def order_less_le)
    have tt0: "t \<le> t0"
      using lower t0J by simp
    let ?M = "\<lambda>s. gauss_measure (s - prevt t J s)"
    let ?f = "\<lambda>w. \<Prod>s\<in>J. (indicator (A s)
        (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. w u)) :: ennreal)"
    let ?rest = "map (\<lambda>s. (s, A s)) (sorted_list_of_set J')"
    interpret PSF: product_sigma_finite ?M
      by (intro product_sigma_finite.intro sigma_finite_gauss_measure)
    have J'sub: "J' \<subset> J"
      using t0J by (auto simp: J'_def)
    have f_meas: "?f \<in> borel_measurable (Pi\<^sub>M J ?M)"
      using Asets by (intro sumprod_measurable) auto
    have prevt_t0: "prevt t J t0 = t"
    proof -
      have e: "{u \<in> J. u < t0} = {}"
        using t0min by fastforce
      show ?thesis unfolding prevt_def e by simp
    qed
    have prevt_eq: "\<And>s. s \<in> J' \<Longrightarrow> prevt t J s = prevt t0 J' s"
    proof -
      fix s assume s: "s \<in> J'"
      have below: "{u \<in> J. u < s} = insert t0 {u \<in> J'. u < s}"
        using J'less[OF s] t0J by (auto simp: J'_def)
      have fin': "finite (insert t0 {u \<in> J'. u < s})"
        using finJ' by simp
      have "prevt t J s = max t (Max (insert t0 {u \<in> J'. u < s}))"
        by (simp add: prevt_def below Max_insert[OF fin'])
      also have "\<dots> = Max (insert t0 {u \<in> J'. u < s})"
        using tt0 fin' by (intro max_absorb2 order_trans[OF tt0 Max_ge]) auto
      also have "\<dots> = prevt t0 J' s"
        by (simp add: prevt_def)
      finally show "prevt t J s = prevt t0 J' s" .
    qed
    have PiM_J': "Pi\<^sub>M J' ?M = inc_prod t0 J'"
      unfolding inc_prod_def
      by (rule PiM_cong[OF refl]) (simp add: prevt_eq)
    have sum_t0: "{u \<in> J. u \<le> t0} = {t0}"
      using t0J t0min by (auto intro: antisym)
    have sum_ins: "\<And>s. s \<in> J' \<Longrightarrow> {u \<in> J. u \<le> s} = insert t0 {u \<in> J'. u \<le> s}"
      using t0min t0J by (auto simp: J'_def)
    have inner: "?f (w(t0 := z)) = indicator (A t0) (x + z) *
        (\<Prod>s\<in>J'. (indicator (A s)
          ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)) :: ennreal))" for z w
    proof -
      have sum_eq: "(\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)
          = z + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)" if s: "s \<in> J'" for s
      proof -
        have fin'': "finite {u \<in> J'. u \<le> s}" using finJ' by simp
        have notin: "t0 \<notin> {u \<in> J'. u \<le> s}" using t0J' by simp
        have "(\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)
            = (\<Sum>u\<in>insert t0 {u \<in> J'. u \<le> s}. (w(t0 := z)) u)"
          by (simp add: sum_ins[OF s])
        also have "\<dots> = z + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. (w(t0 := z)) u)"
          by (simp add: sum.insert[OF fin'' notin])
        also have "(\<Sum>u\<in>{u \<in> J'. u \<le> s}. (w(t0 := z)) u)
            = (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)"
          using t0J' by (intro sum.cong) auto
        finally show ?thesis .
      qed
      have "?f (w(t0 := z)) = (indicator (A t0)
          (x + (\<Sum>u\<in>{u \<in> J. u \<le> t0}. (w(t0 := z)) u)) :: ennreal) *
          (\<Prod>s\<in>J'. (indicator (A s)
            (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)) :: ennreal))"
        by (subst Jins) (rule prod.insert[OF finJ' t0J'])
      also have "(indicator (A t0)
          (x + (\<Sum>u\<in>{u \<in> J. u \<le> t0}. (w(t0 := z)) u)) :: ennreal)
          = indicator (A t0) (x + z)"
        by (simp add: sum_t0)
      also have "(\<Prod>s\<in>J'. (indicator (A s)
            (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)) :: ennreal))
          = (\<Prod>s\<in>J'. (indicator (A s)
            ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)) :: ennreal))"
      proof (rule prod.cong[OF refl])
        fix s assume s: "s \<in> J'"
        have "x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)
            = x + (z + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))"
          using sum_eq[OF s] by (rule arg_cong[where f = "(+) x"])
        also have "\<dots> = (x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)"
          by (rule add.assoc[symmetric])
        finally show "(indicator (A s)
            (x + (\<Sum>u\<in>{u \<in> J. u \<le> s}. (w(t0 := z)) u)) :: ennreal)
            = indicator (A s) ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))"
          by (rule arg_cong[where f = "indicator (A s)"])
      qed
      finally show ?thesis .
    qed
    have g_meas: "\<And>z. (\<lambda>w. \<Prod>s\<in>J'. (indicator (A s)
        ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u)) :: ennreal))
        \<in> borel_measurable (Pi\<^sub>M J' ?M)"
      using Asets by (intro sumprod_measurable) (auto simp: J'_def)
    have IH': "(\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
        (y + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>inc_prod t0 J')
        = wr t0 y ?rest" for y
      using J'less Asets
      by (intro psubset.IH[OF J'sub]) (auto simp: J'_def order_less_imp_le)
    have "(\<integral>\<^sup>+w. ?f w \<partial>inc_prod t J) = integral\<^sup>N (Pi\<^sub>M (insert t0 J') ?M) ?f"
      using Jins by (simp add: inc_prod_def)
    also have "\<dots> = (\<integral>\<^sup>+z. (\<integral>\<^sup>+w. ?f (w(t0 := z)) \<partial>Pi\<^sub>M J' ?M) \<partial>?M t0)"
      using f_meas Jins
      by (intro PSF.product_nn_integral_insert_rev[OF finJ' t0J']) simp
    also have "\<dots> = (\<integral>\<^sup>+z. indicator (A t0) (x + z) *
        (\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
          ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M) \<partial>?M t0)"
    proof (rule nn_integral_cong)
      fix z :: real
      have "(\<integral>\<^sup>+w. ?f (w(t0 := z)) \<partial>Pi\<^sub>M J' ?M)
          = (\<integral>\<^sup>+w. indicator (A t0) (x + z) *
            (\<Prod>s\<in>J'. indicator (A s)
              ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M)"
      proof (rule nn_integral_cong)
        fix v :: "real \<Rightarrow> real"
        show "?f (v(t0 := z)) = indicator (A t0) (x + z) *
            (\<Prod>s\<in>J'. indicator (A s)
              ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. v u)))"
          by (rule inner)
      qed
      also have "\<dots> = indicator (A t0) (x + z) *
          (\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
            ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M)"
        by (rule nn_integral_cmult) (rule g_meas)
      finally show "(\<integral>\<^sup>+w. ?f (w(t0 := z)) \<partial>Pi\<^sub>M J' ?M)
          = indicator (A t0) (x + z) *
          (\<integral>\<^sup>+w. (\<Prod>s\<in>J'. indicator (A s)
            ((x + z) + (\<Sum>u\<in>{u \<in> J'. u \<le> s}. w u))) \<partial>Pi\<^sub>M J' ?M)" .
    qed
    also have "\<dots> = (\<integral>\<^sup>+z. indicator (A t0) (x + z) *
        wr t0 (x + z) ?rest \<partial>?M t0)"
      by (intro nn_integral_cong) (simp add: PiM_J' IH')
    also have "\<dots> = (\<integral>\<^sup>+z. indicator (A t0) (x + z) *
        wr t0 (x + z) ?rest \<partial>gauss_measure (t0 - t))"
      by (simp add: prevt_t0)
    also have "\<dots> = wr t x ((t0, A t0) # ?rest)"
      by simp
    also have "\<dots> = wr t x (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
    proof -
      have slos: "sorted_list_of_set J = t0 # sorted_list_of_set J'"
        unfolding t0_def J'_def using finJ False
        by (rule sorted_list_of_set_nonempty)
      show ?thesis by (simp add: slos)
    qed
    finally show ?thesis .
  qed
qed

lemma emeasure_bm_fdd:
  assumes fin: "finite J" and J: "J \<subseteq> {0..}"
    and A: "\<And>s. s \<in> J \<Longrightarrow> A s \<in> sets borel"
  shows "emeasure (bm_fdd J) (Pi\<^sub>E J A)
       = wr 0 0 (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
proof -
  have PiE_sets: "Pi\<^sub>E J A \<in> sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
    by (intro sets_PiM_I_finite fin A)
  have "emeasure (bm_fdd J) (Pi\<^sub>E J A)
      = emeasure (inc_prod 0 J)
        (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J))"
    unfolding bm_fdd_def
    by (rule emeasure_distr[OF measurable_csum_inc_prod PiE_sets])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator
      (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J)) \<omega> \<partial>inc_prod 0 J)"
    by (rule nn_integral_indicator[symmetric])
      (rule measurable_sets[OF measurable_csum_inc_prod PiE_sets])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<Prod>s\<in>J. indicator (A s)
      (0 + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u))) \<partial>inc_prod 0 J)"
  proof (rule nn_integral_cong)
    fix \<omega> assume \<omega>: "\<omega> \<in> space (inc_prod 0 J)"
    have mem: "csum J \<omega> \<in> Pi\<^sub>E J A
        \<longleftrightarrow> (\<forall>s\<in>J. (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u) \<in> A s)"
      by (auto simp: csum_def PiE_iff extensional_def)
    have "(\<Prod>s\<in>J. (indicator (A s)
          (0 + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)) :: ennreal))
        = (if \<forall>s\<in>J. (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u) \<in> A s then 1 else 0)"
      by (simp add: prod_indicator_conj[OF fin])
    also have "\<dots> = indicator (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J)) \<omega>"
      using \<omega> mem by (auto simp: indicator_def)
    finally show "indicator (csum J -` Pi\<^sub>E J A \<inter> space (inc_prod 0 J)) \<omega>
        = (\<Prod>s\<in>J. (indicator (A s)
          (0 + (\<Sum>u\<in>{u \<in> J. u \<le> s}. \<omega> u)) :: ennreal))" ..
  qed
  also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
    using fin J A by (intro inc_prod_rect) auto
  finally show ?thesis .
qed

subsection \<open>Projectivity\<close>

lemma map_pair_insort:
  "s \<notin> set xs \<Longrightarrow> B s = UNIV \<Longrightarrow>
   map (\<lambda>t. (t, B t)) (insort s xs) = ins s (map (\<lambda>t. (t, B t)) xs)"
  by (induction xs) auto

lemma wr_pairs_extend:
  "finite D \<Longrightarrow> finite J \<Longrightarrow> D \<inter> J = {} \<Longrightarrow> \<forall>s\<in>D. (0::real) \<le> s \<Longrightarrow>
   \<forall>s\<in>J. B s \<in> sets borel \<Longrightarrow> \<forall>s\<in>D. B s = UNIV \<Longrightarrow>
   wr 0 0 (map (\<lambda>s. (s, B s)) (sorted_list_of_set (J \<union> D)))
     = wr 0 0 (map (\<lambda>s. (s, B s)) (sorted_list_of_set J))"
proof (induction D rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert s D)
  have sJD: "s \<notin> J \<union> D"
    using insert.prems insert.hyps by auto
  have finJD: "finite (J \<union> D)"
    using insert.prems insert.hyps by auto
  have "J \<union> insert s D = insert s (J \<union> D)" by auto
  then have "sorted_list_of_set (J \<union> insert s D)
      = insort s (sorted_list_of_set (J \<union> D))"
    using finJD sJD by simp
  then have "map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> insert s D))
      = ins s (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))"
    using sJD insert.prems
    by (simp add: map_pair_insort set_sorted_list_of_set[OF finJD])
  moreover have "wr 0 0 (ins s (map (\<lambda>u. (u, B u))
      (sorted_list_of_set (J \<union> D))))
      = wr 0 0 (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))"
  proof (rule wr_ins)
    fix p assume "p \<in> set (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))"
    then obtain u where u: "u \<in> J \<union> D" "p = (u, B u)"
      by (auto simp: set_sorted_list_of_set[OF finJD])
    then show "snd p \<in> sets borel"
      using insert.prems by auto
  next
    show "0 \<le> s" using insert.prems by simp
  qed
  moreover have "wr 0 0 (map (\<lambda>u. (u, B u)) (sorted_list_of_set (J \<union> D)))
      = wr 0 0 (map (\<lambda>u. (u, B u)) (sorted_list_of_set J))"
    using insert.prems insert.hyps by (intro insert.IH) auto
  ultimately show ?case by simp
qed

theorem bm_fdd_projective:
  assumes JH: "J \<subseteq> H" and finH: "finite H" and H: "H \<subseteq> {0..}"
  shows "bm_fdd J
       = distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))
           (\<lambda>f. restrict f J)"
proof -
  have finJ: "finite J" using JH finH by (rule finite_subset)
  have J0: "J \<subseteq> {0..}" using JH H by blast
  interpret PJ: prob_space "bm_fdd J" by simp
  have restr_meas: "(\<lambda>f. restrict f J) \<in>
      bm_fdd H \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
    by (subst measurable_cong_sets[OF sets_bm_fdd refl])
      (rule measurable_restrict_subset[OF JH])
  show ?thesis
  proof (rule measure_eqI_PiM_finite[OF finJ])
    show "sets (bm_fdd J) = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
      by simp
    show "sets (distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J))
        = sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
      by simp
    show "range (\<lambda>_::nat. Pi\<^sub>E J (\<lambda>_. UNIV :: real set))
        \<subseteq> prod_algebra J (\<lambda>_. borel)"
      by (auto intro!: prod_algebraI_finite[OF finJ])
    show "(\<Union>i::nat. Pi\<^sub>E J (\<lambda>_. UNIV :: real set))
        = space (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))"
      by (auto simp: space_PiM)
    show "\<And>i::nat. emeasure (bm_fdd J) (Pi\<^sub>E J (\<lambda>_. UNIV)) \<noteq> \<infinity>"
      by simp
    fix A :: "real \<Rightarrow> real set"
    assume A: "\<And>i. i \<in> J \<Longrightarrow> A i \<in> sets borel"
    define A' where "A' s = (if s \<in> J then A s else (UNIV :: real set))" for s
    have A'H: "\<And>s. s \<in> H \<Longrightarrow> A' s \<in> sets borel"
      using A by (auto simp: A'_def)
    have space_H: "space (bm_fdd H) = space (Pi\<^sub>M H (\<lambda>_. (borel :: real measure)))"
      by (rule space_bm_fdd)
    have restr_pre: "(\<lambda>f. restrict f J) -` Pi\<^sub>E J A \<inter> space (bm_fdd H)
        = Pi\<^sub>E H A'"
    proof (intro equalityI subsetI)
      fix f assume "f \<in> (\<lambda>f. restrict f J) -` Pi\<^sub>E J A \<inter> space (bm_fdd H)"
      then have f: "restrict f J \<in> Pi\<^sub>E J A"
        and fsp: "f \<in> Pi\<^sub>E H (\<lambda>_. UNIV :: real set)"
        by (auto simp: space_H space_PiM)
      have "f s \<in> A' s" if sH: "s \<in> H" for s
      proof (cases "s \<in> J")
        case True
        then have "restrict f J s \<in> A s"
          using f by (auto simp: PiE_iff)
        then show ?thesis using True by (simp add: A'_def)
      next
        case False
        then show ?thesis by (simp add: A'_def)
      qed
      with fsp show "f \<in> Pi\<^sub>E H A'"
        by (auto simp: PiE_iff)
    next
      fix f assume fH: "f \<in> Pi\<^sub>E H A'"
      then have vals: "\<And>s. s \<in> H \<Longrightarrow> f s \<in> A' s"
        by (auto simp: PiE_iff)
      have "restrict f J \<in> Pi\<^sub>E J A"
      proof (rule PiE_I)
        fix s assume sJ: "s \<in> J"
        have "f s \<in> A' s" using vals JH sJ by blast
        then show "restrict f J s \<in> A s"
          using sJ by (simp add: A'_def)
      next
        fix s assume "s \<notin> J"
        then show "restrict f J s = undefined" by simp
      qed
      moreover have "f \<in> space (bm_fdd H)"
        using fH by (auto simp: space_H space_PiM PiE_iff)
      ultimately show "f \<in> (\<lambda>f. restrict f J) -` Pi\<^sub>E J A
          \<inter> space (bm_fdd H)"
        by auto
    qed
    have "emeasure (distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel))
        (\<lambda>f. restrict f J)) (Pi\<^sub>E J A)
        = emeasure (bm_fdd H) ((\<lambda>f. restrict f J) -` Pi\<^sub>E J A
          \<inter> space (bm_fdd H))"
      by (rule emeasure_distr[OF restr_meas sets_PiM_I_finite[OF finJ A]])
    also have "\<dots> = emeasure (bm_fdd H) (Pi\<^sub>E H A')"
      unfolding restr_pre by (rule refl)
    also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A' s)) (sorted_list_of_set H))"
      by (rule emeasure_bm_fdd[OF finH H A'H])
    also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A' s)) (sorted_list_of_set J))"
    proof -
      have HJ: "H = J \<union> (H - J)" using JH by auto
      show ?thesis
        by (subst HJ)
          (intro wr_pairs_extend finJ, use finH H A JH in \<open>auto simp: A'_def\<close>)
    qed
    also have "\<dots> = wr 0 0 (map (\<lambda>s. (s, A s)) (sorted_list_of_set J))"
      by (intro arg_cong[where f = "wr 0 0"] map_cong refl)
        (simp add: A'_def set_sorted_list_of_set[OF finJ])
    also have "\<dots> = emeasure (bm_fdd J) (Pi\<^sub>E J A)"
      by (rule emeasure_bm_fdd[OF finJ J0 A, symmetric])
    finally show "emeasure (bm_fdd J) (Pi\<^sub>E J A)
        = emeasure (distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel))
          (\<lambda>f. restrict f J)) (Pi\<^sub>E J A)" ..
  qed
qed

subsection \<open>The projective limit\<close>

interpretation BM: polish_projective "{0..} :: real set" bm_fdd
proof (intro polish_projective.intro projective_family.intro)
  show "\<And>J H. J \<subseteq> H \<Longrightarrow> finite H \<Longrightarrow> H \<subseteq> {0..} \<Longrightarrow>
      bm_fdd J = distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
    by (rule bm_fdd_projective)
  show "\<And>J. finite J \<Longrightarrow> J \<subseteq> {0..} \<Longrightarrow> prob_space (bm_fdd J)"
    by (rule prob_space_bm_fdd)
qed

definition wiener_pre :: "(real \<Rightarrow> real) measure" where
  "wiener_pre = BM.lim"

lemma prob_space_wiener_pre: "prob_space wiener_pre"
  unfolding wiener_pre_def
  by (rule prob_spaceI) (rule BM.P.emeasure_space_1)

interpretation W: prob_space wiener_pre
  by (rule prob_space_wiener_pre)

lemma sets_wiener_pre [simp, measurable_cong]:
  "sets wiener_pre = sets (Pi\<^sub>M {0..} (\<lambda>_. (borel :: real measure)))"
  by (simp add: wiener_pre_def)

lemma measurable_coord:
  assumes "t \<in> {0..}"
  shows "(\<lambda>\<omega>. \<omega> t) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
  by (subst measurable_cong_sets[OF sets_wiener_pre refl])
    (rule measurable_component_singleton[OF assms])

lemma measurable_restrict_wiener_pre:
  assumes "J \<subseteq> {0..}"
  shows "(\<lambda>f. restrict f J) \<in> wiener_pre \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
  by (subst measurable_cong_sets[OF sets_wiener_pre refl])
    (rule measurable_restrict_subset[OF assms])

subsection \<open>Marginals of the projective limit\<close>

lemma wiener_pre_marginal:
  assumes fin: "finite J" and J: "J \<subseteq> {0..}"
  shows "distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J) = bm_fdd J"
proof (rule measure_eqI)
  show "sets (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J))
      = sets (bm_fdd J)" by simp
next
  fix X assume "X \<in> sets (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
      (\<lambda>f. restrict f J))"
  then have X: "X \<in> sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))" by simp
  have sp: "space wiener_pre = (\<Pi>\<^sub>E i\<in>{0..}. space (borel :: real measure))"
    by (simp add: wiener_pre_def space_PiM)
  have "emeasure (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
        (\<lambda>f. restrict f J)) X
      = emeasure wiener_pre ((\<lambda>f. restrict f J) -` X \<inter> space wiener_pre)"
    by (rule emeasure_distr[OF measurable_restrict_wiener_pre[OF J] X])
  also have "\<dots> = emeasure BM.lim (prod_emb {0..} (\<lambda>_. borel) J X)"
    by (simp add: wiener_pre_def prod_emb_def sp space_PiM)
  also have "\<dots> = emeasure (bm_fdd J) X"
    using BM.emeasure_lim_emb[OF J fin X] by simp
  finally show "emeasure (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
      (\<lambda>f. restrict f J)) X = emeasure (bm_fdd J) X" .
qed

subsection \<open>Increment distribution and starting point\<close>

lemma wiener_pre_increment:
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s) = gauss_measure (t - s)"
proof (cases "s = t")
  case True
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)
      = distr wiener_pre borel (\<lambda>\<omega>. 0 :: real)"
    by (simp add: True)
  also have "\<dots> = return borel 0"
    by (rule W.distr_const) simp
  also have "\<dots> = gauss_measure (t - s)"
    by (simp add: True gauss_measure_zero)
  finally show ?thesis .
next
  case False
  with st have st': "s < t" by simp
  have stJ: "{s, t} \<subseteq> {0..}" using s st by auto
  have Dmeas: "(\<lambda>g. g t - g s)
      \<in> Pi\<^sub>M {s, t} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
    by measurable
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)
      = distr wiener_pre borel ((\<lambda>g. g t - g s) \<circ> (\<lambda>f. restrict f {s, t}))"
    by (intro distr_cong refl) (simp add: comp_def)
  also have "\<dots> = distr (distr wiener_pre (Pi\<^sub>M {s, t} (\<lambda>_. borel))
      (\<lambda>f. restrict f {s, t})) borel (\<lambda>g. g t - g s)"
    by (rule distr_distr[symmetric, OF Dmeas
        measurable_restrict_wiener_pre[OF stJ]])
  also have "\<dots> = distr (bm_fdd {s, t}) borel (\<lambda>g. g t - g s)"
    by (simp add: wiener_pre_marginal[OF _ stJ])
  also have "\<dots> = distr (inc_prod 0 {s, t}) borel
      ((\<lambda>g. g t - g s) \<circ> csum {s, t})"
    unfolding bm_fdd_def
    by (rule distr_distr[OF Dmeas measurable_csum_inc_prod])
  also have "\<dots> = distr (inc_prod 0 {s, t}) borel (\<lambda>w. w t)"
  proof (intro distr_cong refl)
    fix w :: "real \<Rightarrow> real"
    have "csum {s, t} w t = (\<Sum>u\<in>{u \<in> {s, t}. u \<le> t}. w u)"
      by (simp add: csum_def)
    moreover have "{u \<in> {s, t}. u \<le> t} = {s, t}" using st by auto
    moreover have "(\<Sum>u\<in>{s, t}. w u) = w s + w t"
      using False by simp
    ultimately have 1: "csum {s, t} w t = w s + w t" by simp
    have "csum {s, t} w s = (\<Sum>u\<in>{u \<in> {s, t}. u \<le> s}. w u)"
      by (simp add: csum_def)
    moreover have "{u \<in> {s, t}. u \<le> s} = {s}" using st' by auto
    ultimately have 2: "csum {s, t} w s = w s" by simp
    show "((\<lambda>g. g t - g s) \<circ> csum {s, t}) w = w t"
      by (simp add: comp_def 1 2)
  qed
  also have "\<dots> = gauss_measure (t - s)"
  proof -
    interpret PPS: product_prob_space
      "\<lambda>u. gauss_measure (u - prevt 0 {s, t} u)" "{s, t}"
      by (intro product_prob_space.intro product_sigma_finite.intro
          product_prob_space_axioms.intro sigma_finite_gauss_measure
          prob_space_gauss_measure)
    have lt: "{u \<in> {s, t}. u < t} = {s}" using st' by auto
    have pt: "prevt 0 {s, t} t = s"
      unfolding prevt_def lt using s by (simp add: max_absorb2)
    have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)
        = distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)" by simp
    have "distr (inc_prod 0 {s, t}) borel (\<lambda>w. w t)
        = distr (Pi\<^sub>M {s, t} (\<lambda>u. gauss_measure (u - prevt 0 {s, t} u)))
          (gauss_measure (t - prevt 0 {s, t} t)) (\<lambda>w. w t)"
      by (intro distr_cong refl) (simp_all add: inc_prod_def)
    also have "\<dots> = gauss_measure (t - prevt 0 {s, t} t)"
      by (rule PPS.PiM_component) simp
    finally show ?thesis by (simp add: pt)
  qed
  finally show ?thesis .
qed

lemma wiener_pre_coord_zero:
  "distr wiener_pre borel (\<lambda>\<omega>. \<omega> 0) = gauss_measure 0"
proof -
  have zJ: "{0 :: real} \<subseteq> {0..}" by auto
  have Dmeas: "(\<lambda>g. g 0) \<in> Pi\<^sub>M {0 :: real} (\<lambda>_. borel)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    by measurable
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> 0)
      = distr wiener_pre borel ((\<lambda>g. g 0) \<circ> (\<lambda>f. restrict f {0}))"
    by (intro distr_cong refl) (simp add: comp_def)
  also have "\<dots> = distr (distr wiener_pre (Pi\<^sub>M {0} (\<lambda>_. borel))
      (\<lambda>f. restrict f {0})) borel (\<lambda>g. g 0)"
    by (rule distr_distr[symmetric, OF Dmeas
        measurable_restrict_wiener_pre[OF zJ]])
  also have "\<dots> = distr (bm_fdd {0}) borel (\<lambda>g. g 0)"
    by (simp add: wiener_pre_marginal[OF _ zJ])
  also have "\<dots> = distr (inc_prod 0 {0}) borel ((\<lambda>g. g 0) \<circ> csum {0})"
    unfolding bm_fdd_def
    by (rule distr_distr[OF Dmeas measurable_csum_inc_prod])
  also have "\<dots> = distr (inc_prod 0 {0}) borel (\<lambda>w. w 0)"
  proof (intro distr_cong refl)
    fix w :: "real \<Rightarrow> real"
    have "{u \<in> {0 :: real}. u \<le> 0} = {0}" by auto
    then show "((\<lambda>g. g 0) \<circ> csum {0}) w = w 0"
      by (simp add: csum_def comp_def)
  qed
  also have "\<dots> = gauss_measure 0"
  proof -
    interpret PPS: product_prob_space
      "\<lambda>u. gauss_measure (u - prevt 0 {0 :: real} u)" "{0 :: real}"
      by (intro product_prob_space.intro product_sigma_finite.intro
          product_prob_space_axioms.intro sigma_finite_gauss_measure
          prob_space_gauss_measure)
    have p0: "prevt 0 {0 :: real} 0 = 0"
    proof -
      have e: "{u \<in> {0 :: real}. u < 0} = {}" by auto
      show ?thesis unfolding prevt_def e by simp
    qed
    have "distr (inc_prod 0 {0}) borel (\<lambda>w. w 0)
        = distr (Pi\<^sub>M {0 :: real} (\<lambda>u. gauss_measure (u - prevt 0 {0} u)))
          (gauss_measure (0 - prevt 0 {0} 0)) (\<lambda>w. w 0)"
      by (intro distr_cong refl) (simp_all add: inc_prod_def)
    also have "\<dots> = gauss_measure (0 - prevt 0 {0 :: real} 0)"
      by (rule PPS.PiM_component) simp
    finally show ?thesis by (simp add: p0)
  qed
  finally show ?thesis .
qed

lemma wiener_pre_start: "AE \<omega> in wiener_pre. \<omega> 0 = 0"
proof -
  have cm: "(\<lambda>\<omega>. \<omega> (0::real)) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    by (rule measurable_coord) simp
  have "emeasure wiener_pre {\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0}
      = emeasure wiener_pre ((\<lambda>\<omega>. \<omega> 0) -` (UNIV - {0})
        \<inter> space wiener_pre)"
    by (intro arg_cong2[where f = emeasure] refl) auto
  also have "\<dots> = emeasure (distr wiener_pre borel (\<lambda>\<omega>. \<omega> 0)) (UNIV - {0})"
    by (rule emeasure_distr[symmetric, OF cm]) auto
  also have "\<dots> = emeasure (return borel (0::real)) (UNIV - {0})"
    by (simp add: wiener_pre_coord_zero gauss_measure_zero)
  also have "\<dots> = 0"
    by simp
  finally have null: "emeasure wiener_pre
      {\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0} = 0" .
  have msets: "{\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0} \<in> sets wiener_pre"
    using cm by measurable
  have "{\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0} \<in> null_sets wiener_pre"
    using null msets by (auto simp: null_sets_def)
  then show ?thesis
    by (rule AE_I') auto
qed

subsection \<open>The fourth-moment bound\<close>

lemma wiener_pre_moment4:
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "(\<integral>\<^sup>+\<omega>. ennreal (\<bar>\<omega> t - \<omega> s\<bar> powr 4) \<partial>wiener_pre)
       = ennreal (3 * (t - s)\<^sup>2)"
proof -
  have t0: "0 \<le> t" using s st by simp
  have inc_meas: "(\<lambda>\<omega>. \<omega> t - \<omega> s) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    by (intro borel_measurable_diff measurable_coord) (use s t0 in auto)
  have "(\<integral>\<^sup>+\<omega>. ennreal (\<bar>\<omega> t - \<omega> s\<bar> powr 4) \<partial>wiener_pre)
      = (\<integral>\<^sup>+y. ennreal (\<bar>y\<bar> powr 4)
        \<partial>distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s))"
    by (rule nn_integral_distr[symmetric, OF inc_meas]) simp
  also have "\<dots> = (\<integral>\<^sup>+y. ennreal (\<bar>y\<bar> powr 4) \<partial>gauss_measure (t - s))"
    by (simp add: wiener_pre_increment[OF s st])
  also have "\<dots> = (\<integral>\<^sup>+y. ennreal (y ^ 4) \<partial>gauss_measure (t - s))"
    by (intro nn_integral_cong)
      (simp add: power_abs zero_le_even_power)
  also have "\<dots> = ennreal (3 * (t - s)\<^sup>2)"
    using st by (intro gauss_measure_fourth_moment_nn) simp
  finally show ?thesis .
qed

section \<open>Independent increments\<close>

text \<open>Over a strictly increasing list of times, the increment vector of the
  coordinate process is --- modulo the cumulative-sum isomorphism --- a
  coordinate selection from the independent increment product, hence its
  components are independent.\<close>

lemma sorted_wrt_less_nth_iff:
  fixes l :: "'a :: linorder list"
  assumes l: "sorted_wrt (<) l" and k: "k < length l" and j: "j < length l"
  shows "l ! j < l ! k \<longleftrightarrow> j < k"
proof
  assume "j < k" then show "l ! j < l ! k"
    using l k by (intro sorted_wrt_nth_less) auto
next
  assume lt: "l ! j < l ! k"
  have "\<not> k \<le> j"
  proof
    assume kj: "k \<le> j"
    have "l ! k \<le> l ! j"
      by (rule sorted_nth_mono[OF strict_sorted_imp_sorted[OF l] kj j])
    with lt show False by (meson leD)
  qed
  then show "j < k" by simp
qed

lemma sorted_wrt_less_set_take:
  fixes l :: "'a :: linorder list"
  assumes l: "sorted_wrt (<) l" and k: "k < length l"
  shows "{v \<in> set l. v < l ! k} = set (take k l)"
proof (intro equalityI subsetI)
  fix v assume "v \<in> {v \<in> set l. v < l ! k}"
  then obtain j where j: "j < length l" "v = l ! j" "l ! j < l ! k"
    by (auto simp: in_set_conv_nth)
  have jk: "j < k"
    using sorted_wrt_less_nth_iff[OF l k j(1)] j(3) by simp
  have "take k l ! j = l ! j"
    using jk by (rule nth_take)
  moreover have "j < length (take k l)"
    using jk k j(1) by simp
  ultimately show "v \<in> set (take k l)"
    using j(2) by (metis nth_mem)
next
  fix v assume "v \<in> set (take k l)"
  then obtain j where j: "j < length (take k l)" "take k l ! j = v"
    by (metis in_set_conv_nth)
  have jk: "j < k" and jl: "j < length l"
    using j(1) k by auto
  have vj: "v = l ! j"
    using j(2) nth_take[OF jk, of l] by simp
  have "v \<in> set l"
    using jl vj by simp
  moreover have "v < l ! k"
    using sorted_wrt_less_nth_iff[OF l k jl] jk vj by simp
  ultimately show "v \<in> {v \<in> set l. v < l ! k}" by blast
qed

lemma sorted_wrt_less_Max_last:
  "sorted_wrt (<) xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Max (set xs) = last xs"
proof (induction xs)
  case (Cons a xs)
  show ?case
  proof (cases "xs = []")
    case True then show ?thesis by simp
  next
    case False
    have hd: "a < hd xs"
      using Cons.prems False by (cases xs) auto
    have "a \<le> Max (set xs)"
      by (meson False Max_ge List.finite_set dual_order.trans hd
          hd_in_set less_imp_le)
    then have "Max (set (a # xs)) = Max (set xs)"
      using False by (simp add: max_absorb2)
    also have "\<dots> = last xs"
      using Cons False by simp
    finally show ?thesis using False by simp
  qed
qed simp

theorem bm_increments_indep:
  assumes l: "sorted_wrt (<) l" and l0: "set l \<subseteq> {0..}"
    and len: "2 \<le> length l"
  shows "prob_space.indep_vars wiener_pre (\<lambda>_. borel)
    (\<lambda>k \<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))) {1..<length l}"
proof -
  define n where "n = length l"
  define J where "J = set l"
  define K where "K = {1..<n}"
  have finJ: "finite J" by (simp add: J_def)
  have J0: "J \<subseteq> {0..}" using l0 by (simp add: J_def)
  have n2: "2 \<le> n" using len by (simp add: n_def)
  have Kne: "K \<noteq> {}" using n2 by (auto simp: K_def)
  have distinct_l: "distinct l"
    using l by (simp add: strict_sorted_iff)
  have kn: "\<And>k. k \<in> K \<Longrightarrow> k < length l" and
    k0: "\<And>k. k \<in> K \<Longrightarrow> 0 < k"
    by (auto simp: K_def n_def)
  have lkJ: "\<And>k. k \<in> K \<Longrightarrow> l ! k \<in> J"
    unfolding J_def by (intro nth_mem kn)
  have lk1J: "l ! (k - 1) \<in> J" if k: "k \<in> K" for k
    unfolding J_def using kn[OF k] by (intro nth_mem) simp
  have gap: "l ! (k - 1) < l ! k" if k: "k \<in> K" for k
    using k0[OF k] kn[OF k] by (intro sorted_wrt_nth_less[OF l]) auto
  have lk0: "\<And>k. k \<in> K \<Longrightarrow> 0 \<le> l ! (k - 1)"
    using lk1J J0 by auto
  have below: "\<And>k. k \<in> K \<Longrightarrow> {v \<in> J. v < l ! k} = set (take k l)"
    unfolding J_def by (intro sorted_wrt_less_set_take[OF l] kn)
  have take_ne: "take k l \<noteq> []" if k: "k \<in> K" for k
    using k0[OF k] kn[OF k] by fastforce
  have Max_take: "\<And>k. k \<in> K \<Longrightarrow> Max (set (take k l)) = l ! (k - 1)"
  proof -
    fix k assume k: "k \<in> K"
    have "Max (set (take k l)) = last (take k l)"
      using l by (intro sorted_wrt_less_Max_last sorted_wrt_take take_ne k)
    also have "\<dots> = l ! (k - 1)"
      using kn[OF k] k0[OF k] take_ne[OF k]
      by (simp add: last_conv_nth min_def)
    finally show "Max (set (take k l)) = l ! (k - 1)" .
  qed
  have bound_take: "\<And>k v. k \<in> K \<Longrightarrow> v \<in> set (take k l) \<Longrightarrow> v \<le> l ! (k - 1)"
    using Max_take by (metis List.finite_set Max_ge)
  have prevt_lk: "\<And>k. k \<in> K \<Longrightarrow> prevt 0 J (l ! k) = l ! (k - 1)"
  proof -
    fix k assume k: "k \<in> K"
    have "prevt 0 J (l ! k) = Max (insert 0 (set (take k l)))"
      by (simp add: prevt_def below[OF k])
    also have "\<dots> = max 0 (Max (set (take k l)))"
      using take_ne[OF k] by simp
    also have "\<dots> = l ! (k - 1)"
      using lk0[OF k] by (simp add: Max_take[OF k] max_absorb2)
    finally show "prevt 0 J (l ! k) = l ! (k - 1)" .
  qed
  let ?V = "\<lambda>g. \<lambda>k\<in>K. g (l ! k) - g (l ! (k - 1))"
  let ?U = "\<lambda>\<omega>. \<lambda>k\<in>K. \<omega> (l ! k) - \<omega> (l ! (k - 1))"
  have Vmeas: "?V \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M K (\<lambda>_. (borel :: real measure))"
    by (intro measurable_restrict borel_measurable_diff
        measurable_component_singleton lkJ lk1J)
  have step1: "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
      = distr (bm_fdd J) (Pi\<^sub>M K (\<lambda>_. borel)) ?V"
  proof -
    have restr_comp: "(\<lambda>k\<in>K. x (l ! k) - x (l ! (k - 1)))
        = (\<lambda>k\<in>K. restrict x J (l ! k) - restrict x J (l ! (k - 1)))"
      for x :: "real \<Rightarrow> real"
    proof (rule restrict_ext)
      fix k assume k: "k \<in> K"
      show "x (l ! k) - x (l ! (k - 1))
          = restrict x J (l ! k) - restrict x J (l ! (k - 1))"
        using lkJ[OF k] lk1J[OF k] by simp
    qed
    have "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
        = distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) (?V \<circ> (\<lambda>f. restrict f J))"
    proof (intro distr_cong refl)
      fix x assume "x \<in> space wiener_pre"
      show "?U x = (?V \<circ> (\<lambda>f. restrict f J)) x"
        unfolding comp_def by (rule restr_comp)
    qed
    also have "\<dots> = distr (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
        (\<lambda>f. restrict f J)) (Pi\<^sub>M K (\<lambda>_. borel)) ?V"
      by (rule distr_distr[symmetric, OF Vmeas
          measurable_restrict_wiener_pre[OF J0]])
    also have "\<dots> = distr (bm_fdd J) (Pi\<^sub>M K (\<lambda>_. borel)) ?V"
      by (simp add: wiener_pre_marginal[OF finJ J0])
    finally show ?thesis .
  qed
  have step2: "distr (bm_fdd J) (Pi\<^sub>M K (\<lambda>_. borel)) ?V
      = distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (?V \<circ> csum J)"
    unfolding bm_fdd_def
    by (rule distr_distr[OF Vmeas measurable_csum_inc_prod])
  have tele: "csum J w (l ! k) - csum J w (l ! (k - 1)) = w (l ! k)"
    if k: "k \<in> K" for k and w :: "real \<Rightarrow> real"
  proof -
    have subs: "{u \<in> J. u \<le> l ! (k - 1)} \<subseteq> {u \<in> J. u \<le> l ! k}"
      using gap[OF k] by auto
    have ddiff: "{u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)} = {l ! k}"
    proof (intro equalityI subsetI)
      fix u assume "u \<in> {u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)}"
      then have u: "u \<in> J" "u \<le> l ! k" "\<not> u \<le> l ! (k - 1)" by auto
      have "u = l ! k"
      proof (rule ccontr)
        assume "u \<noteq> l ! k"
        with u have "u < l ! k" by simp
        with u below[OF k] have "u \<in> set (take k l)" by blast
        with bound_take[OF k] u show False by auto
      qed
      then show "u \<in> {l ! k}" by simp
    next
      fix u assume "u \<in> {l ! k}"
      then show "u \<in> {u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)}"
        using lkJ[OF k] gap[OF k] by auto
    qed
    have "csum J w (l ! k) - csum J w (l ! (k - 1))
        = (\<Sum>u\<in>{u \<in> J. u \<le> l ! k}. w u)
          - (\<Sum>u\<in>{u \<in> J. u \<le> l ! (k - 1)}. w u)"
      using lkJ[OF k] lk1J[OF k] by (simp add: csum_def)
    also have "\<dots>
        = (\<Sum>u\<in>{u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)}. w u)"
      using finJ subs by (subst sum_diff) auto
    also have "\<dots> = w (l ! k)"
      unfolding ddiff by simp
    finally show ?thesis .
  qed
  have tele_vec: "(\<lambda>k\<in>K. csum J w (l ! k) - csum J w (l ! (k - 1)))
      = (\<lambda>k\<in>K. w (l ! k))" for w :: "real \<Rightarrow> real"
  proof (rule restrict_ext)
    fix k assume k: "k \<in> K"
    show "csum J w (l ! k) - csum J w (l ! (k - 1)) = w (l ! k)"
      by (rule tele[OF k])
  qed
  have step3: "distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (?V \<circ> csum J)
      = distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (\<lambda>w. \<lambda>k\<in>K. w (l ! k))"
  proof (intro distr_cong refl)
    fix w assume "w \<in> space (inc_prod 0 J)"
    show "(?V \<circ> csum J) w = (\<lambda>w. \<lambda>k\<in>K. w (l ! k)) w"
      unfolding comp_def by (rule tele_vec)
  qed
  have inj: "inj_on (\<lambda>k. l ! k) K"
    using distinct_l kn by (intro inj_on_nth) auto
  have step4: "distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (\<lambda>w. \<lambda>k\<in>K. w (l ! k))
      = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - l ! (k - 1)))"
  proof -
    have "distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (\<lambda>w. \<lambda>k\<in>K. w (l ! k))
        = distr (Pi\<^sub>M J (\<lambda>u. gauss_measure (u - prevt 0 J u)))
          (Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - prevt 0 J (l ! k))))
          (\<lambda>w. \<lambda>k\<in>K. w (l ! k))"
      by (intro distr_cong refl)
        (simp_all add: inc_prod_def cong: sets_PiM_cong)
    also have "\<dots> = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - prevt 0 J (l ! k)))"
      by (intro distr_PiM_reindex prob_space_gauss_measure inj)
        (auto simp: lkJ)
    also have "\<dots> = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - l ! (k - 1)))"
      by (intro PiM_cong refl) (simp add: prevt_lk)
    finally show ?thesis .
  qed
  have comp_distr: "distr wiener_pre borel
      (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1)))
      = gauss_measure (l ! k - l ! (k - 1))" if k: "k \<in> K" for k
    using lk0[OF k] gap[OF k]
    by (intro wiener_pre_increment) (auto intro: less_imp_le)
  have rv: "\<And>k. k \<in> K \<Longrightarrow>
      (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))) \<in> wiener_pre \<rightarrow>\<^sub>M borel"
    using lkJ lk1J J0
    by (intro borel_measurable_diff measurable_coord) auto
  have "W.indep_vars (\<lambda>_. borel)
      (\<lambda>k \<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))) K"
  proof (subst W.indep_vars_iff_distr_eq_PiM'[OF Kne rv])
    have "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
        = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - l ! (k - 1)))"
      unfolding step1 step2 step3 step4 by (rule refl)
    also have "\<dots> = Pi\<^sub>M K (\<lambda>k. distr wiener_pre borel
        (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))))"
    proof (rule PiM_cong[OF refl])
      fix k assume k: "k \<in> K"
      show "gauss_measure (l ! k - l ! (k - 1))
          = distr wiener_pre borel (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1)))"
        by (rule comp_distr[OF k, symmetric])
    qed
    finally show "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
        = Pi\<^sub>M K (\<lambda>k. distr wiener_pre borel
          (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))))" .
  qed
  then show ?thesis by (simp add: K_def n_def)
qed

end
