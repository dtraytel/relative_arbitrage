(*
  Title:   Deterministic_Radius_Market.thy
  Content: Towards Example 3.1 of arXiv:2512.17702 for n - k = 1: the
           explicit trigonometric representation of the deterministic-radius
           market and its Gaussian toolkit.

  The process X_t = sqrt(|x|^2 + t) (cos(W_c(t) + phi), sin(W_c(t) + phi)),
  c(t) = ln(1 + t/|x|^2), is a martingale whose covariance is the sphere
  projection a(X) = I - X X^T/|X|^2; its radius is deterministic, so with
  the constant horizon tau = r^2 - |x|^2 it realises ball_v exactly and
  witnesses stopped_val_fn = ball_v at nonzero interior points for
  k = CARD('n) - 1.  See PLAN_THEOREM_1_1.md, item N4, for the brick
  sequence.  This theory provides bricks 1 and 2: the increment
  distribution of the product Brownian model and the characteristic
  function of gauss_measure.

  VERIFICATION NOTE: proved interactively against the running PIDE session
  (scratch with identical imports); the theory is registered in ROOT but a
  freshly started PIDE snapshots ROOT, so cross-check with the batch build.
*)

theory Deterministic_Radius_Market
  imports Brownian_Continuous
begin

section \<open>The coordinate increment of the product model is Gaussian\<close>

lemma bm_increment_distr:
  fixes i :: "'n::finite"
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s) = gauss_measure (t - s)"
proof -
  have cm: "(\<lambda>\<omega> :: 'n \<Rightarrow> real \<Rightarrow> real. \<omega> i) \<in> bm_paths \<rightarrow>\<^sub>M wiener_pre"
    unfolding bm_paths_def
    by (rule measurable_component_singleton) simp
  have inc: "(\<lambda>\<omega>' :: real \<Rightarrow> real. \<omega>' t - \<omega>' s)
      \<in> wiener_pre \<rightarrow>\<^sub>M borel"
    using s st
    by (intro borel_measurable_diff measurable_coord) auto
  have "distr (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) borel
      (\<lambda>\<omega>. \<omega> i t - \<omega> i s)
      = distr (distr bm_paths wiener_pre (\<lambda>\<omega>. \<omega> i)) borel
          (\<lambda>\<omega>'. \<omega>' t - \<omega>' s)"
    by (subst distr_distr[OF inc cm]) (simp add: o_def)
  also have "distr bm_paths wiener_pre (\<lambda>\<omega>. \<omega> i) = wiener_pre"
    by (rule bm_paths_component)
  also have "distr wiener_pre borel (\<lambda>\<omega>'. \<omega>' t - \<omega>' s)
      = gauss_measure (t - s)"
    by (rule wiener_pre_increment[OF s st])
  finally show ?thesis .
qed

section \<open>The characteristic function of \<open>gauss_measure\<close>\<close>

text \<open>Change of variables \<open>x = \<surd>v\<cdot>y\<close> reduces to the standard normal
  characteristic function of HOL-Probability.\<close>

lemma char_gauss_measure:
  assumes v: "0 < v"
  shows "char (gauss_measure v) a
      = complex_of_real (exp (- a\<^sup>2 * v / 2))"
proof -
  have sv: "0 < sqrt v" using v by simp
  have "char (gauss_measure v) a
      = (CLINT x|density lborel
          (\<lambda>x. ennreal (normal_density 0 (sqrt v) x)). iexp (a * x))"
    unfolding char_def gauss_measure_def using v by simp
  also have "\<dots> = (CLINT x|lborel.
      normal_density 0 (sqrt v) x *\<^sub>R iexp (a * x))"
    by (intro integral_density borel_measurable_normal_density)
      (auto simp: normal_density_nonneg)
  also have "\<dots> = \<bar>sqrt v\<bar> *\<^sub>R (CLINT y|lborel.
      normal_density 0 (sqrt v) (sqrt v * y)
        *\<^sub>R iexp (a * (sqrt v * y)))"
    by (rule lborel_integral_real_affine[where c = "sqrt v" and t = 0,
        simplified]) (use sv in simp)
  also have "\<dots> = (CLINT y|lborel. \<bar>sqrt v\<bar> *\<^sub>R
      (normal_density 0 (sqrt v) (sqrt v * y)
        *\<^sub>R iexp (a * (sqrt v * y))))"
    by (rule integral_scaleR_right[symmetric])
  also have "\<dots> = (CLINT y|lborel.
      std_normal_density y *\<^sub>R iexp ((a * sqrt v) * y))"
  proof (intro Bochner_Integration.integral_cong refl)
    fix y :: real
    have nd: "\<bar>sqrt v\<bar> * normal_density 0 (sqrt v) (sqrt v * y)
        = std_normal_density y"
      using sv
      by (simp add: normal_density_def std_normal_density_def
          power_mult_distrib abs_of_pos field_simps real_sqrt_mult)
    show "\<bar>sqrt v\<bar> *\<^sub>R (normal_density 0 (sqrt v) (sqrt v * y)
          *\<^sub>R iexp (a * (sqrt v * y)))
        = std_normal_density y *\<^sub>R iexp ((a * sqrt v) * y)"
      using nd by (simp add: mult.assoc mult.left_commute)
  qed
  also have "\<dots> = (CLINT y|std_normal_distribution.
      iexp ((a * sqrt v) * y))"
    by (intro integral_density[symmetric])
      (auto simp: std_normal_density_def)
  also have "\<dots> = char std_normal_distribution (a * sqrt v)"
    unfolding char_def ..
  also have "\<dots> = complex_of_real (exp (- (a * sqrt v)\<^sup>2 / 2))"
    by (simp add: char_std_normal_distribution)
  also have "(a * sqrt v)\<^sup>2 = a\<^sup>2 * v"
    using v by (simp add: power_mult_distrib)
  finally show ?thesis by simp
qed

end
