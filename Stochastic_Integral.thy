(*
  Title:   Stochastic_Integral.thy
  Content: Stochastic integration, layer 1: the integral against a
           square-integrable martingale for predictable integrands in
           discrete time (the martingale transform), and Ito's formula for
           the quadratic test function of Example 3.1.

  This is the first layer of the stochastic calculus that
  arXiv:2512.17702 uses:

    * Eq. (1.1) of the paper, V(t) = V(0) + \<integral>\<^sub>0\<^sup>t \<theta>(s) \<bullet> d\<mu>(s), becomes the
      genuine integral mtrans_vec of the strategy \<theta> against the market
      martingale, and is proved to be a martingale (theorem
      martingale_mtrans_vec) -- no assumption about stochastic
      integration is used;

    * Ito's formula for the quadratic test function w of Example 3.1 is
      the THEOREM ito_discrete_quadratic:

        w(X\<^sub>n) = w(X\<^sub>0) + \<Sum>\<^sub>k<\<^sub>n \<nabla>w(X\<^sub>k) \<bullet> \<Delta>X\<^sub>k - [X]\<^sub>n/(n-k),

      the discrete-time form of  dw(X) = \<nabla>w(X) \<bullet> dX + \<onehalf> tr(\<nabla>\<^sup>2w a) dt;

    * consequently the relative value process dV of
      Relative_Arbitrage_Discrete, which was DEFINED there, is now
      identified as the value process of the gradient strategy in the
      sense of Eq. (1.1) (theorem dV_eq_value_process).

  Still missing for the continuous-time paper: the L\<^sup>2 closure of the
  simple integrands, quadratic variation of a continuous martingale
  (Doob--Meyer), and Ito's formula for general C\<^sup>2 functions.
*)

theory Stochastic_Integral
  imports Relative_Arbitrage_Discrete
begin

section \<open>The integral of a predictable integrand (martingale transform)\<close>

definition mtrans ::
  "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "mtrans H X n \<omega> = (\<Sum>k<n. H k \<omega> * (X (Suc k) \<omega> - X k \<omega>))"

lemma mtrans_fun: "mtrans H X n = (\<lambda>\<omega>. \<Sum>k<n. H k \<omega> * (X (Suc k) \<omega> - X k \<omega>))"
  by (rule ext) (simp add: mtrans_def)

lemma mtrans_zero [simp]: "mtrans H X 0 \<omega> = 0"
  by (simp add: mtrans_def)

lemma mtrans_Suc:
  "mtrans H X (Suc n) \<omega> = mtrans H X n \<omega> + H n \<omega> * (X (Suc n) \<omega> - X n \<omega>)"
  by (simp add: mtrans_def)

text \<open>The integrands: predictable (adapted at the left end point of each
  step) and square-integrable, which is what the Cauchy--Schwarz bound
  needs for the integral to be defined.\<close>

locale discrete_integrand = sq_int_martingale M F X
  for M :: "'a measure" and F and X :: "nat \<Rightarrow> 'a \<Rightarrow> real" +
  fixes H :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes H_meas_F: "\<And>n. H n \<in> borel_measurable (F n)"
    and H_sq_integrable: "\<And>n. integrable M (\<lambda>\<omega>. (H n \<omega>)\<^sup>2)"
begin

lemma H_meas [measurable]: "H n \<in> borel_measurable M"
proof -
  have "subalgebra M (F n)"
    by (intro subalgebras) simp
  from measurable_from_subalg[OF this H_meas_F] show ?thesis .
qed

lemma incr_prod_integrable:
  "integrable M (\<lambda>\<omega>. H n \<omega> * (X (Suc n) \<omega> - X n \<omega>))"
  by (rule integrable_prod_of_squares[OF H_sq_integrable incr_sq_integrable])
    measurable

lemma mtrans_meas_F: "mtrans H X n \<in> borel_measurable (F n)"
  unfolding mtrans_fun
proof (intro borel_measurable_sum)
  fix k assume k: "k \<in> {..<n}"
  have 1: "H k \<in> borel_measurable (F n)"
    using H_meas_F[of k] k borel_measurable_mono[of k n] by auto
  have 2: "X (Suc k) \<in> borel_measurable (F n)"
    using k by (intro X_measurable_F) auto
  have 3: "X k \<in> borel_measurable (F n)"
    using k by (intro X_measurable_F) auto
  show "(\<lambda>\<omega>. H k \<omega> * (X (Suc k) \<omega> - X k \<omega>)) \<in> borel_measurable (F n)"
    using 1 2 3 by measurable
qed

lemma mtrans_integrable: "integrable M (mtrans H X n)"
  unfolding mtrans_fun
  by (intro Bochner_Integration.integrable_sum incr_prod_integrable)

text \<open>The integral is a martingale: the discrete-time content of ``the
  stochastic integral of a predictable integrand against a martingale is
  a martingale''.\<close>

theorem martingale_mtrans: "martingale M F 0 (mtrans H X)"
proof (rule martingale_of_cond_exp_diff_Suc_eq_zero)
  show "adapted_process M F 0 (mtrans H X)"
  proof (unfold_locales)
    fix i :: nat assume "0 \<le> i"
    show "mtrans H X i \<in> borel_measurable (F i)"
      by (rule mtrans_meas_F)
  qed
  show "\<And>i. integrable M (mtrans H X i)"
    by (rule mtrans_integrable)
next
  fix i :: nat
  have fun_eq: "(\<lambda>\<omega>. mtrans H X (Suc i) \<omega> - mtrans H X i \<omega>)
      = (\<lambda>\<omega>. H i \<omega> * (X (Suc i) \<omega> - X i \<omega>))"
    by (rule ext) (simp add: mtrans_Suc)
  have pull: "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. H i \<omega> * (X (Suc i) \<omega> - X i \<omega>)) \<omega>
      = H i \<omega> * cond_exp M (F i) (\<lambda>\<omega>. X (Suc i) \<omega> - X i \<omega>) \<omega>"
    by (intro cond_exp_measurable_mult(2) incr_prod_integrable
        incr_integrable H_meas_F)
  have zero: "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. X (Suc i) \<omega> - X i \<omega>) \<omega> = 0"
    by (rule Mg.cond_exp_diff_eq_zero) auto
  from pull zero
  show "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. mtrans H X (Suc i) \<omega> - mtrans H X i \<omega>) \<omega> = 0"
    unfolding fun_eq by eventually_elim simp
qed

end

section \<open>The vector integral of Eq. (1.1)\<close>

definition mtrans_vec ::
  "(nat \<Rightarrow> 'a \<Rightarrow> real^'n) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real^'n) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "mtrans_vec H X n \<omega> = (\<Sum>k<n. (H k \<omega>) \<bullet> (X (Suc k) \<omega> - X k \<omega>))"

lemma mtrans_vec_fun:
  "mtrans_vec H X n = (\<lambda>\<omega>. \<Sum>k<n. (H k \<omega>) \<bullet> (X (Suc k) \<omega> - X k \<omega>))"
  by (rule ext) (simp add: mtrans_vec_def)

lemma mtrans_vec_zero [simp]: "mtrans_vec H X 0 \<omega> = 0"
  by (simp add: mtrans_vec_def)

lemma mtrans_vec_Suc:
  "mtrans_vec H X (Suc n) \<omega>
     = mtrans_vec H X n \<omega> + (H n \<omega>) \<bullet> (X (Suc n) \<omega> - X n \<omega>)"
  by (simp add: mtrans_vec_def)

lemma inner_eq_sum_components:
  fixes u v :: "real^'n::finite"
  shows "u \<bullet> v = (\<Sum>i\<in>UNIV. (u $ i) * (v $ i))"
  by (simp add: inner_vec_def)

locale discrete_vec_integrand = discrete_vec_martingale M F X
  for M :: "'a measure" and F
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite" +
  fixes H :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n"
  assumes H_comp_meas_F: "\<And>n i. (\<lambda>\<omega>. H n \<omega> $ i) \<in> borel_measurable (F n)"
    and H_comp_sq_integrable:
      "\<And>n i. integrable M (\<lambda>\<omega>. (H n \<omega> $ i)\<^sup>2)"
begin

lemma H_comp_meas [measurable]: "(\<lambda>\<omega>. H n \<omega> $ i) \<in> borel_measurable M"
proof -
  have "subalgebra M (F n)"
    by (intro subalgebras) simp
  from measurable_from_subalg[OF this H_comp_meas_F] show ?thesis .
qed

lemma comp_incr_prod_integrable:
  "integrable M (\<lambda>\<omega>. (H n \<omega> $ i) * (X (Suc n) \<omega> $ i - X n \<omega> $ i))"
  by (rule integrable_prod_of_squares[OF H_comp_sq_integrable
        C.incr_sq_integrable]) measurable

lemma vec_incr_prod_integrable:
  "integrable M (\<lambda>\<omega>. (H n \<omega>) \<bullet> (X (Suc n) \<omega> - X n \<omega>))"
proof -
  have eq: "(\<lambda>\<omega>. (H n \<omega>) \<bullet> (X (Suc n) \<omega> - X n \<omega>))
      = (\<lambda>\<omega>. \<Sum>i\<in>UNIV. (H n \<omega> $ i) * (X (Suc n) \<omega> $ i - X n \<omega> $ i))"
    by (rule ext) (simp add: inner_eq_sum_components)
  show ?thesis
    unfolding eq
    by (intro Bochner_Integration.integrable_sum comp_incr_prod_integrable)
qed

lemma mtrans_vec_meas_F: "mtrans_vec H X n \<in> borel_measurable (F n)"
  unfolding mtrans_vec_fun
proof (intro borel_measurable_sum)
  fix k assume k: "k \<in> {..<n}"
  have H': "(\<lambda>\<omega>. H k \<omega> $ i) \<in> borel_measurable (F n)" for i
    using H_comp_meas_F[of k i] k borel_measurable_mono[of k n] by auto
  have X1: "(\<lambda>\<omega>. X (Suc k) \<omega> $ i) \<in> borel_measurable (F n)" for i
    using k by (intro C.X_measurable_F) auto
  have X2: "(\<lambda>\<omega>. X k \<omega> $ i) \<in> borel_measurable (F n)" for i
    using k by (intro C.X_measurable_F) auto
  have "(\<lambda>\<omega>. \<Sum>i\<in>UNIV. (H k \<omega> $ i) * (X (Suc k) \<omega> $ i - X k \<omega> $ i))
      \<in> borel_measurable (F n)"
    using H' X1 X2 by measurable
  then show "(\<lambda>\<omega>. (H k \<omega>) \<bullet> (X (Suc k) \<omega> - X k \<omega>)) \<in> borel_measurable (F n)"
    by (simp add: inner_eq_sum_components)
qed

lemma mtrans_vec_integrable: "integrable M (mtrans_vec H X n)"
  unfolding mtrans_vec_fun
  by (intro Bochner_Integration.integrable_sum vec_incr_prod_integrable)

text \<open>Eq. (1.1) is a martingale: the value process of any predictable,
  square-integrable strategy is a martingale under every market law of the
  class.\<close>

theorem martingale_mtrans_vec: "martingale M F 0 (mtrans_vec H X)"
proof (rule martingale_of_cond_exp_diff_Suc_eq_zero)
  show "adapted_process M F 0 (mtrans_vec H X)"
  proof (unfold_locales)
    fix i :: nat assume "0 \<le> i"
    show "mtrans_vec H X i \<in> borel_measurable (F i)"
      by (rule mtrans_vec_meas_F)
  qed
  show "\<And>i. integrable M (mtrans_vec H X i)"
    by (rule mtrans_vec_integrable)
next
  fix i :: nat
  have fun_eq: "(\<lambda>\<omega>. mtrans_vec H X (Suc i) \<omega> - mtrans_vec H X i \<omega>)
      = (\<lambda>\<omega>. \<Sum>j\<in>UNIV. (H i \<omega> $ j) * (X (Suc i) \<omega> $ j - X i \<omega> $ j))"
    by (rule ext) (simp add: mtrans_vec_Suc inner_eq_sum_components)
  have comp_zero: "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. (H i \<omega> $ j)
        * (X (Suc i) \<omega> $ j - X i \<omega> $ j)) \<omega> = 0" for j
  proof -
    have pull: "AE \<omega> in M.
        cond_exp M (F i) (\<lambda>\<omega>. (H i \<omega> $ j)
          * (X (Suc i) \<omega> $ j - X i \<omega> $ j)) \<omega>
        = (H i \<omega> $ j) * cond_exp M (F i)
            (\<lambda>\<omega>. X (Suc i) \<omega> $ j - X i \<omega> $ j) \<omega>"
      by (intro cond_exp_measurable_mult(2) comp_incr_prod_integrable
          C.incr_integrable H_comp_meas_F)
    have zero: "AE \<omega> in M.
        cond_exp M (F i) (\<lambda>\<omega>. X (Suc i) \<omega> $ j - X i \<omega> $ j) \<omega> = 0"
      by (rule C.Mg.cond_exp_diff_eq_zero) auto
    from pull zero show ?thesis
      by eventually_elim simp
  qed
  have split: "AE \<omega> in M.
      cond_exp M (F i) (\<lambda>\<omega>. \<Sum>j\<in>(UNIV :: 'n set). (H i \<omega> $ j)
          * (X (Suc i) \<omega> $ j - X i \<omega> $ j)) \<omega>
      = (\<Sum>j\<in>(UNIV :: 'n set). cond_exp M (F i)
          (\<lambda>\<omega>. (H i \<omega> $ j) * (X (Suc i) \<omega> $ j - X i \<omega> $ j)) \<omega>)"
    by (intro cond_exp_sum comp_incr_prod_integrable)
  have all_zero: "AE \<omega> in M. \<forall>j\<in>(UNIV :: 'n set). cond_exp M (F i)
      (\<lambda>\<omega>. (H i \<omega> $ j) * (X (Suc i) \<omega> $ j - X i \<omega> $ j)) \<omega> = 0"
    by (rule AE_finite_allI) (auto intro: comp_zero)
  from split all_zero
  show "AE \<omega> in M. cond_exp M (F i)
      (\<lambda>\<omega>. mtrans_vec H X (Suc i) \<omega> - mtrans_vec H X i \<omega>) \<omega> = 0"
    unfolding fun_eq by eventually_elim simp
qed

end

section \<open>Ito's formula for the quadratic test function of Example 3.1\<close>

text \<open>The test function \<open>w(y) = (r\<^sup>2 - |y|\<^sup>2)/(n-k)\<close> of Eq. (3.9) and its
  gradient.  Inside the ball \<open>w\<close> coincides with the value function
  \<open>ball_v\<close>.\<close>

definition qw :: "real \<Rightarrow> nat \<Rightarrow> real^'n \<Rightarrow> real" where
  "qw r k y = (r\<^sup>2 - y \<bullet> y) / real (CARD('n) - k)"

definition grad_qw :: "nat \<Rightarrow> real^'n \<Rightarrow> real^'n" where
  "grad_qw k y = (- (2 / real (CARD('n) - k))) *\<^sub>R y"

lemma qw_eq_ball_v:
  fixes y :: "real^'n::finite"
  assumes "y \<bullet> y \<le> r\<^sup>2"
  shows "qw r k y = ball_v r k y"
  using assms by (simp add: qw_def ball_v_def max_def)

lemma grad_qw_eq_ball_v_gradient:
  fixes y :: "real^'n::finite"
  assumes "norm y < r" and "k < CARD('n)"
  shows "((ball_v r k) has_derivative (\<lambda>h. grad_qw k y \<bullet> h)) (at y)"
  unfolding grad_qw_def by (rule ball_v_gradient[OF assms])

text \<open>The one-step Ito expansion: the increment of \<open>w\<close> is the gradient term
  plus the second-order correction, with no remainder because \<open>w\<close> is
  quadratic.\<close>

lemma qw_step:
  fixes y d :: "real^'n::finite"
  shows "qw r k (y + d)
     = qw r k y + grad_qw k y \<bullet> d - (d \<bullet> d) / real (CARD('n) - k)"
proof -
  define c where "c = real (CARD('n) - k)"
  have exp: "(y + d) \<bullet> (y + d) = y \<bullet> y + 2 * (y \<bullet> d) + d \<bullet> d"
    by (simp add: inner_add_left inner_add_right inner_commute)
  have "qw r k (y + d) = (r\<^sup>2 - (y \<bullet> y + 2 * (y \<bullet> d) + d \<bullet> d)) / c"
    unfolding qw_def c_def by (simp add: exp)
  also have "\<dots> = (r\<^sup>2 - y \<bullet> y) / c - (2 * (y \<bullet> d)) / c - (d \<bullet> d) / c"
    by (simp add: add_divide_distrib diff_divide_distrib)
  also have "\<dots> = qw r k y + grad_qw k y \<bullet> d - (d \<bullet> d) / c"
    unfolding qw_def grad_qw_def c_def
    by (simp add: inner_scaleR_left)
  finally show ?thesis
    by (simp add: c_def)
qed

lemma qvar_vec_Suc:
  "qvar_vec X (Suc n) \<omega>
     = qvar_vec X n \<omega> + (X (Suc n) \<omega> - X n \<omega>) \<bullet> (X (Suc n) \<omega> - X n \<omega>)"
  by (simp add: qvar_vec_def)

text \<open>Ito's formula for \<open>w\<close> in discrete time.  This is the identity that
  the continuous-time development of Relative\_Arbitrage\_Ito can only
  postulate (\<open>sint_def\<close> there); here it is a theorem, with the stochastic
  integral of Eq. (1.1) on the right-hand side.\<close>

theorem ito_discrete_quadratic:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  shows "qw r k (X n \<omega>)
     = qw r k (X 0 \<omega>)
       + mtrans_vec (\<lambda>m \<omega>. grad_qw k (X m \<omega>)) X n \<omega>
       - qvar_vec X n \<omega> / real (CARD('n) - k)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have step: "qw r k (X (Suc n) \<omega>) = qw r k (X n \<omega>)
      + grad_qw k (X n \<omega>) \<bullet> (X (Suc n) \<omega> - X n \<omega>)
      - ((X (Suc n) \<omega> - X n \<omega>) \<bullet> (X (Suc n) \<omega> - X n \<omega>))
        / real (CARD('n) - k)"
    using qw_step[of r k "X n \<omega>" "X (Suc n) \<omega> - X n \<omega>"] by simp
  show ?case
    using Suc step
    by (simp add: mtrans_vec_Suc qvar_vec_Suc add_divide_distrib)
qed

section \<open>The relative value process of Eq. (1.1) for the gradient strategy\<close>

text \<open>The gradient strategy \<open>\<theta>\<^sub>m = \<nabla>w(X\<^sub>m)\<close> is an admissible integrand for
  every square-integrable vector martingale.\<close>

sublocale discrete_vec_martingale
  \<subseteq> G: discrete_vec_integrand M F X "\<lambda>m \<omega>. grad_qw k (X m \<omega>)"
proof -
  have parent: "discrete_vec_martingale M F X"
    by unfold_locales
  show "discrete_vec_integrand M F X (\<lambda>m \<omega>. grad_qw k (X m \<omega>))"
  proof (intro discrete_vec_integrand.intro[OF parent]
      discrete_vec_integrand_axioms.intro)
    fix n :: nat and i :: 'n
    show "(\<lambda>\<omega>. grad_qw k (X n \<omega>) $ i) \<in> borel_measurable (F n)"
    proof -
      have eq: "(\<lambda>\<omega>. grad_qw k (X n \<omega>) $ i)
          = (\<lambda>\<omega>. (- (2 / real (CARD('n) - k))) * (X n \<omega> $ i))"
        by (rule ext) (simp add: grad_qw_def)
      show ?thesis
        unfolding eq using C.X_measurable_F[of n n] by measurable
    qed
    show "integrable M (\<lambda>\<omega>. (grad_qw k (X n \<omega>) $ i)\<^sup>2)"
    proof -
      have eq: "(\<lambda>\<omega>. (grad_qw k (X n \<omega>) $ i)\<^sup>2)
          = (\<lambda>\<omega>. (2 / real (CARD('n) - k))\<^sup>2 * (X n \<omega> $ i)\<^sup>2)"
        by (rule ext) (simp add: grad_qw_def power2_eq_square)
      show ?thesis
        unfolding eq
        by (intro integrable_mult_right comp_sq_integrable)
    qed
  qed
qed

text \<open>The value process of Eq. (1.1) for the gradient strategy: initial
  capital \<open>w(X\<^sub>0)\<close> plus the stochastic integral equals
  \<open>w(X\<^sub>n) + [X]\<^sub>n/(n-k)\<close>.\<close>

corollary ito_value_process:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  shows "qw r k (X 0 \<omega>) + mtrans_vec (\<lambda>m \<omega>. grad_qw k (X m \<omega>)) X n \<omega>
     = qw r k (X n \<omega>) + qvar_vec X n \<omega> / real (CARD('n) - k)"
  using ito_discrete_quadratic[of r k X n \<omega>] by simp

theorem (in discrete_vec_martingale) martingale_gradient_strategy:
  "martingale M F 0 (mtrans_vec (\<lambda>m \<omega>. grad_qw k (X m \<omega>)) X)"
  by (rule G.martingale_mtrans_vec)

text \<open>Consequently the process \<open>dV\<close> of Relative\_Arbitrage\_Discrete, which
  was defined there by the right-hand side of Ito's formula, IS the value
  process of the gradient strategy of Eq. (1.1) as long as the market stays
  in the ball.  The relative-arbitrage theorem of that theory therefore
  speaks about an actual trading strategy and an actual stochastic
  integral.\<close>

theorem (in discrete_volatile_market) dV_eq_value_process:
  "AE \<omega> in M. \<forall>n. n \<le> N \<longrightarrow>
     dV n \<omega> = ball_v r k x0
       + mtrans_vec (\<lambda>m \<omega>. grad_qw k (X m \<omega>)) X n \<omega>"
  using X_start X_in_ball
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof (intro allI impI)
    fix n assume n: "n \<le> N"
    have sq: "X m \<omega> \<bullet> X m \<omega> \<le> r\<^sup>2" if "m \<le> N" for m
    proof -
      have "X m \<omega> \<in> cball 0 r"
        using elim that by blast
      then have "norm (X m \<omega>) \<le> r"
        by (simp add: mem_cball dist_norm)
      then have "(norm (X m \<omega>))\<^sup>2 \<le> r\<^sup>2"
        by (intro power_mono) auto
      then show ?thesis
        by (simp add: dot_square_norm)
    qed
    have v0: "qw r k (X 0 \<omega>) = ball_v r k x0"
      using qw_eq_ball_v[OF sq[of 0]] elim by simp
    have vn: "qw r k (X n \<omega>) = ball_v r k (X n \<omega>)"
      by (rule qw_eq_ball_v[OF sq[OF n]])
    have "ball_v r k x0
        + mtrans_vec (\<lambda>m \<omega>. grad_qw k (X m \<omega>)) X n \<omega>
        = qw r k (X n \<omega>) + qvar_vec X n \<omega> / real (CARD('n) - k)"
      using ito_value_process[of r k X \<omega> n] v0 by simp
    also have "\<dots> = dV n \<omega>"
      unfolding vn dV_def by simp
    finally show "dV n \<omega> = ball_v r k x0
        + mtrans_vec (\<lambda>m \<omega>. grad_qw k (X m \<omega>)) X n \<omega>"
      by simp
  qed
qed

end
