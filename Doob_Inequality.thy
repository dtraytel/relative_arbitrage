(*
  Title:   Doob_Inequality.thy
  Content: Stochastic integration, layer 3a: Doob's maximal inequality for
           discrete-time martingales.

  Neither HOL-Probability nor the AFP entry Martingales contains Doob's
  inequality, and every passage from a time grid to continuous time needs
  it (to dominate sup of |X| when approximating a stopping time).  It is
  therefore proved here from scratch:

    l * P(max of |X_k|, k <= n, >= l)  <=  E[|X_n| on that event]  <=  E[|X_n|]

  The proof is the classical first-passage decomposition: the event that the
  running maximum reaches l is the disjoint union over k <= n of the events
  "l is reached first at time k", each of which lies in F k, and on which
  |X_k| >= l; the submartingale property of |X| on sets of F k -- itself a
  consequence of conditional Jensen (cond_exp_contraction_real) -- replaces
  |X_k| by |X_n|.
*)

theory Doob_Inequality
  imports Time_Discretisation
begin

section \<open>The running maximum\<close>

definition maxabs :: "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real" where
  "maxabs Y n \<omega> = Max ((\<lambda>k. \<bar>Y k \<omega>\<bar>) ` {..n})"

lemma maxabs_ge:
  assumes "k \<le> n"
  shows "\<bar>Y k \<omega>\<bar> \<le> maxabs Y n \<omega>"
  unfolding maxabs_def using assms by (intro Max_ge) auto

lemma maxabs_ge_iff:
  "l \<le> maxabs Y n \<omega> \<longleftrightarrow> (\<exists>k\<le>n. l \<le> \<bar>Y k \<omega>\<bar>)"
proof -
  have "finite ((\<lambda>k. \<bar>Y k \<omega>\<bar>) ` {..n})" by simp
  moreover have "(\<lambda>k. \<bar>Y k \<omega>\<bar>) ` {..n} \<noteq> {}" by simp
  ultimately show ?thesis
    unfolding maxabs_def by (subst Max_ge_iff) auto
qed

lemma maxabs_nonneg: "0 \<le> maxabs Y n \<omega>"
  using maxabs_ge[of 0 n Y \<omega>] by simp

lemma maxabs_attained: "\<exists>j\<le>n. maxabs Y n \<omega> = \<bar>Y j \<omega>\<bar>"
proof -
  have "maxabs Y n \<omega> \<in> (\<lambda>k. \<bar>Y k \<omega>\<bar>) ` {..n}"
    unfolding maxabs_def by (intro Max_in) auto
  then show ?thesis by auto
qed

lemma maxabs_measurable [measurable]:
  assumes "\<And>k. Y k \<in> borel_measurable M"
  shows "maxabs Y n \<in> borel_measurable M"
  unfolding maxabs_def using assms by (intro borel_measurable_Max) auto

section \<open>Square-integrable martingales on a probability space\<close>

locale prob_sq_int_martingale = sq_int_martingale M F X
  for M :: "'a measure" and F and X :: "nat \<Rightarrow> 'a \<Rightarrow> real" +
  assumes prob_space_M: "prob_space M"
begin

sublocale P: prob_space M
  by (rule prob_space_M)

lemma sets_F_M: "A \<in> sets (F n) \<Longrightarrow> A \<in> sets M"
proof -
  assume "A \<in> sets (F n)"
  moreover have "sets (F n) \<subseteq> sets M"
    by (intro sets_F_subset) simp
  ultimately show ?thesis by blast
qed

lemma set_integrable_abs_X:
  assumes "A \<in> sets M"
  shows "set_integrable M A (\<lambda>x. \<bar>X k x\<bar>)"
  unfolding set_integrable_def
  by (intro integrable_mult_indicator assms integrable_abs X_integrable)

subsection \<open>The absolute value of a martingale is a submartingale on sets\<close>

lemma abs_set_integral_mono:
  assumes kn: "k \<le> n" and A: "A \<in> sets (F k)"
  shows "(LINT x:A|M. \<bar>X k x\<bar>) \<le> (LINT x:A|M. \<bar>X n x\<bar>)"
proof -
  have AM: "A \<in> sets M"
    using A by (rule sets_F_M)
  have int_k: "set_integrable M A (\<lambda>x. \<bar>X k x\<bar>)"
    using AM by (rule set_integrable_abs_X)
  have int_n: "set_integrable M A (\<lambda>x. \<bar>X n x\<bar>)"
    using AM by (rule set_integrable_abs_X)
  have int_ce: "set_integrable M A (cond_exp M (F k) (\<lambda>x. \<bar>X n x\<bar>))"
    unfolding set_integrable_def
    by (intro integrable_mult_indicator AM integrable_cond_exp)
  have ae: "AE x in M. \<bar>X k x\<bar> \<le> cond_exp M (F k) (\<lambda>x. \<bar>X n x\<bar>) x"
  proof -
    have mp: "AE x in M. X k x = cond_exp M (F k) (X n) x"
      using kn by (intro Mg.martingale_property) auto
    have contr: "AE x in M.
        \<bar>cond_exp M (F k) (X n) x\<bar> \<le> cond_exp M (F k) (\<lambda>x. \<bar>X n x\<bar>) x"
      using cond_exp_contraction_real[of "X n"] X_integrable by simp
    from mp contr show ?thesis
      by eventually_elim simp
  qed
  have "(LINT x:A|M. \<bar>X k x\<bar>)
      \<le> (LINT x:A|M. cond_exp M (F k) (\<lambda>x. \<bar>X n x\<bar>) x)"
    by (intro set_integral_mono_AE int_k int_ce) (use ae in auto)
  also have "\<dots> = (LINT x:A|M. \<bar>X n x\<bar>)"
    using cond_exp_set_integral[of "\<lambda>x. \<bar>X n x\<bar>" A] A by simp
  finally show ?thesis .
qed

subsection \<open>First passage above a level\<close>

definition hits :: "real \<Rightarrow> nat \<Rightarrow> 'a set" where
  "hits l k = {\<omega> \<in> space M. (\<forall>j<k. \<bar>X j \<omega>\<bar> < l) \<and> l \<le> \<bar>X k \<omega>\<bar>}"

lemma hits_sets_F: "hits l k \<in> sets (F k)"
proof -
  have sp: "space (F j) = space M" for j :: nat
    by simp
  have XM: "X j \<in> borel_measurable (F k)" if "j \<le> k" for j
    using that by (intro X_measurable_F)
  have below: "{\<omega> \<in> space M. \<bar>X j \<omega>\<bar> < l} \<in> sets (F k)" if "j \<le> k" for j
  proof -
    have "{\<omega> \<in> space (F k). \<bar>X j \<omega>\<bar> < l} \<in> sets (F k)"
      using XM[OF that] by measurable
    then show ?thesis unfolding sp .
  qed
  have above: "{\<omega> \<in> space M. l \<le> \<bar>X k \<omega>\<bar>} \<in> sets (F k)"
  proof -
    have "{\<omega> \<in> space (F k). l \<le> \<bar>X k \<omega>\<bar>} \<in> sets (F k)"
      using XM[of k] by measurable
    then show ?thesis unfolding sp .
  qed
  show ?thesis
  proof (cases k)
    case 0
    then have "hits l k = {\<omega> \<in> space M. l \<le> \<bar>X k \<omega>\<bar>}"
      unfolding hits_def by simp
    then show ?thesis
      using above by simp
  next
    case (Suc k')
    have eq: "hits l k = {\<omega> \<in> space M. l \<le> \<bar>X k \<omega>\<bar>}
        \<inter> (\<Inter>j\<in>{..<k}. {\<omega> \<in> space M. \<bar>X j \<omega>\<bar> < l})"
      unfolding hits_def using Suc by auto
    have ne: "{..<k} \<noteq> {}"
      using Suc by auto
    have "(\<Inter>j\<in>{..<k}. {\<omega> \<in> space M. \<bar>X j \<omega>\<bar> < l}) \<in> sets (F k)"
      using ne by (intro sets.finite_INT) (auto intro: below)
    with above show ?thesis
      unfolding eq by (rule sets.Int)
  qed
qed

lemma hits_sets_M: "hits l k \<in> sets M"
  using hits_sets_F by (rule sets_F_M)

lemma hits_disjoint: "disjoint_family_on (hits l) A"
  unfolding disjoint_family_on_def
proof (intro ballI impI)
  fix i j :: nat
  assume "i \<in> A" "j \<in> A" and ne: "i \<noteq> j"
  show "hits l i \<inter> hits l j = {}"
  proof (cases "i < j")
    case True
    then show ?thesis
      unfolding hits_def by auto
  next
    case False
    with ne have "j < i" by simp
    then show ?thesis
      unfolding hits_def by auto
  qed
qed

lemma hits_Union:
  "(\<Union>k\<le>n. hits l k) = {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}"
proof
  show "(\<Union>k\<le>n. hits l k) \<subseteq> {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}"
  proof
    fix \<omega> assume "\<omega> \<in> (\<Union>k\<le>n. hits l k)"
    then obtain k where k: "k \<le> n" "\<omega> \<in> hits l k" by blast
    then have "l \<le> \<bar>X k \<omega>\<bar>" "\<omega> \<in> space M"
      unfolding hits_def by auto
    with k show "\<omega> \<in> {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}"
      using maxabs_ge[of k n X \<omega>] by auto
  qed
next
  show "{\<omega> \<in> space M. l \<le> maxabs X n \<omega>} \<subseteq> (\<Union>k\<le>n. hits l k)"
  proof
    fix \<omega> assume w: "\<omega> \<in> {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}"
    then have ex: "\<exists>k\<le>n. l \<le> \<bar>X k \<omega>\<bar>"
      by (simp add: maxabs_ge_iff)
    define k where "k = (LEAST k. l \<le> \<bar>X k \<omega>\<bar>)"
    from ex obtain k0 where k0: "k0 \<le> n" "l \<le> \<bar>X k0 \<omega>\<bar>" by blast
    have kle: "l \<le> \<bar>X k \<omega>\<bar>"
      unfolding k_def using k0(2) by (rule LeastI)
    have kk0: "k \<le> k0"
      unfolding k_def using k0(2) by (rule Least_le)
    have before: "\<bar>X j \<omega>\<bar> < l" if "j < k" for j
      using that unfolding k_def by (metis not_less_Least not_le_imp_less)
    have "\<omega> \<in> hits l k"
      unfolding hits_def using w kle before by auto
    with kk0 k0(1) show "\<omega> \<in> (\<Union>k\<le>n. hits l k)"
      by auto
  qed
qed

subsection \<open>Doob's weak maximal inequality\<close>

theorem doob_maximal_inequality:
  assumes l: "0 < l"
  shows "l * P.prob {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}
     \<le> (LINT x:{\<omega> \<in> space M. l \<le> maxabs X n \<omega>}|M. \<bar>X n x\<bar>)"
proof -
  have hits_M: "hits l k \<in> sets M" for k
    by (rule hits_sets_M)
  have step: "l * P.prob (hits l k) \<le> (LINT x:hits l k|M. \<bar>X n x\<bar>)"
    if k: "k \<le> n" for k
  proof -
    have "l * P.prob (hits l k) = (LINT x:hits l k|M. l)"
      using hits_M[of k] by (subst set_integral_const) auto
    also have "\<dots> \<le> (LINT x:hits l k|M. \<bar>X k x\<bar>)"
    proof (intro set_integral_mono_AE)
      show "set_integrable M (hits l k) (\<lambda>_. l)"
        unfolding set_integrable_def
        using hits_M[of k] by (intro integrable_mult_indicator) auto
      show "set_integrable M (hits l k) (\<lambda>x. \<bar>X k x\<bar>)"
        using hits_M[of k] by (rule set_integrable_abs_X)
      show "AE x\<in>hits l k in M. l \<le> \<bar>X k x\<bar>"
        by (intro AE_I2) (auto simp: hits_def)
    qed
    also have "\<dots> \<le> (LINT x:hits l k|M. \<bar>X n x\<bar>)"
      using k hits_sets_F by (rule abs_set_integral_mono)
    finally show ?thesis .
  qed
  have "l * P.prob {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}
      = l * P.prob (\<Union>k\<le>n. hits l k)"
    by (simp add: hits_Union)
  also have "\<dots> = l * (\<Sum>k\<le>n. P.prob (hits l k))"
    using hits_disjoint hits_M
    by (subst P.finite_measure_finite_Union) auto
  also have "\<dots> = (\<Sum>k\<le>n. l * P.prob (hits l k))"
    by (simp add: sum_distrib_left)
  also have "\<dots> \<le> (\<Sum>k\<le>n. (LINT x:hits l k|M. \<bar>X n x\<bar>))"
    by (intro sum_mono step) simp
  also have "\<dots> = (LINT x:(\<Union>k\<le>n. hits l k)|M. \<bar>X n x\<bar>)"
    using hits_disjoint hits_M
    by (intro set_integral_finite_Union[symmetric])
      (auto intro: set_integrable_abs_X)
  also have "\<dots> = (LINT x:{\<omega> \<in> space M. l \<le> maxabs X n \<omega>}|M. \<bar>X n x\<bar>)"
    by (simp add: hits_Union)
  finally show ?thesis .
qed

corollary doob_maximal_inequality':
  assumes l: "0 < l"
  shows "l * P.prob {\<omega> \<in> space M. l \<le> maxabs X n \<omega>} \<le> (\<integral>x. \<bar>X n x\<bar> \<partial>M)"
proof -
  have setM: "{\<omega> \<in> space M. l \<le> maxabs X n \<omega>} \<in> sets M"
  proof -
    have "(\<Union>k\<le>n. hits l k) \<in> sets M"
      by (intro sets.finite_UN) (auto intro: hits_sets_M)
    then show ?thesis
      unfolding hits_Union .
  qed
  have le: "(LINT x:{\<omega> \<in> space M. l \<le> maxabs X n \<omega>}|M. \<bar>X n x\<bar>)
      \<le> (\<integral>x. \<bar>X n x\<bar> \<partial>M)"
    unfolding set_lebesgue_integral_def
  proof (intro integral_mono)
    show "integrable M (\<lambda>x. indicat_real {\<omega> \<in> space M. l \<le> maxabs X n \<omega>} x
        *\<^sub>R \<bar>X n x\<bar>)"
      using set_integrable_abs_X[OF setM]
      by (simp add: set_integrable_def)
    show "integrable M (\<lambda>x. \<bar>X n x\<bar>)"
      by (intro integrable_abs X_integrable)
    show "indicat_real {\<omega> \<in> space M. l \<le> maxabs X n \<omega>} x *\<^sub>R \<bar>X n x\<bar>
        \<le> \<bar>X n x\<bar>" if "x \<in> space M" for x
      by (simp add: indicator_def)
  qed
  have "l * P.prob {\<omega> \<in> space M. l \<le> maxabs X n \<omega>}
      \<le> (LINT x:{\<omega> \<in> space M. l \<le> maxabs X n \<omega>}|M. \<bar>X n x\<bar>)"
    by (rule doob_maximal_inequality[OF l])
  with le show ?thesis by simp
qed

subsection \<open>Doob's \<open>L\<^sup>2\<close> maximal inequality\<close>

text \<open>The weak inequality integrates over the levels to the strong one:

    E[(max of |X_k|, k <= n)^2]  <=  4 E[X_n^2].

  The level integration is Tonelli's theorem on the product of the
  probability space with lborel, applied to the region
  \<open>0 \<le> l \<le> maxabs X n \<omega>\<close>: first with the weight \<open>2l\<close>, whose slices in
  \<open>l\<close> give the squared maximum, and then with the weight \<open>2|X n \<omega>|\<close>,
  whose slices give \<open>2|X n| maxabs X n\<close>.  The classical Cauchy--Schwarz
  step at the end is replaced by the elementary bound
  \<open>2ab \<le> 2a^2 + b^2/2\<close>, which yields the same constant \<open>4\<close>.\<close>

lemma maxabs_meas_X [measurable]: "maxabs X n \<in> borel_measurable M"
  by (intro maxabs_measurable X_measurable)

lemma maxabs_sq_le_sum: "(maxabs X n \<omega>)\<^sup>2 \<le> (\<Sum>k\<le>n. (X k \<omega>)\<^sup>2)"
proof -
  obtain j where j: "j \<le> n" and eq: "maxabs X n \<omega> = \<bar>X j \<omega>\<bar>"
    using maxabs_attained[where Y = X and n = n and \<omega> = \<omega>] by blast
  have "(maxabs X n \<omega>)\<^sup>2 = (X j \<omega>)\<^sup>2"
    unfolding eq by simp
  also have "\<dots> \<le> (\<Sum>k\<le>n. (X k \<omega>)\<^sup>2)"
    using j by (intro member_le_sum) auto
  finally show ?thesis .
qed

lemma maxabs_sq_integrable: "integrable M (\<lambda>\<omega>. (maxabs X n \<omega>)\<^sup>2)"
proof (rule Bochner_Integration.integrable_bound
    [of _ "\<lambda>\<omega>. \<Sum>k\<le>n. (X k \<omega>)\<^sup>2"])
  show "integrable M (\<lambda>\<omega>. \<Sum>k\<le>n. (X k \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_sum sq_integrable)
  show "(\<lambda>\<omega>. (maxabs X n \<omega>)\<^sup>2) \<in> borel_measurable M"
    by measurable
  show "AE \<omega> in M. norm ((maxabs X n \<omega>)\<^sup>2)
      \<le> norm (\<Sum>k\<le>n. (X k \<omega>)\<^sup>2)"
    using maxabs_sq_le_sum by (intro AE_I2) (simp add: sum_nonneg)
qed

lemma maxabs_prod_integrable:
  "integrable M (\<lambda>\<omega>. \<bar>X n \<omega>\<bar> * maxabs X n \<omega>)"
proof (rule Bochner_Integration.integrable_bound
    [of _ "\<lambda>\<omega>. (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2"])
  show "integrable M (\<lambda>\<omega>. (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add sq_integrable
        maxabs_sq_integrable)
  show "(\<lambda>\<omega>. \<bar>X n \<omega>\<bar> * maxabs X n \<omega>) \<in> borel_measurable M"
    by measurable
  show "AE \<omega> in M. norm (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)
      \<le> norm ((X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2)"
  proof (intro AE_I2)
    fix \<omega>
    have nn: "0 \<le> \<bar>X n \<omega>\<bar> * maxabs X n \<omega>"
      by (simp add: maxabs_nonneg)
    have "\<bar>X n \<omega>\<bar> * maxabs X n \<omega>
        \<le> 2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)"
      using nn by linarith
    also have "\<dots> \<le> (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2"
      using sum_squares_bound[of "\<bar>X n \<omega>\<bar>" "maxabs X n \<omega>"]
      by (simp add: mult_ac)
    finally have "\<bar>X n \<omega>\<bar> * maxabs X n \<omega>
        \<le> (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2" .
    with nn show "norm (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)
        \<le> norm ((X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2)"
      by simp
  qed
qed

lemma level_set_sets: "{\<omega> \<in> space M. l \<le> maxabs X n \<omega>} \<in> sets M"
  by measurable

theorem doob_L2_inequality:
  "(\<integral>\<omega>. (maxabs X n \<omega>)\<^sup>2 \<partial>M) \<le> 4 * (\<integral>\<omega>. (X n \<omega>)\<^sup>2 \<partial>M)"
proof -
  interpret PSF: pair_sigma_finite M lborel ..
  define R where
    "R = {p \<in> space (M \<Otimes>\<^sub>M lborel).
       0 \<le> snd p \<and> snd p \<le> maxabs X n (fst p)}"
  have R_sets: "R \<in> sets (M \<Otimes>\<^sub>M lborel)"
    unfolding R_def by measurable
  define g where "g = (\<lambda>p :: 'a \<times> real.
    ennreal (2 * snd p) * indicator R p)"
  define h where "h = (\<lambda>p :: 'a \<times> real.
    ennreal (2 * \<bar>X n (fst p)\<bar>) * indicator R p)"
  have g_meas [measurable]: "g \<in> borel_measurable (M \<Otimes>\<^sub>M lborel)"
    unfolding g_def using R_sets by measurable
  have h_meas [measurable]: "h \<in> borel_measurable (M \<Otimes>\<^sub>M lborel)"
    unfolding h_def using R_sets by measurable

  text \<open>The slices in \<open>l\<close>, for a fixed \<open>\<omega>\<close>.\<close>
  have slice: "(indicator R (\<omega>, l) :: ennreal)
      = indicator {0..maxabs X n \<omega>} l" if w: "\<omega> \<in> space M" for \<omega> l
    using w by (auto simp: R_def indicator_def space_pair_measure)
  have inner_2l: "(\<integral>\<^sup>+l. ennreal (2 * l) * indicator {0..b} l \<partial>lborel)
      = ennreal (b\<^sup>2)" if b: "0 \<le> b" for b
  proof -
    have "(\<integral>\<^sup>+l. ennreal (2 * l) * indicator {0..b} l \<partial>lborel)
        = ennreal (b\<^sup>2 - 0\<^sup>2)"
      using b by (intro nn_integral_FTC_Icc[where F = "\<lambda>l. l\<^sup>2"])
        (auto intro!: derivative_eq_intros)
    then show ?thesis by simp
  qed
  have g_slice: "(\<integral>\<^sup>+l. g (\<omega>, l) \<partial>lborel) = ennreal ((maxabs X n \<omega>)\<^sup>2)"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have "(\<integral>\<^sup>+l. g (\<omega>, l) \<partial>lborel)
        = (\<integral>\<^sup>+l. ennreal (2 * l)
            * indicator {0..maxabs X n \<omega>} l \<partial>lborel)"
      unfolding g_def by (intro nn_integral_cong) (simp add: slice[OF w])
    also have "\<dots> = ennreal ((maxabs X n \<omega>)\<^sup>2)"
      by (rule inner_2l[OF maxabs_nonneg])
    finally show ?thesis .
  qed
  have h_slice: "(\<integral>\<^sup>+l. h (\<omega>, l) \<partial>lborel)
      = ennreal (2 * \<bar>X n \<omega>\<bar>) * ennreal (maxabs X n \<omega>)"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have "(\<integral>\<^sup>+l. h (\<omega>, l) \<partial>lborel)
        = (\<integral>\<^sup>+l. ennreal (2 * \<bar>X n \<omega>\<bar>)
            * indicator {0..maxabs X n \<omega>} l \<partial>lborel)"
      unfolding h_def by (intro nn_integral_cong) (simp add: slice[OF w])
    also have "\<dots> = ennreal (2 * \<bar>X n \<omega>\<bar>)
        * emeasure lborel {0..maxabs X n \<omega>}"
      by (rule nn_integral_cmult_indicator) simp
    also have "\<dots> = ennreal (2 * \<bar>X n \<omega>\<bar>) * ennreal (maxabs X n \<omega>)"
      by (simp add: maxabs_nonneg)
    finally show ?thesis .
  qed

  text \<open>The slices in \<open>\<omega>\<close>, for a fixed level \<open>l\<close>, and the weak inequality.\<close>
  have omega_slice: "(indicator R (\<omega>, l) :: ennreal)
      = indicator {\<omega> \<in> space M. l \<le> maxabs X n \<omega>} \<omega>"
    if l: "0 \<le> l" and w: "\<omega> \<in> space M" for l \<omega>
    using l w by (auto simp: R_def indicator_def space_pair_measure)
  have levels: "(\<integral>\<^sup>+\<omega>. g (\<omega>, l) \<partial>M) \<le> (\<integral>\<^sup>+\<omega>. h (\<omega>, l) \<partial>M)" for l
  proof (cases "0 < l")
    case True
    then have l0: "0 \<le> l" by simp
    let ?S = "{\<omega> \<in> space M. l \<le> maxabs X n \<omega>}"
    have S: "?S \<in> sets M"
      by (rule level_set_sets)
    have gl: "(\<integral>\<^sup>+\<omega>. g (\<omega>, l) \<partial>M) = ennreal (2 * l) * emeasure M ?S"
    proof -
      have "(\<integral>\<^sup>+\<omega>. g (\<omega>, l) \<partial>M)
          = (\<integral>\<^sup>+\<omega>. ennreal (2 * l) * indicator ?S \<omega> \<partial>M)"
        unfolding g_def
        by (intro nn_integral_cong) (simp add: omega_slice[OF l0])
      also have "\<dots> = ennreal (2 * l) * emeasure M ?S"
        by (intro nn_integral_cmult_indicator S)
      finally show ?thesis .
    qed
    have hl: "(\<integral>\<^sup>+\<omega>. h (\<omega>, l) \<partial>M)
        = (\<integral>\<^sup>+\<omega>. ennreal (2 * \<bar>X n \<omega>\<bar>) * indicator ?S \<omega> \<partial>M)"
      unfolding h_def
      by (intro nn_integral_cong) (simp add: omega_slice[OF l0])
    have int_S: "integrable M (\<lambda>\<omega>. 2 * (indicat_real ?S \<omega> * \<bar>X n \<omega>\<bar>))"
      using set_integrable_abs_X[OF S]
      by (simp add: set_integrable_def)
    have hl_val: "(\<integral>\<^sup>+\<omega>. ennreal (2 * \<bar>X n \<omega>\<bar>) * indicator ?S \<omega> \<partial>M)
        = ennreal (2 * (LINT x:?S|M. \<bar>X n x\<bar>))"
    proof -
      have "(\<integral>\<^sup>+\<omega>. ennreal (2 * \<bar>X n \<omega>\<bar>) * indicator ?S \<omega> \<partial>M)
          = (\<integral>\<^sup>+\<omega>. ennreal (2 * (indicat_real ?S \<omega> * \<bar>X n \<omega>\<bar>)) \<partial>M)"
        by (intro nn_integral_cong)
          (simp add: indicator_def ennreal_mult'' split: if_split_asm)
      also have "\<dots> = ennreal (\<integral>\<omega>. 2 * (indicat_real ?S \<omega> * \<bar>X n \<omega>\<bar>) \<partial>M)"
        by (intro nn_integral_eq_integral int_S AE_I2) simp
      also have "\<dots> = ennreal (2 * (LINT x:?S|M. \<bar>X n x\<bar>))"
        unfolding set_lebesgue_integral_def by simp
      finally show ?thesis .
    qed
    have real_le: "2 * l * P.prob ?S \<le> 2 * (LINT x:?S|M. \<bar>X n x\<bar>)"
      using doob_maximal_inequality[OF True] by simp
    have "ennreal (2 * l) * emeasure M ?S
        = ennreal (2 * l) * ennreal (P.prob ?S)"
      by (simp add: P.emeasure_eq_measure)
    also have "\<dots> = ennreal (2 * l * P.prob ?S)"
      by (rule ennreal_mult''[symmetric]) simp
    also have "\<dots> \<le> ennreal (2 * (LINT x:?S|M. \<bar>X n x\<bar>))"
      using real_le by (rule ennreal_leI)
    finally have "ennreal (2 * l) * emeasure M ?S
        \<le> ennreal (2 * (LINT x:?S|M. \<bar>X n x\<bar>))" .
    with gl hl hl_val show ?thesis by simp
  next
    case False
    then have "(\<lambda>\<omega>. g (\<omega>, l)) = (\<lambda>\<omega>. 0)"
      unfolding g_def by (auto simp: R_def indicator_def fun_eq_iff)
    then show ?thesis by simp
  qed

  text \<open>Tonelli, twice.\<close>
  have "(\<integral>\<^sup>+\<omega>. ennreal ((maxabs X n \<omega>)\<^sup>2) \<partial>M)
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+l. g (\<omega>, l) \<partial>lborel) \<partial>M)"
    by (intro nn_integral_cong) (simp add: g_slice)
  also have "\<dots> = integral\<^sup>N (M \<Otimes>\<^sub>M lborel) g"
    by (rule lborel.nn_integral_fst[OF g_meas])
  also have "\<dots> = (\<integral>\<^sup>+l. (\<integral>\<^sup>+\<omega>. g (\<omega>, l) \<partial>M) \<partial>lborel)"
    by (rule PSF.nn_integral_snd[OF g_meas, symmetric])
  also have "\<dots> \<le> (\<integral>\<^sup>+l. (\<integral>\<^sup>+\<omega>. h (\<omega>, l) \<partial>M) \<partial>lborel)"
    by (intro nn_integral_mono levels)
  also have "\<dots> = integral\<^sup>N (M \<Otimes>\<^sub>M lborel) h"
    by (rule PSF.nn_integral_snd[OF h_meas])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+l. h (\<omega>, l) \<partial>lborel) \<partial>M)"
    by (rule lborel.nn_integral_fst[OF h_meas, symmetric])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. ennreal (2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)) \<partial>M)"
    by (intro nn_integral_cong)
      (simp add: h_slice ennreal_mult''[symmetric] maxabs_nonneg mult_ac)
  finally have nn_le: "(\<integral>\<^sup>+\<omega>. ennreal ((maxabs X n \<omega>)\<^sup>2) \<partial>M)
      \<le> (\<integral>\<^sup>+\<omega>. ennreal (2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)) \<partial>M)" .

  text \<open>Back to Bochner integrals.\<close>
  have e1: "(\<integral>\<^sup>+\<omega>. ennreal ((maxabs X n \<omega>)\<^sup>2) \<partial>M)
      = ennreal (\<integral>\<omega>. (maxabs X n \<omega>)\<^sup>2 \<partial>M)"
    by (intro nn_integral_eq_integral maxabs_sq_integrable AE_I2) simp
  have e2: "(\<integral>\<^sup>+\<omega>. ennreal (2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)) \<partial>M)
      = ennreal (\<integral>\<omega>. 2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>) \<partial>M)"
    by (intro nn_integral_eq_integral integrable_mult_right
        maxabs_prod_integrable AE_I2)
      (simp add: maxabs_nonneg)
  have prod_nonneg: "0 \<le> (\<integral>\<omega>. 2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>) \<partial>M)"
    by (intro integral_nonneg_AE AE_I2) (simp add: maxabs_nonneg)
  have main: "(\<integral>\<omega>. (maxabs X n \<omega>)\<^sup>2 \<partial>M)
      \<le> (\<integral>\<omega>. 2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>) \<partial>M)"
    using nn_le prod_nonneg unfolding e1 e2 by (simp add: ennreal_le_iff)

  text \<open>The elementary bound \<open>2ab \<le> 2a\<^sup>2 + b\<^sup>2/2\<close>.\<close>
  have amgm: "2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>)
      \<le> 2 * (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2 / 2" for \<omega>
  proof -
    have "0 \<le> 2 * (\<bar>X n \<omega>\<bar> - maxabs X n \<omega> / 2)\<^sup>2"
      by simp
    then show ?thesis
      by (simp add: power2_eq_square algebra_simps)
  qed
  have step: "(\<integral>\<omega>. 2 * (\<bar>X n \<omega>\<bar> * maxabs X n \<omega>) \<partial>M)
      \<le> (\<integral>\<omega>. 2 * (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2 / 2 \<partial>M)"
    using amgm
    by (intro integral_mono integrable_mult_right maxabs_prod_integrable
        Bochner_Integration.integrable_add integrable_divide
        maxabs_sq_integrable sq_integrable) simp_all
  have split: "(\<integral>\<omega>. 2 * (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2 / 2 \<partial>M)
      = 2 * (\<integral>\<omega>. (X n \<omega>)\<^sup>2 \<partial>M) + (\<integral>\<omega>. (maxabs X n \<omega>)\<^sup>2 \<partial>M) / 2"
  proof -
    have "(\<integral>\<omega>. 2 * (X n \<omega>)\<^sup>2 + (maxabs X n \<omega>)\<^sup>2 / 2 \<partial>M)
        = (\<integral>\<omega>. 2 * (X n \<omega>)\<^sup>2 \<partial>M) + (\<integral>\<omega>. (maxabs X n \<omega>)\<^sup>2 / 2 \<partial>M)"
      by (intro Bochner_Integration.integral_add integrable_mult_right
          sq_integrable integrable_divide maxabs_sq_integrable)
    then show ?thesis by simp
  qed
  from main step show ?thesis
    unfolding split by simp
qed

end

section \<open>The maximal inequality for a continuous-time martingale on a grid\<close>

text \<open>A continuous-time square-integrable martingale sampled along a grid is
  a discrete one (Time\_Discretisation), so the inequality above applies to
  it verbatim.\<close>

lemma (in sampled_martingale) grid_doob_L2:
  assumes PS: "prob_space M"
  shows "(\<integral>\<omega>. (maxabs (\<lambda>k. Y (t k)) n \<omega>)\<^sup>2 \<partial>M)
       \<le> 4 * (\<integral>\<omega>. (Y (t n) \<omega>)\<^sup>2 \<partial>M)"
proof -
  have sq: "sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. Y (t k))"
    by unfold_locales
  have psq: "prob_sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. Y (t k))"
    by (intro prob_sq_int_martingale.intro[OF sq]
        prob_sq_int_martingale_axioms.intro PS)
  show ?thesis
    by (rule prob_sq_int_martingale.doob_L2_inequality[OF psq])
qed

section \<open>An integrable bound for the running maximum up to a horizon\<close>

text \<open>Taking the dyadic grids of \<open>[0,u]\<close>, the maxima along them increase,
  and Doob's inequality bounds them uniformly.  Monotone convergence turns
  this into an integrable function \<open>Dsup\<close> --- measurable by construction,
  being a countable supremum --- that dominates the whole grid family, and
  (with continuous paths) the whole of \<open>|Y s|, s \<in> [0,u]\<close>.  That is exactly
  the dominating function the optional-sampling development asks for.\<close>

locale horizon_sq_int_martingale = martingale M F "0 :: real" Y
  for M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" +
  fixes u :: real
  assumes u_pos: "0 < u"
    and prob_space_M: "prob_space M"
    and Y_sq_integrable: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (Y s \<omega>)\<^sup>2)"
begin

sublocale P: prob_space M
  by (rule prob_space_M)

subsection \<open>The dyadic grids of the horizon\<close>

definition dy :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "dy n k = u * real k / 2 ^ n"

lemma dy_nonneg: "0 \<le> dy n k"
  unfolding dy_def using u_pos by simp

lemma dy_mono: "k \<le> j \<Longrightarrow> dy n k \<le> dy n j"
  unfolding dy_def using u_pos by (simp add: divide_right_mono mult_left_mono)

lemma dy_top [simp]: "dy n (2 ^ n) = u"
  unfolding dy_def by simp

lemma dy_le_u: "k \<le> 2 ^ n \<Longrightarrow> dy n k \<le> u"
  using dy_mono[of k "2 ^ n" n] by simp

lemma dy_step: "dy (Suc n) (2 * k) = dy n k"
  unfolding dy_def by simp

lemma grid_martingale: "sampled_martingale M F Y (dy n)"
proof -
  have mg: "martingale M F (0 :: real) Y"
    by unfold_locales
  have tg: "time_grid (dy n)"
    by (intro time_grid.intro) (auto intro: dy_nonneg dy_mono)
  show ?thesis
    by (intro sampled_martingale.intro[OF mg tg]
        sampled_martingale_axioms.intro Y_sq_integrable)
qed

subsection \<open>The maxima along the grids\<close>

definition gsup :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
  "gsup n \<omega> = maxabs (\<lambda>k. Y (dy n k)) (2 ^ n) \<omega>"

lemma gsup_nonneg: "0 \<le> gsup n \<omega>"
  unfolding gsup_def by (rule maxabs_nonneg)

lemma gsup_ge: "k \<le> 2 ^ n \<Longrightarrow> \<bar>Y (dy n k) \<omega>\<bar> \<le> gsup n \<omega>"
  unfolding gsup_def by (rule maxabs_ge)

lemma gsup_measurable [measurable]: "gsup n \<in> borel_measurable M"
  unfolding gsup_def
  by (intro maxabs_measurable random_variable dy_nonneg)

lemma gsup_sq_integrable: "integrable M (\<lambda>\<omega>. (gsup n \<omega>)\<^sup>2)"
proof -
  have "prob_sq_int_martingale M (\<lambda>k. F (dy n k)) (\<lambda>k. Y (dy n k))"
  proof -
    interpret SM: sampled_martingale M F Y "dy n"
      by (rule grid_martingale)
    have sq: "sq_int_martingale M (\<lambda>k. F (dy n k)) (\<lambda>k. Y (dy n k))"
      by (rule SM.D.sq_int_martingale_axioms)
    show ?thesis
      by (intro prob_sq_int_martingale.intro[OF sq]
          prob_sq_int_martingale_axioms.intro prob_space_M)
  qed
  then show ?thesis
    unfolding gsup_def
    by (rule prob_sq_int_martingale.maxabs_sq_integrable)
qed

lemma gsup_le_one_plus_sq: "gsup n \<omega> \<le> 1 + (gsup n \<omega>)\<^sup>2"
proof -
  have sq: "0 \<le> (gsup n \<omega> - 1)\<^sup>2" by simp
  have exp: "(gsup n \<omega> - 1)\<^sup>2 = (gsup n \<omega>)\<^sup>2 - 2 * gsup n \<omega> + 1"
    by (simp add: power2_eq_square algebra_simps)
  have nn: "0 \<le> (gsup n \<omega>)\<^sup>2" by simp
  from sq exp nn show ?thesis by linarith
qed

lemma gsup_integrable: "integrable M (gsup n)"
proof (rule Bochner_Integration.integrable_bound
    [of _ "\<lambda>\<omega>. 1 + (gsup n \<omega>)\<^sup>2"])
  show "integrable M (\<lambda>\<omega>. 1 + (gsup n \<omega>)\<^sup>2)"
    by (intro Bochner_Integration.integrable_add P.integrable_const
        gsup_sq_integrable)
  show "gsup n \<in> borel_measurable M"
    by measurable
  show "AE \<omega> in M. norm (gsup n \<omega>) \<le> norm (1 + (gsup n \<omega>)\<^sup>2)"
    using gsup_le_one_plus_sq gsup_nonneg by (intro AE_I2) simp
qed

lemma gsup_L2: "(\<integral>\<omega>. (gsup n \<omega>)\<^sup>2 \<partial>M) \<le> 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M)"
proof -
  have "(\<integral>\<omega>. (maxabs (\<lambda>k. Y (dy n k)) (2 ^ n) \<omega>)\<^sup>2 \<partial>M)
      \<le> 4 * (\<integral>\<omega>. (Y (dy n (2 ^ n)) \<omega>)\<^sup>2 \<partial>M)"
    by (rule sampled_martingale.grid_doob_L2[OF grid_martingale prob_space_M])
  then show ?thesis
    unfolding gsup_def by simp
qed

lemma gsup_mean_le:
  "(\<integral>\<omega>. gsup n \<omega> \<partial>M) \<le> 1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M)"
proof -
  have "(\<integral>\<omega>. gsup n \<omega> \<partial>M) \<le> (\<integral>\<omega>. 1 + (gsup n \<omega>)\<^sup>2 \<partial>M)"
    using gsup_le_one_plus_sq
    by (intro integral_mono gsup_integrable Bochner_Integration.integrable_add
        P.integrable_const gsup_sq_integrable) simp
  also have "\<dots> = 1 + (\<integral>\<omega>. (gsup n \<omega>)\<^sup>2 \<partial>M)"
    by (simp add: gsup_sq_integrable P.prob_space)
  also have "\<dots> \<le> 1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M)"
    using gsup_L2 by simp
  finally show ?thesis .
qed

lemma gsup_mono: "gsup n \<omega> \<le> gsup (Suc n) \<omega>"
proof -
  obtain j where j: "j \<le> 2 ^ n" and eq: "gsup n \<omega> = \<bar>Y (dy n j) \<omega>\<bar>"
    using maxabs_attained[where Y = "\<lambda>k. Y (dy n k)" and n = "2 ^ n"
        and \<omega> = \<omega>]
    unfolding gsup_def by blast
  have "2 * j \<le> 2 ^ Suc n"
    using j by simp
  then have "\<bar>Y (dy (Suc n) (2 * j)) \<omega>\<bar> \<le> gsup (Suc n) \<omega>"
    by (rule gsup_ge)
  then show ?thesis
    unfolding eq by (simp add: dy_step)
qed

subsection \<open>The countable supremum of the grid maxima\<close>

definition esup :: "'a \<Rightarrow> ennreal" where
  "esup \<omega> = (SUP n. ennreal (gsup n \<omega>))"

definition Dsup :: "'a \<Rightarrow> real" where
  "Dsup \<omega> = enn2real (esup \<omega>)"

lemma esup_measurable [measurable]: "esup \<in> borel_measurable M"
  unfolding esup_def by measurable

lemma Dsup_measurable [measurable]: "Dsup \<in> borel_measurable M"
  unfolding Dsup_def by measurable

lemma esup_nn_integral_le:
  "(\<integral>\<^sup>+\<omega>. esup \<omega> \<partial>M)
     \<le> ennreal (1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M))"
proof -
  have inc: "incseq (\<lambda>n \<omega>. ennreal (gsup n \<omega>))"
    by (intro incseq_SucI le_funI) (simp add: gsup_mono ennreal_leI)
  have "(\<integral>\<^sup>+\<omega>. esup \<omega> \<partial>M)
      = (SUP n. \<integral>\<^sup>+\<omega>. ennreal (gsup n \<omega>) \<partial>M)"
    unfolding esup_def
    by (intro nn_integral_monotone_convergence_SUP inc) measurable
  also have "\<dots> \<le> ennreal (1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M))"
  proof (intro SUP_least)
    fix n
    have "(\<integral>\<^sup>+\<omega>. ennreal (gsup n \<omega>) \<partial>M) = ennreal (\<integral>\<omega>. gsup n \<omega> \<partial>M)"
      by (intro nn_integral_eq_integral gsup_integrable AE_I2)
        (simp add: gsup_nonneg)
    also have "\<dots> \<le> ennreal (1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M))"
      using gsup_mean_le by (rule ennreal_leI)
    finally show "(\<integral>\<^sup>+\<omega>. ennreal (gsup n \<omega>) \<partial>M)
        \<le> ennreal (1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M))" .
  qed
  finally show ?thesis .
qed

lemma esup_finite_AE: "AE \<omega> in M. esup \<omega> \<noteq> \<infinity>"
proof (rule nn_integral_noteq_infinite)
  show "esup \<in> borel_measurable M" by measurable
  have "(\<integral>\<^sup>+\<omega>. esup \<omega> \<partial>M)
      \<le> ennreal (1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M))"
    by (rule esup_nn_integral_le)
  also have "\<dots> < \<infinity>" by simp
  finally show "(\<integral>\<^sup>+\<omega>. esup \<omega> \<partial>M) \<noteq> \<infinity>" by simp
qed

lemma Dsup_eq_AE: "AE \<omega> in M. ennreal (Dsup \<omega>) = esup \<omega>"
  using esup_finite_AE
proof eventually_elim
  case (elim \<omega>)
  then show ?case
    unfolding Dsup_def by (simp add: ennreal_enn2real less_top)
qed

lemma Dsup_nonneg: "0 \<le> Dsup \<omega>"
  unfolding Dsup_def by simp

lemma Dsup_integrable: "integrable M Dsup"
proof (rule integrableI_nonneg)
  show "Dsup \<in> borel_measurable M" by measurable
  show "AE \<omega> in M. 0 \<le> Dsup \<omega>"
    by (intro AE_I2 Dsup_nonneg)
  have "(\<integral>\<^sup>+\<omega>. ennreal (Dsup \<omega>) \<partial>M) = (\<integral>\<^sup>+\<omega>. esup \<omega> \<partial>M)"
    using Dsup_eq_AE by (intro nn_integral_cong_AE) simp
  also have "\<dots> \<le> ennreal (1 + 4 * (\<integral>\<omega>. (Y u \<omega>)\<^sup>2 \<partial>M))"
    by (rule esup_nn_integral_le)
  also have "\<dots> < \<infinity>" by simp
  finally show "(\<integral>\<^sup>+\<omega>. ennreal (Dsup \<omega>) \<partial>M) < \<infinity>" .
qed

lemma gsup_le_Dsup_AE: "AE \<omega> in M. \<forall>n. gsup n \<omega> \<le> Dsup \<omega>"
  using esup_finite_AE
proof eventually_elim
  case (elim \<omega>)
  show ?case
  proof
    fix n
    have "ennreal (gsup n \<omega>) \<le> esup \<omega>"
      unfolding esup_def by (rule SUP_upper) simp
    then have "enn2real (ennreal (gsup n \<omega>)) \<le> enn2real (esup \<omega>)"
      using elim by (intro enn2real_mono) (simp_all add: less_top)
    then show "gsup n \<omega> \<le> Dsup \<omega>"
      unfolding Dsup_def using gsup_nonneg by simp
  qed
qed

subsection \<open>With continuous paths the bound holds at every time\<close>

lemma dy_floor:
  assumes s: "0 \<le> s" and su: "s \<le> u"
  shows dy_floor_le: "dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> s"
    and dy_floor_close: "s - u / 2 ^ n \<le> dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>)"
    and dy_floor_idx: "nat \<lfloor>s * 2 ^ n / u\<rfloor> \<le> 2 ^ n"
proof -
  have x0: "0 \<le> s * 2 ^ n / u"
    using s u_pos by simp
  then have kx: "real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) = of_int \<lfloor>s * 2 ^ n / u\<rfloor>"
    by simp
  have le: "real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> s * 2 ^ n / u"
    unfolding kx by (rule of_int_floor_le)
  have gt: "s * 2 ^ n / u < real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) + 1"
    unfolding kx
    using floor_le_iff[of "s * 2 ^ n / u" "\<lfloor>s * 2 ^ n / u\<rfloor>"] by simp
  show "dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> s"
  proof -
    have "u * real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> u * (s * 2 ^ n / u)"
      using le u_pos by (intro mult_left_mono) auto
    also have "\<dots> = s * 2 ^ n"
      using u_pos by simp
    finally have key: "u * real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> s * 2 ^ n" .
    have "u * real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) / 2 ^ n \<le> s * 2 ^ n / 2 ^ n"
      using key by (intro divide_right_mono) auto
    then show ?thesis
      unfolding dy_def by simp
  qed
  show "s - u / 2 ^ n \<le> dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>)"
  proof -
    have "u * (s * 2 ^ n / u - 1) \<le> u * real (nat \<lfloor>s * 2 ^ n / u\<rfloor>)"
      using gt u_pos by (intro mult_left_mono) auto
    moreover have "u * (s * 2 ^ n / u - 1) = s * 2 ^ n - u"
      using u_pos by (simp add: field_simps)
    ultimately have key: "s * 2 ^ n - u
        \<le> u * real (nat \<lfloor>s * 2 ^ n / u\<rfloor>)"
      by simp
    have eq: "(s * 2 ^ n - u) / 2 ^ n = s - u / 2 ^ n"
      by (simp add: field_simps)
    have "(s * 2 ^ n - u) / 2 ^ n
        \<le> u * real (nat \<lfloor>s * 2 ^ n / u\<rfloor>) / 2 ^ n"
      using key by (intro divide_right_mono) auto
    then show ?thesis
      unfolding dy_def eq[symmetric] .
  qed
  show "nat \<lfloor>s * 2 ^ n / u\<rfloor> \<le> 2 ^ n"
  proof -
    have "s * 2 ^ n \<le> u * 2 ^ n"
      using su by (intro mult_right_mono) auto
    then have xle: "s * 2 ^ n / u \<le> 2 ^ n"
      using u_pos by (simp add: divide_le_eq mult.commute)
    have "\<lfloor>s * 2 ^ n / u\<rfloor> \<le> (2 :: int) ^ n"
      using xle by (simp add: floor_le_iff)
    then show ?thesis
      by (simp add: nat_le_iff)
  qed
qed

lemma dy_floor_tendsto:
  assumes s: "0 \<le> s" and su: "s \<le> u"
  shows "(\<lambda>n. dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>)) \<longlonglongrightarrow> s"
proof (rule tendsto_sandwich
    [of "\<lambda>n. s - u / 2 ^ n" "\<lambda>n. dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>)"
        sequentially "\<lambda>n. s"])
  show "\<forall>\<^sub>F n in sequentially.
      s - u / 2 ^ n \<le> dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>)"
    by (intro always_eventually allI dy_floor_close[OF s su])
  show "\<forall>\<^sub>F n in sequentially. dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> s"
    by (intro always_eventually allI dy_floor_le[OF s su])
  have "(\<lambda>n. u / 2 ^ n) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_divide_realpow_zero) simp
  then have "(\<lambda>n. s - u / 2 ^ n) \<longlonglongrightarrow> s - 0"
    by (intro tendsto_diff tendsto_const)
  then show "(\<lambda>n. s - u / 2 ^ n) \<longlonglongrightarrow> s" by simp
  show "(\<lambda>n. s) \<longlonglongrightarrow> s" by simp
qed

theorem Dsup_dominates:
  assumes cont: "AE \<omega> in M. continuous_on {0..u} (\<lambda>s. Y s \<omega>)"
  shows "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> Dsup \<omega>"
  using cont gsup_le_Dsup_AE
proof eventually_elim
  case (elim \<omega>)
  then have c: "continuous_on {0..u} (\<lambda>s. Y s \<omega>)"
    and gd: "\<forall>n. gsup n \<omega> \<le> Dsup \<omega>"
    by auto
  have seq: "\<And>x a. a \<in> {0..u} \<Longrightarrow> (\<forall>n. x n \<in> {0..u}) \<Longrightarrow> x \<longlonglongrightarrow> a
      \<Longrightarrow> ((\<lambda>s. Y s \<omega>) \<circ> x) \<longlonglongrightarrow> Y a \<omega>"
    using c unfolding continuous_on_sequentially by blast
  show ?case
  proof (intro allI impI)
    fix s :: real
    assume s: "0 \<le> s" and su: "s \<le> u"
    define p where "p = (\<lambda>n. dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>))"
    have pS: "\<forall>n. p n \<in> {0..u}"
    proof
      fix n
      have "dy n (nat \<lfloor>s * 2 ^ n / u\<rfloor>) \<le> u"
        by (intro dy_le_u dy_floor_idx[OF s su])
      then show "p n \<in> {0..u}"
        unfolding p_def using dy_nonneg by simp
    qed
    have plim: "p \<longlonglongrightarrow> s"
      unfolding p_def by (rule dy_floor_tendsto[OF s su])
    have "((\<lambda>s. Y s \<omega>) \<circ> p) \<longlonglongrightarrow> Y s \<omega>"
      using s su pS plim by (intro seq) auto
    then have lim: "(\<lambda>n. \<bar>Y (p n) \<omega>\<bar>) \<longlonglongrightarrow> \<bar>Y s \<omega>\<bar>"
      by (auto intro: tendsto_rabs simp: comp_def)
    have bnd: "\<bar>Y (p n) \<omega>\<bar> \<le> Dsup \<omega>" for n
    proof -
      have "\<bar>Y (p n) \<omega>\<bar> \<le> gsup n \<omega>"
        unfolding p_def by (rule gsup_ge[OF dy_floor_idx[OF s su]])
      also have "\<dots> \<le> Dsup \<omega>"
        using gd by simp
      finally show ?thesis .
    qed
    show "\<bar>Y s \<omega>\<bar> \<le> Dsup \<omega>"
      using bnd by (intro LIMSEQ_le_const2[OF lim]) blast
  qed
qed

end

end
