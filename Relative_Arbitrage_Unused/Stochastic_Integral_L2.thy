section \<open>The \<open>L\<^sup>2\<close> closure of the simple stochastic integrals\<close>

(*<*)
theory Stochastic_Integral_L2
  imports Stochastic_Integral_Simple L2_Limits
begin

(*>*)

text \<open>
  The final layer of open task 15. Everything needed is now in place:

  \<^item> \<open>ito_isometry_simple_diff\<close> (@{theory Relative_Arbitrage_Unused.Stochastic_Integral_Simple}) says the map from
    integrands to integrals is an ISOMETRY, so a sequence of integrands that is
    Cauchy for the norm \<open>E[SUM H\<^sup>2 (dX)\<^sup>2]\<close> has integrals that are Cauchy in
    \<open>L\<^sup>2 M\<close>;
  \<^item> \<open>L2_cauchy_ae_limit\<close> (@{theory Relative_Arbitrage_Unused.L2_Limits}) turns an \<open>L\<^sup>2\<close>-Cauchy sequence into an
    almost-everywhere convergent subsequence, by Riesz-Fischer.

  Composing them gives the extension: the integral of an integrand in the closure
  exists as the almost-everywhere limit of the integrals of approximating simple
  integrands. That is the statement below.

  Import note: @{theory Relative_Arbitrage_Unused.Stochastic_Integral_Simple} and @{theory Relative_Arbitrage_Unused.L2_Limits} meet only at session
  theories (\<open>Martingales.Martingale\<close> and \<open>HOL-Probability.Probability\<close>), so there is
  no diamond over a draft theory.
\<close>
subsection \<open>Integrability of the simple integral\<close>

lemma simple_itg_integrable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>k. H k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H k \<omega>)\<^sup>2)"
  shows "integrable M (simple_itg H X t n)"
proof -
  interpret D: discrete_integrand M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)" H
  proof (intro discrete_integrand.intro discrete_integrand_axioms.intro)
    show "sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. X (t k))"
      by (rule sq_int_martingale_of_sampled[OF X t0 tmono sq])
    show "H m \<in> borel_measurable (F (t m))" for m by (rule H_meas)
    show "integrable M (\<lambda>\<omega>. (H m \<omega>)\<^sup>2)" for m by (rule H_sq)
  qed
  have "integrable M (mtrans H (\<lambda>k. X (t k)) n)" by (rule D.mtrans_integrable)
  thus ?thesis by (simp add: simple_itg_eq_mtrans)
qed

subsection \<open>The extension\<close>

text \<open>
  Here \<open>H m\<close> is the \<open>m\<close>-th approximating simple integrand, all bounded by the same
  constant, and the Cauchy hypothesis is stated in the integrand norm attached to
  the partition. The conclusion is the extended integral, as an almost-everywhere
  limit along a subsequence.
\<close>

theorem simple_itg_L2_closure:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
    and H :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>m k. H m k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>m k. integrable M (\<lambda>\<omega>. (H m k \<omega>)\<^sup>2)"
    and H_bdd: "\<And>m k \<omega>. \<bar>H m k \<omega>\<bar> \<le> B"
    and cauchy: "\<And>d. 0 < d \<Longrightarrow> \<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N.
        (\<integral>\<omega>. (\<Sum>k<n. ((H i k \<omega> - H j k \<omega>)
                       * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2) \<partial>M) < d"
  obtains r g where "strict_mono r" "g \<in> borel_measurable M"
    "AE \<omega> in M. (\<lambda>i. simple_itg (H (r i)) X t n \<omega>) \<longlonglongrightarrow> g \<omega>"
proof -
  interpret P: prob_space M by (rule P)
  define f where "f = (\<lambda>m. simple_itg (H m) X t n)"
  have fint: "integrable M (f m)" for m
    unfolding f_def
    by (rule simple_itg_integrable[OF X t0 tmono sq H_meas H_sq])
  have fsq: "integrable M (\<lambda>\<omega>. (f m \<omega>)\<^sup>2)" for m
    unfolding f_def
    by (rule simple_itg_sq_integrable[OF X t0 tmono sq H_meas H_sq H_bdd])
  have fcauchy: "\<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. (\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M) < d"
    if d: "0 < d" for d
  proof -
    from cauchy[OF d] obtain N where
      N: "\<And>i j. i \<ge> N \<Longrightarrow> j \<ge> N \<Longrightarrow>
          (\<integral>\<omega>. (\<Sum>k<n. ((H i k \<omega> - H j k \<omega>)
                         * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2) \<partial>M) < d"
      by blast
    show ?thesis
    proof (intro exI[of _ N] allI impI)
      fix i j assume ij: "i \<ge> N" "j \<ge> N"
      have "(\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M)
              = (\<integral>\<omega>. (\<Sum>k<n. ((H i k \<omega> - H j k \<omega>)
                             * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2) \<partial>M)"
        unfolding f_def
        by (rule ito_isometry_simple_diff
                  [OF X t0 tmono sq H_meas H_sq H_bdd H_meas H_sq H_bdd])
      also have "\<dots> < d" by (rule N[OF ij])
      finally show "(\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M) < d" .
    qed
  qed
  obtain r g where rg: "strict_mono r" "g \<in> borel_measurable M"
      "AE \<omega> in M. (\<lambda>i. f (r i) \<omega>) \<longlonglongrightarrow> g \<omega>"
    by (rule P.L2_cauchy_ae_limit[OF fint fsq fcauchy]) blast
  show thesis using rg unfolding f_def by (rule that)
qed


(*<*)
end
(*>*)
