section \<open>The stochastic integral of a simple predictable integrand\<close>

text \<open>
  The last construction layer of open task 15. A SIMPLE predictable integrand is
  one subordinate to a partition: constant on each partition interval, with the
  value on the interval starting at \<open>t k\<close> measurable with respect to \<open>F (t k)\<close>.
  Its integral against a continuous-time martingale is the finite sum

    \<open>sum k<n. H k * (X (t (Suc k)) - X (t k))\<close>

  which is precisely the discrete martingale transform \<open>mtrans\<close> of the SAMPLED
  process. So the theorem "the stochastic integral of a predictable integrand
  against a martingale is a martingale" follows for continuous time from the
  discrete \<open>martingale_mtrans\<close>, through the sampling bridge.

  IMPORT NOTE: the imports are \<open>Stochastic_Integral\<close> and \<open>Sampled_Martingale\<close>,
  whose only common ancestor is the session theory \<open>Martingales.Martingale\<close>.
  Importing \<open>Sampled_Quadratic_Variation\<close> instead would have created a diamond
  over the DRAFT theory \<open>Quadratic_Variation\<close> (which \<open>Stochastic_Integral\<close> reaches
  via \<open>Relative_Arbitrage_Discrete\<close>), and such diamonds break loading. The single
  bridge lemma that would have come from there is re-derived below instead; it is
  six lines.
\<close>

theory Stochastic_Integral_Simple
  imports Stochastic_Integral "Martingale_Sampling.Sampled_Martingale"
begin

subsection \<open>The sampled process is a square-integrable discrete martingale\<close>

lemma sq_int_martingale_of_sampled:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
  shows "sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. X (t k))"
proof (intro sq_int_martingale.intro sq_int_martingale_axioms.intro)
  show "nat_sigma_finite_filtered_measure M (\<lambda>k. F (t k))"
    by (rule nat_filtered_of_sampled[OF X t0 tmono])
  show "martingale M (\<lambda>k. F (t k)) 0 (\<lambda>k. X (t k))"
    by (rule martingale_sampled[OF X t0 tmono])
  show "integrable M (\<lambda>\<omega>. (X (t n) \<omega>)\<^sup>2)" for n
    by (rule sq[OF t0])
qed

subsection \<open>The simple integral\<close>

definition simple_itg ::
  "(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)
     \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real"
  where
  "simple_itg H X t n \<omega> = (\<Sum>k<n. H k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))"

lemma simple_itg_zero [simp]: "simple_itg H X t 0 \<omega> = 0"
  by (simp add: simple_itg_def)

lemma simple_itg_Suc:
  "simple_itg H X t (Suc n) \<omega>
     = simple_itg H X t n \<omega> + H n \<omega> * (X (t (Suc n)) \<omega> - X (t n) \<omega>)"
  by (simp add: simple_itg_def)

text \<open>The simple integral IS the martingale transform of the sampled process.\<close>

lemma simple_itg_eq_mtrans: "simple_itg H X t = mtrans H (\<lambda>k. X (t k))"
proof (intro ext)
  fix n \<omega>
  show "simple_itg H X t n \<omega> = mtrans H (\<lambda>k. X (t k)) n \<omega>"
    by (simp add: simple_itg_def mtrans_fun)
qed

subsection \<open>The simple integral is a martingale\<close>

text \<open>
  The continuous-time form of "the stochastic integral of a predictable integrand
  against a martingale is a martingale". The hypotheses on @{term H} are exactly
  simple predictability: @{term "H k"} is measurable for the \<open>sigma\<close>-algebra at the
  LEFT endpoint of the \<open>k\<close>-th partition interval, and square-integrable so that the
  Cauchy-Schwarz bound makes each term integrable.
\<close>

theorem martingale_simple_itg:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>k. H k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H k \<omega>)\<^sup>2)"
  shows "martingale M (\<lambda>k. F (t k)) 0 (simple_itg H X t)"
proof -
  interpret D: discrete_integrand M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)" H
  proof (intro discrete_integrand.intro discrete_integrand_axioms.intro)
    show "sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. X (t k))"
      by (rule sq_int_martingale_of_sampled[OF X t0 tmono sq])
    show "H n \<in> borel_measurable (F (t n))" for n by (rule H_meas)
    show "integrable M (\<lambda>\<omega>. (H n \<omega>)\<^sup>2)" for n by (rule H_sq)
  qed
  have "martingale M (\<lambda>k. F (t k)) 0 (mtrans H (\<lambda>k. X (t k)))"
    by (rule D.martingale_mtrans)
  thus ?thesis by (simp add: simple_itg_eq_mtrans)
qed
subsection \<open>Square-integrability, for a bounded integrand\<close>

text \<open>
  For the isometry the integral itself must be square-integrable. That does NOT
  follow from square-integrability of @{term H} and of the increments: the integral
  is a SUM of products, and squaring it produces cross terms that need a fourth
  moment. The standard hypothesis for simple integrands is that @{term H} is
  bounded, and then an induction along the partition suffices.
\<close>

lemma sq_sum_le_two: "(a + b)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * b\<^sup>2" for a b :: real
proof -
  have "0 \<le> (a - b)\<^sup>2" by simp
  thus ?thesis by (simp add: power2_eq_square algebra_simps)
qed

lemma simple_itg_sq_integrable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>k. H k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H k \<omega>)\<^sup>2)"
    and H_bdd: "\<And>k \<omega>. \<bar>H k \<omega>\<bar> \<le> B"
  shows "integrable M (\<lambda>\<omega>. (simple_itg H X t n \<omega>)\<^sup>2)"
proof -
  interpret D: discrete_integrand M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)" H
  proof (intro discrete_integrand.intro discrete_integrand_axioms.intro)
    show "sq_int_martingale M (\<lambda>k. F (t k)) (\<lambda>k. X (t k))"
      by (rule sq_int_martingale_of_sampled[OF X t0 tmono sq])
    show "H m \<in> borel_measurable (F (t m))" for m by (rule H_meas)
    show "integrable M (\<lambda>\<omega>. (H m \<omega>)\<^sup>2)" for m by (rule H_sq)
  qed
  have Bnn: "0 \<le> B" using H_bdd[of 0 undefined] by (meson abs_ge_zero order_trans)
  have Imeas: "simple_itg H X t m \<in> borel_measurable M" for m
    using D.mtrans_integrable[of m]
    by (simp add: simple_itg_eq_mtrans borel_measurable_integrable)
  show ?thesis
  proof (induction n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have dom: "integrable M
        (\<lambda>\<omega>. 2 * (simple_itg H X t n \<omega>)\<^sup>2
             + 2 * (B\<^sup>2 * ((X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)))"
      using Suc.IH D.incr_sq_integrable[of n] by simp
    show ?case
    proof (rule Bochner_Integration.integrable_bound[OF dom])
      show "(\<lambda>\<omega>. (simple_itg H X t (Suc n) \<omega>)\<^sup>2) \<in> borel_measurable M"
        using Imeas by measurable
      show "AE \<omega> in M. norm ((simple_itg H X t (Suc n) \<omega>)\<^sup>2)
          \<le> norm (2 * (simple_itg H X t n \<omega>)\<^sup>2
                   + 2 * (B\<^sup>2 * ((X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)))"
      proof (intro always_eventually allI)
        fix \<omega>
        have hb: "(H n \<omega>)\<^sup>2 \<le> B\<^sup>2"
        proof -
          have "(H n \<omega>)\<^sup>2 = \<bar>H n \<omega>\<bar>\<^sup>2" by simp
          also have "\<dots> \<le> B\<^sup>2" using H_bdd[of n \<omega>] by (intro power_mono) auto
          finally show ?thesis .
        qed        have "(simple_itg H X t (Suc n) \<omega>)\<^sup>2
            = (simple_itg H X t n \<omega>
               + H n \<omega> * (X (t (Suc n)) \<omega> - X (t n) \<omega>))\<^sup>2"
          by (simp add: simple_itg_Suc)
        also have "\<dots> \<le> 2 * (simple_itg H X t n \<omega>)\<^sup>2
               + 2 * (H n \<omega> * (X (t (Suc n)) \<omega> - X (t n) \<omega>))\<^sup>2"
          by (rule sq_sum_le_two)
        also have "(H n \<omega> * (X (t (Suc n)) \<omega> - X (t n) \<omega>))\<^sup>2
            = (H n \<omega>)\<^sup>2 * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2"
          by (simp add: power_mult_distrib)
        also have "\<dots> \<le> B\<^sup>2 * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2"
          using hb by (simp add: mult_right_mono)
        finally have le: "(simple_itg H X t (Suc n) \<omega>)\<^sup>2
            \<le> 2 * (simple_itg H X t n \<omega>)\<^sup>2
              + 2 * (B\<^sup>2 * (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)"
          by simp
        show "norm ((simple_itg H X t (Suc n) \<omega>)\<^sup>2)
            \<le> norm (2 * (simple_itg H X t n \<omega>)\<^sup>2
                     + 2 * (B\<^sup>2 * ((X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2)))"
          using le by simp
      qed
    qed
  qed
qed

subsection \<open>The Ito isometry\<close>

text \<open>
  The second moment of the simple stochastic integral equals the expected sum of
  \<open>H\<^sup>2\<close> against the squared increments. This is the Ito isometry for simple
  integrands; it is the estimate on which the \<open>L\<^sup>2\<close> extension to general
  predictable integrands rests.
\<close>

theorem ito_isometry_simple:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>k. H k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H k \<omega>)\<^sup>2)"
    and H_bdd: "\<And>k \<omega>. \<bar>H k \<omega>\<bar> \<le> B"
  shows "(\<integral>\<omega>. (simple_itg H X t n \<omega>)\<^sup>2 \<partial>M)
           = (\<integral>\<omega>. (\<Sum>k<n. (H k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2) \<partial>M)"
proof -
  interpret I: sq_int_martingale M "\<lambda>k. F (t k)" "simple_itg H X t"
  proof (intro sq_int_martingale.intro sq_int_martingale_axioms.intro)
    show "nat_sigma_finite_filtered_measure M (\<lambda>k. F (t k))"
      by (rule nat_filtered_of_sampled[OF X t0 tmono])
    show "martingale M (\<lambda>k. F (t k)) 0 (simple_itg H X t)"
      by (rule martingale_simple_itg[OF X t0 tmono sq H_meas H_sq])
    show "integrable M (\<lambda>\<omega>. (simple_itg H X t m \<omega>)\<^sup>2)" for m
      by (rule simple_itg_sq_integrable[OF X t0 tmono sq H_meas H_sq H_bdd])
  qed
  have qv: "qvar (simple_itg H X t) m \<omega>
      = (\<Sum>k<m. (H k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2)" for m \<omega>
    by (simp add: qvar_def simple_itg_Suc)
  have "(\<integral>\<omega>. (simple_itg H X t n \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. (simple_itg H X t 0 \<omega>)\<^sup>2 \<partial>M)
            + (\<integral>\<omega>. qvar (simple_itg H X t) n \<omega> \<partial>M)"
    by (rule I.expectation_sq_qvar)
  thus ?thesis by (simp add: qv)
qed

subsection \<open>The compensated square as a simple integral, exactly\<close>

text \<open>
  This is the algebraic heart of "the compensated square is a stochastic integral",
  and it is an EXACT identity along any partition -- no limit is taken. Writing
  \<open>Y k = X (t k) - X (t 0)\<close> and telescoping, the compensated square equals the
  simple integral of \<open>2 Y\<close> against \<open>X\<close> PLUS the accumulated discrepancy between the
  squared increments of \<open>X\<close> and the increments of the compensator \<open>A\<close>.

  The first term is a simple integral, to which the isometry applies and whose
  contribution is controlled by @{text increment_second_moment_bound}; the
  second has to vanish as the mesh goes to zero, and its second moment involves
  a fourth moment of the increments, so no fixed-partition argument bounds it.

  Note @{term A} is arbitrary: the identity is pure algebra and uses no property of
  either process.
\<close>

lemma compensated_square_decomposition:
  fixes X A :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  shows "(X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2 - (A (t n) \<omega> - A (t 0) \<omega>)
           = simple_itg (\<lambda>k \<omega>. 2 * (X (t k) \<omega> - X (t 0) \<omega>)) X t n \<omega>
             + (\<Sum>k<n. ((X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2
                         - (A (t (Suc k)) \<omega> - A (t k) \<omega>)))"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have sq: "(X (t (Suc n)) \<omega> - X (t 0) \<omega>)\<^sup>2
          = (X (t n) \<omega> - X (t 0) \<omega>)\<^sup>2
            + 2 * (X (t n) \<omega> - X (t 0) \<omega>) * (X (t (Suc n)) \<omega> - X (t n) \<omega>)
            + (X (t (Suc n)) \<omega> - X (t n) \<omega>)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  show ?case
    using Suc.IH by (simp add: sq simple_itg_Suc algebra_simps)
qed

subsection \<open>The isometry in process form\<close>
text \<open>
  The isometry also holds as a statement about PROCESSES, not just expectations:
  the compensator of the square of the integral is the integral of \<open>H\<^sup>2\<close> against the
  squared increments. This is the form that
  \<open>quadratic variation of (integral H dX) = integral of H\<^sup>2 against d[X]\<close>
  takes for a simple integrand.
\<close>

theorem ito_isometry_process:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>k. H k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H k \<omega>)\<^sup>2)"
    and H_bdd: "\<And>k \<omega>. \<bar>H k \<omega>\<bar> \<le> B"
  shows "martingale M (\<lambda>k. F (t k)) 0
           (\<lambda>n \<omega>. (simple_itg H X t n \<omega>)\<^sup>2
                    - (\<Sum>k<n. (H k \<omega>)\<^sup>2
                              * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2))"
proof -
  interpret I: sq_int_martingale M "\<lambda>k. F (t k)" "simple_itg H X t"
  proof (intro sq_int_martingale.intro sq_int_martingale_axioms.intro)
    show "nat_sigma_finite_filtered_measure M (\<lambda>k. F (t k))"
      by (rule nat_filtered_of_sampled[OF X t0 tmono])
    show "martingale M (\<lambda>k. F (t k)) 0 (simple_itg H X t)"
      by (rule martingale_simple_itg[OF X t0 tmono sq H_meas H_sq])
    show "integrable M (\<lambda>\<omega>. (simple_itg H X t m \<omega>)\<^sup>2)" for m
      by (rule simple_itg_sq_integrable[OF X t0 tmono sq H_meas H_sq H_bdd])
  qed
  have qv: "qvar (simple_itg H X t) m \<omega>
      = (\<Sum>k<m. (H k \<omega>)\<^sup>2 * (X (t (Suc k)) \<omega> - X (t k) \<omega>)\<^sup>2)" for m \<omega>
    by (simp add: qvar_def simple_itg_Suc power_mult_distrib)
  have "martingale M (\<lambda>k. F (t k)) 0
      (\<lambda>n \<omega>. (simple_itg H X t n \<omega>)\<^sup>2 - qvar (simple_itg H X t) n \<omega>)"
    by (rule I.qvar_compensates)
  thus ?thesis by (simp add: qv)
qed

subsection \<open>Linearity, and the isometry in difference form\<close>
text \<open>
  The integral is linear in the integrand, so the isometry applies to a DIFFERENCE
  of integrands. That is the form the \<open>L\<^sup>2\<close> extension uses: it says the map
  \<open>H |-> simple_itg H X t n\<close> is an isometry from the integrands with the measure
  \<open>H\<^sup>2 d[X]\<close> into \<open>L\<^sup>2 M\<close>, so a Cauchy sequence of simple integrands has a Cauchy
  sequence of integrals, and the integral extends to the closure.
\<close>

lemma simple_itg_diff:
  "simple_itg (\<lambda>k \<omega>. H k \<omega> - H' k \<omega>) X t n \<omega>
     = simple_itg H X t n \<omega> - simple_itg H' X t n \<omega>"
proof -
  have "(\<Sum>k<n. (H k \<omega> - H' k \<omega>) * (X (t (Suc k)) \<omega> - X (t k) \<omega>))
      = (\<Sum>k<n. H k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>)
                 - H' k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))"
    by (simp add: left_diff_distrib)
  also have "\<dots> = (\<Sum>k<n. H k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))
                  - (\<Sum>k<n. H' k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))"
    by (rule sum_subtractf)
  finally show ?thesis unfolding simple_itg_def .
qed
theorem ito_isometry_simple_diff:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and t :: "nat \<Rightarrow> real"
  assumes X: "martingale M F (0::real) X"
    and t0: "\<And>k. 0 \<le> t k" and tmono: "mono t"
    and sq: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. (X u \<omega>)\<^sup>2)"
    and H_meas: "\<And>k. H k \<in> borel_measurable (F (t k))"
    and H_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H k \<omega>)\<^sup>2)"
    and H_bdd: "\<And>k \<omega>. \<bar>H k \<omega>\<bar> \<le> B"
    and H'_meas: "\<And>k. H' k \<in> borel_measurable (F (t k))"
    and H'_sq: "\<And>k. integrable M (\<lambda>\<omega>. (H' k \<omega>)\<^sup>2)"
    and H'_bdd: "\<And>k \<omega>. \<bar>H' k \<omega>\<bar> \<le> B"
  shows "(\<integral>\<omega>. (simple_itg H X t n \<omega> - simple_itg H' X t n \<omega>)\<^sup>2 \<partial>M)
           = (\<integral>\<omega>. (\<Sum>k<n. ((H k \<omega> - H' k \<omega>)
                            * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2) \<partial>M)"
proof -
  interpret S: sq_int_martingale M "\<lambda>k. F (t k)" "\<lambda>k. X (t k)"
    by (rule sq_int_martingale_of_sampled[OF X t0 tmono sq])
  have HM: "H k \<in> borel_measurable M" for k
    using measurable_from_subalg[OF S.subalgebras[of k] H_meas[of k]] by simp
  have H'M: "H' k \<in> borel_measurable M" for k
    using measurable_from_subalg[OF S.subalgebras[of k] H'_meas[of k]] by simp
  define G where "G = (\<lambda>k \<omega>. H k \<omega> - H' k \<omega>)"
  have G_meas: "G k \<in> borel_measurable (F (t k))" for k
    unfolding G_def using H_meas[of k] H'_meas[of k] by measurable
  have G_sq: "integrable M (\<lambda>\<omega>. (G k \<omega>)\<^sup>2)" for k
  proof -
    have "integrable M (\<lambda>\<omega>. 2 * (H k \<omega>)\<^sup>2 + 2 * (H' k \<omega>)\<^sup>2)"
      using H_sq[of k] H'_sq[of k] by simp
    thus ?thesis
    proof (rule Bochner_Integration.integrable_bound)
      show "(\<lambda>\<omega>. (G k \<omega>)\<^sup>2) \<in> borel_measurable M"
        unfolding G_def using HM[of k] H'M[of k] by measurable      show "AE \<omega> in M. norm ((G k \<omega>)\<^sup>2)
          \<le> norm (2 * (H k \<omega>)\<^sup>2 + 2 * (H' k \<omega>)\<^sup>2)"
      proof (intro always_eventually allI)
        fix \<omega>
        have "(G k \<omega>)\<^sup>2 = (H k \<omega> + (- H' k \<omega>))\<^sup>2" unfolding G_def by simp
        also have "\<dots> \<le> 2 * (H k \<omega>)\<^sup>2 + 2 * (- H' k \<omega>)\<^sup>2"
          by (rule sq_sum_le_two)
        finally show "norm ((G k \<omega>)\<^sup>2)
            \<le> norm (2 * (H k \<omega>)\<^sup>2 + 2 * (H' k \<omega>)\<^sup>2)" by simp
      qed
    qed
  qed
  have G_bdd: "\<bar>G k \<omega>\<bar> \<le> 2 * B" for k \<omega>
  proof -
    have "\<bar>G k \<omega>\<bar> \<le> \<bar>H k \<omega>\<bar> + \<bar>H' k \<omega>\<bar>"
      unfolding G_def by (rule abs_triangle_ineq4)
    also have "\<dots> \<le> B + B" using H_bdd[of k \<omega>] H'_bdd[of k \<omega>] by (rule add_mono)
    finally show ?thesis by simp
  qed
  have "(\<integral>\<omega>. (simple_itg G X t n \<omega>)\<^sup>2 \<partial>M)
          = (\<integral>\<omega>. (\<Sum>k<n. (G k \<omega> * (X (t (Suc k)) \<omega> - X (t k) \<omega>))\<^sup>2) \<partial>M)"
    by (rule ito_isometry_simple[OF X t0 tmono sq G_meas G_sq G_bdd])
  thus ?thesis unfolding G_def by (simp add: simple_itg_diff)
qed

end
