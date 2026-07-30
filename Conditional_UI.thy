section \<open>Uniform integrability of conditional expectations\<close>

text \<open>
  Plan step A3 (STATUS.md 25h), part (a). Two classical facts absent from the
  distribution and the AFP:

  1. Absolute continuity of the integral: for integrable \<open>f\<close> and \<open>e > 0\<close> there
     is \<open>\<delta> > 0\<close> such that \<open>\<integral>\<^bsub>A\<^esub> \<bar>f\<bar> \<le> e\<close> whenever \<open>measure A < \<delta>\<close>.

  2. The family of conditional expectations \<open>cond_exp M (G n) Y\<close> of a FIXED
     integrable \<open>Y\<close> is uniformly integrable (in the sense of
     \<open>Vitali_Convergence.unif_integrable\<close>), with a truncation level uniform in
     the sub-\<open>\<sigma>\<close>-algebra.

  These feed the domination-free optional stopping theorem (A3 part (b)): in the
  round-up sampling argument the sampled values are conditional expectations of
  the horizon value, so Vitali's convergence theorem replaces dominated
  convergence, eliminating the integrable-running-supremum hypothesis that an
  arbitrary \<open>L\<^sup>1\<close> martingale does not satisfy.
\<close>

theory Conditional_UI
  imports Vitali_Convergence Increment_Moments
begin

subsection \<open>Absolute continuity of the integral\<close>

lemma (in finite_measure) integral_abs_small_sets:
  fixes f :: "'a \<Rightarrow> real"
  assumes f: "integrable M f" and e: "0 < e"
  shows "\<exists>\<delta>>0. \<forall>A\<in>sets M. measure M A < \<delta> \<longrightarrow> (\<integral>x\<in>A. \<bar>f x\<bar> \<partial>M) \<le> e"
proof -
  note fm[measurable] = borel_measurable_integrable[OF f]
  have tl: "(\<lambda>n. \<integral>x. max 0 (\<bar>f x\<bar> - real n) \<partial>M) \<longlonglongrightarrow> (\<integral>x. (0::real) \<partial>M)"
  proof (rule integral_dominated_convergence)
    show "(\<lambda>x. 0::real) \<in> borel_measurable M" by simp
    show "(\<lambda>x. max 0 (\<bar>f x\<bar> - real n)) \<in> borel_measurable M" for n
      by measurable
    show "integrable M (\<lambda>x. \<bar>f x\<bar>)" using f by (rule integrable_abs)
    show "AE x in M. (\<lambda>n. max 0 (\<bar>f x\<bar> - real n)) \<longlonglongrightarrow> 0"
    proof (intro AE_I2 tendsto_eventually)
      fix x
      obtain N where "\<bar>f x\<bar> \<le> real N" using real_arch_simple by blast
      hence "max 0 (\<bar>f x\<bar> - real n) = 0" if "N \<le> n" for n
        using that by (simp add: max_def)
      thus "\<forall>\<^sub>F n in sequentially. max 0 (\<bar>f x\<bar> - real n) = 0"
        unfolding eventually_sequentially by blast
    qed
    show "AE x in M. norm (max 0 (\<bar>f x\<bar> - real n)) \<le> \<bar>f x\<bar>" for n
      by (intro AE_I2) auto
  qed
  have "eventually (\<lambda>n. (\<integral>x. max 0 (\<bar>f x\<bar> - real n) \<partial>M) < e/2) sequentially"
    by (rule order_tendstoD(2)[OF tl]) (use e in simp)
  then obtain N where N: "(\<integral>x. max 0 (\<bar>f x\<bar> - real N) \<partial>M) < e/2"
    unfolding eventually_sequentially by blast
  define \<delta> where "\<delta> = e / (2 * (real N + 1))"
  have d0: "0 < \<delta>" unfolding \<delta>_def using e by simp
  have bound: "(\<integral>x\<in>A. \<bar>f x\<bar> \<partial>M) \<le> e" if A: "A \<in> sets M" and mA: "measure M A < \<delta>" for A
  proof -
    have itail: "integrable M (\<lambda>x. max 0 (\<bar>f x\<bar> - real N))"
      by (rule integrable_tail[OF f]) simp
    have i1: "integrable M (\<lambda>x. indicator A x * \<bar>f x\<bar>)"
      by (subst mult.commute)
         (rule integrable_real_mult_indicator[OF A integrable_abs[OF f]])
    have i2: "integrable M (\<lambda>x. indicator A x * max 0 (\<bar>f x\<bar> - real N))"
      by (subst mult.commute) (rule integrable_real_mult_indicator[OF A itail])
    have i3: "integrable M (\<lambda>x. indicator A x * real N)"
      by (subst mult.commute)
         (rule integrable_real_mult_indicator[OF A integrable_const])
    have "(\<integral>x\<in>A. \<bar>f x\<bar> \<partial>M) = (\<integral>x. indicator A x * \<bar>f x\<bar> \<partial>M)"
      unfolding set_lebesgue_integral_def by (simp add: mult.commute)
    also have "\<dots> \<le> (\<integral>x. indicator A x * max 0 (\<bar>f x\<bar> - real N)
                        + indicator A x * real N \<partial>M)"
    proof (rule integral_mono[OF i1])
      show "integrable M (\<lambda>x. indicator A x * max 0 (\<bar>f x\<bar> - real N)
                        + indicator A x * real N)"
        by (rule Bochner_Integration.integrable_add[OF i2 i3])
      show "indicator A x * \<bar>f x\<bar>
              \<le> indicator A x * max 0 (\<bar>f x\<bar> - real N) + indicator A x * real N"
        for x
        by (cases "x \<in> A") (auto simp: indicator_def)
    qed
    also have "\<dots> = (\<integral>x. indicator A x * max 0 (\<bar>f x\<bar> - real N) \<partial>M)
                    + (\<integral>x. indicator A x * real N \<partial>M)"
      by (rule Bochner_Integration.integral_add[OF i2 i3])
    also have "(\<integral>x. indicator A x * max 0 (\<bar>f x\<bar> - real N) \<partial>M)
                \<le> (\<integral>x. max 0 (\<bar>f x\<bar> - real N) \<partial>M)"
      by (rule integral_mono[OF i2 itail]) (auto simp: indicator_def)
    also have "(\<integral>x. indicator A x * real N \<partial>M) = real N * measure M A"
      using A by (simp add: mult.commute)
    also have "real N * measure M A \<le> real N * \<delta>"
      using mA by (intro mult_left_mono) simp_all
    also have "real N * \<delta> \<le> e/2"
    proof -
      have "real N * \<delta> = real N * e / (2 * (real N + 1))"
        unfolding \<delta>_def by simp
      also have "\<dots> \<le> e/2"
      proof (rule mult_imp_div_pos_le)
        show "0 < 2 * (real N + 1)" by simp
        show "real N * e \<le> e / 2 * (2 * (real N + 1))"
          using e by (simp add: field_simps)
      qed
      finally show ?thesis .
    qed
    finally show ?thesis using N by simp
  qed
  from d0 bound show ?thesis by blast
qed

subsection \<open>Uniform integrability of a family of conditional expectations\<close>

text \<open>
  The truncation level \<open>K = E\<bar>Y\<bar>/\<delta> + 1\<close> works simultaneously for every
  sub-\<open>\<sigma>\<close>-algebra: the exceedance set \<open>{cond_exp \<bar>Y\<bar> > K}\<close> is measurable in the
  SUB-algebra, so the tail integral of the conditional expectation collapses to
  a set integral of \<open>\<bar>Y\<bar>\<close> itself over a set of measure \<open>< \<delta>\<close>.
\<close>

lemma (in prob_space) cond_exp_family_unif_integrable:
  fixes Y :: "'a \<Rightarrow> real" and G :: "nat \<Rightarrow> 'a measure"
  assumes Y: "integrable M Y"
    and sub: "\<And>n. sigma_finite_subalgebra M (G n)"
  shows "unif_integrable M (\<lambda>n. cond_exp M (G n) Y)"
  unfolding unif_integrable_def
proof (intro conjI allI impI)
  fix n show "integrable M (cond_exp M (G n) Y)" by (rule integrable_cond_exp)
next
    fix e :: real assume e: "0 < e"
    obtain \<delta> where d0: "0 < \<delta>"
      and dl: "\<And>A. A \<in> sets M \<Longrightarrow> measure M A < \<delta> \<Longrightarrow> (\<integral>x\<in>A. \<bar>Y x\<bar> \<partial>M) \<le> e"
      using integral_abs_small_sets[OF Y e] by blast
    define K where "K = (\<integral>x. \<bar>Y x\<bar> \<partial>M) / \<delta> + 1"
    have EY0: "0 \<le> (\<integral>x. \<bar>Y x\<bar> \<partial>M)" by simp
    have K1: "1 \<le> K" unfolding K_def using EY0 d0 by simp
    have K0: "0 < K" using K1 by simp
    have iY: "integrable M (\<lambda>x. \<bar>Y x\<bar>)" using Y by (rule integrable_abs)
    have tail: "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K)) \<partial>M) \<le> ennreal e"
      for n
    proof -
      let ?g = "cond_exp M (G n) (\<lambda>x. \<bar>Y x\<bar>)"
      have gm: "?g \<in> borel_measurable (G n)" by (rule borel_measurable_cond_exp)
      have gmM: "?g \<in> borel_measurable M"
        by (rule measurable_from_subalg[OF sigma_finite_subalgebra.subalg[OF sub] gm])
      have sp: "space (G n) = space M"
        using sigma_finite_subalgebra.subalg[OF sub] unfolding subalgebra_def by simp
      have spG: "space M \<in> sets (G n)"
        using sets.top[of "G n"] sp by simp
      have contr: "AE x in M. \<bar>cond_exp M (G n) Y x\<bar> \<le> ?g x"
        using sigma_finite_subalgebra.cond_exp_contraction[OF sub Y] by simp
      have g0: "AE x in M. 0 \<le> ?g x"
      proof -
        have eq: "(\<lambda>x. \<bar>\<bar>Y x\<bar>\<bar>) = (\<lambda>x. \<bar>Y x\<bar>)" by simp
        have "AE x in M. \<bar>?g x\<bar> \<le> cond_exp M (G n) (\<lambda>x. \<bar>\<bar>Y x\<bar>\<bar>) x"
          using sigma_finite_subalgebra.cond_exp_contraction[OF sub iY] by simp
        thus ?thesis unfolding eq by (rule eventually_mono) auto
      qed
      define A where "A = {x \<in> space M. K < ?g x}"
      have Asub: "A \<in> sets (G n)"
        unfolding A_def sp[symmetric] using gm by measurable
      have AM: "A \<in> sets M"
        using Asub sigma_finite_subalgebra.subalg[OF sub]
        unfolding subalgebra_def by blast
      have Eg: "(\<integral>x. ?g x \<partial>M) = (\<integral>x. \<bar>Y x\<bar> \<partial>M)"
        by (rule expectation_cond_exp[OF sub spG iY])
      have mA: "measure M A < \<delta>"
      proof -
        have KgM: "{x \<in> space M. K \<le> ?g x} \<in> sets M"
          using gmM by measurable
        have "measure M A \<le> measure M {x \<in> space M. K \<le> ?g x}"
          by (intro finite_measure_mono KgM) (auto simp: A_def)
        also have "\<dots> \<le> (\<integral>x. ?g x \<partial>M) / K"
        proof (rule integral_Markov_inequality_measure)
          show "integrable M ?g" by (rule integrable_cond_exp)
          show "space M \<in> sets M" by (rule sets.top)
          show "AE x in M. 0 \<le> ?g x" by (rule g0)
          show "0 < K" by (rule K0)
        qed
        also have "\<dots> = (\<integral>x. \<bar>Y x\<bar> \<partial>M) / K" unfolding Eg by (rule refl)
        also have "\<dots> < \<delta>"
        proof -
          have "\<delta> * K = (\<integral>x. \<bar>Y x\<bar> \<partial>M) + \<delta>"
            unfolding K_def using d0 by (simp add: field_simps)
          hence "(\<integral>x. \<bar>Y x\<bar> \<partial>M) < \<delta> * K" using d0 by simp
          thus ?thesis using K0 by (simp add: pos_divide_less_eq)
        qed
        finally show ?thesis .
      qed
      have YA: "(\<integral>x\<in>A. \<bar>Y x\<bar> \<partial>M) \<le> e" by (rule dl[OF AM mA])
      have gA: "(\<integral>x\<in>A. ?g x \<partial>M) = (\<integral>x\<in>A. \<bar>Y x\<bar> \<partial>M)"
        by (rule sigma_finite_subalgebra.cond_exp_set_integral
              [OF sub iY Asub, symmetric])
      have ig: "integrable M (\<lambda>x. indicator A x * ?g x)"
        by (subst mult.commute)
           (rule integrable_real_mult_indicator[OF AM integrable_cond_exp])
      have step1: "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K)) \<partial>M)
          \<le> (\<integral>\<^sup>+ x. ennreal (indicator A x * ?g x) \<partial>M)"
      proof (rule nn_integral_mono_AE)
        show "AE x in M. ennreal (max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K))
                \<le> ennreal (indicator A x * ?g x)"
          using contr g0 AE_space
        proof eventually_elim
          case (elim x)
          show ?case
          proof (cases "K < ?g x")
            case True
            hence xA: "x \<in> A" using elim unfolding A_def by simp
            have "max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K) \<le> ?g x"
              using elim K0 by (intro max.boundedI) linarith+
            also have "?g x = indicator A x * ?g x" using xA by simp
            finally show ?thesis by (rule ennreal_leI)
          next
            case False
            have le0: "\<bar>cond_exp M (G n) Y x\<bar> - K \<le> 0"
              using elim False by linarith
            hence z: "max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K) = 0"
              by (simp add: max_def)
            show ?thesis unfolding z
              using elim by (auto simp: indicator_def intro!: ennreal_leI)
          qed
        qed
      qed
      have nn: "AE x in M. 0 \<le> indicator A x * ?g x"
        using g0 by (rule eventually_mono) (auto simp: indicator_def)
      have step2: "(\<integral>\<^sup>+ x. ennreal (indicator A x * ?g x) \<partial>M)
          = ennreal (\<integral>x. indicator A x * ?g x \<partial>M)"
        by (rule nn_integral_eq_integral[OF ig nn])
      have step3: "(\<integral>x. indicator A x * ?g x \<partial>M) = (\<integral>x\<in>A. ?g x \<partial>M)"
        unfolding set_lebesgue_integral_def by (simp add: mult.commute)
      have "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K)) \<partial>M)
          \<le> ennreal (\<integral>x\<in>A. \<bar>Y x\<bar> \<partial>M)"
        using step1 step2 step3 gA by simp
      also have "\<dots> \<le> ennreal e" by (rule ennreal_leI[OF YA])
      finally show ?thesis .
    qed
    show "\<exists>K\<ge>0. \<forall>n.
        (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>cond_exp M (G n) Y x\<bar> - K)) \<partial>M) \<le> ennreal e"
      using less_imp_le[OF K0] tail by blast
qed

subsection \<open>Transfer along almost-everywhere equality, and the averaging form\<close>

lemma unif_integrable_cong_AE:
  fixes f g :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes ui: "unif_integrable M f"
    and gint: "\<And>n. integrable M (g n)"
    and ae: "\<And>n. AE x in M. f n x = g n x"
  shows "unif_integrable M g"
  unfolding unif_integrable_def
proof (intro conjI allI impI gint)
  fix e :: real assume e: "0 < e"
  from ui e obtain K where K: "0 \<le> K"
    and tl: "\<forall>n. (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal e"
    unfolding unif_integrable_def by blast
  have "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g n x\<bar> - K)) \<partial>M) \<le> ennreal e" for n
  proof -
    have "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g n x\<bar> - K)) \<partial>M)
        = (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M)"
      by (rule nn_integral_cong_AE) (use ae[of n] in \<open>auto elim: eventually_mono\<close>)
    also have "\<dots> \<le> ennreal e" using tl by blast
    finally show ?thesis .
  qed
  with K show "\<exists>K\<ge>0. \<forall>n.
      (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g n x\<bar> - K)) \<partial>M) \<le> ennreal e" by blast
qed

text \<open>
  The form the optional-stopping rework consumes directly: a sequence that
  AVERAGES a fixed integrable \<open>Y\<close> over sub-\<open>\<sigma>\<close>-algebras (the set-integral
  identity of optional sampling) IS the corresponding family of conditional
  expectations, hence uniformly integrable.
\<close>

lemma (in prob_space) unif_integrable_of_averaging:
  fixes Y :: "'a \<Rightarrow> real" and f :: "nat \<Rightarrow> 'a \<Rightarrow> real" and G :: "nat \<Rightarrow> 'a measure"
  assumes Y: "integrable M Y"
    and sub: "\<And>n. sigma_finite_subalgebra M (G n)"
    and int: "\<And>n. integrable M (f n)"
    and meas: "\<And>n. f n \<in> borel_measurable (G n)"
    and ident: "\<And>n A. A \<in> sets (G n) \<Longrightarrow> (\<integral>x\<in>A. Y x \<partial>M) = (\<integral>x\<in>A. f n x \<partial>M)"
  shows "unif_integrable M f"
proof (rule unif_integrable_cong_AE[OF cond_exp_family_unif_integrable[OF Y sub] int])
  show "AE x in M. cond_exp M (G n) Y x = f n x" for n
    by (rule sigma_finite_subalgebra.cond_exp_charact[OF sub ident Y int meas])
qed

end