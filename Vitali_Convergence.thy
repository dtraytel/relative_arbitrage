section \<open>Uniform integrability and Vitali's convergence theorem\<close>

text \<open>
  Neither uniform integrability nor Vitali's convergence theorem exists
  anywhere in the Isabelle distribution or the AFP (@{text
  Vitali_Covering_Theorem} in HOL-Analysis is an unrelated result), so they are
  developed here from scratch for the proof of Lemma 2.3 of arXiv:2512.17702,
  which invokes Vitali's theorem to pass the covariation constraint through a
  weak limit.

  The classical statement: on a finite measure space, if a sequence is
  uniformly integrable and converges almost everywhere, then the limit is
  integrable and the convergence also holds in @{text "L\<^sup>1"}.
\<close>

theory Vitali_Convergence
  imports "HOL-Probability.Probability"
begin


definition unif_integrable :: "'a measure \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "unif_integrable M f \<longleftrightarrow>
     (\<forall>n. integrable M (f n)) \<and>
     (\<forall>e>0. \<exists>K\<ge>0. \<forall>n.
        (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal e)"

lemma unif_integrableD_int:
  "unif_integrable M f \<Longrightarrow> integrable M (f n)"
  unfolding unif_integrable_def by blast

lemma unif_integrableD_tail:
  assumes "unif_integrable M f" "0 < e"
  obtains K where "0 \<le> K"
    "\<And>n. (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal e"
  using assms unfolding unif_integrable_def by blast

text \<open>Basic algebra of the clamp used to truncate.\<close>

lemma clamp_diff_abs:
  fixes y K :: real
  assumes "0 \<le> K"
  shows "\<bar>y - max (- K) (min K y)\<bar> = max 0 (\<bar>y\<bar> - K)"
  using assms by (simp add: abs_if max_def min_def)

lemma clamp_abs_le:
  fixes y K :: real
  assumes "0 \<le> K"
  shows "\<bar>max (- K) (min K y)\<bar> \<le> K"
  using assms by (simp add: abs_if max_def min_def)

text \<open>The tail bound passes to an a.e. limit, by Fatou.\<close>

lemma tail_bound_limit:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes fm: "\<And>n. f n \<in> borel_measurable M" and gm: "g \<in> borel_measurable M"
    and conv: "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
    and bnd: "\<And>n. (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal e"
  shows "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g x\<bar> - K)) \<partial>M) \<le> ennreal e"
proof -
  define u where "u = (\<lambda>n x. ennreal (max 0 (\<bar>f n x\<bar> - K)))"
  define v where "v = (\<lambda>x. ennreal (max 0 (\<bar>g x\<bar> - K)))"
  have um: "u n \<in> borel_measurable M" for n
    unfolding u_def using fm by measurable
  have step: "(\<lambda>n. u n x) \<longlonglongrightarrow> v x" if "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
    unfolding u_def v_def
    by (intro tendsto_ennrealI tendsto_max tendsto_diff tendsto_rabs that
              tendsto_const)
  have "AE x in M. v x = liminf (\<lambda>n. u n x)"
  proof -
    have "v x = liminf (\<lambda>n. u n x)" if "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
      using step[OF that] by (intro lim_imp_Liminf[symmetric]) simp
    thus ?thesis using conv by fastforce
  qed
  then have "(\<integral>\<^sup>+ x. v x \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M)"
    by (rule nn_integral_cong_AE)
  also have "\<dots> \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
    by (intro nn_integral_liminf um)
  also have "\<dots> \<le> ennreal e"
  proof (rule order_trans[OF Liminf_le_Limsup])
    show "sequentially \<noteq> bot" by simp
    show "Limsup sequentially (\<lambda>n. integral\<^sup>N M (u n)) \<le> ennreal e"
      using bnd unfolding u_def by (intro Limsup_bounded always_eventually) blast
  qed
  finally show ?thesis unfolding v_def .
qed
text \<open>Integrability of the tail and of the truncation.\<close>

lemma integrable_tail:
  fixes h :: "'a \<Rightarrow> real"
  assumes h: "integrable M h" and K: "0 \<le> K"
  shows "integrable M (\<lambda>x. max 0 (\<bar>h x\<bar> - K))"
proof (rule Bochner_Integration.integrable_bound[OF integrable_abs[OF h]])
  show "(\<lambda>x. max 0 (\<bar>h x\<bar> - K)) \<in> borel_measurable M"
    using h by measurable
  show "AE x in M. norm (max 0 (\<bar>h x\<bar> - K)) \<le> norm \<bar>h x\<bar>"
    using K by simp
qed
lemma (in finite_measure) integrable_clamp:
  fixes h :: "'a \<Rightarrow> real"
  assumes h: "h \<in> borel_measurable M" and K: "0 \<le> K"
  shows "integrable M (\<lambda>x. max (- K) (min K (h x)))"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>_. K"])
  show "integrable M (\<lambda>_. K)" by (rule integrable_const)
  show "(\<lambda>x. max (- K) (min K (h x))) \<in> borel_measurable M"
    using h by measurable
  show "AE x in M. norm (max (- K) (min K (h x))) \<le> norm K"
    using clamp_abs_le[OF K] K by simp
qed
text \<open>Turning the tail bound from a nonnegative into a Bochner integral.\<close>

lemma tail_bochner_le:
  assumes h: "integrable M h" and e: "0 \<le> e" and K: "0 \<le> K"
    and bnd: "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>h x\<bar> - K)) \<partial>M) \<le> ennreal e"
  shows "(\<integral> x. max 0 (\<bar>h x\<bar> - K) \<partial>M) \<le> e"
proof -
  have i: "integrable M (\<lambda>x. max 0 (\<bar>h x\<bar> - K))"
    by (rule integrable_tail[OF h K])  have "ennreal (\<integral> x. max 0 (\<bar>h x\<bar> - K) \<partial>M)
        = (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>h x\<bar> - K)) \<partial>M)"
    by (rule nn_integral_eq_integral[symmetric, OF i]) simp
  also note bnd
  finally show ?thesis using e by simp
qed
subsection \<open>The limit of a uniformly integrable sequence is integrable\<close>

lemma (in finite_measure) unif_integrable_limit_integrable:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes ui: "unif_integrable M f"
    and gm: "g \<in> borel_measurable M"
    and conv: "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
  shows "integrable M g"
proof -
  have fm: "f n \<in> borel_measurable M" for n
    using unif_integrableD_int[OF ui] by (simp add: borel_measurable_integrable)
  obtain K where K: "0 \<le> K"
    and bnd: "\<And>n. (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal 1"
    using unif_integrableD_tail[OF ui zero_less_one] by blast
  have gb: "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g x\<bar> - K)) \<partial>M) \<le> ennreal 1"
    by (rule tail_bound_limit[OF fm gm conv bnd])
  have pt: "ennreal (norm (g x)) \<le> ennreal (max 0 (\<bar>g x\<bar> - K)) + ennreal K" for x
  proof -
    have a: "norm (g x) \<le> max 0 (\<bar>g x\<bar> - K) + K" using K by simp
    have "ennreal (norm (g x)) \<le> ennreal (max 0 (\<bar>g x\<bar> - K) + K)"
      by (rule ennreal_leI[OF a])
    also have "\<dots> = ennreal (max 0 (\<bar>g x\<bar> - K)) + ennreal K"
      by (rule ennreal_plus[OF max.cobounded1 K])
    finally show ?thesis .
  qed  have "(\<integral>\<^sup>+ x. ennreal (norm (g x)) \<partial>M)
        \<le> (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g x\<bar> - K)) + ennreal K \<partial>M)"
    by (intro nn_integral_mono pt)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g x\<bar> - K)) \<partial>M)
                  + (\<integral>\<^sup>+ x. ennreal K \<partial>M)"
    using gm by (intro nn_integral_add) auto
  also have "\<dots> < \<infinity>"
  proof -
    have fin: "emeasure M (space M) < \<top>"
      using finite_emeasure_space less_top by blast
    have k: "(\<integral>\<^sup>+ x. ennreal K \<partial>M) < \<infinity>"
      by (simp add: ennreal_mult_less_top fin)    have t: "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g x\<bar> - K)) \<partial>M) < \<infinity>"
      using gb by (simp add: le_less_trans)
    from k t show ?thesis by simp
  qed
  finally have "(\<integral>\<^sup>+ x. ennreal (norm (g x)) \<partial>M) < \<infinity>" .
  thus ?thesis by (rule integrableI_bounded[OF gm])
qed
subsection \<open>Vitali's convergence theorem\<close>

theorem (in finite_measure) vitali_convergence:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes ui: "unif_integrable M f"
    and gm: "g \<in> borel_measurable M"
    and conv: "AE x in M. (\<lambda>n. f n x) \<longlonglongrightarrow> g x"
  shows "(\<lambda>n. \<integral> x. \<bar>f n x - g x\<bar> \<partial>M) \<longlonglongrightarrow> 0"
proof (subst tendsto_iff, intro allI impI)
  fix e :: real assume e: "0 < e"
  have fint: "integrable M (f n)" for n by (rule unif_integrableD_int[OF ui])
  have fm: "f n \<in> borel_measurable M" for n
    using fint by (simp add: borel_measurable_integrable)
  have gint: "integrable M g"
    by (rule unif_integrable_limit_integrable[OF ui gm conv])
  have e4: "0 < e / 4" using e by simp
  obtain K where K: "0 \<le> K"
    and bnd: "\<And>n. (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal (e/4)"
    using unif_integrableD_tail[OF ui e4] by blast
  have gbnd: "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>g x\<bar> - K)) \<partial>M) \<le> ennreal (e/4)"
    by (rule tail_bound_limit[OF fm gm conv bnd])
  define T where "T = (\<lambda>y::real. max (- K) (min K y))"
  have Tabs: "\<bar>T y\<bar> \<le> K" for y
    unfolding T_def by (rule clamp_abs_le[OF K])
  have Tdiff: "\<bar>y - T y\<bar> = max 0 (\<bar>y\<bar> - K)" for y
    unfolding T_def by (rule clamp_diff_abs[OF K])
  have Tm: "(\<lambda>x. T (f n x)) \<in> borel_measurable M" for n
    unfolding T_def using fm by measurable
  have Tgm: "(\<lambda>x. T (g x)) \<in> borel_measurable M"
    unfolding T_def using gm by measurable

  text \<open>Integrability of the four pieces.\<close>
  have itf: "integrable M (\<lambda>x. max 0 (\<bar>f n x\<bar> - K))" for n
    by (rule integrable_tail[OF fint K])
  have itg: "integrable M (\<lambda>x. max 0 (\<bar>g x\<bar> - K))"
    by (rule integrable_tail[OF gint K])
  have idiff: "integrable M (\<lambda>x. \<bar>f n x - g x\<bar>) " for n
    using fint gint by simp
  have iT: "integrable M (\<lambda>x. \<bar>T (f n x) - T (g x)\<bar>)" for n
  proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>_. 2 * K"])
    show "integrable M (\<lambda>_. 2 * K)" by (rule integrable_const)
    show "(\<lambda>x. \<bar>T (f n x) - T (g x)\<bar>) \<in> borel_measurable M"
      using Tm Tgm by measurable
    show "AE x in M. norm \<bar>T (f n x) - T (g x)\<bar> \<le> norm (2 * K)"
    proof (intro always_eventually allI)
      fix x
      have "\<bar>T (f n x) - T (g x)\<bar> \<le> \<bar>T (f n x)\<bar> + \<bar>T (g x)\<bar>"
        by (rule abs_triangle_ineq4)
      also have "\<dots> \<le> K + K" using Tabs by (intro add_mono)
      finally show "norm \<bar>T (f n x) - T (g x)\<bar> \<le> norm (2 * K)"
        using K by simp
    qed
  qed

  text \<open>The truncated parts converge by dominated convergence.\<close>
  have dc: "(\<lambda>n. \<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M) \<longlonglongrightarrow> 0"
  proof -
    have "(\<lambda>n. \<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M) \<longlonglongrightarrow> (\<integral> x. 0 \<partial>M)"
    proof (rule integral_dominated_convergence[where w = "\<lambda>_. 2 * K"])
      show "(\<lambda>_. 0) \<in> borel_measurable M" by simp
      show "(\<lambda>x. \<bar>T (f i x) - T (g x)\<bar>) \<in> borel_measurable M" for i
        using Tm Tgm by measurable
      show "integrable M (\<lambda>_. 2 * K)" by (rule integrable_const)
      show "AE x in M. norm \<bar>T (f i x) - T (g x)\<bar> \<le> 2 * K" for i
      proof (intro always_eventually allI)
        fix x
        have "\<bar>T (f i x) - T (g x)\<bar> \<le> \<bar>T (f i x)\<bar> + \<bar>T (g x)\<bar>"
          by (rule abs_triangle_ineq4)
        also have "\<dots> \<le> K + K" using Tabs by (intro add_mono)
        finally show "norm \<bar>T (f i x) - T (g x)\<bar> \<le> 2 * K" by simp
      qed
      show "AE x in M. (\<lambda>i. \<bar>T (f i x) - T (g x)\<bar>) \<longlonglongrightarrow> 0"
      proof -
        have "(\<lambda>i. \<bar>T (f i x) - T (g x)\<bar>) \<longlonglongrightarrow> 0"
          if "(\<lambda>n. f n x) \<longlonglongrightarrow> g x" for x
        proof -
          have "(\<lambda>i. T (f i x)) \<longlonglongrightarrow> T (g x)"
            unfolding T_def
            by (intro tendsto_max tendsto_min that tendsto_const)
          hence "(\<lambda>i. T (f i x) - T (g x)) \<longlonglongrightarrow> 0" by (simp add: LIM_zero)
          thus ?thesis by (simp add: tendsto_rabs_zero)
        qed
        thus ?thesis using conv by fastforce
      qed
    qed
    thus ?thesis by simp
  qed

  text \<open>Pointwise triangle inequality through the truncation.\<close>
  have ptw: "\<bar>f n x - g x\<bar> \<le> max 0 (\<bar>f n x\<bar> - K)
                + \<bar>T (f n x) - T (g x)\<bar> + max 0 (\<bar>g x\<bar> - K)" for n x
  proof -
    have "\<bar>f n x - g x\<bar>
          = \<bar>(f n x - T (f n x)) + ((T (f n x) - T (g x)) + (T (g x) - g x))\<bar>"
      by simp
    also have "\<dots> \<le> \<bar>f n x - T (f n x)\<bar>
                     + \<bar>(T (f n x) - T (g x)) + (T (g x) - g x)\<bar>"
      by (rule abs_triangle_ineq)
    also have "\<dots> \<le> \<bar>f n x - T (f n x)\<bar>
                     + (\<bar>T (f n x) - T (g x)\<bar> + \<bar>T (g x) - g x\<bar>)"
      by (intro add_left_mono abs_triangle_ineq)
    finally show ?thesis
      using Tdiff[of "f n x"] Tdiff[of "g x"]
      by (simp add: abs_minus_commute add.assoc)
  qed

  text \<open>Assembling the bound.\<close>
  have le: "(\<integral> x. \<bar>f n x - g x\<bar> \<partial>M)
            \<le> e/4 + (\<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M) + e/4" for n
  proof -
    have "(\<integral> x. \<bar>f n x - g x\<bar> \<partial>M)
          \<le> (\<integral> x. max 0 (\<bar>f n x\<bar> - K)
                    + \<bar>T (f n x) - T (g x)\<bar> + max 0 (\<bar>g x\<bar> - K) \<partial>M)"
      using idiff itf iT itg by (intro integral_mono ptw) auto
    also have "\<dots> = (\<integral> x. max 0 (\<bar>f n x\<bar> - K) \<partial>M)
                    + (\<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M)
                    + (\<integral> x. max 0 (\<bar>g x\<bar> - K) \<partial>M)"
      using itf iT itg by simp
    also have "\<dots> \<le> e/4 + (\<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M) + e/4"
      using tail_bochner_le[OF fint less_imp_le[OF e4] K bnd]
            tail_bochner_le[OF gint less_imp_le[OF e4] K gbnd]
      by (intro add_mono order.refl)
    finally show ?thesis .
  qed

  text \<open>Conclusion.\<close>
  have half: "\<forall>\<^sub>F n in sequentially.
      (\<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M) < e/2"
    using dc e by (auto dest!: tendstoD[where e = "e/2"] simp: dist_real_def)
  show "\<forall>\<^sub>F n in sequentially. dist (\<integral> x. \<bar>f n x - g x\<bar> \<partial>M) 0 < e"
  proof (rule eventually_mono[OF half])
    fix n assume h: "(\<integral> x. \<bar>T (f n x) - T (g x)\<bar> \<partial>M) < e/2"
    have nonneg: "0 \<le> (\<integral> x. \<bar>f n x - g x\<bar> \<partial>M)" by simp
    have "(\<integral> x. \<bar>f n x - g x\<bar> \<partial>M) < e" using le[of n] h by simp
    thus "dist (\<integral> x. \<bar>f n x - g x\<bar> \<partial>M) 0 < e"
      using nonneg by (simp add: dist_real_def)
  qed
qed
subsection \<open>A sufficient condition: a uniform bound on a higher moment\<close>

text \<open>
  The practical criterion, and the one the paper's setting supplies: if the
  @{term p}-th moments are bounded uniformly for some @{term "p > 1"}, the family
  is uniformly integrable. This is the route by which a moment bound of the
  shape of Eq. (2.7) feeds into Lemma 2.3.
\<close>

lemma tail_le_moment:
  fixes y K p :: real
  assumes K: "0 < K" and p: "1 < p"
  shows "max 0 (\<bar>y\<bar> - K) \<le> (1 / K powr (p - 1)) * \<bar>y\<bar> powr p"
proof (cases "\<bar>y\<bar> \<le> K")
  case True
  have "0 \<le> (1 / K powr (p - 1)) * \<bar>y\<bar> powr p" using K by simp
  thus ?thesis using True by simp
next
  case False
  then have y: "0 < \<bar>y\<bar>" using K by simp
  have q: "0 < p - 1" using p by simp
  have "K powr (p - 1) \<le> \<bar>y\<bar> powr (p - 1)"
    using False K q by (simp add: powr_mono2)
  then have "\<bar>y\<bar> * K powr (p - 1) \<le> \<bar>y\<bar> * \<bar>y\<bar> powr (p - 1)"
    using y by (simp add: mult_left_mono)
  also have "\<bar>y\<bar> * \<bar>y\<bar> powr (p - 1) = \<bar>y\<bar> powr p"
    using y by (simp add: powr_mult_base)
  finally have "\<bar>y\<bar> * K powr (p - 1) \<le> \<bar>y\<bar> powr p" .
  then have "\<bar>y\<bar> \<le> \<bar>y\<bar> powr p / K powr (p - 1)"
    using K by (simp add: field_simps)
  moreover have "max 0 (\<bar>y\<bar> - K) \<le> \<bar>y\<bar>" using K by simp
  ultimately show ?thesis by (simp add: field_simps)
qed

lemma unif_integrable_of_moment_bound:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes int: "\<And>n. integrable M (f n)"
    and p: "1 < p" and C: "0 \<le> C"
    and mom: "\<And>n. (\<integral>\<^sup>+ x. ennreal (\<bar>f n x\<bar> powr p) \<partial>M) \<le> ennreal C"
  shows "unif_integrable M f"
  unfolding unif_integrable_def
proof (intro conjI allI impI int)
  fix e :: real assume e: "0 < e"
  define K where "K = max 1 ((C / e) powr (1 / (p - 1)))"
  have q: "0 < p - 1" using p by simp
  have K1: "1 \<le> K" unfolding K_def by simp
  have K0: "0 < K" using K1 by simp
  have Kq: "C / e \<le> K powr (p - 1)"
  proof -
    have "(C / e) powr (1 / (p - 1)) \<le> K" unfolding K_def by simp
    then have "((C / e) powr (1 / (p - 1))) powr (p - 1) \<le> K powr (p - 1)"
      using q by (simp add: powr_mono2)
    moreover have "((C / e) powr (1 / (p - 1))) powr (p - 1) = C / e"
      using C e q by (simp add: powr_powr)
    ultimately show ?thesis by simp
  qed
  have "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal e" for n
  proof -
    have "(\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M)
          \<le> (\<integral>\<^sup>+ x. ennreal ((1 / K powr (p-1)) * \<bar>f n x\<bar> powr p) \<partial>M)"
      by (intro nn_integral_mono ennreal_leI tail_le_moment[OF K0 p])
    also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (1 / K powr (p-1))
                            * ennreal (\<bar>f n x\<bar> powr p) \<partial>M)"
    proof (intro nn_integral_cong)
      fix x assume "x \<in> space M"
      have nn: "0 \<le> 1 / K powr (p-1)" using K0 by simp
      show "ennreal ((1 / K powr (p-1)) * \<bar>f n x\<bar> powr p)
            = ennreal (1 / K powr (p-1)) * ennreal (\<bar>f n x\<bar> powr p)"
        by (rule ennreal_mult'[OF nn])
    qed    also have "\<dots> = ennreal (1 / K powr (p-1))
                    * (\<integral>\<^sup>+ x. ennreal (\<bar>f n x\<bar> powr p) \<partial>M)"
      by (rule nn_integral_cmult) (use int in measurable)
    also have "\<dots> \<le> ennreal (1 / K powr (p-1)) * ennreal C"
      by (intro mult_left_mono mom) simp
    also have "\<dots> = ennreal (C / K powr (p-1))"
      using K0 C by (simp add: ennreal_mult' [symmetric])
    also have "\<dots> \<le> ennreal e"
    proof (intro ennreal_leI)
      have "C / K powr (p-1) \<le> e"
        using Kq e K0 by (simp add: field_simps)
      thus "C / K powr (p - 1) \<le> e" .
    qed
    finally show ?thesis .
  qed
  thus "\<exists>K\<ge>0. \<forall>n. (\<integral>\<^sup>+ x. ennreal (max 0 (\<bar>f n x\<bar> - K)) \<partial>M) \<le> ennreal e"
    using K0 by (intro exI[of _ K] conjI) auto
qed

end
