section \<open>From \<open>L\<^sup>2\<close>-Cauchy to an almost-everywhere limit\<close>

(*<*)
theory L2_Limits
  imports "Martingale_Sampling.Vitali_Convergence"
begin

(*>*)

text \<open>
  Machinery for the \<open>L\<^sup>2\<close> closure of the simple stochastic integrals (the last
  layer of open task 15).

  The classical route is Riesz-Fischer. Its hard step -- extracting from an
  \<open>L\<^sup>1\<close>-Cauchy sequence a subsequence that is Cauchy almost everywhere -- is
  already in the distribution as
  \<open>HOL-Analysis.Set_Integral.cauchy_L1_AE_cauchy_subseq\<close>. What has to be supplied
  here is the passage from \<open>L\<^sup>2\<close>-Cauchy to \<open>L\<^sup>1\<close>-Cauchy, and then the identification
  of the almost-everywhere limit.

  The \<open>L\<^sup>2\<close>-to-\<open>L\<^sup>1\<close> step needs no Cauchy-Schwarz inequality: the pointwise
  arithmetic-geometric bound \<open>\<bar>h\<bar> \<le> e/2 + h\<^sup>2/(2e)\<close>, valid for every \<open>e > 0\<close>
  because it rearranges to \<open>0 \<le> (e - \<bar>h\<bar>)\<^sup>2\<close>, integrates on a probability space to
  \<open>\<bar>\<bar>h\<bar>\<bar>\<^sub>1 \<le> e/2 + \<bar>\<bar>h\<bar>\<bar>\<^sub>2\<^sup>2/(2e)\<close>, and choosing \<open>e\<close> as the \<open>L\<^sup>2\<close> norm gives the
  usual bound.
\<close>
subsection \<open>The arithmetic-geometric bound\<close>

lemma abs_le_am_gm:
  fixes h e :: real
  assumes e: "0 < e"
  shows "\<bar>h\<bar> \<le> e / 2 + h\<^sup>2 / (2 * e)"
proof -
  have "0 \<le> (e - \<bar>h\<bar>)\<^sup>2" by simp
  then have "2 * e * \<bar>h\<bar> \<le> e\<^sup>2 + \<bar>h\<bar>\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  then have "2 * e * \<bar>h\<bar> \<le> e\<^sup>2 + h\<^sup>2" by simp
  thus ?thesis using e by (simp add: field_simps power2_eq_square)
qed

lemma sq_diff_le_two: "(a - b)\<^sup>2 \<le> 2 * a\<^sup>2 + 2 * b\<^sup>2" for a b :: real
proof -
  have "0 \<le> (a + b)\<^sup>2" by simp
  thus ?thesis by (simp add: power2_eq_square algebra_simps)
qed

subsection \<open>An \<open>L\<^sup>2\<close> bound gives an \<open>L\<^sup>1\<close> bound\<close>
lemma (in prob_space) integral_abs_le_of_sq:
  fixes h :: "'a \<Rightarrow> real"
  assumes hsq: "integrable M (\<lambda>\<omega>. (h \<omega>)\<^sup>2)" and hint: "integrable M h"
    and e: "0 < e"
  shows "(\<integral>\<omega>. \<bar>h \<omega>\<bar> \<partial>M) \<le> e / 2 + (\<integral>\<omega>. (h \<omega>)\<^sup>2 \<partial>M) / (2 * e)"
proof -
  have "(\<integral>\<omega>. \<bar>h \<omega>\<bar> \<partial>M) \<le> (\<integral>\<omega>. e / 2 + (h \<omega>)\<^sup>2 / (2 * e) \<partial>M)"
  proof (rule integral_mono)
    show "integrable M (\<lambda>\<omega>. \<bar>h \<omega>\<bar>)" using hint by simp
    show "integrable M (\<lambda>\<omega>. e / 2 + (h \<omega>)\<^sup>2 / (2 * e))"
      using hsq by simp
    show "\<bar>h \<omega>\<bar> \<le> e / 2 + (h \<omega>)\<^sup>2 / (2 * e)" for \<omega>
      by (rule abs_le_am_gm[OF e])
  qed
  also have "(\<integral>\<omega>. e / 2 + (h \<omega>)\<^sup>2 / (2 * e) \<partial>M)
             = e / 2 + (\<integral>\<omega>. (h \<omega>)\<^sup>2 \<partial>M) / (2 * e)"
    using hsq by (simp add: prob_space)
  finally show ?thesis .
qed

subsection \<open>\<open>L\<^sup>2\<close>-Cauchy implies \<open>L\<^sup>1\<close>-Cauchy\<close>

text \<open>
  Given a sequence Cauchy in \<open>L\<^sup>2\<close>, the bound above with \<open>e\<close> chosen small makes it
  Cauchy in \<open>L\<^sup>1\<close>, in exactly the shape
  \<open>cauchy_L1_AE_cauchy_subseq\<close> expects.
\<close>

lemma (in prob_space) cauchy_L2_imp_cauchy_L1:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes fint: "\<And>m. integrable M (f m)"
    and fsq: "\<And>m. integrable M (\<lambda>\<omega>. (f m \<omega>)\<^sup>2)"
    and cauchy2: "\<And>d. 0 < d \<Longrightarrow>
        \<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. (\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M) < d"
    and e: "0 < e"
  shows "\<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. (\<integral>\<omega>. \<bar>f i \<omega> - f j \<omega>\<bar> \<partial>M) < e"
proof -
  define a where "a = e / 2"
  have a: "0 < a" unfolding a_def using e by simp
  define d where "d = a * e"
  have d: "0 < d" unfolding d_def using a e by simp
  from cauchy2[OF d] obtain N where
    N: "\<And>i j. i \<ge> N \<Longrightarrow> j \<ge> N \<Longrightarrow> (\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M) < d" by blast
  show ?thesis
  proof (intro exI[of _ N] allI impI)
    fix i j assume ij: "i \<ge> N" "j \<ge> N"
    have hsq: "integrable M (\<lambda>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2)"
    proof -
      have "integrable M (\<lambda>\<omega>. 2 * (f i \<omega>)\<^sup>2 + 2 * (f j \<omega>)\<^sup>2)"
        using fsq[of i] fsq[of j] by simp
      thus ?thesis
      proof (rule Bochner_Integration.integrable_bound)
        show "(\<lambda>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2) \<in> borel_measurable M"
          using fint[of i] fint[of j] by measurable
        show "AE \<omega> in M. norm ((f i \<omega> - f j \<omega>)\<^sup>2)
            \<le> norm (2 * (f i \<omega>)\<^sup>2 + 2 * (f j \<omega>)\<^sup>2)"
        proof (intro always_eventually allI)
          fix \<omega>
          have "(f i \<omega> - f j \<omega>)\<^sup>2 \<le> 2 * (f i \<omega>)\<^sup>2 + 2 * (f j \<omega>)\<^sup>2"
            by (rule sq_diff_le_two)          thus "norm ((f i \<omega> - f j \<omega>)\<^sup>2)
              \<le> norm (2 * (f i \<omega>)\<^sup>2 + 2 * (f j \<omega>)\<^sup>2)" by simp
        qed
      qed
    qed
    have hint: "integrable M (\<lambda>\<omega>. f i \<omega> - f j \<omega>)"
      using fint[of i] fint[of j] by simp
    have "(\<integral>\<omega>. \<bar>f i \<omega> - f j \<omega>\<bar> \<partial>M)
            \<le> a / 2 + (\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M) / (2 * a)"
      by (rule integral_abs_le_of_sq[OF hsq hint a])
    also have "\<dots> < a / 2 + d / (2 * a)"
      using N[OF ij] a by (simp add: divide_strict_right_mono)
    also have "a / 2 + d / (2 * a) = 3 * e / 4"
      unfolding d_def a_def using e
      by (simp add: field_simps power2_eq_square)
    also have "3 * e / 4 < e" using e by simp
    finally show "(\<integral>\<omega>. \<bar>f i \<omega> - f j \<omega>\<bar> \<partial>M) < e" .
  qed
qed

text \<open>On a probability space, \<open>L\<^sup>2\<close> is contained in \<open>L\<^sup>1\<close>.\<close>

lemma (in prob_space) integrable_of_sq_integrable:
  fixes h :: "'a \<Rightarrow> real"
  assumes hm: "h \<in> borel_measurable M" and hsq: "integrable M (\<lambda>\<omega>. (h \<omega>)\<^sup>2)"
  shows "integrable M h"
proof (rule Bochner_Integration.integrable_bound[of _ "\<lambda>\<omega>. 1 / 2 + (h \<omega>)\<^sup>2 / 2"])
  show "integrable M (\<lambda>\<omega>. 1 / 2 + (h \<omega>)\<^sup>2 / 2)" using hsq by simp
  show "h \<in> borel_measurable M" by (rule hm)
  show "AE \<omega> in M. norm (h \<omega>) \<le> norm (1 / 2 + (h \<omega>)\<^sup>2 / 2)"
  proof (intro always_eventually allI)
    fix \<omega>
    have "\<bar>h \<omega>\<bar> \<le> 1 / 2 + (h \<omega>)\<^sup>2 / (2 * 1)"
      by (rule abs_le_am_gm) simp
    thus "norm (h \<omega>) \<le> norm (1 / 2 + (h \<omega>)\<^sup>2 / 2)" by simp
  qed
qed

subsection \<open>The almost-everywhere limit of an \<open>L\<^sup>2\<close>-Cauchy sequence\<close>
text \<open>
  Riesz-Fischer, assembled: an \<open>L\<^sup>2\<close>-Cauchy sequence is \<open>L\<^sup>1\<close>-Cauchy by the previous
  lemma, hence has a subsequence that is Cauchy almost everywhere by
  \<open>cauchy_L1_AE_cauchy_subseq\<close>, and completeness of the reals turns that into an
  almost-everywhere limit.
\<close>

theorem (in prob_space) L2_cauchy_ae_limit:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes fint: "\<And>m. integrable M (f m)"
    and fsq: "\<And>m. integrable M (\<lambda>\<omega>. (f m \<omega>)\<^sup>2)"
    and cauchy2: "\<And>d. 0 < d \<Longrightarrow>
        \<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. (\<integral>\<omega>. (f i \<omega> - f j \<omega>)\<^sup>2 \<partial>M) < d"
  obtains r g where "strict_mono r"
    "g \<in> borel_measurable M"
    "AE \<omega> in M. (\<lambda>i. f (r i) \<omega>) \<longlonglongrightarrow> g \<omega>"
proof -
  have L1: "\<exists>N. \<forall>i\<ge>N. \<forall>j\<ge>N. (\<integral>\<omega>. norm (f i \<omega> - f j \<omega>) \<partial>M) < e" if "0 < e" for e
    using cauchy_L2_imp_cauchy_L1[OF fint fsq cauchy2 that] by simp
  obtain r where rmono: "strict_mono r"
    and rcauchy: "AE \<omega> in M. Cauchy (\<lambda>i. f (r i) \<omega>)"
    by (rule cauchy_L1_AE_cauchy_subseq[OF fint L1]) blast
  define g where "g = (\<lambda>\<omega>. lim (\<lambda>i. f (r i) \<omega>))"
  have conv: "AE \<omega> in M. (\<lambda>i. f (r i) \<omega>) \<longlonglongrightarrow> g \<omega>"
  proof -
    have "(\<lambda>i. f (r i) \<omega>) \<longlonglongrightarrow> g \<omega>" if "Cauchy (\<lambda>i. f (r i) \<omega>)" for \<omega>
    proof -
      from that have "convergent (\<lambda>i. f (r i) \<omega>)"
        by (rule real_Cauchy_convergent)
      thus ?thesis unfolding g_def by (rule convergent_LIMSEQ_iff[THEN iffD1])
    qed
    thus ?thesis using rcauchy by fastforce
  qed
  have gmeas: "g \<in> borel_measurable M"
  proof -
    have fm: "f (r i) \<in> borel_measurable M" for i
      using fint[of "r i"] by (rule borel_measurable_integrable)
    show ?thesis
      unfolding g_def by (rule borel_measurable_lim_metric[OF fm])
  qed
  show thesis by (rule that[OF rmono gmeas conv])
qed


(*<*)
end
(*>*)
