section \<open>Upper semicontinuity of the essential-infimum exit time (plan item 2.3)\<close>

text \<open>
  Larsson--Ruf (EJP 29 (2024), Proposition 2.2(ii)) --- which arXiv:2512.17702
  Proposition 2.4 defers to verbatim --- proves upper semicontinuity of the value
  function by combining two facts: \<open>g(P) = P\<hyphen>essinf \<tau>\<^sub>K\<close> is usc on the set of
  candidate laws, and Berge's maximum theorem turns a usc integrand into a usc
  supremum. Berge is already available (\<open>Section_2_Compactness.usc_sup_over_compact\<close>);
  this theory supplies the first fact.

  It has to be a separate leaf. The argument needs \<open>Value_Function\<close> (for the
  \<open>measure = 1\<close> characterisation of \<open>essinf\<close>) and \<open>Path_Tightness_Market\<close> (for the
  usc of \<open>\<tau>\<^sub>K\<close> itself and the Portmanteau bridge), and no existing theory imports
  both: \<open>Value_Function\<close> sits under the market/Ito branch while the path-topology
  content sits under the AFP Prokhorov branch.
\<close>

theory Section_2_Usc
  imports Path_Tightness_Market Value_Function
begin

subsection \<open>Superlevel sets of the exit time are closed\<close>

text \<open>
  The \<open>ennreal\<close> threshold is what \<open>ess_inf_time\<close> works with, so the case split on
  \<open>c\<close> is unavoidable. The \<open>top\<close> branch is not degenerate bookkeeping: there
  \<open>{\<tau> \<ge> \<top>}\<close> is EMPTY, because the exit time is a genuine real capped at \<open>T\<close>, and
  the whole space is its complement.
\<close>

lemma etime_superlevel_closed:
  fixes T :: real and c :: ennreal and A :: "'b::polish_space set"
  assumes T: "0 \<le> T" and A: "open A"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         c \<le> ennreal (etime T A (\<lambda>s w. w s) f)}"
proof -
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         ennreal (etime T A (\<lambda>s w. w s) f) < c}"
  proof (cases c rule: ennreal_cases)
    case top
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. w s) f) < c}
        = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      unfolding top by simp
    then show ?thesis
      using openin_topspace[of
          "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)"]
      by simp
  next
    case (real r)
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. w s) f) < c}
        = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           etime T A (\<lambda>s w. w s) f < r}"
      unfolding real
      using etime_nonneg[OF T, of A "\<lambda>s w. w s"]
      by (auto simp: ennreal_less_iff)
    then show ?thesis by (simp add: etime_usc_on_paths[OF T A])
  qed
  have compl: "topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
             c \<le> ennreal (etime T A (\<lambda>s w. w s) f)}
      = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. w s) f) < c}"
    by (auto simp: not_le)
  show ?thesis
    unfolding closedin_def using op unfolding compl by auto
qed

subsection \<open>The essential infimum of the exit time is usc in the law\<close>

text \<open>
  This is the Portmanteau step. It is stated in the ``superlevel sets are closed''
  form rather than as a \<open>limsup\<close> inequality because that is precisely the shape
  Berge's \<open>box\<close> hypothesis consumes downstream, and because it is what upper
  semicontinuity MEANS: \<open>{P. c \<le> g(P)}\<close> is closed under weak limits for every
  threshold \<open>c\<close>.
\<close>

lemma essinf_etime_usc:
  fixes T :: real and c :: ennreal and A :: "'b::polish_space set"
    and Ni :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and A: "open A"
    and wc: "weak_conv_on Ni N sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and pi: "\<And>i. prob_space (Ni i)" and pN: "prob_space N"
    and ge: "\<And>i. c \<le> ess_inf_time (Ni i) (etime T A (\<lambda>s w. w s))"
  shows "c \<le> ess_inf_time N (etime T A (\<lambda>s w. w s))"
proof -
  define S where "S = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      c \<le> ennreal (etime T A (\<lambda>s w. w s) f)}"
  have clS: "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) S"
    unfolding S_def by (rule etime_superlevel_closed[OF T A])
  have sN: "sets N = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
    and ev: "\<forall>\<^sub>F i in sequentially.
        sets (Ni i) = sets (borel_of
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> finite_measure (Ni i)"
    using wc[unfolded weak_conv_on_def] by blast+

  text \<open>Weak convergence only guarantees the \<open>sets\<close> equation EVENTUALLY, so the
    measurability facts below are stated under that hypothesis and discharged
    per index where needed.\<close>
  have Smeas: "S \<in> sets M" if "sets M = sets (borel_of
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for M
    using borel_of_closed[OF clS] that by simp
  have Sspace: "{\<omega> \<in> space M. c \<le> ennreal (etime T A (\<lambda>s w. w s) \<omega>)} = S"
    if "sets M = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for M
  proof -
    have "space M = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using sets_eq_imp_space_eq[OF that] by (simp add: space_borel_of)
    thus ?thesis unfolding S_def by simp
  qed

  have oneN: "measure (Ni i) S = 1"
    if s: "sets (Ni i) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))" for i
  proof -
    have "measure (Ni i)
        {\<omega> \<in> space (Ni i). c \<le> ennreal (etime T A (\<lambda>s w. w s) \<omega>)} = 1"
      using ess_inf_time_ge_iff_measure[OF pi[of i]]
        Smeas[OF s] Sspace[OF s] ge[of i] by simp
    thus ?thesis unfolding Sspace[OF s] .
  qed

  text \<open>To feed \<open>weak_conv_closed_full_measure\<close>, which asks for full measure at
    EVERY index, replace the eventually-good tail by a shifted sequence. Weak
    convergence is invariant under dropping a finite prefix.\<close>
  obtain n0 where n0: "\<And>i. n0 \<le> i \<Longrightarrow>
      sets (Ni i) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
      \<and> finite_measure (Ni i)"
    using ev unfolding eventually_sequentially by blast
  have wc': "weak_conv_on (\<lambda>i. Ni (i + n0)) N sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    unfolding weak_conv_on_def
  proof (intro conjI allI impI)
    show "\<forall>\<^sub>F i in sequentially. sets (Ni (i + n0)) = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> finite_measure (Ni (i + n0))"
      by (intro always_eventually allI n0) simp
    show "sets N = sets (borel_of
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      by (rule sN)
    show "finite_measure N" by (rule prob_space.finite_measure[OF pN])
    fix f :: "(real \<Rightarrow> 'b) \<Rightarrow> real"
    assume f: "continuous_map
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) euclideanreal f"
      and b: "\<exists>B. \<forall>x \<in> topspace
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)). \<bar>f x\<bar> \<le> B"
    have "((\<lambda>i. \<integral>x. f x \<partial>(Ni i))
        \<longlongrightarrow> (\<integral>x. f x \<partial>N)) sequentially"
      using wc[unfolded weak_conv_on_def] f b by blast
    thus "((\<lambda>i. \<integral>x. f x \<partial>(Ni (i + n0)))
        \<longlongrightarrow> (\<integral>x. f x \<partial>N)) sequentially"
      by (rule LIMSEQ_ignore_initial_segment)
  qed
  have one': "measure (Ni (i + n0)) S = 1" for i
    by (rule oneN) (use n0[of "i + n0"] in simp)
  have "measure N S = 1"
    by (rule weak_conv_closed_full_measure[OF wc' clS one' pN])
  thus ?thesis
    using ess_inf_time_ge_iff_measure[OF pN] Smeas[OF sN] Sspace[OF sN] by simp
qed

end
