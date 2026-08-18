section \<open>The essential infimum of a nonnegative function\<close>

(*<*)
theory Essential_Infimum
  imports "HOL-Probability.Probability"
begin

(*>*)

text \<open>
  \<open>ess_inf M f = Sup {c. AE w in M. c \<le> f w}\<close>, the largest almost-sure
  lower bound of \<open>f\<close>, taken in \<open>ennreal\<close> so that the supremum is
  unconditionally defined and no integrability or boundedness hypothesis is
  needed anywhere.  \<open>ess_inf_time\<close> is the same construction for a
  \<open>real\<close>-valued payoff, which is how an exit time is presented; the two were
  defined separately, in two theories, and the second is now visibly an
  instance of the first (\<open>ess_inf_time_eq\<close>).

  Everything here is measure theory: the value is attained as an
  almost-sure bound, it is monotone, it transports along an image measure,
  and it is below every mean.
\<close>

definition ess_inf :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ennreal" where
  "ess_inf M tau = Sup {c. AE \<omega> in M. c \<le> tau \<omega>}"

lemma ess_infI:
  assumes "AE \<omega> in M. c \<le> tau \<omega>"
  shows "c \<le> ess_inf M tau"
  unfolding ess_inf_def using assms by (intro Sup_upper) simp

lemma ess_inf_mono:
  assumes "AE \<omega> in M. tau \<omega> \<le> tau' \<omega>"
  shows "ess_inf M tau \<le> ess_inf M tau'"
  unfolding ess_inf_def
proof (rule Sup_least)
  fix c assume "c \<in> {c. AE \<omega> in M. c \<le> tau \<omega>}"
  then have "AE \<omega> in M. c \<le> tau \<omega>" by simp
  with assms have "AE \<omega> in M. c \<le> tau' \<omega>" by eventually_elim simp
  then show "c \<le> \<Squnion> {c. AE \<omega> in M. c \<le> tau' \<omega>}"
    by (intro Sup_upper) simp
qed

lemma ess_inf_AE: "AE \<omega> in M. ess_inf M tau \<le> tau \<omega>"
proof -
  define S where "S = {c. AE \<omega> in M. c \<le> tau \<omega>}"
  have "0 \<in> S" unfolding S_def by simp
  then have ne: "S \<noteq> {}" by blast
  obtain f :: "nat \<Rightarrow> ennreal"
    where f: "range f \<subseteq> S" and sup: "Sup S = Sup (range f)"
    using ennreal_Sup_countable_SUP[OF ne] by blast
  have fS: "AE \<omega> in M. f n \<le> tau \<omega>" for n
    using f unfolding S_def by blast
  have "AE \<omega> in M. \<forall>n. f n \<le> tau \<omega>"
    using fS by (subst AE_all_countable) blast
  then have "AE \<omega> in M. Sup (range f) \<le> tau \<omega>"
    by eventually_elim (auto intro: Sup_least)
  thus ?thesis unfolding ess_inf_def S_def[symmetric] using sup by simp
qed

lemma ess_inf_min_const:
  "min (ess_inf M tau) c \<le> ess_inf M (\<lambda>\<omega>. min (tau \<omega>) c)"
proof (rule ess_infI)
  have "AE \<omega> in M. ess_inf M tau \<le> tau \<omega>" by (rule ess_inf_AE)
  then show "AE \<omega> in M. min (ess_inf M tau) c \<le> min (tau \<omega>) c"
  proof eventually_elim
    case (elim \<omega>)
    then show ?case by (rule min.mono[OF _ order_refl])
  qed
qed

subsection \<open>A real-valued payoff\<close>

text \<open>\<open>P-ess inf tau\<close> of Eq. (1.6): the largest deterministic almost-sure
  lower bound on \<open>tau\<close>. In \<open>ennreal\<close> the supremum always exists.\<close>

definition ess_inf_time :: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ennreal" where
  "ess_inf_time M tau = Sup {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"

text \<open>Every almost-sure lower bound is dominated by the mean, so the
  essential infimum is below every integral.\<close>

lemma ess_inf_ennreal:
  "ess_inf M (\<lambda>\<omega>. ennreal (tau \<omega>)) = ess_inf_time M tau"
  unfolding ess_inf_def ess_inf_time_def by simp

lemma ess_inf_timeI:
  assumes "AE \<omega> in M. c \<le> ennreal (tau \<omega>)"
  shows "c \<le> ess_inf_time M tau"
  unfolding ess_inf_time_def using assms by (intro Sup_upper) simp

lemma ess_inf_time_AE: "AE \<omega> in M. ess_inf_time M tau \<le> ennreal (tau \<omega>)"
proof -
  define S where "S = {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"
  have "0 \<in> S" unfolding S_def by simp
  then have ne: "S \<noteq> {}" by blast
  obtain f :: "nat \<Rightarrow> ennreal" where f: "range f \<subseteq> S" and sup: "Sup S = Sup (range f)"
    using ennreal_Sup_countable_SUP[OF ne] by blast
  have fS: "AE \<omega> in M. f n \<le> ennreal (tau \<omega>)" for n
    using f unfolding S_def by blast
  have "AE \<omega> in M. \<forall>n. f n \<le> ennreal (tau \<omega>)"
    using fS by (subst AE_all_countable) blast
  then have "AE \<omega> in M. Sup (range f) \<le> ennreal (tau \<omega>)"
    by eventually_elim (auto intro: Sup_least)
  thus ?thesis unfolding ess_inf_time_def S_def[symmetric] using sup by simp
qed

text \<open>The characterisation the upper-semicontinuity argument runs on: the
  essential infimum is at least \<open>c\<close> exactly when \<open>c\<close> is an almost-sure lower
  bound (\<open>ess_inf_timeI\<close> / \<open>ess_inf_time_AE\<close>). The iff lets the weak
  convergence argument work with \<open>{\<tau> \<ge> c}\<close> rather than the essential
  infimum itself.

  This gives a shorter route to Larsson--Ruf's Lemma 2.1 than theirs, who
  prove \<open>P \<mapsto> P-essinf \<tau>\<^sub>K\<close> usc via \<open>inf\<^bsub>\<lambda>>0\<^esub> f\<^sub>\<lambda>\<close> with
  \<open>f\<^sub>\<lambda>(P) = -(1/\<lambda>) log E\<^sub>P[e\<^sup>-\<^sup>\<lambda>\<^sup>\<tau>]\<close> and Portmanteau on each \<open>f\<^sub>\<lambda>\<close>.
  Since upper semicontinuity is closedness of
  \<open>{P : c \<le> P-essinf \<tau>} = {P : P{\<tau> \<ge> c} = 1}\<close>, and \<open>\<tau>\<^sub>K\<close> being usc makes
  \<open>{\<tau>\<^sub>K \<ge> c}\<close> closed, the closed-set form of Portmanteau closes it in one
  step, with no Laplace transform needed.\<close>

lemma ess_inf_time_le_nn_integral:
  assumes M: "prob_space M"
  shows "ess_inf_time M tau \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
  unfolding ess_inf_time_def
proof (rule Sup_least)
  fix c :: ennreal
  assume "c \<in> {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"
  then have ae: "AE \<omega> in M. c \<le> ennreal (tau \<omega>)"
    by simp
  have "c = (\<integral>\<^sup>+\<omega>. c \<partial>M)"
    by (simp add: prob_space.emeasure_space_1[OF M])
  also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
    by (rule nn_integral_mono_AE[OF ae])
  finally show "c \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)" .
qed

text \<open>A deterministic ceiling passes to the essential infimum: the family of
  values \<open>{P\<hyphen>essinf \<tau>\<^sub>K : P \<in> \<P>\<^sub>0}\<close> needs to be bounded above by a real number
  for Berge's theorem, and \<open>ess_inf_time\<close> is \<open>ennreal\<close>-valued. The exit time is
  capped at \<open>T\<close> by construction (\<open>Stopping_Times.etime_le_T\<close>), so the ceiling is
  available for free.\<close>

lemma ess_inf_time_le_const:
  assumes M: "prob_space M" and bnd: "\<And>\<omega>. tau \<omega> \<le> T"
  shows "ess_inf_time M tau \<le> ennreal T"
proof -
  interpret PM: prob_space M by (rule M)
  have "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) \<le> (\<integral>\<^sup>+\<omega>. ennreal T \<partial>M)"
    by (intro nn_integral_mono ennreal_leI bnd)
  also have "(\<integral>\<^sup>+\<omega>. ennreal T \<partial>M) = ennreal T"
    by (simp add: PM.emeasure_space_1)
  finally have "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) \<le> ennreal T" .
  with ess_inf_time_le_nn_integral[OF M] show ?thesis by (rule order_trans)
qed

text \<open>
  Calculus for @{const ess_inf_time}, needed by Proposition 2.4: the
  dynamic programming principle of Eq. (2.9) is an identity between essential
  infima, however the pasting of controls is carried out.

  The workhorse is @{text ess_inf_time_AE}: the essential infimum is itself
  an almost-sure lower bound --- not immediate, since it is a supremum over
  an uncountable family of almost-sure statements. It works because
  @{const ess_inf_time} is a supremum over constants in @{typ ennreal}, and
  @{thm [source] ennreal_Sup_countable_SUP} extracts a countable cofinal
  sequence whose almost-sure statements can be intersected.
\<close>

lemma ess_inf_time_ge_iff:
  "c \<le> ess_inf_time M tau \<longleftrightarrow> (AE \<omega> in M. c \<le> ennreal (tau \<omega>))"
proof
  assume c: "c \<le> ess_inf_time M tau"
  have ae: "AE \<omega> in M. ess_inf_time M tau \<le> ennreal (tau \<omega>)"
    by (rule ess_inf_time_AE)
  show "AE \<omega> in M. c \<le> ennreal (tau \<omega>)"
  proof (rule eventually_mono[OF ae])
    fix \<omega> assume h: "ess_inf_time M tau \<le> ennreal (tau \<omega>)"
    show "c \<le> ennreal (tau \<omega>)" by (rule order_trans[OF c h])
  qed
next
  assume "AE \<omega> in M. c \<le> ennreal (tau \<omega>)"
  then show "c \<le> ess_inf_time M tau" by (rule ess_inf_timeI)
qed

text \<open>In the AFP's vocabulary: \<open>mweak_conv2\<close>
  (\<open>Levy_Prokhorov_Metric.General_Weak_Convergence\<close>) states closed-set
  Portmanteau with \<open>measure\<close>, not \<open>emeasure\<close> or \<open>AE\<close>, so the superlevel
  set has to be presented as a set of full measure: \<open>{\<tau>\<^sub>K \<ge> c}\<close> is closed
  since \<open>\<tau>\<^sub>K\<close> is usc, every \<open>N\<^sub>i\<close> gives it measure 1, and \<open>mweak_conv2\<close>
  yields \<open>1 = limsup N\<^sub>i(A) \<le> N(A) \<le> 1\<close>.\<close>

lemma ess_inf_time_ge_iff_measure:
  assumes P: "prob_space M"
    and m: "{\<omega> \<in> space M. c \<le> ennreal (tau \<omega>)} \<in> sets M"
  shows "c \<le> ess_inf_time M tau
      \<longleftrightarrow> measure M {\<omega> \<in> space M. c \<le> ennreal (tau \<omega>)} = 1"
proof -
  interpret prob_space M by (rule P)
  have "c \<le> ess_inf_time M tau \<longleftrightarrow> (AE \<omega> in M. c \<le> ennreal (tau \<omega>))"
    by (rule ess_inf_time_ge_iff)
  also have "\<dots> \<longleftrightarrow> (AE \<omega> in M. \<omega> \<in> {\<omega> \<in> space M. c \<le> ennreal (tau \<omega>)})"
    by (rule AE_cong) simp
  also have "\<dots> \<longleftrightarrow> measure M {\<omega> \<in> space M. c \<le> ennreal (tau \<omega>)} = 1"
    by (rule AE_in_set_eq_1[OF m])
  finally show ?thesis .
qed

text \<open>Portmanteau is a statement about measures of sets, so the essential
  infimum has to be traded for one: being strictly below \<open>d\<close> is exactly the
  event \<open>{\<tau> < d}\<close> carrying positive mass. This is \<open>ess_inf_time_ge_iff\<close>
  negated, with the almost-sure statement turned into an \<open>emeasure\<close> ---
  which is where measurability of the event is needed, and is the only
  hypothesis.\<close>

lemma ess_inf_time_less_iff:
  assumes m: "{\<omega> \<in> space M. ennreal (tau \<omega>) < d} \<in> sets M"
  shows "ess_inf_time M tau < d
      \<longleftrightarrow> emeasure M {\<omega> \<in> space M. ennreal (tau \<omega>) < d} \<noteq> 0"
proof -
  have eq: "{\<omega> \<in> space M. \<not> (d \<le> ennreal (tau \<omega>))}
      = {\<omega> \<in> space M. ennreal (tau \<omega>) < d}" by auto
  have ae: "(AE \<omega> in M. d \<le> ennreal (tau \<omega>))
      \<longleftrightarrow> emeasure M {\<omega> \<in> space M. ennreal (tau \<omega>) < d} = 0"
    by (rule AE_iff_measurable[OF m eq])
  have "ess_inf_time M tau < d \<longleftrightarrow> \<not> (d \<le> ess_inf_time M tau)" by auto
  also have "\<dots> \<longleftrightarrow> \<not> (AE \<omega> in M. d \<le> ennreal (tau \<omega>))"
    unfolding ess_inf_time_ge_iff ..
  also have "\<dots> \<longleftrightarrow> emeasure M {\<omega> \<in> space M. ennreal (tau \<omega>) < d} \<noteq> 0"
    using ae by simp
  finally show ?thesis .
qed

lemma ess_inf_time_mono:
  assumes "AE \<omega> in M. tau \<omega> \<le> sig \<omega>"
  shows "ess_inf_time M tau \<le> ess_inf_time M sig"
proof (rule ess_inf_timeI)
  have "AE \<omega> in M. ess_inf_time M tau \<le> ennreal (tau \<omega>)"
    by (rule ess_inf_time_AE)
  thus "AE \<omega> in M. ess_inf_time M tau \<le> ennreal (sig \<omega>)"
    using assms by eventually_elim (simp add: ennreal_leI order_trans)
qed

text \<open>
  Superadditivity. This is the shape in which Eq. (2.9) splits the exit time into
  the part before the stopping time and the continuation value.
\<close>

text \<open>The essential infimum transported along a pushforward: exit times of
  a law presented as a distr (e.g.\ a path law, or a member of \<open>\<P>\<^sub>x\<close>
  reconstructed from a limit) can be computed on either side. Needed when
  Lemma 2.3 exhibits weak limits as members of \<open>\<P>\<^sub>x\<close> and Proposition 2.4
  concatenates laws at stopping times.\<close>

lemma ess_inf_time_distr_measurable:
  assumes g: "g \<in> M \<rightarrow>\<^sub>M N" and tau: "tau \<in> borel_measurable N"
  shows "ess_inf_time (distr M N g) tau = ess_inf_time M (\<lambda>\<omega>. tau (g \<omega>))"
proof -
  have m: "{x \<in> space N. c \<le> ennreal (tau x)} \<in> sets N" for c
    using tau by measurable
  have iff: "(AE x in distr M N g. c \<le> ennreal (tau x))
      \<longleftrightarrow> (AE \<omega> in M. c \<le> ennreal (tau (g \<omega>)))" for c
    by (rule AE_distr_iff[OF g m])
  show ?thesis
    unfolding ess_inf_time_def iff by (rule refl)
qed

section \<open>The class \<open>\<P>\<^sub>x\<close> and the value function of Eq. (1.6)\<close>

text \<open>The set of values \<open>P-ess inf tau\<close> attained by the markets of
  \<open>\<P>\<^sub>x\<close> --- the class of Eq. (1.7), in the martingale-problem form of
  \<open>sufficiently_volatile_market\<close> --- started at \<open>x0\<close> and confined to \<open>K\<close>.\<close>

lemma ess_inf_time_distr:
  assumes fm: "f \<in> M \<rightarrow>\<^sub>M N"
    and meas: "\<And>c :: ennreal. {\<omega> \<in> space N. c \<le> ennreal (tau \<omega>)} \<in> sets N"
  shows "ess_inf_time (distr M N f) tau = ess_inf_time M (\<lambda>\<omega>. tau (f \<omega>))"
  unfolding ess_inf_time_def
proof (rule arg_cong[where f = Sup])
  show "{c. AE \<omega> in distr M N f. c \<le> ennreal (tau \<omega>)}
      = {c. AE \<omega> in M. c \<le> ennreal (tau (f \<omega>))}"
    using AE_distr_iff[OF fm meas] by blast
qed

text \<open>The exit time does not notice the restriction to \<open>{0..T}\<close> that \<open>path_law\<close>
  performs, because it only ever inspects times in \<open>[0,T]\<close>.\<close>

lemma ess_inf_distr:
  assumes f: "f \<in> M \<rightarrow>\<^sub>M N"
    and meas: "\<And>c :: ennreal. {y \<in> space N. c \<le> g y} \<in> sets N"
  shows "ess_inf (distr M N f) g = ess_inf M (\<lambda>\<omega>. g (f \<omega>))"
proof -
  have "{c. AE y in distr M N f. c \<le> g y} = {c. AE \<omega> in M. c \<le> g (f \<omega>)}"
    using AE_distr_iff[OF f meas] by simp
  then show ?thesis unfolding ess_inf_def by simp
qed

text \<open>The two pushforward maps, as measurable maps in their own right.\<close>

(*<*)
end
(*>*)
