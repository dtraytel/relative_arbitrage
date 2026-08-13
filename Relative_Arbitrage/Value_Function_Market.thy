

(*<*)
theory Value_Function_Market
  imports Brownian_Optimal_Boundary
begin

(*>*)

text \<open>
  Formalizes the value function of Eq. (1.6) of arXiv:2512.17702,

    \<open>v(x) = Sup {essinf\<^bsub>P\<^esub> tau\<^sub>K | P. P \<in> P\<^sub>x}\<close>,

  as an actual supremum over markets. The sample space is pinned to the
  single type \<open>'n \<Rightarrow> real \<Rightarrow> real\<close> carrying \<open>bm_paths\<close>, since a
  supremum over varying sample-space types cannot be written in HOL, and
  the supremum is valued in \<open>ennreal\<close> so that \<open>Sup\<close> is total and
  \<open>Sup {} = 0\<close> gives the correct value where no market exists. It
  proves \<open>ess_inf_time_le_nn_integral\<close>, bounding an almost-sure lower
  bound on \<open>tau\<close> by \<open>E [tau]\<close>; the inequality \<open>val_fn_le_ball_v\<close>,
  \<open>v(x0) \<le> max (r\<^sup>2 - \<bar>x0\<bar>\<^sup>2) 0 / (n - k)\<close> for \<open>K = cball 0 r\<close>; the
  boundary identity \<open>val_fn_boundary\<close>, where Example 3.1 holds exactly;
  and nonemptiness of the index set via \<open>mkt_exit_vals_nonempty\<close>.\<close>
section \<open>The essential infimum of a nonnegative random time\<close>

text \<open>\<open>P-ess inf tau\<close> of Eq. (1.6): the largest deterministic almost-sure
  lower bound on \<open>tau\<close>. In \<open>ennreal\<close> the supremum always exists.\<close>

definition ess_inf_time :: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ennreal" where
  "ess_inf_time M tau = Sup {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"


text \<open>Every almost-sure lower bound is dominated by the mean, so the
  essential infimum is too. This is what turns the expectation bound of
  @{theory Relative_Arbitrage.Volatile_Market} into a bound on Eq. (1.6).\<close>

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
  capped at \<open>T\<close> by construction (\<open>Exit_Time.etime_le_T\<close>), so the ceiling is
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

lemma ess_inf_time_distr:
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

definition mkt_exit_vals ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal set"
  where
  "mkt_exit_vals k L K x0 =
     {c. \<exists>(M :: ('n \<Rightarrow> real \<Rightarrow> real) measure) F X acov tau.
            sufficiently_volatile_market M F X acov k L K x0 tau
          \<and> c = ess_inf_time M tau}"

definition val_fn ::
  "nat \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real^'n \<Rightarrow> ennreal"
  where
  "val_fn k L K x0 = Sup (mkt_exit_vals k L K x0)"


text \<open>The index set is inhabited: the Brownian market started at \<open>x0\<close> and
  stopped at once never leaves a ball containing \<open>x0\<close>, so it belongs to
  \<open>\<P>\<^sub>x\<^sub>0\<close>. Hence \<open>val_fn\<close> is not the supremum of an empty set.\<close>

lemma mkt_exit_vals_nonempty:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and x0: "norm x0 \<le> r"
  shows "mkt_exit_vals k L (cball 0 r) x0 \<noteq> {}"
proof -
  have "sufficiently_volatile_market
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0)
      (\<lambda>_ _. mat 1) k L (cball 0 r) x0 (\<lambda>_. 0)"
    by (rule Brownian_boundary_market[OF k L x0])
  then show ?thesis
    unfolding mkt_exit_vals_def by blast
qed

section \<open>Example 3.1 for the value function: the upper bound of Eq. (3.9)\<close>
text \<open>For every market of \<open>\<P>\<^sub>x\<^sub>0\<close> confined to the ball, the expected exit
  time is at most \<open>v\<close> of Eq. (3.9) (\<open>expected_exit_time_bound\<close>), hence so is
  every almost-sure lower bound on the exit time, hence so is their
  supremum. This is the \<open>\<le>\<close> half of Example 3.1, for the value function of
  Eq. (1.6) itself.\<close>

theorem val_fn_le_ball_v:
  fixes x0 :: "real^'n::finite"
  shows "val_fn k L (cball 0 r) x0 \<le> ennreal (ball_v r k x0)"
  unfolding val_fn_def
proof (rule Sup_least)
  fix c :: ennreal
  assume "c \<in> mkt_exit_vals k L (cball 0 r) x0"
  then obtain M :: "('n \<Rightarrow> real \<Rightarrow> real) measure" and F X acov tau
    where svm: "sufficiently_volatile_market M F X acov k L (cball 0 r) x0 tau"
      and c: "c = ess_inf_time M tau"
    unfolding mkt_exit_vals_def by blast
  have ps: "prob_space M"
    by (rule sufficiently_volatile_market.prob_space_M[OF svm])
  have "c \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
    unfolding c by (rule ess_inf_time_le_nn_integral[OF ps])
  also have "\<dots> \<le> ennreal (ball_v r k x0)"
    by (rule sufficiently_volatile_market.expected_exit_time_bound[OF svm refl])
  finally show "c \<le> ennreal (ball_v r k x0)" .
qed

text \<open>On the sphere the bound is attained, because there \<open>v\<close> of Eq. (3.9)
  vanishes and \<open>val_fn\<close> is nonnegative. So for boundary starting points
  Example 3.1 is proved exactly --- both inequalities --- for the value
  function of Eq. (1.6), with no assumption beyond \<open>|x0| = r\<close>.\<close>

corollary val_fn_boundary:
  fixes x0 :: "real^'n::finite"
  assumes x0: "norm x0 = r"
  shows "val_fn k L (cball 0 r) x0 = ennreal (ball_v r k x0)"
proof -
  have z: "ball_v r k x0 = 0"
    by (rule ball_v_boundary[OF x0])
  have "val_fn k L (cball 0 r) x0 \<le> 0"
    using val_fn_le_ball_v[of k L r x0] by (simp add: z)
  then show ?thesis
    by (simp add: z)
qed


section \<open>Monotonicity of the value function in the domain\<close>

text \<open>The first structural property of \<open>val_fn\<close>, used repeatedly by
  Section 2's dynamic programming. Of the fourteen assumptions of
  \<open>sufficiently_volatile_market\<close> (@{theory Relative_Arbitrage.Volatile_Market}), the
  domain \<open>K\<close> occurs only in \<open>X_in_K\<close>, which is monotone in \<open>K\<close>; every
  other assumption is untouched by enlarging the domain. So enlarging \<open>K\<close>
  only admits more markets and \<open>val_fn\<close> increases: the locale half is
  \<open>sufficiently_volatile_market_mono_K\<close>, the set-theoretic half
  \<open>mkt_exit_vals_mono\<close>, the conclusion \<open>val_fn_mono\<close>.\<close>

lemma sufficiently_volatile_market_mono_K:
  fixes M :: "'a measure" and X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite"
  assumes sv: "sufficiently_volatile_market M F X acov k L K x0 tau"
    and KK: "K \<subseteq> K'"
  shows "sufficiently_volatile_market M F X acov k L K' x0 tau"
proof -
  interpret sv: sufficiently_volatile_market M F X acov k L K x0 tau
    by (rule sv)
  have K': "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K'"
    using sv.X_in_K by eventually_elim (use KK in blast)
  have mg: "martingale M F 0 X"
    using sv by (simp add: sufficiently_volatile_market_def)
  text \<open>\<open>unfold_locales\<close> cannot be used here: the new assumption
    \<open>coord_Z_martingale\<close> is itself a locale predicate, which \<open>unfold_locales\<close>
    would unfold recursively into the martingale axioms instead of leaving it
    as one goal. The explicit \<open>intro\<close> route keeps the assumptions atomic.\<close>
  show ?thesis
  proof (intro sufficiently_volatile_market.intro[OF mg]
      sufficiently_volatile_market_axioms.intro)
    show "prob_space M" by (rule sv.prob_space_M)
    show "1 \<le> k" by (rule sv.k_lb)
    show "k < CARD('n)" by (rule sv.k_ub)
    show "1 \<le> L" by (rule sv.L_ge)
    show "AE \<omega> in M. X 0 \<omega> = x0" by (rule sv.X_start)
    show "AE \<omega> in M. 0 \<le> tau \<omega>" by (rule sv.tau_nonneg)
    show "tau \<in> borel_measurable M" by (rule sv.tau_meas)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K'" by (rule K')
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> psd (acov s \<omega>)"
      by (rule sv.acov_psd)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow>
        eigen_lb (acov s \<omega>) (CARD('n) - k)"
      by (rule sv.acov_eigen_lb)
    show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> eigen_ub (acov s \<omega>) L"
      by (rule sv.acov_eigen_ub)
    show "AE \<omega> in M. set_borel_measurable lborel {0..} (\<lambda>s. acov s \<omega>)"
      by (rule sv.acov_time_measurable)
    show "AE \<omega> in M. \<forall>t. 0 \<le> t \<longrightarrow>
        set_integrable lborel {0..t} (\<lambda>s. trace (acov s \<omega>))"
      by (rule sv.acov_trace_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        integrable M (\<lambda>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega>)"
      by (rule sv.stopped_sq_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow> integrable M
        (\<lambda>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
               (\<lambda>s. trace (acov s \<omega>)))"
      by (rule sv.compensator_integrable)
    show "\<And>t. 0 \<le> t \<Longrightarrow>
        (\<integral>\<omega>. X (min t (tau \<omega>)) \<omega> \<bullet> X (min t (tau \<omega>)) \<omega> \<partial>M)
          - (\<integral>\<omega>. set_lebesgue_integral lborel {0..min t (tau \<omega>)}
                   (\<lambda>s. trace (acov s \<omega>)) \<partial>M)
        = x0 \<bullet> x0"
      by (rule sv.dynkin_quadratic)
    show "\<And>i. martingale M F 0 (coord_Z X acov i)"
      by (rule sv.coord_Z_martingale)
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
      by (rule sv.tau_stopping)
    show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
      by (rule sv.X_paths_cont)
  qed
qed

lemma mkt_exit_vals_mono:
  fixes x0 :: "real^'n::finite"
  assumes KK: "K \<subseteq> K'"
  shows "mkt_exit_vals k L K x0 \<subseteq> mkt_exit_vals k L K' x0"
proof (rule subsetI)
  fix c :: ennreal
  assume "c \<in> mkt_exit_vals k L K x0"
  then obtain M :: "('n \<Rightarrow> real \<Rightarrow> real) measure" and F X acov tau
    where sv: "sufficiently_volatile_market M F X acov k L K x0 tau"
      and ce: "c = ess_inf_time M tau"
    unfolding mkt_exit_vals_def by blast
  have "sufficiently_volatile_market M F X acov k L K' x0 tau"
    by (rule sufficiently_volatile_market_mono_K[OF sv KK])
  with ce show "c \<in> mkt_exit_vals k L K' x0"
    unfolding mkt_exit_vals_def by blast
qed

theorem val_fn_mono:
  fixes x0 :: "real^'n::finite"
  assumes KK: "K \<subseteq> K'"
  shows "val_fn k L K x0 \<le> val_fn k L K' x0"
  unfolding val_fn_def
  by (rule Sup_subset_mono[OF mkt_exit_vals_mono[OF KK]])


section \<open>Two facts about \<open>val_fn\<close> that need no probability at all\<close>

text \<open>Finiteness is clause (0) of Theorem 1.1: \<open>v = enn2real \<circ> val_fn\<close>
  needs \<open>val_fn < \<top>\<close>, free since a bounded \<open>K\<close> sits inside some
  \<open>cball 0 a\<close>, \<open>val_fn\<close> is monotone in \<open>K\<close>, and on a ball it is bounded by
  the Example 3.1 value \<open>ball_v\<close>.

  \<open>val_fn\<close> vanishes off \<open>K\<close>: the market locale requires \<open>x0 \<in> K\<close>, so
  outside \<open>K\<close> the index set is empty and \<open>val_fn\<close> is \<open>Sup {} = \<bottom> = 0\<close>.\<close>


text \<open>Clause (3) of Theorem 1.1, for the ball: \<open>ball_v r k x\<close> is
  \<open>max (r\<^sup>2 - x \<bullet> x) 0 / (CARD('n) - k)\<close>, vanishing exactly when
  \<open>x \<bullet> x \<ge> r\<^sup>2\<close>, in particular on the sphere. With \<open>val_fn_boundary\<close> this
  gives the zero boundary condition of Eq. (1.10) on
  \<open>cball 0 r - interior (cball 0 r)\<close>.

  For a general compact \<open>K\<close> this is Lemma 5.3 of the paper, reusing the
  measure of Example 3.1 and behind the same weak existence result as
  clauses (1) and (2).\<close>




text \<open>\<open>val_fn k L K x0 = 0\<close> for \<open>x0 \<notin> K\<close>, since the market locale requires
  \<open>x0 \<in> K\<close> (\<open>sufficiently_volatile_market.x0_in_K\<close>), so the index set of the
  supremum is empty and \<open>Sup {} = \<bottom> = 0\<close>.\<close>


(*<*)
end
(*>*)
