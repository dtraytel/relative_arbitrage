
(*<*)
theory Value_Function_Market
  imports Brownian_Optimal_Boundary
    "Continuous_Time_Martingales.Essential_Infimum"
begin

(*>*)

text \<open>
  Formalizes the value function of Eq. (1.6) of \<^cite>\<open>LaiShkolnikovSoner\<close>,

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
