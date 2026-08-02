(*
  Title:   Value_Function.thy
  Content: The value function of Eq. (1.6) of arXiv:2512.17702
           (Lai/Shkolnikov/Soner), as an actual supremum over markets.

  Eq. (1.6) reads   v(x) = sup {P-ess inf tau_K : P in P_x}.

  Two design points force the shape of the definition.

  * The paper's P_x is a set of measures on ONE fixed space,
    Omega = C([0,oo), R^n).  A supremum over markets carried by varying
    sample-space types cannot even be written in HOL, so the sample space
    is pinned to the type 'n => real => real -- the type that carries
    bm_paths, so that the constructed Brownian markets are members.

  * The supremum is valued in ennreal.  Then Sup is total: no
    nonemptiness or boundedness side conditions appear in the definition,
    and Sup {} = 0 gives the correct value where no market exists.

  Results:
  * ess_inf_time_le_nn_integral: an almost-sure lower bound on tau is at
    most E[tau] -- the step that lets the expectation bounds of
    Relative_Arbitrage_Stochastic speak about the essential infimum.
  * val_fn_le_ball_v: v(x0) <= (r^2 - |x0|^2)^+/(n-k) for K = cball 0 r,
    i.e. the "<=" half of Eq. (3.9) of Example 3.1, now as a statement
    about the paper's value function rather than about one market.
  * val_fn_boundary: on the sphere v(x0) = 0 = the value of Eq. (3.9),
    i.e. Example 3.1 holds EXACTLY there, both inequalities.
  * mkt_exit_vals_nonempty: the index set is inhabited, so val_fn is not
    an artefact of an empty supremum.

  Not proved (needs the optimal martingale of Eq. (3.11), i.e. Ito
  calculus): the reverse inequality at interior points.
*)

theory Value_Function
  imports Brownian_Optimal_Boundary
begin

section \<open>The essential infimum of a nonnegative random time\<close>

text \<open>\<open>P-ess inf tau\<close> of Eq. (1.6): the largest deterministic almost-sure
  lower bound on \<open>tau\<close>.  In \<open>ennreal\<close> the supremum always exists.\<close>

definition ess_inf_time :: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ennreal" where
  "ess_inf_time M tau = Sup {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"

lemma ess_inf_time_ge_zero: "0 \<le> ess_inf_time M tau"
  by simp

text \<open>Every almost-sure lower bound is dominated by the mean, so the
  essential infimum is too.  This is what turns the expectation bound of
  Relative\_Arbitrage\_Stochastic into a bound on Eq. (1.6).\<close>

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

text \<open>
  Calculus for @{const ess_inf_time}, needed by Proposition 2.4. The
  dynamic programming principle of Eq. (2.9) is an identity between essential
  infima, so these are required however the pasting of controls is eventually
  carried out.

  The workhorse is @{text ess_inf_time_AE}: the essential infimum is ITSELF an
  almost-sure lower bound. That is not immediate, because it is a supremum over an
  uncountable family of almost-sure statements and such a supremum need not be
  almost sure. It works here because @{const ess_inf_time} is a supremum over a
  set of CONSTANTS in @{typ ennreal}, and @{thm [source] ennreal_Sup_countable_SUP}
  extracts a countable cofinal sequence, whose almost-sure statements can then be
  intersected.
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

lemma ess_inf_time_superadd:
  assumes f: "\<And>\<omega>. 0 \<le> f \<omega>" and g: "\<And>\<omega>. 0 \<le> g \<omega>"
  shows "ess_inf_time M f + ess_inf_time M g \<le> ess_inf_time M (\<lambda>\<omega>. f \<omega> + g \<omega>)"
proof (rule ess_inf_timeI)
  have af: "AE \<omega> in M. ess_inf_time M f \<le> ennreal (f \<omega>)" by (rule ess_inf_time_AE)
  have ag: "AE \<omega> in M. ess_inf_time M g \<le> ennreal (g \<omega>)" by (rule ess_inf_time_AE)
  from af ag
  show "AE \<omega> in M. ess_inf_time M f + ess_inf_time M g \<le> ennreal (f \<omega> + g \<omega>)"
  proof eventually_elim
    fix \<omega>
    assume "ess_inf_time M f \<le> ennreal (f \<omega>)" "ess_inf_time M g \<le> ennreal (g \<omega>)"
    then have "ess_inf_time M f + ess_inf_time M g
                 \<le> ennreal (f \<omega>) + ennreal (g \<omega>)" by (rule add_mono)
    also have "\<dots> = ennreal (f \<omega> + g \<omega>)"
      using f[of \<omega>] g[of \<omega>] by (rule ennreal_plus[symmetric])
    finally show "ess_inf_time M f + ess_inf_time M g \<le> ennreal (f \<omega> + g \<omega>)" .
  qed
qed

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

lemma val_fn_ge_zero: "0 \<le> val_fn k L K x0"
  by simp

text \<open>The index set is inhabited: the Brownian market started at \<open>x0\<close> and
  stopped at once never leaves a ball containing \<open>x0\<close>, so it belongs to
  \<open>\<P>\<^sub>x\<^sub>0\<close>.  Hence \<open>val_fn\<close> is not the supremum of an empty set.\<close>

lemma mkt_exit_vals_nonempty:
  fixes x0 :: "real^'n::finite"
  assumes k: "1 \<le> k" "k < CARD('n)" and L: "1 \<le> L" and x0: "norm x0 \<le> r"
  shows "mkt_exit_vals k L (cball 0 r) x0 \<noteq> {}"
proof -
  have "sufficiently_volatile_market
      (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
      (natural_filtration bm_paths 0 (bmX x0)) (bmX x0)
      (\<lambda>_ _. mat 1) k L (cball 0 r) x0 (\<lambda>_. 0)"
    by (rule Brownian_boundary_market[OF k L x0])
  then show ?thesis
    unfolding mkt_exit_vals_def by blast
qed

section \<open>Example 3.1 for the value function: the upper bound of Eq. (3.9)\<close>
text \<open>For every market of \<open>\<P>\<^sub>x\<^sub>0\<close> confined to the ball, the expected exit
  time is at most \<open>v\<close> of Eq. (3.9) (\<open>expected_exit_time_bound\<close>), hence so is
  every almost-sure lower bound on the exit time, hence so is their
  supremum.  This is the \<open>\<le>\<close> half of Example 3.1, for the value function of
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
  vanishes and \<open>val_fn\<close> is nonnegative.  So for boundary starting points
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

text \<open>The first structural property of \<open>val_fn\<close>, and the one the dynamic
  programming work of Section 2 will use repeatedly.  It rests on a single
  observation about the market locale: of the fourteen assumptions of
  \<open>sufficiently_volatile_market\<close> (Relative\_Arbitrage\_Stochastic.thy), the
  domain \<open>K\<close> occurs in exactly ONE, namely

    \<open>X_in_K: AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> X s \<omega> \<in> K\<close>,

  and that assumption is monotone in \<open>K\<close>.  Every other assumption - the
  martingale property, the eigenvalue bounds on \<open>acov\<close>, the integrability
  conditions, Dynkin's identity - is untouched by enlarging the domain.

  Hence enlarging \<open>K\<close> can only ADMIT MORE MARKETS, so the index set of the
  supremum grows and the value function increases.  The argument splits in
  two.  The locale half is
  \<open>sufficiently_volatile_market_mono_K\<close>, where \<open>unfold_locales\<close> discharges the
  whole \<open>martingale\<close> ancestor from the interpretation at the smaller domain and
  leaves exactly the fourteen assumptions --- thirteen reused verbatim, and
  \<open>X_in_K\<close> weakened by one \<open>eventually_elim\<close>.  The set-theoretic half
  (\<open>mkt_exit_vals_mono\<close>) and the conclusion for \<open>val_fn\<close> (\<open>val_fn_mono\<close>) then
  follow with no further hypotheses.\<close>

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
  show ?thesis
    by (unfold_locales; blast intro: sv.k_lb sv.k_ub sv.L_ge sv.X_start
          sv.tau_nonneg sv.tau_meas K' sv.acov_psd sv.acov_eigen_lb
          sv.acov_eigen_ub sv.acov_trace_integrable sv.stopped_sq_integrable
          sv.compensator_integrable sv.dynkin_quadratic)
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

text \<open>FINITENESS.  This is clause (0) of Theorem 1.1 --- for
  \<open>v = enn2real \<circ> val_fn\<close> to be a faithful real-valued function one needs
  \<open>val_fn < \<top>\<close> --- and it is free: a bounded \<open>K\<close> sits inside some \<open>cball 0 a\<close>,
  \<open>val_fn\<close> is monotone in \<open>K\<close>, and on a ball it is bounded by the explicit
  Example 3.1 value \<open>ball_v\<close>.

  VANISHING OFF \<open>K\<close>.  The market locale requires \<open>x0 \<in> K\<close>, so outside \<open>K\<close> the
  index set of the supremum is EMPTY and \<open>val_fn\<close> is \<open>Sup {} = \<bottom> = 0\<close>.\<close>

lemma val_fn_finite_bounded:
  fixes K :: "(real^'n::finite) set" and x0 :: "real^'n"
  assumes B: "bounded K"
  shows "val_fn k L K x0 < \<top>"
proof -
  obtain a where a: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> a"
    using B unfolding bounded_iff by blast
  have sub: "K \<subseteq> cball 0 a"
    using a by (simp add: subset_iff dist_norm)
  have "val_fn k L K x0 \<le> val_fn k L (cball 0 a) x0"
    by (rule val_fn_mono[OF sub])
  also have "\<dots> \<le> ennreal (ball_v a k x0)" by (rule val_fn_le_ball_v)
  also have "\<dots> < \<top>" by simp
  finally show ?thesis .
qed

text \<open>CLAUSE (3) OF THEOREM 1.1, for the ball.  \<open>ball_v r k x\<close> is
  \<open>max (r\<^sup>2 - x \<bullet> x) 0 / (CARD('n) - k)\<close>, which vanishes exactly when
  \<open>x \<bullet> x \<ge> r\<^sup>2\<close> --- in particular on the sphere.  Combined with
  \<open>val_fn_boundary\<close> this gives the zero boundary condition of Eq. (1.10) on
  \<open>cball 0 r - interior (cball 0 r)\<close>.

  For a GENERAL compact \<open>K\<close> this is Lemma 5.3 of the paper, which reuses the
  measure constructed in Example 3.1 and is therefore behind the same weak
  existence result as clauses (1) and (2).\<close>

lemma ball_v_boundary_zero:
  fixes x0 :: "real^'n::finite"
  assumes x0: "norm x0 = r"
  shows "ball_v r k x0 = 0"
proof -
  have "x0 \<bullet> x0 = r\<^sup>2" using x0 by (simp add: power2_norm_eq_inner[symmetric])
  then show ?thesis unfolding ball_v_def by simp
qed

lemma val_fn_boundary_zero:
  fixes x0 :: "real^'n::finite"
  assumes x0: "norm x0 = r"
  shows "val_fn k L (cball 0 r) x0 = 0"
proof -
  have "val_fn k L (cball 0 r) x0 = ennreal (ball_v r k x0)"
    by (rule val_fn_boundary[OF x0])
  also have "\<dots> = ennreal 0" unfolding ball_v_boundary_zero[OF x0] ..
  finally show ?thesis by simp
qed

lemma val_fn_zero_on_frontier_ball:
  fixes r :: real and x0 :: "real^'n::finite"
  assumes x0: "x0 \<in> cball 0 r - interior (cball (0::real^'n) r)"
  shows "val_fn k L (cball 0 r) x0 = 0"
proof -
  have le: "norm x0 \<le> r" using x0 by (simp add: dist_norm)
  have nlt: "\<not> norm x0 < r"
    using x0 unfolding interior_cball by (simp add: dist_norm)
  have "norm x0 = r" using le nlt by linarith
  then show ?thesis by (rule val_fn_boundary_zero)
qed

text \<open>NOT PROVED HERE, and worth recording why.  \<open>val_fn k L K x0 = 0\<close> for
  \<open>x0 \<notin> K\<close> is TRUE and nearly trivial mathematically --- the market locale
  requires \<open>x0 \<in> K\<close> (\<open>sufficiently_volatile_market.x0_in_K\<close>), so the index set
  of the supremum is empty and \<open>Sup {} = \<bottom> = 0\<close>.  The obstruction is purely one
  of TYPE INFERENCE: eliminating the five-fold existential inside
  \<open>mkt_exit_vals\<close> introduces FRESH type variables for the measure, filtration
  and process, which then fail to unify with the ones in the membership fact
  (PIDE reports "Introduced fixed type variable(s): 'a"), and the resulting
  goal \<open>\<exists>\<dots> \<Longrightarrow> \<exists>\<dots>\<close> is refused by both \<open>simp\<close> and \<open>blast\<close> although the two sides
  print identically.  Fixing it needs the eliminated variables' types pinned
  explicitly in the \<open>obtain\<close>.

  Left undone deliberately: it is not on the path to anything, and
  \<open>val_fn_finite_bounded\<close> above --- which IS clause (0) of Theorem 1.1 --- does
  not depend on it.\<close>

end