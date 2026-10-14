section \<open>Optional sampling at bounded stopping times\<close>

(*<*)
theory Stopping_Time_Sampling
  imports Dyadic_Grids Optional_Sampling "Martingales.Martingale"
begin

(*>*)

text \<open>The \<open>\<sigma>\<close>-algebra \<open>pre_sigma_of M F \<sigma>\<close> of events before a stopping
  time \<open>\<sigma>\<close>, and the optional sampling theorem for a real martingale whose
  paths are dominated and converge along dyadic ceilings: for bounded
  stopping times \<open>\<sigma> \<le> \<rho>\<close> and an event \<open>A\<close> before \<open>\<sigma>\<close>,
  \<open>\<integral>\<^sub>A Y \<sigma> = \<integral>\<^sub>A Y \<rho>\<close>.  The simple case splits
  \<open>A\<close> along the finitely many values of \<open>\<sigma>\<close>; the general case approximates
  \<open>\<sigma>\<close> from above by dyadic ceilings and passes to the limit by dominated
  convergence.\<close>

subsection \<open>The \<open>\<sigma>\<close>-algebra before a stopping time\<close>

text \<open>The \<open>\<sigma>\<close>-algebra of events before a stopping time, as a set of sets.
  For a nonnegative stopping time of a filtration whose events are events of
  \<open>M\<close>, it is the set of events of HOL-Probability's \<open>filtration.pre_sigma\<close>
  (a sigma-generated measure, quantifying over all times); the counterparts of
  \<open>sigma_algebra_pre_sigma_of\<close> and \<open>pre_sigma_of_mono\<close> there are
  \<open>sigma_algebra_pre_sigma\<close> and \<open>mono_pre_sigma\<close>.  The set form is kept
  because every use here quantifies over \<open>t \<ge> 0\<close> only.\<close>

definition pre_sigma_of :: "'a measure \<Rightarrow> (real \<Rightarrow> 'a measure) \<Rightarrow> ('a \<Rightarrow> real)
    \<Rightarrow> 'a set set"
  where "pre_sigma_of M F \<sigma> =
     {A. A \<in> sets M
       \<and> (\<forall>t. 0 \<le> t \<longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t))}"

lemma pre_sigma_ofI:
  "A \<in> sets M \<Longrightarrow> (\<And>t. 0 \<le> t \<Longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t))
    \<Longrightarrow> A \<in> pre_sigma_of M F \<sigma>"
  unfolding pre_sigma_of_def by blast

lemma space_in_pre_sigma_of:
  assumes stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<tau> \<omega> \<le> t} \<in> sets (F t)"
  shows "space M \<in> pre_sigma_of M F \<tau>"
proof (rule pre_sigma_ofI)
  show "space M \<in> sets M" by simp
  fix t :: real assume t: "0 \<le> t"
  have "space M \<inter> {\<omega> \<in> space M. \<tau> \<omega> \<le> t} = {\<omega> \<in> space M. \<tau> \<omega> \<le> t}" by blast
  then show "space M \<inter> {\<omega> \<in> space M. \<tau> \<omega> \<le> t} \<in> sets (F t)"
    using stop[OF t] by simp
qed

lemma pre_sigma_ofI_le:
  assumes T0: "0 \<le> T"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and bd: "\<And>\<omega>. \<sigma> \<omega> \<le> T"
    and S: "S \<in> sets M"
    and key: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> T
      \<Longrightarrow> S \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  shows "S \<in> pre_sigma_of M F \<sigma>"
proof (rule pre_sigma_ofI[OF S])
  fix t :: real assume t: "0 \<le> t"
  show "S \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  proof (cases "t \<le> T")
    case True
    show ?thesis by (rule key[OF t True])
  next
    case False
    have lt: "\<sigma> \<omega> \<le> t" for \<omega> using bd[of \<omega>] False by simp
    have "{\<omega> \<in> space M. \<sigma> \<omega> \<le> t} = {\<omega> \<in> space M. \<sigma> \<omega> \<le> T}"
      using lt bd by blast
    then have "S \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F T)"
      using key[OF T0 order_refl] by simp
    moreover have "sets (F T) \<subseteq> sets (F t)" using mono[OF T0] False by simp
    ultimately show ?thesis by blast
  qed
qed

lemma pre_sigma_of_sets: "A \<in> pre_sigma_of M F \<sigma> \<Longrightarrow> A \<in> sets M"
  unfolding pre_sigma_of_def by blast

lemma pre_sigma_of_cut:
  "A \<in> pre_sigma_of M F \<sigma> \<Longrightarrow> 0 \<le> t
    \<Longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  unfolding pre_sigma_of_def by blast

text \<open>It is a \<open>\<sigma>\<close>-algebra: the complement step is where the stopping-time
  property of \<open>\<sigma>\<close> is spent, since \<open>{\<sigma> \<le> t}\<close> itself has to be in \<open>F t\<close> for
  the relative complement to stay there.\<close>

lemma sigma_algebra_pre_sigma_of:
  assumes filt: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  shows "sigma_algebra (space M) (pre_sigma_of M F \<sigma>)"
proof (rule sigma_algebra_iff2[THEN iffD2], intro conjI ballI allI impI)
  show "pre_sigma_of M F \<sigma> \<subseteq> Pow (space M)"
    using pre_sigma_of_sets sets.sets_into_space by blast
  show "{} \<in> pre_sigma_of M F \<sigma>"
    by (rule pre_sigma_ofI) (simp_all add: stop)
next
  fix A assume A: "A \<in> pre_sigma_of M F \<sigma>"
  show "space M - A \<in> pre_sigma_of M F \<sigma>"
  proof (rule pre_sigma_ofI)
    show "space M - A \<in> sets M" using pre_sigma_of_sets[OF A] by simp
    fix t :: real assume t: "0 \<le> t"
    have spF: "space (F t) = space M"
      using filt[OF t] by (simp add: subalgebra_def)
    have "(space M - A) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}
        = {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} - (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t})" by blast
    moreover have "\<dots> \<in> sets (F t)"
      using stop[OF t] pre_sigma_of_cut[OF A t] by (rule sets.Diff)
    ultimately show "(space M - A) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
      by simp
  qed
next
  fix AA :: "nat \<Rightarrow> 'a set"
  assume AA: "range AA \<subseteq> pre_sigma_of M F \<sigma>"
  show "(\<Union>i. AA i) \<in> pre_sigma_of M F \<sigma>"
  proof (rule pre_sigma_ofI)
    show "(\<Union>i. AA i) \<in> sets M"
      using AA pre_sigma_of_sets by (intro sets.countable_UN) blast
    fix t :: real assume t: "0 \<le> t"
    have "(\<Union>i. AA i) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}
        = (\<Union>i. AA i \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t})" by blast
    moreover have "\<dots> \<in> sets (F t)"
      using AA t by (intro sets.countable_UN) (auto intro: pre_sigma_of_cut)
    ultimately show "(\<Union>i. AA i) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
      by simp
  qed
qed

text \<open>Monotone in the stopping time, and it sits below \<open>M\<close>.  Monotonicity is
  the step the two-stopping-time sampling theorem consumes: the conditioning
  set for the earlier time is legal for the later one.\<close>

lemma pre_sigma_of_mono:
  assumes le: "\<And>\<omega>. \<sigma> \<omega> \<le> \<rho> \<omega>"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<rho> \<omega> \<le> t} \<in> sets (F t)"
  shows "pre_sigma_of M F \<sigma> \<subseteq> pre_sigma_of M F \<rho>"
proof
  fix A assume A: "A \<in> pre_sigma_of M F \<sigma>"
  show "A \<in> pre_sigma_of M F \<rho>"
  proof (rule pre_sigma_ofI)
    show "A \<in> sets M" by (rule pre_sigma_of_sets[OF A])
    fix t :: real assume t: "0 \<le> t"
    have "A \<inter> {\<omega> \<in> space M. \<rho> \<omega> \<le> t}
        = (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) \<inter> {\<omega> \<in> space M. \<rho> \<omega> \<le> t}"
      by (auto intro: order_trans[OF le])
    moreover have "\<dots> \<in> sets (F t)"
      using pre_sigma_of_cut[OF A t] stop[OF t] by (rule sets.Int)
    ultimately show "A \<inter> {\<omega> \<in> space M. \<rho> \<omega> \<le> t} \<in> sets (F t)" by simp
  qed
qed

text \<open>The slice lemma: an \<open>\<F>\<^sub>\<sigma>\<close>-set, cut down to a half-open band of values of
  \<open>\<sigma>\<close>, lands in the filtration at the top of the band.  This is the brick
  the two-stopping-time sampling theorem runs on: for a simple \<open>\<sigma>\<close> with
  values \<open>t\<^sub>1 < \<dots> < t\<^sub>m\<close> the sets \<open>A \<inter> {\<sigma> = t\<^sub>j}\<close> are exactly such bands, so
  the conditioning set decomposes into finitely many pieces that the
  ordinary deterministic-time sampling can already handle.\<close>

lemma pre_sigma_of_band:
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and s: "0 \<le> s" and st: "s \<le> t"
  shows "A \<inter> {\<omega> \<in> space M. s < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> t} \<in> sets (F t)"
proof -
  have t: "0 \<le> t" using s st by simp
  have "A \<inter> {\<omega> \<in> space M. s < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> t}
      = (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) - (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> s})"
    by auto
  moreover have "(A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) \<in> sets (F t)"
    by (rule pre_sigma_of_cut[OF A t])
  moreover have "(A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> s}) \<in> sets (F t)"
    using pre_sigma_of_cut[OF A s] mono[OF s st] by blast
  ultimately show ?thesis by (simp add: sets.Diff)
qed

text \<open>The bottom band, \<open>\<sigma> \<le> t\<^sub>1\<close>, is @{thm [source] pre_sigma_of_cut}
  itself, so a simple \<open>\<sigma>\<close> gives a finite partition of \<open>A\<close> into pieces each
  living in the filtration at its own value.  The value-set form of the slice
  is what the sampling theorem wants: the pieces indexed by the values of \<open>\<sigma>\<close> are genuinely disjoint,
  whereas pieces indexed by positions in a list need not be.\<close>

lemma pre_sigma_of_value_slice:
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and V: "finite V" and Vnn: "\<And>u. u \<in> V \<Longrightarrow> 0 \<le> u"
    and vals: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<sigma> \<omega> \<in> V"
    and v: "v \<in> V"
  shows "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = v} \<in> sets (F v)"
proof (cases "{u \<in> V. u < v} = {}")
  case False
  define b where "b = Max {u \<in> V. u < v}"
  have fin: "finite {u \<in> V. u < v}" using V by simp
  have bmem: "b \<in> {u \<in> V. u < v}" unfolding b_def by (rule Max_in[OF fin False])
  then have b0: "0 \<le> b" and bv: "b < v" using Vnn by auto
  have "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = v}
      = A \<inter> {\<omega> \<in> space M. b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v}"
  proof -
    have "(\<sigma> \<omega> = v) = (b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v)" if w: "\<omega> \<in> space M" for \<omega>
    proof
      assume "\<sigma> \<omega> = v" then show "b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v" using bv by simp
    next
      assume h: "b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v"
      show "\<sigma> \<omega> = v"
      proof (rule ccontr)
        assume "\<sigma> \<omega> \<noteq> v"
        then have "\<sigma> \<omega> \<in> {u \<in> V. u < v}" using vals[OF w] h by auto
        then have "\<sigma> \<omega> \<le> b" unfolding b_def by (rule Max_ge[OF fin])
        then show False using h by simp
      qed
    qed
    then show ?thesis by auto
  qed
  moreover have "A \<inter> {\<omega> \<in> space M. b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v} \<in> sets (F v)"
    by (rule pre_sigma_of_band[OF mono A b0 less_imp_le[OF bv]])
  ultimately show ?thesis by simp
next
  case True
  have "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = v} = A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> v}"
  proof -
    have "(\<sigma> \<omega> = v) = (\<sigma> \<omega> \<le> v)" if w: "\<omega> \<in> space M" for \<omega>
      using vals[OF w] True by force
    then show ?thesis by auto
  qed
  moreover have "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> v} \<in> sets (F v)"
    by (rule pre_sigma_of_cut[OF A Vnn[OF v]])
  ultimately show ?thesis by simp
qed


text \<open>With the \<open>\<F>\<^sub>\<sigma>\<close> layer in place the simple case is the classical
  argument: split the conditioning set along the finitely many values of
  \<open>\<sigma>\<close>, note each piece lies in the filtration at its own value by
  @{thm [source] pre_sigma_of_value_slice}, and apply the ordinary
  deterministic-time martingale identity on each piece.  No optional
  sampling machinery is needed at all.\<close>

theorem set_martingale_sampling_simple:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<sigma> :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Y"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and V: "finite V" and Vnn: "\<And>u. u \<in> V \<Longrightarrow> 0 \<le> u"
    and VU: "\<And>u. u \<in> V \<Longrightarrow> u \<le> U"
    and vals: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<sigma> \<omega> \<in> V"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
       = set_lebesgue_integral M A (Y U)"
proof -
  interpret Mg: martingale M F 0 Y by (rule mg)
  define Av where "Av u = A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = u}" for u :: real
  have AM: "A \<in> sets M" by (rule pre_sigma_of_sets[OF A])
  have Asp: "A \<subseteq> space M" using AM by (rule sets.sets_into_space)
  have AvF: "Av u \<in> sets (F u)" if u: "u \<in> V" for u
    unfolding Av_def by (rule pre_sigma_of_value_slice[OF mono A V Vnn vals u])
  have AvM: "Av u \<in> sets M" if u: "u \<in> V" for u
  proof -
    have "sets (F u) \<subseteq> sets M"
      using Mg.subalgebras[OF Vnn[OF u]] by (simp add: subalgebra_def)
    then show ?thesis using AvF[OF u] by blast
  qed  have disj: "disjoint_family_on Av V"
    unfolding disjoint_family_on_def Av_def by auto
  have un: "(\<Union>u\<in>V. Av u) = A"
  proof
    show "(\<Union>u\<in>V. Av u) \<subseteq> A" unfolding Av_def by blast
    show "A \<subseteq> (\<Union>u\<in>V. Av u)"
    proof
      fix \<omega> assume w: "\<omega> \<in> A"
      then have sp: "\<omega> \<in> space M" using Asp by blast
      then have "\<sigma> \<omega> \<in> V" by (rule vals)
      moreover have "\<omega> \<in> Av (\<sigma> \<omega>)" unfolding Av_def using w sp by simp
      ultimately show "\<omega> \<in> (\<Union>u\<in>V. Av u)" by blast
    qed
  qed

  \<comment> \<open>on each piece the two integrands agree with a DETERMINISTIC-time one\<close>
  have congL: "set_lebesgue_integral M (Av u) (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
      = set_lebesgue_integral M (Av u) (Y u)" if u: "u \<in> V" for u
    unfolding set_lebesgue_integral_def
    by (rule Bochner_Integration.integral_cong)
       (auto simp: Av_def indicator_def)
  have intU: "set_integrable M (Av u) (Y U)" if u: "u \<in> V" for u
  proof -
    have U0: "0 \<le> U" using Vnn[OF u] VU[OF u] by simp
    show ?thesis
      unfolding set_integrable_def
      by (rule integrable_mult_indicator[OF AvM[OF u] Mg.integrable[OF U0]])
  qed
  have intu: "set_integrable M (Av u) (Y u)" if u: "u \<in> V" for u
    unfolding set_integrable_def
    by (rule integrable_mult_indicator[OF AvM[OF u] Mg.integrable[OF Vnn[OF u]]])  have intL: "set_integrable M (Av u) (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)" if u: "u \<in> V" for u
  proof -
    have "(\<lambda>\<omega>. indicat_real (Av u) \<omega> *\<^sub>R Y (\<sigma> \<omega>) \<omega>)
        = (\<lambda>\<omega>. indicat_real (Av u) \<omega> *\<^sub>R Y u \<omega>)"
      by (rule ext) (auto simp: Av_def indicator_def)
    then show ?thesis using intu[OF u] unfolding set_integrable_def by simp
  qed
  have step: "set_lebesgue_integral M (Av u) (Y u)
      = set_lebesgue_integral M (Av u) (Y U)" if u: "u \<in> V" for u
    by (rule Mg.set_integral_eq[OF AvF[OF u] Vnn[OF u] VU[OF u]])

  have "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
      = (\<Sum>u\<in>V. set_lebesgue_integral M (Av u) (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>))"
    unfolding un[symmetric]
    by (rule set_integral_finite_Union[OF V disj intL AvM])
  also have "\<dots> = (\<Sum>u\<in>V. set_lebesgue_integral M (Av u) (Y U))"
    using congL step by simp
  also have "\<dots> = set_lebesgue_integral M A (Y U)"
    unfolding un[symmetric]
    by (rule set_integral_finite_Union[OF V disj intU AvM, symmetric])
  finally show ?thesis .
qed

subsection \<open>Dyadic approximation from above\<close>

text \<open>@{theory Continuous_Time_Martingales.Optional_Sampling}'s \<open>dceil\<close> is
  locale-bound, so the approximation uses the free-standing \<open>dyceil\<close> of
  @{theory Continuous_Time_Martingales.Dyadic_Grids}.  Approximating a stopping
  time from above is what keeps \<open>\<F>\<^sub>\<sigma> \<subseteq> \<F>\<^sub>\<sigma>\<^sub>n\<close>, so the
  conditioning set stays legal all along the approximating sequence.  Each
  approximant takes finitely many values, and a process sampled at such a time
  is measurable.\<close>

lemma borel_measurable_at_simple_time:
  fixes Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<tau> :: "'a \<Rightarrow> real"
  assumes sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<tau> \<omega> \<le> t} \<in> sets (F t)"
    and V: "finite V" and Vnn: "\<And>u. u \<in> V \<Longrightarrow> 0 \<le> u"
    and vals: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<tau> \<omega> \<in> V"
    and Ym: "\<And>u. 0 \<le> u \<Longrightarrow> Y u \<in> borel_measurable M"
  shows "(\<lambda>\<omega>. Y (\<tau> \<omega>) \<omega>) \<in> borel_measurable M"
proof -
  have sps: "space M \<in> pre_sigma_of M F \<tau>" by (rule space_in_pre_sigma_of[OF stop])
  have Sv: "{\<omega> \<in> space M. \<tau> \<omega> = v} \<in> sets M" if v: "v \<in> V" for v
  proof -
    have eq: "space M \<inter> {\<omega> \<in> space M. \<tau> \<omega> = v} = {\<omega> \<in> space M. \<tau> \<omega> = v}"
      by blast
    have "space M \<inter> {\<omega> \<in> space M. \<tau> \<omega> = v} \<in> sets (F v)"
      by (rule pre_sigma_of_value_slice[OF mono sps V Vnn vals v])
    then have "{\<omega> \<in> space M. \<tau> \<omega> = v} \<in> sets (F v)" unfolding eq .
    moreover have "sets (F v) \<subseteq> sets M"
      using sub[OF Vnn[OF v]] by (simp add: subalgebra_def)
    ultimately show ?thesis by blast  qed
  have eq: "(\<Sum>v\<in>V. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = v} \<omega> * Y v \<omega>) = Y (\<tau> \<omega>) \<omega>"
    if w: "\<omega> \<in> space M" for \<omega>
  proof -
    have tv: "\<tau> \<omega> \<in> V" by (rule vals[OF w])
    have "(\<Sum>v\<in>V. indicat_real {\<omega> \<in> space M. \<tau> \<omega> = v} \<omega> * Y v \<omega>)
        = indicat_real {\<omega>' \<in> space M. \<tau> \<omega>' = \<tau> \<omega>} \<omega> * Y (\<tau> \<omega>) \<omega>
          + (\<Sum>v\<in>V - {\<tau> \<omega>}. indicat_real {\<omega>' \<in> space M. \<tau> \<omega>' = v} \<omega> * Y v \<omega>)"
      by (rule sum.remove[OF V tv])
    moreover have "indicat_real {\<omega>' \<in> space M. \<tau> \<omega>' = \<tau> \<omega>} \<omega> = 1"
      using w by simp
    moreover have "(\<Sum>v\<in>V - {\<tau> \<omega>}. indicat_real {\<omega>' \<in> space M. \<tau> \<omega>' = v} \<omega> * Y v \<omega>)
        = 0"
      by (rule sum.neutral) auto
    ultimately show ?thesis by simp
  qed
  have "(\<lambda>\<omega>. \<Sum>v\<in>V. indicat_real {\<omega>' \<in> space M. \<tau> \<omega>' = v} \<omega> * Y v \<omega>)
      \<in> borel_measurable M"
    using Sv Ym Vnn by measurable
  then show ?thesis
    by (subst measurable_cong[OF eq[symmetric]]) simp_all
qed

subsection \<open>Optional sampling at two stopping times: the general case\<close>

text \<open>The general bounded \<open>\<sigma>\<close>: approximate from above by \<open>dyceil\<close>, which
  keeps the conditioning set legal (@{thm [source] pre_sigma_of_mono}) and
  lands in the simple case at every stage; then dominated convergence.\<close>

theorem set_martingale_sampling:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<sigma> :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Y"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U" and U0: "0 \<le> U"
    and cont: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<lambda>n. Y (dyceil n U (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    and Dbd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> U \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> D \<omega>"
    and Dint: "integrable M D"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
       = set_lebesgue_integral M A (Y U)"
proof -
  interpret Mg: martingale M F 0 Y by (rule mg)
  have AM: "A \<in> sets M" by (rule pre_sigma_of_sets[OF A])
  define \<sigma>n where "\<sigma>n n \<omega> = dyceil n U (\<sigma> \<omega>)" for n :: nat and \<omega> :: 'a
  define Vn where "Vn n = (\<lambda>j. min U (real_of_int j / 2^n)) ` {0..\<lceil>2^n * U\<rceil>}"
    for n :: nat
  have Vfin: "finite (Vn n)" for n
    unfolding Vn_def by (rule finite_dyceil_range)
  have Vnn: "0 \<le> u" if "u \<in> Vn n" for u n
  proof -
    from that obtain j where j: "j \<in> {0..\<lceil>2^n * U\<rceil>}"
      and u: "u = min U (real_of_int j / 2^n)" unfolding Vn_def by blast
    show ?thesis using j u U0 by simp
  qed
  have VU: "u \<le> U" if "u \<in> Vn n" for u n
    using that unfolding Vn_def by auto
  have vals: "\<sigma>n n \<omega> \<in> Vn n" for n \<omega>
    unfolding \<sigma>n_def Vn_def
    by (rule dyceil_range[OF U0 sig0 sigU])
  have stopn: "{\<omega> \<in> space M. \<sigma>n n \<omega> \<le> t} \<in> sets (F t)" if t: "0 \<le> t" for n t
    unfolding \<sigma>n_def
    by (rule dyceil_stopping[OF mono stop sub sig0 sigU t])
  have An: "A \<in> pre_sigma_of M F (\<sigma>n n)" for n
  proof -
    have "pre_sigma_of M F \<sigma> \<subseteq> pre_sigma_of M F (\<sigma>n n)"
      unfolding \<sigma>n_def
      by (rule pre_sigma_of_mono)
         (use dyceil_ge[OF sig0 sigU] stopn[unfolded \<sigma>n_def] in auto)
    then show ?thesis using A by blast
  qed
  have simple: "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<sigma>n n \<omega>) \<omega>)
      = set_lebesgue_integral M A (Y U)" for n
    by (rule set_martingale_sampling_simple
        [OF mg mono An Vfin Vnn VU vals])

  \<comment> \<open>and the limit\<close>
  have Ym: "Y u \<in> borel_measurable M" if "0 \<le> u" for u
    using Mg.integrable[OF that] by (rule borel_measurable_integrable)
  have gm: "(\<lambda>\<omega>. indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega>) \<in> borel_measurable M" for n
  proof -
    have "(\<lambda>\<omega>. Y (\<sigma>n n \<omega>) \<omega>) \<in> borel_measurable M"
      by (rule borel_measurable_at_simple_time
          [OF sub mono stopn Vfin Vnn vals Ym])
    then show ?thesis using AM by measurable
  qed
  have lim: "(\<lambda>n. indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega>)
      \<longlonglongrightarrow> indicat_real A \<omega> * Y (\<sigma> \<omega>) \<omega>" if w: "\<omega> \<in> space M" for \<omega>
    unfolding \<sigma>n_def using cont[OF w] by (intro tendsto_intros)
  have bd: "AE \<omega> in M.
      \<forall>n. norm (indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega>) \<le> \<bar>D \<omega>\<bar>"
    using Dbd
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof
      fix n
      have "0 \<le> \<sigma>n n \<omega>" unfolding \<sigma>n_def by (rule dyceil_nonneg[OF sig0 sigU])
      moreover have "\<sigma>n n \<omega> \<le> U" unfolding \<sigma>n_def by (rule dyceil_le_U)
      ultimately have b: "\<bar>Y (\<sigma>n n \<omega>) \<omega>\<bar> \<le> D \<omega>" using elim by simp
      then have D0: "0 \<le> D \<omega>" by simp
      show "norm (indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega>) \<le> \<bar>D \<omega>\<bar>"
        using b D0 by (simp add: indicator_def abs_mult)
    qed
  qed  have glim: "(\<lambda>\<omega>. indicat_real A \<omega> * Y (\<sigma> \<omega>) \<omega>) \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ_metric[OF gm lim])
  have conv: "(\<lambda>n. \<integral>\<omega>. indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega> \<partial>M)
      \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real A \<omega> * Y (\<sigma> \<omega>) \<omega> \<partial>M)"
  proof (rule integral_dominated_convergence[where w = "\<lambda>\<omega>. \<bar>D \<omega>\<bar>"])
    show "(\<lambda>\<omega>. indicat_real A \<omega> * Y (\<sigma> \<omega>) \<omega>) \<in> borel_measurable M"
      by (rule glim)
    show "(\<lambda>\<omega>. indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega>) \<in> borel_measurable M" for n
      by (rule gm)
    show "integrable M (\<lambda>\<omega>. \<bar>D \<omega>\<bar>)" using Dint by simp
    show "AE x in M. norm (indicat_real A x * Y (\<sigma>n n x) x) \<le> \<bar>D x\<bar>" for n
      using bd by (auto elim: eventually_mono)
    show "AE x in M. (\<lambda>n. indicat_real A x * Y (\<sigma>n n x) x)
        \<longlonglongrightarrow> indicat_real A x * Y (\<sigma> x) x"
      by (rule eventually_mono[OF AE_space]) (rule lim)
  qed
  have const: "(\<integral>\<omega>. indicat_real A \<omega> * Y (\<sigma>n n \<omega>) \<omega> \<partial>M)
      = set_lebesgue_integral M A (Y U)" for n
    using simple[of n] unfolding set_lebesgue_integral_def by simp
  have "(\<lambda>n :: nat. set_lebesgue_integral M A (Y U))
      \<longlonglongrightarrow> (\<integral>\<omega>. indicat_real A \<omega> * Y (\<sigma> \<omega>) \<omega> \<partial>M)"
    using conv const by simp
  then have "set_lebesgue_integral M A (Y U)
      = (\<integral>\<omega>. indicat_real A \<omega> * Y (\<sigma> \<omega>) \<omega> \<partial>M)"
    by (simp add: LIMSEQ_const_iff)
  then show ?thesis unfolding set_lebesgue_integral_def by simp
qed

text \<open>Comparing two stopping times: apply
  \<open>set_martingale_sampling\<close> at each of them against the common
  horizon.  The conditioning set is legal for the later one because
  \<open>pre_sigma_of_mono\<close> carries it up.\<close>

theorem set_martingale_sampling_two:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<sigma> \<rho> :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Y"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and stops: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and stopr: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<rho> \<omega> \<le> t} \<in> sets (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U"
    and rho0: "\<And>\<omega>. 0 \<le> \<rho> \<omega>" and rhoU: "\<And>\<omega>. \<rho> \<omega> \<le> U" and U0: "0 \<le> U"
    and le: "\<And>\<omega>. \<sigma> \<omega> \<le> \<rho> \<omega>"
    and conts: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<lambda>n. Y (dyceil n U (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    and contr: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<lambda>n. Y (dyceil n U (\<rho> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<rho> \<omega>) \<omega>"
    and Dbd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> U \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> D \<omega>"
    and Dint: "integrable M D"
  shows "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)       = set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<rho> \<omega>) \<omega>)"
proof -
  have s: "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
      = set_lebesgue_integral M A (Y U)"
    by (rule set_martingale_sampling
        [OF mg mono sub A stops sig0 sigU U0 conts Dbd Dint])
  have Ar: "A \<in> pre_sigma_of M F \<rho>"
    using pre_sigma_of_mono[OF le stopr] A by blast
  have r: "set_lebesgue_integral M A (\<lambda>\<omega>. Y (\<rho> \<omega>) \<omega>)
      = set_lebesgue_integral M A (Y U)"
    by (rule set_martingale_sampling
        [OF mg mono sub Ar stopr rho0 rhoU U0 contr Dbd Dint])
  show ?thesis using s r by simp
qed

text \<open>The same dyadic approximation, without a conditioning set, shows that a
  dominated martingale sampled at a bounded stopping time is integrable.\<close>

lemma integrable_at_bounded_stopping_time:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<sigma> :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Y"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U" and U0: "0 \<le> U"
    and cont: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<lambda>n. Y (dyceil n U (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    and Dbd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> U \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> D \<omega>"
    and Dint: "integrable M D"
  shows "integrable M (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
proof -
  interpret Mg: martingale M F 0 Y by (rule mg)
  have mono: "sets (F s) \<subseteq> sets (F t)" if "0 \<le> s" "s \<le> t" for s t
    using Mg.sets_F_mono[OF that] by simp
  note sub = Mg.subalgebras
  define \<sigma>n where "\<sigma>n n \<omega> = dyceil n U (\<sigma> \<omega>)" for n :: nat and \<omega> :: 'a
  define Vn where "Vn n = (\<lambda>j. min U (real_of_int j / 2^n)) ` {0..\<lceil>2^n * U\<rceil>}"
    for n :: nat
  have Vfin: "finite (Vn n)" for n
    unfolding Vn_def by (rule finite_dyceil_range)
  have Vnn: "0 \<le> u" if "u \<in> Vn n" for u n
  proof -
    from that obtain j where j: "j \<in> {0..\<lceil>2^n * U\<rceil>}"
      and u: "u = min U (real_of_int j / 2^n)" unfolding Vn_def by blast
    show ?thesis using j u U0 by simp
  qed
  have vals: "\<sigma>n n \<omega> \<in> Vn n" for n \<omega>
    unfolding \<sigma>n_def Vn_def by (rule dyceil_range[OF U0 sig0 sigU])
  have stopn: "{\<omega> \<in> space M. \<sigma>n n \<omega> \<le> t} \<in> sets (F t)" if t: "0 \<le> t" for n t
    unfolding \<sigma>n_def by (rule dyceil_stopping[OF mono stop sub sig0 sigU t])
  have Ym: "Y u \<in> borel_measurable M" if "0 \<le> u" for u
    using Mg.integrable[OF that] by (rule borel_measurable_integrable)
  have gm: "(\<lambda>\<omega>. Y (\<sigma>n n \<omega>) \<omega>) \<in> borel_measurable M" for n
    by (rule borel_measurable_at_simple_time
        [OF sub mono stopn Vfin Vnn vals Ym])
  have lim: "(\<lambda>n. Y (\<sigma>n n \<omega>) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>" if w: "\<omega> \<in> space M" for \<omega>
    unfolding \<sigma>n_def by (rule cont[OF w])
  have glim: "(\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>) \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ_metric[OF gm lim])
  have bd: "AE \<omega> in M. norm (Y (\<sigma> \<omega>) \<omega>) \<le> norm \<bar>D \<omega>\<bar>"
    using Dbd
  proof eventually_elim
    case (elim \<omega>)
    have "\<bar>Y (\<sigma> \<omega>) \<omega>\<bar> \<le> D \<omega>" using elim sig0[of \<omega>] sigU[of \<omega>] by simp
    then show ?case by simp
  qed
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[where f = "\<lambda>\<omega>. \<bar>D \<omega>\<bar>"])
    show "integrable M (\<lambda>\<omega>. \<bar>D \<omega>\<bar>)" using Dint by simp
    show "(\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>) \<in> borel_measurable M" by (rule glim)
    show "AE \<omega> in M. norm (Y (\<sigma> \<omega>) \<omega>) \<le> norm \<bar>D \<omega>\<bar>" by (rule bd)
  qed
qed

(*<*)
end
(*>*)
