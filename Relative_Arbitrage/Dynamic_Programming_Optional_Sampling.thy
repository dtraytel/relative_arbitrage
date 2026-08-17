section \<open>Optional sampling at two stopping times\<close>

(*<*)
theory Dynamic_Programming_Optional_Sampling
  imports Dynamic_Programming_Kernels
    "Continuous_Time_Martingales.Time_Discretisation"
begin

(*>*)

section \<open>Optional sampling at two stopping times: the simple case\<close>

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

text \<open>@{theory Continuous_Time_Martingales.Optional_Sampling}'s \<open>dceil\<close> is locale-bound, so here is a
  free-standing one.  Approximating a stopping time from above is what
  keeps \<open>\<F>\<^sub>\<sigma> \<subseteq> \<F>\<^sub>\<sigma>\<^sub>n\<close>, so the conditioning set stays legal all along the
  approximating sequence.\<close>

definition dyceil :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where "dyceil n U x = min U (real_of_int \<lceil>2^n * x\<rceil> / 2^n)"

lemma dyceil_le_U: "dyceil n U x \<le> U"
  unfolding dyceil_def by simp

lemma dyceil_ge:
  assumes x: "0 \<le> x" and xU: "x \<le> U"
  shows "x \<le> dyceil n U x"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have "2^n * x \<le> real_of_int \<lceil>2^n * x\<rceil>" by (rule le_of_int_ceiling)
  then have "x \<le> real_of_int \<lceil>2^n * x\<rceil> / 2^n" using p by (simp add: field_simps)
  then show ?thesis unfolding dyceil_def using xU by simp
qed

lemma dyceil_nonneg:
  assumes x: "0 \<le> x" and xU: "x \<le> U"
  shows "0 \<le> dyceil n U x"
  using x dyceil_ge[OF x xU, of n] by simp

text \<open>Finitely many values --- which is what makes
  @{thm [source] set_martingale_sampling_simple} applicable.\<close>

lemma dyceil_range:
  assumes U: "0 \<le> U" and x: "0 \<le> x" and xU: "x \<le> U"
  shows "dyceil n U x
      \<in> (\<lambda>j. min U (real_of_int j / 2^n)) ` {0..\<lceil>2^n * U\<rceil>}"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have lo: "0 \<le> \<lceil>2^n * x\<rceil>"
  proof -
    have "(0::real) \<le> 2^n * x" using x by simp
    then have "\<lceil>(0::real)\<rceil> \<le> \<lceil>2^n * x\<rceil>" by (rule ceiling_mono)
    then show ?thesis by simp
  qed  have hi: "\<lceil>2^n * x\<rceil> \<le> \<lceil>2^n * U\<rceil>" using xU by (intro ceiling_mono) simp
  show ?thesis unfolding dyceil_def using lo hi by (intro image_eqI) auto
qed

text \<open>\<open>finite_dyceil_range\<close> lives in @{theory Continuous_Time_Martingales.Time_Discretisation}.\<close>


text \<open>The key computation: below the horizon, \<open>dyceil\<close> is at most \<open>t\<close> exactly
  when the original time is at most the grid point just below \<open>t\<close>, which is
  \<open>\<le> t\<close>, so the event lands in the filtration at \<open>t\<close>.\<close>

lemma dyceil_le_iff:
  assumes t: "0 \<le> t" and tU: "t < U"
  shows "(dyceil n U x \<le> t) = (x \<le> real_of_int \<lfloor>2^n * t\<rfloor> / 2^n)"
proof -
  have p: "(0 :: real) < 2^n" by simp
  have "(dyceil n U x \<le> t) = (real_of_int \<lceil>2^n * x\<rceil> / 2^n \<le> t)"
    unfolding dyceil_def using tU by (auto simp: min_le_iff_disj)
  also have "\<dots> = (real_of_int \<lceil>2^n * x\<rceil> \<le> 2^n * t)"
    using p by (simp add: field_simps)
  also have "\<dots> = (\<lceil>2^n * x\<rceil> \<le> \<lfloor>2^n * t\<rfloor>)" by (simp add: le_floor_iff)
  also have "\<dots> = (2^n * x \<le> real_of_int \<lfloor>2^n * t\<rfloor>)" by (simp add: ceiling_le_iff)
  also have "\<dots> = (x \<le> real_of_int \<lfloor>2^n * t\<rfloor> / 2^n)"
    using p by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>\<open>dyceil_grid_le\<close> lives in @{theory Continuous_Time_Martingales.Time_Discretisation}.\<close>


lemma dyceil_tendsto:
  assumes x: "0 \<le> x" and xU: "x \<le> U"
  shows "(\<lambda>n. dyceil n U x) \<longlonglongrightarrow> x"
proof -
  have bnd: "\<bar>dyceil n U x - x\<bar> \<le> (1/2)^n" for n
  proof -
    have p: "(0 :: real) < 2^n" by simp
    have lo: "x \<le> dyceil n U x" by (rule dyceil_ge[OF x xU])
    have "real_of_int \<lceil>2^n * x\<rceil> < 2^n * x + 1"
      using ceiling_correct[of "2^n * x"] by simp
    then have "real_of_int \<lceil>2^n * x\<rceil> / 2^n \<le> x + 1 / 2^n"
      using p by (simp add: field_simps)
    then have "dyceil n U x \<le> x + 1 / 2^n"
      unfolding dyceil_def by simp
    with lo show ?thesis by (simp add: power_one_over)
  qed
  have "(\<lambda>n. dyceil n U x - x) \<longlonglongrightarrow> 0"
  proof (rule Lim_null_comparison)
    show "\<forall>\<^sub>F n in sequentially. norm (dyceil n U x - x) \<le> (1/2)^n"
      using bnd by simp
    show "(\<lambda>n. ((1 :: real)/2)^n) \<longlonglongrightarrow> 0" by (rule LIMSEQ_realpow_zero) simp_all
  qed
  then show ?thesis by (rule Lim_transform[OF tendsto_const])
qed

text \<open>And the stopping-time property survives: \<open>{dyceil \<circ> \<sigma> \<le> t}\<close> is
  \<open>{\<sigma> \<le> (grid point below t)}\<close>, an event of the filtration at that grid
  point, hence at \<open>t\<close>.\<close>

lemma dyceil_stopping:
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U"
    and t: "0 \<le> t"
  shows "{\<omega> \<in> space M. dyceil n U (\<sigma> \<omega>) \<le> t} \<in> sets (F t)"
proof (cases "t < U")
  case True
  define g where "g = real_of_int \<lfloor>2^n * t\<rfloor> / 2^n"
  have g0: "0 \<le> g" unfolding g_def by (rule dyceil_grid_le(2)[OF t])
  have gt: "g \<le> t" unfolding g_def by (rule dyceil_grid_le(1)[OF t])
  have "{\<omega> \<in> space M. dyceil n U (\<sigma> \<omega>) \<le> t} = {\<omega> \<in> space M. \<sigma> \<omega> \<le> g}"
    unfolding g_def using dyceil_le_iff[OF t True] by simp
  moreover have "{\<omega> \<in> space M. \<sigma> \<omega> \<le> g} \<in> sets (F t)"
    using stop[OF g0] mono[OF g0 gt] by blast
  ultimately show ?thesis by simp
next
  case False
  have "dyceil n U (\<sigma> \<omega>) \<le> t" for \<omega>
  proof -
    have "dyceil n U (\<sigma> \<omega>) \<le> U" by (rule dyceil_le_U)
    then show ?thesis using False by simp
  qed
  then have "{\<omega> \<in> space M. dyceil n U (\<sigma> \<omega>) \<le> t} = space M" by blast  moreover have "space M \<in> sets (F t)"
  proof -
    have "space (F t) = space M" using sub[OF t] by (simp add: subalgebra_def)
    then show ?thesis using sets.top[of "F t"] by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open>Sampling a process at a simple stopping time is measurable, because the
  result is a finite sum of pieces.  \<open>space M\<close> is itself an \<open>\<F>\<^sub>\<tau>\<close>-set, so the
  value slices come straight from @{thm [source] pre_sigma_of_value_slice}.\<close>

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

section \<open>Optional sampling at two stopping times: the general case\<close>

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
section \<open>From the pathwise stopping time to the filtration one\<close>

text \<open>\<open>path_stopping_time\<close> is the pathwise notion: \<open>\<theta>\<close> is decided by the
  path up to \<open>\<theta>\<close>.  What the sampling theorem consumes is the filtration
  notion, \<open>{\<theta> \<le> t} \<in> \<F>\<^sub>t\<close>.  The bridge is that below \<open>t\<close> the event only sees
  the path stopped at \<open>t\<close>: \<open>\<theta> \<omega> \<le> t\<close> exactly when
  \<open>\<theta> (\<omega> stopped at t) \<le> t\<close>, and the stopped path is an \<open>\<F>\<^sub>t\<close>-measurable
  function of \<open>\<omega>\<close>.\<close>

lemma path_stopping_time_cut:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "path_stopping_time T \<theta>" and t: "0 \<le> t" and tT: "t \<le> T"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "(\<theta> \<omega> \<le> t) = (\<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t)"
proof
  assume h: "\<theta> \<omega> \<le> t"
  have cs0: "continuous_on {0..T} (\<lambda>s. fst (pstopped T (\<lambda>_. t) \<omega> s))"
    by (rule pstopped_fst_continuous[OF cw]) (use t tT in auto)
  have "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
  proof (rule path_stopping_time_cong[OF st cw cs0])
    fix s assume s: "s \<in> {0..\<theta> \<omega>}"
    then have sT: "s \<in> {0..T}" using h tT by auto
    have "min s t = s" using s h by simp
    then show "\<omega> s = pstopped T (\<lambda>_. t) \<omega> s"
      by (simp add: pstopped_apply[OF sT])
  qed
  then show "\<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t" using h by simp
next
  assume h: "\<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t"
  have cs: "continuous_on {0..T} (\<lambda>s. fst (pstopped T (\<lambda>_. t) \<omega> s))"
    by (rule pstopped_fst_continuous[OF cw]) (use t tT in auto)
  have "\<theta> \<omega> = \<theta> (pstopped T (\<lambda>_. t) \<omega>)"
  proof (rule path_stopping_time_cong[OF st cs cw])
    fix s assume s: "s \<in> {0..\<theta> (pstopped T (\<lambda>_. t) \<omega>)}"
    then have sT: "s \<in> {0..T}" using h tT by auto
    have "min s t = s" using s h by simp
    then show "pstopped T (\<lambda>_. t) \<omega> s = \<omega> s"
      by (simp add: pstopped_apply[OF sT])
  qed
  then show "\<theta> \<omega> \<le> t" using h by simp
qed

text \<open>Hence the event is measurable with respect to the natural filtration at
  \<open>t\<close> --- the stopped path is, and \<open>\<theta>\<close> is Borel.\<close>

text \<open>The times clause (iv) samples at are \<open>(\<theta> + i) \<and> T\<close>, and they are
  stopping times for the same reason \<open>\<theta>\<close> is: shifting forward and capping
  only ever looks further back, so two paths agreeing up to the shifted time
  agree up to \<open>\<theta>\<close> as well.\<close>

lemma path_stopping_time_shift:
  fixes \<theta> :: "'n::finite pairpath \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and i: "0 \<le> i"
  shows "path_stopping_time T (\<lambda>\<omega>. min (\<theta> \<omega> + i) T)"
proof -
  have c1: "0 \<le> min (\<theta> \<omega> + i) T \<and> min (\<theta> \<omega> + i) T \<le> T"
    for \<omega> :: "'n pairpath"
  proof -
    have "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
    moreover have "\<theta> \<omega> \<le> T" by (rule path_stopping_time_le[OF st])
    ultimately show ?thesis using i by simp
  qed
  have c2: "min (\<theta> \<omega>' + i) T = min (\<theta> \<omega> + i) T"
    if cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
      and cw': "continuous_on {0..T} (\<lambda>u. fst (\<omega>' u))"
      and ag: "\<forall>s \<in> {0..min (\<theta> \<omega> + i) T}. \<omega> s = \<omega>' s"
    for \<omega> \<omega>' :: "'n pairpath"
  proof -
    have le: "\<theta> \<omega> \<le> min (\<theta> \<omega> + i) T"
      using i path_stopping_time_le[OF st, of \<omega>] by simp
    have "\<theta> \<omega>' = \<theta> \<omega>"
    proof (rule path_stopping_time_cong[OF st cw cw'])
      fix s assume "s \<in> {0..\<theta> \<omega>}"
      then have "s \<in> {0..min (\<theta> \<omega> + i) T}" using le by auto
      then show "\<omega> s = \<omega>' s" using ag by blast
    qed
    then show ?thesis by simp
  qed
  show ?thesis unfolding path_stopping_time_def using c1 c2 by blast
qed

text \<open>They are also ordered in \<open>i\<close>, which is what lets
  @{thm [source] pre_sigma_of_mono} carry the conditioning set from the
  earlier sampling time to the later one; pure arithmetic, discharged where
  it is used.\<close>

text \<open>The stopping-time event is not merely Borel but lies in the natural
  filtration at \<open>t\<close>, which is what @{thm [source] set_martingale_sampling}
  consumes.  @{thm [source] path_eval_measurable_natural_filtration} ties
  the filtration index to the horizon; decoupling them is the only change
  its proof needs.\<close>

lemma path_eval_measurable_natural_filtration':
  fixes U u v :: real
  assumes v: "v \<in> {0..u}"
  shows "(\<lambda>\<omega> :: 'n::finite pairpath. \<omega> v) \<in> borel_measurable (natural_filtration
      (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
      0 (\<lambda>v \<omega>. \<omega> v) u)"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use v in auto)

lemma pstopped_const_measurable_filtration:
  fixes T t :: real
  assumes T0: "0 \<le> T" and t: "0 \<le> t" and tT: "t \<le> T"
  shows "pstopped T (\<lambda>_. t)
      \<in> natural_filtration (borel_of (mtopology_of
          (path_metric T :: ('n::finite pairpath) metric))) 0 (\<lambda>v \<omega>. \<omega> v) t
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t"
  have spF: "space ?F = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have into: "pstopped T (\<lambda>_. t) \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    if w: "\<omega> \<in> space ?F" for \<omega> :: "'n pairpath"
  proof -
    have m: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w spF by simp
    show ?thesis by (rule pstopped_mspace[OF t tT m])
  qed
  have ev: "(\<lambda>\<omega> :: 'n pairpath. pstopped T (\<lambda>_. t) \<omega> s) \<in> borel_measurable ?F"
    for s
  proof (cases "s \<in> {0..T}")
    case True
    have mem: "min s t \<in> {0..t}" using True t by simp
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min s t)) \<in> borel_measurable ?F"
      by (rule path_eval_measurable_natural_filtration'[OF mem])
    then show ?thesis by (simp add: pstopped_apply[OF True])
  next
    case False
    have "(\<lambda>\<omega> :: 'n pairpath. pstopped T (\<lambda>_. t) \<omega> s)
        = (\<lambda>\<omega> :: 'n pairpath. undefined)"
      by (rule ext) (rule pstopped_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>\<omega>. mdist (path_metric T :: ('n pairpath) metric)
        (pstopped T (\<lambda>_. t) \<omega>) a) \<in> borel_measurable ?F"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

lemma path_stopping_time_event_filtration:
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric)))"
    and t: "0 \<le> t" and tT: "t \<le> T"
  shows "{\<omega> \<in> space (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))). \<theta> \<omega> \<le> t}
      \<in> sets (natural_filtration (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric))) 0 (\<lambda>v \<omega>. \<omega> v) t)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t"
  have spF: "space ?F = space ?B" by simp
  have cm: "pstopped T (\<lambda>_. t) \<in> ?F \<rightarrow>\<^sub>M ?B"
    by (rule pstopped_const_measurable_filtration[OF T0 t tT])
  have thc: "(\<lambda>\<omega> :: 'n pairpath. \<theta> (pstopped T (\<lambda>_. t) \<omega>)) \<in> borel_measurable ?F"
    using cm by (rule measurable_compose) (rule thM)
  have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}
      = {\<omega> \<in> space ?F. \<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t}"
    unfolding spF
  proof (rule Collect_cong, rule conj_cong[OF refl])
    fix \<omega> :: "'n pairpath" assume w: "\<omega> \<in> space ?B"
    have cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
      by (rule path_sets_fst_continuous[OF refl w])
    show "(\<theta> \<omega> \<le> t) = (\<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t)"
      by (rule path_stopping_time_cut[OF st t tT cw])
  qed
  moreover have "{\<omega> \<in> space ?F. \<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t} \<in> sets ?F"
    using thc by measurable
  ultimately show ?thesis by simp
qed

text \<open>Comparing two stopping times: apply
  @{thm [source] set_martingale_sampling} at each of them against the common
  horizon.  The conditioning set is legal for the later one because
  @{thm [source] pre_sigma_of_mono} carries it up.  This is the form clause
  (iv) uses, at \<open>\<sigma> = (\<theta>+i) \<and> T\<close> and \<open>\<rho> = (\<theta>+j) \<and> T\<close>.\<close>

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


(*<*)
end
(*>*)
