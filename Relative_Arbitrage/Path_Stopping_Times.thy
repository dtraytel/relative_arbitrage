section \<open>Stopping times as path functionals\<close>

(*<*)
theory Path_Stopping_Times
  imports Path_Splicing
begin

(*>*)

text \<open>\<open>path_stopping_time T \<theta>\<close> asks that \<open>\<theta>\<close> read only the path up to
  \<open>\<theta>\<close> itself; \<open>pstopped\<close> and \<open>pafter\<close> split a path there, \<open>pre_sigma_of\<close>
  is the sigma-algebra of the past, and \<open>dyceil\<close> is the dyadic ceiling that
  approximates a stopping time from above by simple ones.\<close>

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
  \<open>set_martingale_sampling_simple\<close> applicable.\<close>

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

lemma exit_component_dyceil_tendsto:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>n. fst (\<omega> (min (dyceil n T s) T)) $ c)
      \<longlonglongrightarrow> fst (\<omega> (min s T)) $ c"
proof -
  have cont: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u) $ c)"
    using mspace_path_metricD[OF w] by (intro continuous_intros)
  have conv: "(\<lambda>n. dyceil n T s) \<longlonglongrightarrow> s" by (rule dyceil_tendsto[OF s0 sT])
  have mem: "dyceil n T s \<in> {0..T}" for n
    using dyceil_nonneg[OF s0 sT] dyceil_le_U[of n T s] by simp
  have "(\<lambda>n. fst (\<omega> (dyceil n T s)) $ c) \<longlonglongrightarrow> fst (\<omega> s) $ c"
  proof (rule continuous_on_tendsto_compose[OF cont conv])
    show "\<forall>\<^sub>F n in sequentially. dyceil n T s \<in> {0..T}" using mem by simp
    show "s \<in> {0..T}" using s0 sT by simp
  qed
  moreover have "min (dyceil n T s) T = dyceil n T s" for n
    using dyceil_le_U[of n T s] by simp
  moreover have "min s T = s" using sT by simp
  ultimately show ?thesis by simp
qed

text \<open>And the \<open>stops\<close> hypothesis at the shifted time.  Above the horizon the
  event is everything, since \<open>(\<theta>+i) \<and> T \<le> T\<close>; below it,
  \<open>path_stopping_time_event_filtration\<close> applies to the shifted
  stopping time.\<close>

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
  value slices come straight from \<open>pre_sigma_of_value_slice\<close>.\<close>

definition pstopped :: "real \<Rightarrow> ((real \<Rightarrow> 'b) \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'b)
    \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pstopped T \<theta> \<omega> = restrict (\<lambda>t. \<omega> (min t (\<theta> \<omega>))) {0..T}"

definition pafter :: "real \<Rightarrow> ((real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'b)
    \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pafter T \<theta> \<omega> = restrict (\<lambda>t. \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)) {0..T}"

lemma pstopped_apply: "t \<in> {0..T} \<Longrightarrow> pstopped T \<theta> \<omega> t = \<omega> (min t (\<theta> \<omega>))"
  by (simp add: pstopped_def)

lemma pafter_apply:
  "t \<in> {0..T} \<Longrightarrow> pafter T \<theta> \<omega> t = \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)"
  by (simp add: pafter_def)

lemma pstopped_outside: "t \<notin> {0..T} \<Longrightarrow> pstopped T \<theta> \<omega> t = undefined"
  unfolding pstopped_def restrict_def by (rule if_not_P)

lemma pafter_outside: "t \<notin> {0..T} \<Longrightarrow> pafter T \<theta> \<omega> t = undefined"
  unfolding pafter_def restrict_def by (rule if_not_P)
text \<open>The reassembly law.  This is the analogue of
  @{thm [source] pglue_pcut_pfut} at a random time, and unlike that one it
  costs nothing: no membership hypothesis on \<open>\<omega>\<close>, and no \<open>\<theta>\<close> on the
  right-hand side.\<close>

lemma pstopped_add_pafter:
  fixes \<omega> :: "real \<Rightarrow> 'b::ab_group_add"
  assumes th0: "0 \<le> \<theta> \<omega>" and thT: "\<theta> \<omega> \<le> T" and t: "t \<in> {0..T}"
  shows "pstopped T \<theta> \<omega> t + pafter T \<theta> \<omega> t = \<omega> t"
proof (cases "t \<le> \<theta> \<omega>")
  case True
  then have m1: "min t (\<theta> \<omega>) = t" and m2: "max t (\<theta> \<omega>) = \<theta> \<omega>" by simp_all
  show ?thesis using t by (simp add: pstopped_apply pafter_apply m1 m2)
next
  case False
  then have m1: "min t (\<theta> \<omega>) = \<theta> \<omega>" and m2: "max t (\<theta> \<omega>) = t" by simp_all
  show ?thesis using t by (simp add: pstopped_apply pafter_apply m1 m2)
qed

text \<open>The future factor starts at \<open>0\<close> --- exactly the normalisation the class
  asks of a continuation --- and the two halves live on disjoint stretches of
  time.\<close>

lemma pafter_before:
  fixes \<omega> :: "real \<Rightarrow> 'b::ab_group_add"
  assumes t: "t \<in> {0..T}" and le: "t \<le> \<theta> \<omega>"
  shows "pafter T \<theta> \<omega> t = 0"
  using t le by (simp add: pafter_apply max_absorb2)

text \<open>Evaluating a path at a random time.  This is the one new measurability
  fact the additive split needs, and it is where the paths' continuity is
  spent: approximate the time from above by dyadic rationals, each fixed
  dyadic giving a measurable evaluation among only countably many, and pass
  to the limit inside each path.  Only pointwise continuity of each path is
  used, so no uniform-continuity machinery is needed.  Compare
  @{thm [source] stopped_adapted_of_cont}, which runs the same dyadic
  argument for a real-valued adapted process and delivers the sharper
  \<open>\<F>\<^sub>v\<close>-measurability, needing the paths capped as \<open>\<omega> (min s T)\<close> because it
  asks for continuity on all of \<open>{0..}\<close>.\<close>

lemma pstopped_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes th0: "0 \<le> \<theta> \<omega>" and thT: "\<theta> \<omega> \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pstopped T \<theta> \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. min t (\<theta> \<omega>))" by (intro continuous_intros)
  have im: "(\<lambda>t. min t (\<theta> \<omega>)) ` {0..T} \<subseteq> {0..T}" using th0 thT by auto
  have "continuous_on {0..T} (\<lambda>t. \<omega> (min t (\<theta> \<omega>)))"
    by (rule continuous_on_compose2[OF c m im])
  then show ?thesis unfolding pstopped_def by (rule mspace_path_metricI)
qed

lemma pstopped_const_measurable_filtration:
  fixes T t :: real
  assumes T0: "0 \<le> T" and t: "0 \<le> t" and tT: "t \<le> T"
  shows "pstopped T (\<lambda>_. t)
      \<in> natural_filtration (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure) 0 (\<lambda>v \<omega>. \<omega> v) t
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t"
  have spF: "space ?F = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have into: "pstopped T (\<lambda>_. t) \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if w: "\<omega> \<in> space ?F" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof -
    have m: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      using w spF by simp
    show ?thesis by (rule pstopped_mspace[OF t tT m])
  qed
  have ev: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T (\<lambda>_. t) \<omega> s) \<in> borel_measurable ?F"
    for s
  proof (cases "s \<in> {0..T}")
    case True
    have mem: "min s t \<in> {0..t}" using True t by simp
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (min s t)) \<in> borel_measurable ?F"
      by (rule path_eval_measurable_natural_filtration'[OF mem])
    then show ?thesis by (simp add: pstopped_apply[OF True])
  next
    case False
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T (\<lambda>_. t) \<omega> s)
        = (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). undefined)"
      by (rule ext) (rule pstopped_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>\<omega>. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pstopped T (\<lambda>_. t) \<omega>) a) \<in> borel_measurable ?F"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

lemma pafter_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes th0: "0 \<le> \<theta> \<omega>" and thT: "\<theta> \<omega> \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pafter T \<theta> \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. max t (\<theta> \<omega>))" by (intro continuous_intros)
  have im: "(\<lambda>t. max t (\<theta> \<omega>)) ` {0..T} \<subseteq> {0..T}" using th0 thT by auto
  have "continuous_on {0..T} (\<lambda>t. \<omega> (max t (\<theta> \<omega>)))"
    by (rule continuous_on_compose2[OF c m im])
  then have "continuous_on {0..T} (\<lambda>t. \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>))"
    by (intro continuous_intros)
  then show ?thesis unfolding pafter_def by (rule mspace_path_metricI)
qed

text \<open>A criterion for landing in the path space.  The balls are a base, so
  Borel measurability into \<open>?B\<^sub>T\<close> reduces to measurability of the distance to
  each point, which the additive split can supply, since the distance is a
  sup over time of evaluations and @{thm [source] path_eval_at_measurable_time}
  makes each evaluation measurable.  The generator route through
  @{thm [source] sets_natural_filtration_path} would work too, but needs no
  handle on \<open>natural_filtration\<close>'s generators.\<close>

lemma pstopped_measurable:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach}) \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and thm': "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "pstopped T \<theta> \<in> (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have sp: "space ?B = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have into: "pstopped T \<theta> \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if "\<omega> \<in> space ?B" for \<omega>
    using that sp by (intro pstopped_mspace[OF th0 thT]) simp
  have ev: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> \<omega> t) \<in> borel_measurable ?B" for t
  proof (cases "t \<in> {0..T}")
    case True
    have base: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (min t (\<theta> \<omega>))) \<in> borel_measurable ?B"
    proof (rule path_eval_at_measurable_time
        [where X = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega>" and g = "\<lambda>\<omega>. min t (\<theta> \<omega>)", OF T0])
      show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega>) \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule measurable_ident_sets[OF refl])
      show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). min t (\<theta> \<omega>)) \<in> borel_measurable ?B"
        using thm' by measurable
      show "0 \<le> min t (\<theta> \<omega>)" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
        using True th0[of \<omega>] by simp
      show "min t (\<theta> \<omega>) \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
        using thT[of \<omega>] by simp
    qed
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> \<omega> t)
        = (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (min t (\<theta> \<omega>)))"
      by (rule ext) (rule pstopped_apply[OF True])
    then show ?thesis using base by simp
  next
    case False
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> \<omega> t) = (\<lambda>\<omega>. undefined)"
      by (rule ext) (rule pstopped_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>\<omega>. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pstopped T \<theta> \<omega>) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

lemma pafter_measurable:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach}) \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and thm': "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "pafter T \<theta> \<in> (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have sp: "space ?B = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have into: "pafter T \<theta> \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if "\<omega> \<in> space ?B" for \<omega>
    using that sp by (intro pafter_mspace[OF th0 thT]) simp
  have base0: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (\<theta> \<omega>)) \<in> borel_measurable ?B"
  proof (rule path_eval_at_measurable_time
      [where X = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega>" and g = \<theta>, OF T0])
    show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega>) \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule measurable_ident_sets[OF refl])
    show "\<theta> \<in> borel_measurable ?B" by (rule thm')
    show "0 \<le> \<theta> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" by (rule th0)
    show "\<theta> \<omega> \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" by (rule thT)
  qed
  have ev: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pafter T \<theta> \<omega> t) \<in> borel_measurable ?B" for t
  proof (cases "t \<in> {0..T}")
    case True
    have base: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (max t (\<theta> \<omega>))) \<in> borel_measurable ?B"
    proof (rule path_eval_at_measurable_time
        [where X = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega>" and g = "\<lambda>\<omega>. max t (\<theta> \<omega>)", OF T0])
      show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega>) \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule measurable_ident_sets[OF refl])
      show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). max t (\<theta> \<omega>)) \<in> borel_measurable ?B"
        using thm' by measurable
      show "0 \<le> max t (\<theta> \<omega>)" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
        using th0[of \<omega>] by simp
      show "max t (\<theta> \<omega>) \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
        using True thT[of \<omega>] by simp
    qed
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pafter T \<theta> \<omega> t)
        = (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>))"
      by (rule ext) (rule pafter_apply[OF True])
    then show ?thesis using base base0 by simp
  next
    case False
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pafter T \<theta> \<omega> t) = (\<lambda>\<omega>. undefined)"
      by (rule ext) (rule pafter_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>\<omega>. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pafter T \<theta> \<omega>) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed
subsection \<open>The regular conditional distribution, with both maps and horizons free\<close>

text \<open>\<open>exit_class_rcd\<close> and
  \<open>exit_class_rcd_ksemi\<close> use \<open>pcut r\<close> and \<open>pfut r T\<close> only
  through their measurability, so nothing in either proof is specific to the
  deterministic split.  Here they are with the two maps and the two horizons
  free; the deterministic case is the instance \<open>u := r\<close>, \<open>v := T - r\<close>, and
  the stopping-time case is \<open>u := v := T\<close>, \<open>\<phi>\<^sub>1 := pstopped T \<theta>\<close>,
  \<open>\<phi>\<^sub>2 := pafter T \<theta>\<close>.\<close>

definition path_stopping_time ::
  "real \<Rightarrow> ((real \<Rightarrow> 'a::topological_space \<times> 'b) \<Rightarrow> real) \<Rightarrow> bool"
  where "path_stopping_time T \<theta> \<longleftrightarrow>
     (\<forall>\<omega>. 0 \<le> \<theta> \<omega> \<and> \<theta> \<omega> \<le> T)
     \<and> (\<forall>\<omega> \<omega>'. continuous_on {0..T} (\<lambda>t. fst (\<omega> t)) \<longrightarrow>
          continuous_on {0..T} (\<lambda>t. fst (\<omega>' t)) \<longrightarrow>
          (\<forall>t \<in> {0..\<theta> \<omega>}. \<omega> t = \<omega>' t) \<longrightarrow> \<theta> \<omega>' = \<theta> \<omega>)"

lemma pstopped_eval_min:
  fixes p' :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>" and idem: "pstopped T \<theta> p' = p'"
    and T0: "0 \<le> T" and u: "0 \<le> u"
  shows "p' (min u T) = p' (min (min u T) (\<theta> p'))"
proof -
  have m: "min u T \<in> {0..T}" using T0 u by simp
  have "p' (min u T) = pstopped T \<theta> p' (min u T)" unfolding idem ..
  also have "\<dots> = p' (min (min u T) (\<theta> p'))" by (rule pstopped_apply[OF m])
  finally show ?thesis .
qed

text \<open>On \<open>{\<theta> > i}\<close> an \<open>\<F>\<^sub>i\<close>-set of the glue is a set of the past alone ---
  @{thm [source] pcut_padd_before} --- so its indicator does not depend on
  \<open>w\<close> at all.  On \<open>{\<theta> \<le> i}\<close>, for a fixed past, the \<open>w\<close>-section of an
  \<open>\<F>\<^sub>i\<close>-set of the glue is an \<open>\<F>\<^sub>i\<close>-set of the continuation, because
  @{thm [source] pcut_padd_section} presents it as a function of
  \<^term>\<open>pcut i w\<close>.\<close>

lemma path_stopping_time_nonneg:
  "path_stopping_time T \<theta> \<Longrightarrow> 0 \<le> \<theta> \<omega>"
  unfolding path_stopping_time_def by blast

lemma path_stopping_time_le:
  "path_stopping_time T \<theta> \<Longrightarrow> \<theta> \<omega> \<le> T"
  unfolding path_stopping_time_def by blast

text \<open>Continuity is available wherever it is needed: the space of a path law
  is the set of continuous paths.\<close>

lemma pstopped_fixed_set_measurable:
  fixes T :: real
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure)"
  shows "{p' \<in> space (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure). pstopped T \<theta> p' = p'}
      \<in> sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?D = "{0..T} \<inter> \<rat>"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_le[OF st])
  have pm: "pstopped T \<theta> \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have spB: "space ?B = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have single: "{p' \<in> space ?B. pstopped T \<theta> p' q = p' q} \<in> sets ?B" for q
  proof -
    have m1: "(\<lambda>p' :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> p' q) \<in> borel_measurable ?B"
      by (rule measurable_compose[OF pm pair_law_eval_measurable[OF refl]])
    have m2: "(\<lambda>p' :: (real \<Rightarrow> 'a \<times> 'b). p' q) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    show ?thesis using m1 m2 by measurable
  qed
  have cnt: "countable ?D" by (simp add: countable_rat)
  have ne: "?D \<noteq> {}" using T0 by auto
  have eq: "{p' \<in> space ?B. pstopped T \<theta> p' = p'}
      = (\<Inter>q \<in> ?D. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q})"
  proof
    show "{p' \<in> space ?B. pstopped T \<theta> p' = p'}
        \<subseteq> (\<Inter>q \<in> ?D. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q})" by auto
    show "(\<Inter>q \<in> ?D. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q})
        \<subseteq> {p' \<in> space ?B. pstopped T \<theta> p' = p'}"
    proof
      fix p' :: "(real \<Rightarrow> 'a \<times> 'b)"
      assume h: "p' \<in> (\<Inter>q \<in> ?D. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q})"
      from h ne have sp: "p' \<in> space ?B" by blast
      then have mw: "p' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
        using spB by simp
      \<comment> \<open>\<open>OF\<close> against \<open>0 \<le> ?\<theta> ?\<omega>\<close> is not a higher-order PATTERN, so it has
          no unifiers; let the conclusion fix \<open>\<theta>\<close> and \<open>\<omega>\<close> first.\<close>
      have ms: "pstopped T \<theta> p' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      proof (rule pstopped_mspace)
        show "0 \<le> \<theta> p'" by (rule th0)
        show "\<theta> p' \<le> T" by (rule thT)
        show "p' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)" by (rule mw)
      qed
      have c1: "continuous_on {0..T} (pstopped T \<theta> p')"
        by (rule mspace_path_metricD[OF ms])
      have c2: "continuous_on {0..T} p'" by (rule mspace_path_metricD[OF mw])
      have cd: "continuous_on {0..T} (\<lambda>u. pstopped T \<theta> p' u - p' u)"
        using c1 c2 by (intro continuous_intros)
      have rq: "pstopped T \<theta> p' q - p' q = 0"
        if "q \<in> (\<rat> :: real set)" "q \<in> {0..T}" for q using h that by auto
      have "pstopped T \<theta> p' t = p' t" for t
      proof (cases "t \<in> {0..T}")
        case True
        have "pstopped T \<theta> p' t - p' t = 0"
          by (rule vanishes_of_rational[OF T0 cd rq True])
        then show ?thesis by simp
      next
        case False
        have "pstopped T \<theta> p' t = undefined" by (rule pstopped_outside[OF False])
        moreover have "p' t = undefined"
        proof -
          have "p' t = restrict p' {0..T} t"
            unfolding mspace_path_restrict_self[OF mw] ..
          also have "\<dots> = undefined"
            unfolding restrict_def by (rule if_not_P[OF False])
          finally show ?thesis .
        qed
        ultimately show ?thesis by simp
      qed
      then have "pstopped T \<theta> p' = p'" by (rule ext)
      with sp show "p' \<in> {p' \<in> space ?B. pstopped T \<theta> p' = p'}" by blast
    qed
  qed
  have sub: "(\<lambda>q. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q}) ` ?D \<subseteq> sets ?B"
    using single by blast
  have "(\<Inter>q \<in> ?D. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q}) \<in> sets ?B"
    by (rule sets.countable_INT'[OF cnt ne sub])
  then show ?thesis unfolding eq .
qed

text \<open>The four cheap \<open>Q\<close>-clauses for the stopped past law.  \<open>Qst\<close> is
  \<open>pstopped_idem\<close> transported through
  \<open>AE_distr_iff\<close>; \<open>Q0\<close> is the start clause of \<open>P\<close>, which the
  stopping does not touch because \<open>\<theta> \<ge> 0\<close>; \<open>Qcont\<close> is membership in the
  path space, the one clause that is pointwise on the space.\<close>

lemma path_stopping_time_cong:
  "path_stopping_time T \<theta> \<Longrightarrow> continuous_on {0..T} (\<lambda>t. fst (\<omega> t))
    \<Longrightarrow> continuous_on {0..T} (\<lambda>t. fst (\<omega>' t))
    \<Longrightarrow> (\<And>t. t \<in> {0..\<theta> \<omega>} \<Longrightarrow> \<omega> t = \<omega>' t)
    \<Longrightarrow> \<theta> \<omega>' = \<theta> \<omega>"
  unfolding path_stopping_time_def by blast

text \<open>Hence \<open>\<theta>\<close> reads only the stopped path --- the fact every later step
  needs, and the reason the kernel can be indexed by \<open>pstopped T \<theta> \<omega>\<close>
  alone.\<close>

lemma padd_stopping_time:
  fixes p' w :: "(real \<Rightarrow> 'a::topological_ab_group_add \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>"
    and idem: "pstopped T \<theta> p' = p'"
    and w0: "\<And>t. t \<in> {0..\<theta> p'} \<Longrightarrow> w t = 0"
    and cp: "continuous_on {0..T} (\<lambda>t. fst (p' t))"
    and cwv: "continuous_on {0..T} (\<lambda>t. fst (w t))"
  shows "\<theta> (padd T p' w) = \<theta> p'"
proof (rule path_stopping_time_cong[OF st cp padd_fst_continuous[OF cp cwv]])
  fix t assume t: "t \<in> {0..\<theta> p'}"
  then have tT: "t \<in> {0..T}"
    using path_stopping_time_nonneg[OF st, of p'] path_stopping_time_le[OF st, of p']
    by auto
  show "p' t = padd T p' w t"
    unfolding padd_apply[OF tT] using w0[OF t] by simp
qed

lemma pstopped_padd:
  fixes p' w :: "(real \<Rightarrow> 'a::topological_ab_group_add \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>"
    and idem: "pstopped T \<theta> p' = p'"
    and w0: "\<And>t. t \<in> {0..\<theta> p'} \<Longrightarrow> w t = 0"
    and cp: "continuous_on {0..T} (\<lambda>t. fst (p' t))"
    and cwv: "continuous_on {0..T} (\<lambda>t. fst (w t))"
  shows "pstopped T \<theta> (padd T p' w) = p'"
proof (rule ext)
  fix t :: real
  have th: "\<theta> (padd T p' w) = \<theta> p'"
    by (rule padd_stopping_time[OF st idem w0 cp cwv])
  have th0: "0 \<le> \<theta> p'" by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" by (rule path_stopping_time_le[OF st])
  show "pstopped T \<theta> (padd T p' w) t = p' t"
  proof (cases "t \<in> {0..T}")
    case True
    have m: "min t (\<theta> p') \<in> {0..T}" using True th0 thT by auto
    have m0: "min t (\<theta> p') \<in> {0..\<theta> p'}" using True th0 by auto
    have "pstopped T \<theta> (padd T p' w) t = padd T p' w (min t (\<theta> p'))"
      unfolding pstopped_apply[OF True] th ..
    also have "\<dots> = p' (min t (\<theta> p')) + w (min t (\<theta> p'))"
      by (rule padd_apply[OF m])
    also have "\<dots> = p' (min t (\<theta> p'))" using w0[OF m0] by simp
    also have "\<dots> = pstopped T \<theta> p' t"
      unfolding pstopped_apply[OF True] ..
    finally show ?thesis unfolding idem .
  next
    case False
    have "pstopped T \<theta> (padd T p' w) t = undefined"
      by (rule pstopped_outside[OF False])
    moreover have "p' t = undefined"
      using idem pstopped_outside[OF False] by metis
    ultimately show ?thesis by simp
  qed
qed

lemma pafter_padd:
  fixes p' w :: "(real \<Rightarrow> 'a::topological_ab_group_add \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>"
    and idem: "pstopped T \<theta> p' = p'"
    and w0: "\<And>t. t \<in> {0..\<theta> p'} \<Longrightarrow> w t = 0"
    and wfr: "\<And>t. t \<in> {0..T} \<Longrightarrow> w t = w (max t (\<theta> p'))"
    and wout: "\<And>t. t \<notin> {0..T} \<Longrightarrow> w t = undefined"
    and cp: "continuous_on {0..T} (\<lambda>t. fst (p' t))"
    and cwv: "continuous_on {0..T} (\<lambda>t. fst (w t))"
  shows "pafter T \<theta> (padd T p' w) = w"
proof (rule ext)
  fix t :: real
  have th: "\<theta> (padd T p' w) = \<theta> p'"
    by (rule padd_stopping_time[OF st idem w0 cp cwv])
  have th0: "0 \<le> \<theta> p'" by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" by (rule path_stopping_time_le[OF st])
  show "pafter T \<theta> (padd T p' w) t = w t"
  proof (cases "t \<in> {0..T}")
    case True
    have m1: "max t (\<theta> p') \<in> {0..T}" using True th0 thT by auto
    have m2: "\<theta> p' \<in> {0..T}" using th0 thT by simp
    have m2': "\<theta> p' \<in> {0..\<theta> p'}" using th0 by simp
    have "pafter T \<theta> (padd T p' w) t
        = padd T p' w (max t (\<theta> p')) - padd T p' w (\<theta> p')"
      unfolding pafter_apply[OF True] th ..
    also have "\<dots> = (p' (max t (\<theta> p')) + w (max t (\<theta> p')))
        - (p' (\<theta> p') + w (\<theta> p'))"
      by (simp only: padd_apply[OF m1] padd_apply[OF m2])
    also have "\<dots> = p' (max t (\<theta> p')) - p' (\<theta> p') + w (max t (\<theta> p'))"
      using w0[OF m2'] by simp
    also have "p' (max t (\<theta> p')) = p' (\<theta> p')"
    proof -
      have "p' (max t (\<theta> p')) = pstopped T \<theta> p' (max t (\<theta> p'))"
        unfolding idem ..
      also have "\<dots> = p' (min (max t (\<theta> p')) (\<theta> p'))"
        by (rule pstopped_apply[OF m1])
      also have "min (max t (\<theta> p')) (\<theta> p') = \<theta> p'" by simp
      finally show ?thesis .
    qed
    finally show ?thesis using wfr[OF True] by simp
  next
    case False
    have "pafter T \<theta> (padd T p' w) t = undefined"
      by (rule pafter_outside[OF False])
    then show ?thesis using wout[OF False] by simp
  qed
qed

subsection \<open>The glued law, and the clauses that come for free\<close>

text \<open>The law of the reassembled path: run the past under \<open>Q\<close>, draw a
  continuation from \<open>\<kappa>\<close>, and add.  This is the stopping-time analogue of
  \<open>kglue_law'\<close>, and the only structural difference is that
  \<^const>\<open>padd\<close> replaces \<^const>\<open>pglue\<close>.\<close>

lemma path_stopping_time_max:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add) \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and u: "0 \<le> u" and uT: "u \<le> T"
  shows "path_stopping_time T (\<lambda>\<omega>. max u (\<theta> \<omega>))"
proof -
  have c1: "0 \<le> max u (\<theta> \<omega>) \<and> max u (\<theta> \<omega>) \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    using u uT path_stopping_time_nonneg[OF st, of \<omega>]
      path_stopping_time_le[OF st, of \<omega>] by simp
  have c2: "max u (\<theta> \<omega>') = max u (\<theta> \<omega>)"
    if cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
      and cw': "continuous_on {0..T} (\<lambda>v. fst (\<omega>' v))"
      and ag: "\<forall>s \<in> {0..max u (\<theta> \<omega>)}. \<omega> s = \<omega>' s" for \<omega> \<omega>' :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof -
    have "\<theta> \<omega>' = \<theta> \<omega>"
    proof (rule path_stopping_time_cong[OF st cw cw'])
      fix s assume "s \<in> {0..\<theta> \<omega>}"
      then have "s \<in> {0..max u (\<theta> \<omega>)}" by auto
      then show "\<omega> s = \<omega>' s" using ag by blast
    qed
    then show ?thesis by simp
  qed
  show ?thesis unfolding path_stopping_time_def using c1 c2 by blast
qed

text \<open>The event lemma with the horizon restriction removed: past \<open>T\<close> there is
  nothing left to decide.\<close>

lemma path_stopping_time_shift:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add) \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and i: "0 \<le> i"
  shows "path_stopping_time T (\<lambda>\<omega>. min (\<theta> \<omega> + i) T)"
proof -
  have c1: "0 \<le> min (\<theta> \<omega> + i) T \<and> min (\<theta> \<omega> + i) T \<le> T"
    for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof -
    have "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
    moreover have "\<theta> \<omega> \<le> T" by (rule path_stopping_time_le[OF st])
    ultimately show ?thesis using i by simp
  qed
  have c2: "min (\<theta> \<omega>' + i) T = min (\<theta> \<omega> + i) T"
    if cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
      and cw': "continuous_on {0..T} (\<lambda>u. fst (\<omega>' u))"
      and ag: "\<forall>s \<in> {0..min (\<theta> \<omega> + i) T}. \<omega> s = \<omega>' s"
    for \<omega> \<omega>' :: "(real \<Rightarrow> 'a \<times> 'b)"
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
  \<open>pre_sigma_of_mono\<close> carry the conditioning set from the
  earlier sampling time to the later one; pure arithmetic, discharged where
  it is used.\<close>

text \<open>The stopping-time event is not merely Borel but lies in the natural
  filtration at \<open>t\<close>, which is what \<open>set_martingale_sampling\<close>
  consumes.  @{thm [source] path_eval_measurable_natural_filtration} ties
  the filtration index to the horizon; decoupling them is the only change
  its proof needs.\<close>

lemma path_stopping_time_min:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add) \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and i: "0 \<le> i" and iT: "i \<le> T"
  shows "path_stopping_time T (\<lambda>\<omega>. min i (\<theta> \<omega>))"
proof -
  have c1: "0 \<le> min i (\<theta> \<omega>) \<and> min i (\<theta> \<omega>) \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    using i iT path_stopping_time_nonneg[OF st, of \<omega>]
      path_stopping_time_le[OF st, of \<omega>] by simp
  have c2: "min i (\<theta> \<omega>') = min i (\<theta> \<omega>)"
    if cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
      and cw': "continuous_on {0..T} (\<lambda>v. fst (\<omega>' v))"
      and ag: "\<forall>s \<in> {0..min i (\<theta> \<omega>)}. \<omega> s = \<omega>' s" for \<omega> \<omega>' :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof (cases "\<theta> \<omega> \<le> i")
    case True
    then have "min i (\<theta> \<omega>) = \<theta> \<omega>" by simp
    then have "\<forall>s \<in> {0..\<theta> \<omega>}. \<omega> s = \<omega>' s" using ag by simp
    then have "\<theta> \<omega>' = \<theta> \<omega>"
      by (intro path_stopping_time_cong[OF st cw cw']) blast
    then show ?thesis by simp
  next
    case False
    then have mi: "min i (\<theta> \<omega>) = i" by simp
    have "\<not> \<theta> \<omega>' < i"
    proof
      assume lt: "\<theta> \<omega>' < i"
      have "\<theta> \<omega> = \<theta> \<omega>'"
      proof (rule path_stopping_time_cong[OF st cw' cw])
        fix s assume "s \<in> {0..\<theta> \<omega>'}"
        then have "s \<in> {0..min i (\<theta> \<omega>)}" using lt mi by auto
        then show "\<omega>' s = \<omega> s" using ag by auto
      qed
      then show False using lt False by simp
    qed
    then show ?thesis using mi by simp
  qed
  show ?thesis unfolding path_stopping_time_def using c1 c2 by blast
qed

text \<open>The stopped past, read at \<open>u \<and> T\<close>, is the past read at \<open>u \<and> \<theta>\<close>: this is
  what turns the glue's own clock into the stopping-time family that
  \<open>stopped_increment_of_horizon_gen\<close> samples at.\<close>

lemma pstopped_fst_continuous:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and th0: "0 \<le> \<theta>' \<omega>" and thT: "\<theta>' \<omega> \<le> T"
  shows "continuous_on {0..T} (\<lambda>s. fst (pstopped T \<theta>' \<omega> s))"
proof -
  have e: "fst (pstopped T \<theta>' \<omega> s) = fst (\<omega> (min s (\<theta>' \<omega>)))"
    if "s \<in> {0..T}" for s by (simp add: pstopped_apply[OF that])
  have c1: "continuous_on {0..T} (\<lambda>s :: real. min s (\<theta>' \<omega>))"
    by (intro continuous_intros)
  have "continuous_on {0..T} (\<lambda>s. fst (\<omega> (min s (\<theta>' \<omega>))))"
    by (rule continuous_on_compose2[OF cw c1]) (use th0 thT in auto)
  then show ?thesis by (rule continuous_on_eq) (simp add: e)
qed

lemma path_stopping_time_cut_eq:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>" and tT: "t \<le> T" and le: "\<theta> \<omega> \<le> t"
    and cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
  shows "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
proof (rule path_stopping_time_cong[OF st cw
      pstopped_fst_continuous[OF cw, of "\<lambda>_. t"]])
  show "0 \<le> t" using le path_stopping_time_nonneg[OF st, of \<omega>] by simp
  show "t \<le> T" by (rule tT)
  fix s assume s: "s \<in> {0..\<theta> \<omega>}"
  then have sT: "s \<in> {0..T}" using le tT by auto
  have "min s t = s" using s le by simp
  then show "\<omega> s = pstopped T (\<lambda>_. t) \<omega> s"
    by (simp add: pstopped_apply[OF sT])
qed

lemma pstopped_cut_compose:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>" and tT: "t \<le> T" and le: "\<theta> \<omega> \<le> t"
    and cw: "continuous_on {0..T} (\<lambda>u. fst (\<omega> u))"
  shows "pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>) = pstopped T \<theta> \<omega>"
proof (rule ext)
  fix s :: real
  show "pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s = pstopped T \<theta> \<omega> s"
  proof (cases "s \<in> {0..T}")
    case True
    have th: "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
      by (rule path_stopping_time_cut_eq[OF st tT le cw])
    have th0: "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
    have m: "min s (\<theta> \<omega>) \<in> {0..T}" using True th0 by auto
    have "pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s
        = pstopped T (\<lambda>_. t) \<omega> (min s (\<theta> \<omega>))"
      unfolding pstopped_apply[OF True] th ..
    also have "\<dots> = \<omega> (min (min s (\<theta> \<omega>)) t)" by (rule pstopped_apply[OF m])
    also have "min (min s (\<theta> \<omega>)) t = min s (\<theta> \<omega>)" using le by simp
    finally show ?thesis by (simp add: pstopped_apply[OF True])
  next
    case False
    then show ?thesis by (simp add: pstopped_outside)
  qed
qed

text \<open>The second factor only agrees up to \<open>u\<close> --- exactly as far as an
  \<open>\<F>\<^sub>u\<close>-set can look, so composing with \<^const>\<open>pcut\<close> loses nothing.\<close>

lemma pcut_pafter_cut_compose:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>" and tT: "t \<le> T"
    and u: "0 \<le> u" and ut: "u \<le> t" and le: "\<theta> \<omega> \<le> t"
    and cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
  shows "pcut u (pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>)) = pcut u (pafter T \<theta> \<omega>)"
proof (rule ext)
  fix s :: real
  show "pcut u (pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>)) s
      = pcut u (pafter T \<theta> \<omega>) s"
  proof (cases "s \<in> {0..u}")
    case True
    have th0: "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
    have sT: "s \<in> {0..T}" using True u ut tT by auto
    have th: "\<theta> (pstopped T (\<lambda>_. t) \<omega>) = \<theta> \<omega>"
      by (rule path_stopping_time_cut_eq[OF st tT le cw])
    have m1: "max s (\<theta> \<omega>) \<in> {0..T}"
      using sT th0 path_stopping_time_le[OF st, of \<omega>] by auto
    have m2: "\<theta> \<omega> \<in> {0..T}"
      using th0 path_stopping_time_le[OF st, of \<omega>] by simp
    have mx: "max s (\<theta> \<omega>) \<le> t" using True ut le by simp
    have "pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s
        = pstopped T (\<lambda>_. t) \<omega> (max s (\<theta> \<omega>))
          - pstopped T (\<lambda>_. t) \<omega> (\<theta> \<omega>)"
      unfolding pafter_apply[OF sT] th ..
    also have "\<dots> = \<omega> (min (max s (\<theta> \<omega>)) t) - \<omega> (min (\<theta> \<omega>) t)"
      by (simp only: pstopped_apply[OF m1] pstopped_apply[OF m2])
    also have "\<dots> = \<omega> (max s (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)" using mx le by simp
    finally have "pafter T \<theta> (pstopped T (\<lambda>_. t) \<omega>) s = pafter T \<theta> \<omega> s"
      unfolding pafter_apply[OF sT] .
    then show ?thesis by (simp add: pcut_apply[OF True])
  next
    case False
    have out: "pcut u w s = undefined" for w :: "(real \<Rightarrow> 'a \<times> 'b)"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    show ?thesis unfolding out ..
  qed
qed

text \<open>\<open>u \<or> \<theta>\<close> is a stopping time for the same reason \<open>(\<theta>+i) \<and> T\<close> is
  (@{thm [source] path_stopping_time_shift}): it never looks back less far
  than \<open>\<theta>\<close> does.\<close>

lemma path_stopping_time_cut:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
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

lemma path_stopping_time_event_filtration:
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure)"
    and t: "0 \<le> t" and tT: "t \<le> T"
  shows "{\<omega> \<in> space (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure). \<theta> \<omega> \<le> t}
      \<in> sets (natural_filtration (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure) 0 (\<lambda>v \<omega>. \<omega> v) t)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t"
  have spF: "space ?F = space ?B" by simp
  have cm: "pstopped T (\<lambda>_. t) \<in> ?F \<rightarrow>\<^sub>M ?B"
    by (rule pstopped_const_measurable_filtration[OF T0 t tT])
  have thc: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<theta> (pstopped T (\<lambda>_. t) \<omega>)) \<in> borel_measurable ?F"
    using cm by (rule measurable_compose) (rule thM)
  have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}
      = {\<omega> \<in> space ?F. \<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t}"
    unfolding spF
  proof (rule Collect_cong, rule conj_cong[OF refl])
    fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" assume w: "\<omega> \<in> space ?B"
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
  \<open>set_martingale_sampling\<close> at each of them against the common
  horizon.  The conditioning set is legal for the later one because
  \<open>pre_sigma_of_mono\<close> carries it up.  This is the form clause
  (iv) uses, at \<open>\<sigma> = (\<theta>+i) \<and> T\<close> and \<open>\<rho> = (\<theta>+j) \<and> T\<close>.\<close>

lemma path_stopping_time_shift_event:
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure)"
    and i: "0 \<le> i" and t: "0 \<le> t"
  shows "{\<omega> \<in> space (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure). min (\<theta> \<omega> + i) T \<le> t}
      \<in> sets (natural_filtration (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure) 0 (\<lambda>v \<omega>. \<omega> v) t)"
proof (cases "t \<le> T")
  case True
  have st': "path_stopping_time T (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). min (\<theta> \<omega> + i) T)"
    by (rule path_stopping_time_shift[OF st i])
  have m': "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). min (\<theta> \<omega> + i) T) \<in> borel_measurable
      (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    using thM by measurable
  show ?thesis
    by (rule path_stopping_time_event_filtration[OF T0 st' m' t True])
next
  case False
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t"
  have "{\<omega> \<in> space ?B. min (\<theta> \<omega> + i) T \<le> t} = space ?B"
    using False by auto
  moreover have "space ?B \<in> sets ?F"
  proof -
    have "space ?F = space ?B" by simp
    then show ?thesis using sets.top[of ?F] by simp
  qed
  ultimately show ?thesis by simp
qed

section \<open>Clause (iv) at a stopping time: the increment identity\<close>

text \<open>The assembly.  Every hypothesis of
  \<open>set_martingale_sampling_two\<close> now has a supplier: the
  martingale from the class via @{thm [source] martingale_vec_component},
  the filtration facts from @{thm [source] sets_natural_filtration_mono} and
  the martingale locale, the stopping-time events from
  @{thm [source] path_stopping_time_shift_event}, the convergence from
  @{thm [source] exit_component_dyceil_tendsto}, and the domination from
  @{theory Continuous_Time_Martingales.Doob_Inequality}'s \<open>Dsup\<close> through
  \<open>exit_class_horizon_component\<close>.\<close>

text \<open>The same identity for an arbitrary real process that is a
  \<open>horizon_sq_int_martingale\<close> with continuous paths.  Both of the class's
  martingale clauses are of that shape --- the \<open>X\<close> one componentwise, the
  compensated one entrywise --- so this is the form clause (iv) uses twice.
  \<open>martingale_mat_component\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

text \<open>Square-integrability of the compensated entry, from its
  nonnegative-integral bound.  This is the second half of what
  \<open>horizon_sq_int_martingale\<close> asks for.\<close>

lemma path_stopping_time_event_filtration_all:
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure)"
    and t: "0 \<le> t"
  shows "{\<omega> \<in> space (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure). \<sigma> \<omega> \<le> t}
      \<in> sets (natural_filtration (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure) 0 (\<lambda>v \<omega>. \<omega> v) t)"
proof (cases "t \<le> T")
  case True
  show ?thesis by (rule path_stopping_time_event_filtration[OF T0 st sM t True])
next
  case False
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t"
  have lt: "\<sigma> \<omega> \<le> t" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    using path_stopping_time_le[OF st, of \<omega>] False by simp
  have "{\<omega> \<in> space ?B. \<sigma> \<omega> \<le> t} = space ?B" using lt by blast
  moreover have "space ?B \<in> sets ?F"
  proof -
    have "space ?F = space ?B" by simp
    then show ?thesis using sets.top[of ?F] by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open>A packaging lemma: for a stopping time bounded by \<open>T\<close> it is enough to
  check the \<open>\<F>\<^sub>\<sigma>\<close> condition at times below the horizon.\<close>

lemma path_stopping_time_stopped:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "\<theta> (pstopped T \<theta> \<omega>) = \<theta> \<omega>"
proof (rule path_stopping_time_cong[OF st cw
      pstopped_fst_continuous[OF cw path_stopping_time_nonneg[OF st]
        path_stopping_time_le[OF st]]])
  fix t assume t: "t \<in> {0..\<theta> \<omega>}"
  then have tT: "t \<in> {0..T}" using path_stopping_time_le[OF st, of \<omega>] by auto
  have "min t (\<theta> \<omega>) = t" using t by simp
  then show "\<omega> t = pstopped T \<theta> \<omega> t" by (simp add: pstopped_apply[OF tT])
qed

lemma pstopped_idem:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add)"
  assumes st: "path_stopping_time T \<theta>"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "pstopped T \<theta> (pstopped T \<theta> \<omega>) = pstopped T \<theta> \<omega>"
proof (rule ext)
  fix t :: real
  show "pstopped T \<theta> (pstopped T \<theta> \<omega>) t = pstopped T \<theta> \<omega> t"
  proof (cases "t \<in> {0..T}")
    case True
    have th: "\<theta> (pstopped T \<theta> \<omega>) = \<theta> \<omega>"
      by (rule path_stopping_time_stopped[OF st cw])
    have m: "min t (\<theta> \<omega>) \<in> {0..T}"
      using True path_stopping_time_nonneg[OF st, of \<omega>] by auto
    have "pstopped T \<theta> (pstopped T \<theta> \<omega>) t
        = pstopped T \<theta> \<omega> (min t (\<theta> \<omega>))"
      unfolding pstopped_apply[OF True] th ..
    also have "\<dots> = \<omega> (min (min t (\<theta> \<omega>)) (\<theta> \<omega>))" by (rule pstopped_apply[OF m])
    also have "min (min t (\<theta> \<omega>)) (\<theta> \<omega>) = min t (\<theta> \<omega>)" by simp
    finally show ?thesis by (simp add: pstopped_apply[OF True])
  next
    case False
    then show ?thesis by (simp add: pstopped_outside)
  qed
qed

text \<open>And the future factor of a stopped path is trivial: stopping twice
  leaves nothing after \<open>\<theta>\<close>.  This is the pathwise seed of clause (ii) for
  the kernel --- the continuation starts at \<open>0\<close>.\<close>

text \<open>The re-basing map at a fixed time is an ordinary path-space map, and
  that is all clause (i) of the kernel statement needs, since \<open>\<theta> \<omega>\<close> is a
  fixed number inside an almost-sure statement.\<close>

lemma pstopped_eval_min_T:
  fixes \<omega> :: "real \<Rightarrow> 'b"
  assumes T0: "0 \<le> T" and u: "0 \<le> u"
  shows "pstopped T \<theta> \<omega> (min u T) = \<omega> (min (min u (\<theta> \<omega>)) T)"
proof -
  have m: "min u T \<in> {0..T}" using T0 u by simp
  have "pstopped T \<theta> \<omega> (min u T) = \<omega> (min (min u T) (\<theta> \<omega>))"
    by (rule pstopped_apply[OF m])
  moreover have "min (min u T) (\<theta> \<omega>) = min (min u (\<theta> \<omega>)) T" by simp
  ultimately show ?thesis by simp
qed

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

lemma pstopped_vimage_pre_sigma:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and A: "A \<in> sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "pstopped T \<theta> -` A \<inter> space P
      \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<theta>"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v)"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_le[OF st])
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have mst: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have S: "pstopped T \<theta> -` A \<inter> space P \<in> sets P"
    by (rule measurable_sets[OF mst A])
  show ?thesis
  proof (rule pre_sigma_ofI_le[OF T0 mono thT S])
    fix t :: real assume t: "0 \<le> t" and tT: "t \<le> T"
    let ?g = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> (pstopped T (\<lambda>_. t) \<omega>)"
    have mg: "?g \<in> ?F t \<rightarrow>\<^sub>M ?B"
      unfolding FB
      by (rule measurable_compose
          [OF pstopped_const_measurable_filtration[OF T0 t tT]
             pstopped_measurable[OF T0 thM th0 thT]])
    have gm: "?g -` A \<inter> space P \<in> sets (?F t)"
      using measurable_sets[OF mg A] by simp
    have ev: "{\<omega> \<in> space P. \<theta> \<omega> \<le> t} \<in> sets (?F t)"
      unfolding FB spP
      by (rule path_stopping_time_event_filtration[OF T0 st thM t tT])
    have eqset: "(pstopped T \<theta> -` A \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}
        = (?g -` A \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}"
    proof -
      have "pstopped T \<theta> \<omega> = ?g \<omega>"
        if "\<theta> \<omega> \<le> t" and "\<omega> \<in> space P" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
      proof -
        have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
          by (rule path_sets_fst_continuous[OF setsP that(2)])
        show ?thesis using pstopped_cut_compose[OF st tT that(1) cw] by simp
      qed
      then show ?thesis by auto
    qed
    show "(pstopped T \<theta> -` A \<inter> space P) \<inter> {\<omega> \<in> space P. \<theta> \<omega> \<le> t}
        \<in> sets (?F t)"
      unfolding eqset using gm ev by (rule sets.Int)
  qed
qed

text \<open>The second factor.  An \<open>\<F>\<^sub>u\<close>-set of the path space is a
  \<open>pcut u\<close>-preimage --- \<open>sets_natural_filtration_eq_pcut_vimage\<close>
  --- so only the delayed future on \<open>[0,u]\<close> matters, and that is decided by
  the path stopped at \<open>t\<close> as soon as \<open>u \<or> \<theta> \<le> t\<close>.\<close>

lemma pre_sigma_of_sets: "A \<in> pre_sigma_of M F \<sigma> \<Longrightarrow> A \<in> sets M"
  unfolding pre_sigma_of_def by blast

lemma pre_sigma_of_cut:
  "A \<in> pre_sigma_of M F \<sigma> \<Longrightarrow> 0 \<le> t
    \<Longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  unfolding pre_sigma_of_def by blast

text \<open>It is a \<open>\<sigma>\<close>-algebra: the complement step is where the stopping-time
  property of \<open>\<sigma>\<close> is spent, since \<open>{\<sigma> \<le> t}\<close> itself has to be in \<open>F t\<close> for
  the relative complement to stay there.\<close>

lemma pre_sigma_of_Int:
  assumes A: "A \<in> pre_sigma_of M F \<sigma>" and B: "B \<in> pre_sigma_of M F \<sigma>"
  shows "A \<inter> B \<in> pre_sigma_of M F \<sigma>"
proof (rule pre_sigma_ofI)
  show "A \<inter> B \<in> sets M"
    using pre_sigma_of_sets[OF A] pre_sigma_of_sets[OF B] by (rule sets.Int)
  fix t :: real assume t: "0 \<le> t"
  have "(A \<inter> B) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}
      = (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) \<inter> (B \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t})" by auto
  moreover have "\<dots> \<in> sets (F t)"
    using pre_sigma_of_cut[OF A t] pre_sigma_of_cut[OF B t] by (rule sets.Int)
  ultimately show "(A \<inter> B) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)" by simp
qed

text \<open>The first factor.  Below \<open>t\<close> the stopped path is read off the path
  stopped at \<open>t\<close> --- \<open>pstopped_cut_compose\<close> --- and that composite is
  \<open>\<F>\<^sub>t\<close>-measurable by \<open>pstopped_const_measurable_filtration\<close>.\<close>

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

text \<open>And a deterministic time gives back the filtration itself, which is how
  the new layer connects to everything already proved.\<close>

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

text \<open>And the bottom band, \<open>\<sigma> \<le> t\<^sub>1\<close>, is @{thm [source] pre_sigma_of_cut}
  itself, so a simple \<open>\<sigma>\<close> gives a finite partition of \<open>A\<close> into pieces each
  living in the filtration at its own value.  Stated as the partition it
  will be used as.\<close>

text \<open>The value-set form of the slice, which is what the sampling theorem
  wants: the pieces indexed by the values of \<open>\<sigma>\<close> are genuinely disjoint,
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


(*<*)

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

lemma integrable_at_bounded_stopping_time:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<sigma> :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F 0 Y"
    and mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and sub: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
    and sig0: "\<And>\<omega>. 0 \<le> \<sigma> \<omega>" and sigU: "\<And>\<omega>. \<sigma> \<omega> \<le> U" and U0: "0 \<le> U"
    and cont: "\<And>\<omega>. \<omega> \<in> space M
      \<Longrightarrow> (\<lambda>n. Y (dyceil n U (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    and Dbd: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> U \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> D \<omega>"
    and Dint: "integrable M D"
  shows "integrable M (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
proof -
  interpret Mg: martingale M F 0 Y by (rule mg)
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

theorem stopped_increment_of_horizon_gen:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
    and Y :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real" and \<sigma> \<rho> :: "(real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real"
  assumes T0: "0 < T"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and H: "horizon_sq_int_martingale P
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) Y T"
    and Ycont: "\<And>\<omega>. \<omega> \<in> space P \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    and sts: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and str: "path_stopping_time T \<rho>"
    and rM: "\<rho> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and le: "\<And>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<sigma> \<omega> \<le> \<rho> \<omega>"
    and A: "A \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<sigma>"
  shows "set_lebesgue_integral P A (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)
       = set_lebesgue_integral P A (\<lambda>\<omega>. Y (\<rho> \<omega>) \<omega>)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v)"
  have T0': "0 \<le> T" using T0 by simp
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  interpret H: horizon_sq_int_martingale P ?F Y T by (rule H)

  have mg: "martingale P ?F 0 Y" by (rule H.martingale_axioms)
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have sub: "subalgebra P (?F t)" if "0 \<le> t" for t
    by (rule H.subalgebras[OF that])
  have sig0: "0 \<le> \<sigma> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_nonneg[OF sts])
  have sigU: "\<sigma> \<omega> \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_le[OF sts])
  have rho0: "0 \<le> \<rho> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_nonneg[OF str])
  have rhoU: "\<rho> \<omega> \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_le[OF str])
  have stops: "{\<omega> \<in> space P. \<sigma> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' sts sM t])
  have stopr: "{\<omega> \<in> space P. \<rho> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' str rM t])

  have conv: "(\<lambda>n. Y (dyceil n T s) \<omega>) \<longlonglongrightarrow> Y s \<omega>"
    if w: "\<omega> \<in> space P" and s0: "0 \<le> s" and sT: "s \<le> T" for \<omega> s
  proof (rule continuous_on_tendsto_compose
      [OF Ycont[OF w] dyceil_tendsto[OF s0 sT]])
    show "\<forall>\<^sub>F n in sequentially. dyceil n T s \<in> {0..T}"
      using dyceil_nonneg[OF s0 sT] dyceil_le_U[of _ T s] by simp
    show "s \<in> {0..T}" using s0 sT by simp
  qed
  have conts: "(\<lambda>n. Y (dyceil n T (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    if w: "\<omega> \<in> space P" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule conv[OF w sig0 sigU])
  have contr: "(\<lambda>n. Y (dyceil n T (\<rho> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<rho> \<omega>) \<omega>"
    if w: "\<omega> \<in> space P" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule conv[OF w rho0 rhoU])

  have pathcont: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    by (rule AE_I2) (rule Ycont)
  have Dbd: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates[OF pathcont])
  have Dint: "integrable P H.Dsup" by (rule H.Dsup_integrable)

  show ?thesis
    by (rule set_martingale_sampling_two
        [OF mg mono sub A stops stopr sig0 sigU rho0 rhoU T0' le
          conts contr Dbd Dint])
qed

lemma integrable_at_path_stopping_time:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
    and Y :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real" and \<sigma> :: "(real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real"
  assumes T0: "0 < T"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and H: "horizon_sq_int_martingale P
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) Y T"
    and Ycont: "\<And>\<omega>. \<omega> \<in> space P \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    and sts: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "integrable P (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v)"
  have T0': "0 \<le> T" using T0 by simp
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  interpret H: horizon_sq_int_martingale P ?F Y T by (rule H)

  have mg: "martingale P ?F 0 Y" by (rule H.martingale_axioms)
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "0 \<le> s" and "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that(2)])
  have sub: "subalgebra P (?F t)" if "0 \<le> t" for t
    by (rule H.subalgebras[OF that])
  have sig0: "0 \<le> \<sigma> \<omega>" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_nonneg[OF sts])
  have sigU: "\<sigma> \<omega> \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    by (rule path_stopping_time_le[OF sts])
  have stops: "{\<omega> \<in> space P. \<sigma> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' sts sM t])
  have conts: "(\<lambda>n. Y (dyceil n T (\<sigma> \<omega>)) \<omega>) \<longlonglongrightarrow> Y (\<sigma> \<omega>) \<omega>"
    if w: "\<omega> \<in> space P" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof (rule continuous_on_tendsto_compose
      [OF Ycont[OF w] dyceil_tendsto[OF sig0 sigU]])
    show "\<forall>\<^sub>F n in sequentially. dyceil n T (\<sigma> \<omega>) \<in> {0..T}"
      using dyceil_nonneg[OF sig0 sigU] dyceil_le_U[of _ T "\<sigma> \<omega>"] by simp
    show "\<sigma> \<omega> \<in> {0..T}" using sig0 sigU by simp
  qed
  have pathcont: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    by (rule AE_I2) (rule Ycont)
  have Dbd: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates[OF pathcont])
  have Dint: "integrable P H.Dsup" by (rule H.Dsup_integrable)

  show ?thesis
    by (rule integrable_at_bounded_stopping_time
        [OF mg mono sub stops sig0 sigU T0' conts Dbd Dint])
qed

section \<open>The increment identity moves to the kernel\<close>

text \<open>The stopping-time twin of \<open>pfut_rcd_X_increment_zero\<close>,
  stated once for an arbitrary real integrand \<open>h\<close> on the future factor
  together with the identity \<open>hP\<close> pulling it back to an increment of a
  horizon martingale \<open>Y\<close> of \<open>P\<close>.  Every clause of the class surviving the
  additive split has this shape, so the disintegration is done once here
  and instantiated afterwards.

  The chain follows the deterministic one --- \<open>AE_kernel_integral_zero\<close>
  to rectangles, \<open>integral_ksemi_rect_of_set_integral\<close> to a set
  integral over \<open>P\<close> --- with the conditioning set landing in
  \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<or>\<^sub> \<^sub>\<theta>\<^sub>)\<close> via \<open>rect_vimage_pre_sigma_stopping\<close> instead of a
  deterministic \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>, closed by
  @{thm [source] stopped_increment_of_horizon_gen} instead of
  \<open>martingale.set_integral_eq\<close>.\<close>

text \<open>Clause (iv) for the \<open>X\<close> martingale: the additive split carries it
  across unchanged, since \<^term>\<open>pafter T \<theta> \<omega>\<close> is a difference of values of
  \<open>\<omega>\<close> and the constant \<^term>\<open>\<omega> (\<theta> \<omega>)\<close> cancels between the two times.\<close>

section \<open>The cross term: an increment against a known factor\<close>

text \<open>The compensated clause does not ride along on the additive split,
  because \<^const>\<open>outerp\<close> is quadratic.  Writing \<open>b = fst (\<omega> (\<theta> \<omega>))\<close>,

  \<open>outerp (X\<^sub>u - b) - (\<langle>X\<rangle>\<^sub>u - \<langle>X\<rangle>\<^sub>\<theta>)
     = (outerp X\<^sub>u - \<langle>X\<rangle>\<^sub>u) - X\<^sub>u bᵀ - b X\<^sub>uᵀ + outerp b + \<langle>X\<rangle>\<^sub>\<theta>\<close>

  and between two times the last two summands cancel, leaving a compensated
  increment plus two cross terms \<open>(\<Delta>X) bᵀ\<close> and \<open>b (\<Delta>X)ᵀ\<close>.  The factor \<open>b\<close> is
  \<open>\<F>\<^sub>\<theta>\<close>-measurable but not constant, so those terms need
  \<open>E[\<Delta>Y \<sqdot> Z] = 0\<close> for a square-integrable \<open>\<F>\<^sub>\<sigma>\<close>-measurable \<open>Z\<close>.

  With \<open>\<F>\<^sub>\<sigma>\<close> a genuine \<open>sigma\<close> algebra the argument needs no
  approximation by simple functions: the conditional expectation of the
  increment vanishes (@{thm [source] AE_zero_of_set_integral_zero} against
  @{thm [source] stopped_increment_of_horizon_gen}), and \<open>Z\<close> pulls out of it
  (\<open>cond_exp_measurable_mult\<close>), using square-integrability of the
  increment from Doob's \<open>Dsup_sq_integrable\<close>.\<close>

lemma set_integral_increment_times_known:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
    and Y :: "real \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real" and Z :: "(real \<Rightarrow> 'a \<times> 'b) \<Rightarrow> real"
  assumes T0: "0 < T" and PS: "prob_space P"
    and setsP: "sets P = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and H: "horizon_sq_int_martingale P
        (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) Y T"
    and Ycont: "\<And>\<omega>. \<omega> \<in> space P \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    and sts: "path_stopping_time T \<sigma>"
    and sM: "\<sigma> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and str: "path_stopping_time T \<rho>"
    and rM: "\<rho> \<in> borel_measurable (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and le: "\<And>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<sigma> \<omega> \<le> \<rho> \<omega>"
    and Zpre: "\<And>B. B \<in> sets borel \<Longrightarrow> Z -` B \<inter> space P
        \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<sigma>"
    and Zsq: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (Z \<omega>)\<^sup>2)"
    and A: "A \<in> pre_sigma_of P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) \<sigma>"
  shows "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (Y (\<rho> \<omega>) \<omega> - Y (\<sigma> \<omega>) \<omega>) * Z \<omega>)"
    and "set_lebesgue_integral P A
        (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (Y (\<rho> \<omega>) \<omega> - Y (\<sigma> \<omega>) \<omega>) * Z \<omega>) = 0"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v)"
  let ?D = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Y (\<rho> \<omega>) \<omega> - Y (\<sigma> \<omega>) \<omega>"
  let ?G = "sigma (space P) (pre_sigma_of P ?F \<sigma>)"
  have T0': "0 \<le> T" using T0 by simp
  interpret PP: prob_space P by (rule PS)
  interpret H: horizon_sq_int_martingale P ?F Y T by (rule H)
  have spP: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spP])
  have subF: "subalgebra P (?F t)" if "0 \<le> t" for t
    by (rule H.subalgebras[OF that])
  have stops: "{\<omega> \<in> space P. \<sigma> \<omega> \<le> t} \<in> sets (?F t)" if t: "0 \<le> t" for t
    unfolding FB spP
    by (rule path_stopping_time_event_filtration_all[OF T0' sts sM t])

  \<comment> \<open>\<open>\<F>\<^sub>\<sigma>\<close> as a genuine sub-\<open>\<sigma>\<close>-algebra of \<open>P\<close>\<close>
  have sa: "sigma_algebra (space P) (pre_sigma_of P ?F \<sigma>)"
    by (rule sigma_algebra_pre_sigma_of[OF subF stops])
  have setsG: "sets ?G = pre_sigma_of P ?F \<sigma>"
    by (rule sigma_algebra.sets_measure_of_eq[OF sa])
  have spG: "space ?G = space P" by (simp add: space_measure_of_conv)
  have subG: "subalgebra P ?G"
    unfolding subalgebra_def using spG setsG pre_sigma_of_sets by auto
  have fm: "finite_measure P"
    by (rule finite_measureI) (simp add: PP.emeasure_space_1)
  interpret SF: sigma_finite_subalgebra P ?G
    by (intro finite_measure_subalgebra_is_sigma_finite
        finite_measure_subalgebra.intro
        finite_measure_subalgebra_axioms.intro fm subG)

  \<comment> \<open>the increment: integrable, and square integrable by Doob\<close>
  have intr: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Y (\<rho> \<omega>) \<omega>)"
    by (rule integrable_at_path_stopping_time[OF T0 setsP H Ycont str rM])
  have ints: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Y (\<sigma> \<omega>) \<omega>)"
    by (rule integrable_at_path_stopping_time[OF T0 setsP H Ycont sts sM])
  have intD: "integrable P ?D"
    by (rule Bochner_Integration.integrable_diff[OF intr ints])
  have pathcont: "AE \<omega> in P. continuous_on {0..T} (\<lambda>s. Y s \<omega>)"
    by (rule AE_I2) (rule Ycont)
  have Dbd: "AE \<omega> in P. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Y s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates[OF pathcont])
  have Dsq: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (?D \<omega>)\<^sup>2)"
  proof (rule Bochner_Integration.integrable_bound
      [where f = "\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). 4 * (H.Dsup \<omega>)\<^sup>2"])
    show "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). 4 * (H.Dsup \<omega>)\<^sup>2)"
      using H.Dsup_sq_integrable by simp
    show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). (?D \<omega>)\<^sup>2) \<in> borel_measurable P"
      using intD by simp
    show "AE \<omega> in P. norm ((?D \<omega>)\<^sup>2) \<le> norm (4 * (H.Dsup \<omega>)\<^sup>2)"
      using Dbd
    proof eventually_elim
      case (elim \<omega>)
      have bs: "\<bar>Y (\<sigma> \<omega>) \<omega>\<bar> \<le> H.Dsup \<omega>"
        using elim path_stopping_time_nonneg[OF sts, of \<omega>]
          path_stopping_time_le[OF sts, of \<omega>] by simp
      have br: "\<bar>Y (\<rho> \<omega>) \<omega>\<bar> \<le> H.Dsup \<omega>"
        using elim path_stopping_time_nonneg[OF str, of \<omega>]
          path_stopping_time_le[OF str, of \<omega>] by simp
      have le2: "\<bar>?D \<omega>\<bar> \<le> 2 * H.Dsup \<omega>" using bs br by simp
      have "(?D \<omega>)\<^sup>2 = \<bar>?D \<omega>\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (2 * H.Dsup \<omega>)\<^sup>2"
        by (rule power_mono[OF le2 abs_ge_zero])
      finally show ?case by (simp add: power_mult_distrib)
    qed
  qed

  \<comment> \<open>the known factor\<close>
  have ZG: "Z \<in> borel_measurable ?G"
  proof (rule measurableI)
    show "Z \<omega> \<in> space borel" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" by simp
    fix B :: "real set" assume B: "B \<in> sets borel"
    show "Z -` B \<inter> space ?G \<in> sets ?G" using Zpre[OF B] setsG spG by simp
  qed
  have ZP: "Z \<in> borel_measurable P"
    using ZG measurable_from_subalg[OF subG] by blast
  have Dm: "?D \<in> borel_measurable P" using intD by simp
  have intZD: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Z \<omega> * ?D \<omega>)"
    by (rule integrable_mult_of_sq[OF ZP Dm Zsq Dsq])
  show int1: "integrable P (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). ?D \<omega> * Z \<omega>)"
    using intZD by (simp add: mult.commute)

  \<comment> \<open>the increment conditions to zero\<close>
  have ceD: "AE \<omega> in P. cond_exp P ?G ?D \<omega> = 0"
  proof (rule AE_zero_of_set_integral_zero[OF subG])
    show "integrable P (cond_exp P ?G ?D)" by (rule integrable_cond_exp)
    show "cond_exp P ?G ?D \<in> borel_measurable ?G"
      by (rule borel_measurable_cond_exp)
    fix C assume C: "C \<in> sets ?G"
    then have C': "C \<in> pre_sigma_of P ?F \<sigma>" using setsG by simp
    have CP: "C \<in> sets P" by (rule pre_sigma_of_sets[OF C'])
    have sii: "set_integrable P C (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Y (\<sigma> \<omega>) \<omega>)"
      unfolding set_integrable_def by (rule integrable_mult_indicator[OF CP ints])
    have sij: "set_integrable P C (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Y (\<rho> \<omega>) \<omega>)"
      unfolding set_integrable_def by (rule integrable_mult_indicator[OF CP intr])
    have "set_lebesgue_integral P C (cond_exp P ?G ?D)
        = set_lebesgue_integral P C ?D"
      by (rule SF.cond_exp_set_integral[OF intD C, symmetric])
    also have "\<dots> = set_lebesgue_integral P C (\<lambda>\<omega>. Y (\<rho> \<omega>) \<omega>)
        - set_lebesgue_integral P C (\<lambda>\<omega>. Y (\<sigma> \<omega>) \<omega>)"
      using set_integral_diff(2)[OF sij sii] by simp
    also have "\<dots> = 0"
      using stopped_increment_of_horizon_gen
        [OF T0 setsP H Ycont sts sM str rM le C'] by simp
    finally show "set_lebesgue_integral P C (cond_exp P ?G ?D) = 0" .
  qed
  have ceZD: "AE \<omega> in P. cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>) \<omega>
      = Z \<omega> * cond_exp P ?G ?D \<omega>"
    by (rule SF.cond_exp_measurable_mult(2)[OF intZD intD ZG])
  have ae0: "AE \<omega> in P. cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>) \<omega> = 0"
    using ceZD ceD by eventually_elim simp

  have AP: "A \<in> sets P" by (rule pre_sigma_of_sets[OF A])
  have AG: "A \<in> sets ?G" using A setsG by simp
  have aeA: "AE \<omega>\<in>A in P. cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>) \<omega> = 0"
    using ae0 by (auto elim: eventually_mono)
  have "set_lebesgue_integral P A (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). Z \<omega> * ?D \<omega>)
      = set_lebesgue_integral P A (cond_exp P ?G (\<lambda>\<omega>. Z \<omega> * ?D \<omega>))"
    by (rule SF.cond_exp_set_integral[OF intZD AG])
  also have "\<dots> = set_lebesgue_integral P A (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). 0)"
    by (rule set_lebesgue_integral_cong_AE
        [OF AP SF.borel_measurable_cond_exp' borel_measurable_const aeA])
  also have "\<dots> = 0" by (simp add: set_lebesgue_integral_def)
  finally show "set_lebesgue_integral P A
      (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). ?D \<omega> * Z \<omega>) = 0"
    by (simp add: mult.commute)
qed

text \<open>The known factor is a function of the stopped path, hence \<open>\<F>\<^sub>\<theta>\<close>- and a
  fortiori \<open>\<F>\<^sub>(\<^sub>u\<^sub> \<^sub>\<or>\<^sub> \<^sub>\<theta>\<^sub>)\<close>-measurable.\<close>

section \<open>Clause (iv) for the compensated martingale\<close>

text \<open>The second, and last, clause-(iv) instance.  The pathwise identity is
  the \<^const>\<open>outerp\<close> expansion: with \<open>\<sigma> = i \<or> \<theta>\<close>, \<open>\<rho> = j \<or> \<theta>\<close> and
  \<open>b = fst (\<omega> (\<theta> \<omega>))\<close>,

  \<open>h (pafter T \<theta> \<omega>) = (Ym\<^sub>\<rho> - Ym\<^sub>\<sigma>) - (Yc\<^sub>\<rho> - Yc\<^sub>\<sigma>)\<sqdot>b$d - (Yd\<^sub>\<rho> - Yd\<^sub>\<sigma>)\<sqdot>b$c\<close>

  --- a compensated increment, which @{thm [source] stopped_increment_of_horizon_gen}
  kills, and two cross terms, which
  @{thm [source] set_integral_increment_times_known} kills.  The constants
  \<open>outerp b\<close> and \<open>\<langle>X\<rangle>\<^sub>\<theta>\<close> have already cancelled between the two times.\<close>


(*<*)

(*<*)
end
(*>*)
