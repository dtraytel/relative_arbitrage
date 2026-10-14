section \<open>Stopping times as path functionals\<close>

(*<*)
theory Path_Stopping_Times
  imports Path_Splicing "Continuous_Time_Martingales.Stopping_Time_Sampling"
begin

(*>*)

text \<open>\<open>path_stopping_time T \<theta>\<close> asks that \<open>\<theta>\<close> read only the path up to
  \<open>\<theta>\<close> itself; \<open>pstopped\<close> and \<open>pafter\<close> split a path there.  The
  sigma-algebra of the past, \<open>pre_sigma_of\<close>, and optional sampling of a
  martingale at two bounded stopping times come from
  @{theory Continuous_Time_Martingales.Stopping_Time_Sampling}; \<open>dyceil\<close>
  (@{theory Continuous_Time_Martingales.Dyadic_Grids}) is the dyadic ceiling that
  approximates a stopping time from above by simple ones.\<close>

definition pstopped :: "real \<Rightarrow> ((real \<Rightarrow> 'b) \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'b)
    \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pstopped T \<theta> \<omega> = restrict (\<lambda>t. \<omega> (min t (\<theta> \<omega>))) {0..T}"

definition pafter :: "real \<Rightarrow> ((real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> 'b)
    \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pafter T \<theta> \<omega> = restrict (\<lambda>t. \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)) {0..T}"

lemma pstopped_apply: "t \<in> {0..T} \<Longrightarrow> pstopped T \<theta> \<omega> t = \<omega> (min t (\<theta> \<omega>))"
  by (simp add: pstopped_def)

lemma pstopped_outside: "t \<notin> {0..T} \<Longrightarrow> pstopped T \<theta> \<omega> t = undefined"
  unfolding pstopped_def restrict_def by (rule if_not_P)

text \<open>The reassembly law.  This is the analogue of
  @{thm [source] pglue_pcut_pfut} at a random time, and unlike that one it
  costs nothing: no membership hypothesis on \<open>\<omega>\<close>, and no \<open>\<theta>\<close> on the
  right-hand side.\<close>

text \<open>The future factor starts at \<open>0\<close> --- exactly the normalisation the class
  asks of a continuation --- and the two halves live on disjoint stretches of
  time.\<close>

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
    if True: "s \<in> {0..T}" for s
  proof -
    have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> (min s t)) \<in> borel_measurable ?F"
      by (rule natural_filtration_eval) (use True t in auto)
    then show ?thesis by (simp add: pstopped_apply[OF True])
  qed
  show ?thesis by (rule path_measurable_of_eval[OF T0 into ev])
qed

text \<open>Stopping at a measurable time is measurable: by
  @{thm [source] path_measurable_of_eval} it suffices that each evaluation is,
  and @{thm [source] path_eval_at_measurable_time} makes it so.\<close>

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
  have ev: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pstopped T \<theta> \<omega> t) \<in> borel_measurable ?B"
    if True: "t \<in> {0..T}" for t
  proof -
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
  qed
  show ?thesis by (rule path_measurable_of_eval[OF T0 into ev])
qed

subsection \<open>The regular conditional distribution, with both maps and horizons free\<close>

text \<open>The regular conditional distribution of the past given the future uses
  the two maps only through their measurability, so it is proved
  (\<open>path_rcd\<close>, \<open>path_rcd_ksemi\<close> in \<open>Path_Law_Pasting\<close>) with the two maps
  and the two horizons free; the deterministic split
  (\<open>exit_class_rcd\<close>, \<open>exit_class_rcd_ksemi\<close>) is the instance \<open>u := r\<close>, \<open>v := T - r\<close>, and
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

subsection \<open>The glued law, and the clauses that come for free\<close>

text \<open>The law of the reassembled path: run the past under \<open>Q\<close>, draw a
  continuation from \<open>\<kappa>\<close>, and add.  This is the stopping-time analogue of
  \<open>kglue_law'\<close>, and the only structural difference is that
  \<^const>\<open>padd\<close> replaces \<^const>\<open>pglue\<close>.\<close>

text \<open>Postponing a stopping time by a map \<open>f\<close> of \<open>[0,T]\<close> into itself with
  \<open>x \<le> f x\<close> keeps it a stopping time: two paths agreeing up to the later
  time agree up to the earlier one, which then coincides.\<close>

lemma path_stopping_time_comp_ge:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add) \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>"
    and ge: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> T \<Longrightarrow> x \<le> f x"
    and into: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> T \<Longrightarrow> 0 \<le> f x \<and> f x \<le> T"
  shows "path_stopping_time T (\<lambda>\<omega>. f (\<theta> \<omega>))"
proof -
  have c1: "0 \<le> f (\<theta> \<omega>) \<and> f (\<theta> \<omega>) \<le> T" for \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)"
    using into path_stopping_time_nonneg[OF st, of \<omega>]
      path_stopping_time_le[OF st, of \<omega>] by blast
  have c2: "f (\<theta> \<omega>') = f (\<theta> \<omega>)"
    if cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
      and cw': "continuous_on {0..T} (\<lambda>v. fst (\<omega>' v))"
      and ag: "\<forall>s \<in> {0..f (\<theta> \<omega>)}. \<omega> s = \<omega>' s" for \<omega> \<omega>' :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof -
    have le: "\<theta> \<omega> \<le> f (\<theta> \<omega>)"
      using ge path_stopping_time_nonneg[OF st, of \<omega>]
        path_stopping_time_le[OF st, of \<omega>] by blast
    have "\<theta> \<omega>' = \<theta> \<omega>"
    proof (rule path_stopping_time_cong[OF st cw cw'])
      fix s assume "s \<in> {0..\<theta> \<omega>}"
      then have "s \<in> {0..f (\<theta> \<omega>)}" using le by auto
      then show "\<omega> s = \<omega>' s" using ag by blast
    qed
    then show ?thesis by simp
  qed
  show ?thesis unfolding path_stopping_time_def using c1 c2 by blast
qed

lemma path_stopping_time_max:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add) \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and u: "0 \<le> u" and uT: "u \<le> T"
  shows "path_stopping_time T (\<lambda>\<omega>. max u (\<theta> \<omega>))"
  by (rule path_stopping_time_comp_ge[OF st, where f = "\<lambda>x. max u x"]) (use u uT in auto)

text \<open>The event lemma with the horizon restriction removed: past \<open>T\<close> there is
  nothing left to decide.\<close>

lemma path_stopping_time_shift:
  fixes \<theta> :: "(real \<Rightarrow> 'a::{topological_space,ab_group_add} \<times> 'b::ab_group_add) \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and i: "0 \<le> i"
  shows "path_stopping_time T (\<lambda>\<omega>. min (\<theta> \<omega> + i) T)"
  by (rule path_stopping_time_comp_ge[OF st, where f = "\<lambda>x. min (x + i) T"]) (use i in auto)

text \<open>They are also ordered in \<open>i\<close>, which is what lets
  \<open>pre_sigma_of_mono\<close> carry the conditioning set from the
  earlier sampling time to the later one; pure arithmetic, discharged where
  it is used.\<close>

text \<open>The stopping-time event is not merely Borel but lies in the natural
  filtration at \<open>t\<close>, which is what \<open>set_martingale_sampling\<close>
  consumes.\<close>

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
  then show "\<theta> (pstopped T (\<lambda>_. t) \<omega>) \<le> t"
    using path_stopping_time_cut_eq[OF st tT h cw] by simp
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

section \<open>Clause (iv) at a stopping time: the increment identity\<close>

text \<open>The assembly.  Every hypothesis of
  \<open>set_martingale_sampling_two\<close> now has a supplier: the
  martingale from the class via @{thm [source] martingale_vec_nth},
  the filtration facts from @{thm [source] sets_natural_filtration_mono} and
  the martingale locale, the stopping-time events from
  \<open>path_stopping_time_event_filtration_all\<close>, the convergence from
  \<open>dyceil_tendsto\<close> and continuity of the paths, and the domination from
  @{theory Continuous_Time_Martingales.Doob_Inequality}'s \<open>Dsup\<close> through
  \<open>exit_class_horizon_component\<close>.\<close>

text \<open>The same identity for an arbitrary real process that is a
  \<open>horizon_sq_int_martingale\<close> with continuous paths.  Both of the class's
  martingale clauses are of that shape --- the \<open>X\<close> one componentwise, the
  compensated one entrywise --- so this is the form clause (iv) uses twice.
  \<open>martingale_mat_nth\<close> lives in
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

text \<open>Galmarino's half: the path stopped at \<open>\<theta>\<close> is measurable with respect to
  the \<open>\<sigma>\<close>-algebra of events before \<open>\<theta>\<close>
  (\<open>pre_sigma_of\<close>, from @{theory Continuous_Time_Martingales.Stopping_Time_Sampling}).
  Below \<open>t\<close> the stopped path is read off the path stopped at \<open>t\<close>
  --- \<open>pstopped_cut_compose\<close> --- and that composite is
  \<open>\<F>\<^sub>t\<close>-measurable by \<open>pstopped_const_measurable_filtration\<close>.\<close>

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

section \<open>From the pathwise stopping time to the filtration one\<close>

text \<open>\<open>path_stopping_time\<close> is the pathwise notion: \<open>\<theta>\<close> is decided by the
  path up to \<open>\<theta>\<close>.  What the sampling theorem consumes is the filtration
  notion, \<open>{\<theta> \<le> t} \<in> \<F>\<^sub>t\<close>.  The bridge is that below \<open>t\<close> the event only sees
  the path stopped at \<open>t\<close>: \<open>\<theta> \<omega> \<le> t\<close> exactly when
  \<open>\<theta> (\<omega> stopped at t) \<le> t\<close>, and the stopped path is an \<open>\<F>\<^sub>t\<close>-measurable
  function of \<open>\<omega>\<close>.\<close>

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
        [OF mg stops sig0 sigU T0' conts Dbd Dint])
qed

section \<open>The increment identity moves to the kernel\<close>

text \<open>The stopping-time twin of \<open>pfut_rcd_F_increment_zero\<close>,
  stated once for an arbitrary real integrand \<open>h\<close> on the future factor
  together with the identity \<open>hP\<close> pulling it back to an increment of a
  horizon martingale \<open>Y\<close> of \<open>P\<close>.  Every clause of the class surviving the
  additive split has this shape, so the disintegration is done once here
  and instantiated afterwards.

  The chain follows the deterministic one --- \<open>AE_kernel_integral_zero\<close>
  to rectangles, \<open>integral_ksemi_rect_of_set_integral\<close> to a set
  integral over \<open>P\<close> --- with the conditioning set landing in
  \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<or>\<^sub> \<^sub>\<theta>\<^sub>)\<close> instead of a
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
    by (rule integrable_prod_of_squares[OF Zsq Dsq ZP Dm])
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


section \<open>The exit time of a ball\<close>

text \<open>The capped exit time of the state component of a pair path from an open
  ball, and the pathwise facts about it that the viscosity arguments consume.\<close>

definition pball_exit :: "real \<Rightarrow> real^'n::finite \<Rightarrow> real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  where "pball_exit T x \<epsilon> \<omega> = pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"

lemma pball_exit_nonneg:
  assumes T0: "0 \<le> T" shows "0 \<le> pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def by (rule pexit_nonneg[OF T0])

lemma pball_exit_le:
  assumes T0: "0 \<le> T" shows "pball_exit T x \<epsilon> \<omega> \<le> T"
  unfolding pball_exit_def by (rule pexit_le_T[OF T0])

lemma pball_exit_cong:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and eq: "\<And>t. t \<in> {0..pball_exit T x \<epsilon> \<omega>} \<Longrightarrow> \<omega> t = \<omega>' t"
  shows "pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
  unfolding pball_exit_def
proof (rule pexit_cong_stopping[OF T0 open_ball cont])
  fix t :: real
  assume t: "0 \<le> t" "t \<le> pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t))"
  then have "t \<in> {0..pball_exit T x \<epsilon> \<omega>}" by (simp add: pball_exit_def)
  from eq[OF this] show "fst (\<omega> t) = fst (\<omega>' t)" by simp
qed

text \<open>What makes the exit time useful to the expansion: below
  the horizon the path has actually travelled the full distance \<open>\<epsilon>\<close>.\<close>

lemma pball_exit_outside:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and lt: "pball_exit T x \<epsilon> \<omega> < T"
  shows "\<epsilon> \<le> dist (fst (\<omega> (pball_exit T x \<epsilon> \<omega>))) x"
proof -
  have "fst (\<omega> (pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t)))) \<notin> ball x \<epsilon>"
    using lt unfolding pball_exit_def
    by (intro pexit_mem_of_less_T[OF T0 open_ball cont]) simp
  then show ?thesis
    unfolding pball_exit_def by (simp add: dist_commute)
qed

text \<open>And it is strictly positive when the path starts strictly inside the
  ball --- exactly the situation of the subsolution argument, where the
  starting point is the touching point \<open>x\<close> itself.  Without this the DPP
  bound of \<open>exit_val_cond_at_time\<close> would be vacuous.\<close>

lemma pball_exit_pos:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 < T"
    and start: "dist (fst (\<omega> 0)) x < \<epsilon>"
    and cont: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "0 < pball_exit T x \<epsilon> \<omega>"
proof -
  have T0': "0 \<le> T" using T0 by simp
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have e0: "0 < \<epsilon> - dist (fst (\<omega> 0)) x" using start by simp
  from cont[unfolded continuous_on_iff] z e0
  obtain \<delta> where d0: "0 < \<delta>"
    and dd: "\<And>t. t \<in> {0..T} \<Longrightarrow> dist t 0 < \<delta>
        \<Longrightarrow> dist (fst (\<omega> t)) (fst (\<omega> 0)) < \<epsilon> - dist (fst (\<omega> 0)) x"
    by blast
  have mle: "min \<delta> T \<le> pball_exit T x \<epsilon> \<omega>"
  proof (rule ccontr)
    assume "\<not> min \<delta> T \<le> pball_exit T x \<epsilon> \<omega>"
    then have lt0: "pball_exit T x \<epsilon> \<omega> < min \<delta> T" by (rule not_le_imp_less)
    then have lt: "pexit T (ball x \<epsilon>) (\<lambda>t. fst (\<omega> t)) < min \<delta> T"
      by (simp add: pball_exit_def)
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> fst (\<omega> r) \<in> - ball x \<epsilon> \<and> r < min \<delta> T)
        \<or> T < min \<delta> T"
      using lt[unfolded pexit_less_iff[OF T0']] .
    then obtain r where r: "0 \<le> r" "r \<le> T" "fst (\<omega> r) \<notin> ball x \<epsilon>"
      "r < min \<delta> T" by auto
    have dr: "dist (fst (\<omega> r)) (fst (\<omega> 0)) < \<epsilon> - dist (fst (\<omega> 0)) x"
      using r by (intro dd) (auto simp: dist_real_def)
    have "dist (fst (\<omega> r)) x
        \<le> dist (fst (\<omega> r)) (fst (\<omega> 0)) + dist (fst (\<omega> 0)) x"
      by (rule dist_triangle)
    also have "\<dots> < \<epsilon>" using dr by simp
    finally have "fst (\<omega> r) \<in> ball x \<epsilon>" by (simp add: dist_commute)
    with r(3) show False by simp
  qed
  have m0: "0 < min \<delta> T" using d0 T0 by simp
  show ?thesis by (rule order_less_le_trans[OF m0 mle])
qed

subsection \<open>The ball exit time is a stopping time\<close>

text \<open>\<^const>\<open>path_stopping_time\<close> restricts its congruence clause to
  continuous paths, which is exactly what @{thm [source] pexit_mem_of_less_T}
  shows is forced: attainment of the infimum genuinely fails off the path
  space, so no redefinition of the exit time could have avoided it.  The
  restriction costs nothing, because \<open>space Q = mspace (path_metric T)\<close> is
  the set of continuous paths, and it buys this:\<close>

theorem pball_exit_path_stopping_time:
  fixes x :: "real^'n::finite"
  assumes T0: "0 \<le> T"
  shows "path_stopping_time T (pball_exit T x \<epsilon>)"
  unfolding path_stopping_time_def
proof (intro conjI)
  show "\<forall>\<omega> :: 'n pairpath.
      0 \<le> pball_exit T x \<epsilon> \<omega> \<and> pball_exit T x \<epsilon> \<omega> \<le> T"
    using pball_exit_nonneg[OF T0] pball_exit_le[OF T0] by blast
next
  show "\<forall>\<omega> \<omega>' :: 'n pairpath.
      continuous_on {0..T} (\<lambda>t. fst (\<omega> t)) \<longrightarrow>
      continuous_on {0..T} (\<lambda>t. fst (\<omega>' t)) \<longrightarrow>
      (\<forall>t \<in> {0..pball_exit T x \<epsilon> \<omega>}. \<omega> t = \<omega>' t) \<longrightarrow>
      pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
  proof (intro allI impI)
    fix \<omega> \<omega>' :: "'n pairpath"
    assume c: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
      and c': "continuous_on {0..T} (\<lambda>t. fst (\<omega>' t))"
      and e: "\<forall>t \<in> {0..pball_exit T x \<epsilon> \<omega>}. \<omega> t = \<omega>' t"
    show "pball_exit T x \<epsilon> \<omega>' = pball_exit T x \<epsilon> \<omega>"
      by (rule pball_exit_cong[OF T0 c]) (use e in blast)
  qed
qed

text \<open>So \<open>exit_val_dpp_sup_ge_time\<close> applies at the exit time of
  a ball, and optional sampling at \<open>\<tau> \<and> h\<close> is available for stochastic
  localisation.\<close>

subsection \<open>Measurability of the ball exit time\<close>

text \<open>\<open>pexit_path_measurable\<close> covers closed targets and the ball is open, so
  this cannot be inherited directly.  With the closed set \<open>- ball x \<epsilon>\<close> as
  the hitting target, along a continuous path the sublevel event
  \<open>{\<tau> \<le> t}\<close> is (by @{thm [source] etime_le_iff}, using attainment) the
  event that the path reaches distance \<open>\<ge> \<epsilon>\<close> somewhere on \<open>[0,t]\<close>, and by
  continuity that is decided by countably many times: the rationals of
  \<open>[0,t]\<close> and \<open>t\<close> itself.  A countable intersection of countable unions of
  evaluation events remains measurable.\<close>

lemma pball_exit_le_iff_dense:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T" and t: "0 \<le> t" and tT: "t < T"
    and cont: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
  shows "pball_exit T x \<epsilon> \<omega> \<le> t \<longleftrightarrow>
     (\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x)"
proof -
  have Ac: "closed (- ball x \<epsilon> :: (real^'n) set)"
    by (simp add: closed_Compl)
  have hc: "continuous_on {0..T} (\<lambda>s. dist (fst (\<omega> s)) x)"
    by (intro continuous_on_dist cont continuous_on_const)
  show ?thesis
  proof
    assume le: "pball_exit T x \<epsilon> \<omega> \<le> t"
    then have "etime T (- ball x \<epsilon>) (\<lambda>r g. g r) (\<lambda>s. fst (\<omega> s)) \<le> t"
      by (simp add: pball_exit_def pexit_def)
    then have "\<exists>r\<in>{0..t}. fst (\<omega> r) \<in> - ball x \<epsilon>"
      using etime_le_iff[where X = "\<lambda>r g. g r" and \<omega> = "\<lambda>s. fst (\<omega> s)",
          OF T0 t tT Ac cont] by simp
    then obtain r0 where r0: "r0 \<in> {0..t}" and m0: "fst (\<omega> r0) \<notin> ball x \<epsilon>"
      by auto
    have d0: "\<epsilon> \<le> dist (fst (\<omega> r0)) x"
      using m0 by (simp add: dist_commute)
    show "\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
    proof
      fix n :: nat
      show "\<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
          \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
      proof (cases "r0 = 0 \<or> r0 = t")
        case True
        have mem: "r0 \<in> insert t ({0..t} \<inter> \<rat>)"
          using True r0 t by auto
        have p1: "0 < 1 / real (Suc n)" by simp
        with d0 have "\<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r0)) x" by linarith
        with mem show ?thesis by blast
      next
        case False
        then have r00: "0 < r0" and r0t: "r0 < t" using r0 by auto
        have r0T: "r0 \<in> {0..T}" using r0 tT by auto
        have cw: "continuous (at r0 within {0..T}) (\<lambda>s. dist (fst (\<omega> s)) x)"
          using hc r0T by (simp add: continuous_on_eq_continuous_within)
        have e1: "0 < 1 / real (Suc n)" by simp
        obtain d where dd: "0 < d"
          and near: "\<And>s. s \<in> {0..T} \<Longrightarrow> dist s r0 < d \<Longrightarrow>
              dist (dist (fst (\<omega> s)) x) (dist (fst (\<omega> r0)) x) < 1 / real (Suc n)"
          using cw[unfolded continuous_within_eps_delta, rule_format, OF e1]
          by blast
        obtain q where q: "q \<in> \<rat>" and ql: "r0 - min d r0 < q" and qu: "q < r0"
          using Rats_dense_in_real[of "r0 - min d r0" r0] dd r00 by auto
        have q0: "0 \<le> q" using ql dd r00 by simp
        have qt: "q \<le> t" using qu r0t by simp
        have qT: "q \<in> {0..T}" using q0 qt tT by auto
        have "dist q r0 < d" using ql qu dd by (simp add: dist_real_def)
        then have "dist (dist (fst (\<omega> q)) x) (dist (fst (\<omega> r0)) x)
            < 1 / real (Suc n)"
          by (rule near[OF qT])
        then have "dist (fst (\<omega> r0)) x - 1 / real (Suc n) < dist (fst (\<omega> q)) x"
          by (simp add: dist_real_def abs_diff_less_iff)
        with d0 have "\<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> q)) x" by simp
        moreover have "q \<in> insert t ({0..t} \<inter> \<rat>)" using q q0 qt by auto
        ultimately show ?thesis by blast
      qed
    qed
  next
    assume H: "\<forall>n :: nat. \<exists>r \<in> insert t ({0..t} \<inter> \<rat>).
        \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x"
    have "\<exists>r \<in> {0..t}. \<epsilon> \<le> dist (fst (\<omega> r)) x"
    proof -
      obtain rs where rs: "\<And>n :: nat. rs n \<in> insert t ({0..t} \<inter> \<rat>)
          \<and> \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> (rs n))) x"
        using H by metis
      have rng: "rs n \<in> {0..t}" for n using rs[of n] t by auto
      have bdd: "bounded (range rs)"
      proof (rule boundedI[of _ t])
        fix w assume "w \<in> range rs"
        then obtain n where "w = rs n" by blast
        then show "norm w \<le> t" using rng[of n] t by auto
      qed
      obtain l \<sigma> where sm: "strict_mono \<sigma>" and lim: "(rs \<circ> \<sigma>) \<longlonglongrightarrow> l"
        using bounded_imp_convergent_subsequence[OF bdd] by blast
      have inI: "(rs \<circ> \<sigma>) n \<in> {0..t}" for n using rng[of "\<sigma> n"] by simp
      have lI: "l \<in> {0..t}"
        by (rule closed_sequentially[OF closed_atLeastAtMost _ lim])
          (use inI in blast)
      have lT: "l \<in> {0..T}" using lI tT by auto
      have cl: "continuous (at l within {0..T}) (\<lambda>s. dist (fst (\<omega> s)) x)"
        using hc lT by (simp add: continuous_on_eq_continuous_within)
      have inT: "(rs \<circ> \<sigma>) n \<in> {0..T}" for n using inI[of n] tT by auto
      have tends: "(\<lambda>n. dist (fst (\<omega> ((rs \<circ> \<sigma>) n))) x)
          \<longlonglongrightarrow> dist (fst (\<omega> l)) x"
        using cl[unfolded continuous_within_sequentially, rule_format,
            of "rs \<circ> \<sigma>"] inT lim by (simp add: o_def)
      have low: "\<epsilon> - 1 / real (Suc n) \<le> dist (fst (\<omega> ((rs \<circ> \<sigma>) n))) x" for n
      proof -
        have "\<epsilon> - 1 / real (Suc (\<sigma> n)) < dist (fst (\<omega> (rs (\<sigma> n)))) x"
          using rs[of "\<sigma> n"] by blast
        moreover have "\<epsilon> - 1 / real (Suc n) \<le> \<epsilon> - 1 / real (Suc (\<sigma> n))"
          using seq_suble[OF sm, of n] by (simp add: frac_le)
        ultimately show ?thesis by (simp add: o_def)
      qed
      have lima: "(\<lambda>n. \<epsilon> - 1 / real (Suc n)) \<longlonglongrightarrow> \<epsilon>"
      proof -
        have "(\<lambda>n. 1 / real (Suc n)) \<longlonglongrightarrow> 0"
          using LIMSEQ_inverse_real_of_nat by (simp add: inverse_eq_divide)
        then have "(\<lambda>n. \<epsilon> - 1 / real (Suc n)) \<longlonglongrightarrow> \<epsilon> - 0"
          by (intro tendsto_diff tendsto_const)
        then show ?thesis by simp
      qed
      have "\<epsilon> \<le> dist (fst (\<omega> l)) x"
        by (rule LIMSEQ_le[OF lima tends]) (use low in blast)
      then show ?thesis using lI by blast
    qed
    then obtain r where r: "r \<in> {0..t}" and rd: "\<epsilon> \<le> dist (fst (\<omega> r)) x"
      by blast
    have "fst (\<omega> r) \<notin> ball x \<epsilon>" using rd by (simp add: dist_commute)
    then have "pexit T (ball x \<epsilon>) (\<lambda>s. fst (\<omega> s)) \<le> r"
      using r tT by (intro pexit_le_of_mem[OF T0]) auto
    then have "pball_exit T x \<epsilon> \<omega> \<le> r" by (simp add: pball_exit_def)
    then show "pball_exit T x \<epsilon> \<omega> \<le> t"
      using r by (auto intro: order_trans)
  qed
qed

theorem pball_exit_measurable:
  fixes x :: "real^'n::finite"
  assumes T0: "0 \<le> T"
  shows "pball_exit T x \<epsilon> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
proof (rule borel_measurableI_le)
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  fix a :: real
  show "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} \<in> sets ?B"
  proof (cases "a < 0")
    case True
    have empty: "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} = {}"
    proof (rule set_eqI)
      fix \<omega> :: "'n pairpath"
      have "\<not> pball_exit T x \<epsilon> \<omega> \<le> a"
        using pball_exit_nonneg[OF T0, of x \<epsilon> \<omega>] True by linarith
      then show "\<omega> \<in> {\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
          \<longleftrightarrow> \<omega> \<in> {}" by simp
    qed
    show ?thesis unfolding empty by simp
  next
    case False
    then have a0: "0 \<le> a" by simp
    show ?thesis
    proof (cases "T \<le> a")
      case True
      have ya: "pball_exit T x \<epsilon> \<omega> \<le> a" for \<omega> :: "'n pairpath"
        using pball_exit_le[OF T0, of x \<epsilon> \<omega>] True by linarith
      then have "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a} = space ?B" by auto
      then show ?thesis by simp
    next
      case False
      then have aT: "a < T" by simp
      let ?D = "insert a ({0..a} \<inter> \<rat>)"
      let ?S = "\<lambda>n r. {\<omega> \<in> space ?B. \<epsilon> - 1 / real (Suc n) < dist (fst (\<omega> r)) x}"
      have cntD: "countable ?D"
        by (intro countable_insert countable_Int2 countable_rat)
      have atom: "?S n r \<in> sets ?B" for n r
      proof -
        have "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x) \<in> borel_measurable ?B"
          by (rule dist_eval_measurable)
        then have "(\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x) -` {\<epsilon> - 1 / real (Suc n) <..}
            \<inter> space ?B \<in> sets ?B"
          by (rule measurable_sets) simp
        moreover have "?S n r = (\<lambda>\<omega> :: 'n pairpath. dist (fst (\<omega> r)) x)
            -` {\<epsilon> - 1 / real (Suc n) <..} \<inter> space ?B"
          by auto
        ultimately show ?thesis by simp
      qed
      have eq: "{\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
          = (\<Inter>n. \<Union>r \<in> ?D. ?S n r)"
      proof (rule set_eqI)
        fix \<omega> :: "'n pairpath"
        show "\<omega> \<in> {\<omega> \<in> space ?B. pball_exit T x \<epsilon> \<omega> \<le> a}
            \<longleftrightarrow> \<omega> \<in> (\<Inter>n. \<Union>r \<in> ?D. ?S n r)"
        proof (cases "\<omega> \<in> space ?B")
          case True
          have cw: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
            by (rule path_sets_fst_continuous[OF refl True])
          show ?thesis
            using pball_exit_le_iff_dense[OF T0 a0 aT cw, of x \<epsilon>] True
            by auto
        next
          case False
          then show ?thesis by auto
        qed
      qed
      have un_m: "(\<Union>r \<in> ?D. ?S n r) \<in> sets ?B" for n
        by (rule sets.countable_UN'[OF cntD]) (use atom in blast)
      have "(\<Inter>n. \<Union>r \<in> ?D. ?S n r) \<in> sets ?B"
        using un_m by blast
      with eq show ?thesis by metis
    qed
  qed
qed

subsection \<open>Up to the exit time the path stays in the closed ball\<close>

lemma pball_exit_stays_cball:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and start: "dist (fst (\<omega> 0)) x < \<epsilon>"
    and cont: "continuous_on {0..T} (\<lambda>s. fst (\<omega> s))"
    and s: "0 \<le> s" and sle: "s \<le> pball_exit T x \<epsilon> \<omega>"
  shows "dist (fst (\<omega> s)) x \<le> \<epsilon>"
proof (rule ccontr)
  assume "\<not> dist (fst (\<omega> s)) x \<le> \<epsilon>"
  then have gt: "\<epsilon> < dist (fst (\<omega> s)) x" by simp
  have sT: "s \<le> T" using sle pball_exit_le[OF T0] order_trans by blast
  have notin: "fst (\<omega> s) \<notin> ball x \<epsilon>"
    using gt by (simp add: dist_commute)
  have le1: "pball_exit T x \<epsilon> \<omega> \<le> s"
    unfolding pball_exit_def
    by (rule pexit_le_of_mem[where f = "\<lambda>s. fst (\<omega> s)" and r = s
          and K = "ball x \<epsilon>", OF T0 s sT notin])
  with sle have seq: "s = pball_exit T x \<epsilon> \<omega>" by simp
  have h0: "dist (fst (\<omega> 0)) x \<le> \<epsilon>" using start by simp
  have hc: "continuous_on {0..s} (\<lambda>r. dist (fst (\<omega> r)) x)"
    by (rule continuous_on_subset[of "{0..T}"])
      (use sT in \<open>auto intro!: continuous_on_dist cont continuous_on_const\<close>)
  obtain r where r0: "0 \<le> r" and rs: "r \<le> s" and rd: "dist (fst (\<omega> r)) x = \<epsilon>"
    using IVT'[of "\<lambda>r. dist (fst (\<omega> r)) x" 0 \<epsilon> s] h0 gt s hc by auto
  have rlt: "r < s" using rd gt rs by (cases "r = s") auto
  have "fst (\<omega> r) \<notin> ball x \<epsilon>" using rd by (simp add: dist_commute)
  then have "pball_exit T x \<epsilon> \<omega> \<le> r"
    unfolding pball_exit_def
    by (intro pexit_le_of_mem[OF T0 r0]) (use rs sT in auto)
  with rlt seq show False by simp
qed

(*<*)
end
(*>*)
