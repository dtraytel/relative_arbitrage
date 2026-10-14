section \<open>Exit times of continuous paths\<close>

(*<*)
theory Path_Exit_Times
  imports
    Path_Space_Infinite "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Time_Martingales.Stopping_Times"
begin

(*>*)

text \<open>
  The exit time of a closed set by a continuous path, and how it behaves
  under weak convergence of path laws -- the shape in which Larsson and Ruf
  use it (Lemma 2.1 of \<^cite>\<open>LarssonRuf\<close>).
  The capped exit time is upper semicontinuous on the path space: its strict
  sublevels are open.  Hence the essential infimum of the exit time is upper
  semicontinuous along weak convergence of path laws: lying below a level is
  an open event of positive mass, and the open-set half of the portmanteau
  theorem keeps that mass positive along the sequence.  No Laplace transform
  is needed.\<close>

subsection \<open>The path-space exit time\<close>

text \<open>The capped exit time from \<open>K\<close>, read off a path rather than a sample
  point: the composition of \<open>etime\<close> with the identity process. All laws on
  the path space share this sample space and this exit functional; it is
  the object whose essential infimum a minimum-exit-time value takes.\<close>

definition pexit :: "real \<Rightarrow> ('b :: polish_space) set \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> real"
  where "pexit T K f = etime T (- K) (\<lambda>r g. g r) f"

lemma pexit_le_T: "0 \<le> T \<Longrightarrow> pexit T K f \<le> T"
  unfolding pexit_def by (rule etime_le_T)

lemma pexit_nonneg: "0 \<le> T \<Longrightarrow> 0 \<le> pexit T K f"
  unfolding pexit_def by (rule etime_nonneg)

lemma pexit_less_iff:
  "0 \<le> T \<Longrightarrow> pexit T K f < c
    \<longleftrightarrow> ((\<exists>r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K \<and> r < c) \<or> T < c)"
  unfolding pexit_def by (rule etime_less_iff)

lemma pexit_le_of_mem:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" "r \<le> T" and mem: "f r \<notin> K"
  shows "pexit T K f \<le> r"
  unfolding pexit_def using T0 r mem by (intro etime_le_of_mem) auto

lemma pexit_cong_on:
  assumes "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> U \<Longrightarrow> f t = g t"
  shows "pexit U K f = pexit U K g"
proof -
  have "{t. 0 \<le> t \<and> t \<le> U \<and> f t \<in> - K} = {t. 0 \<le> t \<and> t \<le> U \<and> g t \<in> - K}"
    using assms by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma pexit_eq_of_stays:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T'" and stays: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T' \<Longrightarrow> f s \<in> K"
  shows "pexit T' K f = T'"
proof -
  have e: "{t. 0 \<le> t \<and> t \<le> T' \<and> f t \<in> - K} = {}" using stays by auto
  show ?thesis unfolding pexit_def etime_def e by simp
qed

text \<open>A minimum-exit-time problem posed on \<open>C([0,\<infinity>), \<real>\<^sup>n)\<close>
  takes the essential infimum of the uncapped exit time
  \<open>\<tau>\<^sub>K = inf {t \<ge> 0 : X t \<notin> K}\<close>, whereas \<open>pexit T K\<close> caps at the horizon \<open>T\<close>.
  The cap is monotone in \<open>T\<close> and invisible once a path has exited before
  \<open>T\<close>: raising the horizon does not move the value. Hence for laws under
  which the exit happens before \<open>T\<close> almost surely, every capped horizon
  beyond that point gives the same essential infimum, which licenses working
  at a fixed finite \<open>T\<close>.\<close>

lemma pexit_min_horizon:
  fixes K :: "'b::polish_space set"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "pexit S K f = min (pexit T K f) S"
proof -
  have "pexit S K f < c \<longleftrightarrow> min (pexit T K f) S < c" for c
    using pexit_less_iff[OF S, of K f c] pexit_less_iff[OF order.trans[OF S ST], of K f c] ST
    by (auto simp: min_less_iff_disj)
  from this[of "pexit S K f"] this[of "min (pexit T K f) S"] show ?thesis
    by (meson linorder_neqE order.irrefl)
qed

lemma pexit_cap_eq:
  fixes K :: "'a::polish_space set" and f :: "real \<Rightarrow> 'a"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and ex: "\<not> (pexit r K f = r \<and> f r \<in> K)"
  shows "pexit T K f = pexit r K f"
proof (cases "pexit T K f \<le> r")
  case True
  then show ?thesis using pexit_min_horizon[OF r rT, of K f] by (simp add: min_absorb1)
next
  case False
  then have "f r \<in> K" using pexit_le_of_mem[OF order.trans[OF r rT] r rT] by blast
  moreover have "pexit r K f = r" using False pexit_min_horizon[OF r rT, of K f] by simp
  ultimately show ?thesis using ex by simp
qed

lemma pexit_mono_T:
  assumes T: "0 \<le> T" and TT: "T \<le> T'"
  shows "pexit T K f \<le> pexit T' K f"
  by (simp add: pexit_min_horizon[OF T TT])

text \<open>Upper semicontinuity, in sublevel-set form: strict sublevels of an exit
  time are open in the path topology. A path that is in the open set \<open>A\<close>
  (after a continuous map \<open>\<phi>\<close>) before \<open>c\<close> is so at some single time, and
  evaluation at that time is continuous.\<close>

lemma etime_comp_sublevel_open:
  fixes T c :: real and A :: "'c::topological_space set"
    and \<phi> :: "'b::polish_space \<Rightarrow> 'c"
  assumes T: "0 \<le> T" and A: "open A" and \<phi>: "continuous_on UNIV \<phi>"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). etime T A (\<lambda>s w. \<phi> (w s)) f < c}"
proof (cases "T < c")
  case True
  then have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). etime T A (\<lambda>s w. \<phi> (w s)) f < c}
      = topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    using le_less_trans[OF etime_le_T[OF T, of A "\<lambda>s w. \<phi> (w s)"] True] by simp
  then show ?thesis by (simp only: openin_topspace)
next
  case False
  have eq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). etime T A (\<lambda>s w. \<phi> (w s)) f < c}
      = (\<Union>r \<in> {r. 0 \<le> r \<and> r \<le> T \<and> r < c}.
          {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). \<phi> (f r) \<in> A})"
    using False etime_less_iff[OF T, of A "\<lambda>s w. \<phi> (w s)" _ c] by blast
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). \<phi> (f r) \<in> A}"
    if r: "r \<in> {0..T}" for r
    using open_eval_preimage[OF r open_vimage[OF A \<phi>]] by simp
  show ?thesis unfolding eq by (intro openin_Union) (auto intro: op)
qed

lemma pexit_sublevel_open:
  fixes K :: "('b :: polish_space) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "openin (mtopology_of (path_metric T))
      {f \<in> mspace (path_metric T). pexit T K f < c}"
  using etime_comp_sublevel_open[OF T, where A = "- K" and \<phi> = "\<lambda>x. x"] K
  by (simp add: pexit_def open_Compl)

lemma pexit_measurable:
  fixes K :: "('b :: polish_space) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "pexit T K \<in> borel_measurable
      (path_borel T :: (real \<Rightarrow> 'b) measure)"
proof (rule borel_measurableI_less)
  fix c :: real
  have "{f \<in> space (path_borel T :: (real \<Rightarrow> 'b) measure). pexit T K f < c}
      = {f \<in> mspace (path_metric T). pexit T K f < c}"
    by (simp add: space_borel_of)
  then show "{f \<in> space (path_borel T :: (real \<Rightarrow> 'b) measure). pexit T K f < c}
      \<in> sets (path_borel T)"
    using borel_of_open[OF pexit_sublevel_open[OF T K]] by simp
qed

subsection \<open>The portmanteau theorem on the path space\<close>

text \<open>Along weak convergence of path laws, the measure of an open set can
  only gain mass in the limit (the open-set half of the portmanteau
  theorem).\<close>

lemma weak_conv_open_liminf:
  fixes \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b :: polish_space) measure"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and U: "openin (mtopology_of (path_metric T
      :: (real \<Rightarrow> 'b) metric)) U"
  shows "ereal (measure \<Lambda> U)
      \<le> Liminf sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) U))"
  by (rule weak_conv_openin_liminf[OF wc U])

text \<open>The closed-set half of the portmanteau theorem on the path space: a
  closed condition on paths that every approximating law satisfies with full
  mass survives the weak limit.\<close>

lemma weak_conv_closed_limsup:
  fixes \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b :: polish_space) measure"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and A: "closedin (mtopology_of (path_metric T
      :: (real \<Rightarrow> 'b) metric)) A"
  shows "Limsup sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) A))
      \<le> ereal (measure \<Lambda> A)"
  by (rule weak_conv_closedin_limsup[OF wc A])

subsection \<open>Upper semicontinuity of the essential infimum of the exit time\<close>

text \<open>Upper semicontinuity in the form of \<open>Limsup_le_iff\<close>: whenever
  \<open>ess_inf_time \<Lambda> (pexit T K) < d\<close>, the sublevel \<open>{pexit T K < d}\<close> is an
  open set of positive \<open>\<Lambda>\<close>-mass (\<open>ess_inf_time_less_iff\<close>,
  \<open>pexit_sublevel_open\<close>), so by the open-set portmanteau it eventually has
  positive \<open>\<Lambda>i i\<close>-mass, which is \<open>ess_inf_time (\<Lambda>i i) (pexit T K) < d\<close>.
  Neither probability nor a positive horizon is needed.\<close>

theorem ess_inf_pexit_usc:
  fixes K :: "('b :: polish_space) set"
    and \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure" and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes T0: "0 \<le> T" and K: "closed K"
    and wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
  shows "Limsup sequentially (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
      \<le> ess_inf_time \<Lambda> (pexit T K)"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>"
    using wc unfolding weak_conv_on_def by (auto elim: eventually_mono)
  have sub: "{f \<in> space M. ennreal (pexit T K f) < d}
      = {f \<in> mspace ?m. pexit T K f < (if d = \<top> then T + 1 else enn2real d)}"
    if s: "sets M = sets (borel_of (mtopology_of ?m))" for M d
  proof -
    have sp: "space M = mspace ?m"
      using sets_eq_imp_space_eq[OF s] by (simp add: space_borel_of)
    show ?thesis
    proof (cases "d = \<top>")
      case True
      then show ?thesis
        using sp pexit_le_T[OF T0, of K]
        by (auto intro: order.strict_trans1[OF _ less_add_one])
    next
      case False
      then have "d = ennreal (enn2real d)" by (cases d rule: ennreal_cases) auto
      then show ?thesis
        using sp False pexit_nonneg[OF T0, of K]
        by (auto simp: ennreal_less_iff) (metis ennreal_less_iff)+
    qed
  qed
  have meas: "{f \<in> space M. ennreal (pexit T K f) < d} \<in> sets M"
    if s: "sets M = sets (borel_of (mtopology_of ?m))" for M d
    unfolding sub[OF s] s
    by (rule borel_of_open[OF pexit_sublevel_open[OF T0 K]])
  show ?thesis
    unfolding Limsup_le_iff
  proof (intro allI impI)
    fix d assume d: "ess_inf_time \<Lambda> (pexit T K) < d"
    let ?U = "{f \<in> mspace ?m. pexit T K f < (if d = \<top> then T + 1 else enn2real d)}"
    have "emeasure \<Lambda> ?U \<noteq> 0"
      using d ess_inf_time_less_iff[OF meas[OF wc'[THEN conjunct2, THEN conjunct1]]]
        sub[OF wc'[THEN conjunct2, THEN conjunct1]] by simp
    then have pos: "0 < measure \<Lambda> ?U"
      using finite_measure.emeasure_eq_measure[OF wc'[THEN conjunct2, THEN conjunct2]]
      by (simp add: zero_less_measure_iff)
    have "ereal (measure \<Lambda> ?U)
        \<le> Liminf sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) ?U))"
      by (rule weak_conv_open_liminf[OF wc pexit_sublevel_open[OF T0 K]])
    then have "\<forall>\<^sub>F i in sequentially. ereal 0 < ereal (measure (\<Lambda>i i) ?U)"
      by (rule le_Liminf_iff[THEN iffD1, rule_format]) (use pos in simp)
    with wc'[THEN conjunct1]
    show "\<forall>\<^sub>F i in sequentially. ess_inf_time (\<Lambda>i i) (pexit T K) < d"
    proof eventually_elim
      case (elim i)
      then have "emeasure (\<Lambda>i i) ?U \<noteq> 0"
        by (auto simp: measure_def)
      then show ?case
        using ess_inf_time_less_iff[OF meas[OF elim(1)]] sub[OF elim(1)] by simp
    qed
  qed
qed

subsection \<open>Shifted exit times, confinement, and test functionals\<close>

lemma open_etime_shift_less:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         etime T A (\<lambda>s w. y + w s) f < d}"
  using etime_comp_sublevel_open[OF T A, where \<phi> = "\<lambda>z. y + z"]
  by (simp add: continuous_intros)

subsubsection \<open>The uncapped exit time\<close>

text \<open>The exit time from \<open>K\<close> is the increasing limit of the capped exit times.
  It takes the value \<open>\<top>\<close> exactly on the paths that never leave \<open>K\<close>.\<close>

definition iexit :: "'b::polish_space set \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> ennreal" where
  "iexit K f = (SUP T \<in> {0..}. ennreal (pexit T K f))"

lemma pexit_le_iexit:
  assumes T: "0 \<le> T"
  shows "ennreal (pexit T K f) \<le> iexit K f"
  unfolding iexit_def using T by (intro SUP_upper) simp

lemma pexit_cong_nonneg:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> f s = g s" and T: "0 \<le> T"
  shows "pexit T K f = pexit T K g"
  using eq by (intro pexit_cong_on) simp

lemma iexit_cong_nonneg:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> f s = g s"
  shows "iexit K f = iexit K g"
  unfolding iexit_def by (intro SUP_cong refl) (use pexit_cong_nonneg[OF eq] in auto)

lemma pexit_restrict [simp]: "pexit T K (restrict f {0..T}) = pexit T K f"
  by (rule pexit_cong_on) simp

lemma iexit_nat_sup: "iexit K f = (SUP n :: nat. ennreal (pexit (real n) K f))"
proof (rule antisym)
  show "iexit K f \<le> (SUP n :: nat. ennreal (pexit (real n) K f))"
    unfolding iexit_def
  proof (rule SUP_least)
    fix T :: real assume "T \<in> {0..}"
    then have T: "0 \<le> T" by simp
    obtain n :: nat where n: "T < real n" using reals_Archimedean2 by blast
    have "pexit T K f \<le> pexit (real n) K f"
      by (rule pexit_mono_T[OF T]) (use n in simp)
    then have "ennreal (pexit T K f) \<le> ennreal (pexit (real n) K f)"
      by (rule ennreal_leI)
    also have "\<dots> \<le> (SUP n :: nat. ennreal (pexit (real n) K f))"
      by (rule SUP_upper) simp
    finally show "ennreal (pexit T K f) \<le> (SUP n :: nat. ennreal (pexit (real n) K f))" .
  qed
  show "(SUP n :: nat. ennreal (pexit (real n) K f)) \<le> iexit K f"
    by (rule SUP_least) (auto intro: pexit_le_iexit)
qed

lemma iexit_measurable_gen:
  fixes K :: "('b::polish_space) set" and N :: "'a measure"
  assumes K: "closed K"
    and Ym: "\<And>t. 0 \<le> t \<Longrightarrow> Y t \<in> borel_measurable N"
    and cont: "\<And>\<omega>. \<omega> \<in> space N \<Longrightarrow> continuous_on {0..} (\<lambda>t. Y t \<omega>)"
  shows "(\<lambda>\<omega>. iexit K (\<lambda>t. Y t \<omega>)) \<in> borel_measurable N"
proof -
  have step: "(\<lambda>\<omega>. ennreal (pexit T K (\<lambda>t. Y t \<omega>))) \<in> borel_measurable N"
    if T: "0 \<le> T" for T
  proof -
    have p: "(\<lambda>\<omega>. restrict (\<lambda>t. Y t \<omega>) {0..T})
        \<in> N \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'b) measure)"
    proof (rule pathify_measurable[OF T])
      fix t assume "t \<in> {0..T}"
      then show "Y t \<in> borel_measurable N" by (intro Ym) simp
    next
      fix \<omega> assume "\<omega> \<in> space N"
      from cont[OF this] show "continuous_on {0..T} (\<lambda>t. Y t \<omega>)"
        by (rule continuous_on_subset) auto
    qed
    have "(\<lambda>\<omega>. pexit T K (restrict (\<lambda>t. Y t \<omega>) {0..T})) \<in> borel_measurable N"
      by (rule measurable_compose[OF p pexit_measurable[OF T K]])
    then show ?thesis by simp
  qed
  have "(\<lambda>\<omega>. SUP n :: nat. ennreal (pexit (real n) K (\<lambda>t. Y t \<omega>)))
      \<in> borel_measurable N"
    by (intro borel_measurable_SUP[where I = UNIV]) (use step in auto)
  then show ?thesis by (simp add: iexit_nat_sup)
qed

lemma iexit_measurable_ipath:
  fixes K :: "('b::polish_space) set"
  assumes K: "closed K"
  shows "iexit K \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
proof -
  have "(\<lambda>w :: real \<Rightarrow> 'b. iexit K (\<lambda>t. w t))
      \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
  proof (rule iexit_measurable_gen[OF K])
    show "\<And>t. 0 \<le> t \<Longrightarrow> (\<lambda>w :: real \<Rightarrow> 'b. w t)
        \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
      by (rule ipath_eval_measurable)
  next
    fix w :: "real \<Rightarrow> 'b" assume "w \<in> space (ipath_space :: ((real \<Rightarrow> 'b) measure))"
    then show "continuous_on {0..} (\<lambda>t. w t)"
      by (intro ipath_continuous_on) auto
  qed
  then show ?thesis by simp
qed

subsubsection \<open>Splitting the exit time at an intermediate time\<close>

text \<open>Translating a nonempty set of reals that is bounded below translates
  its infimum.\<close>

lemma cInf_shift_real:
  fixes S :: "real set"
  assumes ne: "S \<noteq> {}" and bdd: "bdd_below S"
  shows "Inf ((\<lambda>s. r + s) ` S) = r + Inf S"
proof -
  obtain m where m: "\<And>s. s \<in> S \<Longrightarrow> m \<le> s" using bdd by (auto simp: bdd_below_def)
  have neI: "(\<lambda>s. r + s) ` S \<noteq> {}" using ne by blast
  have bddI: "bdd_below ((\<lambda>s. r + s) ` S)"
    by (rule bdd_belowI[of _ "r + m"]) (use m in auto)
  show ?thesis
  proof (rule antisym)
    have "Inf ((\<lambda>s. r + s) ` S) - r \<le> s" if s: "s \<in> S" for s
    proof -
      have "Inf ((\<lambda>s. r + s) ` S) \<le> r + s"
        using s by (intro cInf_lower[OF _ bddI]) blast
      then show ?thesis by simp
    qed
    then have "Inf ((\<lambda>s. r + s) ` S) - r \<le> Inf S" by (intro cInf_greatest[OF ne])
    then show "Inf ((\<lambda>s. r + s) ` S) \<le> r + Inf S" by simp
    show "r + Inf S \<le> Inf ((\<lambda>s. r + s) ` S)"
    proof (rule cInf_greatest[OF neI])
      fix z assume "z \<in> (\<lambda>s. r + s) ` S"
      then obtain s where s: "s \<in> S" "z = r + s" by blast
      then show "r + Inf S \<le> z" using cInf_lower[OF s(1) bdd] by simp
    qed
  qed
qed

text \<open>On the survival event the exit time splits exactly: the first piece
  contributes \<open>r\<close> and the rest is the exit time of the time-shifted path
  measured against the shortened horizon.  This is the identity that turns
  the almost-sure bound \<open>\<tau>\<^sub>K \<ge> c\<close> into a bound on the future.\<close>

lemma pexit_split_at_r:
  fixes K :: "'a::polish_space set" and f :: "real \<Rightarrow> 'a"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and surv: "pexit r K f = r" and endK: "f r \<in> K"
  shows "pexit T K f = r + pexit (T - r) K (\<lambda>s. f (r + s))"
proof -
  have stay: "f t \<in> K" if t: "t \<in> {0..r}" for t
  proof (rule ccontr)
    assume nk: "f t \<notin> K"
    have "pexit r K f \<le> t"
      using r t nk by (intro pexit_le_of_mem) auto
    with surv t have "t = r" by simp
    then show False using nk endK by simp
  qed
  define B where "B = {s. 0 \<le> s \<and> s \<le> T - r \<and> f (r + s) \<in> - K} \<union> {T - r}"
  have Beq: "{t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T} = (\<lambda>s. r + s) ` B"
  proof (rule set_eqI, rule iffI)
    fix t assume "t \<in> {t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T}"
    then consider (hit) "0 \<le> t" "t \<le> T" "f t \<in> - K" | (cap) "t = T" by blast
    then show "t \<in> (\<lambda>s. r + s) ` B"
    proof cases
      case hit
      have rt: "r < t"
      proof (rule ccontr)
        assume "\<not> r < t"
        then have "t \<in> {0..r}" using hit(1) by simp
        then show False using stay hit(3) by simp
      qed
      show ?thesis
      proof (rule image_eqI[where x = "t - r"])
        show "t = r + (t - r)" by simp
        show "t - r \<in> B" unfolding B_def using hit rt by simp
      qed
    next
      case cap
      show ?thesis
      proof (rule image_eqI[where x = "T - r"])
        show "t = r + (T - r)" using cap by simp
        show "T - r \<in> B" unfolding B_def by simp
      qed
    qed
  next
    fix t assume "t \<in> (\<lambda>s. r + s) ` B"
    then obtain s where s: "s \<in> B" "t = r + s" by blast
    from s(1) consider (hit) "0 \<le> s" "s \<le> T - r" "f (r + s) \<in> - K" | (cap) "s = T - r"
      unfolding B_def by blast
    then show "t \<in> {t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T}"
    proof cases
      case hit
      then show ?thesis using s(2) r by simp
    next
      case cap
      then show ?thesis using s(2) by simp
    qed
  qed
  have ne: "B \<noteq> {}" unfolding B_def by blast
  have bdd: "bdd_below B"
    unfolding B_def by (rule bdd_belowI[of _ 0]) (use rT in auto)
  have "pexit T K f = Inf ({t. 0 \<le> t \<and> t \<le> T \<and> f t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  also have "\<dots> = Inf ((\<lambda>s. r + s) ` B)" unfolding Beq ..
  also have "\<dots> = r + Inf B" by (rule cInf_shift_real[OF ne bdd])
  also have "\<dots> = r + pexit (T - r) K (\<lambda>s. f (r + s))"
    unfolding pexit_def etime_def B_def ..
  finally show ?thesis .
qed

text \<open>A path whose exit time is at least \<open>c\<close> has stayed in \<open>K\<close> up to
  every earlier time \<open>r\<close>: its exit time capped at \<open>r\<close> is \<open>r\<close>, and its
  position at \<open>r\<close> lies in \<open>K\<close>.\<close>

lemma pexit_surv_of_less:
  fixes f :: "real \<Rightarrow> 'a::polish_space" and K :: "'a set"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" and rT: "r \<le> T" and lt: "r < c"
    and ge: "c \<le> pexit T K f"
  shows "pexit r K f = r \<and> f r \<in> K"
proof -
  have stay: "f t \<in> K" if t: "t \<in> {0..r}" for t
  proof (rule ccontr)
    assume nk: "f t \<notin> K"
    have "pexit T K f \<le> t"
      using T0 t rT nk by (intro pexit_le_of_mem) auto
    moreover have "t \<le> r" using t by simp
    ultimately show False using ge lt by simp
  qed
  have "pexit r K f = r" using stay by (intro pexit_eq_of_stays[OF r]) simp
  moreover have "f r \<in> K" using stay r by simp
  ultimately show ?thesis by simp
qed

subsubsection \<open>Shifted exit times below a level\<close>

text \<open>The countable reduction, at the level of measures: \<open>etime_less_iff_qtimes_open\<close>
  turns the event into a union over the countable \<open>qtimes T\<close>, so
  \<open>positive_of_countable_UN\<close> extracts a single witness time of positive
  mass --- needed before erosion, which requires a fixed time to erode
  around.\<close>

lemma positive_mass_at_some_qtime:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pos: "emeasure P
        {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "\<exists>r \<in> qtimes T. r < d
      \<and> emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
proof -
  have spP: "space P = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sP] by (simp add: space_borel_of)
  define R where "R = {r \<in> qtimes T. r < d}"
  have cR: "countable R" unfolding R_def using countable_qtimes by simp

  text \<open>The pointwise reduction, applied path by path. Continuity of the shifted
    path is what \<open>mspace_path_metricD\<close> supplies.\<close>
  have ptw: "etime T A (\<lambda>s w. x + w s) \<omega> < d
      \<longleftrightarrow> (\<exists>r \<in> R. x + \<omega> r \<in> A)"
    if w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" for \<omega>
  proof -
    have cont: "continuous_on {0..T} (\<lambda>s. x + \<omega> s)"
      by (intro continuous_intros mspace_path_metricD[OF w])
    text \<open>\<open>etime\<close> applies its process only to the one path \<open>\<omega>\<close>, so freezing
      the path inside the process changes nothing mathematically, but the
      reduction lemma is stated for a frozen process.\<close>
    have eq: "etime T A (\<lambda>s w. x + w s) \<omega> = etime T A (\<lambda>s w'. x + \<omega> s) \<omega>"
      unfolding etime_def by simp
    show ?thesis
      unfolding eq R_def
      using etime_less_iff_qtimes_open[OF T A dT cont, of \<omega>] by auto
  qed
  have split: "{\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d}
      = (\<Union>r \<in> R. {\<omega> \<in> space P. x + \<omega> r \<in> A})"
    using ptw unfolding spP by blast

  text \<open>Measurability of each slice comes from openness of the shifted evaluation
    preimage, exactly as in \<open>etime_shift_uniform_margin\<close>.\<close>
  have meas: "{\<omega> \<in> space P. x + \<omega> r \<in> A} \<in> sets P" if r: "r \<in> R" for r
  proof -
    have "r \<in> qtimes T" using r unfolding R_def by simp
    hence rT: "r \<in> {0..T}" using qtimes_subset[OF T] by blast
    have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). x + f r \<in> A}"
      by (rule open_shifted_eval_preimage[OF rT A])
    from borel_of_open[OF this] show ?thesis unfolding sP spP by simp
  qed
  have "emeasure P (\<Union>r \<in> R. {\<omega> \<in> space P. x + \<omega> r \<in> A}) \<noteq> 0"
    using pos unfolding split .
  from positive_of_countable_UN[OF cR meas this] show ?thesis
    unfolding R_def by blast
qed


text \<open>
  The value functional, real-valued: \<open>ess_inf_time\<close> is
  \<open>ennreal\<close>-valued but Berge's supremum needs a real number; the
  conversion is faithful since the exit time is capped at \<open>T\<close>, so the
  essential infimum is never \<open>\<top>\<close>.
\<close>

definition vshift :: "real \<Rightarrow> 'b::{polish_space,real_normed_vector} set
    \<Rightarrow> 'b \<Rightarrow> (real \<Rightarrow> 'b) measure \<Rightarrow> real" where
  "vshift T A y Q = enn2real (ess_inf_time Q (etime T A (\<lambda>s w. y + w s)))"

lemma vshift_le:
  fixes A :: "'b::{polish_space,real_normed_vector} set"
  assumes T: "0 \<le> T" and Q: "prob_space Q"
  shows "vshift T A y Q \<le> T"
proof -
  have "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF Q]) (rule etime_le_T[OF T])
  from enn2real_mono[OF this] show ?thesis
    unfolding vshift_def using T by simp
qed

text \<open>The bridge from the real-valued functional back to the positive-mass
  statement. Both directions of the \<open>ennreal\<close> conversion need the ceiling:
  without it \<open>enn2real\<close> could collapse \<open>\<top>\<close> to \<open>0\<close> and the strict inequality
  would be an artefact.\<close>

lemma vshift_less_iff_positive_mass:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and Q :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d" and d0: "0 \<le> d"
    and sQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pQ: "prob_space Q"
  shows "vshift T A y Q < d
      \<longleftrightarrow> emeasure Q {\<omega> \<in> space Q. etime T A (\<lambda>s w. y + w s) \<omega> < d} \<noteq> 0"
proof -
  have spQ: "space Q = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sQ] by (simp add: space_borel_of)
  have setseq: "{\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d}
      = {\<omega> \<in> space Q. etime T A (\<lambda>s w. y + w s) \<omega> < d}"
    using etime_nonneg[OF T, of A "\<lambda>s w. y + w s"]
    by (auto simp: ennreal_less_iff)
  have meas: "{\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d}
      \<in> sets Q"
    unfolding setseq
    using borel_of_open[OF open_etime_shift_less[OF T A dT]]
    unfolding sQ spQ by simp
  have le: "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF pQ]) (rule etime_le_T[OF T])
  have fin: "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) < \<top>"
    using le ennreal_less_top by (rule order_le_less_trans)
  have "vshift T A y Q < d
      \<longleftrightarrow> ennreal (vshift T A y Q) < ennreal d"
    unfolding vshift_def by (simp add: ennreal_less_iff)
  also have "\<dots> \<longleftrightarrow> ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) < ennreal d"
    unfolding vshift_def by (simp add: ennreal_enn2real[OF fin])
  also have "\<dots> \<longleftrightarrow> emeasure Q
      {\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d} \<noteq> 0"
    by (rule ess_inf_time_less_iff[OF meas])
  finally show ?thesis unfolding setseq .
qed


lemma etime_shift_superlevel_closed:
  fixes T :: real and c :: ennreal
    and A :: "'b::{polish_space,real_normed_vector} set" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         c \<le> ennreal (etime T A (\<lambda>s w. y + w s) f)}"
proof (cases c rule: ennreal_cases)
  case (real r)
  text \<open>The complement of a strict sublevel set, which is open.\<close>
  have eq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         c \<le> ennreal (etime T A (\<lambda>s w. y + w s) f)}
      = topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
             etime T A (\<lambda>s w. y + w s) f < r}"
    using real etime_nonneg[OF T, of A "\<lambda>s w. y + w s"] by (auto simp: ennreal_le_iff)
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). etime T A (\<lambda>s w. y + w s) f < r}"
    using etime_comp_sublevel_open[OF T A, where \<phi> = "\<lambda>z. y + z"] by (simp add: continuous_intros)
  show ?thesis unfolding eq by (rule closedin_diff[OF closedin_topspace op])
qed (simp add: top_unique)

definition rclamp :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rclamp c y = max (- c) (min c y)"

lemma rclamp_bound: "0 \<le> c \<Longrightarrow> \<bar>rclamp c y\<bar> \<le> c"
  by (simp add: rclamp_def abs_le_iff min_def max_def)

lemma rclamp_id:
  assumes "\<bar>y\<bar> \<le> c"
  shows "rclamp c y = y"
proof -
  have "min c y = y"
    using assms by (intro min_absorb2) (simp add: abs_le_iff)
  moreover have "max (- c) y = y"
    using assms by (intro max_absorb2) (simp add: abs_le_iff)
  ultimately show ?thesis by (simp add: rclamp_def)
qed

lemma rclamp_cont: "continuous_map euclideanreal euclideanreal (rclamp c)"
  unfolding continuous_map_iff_continuous2 rclamp_def
  by (intro continuous_intros)

subsubsection \<open>Attainment and the horizon cap\<close>

text \<open>Below the horizon, the exit time from an open set is attained: the
  path is outside the set at that time.\<close>

lemma pexit_mem_of_less_T:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and lt: "pexit T K f < T"
  shows "f (pexit T K f) \<notin> K"
proof -
  let ?S = "{r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K}"
  have cK: "closed (- K)" unfolding closed_def using Kop by simp
  have Sclosed: "closed ?S"
  proof -
    have "?S = f -` (- K) \<inter> {0..T}" by auto
    then show ?thesis using cont cK by (simp add: continuous_on_closed_vimage)
  qed
  have Sbdd: "bdd_below ?S" by (intro bdd_belowI[of _ 0]) auto
  have pe: "pexit T K f = Inf (?S \<union> {T})"
    unfolding pexit_def etime_def by simp
  have Sne: "?S \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> ?S \<noteq> {}"
    then have e: "?S = {}" by simp
    have "pexit T K f = Inf ({} \<union> {T})" unfolding pe e ..
    then have "pexit T K f = T" by simp
    with lt show False by simp
  qed
  have SleT: "Inf ?S \<le> T"
  proof -
    from Sne obtain s where s: "s \<in> ?S" by blast
    then have "Inf ?S \<le> s" using Sbdd by (intro cInf_lower)
    also have "s \<le> T" using s by simp
    finally show ?thesis .
  qed
  have "Inf (?S \<union> {T}) = inf (Inf ?S) (Inf {T})"
    by (rule cInf_union_distrib[OF Sne Sbdd]) auto
  then have "pexit T K f = Inf ?S" using pe SleT by (simp add: inf_min)
  moreover have "Inf ?S \<in> ?S"
    using Sne Sbdd Sclosed by (intro closed_contains_Inf) auto
  ultimately show ?thesis by simp
qed

text \<open>Hence the congruence clause of a stopping time, restricted to continuous
  paths: a path that agrees with \<open>f\<close> up to the exit time of \<open>f\<close> has the
  same exit time.  The asymmetry: the \<open>\<ge>\<close> direction is unconditional (a
  witness for \<open>g\<close> strictly below the exit time of \<open>f\<close> is a witness for \<open>f\<close>
  too), and only the \<open>\<le>\<close> direction needs attainment.\<close>

lemma pexit_cong_stopping:
  fixes f g :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and eq: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pexit T K f \<Longrightarrow> f t = g t"
  shows "pexit T K g = pexit T K f"
proof -
  have th0: "0 \<le> pexit T K f" by (rule pexit_nonneg[OF T0])
  have thT: "pexit T K f \<le> T" by (rule pexit_le_T[OF T0])
  have le: "pexit T K g \<le> pexit T K f"
  proof (cases "pexit T K f < T")
    case True
    have "f (pexit T K f) \<notin> K"
      by (rule pexit_mem_of_less_T[OF T0 Kop cont True])
    then have m: "g (pexit T K f) \<notin> K"
      using eq[OF th0 order_refl] by simp
    show ?thesis
      by (rule pexit_le_of_mem[of T "pexit T K f" g K, OF T0 th0 thT m])
  next
    case False
    with thT have "pexit T K f = T" by simp
    then show ?thesis using pexit_le_T[OF T0, of K g] by simp
  qed
  have ge: "pexit T K f \<le> pexit T K g"
  proof (rule ccontr)
    assume "\<not> pexit T K f \<le> pexit T K g"
    then have lt: "pexit T K g < pexit T K f" by simp
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> g r \<in> - K \<and> r < pexit T K f)
        \<or> T < pexit T K f"
      using lt pexit_less_iff[OF T0] by blast
    with thT obtain r where r: "0 \<le> r" "r \<le> T" "g r \<notin> K"
      "r < pexit T K f" by auto
    have "f r \<notin> K" using eq[OF r(1)] r(4) r(3) by simp
    then have "pexit T K f \<le> r"
      by (rule pexit_le_of_mem[OF T0 r(1) r(2)])
    with r(4) show False by simp
  qed
  from le ge show ?thesis by simp
qed

text \<open>Capping the uncapped exit time returns the capped one.  This is the
  pathwise form of the statement that the horizon is a device: everything the
  capped development says about \<open>pexit T\<close> is a statement about \<open>iexit\<close> below
  the level \<open>T\<close>.\<close>

theorem iexit_cap:
  assumes T: "0 \<le> T"
  shows "min (iexit K f) (ennreal T) = ennreal (pexit T K f)"
proof (cases "iexit K f \<le> ennreal T")
  case True
  have eq: "pexit S K f = pexit T K f" if S: "T \<le> S" for S
  proof -
    have S0: "0 \<le> S" using T S by simp
    have "ennreal (pexit S K f) \<le> ennreal T"
      using True pexit_le_iexit[OF S0, of K f] by simp
    then have "pexit S K f \<le> T" using T by simp
    moreover have "pexit T K f = min (pexit S K f) T"
      by (rule pexit_min_horizon[OF T S])
    ultimately show ?thesis by simp
  qed
  have "iexit K f = ennreal (pexit T K f)"
    unfolding iexit_def
  proof (rule antisym)
    show "(SUP S\<in>{0..}. ennreal (pexit S K f)) \<le> ennreal (pexit T K f)"
    proof (rule SUP_least)
      fix S :: real assume "S \<in> {0..}"
      then have S0: "0 \<le> S" by simp
      show "ennreal (pexit S K f) \<le> ennreal (pexit T K f)"
      proof (cases "T \<le> S")
        case True
        then have "pexit S K f = pexit T K f" by (rule eq)
        then show ?thesis by simp
      next
        case False
        then have "pexit S K f = min (pexit T K f) S"
          by (intro pexit_min_horizon[OF S0]) simp
        then show ?thesis by (simp add: ennreal_leI)
      qed
    qed
    show "ennreal (pexit T K f) \<le> (SUP S\<in>{0..}. ennreal (pexit S K f))"
      using T by (intro SUP_upper) simp
  qed
  with True show ?thesis by simp
next
  case False
  then have gt: "ennreal T < iexit K f" by simp
  obtain S where S0: "0 \<le> S" and Sgt: "ennreal T < ennreal (pexit S K f)"
    using gt unfolding iexit_def by (auto simp: less_SUP_iff)
  have pS: "0 \<le> pexit S K f" by (rule pexit_nonneg[OF S0])
  have TltS: "T < pexit S K f"
    using Sgt pS T by (simp add: ennreal_less_iff)
  have TS: "T \<le> S" using TltS pexit_le_T[OF S0, of K f] by simp
  have "pexit T K f = min (pexit S K f) T"
    by (rule pexit_min_horizon[OF T TS])
  then have pT: "pexit T K f = T" using TltS by simp
  have "min (iexit K f) (ennreal T) = ennreal T"
    using gt by (simp add: min_absorb2 order_less_imp_le)
  then show ?thesis using pT by simp
qed


subsection \<open>Upper semicontinuity in the starting point\<close>

text \<open>The shifted exit-time functional \<open>vshift T A x P\<close> meets the hypotheses of
  Berge's maximum theorem (\<open>usc_sup_over_compactin\<close>) jointly in the starting
  point \<open>x\<close> and the law \<open>P\<close>, so its supremum over a weakly compact family of
  laws is upper semicontinuous in \<open>x\<close>.\<close>

lemma etime_shift_le_of_eroded:
  fixes A :: "'b::{polish_space,banach} set"
  assumes T: "0 \<le> T" and rr: "0 \<le> r" "r \<le> T"
    and mem: "x + \<omega> r \<in> eroded \<delta> A"
    and near: "dist x y < \<delta>"
  shows "etime T A (\<lambda>s w. y + w s) \<omega> \<le> r"
proof -
  have "dist (x + \<omega> r) (y + \<omega> r) < \<delta>" using near by simp
  from eroded_shift[OF mem this] have inA: "y + \<omega> r \<in> A" .
  text \<open>The conclusion drives the unification here: chaining \<open>inA\<close> into the
    rule instead leaves \<open>?X r \<omega> \<in> A\<close> to be solved higher-order, with
    several solutions, so the step fails.\<close>
  show ?thesis
  proof (rule etime_le_of_mem)
    show "0 \<le> T" by (rule T)
    show "0 \<le> r" by (rule rr(1))
    show "r \<le> T" by (rule rr(2))
    show "y + \<omega> r \<in> A" by (rule inA)
  qed
qed

text \<open>From a witness time \<open>r\<close> carrying positive mass, extract an open set of
  paths, still of positive mass, on which the exit time stays below \<open>d\<close>
  for every nearby starting point; openness lets the measure-moving half
  of Berge's \<open>box\<close> go through by Portmanteau.\<close>

lemma etime_shift_uniform_margin:
  fixes T d :: real and A :: "'b::{polish_space,banach} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and r: "0 \<le> r" "r \<le> T" "r < d"
    and pos: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
  shows "\<exists>\<delta>>0. \<exists>G. openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G
      \<and> emeasure P G \<noteq> 0
      \<and> (\<forall>y. dist x y < \<delta> \<longrightarrow> (\<forall>\<omega> \<in> G. etime T A (\<lambda>s w. y + w s) \<omega> < d))"
proof -
  have spP: "space P = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sP] by (simp add: space_borel_of)
  have rT: "r \<in> {0..T}" using r by simp
  have opn: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         x + f r \<in> eroded (1 / Suc n) A}" for n :: nat
    by (rule open_shifted_eval_preimage[OF rT open_eroded])
  have meas: "{\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A} \<in> sets P" for n :: nat
    using borel_of_open[OF opn[of n]] unfolding sP spP by simp
  obtain n :: nat where
    posn: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A} \<noteq> 0"
    by (rule positive_mass_at_some_erosion[OF A meas pos, THEN exE])
  define G where "G = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
      x + f r \<in> eroded (1 / Suc n) A}"
  have Gspace: "G = {\<omega> \<in> space P. x + \<omega> r \<in> eroded (1 / Suc n) A}"
    unfolding G_def spP by simp
  have "(0::real) < 1 / Suc n" by simp
  moreover have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G"
    unfolding G_def by (rule opn)
  moreover have "emeasure P G \<noteq> 0" unfolding Gspace by (rule posn)
  moreover have "etime T A (\<lambda>s w. y + w s) \<omega> < d"
    if near: "dist x y < 1 / Suc n" and \<omega>: "\<omega> \<in> G" for y \<omega>
  proof -
    have le: "etime T A (\<lambda>s w. y + w s) \<omega> \<le> r"
    proof (rule etime_shift_le_of_eroded)
      show "0 \<le> T" by (rule T)
      show "0 \<le> r" by (rule r(1))
      show "r \<le> T" by (rule r(2))
      show "x + \<omega> r \<in> eroded (1 / Suc n) A" using \<omega> unfolding G_def by simp
      show "dist x y < 1 / Suc n" by (rule near)
    qed
    from le r(3) show ?thesis by linarith
  qed
  ultimately show ?thesis by blast
qed

text \<open>Both halves of the \<open>x\<close>-perturbation in one statement: from
  \<open>f(x,P) < d\<close> alone, with no continuity of the pushforward map, there is
  an open set of paths of positive \<open>P\<close>-mass on which the exit time stays
  below \<open>d\<close> for every starting point within \<open>\<delta>\<close> of \<open>x\<close>.\<close>

theorem etime_shift_box_half:
  fixes T d :: real and A :: "'b::{polish_space,banach} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pos: "emeasure P
        {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "\<exists>\<delta>>0. \<exists>G. openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G
      \<and> emeasure P G \<noteq> 0
      \<and> (\<forall>y. dist x y < \<delta> \<longrightarrow> (\<forall>\<omega> \<in> G. etime T A (\<lambda>s w. y + w s) \<omega> < d))"
proof -
  obtain r where r: "r \<in> qtimes T" "r < d"
    and posr: "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
    using positive_mass_at_some_qtime[OF T A dT sP pos] by blast
  have rT: "r \<in> {0..T}" using qtimes_subset[OF T] r(1) by blast
  show ?thesis
  proof (rule etime_shift_uniform_margin[OF T A sP])
    show "0 \<le> r" using rT by simp
    show "r \<le> T" using rT by simp
    show "r < d" by (rule r(2))
    show "emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0" by (rule posr)
  qed
qed

subsubsection \<open>Berge's box hypothesis for the shifted exit time\<close>

text \<open>
  Both perturbations at once, in the sequential form Levy--Prokhorov
  metrisation makes equivalent to the topological one: \<open>f(x,P) < d\<close>
  persists when the starting point moves to any \<open>y\<^sub>i \<rightarrow> x\<close> and the law
  moves to any \<open>Q\<^sub>i \<rightarrow> P\<close> weakly.

  Larsson--Ruf get this from continuity of \<open>(x,P) \<mapsto> (x + \<cdot>)\<^sub>*P\<close>; no
  such theorem is used here. A single open set \<open>G\<close> does all the work --- the
  erosion makes it survive moving \<open>x\<close>, its openness makes it survive
  moving \<open>P\<close> --- and must be open rather than closed, since a closed eroded
  set would give the wrong Portmanteau direction.
\<close>

text \<open>The countable decomposition of \<open>positive_mass_at_some_qtime\<close>, used for
  measurability rather than for extraction:
  the event \<open>{\<tau>\<^sub>K(y + \<cdot>) < d}\<close> is a countable union of open sets, hence open, hence
  Borel; the final monotonicity step below needs this set to be Borel.\<close>

theorem etime_shift_box:
  fixes T d :: real and A :: "'b::{polish_space,banach} set"
    and P :: "(real \<Rightarrow> 'b) measure" and Qi :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
    and x :: 'b and yi :: "nat \<Rightarrow> 'b"
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and wc: "weak_conv_on Qi P sequentially
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and sQ: "\<And>i. sets (Qi i) = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pQ: "\<And>i. prob_space (Qi i)" and pP: "prob_space P"
    and yconv: "yi \<longlonglongrightarrow> x"
    and pos: "emeasure P {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "eventually (\<lambda>i. emeasure (Qi i)
      {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0) sequentially"
proof -
  interpret PP: prob_space P by (rule pP)
  have sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    using wc[unfolded weak_conv_on_def] by blast
  obtain \<delta> G where d0: "0 < \<delta>"
    and Gopen: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)) G"
    and Gpos: "emeasure P G \<noteq> 0"
    and marg: "\<And>y \<omega>. dist x y < \<delta> \<Longrightarrow> \<omega> \<in> G
        \<Longrightarrow> etime T A (\<lambda>s w. y + w s) \<omega> < d"
    using etime_shift_box_half[OF T A dT sP pos] by blast
  have GP: "0 < measure P G"
  proof (rule ccontr)
    assume "\<not> 0 < measure P G"
    hence "measure P G = 0" using measure_nonneg[of P G] by linarith
    hence "ennreal (measure P G) = 0" by simp
    thus False using Gpos PP.emeasure_eq_measure by simp
  qed
  have ev1: "eventually (\<lambda>i. 0 < measure (Qi i) G) sequentially"
    by (rule weak_conv_open_positive_eventually[OF wc Gopen GP sQ pQ pP])
  have ev2: "eventually (\<lambda>i. dist x (yi i) < \<delta>) sequentially"
    using tendstoD[OF yconv d0] by (simp add: dist_commute)
  show ?thesis
  proof (rule eventually_mono[OF eventually_conj[OF ev1 ev2]])
    fix i
    assume h: "0 < measure (Qi i) G \<and> dist x (yi i) < \<delta>"
    interpret QQ: prob_space "Qi i" by (rule pQ)
    have spQ: "space (Qi i) = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using sets_eq_imp_space_eq[OF sQ[of i]] by (simp add: space_borel_of)
    have Gsub: "G \<subseteq> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
      using openin_subset[OF Gopen] by simp
    have sub: "G \<subseteq> {\<omega> \<in> space (Qi i).
        etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
    proof
      fix \<omega> assume w: "\<omega> \<in> G"
      have "etime T A (\<lambda>s w. yi i + w s) \<omega> < d"
        using marg[OF _ w] h by simp
      thus "\<omega> \<in> {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
        using w Gsub spQ by auto
    qed
    have meas: "{\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d}
        \<in> sets (Qi i)"
      using borel_of_open[OF open_etime_shift_less[OF T A dT]]
      unfolding sQ spQ by simp
    have "emeasure (Qi i) G \<noteq> 0"
      using h QQ.emeasure_eq_measure by simp
    moreover have "emeasure (Qi i) G
        \<le> emeasure (Qi i) {\<omega> \<in> space (Qi i).
             etime T A (\<lambda>s w. yi i + w s) \<omega> < d}"
      by (rule emeasure_mono[OF sub meas])
    ultimately show "emeasure (Qi i) {\<omega> \<in> space (Qi i).
        etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0" by auto
  qed
qed

subsubsection \<open>Upper semicontinuity of the supremum over a compact family\<close>

text \<open>
  The supremum of \<open>P \<mapsto> P\<hyphen>essinf \<tau>\<^sub>K(x + \<cdot>)\<close> over a weakly compact family
  of laws is upper semicontinuous in the starting point \<open>x\<close>. Every
  hypothesis of Berge's theorem except the compactness of the family is
  discharged here.
\<close>

theorem vshift_sup_usc:
  fixes T c :: real and A :: "'b::{polish_space,banach} set"
    and C :: "(real \<Rightarrow> 'b) measure set" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A"
    and cC: "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    and neC: "C \<noteq> {}"
    and sC: "\<And>Q. Q \<in> C \<Longrightarrow> sets Q = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pC: "\<And>Q. Q \<in> C \<Longrightarrow> prob_space Q"
    and lt: "Sup (vshift T A x ` C) < c"
  shows "eventually (\<lambda>y. Sup (vshift T A y ` C) < c) (nhds x)"
proof (rule usc_sup_over_compactin)
  show "compactin (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    by (rule cC)
  show "C \<noteq> {}" by (rule neC)
  show "bdd_above (vshift T A y ` C)" for y
    by (rule bdd_aboveI2[of _ _ T]) (use vshift_le[OF T] pC in blast)
  show "Sup (vshift T A x ` C) < c" by (rule lt)
next
  fix P :: "(real \<Rightarrow> 'b) measure" and d :: real
  assume P: "P \<in> C" and small: "vshift T A x P < d"
  have d0: "0 \<le> d"
  proof -
    have "0 \<le> vshift T A x P" unfolding vshift_def by simp
    with small show ?thesis by linarith
  qed
  show "\<exists>U V. open U \<and> openin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) V
      \<and> x \<in> U \<and> P \<in> V
      \<and> (\<forall>y \<in> U. \<forall>Q \<in> V \<inter> C. vshift T A y Q < d)"
  proof (cases "T < d")
    text \<open>Berge quantifies \<open>box\<close> over every threshold above \<open>vshift T A x P\<close>,
      including thresholds beyond \<open>T\<close> --- that branch is trivial since the
      exit time never exceeds \<open>T\<close>, so the whole space works, and is split
      off because the witness machinery above assumes \<open>\<not> T < d\<close>.\<close>
    case True
    have allQ: "vshift T A y Q < d" if "Q \<in> C" for y Q
    proof -
      have "vshift T A y Q \<le> T" by (rule vshift_le[OF T pC[OF that]])
      with True show ?thesis by linarith
    qed
    have oT: "openin (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        (topspace (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))))"
      by (rule openin_topspace)
    have Ptop: "P \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      using sC[OF P] prob_space.finite_measure[OF pC[OF P]] by simp
    text \<open>The witnesses \<open>U = UNIV\<close> and \<open>V = topspace\<close> must be handed over
      explicitly: left to invent them itself, \<open>blast\<close> does not terminate.\<close>
    have inst: "open (UNIV :: 'b set)
        \<and> openin (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
           (topspace (weak_conv_topology
              (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))))
        \<and> x \<in> (UNIV :: 'b set)
        \<and> P \<in> topspace (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))
        \<and> (\<forall>y \<in> (UNIV :: 'b set).
             \<forall>Q \<in> topspace (weak_conv_topology
                 (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) \<inter> C.
               vshift T A y Q < d)"
      using oT Ptop allQ by simp
    thus ?thesis by blast
  next
    case False
    hence dT: "\<not> T < d" by simp
    have posP: "emeasure P {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
      using small
      unfolding vshift_less_iff_positive_mass[OF T A dT d0 sC[OF P] pC[OF P]] .
    show ?thesis
    proof (rule box_of_sequential_euclidean)
      show "metrizable_space (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
        by (rule metrizable_weak_conv_path_topology)
      show "P \<in> topspace (weak_conv_topology
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
        using sC[OF P] prob_space.finite_measure[OF pC[OF P]] by simp
    next
      fix yi :: "nat \<Rightarrow> 'b" and Qi :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure"
      assume yconv: "yi \<longlonglongrightarrow> x"
        and lQ: "limitin (weak_conv_topology
            (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) Qi P sequentially"
        and inC: "\<And>i. Qi i \<in> C"
      text \<open>\<open>weak_conv_on\<close> is \<open>limitin (weak_conv_topology \<dots>)\<close> by definition.
        The membership \<open>Qi i \<in> C\<close> cannot be dropped: \<open>etime_shift_box\<close>
        needs each \<open>Qi i\<close> to be a probability measure, while an arbitrary
        measure near \<open>P\<close> in the weak topology is only finite.\<close>
      have wc: "weak_conv_on Qi P sequentially
          (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
        using lQ .
      have sQi: "sets (Qi i) = sets (path_borel T :: (real \<Rightarrow> 'b) measure)" for i
        by (rule sC[OF inC])
      have pQi: "prob_space (Qi i)" for i by (rule pC[OF inC])
      have ev: "eventually (\<lambda>i. emeasure (Qi i)
          {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0) sequentially"
        by (rule etime_shift_box[OF T A dT wc sQi pQi pC[OF P] yconv posP])
      show "eventually (\<lambda>i. vshift T A (yi i) (Qi i) < d) sequentially"
      proof (rule eventually_mono[OF ev])
        fix i
        assume "emeasure (Qi i)
            {\<omega> \<in> space (Qi i). etime T A (\<lambda>s w. yi i + w s) \<omega> < d} \<noteq> 0"
        thus "vshift T A (yi i) (Qi i) < d"
          unfolding vshift_less_iff_positive_mass[OF T A dT d0
              sC[OF inC] pC[OF inC]] .
      qed
    qed
  qed
qed

text \<open>
  The same with compactness replaced by its sequential form, the one
  obligation a user discharges: every sequence in \<open>\<P>\<^sub>0\<close> has a
  subsequence converging weakly to a member of \<open>\<P>\<^sub>0\<close> --- the \<open>seq\<close>
  hypothesis below, and nothing else about \<open>\<P>\<^sub>0\<close> is used.
\<close>

corollary vshift_sup_usc_of_seq_compact:
  fixes T c :: real and A :: "'b::{polish_space,banach} set"
    and C :: "(real \<Rightarrow> 'b) measure set" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and neC: "C \<noteq> {}"
    and sC: "\<And>Q. Q \<in> C \<Longrightarrow> sets Q = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pC: "\<And>Q. Q \<in> C \<Longrightarrow> prob_space Q"
    and seq: "\<And>\<sigma> :: nat \<Rightarrow> (real \<Rightarrow> 'b) measure. range \<sigma> \<subseteq> C \<Longrightarrow>
        \<exists>L r. L \<in> C \<and> strict_mono r \<and> weak_conv_on (\<sigma> \<circ> r) L sequentially
              (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and lt: "Sup (vshift T A x ` C) < c"
  shows "eventually (\<lambda>y. Sup (vshift T A y ` C) < c) (nhds x)"
proof -
  have sub: "C \<subseteq> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
  proof
    fix Q assume Q: "Q \<in> C"
    show "Q \<in> topspace (weak_conv_topology
        (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)))"
      using sC[OF Q] prob_space.finite_measure[OF pC[OF Q]] by simp
  qed
  have cC: "compactin (weak_conv_topology
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))) C"
    by (rule compactin_of_seq_compact[OF metrizable_weak_conv_path_topology sub])
       (use seq in blast)
  show ?thesis by (rule vshift_sup_usc[OF T A cC neC sC pC lt])
qed

(*<*)
end
(*>*)
