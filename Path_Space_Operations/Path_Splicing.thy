section \<open>Cutting, glueing, shifting and delaying a path\<close>

(*<*)
theory Path_Splicing
  imports
    "Continuous_Time_Martingales.Semidirect_Kernels" Pair_Path_Laws
begin

(*>*)

text \<open>The surgery: \<open>pcut\<close> truncates at a time, \<open>pglue\<close> concatenates two
  paths at a time with the increment carried over, \<open>pshift\<close> re-bases,
  \<open>padd\<close> adds a future to a past, \<open>pdel\<close> delays, \<open>pembed\<close> and \<open>prebase\<close>
  move between horizons, and \<open>pfut\<close> reads the future.  Each is a one-line
  definition on functions; what takes room is that each is continuous where
  it should be and measurable for the Borel algebra of the path metric.\<close>

definition pfut :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pfut r T \<omega> = restrict (\<lambda>s. \<omega> (r + s) - \<omega> r) {0..T - r}"

text \<open>The conditioning-free half of the closure the weak DPP needs: a
  member on \<open>[0,T]\<close> restricted to \<open>[0,S]\<close> is a member on \<open>[0,S]\<close>.  Both
  martingale clauses follow from \<open>martingale_process_law\<close> with the restriction
  as path map, adapted for free since \<open>pcut S \<omega> r = \<omega> r\<close> on \<open>{0..S}\<close>, and
  \<open>martingale_stopped_const\<close> turns the \<open>T\<close>-clause into the \<open>S\<close>-clause.\<close>

definition pcut :: "real \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pcut S \<omega> = restrict \<omega> {0..S}"

text \<open>Every member started at \<open>x\<close> is the \<open>x\<close>-translate of a member started
  at \<open>0\<close>.  This turns the value function into a supremum over a fixed
  family, the shape Berge's theorem needs.  The translation must
  \<open>restrict\<close>, because points of the capped path space are extensional on
  \<open>{0..T}\<close>.\<close>

definition pshift :: "real \<Rightarrow> 'a::{polish_space,banach} \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b::{polish_space,banach}) \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b)"
  where "pshift T x \<omega> = restrict (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t))) {0..T}"

lemma pfut_apply: "s \<in> {0..T - r} \<Longrightarrow> pfut r T \<omega> s = \<omega> (r + s) - \<omega> r"
  by (simp add: pfut_def)

text \<open>Reassembly of the split is addition, so the kernel is pushed
  through the glue map \<^term>\<open>padd T p' w\<close>, not \<open>pglue\<close>.  It is defined
  on the same pair of \<open>T\<close>-path spaces the r.c.d. lives on, and needs no
  \<open>\<theta>\<close> --- the reason the additive split was chosen over freeze-and-rebase.

  The facts below form the foundation layer: the glue lands in the path
  space and is measurable as a map out of the product; given that the
  continuation stands still until \<open>\<theta>\<close>, stopping the glued path returns
  the stopped factor (\<open>pstopped_padd\<close>).\<close>

definition padd :: "real \<Rightarrow> (real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "padd T p' w = restrict (\<lambda>t. p' t + w t) {0..T}"

lemma pcut_apply: "r \<in> {0..S} \<Longrightarrow> pcut S \<omega> r = \<omega> r"
  by (simp add: pcut_def)

lemma pshift_apply: "t \<in> {0..T} \<Longrightarrow> pshift T x \<omega> t = (x + fst (\<omega> t), snd (\<omega> t))"
  by (simp add: pshift_def)

lemma pfut_zero: "0 \<le> T - r \<Longrightarrow> pfut r T \<omega> 0 = 0"
  by (simp add: pfut_def)

lemma padd_apply: "t \<in> {0..T} \<Longrightarrow> padd T p' w t = p' t + w t"
  by (simp add: padd_def)

lemma pcut_measurable:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
  shows "pcut S \<in> Q \<rightarrow>\<^sub>M (path_borel S :: (real \<Rightarrow> 'p) measure)"
proof -
  have "(\<lambda>f :: (real \<Rightarrow> 'p). restrict f {0..S})
      \<in> (path_borel T :: (real \<Rightarrow> 'p) measure)
        \<rightarrow>\<^sub>M (path_borel S :: (real \<Rightarrow> 'p) measure)"
    by (rule restrict_measurable_path_borel[OF S ST])
  then show ?thesis
    unfolding pcut_def using measurable_cong_sets[OF setsQ refl] by blast
qed

lemma pshift_fst: "t \<in> {0..T} \<Longrightarrow> fst (pshift T x \<omega> t) = x + fst (\<omega> t)"
  by (simp add: pshift_def)

lemma pfut_fst:
  "s \<in> {0..T - r} \<Longrightarrow> fst (pfut r T \<omega> s) = fst (\<omega> (r + s)) - fst (\<omega> r)"
  by (simp add: pfut_def)

lemma pshift_snd: "t \<in> {0..T} \<Longrightarrow> snd (pshift T x \<omega> t) = snd (\<omega> t)"
  by (simp add: pshift_def)

lemma padd_mspace:
  fixes p' w :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes p: "p' \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    and w: "w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "padd T p' w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
proof -
  have "continuous_on {0..T} (\<lambda>t. p' t + w t)"
    using mspace_path_metricD[OF p] mspace_path_metricD[OF w]
    by (intro continuous_intros)
  then show ?thesis unfolding padd_def by (rule mspace_path_metricI)
qed

text \<open>The glue with the past fixed: the form the four-cell argument needs,
  since there the continuation is only frozen almost surely, so the
  integrand identities transport via
  \<open>Bochner_Integration.integral_cong_AE\<close> rather than
  pointwise, which needs both sides measurable in \<open>w\<close> alone.\<close>

lemma pfut_in_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "pfut r T \<omega> \<in> mspace (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)"
proof -
  have cw: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have sub: "(\<lambda>s. r + s) ` {0..T - r} \<subseteq> {0..T}" using r rT by auto
  have c1: "continuous_on {0..T - r} (\<lambda>s. \<omega> (r + s))"
    by (rule continuous_on_compose2[OF cw _ sub]) (intro continuous_intros)
  have "continuous_on {0..T - r} (\<lambda>s. \<omega> (r + s) - \<omega> r)"
    by (intro continuous_on_diff c1 continuous_on_const)
  then show ?thesis unfolding pfut_def by (rule mspace_path_metricI)
qed

lemma pshift_outside: "t \<notin> {0..T} \<Longrightarrow> pshift T x \<omega> t = undefined"
  by (auto simp: pshift_def)

lemma pshift_in_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pshift T x \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have "continuous_on {0..T} (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t)))"
    by (intro continuous_intros c)
  then show ?thesis unfolding pshift_def by (rule mspace_path_metricI)
qed

lemma pcut_adapted:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes S: "0 \<le> S" and r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). pcut S \<omega> r) \<in> borel_measurable
      (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<in> {0..S}")
  case True
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). \<omega> r) \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M borel"
    by (rule natural_filtration_eval) (use r ru in auto)
  then show ?thesis using True by (simp add: pcut_apply)
next
  case False
  then have "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). pcut S \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: pcut_def)
  then show ?thesis by simp
qed

text \<open>The rational reduction of the covariation clause, factored out since
  it recurs in every construction of a class member: countably many pairs
  by \<open>AE_ball_countable'\<close>, then \<open>diffquot_all_of_rational\<close> against path
  continuity.\<close>

lemma Lipschitz_pfut:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: (real \<Rightarrow> 'p::{polish_space,banach}) metric)
      (path_metric (T - r) :: (real \<Rightarrow> 'p) metric) (pfut r T)"
proof (rule Lipschitz_path_mapI[OF _ pfut_in_mspace[OF r rT], where B = 2])
  show "0 \<le> T - r" using rT by simp
  fix f g :: "real \<Rightarrow> 'p" and s :: real
  assume f: "f \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    and g: "g \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    and s: "s \<in> {0..T - r}"
  have rs: "r + s \<in> {0..T}" and r0: "r \<in> {0..T}" using s r rT by auto
  have "dist (pfut r T f s) (pfut r T g s) = dist (f (r + s) - f r) (g (r + s) - g r)"
    using s by (simp add: pfut_apply)
  also have "\<dots> = norm ((f (r + s) - g (r + s)) - (f r - g r))"
    by (simp add: dist_norm algebra_simps)
  also have "\<dots> \<le> dist (f (r + s)) (g (r + s)) + dist (f r) (g r)"
    unfolding dist_norm by (rule norm_triangle_ineq4)
  finally show "dist (pfut r T f s) (pfut r T g s) \<le> 2 * mdist (path_metric T) f g"
    using path_dist_le_mdist[OF f g rs] path_dist_le_mdist[OF f g r0] by linarith
qed

lemma pshift_zero:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pshift T 0 \<omega> = \<omega>"
proof -
  have "pshift T 0 \<omega> = restrict \<omega> {0..T}"
    unfolding pshift_def by simp
  also have "\<dots> = \<omega>" by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

lemma padd_measurable_left:
  fixes p' :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes T0: "0 \<le> T"
    and p: "p' \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "(\<lambda>w. padd T p' w)
      \<in> (path_borel T :: (real \<Rightarrow> 'p) measure)
      \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  have into: "padd T p' w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    if "w \<in> space ?B" for w
    using that p by (auto simp: space_borel_of intro: padd_mspace)
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'p). padd T p' w t) \<in> borel_measurable ?B"
    if True: "t \<in> {0..T}" for t
  proof -
    have "(\<lambda>w :: (real \<Rightarrow> 'p). p' t + w t) \<in> borel_measurable ?B"
      by (intro borel_measurable_add borel_measurable_const
          path_law_evaluation_measurable[OF refl])
    then show ?thesis by (simp add: padd_apply[OF True])
  qed
  show ?thesis by (rule path_measurable_of_eval[OF T0 into ev])
qed

lemma pshift_pshift:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  shows "pshift T y (pshift T x \<omega>) = pshift T (y + x) \<omega>"
  by (rule ext) (simp add: pshift_def add.assoc)

lemma pshift_inverse:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pshift T (- x) (pshift T x \<omega>) = \<omega>"
  using pshift_pshift[of T "- x" x \<omega>] pshift_zero[OF w] by simp

lemma ipcut_measurable:
  fixes P :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes S: "0 \<le> S"
    and setsP: "sets P = sets (ipath_space :: (real \<Rightarrow> 'p) measure)"
  shows "pcut S \<in> P \<rightarrow>\<^sub>M (path_borel S :: (real \<Rightarrow> 'p) measure)"
  unfolding pcut_def measurable_cong_sets[OF setsP refl]
  by (rule restrict_ipath_measurable[OF S])

lemma Lipschitz_pshift:
  fixes x :: "'a::{polish_space,banach}"
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})) metric)
      (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric) (pshift T x)"
proof (rule Lipschitz_path_mapI[OF T pshift_in_mspace, where B = 1])
  fix f g :: "real \<Rightarrow> 'a \<times> 'b" and t :: real
  assume f: "f \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and g: "g \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and t: "t \<in> {0..T}"
  have "dist (pshift T x f t) (pshift T x g t)
      = dist (x + fst (f t), snd (f t)) (x + fst (g t), snd (g t))"
    using t by (simp add: pshift_def)
  also have "\<dots> = dist (f t) (g t)"
    by (simp add: dist_prod_def dist_norm)
  finally show "dist (pshift T x f t) (pshift T x g t) \<le> 1 * mdist (path_metric T) f g"
    using path_dist_le_mdist[OF f g t] by simp
qed

lemma padd_measurable:
  fixes T :: real
  assumes T0: "0 \<le> T"
  shows "(\<lambda>p. padd T (fst p) (snd p))
      \<in> (path_borel T :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
        \<Otimes>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)
      \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  let ?M = "?B \<Otimes>\<^sub>M ?B"
  let ?f = "\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). padd T (fst p) (snd p)"
  have spB: "space ?B = mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    by (simp add: space_borel_of)
  have into: "?f p \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    if p: "p \<in> space ?M" for p
  proof -
    have "fst p \<in> space ?B" and "snd p \<in> space ?B"
      using p by (auto simp: space_pair_measure)
    then show ?thesis using spB by (auto intro: padd_mspace)
  qed
  have ev: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). ?f p t) \<in> borel_measurable ?M"
    if True: "t \<in> {0..T}" for t
  proof -
    have e1: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). fst p t) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_fst
            path_law_evaluation_measurable[OF refl]])
    have e2: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). snd p t) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd
            path_law_evaluation_measurable[OF refl]])
    have "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). fst p t + snd p t)
        \<in> borel_measurable ?M"
      using e1 e2 by simp
    then show ?thesis by (simp add: padd_apply[OF True])
  qed
  show ?thesis by (rule path_measurable_of_eval[OF T0 into ev])
qed

text \<open>The split inverts the glue, provided the continuation stands still up
  to \<open>\<theta>\<close> --- which is exactly clause (ii) of the kernel's membership in the
  class.  The stopping time reads only the stopped factor, because on
  \<open>[0, \<theta> p']\<close> the glue agrees with it.\<close>

lemma pfut_measurable:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "pfut r T
      \<in> (path_borel T :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
        \<rightarrow>\<^sub>M (path_borel (T - r) :: (real \<Rightarrow> 'p) measure)"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pfut[OF r rT])

lemma pfut_measurable_law:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
  shows "pfut r T \<in> Q \<rightarrow>\<^sub>M (path_borel (T - r) :: (real \<Rightarrow> 'p) measure)"
  using pfut_measurable[OF r rT] measurable_cong_sets[OF setsQ refl] by blast

text \<open>The exit time of the future, expressed through \<open>pfut\<close>: re-basing at the
  endpoint and adding the endpoint back is the identity on the exit time.\<close>

text \<open>Conditioning on an event of the past keeps martingales martingales:
  \<open>uniform_measure_density_real\<close>, \<open>integral_uniform_measure_eq\<close>,
  \<open>integrable_uniform_measureI\<close>, \<open>set_integral_uniform_measure_eq\<close> and
  \<open>martingale_uniform_measure\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

text \<open>\<open>pair_fst_borel\<close> lives in @{theory Path_Space_Operations.Pair_Path_Laws}.\<close>

lemma pshift_measurable:
  fixes x :: "'a::{polish_space,banach}"
  assumes T: "0 \<le> T"
  shows "pshift T x
      \<in> (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})) measure)
        \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pshift[OF T])

text \<open>The shift is measurable for the natural filtration too, at every
  level: it changes values, not times.  This is what lets the martingale
  clauses be transported --- the past of the shifted path is the shifted
  past.\<close>

lemma pshift_filtration_measurable:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure" and x :: "'a"
  assumes setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "pshift T x \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> v) u"
  have spQ: "space Q = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spF: "space ?F = space Q" by simp
  show ?thesis
  proof (rule measurable_sigma_sets[OF sets_natural_filtration])
    show "(\<Union>i\<in>{0..u}. {(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})
        \<subseteq> Pow (space Q)"
      by auto
    show "pshift T x \<in> space ?F \<rightarrow> space Q"
      using spQ spF by (auto intro: pshift_in_mspace)
    fix y
    assume "y \<in> (\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})"
    then obtain i A where i: "i \<in> {0..u}" and A: "A \<in> sets borel"
      and y: "y = (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` A \<inter> space Q" by blast
    have shim: "pshift T x \<omega> \<in> space Q" if "\<omega> \<in> space Q" for \<omega>
      using that spQ by (simp add: pshift_in_mspace)
    show "pshift T x -` y \<inter> space ?F \<in> sets ?F"
    proof (cases "i \<in> {0..T}")
      case True
      define g where "g = (\<lambda>p :: 'a \<times> 'b. (x + fst p, snd p))"
      have gb: "g \<in> borel_measurable borel"
        unfolding g_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have gA: "g -` A \<in> sets borel"
        using measurable_sets[OF gb A] by simp
      have "pshift T x -` y \<inter> space ?F
          = (\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` (g -` A) \<inter> space Q"
        using True y spF shim by (auto simp: pshift_apply g_def)
      moreover have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> i) -` (g -` A) \<inter> space Q \<in> sets ?F"
        unfolding sets_natural_filtration
        by (rule sigma_sets.Basic)
          (use i gA in \<open>auto intro!: bexI[of _ i] exI[of _ "g -` A"]\<close>)
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "undefined \<in> A")
        case inA: True
        have "pshift T x -` y \<inter> space ?F = space ?F"
        proof
          show "pshift T x -` y \<inter> space ?F \<subseteq> space ?F" by blast
          show "space ?F \<subseteq> pshift T x -` y \<inter> space ?F"
          proof
            fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" assume w: "\<omega> \<in> space ?F"
            then have wq: "\<omega> \<in> space Q" using spF by simp
            have "pshift T x \<omega> i = undefined"
              by (rule pshift_outside[OF False])
            then show "\<omega> \<in> pshift T x -` y \<inter> space ?F"
              using inA w shim[OF wq] spF y by auto
          qed
        qed
        then show ?thesis using sets.top[of ?F] by simp
      next
        case notinA: False
        have "pshift T x -` y \<inter> space ?F = {}"
        proof (rule ccontr)
          assume "pshift T x -` y \<inter> space ?F \<noteq> {}"
          then obtain \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" where "pshift T x \<omega> \<in> y" by blast
          then have "pshift T x \<omega> i \<in> A" using y by blast
          moreover have "pshift T x \<omega> i = undefined"
            by (rule pshift_outside[OF False])
          ultimately show False using notinA by simp
        qed
        then show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>The shifted law\<close>

lemma padd_fst_continuous:
  fixes p' w :: "real \<Rightarrow> 'a::topological_ab_group_add \<times> 'b::ab_group_add"
  assumes cp: "continuous_on {0..T} (\<lambda>t. fst (p' t))"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (w t))"
  shows "continuous_on {0..T} (\<lambda>t. fst (padd T p' w t))"
proof (rule continuous_on_eq[OF continuous_on_add[OF cp cw]])
  fix t :: real assume t: "t \<in> {0..T}"
  show "fst (p' t) + fst (w t) = fst (padd T p' w t)"
    by (simp add: padd_apply[OF t])
qed

lemma mdist_pshift_pshift:
  fixes z y :: "'a::{polish_space,banach}"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})) metric)"
  shows "mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
      (pshift T z \<omega>) (pshift T y \<omega>) \<le> dist z y"
proof -
  have sz: "pshift T z \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule pshift_in_mspace[OF w])
  have sy: "pshift T y \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule pshift_in_mspace[OF w])
  have pw: "dist (pshift T z \<omega> t) (pshift T y \<omega> t) \<le> dist z y" if t: "t \<in> {0..T}" for t
  proof -
    have "dist (pshift T z \<omega> t) (pshift T y \<omega> t)
        = dist (z + fst (\<omega> t), snd (\<omega> t)) (y + fst (\<omega> t), snd (\<omega> t))"
      using t by (simp add: pshift_apply)
    also have "\<dots> = dist (z + fst (\<omega> t)) (y + fst (\<omega> t))"
      by (simp add: dist_Pair_Pair)
    also have "\<dots> = dist z y" by (simp add: dist_norm)
    finally show ?thesis by simp
  qed
  show ?thesis using path_mdist_le_iff_all[OF T sz sy] pw by blast
qed

lemma pexit_pcut:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  shows "pexit U K (\<lambda>t. fst (pcut U \<omega> t)) = pexit U K (\<lambda>t. fst (\<omega> t))"
  by (rule pexit_cong_on) (simp add: pcut_apply)

definition pglue :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> (real \<Rightarrow> 'b)
    \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pglue r T \<omega> \<omega>' =
     restrict (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)) {0..T}"

lemma pexit_pshift:
  fixes y :: "'a::{polish_space,banach}" and \<omega> :: "(real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})"
  shows "pexit U K (\<lambda>t. fst (pshift U y \<omega> t)) = pexit U K (\<lambda>t. y + fst (\<omega> t))"
  by (rule pexit_cong_on) (simp add: pshift_fst)

lemma pglue_le: "t \<in> {0..T} \<Longrightarrow> t \<le> r \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> t"
  by (simp add: pglue_def)

lemma pcut_pglue:
  fixes \<omega> \<omega>' :: "real \<Rightarrow> 'b::ab_group_add"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "pcut r (pglue r T \<omega> \<omega>') = pcut r \<omega>"
proof (rule ext)
  fix t :: real
  show "pcut r (pglue r T \<omega> \<omega>') t = pcut r \<omega> t"
  proof (cases "t \<in> {0..r}")
    case True
    then have tT: "t \<in> {0..T}" using rT by auto
    have "pglue r T \<omega> \<omega>' t = \<omega> t" using True by (intro pglue_le[OF tT]) simp
    then show ?thesis using True by (simp add: pcut_def)
  next
    case False
    have "pcut r (pglue r T \<omega> \<omega>') t = undefined"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    moreover have "pcut r \<omega> t = undefined"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    ultimately show ?thesis by simp
  qed
qed

lemma pcut_pglue_self:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: (real \<Rightarrow> 'p) metric)"
  shows "pcut r (pglue r T \<omega> \<omega>') = \<omega>"
proof -
  have "pcut r (pglue r T \<omega> \<omega>') = pcut r \<omega>" by (rule pcut_pglue[OF r rT])
  also have "\<dots> = \<omega>" unfolding pcut_def by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

text \<open>The almost-sure transfer through a glue, with the underlying measure
  \<open>Q\<close> left free, so that unfolding \<open>process_law_def\<close> cannot
  also unfold a \<open>process_law\<close> hiding inside \<open>Q\<close> itself.\<close>

lemma padd_measurable_ksemi:
  fixes Q :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'p) measure)"
  shows "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)
      \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  have s: "sets (Q \<Otimes>\<^sub>M ?B) = sets (?B \<Otimes>\<^sub>M ?B)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  show ?thesis
    unfolding measurable_cong_sets[OF s refl] by (rule padd_measurable[OF T0])
qed

lemma pglue_ge:
  "t \<in> {0..T} \<Longrightarrow> r \<le> t \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  by (cases "t = r") (auto simp: pglue_def)

lemma pglue_zero: "0 \<le> r \<Longrightarrow> 0 \<le> T \<Longrightarrow> pglue r T \<omega> \<omega>' 0 = \<omega> 0"
  by (rule pglue_le) auto

lemma pglue_in_mspace:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: (real \<Rightarrow> 'p) metric)"
    and w': "\<omega>' \<in> mspace (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)"
  shows "pglue r T \<omega> \<omega>' \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  unfolding pglue_def
  by (rule mspace_path_metricI[OF continuous_on_pglue[OF r rT
        mspace_path_metricD[OF w] mspace_path_metricD[OF w']]])

lemma pglue_measurable:
  fixes Q R :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: (real \<Rightarrow> 'p) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: (real \<Rightarrow> 'p) measure))"
  shows "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M
      (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          path_law_evaluation_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_snd
          path_law_evaluation_measurable[OF setsR]])
  have Xm: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p).
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" for t
    using eQ eR by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "(real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p)"
  proof (rule continuous_on_pglue[OF r rT])
    have "fst p \<in> space Q" "snd p \<in> space R"
      using p by (auto simp: space_pair_measure)
    then show "continuous_on {0..r} (fst p)" "continuous_on {0..T - r} (snd p)"
      using space_of_path_sets[OF setsQ] space_of_path_sets[OF setsR]
      by (auto intro: mspace_path_metricD)
  qed
  show ?thesis
    using pathify_measurable[OF T0 Xm cont] unfolding pglue_def by simp
qed

text \<open>The eigenvalue constraint (1.7) survives concatenation: across the
  glue point the difference quotient is a convex combination of one
  quotient from each piece, which is why the constraint set had to be
  convexified (Lemma 2.1, \<open>sconstraint_convex\<close>) --- the unconvexified set
  of (1.4) would not do.\<close>

subsection \<open>Gluing a continuation onto the half-line\<close>

text \<open>The half-line analogue of \<open>pglue\<close>.  Cutting it at any horizon
  beyond the glue point returns the compact glue, so the finite-horizon
  theory applies to every restriction of an extension without further
  work.\<close>

definition iglue :: "real \<Rightarrow> (real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "iglue r \<omega> \<omega>' =
     restrict (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)) {0..}"

lemma pcut_iglue:
  fixes \<omega> \<omega>' :: "real \<Rightarrow> 'b::ab_group_add"
  assumes S: "0 \<le> S"
  shows "pcut S (iglue r \<omega> \<omega>') = pglue r S \<omega> \<omega>'"
  by (rule ext) (auto simp: pcut_def iglue_def pglue_def)

lemma pdel_clamp_lo: "0 \<le> max 0 (min (s::real) (T::real))"
  by (rule max.cobounded1)

lemma pdel_clamp_hi:
  fixes s T :: real
  assumes "0 \<le> T" shows "max 0 (min s T) \<le> T"
  using assms by (intro max.boundedI) auto

lemma pglue_pcut:
  fixes \<omega> \<omega>' :: "real \<Rightarrow> 'b::ab_group_add"
  assumes r: "0 \<le> r" and rS: "r \<le> S"
  shows "pglue r S \<omega> (pcut (S - r) \<omega>') = pglue r S \<omega> \<omega>'"
  using r rS by (auto simp: pglue_def pcut_def)

lemma pglue_self:
  fixes \<omega> \<omega>' :: "real \<Rightarrow> 'b::ab_group_add"
  shows "pglue r r \<omega> \<omega>' = pcut r \<omega>"
  by (rule ext) (auto simp: pglue_def pcut_def)

lemma iglue_measurable:
  fixes Q R :: "(real \<Rightarrow> 'p::{polish_space,banach}) measure"
  assumes r: "0 \<le> r"
    and setsQ: "sets Q = sets (path_borel r :: (real \<Rightarrow> 'p) measure)"
    and setsR: "sets R = sets (ipath_space :: (real \<Rightarrow> 'p) measure)"
  shows "(\<lambda>p. iglue r (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M ipath_space"
proof -
  have eQ: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          path_law_evaluation_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    if v: "0 \<le> v" for v
  proof -
    have "(\<lambda>f :: (real \<Rightarrow> 'p). f v) \<in> borel_measurable R"
      unfolding measurable_cong_sets[OF setsR refl]
      by (rule ipath_eval_measurable[OF v])
    then show ?thesis by (rule measurable_compose[OF measurable_snd])
  qed
  have Xm: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p).
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" if t: "0 \<le> t" for t
  proof (cases "t \<le> r")
    case True
    then show ?thesis using eQ by simp
  next
    case False
    have m2: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). snd p (t - r))
        \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" using False by (intro eR) simp
    have m3: "(\<lambda>p :: (real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p). snd p 0)
        \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" by (rule eR) simp
    show ?thesis unfolding if_not_P[OF False]
      by (intro borel_measurable_add borel_measurable_diff eQ m2 m3)
  qed
  have cont: "continuous_on {0..} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "(real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p)"
  proof (rule continuous_on_iglue[OF r])
    have "fst p \<in> space Q" "snd p \<in> space R"
      using p by (auto simp: space_pair_measure)
    moreover have "space R = ipath" using setsR
      by (metis sets_eq_imp_space_eq space_ipath_space)
    ultimately show "continuous_on {0..r} (fst p)" "continuous_on {0..} (snd p)"
      using space_of_path_sets[OF setsQ]
      by (auto intro: mspace_path_metricD ipath_continuous_on)
  qed
  show ?thesis
    using ipathify_measurable[OF Xm cont] unfolding iglue_def by simp
qed

lemma pcut_padd_before:
  fixes p' w :: "real \<Rightarrow> 'b::ab_group_add"
  assumes i0: "0 \<le> i" and iT: "i \<le> T"
    and w0: "\<And>u. u \<in> {0..T} \<Longrightarrow> u \<le> r \<Longrightarrow> w u = 0"
    and lt: "i < r"
  shows "pcut i (padd T p' w) = pcut i p'"
proof (rule ext)
  fix s :: real
  show "pcut i (padd T p' w) s = pcut i p' s"
  proof (cases "s \<in> {0..i}")
    case True
    then have sT: "s \<in> {0..T}" using iT by auto
    have "w s = 0" by (rule w0[OF sT]) (use True lt in simp)
    then show ?thesis
      unfolding pcut_apply[OF True] padd_apply[OF sT] by simp
  next
    case False
    have out: "pcut i v s = undefined" for v :: "real \<Rightarrow> 'b"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    show ?thesis unfolding out ..
  qed
qed

lemma pcut_padd_section:
  fixes p' w :: "real \<Rightarrow> 'b::ab_group_add"
  assumes i0: "0 \<le> i" and iT: "i \<le> T"
  shows "pcut i (padd T p' w) = padd i (pcut i p') (pcut i w)"
proof (rule ext)
  fix s :: real
  show "pcut i (padd T p' w) s = padd i (pcut i p') (pcut i w) s"
  proof (cases "s \<in> {0..i}")
    case True
    then have sT: "s \<in> {0..T}" using iT by auto
    show ?thesis
      unfolding pcut_apply[OF True] padd_apply[OF sT] padd_apply[OF True]
        pcut_apply[OF True] ..
  next
    case False
    have out1: "pcut i v s = undefined" for v :: "real \<Rightarrow> 'b"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    have out2: "padd i a b s = undefined" for a b :: "real \<Rightarrow> 'b"
      unfolding padd_def restrict_def by (rule if_not_P[OF False])
    show ?thesis unfolding out1 out2 ..
  qed
qed

text \<open>Assembled: clauses (i)--(iii) are discharged from the lemmas above;
  the two martingale clauses are the remaining input, resting on the two
  collapses above.\<close>

lemma pshift_pcut_comm:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes S0: "0 \<le> S" and ST: "S \<le> T"
  shows "pshift S y (pcut S \<omega>) = pcut S (pshift T y \<omega>)"
proof (rule ext)
  fix t :: real
  show "pshift S y (pcut S \<omega>) t = pcut S (pshift T y \<omega>) t"
  proof (cases "t \<in> {0..S}")
    case True
    then have tT: "t \<in> {0..T}" using ST by auto
    have "pshift S y (pcut S \<omega>) t = (y + fst (pcut S \<omega> t), snd (pcut S \<omega> t))"
      by (rule pshift_apply[OF True])
    also have "\<dots> = (y + fst (\<omega> t), snd (\<omega> t))" by (simp add: pcut_apply[OF True])
    also have "\<dots> = pshift T y \<omega> t" by (rule pshift_apply[OF tT, symmetric])
    also have "\<dots> = pcut S (pshift T y \<omega>) t" by (rule pcut_apply[OF True, symmetric])
    finally show ?thesis .
  next
    case False
    have "pshift S y (pcut S \<omega>) t = undefined" by (rule pshift_outside[OF False])
    moreover have "pcut S (pshift T y \<omega>) t = undefined"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    ultimately show ?thesis by simp
  qed
qed

definition pfst :: "real \<Rightarrow> (real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach}) \<Rightarrow> (real \<Rightarrow> 'a)"
  where "pfst S \<omega> = restrict (\<lambda>t. fst (\<omega> t)) {0..S}"

text \<open>The pointwise half of Larsson--Ruf's Proposition 2.2(ii): the class
  is sequentially compact and the essential infimum of the exit time is
  upper semicontinuous along weak convergence, so the supremum defining
  \<open>exit_val\<close> is a maximum --- needed independently of the DPP, since the
  paper's Section 3.1 opens by fixing an optimizer.

  The usc input (\<open>"Continuous_Path_Spaces.Path_Exit_Times".ess_inf_pexit_usc\<close>) lives on the
  vector path space, so the functional is transported along the
  \<open>X\<close>-component map \<open>pfst\<close>, \<open>1\<close>-Lipschitz between the two path metrics, and
  weak convergence pushes forward.\<close>

lemma pfst_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'a) metric)"
proof -
  have "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))" by (intro continuous_intros)
  then show ?thesis unfolding pfst_def by (rule mspace_path_metricI)
qed

lemma Lipschitz_pfst:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) metric)
      (path_metric T :: (real \<Rightarrow> 'a) metric) (pfst T)"
proof (rule Lipschitz_path_mapI[OF T pfst_mspace[OF T], where B = 1])
  fix \<omega> \<omega>' :: "real \<Rightarrow> 'a \<times> 'b" and t :: real
  assume w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and w': "\<omega>' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and t: "t \<in> {0..T}"
  have "dist (fst (\<omega> t)) (fst (\<omega>' t)) \<le> dist (\<omega> t) (\<omega>' t)"
    by (rule dist_fst_le)
  then show "dist (pfst T \<omega> t) (pfst T \<omega>' t)
      \<le> 1 * mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric) \<omega> \<omega>'"
    using path_dist_le_mdist[OF w w' t] t by (simp add: pfst_def)
qed

lemma pexit_pfst: "pexit S K (pfst S \<omega>) = pexit S K (\<lambda>t. fst (\<omega> t))"
proof -
  have "{r. 0 \<le> r \<and> r \<le> S \<and> pfst S \<omega> r \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> S \<and> fst (\<omega> r) \<in> - K}"
    by (auto simp: pfst_def)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma pfst_measurable:
  fixes N :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure"
  assumes S: "0 \<le> S"
    and setsN: "sets N = sets (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "pfst S \<in> N \<rightarrow>\<^sub>M (path_borel S :: ((real \<Rightarrow> 'a)) measure)"
  unfolding pfst_def
proof (rule pathify_measurable[OF S])
  fix t :: real assume "t \<in> {0..S}"
  show "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). fst (\<omega> t)) \<in> borel_measurable N"
    by (rule measurable_compose[OF path_law_evaluation_measurable[OF setsN] pair_fst_borel])
next
  fix \<omega> :: "(real \<Rightarrow> 'a \<times> 'b)" assume "\<omega> \<in> space N"
  then have "\<omega> \<in> mspace (path_metric S :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    using space_of_path_sets[OF setsN] by simp
  then have "continuous_on {0..S} \<omega>" by (rule mspace_path_metricD)
  then show "continuous_on {0..S} (\<lambda>t. fst (\<omega> t))"
    by (intro continuous_intros)
qed

lemma ess_inf_time_pfst:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})) measure" and K :: "('a) set"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "ess_inf_time (distr Q (path_borel T :: (real \<Rightarrow> 'a) measure) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  have "ess_inf_time (distr Q (path_borel T :: (real \<Rightarrow> 'a) measure) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (pfst T \<omega>))"
    by (rule ess_inf_time_distr_measurable
        [OF pfst_measurable[OF T setsQ] pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

lemma pexit_pshift_eq_etime:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})" and K :: "('a) set" and x :: "'a"
  shows "pexit T K (\<lambda>t. fst (pshift T x \<omega> t))
       = etime T {p :: 'a \<times> 'b. fst p \<in> - K}
           (\<lambda>s w. (x, 0) + w s) \<omega>"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> fst (pshift T x \<omega> r) \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> T
            \<and> (x, 0) + \<omega> r \<in> {p :: 'a \<times> 'b. fst p \<in> - K}}"
    by (auto simp: pshift_fst)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

subsection \<open>A value functional as a shifted supremum at \<open>0\<close>\<close>

lemma pcut_pcut:
  fixes \<omega> :: "real \<Rightarrow> 'b"
  assumes ST: "S \<le> T"
  shows "pcut S (pcut T \<omega>) = pcut S \<omega>"
proof (rule ext)
  fix t :: real
  show "pcut S (pcut T \<omega>) t = pcut S \<omega> t" using ST by (auto simp: pcut_def)
qed

lemma mdist_pglue_le:
  fixes w wt w' wt' :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "w \<in> mspace (path_metric r :: (real \<Rightarrow> 'p) metric)"
    and wt: "wt \<in> mspace (path_metric r :: (real \<Rightarrow> 'p) metric)"
    and w': "w' \<in> mspace (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)"
    and wt': "wt' \<in> mspace (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)"
  shows "mdist (path_metric T :: (real \<Rightarrow> 'p) metric)
        (pglue r T w w') (pglue r T wt wt')
      \<le> mdist (path_metric r :: (real \<Rightarrow> 'p) metric) w wt
        + 2 * mdist (path_metric (T - r) :: (real \<Rightarrow> 'p) metric) w' wt'"
proof -
  let ?d1 = "mdist (path_metric r :: (real \<Rightarrow> 'p) metric) w wt"
  let ?d2 = "mdist (path_metric (T - r) :: (real \<Rightarrow> 'p) metric) w' wt'"
  have T0: "0 \<le> T" using r rT by simp
  have Tr0: "0 \<le> T - r" using rT by simp
  have g1: "pglue r T w w' \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    by (rule pglue_in_mspace[OF r rT w w'])
  have g2: "pglue r T wt wt' \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    by (rule pglue_in_mspace[OF r rT wt wt'])
  have pw1: "dist (w t) (wt t) \<le> ?d1" if "t \<in> {0..r}" for t
    using path_mdist_le_iff_all[OF r w wt] that by blast
  have pw2: "dist (w' t) (wt' t) \<le> ?d2" if "t \<in> {0..T - r}" for t
    using path_mdist_le_iff_all[OF Tr0 w' wt'] that by blast
  have pw: "dist (pglue r T w w' t) (pglue r T wt wt' t) \<le> ?d1 + 2 * ?d2"
    if t: "t \<in> {0..T}" for t
  proof (cases "t \<le> r")
    case True
    then have tr: "t \<in> {0..r}" using t by simp
    have "dist (pglue r T w w' t) (pglue r T wt wt' t) = dist (w t) (wt t)"
      using t True by (simp add: pglue_le)
    also have "\<dots> \<le> ?d1" by (rule pw1[OF tr])
    also have "\<dots> \<le> ?d1 + 2 * ?d2" by simp
    finally show ?thesis .
  next
    case False
    then have tr: "r \<le> t" by simp
    have t1: "t - r \<in> {0..T - r}" using t tr by simp
    have t2: "(0::real) \<in> {0..T - r}" using Tr0 by simp
    have alg: "(w r + (w' (t - r) - w' 0)) - (wt r + (wt' (t - r) - wt' 0))
        = (w r - wt r) + ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0))"
      by (simp add: algebra_simps)
    have "dist (pglue r T w w' t) (pglue r T wt wt' t)
        = norm ((w r - wt r) + ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0)))"
      using t tr by (simp add: pglue_ge dist_norm alg)
    also have "\<dots> \<le> norm (w r - wt r)
        + norm ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0))"
      by (rule norm_triangle_ineq)
    also have "\<dots> \<le> norm (w r - wt r)
        + (norm (w' (t - r) - wt' (t - r)) + norm (w' 0 - wt' 0))"
      by (simp add: norm_triangle_ineq4)
    also have "\<dots> \<le> ?d1 + (?d2 + ?d2)"
      using pw1[of r] pw2[OF t1] pw2[OF t2] r by (simp add: dist_norm)
    finally show ?thesis by simp
  qed
  show ?thesis using path_mdist_le_iff_all[OF T0 g1 g2] pw by blast
qed

lemma Lipschitz_pglue:
  fixes r T :: real
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map
      (prod_metric (path_metric r :: (real \<Rightarrow> 'p::{polish_space,banach}) metric)
        (path_metric (T - r) :: (real \<Rightarrow> 'p) metric))
      (path_metric T :: (real \<Rightarrow> 'p) metric)
      (\<lambda>p. pglue r T (fst p) (snd p))"
proof (rule Lipschitz_path_mapI[where B = 3])
  show "0 \<le> T" using r rT by simp
  show "pglue r T (fst p) (snd p) \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    if "p \<in> mspace (prod_metric (path_metric r :: (real \<Rightarrow> 'p) metric)
        (path_metric (T - r) :: (real \<Rightarrow> 'p) metric))" for p
    using pglue_in_mspace[OF r rT] that by auto
  fix p q :: "(real \<Rightarrow> 'p) \<times> (real \<Rightarrow> 'p)" and t :: real
  assume p: "p \<in> mspace (prod_metric (path_metric r :: (real \<Rightarrow> 'p) metric)
      (path_metric (T - r) :: (real \<Rightarrow> 'p) metric))"
    and q: "q \<in> mspace (prod_metric (path_metric r :: (real \<Rightarrow> 'p) metric)
      (path_metric (T - r) :: (real \<Rightarrow> 'p) metric))"
    and t: "t \<in> {0..T}"
  from p have p1: "fst p \<in> mspace (path_metric r :: (real \<Rightarrow> 'p) metric)"
    and p2: "snd p \<in> mspace (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)"
    by auto
  from q have q1: "fst q \<in> mspace (path_metric r :: (real \<Rightarrow> 'p) metric)"
    and q2: "snd q \<in> mspace (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)"
    by auto
  let ?a = "mdist (path_metric r :: (real \<Rightarrow> 'p) metric) (fst p) (fst q)"
  let ?b = "mdist (path_metric (T - r) :: (real \<Rightarrow> 'p) metric) (snd p) (snd q)"
  let ?pd = "mdist (prod_metric (path_metric r :: (real \<Rightarrow> 'p) metric)
      (path_metric (T - r) :: (real \<Rightarrow> 'p) metric)) p q"
  have pdeq: "?pd = sqrt (?a\<^sup>2 + ?b\<^sup>2)"
    by (simp add: prod_dist_def case_prod_unfold)
  have c: "?a \<le> ?pd" "?b \<le> ?pd"
    unfolding pdeq by (rule real_sqrt_sum_squares_ge1 real_sqrt_sum_squares_ge2)+
  have "dist (pglue r T (fst p) (snd p) t) (pglue r T (fst q) (snd q) t)
      \<le> mdist (path_metric T :: (real \<Rightarrow> 'p) metric)
        (pglue r T (fst p) (snd p)) (pglue r T (fst q) (snd q))"
    by (rule path_dist_le_mdist[OF pglue_in_mspace[OF r rT p1 p2]
          pglue_in_mspace[OF r rT q1 q2] t])
  also have "\<dots> \<le> ?a + 2 * ?b" by (rule mdist_pglue_le[OF r rT p1 q1 p2 q2])
  also have "\<dots> \<le> 3 * ?pd" using c by linarith
  finally show "dist (pglue r T (fst p) (snd p) t) (pglue r T (fst q) (snd q) t) \<le> 3 * ?pd" .
qed

subsection \<open>Weak convergence of the semidirect products\<close>

text \<open>\<open>integral_ksemi_bounded\<close> (all the weak-convergence route needs, since
  test functions for weak convergence are bounded and real by definition)
  and \<open>integral_ksemi_measurable\<close> live in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

text \<open>Pointwise weak convergence of the kernels gives weak convergence of
  the semidirect products.  The proof is dominated convergence over the
  first coordinate: a bounded continuous test function on the product is,
  at each fixed first coordinate, a bounded continuous test function on
  the second, so the inner integrals converge pointwise, and they are all
  bounded by the same constant.\<close>

lemma pexit_pglue_ge:
  fixes K :: "('a::{polish_space,banach}) set" and \<omega> \<omega>' :: "(real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))"
proof -
  have "pexit S K (\<lambda>t. fst (\<omega> t)) = pexit S K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))"
  proof (rule pexit_cong_on)
    fix t assume "0 \<le> t" "t \<le> S"
    then show "fst (\<omega> t) = fst (pglue S T \<omega> \<omega>' t)"
      using order.trans[OF \<open>t \<le> S\<close> ST] by (simp add: pglue_le)
  qed
  also have "\<dots> \<le> pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))" by (rule pexit_mono_T[OF S ST])
  finally show ?thesis .
qed

subsection \<open>The selector as a kernel into a family of laws\<close>

text \<open>\<open>exit_val_measurable_selector_kernel'\<close> below makes the selector
  a Giry-monad kernel, hypothesis \<^emph>\<open>Kp\<close> of \<open>covariation_class_kglue_law'\<close>.  Measurability into the
  class with its Levy-Prokhorov metric then comes for free inside that proof:
  the kernel lands in the subspace, and \<open>covariation_class_compact_metric_space\<close> identifies the class's metric
  topology with the subspace topology of weak convergence.\<close>

lemma pexit_path_measurable:
  fixes K :: "('a::{polish_space,banach}) set" and N :: "((real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsN: "sets N = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pexit T K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pexit T K (pfst T \<omega>)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pfst_measurable[OF T setsN]
          pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

lemma survival_set_measurable:
  fixes K :: "('a::{polish_space,banach}) set"
  assumes r: "0 \<le> r" and Kc: "closed K"
  shows "{p' \<in> space (path_borel r :: ((real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})) measure).
      pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K}
    \<in> sets (path_borel r :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?X = "(path_borel r :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have pm: "(\<lambda>p' :: (real \<Rightarrow> 'a \<times> 'b). pexit r K (\<lambda>t. fst (p' t)))
      \<in> borel_measurable ?X"
    by (rule pexit_path_measurable[OF r Kc refl])
  have em: "(\<lambda>p' :: (real \<Rightarrow> 'a \<times> 'b). fst (p' r)) \<in> borel_measurable ?X"
    by (rule measurable_compose
        [OF path_law_evaluation_measurable[OF refl] pair_fst_borel])
  have s1: "{p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r} \<in> sets ?X"
    using pm by measurable
  have s2: "{p' \<in> space ?X. fst (p' r) \<in> K} \<in> sets ?X"
    using em borel_closed[OF Kc] by (simp add: measurable_sets_Collect)
  have "{p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K}
      = {p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r}
        \<inter> {p' \<in> space ?X. fst (p' r) \<in> K}" by auto
  then show ?thesis using sets.Int[OF s1 s2] by simp
qed

text \<open>The conditioning statement itself (\<open>covariation_val_cond\<close> and
  \<open>covariation_val_cond_time\<close>), the key step of the \<open>\<le>\<close> half of the DPP
  in \<open>Proposition_2_4\<close>.  The chain is:

  \<^item> the hypothesis becomes a measurable property of the pair
    \<open>(pcut r \<omega>, pfut r T \<omega>)\<close>, by \<open>pglue_pcut_pfut\<close>;
  \<^item> @{thm [source] AE_ksemi} disintegrates it along the r.c.d.;
  \<^item> \<open>covariation_class_rcd_member\<close> says the r.c.d. lands in the
    class at the origin, so at a fixed good \<open>p'\<close> the surviving future is a
    class member started at \<open>0\<close> and shifted by the constant \<open>fst (p' r)\<close>;
  \<^item> \<open>covariation_val_ge_of_AE_pshift\<close> turns the almost-sure lower bound
    on its exit time into a lower bound for \<open>exit_val\<close> at that point.

  No localization and no \<open>K\<^sub>\<epsilon>\<close> are needed: the starting point is a single
  vector.\<close>

text \<open>\<open>sets_PiM_mono\<close>, \<open>filtered_measure_PiM\<close>, \<open>martingale_distr\<close> and
  \<open>martingale_PiM_component\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

section \<open>Kernel pasting: a continuation chosen by the endpoint\<close>

text \<open>The step from \<open>pglue_law\<close> (one continuation for every endpoint) to
  what (2.9) needs: a countable family \<open>RR\<close> of candidate continuations and
  a past-measurable index \<open>N\<close> selecting one.  The second factor is the
  product \<open>\<Pi>\<^sub>M i. RR i\<close>, from which the glue picks the \<open>N \<omega>\<close>-th;
  freezing the first coordinate makes the index constant, so
  \<open>martingale_pair_snd_param\<close> and \<open>martingale_PiM_component\<close> carry the
  construction.\<close>

definition pembed :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pembed s T w = restrict (\<lambda>t. w (max (t - s) 0)) {0..T}"

text \<open>Stroock--Varadhan splice the continuation into the same
  \<open>C([0,\<infinity>))\<close>, so no horizon ever varies; here the path space is capped at
  \<open>T\<close>, so \<^term>\<open>exit_class k L (T - s) 0\<close> lives on a different space
  for each \<open>s\<close>, and a continuation kernel indexed by the past would have to
  be measurable into a moving target.

  The additive glue shows the way out: a continuation enters only as a
  delayed law on the fixed \<open>T\<close>-path space, so the object to select is the
  \<^const>\<open>pembed\<close>-image of a rebased law --- \<open>s\<close> is then a mere parameter,
  as the time argument of the paper's value function is, and the candidate
  space no longer moves.

  This rests on two facts: that \<^const>\<open>pembed\<close> is a map of path spaces,
  and that \<open>prebase\<close> inverts it on the left, so nothing is lost by
  working with the delayed law instead of the rebased one.\<close>

lemma pembed_mspace_of_cont:
  fixes w :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and U: "T - s \<le> U"
    and c: "continuous_on {0..U} w"
  shows "pembed s T w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
proof -
  have "continuous_on {0..T} (\<lambda>t. w (max (t - s) 0))"
    by (rule continuous_on_compose2[OF c]) (use s0 sT U in \<open>auto intro!: continuous_intros\<close>)
  then show ?thesis unfolding pembed_def by (rule mspace_path_metricI)
qed

lemma pembed_mspace:
  fixes w :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric (T - s) :: (real \<Rightarrow> 'p) metric)"
  shows "pembed s T w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  by (rule pembed_mspace_of_cont[OF s0 sT order_refl mspace_path_metricD[OF w]])

lemma pembed_mspace_full:
  fixes \<omega> :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "pembed s T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  by (rule pembed_mspace_of_cont[OF s0 sT _ mspace_path_metricD[OF w]]) (use s0 in simp)

definition pdel :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pdel s T = pembed (max 0 (min s T)) T"

lemma pdel_eq_pembed: "0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> pdel s T = pembed s T"
  unfolding pdel_def by simp

lemma pdel_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes T0: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "pdel s T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  unfolding pdel_def
  by (rule pembed_mspace_full[OF pdel_clamp_lo pdel_clamp_hi[OF T0] w])

definition prebase :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "prebase s T w = restrict (\<lambda>u. w (s + u)) {0..T - s}"

lemma pembed_apply: "t \<in> {0..T} \<Longrightarrow> pembed s T w t = w (max (t - s) 0)"
  by (simp add: pembed_def)

lemma pdel_eval: "t \<in> {0..T} \<Longrightarrow> pdel s T \<omega> t = \<omega> (max (t - max 0 (min s T)) 0)"
  unfolding pdel_def by (rule pembed_apply)

lemma pembed_eval_min:
  fixes w :: "real \<Rightarrow> 'b"
  assumes u: "0 \<le> u" and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "pembed s T w (min u T) = w (min (max (u - s) 0) (T - s))"
proof -
  have mem: "min u T \<in> {0..T}" using u s0 sT by simp
  have "pembed s T w (min u T) = w (max (min u T - s) 0)"
    by (rule pembed_apply[OF mem])
  moreover have "max (min u T - s) 0 = min (max (u - s) 0) (T - s)"
    using u s0 sT by (auto simp: min_def max_def)
  ultimately show ?thesis by simp
qed

lemma prebase_apply: "u \<in> {0..T - s} \<Longrightarrow> prebase s T w u = w (s + u)"
  by (simp add: prebase_def)

lemma pexit_delayed_rebase:
  fixes w :: "(real \<Rightarrow> 'a::{polish_space,banach} \<times> 'b::{polish_space,banach})" and y :: "'a"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and frz: "\<And>t. t \<in> {0..T} \<Longrightarrow> t \<le> r \<Longrightarrow> w t = 0"
    and inK: "y \<in> K"
  shows "r + pexit (T - r) K (\<lambda>u. y + fst (prebase r T w u))
      \<le> pexit T K (\<lambda>s. y + fst (w s))"
proof -
  have stays: "y + fst (w s) \<in> K" if "0 \<le> s" "s \<le> r" for s
  proof -
    have "w s = 0" by (rule frz) (use that order.trans[OF that(2) rT] in simp_all)
    then show ?thesis using inK by simp
  qed
  have surv: "pexit r K (\<lambda>s. y + fst (w s)) = r"
    by (rule pexit_eq_of_stays[OF r]) (rule stays)
  have "pexit T K (\<lambda>s. y + fst (w s)) = r + pexit (T - r) K (\<lambda>s. y + fst (w (r + s)))"
    by (rule pexit_split_at_r[OF r rT surv]) (rule stays[OF r order_refl])
  also have "pexit (T - r) K (\<lambda>s. y + fst (w (r + s)))
      = pexit (T - r) K (\<lambda>u. y + fst (prebase r T w u))"
    by (rule pexit_cong_on) (simp add: prebase_apply)
  finally show ?thesis by simp
qed

section \<open>The exit bound for the glued law\<close>

text \<open>The two pathwise lemmas compose into the law-level statement the
  \<open>\<ge>\<close> half needs: if the past already satisfies the DPP integrand bound
  and the continuation attains the value function after \<open>\<theta>\<close>, then the
  glue's exit time is at least \<open>c\<close> almost surely.\<close>

lemma pembed_outside: "t \<notin> {0..T} \<Longrightarrow> pembed s T w t = undefined"
  unfolding pembed_def restrict_def by (rule if_not_P)

lemma pembed_measurable:
  fixes s T :: real
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "pembed s T \<in> (path_borel (T - s) :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
      \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?Bs = "(path_borel (T - s) :: (real \<Rightarrow> 'p) measure)"
  have T0: "0 \<le> T" using s0 sT by simp
  have into: "pembed s T w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    if "w \<in> space ?Bs" for w
    using that by (auto simp: space_borel_of intro: pembed_mspace[OF s0 sT])
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'p). pembed s T w t) \<in> borel_measurable ?Bs"
    if True: "t \<in> {0..T}" for t
  proof -
    have "(\<lambda>w :: (real \<Rightarrow> 'p). w (max (t - s) 0)) \<in> borel_measurable ?Bs"
      by (rule path_law_evaluation_measurable[OF refl])
    then show ?thesis by (simp add: pembed_apply[OF True])
  qed
  show ?thesis by (rule path_measurable_of_eval[OF T0 into ev])
qed

text \<open>\<^const>\<open>prebase\<close> inverts \<^const>\<open>pembed\<close>: the delayed law carries exactly
  the same information as the rebased one, so selecting the delayed law is
  no weaker than selecting the rebased one.\<close>

lemma pembed_pcut:
  fixes \<omega> :: "real \<Rightarrow> 'b"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "pembed s T (pcut (T - s) \<omega>) = pembed s T \<omega>"
proof (rule ext)
  fix t :: real
  show "pembed s T (pcut (T - s) \<omega>) t = pembed s T \<omega> t"
  proof (cases "t \<in> {0..T}")
    case True
    then have m: "max (t - s) 0 \<in> {0..T - s}" using s0 sT by auto
    have "pembed s T (pcut (T - s) \<omega>) t = pcut (T - s) \<omega> (max (t - s) 0)"
      by (rule pembed_apply[OF True])
    also have "\<dots> = \<omega> (max (t - s) 0)" by (rule pcut_apply[OF m])
    also have "\<dots> = pembed s T \<omega> t" by (rule pembed_apply[OF True, symmetric])
    finally show ?thesis .
  next
    case False
    then show ?thesis by (simp add: pembed_outside)
  qed
qed

lemma pembed_measurable_full:
  fixes s T :: real
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "pembed s T \<in> (path_borel T :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
      \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  have a: "0 \<le> T - s" using sT by simp
  have b: "T - s \<le> T" using s0 by simp
  have eq: "(\<lambda>\<omega> :: (real \<Rightarrow> 'p). pembed s T (pcut (T - s) \<omega>)) = pembed s T"
    by (rule ext) (rule pembed_pcut[OF s0 sT])
  have "(\<lambda>\<omega>. pembed s T (pcut (T - s) \<omega>)) \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule measurable_compose[OF pcut_measurable[OF a b refl]
          pembed_measurable[OF s0 sT]])
  then show ?thesis unfolding eq .
qed

text \<open>The clamped delayed embedding: total in \<open>s\<close>, and equal to
  \<^const>\<open>pembed\<close> on the range that matters.  Totality lets the parameter
  live in \<^term>\<open>borel :: real measure\<close> rather than in a restricted space.\<close>

lemma pdel_measurable:
  assumes T0: "0 \<le> T"
  shows "pdel s T \<in> (path_borel T :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
      \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
  unfolding pdel_def
  by (rule pembed_measurable_full[OF pdel_clamp_lo pdel_clamp_hi[OF T0]])

lemma pdel_measurable_pair:
  assumes T0: "0 \<le> T"
  shows "(\<lambda>p. pdel (fst p) T (snd p))
      \<in> (borel :: real measure) \<Otimes>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
        \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  let ?M = "(borel :: real measure) \<Otimes>\<^sub>M ?B"
  have spM: "space ?M = UNIV \<times> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    by (simp add: space_pair_measure space_borel_of)
  have into: "pdel (fst p) T (snd p)
      \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)" if p: "p \<in> space ?M" for p
  proof -
    have "p \<in> UNIV \<times> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
      using p unfolding spM .
    then have "snd p \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
      by (simp add: mem_Times_iff)
    then show ?thesis by (rule pdel_mspace[OF T0])
  qed
  have sndm: "(\<lambda>p :: real \<times> (real \<Rightarrow> 'p). snd p) \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule measurable_snd)
  have ev: "(\<lambda>p. pdel (fst p) T (snd p) t) \<in> borel_measurable ?M"
    if True: "t \<in> {0..T}" for t
  proof -
    have gm: "(\<lambda>p :: real \<times> (real \<Rightarrow> 'p). max (t - max 0 (min (fst p) T)) 0)
        \<in> borel_measurable ?M" by measurable
    have g0: "0 \<le> max (t - max 0 (min (fst p) T)) 0"
      for p :: "real \<times> (real \<Rightarrow> 'p)" by simp
    have gT: "max (t - max 0 (min (fst p) T)) 0 \<le> T"
      for p :: "real \<times> (real \<Rightarrow> 'p)" using True by auto
    have "(\<lambda>p :: real \<times> (real \<Rightarrow> 'p).
        snd p (max (t - max 0 (min (fst p) T)) 0)) \<in> borel_measurable ?M"
      by (rule path_eval_at_measurable_time
          [where X = "\<lambda>p :: real \<times> (real \<Rightarrow> 'p). snd p"
            and g = "\<lambda>p :: real \<times> (real \<Rightarrow> 'p). max (t - max 0 (min (fst p) T)) 0",
            OF T0 sndm gm g0 gT])
    then show ?thesis using True by (simp add: pdel_eval)
  qed
  show ?thesis by (rule path_measurable_of_eval[OF T0 into ev])
qed

subsection \<open>Cutting a law commutes with shifting, and caps its value\<close>

lemma pembed_eval_le:
  fixes w :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes r0: "0 \<le> r" and ru: "r \<le> u" and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>w :: (real \<Rightarrow> 'p). pembed s T w r) \<in> borel_measurable
      (natural_filtration M 0 (\<lambda>v w. w v) (min (max (u - s) 0) (T - s)))"
proof (cases "r \<le> T")
  case True
  have e1: "0 \<le> max (r - s) 0" by simp
  have e2: "max (r - s) 0 \<le> min (max (u - s) 0) (T - s)"
    using r0 ru s0 sT True by (auto simp: min_def max_def)
  have mem: "r \<in> {0..T}" using r0 True by simp
  have "(\<lambda>w :: (real \<Rightarrow> 'p). w (max (r - s) 0)) \<in> borel_measurable
      (natural_filtration M 0 (\<lambda>v w. w v) (min (max (u - s) 0) (T - s)))"
    by (rule natural_filtration_eval[OF e1 e2])
  then show ?thesis by (simp add: pembed_apply[OF mem])
next
  case False
  then have "r \<notin> {0..T}" by simp
  then have "(\<lambda>w :: (real \<Rightarrow> 'p). pembed s T w r) = (\<lambda>w. undefined)"
    by (simp add: pembed_outside)
  then show ?thesis by simp
qed

lemma prebase_outside: "u \<notin> {0..T - s} \<Longrightarrow> prebase s T w u = undefined"
  unfolding prebase_def restrict_def by (rule if_not_P)

text \<open>The two bridges: \<open>pafter\<close> is the delayed future, and the future is
  recovered from it by re-basing, so nothing is lost either way.\<close>

subsection \<open>Where the stopping-time property enters\<close>

text \<open>Everything so far used only Borel measurability of \<open>\<theta>\<close>.  From here on
  \<open>\<theta>\<close> must be a genuine stopping time, which on path space says exactly one
  thing: \<open>\<theta>\<close> is decided by the path up to \<open>\<theta>\<close>.  Two paths agreeing on
  \<open>[0, \<theta> \<omega>]\<close> get the same value, which is what makes \<open>\<theta>\<close> a function of the
  stopped path, and hence makes the kernel a function of the past.\<close>

lemma prebase_pembed:
  fixes w :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric (T - s) :: (real \<Rightarrow> 'p) metric)"
  shows "prebase s T (pembed s T w) = w"
proof (rule ext)
  fix u :: real
  show "prebase s T (pembed s T w) u = w u"
  proof (cases "u \<in> {0..T - s}")
    case True
    then have m: "s + u \<in> {0..T}" using s0 by simp
    have "prebase s T (pembed s T w) u = pembed s T w (s + u)"
      by (rule prebase_apply[OF True])
    also have "\<dots> = w (max (s + u - s) 0)" by (rule pembed_apply[OF m])
    also have "max (s + u - s) 0 = u" using True by simp
    finally show ?thesis .
  next
    case False
    have "prebase s T (pembed s T w) u = undefined"
      by (rule prebase_outside[OF False])
    moreover have "w u = undefined"
    proof -
      have "w u = restrict w {0..T - s} u"
        unfolding mspace_path_restrict_self[OF w] ..
      also have "\<dots> = undefined"
        unfolding restrict_def by (rule if_not_P[OF False])
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
qed

subsection \<open>The delayed class at a fixed freezing time\<close>

text \<open>\<^const>\<open>pembed\<close> is 1-Lipschitz --- it only reindexes time --- hence a
  continuous map of path spaces, so by
  @{thm [source] weak_conv_on_pushforward} it carries weak convergence, and
  the delayed class at a fixed \<open>s\<close> is a continuous image of the compact
  class at horizon \<open>T - s\<close>.\<close>

lemma prebase_mspace:
  fixes w :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "prebase s T w \<in> mspace (path_metric (T - s) :: (real \<Rightarrow> 'p) metric)"
proof -
  have c: "continuous_on {0..T} w" by (rule mspace_path_metricD[OF w])
  have "continuous_on {0..T - s} (\<lambda>u. w (s + u))"
  proof (rule continuous_on_compose2[OF c])
    show "continuous_on {0..T - s} (\<lambda>u :: real. s + u)" by (intro continuous_intros)
    show "(\<lambda>u :: real. s + u) ` {0..T - s} \<subseteq> {0..T}" using s0 by auto
  qed
  then show ?thesis unfolding prebase_def by (rule mspace_path_metricI)
qed

lemma prebase_measurable:
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "prebase s T \<in> (path_borel T :: (real \<Rightarrow> 'p::{polish_space,banach}) measure)
    \<rightarrow>\<^sub>M (path_borel (T - s) :: (real \<Rightarrow> 'p) measure)"
proof -
  let ?B = "(path_borel T :: (real \<Rightarrow> 'p) measure)"
  have sp: "space ?B = mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
    by (simp add: space_borel_of)
  have Ts: "0 \<le> T - s" using sT by simp
  have into: "prebase s T w \<in> mspace (path_metric (T - s) :: (real \<Rightarrow> 'p) metric)"
    if "w \<in> space ?B" for w :: "(real \<Rightarrow> 'p)"
  proof -
    have m: "w \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
      using that sp by simp
    show ?thesis by (rule prebase_mspace[OF s0 sT m])
  qed
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'p). prebase s T w u) \<in> borel_measurable ?B"
    if True: "u \<in> {0..T - s}" for u
  proof -
    have "(\<lambda>w :: (real \<Rightarrow> 'p). w (s + u)) \<in> borel_measurable ?B"
      by (rule path_law_evaluation_measurable[OF refl])
    then show ?thesis by (simp add: prebase_apply[OF True])
  qed
  show ?thesis by (rule path_measurable_of_eval[OF Ts into ev])
qed
text \<open>Hence clause (i) for the kernel: re-based, the conditional law is a
  probability measure on the \<open>(T - \<theta>)\<close>-path space.\<close>

text \<open>Clause (ii) for the kernel.  The pathwise content is already there:
  at \<open>t = \<theta> \<omega>\<close>, when the clock starts, the future factor is still \<open>0\<close>,
  so all that is needed is to push it through the r.c.d., the same chain
  as the mixed glue's transfer: \<open>AE_distr_iff\<close> into the joint law, the
  r.c.d. equation, and @{thm [source] AE_ksemi} back out.  The
  stopping-time property is spent where the kernel is indexed by the
  stopped path: the clock has to be read off that, and
  \<open>path_stopping_time_stopped\<close> says it is the same number.\<close>

text \<open>Clause (iii) at one pair of times.  This is the analogue of the \<open>one\<close>
  step inside \<open>pfut_rcd_diffquot\<close>, and the pathwise content is
  free: after \<open>\<theta>\<close> the future factor's increments are \<open>\<omega>\<close>'s increments,
  because the \<open>- \<omega> (\<theta> \<omega>)\<close> cancels in the difference.  The guard
  \<open>\<theta> p' \<le> p\<close> lives inside the predicate, which makes the conditioning set a
  pair-set, so the transfer is the @{thm [source] AE_ksemi} chain of clause
  (ii) rather than \<open>AE_kernel_full\<close>, and the rational grid
  stays in the original time scale.\<close>

lemma padd_eval_split:
  fixes p' w :: "(real \<Rightarrow> 'a::real_normed_vector \<times> 'b::real_normed_vector)"
  assumes t: "t \<in> {0..T}"
  shows "fst (padd T p' w t) = fst (p' t) + fst (w t)"
    and "snd (padd T p' w t) = snd (p' t) + snd (w t)"
  by (simp_all add: padd_apply[OF t])

text \<open>The pathwise dynamic programming bound, at the value \<open>r\<close> a stopping
  time takes on the path.  The two summands are the paper's \<open>r \<and> \<tau>\<^sub>K\<close>
  and \<open>v(X\<^sub>r) \<sqdot> 1\<^sub>{r \<le> \<tau>\<^sub>K}\<close>.  Because
  \<^const>\<open>padd\<close> keeps both factors on the original clock, the
  continuation's contribution is stated as a bound on \<open>pexit T K\<close> of the
  delayed path \<open>s \<mapsto> fst (p' r) + fst (w s)\<close> --- already including the
  \<open>r\<close> it stands still for --- rather than on a rebased horizon, exactly
  the form \<open>pdelclass\<close> produces.\<close>

lemma pexit_padd_dpp:
  fixes K :: "('a::{polish_space,banach}) set" and p' w :: "(real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and c: "0 \<le> c" and cT: "r + c \<le> T"
    and stop: "\<And>t. t \<in> {0..T} \<Longrightarrow> r \<le> t \<Longrightarrow> p' t = p' r"
    and frz: "\<And>t. t \<in> {0..T} \<Longrightarrow> t \<le> r \<Longrightarrow> w t = 0"
    and cont: "pexit r K (\<lambda>t. fst (p' t)) = r \<Longrightarrow> fst (p' r) \<in> K
        \<Longrightarrow> r + c \<le> pexit T K (\<lambda>s. fst (p' r) + fst (w s))"
  shows "pexit r K (\<lambda>t. fst (p' t))
        + (if pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K then c else 0)
      \<le> pexit T K (\<lambda>t. fst (padd T p' w t))"
proof -
  let ?A = "pexit r K (\<lambda>t. fst (p' t))"
  let ?f = "\<lambda>t. fst (padd T p' w t)"
  have w0: "w t = 0" if "0 \<le> t" "t \<le> r" for t
    by (rule frz) (use that order.trans[OF that(2) rT] in simp_all)
  have ev: "?f t = fst (p' t) + fst (w t)" if "0 \<le> t" "t \<le> T" for t
    using that by (simp add: padd_eval_split(1))
  have Af: "pexit r K ?f = ?A"
  proof (rule pexit_cong_on)
    fix t assume t: "0 \<le> t" "t \<le> r"
    then show "?f t = fst (p' t)"
      using ev[OF t(1) order.trans[OF t(2) rT]] w0[OF t] by simp
  qed
  show ?thesis
  proof (cases "?A = r \<and> fst (p' r) \<in> K")
    case True
    then have Aeq: "?A = r" and inK: "fst (p' r) \<in> K" by simp_all
    have hK: "fst (p' r) + fst (w s) \<in> K" if "0 \<le> s" "s \<le> r" for s
      using w0[OF that] inK by simp
    have fr: "?f r \<in> K" using ev[OF r rT] w0[OF r order_refl] inK by simp
    have rest: "pexit (T - r) K (\<lambda>s. ?f (r + s))
        = pexit (T - r) K (\<lambda>s. fst (p' r) + fst (w (r + s)))"
    proof (rule pexit_cong_on)
      fix s assume "0 \<le> s" "s \<le> T - r"
      then have rs: "0 \<le> r + s" "r + s \<le> T" "r \<le> r + s" using r by linarith+
      then show "?f (r + s) = fst (p' r) + fst (w (r + s))"
        using ev[OF rs(1,2)] stop[of "r + s"] by simp
    qed
    have survh: "pexit r K (\<lambda>s. fst (p' r) + fst (w s)) = r"
      by (rule pexit_eq_of_stays[OF r]) (rule hK)
    have "pexit T K ?f = r + pexit (T - r) K (\<lambda>s. ?f (r + s))"
      by (rule pexit_split_at_r[OF r rT]) (simp_all add: Af Aeq fr)
    also have "\<dots> = pexit T K (\<lambda>s. fst (p' r) + fst (w s))"
      unfolding rest
      by (rule pexit_split_at_r[OF r rT survh, symmetric]) (rule hK[OF r order_refl])
    finally show ?thesis using True cont[OF Aeq inK] by simp
  next
    case False
    have "?A \<le> pexit T K ?f" using pexit_mono_T[OF r rT, of K ?f] Af by simp
    moreover have "(if ?A = r \<and> fst (p' r) \<in> K then c else 0) = 0"
      using False by (rule if_not_P)
    ultimately show ?thesis by simp
  qed
qed

text \<open>The bridge between the two clocks: the selector's optimality is a
  statement at horizon \<open>T - r\<close> about the rebased continuation, while the
  glue wants it at horizon \<open>T\<close> about the delayed one.  Since the delayed
  path stands at \<open>y \<in> K\<close> throughout \<open>[0,r]\<close> it cannot exit there, so its
  exit time is exactly \<open>r\<close> later --- and that \<open>r\<close> is the term
  @{thm [source] pexit_padd_dpp} asks for.\<close>

lemma padd_comp_norm_le:
  fixes p' w :: "'n::finite pairpath"
  assumes t: "t \<in> {0..T}"
  shows "norm (outerp (fst (padd T p' w t)) - snd (padd T p' w t))
      \<le> norm (outerp (fst (p' t)) - snd (p' t))
        + norm (outerp (fst (w t)) - snd (w t))
        + 2 * (norm (fst (p' t)) * norm (fst (w t)))"
proof -
  define a where "a = fst (p' t)"
  define A where "A = snd (p' t)"
  define b where "b = fst (w t)"
  define B where "B = snd (w t)"
  have e: "outerp (fst (padd T p' w t)) - snd (padd T p' w t)
      = ((outerp a - A) + (outerp b - B))
        + ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))"
    unfolding a_def A_def b_def B_def
      padd_eval_split(1)[OF t] padd_eval_split(2)[OF t] outerp_add
    by simp
  have t1: "norm (((outerp a - A) + (outerp b - B))
        + ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j)))
      \<le> norm ((outerp a - A) + (outerp b - B))
        + norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))"
    by (rule norm_triangle_ineq)
  have t2: "norm ((outerp a - A) + (outerp b - B))
      \<le> norm (outerp a - A) + norm (outerp b - B)"
    by (rule norm_triangle_ineq)
  have t3: "norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
      \<le> 2 * (norm a * norm b)"
  proof -
    have "norm ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
        \<le> norm (\<chi> i j. a $ i * b $ j) + norm (\<chi> i j. b $ i * a $ j)"
      by (rule norm_triangle_ineq)
    also have "\<dots> = norm a * norm b + norm b * norm a"
      using norm_outer_prod[of a b] norm_outer_prod[of b a]
      by (simp add: outer_prod_def)
    finally show ?thesis by (simp add: algebra_simps)
  qed
  show ?thesis unfolding e a_def[symmetric] A_def[symmetric]
      b_def[symmetric] B_def[symmetric]
    using t1 t2 t3 by linarith
qed

lemma pglue_pcut_pfut:
  fixes \<omega> :: "(real \<Rightarrow> 'p::{polish_space,banach})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'p) metric)"
  shows "pglue r T (pcut r \<omega>) (pfut r T \<omega>) = \<omega>"
proof (rule ext)
  fix t :: real
  show "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t = \<omega> t"
  proof (cases "t \<in> {0..T}")
    case True
    show ?thesis
    proof (cases "t \<le> r")
      case True
      then have tr: "t \<in> {0..r}" using \<open>t \<in> {0..T}\<close> by simp
      have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t = pcut r \<omega> t"
        by (rule pglue_le[OF \<open>t \<in> {0..T}\<close> True])
      also have "\<dots> = \<omega> t" by (rule pcut_apply[OF tr])
      finally show ?thesis .
    next
      case False
      then have tr: "r \<le> t" by simp
      have m: "t - r \<in> {0..T - r}" using tr \<open>t \<in> {0..T}\<close> by simp
      have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t
          = pcut r \<omega> r + (pfut r T \<omega> (t - r) - pfut r T \<omega> 0)"
        by (rule pglue_ge[OF \<open>t \<in> {0..T}\<close> tr])
      also have "\<dots> = \<omega> r + (\<omega> (r + (t - r)) - \<omega> r - 0)"
        using r rT by (simp add: pcut_apply pfut_apply[OF m] pfut_zero)
      also have "\<dots> = \<omega> t" by simp
      finally show ?thesis .
    qed
  next
    case False
    then have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) t = undefined"
      unfolding pglue_def restrict_def by (rule if_not_P)
    moreover have "\<omega> t = undefined"
      using w False by (auto simp: path_metric_def extensional_def)
    ultimately show ?thesis by simp
  qed
qed

lemma pexit_pglue_measurable:
  fixes K :: "('a::{polish_space,banach}) set"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and Kc: "closed K"
  shows "(\<lambda>p. pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))
      \<in> borel_measurable
          ((path_borel r :: ((real \<Rightarrow> 'a \<times> 'b::{polish_space,banach})) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure))"
proof -
  have T0: "0 \<le> T" using r rT by simp
  show ?thesis
    by (rule measurable_compose[OF pglue_measurable[OF r rT refl refl]
        pexit_path_measurable[OF T0 Kc refl]])
qed


(*<*)
end
(*>*)
