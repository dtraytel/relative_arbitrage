section \<open>Cutting, glueing, shifting and delaying a path\<close>

(*<*)
theory Path_Splicing
  imports Pair_Path_Laws
begin

(*>*)

text \<open>The surgery: \<open>pcut\<close> truncates at a time, \<open>pglue\<close> concatenates two
  paths at a time with the increment carried over, \<open>pshift\<close> re-bases,
  \<open>padd\<close> adds a future to a past, \<open>pdel\<close> delays, \<open>pembed\<close> and \<open>prebase\<close>
  move between horizons, and \<open>pfut\<close> reads the future.  Each is a one-line
  definition on functions; what takes room is that each is continuous where
  it should be and measurable for the Borel algebra of the path metric.\<close>

text \<open>\<open>cInf_shift_real\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>



definition pfut :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pfut r T \<omega> = restrict (\<lambda>s. \<omega> (r + s) - \<omega> r) {0..T - r}"

text \<open>The conditioning-free half of the closure the weak DPP needs: a
  member on \<open>[0,T]\<close> restricted to \<open>[0,S]\<close> is a member on \<open>[0,S]\<close>.  Both
  martingale clauses follow from \<open>martingale_pair_law\<close> with the restriction
  as path map, adapted for free since \<open>pcut S \<omega> r = \<omega> r\<close> on \<open>{0..S}\<close>, and
  \<open>martingale_stopped_const\<close> turns the \<open>T\<close>-clause into the \<open>S\<close>-clause.\<close>

definition pcut :: "real \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pcut S \<omega> = restrict \<omega> {0..S}"

text \<open>Every member started at \<open>x\<close> is the \<open>x\<close>-translate of a member started
  at \<open>0\<close>.  This turns the value function into a supremum over a fixed
  family, the shape Berge's theorem needs.  The translation must
  \<open>restrict\<close>, because points of the capped path space are extensional on
  \<open>{0..T}\<close>.\<close>

definition pshift :: "real \<Rightarrow> real^'n::finite \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath"
  where "pshift T x \<omega> = restrict (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t))) {0..T}"

lemma pfut_apply: "s \<in> {0..T - r} \<Longrightarrow> pfut r T \<omega> s = \<omega> (r + s) - \<omega> r"
  by (simp add: pfut_def)

text \<open>Reassembly of the split is addition (\<open>pstopped_add_pafter\<close>),
  so the kernel is pushed through the glue map \<^term>\<open>padd T p' w\<close>, not
  \<open>pglue\<close>.  It is defined on the same pair of \<open>T\<close>-path spaces the
  r.c.d. lives on, and needs no \<open>\<theta>\<close> --- the reason the additive split was
  chosen over freeze-and-rebase.

  The facts below form the foundation layer: the glue lands in the path
  space, is measurable as a map out of the product, inverts the split, and
  --- given that the continuation stands still until \<open>\<theta>\<close> --- is inverted by
  the split, so no information is lost in either direction.\<close>

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
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "pcut S \<in> Q \<rightarrow>\<^sub>M (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  have "(\<lambda>f :: (real \<Rightarrow> 'a \<times> 'b). restrict f {0..S})
      \<in> (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
        \<rightarrow>\<^sub>M (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    by (rule restrict_measurable_path_borel[OF S ST])
  then show ?thesis
    unfolding pcut_def using measurable_cong_sets[OF setsQ refl] by blast
qed

lemma pshift_fst: "t \<in> {0..T} \<Longrightarrow> fst (pshift T x \<omega> t) = x + fst (\<omega> t)"
  by (simp add: pshift_def)

lemma pfut_fst:
  "s \<in> {0..T - r} \<Longrightarrow> fst (pfut r T \<omega> s) = fst (\<omega> (r + s)) - fst (\<omega> r)"
  by (simp add: pfut_def)

lemma padd_outside: "t \<notin> {0..T} \<Longrightarrow> padd T p' w t = undefined"
  unfolding padd_def restrict_def by (rule if_not_P)

lemma pshift_snd: "t \<in> {0..T} \<Longrightarrow> snd (pshift T x \<omega> t) = snd (\<omega> t)"
  by (simp add: pshift_def)

lemma padd_mspace:
  fixes p' w :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes p: "p' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and w: "w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "padd T p' w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
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
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pfut r T \<omega> \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have cw: "continuous_on {0..T} \<omega>" by (rule mspace_path_metric_continuous[OF w])
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
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T x \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have "continuous_on {0..T} (\<lambda>t. (x + fst (\<omega> t), snd (\<omega> t)))"
    by (intro continuous_intros c)
  then show ?thesis unfolding pshift_def by (rule mspace_path_metricI)
qed

lemma pcut_adapted:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes S: "0 \<le> S" and r: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pcut S \<omega> r) \<in> borel_measurable
      (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<in> {0..S}")
  case True
  have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). \<omega> r) \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M borel"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use r ru in auto)
  then show ?thesis using True by (simp add: pcut_apply)
next
  case False
  then have "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pcut S \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (auto simp: pcut_def)
  then show ?thesis by simp
qed

text \<open>The rational reduction of the covariation clause, factored out since
  it recurs in every construction of a class member: countably many pairs
  by \<open>AE_ball_countable'\<close>, then \<open>diffquot_all_of_rational\<close> against path
  continuity.\<close>

lemma Lipschitz_pfut:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) metric)
      (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric) (pfut r T)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pfut r T \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
      \<rightarrow> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (intro funcsetI pfut_in_mspace[OF r rT])
  have T0: "0 \<le> T" using r rT by simp
  have Tr: "0 \<le> T - r" using rT by simp
  have key: "mdist (path_metric (T - r)) (pfut r T f) (pfut r T g)
      \<le> 2 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      and g: "g \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)" for f g
  proof -
    have sf: "pfut r T f \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      by (rule pfut_in_mspace[OF r rT f])
    have sg: "pfut r T g \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      by (rule pfut_in_mspace[OF r rT g])
    have pw: "\<forall>t\<in>{0..T}. dist (f t) (g t) \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T0 f g] by blast
    have pws: "dist (pfut r T f s) (pfut r T g s) \<le> 2 * mdist (path_metric T) f g"
      if s: "s \<in> {0..T - r}" for s
    proof -
      have rs: "r + s \<in> {0..T}" using s r rT by simp
      have r0: "r \<in> {0..T}" using r rT by simp
      have "dist (pfut r T f s) (pfut r T g s)
          = dist (f (r + s) - f r) (g (r + s) - g r)"
        using s by (simp add: pfut_apply)
      also have "\<dots> = norm ((f (r + s) - g (r + s)) - (f r - g r))"
        by (simp add: dist_norm algebra_simps)
      also have "\<dots> \<le> norm (f (r + s) - g (r + s)) + norm (f r - g r)"
        by (rule norm_triangle_ineq4)
      also have "\<dots> = dist (f (r + s)) (g (r + s)) + dist (f r) (g r)"
        by (simp add: dist_norm)
      finally show ?thesis using bspec[OF pw rs] bspec[OF pw r0] by simp
    qed
    show ?thesis using path_mdist_le_iff_all[OF Tr sf sg] pws by blast
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric).
      \<forall>g\<in>mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric).
        mdist (path_metric (T - r)) (pfut r T f) (pfut r T g)
          \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 2] ballI key)
qed

lemma pshift_zero:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T 0 \<omega> = \<omega>"
proof -
  have "pshift T 0 \<omega> = restrict \<omega> {0..T}"
    unfolding pshift_def by simp
  also have "\<dots> = \<omega>" by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

lemma padd_measurable_left:
  fixes p' :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes T0: "0 \<le> T"
    and p: "p' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "(\<lambda>w. padd T p' w)
      \<in> (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have into: "padd T p' w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if "w \<in> space ?B" for w
    using that p by (auto simp: space_borel_of intro: padd_mspace)
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). padd T p' w t) \<in> borel_measurable ?B" for t
  proof (cases "t \<in> {0..T}")
    case True
    have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). p' t + w t) \<in> borel_measurable ?B"
      by (intro borel_measurable_add borel_measurable_const
          pair_law_eval_measurable[OF refl])
    then show ?thesis by (simp add: padd_apply[OF True])
  next
    case False
    have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). padd T p' w t) = (\<lambda>w. undefined)"
      by (rule ext) (rule padd_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>w. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (padd T p' w) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

lemma pshift_pshift:
  fixes \<omega> :: "'n::finite pairpath"
  shows "pshift T y (pshift T x \<omega>) = pshift T (y + x) \<omega>"
  by (rule ext) (simp add: pshift_def add.assoc)

lemma pshift_inverse:
  fixes \<omega> :: "'n::finite pairpath"
  assumes w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pshift T (- x) (pshift T x \<omega>) = \<omega>"
  using pshift_pshift[of T "- x" x \<omega>] pshift_zero[OF w] by simp

lemma ipcut_measurable:
  fixes P :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes S: "0 \<le> S"
    and setsP: "sets P = sets (ipath_space :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "pcut S \<in> P \<rightarrow>\<^sub>M (path_borel S :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  unfolding pcut_def measurable_cong_sets[OF setsP refl]
  by (rule restrict_ipath_measurable[OF S])

lemma Lipschitz_pshift:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n pairpath) metric)
      (path_metric T :: ('n pairpath) metric) (pshift T x)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pshift T x \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric T :: ('n pairpath) metric)"
    by (intro funcsetI pshift_in_mspace)
  have key: "mdist (path_metric T) (pshift T x f) (pshift T x g)
      \<le> 1 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and g: "g \<in> mspace (path_metric T :: ('n pairpath) metric)" for f g
  proof -
    have sf: "pshift T x f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (rule pshift_in_mspace[OF f])
    have sg: "pshift T x g \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (rule pshift_in_mspace[OF g])
    have pw: "\<forall>t\<in>{0..T}. dist (f t) (g t) \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T f g] by blast
    have pws: "dist (pshift T x f t) (pshift T x g t)
        \<le> mdist (path_metric T) f g" if t: "t \<in> {0..T}" for t
    proof -
      have "dist (pshift T x f t) (pshift T x g t)
          = dist (x + fst (f t), snd (f t)) (x + fst (g t), snd (g t))"
        using t by (simp add: pshift_def)
      also have "\<dots> = dist (f t) (g t)"
        by (simp add: dist_prod_def dist_norm)
      finally show ?thesis using bspec[OF pw t] by simp
    qed
    have "mdist (path_metric T) (pshift T x f) (pshift T x g)
        \<le> mdist (path_metric T) f g"
      using path_mdist_le_iff_all[OF T sf sg] pws by blast
    then show ?thesis by simp
  qed
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>g\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric T) (pshift T x f) (pshift T x g)
          \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 1] ballI key)
qed

lemma padd_measurable:
  fixes T :: real
  assumes T0: "0 \<le> T"
  shows "(\<lambda>p. padd T (fst p) (snd p))
      \<in> (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
        \<Otimes>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?M = "?B \<Otimes>\<^sub>M ?B"
  let ?f = "\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). padd T (fst p) (snd p)"
  have spB: "space ?B = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have into: "?f p \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if p: "p \<in> space ?M" for p
  proof -
    have "fst p \<in> space ?B" and "snd p \<in> space ?B"
      using p by (auto simp: space_pair_measure)
    then show ?thesis using spB by (auto intro: padd_mspace)
  qed
  have ev: "(\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). ?f p t) \<in> borel_measurable ?M"
    for t
  proof (cases "t \<in> {0..T}")
    case True
    have e1: "(\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). fst p t) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_fst
            pair_law_eval_measurable[OF refl]])
    have e2: "(\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). snd p t) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd
            pair_law_eval_measurable[OF refl]])
    have "(\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). fst p t + snd p t)
        \<in> borel_measurable ?M"
      using e1 e2 by simp
    then show ?thesis by (simp add: padd_apply[OF True])
  next
    case False
    have "(\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). ?f p t)
        = (\<lambda>p. undefined)"
      by (rule ext) (rule padd_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>p. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric) (?f p) a)
        \<in> borel_measurable ?M"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

text \<open>The glue inverts the split.  There is no membership hypothesis on
  \<open>\<omega>\<close> beyond being a path: \<open>pstopped_add_pafter\<close> is
  unconditional and \<^const>\<open>padd\<close> restricts to \<open>{0..T}\<close>, where a member of
  the path space already lives.\<close>

text \<open>The split inverts the glue, provided the continuation stands still up
  to \<open>\<theta>\<close> --- which is exactly clause (ii) of the kernel's membership in the
  class.  The stopping time reads only the stopped factor, because on
  \<open>[0, \<theta> p']\<close> the glue agrees with it.\<close>

lemma pfut_measurable:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "pfut r T
      \<in> (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
        \<rightarrow>\<^sub>M (path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pfut[OF r rT])

lemma pfut_measurable_law:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "pfut r T \<in> Q \<rightarrow>\<^sub>M (path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  using pfut_measurable[OF r rT] measurable_cong_sets[OF setsQ refl] by blast

text \<open>The exit time of the future, expressed through \<open>pfut\<close>: re-basing at the
  endpoint and adding the endpoint back is the identity on the exit time.\<close>

text \<open>Conditioning on an event of the past keeps martingales martingales:
  \<open>uniform_measure_density_real\<close>, \<open>integral_uniform_measure_eq\<close>,
  \<open>integrable_uniform_measureI\<close>, \<open>set_integral_uniform_measure_eq\<close> and
  \<open>martingale_uniform_measure\<close> live in
  @{theory Continuous_Time_Martingales.Martingale_Transfer}.\<close>

text \<open>\<open>pair_fst_borel\<close> lives in \<open>Exit_Class_Pasting\<close>.\<close>

lemma pshift_measurable:
  fixes x :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "pshift T x
      \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pshift[OF T])

text \<open>The shift is measurable for the natural filtration too, at every
  level: it changes values, not times.  This is what lets the martingale
  clauses be transported --- the past of the shifted path is the shifted
  past.\<close>

lemma pshift_filtration_measurable:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "pshift T x \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) u"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have spF: "space ?F = space Q" by simp
  show ?thesis
  proof (rule measurable_sigma_sets[OF sets_natural_filtration])
    show "(\<Union>i\<in>{0..u}. {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})
        \<subseteq> Pow (space Q)"
      by auto
    show "pshift T x \<in> space ?F \<rightarrow> space Q"
      using spQ spF by (auto intro: pshift_in_mspace)
    fix y
    assume "y \<in> (\<Union>i\<in>{0..u}.
        {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q | A. A \<in> sets borel})"
    then obtain i A where i: "i \<in> {0..u}" and A: "A \<in> sets borel"
      and y: "y = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space Q" by blast
    have shim: "pshift T x \<omega> \<in> space Q" if "\<omega> \<in> space Q" for \<omega>
      using that spQ by (simp add: pshift_in_mspace)
    show "pshift T x -` y \<inter> space ?F \<in> sets ?F"
    proof (cases "i \<in> {0..T}")
      case True
      define g where "g = (\<lambda>p :: (real^'n) \<times> (real^'n^'n). (x + fst p, snd p))"
      have gb: "g \<in> borel_measurable borel"
        unfolding g_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have gA: "g -` A \<in> sets borel"
        using measurable_sets[OF gb A] by simp
      have "pshift T x -` y \<inter> space ?F
          = (\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` (g -` A) \<inter> space Q"
        using True y spF shim by (auto simp: pshift_apply g_def)
      moreover have "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` (g -` A) \<inter> space Q \<in> sets ?F"
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
            fix \<omega> :: "'n pairpath" assume w: "\<omega> \<in> space ?F"
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
          then obtain \<omega> :: "'n pairpath" where "pshift T x \<omega> \<in> y" by blast
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
  fixes z y :: "real^'n::finite"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "mdist (path_metric T :: ('n pairpath) metric)
      (pshift T z \<omega>) (pshift T y \<omega>) \<le> dist z y"
proof -
  have sz: "pshift T z \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pshift_in_mspace[OF w])
  have sy: "pshift T y \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
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
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  shows "pexit U K (\<lambda>t. fst (pcut U \<omega> t)) = pexit U K (\<lambda>t. fst (\<omega> t))"
  by (rule pexit_cong_on) (simp add: pcut_apply)

definition pglue :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b::ab_group_add) \<Rightarrow> (real \<Rightarrow> 'b)
    \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pglue r T \<omega> \<omega>' =
     restrict (\<lambda>t. if t \<le> r then \<omega> t else \<omega> r + (\<omega>' (t - r) - \<omega>' 0)) {0..T}"

lemma pexit_pshift:
  fixes y :: "real^'n::finite" and \<omega> :: "'n pairpath"
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
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pcut r (pglue r T \<omega> \<omega>') = \<omega>"
proof -
  have "pcut r (pglue r T \<omega> \<omega>') = pcut r \<omega>" by (rule pcut_pglue[OF r rT])
  also have "\<dots> = \<omega>" unfolding pcut_def by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

text \<open>The almost-sure transfer through a glue, with the underlying measure
  \<open>Q\<close> left free, so that unfolding \<open>pair_law_of_def\<close> cannot
  also unfold a \<open>pair_law_of\<close> hiding inside \<open>Q\<close> itself.\<close>

lemma padd_measurable_ksemi:
  fixes Q :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "(\<lambda>p :: ((real \<Rightarrow> 'a \<times> 'b)) \<times> ((real \<Rightarrow> 'a \<times> 'b)). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have s: "sets (Q \<Otimes>\<^sub>M ?B) = sets (?B \<Otimes>\<^sub>M ?B)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  show ?thesis
    unfolding measurable_cong_sets[OF s refl] by (rule padd_measurable[OF T0])
qed

lemma pglue_ge:
  "t \<in> {0..T} \<Longrightarrow> r \<le> t \<Longrightarrow> pglue r T \<omega> \<omega>' t = \<omega> r + (\<omega>' (t - r) - \<omega>' 0)"
  by (cases "t = r") (auto simp: pglue_def)

lemma pexit_pglue_split':
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and c: "0 \<le> c" and cT: "r + c \<le> T"
    and stay: "\<And>t. t \<in> {0..r} \<Longrightarrow> fst (\<omega> t) \<in> K"
    and cont: "\<And>s. 0 \<le> s \<Longrightarrow> s < c \<Longrightarrow> fst (\<omega> r + (\<omega>' s - \<omega>' 0)) \<in> K"
  shows "r + c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
proof -
  have lb: "r + c \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue r T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zI: "z \<in> {0..T}" by simp
      show ?thesis
      proof (rule ccontr)
        assume "\<not> r + c \<le> z"
        then have zc: "z < r + c" by simp
        show False
        proof (cases "z \<le> r")
          case True
          have "fst (\<omega> z) \<in> K" using hit(1) True by (intro stay) simp
          then show False using hit(3) by (simp add: pglue_le[OF zI True])
        next
          case False
          then have rz: "r \<le> z" by simp
          have "fst (\<omega> r + (\<omega>' (z - r) - \<omega>' 0)) \<in> K"
            using rz zc by (intro cont) simp_all
          then show False using hit(3) by (simp add: pglue_ge[OF zI rz])
        qed
      qed
    next
      case cap
      then show ?thesis using cT by simp
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "r + c \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
      \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

text \<open>The pathwise dynamic programming bound at a deterministic time \<open>r\<close>.
  The two summands are the paper's \<open>r \<and> \<tau>\<^sub>K\<close> and \<open>v(X\<^sub>r) \<sqdot> 1\<^sub>{r \<le> \<tau>\<^sub>K}\<close>: the
  first piece's exit time is a lower bound in all cases (\<open>pexit_pglue_ge\<close>), and when it has not exited by \<open>r\<close> --- exactly
  \<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close> --- the continuation adds its own
  survival time on top.\<close>

lemma pglue_zero: "0 \<le> r \<Longrightarrow> 0 \<le> T \<Longrightarrow> pglue r T \<omega> \<omega>' 0 = \<omega> 0"
  by (rule pglue_le) auto

lemma pglue_in_mspace:
  fixes \<omega> \<omega>' :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and w': "\<omega>' \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pglue r T \<omega> \<omega>' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  unfolding pglue_def
  by (rule mspace_path_metricI[OF continuous_on_pglue[OF r rT
        mspace_path_metricD[OF w] mspace_path_metricD[OF w']]])

lemma pglue_measurable:
  fixes Q R :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and setsR: "sets R = sets ((path_borel (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) measure))"
  shows "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M
      (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  have T0: "0 \<le> T" using r rT by simp
  have eQ: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b). fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b). snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_snd
          pair_law_eval_measurable[OF setsR]])
  have Xm: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b).
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" for t
    using eQ eR by simp
  have cont: "continuous_on {0..T} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "(real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b)"
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

lemma pcut_id_on_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes "\<omega> \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pcut r \<omega> = \<omega>"
proof -
  have "\<omega> \<in> extensional {0..r}"
    using assms unfolding path_metric_def mspace_cfunspace by simp
  then show ?thesis unfolding pcut_def by (rule extensional_restrict)
qed

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
  fixes Q R :: "((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure"
  assumes r: "0 \<le> r"
    and setsQ: "sets Q = sets (path_borel r :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
    and setsR: "sets R = sets (ipath_space :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  shows "(\<lambda>p. iglue r (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M R \<rightarrow>\<^sub>M ipath_space"
proof -
  have eQ: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b). fst p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    for v
    by (rule measurable_compose[OF measurable_fst
          pair_law_eval_measurable[OF setsQ]])
  have eR: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b). snd p v) \<in> borel_measurable (Q \<Otimes>\<^sub>M R)"
    if v: "0 \<le> v" for v
  proof -
    have "(\<lambda>f :: (real \<Rightarrow> 'a \<times> 'b). f v) \<in> borel_measurable R"
      unfolding measurable_cong_sets[OF setsR refl]
      by (rule ipath_eval_measurable[OF v])
    then show ?thesis by (rule measurable_compose[OF measurable_snd])
  qed
  have Xm: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b).
        if t \<le> r then fst p t else fst p r + (snd p (t - r) - snd p 0))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" if t: "0 \<le> t" for t
  proof (cases "t \<le> r")
    case True
    then show ?thesis using eQ by simp
  next
    case False
    have m2: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b). snd p (t - r))
        \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" using False by (intro eR) simp
    have m3: "(\<lambda>p :: (real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b). snd p 0)
        \<in> borel_measurable (Q \<Otimes>\<^sub>M R)" by (rule eR) simp
    show ?thesis unfolding if_not_P[OF False]
      by (intro borel_measurable_add borel_measurable_diff eQ m2 m3)
  qed
  have cont: "continuous_on {0..} (\<lambda>t. if t \<le> r then fst p t
        else fst p r + (snd p (t - r) - snd p 0))"
    if p: "p \<in> space (Q \<Otimes>\<^sub>M R)" for p :: "(real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b)"
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
  fixes \<omega> :: "'n::finite pairpath"
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

definition pfst :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> (real \<Rightarrow> real^'n)"
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
  fixes \<omega> :: "'n::finite pairpath"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
proof -
  have "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))" by (intro continuous_intros)
  then show ?thesis unfolding pfst_def by (rule mspace_path_metricI)
qed

lemma Lipschitz_pfst:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n::finite pairpath) metric)
      (path_metric T :: (real \<Rightarrow> real^'n) metric) (pfst T)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pfst T \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
    by (intro funcsetI pfst_mspace[OF T])
  have key: "mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
        (pfst T \<omega>) (pfst T \<omega>')
      \<le> 1 * mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
    if w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and w': "\<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)" for \<omega> \<omega>'
  proof -
    have rw: "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
      by (rule pfst_mspace[OF T w])
    have rw': "pfst T \<omega>' \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
      by (rule pfst_mspace[OF T w'])
    have pw: "\<forall>t\<in>{0..T}. dist (\<omega> t) (\<omega>' t)
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      using path_mdist_le_iff_all[OF T w w'] by blast
    have pwr: "dist (pfst T \<omega> t) (pfst T \<omega>' t)
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      if t: "t \<in> {0..T}" for t
    proof -
      have "dist (fst (\<omega> t)) (fst (\<omega>' t)) \<le> dist (\<omega> t) (\<omega>' t)"
        by (rule dist_fst_le)
      then show ?thesis using bspec[OF pw t] t by (simp add: pfst_def)
    qed
    have "mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
          (pfst T \<omega>) (pfst T \<omega>')
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      using path_mdist_le_iff_all[OF T rw rw'] pwr by blast
    then show ?thesis by simp
  qed
  show "\<exists>B. \<forall>\<omega>\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>\<omega>'\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
            (pfst T \<omega>) (pfst T \<omega>')
          \<le> B * mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
    by (intro exI[of _ 1] ballI key)
qed

lemma pexit_pfst: "pexit S K (pfst S \<omega>) = pexit S K (\<lambda>t. fst (\<omega> t))"
proof -
  have "{r. 0 \<le> r \<and> r \<le> S \<and> pfst S \<omega> r \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> S \<and> fst (\<omega> r) \<in> - K}"
    by (auto simp: pfst_def)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma pfst_measurable:
  fixes N :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S"
    and setsN: "sets N = sets (path_borel S :: ('n pairpath) measure)"
  shows "pfst S \<in> N \<rightarrow>\<^sub>M (path_borel S :: ((real \<Rightarrow> real^'n)) measure)"
  unfolding pfst_def
proof (rule pathify_measurable[OF S])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  fix t :: real assume "t \<in> {0..S}"
  show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> t)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsN] fstB])
next
  fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space N"
  then have "\<omega> \<in> mspace (path_metric S :: ('n pairpath) metric)"
    using space_of_path_sets[OF setsN] by simp
  then have "continuous_on {0..S} \<omega>" by (rule mspace_path_metricD)
  then show "continuous_on {0..S} (\<lambda>t. fst (\<omega> t))"
    by (intro continuous_intros)
qed

text \<open>\<open>ennreal_min_eq\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>

lemma ess_inf_time_pfst:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "ess_inf_time (distr Q (path_borel T :: (real \<Rightarrow> real^'n) measure) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  have "ess_inf_time (distr Q (path_borel T :: (real \<Rightarrow> real^'n) measure) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (pfst T \<omega>))"
    by (rule ess_inf_time_distr_measurable
        [OF pfst_measurable[OF T setsQ] pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

lemma pexit_pcut_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> :: "'n pairpath"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "min (pexit T K (\<lambda>t. fst (\<omega> t))) S
      \<le> pexit S K (\<lambda>t. fst (pcut S \<omega> t))"
proof -
  have T0: "0 \<le> T" using S ST by simp
  have lb: "min (pexit T K (\<lambda>t. fst (\<omega> t))) S \<le> z"
    if z: "z \<in> {r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S}"
    for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> S" "fst (pcut S \<omega> z) \<in> - K" | (cap) "z = S"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zT: "z \<le> T" using ST by simp
      have notin: "fst (\<omega> z) \<in> - K"
        using hit by (simp add: pcut_apply)
      have "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> z"
        unfolding pexit_def
        by (rule etime_le_of_mem[OF T0 hit(1) zT]) (use notin in simp)
      then show ?thesis using hit(2) by simp
    next
      case cap
      then show ?thesis by simp
    qed
  qed
  have "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
      = Inf ({r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S})"
    unfolding pexit_def etime_def ..
  moreover have "min (pexit T K (\<lambda>t. fst (\<omega> t)))  S
      \<le> Inf ({r. 0 \<le> r \<and> r \<le> S \<and> (\<lambda>t. fst (pcut S \<omega> t)) r \<in> - K} \<union> {S})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

lemma pexit_pshift_eq_etime:
  fixes \<omega> :: "'n::finite pairpath" and K :: "(real^'n) set" and x :: "real^'n"
  shows "pexit T K (\<lambda>t. fst (pshift T x \<omega> t))
       = etime T {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}
           (\<lambda>s w. (x, 0) + w s) \<omega>"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> fst (pshift T x \<omega> r) \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> T
            \<and> (x, 0) + \<omega> r \<in> {p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}}"
    by (auto simp: pshift_fst)
  then show ?thesis unfolding pexit_def etime_def by simp
qed

subsection \<open>Turning a supremum of \<open>ennreal\<close>s into a supremum of reals\<close>

text \<open>\<open>ennreal_Sup_image\<close> lives in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


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
  fixes w wt w' wt' :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "w \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and wt: "wt \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and w': "w' \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    and wt': "wt' \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pglue r T w w') (pglue r T wt wt')
      \<le> mdist (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric) w wt
        + 2 * mdist (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric) w' wt'"
proof -
  let ?d1 = "mdist (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric) w wt"
  let ?d2 = "mdist (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric) w' wt'"
  have T0: "0 \<le> T" using r rT by simp
  have Tr0: "0 \<le> T - r" using rT by simp
  have g1: "pglue r T w w' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (rule pglue_in_mspace[OF r rT w w'])
  have g2: "pglue r T wt wt' \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
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
      (prod_metric (path_metric r :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) metric)
        (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric))
      (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
      (\<lambda>p. pglue r T (fst p) (snd p))"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> mspace (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
          (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric))
        \<rightarrow> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    using pglue_in_mspace[OF r rT] by (intro funcsetI) auto
  show "\<exists>B. \<forall>p \<in> mspace (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
          (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)).
      \<forall>q \<in> mspace (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
          (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)).
        mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
            ((\<lambda>p. pglue r T (fst p) (snd p)) p) ((\<lambda>p. pglue r T (fst p) (snd p)) q)
          \<le> B * mdist (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
              (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)) p q"
  proof (intro exI[of _ 3] ballI)
    fix p q :: "(real \<Rightarrow> 'a \<times> 'b) \<times> (real \<Rightarrow> 'a \<times> 'b)"
    assume p: "p \<in> mspace (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric))"
      and q: "q \<in> mspace (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric))"
    from p have p1: "fst p \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      and p2: "snd p \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      by auto
    from q have q1: "fst q \<in> mspace (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      and q2: "snd q \<in> mspace (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      by auto
    let ?a = "mdist (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric) (fst p) (fst q)"
    let ?b = "mdist (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric) (snd p) (snd q)"
    let ?pd = "mdist (prod_metric (path_metric r :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (path_metric (T - r) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)) p q"
    have pdeq: "?pd = sqrt (?a\<^sup>2 + ?b\<^sup>2)"
      by (simp add: prod_dist_def case_prod_unfold)
    have c1: "?a \<le> ?pd"
    proof -
      have "?a = sqrt (?a\<^sup>2)" by simp
      also have "\<dots> \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2)" by (simp add: real_sqrt_le_mono)
      finally show ?thesis using pdeq by simp
    qed
    have c2: "?b \<le> ?pd"
    proof -
      have "?b = sqrt (?b\<^sup>2)" by simp
      also have "\<dots> \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2)" by (simp add: real_sqrt_le_mono)
      finally show ?thesis using pdeq by simp
    qed
    have "mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pglue r T (fst p) (snd p)) (pglue r T (fst q) (snd q)) \<le> ?a + 2 * ?b"
      by (rule mdist_pglue_le[OF r rT p1 q1 p2 q2])
    also have "\<dots> \<le> 3 * ?pd" using c1 c2 by simp
    finally show "mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        ((\<lambda>p. pglue r T (fst p) (snd p)) p) ((\<lambda>p. pglue r T (fst p) (snd p)) q)
        \<le> 3 * ?pd" by simp
  qed
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

definition pcoord :: "real \<Rightarrow> 'n::finite \<Rightarrow> real \<Rightarrow> ('n pairpath) \<Rightarrow> real"
  where "pcoord T i u \<omega> = fst (\<omega> (min u T)) $ i"

definition ploc :: "real \<Rightarrow> 'n::finite \<Rightarrow> real \<Rightarrow> ('n pairpath) \<Rightarrow> real"
  where "ploc T i R \<omega> = etime T {y. R \<le> \<bar>y\<bar>} (pcoord T i) \<omega>"

text \<open>\<open>closed_abs_ge\<close>, \<open>abs_ge_nonempty\<close> live in @{theory Semicontinuous_Analysis.Semicontinuity}.\<close>

lemma pexit_pglue_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))"
proof -
  have lb: "pexit S K (\<lambda>t. fst (\<omega> t)) \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue S T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      show ?thesis
      proof (cases "z \<le> S")
        case True
        have zI: "z \<in> {0..T}" using hit by simp
        have notin: "fst (\<omega> z) \<in> - K"
          using hit True by (simp add: pglue_le[OF zI])
        show ?thesis
          unfolding pexit_def
          by (rule etime_le_of_mem[OF S hit(1) True]) (use notin in simp)
      next
        case False
        then show ?thesis
          using pexit_le_T[OF S, of K "\<lambda>t. fst (\<omega> t)"] by linarith
      qed
    next
      case cap
      then show ?thesis
        using pexit_le_T[OF S, of K "\<lambda>t. fst (\<omega> t)"] ST by linarith
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue S T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "pexit S K (\<lambda>t. fst (\<omega> t))
      \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue S T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

lemma pexit_pglue_dpp:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and c: "0 \<le> c" and cT: "r + c \<le> T"
    and z0: "fst (\<omega>' 0) = 0"
    and cont: "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<Longrightarrow> fst (\<omega> r) \<in> K
        \<Longrightarrow> c \<le> pexit (T - r) K (\<lambda>s. fst (\<omega> r) + fst (\<omega>' s))"
  shows "pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then c else 0)
      \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
proof (cases "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K")
  case True
  then have full: "pexit r K (\<lambda>t. fst (\<omega> t)) = r" and endK: "fst (\<omega> r) \<in> K"
    by simp_all
  have cnt: "c \<le> pexit (T - r) K (\<lambda>s. fst (\<omega> r) + fst (\<omega>' s))"
    by (rule cont[OF full endK])
  have "r + c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
  proof (rule pexit_pglue_split'[OF r rT c cT])
    fix t assume t: "t \<in> {0..r}"
    show "fst (\<omega> t) \<in> K"
    proof (rule ccontr)
      assume nk: "fst (\<omega> t) \<notin> K"
      have "pexit r K (\<lambda>t. fst (\<omega> t)) \<le> t"
        unfolding pexit_def using r t nk by (intro etime_le_of_mem) auto
      with full t have "t = r" by simp
      then show False using nk endK by simp
    qed
  next
    fix s :: real assume s: "0 \<le> s" and sc: "s < c"
    have sTr: "s \<le> T - r" using sc c cT by simp
    show "fst (\<omega> r + (\<omega>' s - \<omega>' 0)) \<in> K"
    proof (rule ccontr)
      assume nk: "fst (\<omega> r + (\<omega>' s - \<omega>' 0)) \<notin> K"
      have eq: "fst (\<omega> r + (\<omega>' s - \<omega>' 0)) = fst (\<omega> r) + fst (\<omega>' s)"
        using z0 by simp
      have "pexit (T - r) K (\<lambda>s. fst (\<omega> r) + fst (\<omega>' s)) \<le> s"
        unfolding pexit_def using s sTr rT nk eq by (intro etime_le_of_mem) auto
      with cnt sc show False by simp
    qed
  qed
  then show ?thesis using True by simp
next
  case False
  have le: "pexit r K (\<lambda>t. fst (\<omega> t)) \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
    by (rule pexit_pglue_ge[OF r rT])
  have "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then c else 0) = 0"
    using False by (rule if_not_P)
  with le show ?thesis by simp
qed

subsection \<open>The selector as a kernel into a family of laws\<close>

text \<open>\<open>exit_val_measurable_selector_kernel'\<close> below makes the selector
  a Giry-monad kernel, hypothesis \<^emph>\<open>Kp\<close> of \<open>exit_class_kglue_law'\<close>.  The other hypothesis, \<^emph>\<open>Kb\<close>
  (measurability into the class with its Levy-Prokhorov metric), is free:
  the selector lands in the subspace, and \<open>exit_class_compact_metric_space\<close> identifies the class's metric
  topology with the subspace topology of weak convergence.\<close>

lemma ploc_nonneg: "0 \<le> T \<Longrightarrow> 0 \<le> ploc T i R \<omega>"
  unfolding ploc_def by (rule etime_nonneg)

lemma pcoord_stopped_bounded:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T: "0 \<le> T" and R: "0 < R"
    and start: "\<bar>pcoord T i 0 \<omega>\<bar> < R"
    and cont: "continuous_on {0..T} (\<lambda>s. pcoord T i s \<omega>)"
    and v: "0 \<le> v"
  shows "\<bar>pcoord T i (min v (ploc T i R \<omega>)) \<omega>\<bar> \<le> R"
proof -
  have nrm: "{y :: real. R \<le> \<bar>y\<bar>} = {y. R \<le> norm y}" by simp
  have s0: "0 \<le> min v (ploc T i R \<omega>)"
    using v ploc_nonneg[OF T, of i R \<omega>] by simp
  have sle: "min v (ploc T i R \<omega>)
      \<le> etime T {y. R \<le> norm y} (pcoord T i) \<omega>"
    unfolding ploc_def[symmetric] nrm[symmetric] by simp
  have "pcoord T i (min v (ploc T i R \<omega>)) \<omega> \<in> cball 0 R"
    using start cont
    by (intro etime_stays_in_cball[OF T R _ _ s0 sle]) simp_all
  then show ?thesis by (simp add: dist_real_def)
qed

subsection \<open>Optional stopping at the localizing time\<close>

text \<open>\<open>Optional_Sampling.optional_stopping\<close> asks for an integrable
  envelope of the unstopped process, which the market locale could not
  supply but a class member has: \<open>Doob_Inequality.horizon_sq_int_martingale\<close>
  builds \<open>Dsup\<close> from Doob's \<open>L\<^sup>2\<close> inequality out of nothing but
  square-integrability, which \<open>exit_class_sq_integrable\<close>
  provides.\<close>

lemma pexit_path_measurable:
  fixes K :: "(real^'n::finite) set" and N :: "('n pairpath) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
  shows "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable N"
proof -
  have "(\<lambda>\<omega> :: 'n pairpath. pexit T K (pfst T \<omega>)) \<in> borel_measurable N"
    by (rule measurable_compose[OF pfst_measurable[OF T setsN]
          pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

lemma survival_set_measurable:
  fixes K :: "(real^'n::finite) set"
  assumes r: "0 \<le> r" and Kc: "closed K"
  shows "{p' \<in> space (path_borel r :: ('n pairpath) measure).
      pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K}
    \<in> sets (path_borel r :: ('n pairpath) measure)"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  have pm: "(\<lambda>p' :: 'n pairpath. pexit r K (\<lambda>t. fst (p' t)))
      \<in> borel_measurable ?X"
    by (rule pexit_path_measurable[OF r Kc refl])
  have em: "(\<lambda>p' :: 'n pairpath. fst (p' r)) \<in> borel_measurable ?X"
    by (rule measurable_compose
        [OF pair_law_eval_measurable[OF refl] pair_fst_borel])
  have s1: "{p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r} \<in> sets ?X"
    using pm by measurable
  have s2: "{p' \<in> space ?X. fst (p' r) \<in> K} \<in> sets ?X"
    using em borel_closed[OF Kc] by (simp add: measurable_sets_Collect)
  have "{p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K}
      = {p' \<in> space ?X. pexit r K (\<lambda>t. fst (p' t)) = r}
        \<inter> {p' \<in> space ?X. fst (p' r) \<in> K}" by auto
  then show ?thesis using sets.Int[OF s1 s2] by simp
qed

text \<open>The conditioning statement itself, discharging the hypothesis of
  \<open>exit_val_dpp_le_of_cond\<close> and hence the DPP at a deterministic
  time.  The chain is:

  \<^item> the hypothesis becomes a measurable property of the pair
    \<open>(pcut r \<omega>, pfut r T \<omega>)\<close>, by \<open>pglue_pcut_pfut\<close>;
  \<^item> @{thm [source] AE_ksemi} disintegrates it along the r.c.d.;
  \<^item> \<open>exit_class_rcd_member\<close> says the r.c.d. lands in the
    class at the origin, so at a fixed good \<open>p'\<close> the surviving future is a
    class member started at \<open>0\<close> and shifted by the constant \<open>fst (p' r)\<close>;
  \<^item> \<open>exit_val_ge_of_AE_pshift\<close> turns the almost-sure lower bound
    on its exit time into a lower bound for \<open>exit_val\<close> at that point.

  No localization and no \<open>K\<^sub>\<epsilon>\<close> are needed: the starting point is a single
  vector.\<close>

lemma pexit_pglue_split:
  fixes K :: "(real^'n::finite) set" and \<omega> \<omega>' :: "'n pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and c: "0 \<le> c" and cT: "r + c \<le> T"
    and stay: "\<And>t. t \<in> {0..r} \<Longrightarrow> fst (\<omega> t) \<in> K"
    and cont: "\<And>s. s \<in> {0..c} \<Longrightarrow> fst (\<omega> r + (\<omega>' s - \<omega>' 0)) \<in> K"
  shows "r + c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
proof -
  have lb: "r + c \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T
        \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "fst (pglue r T \<omega> \<omega>' z) \<in> - K" | (cap) "z = T"
      using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zI: "z \<in> {0..T}" by simp
      show ?thesis
      proof (rule ccontr)
        assume "\<not> r + c \<le> z"
        then have zc: "z < r + c" by simp
        show False
        proof (cases "z \<le> r")
          case True
          have "fst (\<omega> z) \<in> K" using hit(1) True by (intro stay) simp
          then show False using hit(3) by (simp add: pglue_le[OF zI True])
        next
          case False
          then have rz: "r \<le> z" by simp
          have "z - r \<in> {0..c}" using rz zc by simp
          then have "fst (\<omega> r + (\<omega>' (z - r) - \<omega>' 0)) \<in> K" by (rule cont)
          then show False using hit(3) by (simp add: pglue_ge[OF zI rz])
        qed
      qed
    next
      case cap
      then show ?thesis using cT by simp
    qed
  qed
  have "pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))
      = Inf ({t. 0 \<le> t \<and> t \<le> T
          \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "r + c \<le> Inf ({t. 0 \<le> t \<and> t \<le> T
      \<and> (\<lambda>t. fst (pglue r T \<omega> \<omega>' t)) t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
qed

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

lemma pembed_mspace:
  fixes w :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pembed s T w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have c: "continuous_on {0..T - s} w" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. max (t - s) 0)"
    by (intro continuous_intros)
  have im: "(\<lambda>t. max (t - s) 0) ` {0..T} \<subseteq> {0..T - s}" using s0 sT by auto
  have "continuous_on {0..T} (\<lambda>t. w (max (t - s) 0))"
    by (rule continuous_on_compose2[OF c m im])
  then show ?thesis unfolding pembed_def by (rule mspace_path_metricI)
qed

lemma pembed_mspace_full:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pembed s T \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. max (t - s) 0)"
    by (intro continuous_intros)
  have im: "(\<lambda>t. max (t - s) 0) ` {0..T} \<subseteq> {0..T}" using s0 sT by auto
  have "continuous_on {0..T} (\<lambda>t. \<omega> (max (t - s) 0))"
    by (rule continuous_on_compose2[OF c m im])
  then show ?thesis unfolding pembed_def by (rule mspace_path_metricI)
qed

definition pdel :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b)"
  where "pdel s T = pembed (max 0 (min s T)) T"

lemma pdel_eq_pembed: "0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> pdel s T = pembed s T"
  unfolding pdel_def by simp

lemma pdel_mspace:
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes T0: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "pdel s T \<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
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
  fixes w :: "'n::finite pairpath" and y :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and frz: "\<And>t. t \<in> {0..T} \<Longrightarrow> t \<le> r \<Longrightarrow> w t = 0"
    and inK: "y \<in> K"
  shows "r + pexit (T - r) K (\<lambda>u. y + fst (prebase r T w u))
      \<le> pexit T K (\<lambda>s. y + fst (w s))"
proof -
  let ?g = "\<lambda>s. y + fst (w s)"
  let ?h = "\<lambda>u. y + fst (prebase r T w u)"
  have T0: "0 \<le> T" using r rT by simp
  have Tr: "0 \<le> T - r" using rT by simp
  have lb: "r + pexit (T - r) K ?h \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T \<and> ?g t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "?g z \<in> - K" | (cap) "z = T" using z by blast
    then show ?thesis
    proof cases
      case cap
      have "pexit (T - r) K ?h \<le> T - r" by (rule pexit_le_T[OF Tr])
      then show ?thesis unfolding cap by simp
    next
      case hit
      then have zm: "z \<in> {0..T}" by simp
      have zr: "r < z"
      proof (rule ccontr)
        assume "\<not> r < z"
        then have "z \<le> r" by simp
        then have "w z = 0" by (rule frz[OF zm])
        then have "?g z = y" by simp
        then show False using hit(3) inK by simp
      qed
      have um: "z - r \<in> {0..T - r}" using zr hit(2) by simp
      have pe: "prebase r T w (z - r) = w z"
      proof -
        have "prebase r T w (z - r) = w (r + (z - r))" by (rule prebase_apply[OF um])
        then show ?thesis by simp
      qed
      have mem: "?h (z - r) \<in> - K" using hit(3) pe by simp
      have "pexit (T - r) K ?h \<le> z - r"
        unfolding pexit_def
        by (rule etime_le_of_mem[OF Tr _ _]) (use um mem in auto)
      then show ?thesis by simp
    qed
  qed
  have "pexit T K ?g = Inf ({t. 0 \<le> t \<and> t \<le> T \<and> ?g t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "r + pexit (T - r) K ?h
      \<le> Inf ({t. 0 \<le> t \<and> t \<le> T \<and> ?g t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
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
  shows "pembed s T \<in> (path_borel (T - s) :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?Bs = "(path_borel (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have T0: "0 \<le> T" using s0 sT by simp
  have into: "pembed s T w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if "w \<in> space ?Bs" for w
    using that by (auto simp: space_borel_of intro: pembed_mspace[OF s0 sT])
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). pembed s T w t) \<in> borel_measurable ?Bs" for t
  proof (cases "t \<in> {0..T}")
    case True
    have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). w (max (t - s) 0)) \<in> borel_measurable ?Bs"
      by (rule pair_law_eval_measurable[OF refl])
    then show ?thesis by (simp add: pembed_apply[OF True])
  next
    case False
    have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). pembed s T w t) = (\<lambda>w. undefined)"
      by (rule ext) (rule pembed_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>w. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pembed s T w) a) \<in> borel_measurable ?Bs"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
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
  shows "pembed s T \<in> (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have a: "0 \<le> T - s" using sT by simp
  have b: "T - s \<le> T" using s0 by simp
  have eq: "(\<lambda>\<omega> :: (real \<Rightarrow> 'a \<times> 'b). pembed s T (pcut (T - s) \<omega>)) = pembed s T"
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
  shows "pdel s T \<in> (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  unfolding pdel_def
  by (rule pembed_measurable_full[OF pdel_clamp_lo pdel_clamp_hi[OF T0]])

lemma pdel_measurable_pair:
  assumes T0: "0 \<le> T"
  shows "(\<lambda>p. pdel (fst p) T (snd p))
      \<in> (borel :: real measure) \<Otimes>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
        \<rightarrow>\<^sub>M (path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  let ?M = "(borel :: real measure) \<Otimes>\<^sub>M ?B"
  have spM: "space ?M = UNIV \<times> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_pair_measure space_borel_of)
  have into: "pdel (fst p) T (snd p)
      \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)" if p: "p \<in> space ?M" for p
  proof -
    have "p \<in> UNIV \<times> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      using p unfolding spM .
    then have "snd p \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      by (simp add: mem_Times_iff)
    then show ?thesis by (rule pdel_mspace[OF T0])
  qed
  have sndm: "(\<lambda>p :: real \<times> ((real \<Rightarrow> 'a \<times> 'b)). snd p) \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule measurable_snd)
  have ev: "(\<lambda>p. pdel (fst p) T (snd p) t) \<in> borel_measurable ?M" for t
  proof (cases "t \<in> {0..T}")
    case True
    have gm: "(\<lambda>p :: real \<times> ((real \<Rightarrow> 'a \<times> 'b)). max (t - max 0 (min (fst p) T)) 0)
        \<in> borel_measurable ?M" by measurable
    have g0: "0 \<le> max (t - max 0 (min (fst p) T)) 0"
      for p :: "real \<times> ((real \<Rightarrow> 'a \<times> 'b))" by simp
    have gT: "max (t - max 0 (min (fst p) T)) 0 \<le> T"
      for p :: "real \<times> ((real \<Rightarrow> 'a \<times> 'b))" using True by auto
    have "(\<lambda>p :: real \<times> ((real \<Rightarrow> 'a \<times> 'b)).
        snd p (max (t - max 0 (min (fst p) T)) 0)) \<in> borel_measurable ?M"
      by (rule path_eval_at_measurable_time
          [where X = "\<lambda>p :: real \<times> ((real \<Rightarrow> 'a \<times> 'b)). snd p"
            and g = "\<lambda>p :: real \<times> ((real \<Rightarrow> 'a \<times> 'b)). max (t - max 0 (min (fst p) T)) 0",
            OF T0 sndm gm g0 gT])
    then show ?thesis using True by (simp add: pdel_eval)
  next
    case False
    then have "(\<lambda>p :: real \<times> ((real \<Rightarrow> 'a \<times> 'b)). pdel (fst p) T (snd p) t)
        = (\<lambda>p. undefined)"
      unfolding pdel_def by (simp add: pembed_outside)
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>p. mdist (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (pdel (fst p) T (snd p)) a) \<in> borel_measurable ?M"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

subsection \<open>Cutting a law commutes with shifting, and caps its value\<close>

lemma pembed_eval_le:
  fixes w :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes r0: "0 \<le> r" and ru: "r \<le> u" and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). pembed s T w r) \<in> borel_measurable
      (natural_filtration M 0 (\<lambda>v w. w v) (min (max (u - s) 0) (T - s)))"
proof (cases "r \<le> T")
  case True
  have e1: "0 \<le> max (r - s) 0" by simp
  have e2: "max (r - s) 0 \<le> min (max (u - s) 0) (T - s)"
    using r0 ru s0 sT True by (auto simp: min_def max_def)
  have mem: "r \<in> {0..T}" using r0 True by simp
  have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). w (max (r - s) 0)) \<in> borel_measurable
      (natural_filtration M 0 (\<lambda>v w. w v) (min (max (u - s) 0) (T - s)))"
    by (rule path_eval_natural_filtration[OF e1 e2])
  then show ?thesis by (simp add: pembed_apply[OF mem])
next
  case False
  then have "r \<notin> {0..T}" by simp
  then have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). pembed s T w r) = (\<lambda>w. undefined)"
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
  fixes w :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
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

lemma pcoord_stopped_paths_cont:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T: "0 \<le> T"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space Q"
  shows "continuous_on {0..} (\<lambda>s. pcoord T i (min s (ploc T i R \<omega>)) \<omega>)"
proof -
  have c: "continuous_on {0..} (\<lambda>s. pcoord T i s \<omega>)"
    unfolding pcoord_def
    by (rule exit_class_coord_paths_cont[OF T setsQ w])
  have m: "continuous_on {0..} (\<lambda>s :: real. min s (ploc T i R \<omega>))"
    by (intro continuous_intros)
  have mim: "(\<lambda>s :: real. min s (ploc T i R \<omega>)) ` {0..} \<subseteq> {0..}"
    using ploc_nonneg[OF T, of i R \<omega>] by auto
  show ?thesis by (rule continuous_on_compose2[OF c m mim])
qed

lemma prebase_mspace:
  fixes w :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
  shows "prebase s T w \<in> mspace (path_metric (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
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
  shows "prebase s T \<in> (path_borel T :: ((real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})) measure)
    \<rightarrow>\<^sub>M (path_borel (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
proof -
  let ?B = "(path_borel T :: ((real \<Rightarrow> 'a \<times> 'b)) measure)"
  have sp: "space ?B = mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    by (simp add: space_borel_of)
  have Ts: "0 \<le> T - s" using sT by simp
  have into: "prebase s T w \<in> mspace (path_metric (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    if "w \<in> space ?B" for w :: "(real \<Rightarrow> 'a \<times> 'b)"
  proof -
    have m: "w \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
      using that sp by simp
    show ?thesis by (rule prebase_mspace[OF s0 sT m])
  qed
  have ev: "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). prebase s T w u) \<in> borel_measurable ?B" for u
  proof (cases "u \<in> {0..T - s}")
    case True
    have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). w (s + u)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    then show ?thesis by (simp add: prebase_apply[OF True])
  next
    case False
    have "(\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). prebase s T w u) = (\<lambda>w :: (real \<Rightarrow> 'a \<times> 'b). undefined)"
      by (rule ext) (rule prebase_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "(real \<Rightarrow> 'a \<times> 'b)"
    assume am: "a \<in> mspace (path_metric (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
    show "(\<lambda>w. mdist (path_metric (T - s) :: ((real \<Rightarrow> 'a \<times> 'b)) metric)
        (prebase s T w) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF Ts into am ev])
  qed
qed
text \<open>Hence clause (i) for the kernel: re-based, the conditional law is a
  probability measure on the \<open>(T - \<theta>)\<close>-path space.\<close>

text \<open>Clause (ii) for the kernel.  The pathwise content is already there:
  \<open>pafter_before\<close> at \<open>t = \<theta> \<omega>\<close> says the future factor is still
  \<open>0\<close> when the clock starts, so all that is needed is to push it through the
  r.c.d., the same chain as the mixed glue's transfer:
  \<open>AE_distr_iff\<close> into the joint law, the r.c.d. equation, and
  @{thm [source] AE_ksemi} back out.  The stopping-time property is spent
  where the kernel is indexed by the stopped path: the clock has to be read
  off that, and \<open>path_stopping_time_stopped\<close> says it is the
  same number.\<close>

text \<open>Clause (iii) at one pair of times.  This is the analogue of the \<open>one\<close>
  step inside \<open>pfut_rcd_diffquot\<close>, and the pathwise content is
  free: after \<open>\<theta>\<close> the future factor's increments are \<open>\<omega>\<close>'s increments,
  because the \<open>- \<omega> (\<theta> \<omega>)\<close> cancels in the difference.  The guard
  \<open>\<theta> p' \<le> p\<close> lives inside the predicate, which makes the conditioning set a
  pair-set, so the transfer is the @{thm [source] AE_ksemi} chain of clause
  (ii) rather than \<open>AE_kernel_full\<close>, and the rational grid
  stays in the original time scale.\<close>

lemma ploc_eq_T_of_below:
  fixes \<omega> :: "'n::finite pairpath"
  assumes h: "\<And>r. 0 \<le> r \<Longrightarrow> r \<le> T \<Longrightarrow> \<bar>pcoord T i r \<omega>\<bar> < R"
  shows "ploc T i R \<omega> = T"
proof -
  have e: "{r. 0 \<le> r \<and> r \<le> T \<and> pcoord T i r \<omega> \<in> {y :: real. R \<le> \<bar>y\<bar>}} \<union> {T}
      = {T}"
    using h by fastforce
  show ?thesis unfolding ploc_def etime_def e by simp
qed

lemma padd_eval_split:
  fixes p' w :: "(real \<Rightarrow> 'a::real_normed_vector \<times> 'b::real_normed_vector)"
  assumes t: "t \<in> {0..T}"
  shows "fst (padd T p' w t) = fst (p' t) + fst (w t)"
    and "snd (padd T p' w t) = snd (p' t) + snd (w t)"
  by (simp_all add: padd_apply[OF t])

text \<open>The stopping-time analogue of @{thm [source] pexit_pglue_dpp}.  Because
  \<^const>\<open>padd\<close> keeps both factors on the original clock, the
  continuation's contribution is stated as a bound on \<open>pexit T K\<close> of the
  delayed path \<open>s \<mapsto> fst (p' r) + fst (w s)\<close> --- already including the
  \<open>r\<close> it stands still for --- rather than on a rebased horizon, exactly
  the form \<open>pdelclass\<close> produces.\<close>

lemma pexit_padd_dpp:
  fixes K :: "(real^'n::finite) set" and p' w :: "'n pairpath"
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
  let ?b = "?A + (if ?A = r \<and> fst (p' r) \<in> K then c else 0)"
  have T0: "0 \<le> T" using r rT by simp
  have Ar: "?A \<le> r" by (rule pexit_le_T[OF r])
  have ev: "?f t = fst (p' t) + fst (w t)" if t: "t \<in> {0..T}" for t
    unfolding padd_eval_split(1)[OF t] ..
  have lb: "?b \<le> z"
    if z: "z \<in> {t. 0 \<le> t \<and> t \<le> T \<and> ?f t \<in> - K} \<union> {T}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> T" "?f z \<in> - K" | (cap) "z = T" using z by blast
    then show ?thesis
    proof cases
      case cap
      have "(if ?A = r \<and> fst (p' r) \<in> K then c else 0) \<le> c" using c by simp
      with Ar cT show ?thesis unfolding cap by linarith
    next
      case hit
      then have zm: "z \<in> {0..T}" by simp
      show ?thesis
      proof (cases "?A = r \<and> fst (p' r) \<in> K")
        case False
        then have e0: "(if ?A = r \<and> fst (p' r) \<in> K then c else 0) = 0"
          by (rule if_not_P)
        have "?A \<le> z"
        proof (cases "z \<le> r")
          case True
          have fz: "?f z = fst (p' z)"
            unfolding ev[OF zm] using frz[OF zm True] by simp
          have mem: "fst (p' z) \<in> - K" using hit(3) fz by simp
          show ?thesis
            unfolding pexit_def
            by (rule etime_le_of_mem[OF r hit(1) True]) (use mem in simp)
        next
          case False
          then show ?thesis using Ar by simp
        qed
        then show ?thesis unfolding e0 by simp
      next
        case True
        then have Aeq: "?A = r" and inK: "fst (p' r) \<in> K" by blast+
        have e1: "(if ?A = r \<and> fst (p' r) \<in> K then c else 0) = c"
          using True by (rule if_P)
        have zr: "r < z"
        proof (rule ccontr)
          assume "\<not> r < z"
          then have zle: "z \<le> r" by simp
          have fz: "?f z = fst (p' z)"
            unfolding ev[OF zm] using frz[OF zm zle] by simp
          have mem: "fst (p' z) \<in> - K" using hit(3) fz by simp
          have "?A \<le> z"
            unfolding pexit_def
            by (rule etime_le_of_mem[OF r hit(1) zle]) (use mem in simp)
          then have "z = r" using zle Aeq by simp
          then show False using hit(3) fz inK by simp
        qed
        have fz: "?f z = fst (p' r) + fst (w z)"
          unfolding ev[OF zm] using stop[OF zm] zr by simp
        have "r + c \<le> pexit T K (\<lambda>s. fst (p' r) + fst (w s))"
          by (rule cont[OF Aeq inK])
        also have "\<dots> \<le> z"
          unfolding pexit_def
          by (rule etime_le_of_mem[OF T0 hit(1) hit(2)])
             (use hit(3) fz in simp)
        finally have "r + c \<le> z" .
        then show ?thesis using e1 Aeq by simp
      qed
    qed
  qed
  have "pexit T K ?f = Inf ({t. 0 \<le> t \<and> t \<le> T \<and> ?f t \<in> - K} \<union> {T})"
    unfolding pexit_def etime_def ..
  moreover have "?b \<le> Inf ({t. 0 \<le> t \<and> t \<le> T \<and> ?f t \<in> - K} \<union> {T})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show ?thesis by simp
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
  fixes \<omega> :: "(real \<Rightarrow> 'a::{polish_space,real_normed_vector} \<times> 'b::{polish_space,real_normed_vector})"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ((real \<Rightarrow> 'a \<times> 'b)) metric)"
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
  fixes K :: "(real^'n::finite) set"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and Kc: "closed K"
  shows "(\<lambda>p. pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))
      \<in> borel_measurable
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))"
proof -
  have T0: "0 \<le> T" using r rT by simp
  show ?thesis
    by (rule measurable_compose[OF pglue_measurable[OF r rT refl refl]
        pexit_path_measurable[OF T0 Kc refl]])
qed


(*<*)
end
(*>*)
