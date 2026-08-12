(*
  Title:   Brownian_Motion_Continuity.thy
  Content: The Kolmogorov-Chentsov continuous modification of the
           coordinate process on the Wiener measure: existence of
           Brownian motion with continuous paths.
*)

theory Brownian_Motion_Continuity
  imports
    Brownian_Motion
    "Kolmogorov_Chentsov.Kolmogorov_Chentsov"
begin

section \<open>Brownian motion\<close>

definition bm_coord :: "(real, real \<Rightarrow> real, real) stochastic_process" where
  "bm_coord = prob_space.process_of wiener_pre borel {0..} (\<lambda>t \<omega>. \<omega> t) 0"

lemma bm_coord_measurable:
  "\<forall>t\<in>{0..}. (\<lambda>\<omega>. \<omega> t) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
  by (intro ballI measurable_coord)

lemma index_bm_coord [simp]: "proc_index bm_coord = {0..}"
  unfolding bm_coord_def by (rule prob_space.index_process_of[OF prob_space_wiener_pre])

lemma source_bm_coord [simp]: "proc_source bm_coord = wiener_pre"
  unfolding bm_coord_def
  by (intro prob_space.source_process_of[OF prob_space_wiener_pre] bm_coord_measurable) simp

lemma target_bm_coord [simp]: "proc_target bm_coord = borel"
  unfolding bm_coord_def
  by (intro prob_space.target_process_of[OF prob_space_wiener_pre] bm_coord_measurable) simp

lemma process_bm_coord:
  "t \<in> {0..} \<Longrightarrow> process bm_coord t = (\<lambda>\<omega>. \<omega> t)"
  unfolding bm_coord_def
  by (intro prob_space.process_of_apply[OF prob_space_wiener_pre] bm_coord_measurable) simp_all

lemma bm_coord_moment_bound:
  assumes s: "0 \<le> s" and t: "0 \<le> t"
  shows "(\<integral>\<^sup>+x. ennreal (dist (process bm_coord t x)
      (process bm_coord s x) powr 4) \<partial>proc_source bm_coord)
    \<le> ennreal (3 * dist t s powr (1 + 1))"
proof -
  have key: "(\<integral>\<^sup>+x. ennreal (dist (x t') (x s') powr 4) \<partial>wiener_pre)
      = ennreal (3 * dist t' s' powr 2)"
    if s': "0 \<le> s'" and st': "s' \<le> t'" for s' t'
  proof -
    have "(\<integral>\<^sup>+x. ennreal (dist (x t') (x s') powr 4) \<partial>wiener_pre)
        = (\<integral>\<^sup>+x. ennreal (\<bar>x t' - x s'\<bar> powr 4) \<partial>wiener_pre)"
      by (simp add: dist_real_def)
    also have "\<dots> = ennreal (3 * (t' - s')\<^sup>2)"
      by (rule wiener_pre_moment4[OF s' st'])
    also have "\<dots> = ennreal (3 * dist t' s' powr 2)"
    proof (cases "s' = t'")
      case True then show ?thesis by simp
    next
      case False
      then have "0 < dist t' s'" by simp
      then have "dist t' s' powr 2 = dist t' s' ^ 2"
        by simp
      then show ?thesis
        using st' by (simp add: dist_real_def power2_eq_square abs_real_def)
    qed
    finally show ?thesis .
  qed
  have dist44: "dist (process bm_coord u x) (process bm_coord v x)
      = dist (x u) (x v)" if "0 \<le> u" "0 \<le> v" for u v x
    using that by (simp add: process_bm_coord)
  have two: "(1 :: real) + 1 = 2" by simp
  show ?thesis
  proof (cases "s \<le> t")
    case True
    have "(\<integral>\<^sup>+x. ennreal (dist (process bm_coord t x)
        (process bm_coord s x) powr 4) \<partial>proc_source bm_coord)
        = (\<integral>\<^sup>+x. ennreal (dist (x t) (x s) powr 4) \<partial>wiener_pre)"
      unfolding source_bm_coord
      by (intro nn_integral_cong) (simp add: dist44 s t)
    also have "\<dots> = ennreal (3 * dist t s powr 2)"
      by (rule key[OF s True])
    finally show ?thesis by (simp add: two)
  next
    case False
    then have ts: "t \<le> s" by simp
    have "(\<integral>\<^sup>+x. ennreal (dist (process bm_coord t x)
        (process bm_coord s x) powr 4) \<partial>proc_source bm_coord)
        = (\<integral>\<^sup>+x. ennreal (dist (x s) (x t) powr 4) \<partial>wiener_pre)"
      unfolding source_bm_coord
      by (intro nn_integral_cong) (simp add: dist44 s t dist_commute)
    also have "\<dots> = ennreal (3 * dist s t powr 2)"
      by (rule key[OF t ts])
    finally show ?thesis by (simp add: two dist_commute)
  qed
qed

lemma bm_coord_moment_bound':
  assumes s: "0 \<le> s" and t: "0 \<le> t"
  shows "(\<integral>\<^sup>+x. ennreal (dist (process bm_coord t x)
      (process bm_coord s x) powr 4) \<partial>proc_source bm_coord)
    \<le> (3 :: ennreal) * ennreal (dist t s powr (1 + 1))"
proof -
  have e: "(3 :: ennreal) * ennreal (dist t s powr (1 + 1))
      = ennreal (3 * dist t s powr (1 + 1))"
  proof -
    have "(3 :: ennreal) * ennreal (dist t s powr (1 + 1))
        = ennreal 3 * ennreal (dist t s powr (1 + 1))"
      by simp
    also have "\<dots> = ennreal (3 * dist t s powr (1 + 1))"
      by (rule ennreal_mult'[symmetric]) simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding e by (rule bm_coord_moment_bound[OF s t])
qed

theorem bm_coord_modification:
  fixes \<gamma> :: real
  assumes \<gamma>: "\<gamma> \<in> {0<..<1/4}"
  shows "\<exists>B. modification bm_coord B \<and>
    (\<forall>\<omega>. local_holder_on \<gamma> {0..} (\<lambda>t. B t \<omega>))"
  by (rule Kolmogorov_Chentsov[of bm_coord 4 1 3 \<gamma>])
    (use \<gamma> bm_coord_moment_bound bm_coord_moment_bound' in
      \<open>simp_all add: ennreal_mult''\<close>)

text \<open>The main existence theorem: a continuous process starting at 0
  whose increments are centered Gaussians with variance the time gap.\<close>

theorem Brownian_motion_exists:
  fixes \<gamma> :: real
  assumes \<gamma>: "\<gamma> \<in> {0<..<1/4}"
  obtains B :: "(real, real \<Rightarrow> real, real) stochastic_process"
  where "modification bm_coord B"
    and "\<And>\<omega>. local_holder_on \<gamma> {0..} (\<lambda>t. B t \<omega>)"
    and "\<And>\<omega>. continuous_on {0..} (\<lambda>t. B t \<omega>)"
    and "proc_source B = wiener_pre"
    and "AE \<omega> in wiener_pre. B 0 \<omega> = 0"
    and "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow>
      distr wiener_pre borel (\<lambda>\<omega>. B t \<omega> - B s \<omega>) = gauss_measure (t - s)"
proof -
  from bm_coord_modification[OF \<gamma>] obtain B where
    mod: "modification bm_coord B" and
    holder: "\<forall>\<omega>. local_holder_on \<gamma> {0..} (\<lambda>t. B t \<omega>)"
    by blast
  have cont: "\<And>\<omega>. continuous_on {0..} (\<lambda>t. B t \<omega>)"
    using holder local_holder_imp_continuous by blast
  have source_B: "proc_source B = wiener_pre"
    using modificationD(1)[OF mod] by (auto simp: compatible_source)
  have target_B: "sets (proc_target B) = sets (borel :: real measure)"
    using modificationD(1)[OF mod] compatible_target by fastforce
  have B_meas: "\<And>u. process B u \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
  proof -
    fix u
    have "process B u \<in> proc_source B \<rightarrow>\<^sub>M proc_target B"
      by (rule stochastic_process_measurable)
    then show "process B u \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
      using source_B target_B
      by (simp add: measurable_cong_sets[OF refl target_B])
  qed
  have ae_eq: "AE \<omega> in wiener_pre. process bm_coord u \<omega> = process B u \<omega>"
    if u: "u \<in> {0..}" for u
  proof -
    have "AE \<omega> in proc_source bm_coord.
        process bm_coord u \<omega> = process B u \<omega>"
      using u by (intro modificationD(2)[OF mod]) simp
    then show ?thesis
      unfolding source_bm_coord .
  qed
  have ae_coord: "AE \<omega> in wiener_pre. process B u \<omega> = \<omega> u"
    if u: "u \<in> {0..}" for u
    using ae_eq[OF u] by (simp add: process_bm_coord[OF u] eq_commute)
  have start: "AE \<omega> in wiener_pre. B 0 \<omega> = 0"
    using ae_coord[of 0] wiener_pre_start by fastforce
  have incr: "distr wiener_pre borel (\<lambda>\<omega>. B t \<omega> - B s \<omega>)
      = gauss_measure (t - s)" if s: "0 \<le> s" and st: "s \<le> t" for s t
  proof -
    have t0: "0 \<le> t" using s st by simp
    have ae': "AE \<omega> in wiener_pre.
        process B t \<omega> - process B s \<omega> = \<omega> t - \<omega> s"
      using ae_coord[of t] ae_coord[of s] s t0 by fastforce
    have rv_B: "(\<lambda>\<omega>. process B t \<omega> - process B s \<omega>)
        \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
      by (intro borel_measurable_diff B_meas)
    have rv_X: "(\<lambda>\<omega>. \<omega> t - \<omega> s) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
      using s t0 by (intro borel_measurable_diff measurable_coord) auto
    have "distr wiener_pre borel (\<lambda>\<omega>. process B t \<omega> - process B s \<omega>)
        = distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)"
      by (rule distr_cong_AE[OF refl refl ae' rv_B rv_X])
    also have "\<dots> = gauss_measure (t - s)"
      by (rule wiener_pre_increment[OF s st])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule that[OF mod holder[rule_format] cont source_B start incr])
qed


end
