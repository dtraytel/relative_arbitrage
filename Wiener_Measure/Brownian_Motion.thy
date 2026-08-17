section \<open>Brownian motion as the projective limit\<close>

(*<*)
theory Brownian_Motion
  imports Brownian_Finite_Dimensional_Distributions
begin

(*>*)

subsection \<open>The projective limit\<close>

interpretation BM: polish_projective "{0..} :: real set" bm_fdd
proof (intro polish_projective.intro projective_family.intro)
  show "\<And>J H. J \<subseteq> H \<Longrightarrow> finite H \<Longrightarrow> H \<subseteq> {0..} \<Longrightarrow>
      bm_fdd J = distr (bm_fdd H) (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J)"
    by (rule bm_fdd_projective)
  show "\<And>J. finite J \<Longrightarrow> J \<subseteq> {0..} \<Longrightarrow> prob_space (bm_fdd J)"
    by (rule prob_space_bm_fdd)
qed

definition wiener_pre :: "(real \<Rightarrow> real) measure" where
  "wiener_pre = BM.lim"

lemma prob_space_wiener_pre: "prob_space wiener_pre"
  unfolding wiener_pre_def
  by (rule prob_spaceI) (rule BM.P.emeasure_space_1)

interpretation W: prob_space wiener_pre
  by (rule prob_space_wiener_pre)

lemma sets_wiener_pre [simp, measurable_cong]:
  "sets wiener_pre = sets (Pi\<^sub>M {0..} (\<lambda>_. (borel :: real measure)))"
  by (simp add: wiener_pre_def)

lemma measurable_coord:
  assumes "t \<in> {0..}"
  shows "(\<lambda>\<omega>. \<omega> t) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
  by (subst measurable_cong_sets[OF sets_wiener_pre refl])
    (rule measurable_component_singleton[OF assms])

lemma measurable_restrict_wiener_pre:
  assumes "J \<subseteq> {0..}"
  shows "(\<lambda>f. restrict f J) \<in> wiener_pre \<rightarrow>\<^sub>M Pi\<^sub>M J (\<lambda>_. (borel :: real measure))"
  by (subst measurable_cong_sets[OF sets_wiener_pre refl])
    (rule measurable_restrict_subset[OF assms])

subsection \<open>Marginals of the projective limit\<close>

lemma wiener_pre_marginal:
  assumes fin: "finite J" and J: "J \<subseteq> {0..}"
  shows "distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J) = bm_fdd J"
proof (rule measure_eqI)
  show "sets (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel)) (\<lambda>f. restrict f J))
      = sets (bm_fdd J)" by simp
next
  fix X assume "X \<in> sets (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
      (\<lambda>f. restrict f J))"
  then have X: "X \<in> sets (Pi\<^sub>M J (\<lambda>_. (borel :: real measure)))" by simp
  have sp: "space wiener_pre = (\<Pi>\<^sub>E i\<in>{0..}. space (borel :: real measure))"
    by (simp add: wiener_pre_def space_PiM)
  have "emeasure (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
        (\<lambda>f. restrict f J)) X
      = emeasure wiener_pre ((\<lambda>f. restrict f J) -` X \<inter> space wiener_pre)"
    by (rule emeasure_distr[OF measurable_restrict_wiener_pre[OF J] X])
  also have "\<dots> = emeasure BM.lim (prod_emb {0..} (\<lambda>_. borel) J X)"
    by (simp add: wiener_pre_def prod_emb_def sp space_PiM)
  also have "\<dots> = emeasure (bm_fdd J) X"
    using BM.emeasure_lim_emb[OF J fin X] by simp
  finally show "emeasure (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
      (\<lambda>f. restrict f J)) X = emeasure (bm_fdd J) X" .
qed

subsection \<open>Increment distribution and starting point\<close>

lemma wiener_pre_increment:
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s) = gauss_measure (t - s)"
proof (cases "s = t")
  case True
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)
      = distr wiener_pre borel (\<lambda>\<omega>. 0 :: real)"
    by (simp add: True)
  also have "\<dots> = return borel 0"
    by (rule W.distr_const) simp
  also have "\<dots> = gauss_measure (t - s)"
    by (simp add: True gauss_measure_zero)
  finally show ?thesis .
next
  case False
  with st have st': "s < t" by simp
  have stJ: "{s, t} \<subseteq> {0..}" using s st by auto
  have Dmeas: "(\<lambda>g. g t - g s)
      \<in> Pi\<^sub>M {s, t} (\<lambda>_. borel) \<rightarrow>\<^sub>M (borel :: real measure)"
    by measurable
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)
      = distr wiener_pre borel ((\<lambda>g. g t - g s) \<circ> (\<lambda>f. restrict f {s, t}))"
    by (intro distr_cong refl) (simp add: comp_def)
  also have "\<dots> = distr (distr wiener_pre (Pi\<^sub>M {s, t} (\<lambda>_. borel))
      (\<lambda>f. restrict f {s, t})) borel (\<lambda>g. g t - g s)"
    by (rule distr_distr[symmetric, OF Dmeas
        measurable_restrict_wiener_pre[OF stJ]])
  also have "\<dots> = distr (bm_fdd {s, t}) borel (\<lambda>g. g t - g s)"
    by (simp add: wiener_pre_marginal[OF _ stJ])
  also have "\<dots> = distr (inc_prod 0 {s, t}) borel
      ((\<lambda>g. g t - g s) \<circ> csum {s, t})"
    unfolding bm_fdd_def
    by (rule distr_distr[OF Dmeas measurable_csum_inc_prod])
  also have "\<dots> = distr (inc_prod 0 {s, t}) borel (\<lambda>w. w t)"
  proof (intro distr_cong refl)
    fix w :: "real \<Rightarrow> real"
    have "csum {s, t} w t = (\<Sum>u\<in>{u \<in> {s, t}. u \<le> t}. w u)"
      by (simp add: csum_def)
    moreover have "{u \<in> {s, t}. u \<le> t} = {s, t}" using st by auto
    moreover have "(\<Sum>u\<in>{s, t}. w u) = w s + w t"
      using False by simp
    ultimately have 1: "csum {s, t} w t = w s + w t" by simp
    have "csum {s, t} w s = (\<Sum>u\<in>{u \<in> {s, t}. u \<le> s}. w u)"
      by (simp add: csum_def)
    moreover have "{u \<in> {s, t}. u \<le> s} = {s}" using st' by auto
    ultimately have 2: "csum {s, t} w s = w s" by simp
    show "((\<lambda>g. g t - g s) \<circ> csum {s, t}) w = w t"
      by (simp add: comp_def 1 2)
  qed
  also have "\<dots> = gauss_measure (t - s)"
  proof -
    interpret PPS: product_prob_space
      "\<lambda>u. gauss_measure (u - prevt 0 {s, t} u)" "{s, t}"
      by (intro product_prob_space.intro product_sigma_finite.intro
          product_prob_space_axioms.intro sigma_finite_gauss_measure
          prob_space_gauss_measure)
    have lt: "{u \<in> {s, t}. u < t} = {s}" using st' by auto
    have pt: "prevt 0 {s, t} t = s"
      unfolding prevt_def lt using s by (simp add: max_absorb2)
    have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)
        = distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s)" by simp
    have "distr (inc_prod 0 {s, t}) borel (\<lambda>w. w t)
        = distr (Pi\<^sub>M {s, t} (\<lambda>u. gauss_measure (u - prevt 0 {s, t} u)))
          (gauss_measure (t - prevt 0 {s, t} t)) (\<lambda>w. w t)"
      by (intro distr_cong refl) (simp_all add: inc_prod_def)
    also have "\<dots> = gauss_measure (t - prevt 0 {s, t} t)"
      by (rule PPS.PiM_component) simp
    finally show ?thesis by (simp add: pt)
  qed
  finally show ?thesis .
qed

lemma wiener_pre_coord_zero:
  "distr wiener_pre borel (\<lambda>\<omega>. \<omega> 0) = gauss_measure 0"
proof -
  have zJ: "{0 :: real} \<subseteq> {0..}" by auto
  have Dmeas: "(\<lambda>g. g 0) \<in> Pi\<^sub>M {0 :: real} (\<lambda>_. borel)
      \<rightarrow>\<^sub>M (borel :: real measure)"
    by measurable
  have "distr wiener_pre borel (\<lambda>\<omega>. \<omega> 0)
      = distr wiener_pre borel ((\<lambda>g. g 0) \<circ> (\<lambda>f. restrict f {0}))"
    by (intro distr_cong refl) (simp add: comp_def)
  also have "\<dots> = distr (distr wiener_pre (Pi\<^sub>M {0} (\<lambda>_. borel))
      (\<lambda>f. restrict f {0})) borel (\<lambda>g. g 0)"
    by (rule distr_distr[symmetric, OF Dmeas
        measurable_restrict_wiener_pre[OF zJ]])
  also have "\<dots> = distr (bm_fdd {0}) borel (\<lambda>g. g 0)"
    by (simp add: wiener_pre_marginal[OF _ zJ])
  also have "\<dots> = distr (inc_prod 0 {0}) borel ((\<lambda>g. g 0) \<circ> csum {0})"
    unfolding bm_fdd_def
    by (rule distr_distr[OF Dmeas measurable_csum_inc_prod])
  also have "\<dots> = distr (inc_prod 0 {0}) borel (\<lambda>w. w 0)"
  proof (intro distr_cong refl)
    fix w :: "real \<Rightarrow> real"
    have "{u \<in> {0 :: real}. u \<le> 0} = {0}" by auto
    then show "((\<lambda>g. g 0) \<circ> csum {0}) w = w 0"
      by (simp add: csum_def comp_def)
  qed
  also have "\<dots> = gauss_measure 0"
  proof -
    interpret PPS: product_prob_space
      "\<lambda>u. gauss_measure (u - prevt 0 {0 :: real} u)" "{0 :: real}"
      by (intro product_prob_space.intro product_sigma_finite.intro
          product_prob_space_axioms.intro sigma_finite_gauss_measure
          prob_space_gauss_measure)
    have p0: "prevt 0 {0 :: real} 0 = 0"
    proof -
      have e: "{u \<in> {0 :: real}. u < 0} = {}" by auto
      show ?thesis unfolding prevt_def e by simp
    qed
    have "distr (inc_prod 0 {0}) borel (\<lambda>w. w 0)
        = distr (Pi\<^sub>M {0 :: real} (\<lambda>u. gauss_measure (u - prevt 0 {0} u)))
          (gauss_measure (0 - prevt 0 {0} 0)) (\<lambda>w. w 0)"
      by (intro distr_cong refl) (simp_all add: inc_prod_def)
    also have "\<dots> = gauss_measure (0 - prevt 0 {0 :: real} 0)"
      by (rule PPS.PiM_component) simp
    finally show ?thesis by (simp add: p0)
  qed
  finally show ?thesis .
qed

lemma wiener_pre_start: "AE \<omega> in wiener_pre. \<omega> 0 = 0"
proof -
  have cm: "(\<lambda>\<omega>. \<omega> (0::real)) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    by (rule measurable_coord) simp
  have "emeasure wiener_pre {\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0}
      = emeasure wiener_pre ((\<lambda>\<omega>. \<omega> 0) -` (UNIV - {0})
        \<inter> space wiener_pre)"
    by (intro arg_cong2[where f = emeasure] refl) auto
  also have "\<dots> = emeasure (distr wiener_pre borel (\<lambda>\<omega>. \<omega> 0)) (UNIV - {0})"
    by (rule emeasure_distr[symmetric, OF cm]) auto
  also have "\<dots> = emeasure (return borel (0::real)) (UNIV - {0})"
    by (simp add: wiener_pre_coord_zero gauss_measure_zero)
  also have "\<dots> = 0"
    by simp
  finally have null: "emeasure wiener_pre
      {\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0} = 0" .
  have msets: "{\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0} \<in> sets wiener_pre"
    using cm by measurable
  have "{\<omega> \<in> space wiener_pre. \<not> \<omega> 0 = 0} \<in> null_sets wiener_pre"
    using null msets by (auto simp: null_sets_def)
  then show ?thesis
    by (rule AE_I') auto
qed

subsection \<open>The fourth-moment bound\<close>

lemma wiener_pre_moment4:
  assumes s: "0 \<le> s" and st: "s \<le> t"
  shows "(\<integral>\<^sup>+\<omega>. ennreal (\<bar>\<omega> t - \<omega> s\<bar> powr 4) \<partial>wiener_pre)
       = ennreal (3 * (t - s)\<^sup>2)"
proof -
  have t0: "0 \<le> t" using s st by simp
  have inc_meas: "(\<lambda>\<omega>. \<omega> t - \<omega> s) \<in> wiener_pre \<rightarrow>\<^sub>M (borel :: real measure)"
    by (intro borel_measurable_diff measurable_coord) (use s t0 in auto)
  have "(\<integral>\<^sup>+\<omega>. ennreal (\<bar>\<omega> t - \<omega> s\<bar> powr 4) \<partial>wiener_pre)
      = (\<integral>\<^sup>+y. ennreal (\<bar>y\<bar> powr 4)
        \<partial>distr wiener_pre borel (\<lambda>\<omega>. \<omega> t - \<omega> s))"
    by (rule nn_integral_distr[symmetric, OF inc_meas]) simp
  also have "\<dots> = (\<integral>\<^sup>+y. ennreal (\<bar>y\<bar> powr 4) \<partial>gauss_measure (t - s))"
    by (simp add: wiener_pre_increment[OF s st])
  also have "\<dots> = (\<integral>\<^sup>+y. ennreal (y ^ 4) \<partial>gauss_measure (t - s))"
    by (intro nn_integral_cong)
      (simp add: power_abs zero_le_even_power)
  also have "\<dots> = ennreal (3 * (t - s)\<^sup>2)"
    using st by (intro gauss_measure_fourth_moment_nn) simp
  finally show ?thesis .
qed

section \<open>Independent increments\<close>

text \<open>Over a strictly increasing list of times, the increment vector of the
  coordinate process is --- modulo the cumulative-sum isomorphism --- a
  coordinate selection from the independent increment product, hence its
  components are independent.\<close>

text \<open>\<open>sorted_wrt_less_nth_iff\<close> lives in @{theory Wiener_Measure.Sorted_Lists}.\<close>

text \<open>\<open>sorted_wrt_less_set_take\<close> lives in @{theory Wiener_Measure.Sorted_Lists}.\<close>

text \<open>\<open>sorted_wrt_less_Max_last\<close> lives in @{theory Wiener_Measure.Sorted_Lists}.\<close>

theorem bm_increments_indep:
  assumes l: "sorted_wrt (<) l" and l0: "set l \<subseteq> {0..}"
    and len: "2 \<le> length l"
  shows "prob_space.indep_vars wiener_pre (\<lambda>_. borel)
    (\<lambda>k \<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))) {1..<length l}"
proof -
  define n where "n = length l"
  define J where "J = set l"
  define K where "K = {1..<n}"
  have finJ: "finite J" by (simp add: J_def)
  have J0: "J \<subseteq> {0..}" using l0 by (simp add: J_def)
  have n2: "2 \<le> n" using len by (simp add: n_def)
  have Kne: "K \<noteq> {}" using n2 by (auto simp: K_def)
  have distinct_l: "distinct l"
    using l by (simp add: strict_sorted_iff)
  have kn: "\<And>k. k \<in> K \<Longrightarrow> k < length l" and
    k0: "\<And>k. k \<in> K \<Longrightarrow> 0 < k"
    by (auto simp: K_def n_def)
  have lkJ: "\<And>k. k \<in> K \<Longrightarrow> l ! k \<in> J"
    unfolding J_def by (intro nth_mem kn)
  have lk1J: "l ! (k - 1) \<in> J" if k: "k \<in> K" for k
    unfolding J_def using kn[OF k] by (intro nth_mem) simp
  have gap: "l ! (k - 1) < l ! k" if k: "k \<in> K" for k
    using k0[OF k] kn[OF k] by (intro sorted_wrt_nth_less[OF l]) auto
  have lk0: "\<And>k. k \<in> K \<Longrightarrow> 0 \<le> l ! (k - 1)"
    using lk1J J0 by auto
  have below: "\<And>k. k \<in> K \<Longrightarrow> {v \<in> J. v < l ! k} = set (take k l)"
    unfolding J_def by (intro sorted_wrt_less_set_take[OF l] kn)
  have take_ne: "take k l \<noteq> []" if k: "k \<in> K" for k
    using k0[OF k] kn[OF k] by fastforce
  have Max_take: "\<And>k. k \<in> K \<Longrightarrow> Max (set (take k l)) = l ! (k - 1)"
  proof -
    fix k assume k: "k \<in> K"
    have "Max (set (take k l)) = last (take k l)"
      using l by (intro sorted_wrt_less_Max_last sorted_wrt_take take_ne k)
    also have "\<dots> = l ! (k - 1)"
      using kn[OF k] k0[OF k] take_ne[OF k]
      by (simp add: last_conv_nth min_def)
    finally show "Max (set (take k l)) = l ! (k - 1)" .
  qed
  have bound_take: "\<And>k v. k \<in> K \<Longrightarrow> v \<in> set (take k l) \<Longrightarrow> v \<le> l ! (k - 1)"
    using Max_take by (metis List.finite_set Max_ge)
  have prevt_lk: "\<And>k. k \<in> K \<Longrightarrow> prevt 0 J (l ! k) = l ! (k - 1)"
  proof -
    fix k assume k: "k \<in> K"
    have "prevt 0 J (l ! k) = Max (insert 0 (set (take k l)))"
      by (simp add: prevt_def below[OF k])
    also have "\<dots> = max 0 (Max (set (take k l)))"
      using take_ne[OF k] by simp
    also have "\<dots> = l ! (k - 1)"
      using lk0[OF k] by (simp add: Max_take[OF k] max_absorb2)
    finally show "prevt 0 J (l ! k) = l ! (k - 1)" .
  qed
  let ?V = "\<lambda>g. \<lambda>k\<in>K. g (l ! k) - g (l ! (k - 1))"
  let ?U = "\<lambda>\<omega>. \<lambda>k\<in>K. \<omega> (l ! k) - \<omega> (l ! (k - 1))"
  have Vmeas: "?V \<in> Pi\<^sub>M J (\<lambda>_. borel) \<rightarrow>\<^sub>M Pi\<^sub>M K (\<lambda>_. (borel :: real measure))"
    by (intro measurable_restrict borel_measurable_diff
        measurable_component_singleton lkJ lk1J)
  have step1: "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
      = distr (bm_fdd J) (Pi\<^sub>M K (\<lambda>_. borel)) ?V"
  proof -
    have restr_comp: "(\<lambda>k\<in>K. x (l ! k) - x (l ! (k - 1)))
        = (\<lambda>k\<in>K. restrict x J (l ! k) - restrict x J (l ! (k - 1)))"
      for x :: "real \<Rightarrow> real"
    proof (rule restrict_ext)
      fix k assume k: "k \<in> K"
      show "x (l ! k) - x (l ! (k - 1))
          = restrict x J (l ! k) - restrict x J (l ! (k - 1))"
        using lkJ[OF k] lk1J[OF k] by simp
    qed
    have "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
        = distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) (?V \<circ> (\<lambda>f. restrict f J))"
    proof (intro distr_cong refl)
      fix x assume "x \<in> space wiener_pre"
      show "?U x = (?V \<circ> (\<lambda>f. restrict f J)) x"
        unfolding comp_def by (rule restr_comp)
    qed
    also have "\<dots> = distr (distr wiener_pre (Pi\<^sub>M J (\<lambda>_. borel))
        (\<lambda>f. restrict f J)) (Pi\<^sub>M K (\<lambda>_. borel)) ?V"
      by (rule distr_distr[symmetric, OF Vmeas
          measurable_restrict_wiener_pre[OF J0]])
    also have "\<dots> = distr (bm_fdd J) (Pi\<^sub>M K (\<lambda>_. borel)) ?V"
      by (simp add: wiener_pre_marginal[OF finJ J0])
    finally show ?thesis .
  qed
  have step2: "distr (bm_fdd J) (Pi\<^sub>M K (\<lambda>_. borel)) ?V
      = distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (?V \<circ> csum J)"
    unfolding bm_fdd_def
    by (rule distr_distr[OF Vmeas measurable_csum_inc_prod])
  have tele: "csum J w (l ! k) - csum J w (l ! (k - 1)) = w (l ! k)"
    if k: "k \<in> K" for k and w :: "real \<Rightarrow> real"
  proof -
    have subs: "{u \<in> J. u \<le> l ! (k - 1)} \<subseteq> {u \<in> J. u \<le> l ! k}"
      using gap[OF k] by auto
    have ddiff: "{u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)} = {l ! k}"
    proof (intro equalityI subsetI)
      fix u assume "u \<in> {u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)}"
      then have u: "u \<in> J" "u \<le> l ! k" "\<not> u \<le> l ! (k - 1)" by auto
      have "u = l ! k"
      proof (rule ccontr)
        assume "u \<noteq> l ! k"
        with u have "u < l ! k" by simp
        with u below[OF k] have "u \<in> set (take k l)" by blast
        with bound_take[OF k] u show False by auto
      qed
      then show "u \<in> {l ! k}" by simp
    next
      fix u assume "u \<in> {l ! k}"
      then show "u \<in> {u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)}"
        using lkJ[OF k] gap[OF k] by auto
    qed
    have "csum J w (l ! k) - csum J w (l ! (k - 1))
        = (\<Sum>u\<in>{u \<in> J. u \<le> l ! k}. w u)
          - (\<Sum>u\<in>{u \<in> J. u \<le> l ! (k - 1)}. w u)"
      using lkJ[OF k] lk1J[OF k] by (simp add: csum_def)
    also have "\<dots>
        = (\<Sum>u\<in>{u \<in> J. u \<le> l ! k} - {u \<in> J. u \<le> l ! (k - 1)}. w u)"
      using finJ subs by (subst sum_diff) auto
    also have "\<dots> = w (l ! k)"
      unfolding ddiff by simp
    finally show ?thesis .
  qed
  have tele_vec: "(\<lambda>k\<in>K. csum J w (l ! k) - csum J w (l ! (k - 1)))
      = (\<lambda>k\<in>K. w (l ! k))" for w :: "real \<Rightarrow> real"
  proof (rule restrict_ext)
    fix k assume k: "k \<in> K"
    show "csum J w (l ! k) - csum J w (l ! (k - 1)) = w (l ! k)"
      by (rule tele[OF k])
  qed
  have step3: "distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (?V \<circ> csum J)
      = distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (\<lambda>w. \<lambda>k\<in>K. w (l ! k))"
  proof (intro distr_cong refl)
    fix w assume "w \<in> space (inc_prod 0 J)"
    show "(?V \<circ> csum J) w = (\<lambda>w. \<lambda>k\<in>K. w (l ! k)) w"
      unfolding comp_def by (rule tele_vec)
  qed
  have inj: "inj_on (\<lambda>k. l ! k) K"
    using distinct_l kn by (intro inj_on_nth) auto
  have step4: "distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (\<lambda>w. \<lambda>k\<in>K. w (l ! k))
      = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - l ! (k - 1)))"
  proof -
    have "distr (inc_prod 0 J) (Pi\<^sub>M K (\<lambda>_. borel)) (\<lambda>w. \<lambda>k\<in>K. w (l ! k))
        = distr (Pi\<^sub>M J (\<lambda>u. gauss_measure (u - prevt 0 J u)))
          (Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - prevt 0 J (l ! k))))
          (\<lambda>w. \<lambda>k\<in>K. w (l ! k))"
      by (intro distr_cong refl)
        (simp_all add: inc_prod_def cong: sets_PiM_cong)
    also have "\<dots> = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - prevt 0 J (l ! k)))"
      by (intro distr_PiM_reindex prob_space_gauss_measure inj)
        (auto simp: lkJ)
    also have "\<dots> = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - l ! (k - 1)))"
      by (intro PiM_cong refl) (simp add: prevt_lk)
    finally show ?thesis .
  qed
  have comp_distr: "distr wiener_pre borel
      (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1)))
      = gauss_measure (l ! k - l ! (k - 1))" if k: "k \<in> K" for k
    using lk0[OF k] gap[OF k]
    by (intro wiener_pre_increment) (auto intro: less_imp_le)
  have rv: "\<And>k. k \<in> K \<Longrightarrow>
      (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))) \<in> wiener_pre \<rightarrow>\<^sub>M borel"
    using lkJ lk1J J0
    by (intro borel_measurable_diff measurable_coord) auto
  have "W.indep_vars (\<lambda>_. borel)
      (\<lambda>k \<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))) K"
  proof (subst W.indep_vars_iff_distr_eq_PiM'[OF Kne rv])
    have "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
        = Pi\<^sub>M K (\<lambda>k. gauss_measure (l ! k - l ! (k - 1)))"
      unfolding step1 step2 step3 step4 by (rule refl)
    also have "\<dots> = Pi\<^sub>M K (\<lambda>k. distr wiener_pre borel
        (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))))"
    proof (rule PiM_cong[OF refl])
      fix k assume k: "k \<in> K"
      show "gauss_measure (l ! k - l ! (k - 1))
          = distr wiener_pre borel (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1)))"
        by (rule comp_distr[OF k, symmetric])
    qed
    finally show "distr wiener_pre (Pi\<^sub>M K (\<lambda>_. borel)) ?U
        = Pi\<^sub>M K (\<lambda>k. distr wiener_pre borel
          (\<lambda>\<omega>. \<omega> (l ! k) - \<omega> (l ! (k - 1))))" .
  qed
  then show ?thesis by (simp add: K_def n_def)
qed


(*<*)
end
(*>*)
