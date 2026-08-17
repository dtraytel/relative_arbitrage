section \<open>The delayed class and the horizon-parametrised selector\<close>

(*<*)
theory Dynamic_Programming_Delayed_Class
  imports Dynamic_Programming_Additive_Glue
begin

(*>*)

section \<open>The delayed class on a fixed space\<close>

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
  and that \<^const>\<open>prebase\<close> inverts it on the left, so nothing is lost by
  working with the delayed law instead of the rebased one.\<close>

lemma pembed_mspace:
  fixes w :: "'n::finite pairpath"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
  shows "pembed s T w \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T - s} w" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. max (t - s) 0)"
    by (intro continuous_intros)
  have im: "(\<lambda>t. max (t - s) 0) ` {0..T} \<subseteq> {0..T - s}" using s0 sT by auto
  have "continuous_on {0..T} (\<lambda>t. w (max (t - s) 0))"
    by (rule continuous_on_compose2[OF c m im])
  then show ?thesis unfolding pembed_def by (rule mspace_path_metricI)
qed

lemma pembed_measurable:
  fixes s T :: real
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "pembed s T \<in> borel_of (mtopology_of
        (path_metric (T - s) :: ('n::finite pairpath) metric))
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using s0 sT by simp
  have into: "pembed s T w \<in> mspace (path_metric T :: ('n pairpath) metric)"
    if "w \<in> space ?Bs" for w
    using that by (auto simp: space_borel_of intro: pembed_mspace[OF s0 sT])
  have ev: "(\<lambda>w :: 'n pairpath. pembed s T w t) \<in> borel_measurable ?Bs" for t
  proof (cases "t \<in> {0..T}")
    case True
    have "(\<lambda>w :: 'n pairpath. w (max (t - s) 0)) \<in> borel_measurable ?Bs"
      by (rule pair_law_eval_measurable[OF refl])
    then show ?thesis by (simp add: pembed_apply[OF True])
  next
    case False
    have "(\<lambda>w :: 'n pairpath. pembed s T w t) = (\<lambda>w. undefined)"
      by (rule ext) (rule pembed_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>w. mdist (path_metric T :: ('n pairpath) metric)
        (pembed s T w) a) \<in> borel_measurable ?Bs"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

text \<open>\<^const>\<open>prebase\<close> inverts \<^const>\<open>pembed\<close>: the delayed law carries exactly
  the same information as the rebased one, so selecting the delayed law is
  no weaker than selecting the rebased one.\<close>

lemma prebase_pembed:
  fixes w :: "'n::finite pairpath"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
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

definition pdelclass :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
    \<Rightarrow> (('n::finite pairpath) measure) set"
  where "pdelclass k L T s =
     (\<lambda>\<nu>. distr \<nu> (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))) (pembed s T))
       ` exit_class k L (T - s) (0::real^'n)"

text \<open>A delayed law is a probability law on the \<open>T\<close>-space, it stands still on
  \<open>[0,s]\<close>, and re-basing recovers the original --- which is what makes
  \<^const>\<open>pdelclass\<close> the right object for the additive glue to consume.\<close>

lemma pdelclass_prob:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "prob_space \<nu>"
    and "sets \<nu> = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
proof -
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))) (pembed s T)"
    unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets (borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  show "prob_space \<nu>"
    unfolding nu
    by (rule prob_space.prob_space_distr[OF exit_class_prob[OF mu] pm])
  show "sets \<nu> = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" unfolding nu by simp
qed

lemma pdelclass_frozen_at:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "u \<in> {0..T}" and us: "u \<le> s"
  shows "AE w in \<nu>. w u = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)"
    unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets (borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have Phi: "{w \<in> space ?B. w u = 0} \<in> sets ?B"
  proof -
    have "{w \<in> space ?B. w u = 0}
        = (\<lambda>w :: 'n pairpath. w u) -` {0} \<inter> space ?B" by auto
    then show ?thesis
      using measurable_sets[OF ev borel_closed[OF closed_singleton]] by simp
  qed
  have start: "AE v in \<mu>. fst (v 0) = 0 \<and> snd (v 0) = 0"
    by (rule exit_class_start[OF mu])
  have "AE v in \<mu>. pembed s T v u = 0"
    using start
  proof eventually_elim
    case (elim v)
    have "max (u - s) 0 = 0" using us by simp
    then have "pembed s T v u = v 0" unfolding pembed_apply[OF u] by simp
    then show ?case using elim by (simp add: prod_eq_iff)
  qed
  then show ?thesis unfolding nu AE_distr_iff[OF pm Phi] .
qed
text \<open>The \<open>\<forall>\<close>-form of the freezing, which the additive glue's \<open>Kfr\<close> hypothesis
  consumes.  The measurability of the frozen set is the only real content:
  a continuous path vanishing at every rational point of \<open>[0,d]\<close> vanishes
  there, so the set is a countable intersection of evaluation conditions.\<close>

lemma vanishes_of_rational:
  fixes w :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes d0: "0 \<le> d" and cont: "continuous_on {0..d} w"
    and rat: "\<And>q. q \<in> (\<rat> :: real set) \<Longrightarrow> q \<in> {0..d} \<Longrightarrow> w q = 0"
    and u: "u \<in> {0..d}"
  shows "w u = 0"
proof (cases "u = 0")
  case True
  show ?thesis unfolding True by (rule rat) (use d0 in auto)
next
  case False
  then have u0: "0 < u" and ud: "u \<le> d" using u by auto
  have "\<exists>q. q \<in> (\<rat> :: real set) \<and> max 0 (u - 1 / real (Suc n)) < q \<and> q < u"
    for n
  proof -
    have "max 0 (u - 1 / real (Suc n)) < u" using u0 by simp
    then show ?thesis using Rats_dense_in_real by blast
  qed
  then obtain q where q: "\<And>n. q n \<in> (\<rat> :: real set)"
    and ql: "\<And>n. max 0 (u - 1 / real (Suc n)) < q n"
    and qu: "\<And>n. q n < u" by metis
  have qin: "q n \<in> {0..d}" for n using ql[of n] qu[of n] ud by auto
  have qlim: "q \<longlonglongrightarrow> u"
  proof (rule tendsto_sandwich[of "\<lambda>n. max 0 (u - 1 / real (Suc n))" q
      sequentially "\<lambda>_. u"])
    show "\<forall>\<^sub>F n in sequentially. max 0 (u - 1 / real (Suc n)) \<le> q n"
    proof (intro always_eventually allI)
      fix n show "max 0 (u - 1 / real (Suc n)) \<le> q n" using ql[of n] by simp
    qed
    show "\<forall>\<^sub>F n in sequentially. q n \<le> u"
    proof (intro always_eventually allI)
      fix n show "q n \<le> u" using qu[of n] by simp
    qed
    show "(\<lambda>n. max 0 (u - 1 / real (Suc n))) \<longlonglongrightarrow> u"
    proof -
      have "(\<lambda>n. u - 1 / real (Suc n)) \<longlonglongrightarrow> u - 0"
        by (intro tendsto_intros LIMSEQ_Suc[OF lim_1_over_n])
      then have "(\<lambda>n. u - 1 / real (Suc n)) \<longlonglongrightarrow> u" by simp
      then have "(\<lambda>n. max 0 (u - 1 / real (Suc n))) \<longlonglongrightarrow> max 0 u"
        by (intro tendsto_intros)
      then show ?thesis using u0 by simp
    qed
    show "(\<lambda>_. u) \<longlonglongrightarrow> u" by simp
  qed
  have "(\<lambda>n. w (q n)) \<longlonglongrightarrow> w u"
    using cont qin qlim u unfolding continuous_on_sequentially
    by (simp add: o_def)
  moreover have "(\<lambda>n. w (q n)) \<longlonglongrightarrow> 0"
    using rat[OF q qin] by simp
  ultimately show ?thesis by (rule LIMSEQ_unique)
qed

lemma frozen_set_measurable:
  fixes c T :: real
  assumes T0: "0 \<le> T"
  shows "{w \<in> space (borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric))).
      \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}
    \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?D = "{0..min c T} \<inter> (\<rat> :: real set)"
  have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have cnt: "countable ?D" by (simp add: countable_rat)
  have ev: "(\<lambda>w :: 'n pairpath. w q) \<in> borel_measurable ?B" for q
    by (rule pair_law_eval_measurable[OF refl])
  have single: "{w \<in> space ?B. w q = 0} \<in> sets ?B" for q
  proof -
    have "{w \<in> space ?B. w q = 0} = (\<lambda>w :: 'n pairpath. w q) -` {0} \<inter> space ?B"
      by auto
    then show ?thesis
      using measurable_sets[OF ev borel_closed[OF closed_singleton]] by simp
  qed
  have eq: "{w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}
      = {w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}"
  proof (rule set_eqI, rule iffI)
    fix w assume "w \<in> {w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}"
    then show "w \<in> {w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}" using T0 by auto
  next
    fix w assume h: "w \<in> {w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}"
    then have wm: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using spB by simp
    have cw: "continuous_on {0..T} w" by (rule mspace_path_metricD[OF wm])
    show "w \<in> {w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> c \<longrightarrow> w u = 0}"
    proof (intro CollectI conjI allI impI)
      show "w \<in> space ?B" using h by blast
      fix u assume uT: "u \<in> {0..T}" and uc: "u \<le> c"
      have d0: "0 \<le> min c T" using uT uc by auto
      have sub: "{0..min c T} \<subseteq> {0..T}" by auto
      show "w u = 0"
      proof (rule vanishes_of_rational[OF d0 continuous_on_subset[OF cw sub]])
        fix q :: real assume "q \<in> \<rat>" and "q \<in> {0..min c T}"
        then show "w q = 0" using h by auto
      next
        show "u \<in> {0..min c T}" using uT uc by auto
      qed
    qed
  qed
  have "{w \<in> space ?B. \<forall>q \<in> ?D. w q = 0} \<in> sets ?B"
  proof (cases "?D = {}")
    case True
    then have "{w \<in> space ?B. \<forall>q \<in> ?D. w q = 0} = space ?B" by simp
    then show ?thesis by simp
  next
    case False
    have sub: "(\<lambda>q. {w \<in> space ?B. w q = 0}) ` ?D \<subseteq> sets ?B"
      using single by blast
    have "(\<Inter>q \<in> ?D. {w \<in> space ?B. w q = 0}) \<in> sets ?B"
      by (rule sets.countable_INT'[OF cnt False sub])
    moreover have "{w \<in> space ?B. \<forall>q \<in> ?D. w q = 0}
        = (\<Inter>q \<in> ?D. {w \<in> space ?B. w q = 0})" using False by auto
    ultimately show ?thesis by simp
  qed
  then show ?thesis unfolding eq .
qed

lemma pdelclass_frozen:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "AE w in \<nu>. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> s \<longrightarrow> w u = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using s0 sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)"
    unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets (borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric)))"
    by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have Phi: "{w \<in> space ?B. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> s \<longrightarrow> w u = 0} \<in> sets ?B"
    by (rule frozen_set_measurable[OF T0])
  have start: "AE v in \<mu>. fst (v 0) = 0 \<and> snd (v 0) = 0"
    by (rule exit_class_start[OF mu])
  have "AE v in \<mu>. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> s \<longrightarrow> pembed s T v u = 0"
    using start
  proof eventually_elim
    case (elim v)
    show ?case
    proof (intro allI impI)
      fix u assume uT: "u \<in> {0..T}" and us: "u \<le> s"
      have "max (u - s) 0 = 0" using us by simp
      then have "pembed s T v u = v 0" unfolding pembed_apply[OF uT] by simp
      then show "pembed s T v u = 0" using elim by (simp add: prod_eq_iff)
    qed
  qed
  then show ?thesis unfolding nu AE_distr_iff[OF pm Phi] .
qed

section \<open>The horizon enters the value only as a cap\<close>

text \<open>A single identity reduces the horizon-parametrised selector to a
  pushforward, not a new selection theorem: the capped exit time at a
  shorter horizon is the capped exit time at the longer one, capped again
  --- \<^term>\<open>pexit S K f = min (pexit T K f) S\<close>.  Capping by a constant
  commutes with the essential infimum and with the supremum over the
  class, so the horizon acts on the value function as an outer \<open>min\<close> and
  not on which law is optimal.  Consequently one selector, built once at
  the full horizon \<open>T\<close>, is optimal at every shorter horizon, and the
  parameter \<open>s\<close> is carried through only by a pushforward.\<close>

lemma pexit_min_horizon:
  fixes K :: "'b::polish_space set"
  assumes S: "0 \<le> S" and ST: "S \<le> T"
  shows "pexit S K f = min (pexit T K f) S"
proof (rule order.antisym)
  have T0: "0 \<le> T" using S ST by simp
  show "pexit S K f \<le> min (pexit T K f) S"
    using pexit_mono_T[OF S ST, of K f] pexit_le_T[OF S, of K f] by simp
  have lb: "min (pexit T K f) S \<le> z"
    if z: "z \<in> {r. 0 \<le> r \<and> r \<le> S \<and> f r \<in> - K} \<union> {S}" for z
  proof -
    consider (hit) "0 \<le> z" "z \<le> S" "f z \<in> - K" | (cap) "z = S" using z by blast
    then show ?thesis
    proof cases
      case hit
      then have zT: "z \<le> T" using ST by simp
      have "pexit T K f \<le> z"
        unfolding pexit_def
        by (rule etime_le_of_mem[OF T0 hit(1) zT]) (use hit(3) in simp)
      then show ?thesis by simp
    next
      case cap
      then show ?thesis by simp
    qed
  qed
  have "pexit S K f = Inf ({r. 0 \<le> r \<and> r \<le> S \<and> f r \<in> - K} \<union> {S})"
    unfolding pexit_def etime_def ..
  moreover have "min (pexit T K f) S
      \<le> Inf ({r. 0 \<le> r \<and> r \<le> S \<and> f r \<in> - K} \<union> {S})"
    by (intro cInf_greatest) (use lb in auto)
  ultimately show "min (pexit T K f) S \<le> pexit S K f" by simp
qed

text \<open>\<open>ess_inf_time_mono\<close> lives in @{theory Relative_Arbitrage.Value_Function_Market},
  with an almost-sure rather than a pointwise hypothesis; this theory had a
  pointwise copy that shadowed it.\<close>

text \<open>Capping the integrand by a constant caps the essential infimum by the
  same constant.  Both halves are elementary, but the \<open>\<ge>\<close> half has to be
  run through @{thm [source] ennreal_strict_between}: the defining
  supremum need not be attained.\<close>

lemma ess_inf_time_min_const:
  fixes c :: real
  assumes M: "prob_space M"
  shows "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) = min (ess_inf_time M g) (ennreal c)"
proof (rule order.antisym)
  show "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) \<le> min (ess_inf_time M g) (ennreal c)"
  proof (intro min.boundedI)
    show "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) \<le> ess_inf_time M g"
      by (rule ess_inf_time_mono) simp
    show "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) \<le> ennreal c"
      by (rule ess_inf_time_le_const[OF M]) simp
  qed
  show "min (ess_inf_time M g) (ennreal c) \<le> ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)"
  proof (rule ccontr)
    assume "\<not> min (ess_inf_time M g) (ennreal c)
        \<le> ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)"
    then have "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)
        < min (ess_inf_time M g) (ennreal c)" by (rule not_le_imp_less)
    then obtain b where b1: "ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c) < b"
      and b2: "b < min (ess_inf_time M g) (ennreal c)"
      using ennreal_strict_between by blast
    from b2 have bg: "b < ess_inf_time M g"
      by (rule order.strict_trans2[OF _ min.cobounded1])
    from b2 have bc: "b < ennreal c"
      by (rule order.strict_trans2[OF _ min.cobounded2])
    from bg have "b < Sup {e. AE \<omega> in M. e \<le> ennreal (g \<omega>)}"
      unfolding ess_inf_time_def .
    then obtain e where eA: "e \<in> {e. AE \<omega> in M. e \<le> ennreal (g \<omega>)}"
      and be: "b < e" by (auto simp: less_Sup_iff)
    from eA have e: "AE \<omega> in M. e \<le> ennreal (g \<omega>)" by simp
    then have "AE \<omega> in M. b \<le> ennreal (min (g \<omega>) c)"
    proof (rule eventually_mono)
      fix \<omega> assume "e \<le> ennreal (g \<omega>)"
      with be have "b \<le> ennreal (g \<omega>)" by simp
      with bc have "b \<le> min (ennreal (g \<omega>)) (ennreal c)" by simp
      then show "b \<le> ennreal (min (g \<omega>) c)" by (simp add: ennreal_min_eq)
    qed
    then have "b \<le> ess_inf_time M (\<lambda>\<omega>. min (g \<omega>) c)"
      unfolding ess_inf_time_def by (intro Sup_upper) simp
    with b1 show False by simp
  qed
qed

text \<open>The value function at a shorter horizon is the value function at the
  longer one, capped.  The \<open>\<le>\<close> half is @{thm [source] exit_val_horizon_mono}
  together with @{thm [source] exit_val_le_T}; the \<open>\<ge>\<close> half cuts a
  competitor at the longer horizon back to the shorter one
  (@{thm [source] exit_class_pcut}), where the two lemmas above turn
  its value into the capped value.  No pasting is needed in either
  direction --- the pasting is already inside
  @{thm [source] exit_val_horizon_mono}.\<close>

theorem exit_val_horizon_cap:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes S0: "0 \<le> S" and ST: "S \<le> T" and L: "1 \<le> L" and K: "closed K"
  shows "exit_val k L S K x = min (exit_val k L T K x) (ennreal S)"
proof (rule order.antisym)
  show "exit_val k L S K x \<le> min (exit_val k L T K x) (ennreal S)"
    by (intro min.boundedI exit_val_horizon_mono[OF S0 ST L K] exit_val_le_T[OF S0])
  show "min (exit_val k L T K x) (ennreal S) \<le> exit_val k L S K x"
  proof (rule ccontr)
    let ?BS = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
    assume "\<not> min (exit_val k L T K x) (ennreal S) \<le> exit_val k L S K x"
    then have "exit_val k L S K x < min (exit_val k L T K x) (ennreal S)"
      by (rule not_le_imp_less)
    then obtain b where b1: "exit_val k L S K x < b"
      and b2: "b < min (exit_val k L T K x) (ennreal S)"
      using ennreal_strict_between by blast
    from b2 have bT: "b < exit_val k L T K x"
      by (rule order.strict_trans2[OF _ min.cobounded1])
    from b2 have bS: "b < ennreal S"
      by (rule order.strict_trans2[OF _ min.cobounded2])
    from bT have "b < Sup ((\<lambda>Q. ess_inf_time Q
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) ` exit_class k L T x)"
      unfolding exit_val_def .
    then obtain Q :: "('n pairpath) measure"
      where Q: "Q \<in> exit_class k L T x"
        and bQ: "b < ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      by (auto simp: less_Sup_iff)
    have setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
      by (rule exit_class_sets[OF Q])
    have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
    have cutm: "pcut S \<in> Q \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST setsQ])
    have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t)))
        \<in> borel_measurable ?BS"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable ?BS"
        by (rule measurable_compose[OF pfst_measurable[OF S0 refl]
              pexit_measurable[OF S0 K]])
      then show ?thesis by (simp add: pexit_pfst)
    qed
    have mset: "{\<omega> \<in> space ?BS. c \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))}
        \<in> sets ?BS" for c :: ennreal using taum by measurable
    have "ess_inf_time (pair_law_of S (pcut S) Q)
          (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
        = ess_inf_time Q (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (pcut S \<omega> t)))"
      unfolding pair_law_of_def by (rule ess_inf_time_distr[OF cutm mset])
    also have "\<dots> = ess_inf_time Q (\<lambda>\<omega>. min (pexit T K (\<lambda>t. fst (\<omega> t))) S)"
    proof (rule arg_cong[where f = "ess_inf_time Q"], rule ext)
      fix \<omega> :: "'n pairpath"
      have "pexit S K (\<lambda>t. fst (pcut S \<omega> t)) = pexit S K (\<lambda>t. fst (\<omega> t))"
        by (rule pexit_cong_on) (auto simp: pcut_apply)
      then show "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
          = min (pexit T K (\<lambda>t. fst (\<omega> t))) S"
        using pexit_min_horizon[OF S0 ST, of K "\<lambda>t. fst (\<omega> t)"] by simp
    qed
    also have "\<dots> = min (ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
        (ennreal S)"
      by (rule ess_inf_time_min_const[OF PQ])
    finally have val: "ess_inf_time (pair_law_of S (pcut S) Q)
          (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
        = min (ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal S)" .
    have inS: "pair_law_of S (pcut S) Q \<in> exit_class k L S x"
      by (rule exit_class_pcut[OF S0 ST Q])
    have "b < min (ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal S)"
      using bQ bS by simp
    also have "\<dots> = ess_inf_time (pair_law_of S (pcut S) Q)
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))" using val ..
    also have "\<dots> \<le> exit_val k L S K x"
      unfolding exit_val_def using inS by (intro Sup_upper imageI)
    finally show False using b1 by simp
  qed
qed

section \<open>The horizon-parametrised measurable selector\<close>

text \<open>@{thm [source] exit_val_horizon_cap} turns the selection problem into a
  pushforward problem.  The optimizer of the capped value is the optimizer
  of the uncapped one --- capping is an outer \<open>min\<close>, which is monotone ---
  so the selector \<^emph>\<open>at the full horizon\<close> already selects optimally at
  every shorter horizon, once it is cut there.  The parameter \<open>s\<close>
  therefore enters only through the map \<^const>\<open>pembed\<close>, and what has to
  be proved is joint measurability of a pushforward, not a new selection
  theorem.

  Three small facts make the composite work.  First, \<^const>\<open>pembed\<close> reads
  a path only on \<open>[0,T-s]\<close>, so pre-cutting is invisible to it
  (\<open>pembed_pcut\<close>) --- which is what identifies the pushforward of a
  \<open>T\<close>-law with the pushforward of its cut, i.e. with a member of
  \<^const>\<open>pdelclass\<close>.  Second, \<^const>\<open>pembed\<close> maps the \<open>T\<close>-space to itself
  (\<open>pembed_mspace_full\<close>), so no horizon bookkeeping is needed.  Third,
  clamping \<open>s\<close> to \<open>[0,T]\<close> makes the map total, and then
  @{thm [source] path_eval_at_measurable_time} gives joint measurability in
  the pair \<open>(s,\<omega>)\<close>: each evaluation of \<open>pembed s T \<omega>\<close> is the evaluation
  of \<open>\<omega>\<close> at a time that depends measurably on \<open>s\<close>.\<close>

lemma pembed_pcut:
  fixes \<omega> :: "'n::finite pairpath"
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

lemma pembed_mspace_full:
  fixes \<omega> :: "'n::finite pairpath"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pembed s T \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. max (t - s) 0)"
    by (intro continuous_intros)
  have im: "(\<lambda>t. max (t - s) 0) ` {0..T} \<subseteq> {0..T}" using s0 sT by auto
  have "continuous_on {0..T} (\<lambda>t. \<omega> (max (t - s) 0))"
    by (rule continuous_on_compose2[OF c m im])
  then show ?thesis unfolding pembed_def by (rule mspace_path_metricI)
qed

lemma pembed_measurable_full:
  fixes s T :: real
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "pembed s T \<in> borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric))
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have a: "0 \<le> T - s" using sT by simp
  have b: "T - s \<le> T" using s0 by simp
  have eq: "(\<lambda>\<omega> :: 'n pairpath. pembed s T (pcut (T - s) \<omega>)) = pembed s T"
    by (rule ext) (rule pembed_pcut[OF s0 sT])
  have "(\<lambda>\<omega>. pembed s T (pcut (T - s) \<omega>)) \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule measurable_compose[OF pcut_measurable[OF a b refl]
          pembed_measurable[OF s0 sT]])
  then show ?thesis unfolding eq .
qed

text \<open>The clamped delayed embedding: total in \<open>s\<close>, and equal to
  \<^const>\<open>pembed\<close> on the range that matters.  Totality lets the parameter
  live in \<^term>\<open>borel :: real measure\<close> rather than in a restricted space.\<close>

definition pdel :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "pdel s T = pembed (max 0 (min s T)) T"

lemma pdel_eq_pembed: "0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> pdel s T = pembed s T"
  unfolding pdel_def by simp

lemma pdel_clamp_lo: "0 \<le> max 0 (min (s::real) (T::real))"
  by (rule max.cobounded1)

lemma pdel_clamp_hi:
  fixes s T :: real
  assumes "0 \<le> T" shows "max 0 (min s T) \<le> T"
  using assms by (intro max.boundedI) auto

lemma pdel_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pdel s T \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  unfolding pdel_def
  by (rule pembed_mspace_full[OF pdel_clamp_lo pdel_clamp_hi[OF T0] w])

lemma pdel_measurable:
  assumes T0: "0 \<le> T"
  shows "pdel s T \<in> borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric))
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  unfolding pdel_def
  by (rule pembed_measurable_full[OF pdel_clamp_lo pdel_clamp_hi[OF T0]])

lemma pdel_eval: "t \<in> {0..T} \<Longrightarrow> pdel s T \<omega> t = \<omega> (max (t - max 0 (min s T)) 0)"
  unfolding pdel_def by (rule pembed_apply)

lemma pdel_measurable_pair:
  assumes T0: "0 \<le> T"
  shows "(\<lambda>p. pdel (fst p) T (snd p))
      \<in> (borel :: real measure) \<Otimes>\<^sub>M borel_of (mtopology_of
          (path_metric T :: ('n::finite pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?M = "(borel :: real measure) \<Otimes>\<^sub>M ?B"
  have spM: "space ?M = UNIV \<times> mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_pair_measure space_borel_of)
  have into: "pdel (fst p) T (snd p)
      \<in> mspace (path_metric T :: ('n pairpath) metric)" if p: "p \<in> space ?M" for p
  proof -
    have "p \<in> UNIV \<times> mspace (path_metric T :: ('n pairpath) metric)"
      using p unfolding spM .
    then have "snd p \<in> mspace (path_metric T :: ('n pairpath) metric)"
      by (simp add: mem_Times_iff)
    then show ?thesis by (rule pdel_mspace[OF T0])
  qed
  have sndm: "(\<lambda>p :: real \<times> ('n pairpath). snd p) \<in> ?M \<rightarrow>\<^sub>M ?B"
    by (rule measurable_snd)
  have ev: "(\<lambda>p. pdel (fst p) T (snd p) t) \<in> borel_measurable ?M" for t
  proof (cases "t \<in> {0..T}")
    case True
    have gm: "(\<lambda>p :: real \<times> ('n pairpath). max (t - max 0 (min (fst p) T)) 0)
        \<in> borel_measurable ?M" by measurable
    have g0: "0 \<le> max (t - max 0 (min (fst p) T)) 0"
      for p :: "real \<times> ('n pairpath)" by simp
    have gT: "max (t - max 0 (min (fst p) T)) 0 \<le> T"
      for p :: "real \<times> ('n pairpath)" using True by auto
    have "(\<lambda>p :: real \<times> ('n pairpath).
        snd p (max (t - max 0 (min (fst p) T)) 0)) \<in> borel_measurable ?M"
      by (rule path_eval_at_measurable_time
          [where X = "\<lambda>p :: real \<times> ('n pairpath). snd p"
            and g = "\<lambda>p :: real \<times> ('n pairpath). max (t - max 0 (min (fst p) T)) 0",
            OF T0 sndm gm g0 gT])
    then show ?thesis using True by (simp add: pdel_eval)
  next
    case False
    then have "(\<lambda>p :: real \<times> ('n pairpath). pdel (fst p) T (snd p) t)
        = (\<lambda>p. undefined)"
      unfolding pdel_def by (simp add: pembed_outside)
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>p. mdist (path_metric T :: ('n pairpath) metric)
        (pdel (fst p) T (snd p)) a) \<in> borel_measurable ?M"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

subsection \<open>Cutting a law commutes with shifting, and caps its value\<close>

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

lemma pshift_law_pcut:
  fixes R :: "('n::finite pairpath) measure"
  assumes S0: "0 \<le> S" and ST: "S \<le> T"
    and setsR: "sets R = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pshift_law S y (pair_law_of S (pcut S) R)
       = pair_law_of S (pcut S) (pshift_law T y R)"
proof -
  let ?BS = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  let ?BT = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using S0 ST by simp
  have cutR: "pcut S \<in> R \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST setsR])
  have cutT: "pcut S \<in> ?BT \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST refl])
  have shS: "pshift S y \<in> ?BS \<rightarrow>\<^sub>M ?BS" by (rule pshift_measurable[OF S0])
  have shR: "pshift T y \<in> R \<rightarrow>\<^sub>M ?BT"
    unfolding measurable_cong_sets[OF setsR refl] by (rule pshift_measurable[OF T0])
  have "pshift_law S y (pair_law_of S (pcut S) R)
      = distr (distr R ?BS (pcut S)) ?BS (pshift S y)"
    unfolding pshift_law_def pair_law_of_def ..
  also have "\<dots> = distr R ?BS (pshift S y \<circ> pcut S)"
    by (rule distr_distr[OF shS cutR])
  also have "pshift S y \<circ> pcut S = pcut S \<circ> pshift T y"
    by (rule ext) (simp add: pshift_pcut_comm[OF S0 ST])
  also have "distr R ?BS (pcut S \<circ> pshift T y)
      = distr (distr R ?BT (pshift T y)) ?BS (pcut S)"
    by (rule distr_distr[OF cutT shR, symmetric])
  also have "\<dots> = pair_law_of S (pcut S) (pshift_law T y R)"
    unfolding pshift_law_def pair_law_of_def ..
  finally show ?thesis .
qed

text \<open>The value of a cut law is the value of the original, capped.  This is
  the law-level form of @{thm [source] pexit_min_horizon}, and it is what
  makes one selector serve every horizon.\<close>

lemma ess_inf_pexit_pcut_law:
  fixes R :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes S0: "0 \<le> S" and ST: "S \<le> T" and PR: "prob_space R"
    and setsR: "sets R = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and K: "closed K"
  shows "ess_inf_time (pshift_law S y (pair_law_of S (pcut S) R))
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
      = min (ess_inf_time (pshift_law T y R)
          (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal S)"
proof -
  let ?BS = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  let ?P = "pshift_law T y R"
  have T0: "0 \<le> T" using S0 ST by simp
  have setsP: "sets ?P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" by simp
  have PP: "prob_space ?P" by (rule prob_space_pshift_law[OF T0 PR setsR])
  have cutm: "pcut S \<in> ?P \<rightarrow>\<^sub>M ?BS" by (rule pcut_measurable[OF S0 ST setsP])
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit S K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BS"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. pexit S K (pfst S \<omega>)) \<in> borel_measurable ?BS"
      by (rule measurable_compose[OF pfst_measurable[OF S0 refl]
            pexit_measurable[OF S0 K]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  have mset: "{\<omega> \<in> space ?BS. c \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))}
      \<in> sets ?BS" for c :: ennreal using taum by measurable
  have "ess_inf_time (pshift_law S y (pair_law_of S (pcut S) R))
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
      = ess_inf_time (pair_law_of S (pcut S) ?P)
        (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))"
    unfolding pshift_law_pcut[OF S0 ST setsR] ..
  also have "\<dots> = ess_inf_time ?P (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (pcut S \<omega> t)))"
    unfolding pair_law_of_def by (rule ess_inf_time_distr[OF cutm mset])
  also have "\<dots> = ess_inf_time ?P (\<lambda>\<omega>. min (pexit T K (\<lambda>t. fst (\<omega> t))) S)"
  proof (rule arg_cong[where f = "ess_inf_time ?P"], rule ext)
    fix \<omega> :: "'n pairpath"
    have "pexit S K (\<lambda>t. fst (pcut S \<omega> t)) = pexit S K (\<lambda>t. fst (\<omega> t))"
      by (rule pexit_cong_on) (auto simp: pcut_apply)
    then show "pexit S K (\<lambda>t. fst (pcut S \<omega> t))
        = min (pexit T K (\<lambda>t. fst (\<omega> t))) S"
      using pexit_min_horizon[OF S0 ST, of K "\<lambda>t. fst (\<omega> t)"] by simp
  qed
  also have "\<dots> = min (ess_inf_time ?P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      (ennreal S)" by (rule ess_inf_time_min_const[OF PP])
  finally show ?thesis .
qed

subsection \<open>The selector\<close>

text \<open>One selector, every horizon.  \<open>Sel (s,y)\<close> is the \<^const>\<open>pembed\<close>-image of
  the horizon-\<open>T\<close> optimizer started at \<open>y\<close>, cut back to \<open>T-s\<close>; it lands in
  \<^const>\<open>pdelclass\<close>, is jointly measurable in \<open>(s,y)\<close> as a Giry kernel, and
  re-basing it attains \<^term>\<open>exit_val k L (T - s) K y\<close>.  This is the
  continuation @{thm [source] exit_class_aglue} consumes for the
  additive glue.\<close>

theorem exit_val_measurable_selector_horizon:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains Sel where
    "Sel \<in> (borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
    and "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> Sel (s, y) \<in> pdelclass k L T s"
    and "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow>
        distr (Sel (s, y)) (borel_of (mtopology_of
            (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)
          \<in> exit_class k L (T - s) (0 :: real^'n)"
    and "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow>
        ess_inf_time (pshift_law (T - s) y
            (distr (Sel (s, y)) (borel_of (mtopology_of
              (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)))
          (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - s) K y"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?P = "(borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)"
  have T0: "0 \<le> T" using T by simp
  obtain S0 where S0k: "S0 \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
    and S0C: "\<And>y. S0 y \<in> exit_class k L T (0 :: real^'n)"
    and S0val: "\<And>y. ess_inf_time (pshift_law T y (S0 y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K y"
    by (rule exit_val_measurable_selector_kernel'[where k = k, OF T L K]) blast
  have setsS0: "sets (S0 y) = sets ?B" for y by (rule exit_class_sets[OF S0C])
  have PS0: "prob_space (S0 y)" for y by (rule exit_class_prob[OF S0C])
  define Sel where "Sel = (\<lambda>p :: real \<times> (real^'n).
      distr (S0 (snd p)) ?B (pdel (fst p) T))"

  \<comment> \<open>joint measurability: a pushforward along a jointly measurable map\<close>
  have fm: "case_prod (\<lambda>p :: real \<times> (real^'n). pdel (fst p) T)
      \<in> ?P \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B"
  proof -
    have m1: "(\<lambda>q :: (real \<times> (real^'n)) \<times> ('n pairpath). (fst (fst q), snd q))
        \<in> ?P \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M (borel :: real measure) \<Otimes>\<^sub>M ?B" by measurable
    have "(\<lambda>q :: (real \<times> (real^'n)) \<times> ('n pairpath).
        pdel (fst (fst q)) T (snd q)) \<in> ?P \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B"
      using measurable_compose[OF m1 pdel_measurable_pair[OF T0]] by simp
    then show ?thesis by (simp add: case_prod_beta)
  qed
  have gm: "(\<lambda>p :: real \<times> (real^'n). S0 (snd p)) \<in> ?P \<rightarrow>\<^sub>M subprob_algebra ?B"
    by (rule measurable_prob_algebraD[OF measurable_compose[OF measurable_snd S0k]])
  have Selm: "Sel \<in> ?P \<rightarrow>\<^sub>M prob_algebra ?B"
    unfolding Sel_def
  proof (rule measurable_prob_algebraI)
    fix p :: "real \<times> (real^'n)" assume "p \<in> space ?P"
    show "prob_space (distr (S0 (snd p)) ?B (pdel (fst p) T))"
    proof (rule prob_space.prob_space_distr[OF PS0])
      show "pdel (fst p) T \<in> S0 (snd p) \<rightarrow>\<^sub>M ?B"
        unfolding measurable_cong_sets[OF setsS0 refl]
        by (rule pdel_measurable[OF T0])
    qed
  next
    show "(\<lambda>p :: real \<times> (real^'n). distr (S0 (snd p)) ?B (pdel (fst p) T))
        \<in> ?P \<rightarrow>\<^sub>M subprob_algebra ?B"
      by (rule measurable_distr2[OF fm gm])
  qed

  \<comment> \<open>the cut law, and the two identifications it produces\<close>
  have main: "Sel (s, y) = distr (pair_law_of (T - s) (pcut (T - s)) (S0 y))
        ?B (pembed s T)
      \<and> distr (Sel (s, y)) (borel_of (mtopology_of
          (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)
        = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
    if s0: "0 \<le> s" and sT: "s \<le> T" for s y
  proof -
    let ?Bs = "borel_of (mtopology_of
        (path_metric (T - s) :: ('n pairpath) metric))"
    have a: "0 \<le> T - s" using sT by simp
    have b: "T - s \<le> T" using s0 by simp
    have cutm: "pcut (T - s) \<in> S0 y \<rightarrow>\<^sub>M ?Bs"
      by (rule pcut_measurable[OF a b setsS0])
    have cutB: "pcut (T - s) \<in> ?B \<rightarrow>\<^sub>M ?Bs" by (rule pcut_measurable[OF a b refl])
    have emb: "pembed s T \<in> ?Bs \<rightarrow>\<^sub>M ?B" by (rule pembed_measurable[OF s0 sT])
    have embB: "pembed s T \<in> S0 y \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsS0 refl]
      by (rule pembed_measurable_full[OF s0 sT])
    have reb: "prebase s T \<in> ?B \<rightarrow>\<^sub>M ?Bs" by (rule prebase_measurable[OF s0 sT])
    have comp: "pembed s T \<circ> pcut (T - s) = pembed s T"
      by (rule ext) (simp add: pembed_pcut[OF s0 sT])
    have first: "Sel (s, y)
        = distr (pair_law_of (T - s) (pcut (T - s)) (S0 y)) ?B (pembed s T)"
    proof -
      have "distr (pair_law_of (T - s) (pcut (T - s)) (S0 y)) ?B (pembed s T)
          = distr (S0 y) ?B (pembed s T \<circ> pcut (T - s))"
        unfolding pair_law_of_def by (rule distr_distr[OF emb cutm])
      also have "\<dots> = distr (S0 y) ?B (pembed s T)" unfolding comp ..
      finally show ?thesis
        unfolding Sel_def fst_conv snd_conv pdel_eq_pembed[OF s0 sT] ..
    qed
    have second: "distr (Sel (s, y)) ?Bs (prebase s T)
        = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
    proof -
      have "distr (Sel (s, y)) ?Bs (prebase s T)
          = distr (distr (S0 y) ?B (pembed s T)) ?Bs (prebase s T)"
        unfolding Sel_def fst_conv snd_conv pdel_eq_pembed[OF s0 sT] ..
      also have "\<dots> = distr (S0 y) ?Bs (prebase s T \<circ> pembed s T)"
        by (rule distr_distr[OF reb embB])
      also have "\<dots> = distr (S0 y) ?Bs (pcut (T - s))"
      proof (rule distr_cong[OF refl refl])
        fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space (S0 y)"
        then have wm: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using space_of_path_sets[OF setsS0] by simp
        then have cm: "pcut (T - s) \<omega>
            \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
          using measurable_space[OF cutB] by (simp add: space_borel_of)
        have "(prebase s T \<circ> pembed s T) \<omega> = prebase s T (pembed s T \<omega>)" by simp
        also have "\<dots> = prebase s T (pembed s T (pcut (T - s) \<omega>))"
          unfolding pembed_pcut[OF s0 sT] ..
        also have "\<dots> = pcut (T - s) \<omega>" by (rule prebase_pembed[OF s0 sT cm])
        finally show "(prebase s T \<circ> pembed s T) \<omega> = pcut (T - s) \<omega>" .
      qed
      finally show ?thesis unfolding pair_law_of_def .
    qed
    show ?thesis using first second by blast
  qed

  show ?thesis
  proof (rule that)
    show "Sel \<in> ?P \<rightarrow>\<^sub>M prob_algebra ?B" by (rule Selm)
  next
    show "Sel (s, y) \<in> pdelclass k L T s" if s0: "0 \<le> s" and sT: "s \<le> T"
      for s :: real and y :: "real^'n"
    proof -
      have a: "0 \<le> T - s" using sT by simp
      have b: "T - s \<le> T" using s0 by simp
      have cutC: "pair_law_of (T - s) (pcut (T - s)) (S0 y)
          \<in> exit_class k L (T - s) (0 :: real^'n)"
        by (rule exit_class_pcut[OF a b S0C])
      have m1: "Sel (s, y)
          = distr (pair_law_of (T - s) (pcut (T - s)) (S0 y)) ?B (pembed s T)"
        using main[OF s0 sT, of y] by blast
      show ?thesis unfolding pdelclass_def m1 using cutC by (rule imageI)
    qed
  next
    show "distr (Sel (s, y)) (borel_of (mtopology_of
          (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)
        \<in> exit_class k L (T - s) (0 :: real^'n)"
      if s0: "0 \<le> s" and sT: "s \<le> T" for s :: real and y :: "real^'n"
    proof -
      have a: "0 \<le> T - s" using sT by simp
      have b: "T - s \<le> T" using s0 by simp
      have m2: "distr (Sel (s, y)) (borel_of (mtopology_of
            (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)
          = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
        using main[OF s0 sT, of y] by blast
      show ?thesis unfolding m2 by (rule exit_class_pcut[OF a b S0C])
    qed
  next
    show "ess_inf_time (pshift_law (T - s) y
          (distr (Sel (s, y)) (borel_of (mtopology_of
            (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)))
        (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - s) K y"
      if s0: "0 \<le> s" and sT: "s \<le> T" for s :: real and y :: "real^'n"
    proof -
      have a: "0 \<le> T - s" using sT by simp
      have b: "T - s \<le> T" using s0 by simp
      have m2: "distr (Sel (s, y)) (borel_of (mtopology_of
            (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)
          = pair_law_of (T - s) (pcut (T - s)) (S0 y)"
        using main[OF s0 sT, of y] by blast
      have "ess_inf_time (pshift_law (T - s) y
            (pair_law_of (T - s) (pcut (T - s)) (S0 y)))
          (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t)))
          = min (ess_inf_time (pshift_law T y (S0 y))
              (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))) (ennreal (T - s))"
        by (rule ess_inf_pexit_pcut_law[OF a b PS0 setsS0 K])
      also have "\<dots> = min (exit_val k L T K y) (ennreal (T - s))"
        unfolding S0val ..
      also have "\<dots> = exit_val k L (T - s) K y"
        by (rule exit_val_horizon_cap[OF a b L K, symmetric])
      finally show ?thesis unfolding m2 .
    qed
  qed
qed

section \<open>The delayed class supplies the additive glue's kernel clauses\<close>

text \<open>@{thm [source] exit_class_aglue} asks its continuation kernel for
  nine facts.  Four are already in hand for \<^const>\<open>pdelclass\<close> --- \<open>Kp\<close>
  (the selector's own measurability), \<open>prob_space\<close>/\<open>sets\<close>
  (@{thm [source] pdelclass_prob}), \<open>K0\<close>
  (@{thm [source] pdelclass_frozen_at} at \<open>u = 0\<close>) and \<open>Kfr\<close>
  (@{thm [source] pdelclass_frozen}).  The rest follow from one structural
  statement: a delayed law's two class processes are still martingales on
  the fixed \<open>T\<close>-space, in the delayed law's own natural filtration.

  The reason is that delaying is a time change: a delayed path evaluated
  at \<open>u\<close> is the base path evaluated at \<open>\<rho> u = (u - s) \<or> 0 \<and> (T - s)\<close>,
  which is nondecreasing, so @{thm [source] martingale_time_change} turns
  the base martingale into a martingale for the time-changed filtration
  \<open>\<F>\<^sup>\<mu>\<^sub>(\<rho> u)\<close> --- exactly what @{thm [source] martingale_pair_law}
  needs to push the martingale forward along \<^const>\<open>pembed\<close>.  A delayed
  path carries no extra information at time \<open>u\<close>, which is why the
  martingale property survives the delay; taking the base's own filtration
  instead would make the statement false.  \<open>martingale_time_change_cong\<close>
  lives in @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

lemma path_eval_natural_filtration:
  fixes M :: "('n::finite pairpath) measure"
  assumes t0: "0 \<le> t" and tu: "t \<le> u"
  shows "(\<lambda>w :: 'n pairpath. w t)
      \<in> natural_filtration M 0 (\<lambda>v w. w v) u \<rightarrow>\<^sub>M borel"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use t0 tu in auto)

text \<open>The time change itself: reading a delayed path at \<open>u\<close> is reading the
  base path at \<open>\<rho> u\<close>.  Pure arithmetic, no membership.\<close>

lemma pembed_eval_min:
  fixes w :: "'n::finite pairpath"
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

lemma pembed_eval_le:
  fixes w :: "'n::finite pairpath"
  assumes r0: "0 \<le> r" and ru: "r \<le> u" and s0: "0 \<le> s" and sT: "s \<le> T"
  shows "(\<lambda>w :: 'n pairpath. pembed s T w r) \<in> borel_measurable
      (natural_filtration M 0 (\<lambda>v w. w v) (min (max (u - s) 0) (T - s)))"
proof (cases "r \<le> T")
  case True
  have e1: "0 \<le> max (r - s) 0" by simp
  have e2: "max (r - s) 0 \<le> min (max (u - s) 0) (T - s)"
    using r0 ru s0 sT True by (auto simp: min_def max_def)
  have mem: "r \<in> {0..T}" using r0 True by simp
  have "(\<lambda>w :: 'n pairpath. w (max (r - s) 0)) \<in> borel_measurable
      (natural_filtration M 0 (\<lambda>v w. w v) (min (max (u - s) 0) (T - s)))"
    by (rule path_eval_natural_filtration[OF e1 e2])
  then show ?thesis by (simp add: pembed_apply[OF mem])
next
  case False
  then have "r \<notin> {0..T}" by simp
  then have "(\<lambda>w :: 'n pairpath. pembed s T w r) = (\<lambda>w. undefined)"
    by (simp add: pembed_outside)
  then show ?thesis by simp
qed

theorem pdelclass_X_martingale:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "martingale \<nu> (natural_filtration \<nu> 0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. fst (w (min u T)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  let ?rho = "\<lambda>u :: real. min (max (u - s) 0) (T - s)"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have Pmu: "prob_space \<mu>" by (rule exit_class_prob[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nu': "\<nu> = pair_law_of T (pembed s T) \<mu>"
    unfolding nu pair_law_of_def ..
  let ?F = "natural_filtration \<mu> 0 (\<lambda>v w :: 'n pairpath. w v)"
  have mgb: "martingale \<mu> ?F 0 (\<lambda>t w. fst (w (min t (T - s))))"
    by (rule exit_class_X_martingale[OF mu])
  have tc: "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
      (\<lambda>u w. fst (pembed s T w (min u T)))"
  proof (rule martingale_time_change_cong[OF mgb])
    show "0 \<le> ?rho u" if "0 \<le> u" for u :: real using Ts that by simp
    show "?rho u \<le> ?rho v" if "0 \<le> u" "u \<le> v" for u v :: real
      using that by simp
    show "(\<lambda>w :: 'n pairpath. fst (pembed s T w (min u T)))
        = (\<lambda>w. fst (w (min (?rho u) (T - s))))" if u: "0 \<le> u" for u :: real
    proof (rule ext)
      fix w :: "'n pairpath"
      have "pembed s T w (min u T) = w (?rho u)"
        by (rule pembed_eval_min[OF u s0 sT])
      moreover have "min (?rho u) (T - s) = ?rho u" by simp
      ultimately show "fst (pembed s T w (min u T))
          = fst (w (min (?rho u) (T - s)))" by simp
    qed
  qed
  show ?thesis
    unfolding nu'
  proof (rule martingale_pair_law[where T = T and FF = "\<lambda>u. ?F (?rho u)"])
    show "prob_space \<mu>" by (rule Pmu)
    show "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B" by (rule pm)
    show "(\<lambda>w. pembed s T w r) \<in> borel_measurable (?F (?rho u))"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pembed_eval_le[OF that s0 sT])
    show "(\<lambda>w :: 'n pairpath. fst (w (min u T))) \<in> borel_measurable
        (natural_filtration (pair_law_of T (pembed s T) \<mu>)
          0 (\<lambda>v w. w v) u)" if u: "0 \<le> u" for u :: real
    proof -
      have a: "0 \<le> min u T" using u T0 by simp
      have b: "min u T \<le> u" by simp
      have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis
        by (rule measurable_compose
            [OF path_eval_natural_filtration[OF a b] fstB])
    qed
    show "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
        (\<lambda>u w. fst (pembed s T w (min u T)))" by (rule tc)
  qed
qed

theorem pdelclass_comp_martingale:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "martingale \<nu> (natural_filtration \<nu> 0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. outerp (fst (w (min u T))) - snd (w (min u T)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  let ?rho = "\<lambda>u :: real. min (max (u - s) 0) (T - s)"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have Pmu: "prob_space \<mu>" by (rule exit_class_prob[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nu': "\<nu> = pair_law_of T (pembed s T) \<mu>"
    unfolding nu pair_law_of_def ..
  let ?F = "natural_filtration \<mu> 0 (\<lambda>v w :: 'n pairpath. w v)"
  have mgb: "martingale \<mu> ?F 0
      (\<lambda>t w. outerp (fst (w (min t (T - s)))) - snd (w (min t (T - s))))"
    by (rule exit_class_comp_martingale[OF mu])
  have tc: "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
      (\<lambda>u w. outerp (fst (pembed s T w (min u T)))
          - snd (pembed s T w (min u T)))"
  proof (rule martingale_time_change_cong[OF mgb])
    show "0 \<le> ?rho u" if "0 \<le> u" for u :: real using Ts that by simp
    show "?rho u \<le> ?rho v" if "0 \<le> u" "u \<le> v" for u v :: real
      using that by simp
    show "(\<lambda>w :: 'n pairpath. outerp (fst (pembed s T w (min u T)))
          - snd (pembed s T w (min u T)))
        = (\<lambda>w. outerp (fst (w (min (?rho u) (T - s))))
          - snd (w (min (?rho u) (T - s))))" if u: "0 \<le> u" for u :: real
    proof (rule ext)
      fix w :: "'n pairpath"
      have "pembed s T w (min u T) = w (?rho u)"
        by (rule pembed_eval_min[OF u s0 sT])
      moreover have "min (?rho u) (T - s) = ?rho u" by simp
      ultimately show "outerp (fst (pembed s T w (min u T)))
            - snd (pembed s T w (min u T))
          = outerp (fst (w (min (?rho u) (T - s))))
            - snd (w (min (?rho u) (T - s)))" by simp
    qed
  qed
  show ?thesis
    unfolding nu'
  proof (rule martingale_pair_law[where T = T and FF = "\<lambda>u. ?F (?rho u)"])
    show "prob_space \<mu>" by (rule Pmu)
    show "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B" by (rule pm)
    show "(\<lambda>w. pembed s T w r) \<in> borel_measurable (?F (?rho u))"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pembed_eval_le[OF that s0 sT])
    show "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u T))) - snd (w (min u T)))
        \<in> borel_measurable (natural_filtration
          (pair_law_of T (pembed s T) \<mu>) 0 (\<lambda>v w. w v) u)"
      if u: "0 \<le> u" for u :: real
    proof -
      have a: "0 \<le> min u T" using u T0 by simp
      have b: "min u T \<le> u" by simp
      have cm: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
          \<in> borel_measurable borel"
        unfolding outerp_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis
        by (rule measurable_compose
            [OF path_eval_natural_filtration[OF a b] cm])
    qed
    show "martingale \<mu> (\<lambda>u. ?F (?rho u)) 0
        (\<lambda>u w. outerp (fst (pembed s T w (min u T)))
            - snd (pembed s T w (min u T)))" by (rule tc)
  qed
qed

subsection \<open>The covariation clause of the continuation\<close>

text \<open>The guard \<open>s \<le> a\<close> makes this the delayed constraint: below \<open>s\<close> the
  path stands still, so no difference quotient there can lie in
  \<^const>\<open>sconstraint\<close>, and the kernel is only ever asked about the
  stretch after the freeze.  One rational pair at a time
  (@{thm [source] closedin_diffquot_constraint} for measurability, so that
  @{thm [source] AE_distr_iff} applies), then two countable passes, then
  @{thm [source] diffquot_all_of_rational_ge} for the real pairs.\<close>

theorem pdelclass_diffquot:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "AE w in \<nu>. \<forall>a b. s \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T \<longrightarrow>
      (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using s0 sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have setsnu: "sets \<nu> = sets ?B" unfolding nu by simp
  have cov: "AE w in \<mu>. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T - s \<longrightarrow>
      (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
    using mu unfolding exit_class_def by blast
  have one: "AE w in \<nu>.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    if p: "p \<in> {0..T}" and q: "q \<in> {0..T}" and pq: "p < q" and sp: "s \<le> p"
    for p q :: real
  proof -
    have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
      by (simp add: space_borel_of)
    have mset: "{w \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L}
        \<in> sets ?B"
      unfolding spB
      by (rule borel_of_closed[OF closedin_diffquot_constraint[OF p q]])
    have "AE w in \<mu>. (1 / (q - p)) *\<^sub>R
        (snd (pembed s T w q) - snd (pembed s T w p)) \<in> sconstraint k L"
      using cov
    proof eventually_elim
      case (elim w)
      have ep: "pembed s T w p = w (p - s)"
      proof -
        have "pembed s T w p = w (max (p - s) 0)" by (rule pembed_apply[OF p])
        moreover have "max (p - s) 0 = p - s" using sp by simp
        ultimately show ?thesis by simp
      qed
      have eqq: "pembed s T w q = w (q - s)"
      proof -
        have "pembed s T w q = w (max (q - s) 0)" by (rule pembed_apply[OF q])
        moreover have "max (q - s) 0 = q - s" using sp pq by simp
        ultimately show ?thesis by simp
      qed
      have a0: "0 \<le> p - s" using sp by simp
      have ab: "p - s < q - s" using pq by simp
      have bT: "q - s \<le> T - s" using q by simp
      from elim have "(1 / ((q - s) - (p - s))) *\<^sub>R
          (snd (w (q - s)) - snd (w (p - s))) \<in> sconstraint k L"
        using a0 ab bT by blast
      then show ?case unfolding ep eqq by simp
    qed
    then show ?thesis unfolding nu AE_distr_iff[OF pm mset] .
  qed
  have rat: "AE w in \<nu>. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE w in \<nu>. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE w in \<nu>. p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
      proof (cases "p \<in> {0..T} \<and> q \<in> {0..T} \<and> p < q \<and> s \<le> p")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  have spn: "AE w in \<nu>. w \<in> space \<nu>" by (rule AE_space)
  from rat spn show ?thesis
  proof eventually_elim
    case (elim w)
    then have R: "\<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> s \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
      and W: "w \<in> space \<nu>" by blast+
    have mw: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W sets_eq_imp_space_eq[OF setsnu] by (simp add: space_borel_of)
    have cont: "continuous_on {0..T} (\<lambda>u. snd (w u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix a b :: real
      assume sa: "s \<le> a" and ab: "a < b" and bT: "b \<le> T"
      have a0: "0 \<le> a" using sa s0 by simp
      show "(1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
      proof (rule diffquot_all_of_rational_ge
          [OF closed_sconstraint cont _ sa a0 ab bT])
        fix p q :: real
        assume "p \<in> \<rat>" "q \<in> \<rat>" "0 \<le> p" "p < q" "q \<le> T" "s \<le> p"
        then show "(1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p))
            \<in> sconstraint k L" using R bT by auto
      qed
    qed
  qed
qed

subsection \<open>Mean, integrability and the increment identity\<close>

text \<open>A martingale that starts at \<open>0\<close> has mean \<open>0\<close> at every later time; the
  set-integral identity over the whole space is the case \<open>i = 0\<close> of the
  martingale property, and @{thm [source] pdelclass_frozen_at} supplies the
  start.  \<open>martingale_mean_zero_of_start\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra}.\<close>

lemma pdelclass_start_zero:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
  shows "AE w in \<nu>. w (min (0::real) T) = 0"
proof -
  have T0: "0 \<le> T" using s0 sT by simp
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have "AE w in \<nu>. w (0::real) = 0"
    by (rule pdelclass_frozen_at[OF s0 sT m z s0])
  then show ?thesis using T0 by simp
qed

corollary pdelclass_X_int:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "integrable \<nu> (\<lambda>w. fst (w (min u T)) $ e)"
  by (rule martingale.integrable
      [OF martingale_vec_component[OF pdelclass_X_martingale[OF s0 sT m]] u])

corollary pdelclass_comp_int:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "integrable \<nu>
      (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
  by (rule martingale.integrable
      [OF martingale_mat_component[OF pdelclass_comp_martingale[OF s0 sT m]] u])

corollary pdelclass_X_increment:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and C: "C \<in> sets (natural_filtration \<nu> 0 (\<lambda>t w. w t) u)"
    and u: "0 \<le> u" and uv: "u \<le> v"
  shows "set_lebesgue_integral \<nu> C (\<lambda>w. fst (w (min u T)) $ e)
      = set_lebesgue_integral \<nu> C (\<lambda>w. fst (w (min v T)) $ e)"
  by (rule martingale.set_integral_eq
      [OF martingale_vec_component[OF pdelclass_X_martingale[OF s0 sT m]]
        C u uv])

corollary pdelclass_comp_increment:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and C: "C \<in> sets (natural_filtration \<nu> 0 (\<lambda>t w. w t) u)"
    and u: "0 \<le> u" and uv: "u \<le> v"
  shows "set_lebesgue_integral \<nu> C
        (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
      = set_lebesgue_integral \<nu> C
        (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
  by (rule martingale.set_integral_eq
      [OF martingale_mat_component[OF pdelclass_comp_martingale[OF s0 sT m]]
        C u uv])

corollary pdelclass_X_mean:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "(\<integral>w. fst (w (min u T)) $ e \<partial>\<nu>) = 0"
proof (rule martingale_mean_zero_of_start
    [OF martingale_vec_component[OF pdelclass_X_martingale[OF s0 sT m]] _ u])
  show "AE w in \<nu>. fst (w (min (0::real) T)) $ e = 0"
    using pdelclass_start_zero[OF s0 sT m] by (rule eventually_mono) simp
qed

corollary pdelclass_comp_mean:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and m: "\<nu> \<in> pdelclass k L T s"
    and u: "0 \<le> u"
  shows "(\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d \<partial>\<nu>)
      = 0"
proof (rule martingale_mean_zero_of_start
    [OF martingale_mat_component[OF pdelclass_comp_martingale[OF s0 sT m]] _ u])
  show "AE w in \<nu>. (outerp (fst (w (min (0::real) T)))
      - snd (w (min (0::real) T))) $ c $ d = 0"
    using pdelclass_start_zero[OF s0 sT m]
  proof (rule eventually_mono)
    fix w :: "'n pairpath" assume z: "w (min (0::real) T) = 0"
    have "outerp (fst (w (min (0::real) T))) = 0"
      unfolding z by (simp add: outerp_def zero_vec_def vec_eq_iff)
    then show "(outerp (fst (w (min (0::real) T)))
        - snd (w (min (0::real) T))) $ c $ d = 0" unfolding z by simp
  qed
qed

section \<open>The stopped past law satisfies the additive glue's \<open>Q\<close>-clauses\<close>

text \<open>\<open>Qst\<close> --- that the past law is carried by paths which are their own
  stopped versions --- is where the a.e. form is unavoidable, so its
  transfer needs the fixed-point set to be measurable.  It is: two paths
  that agree at every rational of \<open>[0,T]\<close> and are both continuous there
  agree everywhere (@{thm [source] vanishes_of_rational} on their
  difference), so the fixed-point set is a countable intersection of
  evaluation conditions --- the same shape as
  @{thm [source] frozen_set_measurable}.\<close>

lemma pstopped_fixed_set_measurable:
  fixes T :: real
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n::finite pairpath) metric)))"
  shows "{p' \<in> space (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))). pstopped T \<theta> p' = p'}
      \<in> sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?D = "{0..T} \<inter> \<rat>"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have pm: "pstopped T \<theta> \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have single: "{p' \<in> space ?B. pstopped T \<theta> p' q = p' q} \<in> sets ?B" for q
  proof -
    have m1: "(\<lambda>p' :: 'n pairpath. pstopped T \<theta> p' q) \<in> borel_measurable ?B"
      by (rule measurable_compose[OF pm pair_law_eval_measurable[OF refl]])
    have m2: "(\<lambda>p' :: 'n pairpath. p' q) \<in> borel_measurable ?B"
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
      fix p' :: "'n pairpath"
      assume h: "p' \<in> (\<Inter>q \<in> ?D. {p' \<in> space ?B. pstopped T \<theta> p' q = p' q})"
      from h ne have sp: "p' \<in> space ?B" by blast
      then have mw: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using spB by simp
      \<comment> \<open>\<open>OF\<close> against \<open>0 \<le> ?\<theta> ?\<omega>\<close> is not a higher-order PATTERN, so it has
          no unifiers; let the conclusion fix \<open>\<theta>\<close> and \<open>\<omega>\<close> first.\<close>
      have ms: "pstopped T \<theta> p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      proof (rule pstopped_mspace)
        show "0 \<le> \<theta> p'" by (rule th0)
        show "\<theta> p' \<le> T" by (rule thT)
        show "p' \<in> mspace (path_metric T :: ('n pairpath) metric)" by (rule mw)
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
  @{thm [source] pstopped_idem} transported through
  @{thm [source] AE_distr_iff}; \<open>Q0\<close> is the start clause of \<open>P\<close>, which the
  stopping does not touch because \<open>\<theta> \<ge> 0\<close>; \<open>Qcont\<close> is membership in the
  path space, the one clause that is pointwise on the space.\<close>

lemma pstopped_law_prob:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PS: "prob_space P"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "prob_space (pair_law_of T (pstopped T \<theta>) P)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  interpret PP: prob_space P by (rule PS)
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  show ?thesis unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
qed

lemma pstopped_law_idem:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P. pstopped T \<theta> p' = p'"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have mset: "{p' \<in> space ?B. pstopped T \<theta> p' = p'} \<in> sets ?B"
    by (rule pstopped_fixed_set_measurable[OF T0 st thM])
  have "AE \<omega> in P. pstopped T \<theta> (pstopped T \<theta> \<omega>) = pstopped T \<theta> \<omega>"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    then show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
        by (rule path_sets_fst_continuous[OF setsP elim])
      show ?case by (rule pstopped_idem[OF st cw])
    qed
  qed
  then show ?thesis
    unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
qed

lemma pstopped_law_start:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P.
      fst (p' 0) = x \<and> snd (p' 0) = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have ev: "(\<lambda>p' :: 'n pairpath. p' 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{p' \<in> space ?B. fst (p' 0) = x \<and> snd (p' 0) = 0} \<in> sets ?B"
  proof -
    have "{p' \<in> space ?B. fst (p' 0) = x \<and> snd (p' 0) = 0}
        = (\<lambda>p' :: 'n pairpath. p' 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have z: "(0::real) \<in> {0..T}" using T0 by simp
  have "AE \<omega> in P. fst (pstopped T \<theta> \<omega> 0) = x \<and> snd (pstopped T \<theta> \<omega> 0) = 0"
    using P0
  proof eventually_elim
    case (elim \<omega>)
    have "pstopped T \<theta> \<omega> 0 = \<omega> (min 0 (\<theta> \<omega>))" by (rule pstopped_apply[OF z])
    also have "min 0 (\<theta> \<omega>) = 0" using th0[of \<omega>] by simp
    finally show ?case using elim by simp
  qed
  then show ?thesis unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
qed

lemma pstopped_law_cont:
  fixes P :: "('n::finite pairpath) measure"
  assumes p: "p' \<in> space (pair_law_of T (pstopped T \<theta>) P)"
  shows "continuous_on {0..T} p'"
proof -
  have "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    using p by (simp add: space_pair_law_of)
  then show ?thesis by (rule mspace_path_metricD)
qed

text \<open>\<open>Qcov\<close>.  The stopped law's covariation constraint holds up to the
  random horizon \<open>\<theta> p'\<close>, exactly the shape
  @{thm [source] diffquot_all_of_rational} takes once its horizon
  parameter is instantiated with \<open>\<theta> p'\<close> rather than \<open>T\<close>.  No guarded
  variant is needed: the rationals the lemma picks already satisfy
  \<open>q < t \<le> \<theta> p'\<close>.\<close>

theorem pstopped_law_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Pcov: "AE \<omega> in P. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T \<longrightarrow>
        (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P.
      \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> \<theta> p' \<longrightarrow>
        (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have setsQ: "sets ?Q = sets ?B" by (rule sets_pair_law_of)
  have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have one: "AE p' in ?Q. q \<le> \<theta> p' \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
    if p: "p \<in> {0..T}" and q: "q \<in> {0..T}" and pq: "p < q" for p q :: real
  proof -
    have S: "{p' \<in> space ?B.
        (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}
        \<in> sets ?B"
      unfolding spB
      by (rule borel_of_closed[OF closedin_diffquot_constraint[OF p q]])
    have G: "{p' \<in> space ?B. q \<le> \<theta> p'} \<in> sets ?B" using thM by measurable
    have mset: "{p' \<in> space ?B. q \<le> \<theta> p' \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}
        \<in> sets ?B"
    proof -
      have "{p' \<in> space ?B. q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}
          = (space ?B - {p' \<in> space ?B. q \<le> \<theta> p'})
            \<union> {p' \<in> space ?B.
              (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L}"
        by auto
      then show ?thesis using S G by (simp add: sets.Un sets.compl_sets)
    qed
    have "AE \<omega> in P. q \<le> \<theta> (pstopped T \<theta> \<omega>) \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (pstopped T \<theta> \<omega> q) - snd (pstopped T \<theta> \<omega> p))
          \<in> sconstraint k L"
      using Pcov AE_space
    proof eventually_elim
      case (elim \<omega>)
      have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
        by (rule path_sets_fst_continuous[OF setsP elim(2)])
      show ?case
      proof
        assume "q \<le> \<theta> (pstopped T \<theta> \<omega>)"
        then have le: "q \<le> \<theta> \<omega>"
          unfolding path_stopping_time_stopped[OF st cw] .
        have eq: "pstopped T \<theta> \<omega> q = \<omega> q"
        proof -
          have "pstopped T \<theta> \<omega> q = \<omega> (min q (\<theta> \<omega>))" by (rule pstopped_apply[OF q])
          also have "min q (\<theta> \<omega>) = q" using le by simp
          finally show ?thesis .
        qed
        have ep: "pstopped T \<theta> \<omega> p = \<omega> p"
        proof -
          have "pstopped T \<theta> \<omega> p = \<omega> (min p (\<theta> \<omega>))" by (rule pstopped_apply[OF p])
          also have "min p (\<theta> \<omega>) = p" using le pq by simp
          finally show ?thesis .
        qed
        show "(1 / (q - p)) *\<^sub>R
            (snd (pstopped T \<theta> \<omega> q) - snd (pstopped T \<theta> \<omega> p)) \<in> sconstraint k L"
          unfolding eq ep using elim p q pq by auto
      qed
    qed
    then show ?thesis
      unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
  qed
  have rat: "AE p' in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE p' in ?Q. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE p' in ?Q. p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
      proof (cases "p \<in> {0..T} \<and> q \<in> {0..T} \<and> p < q")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  have spn: "AE p' in ?Q. p' \<in> space ?Q" by (rule AE_space)
  from rat spn show ?thesis
  proof eventually_elim
    case (elim p')
    then have R: "\<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> q \<le> \<theta> p' \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
      and W: "p' \<in> space ?Q" by blast+
    have mw: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W by (simp add: space_pair_law_of)
    have cT: "continuous_on {0..T} (\<lambda>u. snd (p' u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    have sub: "{0..\<theta> p'} \<subseteq> {0..T}" using thT[of p'] by auto
    have cont: "continuous_on {0..\<theta> p'} (\<lambda>u. snd (p' u))"
      by (rule continuous_on_subset[OF cT sub])
    show ?case
    proof (intro allI impI)
      fix a b :: real
      assume a0: "0 \<le> a" and ab: "a < b" and bth: "b \<le> \<theta> p'"
      show "(1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
      proof (rule diffquot_all_of_rational[OF closed_sconstraint cont _ a0 ab bth])
        fix p q :: real
        assume pq: "p \<in> \<rat>" "q \<in> \<rat>" "0 \<le> p" "p < q" "q \<le> \<theta> p'"
        have pT: "p \<in> {0..T}" using pq thT[of p'] by auto
        have qT: "q \<in> {0..T}" using pq thT[of p'] th0[of p'] by auto
        show "(1 / (q - p)) *\<^sub>R (snd (p' q) - snd (p' p)) \<in> sconstraint k L"
          using R pq pT qT by blast
      qed
    qed
  qed
qed

text \<open>The last input the two martingale clauses need: the stopped path,
  evaluated at a time \<open>r \<le> u\<close>, is \<open>\<F>\<^sub>u\<close>-measurable as a path point, with
  no componentwise decomposition.  The trick reads it off the \<open>u\<close>-cut
  rather than off the whole path: \<^const>\<open>pcut\<close> is measurable into the
  \<open>u\<close>-horizon space by the description of the natural filtration
  (@{thm [source] sets_natural_filtration_eq_pcut_vimage}), the truncated
  stopping time \<open>r \<and> \<theta>\<close> is \<open>\<F>\<^sub>u\<close>-measurable because \<open>{r \<and> \<theta> \<le> t}\<close> is
  either everything or \<open>{\<theta> \<le> t}\<close> with \<open>t < r\<close>, and
  @{thm [source] path_eval_at_measurable_time} joins the two.\<close>

lemma pstopped_eval_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and r0: "0 \<le> r" and ru: "r \<le> u"
  shows "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> r)
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
proof (cases "r \<le> T")
  case False
  then have "r \<notin> {0..T}" by simp
  then have "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> r) = (\<lambda>\<omega>. undefined)"
    by (simp add: pstopped_outside)
  then show ?thesis by simp
next
  case True
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?G = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  define u' where "u' = min u T"
  have u'0: "0 \<le> u'" using r0 ru True unfolding u'_def by simp
  have u'T: "u' \<le> T" unfolding u'_def by simp
  have u'u: "u' \<le> u" unfolding u'_def by simp
  have ru': "r \<le> u'" using ru True unfolding u'_def by simp
  have rmem: "r \<in> {0..T}" using r0 True by simp
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have spG: "space (?G v) = space P" for v
    unfolding natural_filtration_def by simp
  have nf: "?G v = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  let ?Bu = "borel_of (mtopology_of (path_metric u' :: ('n pairpath) metric))"

  \<comment> \<open>the truncated stopping time is measurable at level \<open>u'\<close>\<close>
  have gm: "(\<lambda>\<omega> :: 'n pairpath. min r (\<theta> \<omega>)) \<in> borel_measurable (?G u')"
  proof (rule borel_measurableI_le)
    fix t :: real
    show "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} \<in> sets (?G u')"
    proof (cases "r \<le> t")
      case True
      have e: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} = space (?G u')"
        using True by auto
      show ?thesis unfolding e by (rule sets.top)
    next
      case False
      then have lt: "t < r" by simp
      show ?thesis
      proof (cases "0 \<le> t")
        case True
        have eqs: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t}
            = {\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}" using lt sp spG by auto
        have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t}
            \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t)"
          by (rule path_stopping_time_event_filtration_all[OF T0 st thM True])
        then have inG: "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> t} \<in> sets (?G t)" unfolding nf .
        have "sets (?G t) \<subseteq> sets (?G u')"
          using lt ru' by (intro sets_natural_filtration_mono) simp
        with inG show ?thesis unfolding eqs by blast
      next
        case False
        then have tneg: "t < 0" by simp
        have e: "{\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t} = {}"
        proof (rule equals0I)
          fix x :: "'n pairpath"
          assume "x \<in> {\<omega> \<in> space (?G u'). min r (\<theta> \<omega>) \<le> t}"
          then have le: "min r (\<theta> x) \<le> t" by blast
          have "0 \<le> min r (\<theta> x)" using r0 th0[of x] by simp
          with le tneg show False by simp
        qed
        show ?thesis unfolding e by simp
      qed
    qed
  qed

  \<comment> \<open>the \<open>u'\<close>-cut is measurable at level \<open>u'\<close>\<close>
  have cutP: "pcut u' \<in> P \<rightarrow>\<^sub>M ?Bu" by (rule pcut_measurable[OF u'0 u'T setsP])
  have cutm: "pcut u' \<in> ?G u' \<rightarrow>\<^sub>M ?Bu"
  proof (rule measurableI)
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space (?G u')"
    then have "\<omega> \<in> space P" using spG by simp
    then show "pcut u' \<omega> \<in> space ?Bu" by (rule measurable_space[OF cutP])
  next
    fix A :: "('n pairpath) set" assume A: "A \<in> sets ?Bu"
    have "pcut u' -` A \<inter> space P \<in> sets (?G u')"
      unfolding sets_natural_filtration_eq_pcut_vimage[OF setsP u'0 u'T]
      using A by blast
    then show "pcut u' -` A \<inter> space (?G u') \<in> sets (?G u')"
      unfolding spG .
  qed

  have g0: "0 \<le> min r (\<theta> \<omega>)" for \<omega> :: "'n pairpath" using r0 th0[of \<omega>] by simp
  have gu: "min r (\<theta> \<omega>) \<le> u'" for \<omega> :: "'n pairpath" using ru' by simp
  have ev: "(\<lambda>\<omega> :: 'n pairpath. pcut u' \<omega> (min r (\<theta> \<omega>)))
      \<in> borel_measurable (?G u')"
    by (rule path_eval_at_measurable_time
        [where X = "pcut u'" and g = "\<lambda>\<omega> :: 'n pairpath. min r (\<theta> \<omega>)",
          OF u'0 cutm gm g0 gu])
  have same: "(\<lambda>\<omega> :: 'n pairpath. pcut u' \<omega> (min r (\<theta> \<omega>)))
      = (\<lambda>\<omega>. pstopped T \<theta> \<omega> r)"
  proof (rule ext)
    fix \<omega> :: "'n pairpath"
    have m: "min r (\<theta> \<omega>) \<in> {0..u'}" using g0[of \<omega>] gu[of \<omega>] by simp
    have "pcut u' \<omega> (min r (\<theta> \<omega>)) = \<omega> (min r (\<theta> \<omega>))" by (rule pcut_apply[OF m])
    also have "\<dots> = pstopped T \<theta> \<omega> r" by (rule pstopped_apply[OF rmem, symmetric])
    finally show "pcut u' \<omega> (min r (\<theta> \<omega>)) = pstopped T \<theta> \<omega> r" .
  qed
  have sub: "subalgebra (?G u) (?G u')"
    unfolding subalgebra_def using spG sets_natural_filtration_mono[OF u'u] by simp
  show ?thesis
    by (rule measurable_from_subalg[OF sub]) (use ev same in simp)
qed

subsection \<open>Stopping a horizon-capped square-integrable martingale\<close>

text \<open>The engine behind \<open>QH\<close> and \<open>QHC\<close>, abstracted out of
  @{thm [source] exit_class_stopped_coord_martingale}: its proof uses
  the localisation time only through nonnegativity and the stopping
  property, so it generalises to any stopping time verbatim.  Doob's
  envelope \<^term>\<open>Dsup\<close> supplies both the dominating function
  \<open>optional_stopping\<close> needs and the square-integrability of the stopped
  process, which is what promotes the conclusion back to a
  \<^const>\<open>horizon_sq_int_martingale\<close>.\<close>

lemma horizon_sq_int_martingale_stopped:
  fixes Q :: "'a measure" and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and \<tau> :: "'a \<Rightarrow> real"
  assumes T0: "0 < T"
    and HZ: "horizon_sq_int_martingale Q F Z T"
    and cap: "\<And>s \<omega>. Z s \<omega> = Z (min s T) \<omega>"
    and contT: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> continuous_on {0..T} (\<lambda>s. Z s \<omega>)"
    and tnn: "\<And>\<omega>. 0 \<le> \<tau> \<omega>"
    and tstop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space Q. \<tau> \<omega> \<le> s} \<in> sets (F s)"
  shows "martingale Q F 0 (\<lambda>v \<omega>. Z (min v (\<tau> \<omega>)) \<omega>)"
    and "\<And>s. 0 \<le> s \<Longrightarrow> integrable Q (\<lambda>\<omega>. (Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2)"
proof -
  interpret HM: horizon_sq_int_martingale Q F Z T by (rule HZ)
  have T0': "0 \<le> T" using T0 by simp
  have mgZ: "martingale Q F 0 Z" by (rule HM.martingale_axioms)
  have adp: "adapted_process Q F 0 Z" by unfold_locales
  have cont0: "continuous_on {0..} (\<lambda>s. Z s \<omega>)" if w: "\<omega> \<in> space Q" for \<omega>
  proof -
    have m: "continuous_on {0..} (\<lambda>s :: real. min s T)"
      by (intro continuous_intros)
    have im: "(\<lambda>s :: real. min s T) ` {0..} \<subseteq> {0..T}" using T0' by auto
    have "continuous_on {0..} (\<lambda>s. Z (min s T) \<omega>)"
      by (rule continuous_on_compose2[OF contT[OF w] m im])
    then show ?thesis using cap by simp
  qed
  have contu: "continuous_on {0..u} (\<lambda>s. Z s \<omega>)"
    if w: "\<omega> \<in> space Q" for \<omega> u
    by (rule continuous_on_subset[OF cont0[OF w]]) auto
  have domT: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    by (rule HM.Dsup_dominates) (intro AE_I2 contu)
  have domA: "AE \<omega> in Q. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>" for u
    using domT
  proof (rule eventually_mono)
    fix \<omega> :: 'a
    assume h: "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> T \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    show "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>"
    proof (intro allI impI)
      fix s :: real assume s: "0 \<le> s"
      have "\<bar>Z (min s T) \<omega>\<bar> \<le> HM.Dsup \<omega>" using h s T0' by simp
      then show "\<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>" using cap[of s \<omega>] by simp
    qed
  qed
  have tnn': "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> 0 \<le> \<tau> \<omega>" by (rule tnn)
  have stad: "(\<lambda>\<omega>. Z (min v (\<tau> \<omega>)) \<omega>) \<in> borel_measurable (F v)"
    if v: "0 \<le> v" for v
    by (rule stopped_adapted_of_cont[OF adp tnn' tstop cont0 v])
  show mgs: "martingale Q F 0 (\<lambda>v \<omega>. Z (min v (\<tau> \<omega>)) \<omega>)"
  proof (rule optional_stopping[where D = "\<lambda>_. HM.Dsup"])
    show "martingale Q F 0 Z" by (rule mgZ)
    show "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> 0 \<le> \<tau> \<omega>" by (rule tnn')
    show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space Q. \<tau> \<omega> \<le> s} \<in> sets (F s)" by (rule tstop)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q. continuous_on {0..u} (\<lambda>s. Z s \<omega>)"
      by (intro AE_I2 contu)
    show "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in Q.
        \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> HM.Dsup \<omega>" by (rule domA)
    show "\<And>u. 0 < u \<Longrightarrow> integrable Q HM.Dsup" by (rule HM.Dsup_integrable)
    show "\<And>v. 0 \<le> v \<Longrightarrow> (\<lambda>\<omega>. Z (min v (\<tau> \<omega>)) \<omega>) \<in> borel_measurable (F v)"
      by (rule stad)
  qed
  show "integrable Q (\<lambda>\<omega>. (Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have m: "(\<lambda>\<omega>. Z (min s (\<tau> \<omega>)) \<omega>) \<in> borel_measurable Q"
      by (rule measurable_from_subalg[OF HM.subalgebras[OF s] stad[OF s]])
    then have m2: "(\<lambda>\<omega>. (Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2) \<in> borel_measurable Q" by simp
    have ae: "AE \<omega> in Q. norm ((Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2) \<le> norm ((HM.Dsup \<omega>)\<^sup>2)"
      using domA[of s]
    proof (rule eventually_mono)
      fix \<omega> :: 'a
      assume h: "\<forall>v. 0 \<le> v \<longrightarrow> v \<le> s \<longrightarrow> \<bar>Z v \<omega>\<bar> \<le> HM.Dsup \<omega>"
      have a: "0 \<le> min s (\<tau> \<omega>)" using s tnn[of \<omega>] by simp
      have b: "min s (\<tau> \<omega>) \<le> s" by simp
      have le: "\<bar>Z (min s (\<tau> \<omega>)) \<omega>\<bar> \<le> HM.Dsup \<omega>" using h a b by blast
      have "(Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2 = \<bar>Z (min s (\<tau> \<omega>)) \<omega>\<bar>\<^sup>2" by simp
      also have "\<dots> \<le> (HM.Dsup \<omega>)\<^sup>2" by (rule power_mono[OF le abs_ge_zero])
      finally show "norm ((Z (min s (\<tau> \<omega>)) \<omega>)\<^sup>2) \<le> norm ((HM.Dsup \<omega>)\<^sup>2)"
        by simp
    qed
    show ?thesis
      by (rule Bochner_Integration.integrable_bound
          [OF HM.Dsup_sq_integrable m2 ae])
  qed
qed

text \<open>\<open>martingale_cong_ge\<close> lives in
  @{theory Continuous_Time_Martingales.Martingale_Algebra},
  general at any \<open>t\<^sub>0\<close> and with the equation oriented \<open>X u = Y u\<close> rather than
  \<open>Y u = X u\<close>.\<close>

subsection \<open>\<open>QH\<close> and \<open>QHC\<close> for the stopped past law\<close>

text \<open>Both clauses by the same three steps: stop the class's horizon
  martingale at \<open>\<theta>\<close> (@{thm [source] horizon_sq_int_martingale_stopped}),
  push the result forward along \<^const>\<open>pstopped\<close>
  (@{thm [source] martingale_pair_law}, with
  @{thm [source] pstopped_eval_filtration} as its adaptedness input and
  \<open>P\<close>'s own filtration --- a stopped path carries no more information than
  the past, so unlike the delayed class there is no time change here), and
  carry the square-integrability across with
  @{thm [source] integrable_distr_eq}.\<close>

lemma pstopped_eval_min_T:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T0: "0 \<le> T" and u: "0 \<le> u"
  shows "pstopped T \<theta> \<omega> (min u T) = \<omega> (min (min u (\<theta> \<omega>)) T)"
proof -
  have m: "min u T \<in> {0..T}" using T0 u by simp
  have "pstopped T \<theta> \<omega> (min u T) = \<omega> (min (min u T) (\<theta> \<omega>))"
    by (rule pstopped_apply[OF m])
  moreover have "min (min u T) (\<theta> \<omega>) = min (min u (\<theta> \<omega>)) T" by simp
  ultimately show ?thesis by simp
qed

theorem pstopped_law_horizon_component:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "horizon_sq_int_martingale (pair_law_of T (pstopped T \<theta>) P)
      (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v))
      (\<lambda>u p'. fst (p' (min u T)) $ c) T"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c"
  have T0': "0 \<le> T" using T0 by simp
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0' thM th0 thT])
  have PQ: "prob_space ?Q" by (rule pstopped_law_prob[OF T0' PS setsP st thM])
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have nf: "?F v = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have spF: "space (?F v) = space P" for v
    unfolding natural_filtration_def by simp
  have tstop: "{\<omega> \<in> space P. \<theta> \<omega> \<le> s} \<in> sets (?F s)" if s: "0 \<le> s" for s
  proof -
    have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> s}
        \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) s)"
      by (rule path_stopping_time_event_filtration_all[OF T0' st thM s])
    then show ?thesis unfolding nf using sp by simp
  qed
  have HZ: "horizon_sq_int_martingale P ?F ?Z T"
    by (rule exit_class_horizon_component[OF T0 L0 P])
  have contT: "continuous_on {0..T} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space P" for \<omega>
  proof -
    have "continuous_on {0..} (\<lambda>s. ?Z s \<omega>)"
      by (rule exit_class_coord_paths_cont[OF T0' setsP w])
    then show ?thesis by (rule continuous_on_subset) auto
  qed
  have cap: "?Z s \<omega> = ?Z (min s T) \<omega>" for s and \<omega> :: "'n pairpath" by simp
  have mgs: "martingale P ?F 0 (\<lambda>v \<omega>. ?Z (min v (\<theta> \<omega>)) \<omega>)"
    by (rule horizon_sq_int_martingale_stopped(1)
        [OF T0 HZ cap contT th0 tstop])
  have sqs: "integrable P (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    by (rule horizon_sq_int_martingale_stopped(2)
        [OF T0 HZ cap contT th0 tstop s])

  \<comment> \<open>step two: push the stopped martingale forward\<close>
  have mgp: "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))"
  proof (rule martingale_cong_ge[OF mgs])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega>. ?Z (min u (\<theta> \<omega>)) \<omega>)
        = (\<lambda>\<omega> :: 'n pairpath. ?Z u (pstopped T \<theta> \<omega>))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "?Z (min u (\<theta> \<omega>)) \<omega> = ?Z u (pstopped T \<theta> \<omega>)"
        using pstopped_eval_min_T[OF T0' u, of \<theta> \<omega>] by simp
    qed
  qed
  have Zm: "?Z u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have a: "0 \<le> min u T" using u T0' by simp
    have b: "min u T \<le> u" by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
        \<in> borel_measurable borel"
    proof -
      have s: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis by (rule measurable_compose[OF s borel_measurable_nth])
    qed
    show ?thesis
      by (rule measurable_compose[OF path_eval_natural_filtration[OF a b] fcB])
  qed
  have mgQ: "martingale ?Q ?G 0 ?Z"
  proof (rule martingale_pair_law[where T = T and FF = ?F])
    show "prob_space P" by (rule PS)
    show "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B" by (rule m1)
    show "(\<lambda>\<omega>. pstopped T \<theta> \<omega> r) \<in> borel_measurable (?F u)"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pstopped_eval_filtration[OF T0' setsP st thM that])
    show "?Z u \<in> borel_measurable
        (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v) u)"
      if "0 \<le> u" for u by (rule Zm[OF that])
    show "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))" by (rule mgp)
  qed

  \<comment> \<open>step three: square integrability travels with the pushforward\<close>
  have sqQ: "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have zb: "(\<lambda>p' :: 'n pairpath. (?Z s p')\<^sup>2) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min s T)) \<in> borel_measurable ?B"
        by (rule pair_law_eval_measurable[OF refl])
      moreover have "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
          \<in> borel_measurable borel"
      proof -
        have s': "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
            \<in> borel_measurable borel"
          by (intro borel_measurable_continuous_onI continuous_intros)
        show ?thesis by (rule measurable_compose[OF s' borel_measurable_nth])
      qed
      ultimately have "(\<lambda>p' :: 'n pairpath. ?Z s p') \<in> borel_measurable ?B"
        by (rule measurable_compose)
      then show ?thesis by simp
    qed
    have "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)
        = integrable P (\<lambda>\<omega>. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)"
      unfolding pair_law_of_def by (rule integrable_distr_eq[OF m1 zb])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)
        = (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "(?Z s (pstopped T \<theta> \<omega>))\<^sup>2 = (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2"
        using pstopped_eval_min_T[OF T0' s, of \<theta> \<omega>] by simp
    qed
    ultimately show ?thesis using sqs[OF s] by simp
  qed
  show ?thesis
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mgQ T0 PQ sqQ)
qed

theorem pstopped_law_horizon_compensated:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L0: "0 \<le> L" and P: "P \<in> exit_class k L T x"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "horizon_sq_int_martingale (pair_law_of T (pstopped T \<theta>) P)
      (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v))
      (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?G = "natural_filtration ?Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  have T0': "0 \<le> T" using T0 by simp
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0' thM th0 thT])
  have PQ: "prob_space ?Q" by (rule pstopped_law_prob[OF T0' PS setsP st thM])
  have sp: "space P = space ?B" by (rule sets_eq_imp_space_eq[OF setsP])
  have nf: "?F v = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) v" for v
    by (rule natural_filtration_cong_space[OF sp])
  have tstop: "{\<omega> \<in> space P. \<theta> \<omega> \<le> s} \<in> sets (?F s)" if s: "0 \<le> s" for s
  proof -
    have "{\<omega> \<in> space ?B. \<theta> \<omega> \<le> s}
        \<in> sets (natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) s)"
      by (rule path_stopping_time_event_filtration_all[OF T0' st thM s])
    then show ?thesis unfolding nf using sp by simp
  qed
  have HZ: "horizon_sq_int_martingale P ?F ?Z T"
    by (rule exit_class_horizon_compensated[OF T0 L0 P])
  have contT: "continuous_on {0..T} (\<lambda>s. ?Z s \<omega>)" if w: "\<omega> \<in> space P" for \<omega>
  proof -
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using w sp by (simp add: space_borel_of)
    show ?thesis by (rule comp_entry_continuous[OF mw])
  qed
  have cap: "?Z s \<omega> = ?Z (min s T) \<omega>" for s and \<omega> :: "'n pairpath" by simp
  have mgs: "martingale P ?F 0 (\<lambda>v \<omega>. ?Z (min v (\<theta> \<omega>)) \<omega>)"
    by (rule horizon_sq_int_martingale_stopped(1)
        [OF T0 HZ cap contT th0 tstop])
  have sqs: "integrable P (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)" if s: "0 \<le> s" for s
    by (rule horizon_sq_int_martingale_stopped(2)
        [OF T0 HZ cap contT th0 tstop s])
  have entB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n).
      (outerp (fst z) - snd z) $ c $ d) \<in> borel_measurable borel"
  proof -
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
    show ?thesis by (rule measurable_compose[OF s n])
  qed
  have mgp: "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))"
  proof (rule martingale_cong_ge[OF mgs])
    fix u :: real assume u: "0 \<le> u"
    show "(\<lambda>\<omega>. ?Z (min u (\<theta> \<omega>)) \<omega>)
        = (\<lambda>\<omega> :: 'n pairpath. ?Z u (pstopped T \<theta> \<omega>))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "?Z (min u (\<theta> \<omega>)) \<omega> = ?Z u (pstopped T \<theta> \<omega>)"
        using pstopped_eval_min_T[OF T0' u, of \<theta> \<omega>] by simp
    qed
  qed
  have Zm: "?Z u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have a: "0 \<le> min u T" using u T0' by simp
    have b: "min u T \<le> u" by simp
    show ?thesis
      by (rule measurable_compose[OF path_eval_natural_filtration[OF a b] entB])
  qed
  have mgQ: "martingale ?Q ?G 0 ?Z"
  proof (rule martingale_pair_law[where T = T and FF = ?F])
    show "prob_space P" by (rule PS)
    show "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B" by (rule m1)
    show "(\<lambda>\<omega>. pstopped T \<theta> \<omega> r) \<in> borel_measurable (?F u)"
      if "0 \<le> r" "r \<le> u" for u r :: real
      by (rule pstopped_eval_filtration[OF T0' setsP st thM that])
    show "?Z u \<in> borel_measurable
        (natural_filtration (pair_law_of T (pstopped T \<theta>) P) 0 (\<lambda>v \<omega>. \<omega> v) u)"
      if "0 \<le> u" for u by (rule Zm[OF that])
    show "martingale P ?F 0 (\<lambda>u \<omega>. ?Z u (pstopped T \<theta> \<omega>))" by (rule mgp)
  qed
  have sqQ: "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)" if s: "0 \<le> s" for s
  proof -
    have zb: "(\<lambda>p' :: 'n pairpath. (?Z s p')\<^sup>2) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min s T)) \<in> borel_measurable ?B"
        by (rule pair_law_eval_measurable[OF refl])
      from measurable_compose[OF this entB]
      have "(\<lambda>p' :: 'n pairpath. ?Z s p') \<in> borel_measurable ?B" by simp
      then show ?thesis by simp
    qed
    have "integrable ?Q (\<lambda>p'. (?Z s p')\<^sup>2)
        = integrable P (\<lambda>\<omega>. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)"
      unfolding pair_law_of_def by (rule integrable_distr_eq[OF m1 zb])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. (?Z s (pstopped T \<theta> \<omega>))\<^sup>2)
        = (\<lambda>\<omega>. (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2)"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      show "(?Z s (pstopped T \<theta> \<omega>))\<^sup>2 = (?Z (min s (\<theta> \<omega>)) \<omega>)\<^sup>2"
        using pstopped_eval_min_T[OF T0' s, of \<theta> \<omega>] by simp
    qed
    ultimately show ?thesis using sqs[OF s] by simp
  qed
  show ?thesis
    by (intro horizon_sq_int_martingale.intro
        horizon_sq_int_martingale_axioms.intro mgQ T0 PQ sqQ)
qed

subsection \<open>Uniform first moments for the delayed class\<close>

text \<open>The six remaining side conditions of the additive glue are Fubini
  statements about \<^const>\<open>ksemi\<close>, needing beyond the per-\<open>p'\<close>
  integrability \<open>Kint\<close>/\<open>KintC\<close> an outer bound: a bound on the inner
  integral that does not depend on \<open>p'\<close>.  The class has one
  (@{thm [source] exit_class_norm_mean_le},
  @{thm [source] exit_class_comp_norm_mean_le}) --- depending only on
  \<open>CARD('n)\<close>, \<open>L\<close> and the horizon --- and it survives the delay, because
  the delayed law reads the base law at an earlier time and the bound is
  monotone in the horizon.  The same constant works for every freezing
  time \<open>s\<close>, which makes the outer integral finite.\<close>

lemma pdelclass_norm_mean_le:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes L0: "0 \<le> L" and s0: "0 \<le> s" and sT: "s \<le> T"
    and m: "\<nu> \<in> pdelclass k L T s" and u: "u \<in> {0..T}"
  shows "(\<integral>w. norm (fst (w u)) \<partial>\<nu>)
      \<le> 1 + real CARD('n) * (real CARD('n) * L * T)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nb: "(\<lambda>w :: 'n pairpath. norm (fst (w u))) \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). norm (fst z))
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have tmem: "max (u - s) 0 \<in> {0..T - s}" using u s0 sT by auto
  have "(\<integral>w. norm (fst (w u)) \<partial>\<nu>)
      = (\<integral>w'. norm (fst (pembed s T w' u)) \<partial>\<mu>)"
    unfolding nu by (rule integral_distr[OF pm nb])
  also have "\<dots> = (\<integral>w'. norm (fst (w' (max (u - s) 0))) \<partial>\<mu>)"
    by (rule Bochner_Integration.integral_cong[OF refl])
       (simp add: pembed_apply[OF u])
  also have "\<dots> \<le> 1 + real CARD('n) * (real CARD('n) * L * (T - s))"
    by (rule exit_class_norm_mean_le[OF Ts L0 mu tmem])
  also have "\<dots> \<le> 1 + real CARD('n) * (real CARD('n) * L * T)"
    using L0 s0 by (intro add_left_mono mult_left_mono mult_left_mono) auto
  finally show ?thesis .
qed

lemma pdelclass_comp_norm_mean_le:
  fixes \<nu> :: "('n::finite pairpath) measure"
  assumes L0: "0 \<le> L" and s0: "0 \<le> s" and sT: "s \<le> T"
    and m: "\<nu> \<in> pdelclass k L T s" and u: "u \<in> {0..T}"
  shows "(\<integral>w. norm (outerp (fst (w u)) - snd (w u)) \<partial>\<nu>)
      \<le> real CARD('n) * (real CARD('n) * L * T) + real CARD('n) * L * T"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  have T0: "0 \<le> T" using s0 sT by simp
  have Ts: "0 \<le> T - s" using sT by simp
  from m obtain \<mu> where mu: "\<mu> \<in> exit_class k L (T - s) (0::real^'n)"
    and nu: "\<nu> = distr \<mu> ?B (pembed s T)" unfolding pdelclass_def by blast
  have setsmu: "sets \<mu> = sets ?Bs" by (rule exit_class_sets[OF mu])
  have pm: "pembed s T \<in> \<mu> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsmu refl]
    by (rule pembed_measurable[OF s0 sT])
  have nb: "(\<lambda>w :: 'n pairpath. norm (outerp (fst (w u)) - snd (w u)))
      \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). norm (outerp (fst z) - snd z))
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have tmem: "max (u - s) 0 \<in> {0..T - s}" using u s0 sT by auto
  have "(\<integral>w. norm (outerp (fst (w u)) - snd (w u)) \<partial>\<nu>)
      = (\<integral>w'. norm (outerp (fst (pembed s T w' u))
            - snd (pembed s T w' u)) \<partial>\<mu>)"
    unfolding nu by (rule integral_distr[OF pm nb])
  also have "\<dots> = (\<integral>w'. norm (outerp (fst (w' (max (u - s) 0)))
        - snd (w' (max (u - s) 0))) \<partial>\<mu>)"
    by (rule Bochner_Integration.integral_cong[OF refl])
       (simp add: pembed_apply[OF u])
  also have "\<dots> \<le> real CARD('n) * (real CARD('n) * L * (T - s))
      + real CARD('n) * L * (T - s)"
    by (rule exit_class_comp_norm_mean_le[OF Ts L0 mu tmem])
  also have "\<dots> \<le> real CARD('n) * (real CARD('n) * L * T)
      + real CARD('n) * L * T"
    using L0 s0 by (intro add_mono mult_left_mono mult_left_mono) auto
  finally show ?thesis .
qed

section \<open>Fubini over the semidirect product: the glue's side conditions\<close>

text \<open>Three generic facts about \<^const>\<open>ksemi\<close>, all from
  @{thm [source] nn_integral_ksemi}: a function of the past alone is
  integrable as soon as it is integrable on the base; a function whose
  inner \<open>\<kappa>\<close>-integral is bounded uniformly in the past is integrable; and
  the inner integral is measurable in the past.  Together with the
  uniform first moments of the delayed class these discharge every side
  condition of the additive glue.\<close>

text \<open>\<open>integral_kernel_measurable\<close> and \<open>integrable_ksemi_of_past_bound\<close> (the
  workhorse: the inner bound may itself be a function of the past, as long
  as that function is integrable --- covering all three shapes the glue
  produces, a constant, \<open>norm (f \<omega>)\<close>, and \<open>norm (f \<omega>) * C\<close>) live in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

subsection \<open>\<open>RXint\<close> and \<open>RCint\<close>\<close>

lemma padd_eval_split:
  fixes p' w :: "'n::finite pairpath"
  assumes t: "t \<in> {0..T}"
  shows "fst (padd T p' w t) = fst (p' t) + fst (w t)"
    and "snd (padd T p' w t) = snd (p' t) + snd (w t)"
  by (simp_all add: padd_apply[OF t])

lemma aglue_law_X_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
  shows "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?S = "ksemi Q ?B \<kappa>"
  let ?t = "min u T"
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using padd_measurable_ksemi[OF T0 setsQ] measurable_cong_sets[OF setsS refl]
    by blast
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> ?t)) \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<omega> ?t) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      fst (padd T (fst p) (snd p) ?t)) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  interpret PQ': prob_space Q by (rule PQ)
  have hint: "integrable Q (\<lambda>p'. norm (fst (p' ?t)) + CX)"
    by (intro Bochner_Integration.integrable_add integrable_norm[OF QXint]
        PQ'.integrable_const)
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (fst (padd T (fst (p', w)) (snd (p', w)) ?t)))
        \<partial>(\<kappa> p')) \<le> ennreal (norm (fst (p' ?t)) + CX)"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have iN: "integrable (\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXint[OF sp]])
    have dom: "norm (fst (padd T p' w ?t)) \<le> norm (fst (p' ?t)) + norm (fst (w ?t))"
      for w :: "'n pairpath"
      unfolding padd_eval_split(1)[OF tm] by (rule norm_triangle_ineq)
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (fst (padd T p' w ?t)))"
    proof (rule Bochner_Integration.integrable_bound
        [OF Bochner_Integration.integrable_add[OF PK.integrable_const iN]])
      show "(\<lambda>w. norm (fst (padd T p' w ?t))) \<in> borel_measurable (\<kappa> p')"
      proof -
        have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
        have "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
          by (rule padd_measurable_left[OF T0])
             (use sp space_of_path_sets[OF setsQ] in simp)
        from measurable_compose[OF this hb]
        have mm: "(\<lambda>w :: 'n pairpath. fst (padd T p' w ?t)) \<in> borel_measurable ?B" .
        then have "(\<lambda>w :: 'n pairpath. fst (padd T p' w ?t))
            \<in> borel_measurable (\<kappa> p')"
          using measurable_cong_sets[OF sK refl] by blast
        then show ?thesis by measurable
      qed
      show "AE w in \<kappa> p'. norm (norm (fst (padd T p' w ?t)))
          \<le> norm (norm (fst (p' ?t)) + norm (fst (w ?t)))"
        using dom by (intro AE_I2) simp
    qed
    have "(\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))
        \<le> (\<integral>w. norm (fst (p' ?t)) + norm (fst (w ?t)) \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono
          [OF iP Bochner_Integration.integrable_add[OF PK.integrable_const iN]])
         (use dom in simp)
    also have "\<dots> = norm (fst (p' ?t)) + (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PK.integrable_const iN]
      by (simp add: PK.prob_space)
    also have "\<dots> \<le> norm (fst (p' ?t)) + CX" using KXbnd[OF sp] by simp
    finally have le: "(\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))
        \<le> norm (fst (p' ?t)) + CX" .
    have "(\<integral>\<^sup>+w. ennreal (norm (fst (padd T p' w ?t))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (fst (padd T p' w ?t)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (norm (fst (p' ?t)) + CX)"
      using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. fst (padd T (fst p) (snd p) ?t))"
    by (rule integrable_ksemi_of_past_bound[OF Kp ne gm hint]) (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> ?t))
      = integrable ?S (\<lambda>p. fst (padd T (fst p) (snd p) ?t))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

text \<open>\<open>RCint\<close>.  \<^const>\<open>outerp\<close> is quadratic, so the glued compensated entry
  is not the sum of the two factors': @{thm [source] outerp_add} produces
  two cross terms, whose norms @{thm [source] norm_outer_prod} evaluates
  exactly.  The inner bound has the third shape
  @{thm [source] integrable_ksemi_of_past_bound} was written for.\<close>

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

lemma aglue_law_comp_integrable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and u: "0 \<le> u"
    and QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and QCint: "integrable Q
      (\<lambda>p'. outerp (fst (p' (min u T))) - snd (p' (min u T)))"
    and KXint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    and KCint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. outerp (fst (w (min u T))) - snd (w (min u T)))"
    and KXbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. norm (fst (w (min u T))) \<partial>(\<kappa> p')) \<le> CX"
    and KCbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w.
      norm (outerp (fst (w (min u T))) - snd (w (min u T))) \<partial>(\<kappa> p')) \<le> CC"
  shows "integrable (aglue_law T \<kappa> Q)
      (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?S = "ksemi Q ?B \<kappa>"
  let ?t = "min u T"
  let ?C = "\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> ?t)) - snd (\<omega> ?t)"
  have tm: "?t \<in> {0..T}" using u T0 by simp
  have ne: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  interpret PQ': prob_space Q by (rule PQ)
  have setsS: "sets ?S = sets (Q \<Otimes>\<^sub>M ?B)" by (rule sets_ksemi[OF Kp ne])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ?S \<rightarrow>\<^sub>M ?B"
    using padd_measurable_ksemi[OF T0 setsQ] measurable_cong_sets[OF setsS refl]
    by blast
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have hb: "?C \<in> borel_measurable ?B"
  proof -
    have e: "(\<lambda>\<omega> :: 'n pairpath. \<omega> ?t) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis by (rule measurable_compose[OF e f])
  qed
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      ?C (padd T (fst p) (snd p))) \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pmP hb])
  have hint: "integrable Q
      (\<lambda>p'. norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
    by (intro Bochner_Integration.integrable_add integrable_norm[OF QCint]
        PQ'.integrable_const Bochner_Integration.integrable_mult_right
        integrable_mult_left integrable_norm[OF QXint])
  have bnd: "(\<integral>\<^sup>+w. ennreal (norm (?C (padd T (fst (p', w)) (snd (p', w)))))
        \<partial>(\<kappa> p'))
      \<le> ennreal (norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
    if sp: "p' \<in> space Q" for p'
  proof -
    interpret PK: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have iNC: "integrable (\<kappa> p') (\<lambda>w. norm (?C w))"
      by (rule integrable_norm[OF KCint[OF sp]])
    have iNX: "integrable (\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXint[OF sp]])
    have iB: "integrable (\<kappa> p') (\<lambda>w. norm (?C p') + norm (?C w)
        + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))))"
      by (intro Bochner_Integration.integrable_add PK.integrable_const iNC
          Bochner_Integration.integrable_mult_right integrable_mult_left iNX)
    have dom: "norm (?C (padd T p' w))
        \<le> norm (?C p') + norm (?C w) + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t)))"
      for w :: "'n pairpath" by (rule padd_comp_norm_le[OF tm])
    have mP: "(\<lambda>w :: 'n pairpath. norm (?C (padd T p' w)))
        \<in> borel_measurable (\<kappa> p')"
    proof -
      have "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
        by (rule padd_measurable_left[OF T0])
           (use sp space_of_path_sets[OF setsQ] in simp)
      from measurable_compose[OF this hb]
      have "(\<lambda>w :: 'n pairpath. ?C (padd T p' w)) \<in> borel_measurable ?B" .
      then have "(\<lambda>w :: 'n pairpath. ?C (padd T p' w))
          \<in> borel_measurable (\<kappa> p')"
        using measurable_cong_sets[OF sK refl] by blast
      then show ?thesis by measurable
    qed
    have iP: "integrable (\<kappa> p') (\<lambda>w. norm (?C (padd T p' w)))"
      by (rule Bochner_Integration.integrable_bound[OF iB mP])
         (use dom in \<open>intro AE_I2, simp\<close>)
    have "(\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))
        \<le> (\<integral>w. norm (?C p') + norm (?C w)
            + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))) \<partial>(\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono[OF iP iB]) (use dom in simp)
    also have "\<dots> = norm (?C p') + (\<integral>w. norm (?C w) \<partial>(\<kappa> p'))
        + 2 * (norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p')))"
      using iNC iNX PK.integrable_const
      by (simp add: PK.prob_space algebra_simps)
    also have "\<dots> \<le> norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX))"
    proof -
      have b1: "(\<integral>w. norm (?C w) \<partial>(\<kappa> p')) \<le> CC" by (rule KCbnd[OF sp])
      have b2: "norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(\<kappa> p'))
          \<le> norm (fst (p' ?t)) * CX"
        by (rule mult_left_mono[OF KXbnd[OF sp] norm_ge_zero])
      from b1 b2 show ?thesis by linarith
    qed
    finally have le: "(\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))
        \<le> norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX))" .
    have "(\<integral>\<^sup>+w. ennreal (norm (?C (padd T p' w))) \<partial>(\<kappa> p'))
        = ennreal (\<integral>w. norm (?C (padd T p' w)) \<partial>(\<kappa> p'))"
      by (rule nn_integral_eq_integral[OF iP]) simp
    also have "\<dots> \<le> ennreal (norm (?C p') + (CC + 2 * (norm (fst (p' ?t)) * CX)))"
      using le by (rule ennreal_leI)
    finally show ?thesis by simp
  qed
  have gi: "integrable ?S (\<lambda>p. ?C (padd T (fst p) (snd p)))"
    by (rule integrable_ksemi_of_past_bound[OF Kp ne gm hint]) (use bnd in simp)
  have "integrable (aglue_law T \<kappa> Q) ?C
      = integrable ?S (\<lambda>p. ?C (padd T (fst p) (snd p)))"
    unfolding aglue_law_def by (rule integrable_distr_eq[OF pm hb])
  then show ?thesis using gi by simp
qed

subsection \<open>\<open>msecX\<close> and \<open>msecC\<close>\<close>

text \<open>One generic lemma covers both, and \<open>gintX\<close>/\<open>gintC\<close> too: the
  conditioning factor enters only through being measurable and bounded by
  \<open>1\<close> --- an \<^const>\<open>indicator\<close> for \<open>msec\<close>, an indicator composed with
  \<^const>\<open>pcut\<close> for \<open>gint\<close>.\<close>

lemma aglue_section_measurable:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and hb: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and cb: "cc \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
  shows "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have pmP: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have gm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      cc (padd T (fst p) (snd p)) * h (padd T (fst p) (snd p)))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    using measurable_compose[OF pmP cb] measurable_compose[OF pmP hb] by simp
  have gi: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
    if sp: "p' \<in> space Q" for p'
  proof (rule Bochner_Integration.integrable_bound[OF Kint[OF sp]])
    have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pl: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
      by (rule padd_measurable_left[OF T0])
         (use sp space_of_path_sets[OF setsQ] in simp)
    have "(\<lambda>w :: 'n pairpath. cc (padd T p' w) * h (padd T p' w))
        \<in> borel_measurable ?B"
      using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
    then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
        \<in> borel_measurable (\<kappa> p')"
      using measurable_cong_sets[OF sK refl] by blast
  next
    show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
        \<le> norm (h (padd T p' w))"
    proof (intro AE_I2)
      fix w :: "'n pairpath"
      have "norm (cc (padd T p' w) * h (padd T p' w))
          = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>" by (simp add: abs_mult)
      also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
        by (rule mult_right_mono[OF c1]) simp
      finally show "norm (cc (padd T p' w) * h (padd T p' w))
          \<le> norm (h (padd T p' w))" by simp
    qed
  qed
  show ?thesis
    by (rule integral_kernel_measurable
        [where g = "\<lambda>p' w. cc (padd T p' w) * h (padd T p' w)", OF Kp gm gi])
qed

corollary aglue_msec_X:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and A: "A \<in> sets (aglue_law T \<kappa> Q)"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
  shows "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
      * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have AB: "A \<in> sets ?B" using A by (simp add: sets_aglue_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis
      by (rule measurable_compose
          [OF measurable_compose[OF ev f] borel_measurable_nth])
  qed
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

text \<open>\<open>gintX\<close>/\<open>gintC\<close>: the same section integral, now integrable in the
  past.  Bounded by \<open>1\<close>, the conditioning factor cannot enlarge the inner
  integral, so the past bound that already served \<open>RXint\<close>/\<open>RCint\<close> serves
  here too.\<close>

lemma aglue_section_int_at:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and hb: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and cb: "cc \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and sp: "p' \<in> space Q"
  shows "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
proof (rule Bochner_Integration.integrable_bound[OF Kint])
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have sK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
  have pl: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule padd_measurable_left[OF T0])
       (use sp space_of_path_sets[OF setsQ] in simp)
  have "(\<lambda>w :: 'n pairpath. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable ?B"
    using measurable_compose[OF pl cb] measurable_compose[OF pl hb] by simp
  then show "(\<lambda>w. cc (padd T p' w) * h (padd T p' w))
      \<in> borel_measurable (\<kappa> p')"
    using measurable_cong_sets[OF sK refl] by blast
next
  show "AE w in \<kappa> p'. norm (cc (padd T p' w) * h (padd T p' w))
      \<le> norm (h (padd T p' w))"
  proof (intro AE_I2)
    fix w :: "'n pairpath"
    have "norm (cc (padd T p' w) * h (padd T p' w))
        = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>" by (simp add: abs_mult)
    also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
      by (rule mult_right_mono[OF c1]) simp
    finally show "norm (cc (padd T p' w) * h (padd T p' w))
        \<le> norm (h (padd T p' w))" by simp
  qed
qed

lemma aglue_section_integrable:
  fixes Q :: "('n::finite pairpath) measure"
    and h cc HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and hb: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and cb: "cc \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and c1: "\<And>\<omega>. \<bar>cc \<omega>\<bar> \<le> 1"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. \<bar>h (padd T p' w)\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))"
proof -
  have m: "(\<lambda>p'. \<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF HBi m])
    show "AE p' in Q. norm (\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
        \<le> norm (HB p')"
    proof (rule eventually_mono[OF AE_space])
      fix p' :: "'n pairpath" assume sp: "p' \<in> space Q"
      have iH: "integrable (\<kappa> p') (\<lambda>w. h (padd T p' w))" by (rule Kint[OF sp])
      have iA: "integrable (\<kappa> p') (\<lambda>w. \<bar>h (padd T p' w)\<bar>)"
        using iH by simp
      have iCH: "integrable (\<kappa> p') (\<lambda>w. cc (padd T p' w) * h (padd T p' w))"
        by (rule aglue_section_int_at[OF T0 setsQ Kp hb cb c1 iH sp])
      have "\<bar>\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p')\<bar>
          \<le> (\<integral>w. \<bar>cc (padd T p' w) * h (padd T p' w)\<bar> \<partial>(\<kappa> p'))"
        by (rule integral_abs_bound)
      also have "\<dots> \<le> (\<integral>w. \<bar>h (padd T p' w)\<bar> \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_mono[OF _ iA])
        show "integrable (\<kappa> p') (\<lambda>w. \<bar>cc (padd T p' w) * h (padd T p' w)\<bar>)"
          using iCH by simp
        show "\<bar>cc (padd T p' w) * h (padd T p' w)\<bar>
            \<le> \<bar>h (padd T p' w)\<bar>" for w :: "'n pairpath"
        proof -
          have "\<bar>cc (padd T p' w) * h (padd T p' w)\<bar>
              = \<bar>cc (padd T p' w)\<bar> * \<bar>h (padd T p' w)\<bar>"
            by (simp add: abs_mult)
          also have "\<dots> \<le> 1 * \<bar>h (padd T p' w)\<bar>"
            by (rule mult_right_mono[OF c1]) simp
          finally show ?thesis by simp
        qed
      qed
      also have "\<dots> \<le> HB p'" by (rule Kbnd[OF sp])
      finally show "norm (\<integral>w. cc (padd T p' w) * h (padd T p' w) \<partial>(\<kappa> p'))
          \<le> norm (HB p')" by simp
    qed
  qed
qed

corollary aglue_msec_C:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and A: "A \<in> sets (aglue_law T \<kappa> Q)"
    and Kint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
  shows "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
      * ((outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
      \<in> borel_measurable Q"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have AB: "A \<in> sets ?B" using A by (simp add: sets_aglue_law)
  have cb: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> :: real) \<in> borel_measurable ?B"
    using AB by (rule borel_measurable_indicator)
  have c1: "\<bar>(indicator A \<omega> :: real)\<bar> \<le> 1" for \<omega> :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (rule linear_continuous_on[OF bl])
    show ?thesis
      by (rule measurable_compose[OF measurable_compose[OF ev s] n])
  qed
  show ?thesis
    by (rule aglue_section_measurable[OF T0 setsQ Kp hb cb c1 Kint])
qed

subsection \<open>\<open>gintX\<close> and \<open>gintC\<close>\<close>

corollary aglue_gint_X:
  fixes Q :: "('n::finite pairpath) measure" and HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and BB: "BB \<in> sets (borel_of (mtopology_of
        (path_metric i :: ('n pairpath) metric)))"
    and Kint: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> (\<integral>w. \<bar>fst (padd T p' w (min u T)) $ e\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
      * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p'))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bi = "borel_of (mtopology_of (path_metric i :: ('n pairpath) metric))"
  have cb: "(\<lambda>x :: 'n pairpath. indicator BB (pcut i x) :: real)
      \<in> borel_measurable ?B"
  proof -
    have pc: "pcut i \<in> ?B \<rightarrow>\<^sub>M ?Bi" by (rule pcut_measurable[OF i0 iT refl])
    have ib: "(\<lambda>x :: 'n pairpath. indicator BB x :: real)
        \<in> borel_measurable ?Bi" using BB by (rule borel_measurable_indicator)
    show ?thesis by (rule measurable_compose[OF pc ib])
  qed
  have c1: "\<bar>(indicator BB (pcut i x) :: real)\<bar> \<le> 1" for x :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ e) \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have f: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
        \<in> borel_measurable borel"
      by (intro borel_measurable_continuous_onI continuous_intros)
    show ?thesis
      by (rule measurable_compose
          [OF measurable_compose[OF ev f] borel_measurable_nth])
  qed
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed

corollary aglue_gint_C:
  fixes Q :: "('n::finite pairpath) measure" and HB :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and BB: "BB \<in> sets (borel_of (mtopology_of
        (path_metric i :: ('n pairpath) metric)))"
    and Kint: "\<And>p'. p' \<in> space Q \<Longrightarrow> integrable (\<kappa> p')
      (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
    and HBi: "integrable Q HB"
    and Kbnd: "\<And>p'. p' \<in> space Q \<Longrightarrow> (\<integral>w.
        \<bar>(outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d\<bar> \<partial>(\<kappa> p')) \<le> HB p'"
  shows "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
      * ((outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bi = "borel_of (mtopology_of (path_metric i :: ('n pairpath) metric))"
  have cb: "(\<lambda>x :: 'n pairpath. indicator BB (pcut i x) :: real)
      \<in> borel_measurable ?B"
  proof -
    have pc: "pcut i \<in> ?B \<rightarrow>\<^sub>M ?Bi" by (rule pcut_measurable[OF i0 iT refl])
    have ib: "(\<lambda>x :: 'n pairpath. indicator BB x :: real)
        \<in> borel_measurable ?Bi" using BB by (rule borel_measurable_indicator)
    show ?thesis by (rule measurable_compose[OF pc ib])
  qed
  have c1: "\<bar>(indicator BB (pcut i x) :: real)\<bar> \<le> 1" for x :: "'n pairpath"
    by (simp add: indicator_def)
  have hb: "(\<lambda>\<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
      \<in> borel_measurable ?B"
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
        \<in> borel_measurable borel"
      unfolding outerp_def
      by (intro borel_measurable_continuous_onI continuous_intros)
    have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
      by (rule bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_vec_nth])
    have n: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI)
         (rule linear_continuous_on[OF bl])
    show ?thesis
      by (rule measurable_compose[OF measurable_compose[OF ev s] n])
  qed
  show ?thesis
    by (rule aglue_section_integrable
        [OF T0 setsQ Kp hb cb c1 Kint HBi Kbnd])
qed


(*<*)
end
(*>*)
