section \<open>The additive glue and its clauses\<close>

(*<*)
theory Dynamic_Programming_Additive_Glue
  imports Dynamic_Programming_Stopping_Clauses
begin

(*>*)

section \<open>The additive glue\<close>

text \<open>Reassembly of the split is addition (@{thm [source] pstopped_add_pafter}),
  so the kernel is pushed through the glue map \<^term>\<open>padd T p' w\<close>, not
  \<^const>\<open>pglue\<close>.  It is defined on the same pair of \<open>T\<close>-path spaces the
  r.c.d. lives on, and needs no \<open>\<theta>\<close> --- the reason the additive split was
  chosen over freeze-and-rebase.

  The facts below form the foundation layer: the glue lands in the path
  space, is measurable as a map out of the product, inverts the split, and
  --- given that the continuation stands still until \<open>\<theta>\<close> --- is inverted by
  the split, so no information is lost in either direction.\<close>

definition padd :: "real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath \<Rightarrow> 'n pairpath"
  where "padd T p' w = restrict (\<lambda>t. p' t + w t) {0..T}"

lemma padd_apply: "t \<in> {0..T} \<Longrightarrow> padd T p' w t = p' t + w t"
  by (simp add: padd_def)

lemma padd_outside: "t \<notin> {0..T} \<Longrightarrow> padd T p' w t = undefined"
  unfolding padd_def restrict_def by (rule if_not_P)

lemma padd_mspace:
  fixes p' w :: "'n::finite pairpath"
  assumes p: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and w: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "padd T p' w \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have "continuous_on {0..T} (\<lambda>t. p' t + w t)"
    using mspace_path_metricD[OF p] mspace_path_metricD[OF w]
    by (intro continuous_intros)
  then show ?thesis unfolding padd_def by (rule mspace_path_metricI)
qed

text \<open>The glue with the past fixed: the form the four-cell argument needs,
  since there the continuation is only frozen almost surely, so the
  integrand identities transport via
  @{thm [source] Bochner_Integration.integral_cong_AE} rather than
  pointwise, which needs both sides measurable in \<open>w\<close> alone.\<close>

lemma padd_measurable_left:
  fixes p' :: "'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and p: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "(\<lambda>w. padd T p' w)
      \<in> borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have into: "padd T p' w \<in> mspace (path_metric T :: ('n pairpath) metric)"
    if "w \<in> space ?B" for w
    using that p by (auto simp: space_borel_of intro: padd_mspace)
  have ev: "(\<lambda>w :: 'n pairpath. padd T p' w t) \<in> borel_measurable ?B" for t
  proof (cases "t \<in> {0..T}")
    case True
    have "(\<lambda>w :: 'n pairpath. p' t + w t) \<in> borel_measurable ?B"
      by (intro borel_measurable_add borel_measurable_const
          pair_law_eval_measurable[OF refl])
    then show ?thesis by (simp add: padd_apply[OF True])
  next
    case False
    have "(\<lambda>w :: 'n pairpath. padd T p' w t) = (\<lambda>w. undefined)"
      by (rule ext) (rule padd_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>w. mdist (path_metric T :: ('n pairpath) metric)
        (padd T p' w) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

lemma padd_measurable:
  fixes T :: real
  assumes T0: "0 \<le> T"
  shows "(\<lambda>p. padd T (fst p) (snd p))
      \<in> borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
        \<Otimes>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?M = "?B \<Otimes>\<^sub>M ?B"
  let ?f = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p)"
  have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have into: "?f p \<in> mspace (path_metric T :: ('n pairpath) metric)"
    if p: "p \<in> space ?M" for p
  proof -
    have "fst p \<in> space ?B" and "snd p \<in> space ?B"
      using p by (auto simp: space_pair_measure)
    then show ?thesis using spB by (auto intro: padd_mspace)
  qed
  have ev: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?f p t) \<in> borel_measurable ?M"
    for t
  proof (cases "t \<in> {0..T}")
    case True
    have e1: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). fst p t) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_fst
            pair_law_eval_measurable[OF refl]])
    have e2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). snd p t) \<in> borel_measurable ?M"
      by (rule measurable_compose[OF measurable_snd
            pair_law_eval_measurable[OF refl]])
    have "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). fst p t + snd p t)
        \<in> borel_measurable ?M"
      using e1 e2 by simp
    then show ?thesis by (simp add: padd_apply[OF True])
  next
    case False
    have "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?f p t)
        = (\<lambda>p. undefined)"
      by (rule ext) (rule padd_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>p. mdist (path_metric T :: ('n pairpath) metric) (?f p) a)
        \<in> borel_measurable ?M"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

text \<open>The glue inverts the split.  There is no membership hypothesis on
  \<open>\<omega>\<close> beyond being a path: @{thm [source] pstopped_add_pafter} is
  unconditional and \<^const>\<open>padd\<close> restricts to \<open>{0..T}\<close>, where a member of
  the path space already lives.\<close>

text \<open>The split inverts the glue, provided the continuation stands still up
  to \<open>\<theta>\<close> --- which is exactly clause (ii) of the kernel's membership in the
  class.  The stopping time reads only the stopped factor, because on
  \<open>[0, \<theta> p']\<close> the glue agrees with it.\<close>

lemma padd_fst_continuous:
  fixes p' w :: "'n::finite pairpath"
  assumes cp: "continuous_on {0..T} (\<lambda>t. fst (p' t))"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (w t))"
  shows "continuous_on {0..T} (\<lambda>t. fst (padd T p' w t))"
proof (rule continuous_on_eq[OF continuous_on_add[OF cp cw]])
  fix t :: real assume t: "t \<in> {0..T}"
  show "fst (p' t) + fst (w t) = fst (padd T p' w t)"
    by (simp add: padd_apply[OF t])
qed

lemma padd_stopping_time:
  fixes p' w :: "'n::finite pairpath"
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
  fixes p' w :: "'n::finite pairpath"
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
  fixes p' w :: "'n::finite pairpath"
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
  \<^const>\<open>kglue_law'\<close>, and the only structural difference is that
  \<^const>\<open>padd\<close> replaces \<^const>\<open>pglue\<close>.\<close>

definition aglue_law :: "real \<Rightarrow> ('n::finite pairpath \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "aglue_law T \<kappa> Q = distr
      (ksemi Q (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))) \<kappa>)
      (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (\<lambda>p. padd T (fst p) (snd p))"

lemma sets_aglue_law:
  "sets (aglue_law T \<kappa> Q)
    = sets (borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric)))"
  unfolding aglue_law_def by (rule sets_distr)

lemma padd_measurable_ksemi:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))
      \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have s: "sets (Q \<Otimes>\<^sub>M ?B) = sets (?B \<Otimes>\<^sub>M ?B)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  show ?thesis
    unfolding measurable_cong_sets[OF s refl] by (rule padd_measurable[OF T0])
qed

lemma prob_space_aglue_law:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "prob_space (aglue_law T \<kappa> Q)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have neQ: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets (ksemi Q ?B \<kappa>) = sets (Q \<Otimes>\<^sub>M ?B)"
    by (rule sets_ksemi[OF Kp neQ])
  have pm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p))
      \<in> ksemi Q ?B \<kappa> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsS refl]
    by (rule padd_measurable_ksemi[OF T0 setsQ])
  show ?thesis
    unfolding aglue_law_def
    by (rule prob_space.prob_space_distr[OF prob_space_ksemi[OF PQ Kp] pm])
qed

text \<open>The transfer lemma: an almost-sure property of the glued law is an
  almost-sure property of the past, then of the continuation.  This is the
  analogue of @{thm [source] AE_kglue_law'}, and as there the base measure
  is kept a free variable.\<close>

lemma AE_aglue_law:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Phi: "{\<omega> \<in> space (borel_of (mtopology_of
            (path_metric T :: ('n pairpath) metric))). \<Phi> \<omega>}
        \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
  shows "(AE \<omega> in aglue_law T \<kappa> Q. \<Phi> \<omega>)
      \<longleftrightarrow> (AE p' in Q. AE w in \<kappa> p'. \<Phi> (padd T p' w))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p)"
  have neQ: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets (ksemi Q ?B \<kappa>) = sets (Q \<Otimes>\<^sub>M ?B)"
    by (rule sets_ksemi[OF Kp neQ])
  have pm2: "?g \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have pm: "?g \<in> ksemi Q ?B \<kappa> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsS refl] by (rule pm2)
  have meas: "{p \<in> space (Q \<Otimes>\<^sub>M ?B). \<Phi> (?g p)} \<in> sets (Q \<Otimes>\<^sub>M ?B)"
  proof -
    have "{p \<in> space (Q \<Otimes>\<^sub>M ?B). \<Phi> (?g p)}
        = ?g -` {\<omega> \<in> space ?B. \<Phi> \<omega>} \<inter> space (Q \<Otimes>\<^sub>M ?B)"
      using measurable_space[OF pm2] by auto
    then show ?thesis using measurable_sets[OF pm2 Phi] by simp
  qed
  have "(AE \<omega> in aglue_law T \<kappa> Q. \<Phi> \<omega>) \<longleftrightarrow> (AE p in ksemi Q ?B \<kappa>. \<Phi> (?g p))"
    unfolding aglue_law_def by (rule AE_distr_iff[OF pm Phi])
  also have "\<dots> \<longleftrightarrow> (AE p' in Q. AE w in \<kappa> p'. \<Phi> (padd T p' w))"
    unfolding AE_ksemi[OF Kp meas] by simp
  finally show ?thesis .
qed

text \<open>Clause (ii) for the glue: the past starts at \<open>x\<close> and the continuation
  at \<open>0\<close>, and \<^const>\<open>padd\<close> adds them.\<close>

lemma aglue_law_start:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q0: "AE p' in Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    and K0: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'. w 0 = 0"
  shows "AE \<omega> in aglue_law T \<kappa> Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have ev0: "(\<lambda>\<omega> :: 'n pairpath. \<omega> 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have Phi: "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0} \<in> sets ?B"
  proof -
    have "{\<omega> \<in> space ?B. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0}
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> 0) -` {(x, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis
      using measurable_sets[OF ev0 borel_closed[OF closed_singleton]] by simp
  qed
  have z: "(0 :: real) \<in> {0..T}" using T0 by simp
  have "AE p' in Q. AE w in \<kappa> p'.
      fst (padd T p' w 0) = x \<and> snd (padd T p' w 0) = 0"
    using Q0 AE_space
  proof eventually_elim
    case (elim p')
    then have q: "fst (p' 0) = x \<and> snd (p' 0) = 0" and sp: "p' \<in> space Q"
      by blast+
    show ?case using K0[OF sp]
    proof eventually_elim
      case (elim w)
      have "padd T p' w 0 = p' 0 + w 0" by (rule padd_apply[OF z])
      then show ?case using q elim by simp
    qed
  qed
  then show ?thesis
    unfolding AE_aglue_law[OF T0 PQ setsQ Kp Phi] .
qed

text \<open>Clause (iii) for the glue, pathwise.  Exactly the three-case argument
  of the deterministic pasting: below \<open>r\<close> only the past moves, above \<open>r\<close>
  only the continuation, and a straddling pair is a convex combination of
  the two difference quotients --- which is why \<^const>\<open>sconstraint\<close> had to
  be convex (@{thm [source] sconstraint_convex}) in the first place.\<close>

lemma padd_diffquot:
  fixes p' w :: "'n::finite pairpath"
  assumes T0: "0 \<le> T" and r0: "0 \<le> r" and rT: "r \<le> T"
    and idem: "\<And>u. u \<in> {0..T} \<Longrightarrow> p' u = p' (min u r)"
    and w0: "\<And>u. u \<in> {0..T} \<Longrightarrow> u \<le> r \<Longrightarrow> w u = 0"
    and A: "\<And>a b. 0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> b \<le> r
      \<Longrightarrow> (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
    and B: "\<And>a b. r \<le> a \<Longrightarrow> a < b \<Longrightarrow> b \<le> T
      \<Longrightarrow> (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
    and s: "0 \<le> s" and stlt: "s < t" and tT: "t \<le> T"
  shows "(1 / (t - s)) *\<^sub>R (snd (padd T p' w t) - snd (padd T p' w s))
      \<in> sconstraint k L"
proof -
  have sT: "s \<in> {0..T}" using s stlt tT by simp
  have tI: "t \<in> {0..T}" using s stlt tT by simp
  have split: "snd (padd T p' w t) - snd (padd T p' w s)
      = (snd (p' t) - snd (p' s)) + (snd (w t) - snd (w s))"
    unfolding padd_apply[OF sT] padd_apply[OF tI] by simp
  consider (early) "t \<le> r" | (late) "r \<le> s" | (mid) "s < r" "r < t"
    using stlt by fastforce
  then show ?thesis
  proof cases
    case early
    have "w t = 0" by (rule w0[OF tI early])
    moreover have "w s = 0"
      by (rule w0[OF sT]) (use stlt early in simp)
    ultimately show ?thesis
      unfolding split using A[OF s stlt early] by simp
  next
    case late
    have "p' t = p' r"
      using idem[OF tI] late stlt by simp
    moreover have "p' s = p' r" using idem[OF sT] late by simp
    ultimately show ?thesis
      unfolding split using B[OF late stlt tT] by simp
  next
    case mid
    let ?a = "(1 / (r - s)) *\<^sub>R (snd (p' r) - snd (p' s))"
    let ?b = "(1 / (t - r)) *\<^sub>R (snd (w t) - snd (w r))"
    have rI: "r \<in> {0..T}" using r0 rT by simp
    have aA: "?a \<in> sconstraint k L" by (rule A[OF s mid(1) order_refl])
    have bB: "?b \<in> sconstraint k L" by (rule B[OF order_refl mid(2) tT])
    have pos: "0 < r - s" "0 < t - r" "0 < t - s" using mid stlt by auto
    have sum1: "(r - s) / (t - s) + (t - r) / (t - s) = 1"
      by (subst add_divide_distrib[symmetric]) (use pos(3) in simp)
    have cc: "((r - s) / (t - s)) *\<^sub>R ?a + ((t - r) / (t - s)) *\<^sub>R ?b
        \<in> sconstraint k L"
      using pos by (intro convexD[OF sconstraint_convex aA bB] sum1) auto
    have e1: "((r - s) / (t - s)) *\<^sub>R ?a
        = (1 / (t - s)) *\<^sub>R (snd (p' r) - snd (p' s))"
      using pos by simp
    have e2: "((t - r) / (t - s)) *\<^sub>R ?b
        = (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w r))"
      using pos by simp
    have pt: "p' t = p' r" using idem[OF tI] mid(2) by simp
    have ws: "w s = 0" by (rule w0[OF sT]) (use mid(1) in simp)
    have wr: "w r = 0" by (rule w0[OF rI]) simp
    have "snd (padd T p' w t) - snd (padd T p' w s)
        = (snd (p' r) - snd (p' s)) + (snd (w t) - snd (w r))"
      unfolding split pt using ws wr by simp
    then show ?thesis
      using cc unfolding e1 e2 by (simp add: scaleR_right_distrib)
  qed
qed

text \<open>Clause (iii) for the glued law.  @{thm [source] exit_class_diffquot_of_pairs}
  reduces it to one pair of deterministic times, where the predicate is a
  closed set (@{thm [source] closedin_diffquot_constraint}) and so passes
  through @{thm [source] AE_aglue_law}; the pathwise content is then
  @{thm [source] padd_diffquot}.\<close>

lemma aglue_law_diffquot:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and Qcov: "AE p' in Q. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> \<theta> p'
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
    and K0: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kcov: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'. \<forall>a b. \<theta> p' \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
  shows "AE \<omega> in aglue_law T \<kappa> Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T
      \<longrightarrow> (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof (rule exit_class_diffquot_of_pairs[OF sets_aglue_law])
  fix p q :: real
  assume pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q"
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have spB: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have mset: "{\<omega> \<in> space ?B.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L} \<in> sets ?B"
    unfolding spB
    by (rule borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]])
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  show "AE \<omega> in aglue_law T \<kappa> Q.
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    unfolding AE_aglue_law[OF T0 PQ setsQ Kp mset]
    using Qst Qcov AE_space
  proof eventually_elim
    case (elim p')
    then have idem': "pstopped T \<theta> p' = p'"
      and cov: "\<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> \<theta> p'
          \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
      and sp: "p' \<in> space Q" by blast+
    have idem: "p' u = p' (min u (\<theta> p'))" if u: "u \<in> {0..T}" for u
    proof -
      have "p' u = pstopped T \<theta> p' u" unfolding idem' ..
      also have "\<dots> = p' (min u (\<theta> p'))" by (rule pstopped_apply[OF u])
      finally show ?thesis .
    qed
    show ?case using K0[OF sp] Kcov[OF sp]
    proof eventually_elim
      case (elim w)
      then have w0: "\<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
        and wcov: "\<forall>a b. \<theta> p' \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
            \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
        by blast+
      show ?case
      proof (rule padd_diffquot[where r = "\<theta> p'"])
        show "0 \<le> T" by (rule T0)
        show "0 \<le> \<theta> p'" by (rule th0)
        show "\<theta> p' \<le> T" by (rule thT)
        show "p' u = p' (min u (\<theta> p'))" if "u \<in> {0..T}" for u
          by (rule idem[OF that])
        show "w u = 0" if "u \<in> {0..T}" "u \<le> \<theta> p'" for u
          using w0 that by blast
        show "(1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
          if "0 \<le> a" "a < b" "b \<le> \<theta> p'" for a b
          using cov that by blast
        show "(1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
          if "\<theta> p' \<le> a" "a < b" "b \<le> T" for a b
          using wcov that by blast
        show "0 \<le> p" using pq(1) by simp
        show "p < q" by (rule pq(3))
        show "q \<le> T" using pq(2) by simp
      qed    qed
  qed
qed

section \<open>Clause (iv) for the glue: the two collapses\<close>

text \<open>The martingale clauses do not need the weak-closedness detour that the
  deterministic pasting theorem takes, because the additive split is
  invertible (@{thm [source] pstopped_padd}, @{thm [source] pafter_padd})
  and the conditioning set collapses on each half of \<open>{\<theta> \<le> i}\<close>.

  \<^item> On \<open>{\<theta> > i}\<close> the continuation has not started, so the glued path agrees
    with the past on \<open>[0,i]\<close> and an \<open>\<F>\<^sub>i\<close>-set of the glue is a set of the past
    alone --- it does not constrain \<open>w\<close> at all.
  \<^item> On \<open>{\<theta> \<le> i}\<close> the past has stopped, so the increment of the glue is the
    increment of the continuation, and for a fixed past the set's \<open>w\<close>-section
    is an \<open>\<F>\<^sub>i\<close>-set of the continuation.

  Both statements are about \<^const>\<open>pcut\<close>, since
  @{thm [source] sets_natural_filtration_eq_pcut_vimage} presents an
  \<open>\<F>\<^sub>i\<close>-set as a \<^const>\<open>pcut\<close>-preimage.  These are the two pathwise facts.\<close>

lemma pcut_padd_before:
  fixes p' w :: "'n::finite pairpath"
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
    have out: "pcut i v s = undefined" for v :: "'n pairpath"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    show ?thesis unfolding out ..
  qed
qed

lemma pcut_padd_section:
  fixes p' w :: "'n::finite pairpath"
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
    have out1: "pcut i v s = undefined" for v :: "'n pairpath"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    have out2: "padd i a b s = undefined" for a b :: "'n pairpath"
      unfolding padd_def restrict_def by (rule if_not_P[OF False])
    show ?thesis unfolding out1 out2 ..
  qed
qed

text \<open>Assembled: clauses (i)--(iii) are discharged from the lemmas above;
  the two martingale clauses are the remaining input, resting on the two
  collapses above.\<close>

theorem exit_class_aglue_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and Q0: "AE p' in Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and Qcov: "AE p' in Q. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> \<theta> p'
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
    and K0: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'. w 0 = 0"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kcov: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'. \<forall>a b. \<theta> p' \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
    and mgX: "martingale (aglue_law T \<kappa> Q)
        (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
    and mgC: "martingale (aglue_law T \<kappa> Q)
        (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
  shows "aglue_law T \<kappa> Q \<in> exit_class k L T x"
  unfolding exit_class_def
proof (intro CollectI conjI)
  show "prob_space (aglue_law T \<kappa> Q)"
    by (rule prob_space_aglue_law[OF T0 PQ setsQ Kp])
  show "sets (aglue_law T \<kappa> Q) = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule sets_aglue_law)
  show "AE \<omega> in aglue_law T \<kappa> Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule aglue_law_start[OF T0 PQ setsQ Kp Q0 K0])
  show "AE \<omega> in aglue_law T \<kappa> Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T
      \<longrightarrow> (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule aglue_law_diffquot[OF T0 PQ setsQ Kp st Qst Qcov Kfr Kcov])
  show "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. fst (\<omega> (min t T)))" by (rule mgX)
  show "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
      (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))" by (rule mgC)
qed

text \<open>The set-integral transfer for the glue --- what a martingale identity
  for \<^const>\<open>aglue_law\<close> has to be pushed through.  Same two steps as
  @{thm [source] AE_aglue_law}: @{thm [source] integral_distr} to the
  semidirect product, then @{thm [source] integral_ksemi_real} to the past
  and the continuation.\<close>

lemma integral_aglue_law:
  fixes Q :: "('n::finite pairpath) measure" and h :: "'n pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and hm: "h \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and hi: "integrable (aglue_law T \<kappa> Q) h"
    and msec: "(\<lambda>p'. \<integral>w. h (padd T p' w) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
  shows "(\<integral>\<omega>. h \<omega> \<partial>(aglue_law T \<kappa> Q))
      = (\<integral>p'. (\<integral>w. h (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). padd T (fst p) (snd p)"
  have neQ: "space Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have setsS: "sets (ksemi Q ?B \<kappa>) = sets (Q \<Otimes>\<^sub>M ?B)"
    by (rule sets_ksemi[OF Kp neQ])
  have pm2: "?g \<in> Q \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B" by (rule padd_measurable_ksemi[OF T0 setsQ])
  have pm: "?g \<in> ksemi Q ?B \<kappa> \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsS refl] by (rule pm2)
  have hgm: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). h (?g p))
      \<in> borel_measurable (Q \<Otimes>\<^sub>M ?B)"
    by (rule measurable_compose[OF pm2 hm])
  have hgi: "integrable (ksemi Q ?B \<kappa>) (\<lambda>p. h (?g p))"
  proof -
    have "integrable (distr (ksemi Q ?B \<kappa>) ?B ?g) h" using hi
      unfolding aglue_law_def .
    then show ?thesis unfolding integrable_distr_eq[OF pm hm] .
  qed
  have "(\<integral>\<omega>. h \<omega> \<partial>(aglue_law T \<kappa> Q)) = (\<integral>p. h (?g p) \<partial>(ksemi Q ?B \<kappa>))"
    unfolding aglue_law_def by (rule integral_distr[OF pm hm])
  also have "\<dots> = (\<integral>p'. (\<integral>w. h (?g (p', w)) \<partial>(\<kappa> p')) \<partial>Q)"
    by (rule integral_ksemi_real[OF Kp hgm hgi neQ]) (use msec in simp)
  finally show ?thesis by simp
qed

subsection \<open>Auxiliaries for clause (iv)\<close>

text \<open>\<open>i \<and> \<theta>\<close> is a stopping time.  Unlike \<open>i \<or> \<theta>\<close> this needs both directions of
  the cut: on \<open>{\<theta> \<le> i}\<close> the value is \<open>\<theta>\<close> and agreement up to \<open>\<theta>\<close> fixes it; on
  \<open>{\<theta> > i}\<close> the value is \<open>i\<close>, and agreement up to \<open>i\<close> still fixes it, because
  a path with \<open>\<theta> < i\<close> would already have been detected by then.\<close>

lemma path_stopping_time_min:
  fixes \<theta> :: "'n::finite pairpath \<Rightarrow> real"
  assumes st: "path_stopping_time T \<theta>" and i: "0 \<le> i" and iT: "i \<le> T"
  shows "path_stopping_time T (\<lambda>\<omega>. min i (\<theta> \<omega>))"
proof -
  have c1: "0 \<le> min i (\<theta> \<omega>) \<and> min i (\<theta> \<omega>) \<le> T" for \<omega> :: "'n pairpath"
    using i iT path_stopping_time_nonneg[OF st, of \<omega>]
      path_stopping_time_le[OF st, of \<omega>] by simp
  have c2: "min i (\<theta> \<omega>') = min i (\<theta> \<omega>)"
    if cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
      and cw': "continuous_on {0..T} (\<lambda>v. fst (\<omega>' v))"
      and ag: "\<forall>s \<in> {0..min i (\<theta> \<omega>)}. \<omega> s = \<omega>' s" for \<omega> \<omega>' :: "'n pairpath"
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
  @{thm [source] stopped_increment_of_horizon_gen} samples at.\<close>

lemma pstopped_eval_min:
  fixes p' :: "'n::finite pairpath"
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
lemma section_padd_in_filtration:
  fixes p' :: "'n::finite pairpath" and N :: "('n pairpath) measure"
  assumes i0: "0 \<le> i" and iT: "i \<le> T"
    and setsN: "sets N = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and pm: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric i :: ('n pairpath) metric)))"
  shows "{w \<in> space N. pcut i (padd T p' w) \<in> B}
      \<in> sets (natural_filtration N 0 (\<lambda>v w. w v) i)"
proof -
  let ?Bi = "borel_of (mtopology_of (path_metric i :: ('n pairpath) metric))"
  have pc: "pcut i p' \<in> mspace (path_metric i :: ('n pairpath) metric)"
  proof -
    have "continuous_on {0..i} p'"
      by (rule continuous_on_subset[OF mspace_path_metricD[OF pm]])
         (use i0 iT in auto)
    then show ?thesis unfolding pcut_def by (rule mspace_path_metricI)
  qed
  have m1: "(\<lambda>q :: 'n pairpath. padd i (pcut i p') q) \<in> ?Bi \<rightarrow>\<^sub>M ?Bi"
  proof (rule measurable_into_path_metric)
    show "padd i (pcut i p') q \<in> mspace (path_metric i :: ('n pairpath) metric)"
      if "q \<in> space ?Bi" for q
      using that pc by (auto simp: space_borel_of intro: padd_mspace)
  next
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric i :: ('n pairpath) metric)"
    show "(\<lambda>q. mdist (path_metric i :: ('n pairpath) metric)
        (padd i (pcut i p') q) a) \<in> borel_measurable ?Bi"
    proof (rule mdist_measurable_of_eval[OF i0 _ am])
      show "padd i (pcut i p') q \<in> mspace (path_metric i :: ('n pairpath) metric)"
        if "q \<in> space ?Bi" for q
        using that pc by (auto simp: space_borel_of intro: padd_mspace)
      fix s :: real
      show "(\<lambda>q :: 'n pairpath. padd i (pcut i p') q s) \<in> borel_measurable ?Bi"
      proof (cases "s \<in> {0..i}")
        case True
        have "(\<lambda>q :: 'n pairpath. pcut i p' s + q s) \<in> borel_measurable ?Bi"
          by (intro borel_measurable_add borel_measurable_const
              pair_law_eval_measurable[OF refl])
        then show ?thesis by (simp add: padd_apply[OF True])
      next
        case False
        have "(\<lambda>q :: 'n pairpath. padd i (pcut i p') q s) = (\<lambda>q. undefined)"
          by (rule ext) (rule padd_outside[OF False])
        then show ?thesis by simp
      qed
    qed
  qed
  have m2: "(\<lambda>w :: 'n pairpath. pcut i w) \<in> N \<rightarrow>\<^sub>M ?Bi"
    by (rule pcut_measurable[OF i0 iT setsN])
  have eq: "{w \<in> space N. pcut i (padd T p' w) \<in> B}
      = (\<lambda>w :: 'n pairpath. pcut i w) -`
          ((\<lambda>q. padd i (pcut i p') q) -` B \<inter> space ?Bi) \<inter> space N"
  proof -
    have "pcut i (padd T p' w) = padd i (pcut i p') (pcut i w)" for w
      by (rule pcut_padd_section[OF i0 iT])
    moreover have "pcut i w \<in> space ?Bi" if "w \<in> space N" for w
      using measurable_space[OF m2 that] .
    ultimately show ?thesis by auto
  qed
  have inner: "(\<lambda>q. padd i (pcut i p') q) -` B \<inter> space ?Bi \<in> sets ?Bi"
    by (rule measurable_sets[OF m1 B])
  have "(\<lambda>w :: 'n pairpath. pcut i w) -`
      ((\<lambda>q. padd i (pcut i p') q) -` B \<inter> space ?Bi) \<inter> space N
      \<in> sets (natural_filtration N 0 (\<lambda>v w. w v) i)"
    by (rule pcut_vimage_natural_filtration[OF i0 iT setsN inner])
  then show ?thesis unfolding eq .
qed

subsection \<open>The conditioning set on \<open>{\<theta> > i}\<close> lives in \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<and>\<^sub> \<^sub>\<theta>\<^sub>)\<close>\<close>

text \<open>The one set-theoretic step of the four-cell argument.  A \<open>pcut i\<close>-set
  intersected with \<open>{\<theta> > i}\<close> is an \<open>\<F>\<^sub>(\<^sub>i\<^sub> \<^sub>\<and>\<^sub> \<^sub>\<theta>\<^sub>)\<close>-set: below \<open>i\<close> the cut
  \<open>{i \<and> \<theta> \<le> t}\<close> forces \<open>\<theta> \<le> t < i\<close> and so meets \<open>{\<theta> > i}\<close> in nothing, while
  from \<open>i\<close> on the cut is everything and the set is already \<open>\<F>\<^sub>i\<close>-measurable.\<close>

lemma pcut_after_in_pre_sigma:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i0: "0 \<le> i" and iT: "i \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric i :: ('n pairpath) metric)))"
  shows "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}
      \<in> pre_sigma_of Q (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v)) (\<lambda>p'. min i (\<theta> p'))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?C = "(pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. i < \<theta> p'}"
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have FB: "?F t = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) t" for t
    by (rule natural_filtration_cong_space[OF spQ])
  have mono: "sets (?F s) \<subseteq> sets (?F t)" if "s \<le> t" for s t
    by (rule sets_natural_filtration_mono[OF that])
  have cutB: "pcut i -` B \<inter> space Q \<in> sets (?F i)"
    by (rule pcut_vimage_natural_filtration[OF i0 iT setsQ B])
  have evi: "{p' \<in> space Q. \<theta> p' \<le> i} \<in> sets (?F i)"
    unfolding FB spQ
    by (rule path_stopping_time_event_filtration[OF T0 st thM i0 iT])
  have QP: "?C \<in> sets Q"
  proof -
    have "sets (?F i) \<subseteq> sets Q"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsQ])
    moreover have "?C = (pcut i -` B \<inter> space Q)
        - ((pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. \<theta> p' \<le> i})" by auto
    ultimately show ?thesis
      using cutB evi sets.Diff sets.Int by (metis (no_types, lifting) subsetD)
  qed
  show ?thesis
  proof (rule pre_sigma_ofI[OF QP])
    fix t :: real assume t: "0 \<le> t"
    show "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} \<in> sets (?F t)"
    proof (cases "i \<le> t")
      case True
      have "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} = ?C"
        using True by auto
      moreover have "?C \<in> sets (?F i)"
      proof -
        have "?C = (pcut i -` B \<inter> space Q)
            - ((pcut i -` B \<inter> space Q) \<inter> {p' \<in> space Q. \<theta> p' \<le> i})" by auto
        then show ?thesis using cutB evi by (simp add: sets.Diff sets.Int)
      qed
      ultimately show ?thesis using mono[OF True] by auto
    next
      case False
      have "?C \<inter> {p' \<in> space Q. min i (\<theta> p') \<le> t} = {}"
        using False by auto
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>Clause (iv): the inner-integral identity\<close>

theorem aglue_inner_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric i :: ('n pairpath) metric)))"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min i T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min j T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Y = "\<lambda>u p' :: 'n pairpath. fst (p' (min u T)) $ c"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])

  \<comment> \<open>the two pointwise halves\<close>
  have after: "?g u p' = indicator B (pcut i p') * ?Y u p'"
    if sp: "p' \<in> space Q" and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
    for p' u
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have m: "min u T \<in> {0..T}" using u0 uT by simp
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    have pdm: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> \<kappa> p' \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsK refl]
      by (rule padd_measurable_left[OF T0' pmem])
    have Xm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c) \<in> borel_measurable ?B"
    proof -
      have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) \<bullet> (axis c 1 :: real^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF pair_law_eval_measurable[OF refl]
              pair_fst_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have icm: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mL: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ c)) \<in> borel_measurable (\<kappa> p')"
      using icm measurable_compose[OF pdm Xm] by simp
    have mR: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Y u p' + fst (w (min u T)) $ c)) \<in> borel_measurable (\<kappa> p')"
      using Xm unfolding measurable_cong_sets[OF setsK refl] by simp
    have cutAE: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Y u p' + fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mL mR])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c)
          = indicator B (pcut i p') * (?Y u p' + fst (w (min u T)) $ c)"
        using cutAE
      proof eventually_elim
        case (elim w)
        show ?case unfolding elim padd_apply[OF m] by simp
      qed
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (\<integral>w. ?Y u p' + fst (w (min u T)) $ c \<partial>(\<kappa> p'))" by simp
    also have "(\<integral>w. ?Y u p' + fst (w (min u T)) $ c \<partial>(\<kappa> p'))
        = ?Y u p' + (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PKi.integrable_const
        Kint[OF sp u0 uT]] by (simp add: PKi.prob_space)
    finally show ?thesis using Kmean[OF sp u0 uT] by simp
  qed

  have before: "?g j p' = ?g i p'"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'" and le: "\<theta> p' \<le> i"
    for p'
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    define C where "C = {w \<in> space (\<kappa> p'). pcut i (padd T p' w) \<in> B}"
    have Cf: "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)"
      unfolding C_def
      by (rule section_padd_in_filtration[OF i0 iT setsK pmem B])
    have CK: "C \<in> sets (\<kappa> p')"
    proof -
      have "sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w :: 'n pairpath. w s) i)
          \<subseteq> sets (\<kappa> p')"
        by (rule sets_natural_filtration_subset)
           (rule pair_law_eval_measurable[OF setsK])
      then show ?thesis using Cf by blast
    qed
    have same: "?Y j p' = ?Y i p'"
    proof -
      have e1: "p' (min i T) = p' (min (min i T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' i0])
      have e2: "p' (min j T) = p' (min (min j T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' j0])
      have m1: "min (min i T) (\<theta> p') = \<theta> p'" using le iT th0[of p'] by simp
      have m2: "min (min j T) (\<theta> p') = \<theta> p'"
        using le ij jT th0[of p'] by simp
      show ?thesis using e1 e2 m1 m2 by simp
    qed
    have dec: "?g u p' = ?Y u p' * measure (\<kappa> p') C
        + set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have m: "min u T \<in> {0..T}" using u0 uT by simp
      have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
      have i1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Y u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Y u p'"] by simp
      have i2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * (fst (w (min u T)) $ c))"
        using integrable_mult_indicator[OF CK Kint[OF sp u0 uT]] by simp
      have "?g u p' = (\<integral>w. indicator C w * ?Y u p'
          + indicator C w * (fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: C_def padd_apply[OF m] indicator_def)
      also have "\<dots> = (\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p'))
          + (\<integral>w. indicator C w * (fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_add[OF i1 i2])
      also have "(\<integral>w. indicator C w * ?Y u p' \<partial>(\<kappa> p')) = ?Y u p' * measure (\<kappa> p') C"
        by (simp add: mult.commute Int_absorb2[OF Csub])
      finally show ?thesis unfolding set_lebesgue_integral_def by simp
    qed
    show ?thesis
      unfolding dec[OF j0 jT] dec[OF i0 iT] same
      using Kinc[OF sp Cf i0 ij jT] by simp
  qed

  \<comment> \<open>the outer split: pointwise on the complement, optional sampling on \<open>?E\<close>\<close>
  have si: "set_integrable Q S (?g u)"
    if "S \<in> sets Q" "0 \<le> u" "u \<le> T" for S u
    unfolding set_integrable_def
    by (rule integrable_mult_indicator[OF that(1) gint[OF that(2,3)]])
  have spint: "set_lebesgue_integral Q (space Q) (?g u) = (\<integral>p'. ?g u p' \<partial>Q)"
    if "0 \<le> u" "u \<le> T" for u
    by (rule set_integral_space[OF gint[OF that]])
  have Esplit: "(\<integral>p'. ?g u p' \<partial>Q)
      = set_lebesgue_integral Q ?E (?g u)
        + set_lebesgue_integral Q (space Q - ?E) (?g u)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have dis: "?E \<inter> (space Q - ?E) = {}" by auto
    have cm: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
    have un: "?E \<union> (space Q - ?E) = space Q" by auto
    have "set_lebesgue_integral Q (?E \<union> (space Q - ?E)) (?g u)
        = set_lebesgue_integral Q ?E (?g u)
          + set_lebesgue_integral Q (space Q - ?E) (?g u)"
      by (rule set_integral_Un[OF dis si[OF Emeas u0 uT] si[OF cm u0 uT]])
    then show ?thesis unfolding un spint[OF u0 uT] .
  qed
  have cmQ: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
  have compl: "set_lebesgue_integral Q (space Q - ?E) (?g j)
      = set_lebesgue_integral Q (space Q - ?E) (?g i)"
  proof (rule set_lebesgue_integral_cong_AE[OF cmQ])
    show "?g j \<in> borel_measurable Q"
      using gint[OF j0 jT] by (simp add: borel_measurable_integrable)
    show "?g i \<in> borel_measurable Q"
      using gint[OF i0 iT] by (simp add: borel_measurable_integrable)
    show "AE x \<in> (space Q - ?E) in Q. ?g j x = ?g i x"
      using Qst AE_space
    proof eventually_elim
      case (elim x)
      then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
      show "x \<in> space Q - ?E \<longrightarrow> ?g j x = ?g i x"
      proof
        assume "x \<in> space Q - ?E"
        then have le: "\<theta> x \<le> i" using sp by simp
        show "?g j x = ?g i x" by (rule before[OF sp idem le])
      qed
    qed
  qed
  have Epart: "set_lebesgue_integral Q ?E (?g j)
      = set_lebesgue_integral Q ?E (?g i)"
  proof -
    have rew: "set_lebesgue_integral Q ?E (?g u)
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y u)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix x assume x: "x \<in> space Q"
      show "indicator ?E x *\<^sub>R ?g u x = indicator (?D \<inter> ?E) x *\<^sub>R ?Y u x"
      proof (cases "x \<in> ?E")
        case True
        then have lt: "i < \<theta> x" by simp
        have gv: "?g u x = indicator B (pcut i x) * ?Y u x"
          by (rule after[OF x lt u0 uT])
        have iv: "indicator (?D \<inter> ?E) x = (indicator B (pcut i x) :: real)"
          using True x by (simp add: indicator_def)
        show ?thesis unfolding gv iv using True by simp
      next
        case False
        then have e1: "indicator ?E x = (0::real)" by simp
        have e2: "indicator (?D \<inter> ?E) x = (0::real)" using False by simp
        show ?thesis unfolding e1 e2 by simp
      qed
    qed
    have sti: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min i (\<theta> p'))"
      by (rule path_stopping_time_min[OF st i0 iT])
    have stj: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min j (\<theta> p'))"
      by (rule path_stopping_time_min[OF st j0 jT])
    have sMi: "(\<lambda>p' :: 'n pairpath. min i (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have sMj: "(\<lambda>p' :: 'n pairpath. min j (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have lemin: "min i (\<theta> p') \<le> min j (\<theta> p')" for p' :: "'n pairpath"
      using ij by simp
    have Cpre: "?D \<inter> ?E \<in> pre_sigma_of Q ?F (\<lambda>p'. min i (\<theta> p'))"
      by (rule pcut_after_in_pre_sigma[OF T0' setsQ st thM i0 iT B])
    have Ycont: "continuous_on {0..T} (\<lambda>s. ?Y s p')"
      if sp: "p' \<in> space Q" for p'
    proof -
      have "continuous_on {0..T} (\<lambda>s. fst (p' s) $ c)"
        using Qcont[OF sp] by (intro continuous_intros)
      moreover have "continuous_on {0..T} (\<lambda>s. fst (p' (min s T)) $ c)
          = continuous_on {0..T} (\<lambda>s. fst (p' s) $ c)"
        by (rule continuous_on_cong[OF refl]) simp
      ultimately show ?thesis by simp
    qed
    have samp: "set_lebesgue_integral Q (?D \<inter> ?E)
          (\<lambda>p'. ?Y (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min j (\<theta> p')) p')"
      by (rule stopped_increment_of_horizon_gen
          [OF T0 setsQ QH Ycont sti sMi stj sMj lemin Cpre])
    have valE: "?Y (min u (\<theta> p')) p' = ?Y u p'"
      if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
        and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
        and ui: "i \<le> u" for p' u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u0])
      moreover have "min (min u (\<theta> p')) T = min (min u T) (\<theta> p')"
        using u0 uT th0[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have Dmeas: "?D \<in> sets Q"
      by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). fst z $ c)
        \<in> borel_measurable borel"
    proof -
      have s: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
          \<in> borel_measurable borel"
        by (intro borel_measurable_continuous_onI continuous_intros)
      show ?thesis by (rule measurable_compose[OF s borel_measurable_nth])
    qed
    have Yfix: "?Y v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule pair_law_eval_measurable[OF setsQ])
      then show ?thesis by (rule measurable_compose[OF _ fcB])
    qed
    have Ym: "(\<lambda>p' :: 'n pairpath. ?Y (min v (\<theta> p')) p') \<in> borel_measurable Q"
      if v0: "0 \<le> v" for v
    proof -
      have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> Q \<rightarrow>\<^sub>M ?B"
        by (rule measurable_ident_sets[OF setsQ])
      have thQ: "\<theta> \<in> borel_measurable Q"
        using thM measurable_cong_sets[OF setsQ refl] by blast
      have gm: "(\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T) \<in> borel_measurable Q"
        using thQ by measurable
      have g0: "0 \<le> min (min v (\<theta> p')) T"
        if "p' \<in> space Q" for p' :: "'n pairpath"
        using v0 th0[of p'] T0' by simp
      have gT: "min (min v (\<theta> p')) T \<le> T"
        if "p' \<in> space Q" for p' :: "'n pairpath" by simp
      have ev: "(\<lambda>p' :: 'n pairpath. p' (min (min v (\<theta> p')) T))
          \<in> borel_measurable Q"
        by (rule path_eval_at_measurable_time
            [where X = "\<lambda>p' :: 'n pairpath. p'"
              and g = "\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T",
              OF T0' idm gm g0 gT])
      show ?thesis by (rule measurable_compose[OF ev fcB])
    qed
    have e1: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y i)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Ym[OF i0] Yfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Y (min i (\<theta> x)) x = ?Y i x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Y (min i (\<theta> x)) x = ?Y i x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Y (min i (\<theta> x)) x = ?Y i x"
            by (rule valE[OF sp idem lt i0 iT order.refl])
        qed
      qed
    qed
    have e2: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Y (min j (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Y j)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Ym[OF j0] Yfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Y (min j (\<theta> x)) x = ?Y j x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Y (min j (\<theta> x)) x = ?Y j x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Y (min j (\<theta> x)) x = ?Y j x"
            by (rule valE[OF sp idem lt j0 jT ij])
        qed
      qed
    qed
    show ?thesis
      unfolding rew[OF i0 iT] rew[OF j0 jT]
      using samp e1 e2 by simp
  qed
  show ?thesis
    unfolding Esplit[OF i0 iT] Esplit[OF j0 jT]
    using compl Epart by simp
qed

subsection \<open>Clause (iv): the increment identity for the glued law\<close>

text \<open>The wrapper.  @{thm [source] sets_natural_filtration_eq_pcut_vimage}
  presents the conditioning set as a \<^const>\<open>pcut\<close>-preimage,
  @{thm [source] integral_aglue_law} carries the set integral to the past
  and the continuation, and there @{thm [source] aglue_inner_increment}
  closes it.\<close>

theorem aglue_law_X_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and A: "A \<in> sets (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v) i)"
    and hi: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. indicator A \<omega> * (fst (\<omega> (min u T)) $ c))"
    and msec: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))
      \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "set_lebesgue_integral (aglue_law T \<kappa> Q) A (\<lambda>\<omega>. fst (\<omega> (min i T)) $ c)
       = set_lebesgue_integral (aglue_law T \<kappa> Q) A (\<lambda>\<omega>. fst (\<omega> (min j T)) $ c)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bi = "borel_of (mtopology_of (path_metric i :: ('n pairpath) metric))"
  let ?R = "aglue_law T \<kappa> Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  obtain B where B: "B \<in> sets ?Bi" and Aeq: "A = pcut i -` B \<inter> space ?R"
    using A
    unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B" for u
    by (rule pair_law_eval_measurable[OF refl])
  have Xm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c) \<in> borel_measurable ?B"
    for u
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) \<bullet> (axis c 1 :: real^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_fst_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have AR: "A \<in> sets ?R"
  proof -
    have "sets (natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) i)
        \<subseteq> sets ?R"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsR])
    then show ?thesis using A by blast
  qed
  have AB: "A \<in> sets ?B" using AR setsR by simp
  have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * (fst (\<omega> (min u T)) $ c))
      \<in> borel_measurable ?B" for u
    using AB Xm[of u] by measurable

  \<comment> \<open>transport one side\<close>
  have tr: "set_lebesgue_integral ?R A (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
      = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have "set_lebesgue_integral ?R A (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
        = (\<integral>\<omega>. indicator A \<omega> * (fst (\<omega> (min u T)) $ c) \<partial>?R)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
        * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
      by (rule integral_aglue_law
          [OF T0' PQ setsQ Kp hm hi[OF u0 uT] msec[OF u0 uT]])
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<partial>Q)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix p' assume sp: "p' \<in> space Q"
      have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sp spQ by (simp add: space_borel_of)
      have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
      have spK: "space (\<kappa> p') = space ?B"
        by (rule sets_eq_imp_space_eq[OF setsK])
      show "(\<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))
          = (\<integral>w. indicator B (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have inR: "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        have "indicator A (padd T p' w)
            = (indicator B (pcut i (padd T p' w)) :: real)"
          unfolding Aeq using inR by (simp add: indicator_def)
        then show "indicator A (padd T p' w)
              * (fst (padd T p' w (min u T)) $ c)
            = indicator B (pcut i (padd T p' w))
              * (fst (padd T p' w (min u T)) $ c)" by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding tr[OF i0 iT] tr[OF j0 jT]
    by (rule aglue_inner_increment
        [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
          i0 ij iT jT B gint[OF _ _ B]])
qed

subsection \<open>Clause (iv) for the glue: the \<open>X\<close> martingale\<close>

text \<open>Assembly.  The componentwise identity is
  @{thm [source] aglue_law_X_increment}; the vector one follows by
  @{thm [source] set_integral_vec_component}, and
  \<open>martingale_of_set_integral_eq\<close> turns it into the martingale property.
  Past the horizon the process is constant, so an index above \<open>T\<close> is pulled
  back to \<open>T\<close> before the identity is applied.\<close>

theorem aglue_law_X_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QH: "\<And>c. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ c) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u c. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ c \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u c. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ c)"
    and Kinc: "\<And>p' C u v c. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ c)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ c)"
    and RXint: "\<And>u. 0 \<le> u
      \<Longrightarrow> integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
    and msec: "\<And>A u c. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and gint: "\<And>u BB c i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ c) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. fst (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have m: "min u T \<in> {0..u}" using u T0' by simp
    have Rb: "?G u = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
      by (rule natural_filtration_cong_space
          [OF sets_eq_imp_space_eq[OF setsR]])
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      unfolding Rb by (rule path_eval_measurable_natural_filtration'[OF m])
    then show ?thesis by (rule measurable_compose) (rule pair_fst_borel)
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule RXint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    have v0: "0 \<le> v" using uv by simp
    have CR: "C \<in> sets ?R" using C SF.sets_F_subset[OF uv(1)] by blast
    have comp: "set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X u \<omega> $ c)
        = set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X v \<omega> $ c)" for c
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      then have uT: "u \<le> T" by simp
      have vT: "min v T \<le> T" by simp
      have uvT: "u \<le> min v T" using uv uT by simp
      have hiA: "integrable ?R (\<lambda>\<omega>. indicator C \<omega> * (fst (\<omega> (min s T)) $ c))"
        if s: "0 \<le> s" for s
      proof -
        have ii: "integrable ?R (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min s T)) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RXint[OF s]])
        show ?thesis using integrable_mult_indicator[OF CR ii] by simp
      qed
      have "set_lebesgue_integral ?R C (\<lambda>\<omega>. fst (\<omega> (min u T)) $ c)
          = set_lebesgue_integral ?R C (\<lambda>\<omega>. fst (\<omega> (min (min v T) T)) $ c)"
        by (rule aglue_law_X_increment
            [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
              uv(1) uvT uT vT C hiA msec[OF CR] gint[OF _ _ _ uv(1) uT]])
      then show ?thesis by simp
    qed
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof -
      have "set_lebesgue_integral ?R C (?X u) $ c
          = set_lebesgue_integral ?R C (?X v) $ c" for c
        using comp[of c]
        unfolding set_integral_vec_component[OF CR RXint[OF uv(1)]]
          set_integral_vec_component[OF CR RXint[OF v0]] .
      then show ?thesis by (simp add: vec_eq_iff)
    qed
  qed
qed

subsection \<open>Clause (iv): the compensated inner-integral identity\<close>

text \<open>\<^const>\<open>outerp\<close> is quadratic, so on the product

  \<open>(outerp (fst (padd p' w s)) - snd (padd p' w s)) $ c $ d
     = Zp s p' + Zw s w + (fst (p' s) $ c * fst (w s) $ d
                           + fst (w s) $ c * fst (p' s) $ d)\<close>

  --- a past compensated entry, a continuation compensated entry, and two
  cross terms.  Inside the inner integral the past factor
  \<^term>\<open>fst (p' s)\<close> is constant, so it pulls out and what remains is a
  continuation increment: on \<open>{\<theta> > i}\<close> the vanishing of the continuation's
  mean, on \<open>{\<theta> \<le> i}\<close> its own increment identity against the section.  The
  four-cell shape is thus unchanged from the \<open>X\<close> clause, with no extra
  cross-term machinery needed.\<close>

theorem aglue_inner_increment_comp:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and B: "B \<in> sets (borel_of (mtopology_of
        (path_metric i :: ('n pairpath) metric)))"
    and gint: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "(\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min i T)))
                - snd (padd T p' w (min i T))) $ c $ d) \<partial>(\<kappa> p')) \<partial>Q)
       = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min j T)))
                - snd (padd T p' w (min j T))) $ c $ d) \<partial>(\<kappa> p')) \<partial>Q)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?F = "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  let ?g = "\<lambda>u p' :: 'n pairpath. \<integral>w. indicator B (pcut i (padd T p' w))
      * ?Z u (padd T p' w) \<partial>(\<kappa> p')"
  let ?E = "{p' \<in> space Q. i < \<theta> p'}"
  let ?D = "pcut i -` B \<inter> space Q"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have evQ: "(\<lambda>p' :: 'n pairpath. \<theta> p') \<in> borel_measurable Q"
    unfolding measurable_cong_sets[OF setsQ refl] by (rule thM)
  have Emeas: "?E \<in> sets Q" using evQ by measurable
  have Dmeas: "?D \<in> sets Q"
    by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])

  \<comment> \<open>the pathwise expansion of the compensated entry along the glue\<close>
  have expand: "?Z u (padd T p' w)
      = ?Z u p' + (?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
    if "0 \<le> u" and "u \<le> T" for u p' w
  proof -
    have m: "min u T \<in> {0..T}" using that by simp
    show ?thesis
      unfolding padd_apply[OF m] by (simp add: outerp_def algebra_simps)
  qed

  have after: "?g u p' = indicator B (pcut i p') * ?Z u p'"
    if sp: "p' \<in> space Q" and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
    for p' u
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    have pdm: "(\<lambda>w :: 'n pairpath. padd T p' w) \<in> \<kappa> p' \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF setsK refl]
      by (rule padd_measurable_left[OF T0' pmem])
    have cut: "AE w in \<kappa> p'. pcut i (padd T p' w) = pcut i p'"
      using Kfr[OF sp]
    proof eventually_elim
      case (elim w)
      show ?case by (rule pcut_padd_before[OF i0 iT _ lt]) (use elim in blast)
    qed
    have evB: "(\<lambda>w :: 'n pairpath. w s) \<in> borel_measurable ?B" for s
      by (rule pair_law_eval_measurable[OF refl])
    have femB: "(\<lambda>w :: 'n pairpath. fst (w s) $ e) \<in> borel_measurable ?B"
      for s e
    proof -
      have "(\<lambda>w :: 'n pairpath. fst (w s) \<bullet> (axis e 1 :: real^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF evB pair_fst_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have semB: "(\<lambda>w :: 'n pairpath. snd (w s) $ e $ f) \<in> borel_measurable ?B"
      for s e f
    proof -
      have "(\<lambda>w :: 'n pairpath. snd (w s) \<bullet> (axis e (axis f 1) :: real^'n^'n))
          \<in> borel_measurable ?B"
        by (intro borel_measurable_inner borel_measurable_const
            measurable_compose[OF evB pair_snd_borel])
      then show ?thesis by (simp add: inner_axis)
    qed
    have ZmB: "?Z v \<in> borel_measurable ?B" for v
    proof -
      have e: "?Z v = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min v T)) $ c
          * fst (\<omega> (min v T)) $ d - snd (\<omega> (min v T)) $ c $ d)"
        by (rule ext) (rule comp_entry_eq)
      show ?thesis unfolding e
        by (intro borel_measurable_diff borel_measurable_times femB semB)
    qed
    have icmc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w)) :: real)
        \<in> borel_measurable (\<kappa> p')"
      by (rule measurable_compose[OF measurable_compose[OF pdm
          pcut_measurable[OF i0 iT refl]] borel_measurable_indicator[OF B]])
    have mLc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i (padd T p' w))
        * ?Z u (padd T p' w)) \<in> borel_measurable (\<kappa> p')"
      using icmc measurable_compose[OF pdm ZmB] by simp
    have mRc: "(\<lambda>w :: 'n pairpath. indicator B (pcut i p')
        * (?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))))
        \<in> borel_measurable (\<kappa> p')"
      using ZmB[of u] femB
      unfolding measurable_cong_sets[OF setsK refl] by simp
    have i1: "integrable (\<kappa> p') (\<lambda>w. ?Z u w)" by (rule KintC[OF sp u0 uT])
    have i2: "integrable (\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d)"
      by (rule integrable_mult_right) (rule Kint[OF sp u0 uT])
    have i3: "integrable (\<kappa> p')
        (\<lambda>w. fst (w (min u T)) $ c * fst (p' (min u T)) $ d)"
      using integrable_mult_right[OF Kint[OF sp u0 uT],
        of "fst (p' (min u T)) $ d"] by (simp add: mult.commute)
    have z2: "(\<integral>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      using Kmean[OF sp u0 uT] by simp
    have z3: "(\<integral>w. fst (w (min u T)) $ c * fst (p' (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      using Kmean[OF sp u0 uT] by simp
    have i23: "integrable (\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)"
      by (rule Bochner_Integration.integrable_add[OF i2 i3])
    have z23: "(\<integral>w. fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d \<partial>(\<kappa> p')) = 0"
      unfolding Bochner_Integration.integral_add[OF i2 i3] z2 z3 by simp
    have i123: "integrable (\<kappa> p') (\<lambda>w. ?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
      by (rule Bochner_Integration.integrable_add[OF i1 i23])
    have z123: "(\<integral>w. ?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d) \<partial>(\<kappa> p')) = 0"
      unfolding Bochner_Integration.integral_add[OF i1 i23]
        KmeanC[OF sp u0 uT] z23 by simp
    have inner: "(\<integral>w. ?Z u p' + (?Z u w
        + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
           + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)) \<partial>(\<kappa> p'))
        = ?Z u p'"
      unfolding Bochner_Integration.integral_add[OF PKi.integrable_const i123]
        z123 by (simp add: PKi.prob_space)
    have "?g u p' = (\<integral>w. indicator B (pcut i p')
        * (?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d))) \<partial>(\<kappa> p'))"
    proof (rule Bochner_Integration.integral_cong_AE[OF mLc mRc])
      show "AE w in \<kappa> p'. indicator B (pcut i (padd T p' w))
            * ?Z u (padd T p' w)
          = indicator B (pcut i p')
            * (?Z u p' + (?Z u w
              + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
                 + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)))"
        using cut
      proof eventually_elim
        case (elim w)
        show ?case unfolding elim expand[OF u0 uT] ..
      qed
    qed
    also have "\<dots> = indicator B (pcut i p')
        * (\<integral>w. ?Z u p' + (?Z u w
          + (fst (p' (min u T)) $ c * fst (w (min u T)) $ d
             + fst (w (min u T)) $ c * fst (p' (min u T)) $ d)) \<partial>(\<kappa> p'))"
      by simp
    finally show ?thesis unfolding inner .
  qed

  have before: "?g j p' = ?g i p'"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'" and le: "\<theta> p' \<le> i"
    for p'
  proof -
    interpret PKi: prob_space "\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
    have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using sp spQ by (simp add: space_borel_of)
    define C where "C = {w \<in> space (\<kappa> p'). pcut i (padd T p' w) \<in> B}"
    have Cf: "C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) i)"
      unfolding C_def
      by (rule section_padd_in_filtration[OF i0 iT setsK pmem B])
    have CK: "C \<in> sets (\<kappa> p')"
    proof -
      have "sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w :: 'n pairpath. w s) i)
          \<subseteq> sets (\<kappa> p')"
        by (rule sets_natural_filtration_subset)
           (rule pair_law_eval_measurable[OF setsK])
      then show ?thesis using Cf by blast
    qed
    have Csub: "C \<subseteq> space (\<kappa> p')" unfolding C_def by blast
    have samev: "p' (min u T) = p' (\<theta> p')" if u: "0 \<le> u" and ui: "i \<le> u" for u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u])
      moreover have "min (min u T) (\<theta> p') = \<theta> p'"
        using le ui th0[of p'] thT[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have dec: "?g u p' = (\<integral>w. indicator C w * ?Z u p' \<partial>(\<kappa> p'))
        + ((\<integral>w. indicator C w * ?Z u w \<partial>(\<kappa> p'))
           + ((\<integral>w. indicator C w * (fst (p' (min u T)) $ c
                * fst (w (min u T)) $ d) \<partial>(\<kappa> p'))
              + (\<integral>w. indicator C w * (fst (w (min u T)) $ c
                * fst (p' (min u T)) $ d) \<partial>(\<kappa> p'))))"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
    proof -
      have j1: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Z u p')"
        using integrable_mult_indicator[OF CK PKi.integrable_const,
          of "?Z u p'"] by simp
      have j2: "integrable (\<kappa> p') (\<lambda>w. indicator C w * ?Z u w)"
        using integrable_mult_indicator[OF CK KintC[OF sp u0 uT]] by simp
      have j3: "integrable (\<kappa> p') (\<lambda>w. indicator C w
          * (fst (p' (min u T)) $ c * fst (w (min u T)) $ d))"
        using integrable_mult_indicator[OF CK
          integrable_mult_right[OF Kint[OF sp u0 uT]]] by simp
      have j4: "integrable (\<kappa> p') (\<lambda>w. indicator C w
          * (fst (w (min u T)) $ c * fst (p' (min u T)) $ d))"
        using integrable_mult_indicator[OF CK
          integrable_mult_right[OF Kint[OF sp u0 uT],
            of "fst (p' (min u T)) $ d"]] by (simp add: mult.commute)
      have "?g u p' = (\<integral>w. indicator C w * ?Z u p'
          + (indicator C w * ?Z u w
             + (indicator C w * (fst (p' (min u T)) $ c
                  * fst (w (min u T)) $ d)
                + indicator C w * (fst (w (min u T)) $ c
                  * fst (p' (min u T)) $ d))) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have ic: "indicator B (pcut i (padd T p' w)) = (indicator C w :: real)"
          unfolding C_def using sw by (simp add: indicator_def)
        show "indicator B (pcut i (padd T p' w)) * ?Z u (padd T p' w)
            = indicator C w * ?Z u p'
              + (indicator C w * ?Z u w
                 + (indicator C w * (fst (p' (min u T)) $ c
                      * fst (w (min u T)) $ d)
                    + indicator C w * (fst (w (min u T)) $ c
                      * fst (p' (min u T)) $ d)))"
          unfolding ic expand[OF u0 uT] by (simp add: field_simps)
      qed
      also have "\<dots> = (\<integral>w. indicator C w * ?Z u p' \<partial>(\<kappa> p'))
          + ((\<integral>w. indicator C w * ?Z u w \<partial>(\<kappa> p'))
             + ((\<integral>w. indicator C w * (fst (p' (min u T)) $ c
                  * fst (w (min u T)) $ d) \<partial>(\<kappa> p'))
                + (\<integral>w. indicator C w * (fst (w (min u T)) $ c
                  * fst (p' (min u T)) $ d) \<partial>(\<kappa> p'))))"
        using Bochner_Integration.integral_add[OF j1
            Bochner_Integration.integrable_add[OF j2
              Bochner_Integration.integrable_add[OF j3 j4]]]
          Bochner_Integration.integral_add[OF j2
            Bochner_Integration.integrable_add[OF j3 j4]]
          Bochner_Integration.integral_add[OF j3 j4]
        by simp
      finally show ?thesis .
    qed
    have zZ: "?Z j p' = ?Z i p'" using samev[OF i0 order_refl] samev[OF j0 ij]
      by simp
    have xc: "fst (p' (min j T)) $ c = fst (p' (min i T)) $ c"
      using samev[OF i0 order_refl] samev[OF j0 ij] by simp
    have xd: "fst (p' (min j T)) $ d = fst (p' (min i T)) $ d"
      using samev[OF i0 order_refl] samev[OF j0 ij] by simp
    have s1: "(\<integral>w. indicator C w * ?Z j p' \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * ?Z i p' \<partial>(\<kappa> p'))" unfolding zZ ..
    have s2: "(\<integral>w. indicator C w * ?Z j w \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * ?Z i w \<partial>(\<kappa> p'))"
      using KincC[OF sp Cf i0 ij jT]
      unfolding set_lebesgue_integral_def by simp
    have pull: "(\<integral>w. indicator C w * (a * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))
        = a * (\<integral>w. indicator C w * fst (w (min u T)) $ e \<partial>(\<kappa> p'))"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u a e
    proof -
      have ii: "integrable (\<kappa> p') (\<lambda>w. indicator C w * fst (w (min u T)) $ e)"
        using integrable_mult_indicator[OF CK Kint[OF sp u0 uT]] by simp
      have "(\<integral>w. indicator C w * (a * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))
          = (\<integral>w. a * (indicator C w * fst (w (min u T)) $ e) \<partial>(\<kappa> p'))"
        by (rule Bochner_Integration.integral_cong[OF refl])
           (simp add: field_simps)
      also have "\<dots> = a * (\<integral>w. indicator C w * fst (w (min u T)) $ e \<partial>(\<kappa> p'))"
        using ii by simp
      finally show ?thesis .
    qed
    have ke: "(\<integral>w. indicator C w * fst (w (min j T)) $ e \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w * fst (w (min i T)) $ e \<partial>(\<kappa> p'))" for e
      using Kinc[OF sp Cf i0 ij jT, of e]
      unfolding set_lebesgue_integral_def by simp
    have s3: "(\<integral>w. indicator C w
          * (fst (p' (min j T)) $ c * fst (w (min j T)) $ d) \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w
          * (fst (p' (min i T)) $ c * fst (w (min i T)) $ d) \<partial>(\<kappa> p'))"
      unfolding pull[OF j0 jT] pull[OF i0 iT] xc ke ..
    have s4: "(\<integral>w. indicator C w
          * (fst (w (min j T)) $ c * fst (p' (min j T)) $ d) \<partial>(\<kappa> p'))
        = (\<integral>w. indicator C w
          * (fst (w (min i T)) $ c * fst (p' (min i T)) $ d) \<partial>(\<kappa> p'))"
    proof -
      have r: "(\<integral>w. indicator C w * (fst (w (min u T)) $ c * a) \<partial>(\<kappa> p'))
          = a * (\<integral>w. indicator C w * fst (w (min u T)) $ c \<partial>(\<kappa> p'))"
        if "0 \<le> u" and "u \<le> T" for u a
      proof -
        have "(\<integral>w. indicator C w * (fst (w (min u T)) $ c * a) \<partial>(\<kappa> p'))
            = (\<integral>w. indicator C w * (a * fst (w (min u T)) $ c) \<partial>(\<kappa> p'))"
          by (rule Bochner_Integration.integral_cong[OF refl])
             (simp add: mult.commute)
        then show ?thesis unfolding pull[OF that] .
      qed
      show ?thesis unfolding r[OF j0 jT] r[OF i0 iT] xd ke ..
    qed
    show ?thesis
      unfolding dec[OF j0 jT] dec[OF i0 iT] s1 s2 s3 s4 ..
  qed

  \<comment> \<open>the outer split, exactly as in the \<open>X\<close> clause\<close>
  have si: "set_integrable Q S (?g u)"
    if "S \<in> sets Q" "0 \<le> u" "u \<le> T" for S u
    unfolding set_integrable_def
    by (rule integrable_mult_indicator[OF that(1) gint[OF that(2,3)]])
  have spint: "set_lebesgue_integral Q (space Q) (?g u) = (\<integral>p'. ?g u p' \<partial>Q)"
    if "0 \<le> u" "u \<le> T" for u
    by (rule set_integral_space[OF gint[OF that]])
  have Esplit: "(\<integral>p'. ?g u p' \<partial>Q)
      = set_lebesgue_integral Q ?E (?g u)
        + set_lebesgue_integral Q (space Q - ?E) (?g u)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have dis: "?E \<inter> (space Q - ?E) = {}" by auto
    have cm: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
    have un: "?E \<union> (space Q - ?E) = space Q" by auto
    have "set_lebesgue_integral Q (?E \<union> (space Q - ?E)) (?g u)
        = set_lebesgue_integral Q ?E (?g u)
          + set_lebesgue_integral Q (space Q - ?E) (?g u)"
      by (rule set_integral_Un[OF dis si[OF Emeas u0 uT] si[OF cm u0 uT]])
    then show ?thesis unfolding un spint[OF u0 uT] .
  qed
  have cmQ: "space Q - ?E \<in> sets Q" by (rule sets.compl_sets[OF Emeas])
  have compl: "set_lebesgue_integral Q (space Q - ?E) (?g j)
      = set_lebesgue_integral Q (space Q - ?E) (?g i)"
  proof (rule set_lebesgue_integral_cong_AE[OF cmQ])
    show "?g j \<in> borel_measurable Q"
      using gint[OF j0 jT] by (simp add: borel_measurable_integrable)
    show "?g i \<in> borel_measurable Q"
      using gint[OF i0 iT] by (simp add: borel_measurable_integrable)
    show "AE x \<in> (space Q - ?E) in Q. ?g j x = ?g i x"
      using Qst AE_space
    proof eventually_elim
      case (elim x)
      then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
      show "x \<in> space Q - ?E \<longrightarrow> ?g j x = ?g i x"
      proof
        assume "x \<in> space Q - ?E"
        then have le: "\<theta> x \<le> i" using sp by simp
        show "?g j x = ?g i x" by (rule before[OF sp idem le])
      qed
    qed
  qed
  have Epart: "set_lebesgue_integral Q ?E (?g j)
      = set_lebesgue_integral Q ?E (?g i)"
  proof -
    have rew: "set_lebesgue_integral Q ?E (?g u)
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z u)"
      if u0: "0 \<le> u" and uT: "u \<le> T" for u
      unfolding set_lebesgue_integral_def
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix x assume x: "x \<in> space Q"
      show "indicator ?E x *\<^sub>R ?g u x = indicator (?D \<inter> ?E) x *\<^sub>R ?Z u x"
      proof (cases "x \<in> ?E")
        case True
        then have lt: "i < \<theta> x" by simp
        have gv: "?g u x = indicator B (pcut i x) * ?Z u x"
          by (rule after[OF x lt u0 uT])
        have iv: "indicator (?D \<inter> ?E) x = (indicator B (pcut i x) :: real)"
          using True x by (simp add: indicator_def)
        show ?thesis unfolding gv iv using True by simp
      next
        case False
        then have e1: "indicator ?E x = (0::real)" by simp
        have e2: "indicator (?D \<inter> ?E) x = (0::real)" using False by simp
        show ?thesis unfolding e1 e2 by simp
      qed
    qed
    have sti: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min i (\<theta> p'))"
      by (rule path_stopping_time_min[OF st i0 iT])
    have stj: "path_stopping_time T (\<lambda>p' :: 'n pairpath. min j (\<theta> p'))"
      by (rule path_stopping_time_min[OF st j0 jT])
    have sMi: "(\<lambda>p' :: 'n pairpath. min i (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have sMj: "(\<lambda>p' :: 'n pairpath. min j (\<theta> p')) \<in> borel_measurable ?B"
      using thM by measurable
    have lemin: "min i (\<theta> p') \<le> min j (\<theta> p')" for p' :: "'n pairpath"
      using ij by simp
    have Cpre: "?D \<inter> ?E \<in> pre_sigma_of Q ?F (\<lambda>p'. min i (\<theta> p'))"
      by (rule pcut_after_in_pre_sigma[OF T0' setsQ st thM i0 iT B])
    have Zcont: "continuous_on {0..T} (\<lambda>s. ?Z s p')"
      if sp: "p' \<in> space Q" for p'
    proof -
      have e: "(\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)
          = (\<lambda>s. fst (p' s) $ c * fst (p' s) $ d - snd (p' s) $ c $ d)"
        by (rule ext) (rule comp_entry_eq)
      have "continuous_on {0..T} (\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)"
        unfolding e using Qcont[OF sp] by (intro continuous_intros)
      moreover have "continuous_on {0..T} (\<lambda>s. ?Z s p')
          = continuous_on {0..T} (\<lambda>s. (outerp (fst (p' s)) - snd (p' s)) $ c $ d)"
        by (rule continuous_on_cong[OF refl]) simp
      ultimately show ?thesis by simp
    qed
    have samp: "set_lebesgue_integral Q (?D \<inter> ?E)
          (\<lambda>p'. ?Z (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min j (\<theta> p')) p')"
      by (rule stopped_increment_of_horizon_gen
          [OF T0 setsQ QHC Zcont sti sMi stj sMj lemin Cpre])
    have valE: "?Z (min u (\<theta> p')) p' = ?Z u p'"
      if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
        and lt: "i < \<theta> p'" and u0: "0 \<le> u" and uT: "u \<le> T"
      for p' u
    proof -
      have "p' (min u T) = p' (min (min u T) (\<theta> p'))"
        by (rule pstopped_eval_min[OF st idem T0' u0])
      moreover have "min (min u (\<theta> p')) T = min (min u T) (\<theta> p')"
        using u0 uT th0[of p'] by simp
      ultimately show ?thesis by simp
    qed
    have Dmeas: "?D \<in> sets Q"
      by (rule measurable_sets[OF pcut_measurable[OF i0 iT setsQ] B])
    have DE: "?D \<inter> ?E \<in> sets Q" using Dmeas Emeas by simp
    have fcB: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n).
        (outerp (fst z) - snd z) $ c $ d) \<in> borel_measurable borel"
    proof -
      have s: "(\<lambda>z :: (real^'n) \<times> (real^'n^'n). outerp (fst z) - snd z)
          \<in> borel_measurable borel"
        unfolding outerp_def
        by (intro borel_measurable_continuous_onI continuous_intros)
      have n1: "(\<lambda>v :: real^'n^'n. v $ c) \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_onI)
          (rule linear_continuous_on[OF bounded_linear_vec_nth])
      have n2: "(\<lambda>v :: real^'n. v $ d) \<in> borel_measurable borel"
        by (rule borel_measurable_nth)
      show ?thesis
        by (rule measurable_compose[OF measurable_compose[OF s n1] n2])
    qed
    have Zfix: "?Z v \<in> borel_measurable Q" for v
    proof -
      have "(\<lambda>p' :: 'n pairpath. p' (min v T)) \<in> borel_measurable Q"
        by (rule pair_law_eval_measurable[OF setsQ])
      then show ?thesis by (rule measurable_compose[OF _ fcB])
    qed
    have Zm: "(\<lambda>p' :: 'n pairpath. ?Z (min v (\<theta> p')) p') \<in> borel_measurable Q"
      if v0: "0 \<le> v" for v
    proof -
      have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> Q \<rightarrow>\<^sub>M ?B"
        by (rule measurable_ident_sets[OF setsQ])
      have thQ: "\<theta> \<in> borel_measurable Q"
        using thM measurable_cong_sets[OF setsQ refl] by blast
      have gm: "(\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T) \<in> borel_measurable Q"
        using thQ by measurable
      have g0: "0 \<le> min (min v (\<theta> p')) T"
        if "p' \<in> space Q" for p' :: "'n pairpath"
        using v0 th0[of p'] T0' by simp
      have gT: "min (min v (\<theta> p')) T \<le> T"
        if "p' \<in> space Q" for p' :: "'n pairpath" by simp
      have ev: "(\<lambda>p' :: 'n pairpath. p' (min (min v (\<theta> p')) T))
          \<in> borel_measurable Q"
        by (rule path_eval_at_measurable_time
            [where X = "\<lambda>p' :: 'n pairpath. p'"
              and g = "\<lambda>p' :: 'n pairpath. min (min v (\<theta> p')) T",
              OF T0' idm gm g0 gT])
      show ?thesis by (rule measurable_compose[OF ev fcB])
    qed
    have e1: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min i (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z i)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Zm[OF i0] Zfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Z (min i (\<theta> x)) x = ?Z i x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Z (min i (\<theta> x)) x = ?Z i x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Z (min i (\<theta> x)) x = ?Z i x"
            by (rule valE[OF sp idem lt i0 iT])
        qed
      qed
    qed
    have e2: "set_lebesgue_integral Q (?D \<inter> ?E) (\<lambda>p'. ?Z (min j (\<theta> p')) p')
        = set_lebesgue_integral Q (?D \<inter> ?E) (?Z j)"
    proof (rule set_lebesgue_integral_cong_AE[OF DE Zm[OF j0] Zfix])
      show "AE x \<in> (?D \<inter> ?E) in Q. ?Z (min j (\<theta> x)) x = ?Z j x"
        using Qst AE_space
      proof eventually_elim
        case (elim x)
        then have idem: "pstopped T \<theta> x = x" and sp: "x \<in> space Q" by blast+
        show "x \<in> ?D \<inter> ?E \<longrightarrow> ?Z (min j (\<theta> x)) x = ?Z j x"
        proof
          assume "x \<in> ?D \<inter> ?E"
          then have lt: "i < \<theta> x" by simp
          show "?Z (min j (\<theta> x)) x = ?Z j x"
            by (rule valE[OF sp idem lt j0 jT])
        qed
      qed
    qed
    show ?thesis
      unfolding rew[OF i0 iT] rew[OF j0 jT]
      using samp e1 e2 by simp
  qed
  show ?thesis
    unfolding Esplit[OF i0 iT] Esplit[OF j0 jT]
    using compl Epart by simp
qed

subsection \<open>Clause (iv): the compensated martingale for the glued law\<close>

theorem aglue_law_comp_increment:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and i0: "0 \<le> i" and ij: "i \<le> j" and iT: "i \<le> T" and jT: "j \<le> T"
    and A: "A \<in> sets (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v) i)"
    and hi: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. indicator A \<omega>
          * ((outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d))"
    and msec: "\<And>u. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gint: "\<And>u BB. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))
      \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "set_lebesgue_integral (aglue_law T \<kappa> Q) A
        (\<lambda>\<omega>. (outerp (fst (\<omega> (min i T))) - snd (\<omega> (min i T))) $ c $ d)
      = set_lebesgue_integral (aglue_law T \<kappa> Q) A
        (\<lambda>\<omega>. (outerp (fst (\<omega> (min j T))) - snd (\<omega> (min j T))) $ c $ d)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Bi = "borel_of (mtopology_of (path_metric i :: ('n pairpath) metric))"
  let ?R = "aglue_law T \<kappa> Q"
  let ?Z = "\<lambda>u \<omega> :: 'n pairpath.
      (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d"
  have T0': "0 \<le> T" using T0 by simp
  have j0: "0 \<le> j" using i0 ij by simp
  have spQ: "space Q = space ?B" by (rule sets_eq_imp_space_eq[OF setsQ])
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have spR: "space ?R = space ?B" by (rule sets_eq_imp_space_eq[OF setsR])
  obtain B where B: "B \<in> sets ?Bi" and Aeq: "A = pcut i -` B \<inter> space ?R"
    using A
    unfolding sets_natural_filtration_eq_pcut_vimage[OF setsR i0 iT] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?B" for u
    by (rule pair_law_eval_measurable[OF refl])
  have fem: "(\<lambda>w :: 'n pairpath. fst (w s) $ e) \<in> borel_measurable ?B" for s e
  proof -
    have "(\<lambda>w :: 'n pairpath. fst (w s) \<bullet> (axis e 1 :: real^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_fst_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have sem: "(\<lambda>w :: 'n pairpath. snd (w s) $ e $ f) \<in> borel_measurable ?B"
    for s e f
  proof -
    have "(\<lambda>w :: 'n pairpath. snd (w s) \<bullet> (axis e (axis f 1) :: real^'n^'n))
        \<in> borel_measurable ?B"
      by (intro borel_measurable_inner borel_measurable_const
          measurable_compose[OF ev pair_snd_borel])
    then show ?thesis by (simp add: inner_axis)
  qed
  have Zm: "?Z u \<in> borel_measurable ?B" for u
  proof -
    have e: "?Z u = (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min u T)) $ c
        * fst (\<omega> (min u T)) $ d - snd (\<omega> (min u T)) $ c $ d)"
      by (rule ext) (rule comp_entry_eq)
    show ?thesis unfolding e
      by (intro borel_measurable_diff borel_measurable_times fem sem)
  qed
  have AR: "A \<in> sets ?R"
  proof -
    have "sets (natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) i)
        \<subseteq> sets ?R"
      by (rule sets_natural_filtration_subset)
         (rule pair_law_eval_measurable[OF setsR])
    then show ?thesis using A by blast
  qed
  have AB: "A \<in> sets ?B" using AR setsR by simp
  have hm: "(\<lambda>\<omega> :: 'n pairpath. indicator A \<omega> * ?Z u \<omega>) \<in> borel_measurable ?B"
    for u using AB Zm[of u] by measurable
  have tr: "set_lebesgue_integral ?R A (?Z u)
      = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
          * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
    if u0: "0 \<le> u" and uT: "u \<le> T" for u
  proof -
    have "set_lebesgue_integral ?R A (?Z u)
        = (\<integral>\<omega>. indicator A \<omega> * ?Z u \<omega> \<partial>?R)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator A (padd T p' w)
        * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
      by (rule integral_aglue_law
          [OF T0' PQ setsQ Kp hm hi[OF u0 uT] msec[OF u0 uT]])
    also have "\<dots> = (\<integral>p'. (\<integral>w. indicator B (pcut i (padd T p' w))
        * ?Z u (padd T p' w) \<partial>(\<kappa> p')) \<partial>Q)"
    proof (rule Bochner_Integration.integral_cong[OF refl])
      fix p' assume sp: "p' \<in> space Q"
      have pmem: "p' \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sp spQ by (simp add: space_borel_of)
      have setsK: "sets (\<kappa> p') = sets ?B" by (rule ksemi_sets_kernel(1)[OF Kp sp])
      have spK: "space (\<kappa> p') = space ?B"
        by (rule sets_eq_imp_space_eq[OF setsK])
      show "(\<integral>w. indicator A (padd T p' w) * ?Z u (padd T p' w) \<partial>(\<kappa> p'))
          = (\<integral>w. indicator B (pcut i (padd T p' w))
            * ?Z u (padd T p' w) \<partial>(\<kappa> p'))"
      proof (rule Bochner_Integration.integral_cong[OF refl])
        fix w assume sw: "w \<in> space (\<kappa> p')"
        have wmem: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
          using sw spK by (simp add: space_borel_of)
        have inR: "padd T p' w \<in> space ?R"
          unfolding spR using padd_mspace[OF pmem wmem]
          by (simp add: space_borel_of)
        have "indicator A (padd T p' w)
            = (indicator B (pcut i (padd T p' w)) :: real)"
          unfolding Aeq using inR by (simp add: indicator_def)
        then show "indicator A (padd T p' w) * ?Z u (padd T p' w)
            = indicator B (pcut i (padd T p' w)) * ?Z u (padd T p' w)"
          by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding tr[OF i0 iT] tr[OF j0 jT]
    by (rule aglue_inner_increment_comp
        [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint KintC
          Kinc KincC i0 ij iT jT B gint[OF _ _ B]])
qed

theorem aglue_law_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and QHC: "\<And>c d. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v c d. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and RCint: "\<And>u. 0 \<le> u \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    and msec: "\<And>A u c d. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gint: "\<And>u BB c d i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "martingale (aglue_law T \<kappa> Q)
      (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>v \<omega>. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?R = "aglue_law T \<kappa> Q"
  let ?G = "natural_filtration ?R 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
  let ?X = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))"
  have T0': "0 \<le> T" using T0 by simp
  have setsR: "sets ?R = sets ?B" by (rule sets_aglue_law)
  have PR: "prob_space ?R" by (rule prob_space_aglue_law[OF T0' PQ setsQ Kp])
  have fin: "finite_measure ?R" using PR by (simp add: prob_space_def)
  have SP: "Stochastic_Process.stochastic_process ?R (0::real)
      (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)"
    by unfold_locales (rule pair_law_eval_measurable[OF setsR])
  interpret SF: finite_filtered_measure ?R ?G 0
    by (rule Stochastic_Process.stochastic_process.finite_filtered_measure_natural_filtration[OF SP fin])
  have Xad: "?X u \<in> borel_measurable (?G u)" if u: "0 \<le> u" for u
  proof -
    have m: "min u T \<in> {0..u}" using u T0' by simp
    have Rb: "?G u = natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u"
      by (rule natural_filtration_cong_space
          [OF sets_eq_imp_space_eq[OF setsR]])
    have evu: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min u T)) \<in> borel_measurable (?G u)"
      unfolding Rb by (rule path_eval_measurable_natural_filtration'[OF m])
    have "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> (min u T))))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF evu measurable_compose
            [OF pair_fst_borel outerp_borel]])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> (min u T)))
        \<in> borel_measurable (?G u)"
      by (rule measurable_compose[OF evu pair_snd_borel])
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule SF.martingale_of_set_integral_eq)
    show "adapted_process ?R ?G 0 ?X"
      unfolding adapted_process_def adapted_process_axioms_def
      using SF.filtered_measure_axioms Xad by blast
    show "integrable ?R (?X u)" if "0 \<le> u" for u by (rule RCint[OF that])
    fix C and u v :: real
    assume uv: "0 \<le> u" "u \<le> v" and C: "C \<in> sets (?G u)"
    have v0: "0 \<le> v" using uv by simp
    have CR: "C \<in> sets ?R" using C SF.sets_F_subset[OF uv(1)] by blast
    have comp: "set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X u \<omega> $ c $ d)
        = set_lebesgue_integral ?R C (\<lambda>\<omega>. ?X v \<omega> $ c $ d)" for c d
    proof (cases "T \<le> u")
      case True
      then have "min u T = T" and "min v T = T" using uv by simp_all
      then show ?thesis by simp
    next
      case False
      then have uT: "u \<le> T" by simp
      have vT: "min v T \<le> T" by simp
      have uvT: "u \<le> min v T" using uv uT by simp
      have hiA: "integrable ?R (\<lambda>\<omega>. indicator C \<omega>
          * ((outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d))"
        if s: "0 \<le> s" for s
      proof -
        have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
          by (rule bounded_linear_compose[OF bounded_linear_vec_nth
              bounded_linear_vec_nth])
        have ii: "integrable ?R (\<lambda>\<omega> :: 'n pairpath.
            (outerp (fst (\<omega> (min s T))) - snd (\<omega> (min s T))) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl RCint[OF s]])
        show ?thesis using integrable_mult_indicator[OF CR ii] by simp
      qed
      have "set_lebesgue_integral ?R C
            (\<lambda>\<omega>. (outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T))) $ c $ d)
          = set_lebesgue_integral ?R C
            (\<lambda>\<omega>. (outerp (fst (\<omega> (min (min v T) T)))
                  - snd (\<omega> (min (min v T) T))) $ c $ d)"
        by (rule aglue_law_comp_increment
            [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint
              KintC Kinc KincC uv(1) uvT uT vT C hiA msec[OF CR]
              gint[OF _ _ _ uv(1) uT]])
      then show ?thesis by simp
    qed
    show "set_lebesgue_integral ?R C (?X u) = set_lebesgue_integral ?R C (?X v)"
    proof -
      have "set_lebesgue_integral ?R C (?X u) $ c $ d
          = set_lebesgue_integral ?R C (?X v) $ c $ d" for c d
        using comp[of c d]
        unfolding set_integral_mat_component[OF CR RCint[OF uv(1)]]
          set_integral_mat_component[OF CR RCint[OF v0]] .
      then show ?thesis by (simp add: vec_eq_iff)
    qed
  qed
qed

section \<open>The additive glue lands in the class\<close>

text \<open>All four clauses hold, with no martingale hypothesis left over.
  Clauses (i)--(iii) come from @{thm [source] exit_class_aglue_law};
  the two martingale clauses are @{thm [source] aglue_law_X_martingale} and
  @{thm [source] aglue_law_comp_martingale}.  The remaining hypotheses
  concern only the two factors --- the stopped past \<open>Q\<close> and the
  continuation kernel \<open>\<kappa>\<close> --- read off the class and the r.c.d. by a caller.\<close>

theorem exit_class_aglue:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Q0: "AE p' in Q. fst (p' 0) = x \<and> snd (p' 0) = 0"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and Qcov: "AE p' in Q. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> \<theta> p'
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (p' b) - snd (p' a)) \<in> sconstraint k L"
    and QH: "\<And>e. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ e) T"
    and QHC: "\<And>c d. horizon_sq_int_martingale Q
        (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ c $ d) T"
    and Qcont: "\<And>p'. p' \<in> space Q \<Longrightarrow> continuous_on {0..T} p'"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kcov: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'. \<forall>a b. \<theta> p' \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
        \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L"
    and Kmean: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. fst (w (min u T)) $ e \<partial>(\<kappa> p')) = 0"
    and KmeanC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
            \<partial>(\<kappa> p')) = 0"
    and Kint: "\<And>p' u e. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    and KintC: "\<And>p' u c d. p' \<in> space Q \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    and Kinc: "\<And>p' C u v e. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
        = set_lebesgue_integral (\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    and KincC: "\<And>p' C u v c d. p' \<in> space Q
      \<Longrightarrow> C \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>s w. w s) u)
      \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> T
      \<Longrightarrow> set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
        = set_lebesgue_integral (\<kappa> p') C
            (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    and RXint: "\<And>u. 0 \<le> u
      \<Longrightarrow> integrable (aglue_law T \<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
    and RCint: "\<And>u. 0 \<le> u \<Longrightarrow> integrable (aglue_law T \<kappa> Q)
        (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    and msecX: "\<And>A u e. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p')) \<in> borel_measurable Q"
    and msecC: "\<And>A u c d. A \<in> sets (aglue_law T \<kappa> Q) \<Longrightarrow> 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> (\<lambda>p'. \<integral>w. indicator A (padd T p' w)
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))
          \<in> borel_measurable Q"
    and gintX: "\<And>u BB e i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p'))"
    and gintC: "\<And>u BB c d i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * ((outerp (fst (padd T p' w (min u T)))
                - snd (padd T p' w (min u T))) $ c $ d) \<partial>(\<kappa> p'))"
  shows "aglue_law T \<kappa> Q \<in> exit_class k L T x"
proof -
  have T0': "0 \<le> T" using T0 by simp
  have QstAE: "AE p' in Q. pstopped T \<theta> p' = p'" by (rule Qst)
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  \<comment> \<open>\<open>K0\<close> is redundant: it is \<open>Kfr\<close> at \<open>u = 0\<close>.  Asking for it POINTWISE on
      \<open>space (\<kappa> p')\<close> --- as an earlier version did --- is unsatisfiable by any
      delayed law, since that space is every continuous path.\<close>
  have K0AE: "AE w in \<kappa> p'. w 0 = 0" if sp: "p' \<in> space Q" for p'
    using Kfr[OF sp]
  proof (rule eventually_mono)
    fix w :: "'n pairpath"
    assume "\<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    then show "w 0 = 0" using T0' th0[of p'] by simp
  qed
  have KfrAE: "AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    if sp: "p' \<in> space Q" for p' by (rule Kfr[OF sp])
  show ?thesis
  proof (rule exit_class_aglue_law
      [OF T0' PQ setsQ Kp st Q0 QstAE Qcov K0AE KfrAE Kcov])
    show "martingale (aglue_law T \<kappa> Q)
        (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. fst (\<omega> (min t T)))"
      by (rule aglue_law_X_martingale
          [OF T0 PQ setsQ Kp st thM Qst QH Qcont Kfr Kmean Kint Kinc
            RXint msecX gintX])
    show "martingale (aglue_law T \<kappa> Q)
        (natural_filtration (aglue_law T \<kappa> Q) 0 (\<lambda>t \<omega>. \<omega> t)) 0
        (\<lambda>t \<omega>. outerp (fst (\<omega> (min t T))) - snd (\<omega> (min t T)))"
      by (rule aglue_law_comp_martingale
          [OF T0 PQ setsQ Kp st thM Qst QHC Qcont Kfr Kmean KmeanC Kint KintC
            Kinc KincC RCint msecC gintC])
  qed
qed


(*<*)
end
(*>*)
