section \<open>The additive glue and its clauses\<close>

(*<*)
theory Dynamic_Programming_Additive_Glue
  imports Dynamic_Programming_Stopping_Clauses
    "Continuous_Time_Martingales.Integrability_Criteria"
    Path_Law_Sampling
begin

(*>*)

section \<open>The additive glue\<close>

















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
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
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
  let ?B = "(path_borel T :: ('n pairpath) measure)"
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



theorem exit_class_aglue_law:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
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
  show "sets (aglue_law T \<kappa> Q) = sets (path_borel T :: ('n pairpath) measure)"
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











theorem exit_class_aglue:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
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
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
      \<Longrightarrow> 0 \<le> i \<Longrightarrow> i \<le> T \<Longrightarrow> integrable Q
        (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
            * (fst (padd T p' w (min u T)) $ e) \<partial>(\<kappa> p'))"
    and gintC: "\<And>u BB c d i. 0 \<le> u \<Longrightarrow> u \<le> T
      \<Longrightarrow> BB \<in> sets (path_borel i :: ('n pairpath) measure)
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
