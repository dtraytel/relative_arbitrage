section \<open>The pathwise bound, the exit bound, and the \<open>\<ge>\<close> half\<close>

(*<*)
theory Dynamic_Programming_Assembly
  imports Dynamic_Programming_Delayed_Class
    "Continuous_Time_Martingales.Integrability_Criteria"
begin

(*>*)

section \<open>The pathwise DPP bound for the additive glue\<close>

text \<open>The stopping-time analogue of @{thm [source] pexit_pglue_dpp}.  Because
  \<^const>\<open>padd\<close> keeps both factors on the original clock, the
  continuation's contribution is stated as a bound on \<open>pexit T K\<close> of the
  delayed path \<open>s \<mapsto> fst (p' r) + fst (w s)\<close> --- already including the
  \<open>r\<close> it stands still for --- rather than on a rebased horizon, exactly
  the form \<^const>\<open>pdelclass\<close> produces.\<close>

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

theorem aglue_law_pexit_ge:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes T0: "0 \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kp: "\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Kc: "closed K" and L1: "1 \<le> L"
    and st: "path_stopping_time T \<theta>"
    and Qst: "AE p' in Q. pstopped T \<theta> p' = p'"
    and Qbnd: "AE p' in Q. c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
        + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
           then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)"
    and Kfr: "\<And>p'. p' \<in> space Q
      \<Longrightarrow> AE w in \<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0"
    and Kval: "\<And>p'. p' \<in> space Q \<Longrightarrow> AE w in \<kappa> p'.
        enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p'))))
          \<le> pexit (T - \<theta> p') K
              (\<lambda>u. fst (p' (\<theta> p')) + fst (prebase (\<theta> p') T w u))"
  shows "AE \<omega> in aglue_law T \<kappa> Q. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?B"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. pexit T K (pfst T \<omega>)) \<in> borel_measurable ?B"
      by (rule measurable_compose[OF pfst_measurable[OF T0 refl]
            pexit_measurable[OF T0 Kc]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  have mset: "{\<omega> \<in> space ?B. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))} \<in> sets ?B"
    using taum by measurable
  have inner: "AE w in \<kappa> p'. c \<le> pexit T K (\<lambda>t. fst (padd T p' w t))"
    if sp: "p' \<in> space Q" and idem: "pstopped T \<theta> p' = p'"
      and bnd: "c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
        + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
           then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)"
    for p'
  proof -
    let ?r = "\<theta> p'"
    let ?y = "fst (p' ?r)"
    let ?c = "enn2real (exit_val k L (T - ?r) K ?y)"
    have r0: "0 \<le> ?r" by (rule th0)
    have rT: "?r \<le> T" by (rule thT)
    have Tr: "0 \<le> T - ?r" using rT by simp
    have c0: "0 \<le> ?c" by simp
    have cle: "?c \<le> T - ?r"
    proof -
      have "ennreal ?c = exit_val k L (T - ?r) K ?y"
        using exit_val_neq_top[of "T - ?r" k L K ?y] Tr by (simp add: less_top)
      also have "\<dots> \<le> ennreal (T - ?r)" by (rule exit_val_le_T[OF Tr])
      finally show ?thesis using Tr by simp
    qed
    have stop: "p' t = p' ?r" if t: "t \<in> {0..T}" and rt: "?r \<le> t" for t
    proof -
      have "p' t = pstopped T \<theta> p' t" unfolding idem ..
      also have "\<dots> = p' (min t ?r)" by (rule pstopped_apply[OF t])
      also have "min t ?r = ?r" using rt by simp
      finally show ?thesis .
    qed
    show ?thesis using Kfr[OF sp] Kval[OF sp]
    proof eventually_elim
      case (elim w)
      then have frz: "\<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> ?r \<longrightarrow> w u = 0"
        and val: "?c \<le> pexit (T - ?r) K (\<lambda>u. ?y + fst (prebase ?r T w u))"
        by blast+
      have cont: "?r + ?c \<le> pexit T K (\<lambda>s. ?y + fst (w s))"
        if "pexit ?r K (\<lambda>t. fst (p' t)) = ?r" and inK: "?y \<in> K"
      proof -
        have "?r + ?c \<le> ?r + pexit (T - ?r) K (\<lambda>u. ?y + fst (prebase ?r T w u))"
          using val by simp
        also have "\<dots> \<le> pexit T K (\<lambda>s. ?y + fst (w s))"
          by (rule pexit_delayed_rebase[OF r0 rT _ inK]) (use frz in blast)
        finally show ?thesis .
      qed
      have "pexit ?r K (\<lambda>t. fst (p' t))
            + (if pexit ?r K (\<lambda>t. fst (p' t)) = ?r \<and> ?y \<in> K then ?c else 0)
          \<le> pexit T K (\<lambda>t. fst (padd T p' w t))"
      proof (rule pexit_padd_dpp[OF r0 rT c0])
        show "?r + ?c \<le> T" using cle by simp
        show "p' t = p' ?r" if "t \<in> {0..T}" "?r \<le> t" for t
          by (rule stop[OF that])
        show "w t = 0" if "t \<in> {0..T}" "t \<le> ?r" for t using frz that by blast
        show "pexit ?r K (\<lambda>t. fst (p' t)) = ?r \<Longrightarrow> ?y \<in> K
            \<Longrightarrow> ?r + ?c \<le> pexit T K (\<lambda>s. ?y + fst (w s))" by (rule cont)
      qed
      with bnd show ?case by linarith
    qed
  qed
  have "AE p' in Q. AE w in \<kappa> p'. c \<le> pexit T K (\<lambda>t. fst (padd T p' w t))"
    using AE_space Qst Qbnd
  proof eventually_elim
    case (elim p')
    then show ?case using inner by blast
  qed
  then show ?thesis
    unfolding AE_aglue_law[OF T0 PQ setsQ Kp mset] .
qed

text \<open>What the selector delivers, in the form @{thm [source] aglue_law_pexit_ge}
  consumes: its optimality is an \<^const>\<open>ess_inf_time\<close> equality, and
  @{thm [source] ess_inf_time_AE} turns the \<open>\<ge>\<close> direction of that into the
  almost-sure bound, once the \<^const>\<open>pshift_law\<close> and \<^const>\<open>prebase\<close>
  layers are peeled off.\<close>

lemma selector_value_AE:
  fixes \<nu> :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes s0: "0 \<le> s" and sT: "s \<le> T" and Kc: "closed K"
    and Pnu: "prob_space \<nu>"
    and setsnu: "sets \<nu> = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and val: "ess_inf_time (pshift_law (T - s) y
          (distr \<nu> (borel_of (mtopology_of
            (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)))
          (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t)))
        = exit_val k L (T - s) K y"
  shows "AE w in \<nu>. enn2real (exit_val k L (T - s) K y)
      \<le> pexit (T - s) K (\<lambda>u. y + fst (prebase s T w u))"
proof -
  let ?Bs = "borel_of (mtopology_of
      (path_metric (T - s) :: ('n pairpath) metric))"
  let ?\<mu> = "distr \<nu> ?Bs (prebase s T)"
  let ?v = "exit_val k L (T - s) K y"
  have Ts: "0 \<le> T - s" using sT by simp
  have reb: "prebase s T \<in> \<nu> \<rightarrow>\<^sub>M ?Bs"
    unfolding measurable_cong_sets[OF setsnu refl]
    by (rule prebase_measurable[OF s0 sT])
  have setsmu: "sets ?\<mu> = sets ?Bs" by simp
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit (T - s) K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?Bs"
  proof -
    have "(\<lambda>\<omega> :: 'n pairpath. pexit (T - s) K (pfst (T - s) \<omega>))
        \<in> borel_measurable ?Bs"
      by (rule measurable_compose[OF pfst_measurable[OF Ts refl]
            pexit_measurable[OF Ts Kc]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  have mset: "{\<omega> \<in> space ?Bs.
      ?v \<le> ennreal (pexit (T - s) K (\<lambda>t. y + fst (\<omega> t)))} \<in> sets ?Bs"
  proof -
    have sh: "(\<lambda>\<omega> :: 'n pairpath. pexit (T - s) K (\<lambda>t. y + fst (\<omega> t)))
        \<in> borel_measurable ?Bs"
    proof -
      have shm: "pshift (T - s) y \<in> ?Bs \<rightarrow>\<^sub>M ?Bs"
        by (rule pshift_measurable[OF Ts])
      have "(\<lambda>\<omega> :: 'n pairpath.
          pexit (T - s) K (\<lambda>t. fst (pshift (T - s) y \<omega> t)))
          \<in> borel_measurable ?Bs"
        by (rule measurable_compose[OF shm taum])
      moreover have "pexit (T - s) K (\<lambda>t. fst (pshift (T - s) y \<omega> t))
          = pexit (T - s) K (\<lambda>t. y + fst (\<omega> t))" for \<omega> :: "'n pairpath"
        by (rule pexit_cong_on) (simp add: pshift_fst)
      ultimately show ?thesis by simp
    qed
    show ?thesis using sh by measurable
  qed
  \<comment> \<open>the optimality, as an almost-sure bound on the SHIFTED law\<close>
  have ae1: "AE \<omega> in pshift_law (T - s) y ?\<mu>.
      ?v \<le> ennreal (pexit (T - s) K (\<lambda>t. fst (\<omega> t)))"
    unfolding val[symmetric] by (rule ess_inf_time_AE)
  have ae2: "AE \<omega> in ?\<mu>.
      ?v \<le> ennreal (pexit (T - s) K (\<lambda>t. y + fst (\<omega> t)))"
  proof -
    have "AE \<omega> in ?\<mu>.
        ?v \<le> ennreal (pexit (T - s) K (\<lambda>t. fst (pshift (T - s) y \<omega> t)))"
      using ae1 unfolding AE_pshift_law_iff[OF Ts setsmu] .
    then show ?thesis
    proof (rule eventually_mono)
      fix \<omega> :: "'n pairpath"
      assume h: "?v \<le> ennreal (pexit (T - s) K
          (\<lambda>t. fst (pshift (T - s) y \<omega> t)))"
      have "pexit (T - s) K (\<lambda>t. fst (pshift (T - s) y \<omega> t))
          = pexit (T - s) K (\<lambda>t. y + fst (\<omega> t))"
        by (rule pexit_cong_on) (simp add: pshift_fst)
      with h show "?v \<le> ennreal (pexit (T - s) K (\<lambda>t. y + fst (\<omega> t)))"
        by simp
    qed
  qed
  have ae3: "AE w in \<nu>. ?v
      \<le> ennreal (pexit (T - s) K (\<lambda>u. y + fst (prebase s T w u)))"
    using ae2 unfolding AE_distr_iff[OF reb mset] .
  show ?thesis using ae3
  proof (rule eventually_mono)
    fix w :: "'n pairpath"
    assume h: "?v \<le> ennreal (pexit (T - s) K (\<lambda>u. y + fst (prebase s T w u)))"
    have fin: "?v \<noteq> \<top>" by (rule exit_val_neq_top[OF Ts])
    have nn: "0 \<le> pexit (T - s) K (\<lambda>u. y + fst (prebase s T w u))"
      by (rule pexit_nonneg[OF Ts])
    have "enn2real ?v
        \<le> enn2real (ennreal (pexit (T - s) K (\<lambda>u. y + fst (prebase s T w u))))"
      by (rule enn2real_mono[OF h]) simp
    then show "enn2real ?v
        \<le> pexit (T - s) K (\<lambda>u. y + fst (prebase s T w u))" using nn by simp
  qed
qed

text \<open>The continuation kernel itself: read the freezing time and the
  starting point off the stopped path and hand both to the selector.  Its
  measurability is the only place the horizon-parametrised selector's
  \<^emph>\<open>joint\<close> measurability is used --- the pair \<open>(\<theta> p', X_(\<theta> p'))\<close> is a
  single measurable function of the past, the second component by
  @{thm [source] path_eval_at_measurable_time}.\<close>

definition selker ::
  "(real \<times> (real^'n::finite) \<Rightarrow> ('n pairpath) measure)
     \<Rightarrow> (('n pairpath) \<Rightarrow> real) \<Rightarrow> ('n pairpath) \<Rightarrow> ('n pairpath) measure"
  where "selker Sel \<theta> p' = Sel (\<theta> p', fst (p' (\<theta> p')))"

lemma selker_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and Sm: "Sel \<in> (borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
  shows "selker Sel \<theta> \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have thQ: "\<theta> \<in> borel_measurable Q"
    using thM measurable_cong_sets[OF setsQ refl] by blast
  have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> Q \<rightarrow>\<^sub>M ?B"
    by (rule measurable_ident_sets[OF setsQ])
  have ev: "(\<lambda>p' :: 'n pairpath. p' (\<theta> p')) \<in> borel_measurable Q"
    by (rule path_eval_at_measurable_time
        [where X = "\<lambda>p' :: 'n pairpath. p'" and g = \<theta>, OF T0 idm thQ])
       (use th0 thT in auto)
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have xm: "(\<lambda>p' :: 'n pairpath. fst (p' (\<theta> p'))) \<in> borel_measurable Q"
    by (rule measurable_compose[OF ev fstB])
  have pm: "(\<lambda>p' :: 'n pairpath. (\<theta> p', fst (p' (\<theta> p'))))
      \<in> Q \<rightarrow>\<^sub>M (borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)"
    by (rule measurable_Pair[OF thQ xm])
  show ?thesis
    unfolding selker_def by (rule measurable_compose[OF pm Sm])
qed

section \<open>The additive glue with the selector kernel\<close>

text \<open>Every kernel hypothesis of @{thm [source] exit_class_aglue} is a
  one-line application of a \<open>pdelclass_\<close> lemma, and every side condition
  an application of the \<open>aglue_\<close> family, with the uniform constants
  supplied by @{thm [source] pdelclass_norm_mean_le} and
  @{thm [source] pdelclass_comp_norm_mean_le}.  What remains as a
  hypothesis concerns the past factor alone.\<close>

theorem exit_class_aglue_selector:
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
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
    and QXint: "\<And>u. 0 \<le> u \<Longrightarrow> integrable Q (\<lambda>p'. fst (p' (min u T)))"
    and QCint: "\<And>u. 0 \<le> u \<Longrightarrow> integrable Q
        (\<lambda>p'. outerp (fst (p' (min u T))) - snd (p' (min u T)))"
    and Sc: "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> Sel (s, y) \<in> pdelclass k L T s"
    and Sm: "Sel \<in> (borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))"
  shows "aglue_law T (selker Sel \<theta>) Q \<in> exit_class k L T x"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?\<kappa> = "selker Sel \<theta>"
  let ?CX = "1 + real CARD('n) * (real CARD('n) * L * T)"
  let ?CC = "real CARD('n) * (real CARD('n) * L * T) + real CARD('n) * L * T"
  have T0': "0 \<le> T" using T0 by simp
  have L0: "0 \<le> L" using L1 by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have Kp: "?\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra ?B"
    by (rule selker_measurable[OF T0' setsQ st thM Sm])
  have Kmem: "?\<kappa> p' \<in> pdelclass k L T (\<theta> p')" for p'
    unfolding selker_def by (rule Sc[OF th0 thT])
  have tm: "min u T \<in> {0..T}" if "0 \<le> u" for u using that T0' by simp
  interpret PQ': prob_space Q by (rule PQ)

  \<comment> \<open>the nine kernel clauses\<close>
  have Kfr: "AE w in ?\<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0" for p'
    by (rule pdelclass_frozen[OF th0 thT Kmem])
  have Kcov: "AE w in ?\<kappa> p'. \<forall>a b. \<theta> p' \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T
      \<longrightarrow> (1 / (b - a)) *\<^sub>R (snd (w b) - snd (w a)) \<in> sconstraint k L" for p'
    by (rule pdelclass_diffquot[OF th0 thT Kmem])
  have KmgX: "martingale (?\<kappa> p') (natural_filtration (?\<kappa> p') 0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. fst (w (min u T)))" for p'
    by (rule pdelclass_X_martingale[OF th0 thT Kmem])
  have KmgC: "martingale (?\<kappa> p') (natural_filtration (?\<kappa> p') 0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. outerp (fst (w (min u T))) - snd (w (min u T)))" for p'
    by (rule pdelclass_comp_martingale[OF th0 thT Kmem])
  have KXvec: "integrable (?\<kappa> p') (\<lambda>w. fst (w (min u T)))"
    if u: "0 \<le> u" for p' u by (rule martingale.integrable[OF KmgX u])
  have KCmat: "integrable (?\<kappa> p')
      (\<lambda>w. outerp (fst (w (min u T))) - snd (w (min u T)))"
    if u: "0 \<le> u" for p' u by (rule martingale.integrable[OF KmgC u])
  have KXbnd: "(\<integral>w. norm (fst (w (min u T))) \<partial>(?\<kappa> p')) \<le> ?CX"
    if u: "0 \<le> u" for p' u
    by (rule pdelclass_norm_mean_le[OF L0 th0 thT Kmem tm[OF u]])
  have KCbnd: "(\<integral>w. norm (outerp (fst (w (min u T))) - snd (w (min u T)))
      \<partial>(?\<kappa> p')) \<le> ?CC" if u: "0 \<le> u" for p' u
    by (rule pdelclass_comp_norm_mean_le[OF L0 th0 thT Kmem tm[OF u]])

  \<comment> \<open>\<open>RXint\<close> and \<open>RCint\<close>\<close>
  have RXint: "integrable (aglue_law T ?\<kappa> Q) (\<lambda>\<omega>. fst (\<omega> (min u T)))"
    if u: "0 \<le> u" for u
    by (rule aglue_law_X_integrable
        [OF T0' PQ setsQ Kp u QXint[OF u] KXvec[OF u] KXbnd[OF u]])
  have RCint: "integrable (aglue_law T ?\<kappa> Q)
      (\<lambda>\<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    if u: "0 \<le> u" for u
    by (rule aglue_law_comp_integrable
        [OF T0' PQ setsQ Kp u QXint[OF u] QCint[OF u] KXvec[OF u]
          KCmat[OF u] KXbnd[OF u] KCbnd[OF u]])
  \<comment> \<open>the glued integrands, split by @{thm [source] padd_eval_split}\<close>
  have KXpadd: "integrable (?\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
    if sp: "p' \<in> space Q" and u: "0 \<le> u" for p' u e
  proof -
    interpret PK: prob_space "?\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    have i: "integrable (?\<kappa> p')
        (\<lambda>w. fst (p' (min u T)) $ e + fst (w (min u T)) $ e)"
      by (intro Bochner_Integration.integrable_add PK.integrable_const
          pdelclass_X_int[OF th0 thT Kmem u])
    have e: "(\<lambda>w :: 'n pairpath. fst (padd T p' w (min u T)) $ e)
        = (\<lambda>w. fst (p' (min u T)) $ e + fst (w (min u T)) $ e)"
      by (rule ext) (simp add: padd_eval_split(1)[OF tm[OF u]])
    show ?thesis unfolding e by (rule i)
  qed
  have KCpadd: "integrable (?\<kappa> p') (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
      - snd (padd T p' w (min u T))) $ c $ d)"
    if sp: "p' \<in> space Q" and u: "0 \<le> u" for p' u c d
  proof -
    interpret PK: prob_space "?\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    let ?t = "min u T"
    have iC: "integrable (?\<kappa> p') (\<lambda>w. (outerp (fst (w ?t)) - snd (w ?t)) $ c $ d)"
      by (rule pdelclass_comp_int[OF th0 thT Kmem u])
    have iX: "integrable (?\<kappa> p') (\<lambda>w. fst (w ?t) $ c)"
      by (rule pdelclass_X_int[OF th0 thT Kmem u])
    have iY: "integrable (?\<kappa> p') (\<lambda>w. fst (w ?t) $ d)"
      by (rule pdelclass_X_int[OF th0 thT Kmem u])
    have i: "integrable (?\<kappa> p')
        (\<lambda>w. ((outerp (fst (p' ?t)) - snd (p' ?t)) $ c $ d
              + (outerp (fst (w ?t)) - snd (w ?t)) $ c $ d)
            + (fst (p' ?t) $ c * fst (w ?t) $ d
              + fst (w ?t) $ c * fst (p' ?t) $ d))"
      by (intro Bochner_Integration.integrable_add PK.integrable_const iC
          integrable_mult_left iY integrable_mult_right iX)
    have e: "(\<lambda>w :: 'n pairpath. (outerp (fst (padd T p' w ?t))
          - snd (padd T p' w ?t)) $ c $ d)
        = (\<lambda>w. ((outerp (fst (p' ?t)) - snd (p' ?t)) $ c $ d
              + (outerp (fst (w ?t)) - snd (w ?t)) $ c $ d)
            + (fst (p' ?t) $ c * fst (w ?t) $ d
              + fst (w ?t) $ c * fst (p' ?t) $ d))"
      by (rule ext)
         (simp add: padd_eval_split(1)[OF tm[OF u]]
            padd_eval_split(2)[OF tm[OF u]] outerp_add algebra_simps)
    show ?thesis unfolding e by (rule i)
  qed
  have KXabnd: "(\<integral>w. \<bar>fst (padd T p' w (min u T)) $ e\<bar> \<partial>(?\<kappa> p'))
      \<le> \<bar>fst (p' (min u T)) $ e\<bar> + ?CX"
    if sp: "p' \<in> space Q" and u: "0 \<le> u" for p' u e
  proof -
    interpret PK: prob_space "?\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    let ?t = "min u T"
    have iN: "integrable (?\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXvec[OF u]])
    have iS: "integrable (?\<kappa> p')
        (\<lambda>w. \<bar>fst (p' ?t) $ e\<bar> + norm (fst (w ?t)))"
      by (intro Bochner_Integration.integrable_add PK.integrable_const iN)
    have iP: "integrable (?\<kappa> p') (\<lambda>w. \<bar>fst (padd T p' w ?t) $ e\<bar>)"
      using KXpadd[OF sp u] by simp
    have dom: "\<bar>fst (padd T p' w ?t) $ e\<bar>
        \<le> \<bar>fst (p' ?t) $ e\<bar> + norm (fst (w ?t))" for w :: "'n pairpath"
    proof -
      have "\<bar>fst (padd T p' w ?t) $ e\<bar>
          = \<bar>fst (p' ?t) $ e + fst (w ?t) $ e\<bar>"
        by (simp add: padd_eval_split(1)[OF tm[OF u]])
      also have "\<dots> \<le> \<bar>fst (p' ?t) $ e\<bar> + \<bar>fst (w ?t) $ e\<bar>" by simp
      moreover have "\<bar>fst (w ?t) $ e\<bar> \<le> norm (fst (w ?t))"
        using Finite_Cartesian_Product.norm_nth_le[of "fst (w ?t)" e] by simp
      ultimately show ?thesis by linarith
    qed
    have "(\<integral>w. \<bar>fst (padd T p' w ?t) $ e\<bar> \<partial>(?\<kappa> p'))
        \<le> (\<integral>w. \<bar>fst (p' ?t) $ e\<bar> + norm (fst (w ?t)) \<partial>(?\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono[OF iP iS]) (use dom in simp)
    also have "\<dots> = \<bar>fst (p' ?t) $ e\<bar> + (\<integral>w. norm (fst (w ?t)) \<partial>(?\<kappa> p'))"
      using Bochner_Integration.integral_add[OF PK.integrable_const iN]
      by (simp add: PK.prob_space)
    also have "\<dots> \<le> \<bar>fst (p' ?t) $ e\<bar> + ?CX" using KXbnd[OF u] by simp
    finally show ?thesis .
  qed
  have KCabnd: "(\<integral>w. \<bar>(outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d\<bar> \<partial>(?\<kappa> p'))
      \<le> norm (outerp (fst (p' (min u T))) - snd (p' (min u T)))
        + (?CC + 2 * (norm (fst (p' (min u T))) * ?CX))"
    if sp: "p' \<in> space Q" and u: "0 \<le> u" for p' u c d
  proof -
    interpret PK: prob_space "?\<kappa> p'" by (rule ksemi_sets_kernel(2)[OF Kp sp])
    let ?t = "min u T"
    let ?C = "\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> ?t)) - snd (\<omega> ?t)"
    have iNC: "integrable (?\<kappa> p') (\<lambda>w. norm (?C w))"
      by (rule integrable_norm[OF KCmat[OF u]])
    have iNX: "integrable (?\<kappa> p') (\<lambda>w. norm (fst (w ?t)))"
      by (rule integrable_norm[OF KXvec[OF u]])
    have iS: "integrable (?\<kappa> p') (\<lambda>w. norm (?C p') + norm (?C w)
        + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))))"
      by (intro Bochner_Integration.integrable_add PK.integrable_const iNC
          Bochner_Integration.integrable_mult_right integrable_mult_left iNX)
    have iP: "integrable (?\<kappa> p') (\<lambda>w. \<bar>?C (padd T p' w) $ c $ d\<bar>)"
      using KCpadd[OF sp u] by simp
    have dom: "\<bar>?C (padd T p' w) $ c $ d\<bar> \<le> norm (?C p') + norm (?C w)
        + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t)))" for w :: "'n pairpath"
    proof -
      have "\<bar>?C (padd T p' w) $ c $ d\<bar> \<le> norm (?C (padd T p' w) $ c)"
        using Finite_Cartesian_Product.norm_nth_le
          [of "?C (padd T p' w) $ c" d] by simp
      also have "\<dots> \<le> norm (?C (padd T p' w))"
        by (rule Finite_Cartesian_Product.norm_nth_le)
      also have "\<dots> \<le> norm (?C p') + norm (?C w)
          + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t)))"
        by (rule padd_comp_norm_le[OF tm[OF u]])
      finally show ?thesis .
    qed
    have "(\<integral>w. \<bar>?C (padd T p' w) $ c $ d\<bar> \<partial>(?\<kappa> p'))
        \<le> (\<integral>w. norm (?C p') + norm (?C w)
            + 2 * (norm (fst (p' ?t)) * norm (fst (w ?t))) \<partial>(?\<kappa> p'))"
      by (rule Bochner_Integration.integral_mono[OF iP iS]) (use dom in simp)
    also have "\<dots> = norm (?C p') + (\<integral>w. norm (?C w) \<partial>(?\<kappa> p'))
        + 2 * (norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(?\<kappa> p')))"
      using iNC iNX PK.integrable_const
      by (simp add: PK.prob_space algebra_simps)
    also have "\<dots> \<le> norm (?C p') + (?CC + 2 * (norm (fst (p' ?t)) * ?CX))"
    proof -
      have b1: "(\<integral>w. norm (?C w) \<partial>(?\<kappa> p')) \<le> ?CC" by (rule KCbnd[OF u])
      have b2: "norm (fst (p' ?t)) * (\<integral>w. norm (fst (w ?t)) \<partial>(?\<kappa> p'))
          \<le> norm (fst (p' ?t)) * ?CX"
        by (rule mult_left_mono[OF KXbnd[OF u] norm_ge_zero])
      from b1 b2 show ?thesis by linarith
    qed
    finally show ?thesis .
  qed

  \<comment> \<open>the four indicator-carrying side conditions\<close>
  have QXabs: "integrable Q (\<lambda>p'. \<bar>fst (p' (min u T)) $ e\<bar> + ?CX)"
    if u: "0 \<le> u" for u e
  proof -
    have "integrable Q (\<lambda>p'. fst (p' (min u T)) $ e)"
      by (rule integrable_bounded_linear
          [OF bounded_linear_vec_nth QXint[OF u]])
    then show ?thesis
      by (intro Bochner_Integration.integrable_add PQ'.integrable_const) simp
  qed
  have QCabs: "integrable Q (\<lambda>p'.
      norm (outerp (fst (p' (min u T))) - snd (p' (min u T)))
        + (?CC + 2 * (norm (fst (p' (min u T))) * ?CX)))"
    if u: "0 \<le> u" for u
  proof -
    have b: "integrable Q (\<lambda>p'. norm (fst (p' (min u T))))"
      by (rule integrable_norm[OF QXint[OF u]])
    show ?thesis
      by (intro Bochner_Integration.integrable_add PQ'.integrable_const
          integrable_norm[OF QCint[OF u]]
          integrable_mult_left Bochner_Integration.integrable_mult_right b)
  qed
  have msecX: "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
        * (fst (padd T p' w (min u T)) $ e) \<partial>(?\<kappa> p')) \<in> borel_measurable Q"
    if A: "A \<in> sets (aglue_law T ?\<kappa> Q)" and u: "0 \<le> u" and uT: "u \<le> T"
    for A u e
    by (rule aglue_msec_X[OF T0' setsQ Kp A]) (rule KXpadd[OF _ u])
  have msecC: "(\<lambda>p'. \<integral>w. indicator A (padd T p' w)
        * ((outerp (fst (padd T p' w (min u T)))
            - snd (padd T p' w (min u T))) $ c $ d) \<partial>(?\<kappa> p'))
      \<in> borel_measurable Q"
    if A: "A \<in> sets (aglue_law T ?\<kappa> Q)" and u: "0 \<le> u" and uT: "u \<le> T"
    for A u c d
    by (rule aglue_msec_C[OF T0' setsQ Kp A]) (rule KCpadd[OF _ u])
  have gintX: "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
        * (fst (padd T p' w (min u T)) $ e) \<partial>(?\<kappa> p'))"
    if u: "0 \<le> u" and uT: "u \<le> T"
      and BB: "BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))"
      and i0: "0 \<le> i" and iT: "i \<le> T" for u BB e i
  proof (rule aglue_gint_X[OF T0' setsQ Kp i0 iT BB _ QXabs[of u e, OF u]])
    show "integrable (?\<kappa> p') (\<lambda>w. fst (padd T p' w (min u T)) $ e)"
      if "p' \<in> space Q" for p' by (rule KXpadd[OF that u])
    show "(\<integral>w. \<bar>fst (padd T p' w (min u T)) $ e\<bar> \<partial>(?\<kappa> p'))
        \<le> \<bar>fst (p' (min u T)) $ e\<bar> + ?CX" if "p' \<in> space Q" for p'
      by (rule KXabnd[OF that u])
  qed
  have gintC: "integrable Q (\<lambda>p'. \<integral>w. indicator BB (pcut i (padd T p' w))
        * ((outerp (fst (padd T p' w (min u T)))
            - snd (padd T p' w (min u T))) $ c $ d) \<partial>(?\<kappa> p'))"
    if u: "0 \<le> u" and uT: "u \<le> T"
      and BB: "BB \<in> sets (borel_of (mtopology_of
          (path_metric i :: ('n pairpath) metric)))"
      and i0: "0 \<le> i" and iT: "i \<le> T" for u BB c d i
  proof (rule aglue_gint_C[OF T0' setsQ Kp i0 iT BB _ QCabs[of u, OF u]])
    show "integrable (?\<kappa> p') (\<lambda>w. (outerp (fst (padd T p' w (min u T)))
        - snd (padd T p' w (min u T))) $ c $ d)"
      if "p' \<in> space Q" for p' by (rule KCpadd[OF that u])
    show "(\<integral>w. \<bar>(outerp (fst (padd T p' w (min u T)))
          - snd (padd T p' w (min u T))) $ c $ d\<bar> \<partial>(?\<kappa> p'))
        \<le> norm (outerp (fst (p' (min u T))) - snd (p' (min u T)))
          + (?CC + 2 * (norm (fst (p' (min u T))) * ?CX))"
      if "p' \<in> space Q" for p' by (rule KCabnd[OF that u])
  qed

  have Kmean: "(\<integral>w. fst (w (min u T)) $ e \<partial>(?\<kappa> p')) = 0"
    if "p' \<in> space Q" and u: "0 \<le> u" and "u \<le> T" for p' u e
    by (rule pdelclass_X_mean[OF th0 thT Kmem u])
  have KmeanC: "(\<integral>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d
      \<partial>(?\<kappa> p')) = 0" if "p' \<in> space Q" and u: "0 \<le> u" and "u \<le> T" for p' u c d
    by (rule pdelclass_comp_mean[OF th0 thT Kmem u])
  have Kint: "integrable (?\<kappa> p') (\<lambda>w. fst (w (min u T)) $ e)"
    if "p' \<in> space Q" and u: "0 \<le> u" and "u \<le> T" for p' u e
    by (rule pdelclass_X_int[OF th0 thT Kmem u])
  have KintC: "integrable (?\<kappa> p')
      (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)"
    if "p' \<in> space Q" and u: "0 \<le> u" and "u \<le> T" for p' u c d
    by (rule pdelclass_comp_int[OF th0 thT Kmem u])
  have Kinc: "set_lebesgue_integral (?\<kappa> p') C (\<lambda>w. fst (w (min u T)) $ e)
      = set_lebesgue_integral (?\<kappa> p') C (\<lambda>w. fst (w (min v T)) $ e)"
    if "p' \<in> space Q"
      and C: "C \<in> sets (natural_filtration (?\<kappa> p') 0 (\<lambda>s w. w s) u)"
      and u: "0 \<le> u" and uv: "u \<le> v" and "v \<le> T" for p' C u v e
    by (rule pdelclass_X_increment[OF th0 thT Kmem C u uv])
  have KincC: "set_lebesgue_integral (?\<kappa> p') C
        (\<lambda>w. (outerp (fst (w (min u T))) - snd (w (min u T))) $ c $ d)
      = set_lebesgue_integral (?\<kappa> p') C
        (\<lambda>w. (outerp (fst (w (min v T))) - snd (w (min v T))) $ c $ d)"
    if "p' \<in> space Q"
      and C: "C \<in> sets (natural_filtration (?\<kappa> p') 0 (\<lambda>s w. w s) u)"
      and u: "0 \<le> u" and uv: "u \<le> v" and "v \<le> T" for p' C u v c d
    by (rule pdelclass_comp_increment[OF th0 thT Kmem C u uv])
  show ?thesis
    by (rule exit_class_aglue
        [OF T0 PQ setsQ Kp st thM Q0 Qst Qcov QH QHC Qcont Kfr Kcov
          Kmean KmeanC Kint KintC Kinc KincC RXint RCint
          msecX msecC gintX gintC])
qed

section \<open>The \<open>\<ge>\<close> half at a stopping time\<close>

text \<open>Assembly.  The competitor is the additive glue of the stopped past and
  the selector's continuation; it lies in the class by
  @{thm [source] exit_class_aglue_selector}, its exit time dominates
  \<open>c\<close> by @{thm [source] aglue_law_pexit_ge}, and the value function
  dominates the essential infimum of any class member's exit time by
  definition.\<close>

theorem exit_val_ge_of_stopped_bound:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x :: "real^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
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
    and Qbnd: "AE p' in Q. c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
        + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
           then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)"
  shows "ennreal c \<le> exit_val k L T K x"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0': "0 \<le> T" using T0 by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  obtain Sel where
    Sm: "Sel \<in> (borel :: real measure) \<Otimes>\<^sub>M (borel :: (real^'n) measure)
        \<rightarrow>\<^sub>M prob_algebra ?B"
    and Sc: "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow> Sel (s, y) \<in> pdelclass k L T s"
    and Sv: "\<And>s y. 0 \<le> s \<Longrightarrow> s \<le> T \<Longrightarrow>
        ess_inf_time (pshift_law (T - s) y
            (distr (Sel (s, y)) (borel_of (mtopology_of
              (path_metric (T - s) :: ('n pairpath) metric))) (prebase s T)))
          (\<lambda>\<omega>. pexit (T - s) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - s) K y"
    by (rule exit_val_measurable_selector_horizon[where k = k, OF T0 L1 Kc]) blast
  let ?\<kappa> = "selker Sel \<theta>"
  let ?R = "aglue_law T ?\<kappa> Q"
  interpret PQ': prob_space Q by (rule PQ)

  \<comment> \<open>the two vector/matrix integrability facts the glue needs\<close>
  have QXint: "integrable Q (\<lambda>p'. fst (p' (min u T)))" if u: "0 \<le> u" for u
  proof -
    have comp: "integrable Q (\<lambda>p'. fst (p' (min u T)) $ e)" for e
    proof -
      interpret HM: horizon_sq_int_martingale Q
          "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
          "\<lambda>u p'. fst (p' (min u T)) $ e" T by (rule QH)
      show ?thesis by (rule martingale.integrable[OF HM.martingale_axioms u])
    qed
    have "integrable Q (\<lambda>p'. (\<chi> e. fst (p' (min u T)) $ e) :: real^'n)"
      by (rule integrable_vec_components) (rule comp)
    then show ?thesis by simp
  qed
  have QCint: "integrable Q
      (\<lambda>p'. outerp (fst (p' (min u T))) - snd (p' (min u T)))"
    if u: "0 \<le> u" for u
  proof -
    have mg: "martingale Q (natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
        (\<lambda>u p'. outerp (fst (p' (min u T))) - snd (p' (min u T)))"
    proof (rule martingale_matI)
      fix i j
      interpret HM: horizon_sq_int_martingale Q
          "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
          "\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ i $ j" T
        by (rule QHC)
      show "martingale Q (natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
          (\<lambda>t p'. (outerp (fst (p' (min t T))) - snd (p' (min t T))) $ i $ j)"
        by (rule HM.martingale_axioms)
    qed
    show ?thesis by (rule martingale.integrable[OF mg u])
  qed

  \<comment> \<open>the competitor is in the class\<close>
  have Rmem: "?R \<in> exit_class k L T x"
    by (rule exit_class_aglue_selector
        [OF T0 L1 PQ setsQ st thM Q0 Qst Qcov QH QHC Qcont QXint QCint Sc Sm])

  \<comment> \<open>and its exit time dominates \<open>c\<close>\<close>
  have Kp: "?\<kappa> \<in> Q \<rightarrow>\<^sub>M prob_algebra ?B"
    by (rule selker_measurable[OF T0' setsQ st thM Sm])
  have Kfr: "AE w in ?\<kappa> p'. \<forall>u. u \<in> {0..T} \<longrightarrow> u \<le> \<theta> p' \<longrightarrow> w u = 0" for p'
    unfolding selker_def
    by (rule pdelclass_frozen[OF th0 thT Sc[OF th0 thT]])
  have Kval: "AE w in ?\<kappa> p'.
      enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p'))))
        \<le> pexit (T - \<theta> p') K
            (\<lambda>u. fst (p' (\<theta> p')) + fst (prebase (\<theta> p') T w u))" for p'
  proof -
    let ?s = "\<theta> p'"  let ?y = "fst (p' ?s)"
    have m: "Sel (?s, ?y) \<in> pdelclass k L T ?s" by (rule Sc[OF th0 thT])
    show ?thesis
      unfolding selker_def
      by (rule selector_value_AE[OF th0 thT Kc
            pdelclass_prob(1)[OF th0 thT m] pdelclass_prob(2)[OF th0 thT m]
            Sv[OF th0 thT]])
  qed
  have Rbnd: "AE \<omega> in ?R. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    by (rule aglue_law_pexit_ge
        [of T Q ?\<kappa> K, OF T0' PQ setsQ Kp Kc L1 st Qst Qbnd Kfr Kval])

  \<comment> \<open>hence \<open>c\<close> is below the value function\<close>
  have "ennreal c \<le> ess_inf_time ?R (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding ess_inf_time_def
  proof (intro Sup_upper CollectI)
    show "AE \<omega> in ?R. ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      using Rbnd by (rule eventually_mono) (simp add: ennreal_leI)
  qed
  also have "\<dots> \<le> exit_val k L T K x"
    unfolding exit_val_def using Rmem by (intro Sup_upper imageI)
  finally show ?thesis .
qed

subsection \<open>Transporting the bound from the law to its stopped version\<close>

text \<open>The DPP integrand reads the path only up to \<open>\<theta>\<close>, so it is unchanged by
  stopping there; transporting it along @{thm [source] AE_distr_iff}
  therefore needs only that it is measurable.  Both of its awkward pieces
  are handled by the same device: a quantity at the random horizon \<open>\<theta>\<close> is
  the quantity at the fixed horizon \<open>T\<close>, capped.  For the exit time that
  is @{thm [source] pexit_min_horizon}; for the value function it is
  @{thm [source] exit_val_horizon_cap}, which is what makes \<open>exit_val\<close> at a
  varying horizon measurable without any joint-measurability theorem.\<close>

lemma enn2real_paper_v_horizon_cap:
  fixes K :: "(real^'n::finite) set" and y :: "real^'n"
  assumes S0: "0 \<le> S" and ST: "S \<le> T" and L1: "1 \<le> L" and Kc: "closed K"
  shows "enn2real (exit_val k L S K y) = min (enn2real (exit_val k L T K y)) S"
proof -
  have T0: "0 \<le> T" using S0 ST by simp
  have a: "ennreal (enn2real (exit_val k L S K y)) = exit_val k L S K y"
    using exit_val_neq_top[OF S0, of k L K y]
    by (simp add: less_top)
  have b: "ennreal (min (enn2real (exit_val k L T K y)) S)
      = min (exit_val k L T K y) (ennreal S)"
  proof -
    have "ennreal (min (enn2real (exit_val k L T K y)) S)
        = min (ennreal (enn2real (exit_val k L T K y))) (ennreal S)"
      by (rule ennreal_min_eq)
    also have "\<dots> = min (exit_val k L T K y) (ennreal S)"
      using exit_val_neq_top[OF T0, of k L K y]
      by (simp add: less_top)
    finally show ?thesis .
  qed
  have "ennreal (enn2real (exit_val k L S K y))
      = ennreal (min (enn2real (exit_val k L T K y)) S)"
    unfolding a b by (rule exit_val_horizon_cap[OF S0 ST L1 Kc])
  then show ?thesis by (subst (asm) ennreal_inj) (use S0 in auto)
qed

lemma dpp_integrand_measurable_stopping:
  fixes K :: "(real^'n::finite) set"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "{p' \<in> space (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric))).
      c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
        + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
           then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)}
    \<in> sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  have T0': "0 \<le> T" using T0 by simp
  have th0: "0 \<le> \<theta> p'" for p' :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> p' \<le> T" for p' :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have idm: "(\<lambda>p' :: 'n pairpath. p') \<in> ?B \<rightarrow>\<^sub>M ?B"
    by (rule measurable_ident_sets[OF refl])
  have fstB: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n)
      \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_onI continuous_intros)
  have xm: "(\<lambda>p' :: 'n pairpath. fst (p' (\<theta> p'))) \<in> borel_measurable ?B"
  proof -
    have "(\<lambda>p' :: 'n pairpath. p' (\<theta> p')) \<in> borel_measurable ?B"
      by (rule path_eval_at_measurable_time
          [where X = "\<lambda>p' :: 'n pairpath. p'" and g = \<theta>, OF T0' idm thM])
         (use th0 thT in auto)
    then show ?thesis by (rule measurable_compose[OF _ fstB])
  qed
  have taum: "(\<lambda>p' :: 'n pairpath. pexit T K (\<lambda>t. fst (p' t)))
      \<in> borel_measurable ?B"
  proof -
    have "(\<lambda>p' :: 'n pairpath. pexit T K (pfst T p')) \<in> borel_measurable ?B"
      by (rule measurable_compose[OF pfst_measurable[OF T0' refl]
            pexit_measurable[OF T0' Kc]])
    then show ?thesis by (simp add: pexit_pfst)
  qed
  \<comment> \<open>the exit time at the RANDOM horizon is the fixed-horizon one, capped\<close>
  have pe: "(\<lambda>p' :: 'n pairpath. pexit (\<theta> p') K (\<lambda>t. fst (p' t)))
      = (\<lambda>p'. min (pexit T K (\<lambda>t. fst (p' t))) (\<theta> p'))"
    by (rule ext) (rule pexit_min_horizon[OF th0 thT])
  have pem: "(\<lambda>p' :: 'n pairpath. pexit (\<theta> p') K (\<lambda>t. fst (p' t)))
      \<in> borel_measurable ?B" unfolding pe using taum thM by measurable
  \<comment> \<open>and so is the value function\<close>
  have vv: "(\<lambda>p' :: 'n pairpath.
      enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))))
      = (\<lambda>p'. min (enn2real (exit_val k L T K (fst (p' (\<theta> p'))))) (T - \<theta> p'))"
  proof (rule ext)
    fix p' :: "'n pairpath"
    have a: "0 \<le> T - \<theta> p'" using thT[of p'] by simp
    have b: "T - \<theta> p' \<le> T" using th0[of p'] by simp
    show "enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p'))))
        = min (enn2real (exit_val k L T K (fst (p' (\<theta> p'))))) (T - \<theta> p')"
      by (rule enn2real_paper_v_horizon_cap[OF a b L1 Kc])
  qed
  have vm: "(\<lambda>p' :: 'n pairpath.
      enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p'))))) \<in> borel_measurable ?B"
  proof -
    have pv: "(\<lambda>y :: real^'n. enn2real (exit_val k L T K y))
        \<in> borel_measurable borel"
      by (rule exit_val_borel_measurable[OF T0 L1 Kc])
    have c1: "(\<lambda>p' :: 'n pairpath. enn2real (exit_val k L T K (fst (p' (\<theta> p')))))
        \<in> borel_measurable ?B" by (rule measurable_compose[OF xm pv])
    show ?thesis unfolding vv using c1 thM by measurable
  qed
  have Km: "K \<in> sets (borel :: (real^'n) measure)"
    using Kc by (simp add: borel_closed)
  have c1: "Measurable.pred ?B
      (\<lambda>p'. pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p')"
  proof -
    have d: "(\<lambda>p'. pexit (\<theta> p') K (\<lambda>t. fst (p' t)) - \<theta> p') \<in> borel_measurable ?B"
      using pem thM by measurable
    have "Measurable.pred ?B
        (\<lambda>p'. pexit (\<theta> p') K (\<lambda>t. fst (p' t)) - \<theta> p' = 0)"
      using d by measurable
    then show ?thesis by simp
  qed
  have c2: "Measurable.pred ?B (\<lambda>p'. fst (p' (\<theta> p')) \<in> K)"
    using xm Km by measurable
  have condm: "Measurable.pred ?B (\<lambda>p'.
      pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K)"
    using c1 c2 by measurable
  have gm: "(\<lambda>p' :: 'n pairpath. pexit (\<theta> p') K (\<lambda>t. fst (p' t))
      + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
         then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0))
      \<in> borel_measurable ?B"
    using pem vm condm by measurable
  show ?thesis using gm by measurable
qed

text \<open>The integrand does not see the stopping: it reads the path only up to
  \<open>\<theta>\<close>, where \<^const>\<open>pstopped\<close> is the identity, and \<open>\<theta>\<close> itself is unchanged
  by @{thm [source] path_stopping_time_stopped}.\<close>

lemma dpp_integrand_pstopped:
  fixes \<omega> :: "'n::finite pairpath" and K :: "(real^'n) set"
  assumes T0: "0 \<le> T" and st: "path_stopping_time T \<theta>"
    and cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
  shows "pexit (\<theta> (pstopped T \<theta> \<omega>)) K (\<lambda>t. fst (pstopped T \<theta> \<omega> t))
        + (if pexit (\<theta> (pstopped T \<theta> \<omega>)) K (\<lambda>t. fst (pstopped T \<theta> \<omega> t))
              = \<theta> (pstopped T \<theta> \<omega>)
            \<and> fst (pstopped T \<theta> \<omega> (\<theta> (pstopped T \<theta> \<omega>))) \<in> K
           then enn2real (exit_val k L (T - \<theta> (pstopped T \<theta> \<omega>)) K
             (fst (pstopped T \<theta> \<omega> (\<theta> (pstopped T \<theta> \<omega>))))) else 0)
      = pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
        + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
           then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)"
proof -
  have th: "\<theta> (pstopped T \<theta> \<omega>) = \<theta> \<omega>"
    by (rule path_stopping_time_stopped[OF st cw])
  have th0: "0 \<le> \<theta> \<omega>" by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" by (rule path_stopping_time_le[OF st])
  have ev: "pstopped T \<theta> \<omega> t = \<omega> t" if t: "0 \<le> t" and tth: "t \<le> \<theta> \<omega>" for t
  proof -
    have m: "t \<in> {0..T}" using t tth thT by simp
    have "pstopped T \<theta> \<omega> t = \<omega> (min t (\<theta> \<omega>))" by (rule pstopped_apply[OF m])
    also have "min t (\<theta> \<omega>) = t" using tth by simp
    finally show ?thesis .
  qed
  have pe: "pexit (\<theta> \<omega>) K (\<lambda>t. fst (pstopped T \<theta> \<omega> t))
      = pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))"
    by (rule pexit_cong_on) (simp add: ev)
  have en: "pstopped T \<theta> \<omega> (\<theta> \<omega>) = \<omega> (\<theta> \<omega>)" by (rule ev[OF th0 order.refl])
  show ?thesis unfolding th pe en ..
qed

theorem exit_val_dpp_ge_const_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and P :: "('n pairpath) measure"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and P: "P \<in> exit_class k L T x"
    and bnd: "AE \<omega> in P. c \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
        + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
           then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)"
  shows "ennreal c \<le> exit_val k L T K x"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  have T0': "0 \<le> T" using T0 by simp
  have L0: "0 \<le> L" using L1 by simp
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have setsP: "sets P = sets ?B" by (rule exit_class_sets[OF P])
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0' thM th0 thT])
  have Pcov: "AE \<omega> in P. \<forall>a b. 0 \<le> a \<longrightarrow> a < b \<longrightarrow> b \<le> T \<longrightarrow>
      (1 / (b - a)) *\<^sub>R (snd (\<omega> b) - snd (\<omega> a)) \<in> sconstraint k L"
    using P unfolding exit_class_def by blast
  have P0: "AE \<omega> in P. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
    by (rule exit_class_start[OF P])
  \<comment> \<open>the bound transports because the integrand does not see the stopping\<close>
  have Qbnd: "AE p' in ?Q. c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
      + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
         then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)"
  proof -
    have mset: "{p' \<in> space ?B. c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
        + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
           then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)}
        \<in> sets ?B"
      by (rule dpp_integrand_measurable_stopping[OF T0 L1 Kc st thM])
    have "AE \<omega> in P. c \<le> pexit (\<theta> (pstopped T \<theta> \<omega>)) K
          (\<lambda>t. fst (pstopped T \<theta> \<omega> t))
        + (if pexit (\<theta> (pstopped T \<theta> \<omega>)) K (\<lambda>t. fst (pstopped T \<theta> \<omega> t))
              = \<theta> (pstopped T \<theta> \<omega>)
            \<and> fst (pstopped T \<theta> \<omega> (\<theta> (pstopped T \<theta> \<omega>))) \<in> K
           then enn2real (exit_val k L (T - \<theta> (pstopped T \<theta> \<omega>)) K
             (fst (pstopped T \<theta> \<omega> (\<theta> (pstopped T \<theta> \<omega>))))) else 0)"
    proof -
      have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
      with bnd show ?thesis
      proof eventually_elim
        case (elim \<omega>)
        have cw: "continuous_on {0..T} (\<lambda>v. fst (\<omega> v))"
          by (rule path_sets_fst_continuous[OF setsP]) (use elim in blast)
        show ?case
          using elim by (simp add: dpp_integrand_pstopped[OF T0' st cw])
      qed
    qed
    then show ?thesis
      unfolding pair_law_of_def AE_distr_iff[OF m1 mset] .
  qed
  show ?thesis
  proof (rule exit_val_ge_of_stopped_bound
      [OF T0 L1 Kc pstopped_law_prob[OF T0' PS setsP st thM] sets_pair_law_of
        st thM pstopped_law_start[OF T0' setsP st thM P0]
        pstopped_law_idem[OF T0' setsP st thM]
        pstopped_law_diffquot[OF T0' setsP st thM Pcov]])
    show "horizon_sq_int_martingale ?Q
        (natural_filtration ?Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. fst (p' (min u T)) $ e) T" for e
      by (rule pstopped_law_horizon_component[OF T0 L0 P st thM])
    show "horizon_sq_int_martingale ?Q
        (natural_filtration ?Q 0 (\<lambda>v \<omega>. \<omega> v))
        (\<lambda>u p'. (outerp (fst (p' (min u T))) - snd (p' (min u T))) $ cc $ dd) T"
      for cc dd
      by (rule pstopped_law_horizon_compensated[OF T0 L0 P st thM])
    show "continuous_on {0..T} p'" if "p' \<in> space ?Q" for p'
      by (rule pstopped_law_cont[OF that])
    show "AE p' in ?Q. c \<le> pexit (\<theta> p') K (\<lambda>t. fst (p' t))
        + (if pexit (\<theta> p') K (\<lambda>t. fst (p' t)) = \<theta> p' \<and> fst (p' (\<theta> p')) \<in> K
           then enn2real (exit_val k L (T - \<theta> p') K (fst (p' (\<theta> p')))) else 0)"
      by (rule Qbnd)
  qed
qed

corollary exit_val_dpp_sup_ge_time:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T0: "0 < T" and L1: "1 \<le> L" and Kc: "closed K"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "(SUP P \<in> exit_class k L T x. ess_inf_time P
            (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
              + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
                 then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))
      \<le> exit_val k L T K x"
proof (rule exit_val_dpp_sup_ge_time_of_const)
  show "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  show "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  show "ennreal c \<le> exit_val k L T K x"
    if P: "P \<in> exit_class k L T x"
      and bnd: "AE \<omega> in P. c \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
        + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
           then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)"
    for P c
    by (rule exit_val_dpp_ge_const_time[OF T0 L1 Kc st thM P bnd])
qed


(*<*)
end
(*>*)
