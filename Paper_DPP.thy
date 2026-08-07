theory Paper_DPP
  imports Paper_Bridge Conditional_UI "Disintegration.Disintegration"
begin

text \<open>The dynamic programming principle of Proposition 2.4 of
  arXiv:2512.17702, split off from \<open>Paper_Bridge\<close>, which had grown past
  13,000 lines.  Everything here is about the VALUE FUNCTION rather than the
  class: the pasting bound, the \<open>\<ge>\<close> half of (2.9) at a deterministic time,
  the reduction of the \<open>\<le>\<close> half to a single conditioning statement, and the
  conditioning layer that statement is being built from.\<close>

section \<open>Towards the dynamic programming principle: the pasting bound\<close>

text \<open>The kernel analogue of @{thm [source] paper_v_paste_ge}: an
  almost-sure lower bound on the exit time of the KERNEL glue is a lower
  bound for @{term paper_v}.  This is what turns
  @{thm [source] paper_pair_class_kglue_law'} into an inequality about the
  value function, and it is the step the \<open>\<ge>\<close> half of (2.9) is built on.\<close>

theorem paper_v_kpaste_ge:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and T0: "0 < T" and L1: "1 \<le> L"
    and K: "closed K"
    and Q: "Q \<in> paper_pair_class k L r x"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and Kb: "Kr \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
            (paper_pair_class k L (T - r) (0::real^'n))
            (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
              (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and Kc: "\<And>\<omega>. Kr \<omega> \<in> paper_pair_class k L (T - r) 0"
    and stay: "AE p in ksemi Q (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) Kr.
        c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  shows "ennreal c \<le> paper_v k L T K x"
proof -
  let ?MR = "borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))"
  let ?BT = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?S = "ksemi Q ?MR Kr"
  have T0': "0 \<le> T" using T0 by simp
  have rT': "r \<le> T" using rT by simp
  have PQ: "prob_space Q" by (rule paper_pair_class_prob[OF Q])
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF Q])
  have G: "kglue_law' r T Kr Q \<in> paper_pair_class k L T x"
    by (rule paper_pair_class_kglue_law'[OF r rT L1 T0 Q Kp Kb Kc])
  have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BT"
    by (rule pexit_path_measurable[OF T0' K refl])
  have mset: "{\<omega> \<in> space ?BT.
      ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))} \<in> sets ?BT"
    using tauT by measurable
  have pm: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ?S \<rightarrow>\<^sub>M ?BT"
    by (rule kglue_law'_measurable[OF r rT' setsQ Kp ne])
  have iff: "(AE \<omega> in kglue_law' r T Kr Q.
        ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t))))
      = (AE p in ?S. ennreal c
          \<le> ennreal (pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))))"
    unfolding kglue_law'_def pair_law_of_def by (rule AE_distr_iff[OF pm mset])
  have "AE p in ?S. ennreal c
      \<le> ennreal (pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))"
    using stay by (auto intro: ennreal_leI elim: eventually_mono)
  then have ae: "AE \<omega> in kglue_law' r T Kr Q.
      ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding iff .
  have "ennreal c
      \<le> ess_inf_time (kglue_law' r T Kr Q) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding ess_inf_time_def using ae by (intro Sup_upper) simp
  also have "\<dots> \<le> paper_v k L T K x"
    unfolding paper_v_def using G by (intro Sup_upper imageI)
  finally show ?thesis .
qed

subsection \<open>The pathwise form of the dynamic programming bound\<close>

text \<open>A strict variant of @{thm [source] pexit_pglue_split}: the continuation
  only has to stay in \<open>K\<close> on the HALF-OPEN interval \<open>{0..<c}\<close>.  The proof is
  the same --- the case analysis already produces a strict inequality --- and
  the strict form is what the essential infimum supplies, since
  \<open>c \<le> pexit\<close> says nothing about the path AT time \<open>c\<close>.\<close>

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

text \<open>The pathwise dynamic programming bound at the DETERMINISTIC time \<open>r\<close>.
  The two summands are the paper's \<open>r \<and> \<tau>\<^sub>K\<close> and \<open>v(X\<^sub>r) \<sqdot> 1\<^sub>{r \<le> \<tau>\<^sub>K}\<close>: the
  first piece's own exit time is a lower bound in all cases
  (@{thm [source] pexit_pglue_ge}), and when the first piece has NOT exited by
  \<open>r\<close> --- which for the capped exit time is exactly
  \<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close>, with no path continuity needed --- the
  continuation adds its own survival time on top.\<close>

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

subsection \<open>The selector as a kernel into the CLASS\<close>

text \<open>@{thm [source] paper_v_measurable_selector_kernel} makes the selector a
  Giry-monad kernel, which is hypothesis \<^emph>\<open>Kp\<close> of
  @{thm [source] paper_pair_class_kglue_law'}.  That theorem also needs
  hypothesis \<^emph>\<open>Kb\<close>: measurability into the CLASS with its Lévy--Prokhorov
  metric, for the natural filtration.  Both come from the same selector, so we
  package them together --- measurability into the subspace is free, because
  the selector lands in the subspace and
  @{thm [source] paper_pair_class_compact_metric_space} identifies the metric
  topology of the class with the subspace topology of weak convergence.\<close>

theorem paper_v_measurable_selector_kernel':
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains S where
    "S \<in> borel \<rightarrow>\<^sub>M prob_algebra (borel_of
        (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (paper_pair_class k L T (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
          (mdist (path_metric T :: ('n pairpath) metric))))"
    and "\<And>y. S y \<in> paper_pair_class k L T 0"
    and "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = paper_v k L T K y"
proof -
  let ?B = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?P = "{N :: ('n pairpath) measure. prob_space N
      \<and> sets N = sets (borel_of (mtopology_of
          (path_metric T :: ('n pairpath) metric)))}"
  let ?C = "paper_pair_class k L T (0::real^'n)"
  obtain S where Sm: "S \<in> borel \<rightarrow>\<^sub>M borel_of ?W"
    and SC: "\<And>y. S y \<in> paper_pair_class k L T 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = paper_v k L T K y"
    by (rule paper_v_measurable_selector[where k = k, OF T L K]) blast
  have SP: "S y \<in> ?P" for y
    using paper_pair_class_prob[OF SC] paper_pair_class_sets[OF SC] by simp
  have polish: "Polish_space (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule Polish_space_path_metric)
  have setsPA: "sets (borel_of (subtopology ?W ?P)) = sets (prob_algebra ?B)"
    by (rule weak_conv_topology_eq_prob_algebra[OF polish])
  have Sk: "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
  proof -
    have r1: "S \<in> borel \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?P"
      by (rule measurable_restrict_space2[OF _ Sm]) (use SP in auto)
    have r2: "S \<in> borel \<rightarrow>\<^sub>M borel_of (subtopology ?W ?P)"
      using r1 by (simp add: borel_of_subtopology)
    show ?thesis using r2 measurable_cong_sets[OF refl setsPA] by blast
  qed
  have Ssub: "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology ?C
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))))"
  proof -
    have top: "Metric_space.mtopology ?C
        (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
          (mdist (path_metric T :: ('n pairpath) metric)))
        = subtopology ?W ?C"
      using L by (intro paper_pair_class_compact_metric_space(2)[OF T]) simp
    have r1: "S \<in> borel \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?C"
      by (rule measurable_restrict_space2[OF _ Sm]) (use SC in auto)
    show ?thesis unfolding top using r1 by (simp add: borel_of_subtopology)
  qed
  show ?thesis
  proof (rule that)
    show "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B" by (rule Sk)
    show "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology ?C
        (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
          (mdist (path_metric T :: ('n pairpath) metric))))" by (rule Ssub)
    show "S y \<in> paper_pair_class k L T 0" for y by (rule SC)
    show "ess_inf_time (pshift_law T y (S y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = paper_v k L T K y" for y by (rule Sval)
  qed
qed

subsection \<open>Small transfer lemmas for the exit time\<close>

text \<open>The capped exit time reads the path only on \<open>{0..U}\<close>, so cutting and
  shifting are transparent to it.\<close>

lemma pexit_cong_on:
  assumes "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> U \<Longrightarrow> f t = g t"
  shows "pexit U K f = pexit U K g"
proof -
  have "{t. 0 \<le> t \<and> t \<le> U \<and> f t \<in> - K} = {t. 0 \<le> t \<and> t \<le> U \<and> g t \<in> - K}"
    using assms by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma pexit_pcut:
  fixes \<omega> :: "'n::finite pairpath"
  shows "pexit U K (\<lambda>t. fst (pcut U \<omega> t)) = pexit U K (\<lambda>t. fst (\<omega> t))"
  by (rule pexit_cong_on) (simp add: pcut_apply)

lemma pexit_pshift:
  fixes y :: "real^'n::finite" and \<omega> :: "'n pairpath"
  shows "pexit U K (\<lambda>t. fst (pshift U y \<omega> t)) = pexit U K (\<lambda>t. y + fst (\<omega> t))"
  by (rule pexit_cong_on) (simp add: pshift_fst)

lemma paper_pair_class_start:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  using Q unfolding paper_pair_class_def by blast

subsection \<open>The value function is Borel measurable\<close>

text \<open>Clause (1) --- upper semicontinuity --- makes every sublevel set
  \<open>{y. v y < b}\<close> open, and the horizon bound makes \<open>v\<close> finite, so the real
  version \<open>enn2real \<circ> v\<close> is Borel measurable.  The dynamic programming
  principle needs this in order to even STATE its integrand as a random
  variable.\<close>

lemma paper_v_open_less:
  fixes K :: "(real^'n::finite) set" and b :: ennreal
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  shows "open {y :: real^'n. paper_v k L T K y < b}"
proof (subst open_subopen, safe)
  fix y :: "real^'n" assume "paper_v k L T K y < b"
  then have "eventually (\<lambda>z. paper_v k L T K z < b) (nhds y)"
    by (rule paper_v_usc_unconditional[OF T L K])
  then obtain U where "open U" "y \<in> U" "\<forall>z\<in>U. paper_v k L T K z < b"
    unfolding eventually_nhds by blast
  then show "\<exists>U. open U \<and> y \<in> U \<and> U \<subseteq> {y. paper_v k L T K y < b}" by blast
qed

lemma paper_v_neq_top:
  fixes K :: "(real^'n::finite) set" and y :: "real^'n"
  assumes T: "0 \<le> T"
  shows "paper_v k L T K y \<noteq> \<top>"
proof -
  have "paper_v k L T K y \<le> ennreal T" by (rule paper_v_le_T[OF T])
  moreover have "(ennreal T :: ennreal) \<noteq> \<top>" by simp
  ultimately show ?thesis by (auto simp: top_unique)
qed

lemma paper_v_borel_measurable:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  shows "(\<lambda>y :: real^'n. enn2real (paper_v k L T K y)) \<in> borel_measurable borel"
proof (subst borel_measurable_iff_less, intro allI)
  fix a :: real
  show "{w \<in> space (borel :: (real^'n) measure).
      enn2real (paper_v k L T K w) < a} \<in> sets (borel :: (real^'n) measure)"
  proof (cases "0 < a")
    case True
    have key: "(enn2real (paper_v k L T K y) < a)
        = (paper_v k L T K y < ennreal a)" for y :: "real^'n"
    proof -
      have fin: "paper_v k L T K y < \<top>"
        using paper_v_neq_top[of T k L K y] T by (simp add: less_top)
      have "(paper_v k L T K y < ennreal a)
          = (ennreal (enn2real (paper_v k L T K y)) < ennreal a)"
        by (simp add: ennreal_enn2real[OF fin])
      also have "\<dots> = (enn2real (paper_v k L T K y) < a)"
        using True by (simp add: ennreal_less_iff)
      finally show ?thesis ..
    qed
    have "{w \<in> space (borel :: (real^'n) measure).
        enn2real (paper_v k L T K w) < a}
        = {y :: real^'n. paper_v k L T K y < ennreal a}"
      by (simp add: key)
    then show ?thesis
      using paper_v_open_less[OF T L K, of k "ennreal a"] by simp
  next
    case False
    have "{w \<in> space (borel :: (real^'n) measure).
        enn2real (paper_v k L T K w) < a} = {}"
    proof (rule equals0I)
      fix w assume "w \<in> {w \<in> space (borel :: (real^'n) measure).
          enn2real (paper_v k L T K w) < a}"
      then have "enn2real (paper_v k L T K w) < a" by simp
      moreover have "0 \<le> enn2real (paper_v k L T K w)" by simp
      ultimately show False using False by simp
    qed
    then show ?thesis by simp
  qed
qed

subsection \<open>The \<open>\<ge>\<close> half of the dynamic programming principle (2.9)\<close>

text \<open>Proposition 2.4 of arXiv:2512.17702 states the dynamic programming
  principle
  \[ v(x) \;=\; \sup_{P \in \mathcal P_x} P\text{-}\operatorname*{ess\,inf}
      \bigl(\theta \wedge \tau_K + v(X_\theta)\,1_{\{\theta \le \tau_K\}}\bigr). \]
  This is its \<open>\<ge>\<close> half at a DETERMINISTIC time \<open>\<theta> = r\<close>, which is the half the
  supersolution argument of \<section>3.2 consumes.  Both summands are read off the
  first piece: \<open>\<theta> \<and> \<tau>_K\<close> is the exit time capped at \<open>r\<close>, i.e.
  \<open>pexit r K\<close>, and \<open>1\<^sub>{\<theta> \<le> \<tau>_K}\<close> is \<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close>.

  The construction: restrict \<open>P\<close> to \<open>[0,r]\<close>, continue from the endpoint with
  the law the measurable selector picks there, and paste.  The pasted law is
  in the class by @{thm [source] paper_pair_class_kglue_law'}, its exit time
  dominates the DPP integrand pathwise by @{thm [source] pexit_pglue_dpp},
  and @{thm [source] paper_v_kpaste_ge} turns that into a bound on \<open>v(x)\<close>.\<close>

theorem paper_v_dpp_ge_const:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and P: "P \<in> paper_pair_class k L T x"
    and c: "AE \<omega> in P. c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)"
  shows "ennreal c \<le> paper_v k L T K x"
proof -
  let ?MR = "borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))"
  let ?BT = "borel_of (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?BR = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  have T0: "0 < T" using r rT by simp
  have T0': "0 \<le> T" using T0 by simp
  have rT': "r \<le> T" using rT by simp
  have Tr: "0 < T - r" using rT by simp
  have Tr': "0 \<le> T - r" using Tr by simp
  have Kbor: "K \<in> sets borel" by (rule borel_closed[OF K])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)

  \<comment> \<open>the optimal continuation from every endpoint, as a kernel\<close>
  obtain S where Sk: "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?MR"
    and Ssub: "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (paper_pair_class k L (T - r) (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
          (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and SC: "\<And>y. S y \<in> paper_pair_class k L (T - r) 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law (T - r) y (S y))
        (\<lambda>\<omega>. pexit (T - r) K (\<lambda>t. fst (\<omega> t))) = paper_v k L (T - r) K y"
    by (rule paper_v_measurable_selector_kernel'[where k = k, OF Tr L1 K]) blast

  \<comment> \<open>the restriction of \<^term>\<open>P\<close> to \<open>[0,r]\<close>, and the kernel it feeds\<close>
  define Q where "Q = pair_law_of r (pcut r) P"
  have QC: "Q \<in> paper_pair_class k L r x"
    unfolding Q_def by (rule paper_pair_class_pcut[OF r rT' P])
  have setsQ: "sets Q = sets ?BR" by (rule paper_pair_class_sets[OF QC])
  interpret PQ: prob_space Q by (rule paper_pair_class_prob[OF QC])
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  define Kr where "Kr = (\<lambda>\<omega> :: 'n pairpath. S (fst (\<omega> r)))"
  have eQ: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable Q"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF setsQ] mfst])
  have Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR"
    unfolding Kr_def by (rule measurable_compose[OF eQ Sk])
  have eF: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r))
      \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M borel"
  proof (rule measurable_compose[OF _ mfst])
    show "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use r in auto)
  qed
  have Kb: "Kr \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
      \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
          (paper_pair_class k L (T - r) (0::real^'n))
          (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
            (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    unfolding Kr_def by (rule measurable_compose[OF eF Ssub])
  have Kc: "Kr \<omega> \<in> paper_pair_class k L (T - r) 0" for \<omega>
    unfolding Kr_def by (rule SC)

  \<comment> \<open>the integrand of (2.9) is a random variable, and only reads \<open>[0,r]\<close>\<close>
  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)" for \<omega>
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable ?BR"
    by (rule pexit_path_measurable[OF r K refl])
  have endm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF refl] mfst])
  have vm: "(\<lambda>\<omega> :: 'n pairpath. enn2real (paper_v k L (T - r) K (fst (\<omega> r))))
      \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF endm paper_v_borel_measurable[OF Tr L1 K]])
  have predm: "Measurable.pred ?BR (\<lambda>\<omega> :: 'n pairpath.
      pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K)"
    using taum endm Kbor by measurable
  have gm: "g \<in> borel_measurable ?BR"
    unfolding g_def using taum vm predm by measurable
  have gset: "{\<omega> \<in> space ?BR. c \<le> g \<omega>} \<in> sets ?BR" using gm by measurable
  have gcut: "g (pcut r \<omega>) = g \<omega>" for \<omega> :: "'n pairpath"
    using r by (simp add: g_def pexit_pcut pcut_apply)
  have pcm: "pcut r \<in> P \<rightarrow>\<^sub>M ?BR"
    by (rule pcut_measurable[OF r rT' paper_pair_class_sets[OF P]])
  have cg: "AE \<omega> in P. c \<le> g \<omega>" using c unfolding g_def .
  have AEQ: "AE \<omega> in Q. c \<le> g \<omega>"
    using cg unfolding Q_def pair_law_of_def AE_distr_iff[OF pcm gset] gcut .

  \<comment> \<open>the selector's optimality, transported to the glued path\<close>
  have inner: "AE \<omega>' in Kr \<omega>. c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
    if gw: "c \<le> g \<omega>" for \<omega> :: "'n pairpath"
  proof -
    define v where "v = enn2real (paper_v k L (T - r) K (fst (\<omega> r)))"
    have vnn: "0 \<le> v" by (simp add: v_def)
    have vfin: "paper_v k L (T - r) K (fst (\<omega> r)) < \<top>"
      using paper_v_neq_top[of "T - r" k L K "fst (\<omega> r)"] Tr' by (simp add: less_top)
    have veq: "ennreal v = paper_v k L (T - r) K (fst (\<omega> r))"
      unfolding v_def by (rule ennreal_enn2real[OF vfin])
    have vle: "v \<le> T - r"
    proof -
      have "ennreal v \<le> ennreal (T - r)"
        unfolding veq by (rule paper_v_le_T[OF Tr'])
      then show ?thesis using Tr' by simp
    qed
    have gw': "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then v else 0)"
      using gw unfolding g_def v_def .
    have Kcw: "Kr \<omega> \<in> paper_pair_class k L (T - r) 0" by (rule Kc)
    have z0: "AE \<omega>' in Kr \<omega>. fst (\<omega>' 0) = 0"
      using paper_pair_class_start[OF Kcw] by (auto elim: eventually_mono)
    have opt: "AE \<omega>' in Kr \<omega>. v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
    proof -
      have ae1: "AE w in pshift_law (T - r) (fst (\<omega> r)) (S (fst (\<omega> r))).
          paper_v k L (T - r) K (fst (\<omega> r))
            \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (w t)))"
        unfolding Sval[symmetric] by (rule ess_inf_time_AE)
      have setsSy: "sets (S (fst (\<omega> r))) = sets ?MR"
        by (rule paper_pair_class_sets[OF SC])
      have shm: "pshift (T - r) (fst (\<omega> r)) \<in> S (fst (\<omega> r)) \<rightarrow>\<^sub>M ?MR"
        using pshift_measurable[OF Tr'] measurable_cong_sets[OF setsSy refl] by blast
      have m1: "(\<lambda>w :: 'n pairpath. ennreal (pexit (T - r) K (\<lambda>t. fst (w t))))
          \<in> borel_measurable ?MR"
        using pexit_path_measurable[OF Tr' K refl] by measurable
      have mset: "{w \<in> space ?MR. paper_v k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (w t)))} \<in> sets ?MR"
        using m1 by measurable
      have ae2: "AE \<omega>' in S (fst (\<omega> r)). paper_v k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (pshift (T - r) (fst (\<omega> r)) \<omega>' t)))"
        using ae1 unfolding pshift_law_def AE_distr_iff[OF shm mset] .
      have ae3: "AE \<omega>' in S (fst (\<omega> r)). paper_v k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
        using ae2 by (simp add: pexit_pshift)
      have ae4: "AE \<omega>' in S (fst (\<omega> r)).
          v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
      proof (rule eventually_mono[OF ae3])
        fix \<omega>' :: "'n pairpath"
        assume "paper_v k L (T - r) K (fst (\<omega> r))
            \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
        then have "ennreal v
            \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
          using veq by simp
        then show "v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
          using pexit_nonneg[OF Tr', of K "\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)"] by simp
      qed
      then show ?thesis unfolding Kr_def .
    qed
    show ?thesis
    proof (rule eventually_mono[OF eventually_conj[OF z0 opt]])
      fix \<omega>' :: "'n pairpath"
      assume h: "fst (\<omega>' 0) = 0
          \<and> v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
      have "pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then v else 0)
          \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
      proof (rule pexit_pglue_dpp[OF r rT' vnn])
        show "r + v \<le> T" using vle by simp
        show "fst (\<omega>' 0) = 0" using h by simp
        show "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<Longrightarrow> fst (\<omega> r) \<in> K
            \<Longrightarrow> v \<le> pexit (T - r) K (\<lambda>s. fst (\<omega> r) + fst (\<omega>' s))"
          using h by simp
      qed
      with gw' show "c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))" by simp
    qed
  qed

  \<comment> \<open>pasting: the glued law is in the class and beats \<open>c\<close>\<close>
  have gluem: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ksemi Q ?MR Kr \<rightarrow>\<^sub>M ?BT"
    by (rule kglue_law'_measurable[OF r rT' setsQ Kp ne])
  have gluem': "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?MR \<rightarrow>\<^sub>M ?BT"
    using gluem measurable_cong_sets[OF sets_ksemi[OF Kp ne] refl] by blast
  have pexm: "(\<lambda>p :: 'n pairpath \<times> 'n pairpath.
      pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t)))
        \<in> borel_measurable (Q \<Otimes>\<^sub>M ?MR)"
    by (rule measurable_compose[OF gluem' pexit_path_measurable[OF T0' K refl]])
  have psetm: "{p \<in> space (Q \<Otimes>\<^sub>M ?MR).
      c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))} \<in> sets (Q \<Otimes>\<^sub>M ?MR)"
    using pexm by measurable
  have stay: "AE p in ksemi Q ?MR Kr.
      c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  proof -
    have "AE \<omega> in Q. AE \<omega>' in Kr \<omega>.
        c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
    proof (rule eventually_mono[OF AEQ])
      fix \<omega> :: "'n pairpath" assume "c \<le> g \<omega>"
      then show "AE \<omega>' in Kr \<omega>. c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
        by (rule inner)
    qed
    then show ?thesis unfolding AE_ksemi[OF Kp psetm] by simp
  qed
  show ?thesis
    by (rule paper_v_kpaste_ge[OF r rT T0 L1 K QC Kp Kb Kc stay])
qed

text \<open>The essential infimum form: the DPP integrand is bounded by \<open>T\<close>, so its
  essential infimum is finite and @{thm [source] ess_inf_time_AE} turns it
  into an almost-sure bound with a REAL constant, which is what the pasting
  construction consumes.\<close>

theorem paper_v_dpp_ge:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and P: "P \<in> paper_pair_class k L T x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))
      \<le> paper_v k L T K x"
proof -
  have Tr': "0 \<le> T - r" using rT by simp
  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)" for \<omega>
  have geta: "g = (\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))"
    by (rule ext) (simp add: g_def)
  have vbnd: "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
      then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0) \<le> T - r"
    for \<omega> :: "'n pairpath"
  proof (cases "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K")
    case True
    have "ennreal (enn2real (paper_v k L (T - r) K (fst (\<omega> r))))
        = paper_v k L (T - r) K (fst (\<omega> r))"
      using paper_v_neq_top[of "T - r" k L K "fst (\<omega> r)"] Tr'
      by (simp add: less_top)
    also have "\<dots> \<le> ennreal (T - r)" by (rule paper_v_le_T[OF Tr'])
    finally have "enn2real (paper_v k L (T - r) K (fst (\<omega> r))) \<le> T - r"
      using Tr' by simp
    then show ?thesis using True by simp
  next
    case False
    then have "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
        then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0) = 0"
      by (rule if_not_P)
    then show ?thesis using Tr' by simp
  qed
  have gle: "g \<omega> \<le> T" for \<omega> :: "'n pairpath"
  proof -
    have "pexit r K (\<lambda>t. fst (\<omega> t)) \<le> r" by (rule pexit_le_T[OF r])
    with vbnd[of \<omega>] show ?thesis unfolding g_def by simp
  qed
  have gnn: "0 \<le> g \<omega>" for \<omega> :: "'n pairpath"
  proof -
    have "0 \<le> pexit r K (\<lambda>t. fst (\<omega> t))" by (rule pexit_nonneg[OF r])
    then show ?thesis unfolding g_def by simp
  qed
  have PP: "prob_space P" by (rule paper_pair_class_prob[OF P])
  have fin: "ess_inf_time P g \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF PP gle])
  have ntop: "ess_inf_time P g < \<top>"
  proof -
    have "(ennreal T :: ennreal) < \<top>" by simp
    with fin show ?thesis by (rule order.strict_trans1)
  qed
  define c where "c = enn2real (ess_inf_time P g)"
  have ceq: "ennreal c = ess_inf_time P g"
    unfolding c_def by (rule ennreal_enn2real[OF ntop])
  have aec0: "AE \<omega> in P. c \<le> g \<omega>"
  proof (rule eventually_mono[OF ess_inf_time_AE[of P g]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P g \<le> ennreal (g \<omega>)"
    then have "ennreal c \<le> ennreal (g \<omega>)" using ceq by simp
    then show "c \<le> g \<omega>" using gnn[of \<omega>] by simp
  qed
  have aec: "AE \<omega> in P. c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)"
    using aec0 unfolding g_def .
  have main: "ennreal c \<le> paper_v k L T K x"
    by (rule paper_v_dpp_ge_const[OF r rT L1 K P aec])
  have "ess_inf_time P (\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)) = ennreal c"
    using ceq geta by simp
  then show ?thesis using main by simp
qed

text \<open>Hence the \<open>\<ge>\<close> half of (2.9) itself, at a deterministic time.\<close>

corollary paper_v_dpp_sup_ge:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
  shows "(SUP P \<in> paper_pair_class k L T x. ess_inf_time P
            (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
              + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
                 then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))
      \<le> paper_v k L T K x"
proof (rule SUP_least)
  fix P :: "('n pairpath) measure"
  assume "P \<in> paper_pair_class k L T x"
  then show "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))
      \<le> paper_v k L T K x"
    by (rule paper_v_dpp_ge[OF r rT L1 K])
qed

subsection \<open>The \<open>\<le>\<close> half of (2.9), reduced to conditioning\<close>

text \<open>Off the survival event the horizon cap at \<open>r\<close> is invisible: a path that
  has already left \<open>K\<close> by time \<open>r\<close> has the same exit time whichever horizon it
  is measured against.  Note the event is \<open>\<not> (pexit r K f = r \<and> f r \<in> K)\<close>,
  which is genuinely weaker than \<open>pexit r K f < r\<close> --- a path may exit exactly
  AT \<open>r\<close>, and @{thm [source] pexit_stable_above_T} does not cover that case.\<close>

lemma pexit_cap_eq:
  fixes K :: "'a::polish_space set" and f :: "real \<Rightarrow> 'a"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and ex: "\<not> (pexit r K f = r \<and> f r \<in> K)"
  shows "pexit T K f = pexit r K f"
proof (cases "pexit r K f < r")
  case True
  then show ?thesis by (rule pexit_stable_above_T[OF r rT])
next
  case False
  then have eqr: "pexit r K f = r" using pexit_le_T[OF r, of K f] by simp
  with ex have nk: "f r \<in> - K" by simp
  show ?thesis
  proof (rule antisym)
    have "pexit T K f \<le> r"
      unfolding pexit_def using r rT nk by (intro etime_le_of_mem) auto
    then show "pexit T K f \<le> pexit r K f" using eqr by simp
    show "pexit r K f \<le> pexit T K f" by (rule pexit_mono_T[OF r rT])
  qed
qed

text \<open>Hence the \<open>\<le>\<close> half of (2.9) reduces to a SINGLE statement about
  conditioning, and no other property of the class is needed:

  \begin{quote}
  if the exit time of \<open>P \<in> \<P>\<^sub>x\<close> is almost surely at least \<open>c\<close>, then almost
  surely ON THE SURVIVAL EVENT \<open>{r \<le> \<tau>\<^sub>K}\<close> the value at the position reached
  is at least the time still to run, \<open>c - r\<close>.
  \end{quote}

  That is exactly the statement that the conditional law of the future given
  \<open>\<F>\<^sub>r\<close> is, almost surely, a member of the class started at \<open>X\<^sub>r\<close>, so that its
  own essential infimum is bounded by \<open>v(X\<^sub>r)\<close>; it is the regular conditional
  distribution argument, and it is the only thing still missing from the
  dynamic programming principle at a deterministic time.  Everything OFF the
  survival event is unconditional, by @{thm [source] pexit_cap_eq}.\<close>

theorem paper_v_dpp_le_of_cond:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and cond: "\<And>P c. P \<in> paper_pair_class k L T x \<Longrightarrow>
        (AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))) \<Longrightarrow>
        (AE \<omega> in P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
            \<longrightarrow> c \<le> r + enn2real (paper_v k L (T - r) K (fst (\<omega> r))))"
  shows "paper_v k L T K x
      \<le> (SUP P \<in> paper_pair_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))"
proof -
  have rT': "r \<le> T" using rT by simp
  have T0': "0 \<le> T" using r rT by simp
  have key: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))"
    if P: "P \<in> paper_pair_class k L T x" for P :: "('n pairpath) measure"
  proof -
    have PP: "prob_space P" by (rule paper_pair_class_prob[OF P])
    have taule: "pexit T K (\<lambda>t. fst (\<omega> t)) \<le> T" for \<omega> :: "'n pairpath"
      by (rule pexit_le_T[OF T0'])
    have fin: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) < \<top>"
    proof -
      have "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) \<le> ennreal T"
        by (rule ess_inf_time_le_const[OF PP taule])
      moreover have "(ennreal T :: ennreal) < \<top>" by simp
      ultimately show ?thesis by (rule order.strict_trans1)
    qed
    define c where
      "c = enn2real (ess_inf_time P (\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))))"
    have ceq: "ennreal c = ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
      unfolding c_def by (rule ennreal_enn2real[OF fin])
    have aeT: "AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    proof (rule eventually_mono[OF ess_inf_time_AE
        [of P "\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t))"]])
      fix \<omega> :: "'n pairpath"
      assume "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
          \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))"
      then have "ennreal c \<le> ennreal (pexit T K (\<lambda>t. fst (\<omega> t)))" using ceq by simp
      then show "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
        using pexit_nonneg[OF T0', of K "\<lambda>t. fst (\<omega> t)"] by simp
    qed
    have aeS: "AE \<omega> in P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
        \<longrightarrow> c \<le> r + enn2real (paper_v k L (T - r) K (fst (\<omega> r)))"
      by (rule cond[OF P aeT])
    have aeg: "AE \<omega> in P. c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)"
    proof (rule eventually_mono[OF eventually_conj[OF aeT aeS]])
      fix \<omega> :: "'n pairpath"
      assume h: "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))
          \<and> (pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             \<longrightarrow> c \<le> r + enn2real (paper_v k L (T - r) K (fst (\<omega> r))))"
      show "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)"
      proof (cases "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K")
        case True
        then have "pexit r K (\<lambda>t. fst (\<omega> t)) = r" by simp
        moreover have "c \<le> r + enn2real (paper_v k L (T - r) K (fst (\<omega> r)))"
          using h True by simp
        ultimately show ?thesis using True by simp
      next
        case False
        have eq: "pexit T K (\<lambda>t. fst (\<omega> t)) = pexit r K (\<lambda>t. fst (\<omega> t))"
          by (rule pexit_cap_eq[OF r rT' False])
        have z: "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
            then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0) = 0"
          using False by (rule if_not_P)
        show ?thesis using h eq z by simp
      qed
    qed
    have aeE: "AE \<omega> in P. ennreal c \<le> ennreal (pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))"
    proof (rule eventually_mono[OF aeg])
      fix \<omega> :: "'n pairpath"
      assume "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)"
      then show "ennreal c \<le> ennreal (pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))"
        by (rule ennreal_leI)
    qed
    have "ennreal c \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))"
      by (rule ess_inf_timeI[OF aeE])
    then show ?thesis unfolding ceq .
  qed
  have pv: "paper_v k L T K x = (SUP Q \<in> paper_pair_class k L T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))"
    unfolding paper_v_def ..
  show ?thesis
    unfolding pv
  proof (rule SUP_least)
    fix P :: "('n pairpath) measure"
    assume P: "P \<in> paper_pair_class k L T x"
    have "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0))"
      by (rule key[OF P])
    also have "\<dots> \<le> (SUP Q \<in> paper_pair_class k L T x. ess_inf_time Q
        (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))"
      using P by (rule SUP_upper)
    finally show "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> (SUP Q \<in> paper_pair_class k L T x. ess_inf_time Q
            (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
              + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
                 then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))" .
  qed
qed

text \<open>Both halves together: Eq. (2.9) at a deterministic time, modulo the
  conditioning statement isolated above.\<close>

corollary paper_v_dpp_eq_of_cond:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and cond: "\<And>P c. P \<in> paper_pair_class k L T x \<Longrightarrow>
        (AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))) \<Longrightarrow>
        (AE \<omega> in P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
            \<longrightarrow> c \<le> r + enn2real (paper_v k L (T - r) K (fst (\<omega> r))))"
  shows "paper_v k L T K x
      = (SUP P \<in> paper_pair_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))"
proof (rule order.antisym)
  show "paper_v k L T K x
      \<le> (SUP P \<in> paper_pair_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))"
    by (rule paper_v_dpp_le_of_cond[OF r rT L1 K cond])
  show "(SUP P \<in> paper_pair_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (paper_v k L (T - r) K (fst (\<omega> r))) else 0)))
      \<le> paper_v k L T K x"
    by (rule paper_v_dpp_sup_ge[OF r rT L1 K])
qed

section \<open>Conditioning on the past: towards the \<open>\<le>\<close> half\<close>

text \<open>The remaining obligation of the dynamic programming principle at a
  deterministic time is the conditioning statement isolated in
  @{thm [source] paper_v_dpp_le_of_cond}.  This section builds its
  ingredients: the exit time SPLITS at \<open>r\<close> on the survival event, and the
  rebased future \<open>pfut\<close> is a measurable map of path spaces.\<close>

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
  contributes \<open>r\<close> and the rest is the exit time of the TIME-SHIFTED path
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
      unfolding pexit_def using r t nk by (intro etime_le_of_mem) auto
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

subsection \<open>The rebased future as a map of path spaces\<close>

text \<open>\<open>pfut r T \<omega>\<close> is the path after \<open>r\<close>, re-based at its own starting point,
  so that it starts at \<open>0\<close> no matter where \<open>\<omega>\<close> was at time \<open>r\<close>.  It is the
  map along which the conditional law of the future is taken.  Like the glue,
  it is Lipschitz --- with constant \<open>2\<close>, because the base point is subtracted
  and so counts once more.\<close>

definition pfut :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "pfut r T \<omega> = restrict (\<lambda>s. \<omega> (r + s) - \<omega> r) {0..T - r}"

lemma pfut_apply: "s \<in> {0..T - r} \<Longrightarrow> pfut r T \<omega> s = \<omega> (r + s) - \<omega> r"
  by (simp add: pfut_def)

lemma pfut_zero: "0 \<le> T - r \<Longrightarrow> pfut r T \<omega> 0 = 0"
  by (simp add: pfut_def)

lemma pfut_fst:
  "s \<in> {0..T - r} \<Longrightarrow> fst (pfut r T \<omega> s) = fst (\<omega> (r + s)) - fst (\<omega> r)"
  by (simp add: pfut_def)

lemma pfut_in_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pfut r T \<omega> \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
proof -
  have cw: "continuous_on {0..T} \<omega>" by (rule mspace_path_metric_continuous[OF w])
  have sub: "(\<lambda>s. r + s) ` {0..T - r} \<subseteq> {0..T}" using r rT by auto
  have c1: "continuous_on {0..T - r} (\<lambda>s. \<omega> (r + s))"
    by (rule continuous_on_compose2[OF cw _ sub]) (intro continuous_intros)
  have "continuous_on {0..T - r} (\<lambda>s. \<omega> (r + s) - \<omega> r)"
    by (intro continuous_on_diff c1 continuous_on_const)
  then show ?thesis unfolding pfut_def by (rule mspace_path_metricI)
qed

lemma Lipschitz_pfut:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n::finite pairpath) metric)
      (path_metric (T - r) :: ('n pairpath) metric) (pfut r T)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pfut r T \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric (T - r) :: ('n pairpath) metric)"
    by (intro funcsetI pfut_in_mspace[OF r rT])
  have T0: "0 \<le> T" using r rT by simp
  have Tr: "0 \<le> T - r" using rT by simp
  have key: "mdist (path_metric (T - r)) (pfut r T f) (pfut r T g)
      \<le> 2 * mdist (path_metric T) f g"
    if f: "f \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and g: "g \<in> mspace (path_metric T :: ('n pairpath) metric)" for f g
  proof -
    have sf: "pfut r T f \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by (rule pfut_in_mspace[OF r rT f])
    have sg: "pfut r T g \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
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
  show "\<exists>B. \<forall>f\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>g\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric (T - r)) (pfut r T f) (pfut r T g)
          \<le> B * mdist (path_metric T) f g"
    by (intro exI[of _ 2] ballI key)
qed

lemma pfut_measurable:
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "pfut r T
      \<in> borel_of (mtopology_of (path_metric T :: ('n::finite pairpath) metric))
        \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric (T - r) :: ('n pairpath) metric))"
  by (intro continuous_map_measurable Lipschitz_continuous_imp_continuous_map
      Lipschitz_pfut[OF r rT])

lemma pfut_measurable_law:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pfut r T \<in> Q \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  using pfut_measurable[OF r rT] measurable_cong_sets[OF setsQ refl] by blast

text \<open>The exit time of the future, expressed through \<open>pfut\<close>: re-basing at the
  endpoint and adding the endpoint back is the identity on the exit time.\<close>

lemma pexit_pfut:
  fixes K :: "(real^'n::finite) set" and \<omega> :: "'n pairpath"
  shows "pexit (T - r) K (\<lambda>s. fst (\<omega> r) + fst (pfut r T \<omega> s))
      = pexit (T - r) K (\<lambda>s. fst (\<omega> (r + s)))"
  by (rule pexit_cong_on) (simp add: pfut_fst)

subsection \<open>Conditioning on an event of the past keeps martingales martingales\<close>

text \<open>The structural fact the \<open>\<le>\<close> half turns on.  Conditioning on an event
  \<open>A\<close> of the PAST rescales the measure by a density that is measurable for
  the filtration at time \<open>0\<close>; a set integral over \<open>C \<in> \<F>\<^sub>i\<close> then becomes one
  over \<open>C \<inter> A \<in> \<F>\<^sub>i\<close>, and the martingale property applies unchanged.  There
  is no approximation and no monotone-class step --- that is what makes this
  route to the conditional law elementary.\<close>

lemma uniform_measure_density_real:
  assumes M: "prob_space M" and pos: "0 < measure M A"
  shows "uniform_measure M A = density M (\<lambda>x. ennreal (indicator A x / measure M A))"
proof -
  interpret PM: prob_space M by (rule M)
  have "(\<lambda>x. indicator A x / emeasure M A)
      = (\<lambda>x. ennreal (indicator A x / measure M A))"
  proof
    fix x show "indicator A x / emeasure M A = ennreal (indicator A x / measure M A)"
    proof (cases "x \<in> A")
      case True
      have "indicator A x / emeasure M A = ennreal 1 / ennreal (measure M A)"
        using True by (simp add: PM.emeasure_eq_measure)
      also have "\<dots> = ennreal (1 / measure M A)"
        by (rule divide_ennreal[OF _ pos]) simp
      finally show ?thesis using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  then show ?thesis unfolding uniform_measure_def by simp
qed

lemma integral_uniform_measure_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and A: "A \<in> sets M" and pos: "0 < measure M A"
    and f: "f \<in> borel_measurable M"
  shows "(\<integral>x. f x \<partial>uniform_measure M A)
      = (\<integral>x. (indicator A x / measure M A) *\<^sub>R f x \<partial>M)"
proof -
  have gm: "(\<lambda>x. indicator A x / measure M A) \<in> borel_measurable M"
    using A by measurable
  show ?thesis
    unfolding uniform_measure_density_real[OF M pos]
    by (rule integral_density[OF f gm]) (use pos in auto)
qed

lemma integrable_uniform_measureI:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and A: "A \<in> sets M" and pos: "0 < measure M A"
    and f: "integrable M f"
  shows "integrable (uniform_measure M A) f"
proof -
  have fm: "f \<in> borel_measurable M" using f by simp
  have gm: "(\<lambda>x. indicator A x / measure M A) \<in> borel_measurable M"
    using A by measurable
  have i1: "integrable M (\<lambda>x. indicator A x *\<^sub>R f x)"
    by (rule integrable_mult_indicator[OF A f])
  have i2: "integrable M (\<lambda>x. (1 / measure M A) *\<^sub>R (indicator A x *\<^sub>R f x))"
    by (rule integrable_scaleR_right[OF i1])
  have eq: "(\<lambda>x. (1 / measure M A) *\<^sub>R (indicator A x *\<^sub>R f x))
      = (\<lambda>x. (indicator A x / measure M A) *\<^sub>R f x)"
    by (rule ext) (simp add: field_simps)
  have "integrable (uniform_measure M A) f
      \<longleftrightarrow> integrable M (\<lambda>x. (indicator A x / measure M A) *\<^sub>R f x)"
    unfolding uniform_measure_density_real[OF M pos]
    by (rule integrable_density[OF fm gm]) (use pos in auto)
  then show ?thesis using i2 eq by simp
qed

lemma set_integral_uniform_measure_eq:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and A: "A \<in> sets M" and pos: "0 < measure M A"
    and f: "f \<in> borel_measurable M" and C: "C \<in> sets M"
  shows "set_lebesgue_integral (uniform_measure M A) C f
      = (1 / measure M A) *\<^sub>R set_lebesgue_integral M (C \<inter> A) f"
proof -
  have cm: "(\<lambda>x. indicator C x *\<^sub>R f x) \<in> borel_measurable M" using f C by measurable
  have "set_lebesgue_integral (uniform_measure M A) C f
      = (\<integral>x. indicator C x *\<^sub>R f x \<partial>uniform_measure M A)"
    unfolding set_lebesgue_integral_def ..
  also have "\<dots> = (\<integral>x. (indicator A x / measure M A) *\<^sub>R (indicator C x *\<^sub>R f x) \<partial>M)"
    by (rule integral_uniform_measure_eq[OF M A pos cm])
  also have "\<dots> = (\<integral>x. (1 / measure M A) *\<^sub>R (indicator (C \<inter> A) x *\<^sub>R f x) \<partial>M)"
    by (intro Bochner_Integration.integral_cong) (auto simp: indicator_def)
  also have "\<dots> = (1 / measure M A) *\<^sub>R (\<integral>x. indicator (C \<inter> A) x *\<^sub>R f x \<partial>M)"
    by (rule integral_scaleR_right)
  finally show ?thesis unfolding set_lebesgue_integral_def .
qed

theorem martingale_uniform_measure:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes M: "prob_space M" and mg: "martingale M F (0::real) X"
    and A: "A \<in> sets (F 0)" and pos: "0 < measure M A"
  shows "martingale (uniform_measure M A) F 0 X"
proof -
  interpret PM: prob_space M by (rule M)
  interpret MG: martingale M F "0::real" X by (rule mg)
  have F0M: "sets (F 0) \<subseteq> sets M" by (rule MG.sets_F_subset[OF order_refl])
  have AM: "A \<in> sets M" using A F0M by blast
  have ea0: "emeasure M A \<noteq> 0" using pos by (simp add: PM.emeasure_eq_measure)
  have eafin: "emeasure M A \<noteq> \<infinity>" by (simp add: PM.emeasure_eq_measure)
  interpret PU: prob_space "uniform_measure M A"
    by (rule prob_space_uniform_measure[OF ea0 eafin])
  have FU: "filtered_measure (uniform_measure M A) F 0"
  proof (unfold_locales)
    show "subalgebra (uniform_measure M A) (F i)" if "0 \<le> i" for i :: real
      using MG.subalgebras[OF that] by (simp add: subalgebra_def)
    show "sets (F i) \<le> sets (F j)" if "0 \<le> i" "i \<le> j" for i j :: real
      by (rule MG.sets_F_mono[OF that])
  qed
  interpret FU: finite_filtered_measure "uniform_measure M A" F "0::real"
    unfolding finite_filtered_measure_def
    using FU PU.finite_measure_axioms by blast
  show ?thesis
  proof (rule FU.martingale_of_set_integral_eq)
    show "adapted_process (uniform_measure M A) F 0 X"
      unfolding adapted_process_def adapted_process_axioms_def
      using FU MG.adapted by blast
    show "integrable (uniform_measure M A) (X i)" if "0 \<le> i" for i
      by (rule integrable_uniform_measureI[OF M AM pos MG.integrable[OF that]])
    fix C and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and C: "C \<in> sets (F i)"
    have CM: "C \<in> sets M" using C MG.sets_F_subset[OF ij(1)] by auto
    have AFi: "A \<in> sets (F i)" using A MG.sets_F_mono[OF order_refl ij(1)] by auto
    have CA: "C \<inter> A \<in> sets (F i)" using C AFi by (rule sets.Int)
    have Xm: "X i \<in> borel_measurable M"
      by (rule measurable_from_subalg[OF MG.subalgebras[OF ij(1)] MG.adapted[OF ij(1)]])
    have j0: "0 \<le> j" using ij by simp
    have Xmj: "X j \<in> borel_measurable M"
      by (rule measurable_from_subalg[OF MG.subalgebras[OF j0] MG.adapted[OF j0]])
    have "set_lebesgue_integral (uniform_measure M A) C (X i)
        = (1 / measure M A) *\<^sub>R set_lebesgue_integral M (C \<inter> A) (X i)"
      by (rule set_integral_uniform_measure_eq[OF M AM pos Xm CM])
    also have "\<dots> = (1 / measure M A) *\<^sub>R set_lebesgue_integral M (C \<inter> A) (X j)"
      using MG.set_integral_eq[OF CA ij(1) ij(2)] by simp
    also have "\<dots> = set_lebesgue_integral (uniform_measure M A) C (X j)"
      by (rule set_integral_uniform_measure_eq[OF M AM pos Xmj CM, symmetric])
    finally show "set_lebesgue_integral (uniform_measure M A) C (X i)
        = set_lebesgue_integral (uniform_measure M A) C (X j)" .
  qed
qed

lemma measurable_fst_borel:
  "(fst :: (real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
  using measurable_fst[of "borel :: (real^'n) measure"
      "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)

theorem martingale_future_of_past:
  fixes P :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
    and Zm: "\<And>u. 0 \<le> u \<Longrightarrow> Z u \<in> borel_measurable
        (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
           0 (\<lambda>v w. w v) u)"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. Z u (pfut r T \<omega>))"
  shows "martingale (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
      (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
        0 (\<lambda>v w. w v)) 0 Z"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?FF = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  interpret PP: prob_space P by (rule PS)
  have Tr: "0 \<le> ?S" using rT by simp
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    using setsP by simp
  have ea0: "emeasure P A \<noteq> 0" using pos by (simp add: PP.emeasure_eq_measure)
  have eafin: "emeasure P A \<noteq> \<infinity>" by (simp add: PP.emeasure_eq_measure)
  have PM: "prob_space ?M" by (rule prob_space_uniform_measure[OF ea0 eafin])
  have phim: "pfut r T
      \<in> ?M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
    by (rule pfut_measurable_law[OF r rT setsM])
  have A': "A \<in> sets (?FF 0)"
  proof -
    have "r + min 0 ?S = r" using Tr by simp
    then show ?thesis using A by simp
  qed
  have mgM: "martingale ?M ?FF 0 (\<lambda>u \<omega>. Z u (pfut r T \<omega>))"
    by (rule martingale_uniform_measure[OF PS mg A' pos])
  show ?thesis
  proof (rule martingale_pair_law[OF PM phim _ Zm mgM])
    fix u v :: real assume v: "0 \<le> v" and vu: "v \<le> u"
    show "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) \<in> borel_measurable (?FF u)"
    proof (cases "v \<le> ?S")
      case True
      have m1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v)) \<in> borel_measurable (?FF u)"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use r v vu True in auto)
      have m2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable (?FF u)"
        unfolding natural_filtration_def
        by (rule measurable_family_vimage_algebra) (use r v vu True Tr in auto)
      have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v) - \<omega> r) \<in> borel_measurable (?FF u)"
        by (rule borel_measurable_diff[OF m1 m2])
      moreover have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. \<omega> (r + v) - \<omega> r)"
        using v True by (auto simp: pfut_apply)
      ultimately show ?thesis by simp
    next
      case False
      then have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. undefined)"
        by (auto simp: pfut_def)
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>The four clauses of (1.7) for the conditioned future law\<close>

text \<open>Clause (i) is free: @{thm [source] pfut_zero} says the rebased future
  starts at \<open>0\<close> no matter where the path was at time \<open>r\<close>, so the initial
  condition holds identically rather than almost surely.\<close>

lemma pfut_law_start:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "AE w in pair_law_of (T - r) (pfut r T) (uniform_measure P A).
      fst (w 0) = 0 \<and> snd (w 0) = 0"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?B = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" using setsP by simp
  have phim: "pfut r T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pfut_measurable_law[OF r rT setsM])
  have ev: "(\<lambda>w :: 'n pairpath. w 0) \<in> borel_measurable ?B"
    by (rule pair_law_eval_measurable[OF refl])
  have mset: "{w \<in> space ?B. fst (w 0) = 0 \<and> snd (w 0) = 0} \<in> sets ?B"
  proof -
    have "{w \<in> space ?B. fst (w 0) = 0 \<and> snd (w 0) = 0}
        = (\<lambda>w :: 'n pairpath. w 0) -` {(0, 0)} \<inter> space ?B"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have iff: "(AE w in pair_law_of ?S (pfut r T) ?M. fst (w 0) = 0 \<and> snd (w 0) = 0)
      = (AE \<omega> in ?M. fst (pfut r T \<omega> 0) = 0 \<and> snd (pfut r T \<omega> 0) = 0)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mset])
  have "AE \<omega> in ?M. fst (pfut r T \<omega> 0) = 0 \<and> snd (pfut r T \<omega> 0) = 0"
    by (rule AE_I2) (simp add: pfut_zero[OF Tr])
  then show ?thesis unfolding iff .
qed

text \<open>Clause (ii) is inheritance: the future's increment over \<open>[p,q]\<close> IS the
  path's increment over \<open>[r+p, r+q]\<close>, the base point cancelling, and the two
  time spans agree.\<close>

lemma pfut_law_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and AM: "A \<in> sets P"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE w in pair_law_of (T - r) (pfut r T) (uniform_measure P A).
      \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
proof (rule paper_pair_class_diffquot_of_pairs[OF sets_pair_law_of])
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?B = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  fix p q :: real
  assume pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q"
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))" using setsP by simp
  have phim: "pfut r T \<in> ?M \<rightarrow>\<^sub>M ?B" by (rule pfut_measurable_law[OF r rT setsM])
  have mm: "{w \<in> space ?B.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L} \<in> sets ?B"
    using borel_of_closed[OF closedin_diffquot_constraint[OF pq(1) pq(2)]]
    by (simp add: space_borel_of)
  have iff: "(AE w in pair_law_of ?S (pfut r T) ?M.
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L)
      = (AE \<omega> in ?M. (1 / (q - p))
          *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L)"
    unfolding pair_law_of_def by (rule AE_distr_iff[OF phim mm])
  have covM: "AE \<omega> in ?M. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    by (rule AE_uniform_measureI[OF AM]) (use cov in \<open>auto elim: eventually_mono\<close>)
  have "AE \<omega> in ?M. (1 / (q - p))
      *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L"
  proof (rule eventually_mono[OF covM])
    fix \<omega> :: "'n pairpath"
    assume h: "\<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    have rp: "0 \<le> r + p" using r pq by simp
    have rpq: "r + p < r + q" using pq by simp
    have rqT: "r + q \<le> T" using pq by simp
    have "(1 / ((r + q) - (r + p)))
        *\<^sub>R (snd (\<omega> (r + q)) - snd (\<omega> (r + p))) \<in> sconstraint k L"
      using h rp rpq rqT by blast
    then have "(1 / (q - p))
        *\<^sub>R (snd (\<omega> (r + q)) - snd (\<omega> (r + p))) \<in> sconstraint k L" by simp
    moreover have "snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)
        = snd (\<omega> (r + q)) - snd (\<omega> (r + p))"
      using pq by (simp add: pfut_apply)
    ultimately show "(1 / (q - p))
        *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L" by simp
  qed
  then show "AE w in pair_law_of ?S (pfut r T) ?M.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    unfolding iff .
qed

text \<open>Clause (iii): the coordinate martingale.  Shift the clock by \<open>r\<close>
  (@{thm [source] martingale_time_change}), subtract the value at \<open>r\<close>
  (@{thm [source] martingale_sub_initial}), and hand the result to
  @{thm [source] martingale_future_of_past}, which conditions on the past
  event and pushes along \<open>pfut\<close>.\<close>

lemma pfut_law_X_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and P: "P \<in> paper_pair_class k L T x"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
  shows "martingale (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
      (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
        0 (\<lambda>v w. w v)) 0 (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?Q = "pair_law_of ?S (pfut r T) ?M"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF P])
  have PS: "prob_space P" by (rule paper_pair_class_prob[OF P])
  have Zm: "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)))
      \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
    if u: "0 \<le> u" for u
  proof (rule measurable_compose[OF _ measurable_fst_borel])
    show "(\<lambda>w :: 'n pairpath. w (min u ?S))
        \<in> natural_filtration ?Q 0 (\<lambda>v w. w v) u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u Tr in auto)
  qed
  have MGX: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule paper_pair_class_X_martingale[OF P])
  have s0: "0 \<le> r + min u ?S" if "0 \<le> u" for u :: real using r Tr that by simp
  have smono: "r + min u ?S \<le> r + min v ?S" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mg1: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (min (r + min u ?S) T)))"
    by (rule martingale_time_change[OF MGX s0 smono])
  have eqmin: "min (r + min u ?S) T = r + min u ?S" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then have "r + min u ?S \<le> T" by simp
    then show ?thesis by simp
  qed
  have mg2: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)))"
    using mg1 by (simp add: eqmin)
  have mg3: "martingale P ?FP 0
      (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) - fst (\<omega> (r + min 0 ?S)))"
    by (rule martingale_sub_initial[OF mg2])
  have mg: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (pfut r T \<omega> (min u ?S)))"
  proof (rule martingale_cong_ge[OF mg3])
    fix u :: real assume u: "0 \<le> u"
    have m: "min u ?S \<in> {0..?S}" using u Tr by simp
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min u ?S)) - fst (\<omega> (r + min 0 ?S)))
        = (\<lambda>\<omega>. fst (pfut r T \<omega> (min u ?S)))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      have "fst (pfut r T \<omega> (min u ?S)) = fst (\<omega> (r + min u ?S)) - fst (\<omega> r)"
        by (rule pfut_fst[OF m])
      then show "fst (\<omega> (r + min u ?S)) - fst (\<omega> (r + min 0 ?S))
          = fst (pfut r T \<omega> (min u ?S))" using Tr by simp
    qed
  qed
  show ?thesis
    by (rule martingale_future_of_past[OF r rT setsP PS A pos Zm mg])
qed

text \<open>Clause (iv) does NOT follow the same way, and the obstruction is
  algebraic rather than probabilistic: \<^const>\<open>outerp\<close> is QUADRATIC, so the
  compensated process of the rebased future is not the increment of the
  compensated process.  Expanding,

  \<^item> \<open>outerp (a - b) = outerp a - (a \<otimes> b + b \<otimes> a) + outerp b\<close>,

  so with \<open>a = X\<^sub>t\<close>, \<open>b = X\<^sub>r\<close>,

  \<^item> \<open>outerp (X\<^sub>t - X\<^sub>r) - (Y\<^sub>t - Y\<^sub>r)
       = (outerp X\<^sub>t - Y\<^sub>t) - (X\<^sub>t \<otimes> X\<^sub>r + X\<^sub>r \<otimes> X\<^sub>t) + (outerp X\<^sub>r + Y\<^sub>r)\<close>.

  The first bracket is clause (iv) for \<open>P\<close>; the third is constant in \<open>t\<close> and
  \<open>\<F>\<^sub>r\<close>-measurable.  The middle term is the real work: it is a martingale
  only because \<open>X\<^sub>r\<close> is \<open>\<F>\<^sub>r\<close>-measurable, so what is needed is "pulling out
  what is known" --- a martingale multiplied entrywise by a fixed
  \<open>F 0\<close>-measurable factor is again a martingale.  The AFP has the
  conditional-expectation half of that (\<open>cond_exp_measurable_mult\<close> in
  \<open>Conditional_Expectation_Banach\<close>, for REAL-valued factors); what is
  missing here is the martingale-level statement, the entrywise lift to
  \<open>real^'n^'n\<close> through @{thm [source] martingale_matI}, and the
  integrability of \<open>X\<^sub>t $ i * X\<^sub>r $ j\<close>, which the class's fourth moments
  (@{thm [source] paper_pair_class_fourth_moment}) supply by
  Cauchy--Schwarz.\<close>

lemma outerp_diff:
  fixes a b :: "real^'n::finite"
  shows "outerp (a - b) = outerp a - ((\<chi> i j. a $ i * b $ j)
      + (\<chi> i j. b $ i * a $ j)) + outerp b"
  by (simp add: outerp_def vec_eq_iff algebra_simps)

lemma outerp_diff_compensated:
  fixes a b :: "real^'n::finite" and Ya Yb :: "real^'n^'n"
  shows "outerp (a - b) - (Ya - Yb)
      = (outerp a - Ya) - ((\<chi> i j. a $ i * b $ j) + (\<chi> i j. b $ i * a $ j))
        + (outerp b + Yb)"
  by (simp add: outerp_diff)

text \<open>"Pulling out what is known", at the MARTINGALE level.  The AFP has the
  conditional-expectation half (\<open>cond_exp_measurable_mult\<close>); this is what
  the cross term of @{thm [source] outerp_diff_compensated} actually needs.
  Note the factor must be measurable for the filtration at the INITIAL time,
  not merely somewhere along it --- otherwise it is not adapted.\<close>

lemma martingale_mult_measurable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real" and v :: "'a \<Rightarrow> real"
  assumes mg: "martingale M F (0::real) X"
    and vm: "v \<in> borel_measurable (F 0)"
    and int: "\<And>u. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. v \<omega> * X u \<omega>)"
  shows "martingale M F 0 (\<lambda>u \<omega>. v \<omega> * X u \<omega>)"
proof -
  interpret MG: martingale M F "0::real" X by (rule mg)
  have FM: "filtered_measure M F (0::real)" by unfold_locales
  have vFu: "v \<in> borel_measurable (F u)" if u: "0 \<le> u" for u
  proof -
    have "subalgebra (F u) (F 0)"
      using MG.subalgebras[OF u] MG.subalgebras[OF order_refl]
        MG.sets_F_mono[OF order_refl u]
      by (simp add: subalgebra_def)
    then show ?thesis by (rule measurable_from_subalg[OF _ vm])
  qed
  have pm: "(\<lambda>\<omega>. v \<omega> * X u \<omega>) \<in> borel_measurable (F u)" if u: "0 \<le> u" for u
    using vFu[OF u] MG.adapted[OF u] by simp
  show ?thesis
  proof (rule MG.martingale_of_set_integral_eq)
    show "adapted_process M F 0 (\<lambda>u \<omega>. v \<omega> * X u \<omega>)"
      unfolding adapted_process_def adapted_process_axioms_def
      using FM pm by blast
    show "integrable M (\<lambda>\<omega>. v \<omega> * X i \<omega>)" if "0 \<le> i" for i by (rule int[OF that])
    fix C and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and C: "C \<in> sets (F i)"
    have j0: "0 \<le> j" using ij by simp
    interpret SF: sigma_finite_subalgebra M "F i" using ij(1) by blast
    have CM: "C \<in> sets M" using C MG.sets_F_subset[OF ij(1)] by blast
    have ae1: "AE \<omega> in M. cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<omega>
        = v \<omega> * cond_exp M (F i) (X j) \<omega>"
      by (rule SF.cond_exp_measurable_mult(2)
          [OF int[OF j0] MG.integrable[OF j0] vFu[OF ij(1)]])
    have ae2: "AE \<omega> in M. X i \<omega> = cond_exp M (F i) (X j) \<omega>"
      by (rule MG.martingale_property[OF ij(1) ij(2)])
    have ae: "AE \<omega> in M. cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<omega> = v \<omega> * X i \<omega>"
      using ae1 ae2 by eventually_elim simp
    have aeC: "AE \<omega>\<in>C in M. cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<omega> = v \<omega> * X i \<omega>"
      using ae by (auto elim: eventually_mono)
    have m1: "cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>) \<in> borel_measurable M"
      by (rule SF.borel_measurable_cond_exp')
    have m2: "(\<lambda>\<omega>. v \<omega> * X i \<omega>) \<in> borel_measurable M"
      using int[OF ij(1)] by simp
    have "set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X j \<omega>)
        = set_lebesgue_integral M C (cond_exp M (F i) (\<lambda>\<omega>. v \<omega> * X j \<omega>))"
      by (rule SF.cond_exp_set_integral[OF int[OF j0] C])
    also have "\<dots> = set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X i \<omega>)"
      by (rule set_lebesgue_integral_cong_AE[OF CM m1 m2 aeC])
    finally show "set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X i \<omega>)
        = set_lebesgue_integral M C (\<lambda>\<omega>. v \<omega> * X j \<omega>)" ..
  qed
qed

text \<open>The two ingredients @{thm [source] martingale_mult_measurable} needs on
  the way to clause (iv): a product is integrable as soon as both squares
  are, and the cross term of @{thm [source] outerp_diff_compensated} is a
  matrix martingale, entry by entry.\<close>

lemma integrable_mult_of_sq:
  fixes f g :: "'a \<Rightarrow> real"
  assumes fm: "f \<in> borel_measurable M" and gm: "g \<in> borel_measurable M"
    and f2: "integrable M (\<lambda>\<omega>. (f \<omega>)\<^sup>2)" and g2: "integrable M (\<lambda>\<omega>. (g \<omega>)\<^sup>2)"
  shows "integrable M (\<lambda>\<omega>. f \<omega> * g \<omega>)"
proof -
  have b: "integrable M (\<lambda>\<omega>. ((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2)" using f2 g2 by simp
  have pm: "(\<lambda>\<omega>. f \<omega> * g \<omega>) \<in> borel_measurable M" using fm gm by simp
  have ae: "AE \<omega> in M. norm (f \<omega> * g \<omega>) \<le> norm (((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2)"
  proof (rule AE_I2)
    fix \<omega>
    have "(0::real) \<le> (\<bar>f \<omega>\<bar> - \<bar>g \<omega>\<bar>)\<^sup>2" by simp
    also have "(\<bar>f \<omega>\<bar> - \<bar>g \<omega>\<bar>)\<^sup>2 = (f \<omega>)\<^sup>2 - 2 * (\<bar>f \<omega>\<bar> * \<bar>g \<omega>\<bar>) + (g \<omega>)\<^sup>2"
      by (simp add: power2_diff)
    finally have le: "2 * (\<bar>f \<omega>\<bar> * \<bar>g \<omega>\<bar>) \<le> (f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2" by simp
    have nn: "(0::real) \<le> ((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2" by simp
    show "norm (f \<omega> * g \<omega>) \<le> norm (((f \<omega>)\<^sup>2 + (g \<omega>)\<^sup>2) / 2)"
      using le nn by (simp add: abs_mult)
  qed
  show ?thesis by (rule Bochner_Integration.integrable_bound[OF b pm ae])
qed

lemma martingale_cross_measurable:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real^'n::finite" and v :: "'a \<Rightarrow> real^'n"
  assumes mg: "\<And>i. martingale M F (0::real) (\<lambda>t \<omega>. X t \<omega> $ i)"
    and vm: "\<And>j. (\<lambda>\<omega>. v \<omega> $ j) \<in> borel_measurable (F 0)"
    and int: "\<And>u i j. 0 \<le> u \<Longrightarrow> integrable M (\<lambda>\<omega>. v \<omega> $ j * X u \<omega> $ i)"
  shows "martingale M F 0
      (\<lambda>t \<omega>. (\<chi> i j. X t \<omega> $ i * v \<omega> $ j) + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j))"
proof (rule martingale_matI)
  fix p q :: 'n
  have mgp: "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ p)" by (rule mg)
  have mgq: "martingale M F 0 (\<lambda>t \<omega>. X t \<omega> $ q)" by (rule mg)
  have vmp: "(\<lambda>\<omega>. v \<omega> $ p) \<in> borel_measurable (F 0)" by (rule vm)
  have vmq: "(\<lambda>\<omega>. v \<omega> $ q) \<in> borel_measurable (F 0)" by (rule vm)
  have intqp: "integrable M (\<lambda>\<omega>. v \<omega> $ q * X u \<omega> $ p)" if "0 \<le> u" for u
    by (rule int[OF that])
  have intpq: "integrable M (\<lambda>\<omega>. v \<omega> $ p * X u \<omega> $ q)" if "0 \<le> u" for u
    by (rule int[OF that])
  have m1: "martingale M F 0 (\<lambda>t \<omega>. v \<omega> $ q * X t \<omega> $ p)"
    by (rule martingale_mult_measurable[OF mgp vmq intqp])
  have m2: "martingale M F 0 (\<lambda>t \<omega>. v \<omega> $ p * X t \<omega> $ q)"
    by (rule martingale_mult_measurable[OF mgq vmp intpq])
  have m: "martingale M F 0 (\<lambda>t \<omega>. v \<omega> $ q * X t \<omega> $ p + v \<omega> $ p * X t \<omega> $ q)"
    by (rule martingale_add[OF m1 m2])
  have eq: "(\<lambda>t \<omega>. ((\<chi> i j. X t \<omega> $ i * v \<omega> $ j)
        + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j)) $ p $ q)
      = (\<lambda>t \<omega>. v \<omega> $ q * X t \<omega> $ p + v \<omega> $ p * X t \<omega> $ q)"
  proof (intro ext)
    fix t :: real and \<omega>
    show "((\<chi> i j. X t \<omega> $ i * v \<omega> $ j) + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j)) $ p $ q
        = v \<omega> $ q * X t \<omega> $ p + v \<omega> $ p * X t \<omega> $ q"
      by (simp add: mult.commute)
  qed
  show "martingale M F 0 (\<lambda>t \<omega>.
      ((\<chi> i j. X t \<omega> $ i * v \<omega> $ j) + (\<chi> i j. v \<omega> $ i * X t \<omega> $ j)) $ p $ q)"
    unfolding eq by (rule m)
qed

text \<open>Differences of martingales.  @{thm [source] martingale_add} is in the
  development but its subtractive companion is in neither the development nor
  the AFP, and the decomposition of
  @{thm [source] outerp_diff_compensated} needs it.\<close>

lemma martingale_diff:
  fixes X Y :: "real \<Rightarrow> 'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes mX: "martingale M F (0::real) X" and mY: "martingale M F 0 Y"
  shows "martingale M F 0 (\<lambda>u \<omega>. X u \<omega> - Y u \<omega>)"
proof -
  interpret MX: martingale M F "0::real" X by (rule mX)
  interpret MY: martingale M F "0::real" Y by (rule mY)
  have FM: "filtered_measure M F (0::real)" by unfold_locales
  show ?thesis
  proof (rule MX.martingale_of_set_integral_eq)
    have dm: "(\<lambda>\<omega>. X u \<omega> - Y u \<omega>) \<in> borel_measurable (F u)" if u: "0 \<le> u" for u
      using MX.adapted[OF u] MY.adapted[OF u] by simp
    show "adapted_process M F 0 (\<lambda>u \<omega>. X u \<omega> - Y u \<omega>)"
      unfolding adapted_process_def adapted_process_axioms_def
      using FM dm by blast
    show "integrable M (\<lambda>\<omega>. X i \<omega> - Y i \<omega>)" if "0 \<le> i" for i
      using MX.integrable[OF that] MY.integrable[OF that] by simp
    fix C and i j :: real
    assume ij: "0 \<le> i" "i \<le> j" and C: "C \<in> sets (F i)"
    have j0: "0 \<le> j" using ij by simp
    have CM: "C \<in> sets M" using C MX.sets_F_subset[OF ij(1)] by blast
    have split: "set_lebesgue_integral M C (\<lambda>\<omega>. X u \<omega> - Y u \<omega>)
        = set_lebesgue_integral M C (X u) - set_lebesgue_integral M C (Y u)"
      if u: "0 \<le> u" for u
    proof -
      have iX: "integrable M (\<lambda>\<omega>. indicator C \<omega> *\<^sub>R X u \<omega>)"
        by (rule integrable_mult_indicator[OF CM MX.integrable[OF u]])
      have iY: "integrable M (\<lambda>\<omega>. indicator C \<omega> *\<^sub>R Y u \<omega>)"
        by (rule integrable_mult_indicator[OF CM MY.integrable[OF u]])
      have "(\<integral>\<omega>. indicator C \<omega> *\<^sub>R (X u \<omega> - Y u \<omega>) \<partial>M)
          = (\<integral>\<omega>. indicator C \<omega> *\<^sub>R X u \<omega> - indicator C \<omega> *\<^sub>R Y u \<omega> \<partial>M)"
        by (simp add: scaleR_diff_right)
      also have "\<dots> = (\<integral>\<omega>. indicator C \<omega> *\<^sub>R X u \<omega> \<partial>M)
          - (\<integral>\<omega>. indicator C \<omega> *\<^sub>R Y u \<omega> \<partial>M)"
        by (rule Bochner_Integration.integral_diff[OF iX iY])
      finally show ?thesis unfolding set_lebesgue_integral_def .
    qed
    have sX: "set_lebesgue_integral M C (X i) = set_lebesgue_integral M C (X j)"
      by (rule MX.set_integral_eq[OF C ij(1) ij(2)])
    have sY: "set_lebesgue_integral M C (Y i) = set_lebesgue_integral M C (Y j)"
      by (rule MY.set_integral_eq[OF C ij(1) ij(2)])
    show "set_lebesgue_integral M C (\<lambda>\<omega>. X i \<omega> - Y i \<omega>)
        = set_lebesgue_integral M C (\<lambda>\<omega>. X j \<omega> - Y j \<omega>)"
      using split[OF ij(1)] split[OF j0] sX sY by simp
  qed
qed

subsection \<open>The shifted processes of a class member\<close>

lemma measurable_snd_borel:
  "(snd :: (real^'n::finite) \<times> (real^'n^'n) \<Rightarrow> real^'n^'n) \<in> borel_measurable borel"
  using measurable_snd[of "borel :: (real^'n) measure"
      "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)

lemma paper_pair_class_comp_martingale:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> paper_pair_class k L T x"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
  using Q unfolding paper_pair_class_def by blast

text \<open>Both coordinate processes of a class member, restarted at \<open>r\<close>: the
  clock is shifted by @{thm [source] martingale_time_change} and the horizon
  cap becomes invisible, since \<open>r + min u (T-r) \<le> T\<close> always.\<close>

lemma paper_pair_class_shifted_X_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and P: "P \<in> paper_pair_class k L T x"
  shows "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
      (\<lambda>u \<omega>. fst (\<omega> (r + min u (T - r))))"
proof -
  let ?S = "T - r"
  have Tr: "0 \<le> ?S" using rT by simp
  have MGX: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    by (rule paper_pair_class_X_martingale[OF P])
  have s0: "0 \<le> r + min u ?S" if "0 \<le> u" for u :: real using r Tr that by simp
  have smono: "r + min u ?S \<le> r + min v ?S" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mg1: "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)) 0
      (\<lambda>u \<omega>. fst (\<omega> (min (r + min u ?S) T)))"
    by (rule martingale_time_change[OF MGX s0 smono])
  have eqmin: "min (r + min u ?S) T = r + min u ?S" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then have "r + min u ?S \<le> T" by simp
    then show ?thesis by simp
  qed
  show ?thesis using mg1 by (simp add: eqmin)
qed

lemma paper_pair_class_shifted_comp_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and P: "P \<in> paper_pair_class k L T x"
  shows "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (r + min u (T - r))))
          - snd (\<omega> (r + min u (T - r))))"
proof -
  let ?S = "T - r"
  have Tr: "0 \<le> ?S" using rT by simp
  have MGY: "martingale P (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min u T))) - snd (\<omega> (min u T)))"
    by (rule paper_pair_class_comp_martingale[OF P])
  have s0: "0 \<le> r + min u ?S" if "0 \<le> u" for u :: real using r Tr that by simp
  have smono: "r + min u ?S \<le> r + min v ?S" if "0 \<le> u" "u \<le> v" for u v :: real
    using that by simp
  have mg1: "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)) 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (min (r + min u ?S) T)))
          - snd (\<omega> (min (r + min u ?S) T)))"
    by (rule martingale_time_change[OF MGY s0 smono])
  have eqmin: "min (r + min u ?S) T = r + min u ?S" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then have "r + min u ?S \<le> T" by simp
    then show ?thesis by simp
  qed
  show ?thesis using mg1 by (simp add: eqmin)
qed

text \<open>The compensated process OF THE REBASED FUTURE, as a martingale under
  \<open>P\<close> itself in the shifted filtration.  This is the clause-(iv) counterpart
  of @{thm [source] paper_pair_class_shifted_X_martingale}, and it is NOT the
  same statement: \<^const>\<open>outerp\<close> is quadratic, so the compensated process of
  the rebased future is not the increment of the compensated process.  The
  decomposition is @{thm [source] outerp_diff_compensated} --- the class's own
  clause (iv) restarted at \<open>r\<close>, minus the cross term
  (@{thm [source] martingale_cross_measurable}, which is where
  \<open>\<F>\<^sub>r\<close>-measurability of \<open>X\<^sub>r\<close> is used), plus an \<open>\<F>\<^sub>r\<close>-measurable constant.

  Both the positive-measure conditioning route (\<open>pfut_law_comp_martingale\<close>)
  and the kernel route of (b3) consume it, which is why it is stated
  separately rather than inlined.\<close>

lemma paper_pair_class_pfut_comp_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> paper_pair_class k L T x"
  shows "martingale P
      (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
      (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
          - snd (pfut r T \<omega> (min u (T - r))))"
proof -
  let ?S = "T - r"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have T0: "0 \<le> T" using r rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF P])
  have PS: "prob_space P" by (rule paper_pair_class_prob[OF P])
  have mem: "r + min u ?S \<in> {0..T}" if "0 \<le> u" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then show ?thesis using r that Tr by simp
  qed

  \<comment> \<open>(A) the class's own clause (iv), restarted at \<open>r\<close>\<close>
  have mgA: "martingale P ?FP 0
      (\<lambda>u \<omega>. outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))"
    by (rule paper_pair_class_shifted_comp_martingale[OF r rT P])
  interpret MGA: martingale P ?FP 0
      "\<lambda>u \<omega>. outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S))"
    by (rule mgA)

  \<comment> \<open>(B) the cross term\<close>
  have mgX: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)))"
    by (rule paper_pair_class_shifted_X_martingale[OF r rT P])
  have mgXi: "martingale P ?FP 0 (\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) $ i)" for i
    by (rule martingale_vec_nth[OF mgX])
  have startm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable (?FP 0)"
    for j
  proof -
    interpret MX: martingale P ?FP 0 "\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) $ j"
      by (rule mgXi)
    have "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min 0 ?S)) $ j)
        \<in> borel_measurable (?FP 0)"
      by (rule MX.adapted[of 0]) simp
    then show ?thesis using Tr by simp
  qed
  have PmX: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min u ?S)) $ i) \<in> borel_measurable P"
    if u: "0 \<le> u" for u i
  proof -
    interpret MX: martingale P ?FP 0 "\<lambda>u \<omega>. fst (\<omega> (r + min u ?S)) $ i"
      by (rule mgXi)
    show ?thesis
      by (rule measurable_from_subalg[OF MGA.subalgebras[OF u] MX.adapted[OF u]])
  qed
  have Pstart: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable P" for j
    using PmX[of 0 j] Tr by simp
  have intB: "integrable P
      (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j * fst (\<omega> (r + min u ?S)) $ i)"
    if u: "0 \<le> u" for u i j
  proof (rule integrable_mult_of_sq)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable P"
      by (rule Pstart)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + min u ?S)) $ i) \<in> borel_measurable P"
      by (rule PmX[OF u])
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> r) $ j)\<^sup>2)"
      using r rT by (intro paper_pair_class_sq_integrable[OF T0 L0 P]) simp
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> (r + min u ?S)) $ i)\<^sup>2)"
      using mem[OF u] by (intro paper_pair_class_sq_integrable[OF T0 L0 P]) simp
  qed
  have mgB: "martingale P ?FP 0 (\<lambda>u \<omega>.
      (\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
      + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))"
  proof (rule martingale_cross_measurable)
    show "martingale P ?FP 0 (\<lambda>t \<omega>. fst (\<omega> (r + min t ?S)) $ i)" for i
      by (rule mgXi)
    show "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j) \<in> borel_measurable (?FP 0)" for j
      by (rule startm)
    show "integrable P
        (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ j * fst (\<omega> (r + min u ?S)) $ i)"
      if "0 \<le> u" for u i j by (rule intB[OF that])
  qed

  \<comment> \<open>(C) the \<open>\<F>\<^sub>r\<close>-measurable constant\<close>
  have evr: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> ?FP 0 \<rightarrow>\<^sub>M borel"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use r Tr in auto)
  have Cmeas: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r)) + snd (\<omega> r))
      \<in> borel_measurable (?FP 0)"
  proof -
    have m1: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r))) \<in> borel_measurable (?FP 0)"
      by (rule measurable_compose
          [OF measurable_compose[OF evr measurable_fst_borel] outerp_borel])
    have m2: "(\<lambda>\<omega> :: 'n pairpath. snd (\<omega> r)) \<in> borel_measurable (?FP 0)"
      by (rule measurable_compose[OF evr measurable_snd_borel])
    show ?thesis by (rule borel_measurable_add[OF m1 m2])
  qed
  have CmeasP: "(\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r)) + snd (\<omega> r))
      \<in> borel_measurable P"
    by (rule measurable_from_subalg[OF MGA.subalgebras[OF order_refl] Cmeas])
  have Cint: "integrable P (\<lambda>\<omega> :: 'n pairpath. outerp (fst (\<omega> r)) + snd (\<omega> r))"
  proof (rule integrable_mat_entries[OF CmeasP])
    fix i j
    have eqf: "(\<lambda>\<omega> :: 'n pairpath. (outerp (fst (\<omega> r)) + snd (\<omega> r)) $ i $ j)
        = (\<lambda>\<omega>. fst (\<omega> r) $ i * fst (\<omega> r) $ j + snd (\<omega> r) $ i $ j)"
      by (rule ext) (simp add: outerp_def)
    have i1: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r) $ i * fst (\<omega> r) $ j)"
      using intB[of 0 i j] Tr by simp
    have i2: "integrable P (\<lambda>\<omega> :: 'n pairpath. snd (\<omega> r) $ i $ j)"
      using r rT by (intro paper_pair_class_Y_entry_integrable[OF T0 L0 P]) simp
    show "integrable P
        (\<lambda>\<omega> :: 'n pairpath. (outerp (fst (\<omega> r)) + snd (\<omega> r)) $ i $ j)"
      unfolding eqf by (rule Bochner_Integration.integrable_add[OF i1 i2])
  qed
  have mgC: "martingale P ?FP 0 (\<lambda>_ \<omega> :: 'n pairpath.
      outerp (fst (\<omega> r)) + snd (\<omega> r))"
    by (rule MGA.martingale_const_fun[OF Cint Cmeas])

  \<comment> \<open>combine, and recognise the result as the future's compensated process\<close>
  have mgABC: "martingale P ?FP 0 (\<lambda>u \<omega>.
      (outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))
      - ((\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
         + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))
      + (outerp (fst (\<omega> r)) + snd (\<omega> r)))"
    by (rule martingale_add[OF martingale_diff[OF mgA mgB] mgC])
  show ?thesis
  proof (rule martingale_cong_ge[OF mgABC])
    fix u :: real assume u: "0 \<le> u"
    have m: "min u ?S \<in> {0..?S}" using u Tr by simp
    show "(\<lambda>\<omega> :: 'n pairpath.
          (outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))
          - ((\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
             + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))
          + (outerp (fst (\<omega> r)) + snd (\<omega> r)))
        = (\<lambda>\<omega>. outerp (fst (pfut r T \<omega> (min u ?S)))
            - snd (pfut r T \<omega> (min u ?S)))"
    proof (rule ext)
      fix \<omega> :: "'n pairpath"
      have f1: "fst (pfut r T \<omega> (min u ?S)) = fst (\<omega> (r + min u ?S)) - fst (\<omega> r)"
        by (rule pfut_fst[OF m])
      have f2: "snd (pfut r T \<omega> (min u ?S)) = snd (\<omega> (r + min u ?S)) - snd (\<omega> r)"
        using m by (simp add: pfut_apply)
      show "(outerp (fst (\<omega> (r + min u ?S))) - snd (\<omega> (r + min u ?S)))
          - ((\<chi> i j. fst (\<omega> (r + min u ?S)) $ i * fst (\<omega> r) $ j)
             + (\<chi> i j. fst (\<omega> r) $ i * fst (\<omega> (r + min u ?S)) $ j))
          + (outerp (fst (\<omega> r)) + snd (\<omega> r))
        = outerp (fst (pfut r T \<omega> (min u ?S)))
            - snd (pfut r T \<omega> (min u ?S))"
        unfolding f1 f2 by (rule outerp_diff_compensated[symmetric])
    qed
  qed
qed

text \<open>Clause (iv) for the conditioned future law.  The decomposition is
  @{thm [source] outerp_diff_compensated}; the three summands are the class's
  own clause (iv) restarted at \<open>r\<close>, the cross term
  (@{thm [source] martingale_cross_measurable}, which is where \<open>\<F>\<^sub>r\<close>-
  measurability of \<open>X\<^sub>r\<close> is used), and an \<open>\<F>\<^sub>r\<close>-measurable constant.\<close>

lemma pfut_law_comp_martingale:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> paper_pair_class k L T x"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
  shows "martingale (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
      (natural_filtration (pair_law_of (T - r) (pfut r T) (uniform_measure P A))
        0 (\<lambda>v w. w v)) 0
      (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?Q = "pair_law_of ?S (pfut r T) ?M"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have T0: "0 \<le> T" using r rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF P])
  have PS: "prob_space P" by (rule paper_pair_class_prob[OF P])
  have FP0: "?FP 0 = natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r"
    using Tr by simp
  have mem: "r + min u ?S \<in> {0..T}" if "0 \<le> u" for u :: real
  proof -
    have "min u ?S \<le> ?S" by simp
    then show ?thesis using r that Tr by simp
  qed

  \<comment> \<open>the integrand is a random variable for the natural filtration of \<open>?Q\<close>\<close>
  have Zm: "(\<lambda>w :: 'n pairpath.
        outerp (fst (w (min u ?S))) - snd (w (min u ?S)))
      \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
    if u: "0 \<le> u" for u
  proof -
    have ev: "(\<lambda>w :: 'n pairpath. w (min u ?S))
        \<in> natural_filtration ?Q 0 (\<lambda>v w. w v) u \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use u Tr in auto)
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u ?S))))
        \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
      by (rule measurable_compose
          [OF measurable_compose[OF ev measurable_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w (min u ?S)))
        \<in> borel_measurable (natural_filtration ?Q 0 (\<lambda>v w. w v) u)"
      by (rule measurable_compose[OF ev measurable_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed

  \<comment> \<open>the whole decomposition is now a lemma of its own\<close>
  have mg: "martingale P ?FP 0 (\<lambda>u \<omega>.
      outerp (fst (pfut r T \<omega> (min u ?S))) - snd (pfut r T \<omega> (min u ?S)))"
    by (rule paper_pair_class_pfut_comp_martingale[OF r rT L0 P])
  show ?thesis
    by (rule martingale_future_of_past[OF r rT setsP PS A pos Zm mg])
qed

text \<open>All four clauses together: \<^emph>\<open>conditioning on an event of the past
  leaves the future in the class, started at the origin.\<close>  This is the
  structural fact the \<open>\<le>\<close> half of (2.9) turns on, and it needs no regular
  conditional distribution.\<close>

theorem paper_pair_class_future_of_past:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and L0: "0 \<le> L"
    and P: "P \<in> paper_pair_class k L T x"
    and A: "A \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    and pos: "0 < measure P A"
  shows "pair_law_of (T - r) (pfut r T) (uniform_measure P A)
      \<in> paper_pair_class k L (T - r) 0"
proof -
  let ?S = "T - r"
  let ?M = "uniform_measure P A"
  let ?Q = "pair_law_of ?S (pfut r T) ?M"
  have Tr: "0 \<le> ?S" using rT by simp
  have setsP: "sets P = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    by (rule paper_pair_class_sets[OF P])
  interpret PP: prob_space P by (rule paper_pair_class_prob[OF P])
  interpret MGX: martingale P
      "natural_filtration P 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u)" 0
      "\<lambda>u \<omega>. fst (\<omega> (min u T))"
    by (rule paper_pair_class_X_martingale[OF P])
  have AM: "A \<in> sets P" using A MGX.sets_F_subset[OF r] by blast
  have setsM: "sets ?M = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    using setsP by simp
  have ea0: "emeasure P A \<noteq> 0" using pos by (simp add: PP.emeasure_eq_measure)
  have eafin: "emeasure P A \<noteq> \<infinity>" by (simp add: PP.emeasure_eq_measure)
  have PM: "prob_space ?M" by (rule prob_space_uniform_measure[OF ea0 eafin])
  have phim: "pfut r T
      \<in> ?M \<rightarrow>\<^sub>M borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
    by (rule pfut_measurable_law[OF r rT setsM])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule prob_space.prob_space_distr[OF PM phim])
  have cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    using P unfolding paper_pair_class_def by blast
  show ?thesis
    unfolding paper_pair_class_def
  proof (intro CollectI conjI)
    show "prob_space ?Q" by (rule PQ)
    show "sets ?Q = sets (borel_of (mtopology_of
        (path_metric ?S :: ('n pairpath) metric)))"
      by (rule sets_pair_law_of)
    show "AE w in ?Q. fst (w 0) = 0 \<and> snd (w 0) = 0"
      by (rule pfut_law_start[OF r rT setsP])
    show "AE w in ?Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> ?S \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
      by (rule pfut_law_diffquot[OF r rT setsP AM cov])
    show "martingale ?Q (natural_filtration ?Q 0 (\<lambda>t w. w t)) 0
        (\<lambda>t w. fst (w (min t ?S)))"
      by (rule pfut_law_X_martingale[OF r rT P A pos])
    show "martingale ?Q (natural_filtration ?Q 0 (\<lambda>t w. w t)) 0
        (\<lambda>t w. outerp (fst (w (min t ?S))) - snd (w (min t ?S)))"
      by (rule pfut_law_comp_martingale[OF r rT L0 P A pos])
  qed
qed

subsection \<open>The survival event belongs to the past\<close>

text \<open>\<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close> says exactly that the path never
  leaves \<open>K\<close> on \<open>{0..r}\<close>, and for a CONTINUOUS path against a CLOSED \<open>K\<close>
  that is decided by the rational times alone.  So the survival event is
  \<open>\<F>\<^sub>r\<close>-measurable --- which is what lets it be used as the conditioning
  event \<open>A\<close> of @{thm [source] paper_pair_class_future_of_past}.\<close>

lemma survival_event_filtration:
  fixes P :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and K: "closed K"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "{\<omega> \<in> space P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K}
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
proof -
  let ?F = "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r"
  let ?Qs = "{0..r} \<inter> (\<rat> :: real set)"
  have spP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have clo: "closure ?Qs = {0..r}"
  proof (rule antisym)
    show "closure ?Qs \<subseteq> {0..r}" by (intro closure_minimal) auto
    show "{0..r} \<subseteq> closure ?Qs" using r by (auto intro: Icc_rats_dense)
  qed
  have key: "(pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K)
      \<longleftrightarrow> (\<forall>q \<in> ?Qs. fst (\<omega> q) \<in> K)" if w: "\<omega> \<in> space P" for \<omega>
  proof
    assume h: "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K"
    show "\<forall>q \<in> ?Qs. fst (\<omega> q) \<in> K"
    proof
      fix q assume q: "q \<in> ?Qs"
      show "fst (\<omega> q) \<in> K"
      proof (rule ccontr)
        assume nk: "fst (\<omega> q) \<notin> K"
        have "pexit r K (\<lambda>t. fst (\<omega> t)) \<le> q"
          unfolding pexit_def using r q nk by (intro etime_le_of_mem) auto
        with h q have "q = r" by simp
        then show False using nk h by simp
      qed
    qed
  next
    assume h: "\<forall>q \<in> ?Qs. fst (\<omega> q) \<in> K"
    have cw: "continuous_on {0..T} \<omega>"
      using w spP by (simp add: mspace_path_metric_continuous)
    have c0: "continuous_on {0..r} \<omega>"
      by (rule continuous_on_subset[OF cw]) (use r rT in auto)
    have c1: "continuous_on (closure ?Qs) (\<lambda>t. fst (\<omega> t))"
      unfolding clo by (rule continuous_on_fst[OF c0])
    have sub: "(\<lambda>t. fst (\<omega> t)) ` ?Qs \<subseteq> K" using h by auto
    have "(\<lambda>t. fst (\<omega> t)) ` closure ?Qs \<subseteq> K"
      by (rule image_closure_subset[OF c1 K sub])
    then have all: "fst (\<omega> t) \<in> K" if "t \<in> {0..r}" for t
      using that clo by auto
    have "pexit r K (\<lambda>t. fst (\<omega> t)) = r"
    proof -
      have emp: "{t. 0 \<le> t \<and> t \<le> r \<and> fst (\<omega> t) \<in> - K} = {}" using all by auto
      have "pexit r K (\<lambda>t. fst (\<omega> t))
          = Inf ({t. 0 \<le> t \<and> t \<le> r \<and> fst (\<omega> t) \<in> - K} \<union> {r})"
        unfolding pexit_def etime_def ..
      also have "\<dots> = r" unfolding emp by simp
      finally show ?thesis .
    qed
    moreover have "fst (\<omega> r) \<in> K" using all r by simp
    ultimately show "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K" by simp
  qed
  have coord: "{\<omega> \<in> space P. fst (\<omega> q) \<in> K} \<in> sets ?F" if q: "q \<in> ?Qs" for q
  proof -
    have ev: "(\<lambda>\<omega> :: 'n pairpath. \<omega> q) \<in> ?F \<rightarrow>\<^sub>M borel"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use q in auto)
    have m: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> q)) \<in> borel_measurable ?F"
      by (rule measurable_compose[OF ev measurable_fst_borel])
    have "{\<omega> \<in> space ?F. fst (\<omega> q) \<in> K} \<in> sets ?F"
      using m borel_closed[OF K] by measurable
    then show ?thesis by simp
  qed
  have zero: "(0::real) \<in> ?Qs" using r Rats_0 by simp
  have ne: "?Qs \<noteq> {}" using zero by blast
  have eq: "{\<omega> \<in> space P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K}
      = (\<Inter>q \<in> ?Qs. {\<omega> \<in> space P. fst (\<omega> q) \<in> K})"
  proof (rule set_eqI, rule iffI)
    fix \<omega> :: "'n pairpath"
    assume "\<omega> \<in> {\<omega> \<in> space P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K}"
    then show "\<omega> \<in> (\<Inter>q \<in> ?Qs. {\<omega> \<in> space P. fst (\<omega> q) \<in> K})"
      using key by auto
  next
    fix \<omega> :: "'n pairpath"
    assume h: "\<omega> \<in> (\<Inter>q \<in> ?Qs. {\<omega> \<in> space P. fst (\<omega> q) \<in> K})"
    have w: "\<omega> \<in> space P" using h zero by blast
    show "\<omega> \<in> {\<omega> \<in> space P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K}"
      using w h key[OF w] by blast
  qed
  have cnt: "countable ?Qs" using countable_rat by blast
  show ?thesis
    unfolding eq using cnt ne coord by (intro sets.countable_INT') auto
qed

subsection \<open>Towards the regular conditional distribution\<close>

text \<open>The workhorse of the disintegration argument.  Every condition
  defining the class is LINEAR in the measure --- \<open>\<mu> C = 1\<close> for the initial
  and covariation clauses, \<open>\<integral> (X\<^sub>t - X\<^sub>s) 1\<^sub>A d\<mu> = 0\<close> for the martingale
  clauses --- so passing from "it holds for \<open>P(\<sqdot> | A)\<close>, every \<open>A \<in> \<F>\<^sub>r\<close>" to
  "it holds for the conditional law at almost every \<open>\<omega>\<close>" never needs a
  separation theorem.  It only needs THIS: a \<open>\<G>\<close>-measurable function all of
  whose \<open>\<G>\<close>-set integrals vanish is almost everywhere zero.\<close>

lemma AE_nonpos_of_set_integral_zero:
  fixes f :: "'a \<Rightarrow> real"
  assumes G: "subalgebra M G" and int: "integrable M f"
    and fm: "f \<in> borel_measurable G"
    and z: "\<And>A. A \<in> sets G \<Longrightarrow> set_lebesgue_integral M A f = 0"
  shows "AE \<omega> in M. f \<omega> \<le> 0"
proof -
  have spG: "space G = space M" using G by (simp add: subalgebra_def)
  let ?A = "{\<omega> \<in> space G. 0 < f \<omega>}"
  have A: "?A \<in> sets G" using fm by measurable
  have AM: "?A \<in> sets M" using A G by (auto simp: subalgebra_def)
  have ii: "integrable M (\<lambda>\<omega>. indicator ?A \<omega> *\<^sub>R f \<omega>)"
    by (rule integrable_mult_indicator[OF AM int])
  have inn: "AE \<omega> in M. 0 \<le> indicator ?A \<omega> *\<^sub>R f \<omega>"
    by (rule AE_I2) (auto simp: indicator_def)
  have zi: "(\<integral>\<omega>. indicator ?A \<omega> *\<^sub>R f \<omega> \<partial>M) = 0"
    using z[OF A] unfolding set_lebesgue_integral_def .
  have "AE \<omega> in M. indicator ?A \<omega> *\<^sub>R f \<omega> = 0"
    using ii inn zi by (simp add: integral_nonneg_eq_0_iff_AE)
  moreover have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  ultimately show ?thesis
    by eventually_elim (auto simp: indicator_def spG split: if_split_asm)
qed

lemma AE_zero_of_set_integral_zero:
  fixes f :: "'a \<Rightarrow> real"
  assumes G: "subalgebra M G" and int: "integrable M f"
    and fm: "f \<in> borel_measurable G"
    and z: "\<And>A. A \<in> sets G \<Longrightarrow> set_lebesgue_integral M A f = 0"
  shows "AE \<omega> in M. f \<omega> = 0"
proof -
  have up: "AE \<omega> in M. f \<omega> \<le> 0"
    by (rule AE_nonpos_of_set_integral_zero[OF G int fm z])
  have zn: "set_lebesgue_integral M A (\<lambda>\<omega>. - f \<omega>) = 0" if A: "A \<in> sets G" for A
  proof -
    have AM: "A \<in> sets M" using A G by (auto simp: subalgebra_def)
    have "(\<integral>\<omega>. indicator A \<omega> *\<^sub>R (- f \<omega>) \<partial>M)
        = (\<integral>\<omega>. - (indicator A \<omega> *\<^sub>R f \<omega>) \<partial>M)" by simp
    also have "\<dots> = - (\<integral>\<omega>. indicator A \<omega> *\<^sub>R f \<omega> \<partial>M)"
      by (rule Bochner_Integration.integral_minus)
    also have "\<dots> = 0" using z[OF A] unfolding set_lebesgue_integral_def by simp
    finally show ?thesis unfolding set_lebesgue_integral_def .
  qed
  have dn: "AE \<omega> in M. - f \<omega> \<le> 0"
    by (rule AE_nonpos_of_set_integral_zero[OF G integrable_minus[OF int] _ zn])
       (use fm in simp)
  show ?thesis using up dn by eventually_elim simp
qed

subsection \<open>Step (b1): the conditional law of the future given the past\<close>

text \<open>The only hypothesis of AFP \<^theory>\<open>Disintegration.Disintegration\<close> that
  is not automatic here is that the future path space is standard Borel, and
  that is immediate: \<open>standard_borel\<close> asks for SOME Polish topology whose
  Borel sets agree, and the path space already IS the Borel algebra of one.\<close>

lemma standard_borel_path_metric:
  "standard_borel (borel_of (mtopology_of
      (path_metric U :: ('n::finite pairpath) metric)))"
  unfolding standard_borel_def
  by (intro exI[of _ "mtopology_of (path_metric U :: ('n pairpath) metric)"]
      conjI Polish_space_path_metric refl)

lemma mspace_path_metric_ne:
  assumes U: "0 \<le> U"
  shows "mspace (path_metric U :: ('n::finite pairpath) metric) \<noteq> {}"
proof -
  have "continuous_on {0..U} (\<lambda>t. (0 :: (real^'n) \<times> (real^'n^'n)))"
    by (rule continuous_on_const)
  then have "restrict (\<lambda>t. (0 :: (real^'n) \<times> (real^'n^'n))) {0..U}
      \<in> mspace (path_metric U :: ('n pairpath) metric)"
    by (rule mspace_path_metricI)
  then show ?thesis by blast
qed

lemma standard_borel_ne_path_metric:
  assumes U: "0 \<le> U"
  shows "standard_borel_ne (borel_of (mtopology_of
      (path_metric U :: ('n::finite pairpath) metric)))"
proof -
  have "space (borel_of (mtopology_of
      (path_metric U :: ('n pairpath) metric))) \<noteq> {}"
    using mspace_path_metric_ne[OF U] by (simp add: space_borel_of)
  then show ?thesis
    unfolding standard_borel_ne_def standard_borel_ne_axioms_def
    using standard_borel_path_metric by blast
qed

text \<open>The regular conditional distribution itself.  Note what the AFP
  actually delivers: \<open>disintegration\<close> constrains RECTANGLES only.  That is
  enough, because the next step converts it to our own \<open>ksemi\<close>, for which the
  almost-sure and integral forms are already proved.\<close>

theorem paper_pair_class_rcd:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
  obtains \<kappa> where
    "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and "\<And>A B. A \<in> sets (borel_of (mtopology_of
            (path_metric r :: ('n pairpath) metric)))
        \<Longrightarrow> B \<in> sets (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))
        \<Longrightarrow> emeasure (distr P
              (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
                \<Otimes>\<^sub>M borel_of (mtopology_of
                  (path_metric (T - r) :: ('n pairpath) metric)))
              (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))) (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of r (pcut r) P))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  have Tr: "0 \<le> T - r" using rT by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have setsnu: "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by simp

  \<comment> \<open>the marginal on the past is the law of \<open>pcut r\<close>\<close>
  have marg: "marginal_measure ?X ?Y ?\<nu> = pair_law_of r (pcut r) P"
  proof (rule measure_eqI)
    show "sets (marginal_measure ?X ?Y ?\<nu>) = sets (pair_law_of r (pcut r) P)"
      by (simp add: sets_marginal_measure)
    fix A assume "A \<in> sets (marginal_measure ?X ?Y ?\<nu>)"
    then have AX: "A \<in> sets ?X" by (simp add: sets_marginal_measure)
    have rect: "A \<times> space ?Y \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using AX by simp
    have "emeasure (marginal_measure ?X ?Y ?\<nu>) A = emeasure ?\<nu> (A \<times> space ?Y)"
      by (rule emeasure_marginal_measure[OF setsnu AX])
    also have "\<dots> = emeasure P (?\<phi> -` (A \<times> space ?Y) \<inter> space P)"
      by (rule emeasure_distr[OF mphi rect])
    also have "\<dots> = emeasure P (pcut r -` A \<inter> space P)"
    proof -
      have "?\<phi> -` (A \<times> space ?Y) \<inter> space P = pcut r -` A \<inter> space P"
        using measurable_space[OF mfut] by auto
      then show ?thesis by simp
    qed
    also have "\<dots> = emeasure (pair_law_of r (pcut r) P) A"
      unfolding pair_law_of_def by (rule emeasure_distr[OF mcut AX, symmetric])
    finally show "emeasure (marginal_measure ?X ?Y ?\<nu>) A
        = emeasure (pair_law_of r (pcut r) P) A" .
  qed

  \<comment> \<open>the two locale obligations\<close>
  have PSF: "projection_sigma_finite ?X ?Y ?\<nu>"
    unfolding projection_sigma_finite_def
  proof (intro conjI)
    show "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by (rule setsnu)
    have "prob_space (pair_law_of r (pcut r) P)"
      unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
    then show "sigma_finite_measure (marginal_measure ?X ?Y ?\<nu>)"
      unfolding marg by (rule prob_space_imp_sigma_finite)
  qed
  have SB: "standard_borel_ne ?Y" by (rule standard_borel_ne_path_metric[OF Tr])
  interpret D: projection_sigma_finite_standard ?X ?Y ?\<nu>
    unfolding projection_sigma_finite_standard_def using PSF SB by blast

  obtain \<kappa> where K: "prob_kernel ?X ?Y \<kappa>"
    and DIS: "measure_kernel.disintegration ?X ?Y \<kappa> ?\<nu>
        (marginal_measure ?X ?Y ?\<nu>)"
    using D.measure_disintegration by blast
  interpret MK: measure_kernel ?X ?Y \<kappa> using K by (simp add: prob_kernel_def)
  have Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y" using K by (simp add: prob_kernel_def')

  show ?thesis
  proof (rule that)
    show "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y" by (rule Km)
    show "emeasure ?\<nu> (A \<times> B)
        = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of r (pcut r) P))"
      if A: "A \<in> sets ?X" and B: "B \<in> sets ?Y" for A B
    proof -
      have "emeasure ?\<nu> (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(marginal_measure ?X ?Y ?\<nu>))"
        using DIS A B unfolding MK.disintegration_def by blast
      then show ?thesis unfolding marg .
    qed
  qed
qed

text \<open>The semidirect product on a RECTANGLE --- the shape in which the AFP's
  disintegration arrives.\<close>

lemma emeasure_ksemi_rect:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and A: "A \<in> sets M" and B: "B \<in> sets N"
  shows "emeasure (ksemi M N Kr) (A \<times> B) = (\<integral>\<^sup>+\<omega>\<in>A. emeasure (Kr \<omega>) B \<partial>M)"
proof -
  have rect: "A \<times> B \<in> sets (M \<Otimes>\<^sub>M N)" using A B by simp
  have "emeasure (ksemi M N Kr) (A \<times> B)
      = (\<integral>\<^sup>+\<omega>. emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B) \<partial>M)"
    unfolding ksemi_def
    by (rule emeasure_bind[OF ne ksemi_kernel_measurable[OF K] rect])
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. indicator A \<omega> * emeasure (Kr \<omega>) B \<partial>M)"
  proof (rule nn_integral_cong)
    fix \<omega> assume w: "\<omega> \<in> space M"
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have spK: "space (Kr \<omega>) = space N" by (rule sets_eq_imp_space_eq[OF sK])
    have "emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B)
        = emeasure (Kr \<omega>) (Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>))"
      by (rule emeasure_distr[OF ksemi_Pair_measurable[OF K w] rect])
    also have "\<dots> = indicator A \<omega> * emeasure (Kr \<omega>) B"
    proof (cases "\<omega> \<in> A")
      case True
      have "Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>) = B"
        using True B sets.sets_into_space[OF B] by (auto simp: spK)
      then show ?thesis using True by simp
    next
      case False
      have "Pair \<omega> -` (A \<times> B) \<inter> space (Kr \<omega>) = {}" using False by auto
      then show ?thesis using False by simp
    qed
    finally show "emeasure (distr (Kr \<omega>) (M \<Otimes>\<^sub>M N) (Pair \<omega>)) (A \<times> B)
        = indicator A \<omega> * emeasure (Kr \<omega>) B" .
  qed
  finally show ?thesis by (simp add: nn_integral_set_ennreal mult.commute)
qed

text \<open>And the conversion.  Two probability measures on \<open>?X \<Otimes>\<^sub>M ?Y\<close> that agree
  on the rectangle \<pi>-system are equal, so the AFP's rectangle-level
  disintegration IS our semidirect product --- after which
  @{thm [source] AE_ksemi} and @{thm [source] nn_integral_ksemi}, proved for
  the kernel-pasting work, give the almost-sure and integral forms with no
  further measure-theoretic induction.\<close>

theorem paper_pair_class_rcd_ksemi:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
  obtains \<kappa> where
    "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?E = "{a \<times> b | a b. a \<in> sets ?X \<and> b \<in> sets ?Y}"
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  interpret Pnu: prob_space ?\<nu> by (rule PP.prob_space_distr[OF mphi])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  obtain \<kappa> where Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and REC: "\<And>A B. A \<in> sets ?X \<Longrightarrow> B \<in> sets ?Y \<Longrightarrow>
        emeasure ?\<nu> (A \<times> B) = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
    by (rule paper_pair_class_rcd[OF r rT setsP PS]) blast
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using Km measurable_cong_sets[OF setsQ refl] by blast
  have setsS: "sets (ksemi ?Q ?Y \<kappa>) = sets (?X \<Otimes>\<^sub>M ?Y)"
  proof -
    have "sets (ksemi ?Q ?Y \<kappa>) = sets (?Q \<Otimes>\<^sub>M ?Y)" by (rule sets_ksemi[OF KQ neQ])
    also have "\<dots> = sets (?X \<Otimes>\<^sub>M ?Y)"
      by (rule sets_pair_measure_cong[OF setsQ refl])
    finally show ?thesis .
  qed
  have eq: "?\<nu> = ksemi ?Q ?Y \<kappa>"
  proof (rule measure_eqI_generator_eq
      [where E = ?E and \<Omega> = "space ?X \<times> space ?Y"
         and A = "\<lambda>_. space ?X \<times> space ?Y"])
    show "Int_stable ?E" by (rule Int_stable_pair_measure_generator)
    show "?E \<subseteq> Pow (space ?X \<times> space ?Y)" using sets.sets_into_space by auto
    show "emeasure ?\<nu> C = emeasure (ksemi ?Q ?Y \<kappa>) C" if C: "C \<in> ?E" for C
    proof -
      from C obtain A B where AB: "A \<in> sets ?X" "B \<in> sets ?Y" "C = A \<times> B"
        by blast
      have AQ: "A \<in> sets ?Q" using AB(1) setsQ by simp
      have "emeasure ?\<nu> C = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
        unfolding AB(3) by (rule REC[OF AB(1) AB(2)])
      also have "\<dots> = emeasure (ksemi ?Q ?Y \<kappa>) C"
        unfolding AB(3)
        by (rule emeasure_ksemi_rect[OF KQ neQ AQ AB(2), symmetric])
      finally show ?thesis .
    qed
    show "sets ?\<nu> = sigma_sets (space ?X \<times> space ?Y) ?E"
      by (simp add: sets_pair_measure)
    show "sets (ksemi ?Q ?Y \<kappa>) = sigma_sets (space ?X \<times> space ?Y) ?E"
      unfolding setsS by (simp add: sets_pair_measure)
    show "range (\<lambda>_. space ?X \<times> space ?Y) \<subseteq> ?E" by auto
    show "(\<Union>i :: nat. space ?X \<times> space ?Y) = space ?X \<times> space ?Y" by simp
    show "emeasure ?\<nu> (space ?X \<times> space ?Y) \<noteq> \<infinity>" for i :: nat
      by (simp add: Pnu.emeasure_eq_measure)
  qed
  show ?thesis by (rule that[OF Km eq])
qed

subsection \<open>Step (b2): the almost-sure clauses pass to the kernel\<close>

text \<open>Clauses (i) and (ii) of (1.7) both say "\<open>\<mu> C = 1\<close> for a fixed
  measurable \<open>C\<close>", and that is LINEAR in \<open>\<mu>\<close>.  So each transfers to the
  kernel by a single nonnegative-integral argument: the complement has
  integral \<open>0\<close>, hence vanishes almost everywhere.\<close>

lemma AE_kernel_full:
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and C: "C \<in> sets N"
    and null: "emeasure (ksemi M N Kr) (space M \<times> (space N - C)) = 0"
  shows "AE \<omega> in M. emeasure (Kr \<omega>) C = 1"
proof -
  have C': "space N - C \<in> sets N" using C by (rule sets.compl_sets)
  have spM: "space M \<in> sets M" by simp
  have mE: "(\<lambda>\<omega>. emeasure (Kr \<omega>) (space N - C)) \<in> borel_measurable M"
    by (rule measurable_compose[OF measurable_prob_algebraD[OF K]
          measurable_emeasure_subprob_algebra[OF C']])
  have "(\<integral>\<^sup>+\<omega>. emeasure (Kr \<omega>) (space N - C) \<partial>M)
      = (\<integral>\<^sup>+\<omega>\<in>space M. emeasure (Kr \<omega>) (space N - C) \<partial>M)"
    by (intro nn_integral_cong) simp
  also have "\<dots> = emeasure (ksemi M N Kr) (space M \<times> (space N - C))"
    by (rule emeasure_ksemi_rect[OF K ne spM C', symmetric])
  also have "\<dots> = 0" by (rule null)
  finally have "(\<integral>\<^sup>+\<omega>. emeasure (Kr \<omega>) (space N - C) \<partial>M) = 0" .
  then have ae: "AE \<omega> in M. emeasure (Kr \<omega>) (space N - C) = 0"
    using mE by (simp add: nn_integral_0_iff_AE)
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with ae show ?thesis
  proof eventually_elim
    fix \<omega> assume z: "emeasure (Kr \<omega>) (space N - C) = 0" and w: "\<omega> \<in> space M"
    interpret PK: prob_space "Kr \<omega>" by (rule ksemi_sets_kernel(2)[OF K w])
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have spK: "space (Kr \<omega>) = space N" by (rule sets_eq_imp_space_eq[OF sK])
    have CK: "C \<in> sets (Kr \<omega>)" using C sK by simp
    have C'K: "space N - C \<in> sets (Kr \<omega>)" using C' sK by simp
    have "emeasure (Kr \<omega>) (C \<union> (space N - C))
        = emeasure (Kr \<omega>) C + emeasure (Kr \<omega>) (space N - C)"
      by (rule plus_emeasure[OF CK C'K, symmetric]) auto
    moreover have "C \<union> (space N - C) = space (Kr \<omega>)"
      using sets.sets_into_space[OF C] by (auto simp: spK)
    ultimately have "emeasure (Kr \<omega>) C = 1"
      using z PK.emeasure_space_1 by simp
    then show "emeasure (Kr \<omega>) C = 1" .
  qed
qed

text \<open>Clause (i) for the kernel.  It is the easiest of the four, because
  @{thm [source] pfut_zero} makes the initial condition hold IDENTICALLY:
  the offending set has EMPTY preimage, not merely a null one.\<close>

lemma pfut_rcd_start:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
  shows "AE p in pair_law_of r (pcut r) P.
      emeasure (\<kappa> p) {w \<in> space (borel_of (mtopology_of
          (path_metric (T - r) :: ('n pairpath) metric))).
        fst (w 0) = 0 \<and> snd (w 0) = 0} = 1"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?C = "{w :: 'n pairpath \<in> space ?Y. fst (w 0) = 0 \<and> snd (w 0) = 0}"
  have Tr: "0 \<le> T - r" using rT by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w 0) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have CY: "?C \<in> sets ?Y"
  proof -
    have "?C = (\<lambda>w :: 'n pairpath. w 0) -` {(0, 0)} \<inter> space ?Y"
      by (auto simp: prod_eq_iff)
    then show ?thesis using measurable_sets[OF ev] by simp
  qed
  have C': "space ?Y - ?C \<in> sets ?Y" using CY by (rule sets.compl_sets)
  have rect: "space ?X \<times> (space ?Y - ?C) \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using C' by simp
  have empty: "?\<phi> -` (space ?X \<times> (space ?Y - ?C)) \<inter> space P = {}"
  proof -
    have "pfut r T \<omega> \<notin> space ?Y - ?C" for \<omega> :: "'n pairpath"
    proof -
      have z: "pfut r T \<omega> 0 = 0" by (rule pfut_zero[OF Tr])
      have "fst (pfut r T \<omega> 0) = 0 \<and> snd (pfut r T \<omega> 0) = 0" by (simp add: z)
      then show ?thesis by simp
    qed
    then show ?thesis by auto
  qed
  have "emeasure (ksemi ?Q ?Y \<kappa>) (space ?X \<times> (space ?Y - ?C))
      = emeasure (distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>) (space ?X \<times> (space ?Y - ?C))"
    unfolding eq ..
  also have "\<dots> = emeasure P (?\<phi> -` (space ?X \<times> (space ?Y - ?C)) \<inter> space P)"
    by (rule emeasure_distr[OF mphi rect])
  also have "\<dots> = 0" unfolding empty by simp
  finally have null: "emeasure (ksemi ?Q ?Y \<kappa>)
      (space ?X \<times> (space ?Y - ?C)) = 0" .
  have spQ: "space ?Q = space ?X" by (rule sets_eq_imp_space_eq[OF setsQ])
  have null': "emeasure (ksemi ?Q ?Y \<kappa>) (space ?Q \<times> (space ?Y - ?C)) = 0"
    using null spQ by simp
  show ?thesis by (rule AE_kernel_full[OF KQ neQ CY null'])
qed

text \<open>A rational-hypothesis variant of
  @{thm [source] paper_pair_class_diffquot_of_pairs}.  The original demands
  the pairwise bound at ALL real pairs, which an almost-sure argument cannot
  supply --- only COUNTABLY many conditions survive the passage from "for
  each, almost surely" to "almost surely, for all".  Its proof already uses
  the hypothesis at rational pairs only, so the weakening is free.\<close>

lemma paper_pair_class_diffquot_of_rational_pairs:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and one: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> p \<in> {0..T} \<Longrightarrow> q \<in> {0..T} \<Longrightarrow> p < q \<Longrightarrow>
      AE \<omega> in Q. (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  shows "AE \<omega> in Q. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
      (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
proof -
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have rat: "AE \<omega> in Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume p: "p \<in> \<rat>"
    show "AE \<omega> in Q. \<forall>q\<in>(\<rat>::real set). 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume q: "q \<in> \<rat>"
      show "AE \<omega> in Q. 0 \<le> p \<longrightarrow> p < q \<longrightarrow> q \<le> T \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      proof (cases "0 \<le> p \<and> p < q \<and> q \<le> T")
        case True
        then have pq: "p \<in> {0..T}" "q \<in> {0..T}" "p < q" by auto
        from one[OF p q pq] show ?thesis by (rule eventually_mono) simp
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  from rat AE_space show ?thesis
  proof eventually_elim
    case (elim \<omega>)
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> T
        \<Longrightarrow> (1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
      and W: "\<omega> \<in> space Q" by blast+
    have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using W spQ by simp
    have cont: "continuous_on {0..T} (\<lambda>u. snd (\<omega> u))"
      using mspace_path_metricD[OF mw] by (intro continuous_intros)
    show ?case
    proof (intro allI impI)
      fix u v :: real
      assume uv: "0 \<le> u" "u < v" "v \<le> T"
      show "(1 / (v - u)) *\<^sub>R (snd (\<omega> v) - snd (\<omega> u)) \<in> sconstraint k L"
        by (rule diffquot_all_of_rational
            [OF closed_sconstraint cont _ uv(1) uv(2) uv(3)]) (rule R)
    qed
  qed
qed

text \<open>The transfer that every full-measure clause needs: an almost-sure
  property of the future under \<open>P\<close> makes the corresponding rectangle
  \<open>ksemi\<close>-null, which is the hypothesis of @{thm [source] AE_kernel_full}.\<close>

lemma ksemi_rect_null_of_AE:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and C: "C \<in> sets (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric)))"
    and ae: "AE \<omega> in P. pfut r T \<omega> \<in> C"
  shows "emeasure (ksemi (pair_law_of r (pcut r) P)
        (borel_of (mtopology_of
          (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>)
      (space (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric)))
        \<times> (space (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric))) - C)) = 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have C': "space ?Y - C \<in> sets ?Y" using C by (rule sets.compl_sets)
  have rect: "space ?X \<times> (space ?Y - C) \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using C' by simp
  have preim: "?\<phi> -` (space ?X \<times> (space ?Y - C)) \<inter> space P
      = pfut r T -` (space ?Y - C) \<inter> space P"
    using measurable_space[OF mcut] by auto
  have mset: "pfut r T -` (space ?Y - C) \<inter> space P \<in> sets P"
    by (rule measurable_sets[OF mfut C'])
  have null: "emeasure P (pfut r T -` (space ?Y - C) \<inter> space P) = 0"
  proof -
    have aeS: "AE \<omega> in P. \<omega> \<notin> pfut r T -` (space ?Y - C) \<inter> space P"
      using ae by (auto elim: eventually_mono)
    have setseq: "{\<omega> \<in> space P. \<not> (\<omega> \<notin> pfut r T -` (space ?Y - C) \<inter> space P)}
        = pfut r T -` (space ?Y - C) \<inter> space P" by auto
    show ?thesis using aeS AE_iff_measurable[OF mset setseq] by blast
  qed
  have "emeasure (ksemi (pair_law_of r (pcut r) P) ?Y \<kappa>)
        (space ?X \<times> (space ?Y - C))
      = emeasure (distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>) (space ?X \<times> (space ?Y - C))"
    unfolding eq ..
  also have "\<dots> = emeasure P (?\<phi> -` (space ?X \<times> (space ?Y - C)) \<inter> space P)"
    by (rule emeasure_distr[OF mphi rect])
  also have "\<dots> = 0" unfolding preim by (rule null)
  finally show ?thesis .
qed

text \<open>The last piece of plumbing: @{thm [source] AE_kernel_full} delivers
  \<open>emeasure (\<kappa> p) C = 1\<close>, while the class's clauses are stated as \<open>AE\<close>
  properties.  The library's @{thm [source] prob_space.AE_prob_1} is phrased
  with the REAL measure, so the bridge goes through
  @{thm [source] finite_measure.emeasure_eq_measure}.\<close>

lemma AE_mem_of_emeasure_1:
  assumes PS: "prob_space M" and one: "emeasure M C = 1"
  shows "AE w in M. w \<in> C"
proof -
  interpret PM: prob_space M by (rule PS)
  have "measure M C = 1" using one by (simp add: PM.emeasure_eq_measure)
  then show ?thesis by (rule PM.AE_prob_1)
qed

text \<open>Clause (ii) for the conditional law.  Only RATIONAL pairs can be
  handled --- an almost-sure statement survives only countably many
  conditions --- which is exactly what
  @{thm [source] paper_pair_class_diffquot_of_rational_pairs} was made for.\<close>

lemma pfut_rcd_diffquot:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE p' in pair_law_of r (pcut r) P.
      AE w in \<kappa> p'. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T - r \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (w t) - snd (w s)) \<in> sconstraint k L"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  have Tr: "0 \<le> ?S" using rT by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have spQ: "space ?Q = space ?X" by (rule sets_eq_imp_space_eq[OF setsQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  define C where "C p q = {w :: 'n pairpath \<in> space ?Y.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L}"
    for p q :: real
  have CY: "C p q \<in> sets ?Y" if "p \<in> {0..?S}" "q \<in> {0..?S}" for p q
    unfolding C_def
    using borel_of_closed[OF closedin_diffquot_constraint[OF that]]
    by (simp add: space_borel_of)
  have aeC: "AE \<omega> in P. pfut r T \<omega> \<in> C p q"
    if pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q" for p q
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    with cov show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      have rp: "0 \<le> r + p" using r pq by simp
      have rpq: "r + p < r + q" using pq by simp
      have rqT: "r + q \<le> T" using pq by simp
      have "(1 / ((r + q) - (r + p))) *\<^sub>R (snd (\<omega> (r + q)) - snd (\<omega> (r + p)))
          \<in> sconstraint k L" using elim rp rpq rqT by blast
      moreover have "snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)
          = snd (\<omega> (r + q)) - snd (\<omega> (r + p))"
        using pq by (simp add: pfut_apply)
      ultimately have inC: "(1 / (q - p))
          *\<^sub>R (snd (pfut r T \<omega> q) - snd (pfut r T \<omega> p)) \<in> sconstraint k L"
        by simp
      have spw: "pfut r T \<omega> \<in> space ?Y"
        using measurable_space[OF mfut] elim by simp
      show ?case unfolding C_def using inC spw by simp
    qed
  qed
  have one: "AE p' in ?Q. emeasure (\<kappa> p') (C p q) = 1"
    if pq: "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q" for p q
  proof -
    have null: "emeasure (ksemi ?Q ?Y \<kappa>)
        (space ?X \<times> (space ?Y - C p q)) = 0"
      by (rule ksemi_rect_null_of_AE
          [OF r rT setsP PS eq CY[OF pq(1) pq(2)] aeC[OF pq]])
    have "emeasure (ksemi ?Q ?Y \<kappa>) (space ?Q \<times> (space ?Y - C p q)) = 0"
      using null spQ by simp
    then show ?thesis by (rule AE_kernel_full[OF KQ neQ CY[OF pq(1) pq(2)]])
  qed
  have rat: "AE p' in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..?S} \<longrightarrow> q \<in> {0..?S} \<longrightarrow> p < q \<longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE p' in ?Q. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..?S} \<longrightarrow> q \<in> {0..?S} \<longrightarrow> p < q \<longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE p' in ?Q. p \<in> {0..?S} \<longrightarrow> q \<in> {0..?S} \<longrightarrow> p < q
          \<longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
      proof (cases "p \<in> {0..?S} \<and> q \<in> {0..?S} \<and> p < q")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  have "AE p' in ?Q. p' \<in> space ?Q" by (rule AE_space)
  with rat show ?thesis
  proof eventually_elim
    case (elim p')
    then have R: "\<And>p q :: real. p \<in> \<rat> \<Longrightarrow> q \<in> \<rat> \<Longrightarrow> p \<in> {0..?S} \<Longrightarrow> q \<in> {0..?S}
        \<Longrightarrow> p < q \<Longrightarrow> emeasure (\<kappa> p') (C p q) = 1"
      and W: "p' \<in> space ?Q" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    show ?case
    proof (rule paper_pair_class_diffquot_of_rational_pairs[OF sK])
      fix p q :: real
      assume pq: "p \<in> \<rat>" "q \<in> \<rat>" "p \<in> {0..?S}" "q \<in> {0..?S}" "p < q"
      have "AE w in \<kappa> p'. w \<in> C p q"
        by (rule AE_mem_of_emeasure_1[OF PK R[OF pq]])
      then show "AE w in \<kappa> p'.
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
        unfolding C_def by (auto elim: eventually_mono)
    qed
  qed
qed

subsection \<open>Step (b3): towards the martingale clauses\<close>

text \<open>Clauses (i) and (ii) needed only \<open>emeasure\<close>, so the unconditional
  @{thm [source] nn_integral_ksemi} sufficed.  The martingale clauses need
  \<open>\<integral>\<^sub>A\<^sub>' X\<^sub>i d\<kappa> p'\<close>, and the coordinate process is NOT bounded on the path
  space, while @{thm [source] integral_ksemi_bounded} --- the only
  Bochner-level disintegration in the development --- assumes a uniform
  bound.  So the unbounded version has to be built, and it is built the
  standard way: through the positive and negative parts, where
  @{thm [source] nn_integral_ksemi} does apply.  First the integrability of
  the sections.\<close>

lemma AE_integrable_ksemi_section:
  fixes g :: "'a \<times> 'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "integrable (ksemi M N Kr) g"
    and ne: "space M \<noteq> {}"
  shows "AE \<omega> in M. integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
proof -
  have gabs: "(\<lambda>p. ennreal (norm (g p))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using gm by measurable
  have fin: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr)) < \<top>"
    using gi by (simp add: integrable_iff_bounded)
  have split: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))
      = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_ksemi[OF K gabs])
  have minner: "(\<lambda>\<omega>. \<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>))
      \<in> borel_measurable M"
  proof (rule nn_integral_measurable_subprob_algebra2)
    show "(\<lambda>(x, y). ennreal (norm (g (x, y)))) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
      using gabs by (simp add: case_prod_unfold)
    show "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N" by (rule measurable_prob_algebraD[OF K])
  qed
  have fin': "(\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<partial>M) \<noteq> \<infinity>"
    using fin split by (simp add: less_top)
  have aefin: "AE \<omega> in M. (\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF minner fin'])
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with aefin show ?thesis
  proof eventually_elim
    fix \<omega> assume z: "(\<integral>\<^sup>+\<omega>'. ennreal (norm (g (\<omega>, \<omega>'))) \<partial>(Kr \<omega>)) \<noteq> \<infinity>"
      and w: "\<omega> \<in> space M"
    have sec: "(\<lambda>\<omega>'. g (\<omega>, \<omega>')) \<in> borel_measurable (Kr \<omega>)"
      by (rule measurable_compose[OF ksemi_Pair_measurable[OF K w] gm])
    show "integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      using sec z by (simp add: integrable_iff_bounded less_top)
  qed
qed

text \<open>The unbounded disintegration of Bochner integrals, through the
  positive and negative parts.  @{thm [source] real_lebesgue_integral_def}
  splits both sides into \<open>enn2real\<close> of nonnegative integrals, and on those
  @{thm [source] nn_integral_ksemi} applies with no boundedness hypothesis at
  all.\<close>

lemma integral_ksemi_real:
  fixes g :: "'a \<times> 'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N"
    and gm: "g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    and gi: "integrable (ksemi M N Kr) g"
    and ne: "space M \<noteq> {}"
    and msec: "(\<lambda>\<omega>. \<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  shows "(\<integral>p. g p \<partial>(ksemi M N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  define A where "A \<omega> = (\<integral>\<^sup>+\<omega>'. ennreal (g (\<omega>, \<omega>')) \<partial>(Kr \<omega>))" for \<omega>
  define B where "B \<omega> = (\<integral>\<^sup>+\<omega>'. ennreal (- g (\<omega>, \<omega>')) \<partial>(Kr \<omega>))" for \<omega>
  have Ksub: "Kr \<in> M \<rightarrow>\<^sub>M subprob_algebra N"
    by (rule measurable_prob_algebraD[OF K])
  have mA: "A \<in> borel_measurable M"
    unfolding A_def
    by (rule nn_integral_measurable_subprob_algebra2[OF _ Ksub])
       (use gm in \<open>simp add: case_prod_unfold\<close>)
  have mB: "B \<in> borel_measurable M"
    unfolding B_def
    by (rule nn_integral_measurable_subprob_algebra2[OF _ Ksub])
       (use gm in \<open>simp add: case_prod_unfold\<close>)
  have nnA: "(\<integral>\<^sup>+p. ennreal (g p) \<partial>(ksemi M N Kr)) = (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M)"
    unfolding A_def by (rule nn_integral_ksemi[OF K]) (use gm in measurable)
  have nnB: "(\<integral>\<^sup>+p. ennreal (- g p) \<partial>(ksemi M N Kr)) = (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
    unfolding B_def by (rule nn_integral_ksemi[OF K]) (use gm in measurable)
  have absfin: "(\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr)) < \<top>"
    using gi by (simp add: integrable_iff_bounded)
  have leA: "(\<integral>\<^sup>+p. ennreal (g p) \<partial>(ksemi M N Kr))
      \<le> (\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))"
    by (intro nn_integral_mono ennreal_leI) simp
  have leB: "(\<integral>\<^sup>+p. ennreal (- g p) \<partial>(ksemi M N Kr))
      \<le> (\<integral>\<^sup>+p. ennreal (norm (g p)) \<partial>(ksemi M N Kr))"
    by (intro nn_integral_mono ennreal_leI) simp
  have finA: "(\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M) < \<top>"
    using leA absfin unfolding nnA[symmetric] by simp
  have finB: "(\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M) < \<top>"
    using leB absfin unfolding nnB[symmetric] by simp
  have aeA: "AE \<omega> in M. A \<omega> \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF mA]) (use finA in \<open>simp add: less_top\<close>)
  have aeB: "AE \<omega> in M. B \<omega> \<noteq> \<infinity>"
    by (rule nn_integral_PInf_AE[OF mB]) (use finB in \<open>simp add: less_top\<close>)
  have eqA: "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (A \<omega>)) \<partial>M) = (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M)"
    using aeA by (intro nn_integral_cong_AE) (auto simp: less_top)
  have eqB: "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (B \<omega>)) \<partial>M) = (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
    using aeB by (intro nn_integral_cong_AE) (auto simp: less_top)
  have iA: "integrable M (\<lambda>\<omega>. enn2real (A \<omega>))"
    using mA eqA finA by (simp add: integrable_iff_bounded)
  have iB: "integrable M (\<lambda>\<omega>. enn2real (B \<omega>))"
    using mB eqB finB by (simp add: integrable_iff_bounded)
  have intA: "(\<integral>\<omega>. enn2real (A \<omega>) \<partial>M) = enn2real (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (A \<omega>)) \<partial>M) = (\<integral>\<omega>. enn2real (A \<omega>) \<partial>M)"
      by (rule nn_integral_eq_integral[OF iA]) simp
    then show ?thesis using eqA by simp
  qed
  have intB: "(\<integral>\<omega>. enn2real (B \<omega>) \<partial>M) = enn2real (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
  proof -
    have "(\<integral>\<^sup>+\<omega>. ennreal (enn2real (B \<omega>)) \<partial>M) = (\<integral>\<omega>. enn2real (B \<omega>) \<partial>M)"
      by (rule nn_integral_eq_integral[OF iB]) simp
    then show ?thesis using eqB by simp
  qed
  have aesec: "AE \<omega> in M. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>))
      = enn2real (A \<omega>) - enn2real (B \<omega>)"
  proof -
    have "AE \<omega> in M. integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      by (rule AE_integrable_ksemi_section[OF K gm gi ne])
    then show ?thesis
    proof eventually_elim
      fix \<omega> assume "integrable (Kr \<omega>) (\<lambda>\<omega>'. g (\<omega>, \<omega>'))"
      then show "(\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) = enn2real (A \<omega>) - enn2real (B \<omega>)"
        unfolding A_def B_def by (rule real_lebesgue_integral_def)
    qed
  qed
  have "(\<integral>p. g p \<partial>(ksemi M N Kr))
      = enn2real (\<integral>\<^sup>+p. ennreal (g p) \<partial>(ksemi M N Kr))
        - enn2real (\<integral>\<^sup>+p. ennreal (- g p) \<partial>(ksemi M N Kr))"
    by (rule real_lebesgue_integral_def[OF gi])
  also have "\<dots> = enn2real (\<integral>\<^sup>+\<omega>. A \<omega> \<partial>M) - enn2real (\<integral>\<^sup>+\<omega>. B \<omega> \<partial>M)"
    unfolding nnA nnB ..
  also have "\<dots> = (\<integral>\<omega>. enn2real (A \<omega>) \<partial>M) - (\<integral>\<omega>. enn2real (B \<omega>) \<partial>M)"
    unfolding intA intB ..
  also have "\<dots> = (\<integral>\<omega>. enn2real (A \<omega>) - enn2real (B \<omega>) \<partial>M)"
    by (rule Bochner_Integration.integral_diff[OF iA iB, symmetric])
  also have "\<dots> = (\<integral>\<omega>. (\<integral>\<omega>'. g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    using aesec msec iA iB
    by (intro Bochner_Integration.integral_cong_AE) auto
  finally show ?thesis .
qed

text \<open>The shape (b3) actually consumes: the integrand is an indicator of a
  RECTANGLE times a function of the future only.  Then the \<open>msec\<close> hypothesis
  of @{thm [source] integral_ksemi_real} is discharged by the AFP's
  fixed-integrand @{thm [source] integral_measurable_subprob_algebra}, and
  the section integral factors as a constant times an integral over the
  kernel.\<close>

lemma integral_ksemi_rect_real:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
    and gi: "integrable (ksemi M N Kr)
        (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
  shows "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p))
        \<partial>(ksemi M N Kr))
      = (\<integral>\<omega>. indicator A \<omega> * (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<partial>M)"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using A A' hm by measurable
  have inner: "(\<integral>\<omega>'. ?g (\<omega>, \<omega>') \<partial>(Kr \<omega>))
      = indicator A \<omega> * (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))" for \<omega>
    by simp
  have msec: "(\<lambda>\<omega>. \<integral>\<omega>'. ?g (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  proof -
    have "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
      by (rule measurable_compose[OF measurable_prob_algebraD[OF K]
            integral_measurable_subprob_algebra[OF hm']])
    then show ?thesis using A by (simp add: inner)
  qed
  show ?thesis
    using integral_ksemi_real[OF K gm gi ne msec] by (simp add: inner)
qed

text \<open>Two small facts used repeatedly in what follows: the map
  \<open>\<omega> \<mapsto> \<integral> h d(Kr \<omega>)\<close> is measurable when the integrand does not depend on \<open>\<omega>\<close>,
  and every measure is a subalgebra of itself --- which is the form
  @{thm [source] AE_zero_of_set_integral_zero} gets applied in, the
  \<open>\<G>\<close>-measurability being supplied by the kernel rather than by a genuine
  sub-\<sigma>-algebra.\<close>

lemma measurable_integral_kernel:
  fixes h :: "'b \<Rightarrow> 'c::{banach,second_countable_topology}"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and hm: "h \<in> borel_measurable N"
  shows "(\<lambda>\<omega>. \<integral>\<omega>'. h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
  by (rule measurable_compose[OF measurable_prob_algebraD[OF K]
      integral_measurable_subprob_algebra[OF hm]])

lemma subalgebra_self: "subalgebra M M"
  by (simp add: subalgebra_def)

text \<open>The workhorse of (b3), at the \<open>ksemi\<close> level.  If every RECTANGLE
  integral of \<open>1\<^sub>A\<^sub>' \<sqdot> h\<close> vanishes, then the kernel's own integral of
  \<open>1\<^sub>A\<^sub>' \<sqdot> h\<close> vanishes almost everywhere.  It isolates exactly the two things
  the path-specific part has to supply: integrability, and the vanishing of
  the rectangle integrals --- which for the martingale clauses is precisely
  @{thm [source] martingale.set_integral_eq} applied to \<open>P\<close>.\<close>

lemma AE_kernel_integral_zero:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A': "A' \<in> sets N"
    and gi: "\<And>A. A \<in> sets M \<Longrightarrow> integrable (ksemi M N Kr)
        (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
    and fi: "integrable M (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))"
    and z: "\<And>A. A \<in> sets M \<Longrightarrow> (\<integral>p. indicator A (fst p)
        * (indicator A' (snd p) * h (snd p)) \<partial>(ksemi M N Kr)) = 0"
  shows "AE \<omega> in M. (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) = 0"
proof -
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have fmeas: "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
    by (rule measurable_integral_kernel[OF K hm'])
  have zz: "set_lebesgue_integral M A
      (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) = 0" if A: "A \<in> sets M" for A
  proof -
    have "set_lebesgue_integral M A (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))
        = (\<integral>\<omega>. indicator A \<omega> * (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<partial>M)"
      unfolding set_lebesgue_integral_def by simp
    also have "\<dots> = (\<integral>p. indicator A (fst p)
        * (indicator A' (snd p) * h (snd p)) \<partial>(ksemi M N Kr))"
      by (rule integral_ksemi_rect_real[OF K ne hm A A' gi[OF A], symmetric])
    also have "\<dots> = 0" by (rule z[OF A])
    finally show ?thesis .
  qed
  show ?thesis
    by (rule AE_zero_of_set_integral_zero[OF subalgebra_self fi fmeas zz])
qed

text \<open>Two path-specific facts the instantiation needs.  First: an INCREMENT
  of the rebased future is an increment of the original path --- the base
  point cancels, which is why the martingale property of \<open>P\<close> applies to it
  unchanged.\<close>

lemma pfut_increment:
  fixes \<omega> :: "'n::finite pairpath"
  assumes u: "u \<in> {0..T - r}" and v: "v \<in> {0..T - r}"
  shows "fst (pfut r T \<omega> v) - fst (pfut r T \<omega> u)
      = fst (\<omega> (r + v)) - fst (\<omega> (r + u))"
  using u v by (simp add: pfut_fst)

text \<open>Second: \<open>pfut\<close> pulls the FUTURE's natural filtration back into \<open>P\<close>'s,
  with the clock shifted by \<open>r\<close>.  This is what puts the conditioning set
  \<open>(pcut r) -` A \<inter> (pfut r T) -` A'\<close> into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>, where the martingale
  property of \<open>P\<close> applies to it.\<close>

lemma pfut_filtration_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))
        \<rightarrow>\<^sub>M natural_filtration
            (pair_law_of (T - r) (pfut r T) P) 0 (\<lambda>v w. w v) u"
proof -
  let ?S = "T - r"
  let ?FF = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)
      (r + min u ?S)"
  have Tr: "0 \<le> ?S" using rT by simp
  have phim: "pfut r T \<in> P \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric ?S :: ('n pairpath) metric))"
    by (rule pfut_measurable_law[OF r rT setsP])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) \<in> borel_measurable (?FF u)"
    if v: "0 \<le> v" and vu: "v \<le> u" for v
  proof (cases "v \<le> ?S")
    case True
    have m1: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v)) \<in> borel_measurable (?FF u)"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use r v vu True in auto)
    have m2: "(\<lambda>\<omega> :: 'n pairpath. \<omega> r) \<in> borel_measurable (?FF u)"
      unfolding natural_filtration_def
      by (rule measurable_family_vimage_algebra) (use r v vu True Tr in auto)
    have "(\<lambda>\<omega> :: 'n pairpath. \<omega> (r + v) - \<omega> r) \<in> borel_measurable (?FF u)"
      by (rule borel_measurable_diff[OF m1 m2])
    moreover have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. \<omega> (r + v) - \<omega> r)"
      using v True by (auto simp: pfut_apply)
    ultimately show ?thesis by simp
  next
    case False
    then have "(\<lambda>\<omega> :: 'n pairpath. pfut r T \<omega> v) = (\<lambda>\<omega>. undefined)"
      by (auto simp: pfut_def)
    then show ?thesis by simp
  qed
  have spF: "space (?FF u) = space P" by simp
  show ?thesis
    by (rule phi_filtration_measurable
        [where FF = "\<lambda>u. natural_filtration P 0
            (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)" and u = u,
         OF phim adap spF])
qed

text \<open>The \<open>gi\<close> hypothesis of @{thm [source] AE_kernel_integral_zero}: since
  the semidirect product IS a pushforward of \<open>P\<close>, integrability of the
  rectangle integrand reduces to integrability of the future part under \<open>P\<close>,
  the two indicators only shrinking the norm.\<close>

lemma integrable_ksemi_of_distr_rect:
  fixes h :: "'b \<Rightarrow> real"
  assumes eq: "ksemi M N Kr = distr P (M \<Otimes>\<^sub>M N) \<phi>"
    and phim: "\<phi> \<in> P \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
    and hi: "integrable P (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
  shows "integrable (ksemi M N Kr)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p)))"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using A A' hm by measurable
  have comp: "integrable P (\<lambda>\<omega>. ?g (\<phi> \<omega>))"
  proof (rule Bochner_Integration.integrable_bound[OF hi])
    show "(\<lambda>\<omega>. ?g (\<phi> \<omega>)) \<in> borel_measurable P"
      by (rule measurable_compose[OF phim gm])
    show "AE \<omega> in P. norm (?g (\<phi> \<omega>)) \<le> norm (h (snd (\<phi> \<omega>)))"
      by (rule AE_I2) (auto simp: indicator_def abs_mult)
  qed
  have "integrable (distr P (M \<Otimes>\<^sub>M N) \<phi>) ?g"
    using comp by (simp add: integrable_distr_eq[OF phim gm])
  then show ?thesis unfolding eq .
qed

text \<open>The \<open>fi\<close> hypothesis: the outer integral of the kernel integral is
  dominated by the \<open>ksemi\<close> integral of \<open>|h|\<close>, because the section integral is
  bounded in norm by the section's own nonnegative integral --- almost
  everywhere, which is where @{thm [source] AE_integrable_ksemi_section}
  earns its keep.\<close>

lemma integrable_kernel_integral:
  fixes h :: "'b \<Rightarrow> real"
  assumes K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra N" and ne: "space M \<noteq> {}"
    and hm: "h \<in> borel_measurable N"
    and A': "A' \<in> sets N"
    and hi: "integrable (ksemi M N Kr) (\<lambda>p. h (snd p))"
  shows "integrable M (\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))"
proof -
  have hm2: "(\<lambda>p :: 'a \<times> 'b. h (snd p)) \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
    using hm by measurable
  have hm': "(\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>') \<in> borel_measurable N"
    using hm A' by measurable
  have fmeas: "(\<lambda>\<omega>. \<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)) \<in> borel_measurable M"
    by (rule measurable_integral_kernel[OF K hm'])
  have aei: "AE \<omega> in M. integrable (Kr \<omega>) h"
    using AE_integrable_ksemi_section[OF K hm2 hi ne] by simp
  have "AE \<omega> in M. \<omega> \<in> space M" by (rule AE_I2) simp
  with aei have bnd: "AE \<omega> in M.
      ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))"
  proof eventually_elim
    fix \<omega> assume i: "integrable (Kr \<omega>) h" and w: "\<omega> \<in> space M"
    have sK: "sets (Kr \<omega>) = sets N" by (rule ksemi_sets_kernel(1)[OF K w])
    have AK: "A' \<in> sets (Kr \<omega>)" using A' sK by simp
    have i2: "integrable (Kr \<omega>) (\<lambda>\<omega>'. indicator A' \<omega>' * h \<omega>')"
      using integrable_mult_indicator[OF AK i] by simp
    have "ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (indicator A' \<omega>' * h \<omega>')) \<partial>(Kr \<omega>))"
      by (rule integral_norm_bound_ennreal[OF i2])
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))"
      by (intro nn_integral_mono ennreal_leI) (simp add: indicator_def abs_mult)
    finally show "ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>)))
        \<le> (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>))" .
  qed
  have "(\<integral>\<^sup>+\<omega>. ennreal (norm (\<integral>\<omega>'. indicator A' \<omega>' * h \<omega>' \<partial>(Kr \<omega>))) \<partial>M)
      \<le> (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>)) \<partial>M)"
    by (rule nn_integral_mono_AE[OF bnd])
  also have "\<dots> = (\<integral>\<^sup>+p. ennreal (norm (h (snd p))) \<partial>(ksemi M N Kr))"
  proof -
    have gmm: "(\<lambda>p :: 'a \<times> 'b. ennreal (norm (h (snd p))))
        \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using hm2 by measurable
    show "(\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. ennreal (norm (h \<omega>')) \<partial>(Kr \<omega>)) \<partial>M)
        = (\<integral>\<^sup>+p. ennreal (norm (h (snd p))) \<partial>(ksemi M N Kr))"
      using nn_integral_ksemi[OF K gmm] by simp
  qed
  also have "\<dots> < \<top>" using hi by (simp add: integrable_iff_bounded)
  finally show ?thesis using fmeas by (simp add: integrable_iff_bounded)
qed

text \<open>The \<open>z\<close> hypothesis: the rectangle integral over the semidirect product
  IS a single SET integral over \<open>P\<close>, the two indicators combining into the
  indicator of \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close>.  That set is where the martingale property
  of \<open>P\<close> gets applied, so this lemma is the whole bridge from the kernel back
  to the original law.\<close>

lemma integral_ksemi_rect_of_set_integral:
  fixes h :: "'b \<Rightarrow> real"
  assumes eq: "ksemi M N Kr = distr P (M \<Otimes>\<^sub>M N) \<phi>"
    and phim: "\<phi> \<in> P \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M N"
    and hm: "h \<in> borel_measurable N"
    and A: "A \<in> sets M" and A': "A' \<in> sets N"
  shows "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * h (snd p))
        \<partial>(ksemi M N Kr))
      = set_lebesgue_integral P (\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
proof -
  let ?g = "\<lambda>p :: 'a \<times> 'b.
      indicator A (fst p) * (indicator A' (snd p) * h (snd p))"
  have gm: "?g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" using A A' hm by measurable
  have "(\<integral>p. ?g p \<partial>(ksemi M N Kr)) = (\<integral>p. ?g p \<partial>(distr P (M \<Otimes>\<^sub>M N) \<phi>))"
    unfolding eq ..
  also have "\<dots> = (\<integral>\<omega>. ?g (\<phi> \<omega>) \<partial>P)" by (rule integral_distr[OF phim gm])
  also have "\<dots> = (\<integral>\<omega>. indicator (\<phi> -` (A \<times> A') \<inter> space P) \<omega> * h (snd (\<phi> \<omega>)) \<partial>P)"
  proof (rule Bochner_Integration.integral_cong[OF refl])
    fix \<omega> assume "\<omega> \<in> space P"
    then show "?g (\<phi> \<omega>)
        = indicator (\<phi> -` (A \<times> A') \<inter> space P) \<omega> * h (snd (\<phi> \<omega>))"
      by (auto simp: indicator_def mem_Times_iff)
  qed
  also have "\<dots> = set_lebesgue_integral P (\<phi> -` (A \<times> A') \<inter> space P)
      (\<lambda>\<omega>. h (snd (\<phi> \<omega>)))"
    unfolding set_lebesgue_integral_def by simp
  finally show ?thesis .
qed

text \<open>The companion of @{thm [source] pfut_filtration_measurable} for the
  PAST.  Together they put \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close> into \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> for
  \<open>A\<close> in the past law's filtration and \<open>A'\<close> in the future law's at level
  \<open>i\<close>, which is what @{thm [source] integral_ksemi_rect_of_set_integral}
  hands to the martingale property of \<open>P\<close>.\<close>

lemma pcut_filtration_measurable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
  shows "pcut r \<in> natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u
      \<rightarrow>\<^sub>M natural_filtration (pair_law_of r (pcut r) P) 0 (\<lambda>v w. w v) u"
proof -
  have phim: "pcut r \<in> P \<rightarrow>\<^sub>M borel_of (mtopology_of
      (path_metric r :: ('n pairpath) metric))"
    by (rule pcut_measurable[OF r rT setsP])
  have adap: "(\<lambda>\<omega> :: 'n pairpath. pcut r \<omega> v)
      \<in> borel_measurable (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) u)"
    if "0 \<le> v" and "v \<le> u" for v
    by (rule pcut_adapted[OF r setsP that])
  have spF: "space (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u)
      = space P" by simp
  show ?thesis
    by (rule phi_filtration_measurable
        [where FF = "\<lambda>u. natural_filtration P 0
            (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) u" and u = u,
         OF phim adap spF])
qed

subsection \<open>The evaluations generate the path space's Borel sets\<close>

text \<open>@{thm [source] pcut_filtration_measurable} lands in the natural
  filtration of the CUT LAW, while the per-\<open>(i,j,A')\<close> statement of (b3)
  quantifies the conditioning set over ALL of \<open>sets ?Q\<close> --- because
  @{thm [source] AE_zero_of_set_integral_zero} is applied with \<open>\<G> = ?Q\<close>, and
  restating it with a genuine sub-\<sigma>-algebra would only move the question to
  the kernel's measurability.  So the two must be the SAME \<sigma>-algebra, i.e.
  the coordinate evaluations have to generate the Borel sets of the path
  space.  They do, and the proof is metric: the distance to a fixed path is
  decided by the RATIONAL times alone, so it is measurable in the filtration,
  hence so is every ball --- and the balls generate, the path space being
  second countable.

  First the coordinates themselves, which is all the easy inclusion needs.\<close>

lemma path_eval_measurable_natural_filtration:
  fixes U v :: real
  assumes v: "v \<in> {0..U}"
  shows "(\<lambda>\<omega> :: 'n::finite pairpath. \<omega> v) \<in> borel_measurable (natural_filtration
      (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
      0 (\<lambda>v \<omega>. \<omega> v) U)"
  unfolding natural_filtration_def
  by (rule measurable_family_vimage_algebra) (use v in auto)

lemma sets_natural_filtration_path_subset:
  fixes U u :: real
  shows "sets (natural_filtration
        (borel_of (mtopology_of (path_metric U :: ('n::finite pairpath) metric)))
        0 (\<lambda>v \<omega>. \<omega> v) u)
      \<subseteq> sets (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  have "(\<Union>i\<in>{0..u}.
      {(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?B | A. A \<in> sets borel})
      \<subseteq> sets ?B"
  proof clarsimp
    fix i :: real and A :: "((real^'n) \<times> (real^'n^'n)) set"
    assume "A \<in> sets borel"
    then show "(\<lambda>\<omega> :: 'n pairpath. \<omega> i) -` A \<inter> space ?B \<in> sets ?B"
      by (rule measurable_sets[OF pair_law_eval_measurable[OF refl]])
  qed
  then show ?thesis
    unfolding sets_natural_filtration by (rule sets.sigma_sets_subset)
qed

text \<open>The metric half.  @{thm [source] path_mdist_le_iff} turns the sup
  distance into a condition at the rational times only --- countably many,
  so @{thm [source] sets.countable_INT'} applies.  Note the intersection is
  over a NONEMPTY index set, which is what keeps \<open>\<omega> \<in> space \<FF>\<close> on the
  \<open>\<supseteq>\<close> side; over an empty one it would be the universe.\<close>

lemma mdist_measurable_natural_filtration:
  fixes U :: real and f :: "'n::finite pairpath"
  assumes U: "0 \<le> U" and f: "f \<in> mspace (path_metric U :: ('n pairpath) metric)"
  shows "(\<lambda>\<omega>. mdist (path_metric U :: ('n pairpath) metric) f \<omega>)
      \<in> borel_measurable (natural_filtration
          (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
          0 (\<lambda>v \<omega>. \<omega> v) U)"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) U"
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have Q0: "(0::real) \<in> {0..U} \<inter> \<rat>" using U by simp
  have neQ: "{0..U} \<inter> (\<rat> :: real set) \<noteq> {}" using Q0 by blast
  have cQ: "countable ({0..U} \<inter> (\<rat> :: real set))"
    by (rule countable_subset[OF _ countable_rat]) simp
  show ?thesis
  proof (subst borel_measurable_iff_le, intro allI)
    fix q :: real
    have iff: "mdist ?m f \<omega> \<le> q \<longleftrightarrow> (\<forall>t\<in>{0..U} \<inter> \<rat>. dist (f t) (\<omega> t) \<le> q)"
      if w: "\<omega> \<in> mspace ?m" for \<omega> :: "'n pairpath"
      by (rule path_mdist_le_iff[OF U f w])
    have mem: "{\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q} \<in> sets ?F"
      if t: "t \<in> {0..U} \<inter> \<rat>" for t
    proof -
      have m: "(\<lambda>\<omega> :: 'n pairpath. dist (f t) (\<omega> t)) \<in> borel_measurable ?F"
        using path_eval_measurable_natural_filtration[of t U] t
        by (intro borel_measurable_dist) auto
      show ?thesis using iffD1[OF borel_measurable_iff_le m] by blast
    qed
    have seteq: "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}
        = (\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
    proof
      show "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}
          \<subseteq> (\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
        using iff spF by auto
    next
      show "(\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})
          \<subseteq> {\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}"
      proof
        fix \<omega> :: "'n pairpath"
        assume w: "\<omega> \<in> (\<Inter>t \<in> {0..U} \<inter> \<rat>.
            {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})"
        have sp: "\<omega> \<in> space ?F" using w Q0 by blast
        then have mw: "\<omega> \<in> mspace ?m" using spF by simp
        have "\<forall>t\<in>{0..U} \<inter> \<rat>. dist (f t) (\<omega> t) \<le> q" using w by blast
        then have "mdist ?m f \<omega> \<le> q" using iff[OF mw] by blast
        then show "\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q}" using sp by simp
      qed
    qed
    have "(\<Inter>t \<in> {0..U} \<inter> \<rat>. {\<omega> \<in> space ?F. dist (f t) (\<omega> t) \<le> q})
        \<in> sets ?F"
      by (rule sets.countable_INT'[OF cQ neQ]) (use mem in auto)
    then show "{\<omega> \<in> space ?F. mdist ?m f \<omega> \<le> q} \<in> sets ?F"
      unfolding seteq .
  qed
qed

text \<open>Hence every metric ball is a filtration event.  The identification of
  the ball with the sublevel set of the distance must NOT be left to
  \<open>auto\<close> or \<open>simp\<close>: with the \<^locale>\<open>Metric_space\<close> interpretation in scope
  the search takes ten minutes on this two-line goal.  A calculation with
  \<open>simp only\<close> closes it instantly.\<close>

lemma mball_in_natural_filtration:
  fixes U :: real and f :: "'n::finite pairpath"
  assumes U: "0 \<le> U" and f: "f \<in> mspace (path_metric U :: ('n pairpath) metric)"
  shows "Metric_space.mball (mspace (path_metric U :: ('n pairpath) metric))
        (mdist (path_metric U :: ('n pairpath) metric)) f e
      \<in> sets (natural_filtration
          (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))
          0 (\<lambda>v \<omega>. \<omega> v) U)"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) U"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have mb: "MS.mball f e = {\<omega> \<in> space ?F. mdist ?m f \<omega> < e}"
  proof (rule set_eqI)
    fix \<omega> :: "'n pairpath"
    have "(\<omega> \<in> MS.mball f e)
        = (f \<in> mspace ?m \<and> \<omega> \<in> mspace ?m \<and> mdist ?m f \<omega> < e)"
      by (rule MS.in_mball)
    also have "\<dots> = (\<omega> \<in> mspace ?m \<and> mdist ?m f \<omega> < e)"
      by (simp only: eqTrueI[OF f] simp_thms)
    also have "\<dots> = (\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> < e})"
      by (simp only: spF mem_Collect_eq)
    finally show "(\<omega> \<in> MS.mball f e)
        = (\<omega> \<in> {\<omega> \<in> space ?F. mdist ?m f \<omega> < e})" .
  qed
  have "{\<omega> \<in> space ?F. mdist ?m f \<omega> < e} \<in> sets ?F"
    by (rule borel_measurable_less[OF mdist_measurable_natural_filtration[OF U f]
        borel_measurable_const])
  then show ?thesis unfolding mb[symmetric] .
qed

text \<open>And the balls generate: the path space is second countable, so its
  Borel \<sigma>-algebra is generated by ANY base
  (@{thm [source] borel_of_second_countable'}), and the balls are one.\<close>

theorem sets_natural_filtration_path:
  fixes U :: real
  assumes U: "0 \<le> U"
  shows "sets (natural_filtration
        (borel_of (mtopology_of (path_metric U :: ('n::finite pairpath) metric)))
        0 (\<lambda>v \<omega>. \<omega> v) U)
      = sets (borel_of (mtopology_of (path_metric U :: ('n pairpath) metric)))"
proof -
  let ?m = "path_metric U :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  let ?F = "natural_filtration ?B 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) U"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  let ?balls = "{MS.mball a \<epsilon> | a \<epsilon>. a \<in> mspace ?m \<and> \<epsilon> > 0}"
  have spF: "space ?F = mspace ?m" by (simp add: space_borel_of)
  have sub: "?balls \<subseteq> Pow (mspace ?m)" using MS.mball_subset_mspace by auto
  have base: "base_in (mtopology_of ?m) ?balls"
    using MS.mtopology_base_in_balls by (simp add: mtopology_of_def)
  have "?B = sigma (topspace (mtopology_of ?m)) ?balls"
    by (rule borel_of_second_countable'
        [OF second_countable_path_metric base_is_subbase[OF base]])
  then have "sets ?B = sigma_sets (mspace ?m) ?balls"
    using sets_measure_of[OF sub] by simp
  also have "\<dots> \<subseteq> sets ?F"
  proof -
    have "?balls \<subseteq> sets ?F" using mball_in_natural_filtration[OF U] by blast
    then have "sigma_sets (space ?F) ?balls \<subseteq> sets ?F"
      by (rule sets.sigma_sets_subset)
    then show ?thesis using spF by simp
  qed
  finally show ?thesis
    using sets_natural_filtration_path_subset[of U U] by blast
qed

subsection \<open>The conditioning rectangle lives in the past-plus-\<open>i\<close> filtration\<close>

text \<open>What @{thm [source] integral_ksemi_rect_of_set_integral} hands to the
  martingale property of \<open>P\<close> is the set \<open>\<phi> \<^sup>-\<^sup>1 (A \<times> A')\<close>.  For the martingale
  property to apply at time \<open>r + i\<close> that set must lie in \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>, and it
  does: the past factor is in \<open>\<F>\<^sub>r\<close> --- this is where
  @{thm [source] sets_natural_filtration_path} is consumed, because \<open>A\<close>
  ranges over ALL Borel sets of the \<open>r\<close>-path space, not merely over the cut
  law's natural filtration --- and the future factor is in \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> by
  @{thm [source] pfut_filtration_measurable}.\<close>

lemma sets_natural_filtration_mono:
  fixes i j :: "'b :: {second_countable_topology, order_topology}"
  assumes ij: "i \<le> j"
  shows "sets (natural_filtration M t\<^sub>0 X i) \<subseteq> sets (natural_filtration M t\<^sub>0 X j)"
  unfolding sets_natural_filtration using ij by (intro sigma_sets_subseteq) force

lemma natural_filtration_cong_space:
  assumes "space M = space N"
  shows "natural_filtration M t\<^sub>0 X t = natural_filtration N t\<^sub>0 X t"
  unfolding natural_filtration_def using assms by simp

lemma pcut_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and A: "A \<in> sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
  shows "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  have sp: "space (pair_law_of r (pcut r) P) = space ?X"
    by (simp add: space_pair_law_of space_borel_of)
  have nfeq: "natural_filtration (pair_law_of r (pcut r) P) 0
        (\<lambda>v w :: 'n pairpath. w v) r
      = natural_filtration ?X 0 (\<lambda>v w. w v) r"
    by (rule natural_filtration_cong_space[OF sp])
  have AQ: "A \<in> sets (natural_filtration (pair_law_of r (pcut r) P) 0
      (\<lambda>v w :: 'n pairpath. w v) r)"
    unfolding nfeq sets_natural_filtration_path[OF r] using A .
  have m: "pcut r \<in> natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r
      \<rightarrow>\<^sub>M natural_filtration (pair_law_of r (pcut r) P) 0 (\<lambda>v w. w v) r"
    by (rule pcut_filtration_measurable[OF r rT setsP])
  have "pcut r -` A \<inter> space (natural_filtration P 0
      (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r)
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) r)"
    by (rule measurable_sets[OF m AQ])
  then show ?thesis by simp
qed

lemma pfut_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  let ?Y = "borel_of (mtopology_of
      (path_metric (T - r) :: ('n pairpath) metric))"
  have sp: "space (pair_law_of (T - r) (pfut r T) P) = space ?Y"
    by (simp add: space_pair_law_of space_borel_of)
  have nfeq: "natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
        (\<lambda>v w :: 'n pairpath. w v) i
      = natural_filtration ?Y 0 (\<lambda>v w. w v) i"
    by (rule natural_filtration_cong_space[OF sp])
  have AQ: "A' \<in> sets (natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
      (\<lambda>v w :: 'n pairpath. w v) i)"
    unfolding nfeq using A' .
  have m: "pfut r T
      \<in> natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min i (T - r))
        \<rightarrow>\<^sub>M natural_filtration (pair_law_of (T - r) (pfut r T) P) 0
            (\<lambda>v w. w v) i"
    by (rule pfut_filtration_measurable[OF r rT setsP])
  have mm: "min i (T - r) = i" using iS by simp
  have "pfut r T -` A' \<inter> space (natural_filtration P 0
      (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
    using measurable_sets[OF m AQ] unfolding mm .
  then show ?thesis by simp
qed

lemma rect_vimage_natural_filtration:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and i: "0 \<le> i" and iS: "i \<le> T - r"
    and A: "A \<in> sets (borel_of (mtopology_of
        (path_metric r :: ('n pairpath) metric)))"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "(\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + i))"
proof -
  have c1: "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) r)"
    by (rule pcut_vimage_natural_filtration[OF r rT setsP A])
  have c1': "pcut r -` A \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
    using c1 sets_natural_filtration_mono[of r "r + i"] i by auto
  have c2: "pfut r T -` A' \<inter> space P
      \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
    by (rule pfut_vimage_natural_filtration[OF r rT setsP i iS A'])
  have "(\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)) -` (A \<times> A') \<inter> space P
      = (pcut r -` A \<inter> space P) \<inter> (pfut r T -` A' \<inter> space P)" by auto
  then show ?thesis using sets.Int[OF c1' c2] by simp
qed

subsection \<open>Step (b3): the martingale increment vanishes under the kernel\<close>

text \<open>The per-\<open>(i,j,A')\<close> statement, and the point at which every piece built
  so far meets.  Read the chain from the outside in:
  @{thm [source] AE_kernel_integral_zero} reduces the almost-sure vanishing
  of the kernel integral to the vanishing of every RECTANGLE integral;
  @{thm [source] integral_ksemi_rect_of_set_integral} turns each rectangle
  integral into a single SET integral over \<open>P\<close>;
  @{thm [source] rect_vimage_natural_filtration} puts that set into
  \<open>\<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close>; and there @{thm [source] martingale.set_integral_eq} closes it.
  The two integrability hypotheses come from
  @{thm [source] integrable_ksemi_of_distr_rect} and
  @{thm [source] integrable_kernel_integral}.

  The statement is COMPONENTWISE (\<open>\<sqdot> $ c\<close>): the workhorse
  @{thm [source] AE_zero_of_set_integral_zero} is real-valued, and \<open>'n\<close> is
  finite, so the finitely many components can be reassembled afterwards
  without leaving the almost-sure world.

  Note the two measures \<^term>\<open>pair_law_of r (pcut r) P\<close> and the Borel algebra
  of the \<open>r\<close>-path space have the same SETS but are not the same term, so the
  hypothesis \<open>eq\<close> --- which mentions the latter --- has to be transported to
  the former before the \<open>ksemi\<close> lemmas apply.\<close>

lemma pfut_rcd_X_increment_zero:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w * ((fst (w j) - fst (w i)) $ c) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?h = "\<lambda>w :: 'n pairpath. (fst (w j) - fst (w i)) $ c"
  have Tr: "0 \<le> ?S" using rT by simp
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have A'Y: "A' \<in> sets ?Y"
    using A' sets_natural_filtration_path_subset[of ?S i] by blast

  \<comment> \<open>transport \<open>eq\<close> from the Borel algebra to the cut law, which have the
      same sets but are different terms\<close>
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast

  \<comment> \<open>the integrand and its integrability under \<open>P\<close>\<close>
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y" for u
    by (rule pair_law_eval_measurable[OF refl])
  have hvec: "(\<lambda>w :: 'n pairpath. fst (w j) - fst (w i)) \<in> borel_measurable ?Y"
    by (intro borel_measurable_diff measurable_compose[OF ev measurable_fst_borel])
  have hm: "?h \<in> borel_measurable ?Y"
  proof -
    have "(\<lambda>w :: 'n pairpath. (fst (w j) - fst (w i)) \<bullet> (axis c 1 :: real^'n))
        \<in> borel_measurable ?Y"
      by (intro borel_measurable_inner hvec borel_measurable_const)
    then show ?thesis by (simp add: inner_axis)
  qed
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)))"
    if u: "u \<in> {0..?S}" for u
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + u) T)))"
      by (rule Mg.integrable) (use r u in simp)
    moreover have "min (r + u) T = r + u" using u rT by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>stated as an equation of FUNCTIONS, and consumed by \<open>unfolding\<close>:
      \<open>simp\<close> distributes the \<open>$ c\<close> over the difference and then the rule's own
      left-hand side no longer matches anything\<close>
  have hP: "(\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))
      = (\<lambda>\<omega>. (fst (\<omega> (r + j)) - fst (\<omega> (r + i))) $ c)"
    by (rule ext) (simp add: pfut_fst[OF j0S] pfut_fst[OF i0S])
  have hi: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))"
    unfolding hP
    by (rule integrable_bounded_linear[OF bounded_linear_vec_nth
        Bochner_Integration.integrable_diff[OF Xint[OF j0S] Xint[OF i0S]]])
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?h (snd p))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
      by (rule measurable_compose[OF measurable_snd hm])
    have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) (\<lambda>p. ?h (snd p))"
      unfolding integrable_distr_eq[OF mphi' hm2] by (rule hi)
    then show ?thesis unfolding eq' .
  qed

  \<comment> \<open>the three hypotheses of @{thm [source] AE_kernel_integral_zero}\<close>
  have gi: "integrable (ksemi ?Q ?Y \<kappa>)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p)))"
    if A: "A \<in> sets ?Q" for A
  proof (rule integrable_ksemi_of_distr_rect)
    show "ksemi ?Q ?Y \<kappa> = distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>" by (rule eq'[symmetric])
    show "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y" by (rule mphi')
    show "?h \<in> borel_measurable ?Y" by (rule hm)
    show "A \<in> sets ?Q" by (rule A)
    show "A' \<in> sets ?Y" by (rule A'Y)
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))" by (rule hi)
  qed
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?\<phi> -` (A \<times> A') \<inter> space P
        \<in> sets (natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i))"
      by (rule rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'])
    have SP: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets P"
    proof -
      have "(0 :: real) \<le> r + i" using r i0 by simp
      then have "sets (natural_filtration P 0
          (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + i)) \<subseteq> sets P"
        by (rule Mg.sets_F_subset)
      then show ?thesis using Sfilt by blast
    qed
    have mi: "min (r + i) T = r + i" using i0 iS rT by simp
    have mj: "min (r + j) T = r + j" using jS rT by simp
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + i) T)))
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (min (r + j) T)))"
      by (rule Mg.set_integral_eq[OF Sfilt]) (use r i0 ij in simp_all)
    then have vec: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + i)))
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (r + j)))"
      unfolding mi mj .
    have comp: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + i)) $ c)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. fst (\<omega> (r + j)) $ c)"
      unfolding set_integral_vec_component[OF SP Xint[OF i0S]]
        set_integral_vec_component[OF SP Xint[OF j0S]]
      using vec by simp
    have si: "set_integrable P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)" if u: "u \<in> {0..?S}" for u
    proof -
      have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + u)) $ c)"
        by (rule integrable_bounded_linear[OF bounded_linear_vec_nth Xint[OF u]])
      then show ?thesis
        unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP])
    qed
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. (fst (\<omega> (r + j)) - fst (\<omega> (r + i))) $ c)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. fst (\<omega> (r + j)) $ c)
          - set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. fst (\<omega> (r + i)) $ c)"
      using set_integral_diff(2)[OF si[OF j0S] si[OF i0S]] by simp
    also have "\<dots> = 0" using comp by simp
    finally have zero: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>))) = 0"
      unfolding hP .
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

text \<open>The other hypothesis
  @{thm [source] sigma_finite_filtered_measure.martingale_of_set_integral_eq}
  wants: the coordinate process is \<open>\<kappa> p'\<close>-integrable at almost every \<open>p'\<close>.
  This one needs no filtration at all --- only that the section of a
  \<open>ksemi\<close>-integrable function is almost surely integrable, which is
  @{thm [source] AE_integrable_ksemi_section} (generalised above from real
  to Banach values, its proof having gone through \<open>norm\<close> all along).\<close>

lemma pfut_rcd_X_integrable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w u))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). fst (snd p u)"
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P "natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      0 "\<lambda>u \<omega>. fst (\<omega> (min u T))" by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd
        measurable_compose[OF ev measurable_fst_borel]])
  have gP: "(\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>)) = (\<lambda>\<omega>. fst (\<omega> (r + u)) - fst (\<omega> r))"
    by (rule ext) (simp add: pfut_fst[OF u])
  have Xint: "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (r + v)))"
    if v: "v \<in> {0..?S}" for v
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. fst (\<omega> (min (r + v) T)))"
      by (rule Mg.integrable) (use r v in simp)
    moreover have "min (r + v) T = r + v" using v rT by simp
    ultimately show ?thesis by simp
  qed
  have r0S: "(0::real) \<in> {0..?S}" using rT by simp
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>))"
      unfolding gP
      by (rule Bochner_Integration.integrable_diff[OF Xint[OF u]])
         (use Xint[OF r0S] r in simp)
    then have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] .
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

subsection \<open>From rational times to all times\<close>

text \<open>The structural step (b3) still needs, and the one an earlier plan note
  had wrong.  Only COUNTABLY many conditions survive the passage from "for
  each, almost surely" to "almost surely, for all", so the martingale
  identity arrives at RATIONAL times only, and extending it to every real
  time is NOT a matter of path continuity alone: pointwise convergence does
  not move a set integral.  It needs UNIFORM INTEGRABILITY.

  And the family in question is a family of conditional expectations of the
  single TERMINAL value, so @{thm [source] prob_space.unif_integrable_of_averaging}
  applies with its hypothesis list verbatim and
  @{thm [source] finite_measure.vitali_convergence} finishes.  Both were
  written for exactly this pattern (the domination-free optional-stopping
  rework) and are reused unchanged; this is why \<open>Paper_DPP\<close> imports
  \<open>Conditional_UI\<close>.  (Do NOT write that as a \<^verbatim>\<open>\<^theory>\<close>
  antiquotation: a session-qualified one hard-codes the session name and makes
  the file unbuildable from any other session.)

  Note the terminal time \<open>S\<close> is a FIXED real, so the pairs \<open>(q, S)\<close> with \<open>q\<close>
  rational are still countably many --- which is what puts the averaging form
  within reach.  Note also that the a.e. convergence Vitali wants is here
  POINTWISE on \<open>space Q\<close>: every point of the path space IS a continuous path.

  (Larsson--Ruf condition with a regular conditional distribution citing
  Stroock--Varadhan Thm 1.3.4, so this route is the authors' own.  Their
  classical conditioning theorem needs none of this because the martingale
  problem is stated with test functions in \<open>C\<^sub>c\<^sup>\<infinity>\<close>, whose martingales are
  BOUNDED; the paper's class (1.7) makes \<open>X\<close> itself and \<open>outerp X - Y\<close> the
  martingales, and those are not.)\<close>

lemma subalgebra_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric S :: ('n pairpath) metric)))"
  shows "subalgebra Q (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?B = "borel_of (mtopology_of (path_metric S :: ('n pairpath) metric))"
  have "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u
      = natural_filtration ?B 0 (\<lambda>v w. w v) u"
    by (rule natural_filtration_cong_space)
       (simp add: sets_eq_imp_space_eq[OF setsQ])
  then have "sets (natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u)
      \<subseteq> sets Q"
    using sets_natural_filtration_path_subset[of S u] setsQ by simp
  then show ?thesis unfolding subalgebra_def by simp
qed

lemma sigma_finite_subalgebra_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes PS: "prob_space Q"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
  shows "sigma_finite_subalgebra Q (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof (rule finite_measure_subalgebra_is_sigma_finite)
  show "finite_measure_subalgebra Q
      (natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u)"
    by (simp add: finite_measure_subalgebra_def
        finite_measure_subalgebra_axioms_def prob_space.finite_measure[OF PS]
        subalgebra_natural_filtration_path[OF setsQ])
qed

theorem integrable_and_set_integral_eq_of_rational_times:
  fixes Q :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
    and PS: "prob_space Q"
    and Zm: "\<And>u. u \<in> {0..S} \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zint: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow> integrable Q (Z q)"
    and ZintS: "integrable Q (Z S)"
    and Zcont: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..S} (\<lambda>u. Z u w)"
    and rat: "\<And>q A. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow>
        A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) q) \<Longrightarrow>
        set_lebesgue_integral Q A (Z q) = set_lebesgue_integral Q A (Z S)"
    and i: "i \<in> {0..S}"
  shows "integrable Q (Z i)
      \<and> (\<forall>A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) i).
          set_lebesgue_integral Q A (Z i) = set_lebesgue_integral Q A (Z S))"
proof (cases "i = S")
  case True
  then show ?thesis using ZintS by simp
next
  case False
  let ?F = "\<lambda>u. natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  interpret PQ: prob_space Q by (rule PS)
  have iS: "i < S" using i False by simp
  have SS: "S \<in> {0..S}" using S by simp

  \<comment> \<open>rationals decreasing to \<open>i\<close> from above, inside the horizon\<close>
  have ex: "\<exists>q\<in>(\<rat> :: real set). i < q \<and> q < min S (i + inverse (real (Suc n)))"
    for n
  proof (rule Rats_dense_in_real)
    show "i < min S (i + inverse (real (Suc n)))" using iS by simp
  qed
  then obtain q :: "nat \<Rightarrow> real" where qrat: "\<And>n. q n \<in> \<rat>"
    and qgt: "\<And>n. i < q n"
    and qlt: "\<And>n. q n < min S (i + inverse (real (Suc n)))" by metis
  have qle: "q n \<le> S" for n using qlt[of n] by simp
  have q0S: "q n \<in> {0..S}" for n using i qgt[of n] qle[of n] by simp
  have qconv: "q \<longlonglongrightarrow> i"
  proof (rule tendsto_sandwich[of "\<lambda>_. i" _ _ "\<lambda>n. i + inverse (real (Suc n))"])
    show "\<forall>\<^sub>F n in sequentially. i \<le> q n" using qgt by (simp add: less_imp_le)
    show "\<forall>\<^sub>F n in sequentially. q n \<le> i + inverse (real (Suc n))"
      using qlt by (simp add: less_imp_le)
  qed (use LIMSEQ_inverse_real_of_nat_add in auto)

  \<comment> \<open>the filtration facts\<close>
  have subA: "subalgebra Q (?F u)" for u
    by (rule subalgebra_natural_filtration_path[OF setsQ])
  have sfs: "sigma_finite_subalgebra Q (?F u)" for u
    by (rule sigma_finite_subalgebra_natural_filtration_path[OF PS setsQ])
  have ZmQ: "Z u \<in> borel_measurable Q" if u: "u \<in> {0..S}" for u
    by (rule measurable_from_subalg[OF subA Zm[OF u]])

  \<comment> \<open>uniform integrability, straight off the averaging form\<close>
  have ui: "unif_integrable Q (\<lambda>n. Z (q n))"
  proof (rule prob_space.unif_integrable_of_averaging[OF PS])
    show "integrable Q (Z S)" by (rule ZintS)
    show "sigma_finite_subalgebra Q (?F (q n))" for n by (rule sfs)
    show "integrable Q (Z (q n))" for n by (rule Zint[OF qrat q0S])
    show "Z (q n) \<in> borel_measurable (?F (q n))" for n by (rule Zm[OF q0S])
    show "set_lebesgue_integral Q B (Z S) = set_lebesgue_integral Q B (Z (q n))"
      if "B \<in> sets (?F (q n))" for n B
      by (rule rat[OF qrat q0S that, symmetric])
  qed

  \<comment> \<open>pointwise convergence, from path continuity\<close>
  have conv: "AE w in Q. (\<lambda>n. Z (q n) w) \<longlonglongrightarrow> Z i w"
  proof (rule AE_I2)
    fix w :: "'n pairpath" assume w: "w \<in> space Q"
    have "((\<lambda>u. Z u w) \<circ> q) \<longlonglongrightarrow> Z i w"
      using Zcont[OF w] q0S i qconv by (simp add: continuous_on_sequentially)
    then show "(\<lambda>n. Z (q n) w) \<longlonglongrightarrow> Z i w" by (simp add: o_def)
  qed

  \<comment> \<open>integrability at the IRRATIONAL time comes free from the same argument\<close>
  have Zi: "integrable Q (Z i)"
    by (rule finite_measure.unif_integrable_limit_integrable
        [OF PQ.finite_measure_axioms ui ZmQ[OF i] conv])
  have vit: "(\<lambda>n. \<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q) \<longlonglongrightarrow> 0"
    by (rule finite_measure.vitali_convergence
        [OF PQ.finite_measure_axioms ui ZmQ[OF i] conv])

  \<comment> \<open>and the set integrals follow the \<open>L\<^sup>1\<close> limit\<close>
  have main: "set_lebesgue_integral Q A (Z i) = set_lebesgue_integral Q A (Z S)"
    if A: "A \<in> sets (?F i)" for A
  proof -
    have AQ: "A \<in> sets Q" using A subA[of i] by (auto simp: subalgebra_def)
    have AF: "A \<in> sets (?F (q n))" for n
      using A sets_natural_filtration_mono[of i "q n"] qgt[of n] by auto
    have bnd: "\<bar>set_lebesgue_integral Q A (Z S) - set_lebesgue_integral Q A (Z i)\<bar>
        \<le> (\<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q)" for n
    proof -
      have s1: "set_integrable Q A (Z (q n))"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ Zint[OF qrat q0S]])
      have s2: "set_integrable Q A (Z i)"
        unfolding set_integrable_def
        by (rule integrable_mult_indicator[OF AQ Zi])
      have dd: "integrable Q (\<lambda>w. indicat_real A w *\<^sub>R (Z (q n) w - Z i w))"
        by (rule integrable_mult_indicator[OF AQ
            Bochner_Integration.integrable_diff[OF Zint[OF qrat q0S] Zi]])
      have d1: "integrable Q (\<lambda>w. \<bar>indicat_real A w *\<^sub>R (Z (q n) w - Z i w)\<bar>)"
        by (rule integrable_abs[OF dd])
      have d2: "integrable Q (\<lambda>w. \<bar>Z (q n) w - Z i w\<bar>)"
        by (intro integrable_abs Bochner_Integration.integrable_diff
            Zint[OF qrat q0S] Zi)
      have "\<bar>set_lebesgue_integral Q A (Z S) - set_lebesgue_integral Q A (Z i)\<bar>
          = \<bar>set_lebesgue_integral Q A (Z (q n))
              - set_lebesgue_integral Q A (Z i)\<bar>"
        using rat[OF qrat q0S AF] by simp
      also have "\<dots> = \<bar>\<integral>w. indicat_real A w *\<^sub>R (Z (q n) w - Z i w) \<partial>Q\<bar>"
        using set_integral_diff(2)[OF s1 s2]
        unfolding set_lebesgue_integral_def by (simp add: scaleR_diff_right)
      also have "\<dots> \<le> (\<integral>w. \<bar>indicat_real A w *\<^sub>R (Z (q n) w - Z i w)\<bar> \<partial>Q)"
        by (rule integral_abs_bound)
      also have "\<dots> \<le> (\<integral>w. \<bar>Z (q n) w - Z i w\<bar> \<partial>Q)"
        by (rule integral_mono[OF d1 d2]) (simp add: indicator_def)
      finally show ?thesis .
    qed
    have "\<bar>set_lebesgue_integral Q A (Z S)
        - set_lebesgue_integral Q A (Z i)\<bar> \<le> 0"
      by (rule LIMSEQ_le_const[OF vit]) (use bnd in blast)
    then show ?thesis by simp
  qed
  show ?thesis using Zi main by blast
qed

subsection \<open>From a generating \<pi>-system to the whole sub-\<sigma>-algebra\<close>

text \<open>The other half of the countability bookkeeping.  The conditioning set
  \<open>A'\<close> of @{thm [source] pfut_rcd_X_increment_zero} also has to range over a
  COUNTABLE family, so what arrives at almost every \<open>p'\<close> is the vanishing of
  the set integral on a \<pi>-system only.  Upgrading that to the generated
  \<sigma>-algebra is a Dynkin argument, and both halves of it are in the
  distribution: @{thm [source] sigma_sets_induct_disjoint} does the induction
  and @{thm [source] lebesgue_integral_countable_add} discharges its
  disjoint-union case.  The complement case is where \<open>space M \<in> E\<close> is used,
  so the \<pi>-system must be given WITH the whole space in it.

  Stated for a general measure and a general generating \<pi>-system: nothing
  here is about paths, and the same lemma serves clause (iv).\<close>

lemma set_integral_zero_of_generator:
  fixes g :: "'a \<Rightarrow> real"
  assumes G: "subalgebra M G"
    and gi: "integrable M g"
    and Est: "Int_stable E"
    and Epow: "E \<subseteq> Pow (space M)"
    and Egen: "sets G = sigma_sets (space M) E"
    and Esp: "space M \<in> E"
    and z: "\<And>B. B \<in> E \<Longrightarrow> set_lebesgue_integral M B g = 0"
    and A: "A \<in> sets G"
  shows "set_lebesgue_integral M A g = 0"
proof -
  have GM: "sets G \<subseteq> sets M" using G by (simp add: subalgebra_def)
  have inM: "B \<in> sets M" if "B \<in> sigma_sets (space M) E" for B
    using that GM Egen by auto
  have si: "set_integrable M B g" if "B \<in> sets M" for B
    unfolding set_integrable_def by (rule integrable_mult_indicator[OF that gi])
  have Asig: "A \<in> sigma_sets (space M) E" using A Egen by simp
  from Est Epow Asig show ?thesis
  proof (induction rule: sigma_sets_induct_disjoint)
    case (basic B)
    then show ?case by (rule z)
  next
    case empty
    show ?case by (simp add: set_lebesgue_integral_def)
  next
    case (compl B)
    have BM: "B \<in> sets M" by (rule inM[OF compl.hyps])
    have CM: "space M - B \<in> sets M" using BM by (rule sets.compl_sets)
    have "set_lebesgue_integral M ((space M - B) \<union> B) g
        = set_lebesgue_integral M (space M - B) g
          + set_lebesgue_integral M B g"
      by (rule set_integral_Un[OF _ si[OF CM] si[OF BM]]) auto
    moreover have "(space M - B) \<union> B = space M"
      using sets.sets_into_space[OF BM] by auto
    ultimately have "set_lebesgue_integral M (space M) g
        = set_lebesgue_integral M (space M - B) g
          + set_lebesgue_integral M B g" by simp
    then show ?case using z[OF Esp] compl.IH by simp
  next
    case (union F)
    have FM: "F i \<in> sets M" for i using union.hyps(2) inM by blast
    have UM: "(\<Union>i. F i) \<in> sets M"
      by (rule sets.countable_nat_UN) (use FM in auto)
    have "set_lebesgue_integral M (\<Union>i. F i) g
        = (\<Sum>i. set_lebesgue_integral M (F i) g)"
      by (rule lebesgue_integral_countable_add[OF FM _ si[OF UM]])
         (use union.hyps(1) in \<open>auto simp: disjoint_family_on_def\<close>)
    also have "\<dots> = 0" using union.IH by simp
    finally show ?case .
  qed
qed

text \<open>And the \<pi>-system the previous lemma is going to be handed.  The key
  identification is that \<open>\<F>\<^sub>s\<close> IS the pullback of the \<open>s\<close>-path space's Borel
  sets along \<^const>\<open>pcut\<close> --- one inclusion is
  @{thm [source] natural_filtration_eq_restrict_vimage} (already in
  \<open>Paper_Bridge\<close>), the other is
  @{thm [source] pcut_vimage_natural_filtration}.

  That identification is what makes the countable \<pi>-system cheap.  Going
  through the coordinate evaluations directly would force a restriction of
  the TIME index to the rationals, and hence a limit-of-measurable-functions
  argument to recover the irrational times.  Going through \<^const>\<open>pcut\<close>
  instead, the continuity of the paths is already encoded in the topology of
  the \<open>s\<close>-path space, and SECOND COUNTABILITY of that space
  (@{thm [source] second_countable_path_metric}) hands over a countable base
  with no limit argument at all.\<close>

lemma sets_natural_filtration_eq_pcut_vimage:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
  shows "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s)
      = {pcut s -` B \<inter> space Q | B. B \<in> sets (borel_of (mtopology_of
          (path_metric s :: ('n pairpath) metric)))}"
proof (rule set_eqI, rule iffI)
  let ?Bs = "borel_of (mtopology_of (path_metric s :: ('n pairpath) metric))"
  fix A :: "('n pairpath) set"
  assume "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)"
  then obtain Bs where Bs: "Bs \<in> sets ?Bs"
    and Aeq: "A = (\<lambda>\<omega> :: 'n pairpath. restrict \<omega> {0..s}) -` Bs \<inter> space Q"
    by (rule natural_filtration_eq_restrict_vimage[OF setsQ s sT]) blast
  have "A = pcut s -` Bs \<inter> space Q" unfolding Aeq pcut_def ..
  with Bs show "A \<in> {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}" by blast
next
  let ?Bs = "borel_of (mtopology_of (path_metric s :: ('n pairpath) metric))"
  fix A :: "('n pairpath) set"
  assume "A \<in> {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}"
  then obtain B where B: "B \<in> sets ?Bs" and Aeq: "A = pcut s -` B \<inter> space Q"
    by blast
  show "A \<in> sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)"
    unfolding Aeq by (rule pcut_vimage_natural_filtration[OF s sT setsQ B])
qed

text \<open>A COUNTABLE \<pi>-system generating the path space's Borel sets.  A base is
  not \<pi>-stable, so close it under FINITE intersections --- still countable,
  and it generates the same \<sigma>-algebra because a \<sigma>-algebra is closed under
  finite intersections.  The whole space is thrown in so that the complement
  case of @{thm [source] set_integral_zero_of_generator} has something to
  work with.\<close>

lemma countable_Int_stable_generator_path:
  fixes s :: real
  obtains D where
    "countable D"
    and "Int_stable D"
    and "D \<subseteq> Pow (mspace (path_metric s :: ('n::finite pairpath) metric))"
    and "mspace (path_metric s :: ('n pairpath) metric) \<in> D"
    and "sets (borel_of (mtopology_of (path_metric s :: ('n pairpath) metric)))
        = sigma_sets (mspace (path_metric s :: ('n pairpath) metric)) D"
proof -
  let ?m = "path_metric s :: ('n pairpath) metric"
  let ?X = "mtopology_of ?m"
  have sc: "second_countable ?X" by (rule second_countable_path_metric)
  \<comment> \<open>NB the base must not be called \<open>OO\<close>: that name is the relation-composition
      operator and the statement then fails to parse\<close>
  then obtain BB where cB: "countable BB" and bB: "base_in ?X BB"
    using second_countable_base_in by blast
  have Bsub: "U \<subseteq> mspace ?m" if "U \<in> BB" for U
    using base_in_subset[OF bB that] by simp
  define B1 where "B1 = insert (mspace ?m) BB"
  have cB1: "countable B1" unfolding B1_def using cB by simp
  have B1sub: "U \<subseteq> mspace ?m" if "U \<in> B1" for U
    using that Bsub unfolding B1_def by auto
  define FF where "FF = {F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> B1}"
  define D where "D = (\<lambda>F. \<Inter> F) ` FF"

  \<comment> \<open>membership in \<open>D\<close>, introduced and eliminated WITHOUT search: \<open>blast\<close> on
      the existential behind an image diverges (it has to invent the witness)\<close>
  have DE: "\<And>A. A \<in> D \<Longrightarrow> (\<And>F. A = \<Inter> F \<Longrightarrow> finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> B1 \<Longrightarrow> thesis')
      \<Longrightarrow> thesis'" for thesis'
  proof -
    fix A assume AD: "A \<in> D"
      and W: "\<And>F. A = \<Inter> F \<Longrightarrow> finite F \<Longrightarrow> F \<noteq> {} \<Longrightarrow> F \<subseteq> B1 \<Longrightarrow> thesis'"
    from AD obtain F where Aeq: "A = \<Inter> F" and FF: "F \<in> FF"
      unfolding D_def by (rule imageE)
    from FF have "finite F" "F \<noteq> {}" "F \<subseteq> B1" unfolding FF_def by simp_all
    with Aeq show thesis' by (rule W)
  qed
  have DI: "\<Inter> F \<in> D" if "finite F" "F \<noteq> {}" "F \<subseteq> B1" for F
  proof -
    have "F \<in> FF" unfolding FF_def using that by simp
    then show ?thesis unfolding D_def by (rule image_eqI[OF refl])
  qed

  have cD: "countable D"
    unfolding D_def FF_def
    by (intro countable_image
        countable_subset[OF _ countable_Collect_finite_subset[OF cB1]]) auto
  have Dpow: "D \<subseteq> Pow (mspace ?m)"
  proof
    fix A assume "A \<in> D"
    then show "A \<in> Pow (mspace ?m)"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      from F(2) obtain U where U: "U \<in> F" by blast
      have "A \<subseteq> U" unfolding Aeq using U by blast
      moreover have "U \<subseteq> mspace ?m" using U F(3) B1sub by blast
      ultimately show "A \<in> Pow (mspace ?m)" by auto
    qed
  qed
  have Dtop: "mspace ?m \<in> D"
  proof -
    have "\<Inter> {mspace ?m} \<in> D"
      by (rule DI) (simp_all add: B1_def)
    then show ?thesis by simp
  qed
  have DInt: "Int_stable D"
    unfolding Int_stable_def
  proof (intro ballI)
    fix A B assume A: "A \<in> D" and B: "B \<in> D"
    from A show "A \<inter> B \<in> D"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      from B show "A \<inter> B \<in> D"
      proof (rule DE)
        fix G assume Beq: "B = \<Inter> G" and G: "finite G" "G \<noteq> {}" "G \<subseteq> B1"
        have "A \<inter> B = \<Inter> (F \<union> G)"
          unfolding Aeq Beq by (simp add: Inter_Un_distrib)
        moreover have "\<Inter> (F \<union> G) \<in> D"
          by (rule DI) (use F G in auto)
        ultimately show "A \<inter> B \<in> D" by simp
      qed
    qed
  qed

  \<comment> \<open>the base already generates, and closing under finite intersections
      changes nothing\<close>
  have Bpow: "BB \<subseteq> Pow (mspace ?m)" using Bsub by auto
  have bsets: "sets (borel_of ?X) = sigma_sets (mspace ?m) BB"
  proof -
    have "borel_of ?X = sigma (topspace ?X) BB"
      by (rule borel_of_second_countable'[OF sc base_is_subbase[OF bB]])
    then have "borel_of ?X = sigma (mspace ?m) BB" by simp
    then show ?thesis using sets_measure_of[OF Bpow] by simp
  qed
  have Deq: "sigma_sets (mspace ?m) D = sigma_sets (mspace ?m) BB"
  proof (rule sigma_sets_eqI)
    fix A assume A: "A \<in> D"
    interpret SA: sigma_algebra "mspace ?m" "sigma_sets (mspace ?m) BB"
      by (rule sigma_algebra_sigma_sets[OF Bpow])
    from A show "A \<in> sigma_sets (mspace ?m) BB"
    proof (rule DE)
      fix F assume Aeq: "A = \<Inter> F" and F: "finite F" "F \<noteq> {}" "F \<subseteq> B1"
      have "U \<in> sigma_sets (mspace ?m) BB" if "U \<in> F" for U
        using that F(3) unfolding B1_def by (auto simp: sigma_sets_top)
      then have "(\<Inter>U\<in>F. U) \<in> sigma_sets (mspace ?m) BB"
        by (rule SA.finite_INT[OF F(1) F(2)])
      then show "A \<in> sigma_sets (mspace ?m) BB" unfolding Aeq by simp
    qed
  next
    fix U assume U: "U \<in> BB"
    have "\<Inter> {U} \<in> D" by (rule DI) (use U in \<open>simp_all add: B1_def\<close>)
    then have "U \<in> D" by simp
    then show "U \<in> sigma_sets (mspace ?m) D" by (rule sigma_sets.Basic)
  qed
  have Dsets: "sets (borel_of ?X) = sigma_sets (mspace ?m) D"
    unfolding bsets Deq ..
  show thesis by (rule that[OF cD DInt Dpow Dtop Dsets])
qed

text \<open>And its pullback: the countable \<pi>-system for \<open>\<F>\<^sub>s\<close> that (b3)'s
  conditioning sets are going to range over.\<close>

lemma countable_pi_system_natural_filtration_path:
  fixes Q :: "('n::finite pairpath) measure"
  assumes setsQ: "sets Q = sets (borel_of (mtopology_of
      (path_metric T :: ('n pairpath) metric)))"
    and s: "0 \<le> s" and sT: "s \<le> T"
  obtains E where
    "countable E"
    and "Int_stable E"
    and "E \<subseteq> Pow (space Q)"
    and "space Q \<in> E"
    and "sets (natural_filtration Q 0 (\<lambda>u \<omega>. \<omega> u) s) = sigma_sets (space Q) E"
proof -
  let ?ms = "path_metric s :: ('n pairpath) metric"
  let ?Bs = "borel_of (mtopology_of ?ms)"
  let ?pb = "\<lambda>U. pcut s -` U \<inter> space Q"
  obtain D where cD: "countable D" and DInt: "Int_stable D"
    and Dpow: "D \<subseteq> Pow (mspace ?ms)" and Dtop: "mspace ?ms \<in> D"
    and Dsets: "sets ?Bs = sigma_sets (mspace ?ms) D"
    by (rule countable_Int_stable_generator_path)
  have spQ: "space Q = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsQ])
  have pin: "pcut s \<in> space Q \<rightarrow> mspace ?ms"
    using restrict_in_mspace[OF s sT] spQ unfolding pcut_def by auto
  define E where "E = ?pb ` D"

  have cE: "countable E" unfolding E_def by (rule countable_image[OF cD])
  have Epow: "E \<subseteq> Pow (space Q)" unfolding E_def by auto
  have Etop: "space Q \<in> E"
  proof -
    have "space Q = ?pb (mspace ?ms)" using pin by auto
    then show ?thesis unfolding E_def by (rule image_eqI[OF _ Dtop])
  qed
  have EInt: "Int_stable E"
    unfolding Int_stable_def
  proof (intro ballI)
    fix A B assume "A \<in> E" "B \<in> E"
    then obtain U V where Aeq: "A = ?pb U" and U: "U \<in> D"
      and Beq: "B = ?pb V" and V: "V \<in> D"
      unfolding E_def by blast
    have "A \<inter> B = ?pb (U \<inter> V)" unfolding Aeq Beq by auto
    moreover have "U \<inter> V \<in> D" using U V DInt by (simp add: Int_stable_def)
    ultimately show "A \<inter> B \<in> E" unfolding E_def by (rule image_eqI)
  qed
  have Egen: "sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)
      = sigma_sets (space Q) E"
  proof -
    have "sets (natural_filtration Q 0 (\<lambda>u \<omega> :: 'n pairpath. \<omega> u) s)
        = {pcut s -` B \<inter> space Q | B. B \<in> sets ?Bs}"
      by (rule sets_natural_filtration_eq_pcut_vimage[OF setsQ s sT])
    also have "\<dots> = {pcut s -` B \<inter> space Q | B. B \<in> sigma_sets (mspace ?ms) D}"
      unfolding Dsets ..
    also have "\<dots> = sigma_sets (space Q) {pcut s -` U \<inter> space Q | U. U \<in> D}"
      by (rule sigma_sets_vimage_commute[OF pin])
    also have "\<dots> = sigma_sets (space Q) E"
      unfolding E_def by (simp add: Setcompr_eq_image)
    finally show ?thesis .
  qed
  show thesis by (rule that[OF cE EInt Epow Etop Egen])
qed

subsection \<open>The martingale property at a fixed law\<close>

text \<open>Everything (b3) needs at a FIXED \<open>p'\<close>, packaged: adaptedness,
  integrability, continuity in time and the set-integral identity against the
  terminal value AT RATIONAL TIMES ONLY give the martingale property.  The
  two upgrades are
  @{thm [source] integrable_and_set_integral_eq_of_rational_times}
  (rational to real, and it supplies the integrability at the irrational
  times too) and, inside its \<open>rat\<close> hypothesis at the call site,
  @{thm [source] set_integral_zero_of_generator} (\<pi>-system to \<open>\<F>\<^sub>q\<close>).

  The process is required to be CONSTANT past \<open>S\<close> --- which the capped
  \<open>\<lambda>u w. w (min u S)\<close> is --- because the filtration is indexed by all of
  \<open>[0,\<infinity>)\<close> while the path space only knows about \<open>[0,S]\<close>.\<close>

lemma martingale_of_rational_set_integral_eq:
  fixes Q :: "('n::finite pairpath) measure"
    and Z :: "real \<Rightarrow> 'n pairpath \<Rightarrow> real"
  assumes S: "0 \<le> S"
    and setsQ: "sets Q = sets (borel_of (mtopology_of
        (path_metric S :: ('n pairpath) metric)))"
    and PS: "prob_space Q"
    and Zm: "\<And>u. u \<in> {0..S} \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zm': "\<And>u. 0 \<le> u \<Longrightarrow>
        Z u \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
    and Zint: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow> integrable Q (Z q)"
    and ZintS: "integrable Q (Z S)"
    and Zcont: "\<And>w. w \<in> space Q \<Longrightarrow> continuous_on {0..S} (\<lambda>u. Z u w)"
    and Zcap: "\<And>u. S \<le> u \<Longrightarrow> Z u = Z S"
    and rat: "\<And>q A. q \<in> \<rat> \<Longrightarrow> q \<in> {0..S} \<Longrightarrow>
        A \<in> sets (natural_filtration Q 0 (\<lambda>v w. w v) q) \<Longrightarrow>
        set_lebesgue_integral Q A (Z q) = set_lebesgue_integral Q A (Z S)"
  shows "martingale Q (natural_filtration Q 0 (\<lambda>v w. w v)) 0 Z"
proof -
  let ?F = "\<lambda>u. natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have fm: "filtered_measure Q ?F 0"
  proof (intro filtered_measure.intro)
    show "subalgebra Q (?F u)" if "(0::real) \<le> u" for u
      by (rule subalgebra_natural_filtration_path[OF setsQ])
    show "sets (?F u) \<subseteq> sets (?F v)" if "(0::real) \<le> u" "u \<le> v" for u v
      by (rule sets_natural_filtration_mono[OF that(2)])
  qed
  interpret SFF: sigma_finite_filtered_measure Q ?F 0
    by (intro sigma_finite_filtered_measure.intro
        sigma_finite_filtered_measure_axioms.intro fm
        sigma_finite_subalgebra_natural_filtration_path[OF PS setsQ])

  \<comment> \<open>integrability AND the identity against the terminal value, both at
      every time in the horizon and both out of the rational data\<close>
  have both: "integrable Q (Z u)
      \<and> (\<forall>A \<in> sets (?F u). set_lebesgue_integral Q A (Z u)
          = set_lebesgue_integral Q A (Z S))"
    if u: "u \<in> {0..S}" for u
    by (rule integrable_and_set_integral_eq_of_rational_times
        [OF S setsQ PS Zm Zint ZintS Zcont rat u])
  have Zall: "integrable Q (Z u)" if u: "0 \<le> u" for u
  proof (cases "u \<le> S")
    case True
    have "u \<in> {0..S}" using u True by simp
    from both[OF this] show ?thesis by blast
  next
    case False
    have "S \<le> u" using False by simp
    then have "Z u = Z S" by (rule Zcap)
    then show ?thesis using ZintS by simp
  qed
  have term_eq: "set_lebesgue_integral Q A (Z u) = set_lebesgue_integral Q A (Z S)"
    if u: "0 \<le> u" and A: "A \<in> sets (?F u)" for u A
  proof (cases "u \<le> S")
    case True
    have "u \<in> {0..S}" using u True by simp
    from both[OF this] show ?thesis using A by blast
  next
    case False
    have "S \<le> u" using False by simp
    then have "Z u = Z S" by (rule Zcap)
    then show ?thesis by (rule arg_cong)
  qed

  show ?thesis
  proof (rule SFF.martingale_of_set_integral_eq)
    show "adapted_process Q ?F 0 Z"
    proof (intro adapted_process.intro adapted_process_axioms.intro)
      show "filtered_measure Q ?F 0" by (rule fm)
      show "Z u \<in> borel_measurable (?F u)" if "(0::real) \<le> u" for u
        by (rule Zm'[OF that])
    qed
    show "integrable Q (Z u)" if "(0::real) \<le> u" for u by (rule Zall[OF that])
    fix A and u v :: real
    assume u: "0 \<le> u" and uv: "u \<le> v" and A: "A \<in> ?F u"
    have AF: "A \<in> sets (?F u)" using A by simp
    have AFv: "A \<in> sets (?F v)"
      using AF sets_natural_filtration_mono[OF uv] by blast
    have "set_lebesgue_integral Q A (Z u) = set_lebesgue_integral Q A (Z S)"
      by (rule term_eq[OF u AF])
    also have "\<dots> = set_lebesgue_integral Q A (Z v)"
      by (rule term_eq[OF _ AFv, symmetric]) (use u uv in simp)
    finally show "set_lebesgue_integral Q A (Z u)
        = set_lebesgue_integral Q A (Z v)" .
  qed
qed

subsection \<open>Clause (iii) for the conditional law\<close>

text \<open>The two pointwise facts about the capped coordinate that the fixed-law
  lemma asks for.  Neither depends on the measure: the natural filtration
  only sees \<open>space Q\<close>, and continuity in time is a property of the path.\<close>

lemma eval_component_measurable_nf:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and u: "0 \<le> u"
  shows "(\<lambda>w :: 'n pairpath. fst (w (min u S)) $ c)
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have ev: "(\<lambda>w :: 'n pairpath. w (min u S)) \<in> borel_measurable ?F"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use S u in auto)
  have f1: "(\<lambda>w :: 'n pairpath. fst (w (min u S))) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF ev measurable_fst_borel])
  have "(\<lambda>w :: 'n pairpath. fst (w (min u S)) \<bullet> (axis c 1 :: real^'n))
      \<in> borel_measurable ?F"
    by (intro borel_measurable_inner f1 borel_measurable_const)
  then show ?thesis by (simp add: inner_axis)
qed

lemma eval_component_continuous:
  fixes w :: "'n::finite pairpath"
  assumes w: "w \<in> mspace (path_metric S :: ('n pairpath) metric)"
  shows "continuous_on {0..S} (\<lambda>u. fst (w (min u S)) $ c)"
proof -
  have "continuous_on {0..S} w" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..S} (\<lambda>u. fst (w u))" by (rule continuous_on_fst)
  then have c1: "continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have "continuous_on {0..S} (\<lambda>u. fst (w (min u S)) $ c)
      = continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    by (rule continuous_on_cong[OF refl]) simp
  then show ?thesis using c1 by simp
qed

text \<open>Clause (iii) of (1.7) for the conditional law.  Everything (b3) built
  meets here:

  \<^item> @{thm [source] pfut_rcd_X_increment_zero} supplies one almost-sure
    condition per \<open>(q, A', c)\<close>, and there are only countably many of those
    --- rational \<open>q\<close>, \<open>A'\<close> in the \<pi>-system of
    @{thm [source] countable_pi_system_natural_filtration_path}, and \<open>c\<close> in
    the finite index type;
  \<^item> @{thm [source] AE_ball_countable'} turns "for each, almost surely" into
    "almost surely, for all";
  \<^item> at a fixed good \<open>p'\<close>, @{thm [source] set_integral_zero_of_generator}
    widens the \<pi>-system to \<open>\<F>\<^sub>q\<close> and
    @{thm [source] martingale_of_rational_set_integral_eq} widens the
    rational times to all times;
  \<^item> @{thm [source] martingale_vecI} puts the finitely many components back
    together.\<close>

theorem pfut_rcd_X_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P (natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v)) 0
        (\<lambda>u \<omega>. fst (\<omega> (min u T)))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. fst (w (min u (T - r))))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: 'n pairpath. w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  \<comment> \<open>the countable \<pi>-system, one per time\<close>
  have exPi: "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    if q: "q \<in> {0..?S}" for q
  proof (rule countable_pi_system_natural_filtration_path
      [where Q = ?Y and T = ?S and s = q])
    show "sets ?Y = sets (borel_of (mtopology_of
        (path_metric ?S :: ('n pairpath) metric)))" ..
    show "0 \<le> q" using q by simp
    show "q \<le> ?S" using q by simp
    fix E assume "countable E" "Int_stable E" "E \<subseteq> Pow (space ?Y)"
      "space ?Y \<in> E" "sets (?G q) = sigma_sets (space ?Y) E"
    then show "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
        \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
      by (intro exI[of _ E] conjI)
  qed
  have "\<forall>q \<in> {0..?S}. \<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    using exPi by blast
  from bchoice[OF this] obtain Eg where
    Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
        \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
        \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  have Espec: "countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    if q: "q \<in> {0..?S}" for q by (rule bspec[OF Espec0 q])

  \<comment> \<open>the countably many almost-sure conditions\<close>
  have step: "AE p' in ?Q.
      (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
    if q: "q \<in> {0..?S}" and A': "A' \<in> sets (?G q)" for q A' and c :: 'n
    by (rule pfut_rcd_X_increment_zero[OF r rT setsP PS K eq mg _ _ _ A'])
       (use q in auto)
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have cEg: "countable (Eg q)" using Espec[OF True] by blast
      have "AE p' in ?Q. \<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
          (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ cEg])
        fix A' assume A': "A' \<in> Eg q"
        have AG: "A' \<in> sets (?G q)"
          using A' Espec[OF True] by auto
        show "AE p' in ?Q. \<forall>c \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
          by (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
             (use step[OF True AG] in blast)
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_X_integrable[OF r rT setsP PS K eq mg True]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S))"
    by (rule pfut_rcd_X_integrable[OF r rT setsP PS K eq mg SS])

  \<comment> \<open>and the assembly at each good \<open>p'\<close>\<close>
  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A' c. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow>
          integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q))"
      and SI: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: ('n pairpath) metric)"
      by (simp add: space_borel_of)

    show ?case
    proof (rule martingale_vecI)
      fix c :: 'n
      have Zint: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)"
        if qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}" for q
      proof -
        have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RI[OF qrat q]])
        moreover have "min q ?S = q" using q by simp
        ultimately show ?thesis by simp
      qed
      have ZintS: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. fst (w (min ?S ?S)) $ c)"
      proof -
        have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          by (rule integrable_bounded_linear[OF bounded_linear_vec_nth SI])
        then show ?thesis by simp
      qed
      show "martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
          (\<lambda>u w. fst (w (min u ?S)) $ c)"
      proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "u \<in> {0..?S}" for u
          by (rule eval_component_measurable_nf[OF Tr]) (use that in simp)
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "0 \<le> u" for u
          by (rule eval_component_measurable_nf[OF Tr that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)"
          if "q \<in> \<rat>" "q \<in> {0..?S}" for q by (rule Zint[OF that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w (min ?S ?S)) $ c)"
          by (rule ZintS)
        show "continuous_on {0..?S} (\<lambda>u. fst (w (min u ?S)) $ c)"
          if "w \<in> space (\<kappa> p')" for w :: "'n pairpath"
          using that spK spY by (intro eval_component_continuous) simp
        show "(\<lambda>w :: 'n pairpath. fst (w (min u ?S)) $ c)
            = (\<lambda>w. fst (w (min ?S ?S)) $ c)" if "?S \<le> u" for u
          using that by simp
        \<comment> \<open>the \<pi>-system widens to \<open>\<F>\<^sub>q\<close> at this fixed \<open>p'\<close>\<close>
        fix q :: real and A
        assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
          and A: "A \<in> sets (natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) q)"
        have AG: "A \<in> sets (?G q)" using A nfK by simp
        have EgS: "countable (Eg q)" "Int_stable (Eg q)"
          "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
          "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
          using Espec[OF q] by blast+
        have subG: "subalgebra (\<kappa> p') (?G q)"
          using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
        have iq: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          by (rule integrable_bounded_linear
              [OF bounded_linear_vec_nth RI[OF qrat q]])
        have iS: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          by (rule integrable_bounded_linear[OF bounded_linear_vec_nth SI])
        have gi: "integrable (\<kappa> p')
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c)"
          by (rule Bochner_Integration.integrable_diff[OF iS iq])
        have gz: "set_lebesgue_integral (\<kappa> p') B
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c) = 0"
          if B: "B \<in> Eg q" for B
        proof -
          have "set_lebesgue_integral (\<kappa> p') B
                (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c)
              = (\<integral>w. indicator B w * ((fst (w ?S) - fst (w q)) $ c) \<partial>(\<kappa> p'))"
            unfolding set_lebesgue_integral_def by simp
          also have "\<dots> = 0" by (rule Z0[OF qrat q B])
          finally show ?thesis .
        qed
        have zA: "set_lebesgue_integral (\<kappa> p') A
            (\<lambda>w :: 'n pairpath. fst (w ?S) $ c - fst (w q) $ c) = 0"
          by (rule set_integral_zero_of_generator
              [OF subG gi EgS(2) _ _ _ gz AG])
             (use EgS(3) EgS(4) EgS(5) spK in simp_all)
        have AQ: "A \<in> sets (\<kappa> p')"
          using AG subG by (auto simp: subalgebra_def)
        have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iS])
        have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath. fst (w q) $ c)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iq])
        have "set_lebesgue_integral (\<kappa> p') A
              (\<lambda>w :: 'n pairpath. fst (w ?S) $ c)
            - set_lebesgue_integral (\<kappa> p') A (\<lambda>w. fst (w q) $ c) = 0"
          using set_integral_diff(2)[OF s1 s2] zA by simp
        then show "set_lebesgue_integral (\<kappa> p') A
              (\<lambda>w :: 'n pairpath. fst (w (min q ?S)) $ c)
            = set_lebesgue_integral (\<kappa> p') A (\<lambda>w. fst (w (min ?S ?S)) $ c)"
          using q by simp
      qed
    qed
  qed
qed

subsection \<open>Clause (iv) for the conditional law\<close>

text \<open>The clause-(iv) twin of
  @{thm [source] pfut_rcd_X_increment_zero}.  Two differences, both
  bookkeeping: the \<open>P\<close>-side martingale is
  @{thm [source] paper_pair_class_pfut_comp_martingale}, which lives in the
  SHIFTED filtration and is therefore read at times \<open>i, j\<close> rather than
  \<open>r+i, r+j\<close> (the two agree, since \<open>?FP i = \<F>\<^sub>(\<^sub>r\<^sub>+\<^sub>i\<^sub>)\<close> for \<open>i \<le> T-r\<close>); and the
  component is a MATRIX entry, so the bounded-linear map is
  @{thm [source] bounded_linear_vec_nth} composed with itself.\<close>

lemma pfut_rcd_comp_increment_zero:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and i0: "0 \<le> i" and ij: "i \<le> j" and jS: "j \<le> T - r"
    and A': "A' \<in> sets (natural_filtration (borel_of (mtopology_of
        (path_metric (T - r) :: ('n pairpath) metric))) 0 (\<lambda>v w. w v) i)"
  shows "AE p' in pair_law_of r (pcut r) P.
      (\<integral>w. indicator A' w
        * ((outerp (fst (w j)) - snd (w j)
            - (outerp (fst (w i)) - snd (w i))) $ c $ d) \<partial>(\<kappa> p')) = 0"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  let ?Zf = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (pfut r T \<omega> (min u ?S)))
      - snd (pfut r T \<omega> (min u ?S))"
  let ?h = "\<lambda>w :: 'n pairpath. (outerp (fst (w j)) - snd (w j)
      - (outerp (fst (w i)) - snd (w i))) $ c $ d"
  have Tr: "0 \<le> ?S" using rT by simp
  have iS: "i \<le> ?S" using ij jS by simp
  have i0S: "i \<in> {0..?S}" using i0 iS by simp
  have j0S: "j \<in> {0..?S}" using i0 ij jS by simp
  have mi: "min i ?S = i" using iS by simp
  have mj: "min j ?S = j" using jS by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P ?FP 0 ?Zf by (rule mg)
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have A'Y: "A' \<in> sets ?Y"
    using A' sets_natural_filtration_path_subset[of ?S i] by blast

  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast

  \<comment> \<open>the integrand\<close>
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y" for u
    by (rule pair_law_eval_measurable[OF refl])
  have compm: "(\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))
      \<in> borel_measurable ?Y" for u
  proof -
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w u))) \<in> borel_measurable ?Y"
      by (rule measurable_compose
          [OF measurable_compose[OF ev measurable_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w u)) \<in> borel_measurable ?Y"
      by (rule measurable_compose[OF ev measurable_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed
  have entm: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
  have hm: "?h \<in> borel_measurable ?Y"
  proof -
    have "(\<lambda>w :: 'n pairpath. (outerp (fst (w j)) - snd (w j))
        - (outerp (fst (w i)) - snd (w i))) \<in> borel_measurable ?Y"
      by (rule borel_measurable_diff[OF compm compm])
    from measurable_compose[OF this entm] show ?thesis by simp
  qed

  \<comment> \<open>the shifted compensated process, and its integrability under \<open>P\<close>\<close>
  have hP: "(\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))
      = (\<lambda>\<omega>. (?Zf j \<omega> - ?Zf i \<omega>) $ c $ d)"
    by (rule ext) (simp add: mi mj)
  have hi: "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))"
    unfolding hP
    by (rule integrable_bounded_linear[OF bl
        Bochner_Integration.integrable_diff[OF Mg.integrable Mg.integrable]])
       (use i0 ij jS in simp_all)
  have hsnd: "integrable (ksemi ?Q ?Y \<kappa>) (\<lambda>p. ?h (snd p))"
  proof -
    have hm2: "(\<lambda>p :: ('n pairpath) \<times> ('n pairpath). ?h (snd p))
        \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
      by (rule measurable_compose[OF measurable_snd hm])
    have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) (\<lambda>p. ?h (snd p))"
      unfolding integrable_distr_eq[OF mphi' hm2] by (rule hi)
    then show ?thesis unfolding eq' .
  qed

  \<comment> \<open>the three hypotheses of @{thm [source] AE_kernel_integral_zero}\<close>
  have gi: "integrable (ksemi ?Q ?Y \<kappa>)
      (\<lambda>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p)))"
    if A: "A \<in> sets ?Q" for A
  proof (rule integrable_ksemi_of_distr_rect)
    show "ksemi ?Q ?Y \<kappa> = distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>" by (rule eq'[symmetric])
    show "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y" by (rule mphi')
    show "?h \<in> borel_measurable ?Y" by (rule hm)
    show "A \<in> sets ?Q" by (rule A)
    show "A' \<in> sets ?Y" by (rule A'Y)
    show "integrable P (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>)))" by (rule hi)
  qed
  have fi: "integrable ?Q (\<lambda>p'. \<integral>w. indicator A' w * ?h w \<partial>(\<kappa> p'))"
    by (rule integrable_kernel_integral[OF KQ neQ hm A'Y hsnd])
  have z: "(\<integral>p. indicator A (fst p) * (indicator A' (snd p) * ?h (snd p))
        \<partial>(ksemi ?Q ?Y \<kappa>)) = 0"
    if A: "A \<in> sets ?Q" for A
  proof -
    have AX: "A \<in> sets ?X" using A setsQ by simp
    have Sfilt: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets (?FP i)"
      using rect_vimage_natural_filtration[OF r rT setsP i0 iS AX A'] mi by simp
    have SP: "?\<phi> -` (A \<times> A') \<inter> space P \<in> sets P"
      using Mg.sets_F_subset[OF i0] Sfilt by blast
    have veq: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P) (?Zf i)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P) (?Zf j)"
      by (rule Mg.set_integral_eq[OF Sfilt i0 ij])
    have comp: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. ?Zf i \<omega> $ c $ d)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega>. ?Zf j \<omega> $ c $ d)"
      unfolding set_integral_mat_component[OF SP Mg.integrable[OF i0]]
        set_integral_mat_component[OF SP Mg.integrable[OF order_trans[OF i0 ij]]]
      using veq by simp
    have si: "set_integrable P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?Zf u \<omega> $ c $ d)" if u: "0 \<le> u" for u
    proof -
      have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?Zf u \<omega> $ c $ d)"
        by (rule integrable_bounded_linear[OF bl Mg.integrable[OF u]])
      then show ?thesis
        unfolding set_integrable_def by (rule integrable_mult_indicator[OF SP])
    qed
    have "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
          (\<lambda>\<omega> :: 'n pairpath. ?Zf j \<omega> $ c $ d - ?Zf i \<omega> $ c $ d)
        = set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. ?Zf j \<omega> $ c $ d)
          - set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
            (\<lambda>\<omega>. ?Zf i \<omega> $ c $ d)"
      by (rule set_integral_diff(2)[OF si[OF order_trans[OF i0 ij]] si[OF i0]])
    also have "\<dots> = 0" using comp by simp
    finally have zero: "set_lebesgue_integral P (?\<phi> -` (A \<times> A') \<inter> space P)
        (\<lambda>\<omega> :: 'n pairpath. ?h (snd (?\<phi> \<omega>))) = 0"
      unfolding hP by simp
    show ?thesis
      unfolding integral_ksemi_rect_of_set_integral
        [OF eq'[symmetric] mphi' hm A A'Y]
      using zero .
  qed
  show ?thesis by (rule AE_kernel_integral_zero[OF KQ neQ hm A'Y gi fi z])
qed

lemma pfut_rcd_comp_integrable:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
    and u: "u \<in> {0..T - r}"
  shows "AE p' in pair_law_of r (pcut r) P.
      integrable (\<kappa> p') (\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?FP = "\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v) (r + min u ?S)"
  let ?Zf = "\<lambda>u \<omega> :: 'n pairpath. outerp (fst (pfut r T \<omega> (min u ?S)))
      - snd (pfut r T \<omega> (min u ?S))"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath).
      outerp (fst (snd p u)) - snd (snd p u)"
  have u0: "0 \<le> u" using u by simp
  have mu: "min u ?S = u" using u by simp
  interpret PP: prob_space P by (rule PS)
  interpret Mg: martingale P ?FP 0 ?Zf by (rule mg)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast
  have SQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have eq': "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = ksemi ?Q ?Y \<kappa>"
  proof -
    have "distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi> = distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
      by (rule distr_cong[OF refl SQY]) simp
    then show ?thesis unfolding eq .
  qed
  have mphi': "?\<phi> \<in> P \<rightarrow>\<^sub>M ?Q \<Otimes>\<^sub>M ?Y"
    using mphi measurable_cong_sets[OF refl SQY[symmetric]] by blast
  have ev: "(\<lambda>w :: 'n pairpath. w u) \<in> borel_measurable ?Y"
    by (rule pair_law_eval_measurable[OF refl])
  have compm: "(\<lambda>w :: 'n pairpath. outerp (fst (w u)) - snd (w u))
      \<in> borel_measurable ?Y"
  proof -
    have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w u))) \<in> borel_measurable ?Y"
      by (rule measurable_compose
          [OF measurable_compose[OF ev measurable_fst_borel] outerp_borel])
    have m2: "(\<lambda>w :: 'n pairpath. snd (w u)) \<in> borel_measurable ?Y"
      by (rule measurable_compose[OF ev measurable_snd_borel])
    show ?thesis by (rule borel_measurable_diff[OF m1 m2])
  qed
  have gm: "?g \<in> borel_measurable (?Q \<Otimes>\<^sub>M ?Y)"
    by (rule measurable_compose[OF measurable_snd compm])
  have gP: "(\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>)) = ?Zf u"
    by (rule ext) (simp add: mu)
  have gi: "integrable (ksemi ?Q ?Y \<kappa>) ?g"
  proof -
    have "integrable P (\<lambda>\<omega> :: 'n pairpath. ?g (?\<phi> \<omega>))"
      unfolding gP by (rule Mg.integrable[OF u0])
    then have "integrable (distr P (?Q \<Otimes>\<^sub>M ?Y) ?\<phi>) ?g"
      unfolding integrable_distr_eq[OF mphi' gm] .
    then show ?thesis unfolding eq' .
  qed
  have "AE p' in ?Q. integrable (\<kappa> p') (\<lambda>w. ?g (p', w))"
    by (rule AE_integrable_ksemi_section[OF KQ gm gi neQ])
  then show ?thesis by simp
qed

text \<open>The two pointwise facts for the compensated entry, as for the
  coordinate.  Continuity is read off the expanded entry
  \<open>X\<^sub>t\<^sup>c X\<^sub>t\<^sup>d - Y\<^sub>t\<^sup>c\<^sup>d\<close> rather than through \<^const>\<open>outerp\<close>, which keeps everything
  inside products and differences of real continuous functions.\<close>

lemma comp_entry_measurable_nf:
  fixes Q :: "('n::finite pairpath) measure"
  assumes S: "0 \<le> S" and u: "0 \<le> u"
  shows "(\<lambda>w :: 'n pairpath.
        (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)
      \<in> borel_measurable (natural_filtration Q 0 (\<lambda>v w. w v) u)"
proof -
  let ?F = "natural_filtration Q 0 (\<lambda>v w :: 'n pairpath. w v) u"
  have ev: "(\<lambda>w :: 'n pairpath. w (min u S)) \<in> borel_measurable ?F"
    unfolding natural_filtration_def
    by (rule measurable_family_vimage_algebra) (use S u in auto)
  have m1: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u S))))
      \<in> borel_measurable ?F"
    by (rule measurable_compose
        [OF measurable_compose[OF ev measurable_fst_borel] outerp_borel])
  have m2: "(\<lambda>w :: 'n pairpath. snd (w (min u S))) \<in> borel_measurable ?F"
    by (rule measurable_compose[OF ev measurable_snd_borel])
  have mm: "(\<lambda>w :: 'n pairpath. outerp (fst (w (min u S))) - snd (w (min u S)))
      \<in> borel_measurable ?F"
    by (rule borel_measurable_diff[OF m1 m2])
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have entm: "(\<lambda>M :: real^'n^'n. M $ c $ d) \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (rule linear_continuous_on[OF bl])
  from measurable_compose[OF mm entm] show ?thesis by simp
qed

lemma comp_entry_continuous:
  fixes w :: "'n::finite pairpath"
  assumes w: "w \<in> mspace (path_metric S :: ('n pairpath) metric)"
  shows "continuous_on {0..S}
      (\<lambda>u. (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)"
proof -
  have cw: "continuous_on {0..S} w" by (rule mspace_path_metricD[OF w])
  have cf: "continuous_on {0..S} (\<lambda>u. fst (w u))"
    using cw by (rule continuous_on_fst)
  have cs: "continuous_on {0..S} (\<lambda>u. snd (w u))"
    using cw by (rule continuous_on_snd)
  have c1: "continuous_on {0..S} (\<lambda>u. fst (w u) $ c)"
    using cf by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have c2: "continuous_on {0..S} (\<lambda>u. fst (w u) $ d)"
    using cf by (rule bounded_linear.continuous_on[OF bounded_linear_vec_nth])
  have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
    by (rule bounded_linear_compose[OF bounded_linear_vec_nth
        bounded_linear_vec_nth])
  have c3: "continuous_on {0..S} (\<lambda>u. snd (w u) $ c $ d)"
    using cs by (rule bounded_linear.continuous_on[OF bl])
  have cc: "continuous_on {0..S}
      (\<lambda>u. fst (w u) $ c * fst (w u) $ d - snd (w u) $ c $ d)"
    by (intro continuous_on_diff continuous_on_mult c1 c2 c3)
  have "continuous_on {0..S}
        (\<lambda>u. (outerp (fst (w (min u S))) - snd (w (min u S))) $ c $ d)
      = continuous_on {0..S}
        (\<lambda>u. fst (w u) $ c * fst (w u) $ d - snd (w u) $ c $ d)"
    by (rule continuous_on_cong[OF refl]) (simp add: outerp_def)
  then show ?thesis using cc by simp
qed

text \<open>Clause (iv) of (1.7) for the conditional law, by the same assembly as
  clause (iii) --- only the index set of components is now a PAIR, and
  @{thm [source] martingale_matI} does the reassembly.\<close>

theorem pfut_rcd_comp_martingale:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (borel_of (mtopology_of
        (path_metric T :: ('n pairpath) metric)))"
    and PS: "prob_space P"
    and K: "\<kappa> \<in> borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
        \<rightarrow>\<^sub>M prob_algebra (borel_of (mtopology_of
            (path_metric (T - r) :: ('n pairpath) metric)))"
    and eq: "distr P
          (borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))
            \<Otimes>\<^sub>M borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric)))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            (borel_of (mtopology_of
              (path_metric (T - r) :: ('n pairpath) metric))) \<kappa>"
    and mg: "martingale P
        (\<lambda>u. natural_filtration P 0 (\<lambda>v \<omega>. \<omega> v) (r + min u (T - r))) 0
        (\<lambda>u \<omega>. outerp (fst (pfut r T \<omega> (min u (T - r))))
            - snd (pfut r T \<omega> (min u (T - r))))"
  shows "AE p' in pair_law_of r (pcut r) P.
      martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
        (\<lambda>u w. outerp (fst (w (min u (T - r)))) - snd (w (min u (T - r))))"
proof -
  let ?X = "borel_of (mtopology_of (path_metric r :: ('n pairpath) metric))"
  let ?S = "T - r"
  let ?Y = "borel_of (mtopology_of (path_metric ?S :: ('n pairpath) metric))"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?G = "\<lambda>q. natural_filtration ?Y 0 (\<lambda>v w :: 'n pairpath. w v) q"
  have Tr: "0 \<le> ?S" using rT by simp
  have SS: "?S \<in> {0..?S}" using Tr by simp
  interpret PP: prob_space P by (rule PS)
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF mcut])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K measurable_cong_sets[OF setsQ refl] by blast

  have exPi: "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    if q: "q \<in> {0..?S}" for q
  proof (rule countable_pi_system_natural_filtration_path
      [where Q = ?Y and T = ?S and s = q])
    show "sets ?Y = sets (borel_of (mtopology_of
        (path_metric ?S :: ('n pairpath) metric)))" ..
    show "0 \<le> q" using q by simp
    show "q \<le> ?S" using q by simp
    fix E assume "countable E" "Int_stable E" "E \<subseteq> Pow (space ?Y)"
      "space ?Y \<in> E" "sets (?G q) = sigma_sets (space ?Y) E"
    then show "\<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
        \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
      by (intro exI[of _ E] conjI)
  qed
  have "\<forall>q \<in> {0..?S}. \<exists>E. countable E \<and> Int_stable E \<and> E \<subseteq> Pow (space ?Y)
      \<and> space ?Y \<in> E \<and> sets (?G q) = sigma_sets (space ?Y) E"
    using exPi by blast
  from bchoice[OF this] obtain Eg where
    Espec0: "\<forall>q \<in> {0..?S}. countable (Eg q) \<and> Int_stable (Eg q)
        \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
        \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    by (rule exE)
  have Espec: "countable (Eg q) \<and> Int_stable (Eg q)
      \<and> Eg q \<subseteq> Pow (space ?Y) \<and> space ?Y \<in> Eg q
      \<and> sets (?G q) = sigma_sets (space ?Y) (Eg q)"
    if q: "q \<in> {0..?S}" for q by (rule bspec[OF Espec0 q])

  have step: "AE p' in ?Q. (\<integral>w. indicator A' w
      * ((outerp (fst (w ?S)) - snd (w ?S)
          - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
    if q: "q \<in> {0..?S}" and A': "A' \<in> sets (?G q)" for q A' and c d :: 'n
    by (rule pfut_rcd_comp_increment_zero
        [OF r rT setsP PS K eq mg _ _ _ A']) (use q in auto)
  have zero_all: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
        (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
            - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume qrat: "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow>
        (\<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
          (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
              - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0)"
    proof (cases "q \<in> {0..?S}")
      case True
      have cEg: "countable (Eg q)" using Espec[OF True] by blast
      have "AE p' in ?Q. \<forall>A' \<in> Eg q. \<forall>c \<in> (UNIV :: 'n set).
          \<forall>d \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
      proof (rule AE_ball_countable'[OF _ cEg])
        fix A' assume A': "A' \<in> Eg q"
        have AG: "A' \<in> sets (?G q)" using A' Espec[OF True] by auto
        show "AE p' in ?Q. \<forall>c \<in> (UNIV :: 'n set). \<forall>d \<in> (UNIV :: 'n set).
            (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
        proof (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
          fix c :: 'n assume "c \<in> (UNIV :: 'n set)"
          show "AE p' in ?Q. \<forall>d \<in> (UNIV :: 'n set).
              (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
                  - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
            by (rule AE_ball_countable'[OF _ countable_finite[OF finite]])
               (use step[OF True AG] in blast)
        qed
      qed
      then show ?thesis by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have rat_int: "AE p' in ?Q. \<forall>q \<in> (\<rat> :: real set). q \<in> {0..?S} \<longrightarrow>
      integrable (\<kappa> p')
        (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix q :: real assume "q \<in> \<rat>"
    show "AE p' in ?Q. q \<in> {0..?S} \<longrightarrow> integrable (\<kappa> p')
        (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
    proof (cases "q \<in> {0..?S}")
      case True
      show ?thesis
        using pfut_rcd_comp_integrable[OF r rT setsP PS K eq mg True]
        by (rule eventually_mono) simp
    next
      case False
      then show ?thesis by auto
    qed
  qed
  have S_int: "AE p' in ?Q. integrable (\<kappa> p')
      (\<lambda>w :: 'n pairpath. outerp (fst (w ?S)) - snd (w ?S))"
    by (rule pfut_rcd_comp_integrable[OF r rT setsP PS K eq mg SS])

  from AE_space zero_all rat_int S_int show ?thesis
  proof eventually_elim
    case (elim p')
    then have W: "p' \<in> space ?Q"
      and Z0: "\<And>q A' c d. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> A' \<in> Eg q \<Longrightarrow>
          (\<integral>w. indicator A' w * ((outerp (fst (w ?S)) - snd (w ?S)
              - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p')) = 0"
      and RI: "\<And>q. q \<in> \<rat> \<Longrightarrow> q \<in> {0..?S} \<Longrightarrow> integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. outerp (fst (w q)) - snd (w q))"
      and SI: "integrable (\<kappa> p')
          (\<lambda>w :: 'n pairpath. outerp (fst (w ?S)) - snd (w ?S))" by blast+
    have PK: "prob_space (\<kappa> p')" by (rule ksemi_sets_kernel(2)[OF KQ W])
    have sK: "sets (\<kappa> p') = sets ?Y" by (rule ksemi_sets_kernel(1)[OF KQ W])
    have spK: "space (\<kappa> p') = space ?Y" by (rule sets_eq_imp_space_eq[OF sK])
    have nfK: "natural_filtration (\<kappa> p') 0 (\<lambda>v w :: 'n pairpath. w v) u = ?G u"
      for u by (rule natural_filtration_cong_space[OF spK])
    have spY: "space ?Y = mspace (path_metric ?S :: ('n pairpath) metric)"
      by (simp add: space_borel_of)

    show ?case
    proof (rule martingale_matI)
      fix c d :: 'n
      have bl: "bounded_linear (\<lambda>M :: real^'n^'n. M $ c $ d)"
        by (rule bounded_linear_compose[OF bounded_linear_vec_nth
            bounded_linear_vec_nth])
      show "martingale (\<kappa> p') (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v)) 0
          (\<lambda>u w. (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)"
      proof (rule martingale_of_rational_set_integral_eq[OF Tr sK PK])
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "u \<in> {0..?S}" for u
          by (rule comp_entry_measurable_nf[OF Tr]) (use that in simp)
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            \<in> borel_measurable (natural_filtration (\<kappa> p') 0 (\<lambda>v w. w v) u)"
          if "0 \<le> u" for u by (rule comp_entry_measurable_nf[OF Tr that])
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min q ?S))) - snd (w (min q ?S))) $ c $ d)"
          if q: "q \<in> \<rat>" "q \<in> {0..?S}" for q
        proof -
          have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w q)) - snd (w q)) $ c $ d)"
            by (rule integrable_bounded_linear[OF bl RI[OF q]])
          moreover have "min q ?S = q" using q by simp
          ultimately show ?thesis by simp
        qed
        show "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
        proof -
          have "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
              (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
            by (rule integrable_bounded_linear[OF bl SI])
          then show ?thesis by simp
        qed
        show "continuous_on {0..?S}
            (\<lambda>u. (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)"
          if "w \<in> space (\<kappa> p')" for w :: "'n pairpath"
          using that spK spY by (intro comp_entry_continuous) simp
        show "(\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min u ?S))) - snd (w (min u ?S))) $ c $ d)
            = (\<lambda>w. (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
          if "?S \<le> u" for u using that by simp
        fix q :: real and A
        assume qrat: "q \<in> \<rat>" and q: "q \<in> {0..?S}"
          and A: "A \<in> sets (natural_filtration (\<kappa> p') 0
              (\<lambda>v w :: 'n pairpath. w v) q)"
        have AG: "A \<in> sets (?G q)" using A nfK by simp
        have EgS: "countable (Eg q)" "Int_stable (Eg q)"
          "Eg q \<subseteq> Pow (space ?Y)" "space ?Y \<in> Eg q"
          "sets (?G q) = sigma_sets (space ?Y) (Eg q)"
          using Espec[OF q] by blast+
        have subG: "subalgebra (\<kappa> p') (?G q)"
          using subalgebra_natural_filtration_path[OF sK, of q] nfK by simp
        have iq: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl RI[OF qrat q]])
        have iS: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
          by (rule integrable_bounded_linear[OF bl SI])
        have gi: "integrable (\<kappa> p') (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          by (rule Bochner_Integration.integrable_diff[OF iS iq])
        have gz: "set_lebesgue_integral (\<kappa> p') B (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          if B: "B \<in> Eg q" for B
        proof -
          have "set_lebesgue_integral (\<kappa> p') B (\<lambda>w :: 'n pairpath.
                (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
                - (outerp (fst (w q)) - snd (w q)) $ c $ d)
              = (\<integral>w. indicator B w * ((outerp (fst (w ?S)) - snd (w ?S)
                  - (outerp (fst (w q)) - snd (w q))) $ c $ d) \<partial>(\<kappa> p'))"
            unfolding set_lebesgue_integral_def by simp
          also have "\<dots> = 0" by (rule Z0[OF qrat q B])
          finally show ?thesis .
        qed
        have zA: "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d
            - (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          by (rule set_integral_zero_of_generator
              [OF subG gi EgS(2) _ _ _ gz AG])
             (use EgS(3) EgS(4) EgS(5) spK in simp_all)
        have AQ: "A \<in> sets (\<kappa> p')" using AG subG by (auto simp: subalgebra_def)
        have s1: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iS])
        have s2: "set_integrable (\<kappa> p') A (\<lambda>w :: 'n pairpath.
            (outerp (fst (w q)) - snd (w q)) $ c $ d)"
          unfolding set_integrable_def
          by (rule integrable_mult_indicator[OF AQ iq])
        have "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
              (outerp (fst (w ?S)) - snd (w ?S)) $ c $ d)
            - set_lebesgue_integral (\<kappa> p') A (\<lambda>w.
              (outerp (fst (w q)) - snd (w q)) $ c $ d) = 0"
          using set_integral_diff(2)[OF s1 s2] zA by simp
        then show "set_lebesgue_integral (\<kappa> p') A (\<lambda>w :: 'n pairpath.
              (outerp (fst (w (min q ?S))) - snd (w (min q ?S))) $ c $ d)
            = set_lebesgue_integral (\<kappa> p') A (\<lambda>w.
              (outerp (fst (w (min ?S ?S))) - snd (w (min ?S ?S))) $ c $ d)"
          using q by simp
      qed
    qed
  qed
qed

end
