section \<open>The pasting bound\<close>
(*<*)
theory Dynamic_Programming_Pasting
  imports Exit_Class_Optimizer "Continuous_Path_Spaces.Conditional_UI" "Disintegration.Disintegration"
    "Continuous_Time_Martingales.Natural_Filtration"
begin

(*>*)
text \<open>The dynamic programming principle of Proposition 2.4 of
  \<^cite>\<open>LaiShkolnikovSoner\<close>, for the value function: the pasting bound, the
  \<open>\<ge>\<close> half of (2.9) at a deterministic time, the reduction of the
  \<open>\<le>\<close> half to a single conditioning statement, and the conditioning
  theory it rests on.\<close>

section \<open>The pasting bound for the dynamic programming principle\<close>

text \<open>The kernel analogue of @{thm [source] exit_val_paste_ge}: an
  almost-sure lower bound on the exit time of the kernel glue is a lower
  bound for @{term exit_val}, turning @{thm [source]
  exit_class_kglue_law'} into an inequality about the value
  function.\<close>

theorem exit_val_kpaste_ge:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
    and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and T0: "0 < T" and L1: "1 \<le> L"
    and K: "closed K"
    and Q: "Q \<in> exit_class k L r x"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and Kb: "Kr \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
            (exit_class k L (T - r) (0::real^'n))
            (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
              (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and Kc: "\<And>\<omega>. Kr \<omega> \<in> exit_class k L (T - r) 0"
    and stay: "AE p in ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr.
        c \<le> pexit T K (\<lambda>t. fst (pglue r T (fst p) (snd p) t))"
  shows "ennreal c \<le> exit_val k L T K x"
proof -
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?BT = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?MR Kr"
  have T0': "0 \<le> T" using T0 by simp
  have rT': "r \<le> T" using rT by simp
  have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF Q])
  have G: "kglue_law' r T Kr Q \<in> exit_class k L T x"
    by (rule exit_class_kglue_law'[OF r rT L1 T0 Q Kp Kb Kc])
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
  also have "\<dots> \<le> exit_val k L T K x"
    unfolding exit_val_def using G by (intro Sup_upper imageI)
  finally show ?thesis .
qed

subsection \<open>The pathwise form of the dynamic programming bound\<close>

text \<open>A strict variant of @{thm [source] pexit_pglue_split}: the
  continuation only has to stay in \<open>K\<close> on the half-open interval
  \<open>{0..<c}\<close>, matching what the essential infimum supplies, since
  \<open>c \<le> pexit\<close> says nothing about the path at time \<open>c\<close>.\<close>

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
  first piece's exit time is a lower bound in all cases (@{thm [source]
  pexit_pglue_ge}), and when it has not exited by \<open>r\<close> --- exactly
  \<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close> --- the continuation adds its own
  survival time on top.\<close>

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

subsection \<open>The selector as a kernel into the class\<close>

text \<open>\<open>exit_val_measurable_selector_kernel'\<close> below makes the selector
  a Giry-monad kernel, hypothesis \<^emph>\<open>Kp\<close> of @{thm [source]
  exit_class_kglue_law'}.  The other hypothesis, \<^emph>\<open>Kb\<close>
  (measurability into the class with its Levy-Prokhorov metric), is free:
  the selector lands in the subspace, and @{thm [source]
  exit_class_compact_metric_space} identifies the class's metric
  topology with the subspace topology of weak convergence.\<close>

theorem exit_val_measurable_selector_kernel':
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains S where
    "S \<in> borel \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (exit_class k L T (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
          (mdist (path_metric T :: ('n pairpath) metric))))"
    and "\<And>y. S y \<in> exit_class k L T 0"
    and "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K y"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?P = "{N :: ('n pairpath) measure. prob_space N
      \<and> sets N = sets (path_borel T :: ('n pairpath) measure)}"
  let ?C = "exit_class k L T (0::real^'n)"
  obtain S where Sm: "S \<in> borel \<rightarrow>\<^sub>M borel_of ?W"
    and SC: "\<And>y. S y \<in> exit_class k L T 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K y"
    by (rule exit_val_measurable_selector[where k = k, OF T L K]) blast
  have SP: "S y \<in> ?P" for y
    using exit_class_prob[OF SC] exit_class_sets[OF SC] by simp
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
      using L by (intro exit_class_compact_metric_space(2)[OF T]) simp
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
    show "S y \<in> exit_class k L T 0" for y by (rule SC)
    show "ess_inf_time (pshift_law T y (S y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        = exit_val k L T K y" for y by (rule Sval)
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

lemma exit_class_start:
  fixes Q :: "('n::finite pairpath) measure"
  assumes Q: "Q \<in> exit_class k L T x"
  shows "AE \<omega> in Q. fst (\<omega> 0) = x \<and> snd (\<omega> 0) = 0"
  using Q unfolding exit_class_def by blast

subsection \<open>The value function is Borel measurable\<close>

text \<open>Clause (1) --- upper semicontinuity --- makes every sublevel set
  \<open>{y. v y < b}\<close> open, and the horizon bound makes \<open>v\<close> finite, so the real
  version \<open>enn2real \<circ> v\<close> is Borel measurable, as needed to state the
  dynamic programming principle's integrand as a random variable.\<close>

lemma exit_val_open_less:
  fixes K :: "(real^'n::finite) set" and b :: ennreal
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  shows "open {y :: real^'n. exit_val k L T K y < b}"
proof (subst open_subopen, safe)
  fix y :: "real^'n" assume "exit_val k L T K y < b"
  then have "eventually (\<lambda>z. exit_val k L T K z < b) (nhds y)"
    by (rule exit_val_usc_unconditional[OF T L K])
  then obtain U where "open U" "y \<in> U" "\<forall>z\<in>U. exit_val k L T K z < b"
    unfolding eventually_nhds by blast
  then show "\<exists>U. open U \<and> y \<in> U \<and> U \<subseteq> {y. exit_val k L T K y < b}" by blast
qed

lemma exit_val_neq_top:
  fixes K :: "(real^'n::finite) set" and y :: "real^'n"
  assumes T: "0 \<le> T"
  shows "exit_val k L T K y \<noteq> \<top>"
proof -
  have "exit_val k L T K y \<le> ennreal T" by (rule exit_val_le_T[OF T])
  moreover have "(ennreal T :: ennreal) \<noteq> \<top>" by simp
  ultimately show ?thesis by (auto simp: top_unique)
qed

lemma exit_val_borel_measurable:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  shows "(\<lambda>y :: real^'n. enn2real (exit_val k L T K y)) \<in> borel_measurable borel"
proof (subst borel_measurable_iff_less, intro allI)
  fix a :: real
  show "{w \<in> space (borel :: (real^'n) measure).
      enn2real (exit_val k L T K w) < a} \<in> sets (borel :: (real^'n) measure)"
  proof (cases "0 < a")
    case True
    have key: "(enn2real (exit_val k L T K y) < a)
        = (exit_val k L T K y < ennreal a)" for y :: "real^'n"
    proof -
      have fin: "exit_val k L T K y < \<top>"
        using exit_val_neq_top[of T k L K y] T by (simp add: less_top)
      have "(exit_val k L T K y < ennreal a)
          = (ennreal (enn2real (exit_val k L T K y)) < ennreal a)"
        by (simp add: ennreal_enn2real[OF fin])
      also have "\<dots> = (enn2real (exit_val k L T K y) < a)"
        using True by (simp add: ennreal_less_iff)
      finally show ?thesis ..
    qed
    have "{w \<in> space (borel :: (real^'n) measure).
        enn2real (exit_val k L T K w) < a}
        = {y :: real^'n. exit_val k L T K y < ennreal a}"
      by (simp add: key)
    then show ?thesis
      using exit_val_open_less[OF T L K, of k "ennreal a"] by simp
  next
    case False
    have "{w \<in> space (borel :: (real^'n) measure).
        enn2real (exit_val k L T K w) < a} = {}"
    proof (rule equals0I)
      fix w assume "w \<in> {w \<in> space (borel :: (real^'n) measure).
          enn2real (exit_val k L T K w) < a}"
      then have "enn2real (exit_val k L T K w) < a" by simp
      moreover have "0 \<le> enn2real (exit_val k L T K w)" by simp
      ultimately show False using False by simp
    qed
    then show ?thesis by simp
  qed
qed

subsection \<open>The \<open>\<ge>\<close> half of the dynamic programming principle (2.9)\<close>

text \<open>Proposition 2.4 of \<^cite>\<open>LaiShkolnikovSoner\<close> states the dynamic programming
  principle
    \<open>v x = (SUP P \<in> exit_class k L T x. P-ess-inf
      (\<theta> \<and> \<tau>\<^sub>K + v (X \<theta>) * 1\<^sub>{\<theta> \<le> \<tau>\<^sub>K}))\<close>.
  This is its \<open>\<ge>\<close> half at a deterministic time \<open>\<theta> = r\<close>.  Both summands are
  read off the first piece: \<open>\<theta> \<and> \<tau>_K\<close> is the exit time capped at \<open>r\<close>, i.e.
  \<open>pexit r K\<close>, and \<open>1\<^sub>{\<theta> \<le> \<tau>_K}\<close> is \<open>pexit r K \<dots> = r \<and> fst (\<omega> r) \<in> K\<close>.

  The proof restricts \<open>P\<close> to \<open>[0,r]\<close>, continues from the endpoint with the
  law the measurable selector picks there, and pastes: the pasted law is in
  the class by @{thm [source] exit_class_kglue_law'}, its exit time
  dominates the DPP integrand pathwise by @{thm [source] pexit_pglue_dpp},
  and @{thm [source] exit_val_kpaste_ge} turns that into a bound on
  \<open>v(x)\<close>.\<close>

theorem exit_val_dpp_ge_const:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and P: "P \<in> exit_class k L T x"
    and c: "AE \<omega> in P. c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)"
  shows "ennreal c \<le> exit_val k L T K x"
proof -
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?BT = "(path_borel T :: ('n pairpath) measure)"
  let ?BR = "(path_borel r :: ('n pairpath) measure)"
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
        (exit_class k L (T - r) (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
          (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and SC: "\<And>y. S y \<in> exit_class k L (T - r) 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law (T - r) y (S y))
        (\<lambda>\<omega>. pexit (T - r) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - r) K y"
    by (rule exit_val_measurable_selector_kernel'[where k = k, OF Tr L1 K]) blast

  \<comment> \<open>the restriction of \<^term>\<open>P\<close> to \<open>[0,r]\<close>, and the kernel it feeds\<close>
  define Q where "Q = pair_law_of r (pcut r) P"
  have QC: "Q \<in> exit_class k L r x"
    unfolding Q_def by (rule exit_class_pcut[OF r rT' P])
  have setsQ: "sets Q = sets ?BR" by (rule exit_class_sets[OF QC])
  interpret PQ: prob_space Q by (rule exit_class_prob[OF QC])
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
          (exit_class k L (T - r) (0::real^'n))
          (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
            (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    unfolding Kr_def by (rule measurable_compose[OF eF Ssub])
  have Kc: "Kr \<omega> \<in> exit_class k L (T - r) 0" for \<omega>
    unfolding Kr_def by (rule SC)

  \<comment> \<open>the integrand of (2.9) is a random variable, and only reads \<open>[0,r]\<close>\<close>
  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)" for \<omega>
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t))) \<in> borel_measurable ?BR"
    by (rule pexit_path_measurable[OF r K refl])
  have endm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF refl] mfst])
  have vm: "(\<lambda>\<omega> :: 'n pairpath. enn2real (exit_val k L (T - r) K (fst (\<omega> r))))
      \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF endm exit_val_borel_measurable[OF Tr L1 K]])
  have predm: "Measurable.pred ?BR (\<lambda>\<omega> :: 'n pairpath.
      pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K)"
    using taum endm Kbor by measurable
  have gm: "g \<in> borel_measurable ?BR"
    unfolding g_def using taum vm predm by measurable
  have gset: "{\<omega> \<in> space ?BR. c \<le> g \<omega>} \<in> sets ?BR" using gm by measurable
  have gcut: "g (pcut r \<omega>) = g \<omega>" for \<omega> :: "'n pairpath"
    using r by (simp add: g_def pexit_pcut pcut_apply)
  have pcm: "pcut r \<in> P \<rightarrow>\<^sub>M ?BR"
    by (rule pcut_measurable[OF r rT' exit_class_sets[OF P]])
  have cg: "AE \<omega> in P. c \<le> g \<omega>" using c unfolding g_def .
  have AEQ: "AE \<omega> in Q. c \<le> g \<omega>"
    using cg unfolding Q_def pair_law_of_def AE_distr_iff[OF pcm gset] gcut .

  \<comment> \<open>the selector's optimality, transported to the glued path\<close>
  have inner: "AE \<omega>' in Kr \<omega>. c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
    if gw: "c \<le> g \<omega>" for \<omega> :: "'n pairpath"
  proof -
    define v where "v = enn2real (exit_val k L (T - r) K (fst (\<omega> r)))"
    have vnn: "0 \<le> v" by (simp add: v_def)
    have vfin: "exit_val k L (T - r) K (fst (\<omega> r)) < \<top>"
      using exit_val_neq_top[of "T - r" k L K "fst (\<omega> r)"] Tr' by (simp add: less_top)
    have veq: "ennreal v = exit_val k L (T - r) K (fst (\<omega> r))"
      unfolding v_def by (rule ennreal_enn2real[OF vfin])
    have vle: "v \<le> T - r"
    proof -
      have "ennreal v \<le> ennreal (T - r)"
        unfolding veq by (rule exit_val_le_T[OF Tr'])
      then show ?thesis using Tr' by simp
    qed
    have gw': "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then v else 0)"
      using gw unfolding g_def v_def .
    have Kcw: "Kr \<omega> \<in> exit_class k L (T - r) 0" by (rule Kc)
    have z0: "AE \<omega>' in Kr \<omega>. fst (\<omega>' 0) = 0"
      using exit_class_start[OF Kcw] by (auto elim: eventually_mono)
    have opt: "AE \<omega>' in Kr \<omega>. v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
    proof -
      have ae1: "AE w in pshift_law (T - r) (fst (\<omega> r)) (S (fst (\<omega> r))).
          exit_val k L (T - r) K (fst (\<omega> r))
            \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (w t)))"
        unfolding Sval[symmetric] by (rule ess_inf_time_AE)
      have setsSy: "sets (S (fst (\<omega> r))) = sets ?MR"
        by (rule exit_class_sets[OF SC])
      have shm: "pshift (T - r) (fst (\<omega> r)) \<in> S (fst (\<omega> r)) \<rightarrow>\<^sub>M ?MR"
        using pshift_measurable[OF Tr'] measurable_cong_sets[OF setsSy refl] by blast
      have m1: "(\<lambda>w :: 'n pairpath. ennreal (pexit (T - r) K (\<lambda>t. fst (w t))))
          \<in> borel_measurable ?MR"
        using pexit_path_measurable[OF Tr' K refl] by measurable
      have mset: "{w \<in> space ?MR. exit_val k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (w t)))} \<in> sets ?MR"
        using m1 by measurable
      have ae2: "AE \<omega>' in S (fst (\<omega> r)). exit_val k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (pshift (T - r) (fst (\<omega> r)) \<omega>' t)))"
        using ae1 unfolding pshift_law_def AE_distr_iff[OF shm mset] .
      have ae3: "AE \<omega>' in S (fst (\<omega> r)). exit_val k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
        using ae2 by (simp add: pexit_pshift)
      have ae4: "AE \<omega>' in S (fst (\<omega> r)).
          v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
      proof (rule eventually_mono[OF ae3])
        fix \<omega>' :: "'n pairpath"
        assume "exit_val k L (T - r) K (fst (\<omega> r))
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
    by (rule exit_val_kpaste_ge[OF r rT T0 L1 K QC Kp Kb Kc stay])
qed

text \<open>The essential infimum form: the DPP integrand is bounded by \<open>T\<close>, so
  its essential infimum is finite, and @{thm [source] ess_inf_time_AE} turns
  it into an almost-sure bound with a real constant.\<close>

theorem exit_val_dpp_ge:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and P: "P \<in> exit_class k L T x"
  shows "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      \<le> exit_val k L T K x"
proof -
  have Tr': "0 \<le> T - r" using rT by simp
  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)" for \<omega>
  have geta: "g = (\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
    by (rule ext) (simp add: g_def)
  have vbnd: "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
      then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0) \<le> T - r"
    for \<omega> :: "'n pairpath"
  proof (cases "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K")
    case True
    have "ennreal (enn2real (exit_val k L (T - r) K (fst (\<omega> r))))
        = exit_val k L (T - r) K (fst (\<omega> r))"
      using exit_val_neq_top[of "T - r" k L K "fst (\<omega> r)"] Tr'
      by (simp add: less_top)
    also have "\<dots> \<le> ennreal (T - r)" by (rule exit_val_le_T[OF Tr'])
    finally have "enn2real (exit_val k L (T - r) K (fst (\<omega> r))) \<le> T - r"
      using Tr' by simp
    then show ?thesis using True by simp
  next
    case False
    then have "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
        then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0) = 0"
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
  have PP: "prob_space P" by (rule exit_class_prob[OF P])
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
         then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)"
    using aec0 unfolding g_def .
  have main: "ennreal c \<le> exit_val k L T K x"
    by (rule exit_val_dpp_ge_const[OF r rT L1 K P aec])
  have "ess_inf_time P (\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)) = ennreal c"
    using ceq geta by simp
  then show ?thesis using main by simp
qed

text \<open>Hence the \<open>\<ge>\<close> half of (2.9) itself, at a deterministic time.\<close>

corollary exit_val_dpp_sup_ge:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
  shows "(SUP P \<in> exit_class k L T x. ess_inf_time P
            (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
              + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
                 then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))
      \<le> exit_val k L T K x"
proof (rule SUP_least)
  fix P :: "('n pairpath) measure"
  assume "P \<in> exit_class k L T x"
  then show "ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
         then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
      \<le> exit_val k L T K x"
    by (rule exit_val_dpp_ge[OF r rT L1 K])
qed

subsection \<open>The \<open>\<le>\<close> half of (2.9), reduced to conditioning\<close>

text \<open>Off the survival event the horizon cap at \<open>r\<close> is invisible: a path
  that has already left \<open>K\<close> by time \<open>r\<close> has the same exit time whichever
  horizon it is measured against.  The event
  \<open>\<not> (pexit r K f = r \<and> f r \<in> K)\<close> is genuinely weaker than
  \<open>pexit r K f < r\<close>, since a path may exit exactly at \<open>r\<close>, a case
  @{thm [source] pexit_stable_above_T} does not cover.\<close>

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

text \<open>Hence the \<open>\<le>\<close> half of (2.9) reduces to a single statement about
  conditioning, and no other property of the class is needed:

  \<open>\begin{quote}\<close>
  if the exit time of \<open>P \<in> \<P>\<^sub>x\<close> is almost surely at least \<open>c\<close>, then almost
  surely on the survival event \<open>{r \<le> \<tau>\<^sub>K}\<close> the value at the position reached
  is at least the time still to run, \<open>c - r\<close>.
  \<open>\end{quote}\<close>

  That is exactly the statement that the conditional law of the future given
  \<open>\<F>\<^sub>r\<close> is, almost surely, a member of the class started at \<open>X\<^sub>r\<close>, so that its
  own essential infimum is bounded by \<open>v(X\<^sub>r)\<close>; it is a regular conditional
  distribution argument.  Off the survival event it is unconditional, by
  @{thm [source] pexit_cap_eq}.\<close>

theorem exit_val_dpp_le_of_cond:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and cond: "\<And>P c. P \<in> exit_class k L T x \<Longrightarrow>
        (AE \<omega> in P. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))) \<Longrightarrow>
        (AE \<omega> in P. pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
            \<longrightarrow> c \<le> r + enn2real (exit_val k L (T - r) K (fst (\<omega> r))))"
  shows "exit_val k L T K x
      \<le> (SUP P \<in> exit_class k L T x. ess_inf_time P
          (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))"
proof -
  have rT': "r \<le> T" using rT by simp
  have T0': "0 \<le> T" using r rT by simp
  have key: "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
    if P: "P \<in> exit_class k L T x" for P :: "('n pairpath) measure"
  proof -
    have PP: "prob_space P" by (rule exit_class_prob[OF P])
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
        \<longrightarrow> c \<le> r + enn2real (exit_val k L (T - r) K (fst (\<omega> r)))"
      by (rule cond[OF P aeT])
    have aeg: "AE \<omega> in P. c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)"
    proof (rule eventually_mono[OF eventually_conj[OF aeT aeS]])
      fix \<omega> :: "'n pairpath"
      assume h: "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))
          \<and> (pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             \<longrightarrow> c \<le> r + enn2real (exit_val k L (T - r) K (fst (\<omega> r))))"
      show "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)"
      proof (cases "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K")
        case True
        then have "pexit r K (\<lambda>t. fst (\<omega> t)) = r" by simp
        moreover have "c \<le> r + enn2real (exit_val k L (T - r) K (fst (\<omega> r)))"
          using h True by simp
        ultimately show ?thesis using True by simp
      next
        case False
        have eq: "pexit T K (\<lambda>t. fst (\<omega> t)) = pexit r K (\<lambda>t. fst (\<omega> t))"
          by (rule pexit_cap_eq[OF r rT' False])
        have z: "(if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
            then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0) = 0"
          using False by (rule if_not_P)
        show ?thesis using h eq z by simp
      qed
    qed
    have aeE: "AE \<omega> in P. ennreal c \<le> ennreal (pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
    proof (rule eventually_mono[OF aeg])
      fix \<omega> :: "'n pairpath"
      assume "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)"
      then show "ennreal c \<le> ennreal (pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
        by (rule ennreal_leI)
    qed
    have "ennreal c \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
      by (rule ess_inf_timeI[OF aeE])
    then show ?thesis unfolding ceq .
  qed
  have pv: "exit_val k L T K x = (SUP Q \<in> exit_class k L T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))"
    unfolding exit_val_def ..
  show ?thesis
    unfolding pv
  proof (rule SUP_least)
    fix P :: "('n pairpath) measure"
    assume P: "P \<in> exit_class k L T x"
    have "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> ess_inf_time P (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))"
      by (rule key[OF P])
    also have "\<dots> \<le> (SUP Q \<in> exit_class k L T x. ess_inf_time Q
        (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))"
      using P by (rule SUP_upper)
    finally show "ess_inf_time P (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
        \<le> (SUP Q \<in> exit_class k L T x. ess_inf_time Q
            (\<lambda>\<omega>. pexit r K (\<lambda>t. fst (\<omega> t))
              + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
                 then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)))" .
  qed
qed

text \<open>Both halves together: Eq. (2.9) at a deterministic time, modulo the
  conditioning statement isolated above.\<close>


(*<*)
end
(*>*)
