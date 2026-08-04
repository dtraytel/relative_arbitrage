(*
  Title:   Exit_Semicontinuity.thy
  Content: The value-side semicontinuity underlying Prop 2.4 of
           arXiv:2512.17702, following LR (arXiv:2003.13611) Lemma 2.1:
           the capped exit time is upper semicontinuous on the path
           space, and the essential infimum of the exit time is upper
           semicontinuous along weak convergence of path laws, via the
           Laplace-transform representation
           essinf tau = inf_{lambda>0} -(1/lambda) log E[exp(-lambda tau)].
*)

theory Exit_Semicontinuity
  imports Path_Space Exit_Time Value_Function
begin

section \<open>The path-space exit time\<close>

text \<open>The capped exit time from \<open>K\<close>, read off a PATH rather than a sample
  point: the composition of \<open>etime\<close> with the identity process.  All laws in
  the paper's class share the same sample space — the path space — and the
  same exit functional; this is the object whose essential infimum the value
  function (1.6) takes.\<close>

definition pexit :: "real \<Rightarrow> ('b :: polish_space) set \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> real"
  where "pexit T K f = etime T (- K) (\<lambda>r g. g r) f"

lemma pexit_le_T: "0 \<le> T \<Longrightarrow> pexit T K f \<le> T"
  unfolding pexit_def by (rule etime_le_T)

lemma pexit_nonneg: "0 \<le> T \<Longrightarrow> 0 \<le> pexit T K f"
  unfolding pexit_def by (rule etime_nonneg)

lemma pexit_less_iff:
  "0 \<le> T \<Longrightarrow> pexit T K f < c
    \<longleftrightarrow> ((\<exists>r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K \<and> r < c) \<or> T < c)"
  unfolding pexit_def by (rule etime_less_iff)

text \<open>Upper semicontinuity, in sublevel-set form: strict sublevels of the
  exit time are open in the path topology.  A path that exits before \<open>c\<close>
  does so at a time where it sits in the OPEN complement of \<open>K\<close>, and
  evaluation at that time is continuous.\<close>

lemma pexit_sublevel_open:
  fixes K :: "('b :: polish_space) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "openin (mtopology_of (path_metric T))
      {f \<in> mspace (path_metric T). pexit T K f < c}"
proof (cases "T < c")
  case True
  then have "{f \<in> mspace (path_metric T). pexit T K f < c}
      = mspace (path_metric T)"
    using pexit_le_T[OF T] by (auto intro: le_less_trans)
  then show ?thesis
    by (metis openin_topspace topspace_mtopology_of)
next
  case False
  have ev: "openin (mtopology_of (path_metric T))
      {f \<in> mspace (path_metric T). f r \<notin> K}" if r: "r \<in> {0..T}" for r
  proof -
    have cm: "continuous_map (mtopology_of (path_metric T)) euclidean
        (\<lambda>f :: real \<Rightarrow> 'b. f r)"
      by (rule continuous_map_path_eval[OF r])
    have op: "openin euclidean (- K)"
      using K by (metis open_Compl open_openin)
    have "openin (mtopology_of (path_metric T))
        {f \<in> topspace (mtopology_of (path_metric T)). f r \<in> - K}"
      by (rule openin_continuous_map_preimage[OF cm op])
    then show ?thesis
      by (simp add: topspace_mtopology_of)
  qed
  have "{f \<in> mspace (path_metric T). pexit T K f < c}
      = (\<Union>r \<in> {0..T} \<inter> {..<c}.
          {f \<in> mspace (path_metric T). f r \<notin> K})"
    using False by (fastforce simp: pexit_less_iff[OF T])
  moreover have "openin (mtopology_of (path_metric T))
      (\<Union>r \<in> {0..T} \<inter> {..<c}. {f \<in> mspace (path_metric T). f r \<notin> K})"
    by (intro openin_Union) (auto intro: ev)
  ultimately show ?thesis by simp
qed

section \<open>The Laplace representation of the essential infimum\<close>

text \<open>LR, proof of Lemma 2.1: with \<open>f\<^sub>\<lambda>(P) = -(1/\<lambda>) ln E\<^sub>P[e\<^sup>-\<^sup>\<lambda>\<^sup>\<tau>]\<close>, the
  essential infimum of a time bounded in \<open>[0, T]\<close> is \<open>inf\<^sub>\<lambda> f\<^sub>\<lambda>\<close>.  Each
  \<open>f\<^sub>\<lambda>\<close> dominates the essential infimum (Jensen-free: the a.s. lower
  bound passes through the decreasing exponential), and as \<open>\<lambda> \<rightarrow> \<infinity>\<close>
  the transform concentrates at the essential infimum.\<close>

lemma exp_neg_time_integrable:
  fixes tau :: "'a \<Rightarrow> real" and l :: real
  assumes M: "prob_space M" and meas: "tau \<in> borel_measurable M"
    and nn: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and lam: "0 \<le> l"
  shows "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))"
proof -
  interpret prob_space M by fact
  have m: "(\<lambda>\<omega>. exp (- l * tau \<omega>)) \<in> borel_measurable M"
    using meas by measurable
  have b: "norm (exp (- l * tau \<omega>)) \<le> 1" if w: "\<omega> \<in> space M" for \<omega>
    using nn[OF w] lam
    by (simp add: exp_le_one_iff mult_nonneg_nonneg abs_of_pos)
  show ?thesis
    by (rule integrable_const_bound[where B = 1])
      (use m b in \<open>auto intro!: AE_I2\<close>)
qed

lemma exp_neg_time_integral_lower:
  fixes tau :: "'a \<Rightarrow> real" and l T :: real
  assumes M: "prob_space M" and meas: "tau \<in> borel_measurable M"
    and nn: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> tau \<omega> \<le> T"
    and lam: "0 \<le> l"
  shows "exp (- l * T) \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
proof -
  interpret prob_space M by fact
  have "exp (- l * T) = (\<integral>\<omega>. exp (- l * T) \<partial>M)"
    by (simp add: prob_space)
  also have "\<dots> \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
  proof (rule Bochner_Integration.integral_mono)
    show "integrable M (\<lambda>\<omega>. exp (- l * T))"
      by (rule integrable_const)
    show "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))"
      by (rule exp_neg_time_integrable[OF M meas nn lam])
    show "exp (- l * T) \<le> exp (- l * tau \<omega>)"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have "l * tau \<omega> \<le> l * T"
        by (rule mult_left_mono[OF le[OF w] lam])
      then show ?thesis by simp
    qed
  qed
  finally show ?thesis .
qed

lemma ess_inf_time_le_laplace:
  fixes tau :: "'a \<Rightarrow> real" and T l :: real
  assumes M: "prob_space M" and meas: "tau \<in> borel_measurable M"
    and nn: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> tau \<omega> \<le> T"
    and lam: "0 < l"
  shows "ess_inf_time M tau
      \<le> ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M))"
  unfolding ess_inf_time_def
proof (rule Sup_least)
  interpret prob_space M by fact
  fix c assume "c \<in> {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"
  then have ae: "AE \<omega> in M. c \<le> ennreal (tau \<omega>)" by simp
  have T0: "0 \<le> T"
    using nn le not_empty by (metis all_not_in_conv order_trans)
  have cT: "c \<le> ennreal T"
  proof -
    have "c = (\<integral>\<^sup>+\<omega>. c \<partial>M)"
      by (simp add: emeasure_space_1)
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
      by (rule nn_integral_mono_AE[OF ae])
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal T \<partial>M)"
      by (intro nn_integral_mono ennreal_leI le)
    also have "\<dots> = ennreal T"
      by (simp add: emeasure_space_1)
    finally show ?thesis .
  qed
  then have cfin: "c < \<top>"
    by (rule le_less_trans) (simp add: less_top)
  define c' where "c' = enn2real c"
  have cc': "c = ennreal c'"
    using cfin by (simp add: c'_def)
  have c'0: "0 \<le> c'" by (simp add: c'_def)
  have aeR: "AE \<omega> in M. c' \<le> tau \<omega>"
    using ae AE_space
  proof (eventually_elim)
    case (elim \<omega>)
    then have "ennreal c' \<le> ennreal (tau \<omega>)"
      using cc' by simp
    then show ?case
      using nn[OF elim(2)] by (simp add: ennreal_le_iff)
  qed
  have intg: "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))"
    by (rule exp_neg_time_integrable[OF M meas nn less_imp_le[OF lam]])
  have up: "(\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) \<le> exp (- l * c')"
  proof -
    have "AE \<omega> in M. exp (- l * tau \<omega>) \<le> exp (- l * c')"
      using aeR
      by eventually_elim
        (use lam in \<open>simp add: mult_left_mono_neg\<close>)
    then have "(\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) \<le> (\<integral>\<omega>. exp (- l * c') \<partial>M)"
      by (intro integral_mono_AE intg integrable_const)
    then show ?thesis by (simp add: prob_space)
  qed
  have pos: "0 < (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
    using exp_neg_time_integral_lower[OF M meas nn le less_imp_le[OF lam]]
    by (rule less_le_trans[OF exp_gt_zero])
  have lnle: "ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) \<le> - l * c'"
  proof -
    have "ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) \<le> ln (exp (- l * c'))"
      by (subst ln_le_cancel_iff) (use pos up in auto)
    then show ?thesis by simp
  qed
  then have "l * c' \<le> - ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
    by linarith
  then have "c' \<le> - ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) / l"
    using lam by (metis pos_le_divide_eq mult.commute)
  then have "c' \<le> - (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
    by (simp add: field_simps)
  then show "c \<le> ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M))"
    unfolding cc' by (rule ennreal_leI)
qed

text \<open>The transform attains the essential infimum in the limit \<open>\<lambda> \<rightarrow> \<infinity>\<close>:
  the mass \<open>p\<close> near the essential infimum survives as \<open>e^{−\<lambda>(e'+\<epsilon>)} p\<close>
  inside the expectation, and \<open>−ln p / \<lambda> \<rightarrow> 0\<close>.\<close>

lemma ess_inf_time_eq_laplace_inf:
  fixes tau :: "'a \<Rightarrow> real" and T :: real
  assumes M: "prob_space M" and meas: "tau \<in> borel_measurable M"
    and nn: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and le: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> tau \<omega> \<le> T"
  shows "(INF l \<in> {0<..}.
      ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))
    = ess_inf_time M tau"
proof (rule antisym)
  show "ess_inf_time M tau \<le> (INF l \<in> {0<..}.
      ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))"
    by (intro INF_greatest ess_inf_time_le_laplace[OF M meas nn le]) auto
  interpret prob_space M by fact
  have eiT: "ess_inf_time M tau \<le> ennreal T"
    unfolding ess_inf_time_def
  proof (rule Sup_least)
    fix c assume "c \<in> {c. AE \<omega> in M. c \<le> ennreal (tau \<omega>)}"
    then have ae: "AE \<omega> in M. c \<le> ennreal (tau \<omega>)" by simp
    have "c = (\<integral>\<^sup>+\<omega>. c \<partial>M)"
      by (simp add: emeasure_space_1)
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
      by (rule nn_integral_mono_AE[OF ae])
    also have "\<dots> \<le> (\<integral>\<^sup>+\<omega>. ennreal T \<partial>M)"
      by (intro nn_integral_mono ennreal_leI le)
    also have "\<dots> = ennreal T"
      by (simp add: emeasure_space_1)
    finally show "c \<le> ennreal T" .
  qed
  then have efin: "ess_inf_time M tau < \<top>"
    by (rule le_less_trans) (simp add: less_top)
  define e' where "e' = enn2real (ess_inf_time M tau)"
  have ee: "ess_inf_time M tau = ennreal e'"
    using efin by (simp add: e'_def)
  have e'0: "0 \<le> e'" by (simp add: e'_def)
  have key: "(INF l \<in> {0<..}.
      ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))
      \<le> ennreal (e' + 2 * \<epsilon>)" if \<epsilon>: "0 < \<epsilon>" for \<epsilon>
  proof -
    define E where "E = {\<omega> \<in> space M. tau \<omega> \<le> e' + \<epsilon>}"
    have EM: "E \<in> sets M"
      unfolding E_def using meas by measurable
    define p where "p = prob E"
    have p_pos: "0 < p"
    proof (rule ccontr)
      assume "\<not> 0 < p"
      then have p0: "p = 0"
        unfolding p_def using measure_nonneg[of M E] by simp
      have "AE \<omega> in M. \<omega> \<notin> E"
        using p0 EM unfolding p_def
        by (intro AE_I[where N = E])
          (auto simp: emeasure_eq_measure)
      then have "AE \<omega> in M. ennreal (e' + \<epsilon>) \<le> ennreal (tau \<omega>)"
        using AE_space
        by eventually_elim (auto simp: E_def intro!: ennreal_leI)
      then have "ennreal (e' + \<epsilon>) \<le> ess_inf_time M tau"
        unfolding ess_inf_time_def by (intro Sup_upper) simp
      then have "e' + \<epsilon> \<le> e'"
        unfolding ee using e'0 by (simp add: ennreal_le_iff)
      with \<epsilon> show False by simp
    qed
    have p1: "p \<le> 1" unfolding p_def by simp
    have lnp0: "0 \<le> - ln p"
    proof -
      have "ln p \<le> ln 1"
        using p_pos p1 by (simp add: ln_le_cancel_iff)
      then show ?thesis by simp
    qed
    define l where "l = max 1 (- ln p / \<epsilon>)"
    have l1: "1 \<le> l" unfolding l_def by simp
    have l0: "0 < l" using l1 by simp
    have lnp: "- ln p / l \<le> \<epsilon>"
    proof (cases "- ln p / \<epsilon> \<le> 1")
      case True
      have "- ln p = (- ln p / \<epsilon>) * \<epsilon>"
        using \<epsilon> by simp
      also have "\<dots> \<le> 1 * \<epsilon>"
        by (rule mult_right_mono[OF True less_imp_le[OF \<epsilon>]])
      finally have nle: "- ln p \<le> \<epsilon>" by simp
      have "- ln p / l \<le> - ln p / 1"
        by (rule frac_le[OF lnp0 order_refl zero_less_one l1])
      with nle show ?thesis by simp
    next
      case False
      then have leq: "l = - ln p / \<epsilon>" unfolding l_def by simp
      have "- ln p / \<epsilon> > 0" using False by simp
      then show ?thesis
        unfolding leq using \<epsilon> by simp
    qed
    have intg: "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))"
      by (rule exp_neg_time_integrable[OF M meas nn less_imp_le[OF l0]])
    have lower: "exp (- l * (e' + \<epsilon>)) * p \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
    proof -
      have ptw: "exp (- l * (e' + \<epsilon>)) * indicat_real E \<omega>
          \<le> exp (- l * tau \<omega>)" if w: "\<omega> \<in> space M" for \<omega>
      proof (cases "\<omega> \<in> E")
        case True
        then have "tau \<omega> \<le> e' + \<epsilon>" by (simp add: E_def)
        then have "l * tau \<omega> \<le> l * (e' + \<epsilon>)"
          by (rule mult_left_mono) (use l0 in simp)
        then show ?thesis using True by simp
      next
        case False
        then show ?thesis by simp
      qed
      have EI: "E \<inter> space M = E"
        using sets.sets_into_space[OF EM] by auto
      have "exp (- l * (e' + \<epsilon>)) * p
          = (\<integral>\<omega>. exp (- l * (e' + \<epsilon>)) * indicat_real E \<omega> \<partial>M)"
        unfolding p_def by (simp add: EI)
      also have "\<dots> \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
      proof (rule Bochner_Integration.integral_mono)
        show "integrable M (\<lambda>\<omega>. exp (- l * (e' + \<epsilon>)) * indicat_real E \<omega>)"
          using EM
          by (intro integrable_mult_right)
            (auto simp: integrable_indicator_iff EI
              emeasure_eq_measure)
        show "integrable M (\<lambda>\<omega>. exp (- l * tau \<omega>))" by (rule intg)
        show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow>
            exp (- l * (e' + \<epsilon>)) * indicat_real E \<omega> \<le> exp (- l * tau \<omega>)"
          by (rule ptw)
      qed
      finally show ?thesis .
    qed
    have pos: "0 < (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
    proof -
      have "(0 :: real) < exp (- l * T)" by simp
      also have "\<dots> \<le> (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
        by (rule exp_neg_time_integral_lower[OF M meas nn le
            less_imp_le[OF l0]])
      finally show ?thesis .
    qed
    have fl_le: "- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) \<le> e' + 2 * \<epsilon>"
    proof -
      have "ln (exp (- l * (e' + \<epsilon>)) * p)
          \<le> ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
        using lower p_pos pos
        by (subst ln_le_cancel_iff) (auto intro: mult_pos_pos)
      then have "- l * (e' + \<epsilon>) + ln p
          \<le> ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)"
        using p_pos by (simp add: ln_mult)
      then have "- ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)
          \<le> l * (e' + \<epsilon>) - ln p"
        by linarith
      then have "- ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M) / l
          \<le> (l * (e' + \<epsilon>) - ln p) / l"
        by (rule divide_right_mono) (use l0 in simp)
      also have "\<dots> = (e' + \<epsilon>) + (- ln p / l)"
        using l0 by (simp add: field_simps)
      also have "\<dots> \<le> (e' + \<epsilon>) + \<epsilon>"
        using lnp by simp
      finally show ?thesis
        using l0 by (simp add: field_simps)
    qed
    have "(INF l \<in> {0<..}.
        ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))
        \<le> ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M))"
      by (rule INF_lower) (use l0 in simp)
    also have "\<dots> \<le> ennreal (e' + 2 * \<epsilon>)"
      by (rule ennreal_leI[OF fl_le])
    finally show ?thesis .
  qed
  show "(INF l \<in> {0<..}.
      ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))
      \<le> ess_inf_time M tau"
    unfolding ee
  proof (rule ennreal_le_epsilon)
    fix \<epsilon> :: real
    assume "ennreal e' < \<top>" and \<epsilon>: "0 < \<epsilon>"
    have "(INF l \<in> {0<..}.
        ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))
        \<le> ennreal (e' + 2 * (\<epsilon> / 2))"
      by (rule key) (use \<epsilon> in simp)
    also have "e' + 2 * (\<epsilon> / 2) = e' + \<epsilon>" by simp
    also have "ennreal (e' + \<epsilon>) = ennreal e' + ennreal \<epsilon>"
      using e'0 less_imp_le[OF \<epsilon>] by (rule ennreal_plus)
    finally show "(INF l \<in> {0<..}.
        ennreal (- (1 / l) * ln (\<integral>\<omega>. exp (- l * tau \<omega>) \<partial>M)))
        \<le> ennreal e' + ennreal \<epsilon>" .
  qed
qed

section \<open>The telescoping step minorant\<close>

text \<open>A decreasing continuous transform of the exit time is approximated
  from below, uniformly up to the mesh modulus, by a positive
  combination of indicators of the OPEN sublevels \<open>{pexit < s_j}\<close> on a
  uniform grid — the device that carries the Laplace transforms through
  weak convergence with nothing but the open-set liminf half of the
  portmanteau theorem.\<close>

definition pstep ::
  "real \<Rightarrow> ('b :: polish_space) set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> real"
  where
  "pstep T K l N f = exp (- l * T)
     + (\<Sum> j = 1..<N. (exp (- l * (real j * T / real N))
          - exp (- l * (real (Suc j) * T / real N)))
        * indicat_real {g. pexit T K g < real j * T / real N} f)"

lemma pstep_sandwich:
  fixes K :: "('b :: polish_space) set" and f :: "real \<Rightarrow> 'b"
  assumes T: "0 < T" and l: "0 < l" and N: "0 < N"
  shows "pstep T K l N f \<le> exp (- l * pexit T K f)
      \<and> exp (- l * pexit T K f)
        \<le> pstep T K l N f + (1 - exp (- l * (T / real N)))"
proof -
  let ?\<tau> = "pexit T K f"
  let ?s = "\<lambda>j. real j * T / real N"
  let ?\<phi> = "\<lambda>j. exp (- l * ?s j)"
  have T0: "0 \<le> T" using T by simp
  have \<tau>0: "0 \<le> ?\<tau>" by (rule pexit_nonneg[OF T0])
  have \<tau>T: "?\<tau> \<le> T" by (rule pexit_le_T[OF T0])
  have err0: "0 \<le> 1 - exp (- l * (T / real N))"
    using T l N by (simp add: mult_nonneg_nonneg)
  show ?thesis
  proof (cases "?\<tau> < T")
    case False
    then have \<tau>eq: "?\<tau> = T" using \<tau>T by simp
    have no_ind: "\<not> ?\<tau> < ?s j" if "j < N" for j
    proof -
      have "?s j \<le> T"
        using that N T
        by (simp add: divide_le_eq mult_right_mono)
      then show ?thesis using \<tau>eq by simp
    qed
    then have "pstep T K l N f = exp (- l * T)"
      unfolding pstep_def by (simp add: indicator_def)
    then show ?thesis
      using \<tau>eq err0 by simp
  next
    case True
    define m where "m = (LEAST j. ?\<tau> < ?s j)"
    have exN: "?\<tau> < ?s N"
      using True N by simp
    have exE: "\<exists>j. ?\<tau> < ?s j" using exN by blast
    have mless: "?\<tau> < ?s m"
      unfolding m_def by (rule LeastI_ex[OF exE])
    have mmin: "\<not> ?\<tau> < ?s j" if "j < m" for j
      using that unfolding m_def by (rule not_less_Least)
    have mN: "m \<le> N"
      unfolding m_def using exN by (rule Least_le)
    have m1: "1 \<le> m"
    proof (rule ccontr)
      assume "\<not> 1 \<le> m"
      then have "m = 0" by simp
      with mless have "?\<tau> < 0" by simp
      with \<tau>0 show False by simp
    qed
    have s_mono: "?s j \<le> ?s k" if "j \<le> k" for j k
      using that T N
      by (simp add: divide_right_mono mult_right_mono)
    have ind_iff: "?\<tau> < ?s j \<longleftrightarrow> m \<le> j" for j
    proof
      assume "?\<tau> < ?s j"
      then show "m \<le> j"
        using mmin[of j] by (cases "j < m") auto
    next
      assume "m \<le> j"
      then have "?s m \<le> ?s j" by (rule s_mono)
      with mless show "?\<tau> < ?s j" by simp
    qed
    have sum_eq: "(\<Sum> j = 1..<N. (?\<phi> j - ?\<phi> (Suc j))
        * indicat_real {g. pexit T K g < ?s j} f)
        = (\<Sum> j = m..<N. ?\<phi> j - ?\<phi> (Suc j))"
      by (intro sum.mono_neutral_cong_right)
        (use m1 in \<open>auto simp: indicator_def ind_iff\<close>)
    have tele: "(\<Sum> j = m..<N. ?\<phi> j - ?\<phi> (Suc j)) = ?\<phi> m - ?\<phi> N"
    proof -
      have "(\<Sum> j = m..<N. ?\<phi> (Suc j) - ?\<phi> j) = ?\<phi> N - ?\<phi> m"
        by (rule sum_Suc_diff'[OF mN])
      moreover have "(\<Sum> j = m..<N. ?\<phi> j - ?\<phi> (Suc j))
          = - (\<Sum> j = m..<N. ?\<phi> (Suc j) - ?\<phi> j)"
        by (simp add: sum_subtractf)
      ultimately show ?thesis by simp
    qed
    have sN: "?s N = T" using N by simp
    have pstep_eq: "pstep T K l N f = ?\<phi> m"
      unfolding pstep_def sum_eq tele using sN by simp
    have lo: "pstep T K l N f \<le> exp (- l * ?\<tau>)"
    proof -
      have "l * ?\<tau> \<le> l * ?s m"
        by (intro mult_left_mono) (use mless l in auto)
      then have "?\<phi> m \<le> exp (- l * ?\<tau>)"
        by (subst exp_le_cancel_iff) linarith
      then show ?thesis unfolding pstep_eq .
    qed
    have hi: "exp (- l * ?\<tau>) \<le> pstep T K l N f
        + (1 - exp (- l * (T / real N)))"
    proof -
      have sm_le: "?s m \<le> ?\<tau> + T / real N"
      proof -
        have "?s (m - 1) \<le> ?\<tau>"
          using mmin[of "m - 1"] m1 by force
        moreover have "?s m = ?s (m - 1) + T / real N"
          using m1 N
          by (simp add: field_simps of_nat_diff)
        ultimately show ?thesis by simp
      qed
      have "l * ?s m \<le> l * (?\<tau> + T / real N)"
        by (intro mult_left_mono sm_le) (use l in auto)
      then have "exp (- l * (?\<tau> + T / real N)) \<le> ?\<phi> m"
        by (subst exp_le_cancel_iff) linarith
      then have "exp (- l * ?\<tau>) - ?\<phi> m
          \<le> exp (- l * ?\<tau>) - exp (- l * (?\<tau> + T / real N))"
        by linarith
      also have "\<dots> = exp (- l * ?\<tau>) * (1 - exp (- l * (T / real N)))"
        by (simp add: algebra_simps exp_add[symmetric] flip: exp_add)
      also have "\<dots> \<le> 1 * (1 - exp (- l * (T / real N)))"
        using \<tau>0 l err0
        by (intro mult_right_mono)
          (auto simp: exp_le_one_iff mult_nonneg_nonneg)
      finally show ?thesis unfolding pstep_eq by simp
    qed
    show ?thesis using lo hi by blast
  qed
qed

lemma pexit_measurable:
  fixes K :: "('b :: polish_space) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "pexit T K \<in> borel_measurable
      (borel_of (mtopology_of (path_metric T
        :: (real \<Rightarrow> 'b) metric)))"
proof (rule borel_measurableI_less)
  fix c :: real
  have "{f \<in> space (borel_of (mtopology_of (path_metric T
        :: (real \<Rightarrow> 'b) metric))). pexit T K f < c}
      = {f \<in> mspace (path_metric T). pexit T K f < c}"
    by (simp add: space_borel_of topspace_mtopology_of)
  then show "{f \<in> space (borel_of (mtopology_of (path_metric T
        :: (real \<Rightarrow> 'b) metric))). pexit T K f < c}
      \<in> sets (borel_of (mtopology_of (path_metric T)))"
    using borel_of_open[OF pexit_sublevel_open[OF T K]] by simp
qed

end
