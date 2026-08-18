
(*<*)
theory Path_Exit_Times
  imports Path_Space Path_Space_Infinite "Continuous_Time_Martingales.Stopping_Times"
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Time_Martingales.Essential_Infimum"
begin

(*>*)

text \<open>
  The exit time of a closed set by a continuous path, and how it behaves
  under weak convergence of path laws -- the shape in which Larsson and Ruf
  use it (Lemma 2.1 of \<^cite>\<open>LarssonRuf\<close>).
  The capped exit time is upper semicontinuous on the path space, and that the essential infimum of the exit time is upper
  semicontinuous along weak convergence of path laws, via the
  Laplace-transform representation

    \<open>essinf tau = Inf\<^bsub>lambda > 0\<^esub> - (1 / lambda) * ln (E [exp (- lambda * tau)])\<close>.\<close>
section \<open>The path-space exit time\<close>
text \<open>(The crowning theorem of this theory is \<open>ess_inf_pexit_usc\<close> at the
  end: the essential infimum of the exit time is upper semicontinuous
  along weak convergence of path laws.)\<close>

text \<open>The capped exit time from \<open>K\<close>, read off a path rather than a sample
  point: the composition of \<open>etime\<close> with the identity process. All laws in
  the paper's class share the same sample space -- the path space -- and the
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

text \<open>The paper (\<^cite>\<open>LaiShkolnikovSoner\<close>, (1.6)--(1.8)) works on \<open>C([0,\<infinity>), \<real>\<^sup>n)\<close> and
  takes the essential infimum of the uncapped exit time
  \<open>\<tau>\<^sub>K = inf {t \<ge> 0 : X t \<notin> K}\<close>, whereas \<open>pexit T K\<close> caps at the horizon \<open>T\<close>.
  The cap is monotone in \<open>T\<close> and invisible once a path has exited before
  \<open>T\<close>: raising the horizon does not move the value. Hence for laws under
  which the exit happens before \<open>T\<close> almost surely, every capped horizon
  beyond that point gives the same essential infimum, which licenses working
  at a fixed finite \<open>T\<close>.\<close>

lemma pexit_mono_T:
  assumes T: "0 \<le> T" and TT: "T \<le> T'"
  shows "pexit T K f \<le> pexit T' K f"
proof (rule ccontr)
  assume "\<not> pexit T K f \<le> pexit T' K f"
  then have lt: "pexit T' K f < pexit T K f" by simp
  have T'0: "0 \<le> T'" using T TT by simp
  from lt have "(\<exists>r. 0 \<le> r \<and> r \<le> T' \<and> f r \<in> - K \<and> r < pexit T K f)
      \<or> T' < pexit T K f"
    using pexit_less_iff[OF T'0] by blast
  then have "pexit T K f < pexit T K f"
  proof
    assume "\<exists>r. 0 \<le> r \<and> r \<le> T' \<and> f r \<in> - K \<and> r < pexit T K f"
    then obtain r where r: "0 \<le> r" "r \<le> T'" "f r \<in> - K"
      and rlt: "r < pexit T K f" by blast
    show ?thesis
    proof (cases "r \<le> T")
      case True
      then show ?thesis
        using pexit_less_iff[OF T] r rlt by blast
    next
      case False
      then have "T < pexit T K f" using rlt by simp
      then show ?thesis
        using pexit_less_iff[OF T] by blast
    qed
  next
    assume "T' < pexit T K f"
    then have "T < pexit T K f" using TT by simp
    then show ?thesis using pexit_less_iff[OF T] by blast
  qed
  then show False by simp
qed

lemma pexit_stable_above_T:
  assumes T: "0 \<le> T" and TT: "T \<le> T'" and ex: "pexit T K f < T"
  shows "pexit T' K f = pexit T K f"
proof (rule antisym)
  show "pexit T K f \<le> pexit T' K f" by (rule pexit_mono_T[OF T TT])
next
  have T'0: "0 \<le> T'" using T TT by simp
  have "pexit T' K f < c" if c: "pexit T K f < c" "c \<le> T" for c
  proof -
    have "\<not> T < c" using c by simp
    with pexit_less_iff[OF T] c(1)
    obtain r where r: "0 \<le> r" "r \<le> T" "f r \<in> - K" "r < c" by blast
    then have "r \<le> T'" using TT by simp
    with r show ?thesis using pexit_less_iff[OF T'0] by blast
  qed
  note key = this
  show "pexit T' K f \<le> pexit T K f"
  proof (rule ccontr)
    assume "\<not> pexit T' K f \<le> pexit T K f"
    then have ab: "pexit T K f < pexit T' K f" by simp
    define c where "c = min ((pexit T K f + pexit T' K f) / 2)
        ((pexit T K f + T) / 2)"
    have c1: "pexit T K f < c" using ab ex unfolding c_def by simp
    have c2: "c \<le> T"
    proof -
      have "c \<le> (pexit T K f + T) / 2"
        unfolding c_def by (rule min.cobounded2)
      also have "\<dots> \<le> T" using ex by argo
      finally show ?thesis .
    qed
    have c3: "c < pexit T' K f"
    proof -
      have "c \<le> (pexit T K f + pexit T' K f) / 2"
        unfolding c_def by (rule min.cobounded1)
      also have "\<dots> < pexit T' K f" using ab by argo
      finally show ?thesis .
    qed
    have "pexit T' K f < c" by (rule key[OF c1 c2])
    with c3 show False by simp
  qed
qed

text \<open>The law-level form: the essential infimum only sees the almost-sure
  class of the exit time, so once the exit happens before \<open>T\<close> almost surely,
  every larger horizon gives the SAME value.  This is what licenses working
  at a fixed finite \<open>T\<close> in place of the paper's \<open>C([0,\<infinity>), \<real>ⁿ)\<close>.\<close>

text \<open>Upper semicontinuity, in sublevel-set form: strict sublevels of the
  exit time are open in the path topology. A path that exits before \<open>c\<close>
  does so at a time where it sits in the open complement of \<open>K\<close>, and
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
      by simp
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

lemma pexit_measurable:
  fixes K :: "('b :: polish_space) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "pexit T K \<in> borel_measurable
      (path_borel T :: (real \<Rightarrow> 'b) measure)"
proof (rule borel_measurableI_less)
  fix c :: real
  have "{f \<in> space (path_borel T :: (real \<Rightarrow> 'b) measure). pexit T K f < c}
      = {f \<in> mspace (path_metric T). pexit T K f < c}"
    by (simp add: space_borel_of)
  then show "{f \<in> space (path_borel T :: (real \<Rightarrow> 'b) measure). pexit T K f < c}
      \<in> sets (path_borel T)"
    using borel_of_open[OF pexit_sublevel_open[OF T K]] by simp
qed

section \<open>The Laplace representation of the essential infimum\<close>

text \<open>\<open>exp_neg_time_integrable\<close>, \<open>exp_neg_time_integral_lower\<close> live in @{theory Continuous_Time_Martingales.Integrability_Criteria}.\<close>


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
      using nn[OF elim(2)] by simp
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
  the mass \<open>p\<close> near the essential infimum survives as \<open>e^{-\<lambda>(e'+\<epsilon>)} p\<close>
  inside the expectation, and \<open>-ln p / \<lambda> \<rightarrow> 0\<close>.\<close>

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
        unfolding ee using e'0 by simp
      with \<epsilon> show False by simp
    qed
    have p1: "p \<le> 1" unfolding p_def by simp
    have lnp0: "0 \<le> - ln p"
    proof -
      have "ln p \<le> ln 1"
        using p_pos p1 by simp
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
  from below, uniformly up to the mesh modulus, by a positive combination of
  indicators of the open sublevels \<open>{pexit < s_j}\<close> on a uniform grid -- the
  device that carries the Laplace transforms through weak convergence with
  nothing but the open-set liminf half of the portmanteau theorem.\<close>

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
    using T l N by simp
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
          by (simp add: field_simps)
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
          auto
      finally show ?thesis unfolding pstep_eq by simp
    qed
    show ?thesis using lo hi by blast
  qed
qed

lemma pstep_integral:
  fixes K :: "('b :: polish_space) set"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and s\<Lambda>: "sets \<Lambda> = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and fin: "finite_measure \<Lambda>"
  shows "(\<integral>f. pstep T K l N f \<partial>\<Lambda>)
      = exp (- l * T) * measure \<Lambda> (space \<Lambda>)
        + (\<Sum> j = 1..<N.
            (exp (- l * (real j * T / real N))
              - exp (- l * (real (Suc j) * T / real N)))
            * measure \<Lambda> {f \<in> mspace (path_metric T).
                pexit T K f < real j * T / real N})"
proof -
  interpret finite_measure \<Lambda> by fact
  have sp\<Lambda>: "space \<Lambda> = mspace (path_metric T)"
    using sets_eq_imp_space_eq[OF s\<Lambda>]
    by (simp add: space_borel_of)
  have setj: "{g. pexit T K g < real j * T / real N} \<inter> space \<Lambda>
      = {f \<in> mspace (path_metric T).
          pexit T K f < real j * T / real N}" for j
    unfolding sp\<Lambda> by auto
  have memj: "{g. pexit T K g < real j * T / real N} \<inter> space \<Lambda>
      \<in> sets \<Lambda>" for j
    unfolding setj s\<Lambda>
    by (intro borel_of_open pexit_sublevel_open[OF T K])
  have int_ind: "integrable \<Lambda>
      (\<lambda>f. indicat_real {g. pexit T K g < real j * T / real N} f)"
    for j
    using memj[of j]
    by (auto simp: integrable_indicator_iff emeasure_eq_measure)
  have int_term: "integrable \<Lambda>
      (\<lambda>f. (exp (- l * (real j * T / real N))
          - exp (- l * (real (Suc j) * T / real N)))
        * indicat_real {g. pexit T K g < real j * T / real N} f)"
    for j
    by (intro integrable_mult_right int_ind)
  have "(\<integral>f. pstep T K l N f \<partial>\<Lambda>)
      = (\<integral>f. exp (- l * T) \<partial>\<Lambda>)
        + (\<integral>f. (\<Sum> j = 1..<N.
            (exp (- l * (real j * T / real N))
              - exp (- l * (real (Suc j) * T / real N)))
            * indicat_real {g. pexit T K g < real j * T / real N} f) \<partial>\<Lambda>)"
    unfolding pstep_def
    by (intro Bochner_Integration.integral_add integrable_const
        Bochner_Integration.integrable_sum int_term)
  also have "(\<integral>f. exp (- l * T) \<partial>\<Lambda>)
      = exp (- l * T) * measure \<Lambda> (space \<Lambda>)"
    by (simp add: mult.commute)
  also have "(\<integral>f. (\<Sum> j = 1..<N.
      (exp (- l * (real j * T / real N))
        - exp (- l * (real (Suc j) * T / real N)))
      * indicat_real {g. pexit T K g < real j * T / real N} f) \<partial>\<Lambda>)
      = (\<Sum> j = 1..<N. (\<integral>f.
          (exp (- l * (real j * T / real N))
            - exp (- l * (real (Suc j) * T / real N)))
          * indicat_real {g. pexit T K g < real j * T / real N} f \<partial>\<Lambda>))"
    by (rule Bochner_Integration.integral_sum[OF int_term])
  also have "\<dots> = (\<Sum> j = 1..<N.
      (exp (- l * (real j * T / real N))
        - exp (- l * (real (Suc j) * T / real N)))
      * measure \<Lambda> {f \<in> mspace (path_metric T).
          pexit T K f < real j * T / real N})"
    by (intro sum.cong refl) (simp add: setj)
  finally show ?thesis .
qed

text \<open>Along weak convergence of path laws, the measure of each open
  sublevel can only gain mass in the limit (portmanteau), and the step
  minorant is a positive combination of such measures plus a
  total-mass term, so its integral is lower semicontinuous.\<close>

lemma weak_conv_open_liminf:
  fixes \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b :: polish_space) measure"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and U: "openin (mtopology_of (path_metric T
      :: (real \<Rightarrow> 'b) metric)) U"
  shows "ereal (measure \<Lambda> U)
      \<le> Liminf sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) U))"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  interpret PM: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)) \<and> finite_measure (\<Lambda>i i))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>
      \<and> (\<forall>f. continuous_map (mtopology_of ?m) euclideanreal f \<longrightarrow>
          (\<exists>B. \<forall>x\<in>topspace (mtopology_of ?m). \<bar>f x\<bar> \<le> B) \<longrightarrow>
          ((\<lambda>i. \<integral>x. f x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>\<Lambda>)))"
    using wc unfolding weak_conv_on_def by blast
  have top: "PM.mtopology = mtopology_of ?m"
    by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin "mspace ?m" "mdist ?m" \<Lambda>i \<Lambda> sequentially
  proof
    show "\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i) = sets (borel_of PM.mtopology)"
      using wc' top by (auto elim: eventually_mono)
    show "sets \<Lambda> = sets (borel_of PM.mtopology)"
      using wc' top by simp
    show "\<forall>\<^sub>F i in sequentially. finite_measure (\<Lambda>i i)"
      using wc' by (auto elim: eventually_mono)
    show "\<exists>A. countable A \<and> A \<subseteq> sets \<Lambda> \<and> \<Union> A = space \<Lambda>
        \<and> (\<forall>a\<in>A. emeasure \<Lambda> a \<noteq> \<infinity>)"
      by (intro exI[of _ "{space \<Lambda>}"])
        (use wc' in \<open>auto simp: finite_measure.emeasure_eq_measure\<close>)
    show "emeasure \<Lambda> (space \<Lambda>) \<noteq> \<top>"
      using wc' by (simp add: finite_measure.emeasure_eq_measure)
  qed
  have cb: "(\<lambda>i. \<integral>x. g x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. g x \<partial>\<Lambda>)"
    if u: "uniformly_continuous_map PM.Self euclidean_metric g"
      and b: "\<exists>B. \<forall>x\<in>mspace ?m. \<bar>g x\<bar> \<le> B" for g :: "(real \<Rightarrow> 'b) \<Rightarrow> real"
  proof -
    have cg: "continuous_map (mtopology_of ?m) euclideanreal g"
      using uniformly_continuous_imp_continuous_map[OF u]
      by (simp add: mtopology_of_def)
    show ?thesis
      using wc' cg b by auto
  qed
  have cls: "Limsup sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) A))
      \<le> ereal (measure \<Lambda> A)"
    if A: "closedin PM.mtopology A" for A
    by (rule MW.mweak_conv2[OF cb A])
  have mass: "(\<lambda>i. measure (\<Lambda>i i) (mspace ?m))
      \<longlonglongrightarrow> measure \<Lambda> (mspace ?m)"
  proof -
    have wcf: "(\<lambda>i. \<integral>x. g x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. g x \<partial>\<Lambda>)"
      if "continuous_map (mtopology_of ?m) euclideanreal g"
        and "\<exists>B. \<forall>x\<in>topspace (mtopology_of ?m). \<bar>g x\<bar> \<le> B"
      for g :: "(real \<Rightarrow> 'b) \<Rightarrow> real"
      using wc' that by blast
    have "(\<lambda>i. \<integral>x. 1 \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. (1::real) \<partial>\<Lambda>)"
      by (rule wcf) (auto intro!: exI[of _ 1])
    moreover have "(\<integral>x. (1::real) \<partial>(\<Lambda>i i)) = measure (\<Lambda>i i) (space (\<Lambda>i i))"
      for i by simp
    moreover have "(\<integral>x. (1::real) \<partial>\<Lambda>) = measure \<Lambda> (space \<Lambda>)" by simp
    ultimately show ?thesis
      using MW.space_N MW.space_Ni
      by (auto elim!: tendsto_cong[THEN iffD1, rotated]
          intro: eventually_mono)
  qed
  show ?thesis
    using MW.mweak_conv3[OF cls mass] U top by simp
qed

text \<open>The closed-set half of the portmanteau theorem on the path space: a
  closed condition on paths that every approximating law satisfies with full
  mass survives the weak limit.\<close>

lemma weak_conv_closed_limsup:
  fixes \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b :: polish_space) measure"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and A: "closedin (mtopology_of (path_metric T
      :: (real \<Rightarrow> 'b) metric)) A"
  shows "Limsup sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) A))
      \<le> ereal (measure \<Lambda> A)"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  interpret PM: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)) \<and> finite_measure (\<Lambda>i i))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>
      \<and> (\<forall>f. continuous_map (mtopology_of ?m) euclideanreal f \<longrightarrow>
          (\<exists>B. \<forall>x\<in>topspace (mtopology_of ?m). \<bar>f x\<bar> \<le> B) \<longrightarrow>
          ((\<lambda>i. \<integral>x. f x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>\<Lambda>)))"
    using wc unfolding weak_conv_on_def by blast
  have top: "PM.mtopology = mtopology_of ?m"
    by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin "mspace ?m" "mdist ?m" \<Lambda>i \<Lambda> sequentially
  proof
    show "\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i) = sets (borel_of PM.mtopology)"
      using wc' top by (auto elim: eventually_mono)
    show "sets \<Lambda> = sets (borel_of PM.mtopology)"
      using wc' top by simp
    show "\<forall>\<^sub>F i in sequentially. finite_measure (\<Lambda>i i)"
      using wc' by (auto elim: eventually_mono)
    show "\<exists>A. countable A \<and> A \<subseteq> sets \<Lambda> \<and> \<Union> A = space \<Lambda>
        \<and> (\<forall>a\<in>A. emeasure \<Lambda> a \<noteq> \<infinity>)"
      by (intro exI[of _ "{space \<Lambda>}"])
        (use wc' in \<open>auto simp: finite_measure.emeasure_eq_measure\<close>)
    show "emeasure \<Lambda> (space \<Lambda>) \<noteq> \<top>"
      using wc' by (simp add: finite_measure.emeasure_eq_measure)
  qed
  have cb: "(\<lambda>i. \<integral>x. g x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. g x \<partial>\<Lambda>)"
    if u: "uniformly_continuous_map PM.Self euclidean_metric g"
      and b: "\<exists>B. \<forall>x\<in>mspace ?m. \<bar>g x\<bar> \<le> B" for g :: "(real \<Rightarrow> 'b) \<Rightarrow> real"
  proof -
    have cg: "continuous_map (mtopology_of ?m) euclideanreal g"
      using uniformly_continuous_imp_continuous_map[OF u]
      by (simp add: mtopology_of_def)
    show ?thesis
      using wc' cg b by auto
  qed
  have A': "closedin PM.mtopology A"
    using A top by metis
  show ?thesis
    by (rule MW.mweak_conv2[OF cb A'])
qed

text \<open>The form the constraint step consumes: a closed set carrying full mass
  under every approximating probability law carries full mass in the limit.\<close>

lemma weak_conv_closed_full_mass:
  fixes \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b :: polish_space) measure"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and A: "closedin (mtopology_of (path_metric T
      :: (real \<Rightarrow> 'b) metric)) A"
    and probs: "\<And>i. prob_space (\<Lambda>i i)" and prob: "prob_space \<Lambda>"
    and full: "\<And>i. measure (\<Lambda>i i) A = 1"
  shows "measure \<Lambda> A = 1"
proof -
  have "ereal 1 = Limsup sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) A))"
    using full by (simp add: Limsup_const)
  also have "\<dots> \<le> ereal (measure \<Lambda> A)"
    by (rule weak_conv_closed_limsup[OF wc A])
  finally have ge: "1 \<le> measure \<Lambda> A" by simp
  have le1: "measure \<Lambda> A \<le> 1"
  proof -
    interpret P: prob_space \<Lambda> by (rule prob)
    show ?thesis by simp
  qed
  from ge le1 show ?thesis by simp
qed

lemma weak_conv_total_mass:
  fixes \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b :: polish_space) measure"
    and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
  shows "(\<lambda>i. measure (\<Lambda>i i) (space (\<Lambda>i i))) \<longlonglongrightarrow> measure \<Lambda> (space \<Lambda>)"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)) \<and> finite_measure (\<Lambda>i i))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>
      \<and> (\<forall>f. continuous_map (mtopology_of ?m) euclideanreal f \<longrightarrow>
          (\<exists>B. \<forall>x\<in>topspace (mtopology_of ?m). \<bar>f x\<bar> \<le> B) \<longrightarrow>
          ((\<lambda>i. \<integral>x. f x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. f x \<partial>\<Lambda>)))"
    using wc unfolding weak_conv_on_def by blast
  have wcf: "(\<lambda>i. \<integral>x. g x \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. g x \<partial>\<Lambda>)"
    if "continuous_map (mtopology_of ?m) euclideanreal g"
      and "\<exists>B. \<forall>x\<in>topspace (mtopology_of ?m). \<bar>g x\<bar> \<le> B"
    for g :: "(real \<Rightarrow> 'b) \<Rightarrow> real"
    using wc' that by blast
  have "(\<lambda>i. \<integral>x. 1 \<partial>(\<Lambda>i i)) \<longlonglongrightarrow> (\<integral>x. (1::real) \<partial>\<Lambda>)"
    by (rule wcf) (auto intro!: exI[of _ 1])
  then show ?thesis by simp
qed

text \<open>The step integrals are lower semicontinuous along weak
  convergence: the mass term converges outright and each open-set term
  can only gain mass, so an \<open>\<epsilon>/(number of terms)\<close> argument gives an
  eventual lower bound.\<close>

lemma pstep_integral_liminf:
  fixes K :: "('b :: polish_space) set"
    and \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure" and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and K: "closed K" and l: "0 \<le> l"
    and wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
  shows "ereal (\<integral>f. pstep T K l N f \<partial>\<Lambda>)
      \<le> Liminf sequentially (\<lambda>i. ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i)))"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  let ?U = "\<lambda>j. {f \<in> mspace ?m. pexit T K f < real j * T / real N}"
  let ?c = "\<lambda>j. exp (- l * (real j * T / real N))
      - exp (- l * (real (Suc j) * T / real N))"
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)) \<and> finite_measure (\<Lambda>i i))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>"
    using wc unfolding weak_conv_on_def by blast
  have dec\<Lambda>: "(\<integral>f. pstep T K l N f \<partial>\<Lambda>)
      = exp (- l * T) * measure \<Lambda> (space \<Lambda>)
        + (\<Sum> j = 1..<N. ?c j * measure \<Lambda> (?U j))"
    using wc' by (intro pstep_integral[OF T K]) auto
  have c0: "0 \<le> exp (- l * T)" by simp
  have cj0: "0 \<le> ?c j" for j
  proof -
    have "l * (real j * T / real N) \<le> l * (real (Suc j) * T / real N)"
      by (intro mult_left_mono l)
        (use T in \<open>auto intro!: divide_right_mono mult_right_mono\<close>)
    then show ?thesis
      by simp
  qed
  have eps: "ereal ((\<integral>f. pstep T K l N f \<partial>\<Lambda>) - e)
      \<le> Liminf sequentially (\<lambda>i. ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i)))"
    if e: "0 < e" for e
  proof -
    define S where "S = exp (- l * T) + (\<Sum> j = 1..<N. ?c j)"
    have S0: "0 \<le> S"
      unfolding S_def by (intro add_nonneg_nonneg sum_nonneg cj0) simp
    define e' where "e' = e / (S + 1)"
    have e': "0 < e'"
      unfolding e'_def using e S0 by simp
    have massT: "(\<lambda>i. measure (\<Lambda>i i) (space (\<Lambda>i i)))
        \<longlonglongrightarrow> measure \<Lambda> (space \<Lambda>)"
      by (rule weak_conv_total_mass[OF wc])
    have evm: "\<forall>\<^sub>F i in sequentially.
        measure \<Lambda> (space \<Lambda>) - e' < measure (\<Lambda>i i) (space (\<Lambda>i i))"
      by (rule order_tendstoD[OF massT]) (use e' in simp)
    have evU: "\<forall>\<^sub>F i in sequentially.
        measure \<Lambda> (?U j) - e' < measure (\<Lambda>i i) (?U j)" for j
    proof -
      have "ereal (measure \<Lambda> (?U j))
          \<le> Liminf sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) (?U j)))"
        by (rule weak_conv_open_liminf[OF wc
            pexit_sublevel_open[OF T K]])
      moreover have "ereal (measure \<Lambda> (?U j) - e')
          < ereal (measure \<Lambda> (?U j))"
        using e' by simp
      ultimately have "ereal (measure \<Lambda> (?U j) - e')
          < Liminf sequentially (\<lambda>i. ereal (measure (\<Lambda>i i) (?U j)))"
        by order
      then have "\<forall>\<^sub>F i in sequentially. ereal (measure \<Lambda> (?U j) - e')
          < ereal (measure (\<Lambda>i i) (?U j))"
        using le_Liminf_iff[THEN iffD1, OF order_refl] by blast
      then show ?thesis
        by (simp add: eventually_mono)
    qed
    have evS: "\<forall>\<^sub>F i in sequentially.
        sets (\<Lambda>i i) = sets (borel_of (mtopology_of ?m))
        \<and> finite_measure (\<Lambda>i i)"
      using wc' by blast
    have evAll: "\<forall>\<^sub>F i in sequentially.
        \<forall>j \<in> {1..<N}. measure \<Lambda> (?U j) - e' < measure (\<Lambda>i i) (?U j)"
      by (rule eventually_ball_finite) (auto intro: evU)
    have main: "\<forall>\<^sub>F i in sequentially.
        ereal ((\<integral>f. pstep T K l N f \<partial>\<Lambda>) - e)
        \<le> ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i))"
      using evm evAll evS
    proof (eventually_elim)
      case (elim i)
      have deci: "(\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i))
          = exp (- l * T) * measure (\<Lambda>i i) (space (\<Lambda>i i))
            + (\<Sum> j = 1..<N. ?c j * measure (\<Lambda>i i) (?U j))"
        using elim by (intro pstep_integral[OF T K]) auto
      have t0: "exp (- l * T) * (measure \<Lambda> (space \<Lambda>) - e')
          \<le> exp (- l * T) * measure (\<Lambda>i i) (space (\<Lambda>i i))"
        by (intro mult_left_mono c0) (use elim in auto)
      have tj: "?c j * (measure \<Lambda> (?U j) - e')
          \<le> ?c j * measure (\<Lambda>i i) (?U j)"
        if j: "j \<in> {1..<N}" for j
      proof -
        have "measure \<Lambda> (?U j) - e' < measure (\<Lambda>i i) (?U j)"
          using elim(2) j by blast
        then show ?thesis
          by (intro mult_left_mono cj0) simp
      qed
      have "(\<integral>f. pstep T K l N f \<partial>\<Lambda>) - S * e'
          = exp (- l * T) * (measure \<Lambda> (space \<Lambda>) - e')
            + (\<Sum> j = 1..<N. ?c j * (measure \<Lambda> (?U j) - e'))"
        unfolding dec\<Lambda> S_def
        by (simp add: algebra_simps sum.distrib sum_distrib_left
            sum_distrib_right sum_subtractf)
      also have "\<dots> \<le> exp (- l * T) * measure (\<Lambda>i i) (space (\<Lambda>i i))
          + (\<Sum> j = 1..<N. ?c j * measure (\<Lambda>i i) (?U j))"
        by (intro add_mono t0 sum_mono tj)
      also have "\<dots> = (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i))"
        by (rule deci[symmetric])
      finally have le1: "(\<integral>f. pstep T K l N f \<partial>\<Lambda>) - S * e'
          \<le> (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i))" .
      have "S * e' \<le> e"
        unfolding e'_def using S0 e
        by (simp add: divide_le_eq mult_left_mono field_simps)
      with le1 show ?case by simp
    qed
    show ?thesis
      by (intro Liminf_bounded main)
  qed
  show ?thesis
  proof (rule ereal_le_epsilon2)
    fix e :: real assume e: "0 < e"
    have "ereal ((\<integral>f. pstep T K l N f \<partial>\<Lambda>) - e)
        \<le> Liminf sequentially (\<lambda>i. ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i)))"
      by (rule eps[OF e])
    then show "ereal (\<integral>f. pstep T K l N f \<partial>\<Lambda>)
        \<le> Liminf sequentially
          (\<lambda>i. ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i))) + ereal e"
      by (cases "Liminf sequentially
          (\<lambda>i. ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i)))") auto
  qed
qed

lemma pstep_integrable:
  fixes K :: "('b :: polish_space) set" and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and K: "closed K"
    and s\<Lambda>: "sets \<Lambda> = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and fin: "finite_measure \<Lambda>"
  shows "integrable \<Lambda> (pstep T K l N)"
proof -
  interpret finite_measure \<Lambda> by fact
  have memj: "{g. pexit T K g < real j * T / real N} \<inter> space \<Lambda>
      \<in> sets \<Lambda>" for j
  proof -
    have sp\<Lambda>: "space \<Lambda> = mspace (path_metric T)"
      using sets_eq_imp_space_eq[OF s\<Lambda>]
      by (simp add: space_borel_of)
    have eq: "{g. pexit T K g < real j * T / real N} \<inter> space \<Lambda>
        = {f \<in> mspace (path_metric T).
            pexit T K f < real j * T / real N}"
      unfolding sp\<Lambda> by auto
    have "{f \<in> mspace (path_metric T).
        pexit T K f < real j * T / real N}
        \<in> sets (path_borel T)"
      by (intro borel_of_open pexit_sublevel_open[OF T K])
    then show ?thesis
      unfolding eq s\<Lambda> .
  qed
  have int_ind: "integrable \<Lambda>
      (\<lambda>f. indicat_real {g. pexit T K g < real j * T / real N} f)"
    for j
    using memj[of j]
    by (auto simp: integrable_indicator_iff emeasure_eq_measure)
  show ?thesis
    unfolding pstep_def
    by (intro Bochner_Integration.integrable_add integrable_const
        Bochner_Integration.integrable_sum integrable_mult_right
        int_ind)
qed

lemma exp_pexit_integral_liminf:
  fixes K :: "('b :: polish_space) set"
    and \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure" and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 < T" and K: "closed K" and l: "0 < l"
    and wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
  shows "ereal (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)
      \<le> Liminf sequentially
        (\<lambda>i. ereal (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i)))"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  let ?E = "\<lambda>M. (\<integral>f. exp (- l * pexit T K f) \<partial>M)"
  let ?L = "Liminf sequentially
      (\<lambda>i. ereal (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i)))"
  have T0: "0 \<le> T" using T by simp
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)) \<and> finite_measure (\<Lambda>i i))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>"
    using wc unfolding weak_conv_on_def by blast
  have exp_int: "integrable M (\<lambda>f. exp (- l * pexit T K f))"
    if s: "sets M = sets (borel_of (mtopology_of ?m))"
      and f: "finite_measure M" for M
  proof -
    interpret finite_measure M by fact
    have p: "pexit T K \<in> borel_measurable M"
      using pexit_measurable[OF T0 K] s
      by (metis measurable_cong_sets)
    have m: "(\<lambda>f. exp (- l * pexit T K f)) \<in> borel_measurable M"
      using p by measurable
    have b: "norm (exp (- l * pexit T K f)) \<le> 1" for f
      using pexit_nonneg[OF T0, of K f] l
      by simp
    show ?thesis
      by (rule integrable_const_bound[where B = 1])
        (use m b in \<open>auto\<close>)
  qed
  have key: "ereal (?E \<Lambda> - (1 - exp (- l * (T / real N)))
      * measure \<Lambda> (space \<Lambda>)) \<le> ?L" if N: "0 < N" for N
  proof -
    have sand: "pstep T K l N f \<le> exp (- l * pexit T K f)
        \<and> exp (- l * pexit T K f)
          \<le> pstep T K l N f + (1 - exp (- l * (T / real N)))" for f
      by (rule pstep_sandwich[OF T l N])
    have int_pstep: "integrable \<Lambda> (pstep T K l N)"
      using wc' by (intro pstep_integrable[OF T0 K]) auto
    have int_e: "integrable \<Lambda> (\<lambda>f. exp (- l * pexit T K f))"
      using wc' by (intro exp_int) auto
    have fm\<Lambda>: "finite_measure \<Lambda>" using wc' by blast
    have up: "?E \<Lambda> \<le> (\<integral>f. pstep T K l N f \<partial>\<Lambda>)
        + (1 - exp (- l * (T / real N))) * measure \<Lambda> (space \<Lambda>)"
    proof -
      have "?E \<Lambda> \<le> (\<integral>f. pstep T K l N f
          + (1 - exp (- l * (T / real N))) \<partial>\<Lambda>)"
        by (intro Bochner_Integration.integral_mono int_e
            Bochner_Integration.integrable_add int_pstep
            finite_measure.integrable_const[OF fm\<Lambda>])
          (use sand in simp)
      also have "\<dots> = (\<integral>f. pstep T K l N f \<partial>\<Lambda>)
          + (1 - exp (- l * (T / real N))) * measure \<Lambda> (space \<Lambda>)"
        by (subst Bochner_Integration.integral_add
            [OF int_pstep finite_measure.integrable_const[OF fm\<Lambda>]])
          (simp add: mult.commute)
      finally show ?thesis .
    qed
    have lo: "\<forall>\<^sub>F i in sequentially.
        ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i))
        \<le> ereal (?E (\<Lambda>i i))"
      using wc'[THEN conjunct1]
    proof (eventually_elim)
      case (elim i)
      have i1: "integrable (\<Lambda>i i) (pstep T K l N)"
        using elim by (intro pstep_integrable[OF T0 K]) auto
      have i2: "integrable (\<Lambda>i i) (\<lambda>f. exp (- l * pexit T K f))"
        using elim by (intro exp_int) auto
      show ?case
        by (intro ereal_less_eq(3)[THEN iffD2]
            Bochner_Integration.integral_mono i1 i2)
          (use sand in simp)
    qed
    have "ereal (?E \<Lambda> - (1 - exp (- l * (T / real N)))
        * measure \<Lambda> (space \<Lambda>)) \<le> ereal (\<integral>f. pstep T K l N f \<partial>\<Lambda>)"
      using up by simp
    also have "\<dots> \<le> Liminf sequentially
        (\<lambda>i. ereal (\<integral>f. pstep T K l N f \<partial>(\<Lambda>i i)))"
      by (rule pstep_integral_liminf[OF T0 K less_imp_le[OF l] wc])
    also have "\<dots> \<le> ?L"
      by (rule Liminf_mono[OF lo])
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases ?L)
    case (real r)
    have Nbound: "?E \<Lambda> - (1 - exp (- l * (T / real N)))
        * measure \<Lambda> (space \<Lambda>) \<le> r" if N: "0 < N" for N
      using key[OF N] real by simp
    have errlim: "(\<lambda>N. ?E \<Lambda> - (1 - exp (- l * (T / real N)))
        * measure \<Lambda> (space \<Lambda>)) \<longlonglongrightarrow> ?E \<Lambda>"
    proof -
      have "(\<lambda>N. T * (1 / real N)) \<longlonglongrightarrow> T * 0"
        by (intro tendsto_mult tendsto_const lim_1_over_n)
      then have "(\<lambda>N. T / real N) \<longlonglongrightarrow> 0" by simp
      then have "(\<lambda>N. exp (- l * (T / real N))) \<longlonglongrightarrow> exp (- l * 0)"
        by (intro tendsto_intros)
      then have z: "(\<lambda>N. (1 - exp (- l * (T / real N)))
          * measure \<Lambda> (space \<Lambda>)) \<longlonglongrightarrow> (1 - exp (- l * 0))
          * measure \<Lambda> (space \<Lambda>)"
        by (intro tendsto_intros)
      have "(\<lambda>N. ?E \<Lambda> - (1 - exp (- l * (T / real N)))
          * measure \<Lambda> (space \<Lambda>)) \<longlonglongrightarrow> ?E \<Lambda> - (1 - exp (- l * 0))
          * measure \<Lambda> (space \<Lambda>)"
        by (intro tendsto_diff tendsto_const z)
      then show ?thesis by simp
    qed
    have "?E \<Lambda> \<le> r"
      by (intro LIMSEQ_le_const2[OF errlim])
        (metis Nbound Suc_le_eq)
    then show ?thesis using real by simp
  next
    case PInf
    then show ?thesis by simp
  next
    case MInf
    have "ereal (?E \<Lambda> - (1 - exp (- l * (T / real 1)))
        * measure \<Lambda> (space \<Lambda>)) \<le> ?L"
      by (rule key) simp
    then show ?thesis using MInf by simp
  qed
qed

section \<open>Upper semicontinuity of the essential infimum of the exit time\<close>

theorem ess_inf_pexit_usc:
  fixes K :: "('b :: polish_space) set"
    and \<Lambda>i :: "nat \<Rightarrow> (real \<Rightarrow> 'b) measure" and \<Lambda> :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 < T" and K: "closed K"
    and wc: "weak_conv_on \<Lambda>i \<Lambda> sequentially
      (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))"
    and probs: "\<And>i. prob_space (\<Lambda>i i)" and prob: "prob_space \<Lambda>"
  shows "Limsup sequentially (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
      \<le> ess_inf_time \<Lambda> (pexit T K)"
proof -
  let ?m = "path_metric T :: (real \<Rightarrow> 'b) metric"
  have T0: "0 \<le> T" using T by simp
  have wc': "(\<forall>\<^sub>F i in sequentially. sets (\<Lambda>i i)
        = sets (borel_of (mtopology_of ?m)) \<and> finite_measure (\<Lambda>i i))
      \<and> sets \<Lambda> = sets (borel_of (mtopology_of ?m)) \<and> finite_measure \<Lambda>"
    using wc unfolding weak_conv_on_def by blast
  have pm: "pexit T K \<in> borel_measurable M"
    if s: "sets M = sets (borel_of (mtopology_of ?m))"
    for M :: "(real \<Rightarrow> 'b) measure"
    using pexit_measurable[OF T0 K] s
    by (metis measurable_cong_sets)
  have pm\<Lambda>: "pexit T K \<in> borel_measurable \<Lambda>"
    using wc' by (intro pm) blast
  have Epos\<Lambda>: "0 < (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)"
    if l: "0 < l" for l
  proof -
    have "(0 :: real) < exp (- l * T)" by simp
    also have "\<dots> \<le> (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)"
      by (rule exp_neg_time_integral_lower[OF prob pm\<Lambda>
          pexit_nonneg[OF T0] pexit_le_T[OF T0]
          less_imp_le[OF l]])
    finally show ?thesis .
  qed
  have Ele1\<Lambda>: "(\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) \<le> 1"
    if l: "0 < l" for l
  proof -
    interpret prob_space \<Lambda> by fact
    have "(\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) \<le> (\<integral>f. 1 \<partial>\<Lambda>)"
      by (intro Bochner_Integration.integral_mono integrable_const
          exp_neg_time_integrable[OF prob pm\<Lambda>
            pexit_nonneg[OF T0] less_imp_le[OF l]])
        (use pexit_nonneg[OF T0] l in
          \<open>auto intro!: mult_nonneg_nonneg\<close>)
    then show ?thesis by (simp add: prob_space)
  qed
  have flnn: "0 \<le> - (1 / l) * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)"
    if l: "0 < l" for l
  proof -
    have "ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) \<le> ln 1"
      using Epos\<Lambda>[OF l] Ele1\<Lambda>[OF l]
      by simp
    then have "ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) \<le> 0" by simp
    then show ?thesis
      using l by (simp add: divide_nonpos_pos)
  qed
  have step: "Limsup sequentially
      (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
      \<le> ennreal (- (1 / l) * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + \<epsilon>)"
    if l: "0 < l" and \<epsilon>: "0 < \<epsilon>" for l \<epsilon>
  proof -
    have lower: "ereal (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)
        \<le> Liminf sequentially
          (\<lambda>i. ereal (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i)))"
      by (rule exp_pexit_integral_liminf[OF T K l wc])
    have shrink: "(\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) * exp (- l * \<epsilon>)
        < (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)"
    proof -
      have "exp (- l * \<epsilon>) < 1"
        using l \<epsilon> by simp
      then show ?thesis
        using Epos\<Lambda>[OF l] by (simp add: mult_less_cancel_left)
    qed
    have evE: "\<forall>\<^sub>F i in sequentially.
        (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) * exp (- l * \<epsilon>)
        < (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))"
    proof -
      have "ereal ((\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) * exp (- l * \<epsilon>))
          < Liminf sequentially
            (\<lambda>i. ereal (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i)))"
        by (rule less_le_trans[OF _ lower]) (use shrink in simp)
      then have "\<forall>\<^sub>F i in sequentially.
          ereal ((\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) * exp (- l * \<epsilon>))
          < ereal (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))"
        using le_Liminf_iff[THEN iffD1, OF order_refl] by blast
      then show ?thesis
        by (simp add: eventually_mono)
    qed
    have main: "\<forall>\<^sub>F i in sequentially.
        ess_inf_time (\<Lambda>i i) (pexit T K)
        \<le> ennreal (- (1 / l)
          * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + \<epsilon>)"
      using evE wc'[THEN conjunct1]
    proof (eventually_elim)
      case (elim i)
      have si: "sets (\<Lambda>i i) = sets (borel_of (mtopology_of ?m))"
        and fi: "finite_measure (\<Lambda>i i)"
        using elim by auto
      have pmi: "pexit T K \<in> borel_measurable (\<Lambda>i i)"
        by (rule pm[OF si])
      have L1i: "ess_inf_time (\<Lambda>i i) (pexit T K)
          \<le> ennreal (- (1 / l)
            * ln (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i)))"
        by (rule ess_inf_time_le_laplace[OF probs pmi
            pexit_nonneg[OF T0] pexit_le_T[OF T0] l])
      have pos_i: "0 < (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))"
      proof -
        have "(0 :: real)
            < (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) * exp (- l * \<epsilon>)"
          using Epos\<Lambda>[OF l] by simp
        also have "\<dots> < (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))"
          by (rule elim(1))
        finally show ?thesis .
      qed
      have lnb: "ln ((\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)
          * exp (- l * \<epsilon>))
          \<le> ln (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))"
        using elim(1) pos_i Epos\<Lambda>[OF l]
        by (subst ln_le_cancel_iff) auto
      have lnsplit: "ln ((\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)
          * exp (- l * \<epsilon>))
          = ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + (- l * \<epsilon>)"
        using Epos\<Lambda>[OF l] by (simp add: ln_mult)
      have "- (1 / l) * ln (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))
          \<le> - (1 / l) * (ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)
            + (- l * \<epsilon>))"
        using lnb lnsplit l
        by (intro mult_left_mono_neg) auto
      also have "\<dots> = - (1 / l)
          * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + \<epsilon>"
        using l by (simp add: field_simps)
      finally have "- (1 / l)
          * ln (\<integral>f. exp (- l * pexit T K f) \<partial>(\<Lambda>i i))
          \<le> - (1 / l) * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + \<epsilon>" .
      then show ?case
        using L1i by (meson ennreal_leI order_trans)
    qed
    show ?thesis
      by (intro Limsup_bounded main)
  qed
  have perl: "Limsup sequentially
      (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
      \<le> ennreal (- (1 / l) * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>))"
    if l: "0 < l" for l
  proof (rule ennreal_le_epsilon)
    fix \<epsilon> :: real
    assume "ennreal (- (1 / l)
        * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)) < \<top>"
      and \<epsilon>: "0 < \<epsilon>"
    have "Limsup sequentially (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
        \<le> ennreal (- (1 / l)
          * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + \<epsilon>)"
      by (rule step[OF l \<epsilon>])
    also have "ennreal (- (1 / l)
        * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>) + \<epsilon>)
        = ennreal (- (1 / l)
          * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)) + ennreal \<epsilon>"
      using flnn[OF l] less_imp_le[OF \<epsilon>] by (rule ennreal_plus)
    finally show "Limsup sequentially
        (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
        \<le> ennreal (- (1 / l)
          * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)) + ennreal \<epsilon>" .
  qed
  have "Limsup sequentially (\<lambda>i. ess_inf_time (\<Lambda>i i) (pexit T K))
      \<le> (INF l \<in> {0<..}. ennreal (- (1 / l)
        * ln (\<integral>f. exp (- l * pexit T K f) \<partial>\<Lambda>)))"
    by (intro INF_greatest perl) auto
  also have "\<dots> = ess_inf_time \<Lambda> (pexit T K)"
    by (rule ess_inf_time_eq_laplace_inf[OF prob pm\<Lambda>
        pexit_nonneg[OF T0] pexit_le_T[OF T0]])
  finally show ?thesis .
qed


section \<open>Shifted exit times, confinement, and test functionals\<close>

lemma open_etime_shift_less:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
  shows "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         etime T A (\<lambda>s w. y + w s) f < d}"
proof -
  have eq: "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
        etime T A (\<lambda>s w. y + w s) f < d}
      = (\<Union>r \<in> {r \<in> qtimes T. r < d}.
           {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). y + f r \<in> A})"
  proof -
    have "etime T A (\<lambda>s w. y + w s) f < d
        \<longleftrightarrow> (\<exists>r \<in> {r \<in> qtimes T. r < d}. y + f r \<in> A)"
      if w: "f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" for f
    proof -
      have cont: "continuous_on {0..T} (\<lambda>s. y + f s)"
        by (intro continuous_intros mspace_path_metricD[OF w])
      have e: "etime T A (\<lambda>s w. y + w s) f = etime T A (\<lambda>s w'. y + f s) f"
        unfolding etime_def by simp
      show ?thesis unfolding e
        using etime_less_iff_qtimes_open[OF T A dT cont, of f] by auto
    qed
    thus ?thesis by blast
  qed
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). y + f r \<in> A}"
    if r: "r \<in> {r \<in> qtimes T. r < d}" for r
  proof -
    have "r \<in> qtimes T" using r by simp
    hence rT: "r \<in> {0..T}" using qtimes_subset[OF T] by blast
    show ?thesis by (rule open_shifted_eval_preimage[OF rT A])
  qed
  show ?thesis unfolding eq by (rule openin_Union) (use op in blast)
qed

subsection \<open>Berge's box hypothesis for the shifted exit time\<close>

text \<open>
  Both perturbations at once, in the sequential form Levy--Prokhorov
  metrisation makes equivalent to the topological one: \<open>f(x,P) < d\<close>
  persists when the starting point moves to any \<open>y\<^sub>i \<rightarrow> x\<close> and the law
  moves to any \<open>Q\<^sub>i \<rightarrow> P\<close> weakly.

  Larsson--Ruf get this from continuity of \<open>(x,P) \<mapsto> (x + \<cdot>)\<^sub>*P\<close>; no
  such theorem is used here. A single open set \<open>G\<close> does all the work --- the
  erosion makes it survive moving \<open>x\<close>, its openness makes it survive
  moving \<open>P\<close> --- and must be open rather than closed, since a closed eroded
  set would give the wrong Portmanteau direction.
\<close>

lemma past_test_functional_cont:
  fixes h :: "(real \<Rightarrow> real^'m::finite) \<Rightarrow> real"
  assumes st: "0 \<le> s" and sT: "s \<le> T"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal (\<lambda>f. h (restrict f {0..s}))"
proof -
  have rc: "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric))
      (\<lambda>f. restrict f {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal (h \<circ> (\<lambda>f. restrict f {0..s}))"
    by (rule continuous_map_compose[OF rc hc])
  then show ?thesis by (simp add: o_def)
qed

text \<open>The exit time from \<open>K\<close> is the increasing limit of the capped exit times.
  It takes the value \<open>\<top>\<close> exactly on the paths that never leave \<open>K\<close>.\<close>

definition iexit :: "'b::polish_space set \<Rightarrow> (real \<Rightarrow> 'b) \<Rightarrow> ennreal" where
  "iexit K f = (SUP T \<in> {0..}. ennreal (pexit T K f))"

lemma pexit_le_iexit:
  assumes T: "0 \<le> T"
  shows "ennreal (pexit T K f) \<le> iexit K f"
  unfolding iexit_def using T by (intro SUP_upper) simp

text \<open>Hence the elementary bound identifying \<open>iexit\<close> as the first time the
  path is outside \<open>K\<close>.\<close>

subsection \<open>The essential infimum of an unbounded time\<close>

lemma pexit_cong_nonneg:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> f s = g s" and T: "0 \<le> T"
  shows "pexit T K f = pexit T K g"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K} = {r. 0 \<le> r \<and> r \<le> T \<and> g r \<in> - K}"
    using eq by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma iexit_cong_nonneg:
  assumes eq: "\<And>s. 0 \<le> s \<Longrightarrow> f s = g s"
  shows "iexit K f = iexit K g"
  unfolding iexit_def by (intro SUP_cong refl) (use pexit_cong_nonneg[OF eq] in auto)

lemma pexit_restrict [simp]: "pexit T K (restrict f {0..T}) = pexit T K f"
proof -
  have "{r. 0 \<le> r \<and> r \<le> T \<and> restrict f {0..T} r \<in> - K}
      = {r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K}" by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

lemma iexit_nat_sup: "iexit K f = (SUP n :: nat. ennreal (pexit (real n) K f))"
proof (rule antisym)
  show "iexit K f \<le> (SUP n :: nat. ennreal (pexit (real n) K f))"
    unfolding iexit_def
  proof (rule SUP_least)
    fix T :: real assume "T \<in> {0..}"
    then have T: "0 \<le> T" by simp
    obtain n :: nat where n: "T < real n" using reals_Archimedean2 by blast
    have "pexit T K f \<le> pexit (real n) K f"
      by (rule pexit_mono_T[OF T]) (use n in simp)
    then have "ennreal (pexit T K f) \<le> ennreal (pexit (real n) K f)"
      by (rule ennreal_leI)
    also have "\<dots> \<le> (SUP n :: nat. ennreal (pexit (real n) K f))"
      by (rule SUP_upper) simp
    finally show "ennreal (pexit T K f) \<le> (SUP n :: nat. ennreal (pexit (real n) K f))" .
  qed
  show "(SUP n :: nat. ennreal (pexit (real n) K f)) \<le> iexit K f"
    by (rule SUP_least) (auto intro: pexit_le_iexit)
qed

lemma iexit_measurable_gen:
  fixes K :: "('b::polish_space) set" and N :: "'a measure"
  assumes K: "closed K"
    and Ym: "\<And>t. 0 \<le> t \<Longrightarrow> Y t \<in> borel_measurable N"
    and cont: "\<And>\<omega>. \<omega> \<in> space N \<Longrightarrow> continuous_on {0..} (\<lambda>t. Y t \<omega>)"
  shows "(\<lambda>\<omega>. iexit K (\<lambda>t. Y t \<omega>)) \<in> borel_measurable N"
proof -
  have step: "(\<lambda>\<omega>. ennreal (pexit T K (\<lambda>t. Y t \<omega>))) \<in> borel_measurable N"
    if T: "0 \<le> T" for T
  proof -
    have p: "(\<lambda>\<omega>. restrict (\<lambda>t. Y t \<omega>) {0..T})
        \<in> N \<rightarrow>\<^sub>M (path_borel T :: (real \<Rightarrow> 'b) measure)"
    proof (rule pathify_measurable[OF T])
      fix t assume "t \<in> {0..T}"
      then show "Y t \<in> borel_measurable N" by (intro Ym) simp
    next
      fix \<omega> assume "\<omega> \<in> space N"
      from cont[OF this] show "continuous_on {0..T} (\<lambda>t. Y t \<omega>)"
        by (rule continuous_on_subset) auto
    qed
    have "(\<lambda>\<omega>. pexit T K (restrict (\<lambda>t. Y t \<omega>) {0..T})) \<in> borel_measurable N"
      by (rule measurable_compose[OF p pexit_measurable[OF T K]])
    then show ?thesis by simp
  qed
  have "(\<lambda>\<omega>. SUP n :: nat. ennreal (pexit (real n) K (\<lambda>t. Y t \<omega>)))
      \<in> borel_measurable N"
    by (intro borel_measurable_SUP[where I = UNIV]) (use step in auto)
  then show ?thesis by (simp add: iexit_nat_sup)
qed

lemma iexit_measurable_ipath:
  fixes K :: "('b::polish_space) set"
  assumes K: "closed K"
  shows "iexit K \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
proof -
  have "(\<lambda>w :: real \<Rightarrow> 'b. iexit K (\<lambda>t. w t))
      \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
  proof (rule iexit_measurable_gen[OF K])
    show "\<And>t. 0 \<le> t \<Longrightarrow> (\<lambda>w :: real \<Rightarrow> 'b. w t)
        \<in> borel_measurable (ipath_space :: ((real \<Rightarrow> 'b) measure))"
      by (rule ipath_eval_measurable)
  next
    fix w :: "real \<Rightarrow> 'b" assume "w \<in> space (ipath_space :: ((real \<Rightarrow> 'b) measure))"
    then show "continuous_on {0..} (\<lambda>t. w t)"
      by (intro ipath_continuous_on) auto
  qed
  then show ?thesis by simp
qed

text \<open>On the survival event the exit time splits exactly: the first piece
  contributes \<open>r\<close> and the rest is the exit time of the time-shifted path
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

lemma pexit_surv_of_less:
  fixes f :: "real \<Rightarrow> 'a::polish_space" and K :: "'a set"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" and rT: "r \<le> T" and lt: "r < c"
    and ge: "c \<le> pexit T K f"
  shows "pexit r K f = r \<and> f r \<in> K"
proof -
  have stay: "f t \<in> K" if t: "t \<in> {0..r}" for t
  proof (rule ccontr)
    assume nk: "f t \<notin> K"
    have "pexit T K f \<le> t"
      unfolding pexit_def using T0 t rT nk by (intro etime_le_of_mem) auto
    moreover have "t \<le> r" using t by simp
    ultimately show False using ge lt by simp
  qed
  have empt: "{t. 0 \<le> t \<and> t \<le> r \<and> f t \<in> - K} \<union> {r} = {r}" using stay by auto
  have "pexit r K f = r" unfolding pexit_def etime_def empt by simp
  moreover have "f r \<in> K" using stay r by simp
  ultimately show ?thesis by simp
qed

text \<open>The pointwise core: at a single path, the deterministic bound at
  countably many rational times below \<open>c\<close> gives the bound at an arbitrary
  time \<open>s\<close>, with no measure theory at all.\<close>

lemma pexit_cong_on:
  assumes "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> U \<Longrightarrow> f t = g t"
  shows "pexit U K f = pexit U K g"
proof -
  have "{t. 0 \<le> t \<and> t \<le> U \<and> f t \<in> - K} = {t. 0 \<le> t \<and> t \<le> U \<and> g t \<in> - K}"
    using assms by auto
  then show ?thesis unfolding pexit_def etime_def by simp
qed

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

text \<open>\<open>ess_inf_time_mono\<close> lives in \<open>Value_Function_Market\<close>,
  with an almost-sure rather than a pointwise hypothesis; this theory had a
  pointwise copy that shadowed it.\<close>

text \<open>Capping the integrand by a constant caps the essential infimum by the
  same constant.  Both halves are elementary, but the \<open>\<ge>\<close> half has to be
  run through \<open>ennreal_strict_between\<close>: the defining
  supremum need not be attained.\<close>

lemma positive_mass_at_some_qtime:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and P :: "(real \<Rightarrow> 'b) measure" and x :: 'b
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d"
    and sP: "sets P = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pos: "emeasure P
        {\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d} \<noteq> 0"
  shows "\<exists>r \<in> qtimes T. r < d
      \<and> emeasure P {\<omega> \<in> space P. x + \<omega> r \<in> A} \<noteq> 0"
proof -
  have spP: "space P = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sP] by (simp add: space_borel_of)
  define R where "R = {r \<in> qtimes T. r < d}"
  have cR: "countable R" unfolding R_def using countable_qtimes by simp

  text \<open>The pointwise reduction, applied path by path. Continuity of the shifted
    path is what \<open>mspace_path_metricD\<close> supplies.\<close>
  have ptw: "etime T A (\<lambda>s w. x + w s) \<omega> < d
      \<longleftrightarrow> (\<exists>r \<in> R. x + \<omega> r \<in> A)"
    if w: "\<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric)" for \<omega>
  proof -
    have cont: "continuous_on {0..T} (\<lambda>s. x + \<omega> s)"
      by (intro continuous_intros mspace_path_metricD[OF w])
    text \<open>\<open>etime\<close> applies its process only to the one path \<open>\<omega>\<close>, so freezing
      the path inside the process changes nothing mathematically, but the
      reduction lemma is stated for a frozen process.\<close>
    have eq: "etime T A (\<lambda>s w. x + w s) \<omega> = etime T A (\<lambda>s w'. x + \<omega> s) \<omega>"
      unfolding etime_def by simp
    show ?thesis
      unfolding eq R_def
      using etime_less_iff_qtimes_open[OF T A dT cont, of \<omega>] by auto
  qed
  have split: "{\<omega> \<in> space P. etime T A (\<lambda>s w. x + w s) \<omega> < d}
      = (\<Union>r \<in> R. {\<omega> \<in> space P. x + \<omega> r \<in> A})"
    using ptw unfolding spP by blast

  text \<open>Measurability of each slice comes from openness of the shifted evaluation
    preimage, exactly as in \<open>etime_shift_uniform_margin\<close>.\<close>
  have meas: "{\<omega> \<in> space P. x + \<omega> r \<in> A} \<in> sets P" if r: "r \<in> R" for r
  proof -
    have "r \<in> qtimes T" using r unfolding R_def by simp
    hence rT: "r \<in> {0..T}" using qtimes_subset[OF T] by blast
    have "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric). x + f r \<in> A}"
      by (rule open_shifted_eval_preimage[OF rT A])
    from borel_of_open[OF this] show ?thesis unfolding sP spP by simp
  qed
  have "emeasure P (\<Union>r \<in> R. {\<omega> \<in> space P. x + \<omega> r \<in> A}) \<noteq> 0"
    using pos unfolding split .
  from positive_of_countable_UN[OF cR meas this] show ?thesis
    unfolding R_def by blast
qed

text \<open>Both halves of the \<open>x\<close>-perturbation in one statement: from
  \<open>f(x,P) < d\<close> alone, with no continuity of the pushforward map, there is
  an open set of paths of positive \<open>P\<close>-mass on which the exit time stays
  below \<open>d\<close> for every starting point within \<open>\<delta>\<close> of \<open>x\<close>.\<close>

definition vshift :: "real \<Rightarrow> 'b::{polish_space,real_normed_vector} set
    \<Rightarrow> 'b \<Rightarrow> (real \<Rightarrow> 'b) measure \<Rightarrow> real" where
  "vshift T A y Q = enn2real (ess_inf_time Q (etime T A (\<lambda>s w. y + w s)))"

lemma vshift_le:
  fixes A :: "'b::{polish_space,real_normed_vector} set"
  assumes T: "0 \<le> T" and Q: "prob_space Q"
  shows "vshift T A y Q \<le> T"
proof -
  have "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF Q]) (rule etime_le_T[OF T])
  from enn2real_mono[OF this] show ?thesis
    unfolding vshift_def using T by simp
qed

text \<open>The bridge from the real-valued functional back to the positive-mass
  statement. Both directions of the \<open>ennreal\<close> conversion need the ceiling:
  without it \<open>enn2real\<close> could collapse \<open>\<top>\<close> to \<open>0\<close> and the strict inequality
  would be an artefact.\<close>

lemma vshift_less_iff_positive_mass:
  fixes T d :: real and A :: "'b::{polish_space,real_normed_vector} set"
    and Q :: "(real \<Rightarrow> 'b) measure"
  assumes T: "0 \<le> T" and A: "open A" and dT: "\<not> T < d" and d0: "0 \<le> d"
    and sQ: "sets Q = sets (path_borel T :: (real \<Rightarrow> 'b) measure)"
    and pQ: "prob_space Q"
  shows "vshift T A y Q < d
      \<longleftrightarrow> emeasure Q {\<omega> \<in> space Q. etime T A (\<lambda>s w. y + w s) \<omega> < d} \<noteq> 0"
proof -
  have spQ: "space Q = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    using sets_eq_imp_space_eq[OF sQ] by (simp add: space_borel_of)
  have setseq: "{\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d}
      = {\<omega> \<in> space Q. etime T A (\<lambda>s w. y + w s) \<omega> < d}"
    using etime_nonneg[OF T, of A "\<lambda>s w. y + w s"]
    by (auto simp: ennreal_less_iff)
  have meas: "{\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d}
      \<in> sets Q"
    unfolding setseq
    using borel_of_open[OF open_etime_shift_less[OF T A dT]]
    unfolding sQ spQ by simp
  have le: "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF pQ]) (rule etime_le_T[OF T])
  have fin: "ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) < \<top>"
    using le ennreal_less_top by (rule order_le_less_trans)
  have "vshift T A y Q < d
      \<longleftrightarrow> ennreal (vshift T A y Q) < ennreal d"
    unfolding vshift_def by (simp add: ennreal_less_iff)
  also have "\<dots> \<longleftrightarrow> ess_inf_time Q (etime T A (\<lambda>s w. y + w s)) < ennreal d"
    unfolding vshift_def by (simp add: ennreal_enn2real[OF fin])
  also have "\<dots> \<longleftrightarrow> emeasure Q
      {\<omega> \<in> space Q. ennreal (etime T A (\<lambda>s w. y + w s) \<omega>) < ennreal d} \<noteq> 0"
    by (rule ess_inf_time_less_iff[OF meas])
  finally show ?thesis unfolding setseq .
qed

text \<open>
  Granted Lemma 2.3, this gives clause (1) of Theorem 1.1: the supremum
  of \<open>P \<mapsto> P\<hyphen>essinf \<tau>\<^sub>K(x + \<cdot>)\<close> over a weakly compact family of laws is
  upper semicontinuous in the starting point \<open>x\<close>. Every other hypothesis
  of Berge is discharged here; compactness of the family is Lemma 2.3.
\<close>

lemma etime_shift_superlevel_closed:
  fixes T :: real and c :: ennreal
    and A :: "'b::{polish_space,real_normed_vector} set" and y :: 'b
  assumes T: "0 \<le> T" and A: "open A"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         c \<le> ennreal (etime T A (\<lambda>s w. y + w s) f)}"
proof -
  have op: "openin (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
      {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
         ennreal (etime T A (\<lambda>s w. y + w s) f) < c}"
  proof (cases "ennreal T < c")
    text \<open>One split, on whether the threshold is beyond the cap, rather than the
      two that \<open>ennreal_cases\<close> would give: above the cap every path qualifies,
      and below it the threshold is automatically a real \<open>r\<close> with \<open>\<not> T < r\<close>,
      which is exactly the hypothesis \<open>open_etime_shift_less\<close> wants.\<close>
    case True
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
          ennreal (etime T A (\<lambda>s w. y + w s) f) < c}
        = mspace (path_metric T :: (real \<Rightarrow> 'b) metric)"
    proof -
      have "ennreal (etime T A (\<lambda>s w. y + w s) f) < c" for f
      proof -
        have "etime T A (\<lambda>s w. y + w s) f \<le> T" by (rule etime_le_T[OF T])
        hence "ennreal (etime T A (\<lambda>s w. y + w s) f) \<le> ennreal T"
          by (rule ennreal_leI)
        thus ?thesis using True by (rule order_le_less_trans)
      qed
      thus ?thesis by blast
    qed
    then show ?thesis
      using openin_topspace[of
          "mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric)"]
      by simp
  next
    case False
    hence cT: "c \<le> ennreal T" by simp
    then obtain r where r: "0 \<le> r" "c = ennreal r"
      by (cases c rule: ennreal_cases) (auto simp: top_unique)
    have rT: "\<not> T < r"
    proof
      assume "T < r"
      hence "ennreal T < ennreal r" using T by (simp add: ennreal_less_iff)
      thus False using False r(2) by simp
    qed
    have "{f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
          ennreal (etime T A (\<lambda>s w. y + w s) f) < c}
        = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
          etime T A (\<lambda>s w. y + w s) f < r}"
      unfolding r(2)
      using etime_nonneg[OF T, of A "\<lambda>s w. y + w s"]
      by (auto simp: ennreal_less_iff)
    then show ?thesis by (simp add: open_etime_shift_less[OF T A rT])
  qed
  have compl: "topspace (mtopology_of (path_metric T :: (real \<Rightarrow> 'b) metric))
        - {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
             c \<le> ennreal (etime T A (\<lambda>s w. y + w s) f)}
      = {f \<in> mspace (path_metric T :: (real \<Rightarrow> 'b) metric).
           ennreal (etime T A (\<lambda>s w. y + w s) f) < c}"
    by (auto simp: not_le)
  show ?thesis
    unfolding closedin_def using op unfolding compl by auto
qed

definition confined_paths ::
  "real \<Rightarrow> (real^'m::finite) set \<Rightarrow> real^'m \<Rightarrow> (real \<Rightarrow> real^'m) set"
  where
  "confined_paths T K x0 =
     {f \<in> mspace (path_metric T :: (real \<Rightarrow> real^'m) metric).
        f 0 = x0 \<and> (\<forall>t\<in>{0..T}. f t \<in> K)}"

lemma closedin_confined_paths:
  fixes K :: "(real^'m::finite) set"
  assumes T: "0 \<le> T" and K: "closed K"
  shows "closedin (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      (confined_paths T K x0)"
proof -
  let ?X = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  interpret PM: Metric_space
      "mspace (path_metric T :: (real \<Rightarrow> real^'m) metric)"
      "mdist (path_metric T :: (real \<Rightarrow> real^'m) metric)"
    by (rule Metric_space_mspace_mdist)
  have ts: "topspace ?X
      = mspace (path_metric T :: (real \<Rightarrow> real^'m) metric)"
    unfolding mtopology_of_def by (rule PM.topspace_mtopology)
  have c0: "closedin ?X {f \<in> topspace ?X. f 0 \<in> {x0}}"
    by (rule closedin_continuous_map_preimage[OF continuous_map_path_eval])
      (use T in \<open>auto\<close>)
  have ct: "closedin ?X {f \<in> topspace ?X. f t \<in> K}"
    if t: "t \<in> {0..T}" for t
    by (rule closedin_continuous_map_preimage[OF
          continuous_map_path_eval[OF t]])
      (simp add: K)
  have eq: "confined_paths T K x0
      = {f \<in> topspace ?X. f 0 \<in> {x0}}
        \<inter> (\<Inter>t\<in>{0..T}. {f \<in> topspace ?X. f t \<in> K})"
    using T unfolding confined_paths_def ts by auto
  show ?thesis
    unfolding eq
    by (intro closedin_Int c0 closedin_INT ct) (use T in auto)
qed

definition rclamp :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rclamp c y = max (- c) (min c y)"

lemma rclamp_bound: "0 \<le> c \<Longrightarrow> \<bar>rclamp c y\<bar> \<le> c"
  by (simp add: rclamp_def abs_le_iff min_def max_def)

lemma rclamp_id:
  assumes "\<bar>y\<bar> \<le> c"
  shows "rclamp c y = y"
proof -
  have "min c y = y"
    using assms by (intro min_absorb2) (simp add: abs_le_iff)
  moreover have "max (- c) y = y"
    using assms by (intro max_absorb2) (simp add: abs_le_iff)
  ultimately show ?thesis by (simp add: rclamp_def)
qed

lemma rclamp_cont: "continuous_map euclideanreal euclideanreal (rclamp c)"
  unfolding continuous_map_iff_continuous2 rclamp_def
  by (intro continuous_intros)

lemma martingale_test_functional_cont:
  fixes h :: "(real \<Rightarrow> real^'m::finite) \<Rightarrow> real" and c :: real
  assumes st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal
      (\<lambda>f. rclamp c (f t $ i - f s $ i) * h (restrict f {0..s}))"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have evdiff: "continuous_map ?PT euclidean (\<lambda>f. f t - f s)"
    by (intro continuous_map_diff continuous_map_path_eval tI sI)
  have cmp_i: "continuous_map (euclidean :: (real^'m) topology)
      euclideanreal (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have part1': "continuous_map ?PT euclideanreal
      ((rclamp c \<circ> (\<lambda>v. v $ i)) \<circ> (\<lambda>f. f t - f s))"
    by (intro continuous_map_compose[OF evdiff]
        continuous_map_compose[OF cmp_i] rclamp_cont)
  have part1: "continuous_map ?PT euclideanreal
      (\<lambda>f. rclamp c (f t $ i - f s $ i))"
    using part1' by (simp add: o_def)
  have rc: "continuous_map ?PT
      (mtopology_of (path_metric s :: (real \<Rightarrow> real^'m) metric))
      (\<lambda>f. restrict f {0..s})"
    by (rule Lipschitz_continuous_imp_continuous_map
        [OF Lipschitz_restrict_path_metric[OF st sT]])
  have part2': "continuous_map ?PT euclideanreal
      (h \<circ> (\<lambda>f. restrict f {0..s}))"
    by (rule continuous_map_compose[OF rc hc])
  have part2: "continuous_map ?PT euclideanreal
      (\<lambda>f. h (restrict f {0..s}))"
    using part2' by (simp add: o_def)
  show ?thesis
    by (rule continuous_map_real_mult[OF part1 part2])
qed

lemma covariation_test_functional_cont:
  fixes h :: "(real \<Rightarrow> real^'m::finite) \<Rightarrow> real" and c :: real
  assumes st: "0 \<le> s" and sT: "s \<le> T" and tI: "t \<in> {0..T}"
    and hc: "continuous_map (mtopology_of
        (path_metric s :: (real \<Rightarrow> real^'m) metric)) euclideanreal h"
  shows "continuous_map
      (mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric))
      euclideanreal
      (\<lambda>f. (rclamp c (f t $ i - f s $ i))\<^sup>2 * h (restrict f {0..s}))"
proof -
  let ?PT = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'m) metric)"
  have sI: "s \<in> {0..T}" using st sT by simp
  have evdiff: "continuous_map ?PT euclidean (\<lambda>f. f t - f s)"
    by (intro continuous_map_diff continuous_map_path_eval tI sI)
  have cmp_i: "continuous_map (euclidean :: (real^'m) topology)
      euclideanreal (\<lambda>v. v $ i)"
    unfolding continuous_map_iff_continuous2
    by (rule linear_continuous_on[OF bounded_linear_vec_nth])
  have part1': "continuous_map ?PT euclideanreal
      ((rclamp c \<circ> (\<lambda>v. v $ i)) \<circ> (\<lambda>f. f t - f s))"
    by (intro continuous_map_compose[OF evdiff]
        continuous_map_compose[OF cmp_i] rclamp_cont)
  have part1: "continuous_map ?PT euclideanreal
      (\<lambda>f. rclamp c (f t $ i - f s $ i))"
    using part1' by (simp add: o_def)
  have part1sq: "continuous_map ?PT euclideanreal
      (\<lambda>f. (rclamp c (f t $ i - f s $ i))\<^sup>2)"
    using continuous_map_real_mult[OF part1 part1]
    by (simp add: power2_eq_square)
  have part2: "continuous_map ?PT euclideanreal
      (\<lambda>f. h (restrict f {0..s}))"
    by (rule past_test_functional_cont[OF st sT hc])
  show ?thesis
    by (rule continuous_map_real_mult[OF part1sq part2])
qed

lemma pexit_le_of_mem:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and r: "0 \<le> r" "r \<le> T" and mem: "f r \<notin> K"
  shows "pexit T K f \<le> r"
  unfolding pexit_def using T0 r mem by (intro etime_le_of_mem) auto

lemma pexit_mem_of_less_T:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and lt: "pexit T K f < T"
  shows "f (pexit T K f) \<notin> K"
proof -
  let ?S = "{r. 0 \<le> r \<and> r \<le> T \<and> f r \<in> - K}"
  have cK: "closed (- K)" unfolding closed_def using Kop by simp
  have Sclosed: "closed ?S"
  proof -
    have "?S = f -` (- K) \<inter> {0..T}" by auto
    then show ?thesis using cont cK by (simp add: continuous_on_closed_vimage)
  qed
  have Sbdd: "bdd_below ?S" by (intro bdd_belowI[of _ 0]) auto
  have pe: "pexit T K f = Inf (?S \<union> {T})"
    unfolding pexit_def etime_def by simp
  have Sne: "?S \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> ?S \<noteq> {}"
    then have e: "?S = {}" by simp
    have "pexit T K f = Inf ({} \<union> {T})" unfolding pe e ..
    then have "pexit T K f = T" by simp
    with lt show False by simp
  qed
  have SleT: "Inf ?S \<le> T"
  proof -
    from Sne obtain s where s: "s \<in> ?S" by blast
    then have "Inf ?S \<le> s" using Sbdd by (intro cInf_lower)
    also have "s \<le> T" using s by simp
    finally show ?thesis .
  qed
  have "Inf (?S \<union> {T}) = inf (Inf ?S) (Inf {T})"
    by (rule cInf_union_distrib[OF Sne Sbdd]) auto
  then have "pexit T K f = Inf ?S" using pe SleT by (simp add: inf_min)
  moreover have "Inf ?S \<in> ?S"
    using Sne Sbdd Sclosed by (intro closed_contains_Inf) auto
  ultimately show ?thesis by simp
qed

text \<open>The second is the congruence clause of a stopping time, restricted to
  continuous paths.  The asymmetry: the \<open>\<ge>\<close> direction is unconditional (a
  witness for \<open>g\<close> strictly below the exit time of \<open>f\<close> is a witness for \<open>f\<close>
  too), and only the \<open>\<le>\<close> direction needs attainment.\<close>

lemma pexit_cong_stopping:
  fixes f g :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T" and Kop: "open K"
    and cont: "continuous_on {0..T} f"
    and eq: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pexit T K f \<Longrightarrow> f t = g t"
  shows "pexit T K g = pexit T K f"
proof -
  have th0: "0 \<le> pexit T K f" by (rule pexit_nonneg[OF T0])
  have thT: "pexit T K f \<le> T" by (rule pexit_le_T[OF T0])
  have le: "pexit T K g \<le> pexit T K f"
  proof (cases "pexit T K f < T")
    case True
    have "f (pexit T K f) \<notin> K"
      by (rule pexit_mem_of_less_T[OF T0 Kop cont True])
    then have m: "g (pexit T K f) \<notin> K"
      using eq[OF th0 order_refl] by simp
    show ?thesis
      by (rule pexit_le_of_mem[of T "pexit T K f" g K, OF T0 th0 thT m])
  next
    case False
    with thT have "pexit T K f = T" by simp
    then show ?thesis using pexit_le_T[OF T0, of K g] by simp
  qed
  have ge: "pexit T K f \<le> pexit T K g"
  proof (rule ccontr)
    assume "\<not> pexit T K f \<le> pexit T K g"
    then have lt: "pexit T K g < pexit T K f" by simp
    have "(\<exists>r. 0 \<le> r \<and> r \<le> T \<and> g r \<in> - K \<and> r < pexit T K f)
        \<or> T < pexit T K f"
      using lt pexit_less_iff[OF T0] by blast
    with thT obtain r where r: "0 \<le> r" "r \<le> T" "g r \<notin> K"
      "r < pexit T K f" by auto
    have "f r \<notin> K" using eq[OF r(1)] r(4) r(3) by simp
    then have "pexit T K f \<le> r"
      by (rule pexit_le_of_mem[OF T0 r(1) r(2)])
    with r(4) show False by simp
  qed
  from le ge show ?thesis by simp
qed

lemma pexit_eq_of_stays:
  fixes f :: "real \<Rightarrow> 'b::polish_space"
  assumes T0: "0 \<le> T'" and stays: "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> T' \<Longrightarrow> f s \<in> K"
  shows "pexit T' K f = T'"
proof (rule order.antisym)
  show "pexit T' K f \<le> T'" by (rule pexit_le_T[OF T0])
  show "T' \<le> pexit T' K f"
  proof (rule ccontr)
    assume "\<not> T' \<le> pexit T' K f"
    then have "pexit T' K f < T'" by simp
    then have "(\<exists>r. 0 \<le> r \<and> r \<le> T' \<and> f r \<in> - K \<and> r < T') \<or> T' < T'"
      using pexit_less_iff[OF T0] by blast
    then show False using stays by auto
  qed
qed


text \<open>Capping the uncapped exit time returns the capped one.  This is the
  pathwise form of the statement that the horizon is a device: everything the
  capped development says about \<open>pexit T\<close> is a statement about \<open>iexit\<close> below
  the level \<open>T\<close>.\<close>

theorem iexit_cap:
  assumes T: "0 \<le> T"
  shows "min (iexit K f) (ennreal T) = ennreal (pexit T K f)"
proof (cases "iexit K f \<le> ennreal T")
  case True
  have eq: "pexit S K f = pexit T K f" if S: "T \<le> S" for S
  proof -
    have S0: "0 \<le> S" using T S by simp
    have "ennreal (pexit S K f) \<le> ennreal T"
      using True pexit_le_iexit[OF S0, of K f] by simp
    then have "pexit S K f \<le> T" using T by simp
    moreover have "pexit T K f = min (pexit S K f) T"
      by (rule pexit_min_horizon[OF T S])
    ultimately show ?thesis by simp
  qed
  have "iexit K f = ennreal (pexit T K f)"
    unfolding iexit_def
  proof (rule antisym)
    show "(SUP S\<in>{0..}. ennreal (pexit S K f)) \<le> ennreal (pexit T K f)"
    proof (rule SUP_least)
      fix S :: real assume "S \<in> {0..}"
      then have S0: "0 \<le> S" by simp
      show "ennreal (pexit S K f) \<le> ennreal (pexit T K f)"
      proof (cases "T \<le> S")
        case True
        then have "pexit S K f = pexit T K f" by (rule eq)
        then show ?thesis by simp
      next
        case False
        then have "pexit S K f = min (pexit T K f) S"
          by (intro pexit_min_horizon[OF S0]) simp
        then show ?thesis by (simp add: ennreal_leI)
      qed
    qed
    show "ennreal (pexit T K f) \<le> (SUP S\<in>{0..}. ennreal (pexit S K f))"
      using T by (intro SUP_upper) simp
  qed
  with True show ?thesis by simp
next
  case False
  then have gt: "ennreal T < iexit K f" by simp
  obtain S where S0: "0 \<le> S" and Sgt: "ennreal T < ennreal (pexit S K f)"
    using gt unfolding iexit_def by (auto simp: less_SUP_iff)
  have pS: "0 \<le> pexit S K f" by (rule pexit_nonneg[OF S0])
  have TltS: "T < pexit S K f"
    using Sgt pS T by (simp add: ennreal_less_iff)
  have TS: "T \<le> S" using TltS pexit_le_T[OF S0, of K f] by simp
  have "pexit T K f = min (pexit S K f) T"
    by (rule pexit_min_horizon[OF T TS])
  then have pT: "pexit T K f = T" using TltS by simp
  have "min (iexit K f) (ennreal T) = ennreal T"
    using gt by (simp add: min_absorb2 order_less_imp_le)
  then show ?thesis using pT by simp
qed

(*<*)
end
(*>*)
