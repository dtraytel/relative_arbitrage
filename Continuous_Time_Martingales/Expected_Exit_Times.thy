section \<open>Expected exit times from optional sampling\<close>

(*<*)
theory Expected_Exit_Times
  imports Stopped_Adaptedness
begin
(*>*)

text \<open>A nonnegative stopping time of a filtration indexed from \<open>0\<close> is
  measurable.\<close>

lemma stopping_time_borel_measurable:
  fixes tau :: "'a \<Rightarrow> real"
  assumes fm: "filtered_measure M F (0::real)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
  shows "tau \<in> borel_measurable M"
proof (rule borel_measurable_iff_le[THEN iffD2], intro allI)
  fix a :: real
  show "{\<omega> \<in> space M. tau \<omega> \<le> a} \<in> sets M"
  proof (cases "0 \<le> a")
    case True
    then show ?thesis
      using tau_stop[OF True] filtered_measure.subalgebras[OF fm True]
      by (auto simp: subalgebra_def)
  next
    case False
    then have e: "{\<omega> \<in> space M. tau \<omega> \<le> a} = {}"
      using tau_nonneg by force
    show ?thesis unfolding e by simp
  qed
qed

text \<open>The core estimate.  \<open>Z\<close> is a real martingale with continuous paths,
  dominated on bounded intervals by integrable functions, and up to the
  stopping time \<open>tau\<close> it stays below the line \<open>R - c s\<close>.  Optional sampling
  at the bounded stopping time \<open>min t tau\<close> gives
  \<open>E[Z 0] = E[Z (t \<and> tau)] \<le> R - c E[t \<and> tau]\<close>.  No sign condition on \<open>c\<close> is
  needed here.\<close>

theorem stopped_time_mean_bound:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
    and D :: "real \<Rightarrow> 'a \<Rightarrow> real" and c R t :: real
  assumes P: "prob_space M"
    and mg: "martingale M F 0 Z"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. Z s \<omega>)"
    and dom: "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D u \<omega>"
    and D_int: "\<And>u. 0 < u \<Longrightarrow> integrable M (D u)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and bound: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> Z s \<omega> + c * s \<le> R"
    and t: "0 \<le> t"
  shows "c * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)"
proof -
  interpret P: prob_space M by (rule P)
  interpret Mg: martingale M F 0 Z by (rule mg)
  have tau_meas: "tau \<in> borel_measurable M"
    by (rule stopping_time_borel_measurable[OF Mg.filtered_measure_axioms tau_nonneg tau_stop])
  have stopped_meas: "(\<lambda>\<omega>. Z (min t (tau \<omega>)) \<omega>) \<in> borel_measurable M"
    by (rule measurable_from_subalg[OF Mg.subalgebras[OF t]
          stopped_adapted_of_cont[OF Mg.adapted_process_axioms tau_nonneg tau_stop cont t]])
  have os: "(\<integral>\<omega>. Z (min t (tau \<omega>)) \<omega> \<partial>M) = (\<integral>\<omega>. Z 0 \<omega> \<partial>M)
      \<and> integrable M (\<lambda>\<omega>. Z (min t (tau \<omega>)) \<omega>)"
  proof (cases "0 < t")
    case True
    interpret S: stopped_cont_martingale M F Z tau t "D t"
    proof (intro stopped_cont_martingale.intro[OF mg] stopped_cont_martingale_axioms.intro)
      show "0 < t" by (rule True)
      show "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>" by (rule tau_nonneg)
      show "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)" by (rule tau_stop)
      show "AE \<omega> in M. continuous_on {0..t} (\<lambda>s. Z s \<omega>)"
        by (intro AE_I2 continuous_on_subset[OF cont]) auto
      show "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> t \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D t \<omega>"
        by (rule dom[OF True])
      show "integrable M (D t)" by (rule D_int[OF True])
      show "(\<lambda>\<omega>. Z (min t (tau \<omega>)) \<omega>) \<in> borel_measurable M" by (rule stopped_meas)
    qed
    show ?thesis using S.optional_sampling S.stopped_integrable by blast
  next
    case False
    with t have t0: "t = 0" by simp
    have eq: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> Z (min t (tau \<omega>)) \<omega> = Z 0 \<omega>"
      using tau_nonneg t0 by (simp add: min_def)
    have "(\<integral>\<omega>. Z (min t (tau \<omega>)) \<omega> \<partial>M) = (\<integral>\<omega>. Z 0 \<omega> \<partial>M)"
      by (rule Bochner_Integration.integral_cong[OF refl eq])
    moreover have "integrable M (\<lambda>\<omega>. Z (min t (tau \<omega>)) \<omega>) \<longleftrightarrow> integrable M (\<lambda>\<omega>. Z 0 \<omega>)"
      by (rule Bochner_Integration.integrable_cong) (simp_all add: eq)
    then have "integrable M (\<lambda>\<omega>. Z (min t (tau \<omega>)) \<omega>)"
      using Mg.integrable[OF order_refl] by simp
    ultimately show ?thesis by blast
  qed
  have mint: "integrable M (\<lambda>\<omega>. min t (tau \<omega>))"
  proof (rule P.integrable_const_bound[of _ t])
    show "AE \<omega> in M. norm (min t (tau \<omega>)) \<le> t"
      using AE_space by eventually_elim (use tau_nonneg t in auto)
    show "(\<lambda>\<omega>. min t (tau \<omega>)) \<in> borel_measurable M"
      using tau_meas by measurable
  qed
  have pw: "AE \<omega> in M. Z (min t (tau \<omega>)) \<omega> + c * min t (tau \<omega>) \<le> R"
    using bound AE_space
  proof eventually_elim
    case (elim \<omega>)
    have "0 \<le> min t (tau \<omega>)" using tau_nonneg[OF elim(2)] t by simp
    moreover have "min t (tau \<omega>) \<le> tau \<omega>" by simp
    ultimately show ?case using elim(1) by blast
  qed
  have int_l: "integrable M (\<lambda>\<omega>. Z (min t (tau \<omega>)) \<omega> + c * min t (tau \<omega>))"
    using os mint by (intro Bochner_Integration.integrable_add integrable_mult_right) auto
  have "(\<integral>\<omega>. Z (min t (tau \<omega>)) \<omega> + c * min t (tau \<omega>) \<partial>M) \<le> (\<integral>\<omega>. R \<partial>M)"
    by (rule integral_mono_AE[OF int_l _ pw]) simp
  also have "\<dots> = R" by (simp add: P.prob_space)
  finally have "(\<integral>\<omega>. Z (min t (tau \<omega>)) \<omega> \<partial>M) + c * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> R"
    using os mint by simp
  then show ?thesis using os by simp
qed

text \<open>For \<open>c > 0\<close> the bound passes to \<open>tau\<close> itself by monotone convergence:
  \<open>tau\<close> is integrable and \<open>E[tau] \<le> (R - E[Z 0]) / c\<close>.\<close>

theorem stopping_time_integrable_bound:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Z :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
    and D :: "real \<Rightarrow> 'a \<Rightarrow> real" and c R :: real
  assumes P: "prob_space M"
    and mg: "martingale M F 0 Z"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. Z s \<omega>)"
    and dom: "\<And>u. 0 < u \<Longrightarrow> AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Z s \<omega>\<bar> \<le> D u \<omega>"
    and D_int: "\<And>u. 0 < u \<Longrightarrow> integrable M (D u)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and bound: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> Z s \<omega> + c * s \<le> R"
    and c: "0 < c"
  shows "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) \<le> ennreal ((R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)) / c)"
    and "integrable M tau"
    and "(\<integral>\<omega>. tau \<omega> \<partial>M) \<le> (R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)) / c"
proof -
  interpret P: prob_space M by (rule P)
  interpret Mg: martingale M F 0 Z by (rule mg)
  define B where "B = (R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)) / c"
  have tau_meas: "tau \<in> borel_measurable M"
    by (rule stopping_time_borel_measurable[OF Mg.filtered_measure_axioms tau_nonneg tau_stop])
  have mint: "integrable M (\<lambda>\<omega>. min t (tau \<omega>))" if t: "0 \<le> t" for t
  proof (rule P.integrable_const_bound[of _ t])
    show "AE \<omega> in M. norm (min t (tau \<omega>)) \<le> t"
      using AE_space by eventually_elim (use tau_nonneg t in auto)
    show "(\<lambda>\<omega>. min t (tau \<omega>)) \<in> borel_measurable M"
      using tau_meas by measurable
  qed
  have bnd: "(\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> B" if t: "0 \<le> t" for t
  proof -
    have "c * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)"
      by (rule stopped_time_mean_bound[OF P mg cont dom D_int tau_nonneg tau_stop bound t])
    then show ?thesis
      unfolding B_def using c by (simp add: pos_le_divide_eq mult.commute)
  qed
  have B0: "0 \<le> B"
  proof -
    have "AE \<omega> in M. 0 \<le> min 0 (tau \<omega>)"
      using AE_space by eventually_elim (use tau_nonneg in auto)
    then have "0 \<le> (\<integral>\<omega>. min 0 (tau \<omega>) \<partial>M)" by (rule integral_nonneg_AE)
    also have "\<dots> \<le> B" by (rule bnd) simp
    finally show ?thesis .
  qed
  have bound_n: "(\<integral>\<^sup>+\<omega>. ennreal (min (real n) (tau \<omega>)) \<partial>M) \<le> ennreal B" for n
  proof -
    have nn: "AE \<omega> in M. 0 \<le> min (real n) (tau \<omega>)"
      using AE_space by eventually_elim (use tau_nonneg in auto)
    have "(\<integral>\<^sup>+\<omega>. ennreal (min (real n) (tau \<omega>)) \<partial>M)
        = ennreal (\<integral>\<omega>. min (real n) (tau \<omega>) \<partial>M)"
      by (rule nn_integral_eq_integral[OF mint nn]) simp
    also have "\<dots> \<le> ennreal B"
      by (intro ennreal_leI bnd) simp
    finally show ?thesis .
  qed
  have sup_eq: "AE \<omega> in M. (SUP n. ennreal (min (real n) (tau \<omega>))) = ennreal (tau \<omega>)"
    using AE_space
  proof eventually_elim
    case (elim \<omega>)
    obtain m where m: "tau \<omega> \<le> real m"
      using real_arch_simple by blast
    have le: "(SUP n. ennreal (min (real n) (tau \<omega>))) \<le> ennreal (tau \<omega>)"
      by (intro SUP_least ennreal_leI) auto
    have "ennreal (tau \<omega>) = ennreal (min (real m) (tau \<omega>))"
      using m by (simp add: min_def)
    also have "\<dots> \<le> (SUP n. ennreal (min (real n) (tau \<omega>)))"
      by (rule SUP_upper) simp
    finally show ?case
      using le by (rule antisym[rotated])
  qed
  have meas_min: "(\<lambda>\<omega>. min (real n) (tau \<omega>)) \<in> borel_measurable M" for n
    using tau_meas by measurable
  have incseq: "incseq (\<lambda>n \<omega>. ennreal (min (real n) (tau \<omega>)))"
    by (intro incseq_SucI le_funI ennreal_leI) (auto simp: min_def)
  have "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)
      = (\<integral>\<^sup>+\<omega>. (SUP n. ennreal (min (real n) (tau \<omega>))) \<partial>M)"
    by (rule nn_integral_cong_AE) (use sup_eq in \<open>simp add: eq_commute\<close>)
  also have "\<dots> = (SUP n. \<integral>\<^sup>+\<omega>. ennreal (min (real n) (tau \<omega>)) \<partial>M)"
    by (rule nn_integral_monotone_convergence_SUP[OF incseq]) (use meas_min in measurable)
  also have "\<dots> \<le> ennreal B"
    by (rule SUP_least) (rule bound_n)
  finally have nnb: "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) \<le> ennreal B" .
  then show "(\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M) \<le> ennreal ((R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)) / c)"
    unfolding B_def .
  have nn: "AE \<omega> in M. 0 \<le> tau \<omega>"
    using AE_space by eventually_elim (use tau_nonneg in auto)
  show int: "integrable M tau"
    by (rule integrableI_nonneg[OF tau_meas nn])
      (use order.strict_trans1[OF nnb ennreal_less_top] in simp)
  have "ennreal (\<integral>\<omega>. tau \<omega> \<partial>M) = (\<integral>\<^sup>+\<omega>. ennreal (tau \<omega>) \<partial>M)"
    by (rule nn_integral_eq_integral[OF int nn, symmetric])
  with nnb have "ennreal (\<integral>\<omega>. tau \<omega> \<partial>M) \<le> ennreal B" by simp
  then show "(\<integral>\<omega>. tau \<omega> \<partial>M) \<le> (R - (\<integral>\<omega>. Z 0 \<omega> \<partial>M)) / c"
    using B0 unfolding B_def by simp
qed

text \<open>The form of the estimate with an explicit Doob--Meyer-type split
  \<open>Z = Y - A\<close>: \<open>Y\<close> is bounded above by \<open>R\<close> and \<open>A\<close> grows at least at rate
  \<open>c\<close> up to \<open>tau\<close>.  (\<open>A 0 = 0\<close> is not needed; with it, \<open>E[Z 0] = E[Y 0]\<close>.)\<close>

corollary expected_exit_time_bound:
  fixes M :: "'a measure" and F :: "real \<Rightarrow> 'a measure"
    and Y A :: "real \<Rightarrow> 'a \<Rightarrow> real" and tau :: "'a \<Rightarrow> real"
    and D :: "real \<Rightarrow> 'a \<Rightarrow> real" and c R :: real
  assumes P: "prob_space M"
    and mg: "martingale M F 0 (\<lambda>t \<omega>. Y t \<omega> - A t \<omega>)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. Y s \<omega> - A s \<omega>)"
    and dom: "\<And>u. 0 < u \<Longrightarrow>
      AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>Y s \<omega> - A s \<omega>\<bar> \<le> D u \<omega>"
    and D_int: "\<And>u. 0 < u \<Longrightarrow> integrable M (D u)"
    and tau_nonneg: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> 0 \<le> tau \<omega>"
    and tau_stop: "\<And>s. 0 \<le> s \<Longrightarrow> {\<omega> \<in> space M. tau \<omega> \<le> s} \<in> sets (F s)"
    and Y_le: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> Y s \<omega> \<le> R"
    and A_ge: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> c * s \<le> A s \<omega>"
  shows "\<And>t. 0 \<le> t \<Longrightarrow>
      c * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> R - (\<integral>\<omega>. Y 0 \<omega> - A 0 \<omega> \<partial>M)"
    and "0 < c \<Longrightarrow> integrable M tau"
    and "0 < c \<Longrightarrow> (\<integral>\<omega>. tau \<omega> \<partial>M) \<le> (R - (\<integral>\<omega>. Y 0 \<omega> - A 0 \<omega> \<partial>M)) / c"
proof -
  have bound: "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> tau \<omega> \<longrightarrow> (Y s \<omega> - A s \<omega>) + c * s \<le> R"
    using Y_le A_ge
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix s assume "0 \<le> s" "s \<le> tau \<omega>"
      then have "Y s \<omega> \<le> R" "c * s \<le> A s \<omega>" using elim by blast+
      then show "Y s \<omega> - A s \<omega> + c * s \<le> R" by linarith
    qed
  qed
  show "c * (\<integral>\<omega>. min t (tau \<omega>) \<partial>M) \<le> R - (\<integral>\<omega>. Y 0 \<omega> - A 0 \<omega> \<partial>M)"
    if "0 \<le> t" for t
    using stopped_time_mean_bound[OF P mg cont dom D_int tau_nonneg tau_stop bound that]
    by simp
  show "integrable M tau" if "0 < c"
    using stopping_time_integrable_bound(2)[OF P mg cont dom D_int tau_nonneg tau_stop bound that] .
  show "(\<integral>\<omega>. tau \<omega> \<partial>M) \<le> (R - (\<integral>\<omega>. Y 0 \<omega> - A 0 \<omega> \<partial>M)) / c" if "0 < c"
    using stopping_time_integrable_bound(3)[OF P mg cont dom D_int tau_nonneg tau_stop bound that]
    by simp
qed

text \<open>The domination hypothesis is automatic for square-integrable martingales
  with continuous paths (Doob's \<open>L\<^sup>2\<close> inequality): the squared process is
  dominated on \<open>[0, u]\<close> by an integrable function.\<close>

lemma sq_martingale_envelope:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes P: "prob_space M"
    and mg: "martingale M F (0::real) X"
    and sq: "\<And>s. 0 \<le> s \<Longrightarrow> integrable M (\<lambda>\<omega>. (X s \<omega>)\<^sup>2)"
    and cont: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> continuous_on {0..} (\<lambda>s. X s \<omega>)"
    and u: "0 < u"
  shows "\<exists>D. (AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> (X s \<omega>)\<^sup>2 \<le> D \<omega>) \<and> integrable M D"
proof -
  interpret H: horizon_sq_int_martingale M F X u
    by (intro horizon_sq_int_martingale.intro[OF mg]
        horizon_sq_int_martingale_axioms.intro u P sq)
  have "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> \<bar>X s \<omega>\<bar> \<le> H.Dsup \<omega>"
    by (rule H.Dsup_dominates) (intro AE_I2 continuous_on_subset[OF cont]; auto)
  then have "AE \<omega> in M. \<forall>s. 0 \<le> s \<longrightarrow> s \<le> u \<longrightarrow> (X s \<omega>)\<^sup>2 \<le> (H.Dsup \<omega>)\<^sup>2"
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (intro allI impI)
      fix s :: real assume "0 \<le> s" "s \<le> u"
      then have "\<bar>X s \<omega>\<bar> \<le> H.Dsup \<omega>" using elim by blast
      then have "\<bar>X s \<omega>\<bar>\<^sup>2 \<le> (H.Dsup \<omega>)\<^sup>2" by (rule power_mono) simp
      then show "(X s \<omega>)\<^sup>2 \<le> (H.Dsup \<omega>)\<^sup>2" by simp
    qed
  qed
  then show ?thesis
    by (intro exI[of _ "\<lambda>\<omega>. (H.Dsup \<omega>)\<^sup>2"] conjI H.Dsup_sq_integrable)
qed

(*<*)
end
(*>*)
