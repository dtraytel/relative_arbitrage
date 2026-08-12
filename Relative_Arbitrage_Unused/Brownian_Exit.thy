

(*<*)
theory Brownian_Exit
  imports "Relative_Arbitrage.Brownian_Continuous" "Relative_Arbitrage.Exit_Time"
begin

(*>*)

text \<open>
  The exit time of the continuous Brownian state process from a ball.

    The exit time of \<open>Exit_Time\<close> is applied to the continuous state process cbmX
    of \<open>Brownian_Continuous\<close>: it is a stopping time for the natural filtration of
    that process, and up to and including it the process stays in the closed
    ball.  This is the data the exit-time market needs.\<close>
section \<open>The exterior of an open ball\<close>

lemma closed_norm_exterior:
  "closed {y :: 'b :: real_normed_vector. r \<le> norm y}"
proof -
  have "{y :: 'b. r \<le> norm y} = - ball 0 r"
    by (auto simp: dist_norm)
  then show ?thesis
    by (simp add: closed_Compl)
qed

lemma norm_exterior_nonempty:
  fixes r :: real
  shows "{y :: real^'n::finite. r \<le> norm y} \<noteq> {}"
proof -
  obtain i :: 'n where "True"
    by auto
  let ?y = "(\<chi> _. max r 0 + 1) :: real^'n"
  have "\<bar>?y $ i\<bar> \<le> norm ?y"
    by (rule component_le_norm_cart)
  then have "r \<le> norm ?y"
    by simp
  then show ?thesis
    by blast
qed

section \<open>The ball exit time of the continuous state process\<close>

definition btau :: "real \<Rightarrow> real \<Rightarrow> real^'n::finite
    \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> real"
  where "btau T r x0 \<omega> = etime T {y :: real^'n. r \<le> norm y} (cbmX x0) \<omega>"

lemma btau_nonneg:
  assumes T: "0 \<le> T"
  shows "0 \<le> btau T r x0 \<omega>"
  unfolding btau_def by (rule etime_nonneg[OF T])

lemma btau_le_T: "0 \<le> T \<Longrightarrow> btau T r x0 \<omega> \<le> T"
  unfolding btau_def by (rule etime_le_T)

lemma cont_adapted_cbmX:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "cont_adapted_process (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)
    (natural_filtration bm_paths 0 (cbmX x0)) (cbmX x0) T"
proof (intro cont_adapted_process.intro cont_adapted_process_axioms.intro
    adapted_process_natural_filtration_of T)
  show "\<And>u. 0 \<le> u \<Longrightarrow>
      cbmX x0 u \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
    by (rule measurable_cbmX)
  show "\<And>\<omega>. \<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) \<Longrightarrow>
      continuous_on {0..T} (\<lambda>s. cbmX x0 s \<omega>)"
    by (rule continuous_on_subset[OF cbmX_cont]) auto
qed

theorem btau_stopping_time:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T" and t: "0 \<le> t"
  shows "{\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      btau T r x0 \<omega> \<le> t}
    \<in> sets (natural_filtration bm_paths 0 (cbmX x0) t)"
  unfolding btau_def
  by (rule cont_adapted_process.etime_stopping_time
      [OF cont_adapted_cbmX[OF T] closed_norm_exterior norm_exterior_nonempty t])

lemma btau_measurable:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T"
  shows "btau T r x0
    \<in> borel_measurable (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure)"
proof (rule borel_measurable_iff_le[THEN iffD2], intro allI)
  fix a :: real
  show "{\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      btau T r x0 \<omega> \<le> a} \<in> sets bm_paths"
  proof (cases "0 \<le> a")
    case True
    have "{\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        btau T r x0 \<omega> \<le> a}
        \<in> sets (natural_filtration bm_paths 0 (cbmX x0) a)"
      by (rule btau_stopping_time[OF T True])
    moreover have "sets (natural_filtration
        (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure) 0 (cbmX x0) a)
        \<subseteq> sets bm_paths"
      by (intro sets_natural_filtration_subset measurable_cbmX)
    ultimately show ?thesis
      by blast
  next
    case False
    have empty: "{\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        btau T r x0 \<omega> \<le> a} = {}"
    proof (intro equalityI subsetI)
      fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
      assume "\<omega> \<in> {\<omega> \<in> space (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
          btau T r x0 \<omega> \<le> a}"
      then have "btau T r x0 \<omega> \<le> a"
        by simp
      moreover have "0 \<le> btau T r x0 \<omega>"
        by (rule btau_nonneg[OF T])
      ultimately show "\<omega> \<in> {}"
        using False by simp
    qed simp
    show ?thesis
      unfolding empty by simp
  qed
qed

section \<open>Up to the exit time the process stays in the closed ball\<close>

theorem cbmX_in_cball_AE:
  fixes x0 :: "real^'n::finite"
  assumes T: "0 \<le> T" and r: "0 < r" and start: "norm x0 < r"
  shows "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
    \<forall>s. 0 \<le> s \<longrightarrow> s \<le> btau T r x0 \<omega> \<longrightarrow> cbmX x0 s \<omega> \<in> cball 0 r"
proof -
  have start0: "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
      cbmX x0 0 \<omega> = x0"
  proof -
    have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        cbmX x0 0 \<omega> = bmX x0 0 \<omega>"
      by (intro cbmX_ae_eq) simp
    moreover have "AE \<omega> in (bm_paths :: ('n \<Rightarrow> real \<Rightarrow> real) measure).
        bmX x0 0 \<omega> = x0"
      by (rule bmX_start)
    ultimately show ?thesis
      by eventually_elim simp
  qed
  then show ?thesis
  proof eventually_elim
    fix \<omega> :: "'n \<Rightarrow> real \<Rightarrow> real"
    assume w: "cbmX x0 0 \<omega> = x0"
    show "\<forall>s. 0 \<le> s \<longrightarrow> s \<le> btau T r x0 \<omega> \<longrightarrow> cbmX x0 s \<omega> \<in> cball 0 r"
    proof (intro allI impI)
      fix s :: real
      assume s: "0 \<le> s" and sle: "s \<le> btau T r x0 \<omega>"
      have st: "norm (cbmX x0 0 \<omega>) < r"
        using w start by simp
      have cont: "continuous_on {0..T} (\<lambda>s. cbmX x0 s \<omega>)"
        by (rule continuous_on_subset[OF cbmX_cont]) auto
      have sle': "s \<le> etime T {y :: real^'n. r \<le> norm y} (cbmX x0) \<omega>"
        using sle unfolding btau_def .
      show "cbmX x0 s \<omega> \<in> cball 0 r"
        by (rule etime_stays_in_cball[OF T r st cont s sle'])
    qed
  qed
qed


(*<*)
end
(*>*)
