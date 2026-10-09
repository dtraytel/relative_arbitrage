section \<open>The optimal selector and the measurable value function\<close>
(*<*)
theory Dynamic_Programming_Pasting
  imports
    "Disintegration.Disintegration" Exit_Class_Optimizer
begin

(*>*)
text \<open>Ingredients of the dynamic programming principle of Proposition 2.4 of
  \<^cite>\<open>LaiShkolnikovSoner\<close>: the optimal selector as a kernel, the
  almost-sure form of its optimality, and the Borel measurability of the
  value function.  The principle itself is assembled in
  \<open>Dynamic_Programming_Assembly\<close> (the \<open>\<ge>\<close> half, at a stopping time and
  hence at a deterministic time) and \<open>Proposition_2_4\<close>.\<close>

subsection \<open>The optimal selector as a kernel\<close>

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

subsection \<open>An optimal law, as an almost-sure bound\<close>

text \<open>What a selector's optimality gives, in the form the pasting arguments
  consume: an \<^const>\<open>ess_inf_time\<close> equality under the shifted law, turned
  by @{thm [source] ess_inf_time_AE} into the almost-sure bound
  \<open>v(y) \<le> \<tau>\<^sub>K\<close> on the unshifted paths.\<close>

lemma exit_val_le_pexit_AE:
  fixes \<mu> :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes S0: "0 \<le> S"
    and setsmu: "sets \<mu> = sets (path_borel S :: ('n pairpath) measure)"
    and val: "ess_inf_time (pshift_law S y \<mu>) (\<lambda>\<omega>. pexit S K (\<lambda>t. fst (\<omega> t)))
        = exit_val k L S K y"
  shows "AE \<omega> in \<mu>. enn2real (exit_val k L S K y) \<le> pexit S K (\<lambda>t. y + fst (\<omega> t))"
proof -
  have "AE \<omega> in pshift_law S y \<mu>.
      exit_val k L S K y \<le> ennreal (pexit S K (\<lambda>t. fst (\<omega> t)))"
    unfolding val[symmetric] by (rule ess_inf_time_AE)
  then have "AE \<omega> in \<mu>. exit_val k L S K y \<le> ennreal (pexit S K (\<lambda>t. y + fst (\<omega> t)))"
    unfolding AE_pshift_law_iff[OF S0 setsmu] pexit_pshift .
  then show ?thesis
    by (rule eventually_mono) (rule enn2real_leI[OF pexit_nonneg[OF S0]])
qed

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

(*<*)
end
(*>*)
