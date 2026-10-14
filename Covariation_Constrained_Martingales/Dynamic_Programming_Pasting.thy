section \<open>The optimal selector and the measurable value function\<close>
(*<*)
theory Dynamic_Programming_Pasting
  imports
    "Disintegration.Disintegration" Covariation_Class_Optimizer
begin

(*>*)
text \<open>Ingredients of the dynamic programming principle: the optimal selector
  as a kernel, the
  almost-sure form of its optimality, and the Borel measurability of the
  value function.  The principle itself is assembled in
  \<open>Dynamic_Programming_Assembly\<close> (the \<open>\<ge>\<close> half, at a stopping time and
  hence at a deterministic time) and \<open>Dynamic_Programming_Principle\<close>.\<close>

subsection \<open>The optimal selector as a kernel\<close>

text \<open>A map into the weak-convergence Borel space whose values are
  probability measures on \<open>borel_of X\<close> is a kernel: it is measurable into
  the probability algebra, by @{thm [source] weak_conv_topology_eq_prob_algebra}.\<close>

lemma measurable_prob_algebra_weak_conv:
  assumes X: "Polish_space X" and f: "f \<in> M \<rightarrow>\<^sub>M borel_of (weak_conv_topology X)"
    and P: "\<And>x. x \<in> space M \<Longrightarrow> prob_space (f x) \<and> sets (f x) = sets (borel_of X)"
  shows "f \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of X)"
proof -
  have "f \<in> M \<rightarrow>\<^sub>M restrict_space (borel_of (weak_conv_topology X))
      {N. prob_space N \<and> sets N = sets (borel_of X)}" (is "_ \<in> M \<rightarrow>\<^sub>M ?R")
    by (rule measurable_restrict_space2[OF _ f]) (use P in auto)
  moreover have "M \<rightarrow>\<^sub>M ?R = M \<rightarrow>\<^sub>M prob_algebra (borel_of X)"
    using measurable_cong_sets[OF refl weak_conv_topology_eq_prob_algebra[OF X]]
    by (simp add: borel_of_subtopology)
  ultimately show ?thesis by simp
qed

theorem covariation_val_measurable_selector_kernel':
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and SST: "\<sigma> ** transpose \<sigma> \<in> S" and K: "closed K"
  obtains Sel where
    "Sel \<in> borel \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and "\<And>y. Sel y \<in> covariation_class S T 0"
    and "\<And>y. ess_inf_time (pshift_law T y (Sel y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K y"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  obtain Sel where Sm: "Sel \<in> borel \<rightarrow>\<^sub>M borel_of ?W"
    and SC: "\<And>y. Sel y \<in> covariation_class S T 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law T y (Sel y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K y"
    by (rule covariation_val_measurable_selector[OF T B0 B D0 D Sc SST K]) blast+
  have Sk: "Sel \<in> borel \<rightarrow>\<^sub>M prob_algebra ?B"
    by (rule measurable_prob_algebra_weak_conv[OF Polish_space_path_metric Sm])
      (use covariation_class_prob[OF SC] covariation_class_sets[OF SC] in simp)
  show ?thesis by (rule that[OF Sk SC Sval])
qed

subsection \<open>An optimal law, as an almost-sure bound\<close>

text \<open>What a selector's optimality gives, in the form the pasting arguments
  consume: an \<^const>\<open>ess_inf_time\<close> equality under the shifted law, turned
  by @{thm [source] ess_inf_time_AE} into the almost-sure bound
  \<open>v(y) \<le> \<tau>\<^sub>K\<close> on the unshifted paths.\<close>

lemma covariation_val_le_pexit_AE:
  fixes \<mu> :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes U0: "0 \<le> U"
    and setsmu: "sets \<mu> = sets (path_borel U :: ('n pairpath) measure)"
    and val: "ess_inf_time (pshift_law U y \<mu>) (\<lambda>\<omega>. pexit U K (\<lambda>t. fst (\<omega> t)))
        = covariation_val S U K y"
  shows "AE \<omega> in \<mu>. enn2real (covariation_val S U K y) \<le> pexit U K (\<lambda>t. y + fst (\<omega> t))"
proof -
  have "AE \<omega> in pshift_law U y \<mu>.
      covariation_val S U K y \<le> ennreal (pexit U K (\<lambda>t. fst (\<omega> t)))"
    unfolding val[symmetric] by (rule ess_inf_time_AE)
  then have "AE \<omega> in \<mu>. covariation_val S U K y \<le> ennreal (pexit U K (\<lambda>t. y + fst (\<omega> t)))"
    unfolding AE_pshift_law_iff[OF U0 setsmu] pexit_pshift .
  then show ?thesis
    by (rule eventually_mono) (rule enn2real_leI[OF pexit_nonneg[OF U0]])
qed

subsection \<open>The value function is Borel measurable\<close>

text \<open>Upper semicontinuity makes every sublevel set
  \<open>{y. v y < b}\<close> open, so \<open>v\<close> and its real version \<open>enn2real \<circ> v\<close> are
  Borel measurable, as needed to state the dynamic programming principle's
  integrand as a random variable.\<close>

lemma covariation_val_open_less:
  fixes K :: "(real^'n::finite) set" and b :: ennreal and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and SST: "\<sigma> ** transpose \<sigma> \<in> S" and K: "closed K"
  shows "open {y :: real^'n. covariation_val S T K y < b}"
proof (subst open_subopen, safe)
  fix y :: "real^'n" assume lt: "covariation_val S T K y < b"
  have "eventually (\<lambda>z. covariation_val S T K z < b) (nhds y)"
    by (rule covariation_val_usc[OF T B0 B D0 D Sc K
          covariation_class_nonempty[OF less_imp_le[OF T] Sc SST] lt])
  then obtain U where "open U" "y \<in> U" "\<forall>z\<in>U. covariation_val S T K z < b"
    unfolding eventually_nhds by blast
  then show "\<exists>U. open U \<and> y \<in> U \<and> U \<subseteq> {y. covariation_val S T K y < b}" by blast
qed

lemma covariation_val_neq_top:
  fixes K :: "(real^'n::finite) set" and y :: "real^'n"
  assumes T: "0 \<le> T"
  shows "covariation_val S T K y \<noteq> \<top>"
proof -
  have "covariation_val S T K y \<le> ennreal T" by (rule covariation_val_le_T[OF T])
  moreover have "(ennreal T :: ennreal) \<noteq> \<top>" by simp
  ultimately show ?thesis by (auto simp: top_unique)
qed

lemma covariation_val_borel_measurable:
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and SST: "\<sigma> ** transpose \<sigma> \<in> S" and K: "closed K"
  shows "(\<lambda>y :: real^'n. enn2real (covariation_val S T K y)) \<in> borel_measurable borel"
  by (intro borel_measurable_enn2real borel_measurableI_less)
    (simp add: borel_open covariation_val_open_less[OF T B0 B D0 D Sc SST K])

(*<*)
end
(*>*)
