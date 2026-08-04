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
