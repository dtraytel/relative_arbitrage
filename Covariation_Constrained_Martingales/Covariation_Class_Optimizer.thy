section \<open>Attainment, the measurable optimizer, and the semidirect product\<close>

(*<*)
theory Covariation_Class_Optimizer
  imports
    Covariation_Class_Pasting
begin

(*>*)

subsection \<open>The class is a compact metric space of measures\<close>

text \<open>The AFP entry \<open>Levy_Prokhorov_Metric\<close> makes the space of finite
  Borel measures on a separable metric space a metric space for the
  L\'evy--Prokhorov distance, whose topology is \<open>weak_conv_topology\<close>, the
  topology \<open>weak_conv_on\<close> is a \<open>limitin\<close> of.  Prokhorov's theorem turns
  tightness into relative compactness, and weak closedness collapses the
  closure: for a closed \<open>S\<close> with the two bounds the class is a compact subset of a metric space, the
  input @{thm [source] Metric_space.usc_measurable_selection} wants.\<close>

lemma covariation_class_subset_weak_topspace:
  "covariation_class S T x \<subseteq> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: ('n::finite pairpath) metric)))"
proof
  fix N :: "('n pairpath) measure"
  assume N: "N \<in> covariation_class S T x"
  show "N \<in> topspace (weak_conv_topology
      (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    using covariation_class_sets[OF N] prob_space.finite_measure[OF covariation_class_prob[OF N]] by simp
qed

theorem covariation_class_compactin_weak:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S"
  shows "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (covariation_class S T x)"
proof (rule compactin_of_seq_compact
    [OF metrizable_weak_conv_path_topology covariation_class_subset_weak_topspace])
  fix \<sigma> :: "nat \<Rightarrow> ('n pairpath) measure"
  assume "range \<sigma> \<subseteq> covariation_class S T x"
  then have mem: "\<sigma> m \<in> covariation_class S T x" for m by auto
  have "\<exists>r l. strict_mono r \<and> l \<in> covariation_class S T x
      \<and> weak_conv_on (\<sigma> \<circ> r) l sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule covariation_class_convergent_subsequence[where Qm = \<sigma>,
        OF T B0 B D0 D Sc mem])
  then show "\<exists>l r. l \<in> covariation_class S T x \<and> strict_mono r \<and> limitin
      (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (\<sigma> \<circ> r) l sequentially"
    by blast
qed

subsubsection \<open>Relative compactness and compactness for sets of positive semidefinite matrices\<close>

text \<open>Lemmas 2.2 and 2.3 of \<^cite>\<open>LaiShkolnikovSoner\<close> are stated for a set
  \<open>S \<subseteq> \<bbbS>\<^sup>n\<^sub>+\<close> of positive semidefinite matrices: bounded for relative
  compactness, compact and convex for compactness.  A bounded set of positive semidefinite matrices supplies
  both bounds the statements above take, with the same constant: a diagonal
  entry of a positive semidefinite matrix is nonnegative and at most its norm.\<close>

lemma psd_diag_le_norm:
  fixes a :: "real^'n::finite^'n"
  assumes psd: "psd a"
  shows "0 \<le> a $ j $ j \<and> a $ j $ j \<le> norm a"
proof
  show "0 \<le> a $ j $ j" by (rule psd_diag_nonneg[OF psd])
  have "a $ j $ j \<le> norm (a $ j)"
    using component_le_norm_cart[of "a $ j" j] by linarith
  also have "\<dots> \<le> norm a" by (rule Finite_Cartesian_Product.norm_nth_le)
  finally show "a $ j $ j \<le> norm a" .
qed

text \<open>For a bounded set of positive semidefinite matrices the
  class is relatively compact for weak convergence of laws on the path space.\<close>

theorem covariation_class_relatively_compact:
  fixes x :: "real^'n::finite" and S :: "(real^'n^'n) set"
  assumes T: "0 < T" and psd: "\<And>a. a \<in> S \<Longrightarrow> psd a" and bd: "bounded S"
  shows "compactin (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))
         closure_of covariation_class S T x)"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  from bd obtain B where B0: "0 < B" and B: "\<And>a. a \<in> S \<Longrightarrow> norm a \<le> B"
    unfolding bounded_pos by blast
  have D: "0 \<le> a $ j $ j \<and> a $ j $ j \<le> B" if a: "a \<in> S" for a j
    using psd_diag_le_norm[OF psd[OF a], of j] B[OF a] by linarith
  have met: "metrizable_space ?X"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  have sep: "separable_space ?X" by (rule separable_path_metric)
  have bound: "covariation_class S T x
      \<subseteq> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> covariation_class S T x"
    have "N (space N) \<le> ennreal 1"
      by (simp add: prob_space.emeasure_space_1[OF covariation_class_prob[OF N]])
    moreover have "sets N = sets (borel_of ?X)" by (rule covariation_class_sets[OF N])
    ultimately show "N \<in> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
      by simp
  qed
  have tight: "tight_on_set ?X (covariation_class S T x)"
    by (rule covariation_class_tight_on_set[OF T less_imp_le[OF B0] B less_imp_le[OF B0] D])
  show ?thesis by (rule tight_imp_relatively_compact[OF met sep bound tight])
qed

text \<open>For a compact set of positive semidefinite matrices the class is
  compact.  No convexity of \<open>S\<close> is needed: closedness of the class
  under weak limits needs only \<open>S\<close> closed, so convexity is not used.\<close>

theorem covariation_class_compact:
  fixes x :: "real^'n::finite" and S :: "(real^'n^'n) set"
  assumes T: "0 < T" and psd: "\<And>a. a \<in> S \<Longrightarrow> psd a" and cS: "compact S"
  shows "compactin (weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (covariation_class S T x)"
proof -
  from compact_imp_bounded[OF cS] obtain B where B0: "0 < B" and B: "\<And>a. a \<in> S \<Longrightarrow> norm a \<le> B"
    unfolding bounded_pos by blast
  have D: "0 \<le> a $ j $ j \<and> a $ j $ j \<le> B" if a: "a \<in> S" for a j
    using psd_diag_le_norm[OF psd[OF a], of j] B[OF a] by linarith
  show ?thesis
    by (rule covariation_class_compactin_weak[OF T less_imp_le[OF B0] B less_imp_le[OF B0] D
          compact_imp_closed[OF cS]])
qed

text \<open>The class packaged exactly as \<open>Metric_space.usc_measurable_selection\<close>
  consumes it: a compact metric space, the metric being the
  L\'evy--Prokhorov metric restricted to the class, and its topology the
  subspace topology of weak convergence.\<close>

theorem covariation_class_compact_metric_space:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S"
  shows "Metric_space (covariation_class S T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))"
    and "Metric_space.mtopology (covariation_class S T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))
      = subtopology (weak_conv_topology
          (mtopology_of (path_metric T :: ('n pairpath) metric)))
          (covariation_class S T x)"
    and "compact_space (Metric_space.mtopology (covariation_class S T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))))"
proof -
  interpret LP: Levy_Prokhorov "mspace (path_metric T :: ('n pairpath) metric)"
      "mdist (path_metric T :: ('n pairpath) metric)"
    by (simp add: Levy_Prokhorov_def)
  have Xeq: "LP.mtopology = mtopology_of (path_metric T :: ('n pairpath) metric)"
    by (simp add: mtopology_of_def)
  have sepLP: "separable_space LP.mtopology"
    using separable_path_metric Xeq by simp
  have LPtop: "LP.LPm.mtopology
      = weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
    using LP.LPmtopology_eq_weak_conv_topology[OF sepLP] Xeq by simp
  have subC: "covariation_class S T x \<subseteq> LP.\<P>"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> covariation_class S T x"
    have p: "prob_space N" by (rule covariation_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with covariation_class_sets[OF N] Xeq show "N \<in> LP.\<P>" by (simp add: LP.inP_iff)
  qed
  have SMloc: "Submetric LP.\<P> LP.LPm (covariation_class S T x)"
    unfolding Submetric_def Submetric_axioms_def
    using LP.LPm.Metric_space_axioms subC by blast
  interpret SM: Submetric "LP.\<P>" "LP.LPm" "covariation_class S T x"
    by (rule SMloc)
  show ms: "Metric_space (covariation_class S T x) LP.LPm"
    by (rule SM.sub.Metric_space_axioms)
  show top: "SM.sub.mtopology
      = subtopology (weak_conv_topology
          (mtopology_of (path_metric T :: ('n pairpath) metric)))
          (covariation_class S T x)"
    using SM.mtopology_submetric LPtop by simp
  show "compact_space SM.sub.mtopology"
    unfolding top
    by (rule compact_space_subtopology[OF covariation_class_compactin_weak[OF T B0 B D0 D Sc]])
qed

subsection \<open>A measurable optimizer: Larsson--Ruf Proposition 2.2(ii)\<close>

text \<open>The supremum defining the value is attained, and the optimizer can be chosen
  measurably in the starting point: the class at the origin is a compact
  metric space (@{thm [source] covariation_class_compact_metric_space}),
  the payoff is jointly upper semicontinuous
  (@{thm [source] ess_inf_pexit_pshift_usc}), and
  @{thm [source] Metric_space.usc_measurable_selection} does the rest.

  Two facts connect these to the theorem.  First, upper semicontinuity in
  the law is the joint statement along a constant parameter sequence, and
  closedness in a metric topology is sequential closedness
  (@{thm [source] Metric_space.closure_of_sequentially}).  Second, the
  supremum over a closed, hence compact, subset is upper semicontinuous
  in the parameter: it is the supremum of the real exit functional
  (@{thm [source] ess_inf_pexit_Sup_eq_vshift}), to which Berge's theorem
  applies (@{thm [source] vshift_sup_usc}).

  After @{thm [source] covariation_class_shift_image} the functional
  whose supremum is @{term covariation_val} is a function of the starting point
  and a member of the fixed class at the origin.  The selection theorem's
  measurability hypothesis --- that the supremum over each closed set be
  measurable in the parameter --- comes from joint upper semicontinuity,
  in turn from joint continuity of the shift: shifting a path by a
  constant vector moves it by exactly that vector in the sup metric, so a
  uniformly continuous test function is displaced uniformly.  Weak
  convergence may be tested against bounded uniformly continuous
  functions (@{thm [source] mweak_conv_fin.mweak_conv_eq1}), so no
  tightness is needed; @{thm [source] weak_conv_on_pushforward_uniform}
  packages the argument.\<close>

theorem covariation_val_measurable_selector:
  fixes K :: "(real^'n::finite) set" and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and K: "closed K"
  obtains Sel where
    "Sel \<in> borel \<rightarrow>\<^sub>M borel_of (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and "\<And>y. Sel y \<in> covariation_class S T 0"
    and "\<And>y. pshift_law T y (Sel y) \<in> covariation_class S T y"
    and "\<And>y. ess_inf_time (pshift_law T y (Sel y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K y"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?C = "covariation_class S T (0 :: real^'n)"
  let ?g = "\<lambda>(y :: real^'n) (R :: ('n pairpath) measure).
      ess_inf_time (pshift_law T y R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
  have T0: "0 \<le> T" using T by simp
  interpret MC: Metric_space "covariation_class S T (0 :: real^'n)"
      "Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))"
    by (rule covariation_class_compact_metric_space(1)[OF T B0 B D0 D Sc])
  have Ctop: "MC.mtopology = subtopology ?W ?C"
    by (rule covariation_class_compact_metric_space(2)[OF T B0 B D0 D Sc])
  have Ccpt: "compact_space MC.mtopology"
    by (rule covariation_class_compact_metric_space(3)[OF T B0 B D0 D Sc])
  have Cne: "?C \<noteq> {}" by (rule covariation_class_nonempty[OF T0 Sc SST])
  have prC: "prob_space R" if "R \<in> ?C" for R by (rule covariation_class_prob[OF that])
  have stC: "sets R = sets ?B" if "R \<in> ?C" for R
    by (rule covariation_class_sets[OF that])
  have convC: "weak_conv_on sq Rl sequentially ?X"
    if "limitin MC.mtopology sq Rl sequentially" for sq Rl
    using that unfolding Ctop by (simp add: limitin_subtopology)
  have limC: "Rl \<in> ?C" if "limitin MC.mtopology sq Rl sequentially" for sq Rl
    using that unfolding Ctop by (simp add: limitin_subtopology)
  \<comment> \<open>the first hypothesis: upper semicontinuity in the law\<close>
  have hypA: "openin MC.mtopology {R \<in> ?C. ?g y R < c}" for y c
  proof -
    let ?A = "{R \<in> ?C. c \<le> ?g y R}"
    have Asub: "?A \<subseteq> ?C" by blast
    have Acl: "MC.mtopology closure_of ?A \<subseteq> ?A"
    proof
      fix Rl assume "Rl \<in> MC.mtopology closure_of ?A"
      then obtain sq where sq: "range sq \<subseteq> ?A \<inter> ?C"
        and lim: "limitin MC.mtopology sq Rl sequentially"
        by (auto simp: MC.closure_of_sequentially)
      have memC: "sq m \<in> ?C" for m using sq by blast
      have memA: "c \<le> ?g y (sq m)" for m using sq by blast
      have RlC: "Rl \<in> ?C" by (rule limC[OF lim])
      have wc: "weak_conv_on sq Rl sequentially ?X" by (rule convC[OF lim])
      have "Limsup sequentially (\<lambda>m. ?g y (sq m)) \<le> ?g y Rl"
        by (rule ess_inf_pexit_pshift_usc
            [OF T0 K tendsto_const prC[OF memC] stC[OF memC]
                prC[OF RlC] stC[OF RlC] wc])
      moreover have "c \<le> Liminf sequentially (\<lambda>m. ?g y (sq m))"
        using memA by (intro Liminf_bounded always_eventually) blast
      moreover have "Liminf sequentially (\<lambda>m. ?g y (sq m))
          \<le> Limsup sequentially (\<lambda>m. ?g y (sq m))"
        by (rule Liminf_le_Limsup) simp
      ultimately have "c \<le> ?g y Rl" by simp
      with RlC show "Rl \<in> ?A" by blast
    qed
    have Asub': "?A \<subseteq> topspace MC.mtopology" using Asub by simp
    have "MC.mtopology closure_of ?A = ?A"
      using Acl closure_of_subset[OF Asub'] by blast
    then have "closedin MC.mtopology ?A" by (simp add: closure_of_eq)
    then have "openin MC.mtopology (topspace MC.mtopology - ?A)"
      by (rule openin_diff[OF openin_topspace])
    moreover have "topspace MC.mtopology - ?A = {R \<in> ?C. ?g y R < c}"
      by (auto simp: not_le)
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>the second hypothesis: the supremum over a compact set is measurable,
    being upper semicontinuous by Berge's theorem\<close>
  have hypB: "(\<lambda>y. Sup (?g y ` Cs)) \<in> borel_measurable (borel :: (real^'n) measure)"
    if Cl: "closedin MC.mtopology Cs" for Cs
  proof (cases "Cs = {}")
    case False
    let ?A = "{p :: (real^'n) \<times> (real^'n^'n). fst p \<in> - K}"
    let ?f = "\<lambda>y. Sup (vshift T ?A (y, 0) ` Cs)"
    have CsC: "Cs \<subseteq> ?C" using Cl by (metis closedin_subset MC.topspace_mtopology)
    have Cscpt: "compactin ?W Cs"
      using closedin_compact_space[OF Ccpt Cl] unfolding Ctop by (simp add: compactin_subtopology)
    have Aopen: "open ?A"
      using open_vimage_fst[OF open_Compl[OF K]] by (simp add: vimage_def)
    have "open {y. ?f y < c}" for c
    proof (subst open_subopen, safe)
      fix y assume lt: "?f y < c"
      have "eventually (\<lambda>z. Sup (vshift T ?A z ` Cs) < c) (nhds (y, 0))"
        by (rule vshift_sup_usc[OF T0 Aopen Cscpt False _ _ lt]) (use CsC stC prC in auto)
      then have "eventually (\<lambda>z. ?f z < c) (nhds y)"
        by (rule eventually_compose_filterlim) (auto intro!: tendsto_intros filterlim_ident)
      then obtain U where "open U" "y \<in> U" "\<forall>z\<in>U. ?f z < c"
        unfolding eventually_nhds by blast
      then show "\<exists>U. open U \<and> y \<in> U \<and> U \<subseteq> {y. ?f y < c}" by blast
    qed
    then have "(\<lambda>y. ennreal (?f y)) \<in> borel_measurable borel"
      by (intro measurable_compose[OF _ measurable_ennreal] borel_measurableI_less)
        (simp add: borel_open)
    moreover have "Sup (?g y ` Cs) = ennreal (?f y)" for y
      by (rule ess_inf_pexit_Sup_eq_vshift[OF T0 CsC False])
    ultimately show ?thesis by simp
  qed simp
  \<comment> \<open>the selection theorem, and the transfer back to the value function\<close>
  obtain s where sm: "s \<in> (borel :: (real^'n) measure) \<rightarrow>\<^sub>M borel_of MC.mtopology"
    and sC: "\<And>y. s y \<in> ?C"
    and sopt: "\<And>y. y \<in> space (borel :: (real^'n) measure)
        \<Longrightarrow> ?g y (s y) = Sup (?g y ` ?C)"
    by (rule MC.usc_measurable_selection
        [where P = "borel :: (real^'n) measure" and f = ?g, OF Ccpt Cne]) (use hypA hypB in blast)+
  have topC: "?C \<subseteq> topspace ?W"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> ?C"
    have p: "prob_space N" by (rule covariation_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with covariation_class_sets[OF N] show "N \<in> topspace ?W" by simp
  qed
  have smW: "s \<in> (borel :: (real^'n) measure) \<rightarrow>\<^sub>M borel_of ?W"
  proof (rule measurable_sigma_sets)
    show "sets (borel_of ?W) = sigma_sets (topspace ?W) {U. openin ?W U}"
      by (rule sets_borel_of)
    have "U \<subseteq> topspace ?W" if "openin ?W U" for U by (rule openin_subset[OF that])
    then show "{U. openin ?W U} \<subseteq> Pow (topspace ?W)" by auto
    show "s \<in> space (borel :: (real^'n) measure) \<rightarrow> topspace ?W"
      using sC topC by auto
    show "s -` U \<inter> space (borel :: (real^'n) measure)
        \<in> sets (borel :: (real^'n) measure)" if "U \<in> {U. openin ?W U}" for U
    proof -
      have "openin MC.mtopology (U \<inter> ?C)"
        unfolding Ctop using that by (auto simp: openin_subtopology)
      then have "U \<inter> ?C \<in> sets (borel_of MC.mtopology)" by (rule borel_of_open)
      then have "s -` (U \<inter> ?C) \<inter> space (borel :: (real^'n) measure)
          \<in> sets (borel :: (real^'n) measure)" by (rule measurable_sets[OF sm])
      moreover have "s -` (U \<inter> ?C) = s -` U" using sC by auto
      ultimately show ?thesis by simp
    qed
  qed
  have shiftmem: "pshift_law T y (s y) \<in> covariation_class S T y" for y
    using covariation_class_pshift[OF T0 sC, of y] by simp
  have supeq: "Sup (?g y ` ?C) = covariation_val S T K y" for y
  proof -
    have "covariation_class S T y = pshift_law T y ` ?C"
      by (rule covariation_class_shift_image[OF T0])
    then have "(\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
          ` covariation_class S T y = ?g y ` ?C"
      by (simp add: image_image)
    then show ?thesis unfolding covariation_val_def by simp
  qed
  have sval: "ess_inf_time (pshift_law T y (s y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      = covariation_val S T K y" for y
    using sopt[of y] supeq[of y] by simp
  show ?thesis by (rule that[OF smW sC shiftmem sval])
qed

text \<open>In particular the supremum defining the value is attained at every starting point.\<close>

theorem covariation_val_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
  assumes T: "0 < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S" and K: "closed K"
  shows "\<exists>Q \<in> covariation_class S T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = covariation_val S T K x"
proof -
  obtain Sel where "\<And>y. pshift_law T y (Sel y) \<in> covariation_class S T y"
    and "\<And>y. ess_inf_time (pshift_law T y (Sel y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      = covariation_val S T K y"
    using covariation_val_measurable_selector[OF T B0 B D0 D Sc SST K] by metis
  then show ?thesis by blast
qed

subsection \<open>The optimizer as a Giry-monad kernel\<close>

text \<open>Kernel pasting glues with the Giry monad's @{term bind}, which wants
  the continuation as a measurable map into @{term prob_algebra} --- the
  measurable space of probability measures --- not merely into the Borel
  algebra of the weak topology.  The AFP supplies the bridge: on a Polish
  space the two agree once one restricts to probability measures with the
  right \<open>sets\<close> (@{thm [source] weak_conv_topology_eq_prob_algebra}), and
  that is where the selector lands anyway.  The same bridge, read backwards,
  gives the measurability into the compact class that the rounding step
  of the proof below needs.\<close>

theorem covariation_class_kglue_law':
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n" and \<sigma> :: "real^'n^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and B0: "0 \<le> B"
    and B: "\<And>a :: real^'n^'n. a \<in> S \<Longrightarrow> norm a \<le> B"
    and D0: "0 \<le> D"
    and D: "\<And>(a :: real^'n^'n) j. a \<in> S \<Longrightarrow> 0 \<le> a $ j $ j \<and> a $ j $ j \<le> D"
    and Sc: "closed S" and Sv: "convex S"
    and SST: "\<sigma> ** transpose \<sigma> \<in> S"
    and T0: "0 < T"
    and Q: "Q \<in> covariation_class S r x"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and Kc: "\<And>\<omega>. Kr \<omega> \<in> covariation_class S (T - r) 0"
  shows "kglue_law' r T Kr Q \<in> covariation_class S T x"
proof -
  let ?s = "T - r"
  let ?C0 = "covariation_class S ?s (0::real^'n)"
  let ?dd = "Levy_Prokhorov.LPm (mspace (path_metric ?s :: ('n pairpath) metric))
      (mdist (path_metric ?s :: ('n pairpath) metric))"
  let ?MR = "(path_borel ?s :: ('n pairpath) measure)"
  let ?X = "mtopology_of (path_metric r :: ('n pairpath) metric)"
  let ?Y = "mtopology_of (path_metric ?s :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have s0: "0 < ?s" using rT by simp
  have s0': "0 \<le> ?s" using s0 by simp
  have rT': "r \<le> T" using rT by simp
  have setsQ: "sets Q = sets (borel_of ?X)" by (rule covariation_class_sets[OF Q])
  have PQ: "prob_space Q" by (rule covariation_class_prob[OF Q])
  interpret MC: Metric_space "covariation_class S ?s (0::real^'n)" ?dd
    by (rule covariation_class_compact_metric_space(1)[OF s0 B0 B D0 D Sc])
  have Ctop: "MC.mtopology = subtopology (weak_conv_topology ?Y) ?C0"
    by (rule covariation_class_compact_metric_space(2)[OF s0 B0 B D0 D Sc])
  have Ccpt: "compact_space MC.mtopology"
    by (rule covariation_class_compact_metric_space(3)[OF s0 B0 B D0 D Sc])
  have Cne: "?C0 \<noteq> {}" by (rule covariation_class_nonempty[OF s0' Sc SST])
  \<comment> \<open>the kernel is measurable into the class, from the time-\<open>r\<close> \<open>\<sigma>\<close>-algebra\<close>
  have Kb: "Kr \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r \<rightarrow>\<^sub>M borel_of MC.mtopology"
  proof -
    have nf: "sets (natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r) = sets Q"
      unfolding natural_filtration_cong_space[OF sets_eq_imp_space_eq[OF setsQ]] setsQ
      by (rule sets_natural_filtration_path[OF r])
    have "Q \<rightarrow>\<^sub>M restrict_space (borel_of (weak_conv_topology ?Y))
        {N. prob_space N \<and> sets N = sets ?MR} = Q \<rightarrow>\<^sub>M prob_algebra ?MR"
      using measurable_cong_sets[OF refl
          weak_conv_topology_eq_prob_algebra[OF Polish_space_path_metric]]
      by (simp add: borel_of_subtopology)
    then have "Kr \<in> Q \<rightarrow>\<^sub>M restrict_space (borel_of (weak_conv_topology ?Y))
        {N. prob_space N \<and> sets N = sets ?MR}"
      using Kp by simp
    then have "Kr \<in> Q \<rightarrow>\<^sub>M borel_of (weak_conv_topology ?Y)"
      unfolding measurable_restrict_space2_iff by blast
    then show ?thesis unfolding Ctop borel_of_subtopology measurable_cong_sets[OF nf refl]
      by (rule measurable_restrict_space2[rotated]) (use Kc in auto)
  qed
  \<comment> \<open>round the kernel to a dense sequence of the compact class\<close>
  obtain z :: "nat \<Rightarrow> ('n pairpath) measure"
    and Nm :: "nat \<Rightarrow> 'n pairpath \<Rightarrow> nat"
    where zC: "\<And>j. z j \<in> ?C0"
    and Nmeas: "\<And>m. Nm m \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M count_space UNIV"
    and zclose: "\<And>m \<omega>. ?dd (z (Nm m \<omega>)) (Kr \<omega>) < (1/2)^m"
    by (rule MC.countably_valued_approx[OF MC.compact_space_imp_separable[OF Ccpt] Cne Kb Kc]) blast
  have NmQ: "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" for m
  proof -
    interpret MQ0: martingale Q "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      "0::real" "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n"
      by (rule covariation_class_martingale_fst[OF Q])
    show ?thesis by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nmeas])
  qed
  \<comment> \<open>each rounded glue is in the class, and is the kernel glue at the rounding\<close>
  have memm: "kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q \<in> covariation_class S T x" for m
  proof -
    have "kglue_law r T (Nm m) Q z \<in> covariation_class S T x"
      by (rule covariation_class_kglue_law[OF r rT' Sc Sv B0 B Q zC Nmeas])
    moreover have "kglue_law r T (Nm m) Q z = kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q"
    proof (rule kglue_law_eq_kglue_law'[OF r rT' PQ _ setsQ _ NmQ])
      show "prob_space (z j)" for j by (rule covariation_class_prob[OF zC])
      show "sets (z j) = sets ?MR" for j by (rule covariation_class_sets[OF zC])
      show "(\<lambda>\<omega>. z (Nm m \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR"
      proof (rule measurable_compose_countable[where f = "\<lambda>j (_ :: 'n pairpath). z j"])
        show "(\<lambda>\<omega>. z j) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for j
          using covariation_class_prob[OF zC] covariation_class_sets[OF zC]
          by (simp add: measurable_const space_prob_algebra)
        show "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
      qed
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>the kernels converge pointwise, hence the semidirect products do\<close>
  have Kpm: "(\<lambda>\<omega>. z (Nm m \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for m
  proof (rule measurable_compose_countable[where f = "\<lambda>j (_ :: 'n pairpath). z j"])
    show "(\<lambda>\<omega>. z j) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for j
      using covariation_class_prob[OF zC] covariation_class_sets[OF zC]
      by (simp add: measurable_const space_prob_algebra)
    show "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" by (rule NmQ)
  qed
  have kconv: "weak_conv_on (\<lambda>m. z (Nm m \<omega>)) (Kr \<omega>) sequentially ?Y" for \<omega>
  proof -
    have "limitin MC.mtopology (\<lambda>m. z (Nm m \<omega>)) (Kr \<omega>) sequentially"
      by (rule MC.limitin_of_dist_half[OF zC Kc zclose])
    then show ?thesis unfolding Ctop by (simp add: limitin_subtopology)
  qed
  have swc: "weak_conv_on (\<lambda>m. ksemi Q ?MR (\<lambda>\<omega>. z (Nm m \<omega>)))
      (ksemi Q ?MR Kr) sequentially (prod_topology ?X ?Y)"
    by (rule ksemi_weak_conv[OF PQ setsQ second_countable_path_metric
          second_countable_path_metric Kpm Kp]) (rule kconv)
  \<comment> \<open>push forward along the continuous glue\<close>
  have cglue: "continuous_map (prod_topology ?X ?Y)
      (mtopology_of (path_metric T :: ('n pairpath) metric))
      (\<lambda>p. pglue r T (fst p) (snd p))"
    using Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pglue[OF r rT']]
    by simp
  have gconv: "weak_conv_on (\<lambda>m. kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q)
      (kglue_law' r T Kr Q) sequentially
      (mtopology_of (path_metric T :: ('n pairpath) metric))"
    using weak_conv_on_pushforward[OF cglue swc]
    unfolding kglue_law'_def process_law_def by simp
  \<comment> \<open>weak closedness finishes\<close>
  have pl: "prob_space (kglue_law' r T Kr Q)"
    by (rule prob_space_kglue_law'[OF r rT' PQ setsQ Kp])
  show ?thesis
    by (rule covariation_class_weak_closed[OF T0 B0 B D0 D Sc memm gconv pl sets_kglue_law'])
qed


(*<*)
end
(*>*)
