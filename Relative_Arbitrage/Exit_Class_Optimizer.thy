section \<open>Attainment, the measurable optimizer, and the semidirect product\<close>

(*<*)
theory Exit_Class_Optimizer
  imports Exit_Class_Pasting
    "Semicontinuous_Analysis.Semicontinuous_Selection"
    "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Path_Spaces.Path_Exit_Times"
    Path_Law_Sampling
begin

(*>*)

section \<open>The clauses of Theorem 1.1 proved for the paper's own \<open>v\<close>\<close>

text \<open>The clauses of Theorem 1.1 proved for \<open>exit_val\<close> --- the faithful
  rendering of Eq. (1.6) --- collected in one place.

  Clause (2), the viscosity property, needs the dynamic programming
  principle of Proposition 2.4 and, on top of that, Section 3's
  It\<open>\<^bold>o\<close>/SDE layer, and is not covered here.  Clause (3) is here only for
  the ball; the interior value for \<open>n - k \<ge> 2\<close> remains unproved.
  Clause (4), uniqueness, is \<open>Value_Function_Uniqueness.theorem_1_1_uniqueness_general\<close>,
  a statement about viscosity solutions rather than about \<open>exit_val\<close>.\<close>

section \<open>The supremum in (1.6) is attained\<close>




theorem exit_val_attained:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  shows "\<exists>Q \<in> exit_class k L T x.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K x"
proof -
  let ?C = "exit_class k L T x"
  let ?S = "\<lambda>Q :: ('n pairpath) measure.
      ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
  let ?Y = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'n) metric)"
  let ?p = "\<lambda>Q :: ('n pairpath) measure. distr Q (borel_of ?Y) (pfst T)"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L by simp
  have ne: "?C \<noteq> {}"
    using exit_class_shift_image[OF T0, of k L x]
      exit_class_nonempty[OF T0 L] by auto
  have imne: "?S ` ?C \<noteq> {}" using ne by simp
  obtain f :: "nat \<Rightarrow> ennreal" where finc: "incseq f"
    and frange: "range f \<subseteq> ?S ` ?C"
    and fsup: "Sup (?S ` ?C) = (SUP i. f i)"
    using ennreal_Sup_countable_SUP[OF imne] by blast
  have "\<forall>i. \<exists>Q. Q \<in> ?C \<and> f i = ?S Q" using frange by blast
  then obtain Qm :: "nat \<Rightarrow> ('n pairpath) measure"
    where Qm: "\<And>i. Qm i \<in> ?C" and fQ: "\<And>i. f i = ?S (Qm i)" by metis
  have sub: "\<exists>a Q. strict_mono a \<and> Q \<in> ?C
      \<and> weak_conv_on (Qm \<circ> a) Q sequentially
          (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule exit_class_convergent_subsequence[OF T L0]) (rule Qm)
  obtain a Q where sm: "strict_mono a" and Qc: "Q \<in> ?C"
    and wc: "weak_conv_on (Qm \<circ> a) Q sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
    using sub by blast
  have pQ: "prob_space (Qm i)" for i by (rule exit_class_prob[OF Qm])
  have pQc: "prob_space Q" by (rule exit_class_prob[OF Qc])
  have wcY: "weak_conv_on (\<lambda>i. ?p (Qm (a i))) (?p Q) sequentially ?Y"
  proof -
    have "weak_conv_on (\<lambda>i. distr ((Qm \<circ> a) i) (borel_of ?Y) (pfst T))
        (distr Q (borel_of ?Y) (pfst T)) sequentially ?Y"
      by (rule weak_conv_on_pushforward
          [OF Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pfst[OF T0]] wc])
    then show ?thesis by simp
  qed
  have lim: "Limsup sequentially (\<lambda>i. ess_inf_time (?p (Qm (a i))) (pexit T K))
      \<le> ess_inf_time (?p Q) (pexit T K)"
  proof (rule ess_inf_pexit_usc[OF T K wcY])
    show "prob_space (?p (Qm (a i)))" for i
      by (rule prob_space.prob_space_distr[OF pQ pfst_measurable[OF T0]])
        (rule exit_class_sets[OF Qm])
    show "prob_space (?p Q)"
      by (rule prob_space.prob_space_distr[OF pQc pfst_measurable[OF T0]])
        (rule exit_class_sets[OF Qc])
  qed
  have eqS: "ess_inf_time (?p R) (pexit T K) = ?S R" if "R \<in> ?C" for R
    by (rule ess_inf_time_pfst[OF T0 K exit_class_sets[OF that]])
  have lim': "Limsup sequentially (\<lambda>i. ?S (Qm (a i))) \<le> ?S Q"
    using lim by (simp add: eqS[OF Qm] eqS[OF Qc])
  have "f \<longlonglongrightarrow> (SUP i. f i)" using finc by (rule LIMSEQ_SUP)
  then have "(f \<circ> a) \<longlonglongrightarrow> (SUP i. f i)"
    by (rule LIMSEQ_subseq_LIMSEQ[OF _ sm])
  then have "Limsup sequentially (\<lambda>i. ?S (Qm (a i))) = (SUP i. f i)"
    using fQ by (simp add: lim_imp_Limsup o_def)
  with lim' fsup have ge: "Sup (?S ` ?C) \<le> ?S Q" by simp
  have le: "?S Q \<le> Sup (?S ` ?C)" using Qc by (intro Sup_upper imageI)
  from ge le have "?S Q = Sup (?S ` ?C)" by simp
  then show ?thesis using Qc unfolding exit_val_def by blast
qed

text \<open>The measurable selection theorem for upper semicontinuous payoffs,
  Bertsekas--Shreve (1978) Prop. 7.33, lives in
  @{theory Semicontinuous_Analysis.Semicontinuous_Selection}, as
  \<open>Metric_space.usc_measurable_selection\<close>.\<close>

section \<open>The paper's class is a compact metric space of measures\<close>

text \<open>The AFP entry \<open>Levy_Prokhorov_Metric\<close> makes the space of finite
  Borel measures on a separable metric space a metric space for the
  L\'evy--Prokhorov distance, whose topology is \<open>weak_conv_topology\<close>, the
  topology \<open>weak_conv_on\<close> is a \<open>limitin\<close> of.  Prokhorov's theorem turns
  tightness into relative compactness, and weak closedness collapses the
  closure: the paper's class is a compact subset of a metric space, the
  input @{thm [source] Metric_space.usc_measurable_selection} wants.\<close>

theorem exit_class_compactin_weak:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "compactin (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))
      (exit_class k L T x)"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?C = "exit_class k L T x"
  interpret LP: Levy_Prokhorov "mspace (path_metric T :: ('n pairpath) metric)"
      "mdist (path_metric T :: ('n pairpath) metric)"
    by (simp add: Levy_Prokhorov_def)
  have Xeq: "LP.mtopology = ?X" by (simp add: mtopology_of_def)
  have sep: "separable_space ?X" by (rule separable_path_metric)
  have met: "metrizable_space ?X"
    unfolding mtopology_of_def
    by (rule Metric_space.metrizable_space_mtopology[OF Metric_space_mspace_mdist])
  have sepLP: "separable_space LP.mtopology" using sep Xeq by simp
  have LPtop: "LP.LPm.mtopology = ?W"
    using LP.LPmtopology_eq_weak_conv_topology[OF sepLP] Xeq by simp
  have bound: "?C \<subseteq> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> ?C"
    have "prob_space N" by (rule exit_class_prob[OF N])
    then have "N (space N) \<le> ennreal 1" by (simp add: prob_space.emeasure_space_1)
    moreover have "sets N = sets (borel_of ?X)" by (rule exit_class_sets[OF N])
    ultimately show "N \<in> {N. N (space N) \<le> ennreal 1 \<and> sets N = sets (borel_of ?X)}"
      by simp
  qed
  have topC: "?C \<subseteq> topspace ?W"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> ?C"
    have p: "prob_space N" by (rule exit_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with exit_class_sets[OF N] show "N \<in> topspace ?W" by simp
  qed
  have tight: "tight_on_set ?X ?C"
    by (rule tight_on_set_paper_pair_class[OF T L]) simp
  have rc: "compactin ?W (?W closure_of ?C)"
    by (rule tight_imp_relatively_compact[OF met sep bound tight])
  have cl: "?W closure_of ?C \<subseteq> ?C"
  proof
    fix Q :: "('n pairpath) measure"
    assume Qc: "Q \<in> ?W closure_of ?C"
    then have QL: "Q \<in> LP.LPm.mtopology closure_of ?C" using LPtop by simp
    then obtain sq :: "nat \<Rightarrow> ('n pairpath) measure"
      where sq: "range sq \<subseteq> ?C \<inter> LP.\<P>"
        and lim: "limitin LP.LPm.mtopology sq Q sequentially"
      by (auto simp: LP.LPm.closure_of_sequentially)
    have QP: "Q \<in> LP.\<P>" using QL by (auto simp: LP.LPm.closure_of_sequentially)
    have mem: "sq i \<in> ?C" for i using sq by blast
    have wc: "weak_conv_on sq Q sequentially ?X" using lim LPtop by simp
    have prob: "prob_space Q"
      by (rule weak_conv_on_prob_space[OF wc]) (rule exit_class_prob[OF mem])
    have setsQ: "sets Q = sets (borel_of ?X)"
      using QP Xeq by (simp add: LP.inP_iff)
    show "Q \<in> ?C" by (rule exit_class_weak_closed[OF T L mem wc prob setsQ])
  qed
  have sub: "?C \<subseteq> ?W closure_of ?C" by (rule closure_of_subset[OF topC])
  from cl sub have "?W closure_of ?C = ?C" by blast
  with rc show ?thesis by simp
qed

section \<open>Joint continuity of the shift\<close>

text \<open>After @{thm [source] exit_class_shift_image} the functional
  whose supremum is @{term exit_val} is a function of the starting point
  and a member of the fixed class at the origin.  The selection theorem's
  measurability hypothesis --- that the supremum over each closed set be
  measurable in the parameter --- comes from joint upper semicontinuity,
  in turn from joint continuity of the shift: shifting a path by a
  constant vector moves it by exactly that vector in the sup metric, so a
  uniformly continuous test function is displaced uniformly.  Weak
  convergence may be tested against bounded uniformly continuous
  functions (@{thm [source] mweak_conv_fin.mweak_conv_eq1}), so no
  tightness is needed.\<close>




theorem exit_class_compact_metric_space:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "Metric_space (exit_class k L T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))"
    and "Metric_space.mtopology (exit_class k L T x)
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))
      = subtopology (weak_conv_topology
          (mtopology_of (path_metric T :: ('n pairpath) metric)))
          (exit_class k L T x)"
    and "compact_space (Metric_space.mtopology (exit_class k L T x)
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
  have subC: "exit_class k L T x \<subseteq> LP.\<P>"
  proof
    fix N :: "('n pairpath) measure"
    assume N: "N \<in> exit_class k L T x"
    have p: "prob_space N" by (rule exit_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with exit_class_sets[OF N] Xeq show "N \<in> LP.\<P>" by (simp add: LP.inP_iff)
  qed
  have SMloc: "Submetric LP.\<P> LP.LPm (exit_class k L T x)"
    unfolding Submetric_def Submetric_axioms_def
    using LP.LPm.Metric_space_axioms subC by blast
  interpret SM: Submetric "LP.\<P>" "LP.LPm" "exit_class k L T x"
    by (rule SMloc)
  show ms: "Metric_space (exit_class k L T x) LP.LPm"
    by (rule SM.sub.Metric_space_axioms)
  show top: "SM.sub.mtopology
      = subtopology (weak_conv_topology
          (mtopology_of (path_metric T :: ('n pairpath) metric)))
          (exit_class k L T x)"
    using SM.mtopology_submetric LPtop by simp
  show "compact_space SM.sub.mtopology"
    unfolding top
    by (rule compact_space_subtopology[OF exit_class_compactin_weak[OF T L]])
qed

section \<open>A measurable optimizer: Larsson--Ruf Proposition 2.2(ii)\<close>

text \<open>The optimizer of @{thm [source] exit_val_attained} can be chosen
  measurably in the starting point: the class at the origin is a compact
  metric space (@{thm [source] exit_class_compact_metric_space}),
  the payoff is jointly upper semicontinuous
  (@{thm [source] ess_inf_pexit_pshift_usc}), and
  @{thm [source] Metric_space.usc_measurable_selection} does the rest.

  Two facts connect these to the theorem.  First, upper semicontinuity in
  the law is the joint statement along a constant parameter sequence, and
  closedness in a metric topology is sequential closedness
  (@{thm [source] Metric_space.closure_of_sequentially}).  Second, the
  supremum over a closed, hence compact, subset is upper semicontinuous
  in the parameter: for each parameter and each \<open>b < c\<close>, pick a law
  beating \<open>b\<close>, extract a convergent subsequence by
  @{thm [source] Metric_space.compactin_sequentially}, and let the joint
  statement close the gap --- attainment is not needed, only \<open>b < c\<close> for
  every \<open>b\<close> below \<open>c\<close> (@{thm [source] ennreal_strict_between}).\<close>

theorem exit_val_measurable_selector:
  fixes K :: "(real^'n::finite) set"
  assumes T: "0 < T" and L: "1 \<le> L" and K: "closed K"
  obtains S where
    "S \<in> borel \<rightarrow>\<^sub>M borel_of (weak_conv_topology
        (mtopology_of (path_metric T :: ('n pairpath) metric)))"
    and "\<And>y. S y \<in> exit_class k L T 0"
    and "\<And>y. pshift_law T y (S y) \<in> exit_class k L T y"
    and "\<And>y. ess_inf_time (pshift_law T y (S y))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K y"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?W = "weak_conv_topology (mtopology_of (path_metric T :: ('n pairpath) metric))"
  let ?C = "exit_class k L T (0 :: real^'n)"
  let ?g = "\<lambda>(y :: real^'n) (R :: ('n pairpath) measure).
      ess_inf_time (pshift_law T y R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L by simp
  interpret MC: Metric_space "exit_class k L T (0 :: real^'n)"
      "Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))"
    by (rule exit_class_compact_metric_space(1)[OF T L0])
  have Ctop: "MC.mtopology = subtopology ?W ?C"
    by (rule exit_class_compact_metric_space(2)[OF T L0])
  have Ccpt: "compact_space MC.mtopology"
    by (rule exit_class_compact_metric_space(3)[OF T L0])
  have Cne: "?C \<noteq> {}" by (rule exit_class_nonempty[OF T0 L])
  have prC: "prob_space R" if "R \<in> ?C" for R by (rule exit_class_prob[OF that])
  have stC: "sets R = sets ?B" if "R \<in> ?C" for R
    by (rule exit_class_sets[OF that])
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
            [OF T K tendsto_const prC[OF memC] stC[OF memC]
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
  \<comment> \<open>the second hypothesis: the supremum over a compact set is measurable\<close>
  have hypB: "(\<lambda>y. Sup (?g y ` Cs)) \<in> borel_measurable (borel :: (real^'n) measure)"
    if Cl: "closedin MC.mtopology Cs" for Cs
  proof (rule borel_measurableI_ge)
    fix c :: ennreal
    have CsC: "Cs \<subseteq> ?C" using Cl by (metis closedin_subset MC.topspace_mtopology)
    have Cscpt: "compactin MC.mtopology Cs"
      by (rule closedin_compact_space[OF Ccpt Cl])
    have "closed {y :: real^'n. c \<le> Sup (?g y ` Cs)}"
    proof (subst closed_sequential_limits, intro allI impI)
      fix ym :: "nat \<Rightarrow> real^'n" and y :: "real^'n"
      assume h: "(\<forall>m. ym m \<in> {y. c \<le> Sup (?g y ` Cs)}) \<and> ym \<longlonglongrightarrow> y"
      then have cs: "c \<le> Sup (?g (ym m) ` Cs)" for m by blast
      have yc: "ym \<longlonglongrightarrow> y" using h by blast
      have below: "b \<le> Sup (?g y ` Cs)" if b: "b < c" for b
      proof -
        have "\<exists>R. R \<in> Cs \<and> b < ?g (ym m) R" for m
        proof -
          have "b < Sup (?g (ym m) ` Cs)" using b cs[of m] by simp
          then show ?thesis by (auto simp: less_Sup_iff)
        qed
        then obtain Rm where Rm: "\<And>m. Rm m \<in> Cs"
          and bR: "\<And>m. b < ?g (ym m) (Rm m)" by metis
        from Cscpt Rm obtain Rl a where Rl: "Rl \<in> Cs" and sm: "strict_mono a"
          and lim: "limitin MC.mtopology (Rm \<circ> a) Rl sequentially"
          unfolding MC.compactin_sequentially by (metis image_subsetI)
        have RlC: "Rl \<in> ?C" using Rl CsC by blast
        have RmC: "(Rm \<circ> a) m \<in> ?C" for m using Rm CsC by auto
        have wc: "weak_conv_on (Rm \<circ> a) Rl sequentially ?X" by (rule convC[OF lim])
        have yca: "(\<lambda>m. ym (a m)) \<longlonglongrightarrow> y"
          using LIMSEQ_subseq_LIMSEQ[OF yc sm] by (simp add: o_def)
        have "Limsup sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m)) \<le> ?g y Rl"
          by (rule ess_inf_pexit_pshift_usc
              [OF T K yca prC[OF RmC] stC[OF RmC] prC[OF RlC] stC[OF RlC] wc])
        moreover have "b \<le> Liminf sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m))"
          using bR by (intro Liminf_bounded always_eventually) (auto simp: less_imp_le)
        moreover have "Liminf sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m))
            \<le> Limsup sequentially (\<lambda>m. ?g (ym (a m)) ((Rm \<circ> a) m))"
          by (rule Liminf_le_Limsup) simp
        ultimately have "b \<le> ?g y Rl" by simp
        also have "\<dots> \<le> Sup (?g y ` Cs)" using Rl by (intro Sup_upper imageI)
        finally show ?thesis .
      qed
      have "c \<le> Sup (?g y ` Cs)"
      proof (rule ccontr)
        assume "\<not> c \<le> Sup (?g y ` Cs)"
        then have "Sup (?g y ` Cs) < c" by simp
        then obtain b where "Sup (?g y ` Cs) < b" and "b < c"
          using ennreal_strict_between by blast
        with below[of b] show False by simp
      qed
      then show "y \<in> {y. c \<le> Sup (?g y ` Cs)}" by blast
    qed
    then show "{y \<in> space (borel :: (real^'n) measure). c \<le> Sup (?g y ` Cs)}
        \<in> sets (borel :: (real^'n) measure)" by simp
  qed
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
    have p: "prob_space N" by (rule exit_class_prob[OF N])
    then have "finite_measure N"
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
    with exit_class_sets[OF N] show "N \<in> topspace ?W" by simp
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
  have shiftmem: "pshift_law T y (s y) \<in> exit_class k L T y" for y
    using exit_class_pshift[OF T0 sC, of y] by simp
  have supeq: "Sup (?g y ` ?C) = exit_val k L T K y" for y
  proof -
    have "exit_class k L T y = pshift_law T y ` ?C"
      by (rule exit_class_shift_image[OF T0])
    then have "(\<lambda>Q. ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
          ` exit_class k L T y = ?g y ` ?C"
      by (simp add: image_image)
    then show ?thesis unfolding exit_val_def by simp
  qed
  have sval: "ess_inf_time (pshift_law T y (s y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))
      = exit_val k L T K y" for y
    using sopt[of y] supeq[of y] by simp
  show ?thesis by (rule that[OF smW sC shiftmem sval])
qed

section \<open>The optimizer as a Giry-monad kernel\<close>

text \<open>Kernel pasting glues with the Giry monad's @{term bind}, which wants
  the continuation as a measurable map into @{term prob_algebra} --- the
  measurable space of probability measures --- not merely into the Borel
  algebra of the weak topology.  The AFP supplies the bridge: on a Polish
  space the two agree once one restricts to probability measures with the
  right \<open>sets\<close> (@{thm [source] weak_conv_topology_eq_prob_algebra}), and
  that is where the selector lands anyway.\<close>












theorem exit_class_kglue_law':
  fixes Q :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L"
    and T0: "0 < T"
    and Q: "Q \<in> exit_class k L r x"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and Kb: "Kr \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
            (exit_class k L (T - r) (0::real^'n))
            (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
              (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and Kc: "\<And>\<omega>. Kr \<omega> \<in> exit_class k L (T - r) 0"
  shows "kglue_law' r T Kr Q \<in> exit_class k L T x"
proof -
  let ?s = "T - r"
  let ?C0 = "exit_class k L ?s (0::real^'n)"
  let ?dd = "Levy_Prokhorov.LPm (mspace (path_metric ?s :: ('n pairpath) metric))
      (mdist (path_metric ?s :: ('n pairpath) metric))"
  let ?MR = "(path_borel ?s :: ('n pairpath) measure)"
  let ?X = "mtopology_of (path_metric r :: ('n pairpath) metric)"
  let ?Y = "mtopology_of (path_metric ?s :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have s0: "0 < ?s" using rT by simp
  have s0': "0 \<le> ?s" using s0 by simp
  have L0: "0 \<le> L" using L1 by simp
  have rT': "r \<le> T" using rT by simp
  have setsQ: "sets Q = sets (borel_of ?X)" by (rule exit_class_sets[OF Q])
  have PQ: "prob_space Q" by (rule exit_class_prob[OF Q])
  interpret MC: Metric_space "exit_class k L ?s (0::real^'n)" ?dd
    by (rule exit_class_compact_metric_space(1)[OF s0 L0])
  have Ctop: "MC.mtopology = subtopology (weak_conv_topology ?Y) ?C0"
    by (rule exit_class_compact_metric_space(2)[OF s0 L0])
  have Ccpt: "compact_space MC.mtopology"
    by (rule exit_class_compact_metric_space(3)[OF s0 L0])
  have Cne: "?C0 \<noteq> {}" by (rule exit_class_nonempty[OF s0' L1])
  \<comment> \<open>round the kernel to a dense sequence of the compact class\<close>
  obtain z :: "nat \<Rightarrow> ('n pairpath) measure"
    and Nm :: "nat \<Rightarrow> 'n pairpath \<Rightarrow> nat"
    where zC: "\<And>j. z j \<in> ?C0"
    and Nmeas: "\<And>m. Nm m \<in> natural_filtration Q 0 (\<lambda>v \<omega>. \<omega> v) r
        \<rightarrow>\<^sub>M count_space UNIV"
    and zclose: "\<And>m \<omega>. ?dd (z (Nm m \<omega>)) (Kr \<omega>) < (1/2)^m"
    by (rule MC.countably_valued_approx[OF Ccpt Cne Kb Kc]) blast
  have NmQ: "Nm m \<in> Q \<rightarrow>\<^sub>M count_space UNIV" for m
  proof -
    interpret MQ0: martingale Q "natural_filtration Q 0 (\<lambda>v \<omega> :: 'n pairpath. \<omega> v)"
      "0::real" "\<lambda>u \<omega>. fst (\<omega> (min u r)) :: real^'n"
      by (rule exit_class_X_martingale[OF Q])
    show ?thesis by (rule measurable_from_subalg[OF MQ0.subalgebras[OF r] Nmeas])
  qed
  \<comment> \<open>each rounded glue is in the class, and is the kernel glue at the rounding\<close>
  have memm: "kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q \<in> exit_class k L T x" for m
  proof -
    have "kglue_law r T (Nm m) Q z \<in> exit_class k L T x"
      by (rule exit_class_kglue_law[OF r rT' L0 Q zC Nmeas])
    moreover have "kglue_law r T (Nm m) Q z = kglue_law' r T (\<lambda>\<omega>. z (Nm m \<omega>)) Q"
    proof (rule kglue_law_eq_kglue_law'[OF r rT' PQ _ setsQ _ NmQ])
      show "prob_space (z j)" for j by (rule exit_class_prob[OF zC])
      show "sets (z j) = sets ?MR" for j by (rule exit_class_sets[OF zC])
      show "(\<lambda>\<omega>. z (Nm m \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR"
      proof (rule measurable_compose_countable[where f = "\<lambda>j (_ :: 'n pairpath). z j"])
        show "(\<lambda>\<omega>. z j) \<in> Q \<rightarrow>\<^sub>M prob_algebra ?MR" for j
          using exit_class_prob[OF zC] exit_class_sets[OF zC]
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
      using exit_class_prob[OF zC] exit_class_sets[OF zC]
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
    unfolding kglue_law'_def pair_law_of_def by simp
  \<comment> \<open>weak closedness finishes\<close>
  have pl: "prob_space (kglue_law' r T Kr Q)"
    by (rule prob_space_kglue_law'[OF r rT' PQ setsQ Kp])
  show ?thesis
    by (rule exit_class_weak_closed[OF T0 L0 memm gconv pl]) simp
qed


(*<*)
end
(*>*)
