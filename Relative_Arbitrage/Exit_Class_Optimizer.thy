section \<open>Attainment, the measurable optimizer, and the semidirect product\<close>

(*<*)
theory Exit_Class_Optimizer
  imports Exit_Class_Pasting
    "Semicontinuous_Analysis.Semicontinuous_Selection"
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

text \<open>The pointwise half of Larsson--Ruf's Proposition 2.2(ii): the class
  is sequentially compact and the essential infimum of the exit time is
  upper semicontinuous along weak convergence, so the supremum defining
  \<open>exit_val\<close> is a maximum --- needed independently of the DPP, since the
  paper's Section 3.1 opens by fixing an optimizer.

  The usc input (\<open>Exit_Semicontinuity.ess_inf_pexit_usc\<close>) lives on the
  vector path space, so the functional is transported along the
  \<open>X\<close>-component map \<open>pfst\<close>, \<open>1\<close>-Lipschitz between the two path metrics, and
  weak convergence pushes forward.\<close>

lemma pfst_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
proof -
  have "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  then have "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))" by (intro continuous_intros)
  then show ?thesis unfolding pfst_def by (rule mspace_path_metricI)
qed

lemma Lipschitz_pfst:
  fixes T :: real
  assumes T: "0 \<le> T"
  shows "Lipschitz_continuous_map (path_metric T :: ('n::finite pairpath) metric)
      (path_metric T :: (real \<Rightarrow> real^'n) metric) (pfst T)"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "pfst T \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<rightarrow> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
    by (intro funcsetI pfst_mspace[OF T])
  have key: "mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
        (pfst T \<omega>) (pfst T \<omega>')
      \<le> 1 * mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
    if w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      and w': "\<omega>' \<in> mspace (path_metric T :: ('n pairpath) metric)" for \<omega> \<omega>'
  proof -
    have rw: "pfst T \<omega> \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
      by (rule pfst_mspace[OF T w])
    have rw': "pfst T \<omega>' \<in> mspace (path_metric T :: (real \<Rightarrow> real^'n) metric)"
      by (rule pfst_mspace[OF T w'])
    have pw: "\<forall>t\<in>{0..T}. dist (\<omega> t) (\<omega>' t)
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      using path_mdist_le_iff_all[OF T w w'] by blast
    have pwr: "dist (pfst T \<omega> t) (pfst T \<omega>' t)
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      if t: "t \<in> {0..T}" for t
    proof -
      have "dist (fst (\<omega> t)) (fst (\<omega>' t)) \<le> dist (\<omega> t) (\<omega>' t)"
        by (rule dist_fst_le)
      then show ?thesis using bspec[OF pw t] t by (simp add: pfst_def)
    qed
    have "mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
          (pfst T \<omega>) (pfst T \<omega>')
        \<le> mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
      using path_mdist_le_iff_all[OF T rw rw'] pwr by blast
    then show ?thesis by simp
  qed
  show "\<exists>B. \<forall>\<omega>\<in>mspace (path_metric T :: ('n pairpath) metric).
      \<forall>\<omega>'\<in>mspace (path_metric T :: ('n pairpath) metric).
        mdist (path_metric T :: (real \<Rightarrow> real^'n) metric)
            (pfst T \<omega>) (pfst T \<omega>')
          \<le> B * mdist (path_metric T :: ('n pairpath) metric) \<omega> \<omega>'"
    by (intro exI[of _ 1] ballI key)
qed

lemma ess_inf_time_pfst:
  fixes Q :: "('n::finite pairpath) measure" and K :: "(real^'n) set"
  assumes T: "0 \<le> T" and K: "closed K"
    and setsQ: "sets Q = sets (path_borel T :: ('n pairpath) measure)"
  shows "ess_inf_time (distr Q (path_borel T :: (real \<Rightarrow> real^'n) measure) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  have "ess_inf_time (distr Q (path_borel T :: (real \<Rightarrow> real^'n) measure) (pfst T)) (pexit T K)
      = ess_inf_time Q (\<lambda>\<omega>. pexit T K (pfst T \<omega>))"
    by (rule ess_inf_time_distr_measurable
        [OF pfst_measurable[OF T setsQ] pexit_measurable[OF T K]])
  then show ?thesis by (simp add: pexit_pfst)
qed

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

lemma mdist_pshift_pshift:
  fixes z y :: "real^'n::finite"
  assumes T: "0 \<le> T" and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "mdist (path_metric T :: ('n pairpath) metric)
      (pshift T z \<omega>) (pshift T y \<omega>) \<le> dist z y"
proof -
  have sz: "pshift T z \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pshift_in_mspace[OF w])
  have sy: "pshift T y \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pshift_in_mspace[OF w])
  have pw: "dist (pshift T z \<omega> t) (pshift T y \<omega> t) \<le> dist z y" if t: "t \<in> {0..T}" for t
  proof -
    have "dist (pshift T z \<omega> t) (pshift T y \<omega> t)
        = dist (z + fst (\<omega> t), snd (\<omega> t)) (y + fst (\<omega> t), snd (\<omega> t))"
      using t by (simp add: pshift_apply)
    also have "\<dots> = dist (z + fst (\<omega> t)) (y + fst (\<omega> t))"
      by (simp add: dist_Pair_Pair)
    also have "\<dots> = dist z y" by (simp add: dist_norm)
    finally show ?thesis by simp
  qed
  show ?thesis using path_mdist_le_iff_all[OF T sz sy] pw by blast
qed

lemma pshift_law_weak_conv_joint:
  fixes ym :: "nat \<Rightarrow> real^'n::finite" and Rm :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes T: "0 \<le> T"
    and yc: "ym \<longlonglongrightarrow> y"
    and prR: "\<And>m. prob_space (Rm m)"
    and setsR: "\<And>m. sets (Rm m) = sets (path_borel T :: ('n pairpath) measure)"
    and prR': "prob_space R"
    and setsR': "sets R = sets (path_borel T :: ('n pairpath) measure)"
    and wc: "weak_conv_on Rm R sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
  shows "weak_conv_on (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "mspace (path_metric T :: ('n pairpath) metric)"
  have prS: "prob_space (pshift_law T z (Rm m))" for z m
    by (rule prob_space_pshift_law[OF T prR setsR])
  have fmS: "finite_measure (pshift_law T z (Rm m))" for z m
    using prS[of z m] by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmS': "finite_measure (pshift_law T y R)"
    using prob_space_pshift_law[OF T prR' setsR']
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have MWfin: "mweak_conv_fin ?S (mdist (path_metric T :: ('n pairpath) metric))
      (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R) sequentially"
    unfolding mweak_conv_fin_def mweak_conv_fin_axioms_def
    using fmS fmS' by (simp add: mtopology_of_def)
  interpret MW: mweak_conv_fin ?S "mdist (path_metric T :: ('n pairpath) metric)"
      "\<lambda>m. pshift_law T (ym m) (Rm m)" "pshift_law T y R" sequentially
    by (rule MWfin)
  show ?thesis
    unfolding mtopology_of_def
  proof (rule MW.mweak_conv_eq1[THEN iffD2], intro allI impI)
    fix f :: "'n pairpath \<Rightarrow> real"
    assume uc: "uniformly_continuous_map MW.Self euclidean_metric f"
    assume bnd: "\<exists>B. \<forall>x \<in> ?S. \<bar>f x\<bar> \<le> B"
    from bnd obtain B where B: "\<And>x. x \<in> ?S \<Longrightarrow> \<bar>f x\<bar> \<le> B" by blast
    have cf: "continuous_map ?X euclideanreal f"
      using uniformly_continuous_imp_continuous_map[OF uc]
      by (simp add: mtopology_of_def)
    have fm: "f \<in> borel_measurable ?B"
      using continuous_map_measurable[OF cf] by (simp add: borel_of_euclidean)
    have shiftm: "pshift T z \<in> Rm m \<rightarrow>\<^sub>M ?B" for z m
      using pshift_measurable[OF T] measurable_cong_sets[OF setsR refl] by blast
    have spRm: "space (Rm m) = ?S" for m by (rule space_of_path_sets[OF setsR])
    have hmeas: "(\<lambda>\<omega>. f (pshift T z \<omega>)) \<in> borel_measurable (Rm m)" for z m
      using fm shiftm by simp
    have hbnd: "\<bar>f (pshift T z \<omega>)\<bar> \<le> B" if "\<omega> \<in> space (Rm m)" for z m \<omega>
    proof -
      have "\<omega> \<in> ?S" using that spRm by simp
      then have "pshift T z \<omega> \<in> ?S" by (rule pshift_in_mspace)
      then show ?thesis by (rule B)
    qed
    have intg: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T z \<omega>))" for z m
    proof -
      interpret PR: prob_space "Rm m" by (rule prR)
      have ae: "AE \<omega> in Rm m. norm (f (pshift T z \<omega>)) \<le> \<bar>B\<bar>"
      proof (intro AE_I2)
        fix \<omega> assume "\<omega> \<in> space (Rm m)"
        then have "\<bar>f (pshift T z \<omega>)\<bar> \<le> B" by (rule hbnd)
        then show "norm (f (pshift T z \<omega>)) \<le> \<bar>B\<bar>" by simp
      qed
      from PR.integrable_const_bound[OF ae hmeas] show ?thesis .
    qed
    have distr_int: "(\<integral>\<omega>. f \<omega> \<partial>(pshift_law T z S)) = (\<integral>\<omega>. f (pshift T z \<omega>) \<partial>S)"
      if "sets S = sets ?B" for z and S :: "('n pairpath) measure"
    proof -
      have m: "pshift T z \<in> S \<rightarrow>\<^sub>M ?B"
        using pshift_measurable[OF T] measurable_cong_sets[OF that refl] by blast
      show ?thesis unfolding pshift_law_def by (rule integral_distr[OF m fm])
    qed
    have lim2: "(\<lambda>m. \<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) \<longlonglongrightarrow> (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)"
    proof -
      have cshift: "continuous_map ?X ?X (pshift T y)"
        by (rule Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pshift[OF T]])
      have cg: "continuous_map ?X euclideanreal (\<lambda>\<omega>. f (pshift T y \<omega>))"
        using continuous_map_compose[OF cshift cf] by (simp add: comp_def)
      have bg: "\<exists>B'. \<forall>x \<in> topspace ?X. \<bar>f (pshift T y x)\<bar> \<le> B'"
      proof (intro exI[of _ B] ballI)
        fix x assume "x \<in> topspace ?X"
        then have "x \<in> ?S" by simp
        then show "\<bar>f (pshift T y x)\<bar> \<le> B" using B pshift_in_mspace by blast
      qed
      show ?thesis using wc[unfolded weak_conv_on_def] cg bg by blast
    qed
    have lim1: "(\<lambda>m. (\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))) \<longlonglongrightarrow> 0"
    proof (rule LIMSEQ_I)
      fix e :: real assume e: "0 < e"
      then have e2: "0 < e/2" by simp
      have ucd: "\<forall>ep>0. \<exists>dl>0. \<forall>u\<in>?S. \<forall>v\<in>?S.
          mdist (path_metric T :: ('n pairpath) metric) v u < dl \<longrightarrow> \<bar>f v - f u\<bar> < ep"
        using uc unfolding uniformly_continuous_map_def by (simp add: dist_real_def)
      from ucd e2 obtain del where d0: "0 < del"
        and dd0: "\<forall>u\<in>?S. \<forall>v\<in>?S.
            mdist (path_metric T :: ('n pairpath) metric) v u < del
              \<longrightarrow> \<bar>f v - f u\<bar> < e/2"
        by blast
      have dd: "\<bar>f v - f u\<bar> < e/2" if "u \<in> ?S" and "v \<in> ?S"
        and "mdist (path_metric T :: ('n pairpath) metric) v u < del" for u v
        using dd0 that by blast
      from LIMSEQ_D[OF yc d0] obtain M0
        where M0: "\<And>m. M0 \<le> m \<Longrightarrow> norm (ym m - y) < del" by blast
      have main: "norm ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
          - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) - 0) < e" if mM: "M0 \<le> m" for m
      proof -
        interpret PRm: prob_space "Rm m" by (rule prR)
        have cint: "(\<integral>\<omega>. (c::real) \<partial>(Rm m)) = c" for c
          by (simp add: PRm.prob_space)
        have i1: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T (ym m) \<omega>))" by (rule intg)
        have i2: "integrable (Rm m) (\<lambda>\<omega>. f (pshift T y \<omega>))" by (rule intg)
        have idiff: "integrable (Rm m)
            (\<lambda>\<omega>. f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>))"
          using i1 i2 by (rule Bochner_Integration.integrable_diff)
        have icu: "integrable (Rm m) (\<lambda>\<omega>. e/2 :: real)" by (rule PRm.integrable_const)
        have icl: "integrable (Rm m) (\<lambda>\<omega>. - (e/2) :: real)"
          by (rule PRm.integrable_const)
        have key: "\<bar>f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)\<bar> \<le> e/2"
          if w: "\<omega> \<in> space (Rm m)" for \<omega>
        proof -
          have wm: "\<omega> \<in> ?S" using w spRm by simp
          have m1: "pshift T (ym m) \<omega> \<in> ?S" by (rule pshift_in_mspace[OF wm])
          have m2: "pshift T y \<omega> \<in> ?S" by (rule pshift_in_mspace[OF wm])
          have "mdist (path_metric T :: ('n pairpath) metric)
              (pshift T (ym m) \<omega>) (pshift T y \<omega>) \<le> dist (ym m) y"
            by (rule mdist_pshift_pshift[OF T wm])
          also have "\<dots> < del" using M0[OF mM] by (simp add: dist_norm)
          finally have "mdist (path_metric T :: ('n pairpath) metric)
              (pshift T (ym m) \<omega>) (pshift T y \<omega>) < del" .
          from dd[OF m2 m1 this] show ?thesis by simp
        qed
        have ptu: "f (pshift T (ym m) x) - f (pshift T y x) \<le> e/2"
          if "x \<in> space (Rm m)" for x using key[OF that] by linarith
        have ptl: "- (e/2) \<le> f (pshift T (ym m) x) - f (pshift T y x)"
          if "x \<in> space (Rm m)" for x using key[OF that] by linarith
        have eq: "(\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
            - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))
            = (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
          by (rule Bochner_Integration.integral_diff[OF i1 i2, symmetric])
        have up: "(\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m)) \<le> e/2"
        proof -
          have "(\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))
              \<le> (\<integral>\<omega>. e/2 \<partial>(Rm m))"
            by (rule integral_mono[OF idiff icu ptu])
          also have "\<dots> = e/2" by (rule cint)
          finally show ?thesis .
        qed
        have lo: "- (e/2) \<le> (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
        proof -
          have "- (e/2) = (\<integral>\<omega>. - (e/2) \<partial>(Rm m))" by (rule cint[symmetric])
          also have "\<dots> \<le> (\<integral>\<omega>. (f (pshift T (ym m) \<omega>) - f (pshift T y \<omega>)) \<partial>(Rm m))"
            by (rule integral_mono[OF icl idiff ptl])
          finally show ?thesis .
        qed
        from up lo have "\<bar>(\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
            - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m))\<bar> \<le> e/2"
          unfolding eq by simp
        then show ?thesis using e by simp
      qed
      then show "\<exists>no. \<forall>m\<ge>no. norm ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
          - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)) - 0) < e" by blast
    qed
    have "(\<lambda>m. ((\<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        - (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)))
        + (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>(Rm m)))
        \<longlonglongrightarrow> 0 + (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)"
      by (rule tendsto_add[OF lim1 lim2])
    then have "(\<lambda>m. \<integral>\<omega>. f (pshift T (ym m) \<omega>) \<partial>(Rm m))
        \<longlonglongrightarrow> (\<integral>\<omega>. f (pshift T y \<omega>) \<partial>R)" by simp
    then show "(\<lambda>m. \<integral>\<omega>. f \<omega> \<partial>(pshift_law T (ym m) (Rm m)))
        \<longlonglongrightarrow> (\<integral>\<omega>. f \<omega> \<partial>(pshift_law T y R))"
      by (simp add: distr_int[OF setsR] distr_int[OF setsR'])
  qed
qed

text \<open>Joint upper semicontinuity of the payoff, in sequential form.  The
  parameter and the law move together; joint continuity of the shift
  carries the pair to a weakly convergent sequence of laws, and
  @{thm [source] ess_inf_pexit_usc} --- which lives on the vector path
  space --- is reached through @{thm [source] Lipschitz_pfst} exactly as
  in @{thm [source] exit_val_attained}.\<close>

lemma ess_inf_pexit_pshift_usc:
  fixes ym :: "nat \<Rightarrow> real^'n::finite" and Rm :: "nat \<Rightarrow> ('n pairpath) measure"
    and K :: "(real^'n) set"
  assumes T: "0 < T" and K: "closed K"
    and yc: "ym \<longlonglongrightarrow> y"
    and prR: "\<And>m. prob_space (Rm m)"
    and setsR: "\<And>m. sets (Rm m) = sets (path_borel T :: ('n pairpath) measure)"
    and prR': "prob_space R"
    and setsR': "sets R = sets (path_borel T :: ('n pairpath) measure)"
    and wc: "weak_conv_on Rm R sequentially
        (mtopology_of (path_metric T :: ('n pairpath) metric))"
  shows "Limsup sequentially (\<lambda>m. ess_inf_time (pshift_law T (ym m) (Rm m))
        (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))))
      \<le> ess_inf_time (pshift_law T y R) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
proof -
  let ?Y = "mtopology_of (path_metric T :: (real \<Rightarrow> real^'n) metric)"
  let ?p = "\<lambda>Q :: ('n pairpath) measure. distr Q (borel_of ?Y) (pfst T)"
  have T0: "0 \<le> T" using T by simp
  have wcs: "weak_conv_on (\<lambda>m. pshift_law T (ym m) (Rm m)) (pshift_law T y R)
      sequentially (mtopology_of (path_metric T :: ('n pairpath) metric))"
    by (rule pshift_law_weak_conv_joint[OF T0 yc prR setsR prR' setsR' wc])
  have prS: "prob_space (pshift_law T (ym m) (Rm m))" for m
    by (rule prob_space_pshift_law[OF T0 prR setsR])
  have prS': "prob_space (pshift_law T y R)"
    by (rule prob_space_pshift_law[OF T0 prR' setsR'])
  have wcY: "weak_conv_on (\<lambda>m. ?p (pshift_law T (ym m) (Rm m)))
      (?p (pshift_law T y R)) sequentially ?Y"
    by (rule weak_conv_on_pushforward
        [OF Lipschitz_continuous_imp_continuous_map[OF Lipschitz_pfst[OF T0]] wcs])
  have lim: "Limsup sequentially
        (\<lambda>m. ess_inf_time (?p (pshift_law T (ym m) (Rm m))) (pexit T K))
      \<le> ess_inf_time (?p (pshift_law T y R)) (pexit T K)"
  proof (rule ess_inf_pexit_usc[OF T K wcY])
    show "prob_space (?p (pshift_law T (ym m) (Rm m)))" for m
      by (rule prob_space.prob_space_distr[OF prS pfst_measurable[OF T0]]) simp
    show "prob_space (?p (pshift_law T y R))"
      by (rule prob_space.prob_space_distr[OF prS' pfst_measurable[OF T0]]) simp
  qed
  have eqS: "ess_inf_time (?p S) (pexit T K)
      = ess_inf_time S (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    if "sets S = sets (path_borel T :: ('n pairpath) measure)"
    for S :: "('n pairpath) measure"
    by (rule ess_inf_time_pfst[OF T0 K that])
  show ?thesis using lim by (simp add: eqS)
qed

text \<open>The class packaged exactly as @{thm [source]
  Metric_space.usc_measurable_selection} consumes it: a compact metric
  space, the metric being L\'evy--Prokhorov restricted to the class, and
  its topology the subspace topology of weak convergence.\<close>

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

lemma Polish_space_path_metric:
  "Polish_space (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))"
  unfolding mtopology_of_def
  by (rule Metric_space.Polish_space_mtopology
      [OF Metric_space_mspace_mdist path_metric_polish(1) path_metric_polish(2)])

section \<open>Kernel pasting: the semidirect product\<close>

text \<open>@{thm [source] exit_class_kglue_law} glues with a countably
  valued index, which @{thm [source] Metric_space.usc_measurable_selection}
  cannot supply.  The replacement is the Giry monad's semidirect product:
  run \<open>Q\<close>, then continue with the law the kernel picks at the endpoint
  reached.  \<open>ksemi\<close> and its API live in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

subsection \<open>The glued law, and the two almost-sure clauses of (1.7)\<close>

definition kglue_law' :: "real \<Rightarrow> real \<Rightarrow> ('n::finite pairpath \<Rightarrow> ('n pairpath) measure)
    \<Rightarrow> ('n pairpath) measure \<Rightarrow> ('n pairpath) measure"
  where "kglue_law' r T Kr Q
     = pair_law_of T (\<lambda>p. pglue r T (fst p) (snd p))
         (ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr)"

lemma sets_kglue_law'[simp]:
  "sets (kglue_law' r T Kr Q)
     = sets (path_borel T :: ('n::finite pairpath) measure)"
  unfolding kglue_law'_def by (rule sets_pair_law_of)

lemma kglue_law'_measurable:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and ne: "space Q \<noteq> {}"
  shows "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr
        \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  have "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> Q \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    by (rule pglue_measurable[OF r rT setsQ refl])
  then show ?thesis
    using measurable_cong_sets[OF sets_ksemi[OF K ne] refl] by blast
qed

lemma prob_space_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "prob_space (kglue_law' r T Kr Q)"
proof -
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  interpret PK: prob_space "ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr"
    by (rule prob_space_ksemi[OF PQ K])
  show ?thesis
    unfolding kglue_law'_def pair_law_of_def
    by (rule PK.prob_space_distr[OF kglue_law'_measurable[OF r rT setsQ K ne]])
qed

text \<open>The almost-sure transfer.  Note that the second-coordinate property
  \<open>B\<close> may depend on the first coordinate --- it has to, since the kernel
  does.  That is the only difference from
  @{thm [source] AE_kglue_law}; the proof is the same, with
  @{thm [source] AE_ksemi} in place of the product space's
  \<open>AE_pair_measure\<close>.\<close>

lemma AE_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T" and PQ: "prob_space Q"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and K: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and mset: "{\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric). P \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and A: "AE \<omega> in Q. A \<omega>"
    and B: "\<And>\<omega>. \<omega> \<in> space Q \<Longrightarrow> AE \<omega>' in Kr \<omega>. B \<omega> \<omega>'"
    and imp: "\<And>\<omega> \<omega>'. \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<Longrightarrow>
        \<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric) \<Longrightarrow>
        A \<omega> \<Longrightarrow> B \<omega> \<omega>' \<Longrightarrow> P (pglue r T \<omega> \<omega>')"
  shows "AE \<omega> in kglue_law' r T Kr Q. P \<omega>"
proof -
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?S = "ksemi Q ?MR Kr"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  interpret PQ: prob_space Q by (rule PQ)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have phim: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ?S \<rightarrow>\<^sub>M ?B"
    by (rule kglue_law'_measurable[OF r rT setsQ K ne])
  have mset': "{\<omega> \<in> space ?B. P \<omega>} \<in> sets ?B"
    using mset by (simp add: space_borel_of)
  have iff: "(AE \<omega> in kglue_law' r T Kr Q. P \<omega>)
      = (AE p in ?S. P (pglue r T (fst p) (snd p)))"
    unfolding kglue_law'_def pair_law_of_def by (rule AE_distr_iff[OF phim mset'])
  have evm: "{p \<in> space ?S. P (pglue r T (fst p) (snd p))} \<in> sets ?S"
  proof -
    have "{p \<in> space ?S. P (pglue r T (fst p) (snd p))}
        = (\<lambda>p. pglue r T (fst p) (snd p)) -` {\<omega> \<in> space ?B. P \<omega>} \<inter> space ?S"
      using measurable_space[OF phim] by auto
    then show ?thesis using measurable_sets[OF phim mset'] by simp
  qed
  have evm': "{p \<in> space (Q \<Otimes>\<^sub>M ?MR). P (pglue r T (fst p) (snd p))}
      \<in> sets (Q \<Otimes>\<^sub>M ?MR)"
    using evm sets_ksemi[OF K ne] space_ksemi[OF K ne] by simp
  have inner: "AE \<omega> in Q. AE \<omega>' in Kr \<omega>. P (pglue r T \<omega> \<omega>')"
  proof -
    have QA: "AE \<omega> in Q. A \<omega>
        \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric) \<and> \<omega> \<in> space Q"
      using A AE_space[of Q] space_of_path_sets[OF setsQ]
      by (auto intro: eventually_conj)
    show ?thesis
    proof (rule eventually_mono[OF QA])
      fix \<omega> :: "'n pairpath"
      assume w: "A \<omega> \<and> \<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)
          \<and> \<omega> \<in> space Q"
      then have wQ: "\<omega> \<in> space Q" by blast
      have sk: "sets (Kr \<omega>) = sets ?MR" by (rule ksemi_sets_kernel(1)[OF K wQ])
      have KB: "AE \<omega>' in Kr \<omega>. B \<omega> \<omega>' \<and> \<omega>' \<in> space (Kr \<omega>)"
        using B[OF wQ] AE_space[of "Kr \<omega>"] by (auto intro: eventually_conj)
      show "AE \<omega>' in Kr \<omega>. P (pglue r T \<omega> \<omega>')"
      proof (rule eventually_mono[OF KB])
        fix \<omega>' :: "'n pairpath"
        assume "B \<omega> \<omega>' \<and> \<omega>' \<in> space (Kr \<omega>)"
        then have "\<omega>' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
          and "B \<omega> \<omega>'"
          using sk by (auto simp: space_of_path_sets sets_eq_imp_space_eq
              space_borel_of)
        with w show "P (pglue r T \<omega> \<omega>')" by (simp add: imp)
      qed
    qed
  qed
  have "AE p in ?S. P (pglue r T (fst p) (snd p))"
    using AE_ksemi[OF K evm'] inner by simp
  then show ?thesis unfolding iff .
qed

text \<open>Clause (i) of (1.7) for the kernel glue.\<close>

text \<open>Clause (ii): the covariation difference quotient.  The kernel's
  values have to lie in the class at the origin --- this is the first
  place where that is used, and it is where the almost-sure statement of
  the continuation enters, one \<open>\<omega>\<close> at a time.\<close>

subsection \<open>The glue is continuous, and the product is a Polish product\<close>

text \<open>Proving clauses (iii) and (iv) directly for @{const ksemi} runs into
  two obstructions: the distribution's \<open>integral_bind\<close> covers only
  bounded real integrands, and the first-factor martingale property is
  false for a semidirect product (the weight \<open>(Kr \<omega>)(A\<^sub>\<omega>)\<close> in the
  disintegrated set integral is only \<open>\<F>\<^sub>r\<close>-measurable).

  Neither has to be faced.  The class is weakly closed
  (@{thm [source] exit_class_weak_closed}), the glue with a countably
  valued index is already in it
  (@{thm [source] exit_class_kglue_law}), and the class at the origin
  is a compact metric space
  (@{thm [source] exit_class_compact_metric_space}), hence separable,
  so any kernel into it is a pointwise limit of countably valued ones.  If
  the semidirect products converge weakly, the glued laws do too, and weak
  closedness finishes --- which needs continuity of the glue and the
  identity of the two \<open>\<sigma>\<close>-algebras on the product.\<close>

lemma second_countable_path_metric:
  "second_countable (mtopology_of (path_metric T :: (real \<Rightarrow> 'b::polish_space) metric))"
  unfolding mtopology_of_def
  by (rule Metric_space.separable_space_imp_second_countable
      [OF Metric_space_mspace_mdist path_metric_polish(2)])

lemma mdist_pglue_le:
  fixes w wt w' wt' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "w \<in> mspace (path_metric r :: ('n pairpath) metric)"
    and wt: "wt \<in> mspace (path_metric r :: ('n pairpath) metric)"
    and w': "w' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
    and wt': "wt' \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
  shows "mdist (path_metric T :: ('n pairpath) metric)
        (pglue r T w w') (pglue r T wt wt')
      \<le> mdist (path_metric r :: ('n pairpath) metric) w wt
        + 2 * mdist (path_metric (T - r) :: ('n pairpath) metric) w' wt'"
proof -
  let ?d1 = "mdist (path_metric r :: ('n pairpath) metric) w wt"
  let ?d2 = "mdist (path_metric (T - r) :: ('n pairpath) metric) w' wt'"
  have T0: "0 \<le> T" using r rT by simp
  have Tr0: "0 \<le> T - r" using rT by simp
  have g1: "pglue r T w w' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pglue_in_mspace[OF r rT w w'])
  have g2: "pglue r T wt wt' \<in> mspace (path_metric T :: ('n pairpath) metric)"
    by (rule pglue_in_mspace[OF r rT wt wt'])
  have pw1: "dist (w t) (wt t) \<le> ?d1" if "t \<in> {0..r}" for t
    using path_mdist_le_iff_all[OF r w wt] that by blast
  have pw2: "dist (w' t) (wt' t) \<le> ?d2" if "t \<in> {0..T - r}" for t
    using path_mdist_le_iff_all[OF Tr0 w' wt'] that by blast
  have pw: "dist (pglue r T w w' t) (pglue r T wt wt' t) \<le> ?d1 + 2 * ?d2"
    if t: "t \<in> {0..T}" for t
  proof (cases "t \<le> r")
    case True
    then have tr: "t \<in> {0..r}" using t by simp
    have "dist (pglue r T w w' t) (pglue r T wt wt' t) = dist (w t) (wt t)"
      using t True by (simp add: pglue_le)
    also have "\<dots> \<le> ?d1" by (rule pw1[OF tr])
    also have "\<dots> \<le> ?d1 + 2 * ?d2" by simp
    finally show ?thesis .
  next
    case False
    then have tr: "r \<le> t" by simp
    have t1: "t - r \<in> {0..T - r}" using t tr by simp
    have t2: "(0::real) \<in> {0..T - r}" using Tr0 by simp
    have alg: "(w r + (w' (t - r) - w' 0)) - (wt r + (wt' (t - r) - wt' 0))
        = (w r - wt r) + ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0))"
      by (simp add: algebra_simps)
    have "dist (pglue r T w w' t) (pglue r T wt wt' t)
        = norm ((w r - wt r) + ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0)))"
      using t tr by (simp add: pglue_ge dist_norm alg)
    also have "\<dots> \<le> norm (w r - wt r)
        + norm ((w' (t - r) - wt' (t - r)) - (w' 0 - wt' 0))"
      by (rule norm_triangle_ineq)
    also have "\<dots> \<le> norm (w r - wt r)
        + (norm (w' (t - r) - wt' (t - r)) + norm (w' 0 - wt' 0))"
      by (simp add: norm_triangle_ineq4)
    also have "\<dots> \<le> ?d1 + (?d2 + ?d2)"
      using pw1[of r] pw2[OF t1] pw2[OF t2] r by (simp add: dist_norm)
    finally show ?thesis by simp
  qed
  show ?thesis using path_mdist_le_iff_all[OF T0 g1 g2] pw by blast
qed

lemma Lipschitz_pglue:
  fixes r T :: real
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "Lipschitz_continuous_map
      (prod_metric (path_metric r :: ('n::finite pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric))
      (path_metric T :: ('n pairpath) metric)
      (\<lambda>p. pglue r T (fst p) (snd p))"
  unfolding Lipschitz_continuous_map_def
proof (intro conjI)
  show "(\<lambda>p. pglue r T (fst p) (snd p))
      \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
          (path_metric (T - r) :: ('n pairpath) metric))
        \<rightarrow> mspace (path_metric T :: ('n pairpath) metric)"
    using pglue_in_mspace[OF r rT] by (intro funcsetI) auto
  show "\<exists>B. \<forall>p \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
          (path_metric (T - r) :: ('n pairpath) metric)).
      \<forall>q \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
          (path_metric (T - r) :: ('n pairpath) metric)).
        mdist (path_metric T :: ('n pairpath) metric)
            ((\<lambda>p. pglue r T (fst p) (snd p)) p) ((\<lambda>p. pglue r T (fst p) (snd p)) q)
          \<le> B * mdist (prod_metric (path_metric r :: ('n pairpath) metric)
              (path_metric (T - r) :: ('n pairpath) metric)) p q"
  proof (intro exI[of _ 3] ballI)
    fix p q :: "'n pairpath \<times> 'n pairpath"
    assume p: "p \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric))"
      and q: "q \<in> mspace (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric))"
    from p have p1: "fst p \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and p2: "snd p \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by auto
    from q have q1: "fst q \<in> mspace (path_metric r :: ('n pairpath) metric)"
      and q2: "snd q \<in> mspace (path_metric (T - r) :: ('n pairpath) metric)"
      by auto
    let ?a = "mdist (path_metric r :: ('n pairpath) metric) (fst p) (fst q)"
    let ?b = "mdist (path_metric (T - r) :: ('n pairpath) metric) (snd p) (snd q)"
    let ?pd = "mdist (prod_metric (path_metric r :: ('n pairpath) metric)
        (path_metric (T - r) :: ('n pairpath) metric)) p q"
    have pdeq: "?pd = sqrt (?a\<^sup>2 + ?b\<^sup>2)"
      by (simp add: prod_dist_def case_prod_unfold)
    have c1: "?a \<le> ?pd"
    proof -
      have "?a = sqrt (?a\<^sup>2)" by simp
      also have "\<dots> \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2)" by (simp add: real_sqrt_le_mono)
      finally show ?thesis using pdeq by simp
    qed
    have c2: "?b \<le> ?pd"
    proof -
      have "?b = sqrt (?b\<^sup>2)" by simp
      also have "\<dots> \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2)" by (simp add: real_sqrt_le_mono)
      finally show ?thesis using pdeq by simp
    qed
    have "mdist (path_metric T :: ('n pairpath) metric)
        (pglue r T (fst p) (snd p)) (pglue r T (fst q) (snd q)) \<le> ?a + 2 * ?b"
      by (rule mdist_pglue_le[OF r rT p1 q1 p2 q2])
    also have "\<dots> \<le> 3 * ?pd" using c1 c2 by simp
    finally show "mdist (path_metric T :: ('n pairpath) metric)
        ((\<lambda>p. pglue r T (fst p) (snd p)) p) ((\<lambda>p. pglue r T (fst p) (snd p)) q)
        \<le> 3 * ?pd" by simp
  qed
qed

subsection \<open>Weak convergence of the semidirect products\<close>

text \<open>\<open>integral_ksemi_bounded\<close> (all the weak-convergence route needs, since
  test functions for weak convergence are bounded and real by definition)
  and \<open>integral_ksemi_measurable\<close> live in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

text \<open>Pointwise weak convergence of the kernels gives weak convergence of
  the semidirect products.  The proof is dominated convergence over the
  first coordinate: a bounded continuous test function on the product is,
  at each fixed first coordinate, a bounded continuous test function on
  the second, so the inner integrals converge pointwise, and they are all
  bounded by the same constant.\<close>

lemma ksemi_weak_conv:
  fixes Krm :: "nat \<Rightarrow> 'a \<Rightarrow> 'b measure" and X :: "'a topology" and Y :: "'b topology"
  assumes PM: "prob_space M"
    and setsM: "sets M = sets (borel_of X)"
    and scX: "second_countable X" and scY: "second_countable Y"
    and Km: "\<And>m. Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of Y)"
    and K: "Kr \<in> M \<rightarrow>\<^sub>M prob_algebra (borel_of Y)"
    and conv: "\<And>\<omega>. \<omega> \<in> space M
        \<Longrightarrow> weak_conv_on (\<lambda>m. Krm m \<omega>) (Kr \<omega>) sequentially Y"
  shows "weak_conv_on (\<lambda>m. ksemi M (borel_of Y) (Krm m))
      (ksemi M (borel_of Y) Kr) sequentially (prod_topology X Y)"
proof -
  let ?N = "borel_of Y"
  let ?Z = "prod_topology X Y"
  interpret PM: prob_space M by (rule PM)
  have ne: "space M \<noteq> {}" by (rule PM.not_empty)
  have spX: "space M = topspace X"
    using setsM by (simp add: sets_eq_imp_space_eq space_borel_of)
  have bprod: "sets (M \<Otimes>\<^sub>M ?N) = sets (borel_of ?Z)"
  proof -
    have "sets (M \<Otimes>\<^sub>M ?N) = sets (borel_of X \<Otimes>\<^sub>M borel_of Y)"
      by (rule sets_pair_measure_cong[OF setsM refl])
    also have "\<dots> = sets (borel_of ?Z)"
      by (rule arg_cong[where f = sets, OF borel_of_prod[OF scX scY]])
    finally show ?thesis .
  qed
  have setsK: "sets (ksemi M ?N Kr) = sets (borel_of ?Z)"
    using sets_ksemi[OF K ne] bprod by simp
  have setsKm: "sets (ksemi M ?N (Krm m)) = sets (borel_of ?Z)" for m
  proof -
    have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
    show ?thesis using sets_ksemi[OF Kmm ne] bprod by simp
  qed
  have fmK: "finite_measure (ksemi M ?N Kr)"
    using prob_space_ksemi[OF PM K]
    by (simp add: prob_space.emeasure_space_1 finite_measureI)
  have fmKm: "finite_measure (ksemi M ?N (Krm m))" for m
  proof -
    have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
    show ?thesis using prob_space_ksemi[OF PM Kmm]
      by (simp add: prob_space.emeasure_space_1 finite_measureI)
  qed
  show ?thesis
    unfolding weak_conv_on_def
  proof (intro conjI allI impI)
    show "\<forall>\<^sub>F m in sequentially. sets (ksemi M ?N (Krm m)) = sets (borel_of ?Z)
        \<and> finite_measure (ksemi M ?N (Krm m))"
      by (intro always_eventually allI conjI setsKm fmKm)
    show "sets (ksemi M ?N Kr) = sets (borel_of ?Z)" by (rule setsK)
    show "finite_measure (ksemi M ?N Kr)" by (rule fmK)
    fix f :: "'a \<times> 'b \<Rightarrow> real"
    assume cf: "continuous_map ?Z euclideanreal f"
    assume bf: "\<exists>B. \<forall>p \<in> topspace ?Z. \<bar>f p\<bar> \<le> B"
    from bf obtain B where B: "\<And>p. p \<in> topspace ?Z \<Longrightarrow> \<bar>f p\<bar> \<le> B" by blast
    have fm: "f \<in> borel_measurable (M \<Otimes>\<^sub>M ?N)"
    proof -
      have "f \<in> borel_of ?Z \<rightarrow>\<^sub>M borel_of euclideanreal"
        by (rule continuous_map_measurable[OF cf])
      then have "f \<in> borel_measurable (borel_of ?Z)"
        by (simp add: borel_of_euclidean)
      then show ?thesis unfolding measurable_cong_sets[OF bprod refl] .
    qed
    have spZ: "space (M \<Otimes>\<^sub>M ?N) = topspace ?Z"
    proof -
      have "space (M \<Otimes>\<^sub>M ?N) = space (borel_of ?Z)"
        by (rule sets_eq_imp_space_eq[OF bprod])
      then show ?thesis by (simp add: space_borel_of)
    qed
    have fb: "\<bar>f p\<bar> \<le> B" if "p \<in> space (M \<Otimes>\<^sub>M ?N)" for p
      using that spZ by (simp add: B)
    \<comment> \<open>the two disintegrations\<close>
    have dK: "(\<integral>p. f p \<partial>(ksemi M ?N Kr)) = (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
      by (rule integral_ksemi_bounded[OF PM K fm fb])
    have dKm: "(\<integral>p. f p \<partial>(ksemi M ?N (Krm m)))
        = (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<partial>M)" for m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      show ?thesis by (rule integral_ksemi_bounded[OF PM Kmm fm fb])
    qed
    \<comment> \<open>the inner integrals converge pointwise and are uniformly bounded\<close>
    have inner_lim: "(\<lambda>m. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<longlonglongrightarrow> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
      if w: "\<omega> \<in> space M" for \<omega>
    proof -
      have wX: "\<omega> \<in> topspace X" using w spX by simp
      have cpair: "continuous_map Y ?Z (Pair \<omega>)"
        unfolding continuous_map_pairwise using wX by (simp add: o_def)
      have cg: "continuous_map Y euclideanreal (\<lambda>\<omega>'. f (\<omega>, \<omega>'))"
        using continuous_map_compose[OF cpair cf] by (simp add: comp_def)
      have bg: "\<exists>B'. \<forall>y \<in> topspace Y. \<bar>f (\<omega>, y)\<bar> \<le> B'"
        using B wX by (intro exI[of _ B]) auto
      show ?thesis using conv[OF w, unfolded weak_conv_on_def] cg bg by blast
    qed
    have inner_meas: "(\<lambda>\<omega>. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<in> borel_measurable M" for m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      show ?thesis by (rule integral_ksemi_measurable[OF Kmm fm])
    qed
    have inner_meas': "(\<lambda>\<omega>. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<in> borel_measurable M"
      by (rule integral_ksemi_measurable[OF K fm])
    have inner_bnd: "\<bar>\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)\<bar> \<le> \<bar>B\<bar>" if w: "\<omega> \<in> space M" for \<omega> m
    proof -
      have Kmm: "Krm m \<in> M \<rightarrow>\<^sub>M prob_algebra ?N" by (rule Km)
      interpret PK: prob_space "Krm m \<omega>" by (rule ksemi_sets_kernel(2)[OF Kmm w])
      have sk: "sets (Krm m \<omega>) = sets ?N" by (rule ksemi_sets_kernel(1)[OF Kmm w])
      have gm: "(\<lambda>\<omega>'. f (\<omega>, \<omega>')) \<in> borel_measurable (Krm m \<omega>)"
      proof -
        have "Pair \<omega> \<in> Krm m \<omega> \<rightarrow>\<^sub>M M \<Otimes>\<^sub>M ?N"
          by (rule ksemi_Pair_measurable[OF Kmm w])
        from measurable_compose[OF this fm] show ?thesis by simp
      qed
      have spk: "space (Krm m \<omega>) = space ?N" by (rule sets_eq_imp_space_eq[OF sk])
      have gb: "\<bar>f (\<omega>, \<omega>')\<bar> \<le> \<bar>B\<bar>" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
      proof -
        have "\<omega>' \<in> space ?N" using that spk by simp
        then have "(\<omega>, \<omega>') \<in> space (M \<Otimes>\<^sub>M ?N)"
          using w by (simp add: space_pair_measure)
        then show ?thesis using fb[of "(\<omega>, \<omega>')"] by simp
      qed
      have gbu: "f (\<omega>, \<omega>') \<le> \<bar>B\<bar>" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
        using gb[OF that] by (simp add: abs_le_iff)
      have gbl: "- \<bar>B\<bar> \<le> f (\<omega>, \<omega>')" if "\<omega>' \<in> space (Krm m \<omega>)" for \<omega>'
        using gb[OF that] by (simp add: abs_le_iff)
      have cint: "(\<integral>\<omega>'. (c::real) \<partial>(Krm m \<omega>)) = c" for c
        by (simp add: PK.prob_space)
      have ig: "integrable (Krm m \<omega>) (\<lambda>\<omega>'. f (\<omega>, \<omega>'))"
        by (rule PK.integrable_const_bound[of _ "\<bar>B\<bar>"])
          (use gb gm in \<open>auto\<close>)
      have ic: "integrable (Krm m \<omega>) (\<lambda>\<omega>'. \<bar>B\<bar>)" by (rule PK.integrable_const)
      have ic': "integrable (Krm m \<omega>) (\<lambda>\<omega>'. - \<bar>B\<bar>)" by (rule PK.integrable_const)
      have up: "(\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> \<bar>B\<bar>"
      proof -
        have "(\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> (\<integral>\<omega>'. \<bar>B\<bar> \<partial>(Krm m \<omega>))"
          by (rule integral_mono[OF ig ic gbu])
        also have "\<dots> = \<bar>B\<bar>" by (rule cint)
        finally show ?thesis .
      qed
      have lo: "- \<bar>B\<bar> \<le> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))"
      proof -
        have "- \<bar>B\<bar> = (\<integral>\<omega>'. - \<bar>B\<bar> \<partial>(Krm m \<omega>))" by (rule cint[symmetric])
        also have "\<dots> \<le> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))"
          by (rule integral_mono[OF ic' ig gbl])
        finally show ?thesis .
      qed
      from up lo show ?thesis by simp
    qed
    have "(\<lambda>m. \<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<partial>M)
        \<longlonglongrightarrow> (\<integral>\<omega>. (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>)) \<partial>M)"
    proof (rule integral_dominated_convergence
        [where w = "\<lambda>_. \<bar>B\<bar>", OF inner_meas' inner_meas])
      show "integrable M (\<lambda>_. \<bar>B\<bar>)" by simp
      show "AE \<omega> in M. (\<lambda>m. \<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>))
          \<longlonglongrightarrow> (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Kr \<omega>))"
        using inner_lim by (intro AE_I2) blast
      show "AE \<omega> in M. norm (\<integral>\<omega>'. f (\<omega>, \<omega>') \<partial>(Krm m \<omega>)) \<le> \<bar>B\<bar>" for m
        using inner_bnd by (intro AE_I2) simp
    qed
    then show "(\<lambda>m. \<integral>p. f p \<partial>(ksemi M ?N (Krm m)))
        \<longlonglongrightarrow> (\<integral>p. f p \<partial>(ksemi M ?N Kr))"
      by (simp add: dK dKm)
  qed
qed

subsection \<open>Countably valued approximation of a kernel\<close>

text \<open>\<open>countably_valued_approx\<close>, \<open>limitin_of_dist_half\<close> live in @{theory Semicontinuous_Analysis.Semicontinuous_Selection}.\<close>


subsection \<open>The two constructions agree at a countably valued kernel\<close>

text \<open>With a countably valued index the
  product-of-all-candidates construction and the Giry semidirect product
  give the same law, because the second coordinate of the product,
  evaluated at a first-coordinate-measurable index, has exactly the
  kernel's law.  Both sides reduce to
  \<open>\<integral>\<^sup>+\<omega>. (RR (N \<omega>)) {\<omega>'. pglue r T \<omega> \<omega>' \<in> A} \<partial>Q\<close>: on the left by Fubini and
  @{thm [source] distr_PiM_component}, on the right by @{thm [source]
  emeasure_bind} and @{thm [source] emeasure_distr}.\<close>

lemma kglue_law_eq_kglue_law':
  fixes Q :: "('n::finite pairpath) measure"
    and RR :: "nat \<Rightarrow> ('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and PQ: "prob_space Q" and PR: "\<And>j. prob_space (RR j)"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and setsR: "\<And>j. sets (RR j) = sets ((path_borel (T - r) :: ('n pairpath) measure))"
    and Nm: "N \<in> Q \<rightarrow>\<^sub>M count_space UNIV"
    and K: "(\<lambda>\<omega>. RR (N \<omega>)) \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
  shows "kglue_law r T N Q RR = kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q"
proof (rule measure_eqI)
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?S = "Pi\<^sub>M UNIV RR"
  let ?P = "Q \<Otimes>\<^sub>M ?S"
  interpret PQ: prob_space Q by (rule PQ)
  interpret PS: prob_space ?S by (rule prob_space_PiM) (rule PR)
  have ne: "space Q \<noteq> {}" by (rule PQ.not_empty)
  have gm: "kglue r T N \<in> ?P \<rightarrow>\<^sub>M ?B"
    by (rule kglue_measurable[OF r rT setsQ setsR Nm])
  have pm: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)) \<rightarrow>\<^sub>M ?B"
    by (rule kglue_law'_measurable[OF r rT setsQ K ne])
  show "sets (kglue_law r T N Q RR) = sets (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q)"
    by simp
  fix A :: "('n pairpath) set"
  assume A: "A \<in> sets (kglue_law r T N Q RR)"
  then have AB: "A \<in> sets ?B" by simp
  \<comment> \<open>the section of the pulled-back set, one \<open>\<omega>\<close> at a time\<close>
  have sec: "emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
      = emeasure ?S (Pair \<omega> -` (kglue r T N -` A \<inter> space ?P))"
    if w: "\<omega> \<in> space Q" for \<omega>
  proof -
    have Pj: "prob_space (RR i)" if "i \<in> (UNIV :: nat set)" for i by (rule PR)
    have mj: "(\<lambda>f :: nat \<Rightarrow> 'n pairpath. f (N \<omega>)) \<in> ?S \<rightarrow>\<^sub>M RR (N \<omega>)"
      by (rule measurable_component_singleton) simp
    have dj: "distr ?S (RR (N \<omega>)) (\<lambda>f. f (N \<omega>)) = RR (N \<omega>)"
      by (rule distr_PiM_component[OF Pj UNIV_I])
    have pglm: "pglue r T \<omega> \<in> RR (N \<omega>) \<rightarrow>\<^sub>M ?B"
    proof -
      have p1: "Pair \<omega> \<in> RR (N \<omega>) \<rightarrow>\<^sub>M Q \<Otimes>\<^sub>M ?MR"
        using measurable_Pair1'[OF w, of ?MR]
          measurable_cong_sets[OF setsR refl] by blast
      have p2: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> Q \<Otimes>\<^sub>M ?MR \<rightarrow>\<^sub>M ?B"
        by (rule pglue_measurable[OF r rT setsQ refl])
      from measurable_compose[OF p1 p2] show ?thesis by (simp add: comp_def)
    qed
    have Am: "{\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<in> sets (RR (N \<omega>))"
    proof -
      have "{\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
          = pglue r T \<omega> -` A \<inter> space (RR (N \<omega>))" by auto
      then show ?thesis using measurable_sets[OF pglm AB] by simp
    qed
    have "emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
        = emeasure (distr ?S (RR (N \<omega>)) (\<lambda>f. f (N \<omega>)))
            {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}"
      unfolding dj ..
    also have "\<dots> = emeasure ?S
        ((\<lambda>f. f (N \<omega>)) -` {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<inter> space ?S)"
      by (rule emeasure_distr[OF mj Am])
    also have "(\<lambda>f. f (N \<omega>)) -` {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}
          \<inter> space ?S
        = Pair \<omega> -` (kglue r T N -` A \<inter> space ?P)"
      using w measurable_space[OF mj] by (auto simp: space_pair_measure kglue_def)
    finally show ?thesis .
  qed
  \<comment> \<open>the left-hand side by Fubini\<close>
  have lhs: "emeasure (kglue_law r T N Q RR) A
      = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
  proof -
    have "emeasure (kglue_law r T N Q RR) A
        = emeasure ?P (kglue r T N -` A \<inter> space ?P)"
      unfolding kglue_law_def pair_law_of_def by (rule emeasure_distr[OF gm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure ?S (Pair \<omega> -` (kglue r T N -` A \<inter> space ?P)) \<partial>Q)"
      by (rule PS.emeasure_pair_measure_alt) (rule measurable_sets[OF gm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>))
        {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
      by (rule nn_integral_cong) (simp add: sec)
    finally show ?thesis .
  qed
  \<comment> \<open>the right-hand side by the semidirect product's disintegration\<close>
  have rhs: "emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A
      = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
  proof -
    define C where "C = (\<lambda>p. pglue r T (fst p) (snd p)) -` A
        \<inter> space (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)))"
    have Cs: "C \<in> sets (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>)))"
      unfolding C_def by (rule measurable_sets[OF pm AB])
    have Csp: "C \<in> sets (Q \<Otimes>\<^sub>M ?MR)" using Cs sets_ksemi[OF K ne] by simp
    have "emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A
        = emeasure (ksemi Q ?MR (\<lambda>\<omega>. RR (N \<omega>))) C"
      unfolding kglue_law'_def pair_law_of_def C_def
      by (rule emeasure_distr[OF pm AB])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C \<partial>Q)"
      unfolding ksemi_def
      by (rule emeasure_bind[OF ne ksemi_kernel_measurable[OF K] Csp])
    also have "\<dots> = (\<integral>\<^sup>+\<omega>. emeasure (RR (N \<omega>))
        {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A} \<partial>Q)"
    proof (rule nn_integral_cong)
      fix \<omega> assume w: "\<omega> \<in> space Q"
      have spR: "space (RR (N \<omega>)) = space ?MR"
        by (rule sets_eq_imp_space_eq[OF setsR])
      have "emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C
          = emeasure (RR (N \<omega>)) (Pair \<omega> -` C \<inter> space (RR (N \<omega>)))"
        by (rule emeasure_distr[OF ksemi_Pair_measurable[OF K w] Csp])
      also have "Pair \<omega> -` C \<inter> space (RR (N \<omega>))
          = {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}"
        unfolding C_def
        using w spR space_ksemi[OF K ne] by (auto simp: space_pair_measure)
      finally show "emeasure (distr (RR (N \<omega>)) (Q \<Otimes>\<^sub>M ?MR) (Pair \<omega>)) C
          = emeasure (RR (N \<omega>)) {\<omega>' \<in> space (RR (N \<omega>)). pglue r T \<omega> \<omega>' \<in> A}" .
    qed
    finally show ?thesis .
  qed
  show "emeasure (kglue_law r T N Q RR) A
      = emeasure (kglue_law' r T (\<lambda>\<omega>. RR (N \<omega>)) Q) A"
    using lhs rhs by simp
qed

subsection \<open>Kernel pasting: clauses (iii) and (iv), by weak closedness\<close>

text \<open>The class is closed under concatenation with a continuation chosen
  by an arbitrary measurable kernel, not just a countably valued index ---
  and the two martingale clauses never have to be proved for the
  semidirect product.

  Round the kernel to the dense sequence of the compact class
  (@{thm [source] Metric_space.countably_valued_approx}); each rounded
  glue is a legitimate pasting
  (@{thm [source] exit_class_kglue_law}) and, by
  @{thm [source] kglue_law_eq_kglue_law'}, is the kernel glue at the
  rounded kernel; the semidirect products converge weakly
  (@{thm [source] ksemi_weak_conv}), the glue is continuous
  (@{thm [source] Lipschitz_pglue}), so the glued laws converge; and the
  class is weakly closed
  (@{thm [source] exit_class_weak_closed}).\<close>

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
