section \<open>Kernels into the class: measurability and repair\<close>

(*<*)
theory Dynamic_Programming_Kernels
  imports Dynamic_Programming_Conditioning
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
begin

(*>*)

section \<open>Kernels into the class: measurability and repair\<close>

text \<open>@{thm [source] exit_class_kglue_law'} asks a kernel for two
  measurability facts: into \<^const>\<open>prob_algebra\<close> (its \<open>Kp\<close>) and into the
  class carrying its Levy-Prokhorov metric (its \<open>Kb\<close>).  The second is
  available only for the measurable selector, where @{thm [source]
  exit_val_measurable_selector_kernel'} produces it as part of the packaging.
  Every further kernel construction needs it too, so here it is as a
  factory: \<open>Kb\<close> is free once the kernel is measurable into
  \<^const>\<open>prob_algebra\<close> and lands in the class.

  The chain is: \<^const>\<open>prob_algebra\<close> is the Borel algebra of the weak
  topology restricted to the probability measures
  (@{thm [source] weak_conv_topology_eq_prob_algebra}); a map into a
  restricted space that lands in the restricting set is measurable into the
  ambient space; and the class's own metric topology is the subspace
  topology of weak convergence
  (@{thm [source] exit_class_compact_metric_space}).\<close>

lemma kernel_class_LP_measurable:
  fixes Kr :: "'a \<Rightarrow> ('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "1 \<le> L"
    and Kp: "Kr \<in> G \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and Kc: "\<And>\<omega>. Kr \<omega> \<in> exit_class k L T (0 :: real^'n)"
  shows "Kr \<in> G \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
      (exit_class k L T (0::real^'n))
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric))))"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?W = "weak_conv_topology (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
  let ?P = "{N :: ('n pairpath) measure. prob_space N \<and> sets N = sets ?B}"
  let ?C = "exit_class k L T (0::real^'n)"
  have inP: "Kr \<omega> \<in> ?P" for \<omega>
    using exit_class_prob[OF Kc] exit_class_sets[OF Kc] by simp
  have polish: "Polish_space (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
    by (rule Polish_space_path_metric)
  have setsPA: "sets (borel_of (subtopology ?W ?P)) = sets (prob_algebra ?B)"
    by (rule weak_conv_topology_eq_prob_algebra[OF polish])
  have r1: "Kr \<in> G \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?P"
  proof -
    have "Kr \<in> G \<rightarrow>\<^sub>M borel_of (subtopology ?W ?P)"
      using Kp measurable_cong_sets[OF refl setsPA[symmetric]] by blast
    then show ?thesis by (simp add: borel_of_subtopology)
  qed

  \<comment> \<open>a map into a restricted space that LANDS in the restricting set is
      measurable into the ambient space\<close>
  have amb: "Kr \<in> G \<rightarrow>\<^sub>M borel_of ?W"
  proof (rule measurableI)
    fix \<omega> assume w: "\<omega> \<in> space G"
    have "Kr \<omega> \<in> space (restrict_space (borel_of ?W) ?P)"
      by (rule measurable_space[OF r1 w])
    then show "Kr \<omega> \<in> space (borel_of ?W)" by (simp add: space_restrict_space)
  next
    fix A assume A: "A \<in> sets (borel_of ?W)"
    have "?P \<inter> A \<in> sets (restrict_space (borel_of ?W) ?P)"
      using A by (auto simp: sets_restrict_space)
    from measurable_sets[OF r1 this]
    have "Kr -` (?P \<inter> A) \<inter> space G \<in> sets G" .
    moreover have "Kr -` (?P \<inter> A) \<inter> space G = Kr -` A \<inter> space G"
      using inP by auto
    ultimately show "Kr -` A \<inter> space G \<in> sets G" by simp
  qed

  have top: "Metric_space.mtopology ?C
      (Levy_Prokhorov.LPm (mspace (path_metric T :: ('n pairpath) metric))
        (mdist (path_metric T :: ('n pairpath) metric)))
      = subtopology ?W ?C"
    using L by (intro exit_class_compact_metric_space(2)[OF T]) simp
  have r2: "Kr \<in> G \<rightarrow>\<^sub>M restrict_space (borel_of ?W) ?C"
    by (rule measurable_restrict_space2[OF _ amb]) (use Kc in auto)
  show ?thesis unfolding top using r2 by (simp add: borel_of_subtopology)
qed

text \<open>The "do nothing" branch of the mixed kernel: gluing a law onto its
  own regular conditional distribution gives the law back.  This is the
  law-level counterpart of @{thm [source] pglue_pcut_pfut}, and it is what
  lets a single fixed-time gluing change the law only on a chosen
  \<open>\<F>\<^sub>r\<close>-event and leave it alone elsewhere.\<close>

theorem kglue_law'_rcd_eq:
  fixes P :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and eq: "distr P
          ((path_borel r :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel (T - r) :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi (pair_law_of r (pcut r) P)
            ((path_borel (T - r) :: ('n pairpath) measure)) \<kappa>"
  shows "kglue_law' r T \<kappa> (pair_law_of r (pcut r) P) = P"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?Y = "(path_borel (T - r) :: ('n pairpath) measure)"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (pcut r \<omega>, pfut r T \<omega>)"
  let ?g = "\<lambda>p :: ('n pairpath) \<times> ('n pairpath). pglue r T (fst p) (snd p)"
  have spP: "space P = mspace (path_metric T :: ('n pairpath) metric)"
    by (rule space_of_path_sets[OF setsP])
  have mcut: "pcut r \<in> P \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT setsP])
  have mfut: "pfut r T \<in> P \<rightarrow>\<^sub>M ?Y" by (rule pfut_measurable_law[OF r rT setsP])
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using mcut mfut by simp
  have gm: "?g \<in> ?X \<Otimes>\<^sub>M ?Y \<rightarrow>\<^sub>M ?B"
    by (rule pglue_measurable[OF r rT refl refl])
  have "kglue_law' r T \<kappa> ?Q = distr (ksemi ?Q ?Y \<kappa>) ?B ?g"
    unfolding kglue_law'_def pair_law_of_def ..
  also have "\<dots> = distr (distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>) ?B ?g" unfolding eq ..
  also have "\<dots> = distr P ?B (?g \<circ> ?\<phi>)" by (rule distr_distr[OF gm mphi])
  also have "\<dots> = distr P ?B (\<lambda>\<omega>. \<omega>)"
  proof (rule distr_cong[OF refl refl])
    fix \<omega> :: "'n pairpath" assume "\<omega> \<in> space P"
    then have mw: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using spP by simp
    show "(?g \<circ> ?\<phi>) \<omega> = \<omega>" by (simp add: pglue_pcut_pfut[OF r rT mw])
  qed
  also have "\<dots> = P" by (rule distr_id2[OF setsP[symmetric]])
  finally show ?thesis .
qed

text \<open>The other branch needs a repair, and the repair needs the class to be
  a measurable set of laws.  It is: the class is compact in the weak
  topology (@{thm [source] exit_class_compactin_weak}), that topology
  is the Levy-Prokhorov metric topology hence Hausdorff, so the class is
  closed, hence Borel; and \<^const>\<open>prob_algebra\<close> is that Borel algebra
  restricted to the probability measures, which the class already consists
  of.\<close>

lemma exit_class_sets_prob_algebra:
  fixes x :: "real^'n::finite"
  assumes T: "0 < T" and L: "0 \<le> L"
  shows "exit_class k L T x
      \<in> sets (prob_algebra (path_borel T :: ('n pairpath) measure))"
proof -
  let ?X = "mtopology_of (path_metric T :: ('n pairpath) metric)"
  let ?W = "weak_conv_topology (mtopology_of
      (path_metric T :: ('n pairpath) metric))"
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?P = "{N :: ('n pairpath) measure. prob_space N \<and> sets N = sets ?B}"
  let ?C = "exit_class k L T x"
  interpret LP: Levy_Prokhorov "mspace (path_metric T :: ('n pairpath) metric)"
      "mdist (path_metric T :: ('n pairpath) metric)"
    by (simp add: Levy_Prokhorov_def)
  have Xeq: "LP.mtopology = ?X" by (simp add: mtopology_of_def)
  have sepLP: "separable_space LP.mtopology"
    using separable_path_metric Xeq by simp
  have LPtop: "LP.LPm.mtopology = ?W"
    using LP.LPmtopology_eq_weak_conv_topology[OF sepLP] Xeq by simp
  have haus: "Hausdorff_space ?W"
    using LP.LPm.Hausdorff_space_mtopology LPtop by simp
  have clo: "closedin ?W ?C"
    by (rule compactin_imp_closedin[OF haus
        exit_class_compactin_weak[OF T L]])
  have CW: "?C \<in> sets (borel_of ?W)" by (rule borel_of_closed[OF clo])
  have polish: "Polish_space ?X" by (rule Polish_space_path_metric)
  have setsPA: "sets (borel_of (subtopology ?W ?P)) = sets (prob_algebra ?B)"
    by (rule weak_conv_topology_eq_prob_algebra[OF polish])
  have sub: "?C \<subseteq> ?P"
  proof
    fix N :: "('n pairpath) measure" assume N: "N \<in> ?C"
    show "N \<in> ?P"
      using exit_class_prob[OF N] exit_class_sets[OF N] by simp
  qed
  have "?C = ?P \<inter> ?C" using sub by auto
  moreover have "?P \<inter> ?C \<in> sets (restrict_space (borel_of ?W) ?P)"
    using CW by (auto simp: sets_restrict_space)
  ultimately have "?C \<in> sets (borel_of (subtopology ?W ?P))"
    by (simp add: borel_of_subtopology)
  then show ?thesis using setsPA by simp
qed

text \<open>The repair.  A regular conditional distribution lands in the class
  only almost surely, while @{thm [source] exit_class_kglue_law'}
  asks for it at every point.  Since the class is a measurable set of laws,
  the kernel can be redirected to a fixed member off the good set, and the
  good set carries full measure, so nothing is lost.\<close>

lemma kernel_repair_into_class:
  fixes \<kappa> :: "'a \<Rightarrow> ('n::finite pairpath) measure"
  assumes T: "0 < T" and L: "1 \<le> L"
    and Km: "\<kappa> \<in> G \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
  obtains \<kappa>' where
    "\<kappa>' \<in> G \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and "\<And>p. \<kappa>' p \<in> exit_class k L T (0::real^'n)"
    and "\<And>p. \<kappa> p \<in> exit_class k L T (0::real^'n) \<Longrightarrow> \<kappa>' p = \<kappa> p"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?C = "exit_class k L T (0::real^'n)"
  have T0: "0 \<le> T" using T by simp
  have L0: "0 \<le> L" using L by simp
  obtain W where W: "W \<in> ?C"
    using exit_class_nonempty[OF T0 L] by blast
  have CS: "?C \<in> sets (prob_algebra ?B)"
    by (rule exit_class_sets_prob_algebra[OF T L0])
  have Wsp: "W \<in> space (prob_algebra ?B)"
    using exit_class_prob[OF W] exit_class_sets[OF W]
    by (simp add: space_prob_algebra)
  define \<kappa>' where "\<kappa>' = (\<lambda>p. if \<kappa> p \<in> ?C then \<kappa> p else W)"
  have good: "{p \<in> space G. \<kappa> p \<in> ?C} \<in> sets G"
  proof -
    have "\<kappa> -` ?C \<inter> space G \<in> sets G" by (rule measurable_sets[OF Km CS])
    moreover have "{p \<in> space G. \<kappa> p \<in> ?C} = \<kappa> -` ?C \<inter> space G" by auto
    ultimately show ?thesis by simp
  qed
  have m: "\<kappa>' \<in> G \<rightarrow>\<^sub>M prob_algebra ?B"
    unfolding \<kappa>'_def
    by (rule measurable_If[OF Km _ good]) (use Wsp in simp)
  have inC: "\<kappa>' p \<in> ?C" for p unfolding \<kappa>'_def using W by simp
  have agree: "\<kappa>' p = \<kappa> p" if "\<kappa> p \<in> ?C" for p unfolding \<kappa>'_def using that by simp
  show thesis by (rule that[OF m inC agree])
qed

text \<open>The mixed kernel itself: optimal on a chosen event of the past, the
  law's own conditional distribution elsewhere.  Measurability is
  @{thm [source] measurable_If}; the event has to be one the past can see,
  which for \<open>{\<theta> = t}\<close> is exactly the stopping-time property.\<close>

text \<open>\<open>kernel_mix_measurable\<close> lives in
  @{theory Continuous_Time_Martingales.Semidirect_Kernels}.\<close>

text \<open>The one-step engine of the stopping-time construction: glue \<open>P\<close> at a
  fixed time \<open>r\<close> with a kernel that plays the optimal continuation on a
  chosen event \<open>A\<close> of the past and \<open>P\<close>'s own conditional law elsewhere.  The
  result is again a class member, and off \<open>A\<close> nothing has changed
  (@{thm [source] kglue_law'_rcd_eq}).

  Iterating this over the finitely many values of a simple stopping time,
  with \<open>A = {\<theta> = t_j}\<close> --- an \<open>\<F>\<^sub>t\<^sub>j\<close>-event exactly because \<open>\<theta>\<close> is a stopping
  time --- is the construction the \<open>\<ge>\<close> half needs.
  @{thm [source] exit_class_kglue_law'} asks for the kernel's
  measurability with respect to the natural filtration at \<open>r\<close>, which is the
  whole of \<open>sets Q\<close> by @{thm [source] sets_natural_filtration_path}.\<close>

text \<open>Gluing does not touch the past: the \<open>r\<close>-cut of a glued path is the
  \<open>r\<close>-cut of its first factor, and if that factor already lives in the
  \<open>r\<close>-path space it is the factor.  This is what makes an \<open>\<F>\<^sub>r\<close>-event survive
  a glue at \<open>r\<close>.\<close>

lemma pcut_pglue:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
  shows "pcut r (pglue r T \<omega> \<omega>') = pcut r \<omega>"
proof (rule ext)
  fix t :: real
  show "pcut r (pglue r T \<omega> \<omega>') t = pcut r \<omega> t"
  proof (cases "t \<in> {0..r}")
    case True
    then have tT: "t \<in> {0..T}" using rT by auto
    have "pglue r T \<omega> \<omega>' t = \<omega> t" using True by (intro pglue_le[OF tT]) simp
    then show ?thesis using True by (simp add: pcut_def)
  next
    case False
    have "pcut r (pglue r T \<omega> \<omega>') t = undefined"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    moreover have "pcut r \<omega> t = undefined"
      unfolding pcut_def restrict_def by (rule if_not_P[OF False])
    ultimately show ?thesis by simp
  qed
qed

lemma pcut_pglue_self:
  fixes \<omega> \<omega>' :: "'n::finite pairpath"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and w: "\<omega> \<in> mspace (path_metric r :: ('n pairpath) metric)"
  shows "pcut r (pglue r T \<omega> \<omega>') = \<omega>"
proof -
  have "pcut r (pglue r T \<omega> \<omega>') = pcut r \<omega>" by (rule pcut_pglue[OF r rT])
  also have "\<dots> = \<omega>" unfolding pcut_def by (rule mspace_path_restrict_self[OF w])
  finally show ?thesis .
qed

text \<open>The almost-sure transfer through a glue, with the underlying measure
  \<open>Q\<close> left free, so that unfolding @{thm [source] pair_law_of_def} cannot
  also unfold a \<open>pair_law_of\<close> hiding inside \<open>Q\<close> itself.\<close>

lemma AE_kglue_law_of_kernel:
  fixes Q :: "('n::finite pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r \<le> T"
    and setsQ: "sets Q = sets (path_borel r :: ('n pairpath) measure)"
    and Kp: "Kr \<in> Q \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and ne: "space Q \<noteq> {}"
    and mset: "{\<omega> \<in> space (path_borel T :: ('n pairpath) measure). \<Phi> \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
  shows "(AE \<omega> in kglue_law' r T Kr Q. \<Phi> \<omega>)
      = (AE p in ksemi Q ((path_borel (T - r) :: ('n pairpath) measure)) Kr.
          \<Phi> (pglue r T (fst p) (snd p)))"
  unfolding kglue_law'_def pair_law_of_def
  by (rule AE_distr_iff[OF kglue_law'_measurable[OF r rT setsQ Kp ne] mset])

theorem exit_class_kglue_mixed:
  fixes P :: "('n::finite pairpath) measure" and x :: "real^'n"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L"
    and P: "P \<in> exit_class k L T x"
    and A: "A \<in> sets (path_borel r :: ('n pairpath) measure)"
    and Sp: "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ((path_borel (T - r) :: ('n pairpath) measure))"
    and Sc: "\<And>y. S y \<in> exit_class k L (T - r) (0::real^'n)"
  obtains \<kappa>' where
    "kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P)
        \<in> exit_class k L T x"
    and "\<And>p'. p' \<in> A \<Longrightarrow> \<kappa>' p' = S (fst (p' r))"
    and "\<And>p'. \<kappa>' p' \<in> exit_class k L (T - r) (0::real^'n)"
    and "\<And>\<Phi>. {\<omega> \<in> space (path_borel T :: ('n pairpath) measure). \<Phi> \<omega>}
          \<in> sets (path_borel T :: ('n pairpath) measure)
        \<Longrightarrow> (AE \<omega> in P. \<Phi> \<omega>)
        \<Longrightarrow> AE \<omega> in kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P).
              pcut r \<omega> \<in> A \<or> \<Phi> \<omega>"
    and "\<And>\<Phi>. {\<omega> \<in> space (path_borel T :: ('n pairpath) measure). \<Phi> \<omega>}
          \<in> sets (path_borel T :: ('n pairpath) measure)
        \<Longrightarrow> (\<And>p'. p' \<in> A
              \<Longrightarrow> p' \<in> mspace (path_metric r :: ('n pairpath) metric)
              \<Longrightarrow> AE \<omega>' in S (fst (p' r)). \<Phi> (pglue r T p' \<omega>'))
        \<Longrightarrow> AE \<omega> in kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P).
              pcut r \<omega> \<notin> A \<or> \<Phi> \<omega>"
proof -
  let ?X = "(path_borel r :: ('n pairpath) measure)"
  let ?s = "T - r"
  let ?Y = "(path_borel ?s :: ('n pairpath) measure)"
  let ?Q = "pair_law_of r (pcut r) P"
  have rT': "r \<le> T" using rT by simp
  have s0: "0 < ?s" using rT by simp
  have T0: "0 < T" using r rT by simp
  have setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    by (rule exit_class_sets[OF P])
  have PS: "prob_space P" by (rule exit_class_prob[OF P])
  have QC: "?Q \<in> exit_class k L r x"
    by (rule exit_class_pcut[OF r rT' P])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have spQ: "space ?Q = space ?X" by (rule sets_eq_imp_space_eq[OF setsQ])

  \<comment> \<open>the natural filtration at \<open>r\<close> IS all of \<open>sets ?Q\<close>\<close>
  have nfQ: "sets (natural_filtration ?Q 0 (\<lambda>v w :: 'n pairpath. w v) r)
      = sets ?Q"
  proof -
    have "natural_filtration ?Q 0 (\<lambda>v w :: 'n pairpath. w v) r
        = natural_filtration ?X 0 (\<lambda>v w. w v) r"
      by (rule natural_filtration_cong_space[OF spQ])
    then show ?thesis
      using sets_natural_filtration_path[OF r] setsQ by simp
  qed

  \<comment> \<open>the conditional law of \<open>P\<close>'s future, repaired to land in the class
      everywhere\<close>
  obtain \<kappa> where Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and eq: "distr P (?X \<Otimes>\<^sub>M ?Y) (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>))
        = ksemi ?Q ?Y \<kappa>"
    by (rule exit_class_rcd_ksemi[OF r rT' setsP PS])
  obtain \<kappa>0 where K0m: "\<kappa>0 \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and K0c: "\<And>p'. \<kappa>0 p' \<in> exit_class k L ?s (0::real^'n)"
    and K0a: "\<And>p'. \<kappa> p' \<in> exit_class k L ?s (0::real^'n)
        \<Longrightarrow> \<kappa>0 p' = \<kappa> p'"
    by (rule kernel_repair_into_class[where k = k, OF s0 L1 Km]) blast

  \<comment> \<open>the mixed kernel\<close>
  define \<kappa>' where "\<kappa>' = (\<lambda>p'. if p' \<in> A then S (fst (p' r)) else \<kappa>0 p')"
  have evm: "(\<lambda>p' :: 'n pairpath. fst (p' r)) \<in> ?Q \<rightarrow>\<^sub>M borel"
    by (rule measurable_compose
        [OF pair_law_eval_measurable[OF setsQ] pair_fst_borel])
  have Smq: "(\<lambda>p' :: 'n pairpath. S (fst (p' r))) \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    by (rule measurable_compose[OF evm Sp])
  have K0q: "\<kappa>0 \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using K0m measurable_cong_sets[OF setsQ refl] by blast
  have AQ: "A \<in> sets ?Q" using A setsQ by simp
  have Kp: "\<kappa>' \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    unfolding \<kappa>'_def by (rule kernel_mix_measurable[OF AQ Smq K0q])
  have Kc: "\<kappa>' p' \<in> exit_class k L ?s (0::real^'n)" for p'
    unfolding \<kappa>'_def using Sc K0c by simp
  have KpF: "\<kappa>' \<in> natural_filtration ?Q 0 (\<lambda>v w :: 'n pairpath. w v) r
      \<rightarrow>\<^sub>M prob_algebra ?Y"
    using Kp measurable_cong_sets[OF nfQ[symmetric] refl] by blast
  have Kb: "\<kappa>' \<in> natural_filtration ?Q 0 (\<lambda>v w :: 'n pairpath. w v) r
      \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
          (exit_class k L ?s (0::real^'n))
          (Levy_Prokhorov.LPm (mspace (path_metric ?s :: ('n pairpath) metric))
            (mdist (path_metric ?s :: ('n pairpath) metric))))"
    by (rule kernel_class_LP_measurable[OF s0 L1 KpF Kc])

  have glue: "kglue_law' r T \<kappa>' ?Q \<in> exit_class k L T x"
    by (rule exit_class_kglue_law'[OF r rT L1 T0 QC Kp Kb Kc])
  have onA: "\<kappa>' p' = S (fst (p' r))" if "p' \<in> A" for p'
    unfolding \<kappa>'_def using that by simp

  \<comment> \<open>off \<open>A\<close> the mixed kernel IS the conditional law, so the glued law
      inherits every almost-sure property of \<open>P\<close> there\<close>
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have L0: "0 \<le> L" using L1 by simp
  have ne: "space ?Q \<noteq> {}"
  proof -
    have "prob_space ?Q" by (rule exit_class_prob[OF QC])
    then show ?thesis by (rule prob_space.not_empty)
  qed
  have Km': "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using Km measurable_cong_sets[OF setsQ[symmetric] refl] by blast
  have kae: "AE p' in ?Q. \<kappa>0 p' = \<kappa> p'"
  proof -
    have "AE p' in ?Q. \<kappa> p' \<in> exit_class k L ?s (0::real^'n)"
      by (rule exit_class_rcd_member[OF r rT' L0 P Km eq])
    then show ?thesis
    proof (rule eventually_mono)
      fix p' :: "'n pairpath"
      assume "\<kappa> p' \<in> exit_class k L ?s (0::real^'n)"
      then show "\<kappa>0 p' = \<kappa> p'" by (rule K0a)
    qed
  qed
  have setsQY: "sets (?Q \<Otimes>\<^sub>M ?Y) = sets (?X \<Otimes>\<^sub>M ?Y)"
    by (rule sets_pair_measure_cong[OF setsQ refl])
  have glmQ: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ?Q \<Otimes>\<^sub>M ?Y \<rightarrow>\<^sub>M ?B"
  proof -
    have "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ksemi ?Q ?Y \<kappa>' \<rightarrow>\<^sub>M ?B"
      by (rule kglue_law'_measurable[OF r rT' setsQ Kp ne])
    then show ?thesis
      using measurable_cong_sets[OF sets_ksemi[OF Kp ne] refl] by blast
  qed
  have glm: "(\<lambda>p. pglue r T (fst p) (snd p)) \<in> ?X \<Otimes>\<^sub>M ?Y \<rightarrow>\<^sub>M ?B"
    using glmQ measurable_cong_sets[OF setsQY refl] by blast
  have pcm: "pcut r \<in> ?B \<rightarrow>\<^sub>M ?X" by (rule pcut_measurable[OF r rT' refl])
  have offA: "AE \<omega> in kglue_law' r T \<kappa>' ?Q. pcut r \<omega> \<in> A \<or> \<Phi> \<omega>"
    if Pm: "{\<omega> \<in> space ?B. \<Phi> \<omega>} \<in> sets ?B" and aeP: "AE \<omega> in P. \<Phi> \<omega>"
    for \<Phi> :: "'n pairpath \<Rightarrow> bool"
  proof -
    have mset2: "{\<omega> \<in> space ?B. pcut r \<omega> \<in> A \<or> \<Phi> \<omega>} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B. pcut r \<omega> \<in> A \<or> \<Phi> \<omega>}
          = (pcut r -` A \<inter> space ?B) \<union> {\<omega> \<in> space ?B. \<Phi> \<omega>}" by blast
      moreover have "pcut r -` A \<inter> space ?B \<in> sets ?B"
        by (rule measurable_sets[OF pcm A])
      ultimately show ?thesis using Pm by simp
    qed
    have mset3: "{p \<in> space (?Q \<Otimes>\<^sub>M ?Y).
          pcut r (pglue r T (fst p) (snd p)) \<in> A
            \<or> \<Phi> (pglue r T (fst p) (snd p))} \<in> sets (?Q \<Otimes>\<^sub>M ?Y)"
    proof -
      have "{p \<in> space (?Q \<Otimes>\<^sub>M ?Y). pcut r (pglue r T (fst p) (snd p)) \<in> A
            \<or> \<Phi> (pglue r T (fst p) (snd p))}
          = (\<lambda>p. pglue r T (fst p) (snd p))
              -` {\<omega> \<in> space ?B. pcut r \<omega> \<in> A \<or> \<Phi> \<omega>} \<inter> space (?Q \<Otimes>\<^sub>M ?Y)"
        by (auto dest: measurable_space[OF glmQ])
      then show ?thesis using measurable_sets[OF glmQ mset2] by simp
    qed
    have iff: "(AE \<omega> in kglue_law' r T \<kappa>' ?Q. pcut r \<omega> \<in> A \<or> \<Phi> \<omega>)
        = (AE p in ksemi ?Q ?Y \<kappa>'. pcut r (pglue r T (fst p) (snd p)) \<in> A
              \<or> \<Phi> (pglue r T (fst p) (snd p)))"
      by (rule AE_kglue_law_of_kernel[OF r rT' setsQ Kp ne mset2])
    have msetg: "{p \<in> space (?X \<Otimes>\<^sub>M ?Y). \<Phi> (pglue r T (fst p) (snd p))}
        \<in> sets (?X \<Otimes>\<^sub>M ?Y)"
    proof -
      have "{p \<in> space (?X \<Otimes>\<^sub>M ?Y). \<Phi> (pglue r T (fst p) (snd p))}
          = (\<lambda>p. pglue r T (fst p) (snd p)) -` {\<omega> \<in> space ?B. \<Phi> \<omega>}
              \<inter> space (?X \<Otimes>\<^sub>M ?Y)"
        by (auto dest: measurable_space[OF glm])
      then show ?thesis using measurable_sets[OF glm Pm] by simp
    qed
    have m1: "(\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>)) \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y"
      by (rule measurable_Pair[OF pcut_measurable[OF r rT' setsP]
            pfut_measurable_law[OF r rT' setsP]])
    have aeg: "AE \<omega> in P. \<Phi> (pglue r T (pcut r \<omega>) (pfut r T \<omega>))"
    proof (rule eventually_mono[OF eventually_conj[OF AE_space aeP]])
      fix \<omega> :: "'n pairpath"
      assume h: "\<omega> \<in> space P \<and> \<Phi> \<omega>"
      then have "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using sets_eq_imp_space_eq[OF setsP] by (simp add: space_borel_of)
      then have "pglue r T (pcut r \<omega>) (pfut r T \<omega>) = \<omega>"
        by (rule pglue_pcut_pfut[OF r rT'])
      then show "\<Phi> (pglue r T (pcut r \<omega>) (pfut r T \<omega>))" using h by simp
    qed
    have "AE p in distr P (?X \<Otimes>\<^sub>M ?Y) (\<lambda>\<omega>. (pcut r \<omega>, pfut r T \<omega>)).
        \<Phi> (pglue r T (fst p) (snd p))"
      unfolding AE_distr_iff[OF m1 msetg] using aeg by simp
    then have src: "AE p in ksemi ?Q ?Y \<kappa>. \<Phi> (pglue r T (fst p) (snd p))"
      unfolding eq .
    have msetg': "{p \<in> space (?Q \<Otimes>\<^sub>M ?Y). \<Phi> (pglue r T (fst p) (snd p))}
        \<in> sets (?Q \<Otimes>\<^sub>M ?Y)"
      using msetg setsQY sets_eq_imp_space_eq[OF setsQY] by simp
    have src': "AE p' in ?Q. AE \<omega>' in \<kappa> p'. \<Phi> (pglue r T p' \<omega>')"
      using src unfolding AE_ksemi[OF Km' msetg'] by simp
    have inner: "AE p' in ?Q. AE \<omega>' in \<kappa>' p'.
        pcut r (pglue r T p' \<omega>') \<in> A \<or> \<Phi> (pglue r T p' \<omega>')"
    proof (rule eventually_mono[OF eventually_conj[OF AE_space
        eventually_conj[OF kae src']]])
      fix p' :: "'n pairpath"
      assume h: "p' \<in> space ?Q
          \<and> (\<kappa>0 p' = \<kappa> p' \<and> (AE \<omega>' in \<kappa> p'. \<Phi> (pglue r T p' \<omega>')))"
      have w: "p' \<in> mspace (path_metric r :: ('n pairpath) metric)"
        using h spQ by (simp add: space_borel_of)
      show "AE \<omega>' in \<kappa>' p'. pcut r (pglue r T p' \<omega>') \<in> A
          \<or> \<Phi> (pglue r T p' \<omega>')"
      proof (cases "p' \<in> A")
        case True
        have "pcut r (pglue r T p' \<omega>') \<in> A" for \<omega>' :: "'n pairpath"
          using pcut_pglue_self[OF r rT' w] True by simp
        then show ?thesis by simp
      next
        case False
        then have "\<kappa>' p' = \<kappa> p'" unfolding \<kappa>'_def using h by simp
        then have kk: "\<kappa>' p' = \<kappa> p'" .
        have "AE \<omega>' in \<kappa> p'. \<Phi> (pglue r T p' \<omega>')" using h by simp
        then have "AE \<omega>' in \<kappa> p'.
            pcut r (pglue r T p' \<omega>') \<in> A \<or> \<Phi> (pglue r T p' \<omega>')"
          by (auto elim: eventually_mono)
        then show ?thesis unfolding kk .
      qed
    qed
    show ?thesis unfolding iff AE_ksemi[OF Kp mset3] using inner by simp
  qed

  \<comment> \<open>and ON \<open>A\<close> the mixed kernel IS the optimal continuation, so the glued
      law inherits every almost-sure property of \<open>S\<close> there\<close>
  have onAae: "AE \<omega> in kglue_law' r T \<kappa>' ?Q. pcut r \<omega> \<notin> A \<or> \<Phi> \<omega>"
    if Pm: "{\<omega> \<in> space ?B. \<Phi> \<omega>} \<in> sets ?B"
      and aeS: "\<And>p'. p' \<in> A
        \<Longrightarrow> p' \<in> mspace (path_metric r :: ('n pairpath) metric)
        \<Longrightarrow> AE \<omega>' in S (fst (p' r)). \<Phi> (pglue r T p' \<omega>')"
    for \<Phi> :: "'n pairpath \<Rightarrow> bool"
  proof -
    have mset2: "{\<omega> \<in> space ?B. pcut r \<omega> \<notin> A \<or> \<Phi> \<omega>} \<in> sets ?B"
    proof -
      have "{\<omega> \<in> space ?B. pcut r \<omega> \<notin> A \<or> \<Phi> \<omega>}
          = (space ?B - (pcut r -` A \<inter> space ?B)) \<union> {\<omega> \<in> space ?B. \<Phi> \<omega>}"
        by blast
      moreover have "pcut r -` A \<inter> space ?B \<in> sets ?B"
        by (rule measurable_sets[OF pcm A])
      ultimately show ?thesis using Pm by simp
    qed
    have mset3: "{p \<in> space (?Q \<Otimes>\<^sub>M ?Y).
          pcut r (pglue r T (fst p) (snd p)) \<notin> A
            \<or> \<Phi> (pglue r T (fst p) (snd p))} \<in> sets (?Q \<Otimes>\<^sub>M ?Y)"
    proof -
      have "{p \<in> space (?Q \<Otimes>\<^sub>M ?Y). pcut r (pglue r T (fst p) (snd p)) \<notin> A
            \<or> \<Phi> (pglue r T (fst p) (snd p))}
          = (\<lambda>p. pglue r T (fst p) (snd p))
              -` {\<omega> \<in> space ?B. pcut r \<omega> \<notin> A \<or> \<Phi> \<omega>} \<inter> space (?Q \<Otimes>\<^sub>M ?Y)"
        by (auto dest: measurable_space[OF glmQ])
      then show ?thesis using measurable_sets[OF glmQ mset2] by simp
    qed
    have iff: "(AE \<omega> in kglue_law' r T \<kappa>' ?Q. pcut r \<omega> \<notin> A \<or> \<Phi> \<omega>)
        = (AE p in ksemi ?Q ?Y \<kappa>'. pcut r (pglue r T (fst p) (snd p)) \<notin> A
              \<or> \<Phi> (pglue r T (fst p) (snd p)))"
      by (rule AE_kglue_law_of_kernel[OF r rT' setsQ Kp ne mset2])
    have inner: "AE p' in ?Q. AE \<omega>' in \<kappa>' p'.
        pcut r (pglue r T p' \<omega>') \<notin> A \<or> \<Phi> (pglue r T p' \<omega>')"
    proof (rule eventually_mono[OF AE_space])
      fix p' :: "'n pairpath"
      assume hs: "p' \<in> space ?Q"
      have w: "p' \<in> mspace (path_metric r :: ('n pairpath) metric)"
        using hs spQ by (simp add: space_borel_of)
      show "AE \<omega>' in \<kappa>' p'. pcut r (pglue r T p' \<omega>') \<notin> A
          \<or> \<Phi> (pglue r T p' \<omega>')"
      proof (cases "p' \<in> A")
        case True
        then have kk: "\<kappa>' p' = S (fst (p' r))" by (rule onA)
        have "AE \<omega>' in S (fst (p' r)). \<Phi> (pglue r T p' \<omega>')"
          by (rule aeS[OF True w])
        then have "AE \<omega>' in S (fst (p' r)).
            pcut r (pglue r T p' \<omega>') \<notin> A \<or> \<Phi> (pglue r T p' \<omega>')"
          by (auto elim: eventually_mono)
        then show ?thesis unfolding kk .
      next
        case False
        have "pcut r (pglue r T p' \<omega>') \<notin> A" for \<omega>' :: "'n pairpath"
          using pcut_pglue_self[OF r rT' w] False by simp
        then show ?thesis by simp
      qed
    qed
    show ?thesis unfolding iff AE_ksemi[OF Kp mset3] using inner by simp
  qed
  show thesis by (rule that[OF glue onA Kc offA onAae])
qed

subsection \<open>The \<open>\<ge>\<close> half at a random time, reduced to a constant\<close>

text \<open>The passage from a constant lower bound to the essential infimum does
  not care whether the time is deterministic: it needs only that the
  integrand lies between \<open>0\<close> and \<open>T\<close>, which holds for every
  \<open>0 \<le> \<theta> \<omega> \<le> T\<close>, with no measurability and no stopping-time property.  So
  the whole \<open>\<ge>\<close> half at a random time reduces to the constant statement,
  exactly as @{thm [source] exit_val_dpp_sup_ge} reduces to
  @{thm [source] exit_val_dpp_ge_const}.\<close>

theorem exit_val_dpp_sup_ge_time_of_const:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and \<theta> :: "'n pairpath \<Rightarrow> real"
  assumes th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
    and const: "\<And>P c. P \<in> exit_class k L T x \<Longrightarrow>
        (AE \<omega> in P. c \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
            + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
               then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
        \<Longrightarrow> ennreal c \<le> exit_val k L T K x"
  shows "(SUP P \<in> exit_class k L T x. ess_inf_time P
            (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
              + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
                 then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)))
      \<le> exit_val k L T K x"
proof (rule SUP_least)
  fix P :: "('n pairpath) measure"
  assume P: "P \<in> exit_class k L T x"
  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
        + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
           then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)" for \<omega>
  have geta: "g = (\<lambda>\<omega> :: 'n pairpath. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))"
    by (rule ext) (simp add: g_def)
  have vbnd: "(if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
      then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0) \<le> T - \<theta> \<omega>"
    for \<omega> :: "'n pairpath"
  proof -
    have Tr': "0 \<le> T - \<theta> \<omega>" using thT[of \<omega>] by simp
    show ?thesis
    proof (cases "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K")
      case True
      have "ennreal (enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))))
          = exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))"
        using exit_val_neq_top[of "T - \<theta> \<omega>" k L K "fst (\<omega> (\<theta> \<omega>))"] Tr'
        by (simp add: less_top)
      also have "\<dots> \<le> ennreal (T - \<theta> \<omega>)" by (rule exit_val_le_T[OF Tr'])
      finally have "enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) \<le> T - \<theta> \<omega>"
        using Tr' by simp
      then show ?thesis using True by simp
    next
      case False
      then have "(if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
          then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0) = 0"
        by (rule if_not_P)
      then show ?thesis using Tr' by simp
    qed
  qed
  have gle: "g \<omega> \<le> T" for \<omega> :: "'n pairpath"
  proof -
    have "pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) \<le> \<theta> \<omega>" by (rule pexit_le_T[OF th0])
    with vbnd[of \<omega>] show ?thesis unfolding g_def by linarith
  qed
  have gnn: "0 \<le> g \<omega>" for \<omega> :: "'n pairpath"
  proof -
    have p: "0 \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))" by (rule pexit_nonneg[OF th0])
    have q: "0 \<le> (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
        then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)" by simp
    from p q show ?thesis unfolding g_def by linarith
  qed
  have PP: "prob_space P" by (rule exit_class_prob[OF P])
  have fin: "ess_inf_time P g \<le> ennreal T"
    by (rule ess_inf_time_le_const[OF PP gle])
  have ntop: "ess_inf_time P g < \<top>"
  proof -
    have "(ennreal T :: ennreal) < \<top>" by simp
    with fin show ?thesis by (rule order.strict_trans1)
  qed
  define c where "c = enn2real (ess_inf_time P g)"
  have ceq: "ennreal c = ess_inf_time P g"
    unfolding c_def by (rule ennreal_enn2real[OF ntop])
  have aec0: "AE \<omega> in P. c \<le> g \<omega>"
  proof (rule eventually_mono[OF ess_inf_time_AE[of P g]])
    fix \<omega> :: "'n pairpath"
    assume "ess_inf_time P g \<le> ennreal (g \<omega>)"
    then have "ennreal c \<le> ennreal (g \<omega>)" using ceq by simp
    then show "c \<le> g \<omega>" using gnn[of \<omega>] by simp
  qed
  have aec: "AE \<omega> in P. c \<le> pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)"
    using aec0 unfolding g_def .
  have main: "ennreal c \<le> exit_val k L T K x" by (rule const[OF P aec])
  have "ess_inf_time P (\<lambda>\<omega> :: 'n pairpath. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0)) = ennreal c"
    using ceq geta by simp
  then show "ess_inf_time P (\<lambda>\<omega>. pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t))
      + (if pexit (\<theta> \<omega>) K (\<lambda>t. fst (\<omega> t)) = \<theta> \<omega> \<and> fst (\<omega> (\<theta> \<omega>)) \<in> K
         then enn2real (exit_val k L (T - \<theta> \<omega>) K (fst (\<omega> (\<theta> \<omega>)))) else 0))
      \<le> exit_val k L T K x"
    using main by simp
qed

subsection \<open>The constant form at a random time with two values\<close>

text \<open>At the horizon \<open>0\<close> there is nothing left to gain, so the DPP
  integrand at \<open>\<theta> = T\<close> is the plain exit time, which is why a stopping time
  with values \<open>{r, T}\<close> costs exactly one glue.\<close>

lemma exit_val_horizon_zero:
  fixes K :: "(real^'n::finite) set" and y :: "real^'n"
  shows "exit_val k L 0 K y = 0"
proof -
  have "exit_val k L 0 K y \<le> ennreal 0" by (rule exit_val_le_T[OF order.refl])
  then show ?thesis by simp
qed

text \<open>The selector's optimality, transported to the glued path.  This is
  the \<open>inner\<close> step of @{thm [source] exit_val_dpp_ge_const}, pulled out so
  that the mixed glue can use it for the branch that lands on the gluing
  event.\<close>

lemma pexit_pglue_selector_ge:
  fixes K :: "(real^'n::finite) set" and \<omega> :: "'n pairpath"
  assumes r: "0 \<le> r" and rT: "r < T" and K: "closed K"
    and SC: "S (fst (\<omega> r)) \<in> exit_class k L (T - r) (0::real^'n)"
    and Sval: "ess_inf_time (pshift_law (T - r) (fst (\<omega> r)) (S (fst (\<omega> r))))
        (\<lambda>w. pexit (T - r) K (\<lambda>t. fst (w t)))
      = exit_val k L (T - r) K (fst (\<omega> r))"
    and gw: "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)"
  shows "AE \<omega>' in S (fst (\<omega> r)). c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
proof -
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  have rT': "r \<le> T" using rT by simp
  have Tr': "0 \<le> T - r" using rT by simp
  define v where "v = enn2real (exit_val k L (T - r) K (fst (\<omega> r)))"
  have vnn: "0 \<le> v" by (simp add: v_def)
  have vfin: "exit_val k L (T - r) K (fst (\<omega> r)) < \<top>"
    using exit_val_neq_top[of "T - r" k L K "fst (\<omega> r)"] Tr' by (simp add: less_top)
  have veq: "ennreal v = exit_val k L (T - r) K (fst (\<omega> r))"
    unfolding v_def by (rule ennreal_enn2real[OF vfin])
  have vle: "v \<le> T - r"
  proof -
    have "ennreal v \<le> ennreal (T - r)" unfolding veq by (rule exit_val_le_T[OF Tr'])
    then show ?thesis using Tr' by simp
  qed
  have gw': "c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
      + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then v else 0)"
    using gw unfolding v_def .
  have z0: "AE \<omega>' in S (fst (\<omega> r)). fst (\<omega>' 0) = 0"
    using exit_class_start[OF SC] by (auto elim: eventually_mono)
  have opt: "AE \<omega>' in S (fst (\<omega> r)).
      v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
  proof -
    have ae1: "AE w in pshift_law (T - r) (fst (\<omega> r)) (S (fst (\<omega> r))).
        exit_val k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (w t)))"
      unfolding Sval[symmetric] by (rule ess_inf_time_AE)
    have setsSy: "sets (S (fst (\<omega> r))) = sets ?MR"
      by (rule exit_class_sets[OF SC])
    have shm: "pshift (T - r) (fst (\<omega> r)) \<in> S (fst (\<omega> r)) \<rightarrow>\<^sub>M ?MR"
      using pshift_measurable[OF Tr'] measurable_cong_sets[OF setsSy refl] by blast
    have m1: "(\<lambda>w :: 'n pairpath. ennreal (pexit (T - r) K (\<lambda>t. fst (w t))))
        \<in> borel_measurable ?MR"
      using pexit_path_measurable[OF Tr' K refl] by measurable
    have mset: "{w \<in> space ?MR. exit_val k L (T - r) K (fst (\<omega> r))
        \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (w t)))} \<in> sets ?MR"
      using m1 by measurable
    have ae2: "AE \<omega>' in S (fst (\<omega> r)). exit_val k L (T - r) K (fst (\<omega> r))
        \<le> ennreal (pexit (T - r) K
            (\<lambda>t. fst (pshift (T - r) (fst (\<omega> r)) \<omega>' t)))"
      using ae1 unfolding pshift_law_def AE_distr_iff[OF shm mset] .
    have ae3: "AE \<omega>' in S (fst (\<omega> r)). exit_val k L (T - r) K (fst (\<omega> r))
        \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
      using ae2 by (simp add: pexit_pshift)
    show ?thesis
    proof (rule eventually_mono[OF ae3])
      fix \<omega>' :: "'n pairpath"
      assume "exit_val k L (T - r) K (fst (\<omega> r))
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
      then have "ennreal v
          \<le> ennreal (pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)))"
        using veq by simp
      then show "v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
        using pexit_nonneg[OF Tr', of K "\<lambda>t. fst (\<omega> r) + fst (\<omega>' t)"] by simp
    qed
  qed
  show ?thesis
  proof (rule eventually_mono[OF eventually_conj[OF z0 opt]])
    fix \<omega>' :: "'n pairpath"
    assume h: "fst (\<omega>' 0) = 0
        \<and> v \<le> pexit (T - r) K (\<lambda>t. fst (\<omega> r) + fst (\<omega>' t))"
    have "pexit r K (\<lambda>t. fst (\<omega> t))
          + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K then v else 0)
        \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))"
    proof (rule pexit_pglue_dpp[OF r rT' vnn])
      show "r + v \<le> T" using vle by simp
      show "fst (\<omega>' 0) = 0" using h by simp
      show "pexit r K (\<lambda>t. fst (\<omega> t)) = r \<Longrightarrow> fst (\<omega> r) \<in> K
          \<Longrightarrow> v \<le> pexit (T - r) K (\<lambda>s. fst (\<omega> r) + fst (\<omega>' s))"
        using h by simp
    qed
    with gw' show "c \<le> pexit T K (\<lambda>t. fst (pglue r T \<omega> \<omega>' t))" by simp
  qed
qed

text \<open>The constant form of the \<open>\<ge>\<close> half at the two-valued stopping time
  \<open>\<theta> = (if pcut r \<omega> \<in> A then r else T)\<close>, for an arbitrary \<open>\<F>\<^sub>r\<close>-event \<open>A\<close>.
  The hypothesis is exactly \<open>c \<le> integrand\<^sub>\<theta>\<close> for that \<open>\<theta>\<close>, read through
  @{thm [source] exit_val_horizon_zero} on the \<open>\<theta> = T\<close> branch.  One glue does
  it: the mixed kernel plays the optimal continuation on \<open>A\<close> and the
  conditional law of \<open>P\<close> off it, and the two transfer conclusions of
  @{thm [source] exit_class_kglue_mixed} cover the two branches.\<close>

theorem exit_val_dpp_ge_const_two:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and P: "P \<in> exit_class k L T x"
    and A: "A \<in> sets (path_borel r :: ('n pairpath) measure)"
    and c: "AE \<omega> in P.
        (pcut r \<omega> \<in> A \<longrightarrow> c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
        \<and> (pcut r \<omega> \<notin> A \<longrightarrow> c \<le> pexit T K (\<lambda>t. fst (\<omega> t)))"
  shows "ennreal c \<le> exit_val k L T K x"
proof -
  let ?BT = "(path_borel T :: ('n pairpath) measure)"
  let ?BR = "(path_borel r :: ('n pairpath) measure)"
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  have rT': "r \<le> T" using rT by simp
  have T0: "0 < T" using r rT by simp
  have T0': "0 \<le> T" using T0 by simp
  have Tr: "0 < T - r" using rT by simp
  have Tr': "0 \<le> T - r" using Tr by simp
  have Kbor: "K \<in> sets borel" by (rule borel_closed[OF K])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)

  obtain S where Sk: "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?MR"
    and Ssub: "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (exit_class k L (T - r) (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
          (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and SC: "\<And>y. S y \<in> exit_class k L (T - r) 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law (T - r) y (S y))
        (\<lambda>\<omega>. pexit (T - r) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - r) K y"
    by (rule exit_val_measurable_selector_kernel'[where k = k, OF Tr L1 K]) blast

  \<comment> \<open>the integrand at \<open>r\<close>, and the part of \<open>A\<close> where it beats \<open>c\<close>\<close>
  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)" for \<omega>
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BR"
    by (rule pexit_path_measurable[OF r K refl])
  have endm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF refl] mfst])
  have vm: "(\<lambda>\<omega> :: 'n pairpath. enn2real (exit_val k L (T - r) K (fst (\<omega> r))))
      \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF endm exit_val_borel_measurable[OF Tr L1 K]])
  have predm: "Measurable.pred ?BR (\<lambda>\<omega> :: 'n pairpath.
      pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K)"
    using taum endm Kbor by measurable
  have gm: "g \<in> borel_measurable ?BR"
    unfolding g_def using taum vm predm by measurable
  have gset: "{\<omega> \<in> space ?BR. c \<le> g \<omega>} \<in> sets ?BR" using gm by measurable
  have gcut: "g (pcut r \<omega>) = g \<omega>" for \<omega> :: "'n pairpath"
    using r by (simp add: g_def pexit_pcut pcut_apply)
  define A' where "A' = A \<inter> {\<omega> \<in> space ?BR. c \<le> g \<omega>}"
  have A's: "A' \<in> sets ?BR" unfolding A'_def using A gset by simp

  obtain \<kappa>' where glue: "kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P)
        \<in> exit_class k L T x"
    and onA: "\<And>p'. p' \<in> A' \<Longrightarrow> \<kappa>' p' = S (fst (p' r))"
    and Kc: "\<And>p'. \<kappa>' p' \<in> exit_class k L (T - r) (0::real^'n)"
    and offA: "\<And>\<Phi>. {\<omega> \<in> space ?BT. \<Phi> \<omega>} \<in> sets ?BT \<Longrightarrow> (AE \<omega> in P. \<Phi> \<omega>)
        \<Longrightarrow> AE \<omega> in kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P).
              pcut r \<omega> \<in> A' \<or> \<Phi> \<omega>"
    and onAae: "\<And>\<Phi>. {\<omega> \<in> space ?BT. \<Phi> \<omega>} \<in> sets ?BT
        \<Longrightarrow> (\<And>p'. p' \<in> A'
              \<Longrightarrow> p' \<in> mspace (path_metric r :: ('n pairpath) metric)
              \<Longrightarrow> AE \<omega>' in S (fst (p' r)). \<Phi> (pglue r T p' \<omega>'))
        \<Longrightarrow> AE \<omega> in kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P).
              pcut r \<omega> \<notin> A' \<or> \<Phi> \<omega>"
    by (rule exit_class_kglue_mixed[OF r rT L1 P A's Sk SC]) blast
  define R where "R = kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P)"
  have RC: "R \<in> exit_class k L T x" unfolding R_def by (rule glue)

  have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BT"
    by (rule pexit_path_measurable[OF T0' K refl])
  have pcm: "pcut r \<in> ?BT \<rightarrow>\<^sub>M ?BR" by (rule pcut_measurable[OF r rT' refl])
  have m2: "{\<omega> \<in> space ?BT. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))} \<in> sets ?BT"
    using tauT by measurable
  have m1: "{\<omega> \<in> space ?BT. pcut r \<omega> \<in> A'
      \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))} \<in> sets ?BT"
  proof -
    have "{\<omega> \<in> space ?BT. pcut r \<omega> \<in> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))}
        = (pcut r -` A' \<inter> space ?BT)
            \<union> {\<omega> \<in> space ?BT. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))}" by blast
    moreover have "pcut r -` A' \<inter> space ?BT \<in> sets ?BT"
      by (rule measurable_sets[OF pcm A's])
    ultimately show ?thesis using m2 by simp
  qed

  \<comment> \<open>off \<open>A'\<close>: the glued law is \<open>P\<close>'s, and the hypothesis is already the bound\<close>
  have aeP1: "AE \<omega> in P. pcut r \<omega> \<in> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    using c AE_space
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (cases "pcut r \<omega> \<in> A")
      case True
      have "pcut r \<omega> \<in> space ?BR"
        using measurable_space[OF pcut_measurable[OF r rT'
            exit_class_sets[OF P]] elim(2)] .
      moreover have "c \<le> g (pcut r \<omega>)"
      proof -
        have "c \<le> g \<omega>" using elim(1) True unfolding g_def by simp
        then show ?thesis unfolding gcut .
      qed
      ultimately show ?thesis unfolding A'_def using True by simp
    next
      case False
      then have "pcut r \<omega> \<notin> A'" unfolding A'_def by simp
      then show ?thesis using elim(1) False by simp
    qed
  qed
  have off: "AE \<omega> in R. pcut r \<omega> \<in> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof -
    have "AE \<omega> in R. pcut r \<omega> \<in> A'
        \<or> (pcut r \<omega> \<in> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t)))"
      unfolding R_def by (rule offA[OF m1 aeP1])
    then show ?thesis by (auto elim: eventually_mono)
  qed

  \<comment> \<open>on \<open>A'\<close>: the selector's optimality, through @{thm [source] pexit_pglue_dpp}\<close>
  have on: "AE \<omega> in R. pcut r \<omega> \<notin> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    unfolding R_def
  proof (rule onAae[OF m2])
    fix p' :: "'n pairpath"
    assume pA: "p' \<in> A'"
    have cg: "c \<le> g p'" using pA unfolding A'_def by simp
    show "AE \<omega>' in S (fst (p' r)).
        c \<le> pexit T K (\<lambda>t. fst (pglue r T p' \<omega>' t))"
    proof (rule pexit_pglue_selector_ge[OF r rT K])
      show "S (fst (p' r)) \<in> exit_class k L (T - r) (0::real^'n)"
        by (rule SC)
      show "ess_inf_time (pshift_law (T - r) (fst (p' r)) (S (fst (p' r))))
          (\<lambda>w. pexit (T - r) K (\<lambda>t. fst (w t)))
        = exit_val k L (T - r) K (fst (p' r))" by (rule Sval)
      show "c \<le> pexit r K (\<lambda>t. fst (p' t))
          + (if pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (p' r))) else 0)"
        using cg unfolding g_def .
    qed
  qed

  have all: "AE \<omega> in R. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
  proof (rule eventually_mono[OF eventually_conj[OF off on]])
    fix \<omega> :: "'n pairpath"
    assume "(pcut r \<omega> \<in> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t)))
        \<and> (pcut r \<omega> \<notin> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t)))"
    then show "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))" by blast
  qed

  have "ennreal c \<le> ess_inf_time R (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t)))"
    unfolding ess_inf_time_ge_iff using all
    by (auto elim: eventually_mono intro: ennreal_leI)
  also have "\<dots> \<le> exit_val k L T K x"
    unfolding exit_val_def by (rule SUP_upper[OF RC])
  finally show ?thesis .
qed

text \<open>Feeding that into @{thm [source] exit_val_dpp_sup_ge_time_of_const}
  gives the \<open>\<ge>\<close> half of (2.9) at the two-valued stopping time.\<close>

subsection \<open>The induction step: one glue, with the rest left as a predicate\<close>

text \<open>@{thm [source] exit_val_dpp_ge_const_two} is this lemma with
  \<open>\<Psi> \<omega> = (c \<le> \<tau>\<^sub>K \<omega>)\<close>.  Leaving \<open>\<Psi>\<close> free turns it into the step of the
  induction over the values of a simple stopping time: glue at \<open>r\<close> on the
  \<open>\<F>\<^sub>r\<close>-event \<open>A\<close>, keep whatever \<open>\<Psi>\<close> says off it, and hand the result to the
  next value.  The conclusion records \<open>pcut r \<omega> \<in> A\<close> alongside the bound so
  that the next step can see those paths have \<open>\<theta> \<omega> = r\<close> and are not in the
  next gluing event, which keeps the earlier glues from being undone.\<close>

theorem exit_val_dpp_ge_step:
  fixes K :: "(real^'n::finite) set" and x :: "real^'n"
    and P :: "('n pairpath) measure" and \<Psi> :: "'n pairpath \<Rightarrow> bool"
  assumes r: "0 \<le> r" and rT: "r < T" and L1: "1 \<le> L" and K: "closed K"
    and P: "P \<in> exit_class k L T x"
    and A: "A \<in> sets (path_borel r :: ('n pairpath) measure)"
    and Psm: "{\<omega> \<in> space (path_borel T :: ('n pairpath) measure). \<Psi> \<omega>}
        \<in> sets (path_borel T :: ('n pairpath) measure)"
    and c: "AE \<omega> in P.
        (pcut r \<omega> \<in> A \<longrightarrow> c \<le> pexit r K (\<lambda>t. fst (\<omega> t))
            + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
               then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0))
        \<and> (pcut r \<omega> \<notin> A \<longrightarrow> \<Psi> \<omega>)"
  obtains R where "R \<in> exit_class k L T x"
    and "AE \<omega> in R.
        (pcut r \<omega> \<in> A \<and> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))) \<or> \<Psi> \<omega>"
proof -
  let ?BT = "(path_borel T :: ('n pairpath) measure)"
  let ?BR = "(path_borel r :: ('n pairpath) measure)"
  let ?MR = "(path_borel (T - r) :: ('n pairpath) measure)"
  have rT': "r \<le> T" using rT by simp
  have T0': "0 \<le> T" using r rT by simp
  have Tr: "0 < T - r" using rT by simp
  have Kbor: "K \<in> sets borel" by (rule borel_closed[OF K])
  have mfst: "(fst :: (real^'n) \<times> (real^'n^'n) \<Rightarrow> real^'n) \<in> borel_measurable borel"
    using measurable_fst[of "borel :: (real^'n) measure"
        "borel :: (real^'n^'n) measure"] by (simp add: borel_prod)

  obtain S where Sk: "S \<in> borel \<rightarrow>\<^sub>M prob_algebra ?MR"
    and Ssub: "S \<in> borel \<rightarrow>\<^sub>M borel_of (Metric_space.mtopology
        (exit_class k L (T - r) (0::real^'n))
        (Levy_Prokhorov.LPm (mspace (path_metric (T - r) :: ('n pairpath) metric))
          (mdist (path_metric (T - r) :: ('n pairpath) metric))))"
    and SC: "\<And>y. S y \<in> exit_class k L (T - r) 0"
    and Sval: "\<And>y. ess_inf_time (pshift_law (T - r) y (S y))
        (\<lambda>\<omega>. pexit (T - r) K (\<lambda>t. fst (\<omega> t))) = exit_val k L (T - r) K y"
    by (rule exit_val_measurable_selector_kernel'[where k = k, OF Tr L1 K]) blast

  define g :: "'n pairpath \<Rightarrow> real" where
    "g \<omega> = pexit r K (\<lambda>t. fst (\<omega> t))
        + (if pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K
           then enn2real (exit_val k L (T - r) K (fst (\<omega> r))) else 0)" for \<omega>
  have taum: "(\<lambda>\<omega> :: 'n pairpath. pexit r K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BR"
    by (rule pexit_path_measurable[OF r K refl])
  have endm: "(\<lambda>\<omega> :: 'n pairpath. fst (\<omega> r)) \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF pair_law_eval_measurable[OF refl] mfst])
  have vm: "(\<lambda>\<omega> :: 'n pairpath. enn2real (exit_val k L (T - r) K (fst (\<omega> r))))
      \<in> borel_measurable ?BR"
    by (rule measurable_compose[OF endm exit_val_borel_measurable[OF Tr L1 K]])
  have predm: "Measurable.pred ?BR (\<lambda>\<omega> :: 'n pairpath.
      pexit r K (\<lambda>t. fst (\<omega> t)) = r \<and> fst (\<omega> r) \<in> K)"
    using taum endm Kbor by measurable
  have gm: "g \<in> borel_measurable ?BR"
    unfolding g_def using taum vm predm by measurable
  have gset: "{\<omega> \<in> space ?BR. c \<le> g \<omega>} \<in> sets ?BR" using gm by measurable
  have gcut: "g (pcut r \<omega>) = g \<omega>" for \<omega> :: "'n pairpath"
    using r by (simp add: g_def pexit_pcut pcut_apply)
  define A' where "A' = A \<inter> {\<omega> \<in> space ?BR. c \<le> g \<omega>}"
  have A's: "A' \<in> sets ?BR" unfolding A'_def using A gset by simp
  have A'A: "A' \<subseteq> A" unfolding A'_def by simp

  obtain \<kappa>' where glue: "kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P)
        \<in> exit_class k L T x"
    and onA: "\<And>p'. p' \<in> A' \<Longrightarrow> \<kappa>' p' = S (fst (p' r))"
    and Kc: "\<And>p'. \<kappa>' p' \<in> exit_class k L (T - r) (0::real^'n)"
    and offA: "\<And>\<Phi>. {\<omega> \<in> space ?BT. \<Phi> \<omega>} \<in> sets ?BT \<Longrightarrow> (AE \<omega> in P. \<Phi> \<omega>)
        \<Longrightarrow> AE \<omega> in kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P).
              pcut r \<omega> \<in> A' \<or> \<Phi> \<omega>"
    and onAae: "\<And>\<Phi>. {\<omega> \<in> space ?BT. \<Phi> \<omega>} \<in> sets ?BT
        \<Longrightarrow> (\<And>p'. p' \<in> A'
              \<Longrightarrow> p' \<in> mspace (path_metric r :: ('n pairpath) metric)
              \<Longrightarrow> AE \<omega>' in S (fst (p' r)). \<Phi> (pglue r T p' \<omega>'))
        \<Longrightarrow> AE \<omega> in kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P).
              pcut r \<omega> \<notin> A' \<or> \<Phi> \<omega>"
    by (rule exit_class_kglue_mixed[OF r rT L1 P A's Sk SC]) blast
  define R where "R = kglue_law' r T \<kappa>' (pair_law_of r (pcut r) P)"
  have RC: "R \<in> exit_class k L T x" unfolding R_def by (rule glue)

  have tauT: "(\<lambda>\<omega> :: 'n pairpath. pexit T K (\<lambda>t. fst (\<omega> t)))
      \<in> borel_measurable ?BT"
    by (rule pexit_path_measurable[OF T0' K refl])
  have pcm: "pcut r \<in> ?BT \<rightarrow>\<^sub>M ?BR" by (rule pcut_measurable[OF r rT' refl])
  have m2: "{\<omega> \<in> space ?BT. c \<le> pexit T K (\<lambda>t. fst (\<omega> t))} \<in> sets ?BT"
    using tauT by measurable
  have m1: "{\<omega> \<in> space ?BT. pcut r \<omega> \<in> A' \<or> \<Psi> \<omega>} \<in> sets ?BT"
  proof -
    have "{\<omega> \<in> space ?BT. pcut r \<omega> \<in> A' \<or> \<Psi> \<omega>}
        = (pcut r -` A' \<inter> space ?BT) \<union> {\<omega> \<in> space ?BT. \<Psi> \<omega>}" by blast
    moreover have "pcut r -` A' \<inter> space ?BT \<in> sets ?BT"
      by (rule measurable_sets[OF pcm A's])
    ultimately show ?thesis using Psm by simp
  qed

  have aeP1: "AE \<omega> in P. pcut r \<omega> \<in> A' \<or> \<Psi> \<omega>"
    using c AE_space
  proof eventually_elim
    case (elim \<omega>)
    show ?case
    proof (cases "pcut r \<omega> \<in> A")
      case True
      have "pcut r \<omega> \<in> space ?BR"
        using measurable_space[OF pcut_measurable[OF r rT'
            exit_class_sets[OF P]] elim(2)] .
      moreover have "c \<le> g (pcut r \<omega>)"
      proof -
        have "c \<le> g \<omega>" using elim(1) True unfolding g_def by simp
        then show ?thesis unfolding gcut .
      qed
      ultimately show ?thesis unfolding A'_def using True by simp
    next
      case False
      then show ?thesis using elim(1) by simp
    qed
  qed
  have off: "AE \<omega> in R. pcut r \<omega> \<in> A' \<or> \<Psi> \<omega>"
  proof -
    have "AE \<omega> in R. pcut r \<omega> \<in> A' \<or> (pcut r \<omega> \<in> A' \<or> \<Psi> \<omega>)"
      unfolding R_def by (rule offA[OF m1 aeP1])
    then show ?thesis by (auto elim: eventually_mono)
  qed

  have on: "AE \<omega> in R. pcut r \<omega> \<notin> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))"
    unfolding R_def
  proof (rule onAae[OF m2])
    fix p' :: "'n pairpath"
    assume pA: "p' \<in> A'"
    have cg: "c \<le> g p'" using pA unfolding A'_def by simp
    show "AE \<omega>' in S (fst (p' r)).
        c \<le> pexit T K (\<lambda>t. fst (pglue r T p' \<omega>' t))"
    proof (rule pexit_pglue_selector_ge[OF r rT K])
      show "S (fst (p' r)) \<in> exit_class k L (T - r) (0::real^'n)"
        by (rule SC)
      show "ess_inf_time (pshift_law (T - r) (fst (p' r)) (S (fst (p' r))))
          (\<lambda>w. pexit (T - r) K (\<lambda>t. fst (w t)))
        = exit_val k L (T - r) K (fst (p' r))" by (rule Sval)
      show "c \<le> pexit r K (\<lambda>t. fst (p' t))
          + (if pexit r K (\<lambda>t. fst (p' t)) = r \<and> fst (p' r) \<in> K
             then enn2real (exit_val k L (T - r) K (fst (p' r))) else 0)"
        using cg unfolding g_def .
    qed
  qed

  have all: "AE \<omega> in R.
      (pcut r \<omega> \<in> A \<and> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))) \<or> \<Psi> \<omega>"
  proof (rule eventually_mono[OF eventually_conj[OF off on]])
    fix \<omega> :: "'n pairpath"
    assume hh: "(pcut r \<omega> \<in> A' \<or> \<Psi> \<omega>)
        \<and> (pcut r \<omega> \<notin> A' \<or> c \<le> pexit T K (\<lambda>t. fst (\<omega> t)))"
    show "(pcut r \<omega> \<in> A \<and> c \<le> pexit T K (\<lambda>t. fst (\<omega> t))) \<or> \<Psi> \<omega>"
    proof (cases "pcut r \<omega> \<in> A'")
      case True
      then have "pcut r \<omega> \<in> A" using A'A by blast
      moreover have "c \<le> pexit T K (\<lambda>t. fst (\<omega> t))" using hh True by simp
      ultimately show ?thesis by simp
    next
      case False
      then show ?thesis using hh by simp
    qed
  qed
  show thesis by (rule that[OF RC all])
qed

subsection \<open>The chain of a simple stopping time\<close>

text \<open>A simple stopping time is a list of (time, \<open>\<F>\<^sub>t\<close>-event) pairs read in
  order: at the first \<open>t\<close> whose event fires, \<open>\<theta> = t\<close>.  \<open>dpp_chain\<close> is the
  hypothesis \<open>c \<le> integrand\<^sub>\<theta>\<close> written out along that list, exactly the
  shape @{thm [source] exit_val_dpp_ge_step} consumes: its head is the step's
  hypothesis and its tail is the step's \<open>\<Psi>\<close>.\<close>

primrec dpp_chain :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real^'n::finite) set \<Rightarrow> real
    \<Rightarrow> (real \<times> ('n pairpath) set) list \<Rightarrow> 'n pairpath \<Rightarrow> bool"
  where
    "dpp_chain k L T K c [] \<omega> = (c \<le> pexit T K (\<lambda>s. fst (\<omega> s)))"
  | "dpp_chain k L T K c (p # rs) \<omega> =
      ((pcut (fst p) \<omega> \<in> snd p \<longrightarrow> c \<le> pexit (fst p) K (\<lambda>s. fst (\<omega> s))
          + (if pexit (fst p) K (\<lambda>s. fst (\<omega> s)) = fst p \<and> fst (\<omega> (fst p)) \<in> K
             then enn2real (exit_val k L (T - fst p) K (fst (\<omega> (fst p)))) else 0))
       \<and> (pcut (fst p) \<omega> \<notin> snd p \<longrightarrow> dpp_chain k L T K c rs \<omega>))"

text \<open>The integrand at a fixed time is a random variable on the \<open>t\<close>-path
  space, and it only reads \<open>[0,t]\<close> --- the two facts the \<open>gm\<close>/\<open>gcut\<close> pair of
  @{thm [source] exit_val_dpp_ge_step} needs, pulled out so the chain's
  measurability induction can reuse them.\<close>

text \<open>The events of a stopping time are pairwise exclusive along the list:
  once one fires, none of the later ones does.  That is what stops a glue at
  \<open>t\<^sub>j\<close> from undoing an earlier glue.\<close>

primrec dpp_disj :: "(real \<times> ('n::finite pairpath) set) list \<Rightarrow> 'n pairpath \<Rightarrow> bool"
  where
    "dpp_disj [] \<omega> = True"
  | "dpp_disj (p # rs) \<omega> =
      ((pcut (fst p) \<omega> \<in> snd p \<longrightarrow> (\<forall>q \<in> set rs. pcut (fst q) \<omega> \<notin> snd q))
       \<and> dpp_disj rs \<omega>)"

text \<open>The induction: iterate @{thm [source] exit_val_dpp_ge_step} down the
  list, carrying \<open>D\<close>, the paths already glued and already good.  The
  invariant is \<open>D \<omega> \<or> dpp_chain rs \<omega>\<close>: \<open>D\<close> implies the bound, and \<open>D\<close>
  implies that none of the remaining events fires, so no later glue touches
  those paths.\<close>

subsection \<open>Splitting at a stopping time without re-clocking\<close>

text \<open>Stroock--Varadhan concatenate at a stopping time on \<open>C([0,\<infinity>))\<close> and
  never rebase the time axis: the continuation lives on the same path space
  and is spliced in place.  Transplanted to the capped space this makes the
  past/future split additive: freeze the path after \<open>\<theta>\<close>, and keep the
  increments after \<open>\<theta>\<close> as a second path that is \<open>0\<close> before \<open>\<theta>\<close>.  Both live
  on the same \<open>T\<close>-path space, so the random horizon \<open>T - \<theta>\<close> never appears
  and reassembly is addition, needing no reference to \<open>\<theta>\<close> on the far side; a
  freeze-and-rebase design would need \<open>\<theta>\<close> back and so does not work here.\<close>

definition pstopped :: "real \<Rightarrow> ('n::finite pairpath \<Rightarrow> real) \<Rightarrow> 'n pairpath
    \<Rightarrow> 'n pairpath"
  where "pstopped T \<theta> \<omega> = restrict (\<lambda>t. \<omega> (min t (\<theta> \<omega>))) {0..T}"

definition pafter :: "real \<Rightarrow> ('n::finite pairpath \<Rightarrow> real) \<Rightarrow> 'n pairpath
    \<Rightarrow> 'n pairpath"
  where "pafter T \<theta> \<omega> = restrict (\<lambda>t. \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)) {0..T}"

lemma pstopped_apply: "t \<in> {0..T} \<Longrightarrow> pstopped T \<theta> \<omega> t = \<omega> (min t (\<theta> \<omega>))"
  by (simp add: pstopped_def)

lemma pafter_apply:
  "t \<in> {0..T} \<Longrightarrow> pafter T \<theta> \<omega> t = \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>)"
  by (simp add: pafter_def)

lemma pstopped_outside: "t \<notin> {0..T} \<Longrightarrow> pstopped T \<theta> \<omega> t = undefined"
  unfolding pstopped_def restrict_def by (rule if_not_P)

lemma pafter_outside: "t \<notin> {0..T} \<Longrightarrow> pafter T \<theta> \<omega> t = undefined"
  unfolding pafter_def restrict_def by (rule if_not_P)
text \<open>The reassembly law.  This is the analogue of
  @{thm [source] pglue_pcut_pfut} at a random time, and unlike that one it
  costs nothing: no membership hypothesis on \<open>\<omega>\<close>, and no \<open>\<theta>\<close> on the
  right-hand side.\<close>

lemma pstopped_add_pafter:
  fixes \<omega> :: "'n::finite pairpath"
  assumes th0: "0 \<le> \<theta> \<omega>" and thT: "\<theta> \<omega> \<le> T" and t: "t \<in> {0..T}"
  shows "pstopped T \<theta> \<omega> t + pafter T \<theta> \<omega> t = \<omega> t"
proof (cases "t \<le> \<theta> \<omega>")
  case True
  then have m1: "min t (\<theta> \<omega>) = t" and m2: "max t (\<theta> \<omega>) = \<theta> \<omega>" by simp_all
  show ?thesis using t by (simp add: pstopped_apply pafter_apply m1 m2)
next
  case False
  then have m1: "min t (\<theta> \<omega>) = \<theta> \<omega>" and m2: "max t (\<theta> \<omega>) = t" by simp_all
  show ?thesis using t by (simp add: pstopped_apply pafter_apply m1 m2)
qed

text \<open>The future factor starts at \<open>0\<close> --- exactly the normalisation the class
  asks of a continuation --- and the two halves live on disjoint stretches of
  time.\<close>

lemma pafter_before:
  fixes \<omega> :: "'n::finite pairpath"
  assumes t: "t \<in> {0..T}" and le: "t \<le> \<theta> \<omega>"
  shows "pafter T \<theta> \<omega> t = 0"
  using t le by (simp add: pafter_apply max_absorb2)

text \<open>Evaluating a path at a random time.  This is the one new measurability
  fact the additive split needs, and it is where the paths' continuity is
  spent: approximate the time from above by dyadic rationals, each fixed
  dyadic giving a measurable evaluation among only countably many, and pass
  to the limit inside each path.  Only pointwise continuity of each path is
  used, so no uniform-continuity machinery is needed.  Compare
  @{thm [source] stopped_adapted_of_cont}, which runs the same dyadic
  argument for a real-valued adapted process and delivers the sharper
  \<open>\<F>\<^sub>v\<close>-measurability, needing the paths capped as \<open>\<omega> (min s T)\<close> because it
  asks for continuity on all of \<open>{0..}\<close>.\<close>

lemma path_eval_at_measurable_time:
  fixes M :: "'a measure" and g :: "'a \<Rightarrow> real"
    and X :: "'a \<Rightarrow> 'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and Xm: "X \<in> M \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
    and gm: "g \<in> borel_measurable M"
    and g0: "\<And>w. w \<in> space M \<Longrightarrow> 0 \<le> g w"
    and gT: "\<And>w. w \<in> space M \<Longrightarrow> g w \<le> T"
  shows "(\<lambda>w. X w (g w)) \<in> borel_measurable M"
proof -
  define gn where "gn n w = max 0 (min T (real_of_int \<lceil>2^n * g w\<rceil> / 2^n))"
    for n :: nat and w :: 'a
  have gnrange: "gn n w \<in> {0..T}" for n w using T0 by (simp add: gn_def)

  \<comment> \<open>each approximant is measurable: countably many dyadic values\<close>
  have stepm: "(\<lambda>w. X w (gn n w)) \<in> borel_measurable M" for n
  proof -
    have fj: "(\<lambda>w. X w (max 0 (min T (real_of_int j / 2^n)))) \<in> borel_measurable M"
      for j :: int
      by (rule measurable_compose[OF Xm pair_law_eval_measurable[OF refl]])
    have cj: "(\<lambda>w. \<lceil>2^n * g w\<rceil>) \<in> M \<rightarrow>\<^sub>M count_space UNIV"
      using gm by measurable
    have "(\<lambda>w. X w (max 0 (min T (real_of_int \<lceil>2^n * g w\<rceil> / 2^n))))
        \<in> borel_measurable M"
      by (rule measurable_compose_countable[OF fj cj])
    then show ?thesis unfolding gn_def .
  qed

  \<comment> \<open>and they converge, inside each path, by continuity of that path\<close>
  have conv: "(\<lambda>n. X w (gn n w)) \<longlonglongrightarrow> X w (g w)" if w: "w \<in> space M" for w
  proof -
    have cont: "continuous_on {0..T} (X w)"
    proof (rule mspace_path_metricD)
      show "X w \<in> mspace (path_metric T :: ('n pairpath) metric)"
        using measurable_space[OF Xm w] by (simp add: space_borel_of)
    qed
    have bnd: "\<bar>real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w\<bar> \<le> (1/2)^n" for n
    proof -
      have p: "(0 :: real) < 2^n" by simp
      have lo: "2^n * g w \<le> real_of_int \<lceil>2^n * g w\<rceil>" by (rule le_of_int_ceiling)
      have hi: "real_of_int \<lceil>2^n * g w\<rceil> < 2^n * g w + 1"
        using ceiling_correct[of "2^n * g w"] by simp
      have "0 \<le> real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w"
        using lo p by (simp add: field_simps)
      moreover have "real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w \<le> 1 / 2^n"
      proof -
        have "real_of_int \<lceil>2^n * g w\<rceil> \<le> 2^n * g w + 1" using hi by simp
        then have "real_of_int \<lceil>2^n * g w\<rceil> / 2^n \<le> (2^n * g w + 1) / 2^n"
          by (rule divide_right_mono) simp
        also have "\<dots> = g w + 1 / 2^n" using p by (simp add: field_simps)
        finally show ?thesis by simp
      qed      ultimately show ?thesis by (simp add: power_one_over)
    qed
    have "(\<lambda>n. real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w) \<longlonglongrightarrow> 0"
    proof (rule Lim_null_comparison)
      show "\<forall>\<^sub>F n in sequentially.
          norm (real_of_int \<lceil>2^n * g w\<rceil> / 2^n - g w) \<le> (1/2)^n"
        using bnd by simp
      show "(\<lambda>n. ((1 :: real)/2)^n) \<longlonglongrightarrow> 0"
        by (rule LIMSEQ_realpow_zero) simp_all
    qed
    then have "(\<lambda>n. real_of_int \<lceil>2^n * g w\<rceil> / 2^n) \<longlonglongrightarrow> g w"
      by (rule Lim_transform[OF tendsto_const])
    then have "(\<lambda>n. gn n w) \<longlonglongrightarrow> max 0 (min T (g w))"
      unfolding gn_def by (intro tendsto_max tendsto_min tendsto_const)
    then have gconv: "(\<lambda>n. gn n w) \<longlonglongrightarrow> g w"
      using g0[OF w] gT[OF w] by simp
    show ?thesis
    proof (rule continuous_on_tendsto_compose[OF cont gconv])
      show "\<forall>\<^sub>F n in sequentially. gn n w \<in> {0..T}" using gnrange by simp
      show "g w \<in> {0..T}" using g0[OF w] gT[OF w] by simp
    qed
  qed
  show ?thesis by (rule borel_measurable_LIMSEQ_metric[OF stepm conv])
qed

text \<open>Both halves of the split are again capped paths.  Freezing and
  rebasing preserve continuity, and @{thm [source] mspace_path_metricI} does
  the extensionality --- both maps are \<open>restrict\<close>ed by construction.\<close>

lemma pstopped_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes th0: "0 \<le> \<theta> \<omega>" and thT: "\<theta> \<omega> \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pstopped T \<theta> \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. min t (\<theta> \<omega>))" by (intro continuous_intros)
  have im: "(\<lambda>t. min t (\<theta> \<omega>)) ` {0..T} \<subseteq> {0..T}" using th0 thT by auto
  have "continuous_on {0..T} (\<lambda>t. \<omega> (min t (\<theta> \<omega>)))"
    by (rule continuous_on_compose2[OF c m im])
  then show ?thesis unfolding pstopped_def by (rule mspace_path_metricI)
qed

lemma pafter_mspace:
  fixes \<omega> :: "'n::finite pairpath"
  assumes th0: "0 \<le> \<theta> \<omega>" and thT: "\<theta> \<omega> \<le> T"
    and w: "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "pafter T \<theta> \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} \<omega>" by (rule mspace_path_metricD[OF w])
  have m: "continuous_on {0..T} (\<lambda>t. max t (\<theta> \<omega>))" by (intro continuous_intros)
  have im: "(\<lambda>t. max t (\<theta> \<omega>)) ` {0..T} \<subseteq> {0..T}" using th0 thT by auto
  have "continuous_on {0..T} (\<lambda>t. \<omega> (max t (\<theta> \<omega>)))"
    by (rule continuous_on_compose2[OF c m im])
  then have "continuous_on {0..T} (\<lambda>t. \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>))"
    by (intro continuous_intros)
  then show ?thesis unfolding pafter_def by (rule mspace_path_metricI)
qed

text \<open>A criterion for landing in the path space.  The balls are a base, so
  Borel measurability into \<open>?B\<^sub>T\<close> reduces to measurability of the distance to
  each point, which the additive split can supply, since the distance is a
  sup over time of evaluations and @{thm [source] path_eval_at_measurable_time}
  makes each evaluation measurable.  The generator route through
  @{thm [source] sets_natural_filtration_path} would work too, but needs no
  handle on \<open>natural_filtration\<close>'s generators.\<close>

lemma measurable_into_path_metric:
  fixes f :: "'a \<Rightarrow> 'n::finite pairpath"
  assumes into: "\<And>w. w \<in> space M
      \<Longrightarrow> f w \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and dm: "\<And>a. a \<in> mspace (path_metric T :: ('n pairpath) metric)
      \<Longrightarrow> (\<lambda>w. mdist (path_metric T :: ('n pairpath) metric) (f w) a)
          \<in> borel_measurable M"
  shows "f \<in> M \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  let ?m = "path_metric T :: ('n pairpath) metric"
  let ?B = "borel_of (mtopology_of ?m)"
  interpret MS: Metric_space "mspace ?m" "mdist ?m"
    by (rule Metric_space_mspace_mdist)
  let ?balls = "{MS.mball a \<epsilon> | a \<epsilon>. a \<in> mspace ?m \<and> \<epsilon> > 0}"
  have sub: "?balls \<subseteq> Pow (mspace ?m)" using MS.mball_subset_mspace by auto
  have base: "base_in (mtopology_of ?m) ?balls"
    using MS.mtopology_base_in_balls by (simp add: mtopology_of_def)
  have "?B = sigma (topspace (mtopology_of ?m)) ?balls"
    by (rule borel_of_second_countable'
        [OF second_countable_path_metric base_is_subbase[OF base]])
  then have setsB: "sets ?B = sigma_sets (mspace ?m) ?balls"
    using sets_measure_of[OF sub] by simp
  show ?thesis
  proof (rule measurable_sigma_sets[OF setsB sub])
    show "f \<in> space M \<rightarrow> mspace ?m" using into by blast
  next
    fix A assume "A \<in> ?balls"
    then obtain a e where A: "A = MS.mball a e" and am: "a \<in> mspace ?m"
      and epos: "e > 0" by blast
    have ball: "(\<omega> \<in> MS.mball a e) = (\<omega> \<in> mspace ?m \<and> mdist ?m \<omega> a < e)"
      for \<omega> :: "'n pairpath"
      using am by (simp only: MS.in_mball MS.commute conj_commute simp_thms)
    have "f -` A \<inter> space M = {w \<in> space M. mdist ?m (f w) a < e}"
      unfolding A using into by (auto simp only: ball vimage_eq Int_iff)    then show "f -` A \<inter> space M \<in> sets M" using dm[OF am] by simp
  qed
qed

text \<open>Hypothesis (ii) of the criterion: the distance to a fixed path is a
  sup of evaluations over the rationals (@{thm [source] path_mdist_le_iff}),
  hence a countable intersection.\<close>

lemma mdist_measurable_of_eval:
  fixes f :: "'a \<Rightarrow> 'n::finite pairpath"
  assumes T0: "0 \<le> T"
    and into: "\<And>w. w \<in> space M
      \<Longrightarrow> f w \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    and ev: "\<And>t. (\<lambda>w. f w t) \<in> borel_measurable M"
  shows "(\<lambda>w. mdist (path_metric T :: ('n pairpath) metric) (f w) a)
      \<in> borel_measurable M"
proof (rule borel_measurable_iff_le[THEN iffD2], intro allI)
  fix q :: real
  have cnt: "countable ({0..T} \<inter> \<rat>)" by (simp add: countable_rat)
  have ne: "{0..T} \<inter> \<rat> \<noteq> {}" using T0 by auto
  have eq: "{w \<in> space M. mdist (path_metric T :: ('n pairpath) metric) (f w) a \<le> q}
      = (\<Inter>t \<in> {0..T} \<inter> \<rat>. {w \<in> space M. dist (f w t) (a t) \<le> q})"
    using ne by (auto simp: path_mdist_le_iff[OF T0 into am])
  have inner: "{w \<in> space M. dist (f w t) (a t) \<le> q} \<in> sets M" for t
    using ev[of t] by measurable
  show "{w \<in> space M. mdist (path_metric T :: ('n pairpath) metric) (f w) a \<le> q}
      \<in> sets M"
    unfolding eq by (intro sets.countable_INT'[OF cnt ne]) (auto simp: inner)qed

text \<open>Hence both halves of the split are measurable maps of the path.  Only
  Borel measurability of \<open>\<theta>\<close> is used here; the stopping-time property is
  what makes the kernel a function of the past, entering later through
  @{thm [source] stopped_adapted_of_cont}.\<close>

lemma pstopped_measurable:
  fixes \<theta> :: "'n::finite pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and thm': "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "pstopped T \<theta> \<in> (path_borel T :: ('n pairpath) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have sp: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have into: "pstopped T \<theta> \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    if "\<omega> \<in> space ?B" for \<omega>
    using that sp by (intro pstopped_mspace[OF th0 thT]) simp
  have ev: "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> t) \<in> borel_measurable ?B" for t
  proof (cases "t \<in> {0..T}")
    case True
    have base: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (min t (\<theta> \<omega>))) \<in> borel_measurable ?B"
    proof (rule path_eval_at_measurable_time
        [where X = "\<lambda>\<omega> :: 'n pairpath. \<omega>" and g = "\<lambda>\<omega>. min t (\<theta> \<omega>)", OF T0])
      show "(\<lambda>\<omega> :: 'n pairpath. \<omega>) \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule measurable_ident_sets[OF refl])
      show "(\<lambda>\<omega> :: 'n pairpath. min t (\<theta> \<omega>)) \<in> borel_measurable ?B"
        using thm' by measurable
      show "0 \<le> min t (\<theta> \<omega>)" for \<omega> :: "'n pairpath"
        using True th0[of \<omega>] by simp
      show "min t (\<theta> \<omega>) \<le> T" for \<omega> :: "'n pairpath"
        using thT[of \<omega>] by simp
    qed
    have "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> t)
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> (min t (\<theta> \<omega>)))"
      by (rule ext) (rule pstopped_apply[OF True])
    then show ?thesis using base by simp
  next
    case False
    have "(\<lambda>\<omega> :: 'n pairpath. pstopped T \<theta> \<omega> t) = (\<lambda>\<omega>. undefined)"
      by (rule ext) (rule pstopped_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>\<omega>. mdist (path_metric T :: ('n pairpath) metric)
        (pstopped T \<theta> \<omega>) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed

lemma pafter_measurable:
  fixes \<theta> :: "'n::finite pairpath \<Rightarrow> real"
  assumes T0: "0 \<le> T"
    and thm': "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and th0: "\<And>\<omega>. 0 \<le> \<theta> \<omega>" and thT: "\<And>\<omega>. \<theta> \<omega> \<le> T"
  shows "pafter T \<theta> \<in> (path_borel T :: ('n pairpath) measure)
      \<rightarrow>\<^sub>M (path_borel T :: ('n pairpath) measure)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have sp: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have into: "pafter T \<theta> \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    if "\<omega> \<in> space ?B" for \<omega>
    using that sp by (intro pafter_mspace[OF th0 thT]) simp
  have base0: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (\<theta> \<omega>)) \<in> borel_measurable ?B"
  proof (rule path_eval_at_measurable_time
      [where X = "\<lambda>\<omega> :: 'n pairpath. \<omega>" and g = \<theta>, OF T0])
    show "(\<lambda>\<omega> :: 'n pairpath. \<omega>) \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule measurable_ident_sets[OF refl])
    show "\<theta> \<in> borel_measurable ?B" by (rule thm')
    show "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath" by (rule th0)
    show "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath" by (rule thT)
  qed
  have ev: "(\<lambda>\<omega> :: 'n pairpath. pafter T \<theta> \<omega> t) \<in> borel_measurable ?B" for t
  proof (cases "t \<in> {0..T}")
    case True
    have base: "(\<lambda>\<omega> :: 'n pairpath. \<omega> (max t (\<theta> \<omega>))) \<in> borel_measurable ?B"
    proof (rule path_eval_at_measurable_time
        [where X = "\<lambda>\<omega> :: 'n pairpath. \<omega>" and g = "\<lambda>\<omega>. max t (\<theta> \<omega>)", OF T0])
      show "(\<lambda>\<omega> :: 'n pairpath. \<omega>) \<in> ?B \<rightarrow>\<^sub>M ?B" by (rule measurable_ident_sets[OF refl])
      show "(\<lambda>\<omega> :: 'n pairpath. max t (\<theta> \<omega>)) \<in> borel_measurable ?B"
        using thm' by measurable
      show "0 \<le> max t (\<theta> \<omega>)" for \<omega> :: "'n pairpath"
        using th0[of \<omega>] by simp
      show "max t (\<theta> \<omega>) \<le> T" for \<omega> :: "'n pairpath"
        using True thT[of \<omega>] by simp
    qed
    have "(\<lambda>\<omega> :: 'n pairpath. pafter T \<theta> \<omega> t)
        = (\<lambda>\<omega> :: 'n pairpath. \<omega> (max t (\<theta> \<omega>)) - \<omega> (\<theta> \<omega>))"
      by (rule ext) (rule pafter_apply[OF True])
    then show ?thesis using base base0 by simp
  next
    case False
    have "(\<lambda>\<omega> :: 'n pairpath. pafter T \<theta> \<omega> t) = (\<lambda>\<omega>. undefined)"
      by (rule ext) (rule pafter_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric T :: ('n pairpath) metric)"
    show "(\<lambda>\<omega>. mdist (path_metric T :: ('n pairpath) metric)
        (pafter T \<theta> \<omega>) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF T0 into am ev])
  qed
qed
subsection \<open>The regular conditional distribution, with both maps and horizons free\<close>

text \<open>@{thm [source] exit_class_rcd} and
  @{thm [source] exit_class_rcd_ksemi} use \<open>pcut r\<close> and \<open>pfut r T\<close> only
  through their measurability, so nothing in either proof is specific to the
  deterministic split.  Here they are with the two maps and the two horizons
  free; the deterministic case is the instance \<open>u := r\<close>, \<open>v := T - r\<close>, and
  the stopping-time case is \<open>u := v := T\<close>, \<open>\<phi>\<^sub>1 := pstopped T \<theta>\<close>,
  \<open>\<phi>\<^sub>2 := pafter T \<theta>\<close>.\<close>

theorem path_rcd:
  fixes P :: "('n::finite pairpath) measure"
  assumes v: "0 \<le> v" and PS: "prob_space P"
    and m1: "\<phi>1 \<in> P \<rightarrow>\<^sub>M (path_borel u :: ('n pairpath) measure)"
    and m2: "\<phi>2 \<in> P \<rightarrow>\<^sub>M (path_borel v :: ('n pairpath) measure)"
  obtains \<kappa> where
    "\<kappa> \<in> (path_borel u :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel v :: ('n pairpath) measure)"
    and "\<And>A B. A \<in> sets (path_borel u :: ('n pairpath) measure)
        \<Longrightarrow> B \<in> sets (path_borel v :: ('n pairpath) measure)
        \<Longrightarrow> emeasure (distr P
              ((path_borel u :: ('n pairpath) measure)
                \<Otimes>\<^sub>M (path_borel v :: ('n pairpath) measure))
              (\<lambda>\<omega>. (\<phi>1 \<omega>, \<phi>2 \<omega>))) (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of u \<phi>1 P))"
proof -
  let ?X = "(path_borel u :: ('n pairpath) measure)"
  let ?Y = "(path_borel v :: ('n pairpath) measure)"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (\<phi>1 \<omega>, \<phi>2 \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  interpret PP: prob_space P by (rule PS)
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using m1 m2 by simp
  have setsnu: "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by simp

  have marg: "marginal_measure ?X ?Y ?\<nu> = pair_law_of u \<phi>1 P"
  proof (rule measure_eqI)
    show "sets (marginal_measure ?X ?Y ?\<nu>) = sets (pair_law_of u \<phi>1 P)"
      by (simp add: sets_marginal_measure)
    fix A assume "A \<in> sets (marginal_measure ?X ?Y ?\<nu>)"
    then have AX: "A \<in> sets ?X" by (simp add: sets_marginal_measure)
    have rect: "A \<times> space ?Y \<in> sets (?X \<Otimes>\<^sub>M ?Y)" using AX by simp
    have "emeasure (marginal_measure ?X ?Y ?\<nu>) A = emeasure ?\<nu> (A \<times> space ?Y)"
      by (rule emeasure_marginal_measure[OF setsnu AX])
    also have "\<dots> = emeasure P (?\<phi> -` (A \<times> space ?Y) \<inter> space P)"
      by (rule emeasure_distr[OF mphi rect])
    also have "\<dots> = emeasure P (\<phi>1 -` A \<inter> space P)"
    proof -
      have "?\<phi> -` (A \<times> space ?Y) \<inter> space P = \<phi>1 -` A \<inter> space P"
        using measurable_space[OF m2] by auto
      then show ?thesis by simp
    qed
    also have "\<dots> = emeasure (pair_law_of u \<phi>1 P) A"
      unfolding pair_law_of_def by (rule emeasure_distr[OF m1 AX, symmetric])
    finally show "emeasure (marginal_measure ?X ?Y ?\<nu>) A
        = emeasure (pair_law_of u \<phi>1 P) A" .
  qed

  have PSF: "projection_sigma_finite ?X ?Y ?\<nu>"
    unfolding projection_sigma_finite_def
  proof (intro conjI)
    show "sets ?\<nu> = sets (?X \<Otimes>\<^sub>M ?Y)" by (rule setsnu)
    have "prob_space (pair_law_of u \<phi>1 P)"
      unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
    then show "sigma_finite_measure (marginal_measure ?X ?Y ?\<nu>)"
      unfolding marg by (rule prob_space_imp_sigma_finite)
  qed
  have SB: "standard_borel_ne ?Y" by (rule standard_borel_ne_path_metric[OF v])
  interpret D: projection_sigma_finite_standard ?X ?Y ?\<nu>
    unfolding projection_sigma_finite_standard_def using PSF SB by blast

  obtain \<kappa> where K: "prob_kernel ?X ?Y \<kappa>"
    and DIS: "measure_kernel.disintegration ?X ?Y \<kappa> ?\<nu>
        (marginal_measure ?X ?Y ?\<nu>)"
    using D.measure_disintegration by blast
  interpret MK: measure_kernel ?X ?Y \<kappa> using K by (simp add: prob_kernel_def)
  have Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y" using K by (simp add: prob_kernel_def')

  show ?thesis
  proof (rule that)
    show "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y" by (rule Km)
    show "emeasure ?\<nu> (A \<times> B)
        = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(pair_law_of u \<phi>1 P))"
      if A: "A \<in> sets ?X" and B: "B \<in> sets ?Y" for A B
    proof -
      have "emeasure ?\<nu> (A \<times> B)
          = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>(marginal_measure ?X ?Y ?\<nu>))"
        using DIS A B unfolding MK.disintegration_def by blast
      then show ?thesis unfolding marg .
    qed
  qed
qed

theorem path_rcd_ksemi:
  fixes P :: "('n::finite pairpath) measure"
  assumes v: "0 \<le> v" and PS: "prob_space P"
    and m1: "\<phi>1 \<in> P \<rightarrow>\<^sub>M (path_borel u :: ('n pairpath) measure)"
    and m2: "\<phi>2 \<in> P \<rightarrow>\<^sub>M (path_borel v :: ('n pairpath) measure)"
  obtains \<kappa> where
    "\<kappa> \<in> (path_borel u :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel v :: ('n pairpath) measure)"
    and "distr P
          ((path_borel u :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel v :: ('n pairpath) measure))
          (\<lambda>\<omega>. (\<phi>1 \<omega>, \<phi>2 \<omega>))
        = ksemi (pair_law_of u \<phi>1 P)
            (path_borel v :: ('n pairpath) measure) \<kappa>"
proof -
  let ?X = "(path_borel u :: ('n pairpath) measure)"
  let ?Y = "(path_borel v :: ('n pairpath) measure)"
  let ?\<phi> = "\<lambda>\<omega> :: 'n pairpath. (\<phi>1 \<omega>, \<phi>2 \<omega>)"
  let ?\<nu> = "distr P (?X \<Otimes>\<^sub>M ?Y) ?\<phi>"
  let ?Q = "pair_law_of u \<phi>1 P"
  let ?E = "{a \<times> b | a b. a \<in> sets ?X \<and> b \<in> sets ?Y}"
  interpret PP: prob_space P by (rule PS)
  have mphi: "?\<phi> \<in> P \<rightarrow>\<^sub>M ?X \<Otimes>\<^sub>M ?Y" using m1 m2 by simp
  interpret Pnu: prob_space ?\<nu> by (rule PP.prob_space_distr[OF mphi])
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
  have setsQ: "sets ?Q = sets ?X" by (rule sets_pair_law_of)
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  obtain \<kappa> where Km: "\<kappa> \<in> ?X \<rightarrow>\<^sub>M prob_algebra ?Y"
    and REC: "\<And>A B. A \<in> sets ?X \<Longrightarrow> B \<in> sets ?Y \<Longrightarrow>
        emeasure ?\<nu> (A \<times> B) = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
    by (rule path_rcd[OF v PS m1 m2]) blast
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?Y"
    using Km measurable_cong_sets[OF setsQ refl] by blast
  have setsS: "sets (ksemi ?Q ?Y \<kappa>) = sets (?X \<Otimes>\<^sub>M ?Y)"
  proof -
    have "sets (ksemi ?Q ?Y \<kappa>) = sets (?Q \<Otimes>\<^sub>M ?Y)" by (rule sets_ksemi[OF KQ neQ])
    also have "\<dots> = sets (?X \<Otimes>\<^sub>M ?Y)"
      by (rule sets_pair_measure_cong[OF setsQ refl])
    finally show ?thesis .
  qed
  have eq: "?\<nu> = ksemi ?Q ?Y \<kappa>"
  proof (rule measure_eqI_generator_eq
      [where E = ?E and \<Omega> = "space ?X \<times> space ?Y"
         and A = "\<lambda>_. space ?X \<times> space ?Y"])
    show "Int_stable ?E" by (rule Int_stable_pair_measure_generator)
    show "?E \<subseteq> Pow (space ?X \<times> space ?Y)" using sets.sets_into_space by auto
    show "emeasure ?\<nu> C = emeasure (ksemi ?Q ?Y \<kappa>) C" if C: "C \<in> ?E" for C
    proof -
      from C obtain A B where AB: "A \<in> sets ?X" "B \<in> sets ?Y" "C = A \<times> B"
        by blast
      have AQ: "A \<in> sets ?Q" using AB(1) setsQ by simp
      have "emeasure ?\<nu> C = (\<integral>\<^sup>+p\<in>A. emeasure (\<kappa> p) B \<partial>?Q)"
        unfolding AB(3) by (rule REC[OF AB(1) AB(2)])
      also have "\<dots> = emeasure (ksemi ?Q ?Y \<kappa>) C"
        unfolding AB(3)
        by (rule emeasure_ksemi_rect[OF KQ neQ AQ AB(2), symmetric])
      finally show ?thesis .
    qed
    show "sets ?\<nu> = sigma_sets (space ?X \<times> space ?Y) ?E"
      by (simp add: sets_pair_measure)
    show "sets (ksemi ?Q ?Y \<kappa>) = sigma_sets (space ?X \<times> space ?Y) ?E"
      unfolding setsS by (simp add: sets_pair_measure)
    show "range (\<lambda>_. space ?X \<times> space ?Y) \<subseteq> ?E" by auto
    show "(\<Union>i :: nat. space ?X \<times> space ?Y) = space ?X \<times> space ?Y" by simp
    show "emeasure ?\<nu> (space ?X \<times> space ?Y) \<noteq> \<infinity>" for i :: nat
      by (simp add: Pnu.emeasure_eq_measure)
  qed
  show ?thesis by (rule that[OF Km eq])
qed

text \<open>The conditional law of the increments after \<open>\<theta>\<close> given the path stopped
  at \<open>\<theta>\<close>.  Both factors live on the same \<open>T\<close>-path space, so this is
  @{thm [source] path_rcd_ksemi} at \<open>u = v = T\<close>.\<close>

subsection \<open>Identifying the class the conditional law lives in\<close>

text \<open>\<open>pafter T \<theta> \<omega>\<close> is frozen on \<open>[0,\<theta>]\<close>, so it is not a member of
  \<open>exit_class k L T 0\<close>: the covariation constraint fails while the
  path stands still.  It is instead the delayed embedding of the ordinary
  rebased future \<open>pfut \<theta> T \<omega>\<close>, padded with \<open>0\<close> on \<open>[0,\<theta>]\<close> and running the
  future after that; the class statement for the kernel is thus a statement
  about \<open>prebase \<theta> T \<circ> pafter T \<theta>\<close>, exactly what @{thm [source]
  exit_class_rcd_member} says about the law of \<open>pfut r T\<close>.  The random
  horizon \<open>T - \<theta>\<close> is harmless: inside an almost-sure statement over the
  past, \<open>\<theta>\<close> is a fixed number, and the kernel's codomain stays a fixed space
  by keeping \<open>pafter\<close> on the \<open>T\<close>-space.\<close>

definition pembed :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "pembed s T w = restrict (\<lambda>t. w (max (t - s) 0)) {0..T}"

definition prebase :: "real \<Rightarrow> real \<Rightarrow> 'n::finite pairpath \<Rightarrow> 'n pairpath"
  where "prebase s T w = restrict (\<lambda>u. w (s + u)) {0..T - s}"

lemma pembed_apply: "t \<in> {0..T} \<Longrightarrow> pembed s T w t = w (max (t - s) 0)"
  by (simp add: pembed_def)

lemma prebase_apply: "u \<in> {0..T - s} \<Longrightarrow> prebase s T w u = w (s + u)"
  by (simp add: prebase_def)

lemma pembed_outside: "t \<notin> {0..T} \<Longrightarrow> pembed s T w t = undefined"
  unfolding pembed_def restrict_def by (rule if_not_P)

lemma prebase_outside: "u \<notin> {0..T - s} \<Longrightarrow> prebase s T w u = undefined"
  unfolding prebase_def restrict_def by (rule if_not_P)

text \<open>The two bridges: \<open>pafter\<close> is the delayed future, and the future is
  recovered from it by re-basing, so nothing is lost either way.\<close>

subsection \<open>Where the stopping-time property enters\<close>

text \<open>Everything so far used only Borel measurability of \<open>\<theta>\<close>.  From here on
  \<open>\<theta>\<close> must be a genuine stopping time, which on path space says exactly one
  thing: \<open>\<theta>\<close> is decided by the path up to \<open>\<theta>\<close>.  Two paths agreeing on
  \<open>[0, \<theta> \<omega>]\<close> get the same value, which is what makes \<open>\<theta>\<close> a function of the
  stopped path, and hence makes the kernel a function of the past.\<close>

definition path_stopping_time :: "real \<Rightarrow> ('n::finite pairpath \<Rightarrow> real) \<Rightarrow> bool"
  where "path_stopping_time T \<theta> \<longleftrightarrow>
     (\<forall>\<omega>. 0 \<le> \<theta> \<omega> \<and> \<theta> \<omega> \<le> T)
     \<and> (\<forall>\<omega> \<omega>'. continuous_on {0..T} (\<lambda>t. fst (\<omega> t)) \<longrightarrow>
          continuous_on {0..T} (\<lambda>t. fst (\<omega>' t)) \<longrightarrow>
          (\<forall>t \<in> {0..\<theta> \<omega>}. \<omega> t = \<omega>' t) \<longrightarrow> \<theta> \<omega>' = \<theta> \<omega>)"

lemma path_stopping_time_nonneg:
  "path_stopping_time T \<theta> \<Longrightarrow> 0 \<le> \<theta> \<omega>"
  unfolding path_stopping_time_def by blast

lemma path_stopping_time_le:
  "path_stopping_time T \<theta> \<Longrightarrow> \<theta> \<omega> \<le> T"
  unfolding path_stopping_time_def by blast

text \<open>Continuity is available wherever it is needed: the space of a path law
  is the set of continuous paths.\<close>

lemma path_sets_fst_continuous:
  fixes N :: "('n::finite pairpath) measure"
  assumes setsN: "sets N = sets (path_borel T :: ('n pairpath) measure)"
    and w: "\<omega> \<in> space N"
  shows "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
proof -
  have "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
    using w space_of_path_sets[OF setsN] by simp
  then have "continuous_on {0..T} \<omega>" by (rule mspace_path_metric_continuous)
  then show ?thesis by (rule continuous_on_fst)
qed

lemma path_stopping_time_cong:
  "path_stopping_time T \<theta> \<Longrightarrow> continuous_on {0..T} (\<lambda>t. fst (\<omega> t))
    \<Longrightarrow> continuous_on {0..T} (\<lambda>t. fst (\<omega>' t))
    \<Longrightarrow> (\<And>t. t \<in> {0..\<theta> \<omega>} \<Longrightarrow> \<omega> t = \<omega>' t)
    \<Longrightarrow> \<theta> \<omega>' = \<theta> \<omega>"
  unfolding path_stopping_time_def by blast

text \<open>Hence \<open>\<theta>\<close> reads only the stopped path --- the fact every later step
  needs, and the reason the kernel can be indexed by \<open>pstopped T \<theta> \<omega>\<close>
  alone.\<close>

lemma pstopped_fst_continuous:
  fixes \<omega> :: "'n::finite pairpath"
  assumes cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
    and th0: "0 \<le> \<theta>' \<omega>" and thT: "\<theta>' \<omega> \<le> T"
  shows "continuous_on {0..T} (\<lambda>s. fst (pstopped T \<theta>' \<omega> s))"
proof -
  have e: "fst (pstopped T \<theta>' \<omega> s) = fst (\<omega> (min s (\<theta>' \<omega>)))"
    if "s \<in> {0..T}" for s by (simp add: pstopped_apply[OF that])
  have c1: "continuous_on {0..T} (\<lambda>s :: real. min s (\<theta>' \<omega>))"
    by (intro continuous_intros)
  have "continuous_on {0..T} (\<lambda>s. fst (\<omega> (min s (\<theta>' \<omega>))))"
    by (rule continuous_on_compose2[OF cw c1]) (use th0 thT in auto)
  then show ?thesis by (rule continuous_on_eq) (simp add: e)
qed

lemma path_stopping_time_stopped:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "path_stopping_time T \<theta>"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "\<theta> (pstopped T \<theta> \<omega>) = \<theta> \<omega>"
proof (rule path_stopping_time_cong[OF st cw
      pstopped_fst_continuous[OF cw path_stopping_time_nonneg[OF st]
        path_stopping_time_le[OF st]]])
  fix t assume t: "t \<in> {0..\<theta> \<omega>}"
  then have tT: "t \<in> {0..T}" using path_stopping_time_le[OF st, of \<omega>] by auto
  have "min t (\<theta> \<omega>) = t" using t by simp
  then show "\<omega> t = pstopped T \<theta> \<omega> t" by (simp add: pstopped_apply[OF tT])
qed

lemma pstopped_idem:
  fixes \<omega> :: "'n::finite pairpath"
  assumes st: "path_stopping_time T \<theta>"
    and cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
  shows "pstopped T \<theta> (pstopped T \<theta> \<omega>) = pstopped T \<theta> \<omega>"
proof (rule ext)
  fix t :: real
  show "pstopped T \<theta> (pstopped T \<theta> \<omega>) t = pstopped T \<theta> \<omega> t"
  proof (cases "t \<in> {0..T}")
    case True
    have th: "\<theta> (pstopped T \<theta> \<omega>) = \<theta> \<omega>"
      by (rule path_stopping_time_stopped[OF st cw])
    have m: "min t (\<theta> \<omega>) \<in> {0..T}"
      using True path_stopping_time_nonneg[OF st, of \<omega>] by auto
    have "pstopped T \<theta> (pstopped T \<theta> \<omega>) t
        = pstopped T \<theta> \<omega> (min t (\<theta> \<omega>))"
      unfolding pstopped_apply[OF True] th ..
    also have "\<dots> = \<omega> (min (min t (\<theta> \<omega>)) (\<theta> \<omega>))" by (rule pstopped_apply[OF m])
    also have "min (min t (\<theta> \<omega>)) (\<theta> \<omega>) = min t (\<theta> \<omega>)" by simp
    finally show ?thesis by (simp add: pstopped_apply[OF True])
  next
    case False
    then show ?thesis by (simp add: pstopped_outside)
  qed
qed

text \<open>And the future factor of a stopped path is trivial: stopping twice
  leaves nothing after \<open>\<theta>\<close>.  This is the pathwise seed of clause (ii) for
  the kernel --- the continuation starts at \<open>0\<close>.\<close>

text \<open>The re-basing map at a fixed time is an ordinary path-space map, and
  that is all clause (i) of the kernel statement needs, since \<open>\<theta> \<omega>\<close> is a
  fixed number inside an almost-sure statement.\<close>

lemma prebase_mspace:
  fixes w :: "'n::finite pairpath"
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
    and w: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
  shows "prebase s T w \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
proof -
  have c: "continuous_on {0..T} w" by (rule mspace_path_metricD[OF w])
  have "continuous_on {0..T - s} (\<lambda>u. w (s + u))"
  proof (rule continuous_on_compose2[OF c])
    show "continuous_on {0..T - s} (\<lambda>u :: real. s + u)" by (intro continuous_intros)
    show "(\<lambda>u :: real. s + u) ` {0..T - s} \<subseteq> {0..T}" using s0 by auto
  qed
  then show ?thesis unfolding prebase_def by (rule mspace_path_metricI)
qed

lemma prebase_measurable:
  assumes s0: "0 \<le> s" and sT: "s \<le> T"
  shows "prebase s T \<in> (path_borel T :: ('n::finite pairpath) measure)
    \<rightarrow>\<^sub>M (path_borel (T - s) :: ('n pairpath) measure)"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  have sp: "space ?B = mspace (path_metric T :: ('n pairpath) metric)"
    by (simp add: space_borel_of)
  have Ts: "0 \<le> T - s" using sT by simp
  have into: "prebase s T w \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
    if "w \<in> space ?B" for w :: "'n pairpath"
  proof -
    have m: "w \<in> mspace (path_metric T :: ('n pairpath) metric)"
      using that sp by simp
    show ?thesis by (rule prebase_mspace[OF s0 sT m])
  qed
  have ev: "(\<lambda>w :: 'n pairpath. prebase s T w u) \<in> borel_measurable ?B" for u
  proof (cases "u \<in> {0..T - s}")
    case True
    have "(\<lambda>w :: 'n pairpath. w (s + u)) \<in> borel_measurable ?B"
      by (rule pair_law_eval_measurable[OF refl])
    then show ?thesis by (simp add: prebase_apply[OF True])
  next
    case False
    have "(\<lambda>w :: 'n pairpath. prebase s T w u) = (\<lambda>w :: 'n pairpath. undefined)"
      by (rule ext) (rule prebase_outside[OF False])
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule measurable_into_path_metric[OF into])
    fix a :: "'n pairpath"
    assume am: "a \<in> mspace (path_metric (T - s) :: ('n pairpath) metric)"
    show "(\<lambda>w. mdist (path_metric (T - s) :: ('n pairpath) metric)
        (prebase s T w) a) \<in> borel_measurable ?B"
      by (rule mdist_measurable_of_eval[OF Ts into am ev])
  qed
qed
text \<open>Hence clause (i) for the kernel: re-based, the conditional law is a
  probability measure on the \<open>(T - \<theta>)\<close>-path space.\<close>

text \<open>Clause (ii) for the kernel.  The pathwise content is already there:
  @{thm [source] pafter_before} at \<open>t = \<theta> \<omega>\<close> says the future factor is still
  \<open>0\<close> when the clock starts, so all that is needed is to push it through the
  r.c.d., the same chain as the mixed glue's transfer:
  @{thm [source] AE_distr_iff} into the joint law, the r.c.d. equation, and
  @{thm [source] AE_ksemi} back out.  The stopping-time property is spent
  where the kernel is indexed by the stopped path: the clock has to be read
  off that, and @{thm [source] path_stopping_time_stopped} says it is the
  same number.\<close>

text \<open>Clause (iii) at one pair of times.  This is the analogue of the \<open>one\<close>
  step inside @{thm [source] pfut_rcd_diffquot}, and the pathwise content is
  free: after \<open>\<theta>\<close> the future factor's increments are \<open>\<omega>\<close>'s increments,
  because the \<open>- \<omega> (\<theta> \<omega>)\<close> cancels in the difference.  The guard
  \<open>\<theta> p' \<le> p\<close> lives inside the predicate, which makes the conditioning set a
  pair-set, so the transfer is the @{thm [source] AE_ksemi} chain of clause
  (ii) rather than @{thm [source] AE_kernel_full}, and the rational grid
  stays in the original time scale.\<close>

lemma AE_rcd_stopping_diffquot_at:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PS: "prob_space P"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Km: "\<kappa> \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and eq: "distr P
          ((path_borel T :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel T :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>))
        = ksemi (pair_law_of T (pstopped T \<theta>) P)
            (path_borel T :: ('n pairpath) measure) \<kappa>"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
    and p: "p \<in> {0..T}" and q: "q \<in> {0..T}" and pq: "p < q"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P. AE w in \<kappa> p'.
      \<theta> p' \<le> p \<longrightarrow>
        (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
proof -
  let ?B = "(path_borel T :: ('n pairpath) measure)"
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  interpret PP: prob_space P by (rule PS)
  have th0: "0 \<le> \<theta> \<omega>" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_nonneg[OF st])
  have thT: "\<theta> \<omega> \<le> T" for \<omega> :: "'n pairpath"
    by (rule path_stopping_time_le[OF st])
  have m1: "pstopped T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pstopped_measurable[OF T0 thM th0 thT])
  have m2: "pafter T \<theta> \<in> P \<rightarrow>\<^sub>M ?B"
    unfolding measurable_cong_sets[OF setsP refl]
    by (rule pafter_measurable[OF T0 thM th0 thT])
  have mphi: "(\<lambda>\<omega> :: 'n pairpath. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>))
      \<in> P \<rightarrow>\<^sub>M ?B \<Otimes>\<^sub>M ?B" using m1 m2 by simp
  have setsQ: "sets ?Q = sets ?B" by (rule sets_pair_law_of)
  have PQ: "prob_space ?Q"
    unfolding pair_law_of_def by (rule PP.prob_space_distr[OF m1])
  have neQ: "space ?Q \<noteq> {}" by (rule prob_space.not_empty[OF PQ])
  have KQ: "\<kappa> \<in> ?Q \<rightarrow>\<^sub>M prob_algebra ?B"
    using Km measurable_cong_sets[OF setsQ refl] by blast

  \<comment> \<open>the constraint set at this pair of times is closed, hence measurable\<close>
  define C where "C = {w :: 'n pairpath \<in> space ?B.
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L}"
  have CB: "C \<in> sets ?B"
    unfolding C_def
    using borel_of_closed[OF closedin_diffquot_constraint[OF p q]]
    by (simp add: space_borel_of)

  \<comment> \<open>the conditioning set is a measurable PAIR-set\<close>
  have msetN: "{pp \<in> space (N \<Otimes>\<^sub>M ?B). \<theta> (fst pp) \<le> p \<longrightarrow> snd pp \<in> C}
      \<in> sets (N \<Otimes>\<^sub>M ?B)" if setsN: "sets N = sets ?B"
    for N :: "('n pairpath) measure"
  proof -
    have mf: "(\<lambda>pp :: 'n pairpath \<times> 'n pairpath. fst pp) \<in> N \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B"
      unfolding measurable_cong_sets[OF refl setsN, symmetric]
      by (rule measurable_fst)
    have mth: "(\<lambda>pp :: 'n pairpath \<times> 'n pairpath. \<theta> (fst pp))
        \<in> borel_measurable (N \<Otimes>\<^sub>M ?B)"
      using mf by (rule measurable_compose) (rule thM)
    have ms: "(\<lambda>pp :: 'n pairpath \<times> 'n pairpath. snd pp) \<in> N \<Otimes>\<^sub>M ?B \<rightarrow>\<^sub>M ?B"
      by (rule measurable_snd)
    have "{pp \<in> space (N \<Otimes>\<^sub>M ?B). \<theta> (fst pp) \<le> p \<longrightarrow> snd pp \<in> C}
        = (space (N \<Otimes>\<^sub>M ?B) - {pp \<in> space (N \<Otimes>\<^sub>M ?B). \<theta> (fst pp) \<le> p})
          \<union> (snd -` C \<inter> space (N \<Otimes>\<^sub>M ?B))" by blast
    moreover have "{pp \<in> space (N \<Otimes>\<^sub>M ?B). \<theta> (fst pp) \<le> p} \<in> sets (N \<Otimes>\<^sub>M ?B)"
      using mth by measurable
    moreover have "snd -` C \<inter> space (N \<Otimes>\<^sub>M ?B) \<in> sets (N \<Otimes>\<^sub>M ?B)"
      by (rule measurable_sets[OF ms CB])
    ultimately show ?thesis by simp
  qed

  \<comment> \<open>pathwise: after \<open>\<theta>\<close> the future factor's increments ARE \<open>\<omega>\<close>'s\<close>
  have path: "AE \<omega> in P.
      \<theta> (pstopped T \<theta> \<omega>) \<le> p \<longrightarrow> pafter T \<theta> \<omega> \<in> C"
  proof -
    have "AE \<omega> in P. \<omega> \<in> space P" by (rule AE_space)
    with cov show ?thesis
    proof eventually_elim
      case (elim \<omega>)
      show ?case
      proof
        have cw: "continuous_on {0..T} (\<lambda>t. fst (\<omega> t))"
          by (rule path_sets_fst_continuous[OF setsP]) (use elim in blast)
        assume le: "\<theta> (pstopped T \<theta> \<omega>) \<le> p"
        then have thp: "\<theta> \<omega> \<le> p"
          using path_stopping_time_stopped[OF st cw] by simp
        have wq: "pafter T \<theta> \<omega> q = \<omega> q - \<omega> (\<theta> \<omega>)"
        proof -
          have "max q (\<theta> \<omega>) = q" using thp pq by simp
          then show ?thesis by (simp add: pafter_apply[OF q])
        qed
        have wp: "pafter T \<theta> \<omega> p = \<omega> p - \<omega> (\<theta> \<omega>)"
        proof -
          have "max p (\<theta> \<omega>) = p" using thp by simp
          then show ?thesis by (simp add: pafter_apply[OF p])
        qed
        have sp: "pafter T \<theta> \<omega> \<in> space ?B"
        proof -
          have "\<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
            using elim(2) sets_eq_imp_space_eq[OF setsP] by (simp add: space_borel_of)
          then have "pafter T \<theta> \<omega> \<in> mspace (path_metric T :: ('n pairpath) metric)"
            by (rule pafter_mspace[OF th0 thT])
          then show ?thesis by (simp add: space_borel_of)
        qed
        have "(1 / (q - p)) *\<^sub>R (snd (\<omega> q) - snd (\<omega> p)) \<in> sconstraint k L"
          using elim(1) p q pq by auto
        then show "pafter T \<theta> \<omega> \<in> C"
          unfolding C_def using sp by (simp add: wq wp)
      qed
    qed
  qed

  \<comment> \<open>and the transfer\<close>
  have joint: "AE pp in distr P (?B \<Otimes>\<^sub>M ?B)
      (\<lambda>\<omega>. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>)).
        \<theta> (fst pp) \<le> p \<longrightarrow> snd pp \<in> C"
    unfolding AE_distr_iff[OF mphi msetN[OF refl]] using path by simp
  then have "AE pp in ksemi ?Q ?B \<kappa>. \<theta> (fst pp) \<le> p \<longrightarrow> snd pp \<in> C"
    unfolding eq .
  then have "AE p' in ?Q. AE w in \<kappa> p'. \<theta> p' \<le> p \<longrightarrow> w \<in> C"
    unfolding AE_ksemi[OF KQ msetN[OF setsQ]] by simp
  then show ?thesis unfolding C_def by (auto elim: eventually_mono)
qed

text \<open>Collecting the pairs.  Two \<open>AE_ball_countable'\<close> passes on the past-law
  gather the rational pairs, and two more, applied to \<open>\<kappa> p'\<close>, move the
  almost-sure quantifier over \<open>w\<close> outside the countable conjunction.  What
  remains is a purely pathwise step: extending from rational to real times
  by continuity of \<open>w\<close> and closedness of \<open>sconstraint k L\<close>.\<close>

lemma AE_rcd_stopping_diffquot_rat:
  fixes P :: "('n::finite pairpath) measure"
  assumes T0: "0 \<le> T" and PS: "prob_space P"
    and setsP: "sets P = sets (path_borel T :: ('n pairpath) measure)"
    and st: "path_stopping_time T \<theta>"
    and thM: "\<theta> \<in> borel_measurable (path_borel T :: ('n pairpath) measure)"
    and Km: "\<kappa> \<in> (path_borel T :: ('n pairpath) measure)
        \<rightarrow>\<^sub>M prob_algebra (path_borel T :: ('n pairpath) measure)"
    and eq: "distr P
          ((path_borel T :: ('n pairpath) measure)
            \<Otimes>\<^sub>M (path_borel T :: ('n pairpath) measure))
          (\<lambda>\<omega>. (pstopped T \<theta> \<omega>, pafter T \<theta> \<omega>))
        = ksemi (pair_law_of T (pstopped T \<theta>) P)
            (path_borel T :: ('n pairpath) measure) \<kappa>"
    and cov: "AE \<omega> in P. \<forall>s t. 0 \<le> s \<longrightarrow> s < t \<longrightarrow> t \<le> T \<longrightarrow>
        (1 / (t - s)) *\<^sub>R (snd (\<omega> t) - snd (\<omega> s)) \<in> sconstraint k L"
  shows "AE p' in pair_law_of T (pstopped T \<theta>) P. AE w in \<kappa> p'.
      \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> \<theta> p' \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
proof -
  let ?Q = "pair_law_of T (pstopped T \<theta>) P"
  have one: "AE p' in ?Q. AE w in \<kappa> p'. \<theta> p' \<le> p \<longrightarrow>
      (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
    if "p \<in> {0..T}" "q \<in> {0..T}" "p < q" for p q :: real
    by (rule AE_rcd_stopping_diffquot_at
        [OF T0 PS setsP st thM Km eq cov that(1) that(2) that(3)])
  have rat: "AE p' in ?Q. \<forall>p\<in>(\<rat>::real set). \<forall>q\<in>(\<rat>::real set).
      p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow>
        (AE w in \<kappa> p'. \<theta> p' \<le> p \<longrightarrow>
          (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L)"
  proof (rule AE_ball_countable'[OF _ countable_rat])
    fix p :: real assume "p \<in> \<rat>"
    show "AE p' in ?Q. \<forall>q\<in>(\<rat>::real set).
        p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow>
          (AE w in \<kappa> p'. \<theta> p' \<le> p \<longrightarrow>
            (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L)"
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix q :: real assume "q \<in> \<rat>"
      show "AE p' in ?Q. p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow>
          (AE w in \<kappa> p'. \<theta> p' \<le> p \<longrightarrow>
            (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L)"
      proof (cases "p \<in> {0..T} \<and> q \<in> {0..T} \<and> p < q")
        case True
        then show ?thesis using one[of p q] by auto
      next
        case False
        then show ?thesis by auto
      qed
    qed
  qed
  show ?thesis
    using rat
  proof eventually_elim
    case (elim p')
    show ?case
    proof (rule AE_ball_countable'[OF _ countable_rat])
      fix p :: real assume p: "p \<in> \<rat>"
      show "AE w in \<kappa> p'. \<forall>q\<in>(\<rat>::real set).
          p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q \<longrightarrow> \<theta> p' \<le> p \<longrightarrow>
            (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
      proof (rule AE_ball_countable'[OF _ countable_rat])
        fix q :: real assume q: "q \<in> \<rat>"
        show "AE w in \<kappa> p'. p \<in> {0..T} \<longrightarrow> q \<in> {0..T} \<longrightarrow> p < q
            \<longrightarrow> \<theta> p' \<le> p \<longrightarrow>
              (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
        proof (cases "p \<in> {0..T} \<and> q \<in> {0..T} \<and> p < q")
          case True
          then have "AE w in \<kappa> p'. \<theta> p' \<le> p \<longrightarrow>
              (1 / (q - p)) *\<^sub>R (snd (w q) - snd (w p)) \<in> sconstraint k L"
            using elim p q by blast
          then show ?thesis by (auto elim: eventually_mono)
        next
          case False
          then show ?thesis by auto
        qed
      qed
    qed
  qed
qed

text \<open>\<open>diffquot_all_of_rational_ge\<close> lives in @{theory Continuous_Path_Spaces.Increment_Moments}.\<close>


text \<open>Clause (iii) for the kernel, closed: the rational pairs collected by
  @{thm [source] AE_rcd_stopping_diffquot_rat}, extended to all real times by
  @{thm [source] diffquot_all_of_rational_ge} inside the almost-sure
  quantifier.  The continuity that the extension needs comes from the paths
  themselves --- every point of the path space is continuous --- via
  @{thm [source] AE_space} on \<open>\<kappa> p'\<close>.\<close>

section \<open>The \<open>\<F>\<^sub>\<sigma>\<close> layer\<close>

text \<open>Clause (iv) needs optional sampling at two stopping times, while
  @{theory Continuous_Time_Martingales.Optional_Sampling}'s \<open>set_optional_sampling\<close> only samples one stopping
  time at deterministic times.  The missing ingredient is the \<open>\<sigma>\<close>-algebra of
  the past at a stopping time, built here directly.\<close>

definition pre_sigma_of :: "'a measure \<Rightarrow> (real \<Rightarrow> 'a measure) \<Rightarrow> ('a \<Rightarrow> real)
    \<Rightarrow> 'a set set"
  where "pre_sigma_of M F \<sigma> =
     {A. A \<in> sets M
       \<and> (\<forall>t. 0 \<le> t \<longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t))}"

lemma pre_sigma_ofI:
  "A \<in> sets M \<Longrightarrow> (\<And>t. 0 \<le> t \<Longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t))
    \<Longrightarrow> A \<in> pre_sigma_of M F \<sigma>"
  unfolding pre_sigma_of_def by blast

lemma pre_sigma_of_sets: "A \<in> pre_sigma_of M F \<sigma> \<Longrightarrow> A \<in> sets M"
  unfolding pre_sigma_of_def by blast

lemma pre_sigma_of_cut:
  "A \<in> pre_sigma_of M F \<sigma> \<Longrightarrow> 0 \<le> t
    \<Longrightarrow> A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  unfolding pre_sigma_of_def by blast

text \<open>It is a \<open>\<sigma>\<close>-algebra: the complement step is where the stopping-time
  property of \<open>\<sigma>\<close> is spent, since \<open>{\<sigma> \<le> t}\<close> itself has to be in \<open>F t\<close> for
  the relative complement to stay there.\<close>

lemma sigma_algebra_pre_sigma_of:
  assumes filt: "\<And>t. 0 \<le> t \<Longrightarrow> subalgebra M (F t)"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
  shows "sigma_algebra (space M) (pre_sigma_of M F \<sigma>)"
proof (rule sigma_algebra_iff2[THEN iffD2], intro conjI ballI allI impI)
  show "pre_sigma_of M F \<sigma> \<subseteq> Pow (space M)"
    using pre_sigma_of_sets sets.sets_into_space by blast
  show "{} \<in> pre_sigma_of M F \<sigma>"
    by (rule pre_sigma_ofI) (simp_all add: stop)
next
  fix A assume A: "A \<in> pre_sigma_of M F \<sigma>"
  show "space M - A \<in> pre_sigma_of M F \<sigma>"
  proof (rule pre_sigma_ofI)
    show "space M - A \<in> sets M" using pre_sigma_of_sets[OF A] by simp
    fix t :: real assume t: "0 \<le> t"
    have spF: "space (F t) = space M"
      using filt[OF t] by (simp add: subalgebra_def)
    have "(space M - A) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}
        = {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} - (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t})" by blast
    moreover have "\<dots> \<in> sets (F t)"
      using stop[OF t] pre_sigma_of_cut[OF A t] by (rule sets.Diff)
    ultimately show "(space M - A) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
      by simp
  qed
next
  fix AA :: "nat \<Rightarrow> 'a set"
  assume AA: "range AA \<subseteq> pre_sigma_of M F \<sigma>"
  show "(\<Union>i. AA i) \<in> pre_sigma_of M F \<sigma>"
  proof (rule pre_sigma_ofI)
    show "(\<Union>i. AA i) \<in> sets M"
      using AA pre_sigma_of_sets by (intro sets.countable_UN) blast
    fix t :: real assume t: "0 \<le> t"
    have "(\<Union>i. AA i) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}
        = (\<Union>i. AA i \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t})" by blast
    moreover have "\<dots> \<in> sets (F t)"
      using AA t by (intro sets.countable_UN) (auto intro: pre_sigma_of_cut)
    ultimately show "(\<Union>i. AA i) \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t} \<in> sets (F t)"
      by simp
  qed
qed

text \<open>Monotone in the stopping time, and it sits below \<open>M\<close>.  Monotonicity is
  the step the two-stopping-time sampling theorem consumes: the conditioning
  set for the earlier time is legal for the later one.\<close>

lemma pre_sigma_of_mono:
  assumes le: "\<And>\<omega>. \<sigma> \<omega> \<le> \<rho> \<omega>"
    and stop: "\<And>t. 0 \<le> t \<Longrightarrow> {\<omega> \<in> space M. \<rho> \<omega> \<le> t} \<in> sets (F t)"
  shows "pre_sigma_of M F \<sigma> \<subseteq> pre_sigma_of M F \<rho>"
proof
  fix A assume A: "A \<in> pre_sigma_of M F \<sigma>"
  show "A \<in> pre_sigma_of M F \<rho>"
  proof (rule pre_sigma_ofI)
    show "A \<in> sets M" by (rule pre_sigma_of_sets[OF A])
    fix t :: real assume t: "0 \<le> t"
    have "A \<inter> {\<omega> \<in> space M. \<rho> \<omega> \<le> t}
        = (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) \<inter> {\<omega> \<in> space M. \<rho> \<omega> \<le> t}"
      by (auto intro: order_trans[OF le])
    moreover have "\<dots> \<in> sets (F t)"
      using pre_sigma_of_cut[OF A t] stop[OF t] by (rule sets.Int)
    ultimately show "A \<inter> {\<omega> \<in> space M. \<rho> \<omega> \<le> t} \<in> sets (F t)" by simp
  qed
qed

text \<open>And a deterministic time gives back the filtration itself, which is how
  the new layer connects to everything already proved.\<close>

text \<open>The slice lemma: an \<open>\<F>\<^sub>\<sigma>\<close>-set, cut down to a half-open band of values of
  \<open>\<sigma>\<close>, lands in the filtration at the top of the band.  This is the brick
  the two-stopping-time sampling theorem runs on: for a simple \<open>\<sigma>\<close> with
  values \<open>t\<^sub>1 < \<dots> < t\<^sub>m\<close> the sets \<open>A \<inter> {\<sigma> = t\<^sub>j}\<close> are exactly such bands, so
  the conditioning set decomposes into finitely many pieces that the
  ordinary deterministic-time sampling can already handle.\<close>

lemma pre_sigma_of_band:
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and s: "0 \<le> s" and st: "s \<le> t"
  shows "A \<inter> {\<omega> \<in> space M. s < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> t} \<in> sets (F t)"
proof -
  have t: "0 \<le> t" using s st by simp
  have "A \<inter> {\<omega> \<in> space M. s < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> t}
      = (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) - (A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> s})"
    by auto
  moreover have "(A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> t}) \<in> sets (F t)"
    by (rule pre_sigma_of_cut[OF A t])
  moreover have "(A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> s}) \<in> sets (F t)"
    using pre_sigma_of_cut[OF A s] mono[OF s st] by blast
  ultimately show ?thesis by (simp add: sets.Diff)
qed

text \<open>And the bottom band, \<open>\<sigma> \<le> t\<^sub>1\<close>, is @{thm [source] pre_sigma_of_cut}
  itself, so a simple \<open>\<sigma>\<close> gives a finite partition of \<open>A\<close> into pieces each
  living in the filtration at its own value.  Stated as the partition it
  will be used as.\<close>

text \<open>The value-set form of the slice, which is what the sampling theorem
  wants: the pieces indexed by the values of \<open>\<sigma>\<close> are genuinely disjoint,
  whereas pieces indexed by positions in a list need not be.\<close>

lemma pre_sigma_of_value_slice:
  assumes mono: "\<And>s t. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> sets (F s) \<subseteq> sets (F t)"
    and A: "A \<in> pre_sigma_of M F \<sigma>"
    and V: "finite V" and Vnn: "\<And>u. u \<in> V \<Longrightarrow> 0 \<le> u"
    and vals: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> \<sigma> \<omega> \<in> V"
    and v: "v \<in> V"
  shows "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = v} \<in> sets (F v)"
proof (cases "{u \<in> V. u < v} = {}")
  case False
  define b where "b = Max {u \<in> V. u < v}"
  have fin: "finite {u \<in> V. u < v}" using V by simp
  have bmem: "b \<in> {u \<in> V. u < v}" unfolding b_def by (rule Max_in[OF fin False])
  then have b0: "0 \<le> b" and bv: "b < v" using Vnn by auto
  have "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = v}
      = A \<inter> {\<omega> \<in> space M. b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v}"
  proof -
    have "(\<sigma> \<omega> = v) = (b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v)" if w: "\<omega> \<in> space M" for \<omega>
    proof
      assume "\<sigma> \<omega> = v" then show "b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v" using bv by simp
    next
      assume h: "b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v"
      show "\<sigma> \<omega> = v"
      proof (rule ccontr)
        assume "\<sigma> \<omega> \<noteq> v"
        then have "\<sigma> \<omega> \<in> {u \<in> V. u < v}" using vals[OF w] h by auto
        then have "\<sigma> \<omega> \<le> b" unfolding b_def by (rule Max_ge[OF fin])
        then show False using h by simp
      qed
    qed
    then show ?thesis by auto
  qed
  moreover have "A \<inter> {\<omega> \<in> space M. b < \<sigma> \<omega> \<and> \<sigma> \<omega> \<le> v} \<in> sets (F v)"
    by (rule pre_sigma_of_band[OF mono A b0 less_imp_le[OF bv]])
  ultimately show ?thesis by simp
next
  case True
  have "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> = v} = A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> v}"
  proof -
    have "(\<sigma> \<omega> = v) = (\<sigma> \<omega> \<le> v)" if w: "\<omega> \<in> space M" for \<omega>
      using vals[OF w] True by force
    then show ?thesis by auto
  qed
  moreover have "A \<inter> {\<omega> \<in> space M. \<sigma> \<omega> \<le> v} \<in> sets (F v)"
    by (rule pre_sigma_of_cut[OF A Vnn[OF v]])
  ultimately show ?thesis by simp
qed


(*<*)
end
(*>*)
