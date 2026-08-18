section \<open>Kernels into the class: measurability and repair\<close>

(*<*)
theory Dynamic_Programming_Kernels
  imports Dynamic_Programming_Conditioning
    "Continuous_Time_Martingales.Integrability_Criteria"
    "Continuous_Path_Spaces.Increment_Moments"
    "Continuous_Time_Martingales.Essential_Infimum"
    "Continuous_Path_Spaces.Path_Exit_Times"
    Path_Law_Pasting
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








end
(*>*)
