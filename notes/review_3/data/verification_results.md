# PIDE-verified claims (verification round, 2026-10-07)


## simplify-essinf: give a direct proof of Path_Exit_Times.ess_inf_pexit_usc that does not use the Laplace-transform route, and identify which lemmas would become dead

CONFIRMED. A direct proof of exactly the same statement as ess_inf_pexit_usc is 69 lines from `theorem` to `qed`. An ML `@{assert}` checks that its prop is `aconv` to the original's. It needs no Laplace lemmas, no pstep*, no exp_pexit_integral_liminf and no ess_inf_pexit_usc. A second version drops hypotheses: it takes only `0 <= T`, `closed K` and `wc`, and is 65 lines. Both files check in PIDE session "ra" with 0 errors, 0 bad commands and 0 warnings, and `thm_oracles` reports no oracles. The original statement follows from the minimal version in one line (`using T K wc by (intro ess_inf_pexit_usc_min) auto`, also checked). The proof goes as the claim says. Limsup_le_iff turns the goal into: for all d > ess_inf_Λ, eventually ess_inf_{Λi} < d. The ennreal sublevel {ennreal (pexit f) < d} equals the real sublevel {pexit f < (if d=⊤ then T+1 else enn2real d)}. That set is open by pexit_sublevel_open. ess_inf_time_less_iff gives positive Λ-mass, weak_conv_open_liminf with le_Liminf_iff gives eventually positive Λi-mass, and ess_inf_time_less_iff converts back. One deviation from the claim: weak_conv_open_positive_eventually (Path_Space) cannot be used directly. It requires `sets (Ni i) = ...` for ALL i, but weak_conv_on only gives this eventually. So weak_conv_open_liminf (Path_Exit_Times, 78 lines) stays alive and is used by the new proof. Dead code after the switch: about 789 lines in Path_Exit_Times.thy, plus 51 lines in Integrability_Criteria.thy, plus 107 lines saved in the theorem body itself (172 down to 65), about 947 lines in total.

- **[confirmed]** ess_inf_pexit_usc has a direct proof of about 60 lines via ess_inf_time_less_iff, pexit_sublevel_open, the open-set portmanteau and Limsup_le_iff, without the Laplace route  
  Evidence: File Essinf_Direct.thy contains theorem ess_inf_pexit_usc_direct with the original hypotheses (0<T, closed K, wc, probs, prob). It is 69 lines and checks with 0 errors, 0 bad and 0 unprocessed (136/136 commands finished). `ML ‹@{assert} (Thm.prop_of @{thm ess_inf_pexit_usc} aconv Thm.prop_of @{thm ess_inf_pexit_usc_direct})›` passes. `thm_oracles ess_inf_pexit_usc_direct` prints `oracles:` with nothing after it. File Essinf_Direct_Min.thy contains ess_inf_pexit_usc_min, which assumes only `0 <= T`, `closed K` and `wc`; it checks clean (146/146 commands finished, 0 errors, 0 bad). Lemmas the proof uses: weak_conv_on_def, sets_eq_imp_space_eq, space_borel_of, pexit_le_T, pexit_nonneg, ennreal_cases, ennreal_less_iff, borel_of_open, pexit_sublevel_open, Limsup_le_iff, ess_inf_time_less_iff, finite_measure.emeasure_eq_measure, zero_less_measure_iff, weak_conv_open_liminf, le_Liminf_iff, measure_def. No [simp]/[intro]/declare attributes occur in the Laplace block (lines 196-1318), so simp cannot pick up Laplace lemmas implicitly. Final proof of the minimal version:
proof -
  let ?m = "path_metric T :: (real => 'b) metric"
  have wc': "(∀F i in sequentially. sets (Λi i) = sets (borel_of (mtopology_of ?m))) ∧ sets Λ = sets (borel_of (mtopology_of ?m)) ∧ finite_measure Λ"
    using wc unfolding weak_conv_on_def by (auto elim: eventually_mono)
  have sub: "{f ∈ space M. ennreal (pexit T K f) < d} = {f ∈ mspace ?m. pexit T K f < (if d = ⊤ then T + 1 else enn2real d)}" if s: "sets M = sets (borel_of (mtopology_of ?m))" for M d
  proof -
    have sp: "space M = mspace ?m" using sets_eq_imp_space_eq[OF s] by (simp add: space_borel_of)
    show ?thesis
    proof (cases "d = ⊤")
      case True then show ?thesis using sp pexit_le_T[OF T0, of K] by (auto intro: order.strict_trans1[OF _ less_add_one])
    next
      case False
      then have "d = ennreal (enn2real d)" by (cases d rule: ennreal_cases) auto
      then show ?thesis using sp False pexit_nonneg[OF T0, of K] by (auto simp: ennreal_less_iff) (metis ennreal_less_iff)+
    qed
  qed
  have meas: "{f ∈ space M. ennreal (pexit T K f) < d} ∈ sets M" if s: "sets M = sets (borel_of (mtopology_of ?m))" for M d
    unfolding sub[OF s] s by (rule borel_of_open[OF pexit_sublevel_open[OF T0 K]])
  show ?thesis unfolding Limsup_le_iff
  proof (intro allI impI)
    fix d assume d: "ess_inf_time Λ (pexit T K) < d"
    let ?U = "{f ∈ mspace ?m. pexit T K f < (if d = ⊤ then T + 1 else enn2real d)}"
    have "emeasure Λ ?U ≠ 0" using d ess_inf_time_less_iff[OF meas[OF wc'[THEN conjunct2, THEN conjunct1]]] sub[OF wc'[THEN conjunct2, THEN conjunct1]] by simp
    then have pos: "0 < measure Λ ?U" using finite_measure.emeasure_eq_measure[OF wc'[THEN conjunct2, THEN conjunct2]] by (simp add: zero_less_measure_iff)
    have "ereal (measure Λ ?U) ≤ Liminf sequentially (λi. ereal (measure (Λi i) ?U))" by (rule weak_conv_open_liminf[OF wc pexit_sublevel_open[OF T0 K]])
    then have "∀F i in sequentially. ereal 0 < ereal (measure (Λi i) ?U)" by (rule le_Liminf_iff[THEN iffD1, rule_format]) (use pos in simp)
    with wc'[THEN conjunct1] show "∀F i in sequentially. ess_inf_time (Λi i) (pexit T K) < d"
    proof eventually_elim
      case (elim i)
      then have "emeasure (Λi i) ?U ≠ 0" by (auto simp: measure_def)
      then show ?case using ess_inf_time_less_iff[OF meas[OF elim(1)]] sub[OF elim(1)] by simp
    qed
  qed
qed  
  Impact (lines): 947. Hypotheses the original states but does not need: `probs` and `prob` are not needed at all. On the limit side, finiteness comes from the finite_measure Λ part of weak_conv_on. On the approximating side, measure > 0 already implies emeasure ≠ 0. `0 < T` can be weakened to `0 <= T`. If the original statement is kept, the 69-line proof can be swapped in as-is, so no caller changes. The callers are Exit_Class_Optimizer.thy:75, Path_Law_Pasting.thy:598 and :909, and Path_Splicing.thy:901. Lemmas that become dead (checked with `grep -rnw` over the repo .thy files; the only other hits are in the generated output/document/*.tex): in Continuous_Path_Spaces/Path_Exit_Times.thy, ess_inf_time_le_laplace with its section header (193-270, 78 lines), ess_inf_time_eq_laplace_inf (271-455, 185), the pstep definition with pstep_sandwich and pstep_integral (456-656, 201), weak_conv_total_mass (819-843, 25; its only user is pstep_integral_liminf), pstep_integral_liminf (844-977, 134), pstep_integrable (978-1014, 37) and exp_pexit_integral_liminf (1015-1143, 129). That is 789 dead lines. In addition, the body of ess_inf_pexit_usc shrinks from 172 to about 65-69 lines, saving about 105. Also in Continuous_Time_Martingales/Integrability_Criteria.thy, exp_neg_time_integrable and exp_neg_time_integral_lower with their text block (346-396, 51 lines) become dead: their only users are the Laplace lemmas and the old ess_inf_pexit_usc. Lemmas that stay alive: weak_conv_open_liminf (657-734), now used by the new proof; weak_conv_closed_limsup (used in Exit_Class_Tightness:362); weak_conv_closed_full_mass (used in Exit_Class, Pair_Path_Laws and Pair_Path_Space). weak_conv_open_positive_eventually in Path_Space cannot replace weak_conv_open_liminf without extra work, because it needs sets equality for every i, not just eventually. Documentation that would need updating: the theory header text (Path_Exit_Times.thy lines 14-22) and the section title at line 193, which describe the Laplace route. A side observation: weak_conv_open_liminf and weak_conv_closed_limsup repeat about 40 lines of identical mweak_conv_fin interpretation boilerplate.


## dryrun-analytic: check that the 16-theory operator and comparison layer of Relative_Arbitrage builds without probability theory once cInf_mult_pos is supplied locally

Confirmed. The 16 theories, copied into /tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad/verify/analytic/, check in the PIDE session "ra" with 0 errors, 0 bad commands (so no sorry) and 0 failed commands. Real_Inf_Scaling.thy (cInf_mult_pos copied verbatim, imports only HOL-Analysis.Analysis) also checks cleanly. The proofs needed no change. The only edits were: (a) the 2 import lines in Operator_Envelopes and Comparison_Jets, changed from "Continuous_Time_Martingales.Integrability_Criteria" to Real_Inf_Scaling; (b) 24 lines of prose in 8 files, where a document antiquotation @{theory Relative_Arbitrage.X} (and one @{theory Continuous_Time_Martingales.Integrability_Criteria}) was replaced by the plain cartouche \<open>X\<close>. Fix (b) was needed because a theory loaded from outside its session has no qualifier, so these document references fail with 'Unknown ancestor theory'. No import came from a forbidden session apart from the Integrability_Criteria one. The ancestor check printed 'FORBIDDEN ANCESTORS: []'. There are 331 ancestors in all, and their session qualifiers are exactly: (none), HOL, HOL-Analysis, HOL-Combinatorics, HOL-Computational_Algebra, HOL-Library, HOL-Real_Asymp, Lower_Semicontinuous, Second_Order_Viscosity_Analysis, Semicontinuous_Analysis, Symmetric_Matrix_Spectra, Tools. Thm_Deps.all_oracles is empty for comparison_two_domain, comparison_expandable, uniqueness_expandable, viscosity_uniqueness_compact and max_principle_boundary_holds. Timing: the summed command time over the 16 theories plus Real_Inf_Scaling is about 153 s. Wall clock was about 6 minutes (11:38:28 to about 11:44:30) on a session shared with other agents' loads, including one forced re-execution. Nothing in the repository was modified (git status is clean).

- **[confirmed]** The operator and comparison layer (16 theories, Curvature_Operator to Comparison_Two_Domain) compiles with imports only from Symmetric_Matrix_Spectra, Second_Order_Viscosity_Analysis, Semicontinuous_Analysis.Semicontinuity/Semicontinuous_Envelopes and HOL-Analysis, once cInf_mult_pos is supplied locally. Nothing else from HOL-Probability, Continuous_Time_Martingales or Continuous_Path_Spaces is used.  
  Evidence: Setup. The 16 theories were copied unchanged with cp. Real_Inf_Scaling.thy was created with imports "HOL-Analysis.Analysis" and cInf_mult_pos copied verbatim by sed from Continuous_Time_Martingales/Integrability_Criteria.thy lines 24-56. Comparison_Two_Domain.thy was then loaded with the read tool.

Imports. The only forbidden-session import was "Continuous_Time_Martingales.Integrability_Criteria", which appears in Operator_Envelopes.thy line 6 and Comparison_Jets.thy line 6; both were replaced by Real_Inf_Scaling. Every other import in the 16 files was already from Symmetric_Matrix_Spectra, Semicontinuous_Analysis.{Semicontinuity, Semicontinuous_Envelopes} or Second_Order_Viscosity_Analysis.{Test_Functions, Viscosity_Solutions, Doubling_Of_Variables, Soft_Penalty}, or was a theory of the layer itself. These were left as they were.

The one fix needed. On first load, Viscosity_Ball line 10 failed with: Unknown ancestor theory "Relative_Arbitrage.Curvature_Operator". The cause is that the copies load with an empty qualifier, so document antiquotations @{theory Relative_Arbitrage.X} cannot resolve. All 24 such lines, in Viscosity_Ball (1), Operator_Formula (1), Operator_Envelopes (3, plus 1 @{theory Continuous_Time_Martingales.Integrability_Criteria} at line 1198), Operator_Envelope_Continuity (8), Comparison_Jets (3), Comparison_Strictness (3), Comparison_Principle (2) and Comparison_Two_Domain (2), were rewritten by sed to the plain cartouche \<open>X\<close>. These lines are text only; no proof or statement was touched.

Spurious failures. On the first pass, 15 forked proofs failed in Operator_Envelopes (8), Operator_Envelope_Continuity (3), Comparison_Localisation (3) and Comparison_Principle (1). All had an empty 'bad' message and synchronised, ever-growing timings, and the downstream oracle ML command was marked 'canceled', so these were interrupts, not proof failures. I forced re-execution by inserting a blank line before 'theorem feasible_conj' (Operator_Envelopes line 628) and then reverting it, so the final content is the same. After the re-run, the same unchanged proof text checked cleanly.

Final get_state per theory. Every theory shows 0 errors, 0 bad and 0 failed. The only warnings are the harmless Bibtex ones ('Unknown session context: cannot check Bibtex entry LaiShkolnikovSoner').

| Theory | Commands | Summed time (ms) |
|---|---|---|
| Curvature_Operator | 819 | 5722 |
| Viscosity_Definitions | 68 | 3765 |
| Viscosity_Ball | 442 | 41936 |
| Constraint_Set_Convexity | 523 | 3855 |
| Viscosity_Comparison_Interface | 229 | 1765 |
| Ball_Solution | 921 | 3849 |
| Eigenvalue_Bound_Exact | 1427 | 6375 |
| Operator_Continuity | 455 | 1432 |
| Operator_Formula | 4309 | 29775 |
| Operator_Envelopes | 3467 | 13000 |
| Operator_Envelope_Continuity | 1171 | 3843 |
| Comparison_Jets | 14 | 126 |
| Comparison_Strictness | 2218 | 5101 |
| Comparison_Localisation | 2560 | 10007 |
| Comparison_Principle | 2900 | 17430 |
| Comparison_Two_Domain | 2100 | 4527 |
| Real_Inf_Scaling | 114 | 618 |

The total is about 153 s of summed command time. Wall clock was about 6 minutes on a shared, contended session.

Ancestor check (Analytic_Ancestor_Check.thy, imports Comparison_Two_Domain):
- 'FORBIDDEN ANCESTORS: []' for the prefixes HOL-Probability., Continuous_Time_Martingales., Continuous_Path_Spaces., Martingales. and Relative_Arbitrage.
- 'NUMBER OF ANCESTORS: 331'.
- 'ANCESTOR QUALIFIERS: , HOL, HOL-Analysis, HOL-Combinatorics, HOL-Computational_Algebra, HOL-Library, HOL-Real_Asymp, Lower_Semicontinuous, Second_Order_Viscosity_Analysis, Semicontinuous_Analysis, Symmetric_Matrix_Spectra, Tools'.
- The ancestors with no qualifier are exactly the 16 copies, Real_Inf_Scaling, Complex_Main, Main and Pure. 'Tools' is only Tools.Code_Generator.
- The oracle check (Thm_Deps.all_oracles) returned [] for comparison_two_domain, comparison_expandable, uniqueness_expandable, viscosity_uniqueness_compact and max_principle_boundary_holds. Joining these proofs succeeded, and none uses the skip_proof oracle.  
  Impact (lines): 0. Caveats for anyone acting on this:

1. Session parents. The ROOT of Semicontinuous_Analysis declares parent "HOL-Probability", but the two theories used (Semicontinuity, Semicontinuous_Envelopes) import only HOL-Analysis and the AFP entry Lower_Semicontinuous, whose parent is HOL-Analysis. A split-off analytic session therefore needs to load them through 'sessions Semicontinuous_Analysis Lower_Semicontinuous' and must not use Semicontinuous_Analysis as its parent. Transitive dependencies also include AFP Lower_Semicontinuous and HOL-Library, HOL-Combinatorics, HOL-Computational_Algebra and HOL-Real_Asymp, all reached via HOL-Analysis. Lebesgue measure from HOL-Analysis is present, which is still HOL-Probability-free.

2. Moving the layer out of the Relative_Arbitrage session would break the 24 @{theory Relative_Arbitrage.X} antiquotations in its prose. They must be requalified to the new session name.

3. Unused import. Second_Order_Viscosity_Analysis.Crandall_Ishii_Sums is not an ancestor of the layer, although Theorem_On_Sums is.

4. Stale prose, not machine-checked:
   - Operator_Envelopes line 1198 says cInf_mult_pos lives in Integrability_Criteria, while Comparison_Strictness line 447 says it lives in Operator_Envelopes.
   - Viscosity_Comparison_Interface lines 27-31 still say the comparison half is 'Axiomatized (as the locale assumption of comparison_principle)', although Comparison_Principle now proves it.

5. The first-pass failures (empty messages, canceled ML command) came from other agents' activity on the shared PIDE session, not from the proofs.


## libdup-check: decide whether 8 repository lemmas follow from library facts in a few lines, with machine-checked derivations in PIDE session "ra"

I checked all 8 claims in scratch theories in /tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad/verify/libdup-check/ (LibDup_A..G.thy, plus copied AFP Fair_Games_Theorem files). All 10 theories finished OK in PIDE with 0 errors and 0 bad/sorry commands. The repository was not modified (git status is clean).
- Confirmed, each a 1-line proof from the library: claim 1 (Lipschitz_imp_absolutely_continuous), claim 2 (BMC.indep_vars_PiM_coordinate), claim 3 (martingale.add and martingale.diff), claim 6 (continuous_map_diff), claim 7 (Product_Vector.norm_Pair_le). For claims 1, 3 and 7, solve_direct lists the library fact next to the repository lemma. The repository text is wrong in two places: Covariation_Density says the Lipschitz-implies-absolutely-continuous step is not in the distribution, and Exit_Class_Witness says indep_vars_PiM_coordinate is "not in scope". Both are false.
- Partially confirmed: claim 4. The Disintegration lemmas (prob_kernel.integrable_kernel_integrable, prob_kernel.integral_fst) need two extra things: `sigma_finite_measure M`, and a bridging lemma that ksemi is a disintegration (about 20 lines, proved). With those, each repository lemma is a 3-line corollary, and the library version is more general: Banach-valued, with no gm or msec measurability hypotheses. The repository lemmas need no sigma-finiteness, but every call site I looked at has M a probability space.
- Partially confirmed: claim 5. pre_sigma_of is not literally an instance of filtration.pre_sigma (set of sets vs. a sigma-generated measure; t>=0 vs. all t; an extra A in sets M conjunct). I proved they are equal under: filtration, sets(F t) ⊆ sets M, σ>=0, and the library stopping_time. For the natural filtration this follows from evaluation measurability alone (a 6-line corollary). The general proof is about 40 lines, not 5.
- Partially confirmed: claim 8. The closest library theorem is Fair_Games_Theorem.Optional_Stopping's nat_sigma_finite_filtered_measure.stopped_process_submartingale, which covers submartingales only. There is no martingale version in Martingales, Doob_Convergence or Fair_Games_Theorem. Applying it to X and -X plus martingale_iff re-derives martingale_stopped in about 16 lines (checked). However, Fair_Games_Theorem is not a session dependency of the repository and is not importable in the "ra" session ("Bad theory import"), so I loaded copies of its sources.

- **[confirmed]** 1. Covariation_Density.lipschitz_imp_absolutely_continuous_on duplicates HOL-Analysis Absolute_Continuity.Lipschitz_imp_absolutely_continuous  
  Evidence: thm output, identical up to renaming M/B: Absolute_Continuity.Lipschitz_imp_absolutely_continuous: (⋀x y. x ∈ ?S ⟹ y ∈ ?S ⟹ norm (?f x - ?f y) ≤ ?B * ¦x - y¦) ⟹ absolutely_continuous_on ?S ?f. The repository lemma has the same statement with ?M (and fixes 'a::euclidean_space, as absolutely_continuous_on does). Accepted: `lemma C1: fixes f :: "real ⇒ 'a::euclidean_space" assumes lip: "⋀x y. x ∈ S ⟹ y ∈ S ⟹ norm (f x - f y) ≤ M * ¦x - y¦" shows "absolutely_continuous_on S f" by (rule Lipschitz_imp_absolutely_continuous[OF lip])`. Auto solve_direct on the goal lists both facts. The theory text says the step is 'not available in the Isabelle distribution'; that is false for the Isabelle2026-RC3 in use (src/HOL/Analysis/Absolute_Continuity.thy:859).  
  Impact (lines): 42. The repository proof is Relative_Arbitrage/Covariation_Density.thy lines 27-68 and has 2 uses, so it can be deleted (or turned into a 1-line alias). The intro text at lines 21-22 should be corrected.

- **[confirmed]** 2. Exit_Class_Witness.bm_coordinates_indep follows from Kolmogorov_Chentsov_Extras product_prob_space.indep_vars_PiM_coordinate  
  Evidence: Library: product_prob_space ?M ⟹ ?I ≠ {} ⟹ prob_space.indep_vars (Pi⇩M ?I ?M) ?M (λx f. f x) ?I. bm_paths_def: bm_paths = Pi⇩M UNIV (λ_. wiener_pre). The interpretation BMC: product_prob_space (λ_. wiener_pre) UNIV is in Wiener_Measure.Product_Brownian_Motion, which imports Kolmogorov_Chentsov_Extras. Accepted in a theory importing Relative_Arbitrage.Exit_Class_Witness: `lemma C2: "prob_space.indep_vars (bm_paths :: ('n::finite ⇒ real ⇒ real) measure) (λ_. wiener_pre) (λk ω. ω k) UNIV" unfolding bm_paths_def by (rule BMC.indep_vars_PiM_coordinate) simp`.  
  Impact (lines): 22. The in-proof comment says indep_vars_PiM_coordinate 'is not in scope here'; that is false, since BMC.indep_vars_PiM_coordinate resolves. The 26-line proof (lines 23-48) becomes a 2-line proof.

- **[confirmed]** 3. Martingale_Algebra.martingale_add / martingale_diff duplicate AFP Martingales lemmas  
  Evidence: Library (Martingales/Martingale.thy, context martingale): martingale.add: martingale ?M ?F ?t⇩0 ?X ⟹ martingale ?M ?F ?t⇩0 ?Y ⟹ martingale ?M ?F ?t⇩0 (λi ξ. ?X i ξ + ?Y i ξ); martingale.diff: same with (λi x. ?X i x - ?Y i x). Accepted: C3_add (index type real, as in the repo) `by (rule martingale.add[OF mX mY])`; C3_diff (repo's general index type) `by (rule martingale.diff[OF MX MY])`; also C3_add_general for the general index type. solve_direct lists martingale.add/diff next to the repository lemmas. The library add is more general than the repo's martingale_add, which is restricted to a real index.  
  Impact (lines): 60. Continuous_Time_Martingales/Martingale_Algebra.thy lines 20-56 and 72-96. The header text ('Elementary closure properties the AFP's Martingales entry does not record: sums, differences, ...') and the remark before martingale_diff ('The AFP entry does not record the difference') are wrong. The AFP also has martingale.scaleR_const and martingale.uminus.

- **[partially]** 4. Path_Law_Pasting.AE_integrable_ksemi_section and integral_ksemi_real follow from AFP Disintegration prob_kernel lemmas  
  Evidence: Library: prob_kernel.integrable_kernel_integrable: prob_kernel ?X ?Y ?κ ⟹ integrable ?ν ?f ⟹ measure_kernel.disintegration ?X ?Y ?κ ?ν ?μ ⟹ sigma_finite_measure ?μ ⟹ AE x in ?μ. integrable (?κ x) (λy. ?f (x, y)). prob_kernel.integral_fst: same hypotheses ⟹ integral⇧L ?ν ?f = LINT x|?μ. LINT y|?κ x. ?f (x, y) (Banach-valued). Bridging lemma, accepted: `lemma ksemi_disintegration: assumes K: "Kr ∈ M →⇩M prob_algebra N" and ne: "space M ≠ {}" shows "measure_kernel.disintegration M N Kr (ksemi M N Kr) M"`, about 20 lines via prob_kernel_def', disintegrationI, sets_ksemi, nn_integral_ksemi and nn_integral_cmult_indicator. With it, both are accepted: `C4_AE_integrable` (K, gi, ne, sf: sigma_finite_measure M ⟹ AE ω in M. integrable (Kr ω) (λω'. g (ω, ω'))) and `C4_integral` (same ⟹ ∫p. g p ∂ksemi M N Kr = ∫ω. ∫ω'. g (ω, ω') ∂Kr ω ∂M), each `using prob_kernel.<lemma>[OF _ gi ksemi_disintegration[OF K ne] sf] K by (simp add: prob_kernel_def')`. The library route needs the extra hypothesis sigma_finite_measure M, which the repository lemmas do not assume. In return it drops gm and msec and works for Banach-valued g, not only real.  
  Impact (lines): 95. Not 5 lines: it needs the one-time ~20-line ksemi_disintegration bridge plus the sigma-finite hypothesis. The repository lemmas (37 + 87 lines) are therefore strictly more general in M. At the call sites I inspected (Path_Law_Sampling 2106/3071, Path_Law_Pasting 2262), M is a prob_space, so the library route would work there. Estimated net saving is about 95 lines, but call sites need the extra prob_space argument.

- **[partially]** 5. Path_Stopping_Times.pre_sigma_of is an instance of / equal to HOL-Probability filtration.pre_sigma under a natural filtration  
  Evidence: Definitions differ. pre_sigma_of M F σ = {A. A ∈ sets M ∧ (∀t. 0 ≤ t ⟶ A ∩ {ω∈space M. σ ω ≤ t} ∈ sets (F t))} is a set of sets, has no locale, and quantifies only t ≥ 0. filtration.pre_sigma T = sigma Ω {A. ∀t. {ω∈A. T ω ≤ t} ∈ sets (F t)} is a measure, lives in locale filtration Ω F, and quantifies all t. Proved equality (accepted, about 40 lines): `lemma pre_sigma_of_eq_pre_sigma: assumes "filtration (space M) F" "⋀t. sets (F t) ⊆ sets M" "⋀ω. ω ∈ space M ⟹ 0 ≤ σ ω" "stopping_time F σ" shows "pre_sigma_of M F σ = sets (filtration.pre_sigma (space M) F σ)"`. The ⊆ direction uses the empty cut for t<0. The ⊇ direction gets A ⊆ space M from the cut at t = σ ω, and A ∈ sets M from A = ⋃n. {ω∈A. σ ω ≤ n}. Corollary for the natural filtration, accepted (6-line proof via sets_natural_filtration_mono and sets.sigma_sets_subset): `pre_sigma_of_natural_eq_pre_sigma: (⋀v. X v ∈ P →⇩M borel) ⟹ (⋀ω. ω ∈ space P ⟹ 0 ≤ θ ω) ⟹ stopping_time (natural_filtration P 0 X) θ ⟹ pre_sigma_of P (natural_filtration P 0 X) θ = sets (filtration.pre_sigma (space P) (natural_filtration P 0 X) θ)`.  
  Impact (lines): 0. The two notions agree whenever σ is a nonnegative stopping time of a filtration contained in sets M, which is the situation in the repository (natural filtration, path_stopping_time with 0 ≤ θ ≤ T). Switching would let the repository reuse library facts such as sigma_algebra_pre_sigma, mono_pre_sigma and measurable_stopping_time_pre_sigma. But the bridge alone costs about 45 lines, and pre_sigma_of has 98 occurrences, so the net saving is unclear. I report 0 removable lines.

- **[confirmed]** 6. Path_Tightness.continuous_map_real_diff duplicates HOL-Analysis continuous_map_diff  
  Evidence: Library: Abstract_Limits.continuous_map_diff: continuous_map ?X euclidean ?f ⟹ continuous_map ?X euclidean ?g ⟹ continuous_map ?X euclidean (λx. ?f x - ?g x), for any real_normed_vector. The repo lemma is its instance at euclideanreal. Accepted: `lemma C6: assumes f: "continuous_map X euclideanreal f" and g: "continuous_map X euclideanreal g" shows "continuous_map X euclideanreal (λx. f x - g x)" by (rule continuous_map_diff[OF f g])`.  
  Impact (lines): 6. The surrounding text calls it 'missing-in-library'; that is false. continuous_map_diff is also tagged [continuous_intros].

- **[confirmed]** 7. Doubling_Of_Variables.norm_Pair_le duplicates and shadows Product_Vector.norm_Pair_le  
  Evidence: Library Product_Vector.norm_Pair_le: norm (?x, ?y) ≤ norm ?x + norm ?y. Doubling_Of_Variables.norm_Pair_le: norm (?a, ?b) ≤ norm ?a + norm ?b, the same up to variable names, both for real_normed_vector. In a theory importing Second_Order_Viscosity_Analysis.Doubling_Of_Variables, `Facts.intern facts "norm_Pair_le"` returns "Doubling_Of_Variables.norm_Pair_le", and both full names exist. So the unqualified name is shadowed by the repository copy. This is harmless semantically because the statements coincide. Accepted: `lemma C7: ... shows "norm ((a, b) :: 'a × 'b) ≤ norm a + norm b" by (rule Product_Vector.norm_Pair_le)`. solve_direct lists both.  
  Impact (lines): 10. Uses (Doubling_Of_Variables 3496/3498, Pair_Path_Laws 463) would resolve to the library fact unchanged if the duplicate (lines 3473-3482) were deleted.

- **[partially]** 8. Quadratic_Variation stopped section (stopped_sq_int_martingale locale, martingale_stopped) vs AFP Doob_Convergence / Fair_Games_Theorem  
  Evidence: No library theorem states that a stopped martingale is a martingale. The closest is Fair_Games_Theorem.Optional_Stopping: nat_sigma_finite_filtered_measure.stopped_process_submartingale: nat_sigma_finite_filtered_measure ?M ?F ⟹ submartingale_linorder ?M ?F 0 ?X ⟹ linearly_filtered_measure.stopping_time ?M ?F 0 ?τ ⟹ submartingale ?M ?F 0 (stopped_process ?X ?τ). Here stopped_process X τ i ω = X (min i (τ ω)) ω, the same as the repository's stopped. Doob_Convergence.Stopping_Time defines linearly_filtered_measure.stopping_time (T ∈ space M → {t0..} ∧ ∀t≥t0. pred (F t) (λx. T x ≤ t)), which is equivalent to the locale's stopping_time_T (1-line proof). Re-derivation accepted inside `context stopped_sq_int_martingale` (about 16 lines): st by (auto simp: stopping_time_def pred_def); s1 and s2 = stopped_process_submartingale for X and for -X (martingale.uminus[OF martingale_X], submartingale_linorder_def, martingale_iff); supermartingale via submartingale.uminus[OF s2]; finish with martingale_iff. HOL-Probability Stopping_Time also has a stopping_time notion but nothing about stopped processes.  
  Impact (lines): 25. Fair_Games_Theorem (and Doob_Convergence) is NOT a session dependency of the repository and is not importable in the 'ra' PIDE session ('Bad theory import'). To check C8 I copied /opt/afp/thys/Doob_Convergence/Stopping_Time.thy (renamed theory to Doob_Stopping_Time) and the three Fair_Games_Theorem theories into my scratch dir; all loaded with 0 errors under Isabelle2026-RC3. Adopting it would mean adding Fair_Games_Theorem to the Continuous_Time_Martingales ROOT. The stopped Dynkin identity (stopped_expectation_sq_qvar) and qvar_stopped have no library counterpart. martingale_stopped (Quadratic_Variation.thy 521-563) would shrink by about 25 lines.


## clone-derivations: check whether 8 suspected internal clones (a repository lemma that is a special case of another, proved again at length) can be derived from the more general lemma in about 10 lines, checked in PIDE session "ra".

All 8 claims were checked in Isabelle. 7 are confirmed and 1 is partial. All three scratch theories end with 0 errors, 0 failed commands and 0 sorries. A deliberate 1 = 2 lemma was added and correctly rejected, then removed, so the checking pipeline is not passing everything. Confirmed: (1) exit_val_boundary_zero follows from exit_val_le_ball_bound in a 5-line body (original proof 100 lines). (2) diffquot_all_of_rational is diffquot_all_of_rational_ge with r := 0, one line (original 85 lines). (3) exit_val_visc_subsol is exit_val_visc_subsol_any with Omega := interior K, one line (original 95 lines). (4) feasible_scale (Operator_Envelopes) and feasible_scaleR_p (Comparison_Strictness) state exactly the same fact as feasible_scale_p (Viscosity_Comparison_Interface). The same holds for ell_op_scaleR_p vs ell_op_scale_p and for ell_op_scaleR_matrix vs ell_op_dilation: each one is proved by `rule` from its twin. Viscosity_Comparison_Interface is already imported by both other theories, so the copies there can simply be deleted. (6) exit_val_attained follows from exit_val_measurable_selector in a 5-line body (original 66 lines). (7) Exit_Class.outerp_eq_outer_prod and Pair_Path_Space.outerp_eq_outer_prod have the same statement, and Exit_Class imports Pair_Path_Space, so the Exit_Class copy is a pure duplicate. (8) `bmpair T = sbmpair (mat 1) T` is proved by `(rule ext) (simp add: bmpair_def sbmpair_def)`. The whole sbmpair package (Value_Function_Euler_Construction lines 46-418) was copied verbatim into a theory importing only Exit_Class_Witness and checks unchanged. bmpair_law_in_paper_pair_class then follows in 2 lines, so the 334-line bmpair package can become a corollary. Partial (5): doubling_maximiser_exists and tilted_doubled_hessian_nonpositive follow in one `rule` step from their _gen versions with the penalty set to (alpha/2)*norm(d)^2. sums_matrix_inequality is stated for any 'a::euclidean_space, while sums_matrix_inequality_gen is stated only for real^'n (it uses a matrix Z). So only the real^'n special case is derivable (8-line proof, checked). It also sits in an upstream theory (Theorem_On_Sums) and is reached through the equally generic sums_gives_ordering. The one downstream use found is at real^'n (Crandall_Ishii_Sums.theorem_on_sums_stage), but dropping the generality would be a design decision. Estimated savings: about 750-800 lines in total, about 320 of them from bmpair.

- **[confirmed]** 1. Exit_Class_Witness.exit_val_boundary_zero is derivable from exit_val_le_ball_bound (same theory)  
  Evidence: Isabelle accepted (Clone_RA.thy, lines 12-22, all commands finished, 0 errors):
lemma exit_val_boundary_zero':
  fixes r :: real and x :: "real^'n::finite"
  assumes k: "k < CARD('n)" and T: "0 < T" and L: "0 \<le> L" and x: "norm x = r"
  shows "exit_val k L T (cball 0 r) x = 0"
proof -
  have "x \<bullet> x = r * r"
    using x by (simp add: power2_norm_eq_inner[symmetric] power2_eq_square)
  then show ?thesis
    using exit_val_le_ball_bound[OF k _ L order_refl, of T r x] T by simp
qed
The original proof covers Exit_Class_Witness.thy lines 1066-1165 (100 lines). exit_val_le_ball_bound (line 1175) does not use exit_val_boundary_zero, and nothing between the two lemmas uses it, so it can be moved after the bound and replaced by this proof.  
  Impact (lines): 90. Its one use is Value_Function_Uniqueness.thy:365, which is unaffected.

- **[confirmed]** 2. Increment_Moments.diffquot_all_of_rational is diffquot_all_of_rational_ge with r := 0  
  Evidence: Isabelle accepted (Clone_SOVA.thy, statement copied verbatim):
  by (rule diffquot_all_of_rational_ge[where r = 0, OF S cont rat st(1) st]) auto
The original proof covers Continuous_Path_Spaces/Increment_Moments.thy lines 2185-2269 (85 lines). The _ge proof (2325-2412) does not use the plain version, so _ge can come first and the plain lemma becomes a one-liner.  
  Impact (lines): 76. The plain lemma has about 9 uses across Relative_Arbitrage. They can keep using it once it is restated as a corollary.

- **[confirmed]** 3. Value_Function_Subsolution.exit_val_visc_subsol is derivable from exit_val_visc_subsol_any  
  Evidence: Isabelle accepted, with the statement copied verbatim:
  by (rule exit_val_visc_subsol_any[OF T L1 Kc kn])
(Omega is a free variable in _any and is instantiated with interior K.) The original proof covers Value_Function_Subsolution.thy lines 3153-3247 (95 lines). The _any proof (3255-3348) does not use exit_val_visc_subsol, so the order can be swapped.  
  Impact (lines): 88. The source comment at line 3251 already says the _any proof does not use x in interior K. The two proofs are near-verbatim copies.

- **[confirmed]** 4. feasible_scaleR_p / feasible_scale / feasible_scale_p are three statements of one fact; ell_op_scaleR_p = ell_op_scale_p; ell_op_scaleR_matrix = ell_op_dilation  
  Evidence: Isabelle accepted 7 one-line cross-derivations, each a single `by (rule X[OF ...])` from the twin lemma:
- feasible_scale (Operator_Envelopes:808) proves the statement of feasible_scaleR_p.
- feasible_scale_p (Viscosity_Comparison_Interface:45) proves the same statement.
- feasible_scaleR_p proves feasible_scale's statement.
- ell_op_scale_p proves ell_op_scaleR_p's statement and vice versa.
- ell_op_dilation[OF t ne] proves ell_op_scaleR_matrix's statement, and ell_op_scaleR_matrix[OF c ne] proves ell_op_dilation's.
All statements are identical up to variable names (c / theta, p / q).
Import graph (computed from the imports sections): Viscosity_Comparison_Interface is an ancestor of both Operator_Envelopes and Comparison_Strictness. The copies in Operator_Envelopes and Comparison_Strictness can therefore be deleted outright.
Original proof lengths: feasible_scale_p 19 lines, feasible_scale 13, feasible_scaleR_p 14, ell_op_scale_p 5, ell_op_scaleR_p 5, ell_op_dilation 51 (VCI 85-135), ell_op_scaleR_matrix 19.  
  Impact (lines): 51. 51 lines = deleting feasible_scale, feasible_scaleR_p, ell_op_scaleR_p and ell_op_scaleR_matrix. About 30 more could be saved: ell_op_dilation's 51-line hand-rolled Inf-scaling argument could become the 19-line ell_op_scaleR_matrix proof if cInf_mult_pos (now in Operator_Envelopes) moved upstream of VCI. I did not check that move.

- **[partially]** 5. Doubling_Of_Variables: quadratic-penalty lemmas are special cases of the _gen (general penalty) lemmas  
  Evidence: (a) doubling_maximiser_exists (lines 346-389, 44 lines): Isabelle accepted
  by (rule doubling_maximiser_exists_gen[where Pn = "\<lambda>d. (\<alpha>/2) * (norm d)\<^sup>2", OF cK neK cu cw]) (intro continuous_intros)

(b) tilted_doubled_hessian_nonpositive (lines 3421-3471, 51 lines): Isabelle accepted
  by (rule tilted_doubled_hessian_nonpositive_gen[where P = "\<lambda>d. (\<alpha>/2) * (norm d)\<^sup>2", OF blW rz mx expPsi])

(c) sums_matrix_inequality (Theorem_On_Sums.thy 900-953, 54 lines) is NOT a special case as stated. It is over 'a::euclidean_space, while sums_matrix_inequality_gen is only over real^'n (it uses a matrix Z and *v). At 'a = real^'n, Isabelle accepted this derivation (statement and conclusion copied verbatim):
proof -
  have Pjet: "((\<lambda>h. ((\<alpha>/2) * (norm ((fst zh - snd zh) + h))\<^sup>2 - (\<alpha>/2) * (norm (fst zh - snd zh))\<^sup>2
      - (\<alpha> *\<^sub>R (fst zh - snd zh)) \<bullet> h - (h \<bullet> ((\<alpha> *\<^sub>R mat 1) *v h))/2) / (norm h)\<^sup>2) \<longlongrightarrow> 0) (at 0)"
    by (simp add: power2_norm_eq_inner inner_commute scaleR_matrix_vector_assoc[symmetric] algebra_simps)
  from sums_matrix_inequality_gen[where Pn = "\<lambda>d. (\<alpha>/2) * (norm d)\<^sup>2", OF expPsi Pjet scW neg v]
  show ?thesis by (simp add: scaleR_matrix_vector_assoc[symmetric] inner_add_right)
qed
A first attempt with `scaleR_matrix_vector_assoc` in the forward direction failed. The [symmetric] version passed.  
  Impact (lines): 70. About 35 lines are saved by each of (a) and (b). (c) would also need moving: Theorem_On_Sums is upstream of Doubling_Of_Variables, and the generic sums_gives_ordering (DoV:1222) and sums_ordering_at_interior_max (DoV:1262) are built on it. The one downstream use found (Crandall_Ishii_Sums.theorem_on_sums_stage) is at real^'n, so dropping the generality looks feasible but was not checked.

- **[confirmed]** 6. Exit_Class_Optimizer.exit_val_attained is derivable from exit_val_measurable_selector  
  Evidence: Isabelle accepted, with the statement copied verbatim:
proof -
  obtain S where "\<And>y. pshift_law T y (S y) \<in> exit_class k L T y"
    and "\<And>y. ess_inf_time (pshift_law T y (S y)) (\<lambda>\<omega>. pexit T K (\<lambda>t. fst (\<omega> t))) = exit_val k L T K y"
    using exit_val_measurable_selector[OF T L K, of k] by metis
  then show ?thesis by blast
qed
The original proof covers Exit_Class_Optimizer.thy lines 31-96 (66 lines). The selector's proof (269-449) does not use exit_val_attained; grep finds only a text mention at line 251. Both lemmas take the same assumptions (0<T, 1<=L, closed K).  
  Impact (lines): 55. Used at Value_Function_Subsolution:590 and :1550, which are unaffected.

- **[confirmed]** 7. Exit_Class.outerp_eq_outer_prod duplicates Pair_Path_Space.outerp_eq_outer_prod  
  Evidence: `thm Exit_Class.outerp_eq_outer_prod Pair_Path_Space.outerp_eq_outer_prod` prints
  outerp ?x = Outer_Products.outer_prod ?x ?x
  outerp ?v = Outer_Products.outer_prod ?v ?v
The statements are identical, and there is only one outerp constant (defined in Pair_Path_Space:718). Each lemma proves the other's statement by `rule`, accepted. Exit_Class has Pair_Path_Space among its ancestors (via Path_Law_Sampling, computed from the imports sections), so the Exit_Class copy (lines 218-219) is redundant and only shadows the short name.  
  Impact (lines): 2. This is trivial and only costs 2 lines, but it is a real name clash.

- **[confirmed]** 8. bmpair (Exit_Class_Witness) = sbmpair (mat 1), so the bmpair package becomes a corollary  
  Evidence: Isabelle accepted
  lemma bmpair_eq_sbmpair: "bmpair T = sbmpair (mat 1) T"  by (rule ext) (simp add: bmpair_def sbmpair_def)
and
  corollary bmpair_law_in_paper_pair_class' (statement verbatim):
    unfolding bmpair_eq_sbmpair
    by (rule sbmpair_law_in_paper_pair_class[OF T L]) (use mat_1_in_sconstraint[OF L] in simp)
sbmpair is defined downstream (Value_Function_Euler_Construction imports Value_Function_Subsolution). I therefore copied its whole package verbatim (VFEC lines 46-418, 373 lines) into Sbm_Move.thy, which imports only Relative_Arbitrage.Exit_Class_Witness. All 560 commands finished with 0 errors, and the bmpair corollary also checks there. By name, the sbmpair package uses no fact from Exit_Class_Witness at or after line 544, so it can replace the bmpair block in place. The bmpair package (Exit_Class_Witness 544-877) is 334 lines. Downstream uses are bmpair, bmpair_def (Exit_Class_Infinite) and bmpair_law_in_paper_pair_class, all easy to recover as corollaries.  
  Impact (lines): 320. Refactor: move the sbmpair definition and its lemmas through sbmpair_law_in_paper_pair_class into Exit_Class_Witness at line 544. Define bmpair as an abbreviation of sbmpair (mat 1), or keep it as a constant with bmpair_eq_sbmpair. Exit_Class_Infinite uses bmpair_def, so it would need the one-line derived equation. The rest of Value_Function_Euler_Construction then uses the moved package.


## dryrun-pathtoolkit: check whether the path toolkit (Pair_Path_Space, Pair_Path_Laws, Path_Splicing, Path_Stopping_Times, Path_Law_Pasting, Path_Law_Sampling) still compiles once the two Second_Order_Viscosity_Analysis imports are dropped, confirm by ML that no SOVA theory is an ancestor, and find which other Pair_Path_Space imports are unnecessary.

CONFIRMED. The six theories were copied to /tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad/verify/pathtk/ and the two SOVA imports were deleted from the copy of Pair_Path_Space. All six then check in PIDE (session "ra") with 0 errors, 0 failed, 0 bad (no sorry) and 0 unprocessed. The only warnings are 3 harmless ones in Pair_Path_Space: an "Ignoring sort constraints" warning on the pairpath type_synonym, plus two "cannot check Bibtex entry" warnings that only appear because the copies are outside a session.

Exactly one fix was needed, and it is not a proof. Pair_Path_Laws line 203 is a text block containing `@{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}`. That antiquotation fails with 'Unknown ancestor theory' once SOVA is gone. I deleted that one text line; the fact it mentions (dist_pair_le) is not used anywhere in the toolkit.

The proof at Pair_Path_Laws:463, `by (rule norm_Pair_le)`, now resolves to HOL's Product_Vector.norm_Pair_le. In the copy, `thm norm_Pair_le` prints `norm (?x, ?y) ≤ norm ?x + norm ?y`, and an ML term comparison shows the HOL and SOVA statements are the same up to renaming the variables (x,y vs a,b, both of sort real_normed_vector).

Ancestor check, by ML over Theory.nodes_of in a scratch theory importing the copied Path_Law_Sampling:
- The copy has 419 ancestors and no SOVA ancestors.
- None of its ancestors is from Relative_Arbitrage.*, so the heap versions of the theories were not used by accident.
- Control: the heap theory Relative_Arbitrage.Path_Law_Sampling has 8 SOVA ancestors (Doubling_Of_Variables, Theorem_On_Sums, Sup_Convolution, Jensen_Lemma, Alexandrov, Moreau_Envelope, Rademacher, Convex_Subgradients).

Timing:
- First run: about 274 s wall-clock from load until all six were ok, including the restart caused by the text fix (about 136 s after the fix). Summed PIDE command time is about 269 s.
- Final run with fewer imports: at most 149 s wall-clock; summed command time about 227 s.

Optional import analysis: 22 of the 35 imports of Pair_Path_Space are already implied by the others. Removing Vitali_Convergence and Brownian_Finite_Dimensional_Distributions as well still checks cleanly. Semicontinuity and Modification_Transfer are genuinely needed.

Downstream: with this change, Path_Tightness_Market and Exit_Time_Semicontinuity would also lose all SOVA ancestry. Copies of both, built on the reduced toolkit, check with 0 errors and have no SOVA ancestors. Every other theory in the session still reaches SOVA through its own imports (Viscosity_Definitions, Comparison_Jets, Operator_Envelopes, Value_Function_Euler_Construction).

The repository was not modified (`git status` is clean).

- **[confirmed]** The path toolkit (Pair_Path_Space .. Path_Law_Sampling) does not need Second_Order_Viscosity_Analysis: deleting the imports Second_Order_Viscosity_Analysis.Sup_Convolution and Second_Order_Viscosity_Analysis.Doubling_Of_Variables from Pair_Path_Space leaves all six theories checking.  
  Evidence: The copies were loaded in PIDE session 'ra' by reading Path_Law_Sampling.thy. After the one fix below, every theory has 0 errors, 0 failed, 0 bad and 0 unprocessed:
- Pair_Path_Space: 2767 commands, 34.9 s
- Pair_Path_Laws: 7989 commands, 71.9 s
- Path_Splicing: 3900 commands, 28.4 s
- Path_Stopping_Times: 4048 commands, 21.7 s
- Path_Law_Pasting: 6586 commands, 38.7 s
- Path_Law_Sampling: 5842 commands, 73.8 s

The only warnings are in Pair_Path_Space: 'Ignoring sort constraints' on `type_synonym 'n pairpath`, and two 'Unknown session context: cannot check Bibtex entry LaiShkolnikovSoner' warnings, which come only from loading the copy outside a session.

The single fix needed: Pair_Path_Laws line 203, `text \<open>\<open>dist_pair_le\<close> lives in @{theory Second_Order_Viscosity_Analysis.Doubling_Of_Variables}.\<close>`, failed with 'Unknown ancestor theory "Second_Order_Viscosity_Analysis.Doubling_Of_Variables"'. I deleted that line. dist_pair_le is not used anywhere in the six theories; its only real use is in Value_Function_Euler_Construction, which imports Doubling_Of_Variables itself.

No proof needed changing. `by (rule norm_Pair_le)` at Pair_Path_Laws:463 went through unchanged. `thm norm_Pair_le` in the copy context prints `norm (?x, ?y) ≤ norm ?x + norm ?y`, which is HOL's version with variables x,y.

Total time: about 274 s wall-clock from the first load to all six ok, including recomputation after the fix, which restarted everything from Pair_Path_Laws onward; the post-fix part took about 136 s.  
  Impact (lines): 3. Lines saved: the two import lines plus the one text line. The `sessions` clause in the ROOT must keep Second_Order_Viscosity_Analysis, because Viscosity_Definitions, Comparison_Jets, Comparison_Two_Domain, Operator_Envelopes and Value_Function_Euler_Construction import it directly.

- **[confirmed]** No Second_Order_Viscosity_Analysis theory is an ancestor of the modified Path_Law_Sampling (ML check via Theory.nodes_of).  
  Evidence: ML in Pathtk_Ancestor_Check.thy, which imports the copied Path_Law_Sampling. Output with the SOVA imports removed:
- 'copy: self = Pathtk_Ancestor_Check; #ancestors = 419; SOVA ancestors = []'
- 'copy: Relative_Arbitrage.* ancestors = []'
- 'copy: ancestors outside any session qualifier = [Pathtk_Ancestor_Check, Path_Law_Sampling, Path_Law_Pasting, Path_Stopping_Times, Path_Splicing, Pair_Path_Laws, Pair_Path_Space, Complex_Main, Main, Pure]'

Control, using Build.get_theory on the heap theory: 'control (heap Relative_Arbitrage.Path_Law_Sampling): SOVA ancestors = [Second_Order_Viscosity_Analysis.Doubling_Of_Variables, ...Theorem_On_Sums, ...Sup_Convolution, ...Jensen_Lemma, ...Alexandrov, ...Moreau_Envelope, ...Rademacher, ...Convex_Subgradients]'.

After the further import reduction (next result), the copy has 416 ancestors and still none from SOVA. In Isabelle2026-RC3, Thy_Info is renamed, so Build.get_theory was used instead.  
  Impact (lines): 0. 

- **[confirmed]** Doubling_Of_Variables.norm_Pair_le has the same name and statement as HOL's Product_Vector.norm_Pair_le.  
  Evidence: Checked in a scratch theory importing Second_Order_Viscosity_Analysis.Doubling_Of_Variables:
- Pattern.matches (prop_of Product_Vector.norm_Pair_le, prop_of Doubling_Of_Variables.norm_Pair_le) = true.
- aconv = false, but only because the variable names differ (x,y vs a,b).
- Both are Trueprop (norm (Pair v w) ≤ norm v + norm w) with v :: ?'a::real_normed_vector and w :: ?'b::real_normed_vector.
- `lemma "norm ((a,b) :: 'a::real_normed_vector × 'b::real_normed_vector) ≤ norm a + norm b" by (rule Product_Vector.norm_Pair_le)` is accepted.  
  Impact (lines): 0. 

- **[partially]** Optional: which other Pair_Path_Space imports are unnecessary (Semicontinuity, Vitali_Convergence, Modification_Transfer, Brownian_Finite_Dimensional_Distributions; plus general redundancy).  
  Evidence: Redundancy (ML): Context.make_parents keeps only 13 of the 35 imports as maximal parents. The other 22 are already implied by those 13:
- Path_Space, Path_Space_Infinite, Pathwise_Quadratic_Variation, Stopped_Localization, Increment_Moments, Holder_Interpolation
- Doob_Inequality, Optional_Sampling, Stopping_Times, Integrability_Criteria, Essential_Infimum, Martingale_Algebra, Martingale_Transfer, Time_Discretisation, Vitali_Convergence (implied by Conditional_UI), Stopped_Adaptedness
- Matrix_Algebra, Ky_Fan, Orthonormal_Families, Outer_Products, Symmetric_Spectral
- Berge

The 13 maximal parents are Path_Exit_Times, Path_Tightness, Adapted_Quadratic_Variation, Conditional_UI, Natural_Filtration, Semidirect_Kernels, Modification_Transfer, Poincare_Separation, Householder_Rotation, Semicontinuity, Semicontinuous_Selection, Brownian_Finite_Dimensional_Distributions and Disintegration.

Removal experiments, each a full recheck of the six theories:
1. Removing all four candidates gave 'Undefined fact: lsc_diff_continuous' (Pair_Path_Laws:612) and 'Undefined fact: lsc_attains_inf_gen' (Pair_Path_Laws:633). Semicontinuity is NEEDED.
2. Removing only Modification_Transfer, Vitali_Convergence and Brownian_FDD left exactly 5 errors, all 'Undefined fact: sets_natural_filtration_subset' in Path_Law_Sampling at lines 52, 337, 639, 1048 and 1544; the other five theories were ok. Modification_Transfer is NEEDED.
3. Removing only Vitali_Convergence and Brownian_Finite_Dimensional_Distributions: all six theories have 0 errors, 0 failed and 0 bad (summed command time about 227 s, wall-clock at most 149 s), and the ancestor check gives 416 ancestors with SOVA = []. Both imports are UNNECESSARY.

Downstream (extra check): in the real session, Path_Tightness_Market and Exit_Time_Semicontinuity would also lose SOVA ancestry. I copied both on top of the reduced toolkit, qualifying their heap imports Ito_Market and Value_Function_Market and adjusting one @{theory} antiquotation to the unqualified name; both changes are artifacts of the copy setup. Both check with 0 errors and 0 bad, and the ancestor check gives 437 ancestors with SOVA = [].  
  Impact (lines): 17. Only Vitali_Convergence and Brownian_FDD were tested by actual removal. The other maximal parents (Householder_Rotation, Poincare_Separation, Semicontinuous_Selection, Disintegration, ...) appear to be used according to a grep (rotm_vec_cont, norm_outer_prod, ennreal_strict_between, marginal_measure/measure_disintegration), but I did not test removing them. The 22 implied imports can be removed with no change in behaviour, since make_parents already discards them; deleting them is cosmetic and saves roughly 15 import lines. The Wiener_Measure session is still needed by Brownian_Market (Wiener_Measure.Continuous_Brownian_Motion).


## comparison-rebase: can the off-diagonal step of the live comparison (comparison_two_domain -> comparison_2dom_off_diagonal -> comparison_supconv_maximiser_complete_gen -> ...) be rebased on Crandall_Ishii_Sums.theorem_on_sums_quadratic_closed by a penalty-majorant reduction, and how much would it save?

Feasible: yes. I wrote a sorry skeleton in /tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad/verify/comparison-rebase/CIS_Rebase.thy (imports Second_Order_Viscosity_Analysis.Crandall_Ishii_Sums and Relative_Arbitrage.Comparison_Two_Domain). In PIDE session "ra" it ends with 0 errors, 0 failures and 9 bad commands, all of them deliberate sorries. theorem_on_sums_quadratic_closed applies to the shifted and capped instance with OF and no error. The off-diagonal contradiction (c) is fully proved from the sorried lemmas. A drop-in theorem was checked by an ML aconv test to have exactly the same proposition as comparison_2dom_off_diagonal, so comparison_two_domain would go through unchanged.

The size argument does not hold up. A name-based reachability analysis from the Statement theories says the rebase would make about 3,344 lines dead; realistically about 2,900-3,200, because some helpers would be refactored rather than deleted. That is in line with the reviewer's 2,500-3,500. But the rebase also needs about 500-800 new proof lines, and it brings about 3,191 lines into the live path that are currently not on it (Crandall_Ishii_Sums plus support). So the code the main theorem depends on does not shrink; it grows by roughly 300-600 lines. Simply deleting the unused Crandall_Ishii_Sums.thy removes about 2,639 lines with no new work, nearly the same total as the rebase (about -2,700).

Recommendation: keep the current proof. Either delete Crandall_Ishii_Sums.thy or keep it as a standalone library result that nothing depends on. Separately, the compact-uniqueness branch (theorem_1_1_uniqueness_general) is not reachable from the Statement. About 1,739 lines are reachable only from it, and they can go regardless of this decision. Only rebase if matching the paper's citation of the theorem on sums [CI90] is worth about 600 lines of new work.

- **[confirmed]** A rebase of comparison_2dom_off_diagonal (the off-diagonal premise that comparison_two_domain uses) on theorem_on_sums_quadratic_closed via a penalty-majorant reduction typechecks and can replace the current lemma without touching comparison_two_domain.  
  Evidence: CIS_Rebase.thy in session 'ra' ends with 0 errors, 0 failures and 9 bad commands, all deliberate sorries: (a0) at line 15, GLUE1-4' at lines 54/58/60/62/72/74, (b1) at line 94, (b2) at line 110.
- comparison_2dom_off_diagonal_cis, with the exact assumptions of comparison_2dom_off_diagonal, is proved with no sorry from (a), (b1), (b2), the 4 proved matrix-bookkeeping lemmas and ell_op_env_strict_contradiction.
- comparison_2dom_off_diagonal_replacement is proved 'by (rule comparison_2dom_off_diagonal_cis[OF assms])'.
- An ML_val check, 'Thm.prop_of @{thm comparison_2dom_off_diagonal} aconv Thm.prop_of @{thm comparison_2dom_off_diagonal_replacement}', printed SAME STATEMENT.
- Inside the proof of (a), 'theorem_on_sums_quadratic_closed[OF usc1 lsc1 bu1 bw1 kap mx1 l0 la1]' was accepted. The instance is u1 x = (if x in cball xh r then A x - g.x else C1) and w1 y = (if y in cball xh r then -Bf(y-d0) - g.(y-d0) else C2), with d0 = xh-yh, g = Gf d0 and alpha = kappa. Both jets then sit at xh with gradient kappa*(xh-xh) = 0.
- (c) instantiates (a) with Pn = soft_pen kP, Gf = soft_grad kP, Zf = soft_hess kP, kappa = kP, r = kg, lam = 1/(4 kP). It uses the existing soft_pen_semiconcave, soft_pen_jet_field, supconv_continuous, supconv_le, cball_subset_interior_of_far_from_boundary, atu_of_positive_ball, supconv_attain_radius, supconv_radius_uniform and soft_grad_norm_pos, so 'g ~= 0' gives the off-diagonal p ~= 0.

Skeleton statements:
(a0) semiconcave_tangent_majorant: convex_on UNIV (%d. (k/2)|d|^2 - Pn d) and the Pjet expansion imply Pn d <= Pn d0 + Gf d0 . (d-d0) + (k/2)|d-d0|^2.
(a) theorem_on_sums_semiconcave_local: A and Bf continuous and bounded above, 0<k, semiconcave Pn with the jet expansion, 0<r, a local max of A x + Bf y - Pn(x-y) on cball xh r x cball yh r, 0<lam, 2 lam k<1. Conclusion: EX X Y. (Gf(xh-yh),X) : superjet_cl A xh & (Gf(xh-yh),Y) : subjet_cl (%y. -Bf y) yh & (ALL v. v.X v <= v.Y v).
(b1) closed_superjet_subsol_bound: visc_subsol k L Om u, 0<theta, kk, LL, theta*u <= Bu, 0<eps, theta*u usc, 0<rho, attainment points of supconv (theta u) eps within rho of x0 lie in Om, and (p,X) : superjet_cl (supconv (%y. theta*u y) eps) x0. Conclusion: ell_op_lsc k L p (matrix X) <= ereal theta.
(b2) closed_subjet_supersol_bound: the dual for supersol_jet, with (p,Y) : subjet_cl (%y. - supconv (-w) eps y) y0 and p ~= 0. Conclusion: 1 <= ell_op_usc k L p (matrix Y).
Proved bookkeeping: superjet_cl_lin_sym, subjet_cl_lin_sym, transpose_matrix_of_sym, psd_matrix_diff (from v.X v <= v.Y v to psd (matrix Y - matrix X)).  
  Impact (lines): 0. No conceptual obstruction was found. I checked each sorried statement by hand and believe each is true. CIS needs a GLOBAL maximum over UNIV x UNIV with u bounded above and w bounded below. The comparison only has maximality over UNIV x K' (and the linear tilt g.x is unbounded), so capping outside a ball (GLUE 1-3) is required. CIS's jets are linear maps, while ell_op takes real^n^n matrices, so a 'matrix X' conversion is needed; it is proved here.

- **[partially]** How much of (a) and (b) is real work.  
  Evidence: None of the sorried pieces was proved, so these estimates come from reading the existing proofs they would be adapted from. Each piece is routine but not one line.
- (a0) tangent majorant: 40-70 lines. Convexity plus a one-sided directional-derivative limit from the Pjet expansion, or subdiff_nonempty plus identifying the subgradient.
- GLUE1, choice of caps C1/C2 and the global-max inequality from maj+mx: 60-100 lines.
- GLUE2/2', usc/lsc of the capped functions: 20-40 lines each. usc_extend_const_below exists; the w side goes through negation.
- GLUE3, bounds: 15-25 lines.
- GLUE4/4', closed semijets are local, absorb a linear term and translate by d0: 80-150 lines. Needs re-indexing the sequences hidden under EX xs ps Xs.
- (b1)/(b2): 80-120 lines each. A one-sided-superjet variant of subsol_shifted_bound_supconv / supersol_shifted_bound_supconv_ne, attainment via supconv_attained_usc, an index shift until dist(xs i, x0) <= rho, conversion of pointwise convergence of Xs to matrix convergence, then ell_op_lsc_le_of_nearby / ell_op_usc_ge_of_nearby with ell_op_usc_eq_at_nonzero.
- (c)+(d) as written and proved: about 130 lines.
Total new code: about 500-800 lines.  
  Impact (lines): 0. (b) is the cheaper half: it is a refactor of existing code. subsol_shifted_bound_supconv only uses the upper half of its two-sided jet hypothesis, via superjet_local_max.

- **[partially]** The rebase saves 2,500-3,500 lines.  
  Evidence: Method: a name-based reachability graph over all 3,019 top-level blocks in the repo (script tools/deps.py and tools/reach.py, graph tools/graph.json), with roots = all blocks in Statement/*.thy. I replaced comparison_2dom_off_diagonal's dependencies with those of the skeleton, including theorem_on_sums_quadratic_closed.

Blocks that become dead: 81 blocks, 3,344 lines:
- Comparison_Principle: comparison_supconv_maximiser_complete_gen (494 lines).
- Comparison_Localisation, 8 blocks, 488 lines: comparison_supconv_bounded_family, comparison_supconv_sequence_complete, env_strict_contradiction_of_shifted_limits, env_strict_contradiction_of_nearby, subsol_shifted_bound_supconv, supersol_shifted_bound_supconv, supersol_shifted_bound_supconv_ne, supconv_attained_usc_family.
- Doubling_Of_Variables, 41 blocks, 1,643 lines: shifted_jensen_family_gen, tilted_doubled_jet_slices_gen, tilted_doubled_hessian_nonpositive_gen, tilted_doubled_psd_ordering_gen, doubled_supconv_jet_exists_shifted_gen, sums_psd_at_interior_max_gen, sums_matrix_inequality_gen, sums_gives_ordering_gen, sums_ordering_at_interior_max_gen, norm_block_matrices_bounded_gen, block_form_bound_fst_gen/snd_gen, penalty_gradient_nearby_upper_gen/bound_gen, jet_transfer_quadratic, mxK_of_UNIV_snd, tilt_sequence_pos/lt/tendsto, shifted_family_parameters, semiconvex_penalty_gen, doubled_penalty_jet, doubled_functional_semiconvex_gen, linear_block_*_gen, sym_block_*_gen, block_*_matrix_apply_gen, transpose_matrix_block_*_gen, diff_displacement_bound, bounded_seq_limit_point(_triple), tendsto_of_norm_bound, hessian_abs_bound_of_two_sided, convex_on_prod_diff, semiconvex_shift_perturb, shifted_annulus_bound_split_gen, doubled_jet_slice_*_gen.
- Soft_Penalty, 16 blocks, 403 lines: soft_rho_exists, soft_rsmall_of_rho, soft_hess_sym, soft_hess_bound, soft_hess_quadform_bounds, soft_grad_lipschitz, soft_shrink(_lipschitz), soft_R_lipschitz, soft_grad_split, soft_grad_norm_eq, soft_gap_pos, exists_small_rho_aux, norm_le_soft_R, abs_norm_diff_le, sqrt_norm_sq_add_one_ge_one.
- Matrix_Algebra, 11 blocks, 185 lines.
- Symmetric_Spectral, 3 blocks, 93 lines.
- Theorem_On_Sums: superjet_local_max (38 lines).
I also grep-checked the use counts of the main chain lemmas.

Counter-weights:
- The rebase makes theorem_on_sums_quadratic_closed live. Its reachable closure is 262 blocks, 9,295 lines, of which 3,191 lines are currently not reachable from the Statement.
- About 500-800 new lines are needed.
- Net repo size, with CIS kept: about -2,500 to -2,900. Net live (trusted-path) size: about +300 to +600, i.e. no reduction.
- Deleting CIS alone (2,639 lines; the only blocks reachable exclusively from it are its own) gives about the same repo saving with no new work.
- Caveat: theorem_1_1_uniqueness_general -> viscosity_uniqueness_compact -> max_principle_boundary_holds -> comparison_soft_complete -> comparison_soft_off_diagonal -> comparison_from_localised_maximiser_soft/_gen ALSO consumes comparison_supconv_maximiser_complete_gen. If that branch is kept and not rebased too, only about 25 lines become dead. The branch is not reachable from the Statement: Exit_Class_Optimizer mentions it only in text. About 1,739 lines are reachable only from it.  
  Impact (lines): 2700. Limits of the analysis: it is name-based, so duplicate names are merged and a block runs to the next header with text blocks stripped. That tends to overstate what is reachable, so the dead-code counts are on the low side. Realistic dead code is about 2,900-3,200 lines, because subsol_shifted_bound_supconv and similar would be refactored for (b), not deleted. The impact_lines figure (2,700) is the net repo reduction if CIS is kept anyway; relative to the alternative of deleting CIS, the net saving is about 0.

- **[confirmed]** Alternative recommendation: keep the current comparison proof and either delete CIS or keep it as a standalone library result.  
  Evidence: Per the graph analysis:
- Crandall_Ishii_Sums is used by nothing. Deleting it removes 2,639 lines; no other block depends only on it.
- Comparison_* has 43 blocks (3,008 lines) and Second_Order_Viscosity_Analysis has 188 blocks (6,992 lines) that are currently not reachable from the Statement. Among them, the compact-uniqueness branch accounts for about 1,739 lines reachable only from it.
- Whichever option is chosen, rebase or not, the tie between the gen-penalty Jensen machinery and comparison_supconv_maximiser_complete_gen stays until both off-diagonal consumers (comparison_2dom_off_diagonal and comparison_soft_off_diagonal) are rebased or removed.  
  Impact (lines): 2639. Recommended order:
1. Delete Crandall_Ishii_Sums.thy, or move it to a separate library session clearly marked as not used. It saves about 2,639 lines with no risk.
2. Separately, decide whether theorem_1_1_uniqueness_general is wanted. If not, delete the compact-uniqueness branch (about 1,739 exclusive lines).
3. Do the CIS rebase only if paper faithfulness (Theorem 4.2 via the theorem on sums [CI90]) is valued over size. It is feasible: about 500-800 new lines with no conceptual obstacle, and the skeleton above is a ready plan.
