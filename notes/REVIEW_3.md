# Review III: faithfulness, dead code, clones, generalisation, session structure

Date: 2026-10-07. Commit reviewed: `3bc3803`. Companion plan: `notes/PLAN_RESTRUCTURING_3.md`.
Data, scripts and the full per-cluster findings: `notes/review_3/`.

This review asked five questions of the whole development (8 sessions, 112 theories,
120 625 lines):

1. Is the proved theorem faithful to the paper?
2. What can be generalised or simplified?
3. What is proved more than once?
4. Is every result in the right session, and are these the right sessions?
5. If not, what is the plan?

The short answers:

1. **Yes, with one real gap in the headline formula and several gaps in the evidence and the prose.**
   Every definition reachable from `theorem_1_1` matches the paper. The formula assumes
   `expandable K` and `K ≠ {}` for all five clauses, but the paper assumes its `T_ι`
   hypothesis only for uniqueness. A strengthened theorem with the paper's hypothesis
   structure was proved in PIDE in 60 lines from existing lemmas.
2. **About a quarter of the code is not used by any deliverable** (≈31 000 lines). The
   other large items:
   - one 1 100-line proof that has a 69-line replacement (verified);
   - a probability-free half of the paper session that is built after the whole probability stack (verified);
   - three generalisations the data supports: the abstract constraint set, an abstract
     geometric operator, and the paper's own generality for Lemmas 2.2 and 2.3.
3. **Yes, at three levels.** About 50 statement-level duplicates and library re-proofs
   were found by higher-order matching, and 12 of them were re-derived in one to ten lines
   in PIDE. About 30 proof-level twins were found by reading. The largest twin is a complete
   second formalisation of the problem, the "market" layer (≈5 000 lines), which nothing uses.
4. **No.** Library sessions still hold paper material, and the paper session still holds
   library material. About 45 % of the paper session's build and 87 % of
   `Continuous_Path_Spaces`' build re-checks sessions that are not ancestors.
5. **See `PLAN_RESTRUCTURING_3.md`.** It splits the paper session along the paper's own
   seam: Sections 2–3 are probabilistic, Section 4 is pure PDE. It rebases two library
   sessions and works in phases, each ending in a green build of the Statement session.

---

## 0. Method (reproducible)

| step | tool | output |
|---|---|---|
| full build of all sessions with heaps | `isabelle build -b -d . -o threads=3 Relative_Arbitrage_Statement` | timings in `review_3/data/build_timings.txt`, re-check costs in `recheck_costs.txt` |
| PIDE session on the `Relative_Arbitrage_Statement` heap | PIDE MCP | all ML below runs in it |
| oracle check | `Thm_Deps.all_oracles` on `theorem_1_1`, `example_3_1_closed_form` | **none**: no `sorry`, no `skip_proof`, no axiomatization anywhere |
| dependency closure | `Proofterm.fold_body_thms` from the six deliverables (Theorem 1.1, Example 3.1, the four `Paper_Readings` theorems) | `facts.tsv`: every user fact with its direct named dependencies and statement constants |
| dead code | facts outside the closure, mapped to source lines | `dead_code_by_theory.txt` |
| clones | every proper fact in scope (59 574 after filtering) indexed in a discrimination net on its conclusion; each user fact matched by `Pattern.match` against them, premises as a subset | `clones.tsv` (420 pairs) |
| lowest legal home | greatest fixpoint: a fact can live in session S if its statement constants and direct dependencies are visible from S or can move with it | `placement.txt`, `probability_free_whatif.txt` |
| actually needed imports | the theories that supply a used fact or constant, compared with each `imports` line | `actual_imports.txt`, `critical_path.txt` |
| line-by-line reading | 17 readers, one per cluster of theories, every line read | `data/reader_findings_by_cluster.md` (446 findings) |
| verification | 6 PIDE agents: dry runs of two session splits, a short proof, 8 library and 8 internal clone derivations, a rebase skeleton | `data/verification_results.md` |
| faithfulness checks | `review_3/Faithfulness_Checks.thy` (checked in PIDE, not part of any session) | §1 |

`review_3/Review_Analysis.thy` and the Python scripts beside it regenerate every table.
Two caveats apply to the semantic analyses:

- They see named facts and constants. They do not see notation, abbreviations (unfolded at
  parse time), type-class instances or document antiquotations. Every import or move they
  suggest therefore needs a build to confirm, and the two dry runs below did exactly that.
- "Outside the closure" means *not needed by a deliverable*, not *delete*. Library sessions
  legitimately hold results this paper does not use, and faithfulness evidence is outside the
  closure only because no deliverable cites it (§1.3).

---

## 1. Faithfulness to arXiv:2512.17702

### 1.1 What matches

Each definition reachable from `theorem_1_1` was read against the paper. All agree:

| paper | formal | verdict |
|---|---|---|
| Eq. (1.9) `F(p,M) = inf{−½tr(Ma) : a ⪰ 0, ap = 0, λ_(n−k)(a) ≥ 1, λ_(1)(a) ≤ L}` | `ell_op`, `feasible`, `psd`, `eigen_lb` (Courant–Fischer form), `eigen_ub` | faithful; `eigen_lb_iff_eigval_ge` proves the Courant–Fischer reading equals `λ_(n−k) ≥ 1`, but nothing cites it (§1.3) |
| Eq. (1.5) `Π_m(a) = inf{tr(aP) : P² = P, tr P = m}` | `Pi_proj` over *orthogonal* projections | faithful under the documented orthogonality reading (§1.2) |
| Eq. (1.7) the class `𝒫_x` | `xclass`: laws on `C([0,∞), ℝⁿ)`, `X` a martingale for its natural filtration, some `A` with `X Xᵀ − A` a martingale, `A` absolutely continuous on compacts with a.e. derivative in `S` (`density_cond`) | faithful; since commit `614ecf8` the derivative reading is the paper's own |
| Eq. (1.6) `v(x) = sup_{P∈𝒫_x} P-ess inf τ_K` | `xval` = `Sup (ess_inf Q (iexit K))` | faithful; `iexit` is the uncapped first exit time |
| Def. 3.1 (sub/super, zero boundary condition, `u*`, `u_*`, `F_*`, `F^*`, `C²(ℝⁿ)` test functions, global touching on `K`) | `visc_subsol_env2`, `visc_supersol_env2`, `lsc_envK`, `ell_op_lsc`, `ell_op_usc`, `test_fun_C2` | faithful; envelopes taken within `K` (§1.2) |
| Theorem 1.1, clauses (0)–(4) | `theorem_1_1` | faithful in content; hypotheses too strong (§1.2) |
| Example 3.1 | `example_3_1_closed_form` | faithful, for every `1 ≤ k < n` |
| `T_ι` hypothesis | `expandable` (weaker; `paper_expandable_imp_expandable` proved) | faithful (formal hypothesis is weaker, so the theorem is stronger) |

Checked mechanically:

- `Thm_Deps.all_oracles [theorem_1_1, example_3_1_closed_form] = []`.
- No `axiomatization`, `sorry`, `oops` or `ML` escape hatch exists in any user theory.
- The build succeeds with `quick_and_dirty` off.

### 1.2 Gaps

**(a) The headline formula is weaker than the paper's theorem.** `theorem_1_1` assumes
`expandable K` and `K ≠ {}` for all five conjuncts. The paper assumes the `T_ι` family only
for uniqueness ("Suppose, *in addition*, …") and never assumes non-emptiness. The clause
lemmas in `Statement_Auxiliary` already hold for every compact `K`, so this is a defect of
assembly, not of the mathematics. The fix is checked in PIDE as
`Faithfulness_Checks.theorem_1_1_strong` (60 lines, 0 errors):

- clauses (0)–(3) hold for every compact `K`;
- clause (4) is `expandable K ⟶ …`;
- `K ≠ {}` is gone (case split; uniqueness is vacuous on `∅`).

**(b) "F reads only the symmetric part of M" is asserted, not proved.** The statement
document justifies taking `F_*`, `F^*` over `ℝⁿ × ℝⁿˣⁿ` instead of the paper's `ℝⁿ × 𝕊ⁿ`
by "F factors through M ↦ (M+Mᵀ)/2". Two theories have a `section` with that title and no
lemma in it.

The lemma existed once: `notes/UNUSED_THMS.md` records that a dead-code pass deleted the
`sym_part` cluster, `ell_op_image_sym` included, because no proof used it. It is re-proved
as `Faithfulness_Checks.ell_op_sym_part` (25 lines).

**This is the most important process finding of the review:** faithfulness evidence must be
a root of every dead-code pass (plan phase 1).

**(c) The documented reading of Eq. (1.5) is justified by a false claim.** The statement
says that under the literal reading (`P² = P` without symmetry) "S and every `𝒫_x` would be
empty whenever k ≤ n−2". This is false:

- For `a = cI`, `tr(aP) = c·tr P = cm` for *every* idempotent `P` of trace `m`, so the
  identity satisfies the literal constraint. This is checked as
  `literal_reading_keeps_identity`, and Brownian motion lies in the literal `𝒫_x`.
- What the literal reading actually does is send `Π_m(a)` to `−∞` for every non-scalar `a`
  and `k < m < n`. That collapses `S` to `{cI : 1 − k/n ≤ c ≤ L}`, contradicts Lemma 2.1,
  and changes `v`.

So the orthogonal reading is still the right one, for a different reason. The same false
sentence is in `Statement/theorem_1_1_unfolded.html`.

**(d) Other readings and their status.**

- **Envelope within `K`:** settled and checked (`Paper_Readings`).
- **`T_ι` read on the data:** settled and checked.
- **Absolute continuity of `⟨X⟩`:** this is how `d⟨X⟩/dt` is read, and it is now the
  definition itself. But the prose in `Theorem_1_1_Statement.thy` lines 55–69 still
  describes the older difference-quotient definition. It also asserts, unproved, that a
  singular part "only makes `X` exit sooner, so the value function is unaffected". That
  sentence should go.
- **`density_cond_def` is not displayed** in the statement document, although `xclass_def`
  uses it.

**(e) Paper results the formalisation states in a weaker form or not at all.** None affects
Theorem 1.1. All matter for a faithful *library* of the paper:

- **Theorem 4.2(a)** is formalised with an extra continuity hypothesis on `u` and `w`
  (`max_principle_boundary_holds`), and nothing uses it. Theorem 4.2(b), 4.3 and
  Proposition 4.1 are faithful and on the path.
- **Lemmas 2.2 and 2.3** are proved only for `S = sconstraint k L`. The paper states them
  for any bounded (resp. compact convex) `S ⊆ 𝕊ⁿ₊`; see §5, G-B.
- **Proposition 2.4**, the dynamic programming *equality* with attainment by optimisers, is
  never stated. The two halves the value-function proofs need are proved, and the remaining
  combination is short. `Relative_Arbitrage/document/root.tex` nevertheless says the DPP
  "is proved here in full".
- **Lemma 2.1** (convex hull) is proved as `lemma_2_1_exact`, but no deliverable cites it.
- **Section 5** (continuity of `v` for convex `K`: Propositions 5.1 and 5.2, Lemma 5.3, and
  Propositions 5.4 and 5.5) is not formalised at all. No README or ROOT says so.
  - Proposition 5.1 (continuity on the interior) is the dilation argument of Theorem 4.3
    followed by Theorem 4.2(b). Both ingredients are formalised: `comparison_two_domain`
    and the scaling lemmas of the operator. So Proposition 5.1 and its corollary 5.2 are
    likely short.
  - Lemma 5.3's deterministic core, `eigen_lb_dim_obstruction`, is listed as done in
    `notes/STATUS.md`, but it no longer exists in any theory. It was removed before the
    repository's history begins, and `notes/UNUSED_THMS.md` does not record it.
  - Propositions 5.4 and 5.5 defer to another paper "word by word".

**(f) Prose that is wrong (selection).**

- `Relative_Arbitrage/document/root.tex`: "whose instantaneous covariation has its *k
  smallest eigenvalues* bounded below". The condition is `λ_(n−k) ≥ 1`, i.e. the `n−k`
  largest eigenvalues.
- `theorem_1_1_iexit`'s clause (0) comment says the real bound "also says the value is
  finite". `enn2real ⊤ = 0`, so it does not. `theorem_1_1` itself is correct here.
- `NOTES_FOR_AUTHORS.md`:
  - cites `Value_Function_Viscosity`, which no longer exists;
  - says "whenever the horizon does not bind", which is stale since the infinite-horizon bridge;
  - says the library sessions "mention nothing of this paper". 119 lines in 28 library
    theories do.
- `Exit_Time_Semicontinuity` (lines 83–85, 1893) says "the paper's class (1.7) consists of
  stopped markets". `Exit_Class_Limits` says the opposite, correctly.
- "Eq. (1.10)" is used for the zero boundary condition in five places. It is the
  geometric identity of Remark 1.1(b).

### 1.3 Evidence that exists but is dead

Each of the following lemmas closes a faithfulness question, and none is reachable from
`theorem_1_1`, so the next dead-code pass would delete them:

- `eigen_lb_iff_eigval_ge` (Courant–Fischer reading);
- `lemma_2_1_exact` (Eq. 1.5 is the convex hull of Eq. 1.4);
- `poincare_separation`;
- `convex_expandable` (the uniqueness hypothesis is not vacuous);
- `paper_class_marginal` and `paper_class_lift` (the class bridge).

They belong in `Paper_Readings` (plan phase 1).

---

## 2. Dead code

Facts outside the closure of the six deliverables, by session. Lines are estimated as the
extent to the next top-level command, and blocks shared with a used fact are counted as live.

| session | lines | outside closure | largest blocks |
|---|---:|---:|---|
| `Symmetric_Matrix_Spectra` | 7 601 | ~1 059 (14 %) | `Ky_Fan` 315, `Matrix_Algebra` 368, `Poincare_Separation` 246 |
| `Semicontinuous_Analysis` | 2 318 | ~311 (13 %) | `Berge` 218 (a second, type-class Berge theorem) |
| `Second_Order_Viscosity_Analysis` | 18 473 | ~6 323 (34 %) | `Crandall_Ishii_Sums` 2 502 (**whole theory**), `Doubling_Of_Variables` 1 988, `Theorem_On_Sums` 607, `Test_Functions` 303, `Viscosity_Solutions` (**whole theory**) |
| `Continuous_Time_Martingales` | 9 281 | ~1 011 (11 %) | `Quadratic_Variation` 300 (stopped section), `Moment_Bounds` (**whole theory**) |
| `Wiener_Measure` | 3 801 | ~997 (26 %) | `Vector_Brownian_Martingales` 377 |
| `Continuous_Path_Spaces` | 13 517 | ~4 047 (30 %) | `Path_Tightness` 2 353 (projective limit, continuous modification, scalar tightness), `Stopped_Localization` 410, `Pathwise_Quadratic_Variation` 315 |
| `Relative_Arbitrage` | 64 967 | ~17 208 (26 %) | see below |
| `Relative_Arbitrage_Statement` | 667 | ~43 | 7 of 14 re-exports in `Statement_Auxiliary` |
| **total** | **120 625** | **~31 000 (26 %)** | |

Inside `Relative_Arbitrage`:

- **The market layer: 8 theories, ≈5 600 lines, zero facts used.** These are
  `Volatile_Market`, `Ito_Market`, `Brownian_Market`, `Optimal_Exit_Time`,
  `Brownian_Optimal_Boundary`, `Value_Function_Market`, `Path_Tightness_Market` and
  `Exit_Time_Semicontinuity`. They are a second formalisation of the problem over abstract
  markets, with its own value function, compactness and semicontinuity. It is still on the
  build's critical path, because `Exit_Class_Limits` imports `Exit_Time_Semicontinuity` for
  nothing.
- **Theorem 4.2(a) and the quadratic-penalty route to it** (`Comparison_Principle` 1 281,
  `Comparison_Localisation` 722, `Comparison_Strictness` 467). The compact-uniqueness
  branch (`theorem_1_1_uniqueness_general`) alone holds ≈1 740 lines reachable from nothing
  else.
- **Abandoned constructions:**
  - the simple-stopping-time kernel route in `Dynamic_Programming_Kernels` (1 059);
  - the ball-version Euler chain plus the plain (non-envelope) Case 1 (≈1 600 across
    `Value_Function_Euler_Construction`, `_Supersolution_Case_1` and `Pair_Path_Laws`);
  - the deterministic-time quadratic subsolution chain (`Value_Function_Subsolution` 822);
  - the smooth ball-solution strand (`Viscosity_Ball`, `Viscosity_Comparison_Interface` and
    9 of 11 facts of `Ball_Solution`).
- **Two theories with no lemma at all:** `Comparison_Jets` (48 lines) and
  `Dynamic_Programming_Optional_Sampling` (33). Both still sit in the import chain.
- **148 of the 342 user-defined constants never occur in the closure.**

One hazard for deleting any of this: `Viscosity_Comparison_Interface` (dead) contains a
global `declare transpose_matrix_vector [simp del]`. Every downstream theory currently
inherits it, so deleting the theory can change simp behaviour elsewhere. Move the
declaration to wherever it is needed first.

---

## 3. Clones

### 3.1 Re-proofs of library facts

Found by matching or by reading, and re-derived in PIDE (`data/verification_results.md`):

| repository lemma | library fact | derivation |
|---|---|---|
| `Covariation_Density.lipschitz_imp_absolutely_continuous_on` (42 lines; text says "not in the distribution") | `Absolute_Continuity.Lipschitz_imp_absolutely_continuous` | `rule`, 1 line |
| `Exit_Class_Witness.bm_coordinates_indep` (26 lines; text says "not in scope") | AFP `indep_vars_PiM_coordinate` (`BMC.` instance) | 2 lines |
| `Martingale_Algebra.martingale_add`, `martingale_diff` (text: "the AFP entry does not record") | AFP `martingale.add`, `martingale.diff` (more general) | 1 line each |
| `Path_Tightness.continuous_map_real_diff` (text: "missing in library") | `continuous_map_diff` | 1 line |
| `Doubling_Of_Variables.norm_Pair_le` — **same name, shadows HOL's** | `Product_Vector.norm_Pair_le` | 1 line |
| `bm_prj_measurable`, `prob_space_pair_measure`, `integral_of_bounded_linear`, `trace_diff_matrix`, `inner_sum_scaleR_Basis`, `abs_norm_diff_le`, `norm_Pair_left/right_zero`, 8 `Matrix_Algebra` distributivity lemmas | `borel_measurable_nth`, `prob_space_pair`, `integral_bounded_linear`, `trace_sub`, `inner_sum_left_Basis`, `norm_triangle_ineq3`, `norm_Pair1/2`, `Finite_Cartesian_Product` | matcher (`EQUIV`/`INSTANCE`) |
| `Path_Law_Pasting.AE_integrable_ksemi_section`, `integral_ksemi_real` | AFP Disintegration `prob_kernel.integrable_kernel_integrable`, `integral_fst` | partial: needs a 20-line bridge `ksemi` is a disintegration, and σ-finiteness (true at every call site) |
| `Path_Stopping_Times.pre_sigma_of` | HOL-Probability `filtration.pre_sigma` | partial: equal for nonnegative stopping times of a sub-filtration (40-line bridge) |
| `Path_Tightness` `dyadic_ext` continuous modification (dead anyway) | AFP `Kolmogorov_Chentsov.continuous_modification` | reader |
| `Quadratic_Variation` stopped-martingale section (dead) | AFP Fair_Games_Theorem `stopped_process_submartingale` (sub-martingales only) | partial: 16-line re-derivation |

Three of these carry prose claiming the library lacks the fact. The claim is false in all
three.

### 3.2 Internal duplicates and special cases (statement level)

From the matcher (≈50 genuine pairs after removing interpretation-generated locale facts)
and re-derived in PIDE:

| clone | of | original proof | derivation |
|---|---|---:|---:|
| `exit_val_boundary_zero` | `exit_val_le_ball_bound` | 100 | 5 |
| `diffquot_all_of_rational` | `diffquot_all_of_rational_ge` (`r = 0`) | 85 | 1 |
| `exit_val_visc_subsol` | `exit_val_visc_subsol_any` (`Ω = interior K`) | 95 | 1 |
| `exit_val_attained` | `exit_val_measurable_selector` | 66 | 5 |
| `feasible_scale`, `feasible_scaleR_p`, `feasible_scale_p` (3 theories) | each other | — | 1 |
| `ell_op_scale_p` = `ell_op_scaleR_p`; `ell_op_dilation` = `ell_op_scaleR_matrix` | each other | 51 | 1 |
| `outerp_eq_outer_prod` in `Exit_Class` and in `Pair_Path_Space` | — | — | name clash |
| `bmpair` package (334 lines) | `sbmpair (mat 1)` | 334 | `bmpair_eq_sbmpair` by `ext`/`simp` |
| `doubling_maximiser_exists`, `tilted_doubled_hessian_nonpositive` | their `_gen` versions | 44 + 51 | 1 each |
| `sym_inner_swap` = `inner_matrix_sym` = `matrix_symmetric_swap`; `onormal_parseval` = `parseval_onormal`; `quadform_sum_outer` = `quadform_weighted_outer_sum_eq`; `zero_le_fourth` = `pow4_nonneg`; `quadratic_test_grad_derivative` (SMS) instance of `quadratic_grad_derivative_at` (SOVA) | — | — | matcher |

### 3.3 Proof-level twins (same argument for different objects)

Statement matching cannot see these. They are reported by the readers, with locations in
`data/reader_findings_by_cluster.md`.

| twin | size | remedy |
|---|---:|---|
| market layer vs class layer: Example 3.1 upper bound, zero on the sphere, Brownian non-emptiness, Lemma 2.2 extraction, clause (1) via Berge, Lemma 2.3 test-to-event upgrade, translation invariance | ≈3 500 | delete the market layer |
| `X` vs compensated process `outerp X − Y`: 7 pairs in `Path_Law_Sampling`, plus `Dynamic_Programming_*`, `Exit_Time_Semicontinuity` | ≈2 450 | one lemma over a continuous `f` of the stopped path |
| coordinate weak-limit chain (`Pair_Path_Space`, `Exit_Class_Limits`) vs the generic `F`-chain beside it (`martingale_F_limit`, already used for the compensated clause) | ≈1 260 | instantiate `F := λp. fst p $ i` |
| quadratic vs general penalty through `Doubling_Of_Variables`/`Theorem_On_Sums` | ≈1 400 | keep `_gen`; the quadratic copies are dead or one-line instances |
| ball vs region Euler limit chain | ≈1 250 | the ball chain is dead |
| optional sampling by dyadic approximation in CTM and again (more generally) in `Path_Stopping_Times` | ≈600 | one theorem, in CTM |
| "approach `t` from below" continuity argument, six copies | ≈480 | one lemma |
| sup-convolution attainment, four proofs and seven corollaries | ≈470 | `supconv_attained_usc` in `Sup_Convolution` |
| `tanp`/`uvec` vs `tanpU`/`uvecV` (`P = mat 1`) | ≈500 | generalise with a centre `y0` |
| deterministic-time DPP `≥` half (kernel route) vs the stopping-time half at constant `θ` | ≈350 | derive the former |
| plain vs envelope Case 1 | ≈300 | the plain one is dead |
| martingale square, norm vs coordinate (WM) | ≈300 | one lemma over a bounded linear functional |
| `exit_val_ball_lower_plus` vs `exit_val_ball_lower_subspace` | ≈230 | one lemma |
| increment independence, three proofs (WM and `Exit_Class_Witness`) | ≈200 | one lemma |
| CTM: sampling a martingale on a grid, four proofs; five dyadic-grid constructions | ≈440 | one `Dyadic_Grids` theory |
| `iexit_class_qvmat` vs `xclass_qvmata` | ≈150 | one AE lemma next to `qvmat_eq_A_localised` |

### 3.4 Predicate variants

`Viscosity_Definitions` has ten viscosity predicates, varying along four axes:

- touching: ball vs `K`;
- test class: `test_fun_at` vs `test_fun_C2`;
- operator: `F`, `F_*`, `F^*`;
- function: `u` vs `lsc_env u`.

Six are on the path to Theorem 1.1. The generic layer introduced by the previous plan
(`Second_Order_Viscosity_Analysis.Viscosity_Solutions` and five `_eq_gen` bridges) is used
by nothing. It also lacks the `env2` variant the statement uses.

---

## 4. Simplifications verified or measured

| item | evidence | effect |
|---|---|---|
| `ess_inf_pexit_usc`: direct proof via `ess_inf_time_less_iff`, open sublevel sets and the open-set portmanteau, instead of the Laplace-transform route | **checked in PIDE**: 69 lines, the identical statement (`aconv`). A 65-line variant drops two hypotheses (`probs`, `prob`) and weakens `0 < T` to `0 ≤ T` | −947 lines |
| one-line derivations of §3.2 | **checked** | −750 lines |
| `theorem_1_1` assembled directly from the clause lemmas (no hidden `Statement_Auxiliary`, 7 of whose 14 re-exports are dead) | reader + closure | −150 lines; the statement document then shows what it states |
| comparison rebased on `Crandall_Ishii_Sums` | **sorry skeleton checked in PIDE**: feasible, and the replacement has the identical statement. But it needs 500–800 new lines and makes ≈3 200 currently unreachable lines live, so the live path grows | **not recommended**; keep the current proof, and delete or quarantine CIS |
| `Equicontinuity` imports `HOL-Complex_Analysis.Great_Picard` for `Arzela_Ascoli` alone | measured: 226 s CPU and 13 400 lines re-checked in every CPS build | a ~180-line local copy with attribution, or an upstream move |
| `Increment_Moments.second_moment_partition_bound` | reader: 20 lines from CTM's energy identity | −115 lines |

---

## 5. Generalisation potential

| id | generalisation | evidence | value |
|---|---|---|---|
| G-A | **The headline theorem with the paper's hypotheses** (existence for every compact `K`) | checked (§1.2a) | high, trivial |
| G-B | **Abstract constraint set** (`covariation_class S`, started under the previous plan's G11): Lemmas 2.2 and 2.3 for any bounded (resp. compact convex) `S ⊆ 𝕊ⁿ₊` as in the paper | the class chain uses closed, convex, bounded, `mat 1 ∈ S` and a diagonal bound. `sconstraint_def` itself is unfolded in only 4 theories (`Exit_Class_Witness`, `_Marginals`, `Value_Function_Euler_Construction`, `_Subsolution`). `exit_class_def` is unfolded ad hoc in 15 theories, the main mechanical cost | high: restores the paper's generality, makes the DPP a reusable theorem |
| G-C | **Abstract geometric operator** for Section 4: comparison and uniqueness for any `F` that is degenerate elliptic, positively homogeneous, continuous off `p = 0`, with `F^*(0,0) < 1`, a small-shift bound and rotation/dilation invariance | `uniqueness_expandable`'s closure (469 facts) consumes exactly 23 operator facts: 2 raw unfoldings (`ell_op_def`, `feasible_def`) and ~12 properties (`review_3/data/operator_and_class_interface.txt`) | high: a comparison principle for codimension mean-curvature-type equations |
| G-D | **Types:** ≈600 lines of SOVA statements fixed to `real^'n` mention no matrix. ≈110 path-toolkit statements are typed at a product codomain they never inspect | reader | medium |
| G-E | **Constants:** the paper's `8C²` and fourth-moment exponents are hard-wired in `Path_Tightness`/`Increment_Moments`. Rademacher is advertised for locally Lipschitz functions but assumes a global bound | reader | low–medium |
| G-F | **Hypotheses:** `ess_inf_pexit_usc` needs neither `probs` nor `prob` (checked). Theorem 4.2(a)'s continuity hypothesis is avoidable (`comparison_two_domain` already works with usc/lsc data). `jensen_lemma`'s `0 < ρ` is derivable | checked / reader | low |
| G-G | **One viscosity predicate family:** two generic definitions parametrised by test class and touching locality cover all six used variants | reader (§3.4) | medium |

---

## 6. Session structure

### 6.1 Measured

Single-parent heaps mean that every `sessions` import that is not an ancestor is re-checked
inside the importing session's build:

| session build | own theories | re-checked (CPU) |
|---|---:|---|
| `Continuous_Path_Spaces` | 129 s | Riesz_Representation 268 s, HOL-Complex_Analysis 226 s, Standard_Borel_Spaces 178 s, Levy_Prokhorov_Metric 150 s, Kolmogorov_Chentsov 34 s, Semicontinuous_Analysis 26 s → **87 % of the build** |
| `Relative_Arbitrage` | 626 s | SMS 107 s, SOVA 100 s, Disintegration 90 s, S_Finite_Measure_Monad 79 s, Kolmogorov_Chentsov 76 s, Wiener_Measure 40 s, Lower_Semicontinuous 30 s, LPM 24 s, SemiC 14 s → **≈45 %** |

Critical path through user theories:

- 577 s over 35 theories with today's imports;
- 418 s over 24 theories if every theory imported only what it uses;
- shorter still once dead theories are removed.

The chain runs `Matrix_Algebra → Theorem_On_Sums → Doubling_Of_Variables → Pair_Path_Space
→ …`, because the path toolkit imports SOVA. Verified dry run: it does not need SOVA at all,
and its only SOVA use is the shadowing `norm_Pair_le`.

### 6.2 The paper session has a probability-free half (verified)

The lowest-legal-home fixpoint found that 529 of the 1 516 paper-session facts need nothing
beyond `Symmetric_Matrix_Spectra`, `Second_Order_Viscosity_Analysis` and the two
HOL-Analysis-level theories of `Semicontinuous_Analysis`:

- all of the operator layer (Eq. 1.9, Lemma 2.1, Lemma 3.1, the envelopes);
- the viscosity predicates;
- all of Section 4.

The only external blocker is `Continuous_Time_Martingales.Integrability_Criteria.cInf_mult_pos`,
a fact about real infima.

**Dry run in PIDE:** the 16 theories, copied with that one lemma supplied locally, check
with 0 errors and 0 sorries. No ancestor comes from HOL-Probability, CTM, CPS, Martingales
or `Relative_Arbitrage`. No proof was changed; only 24 `@{theory Relative_Arbitrage.…}`
antiquotations in prose needed rewriting.

This is the paper's own seam: Sections 2–3 are stochastic control, Section 4 is pure PDE.
Today Section 4 is built after the whole probability stack.

### 6.3 Misplaced material (selection; full list in the reader findings)

**In the paper session but paper-free:**

- ≈540 lines of Brownian-motion theory in `Exit_Class_Witness`, plus the `sbmpair`
  package (→ `Wiener_Measure`);
- ≈30 matrix lemmas: `outerp` family, psd, onormal, threshold selection, rotation
  continuity, the Courant–Fischer bound `eigval_ge_of_subspace` and the general Poincaré
  separation (→ `Symmetric_Matrix_Spectra`, which advertises Poincaré separation but
  contains only scaffolding for it);
- optional sampling at a stopping time, `pre_sigma_of` and `dyceil` (→ CTM);
- `Covariation_Density` (paper-free real analysis importing `Exit_Class` for nothing);
- the QV identifications in `Pair_Path_Space` (→ CPS);
- `pball_exit` and the exit-time semicontinuity block (→ `Path_Exit_Times`, whose own text
  still points to it).

**In library sessions but paper-specific or in the wrong library:**

- `Moment_Bounds` (Eq. 2.7, dead) in CTM;
- the paper's `8C²` in `Path_Tightness`;
- 119 lines of paper prose in 28 library theories;
- the martingale fourth-moment estimate (`Increment_Moments` 1–1 975) in CPS though it is
  CTM material;
- `Stopped_Localization` and both QV theories in CPS though they do not use the path space;
- `cInf_mult_pos`, `ennreal_min_eq` and `bm_prj_measurable` in CTM's grab-bag
  `Integrability_Criteria`.

**Library sessions with the wrong parent:**

- `Semicontinuous_Analysis` is based on HOL-Probability only because of
  `Semicontinuous_Selection` (measurable selection). Its other three theories are
  HOL-Analysis-level, and the analytic half of the paper session needs exactly those.
- `Continuous_Path_Spaces` pulls in `HOL-Complex_Analysis` for one theorem.

### 6.4 Residue of earlier mechanical moves

- 168 "`X` lives in `Y`" pointer texts.
- About 60 text blocks and section headers separated from the lemmas they describe
  (`Path_Law_Pasting`, `Path_Law_Sampling`, `Dynamic_Programming_*`).
- Empty `section`s that announce theorems that do not follow (§1.2b).
- Theory names that no longer describe their content:
  - `Value_Function_Supersolution_Case_1` is mostly Euler and tangential material, and the
    live Case 1 is in `_Case_2`;
  - `Value_Function_Assembly` assembles nothing;
  - `Curvature_Operator` contains no curvature operator;
  - `Theorem_On_Sums` states no theorem on sums.
- `notes/UNUSED_THMS.md` and `notes/OPEN_ITEMS.md` name theories that no longer exist.
- A compiled `notes/restructuring_2/__pycache__/thy_parse.cpython-314.pyc` is tracked by git.

### 6.5 Were the previous plan's predictions right?

| PLAN_RESTRUCTURING_2 item | status now |
|---|---|
| §11 "promotion of the path toolkit to its own session is unblocked" | confirmed, and stronger: the toolkit needs no SOVA (dry run) |
| G2 "viscosity predicates over an abstract operator" (phase 9) | executed, but the generic layer is used by nothing and misses `env2`; G-C/G-G above is the version that pays |
| G11 "class over an abstract constraint set" | started (`covariation_class`); 15 theories still unfold `exit_class_def` |
| G4 "one essential infimum" | half done: `ess_inf_time` still duplicates `ess_inf` lemma by lemma |
| §6.3 "fresh `unused_thms` pass" | done here semantically. The earlier passes deleted faithfulness evidence (§1.2b), so the next pass needs explicit roots |
| §2.11 "the mathematics must not be improved" | this review recommends a few proof replacements (§4) because they are verified drop-ins |
