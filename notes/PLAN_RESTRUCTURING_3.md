# Restructuring plan III

Date: 2026-10-07. Written for commit `1a5b6d7`. It is the companion to `notes/REVIEW_3.md`,
whose section numbers (§) it cites, and its data is in `notes/review_3/`.

It supersedes `PLAN_RESTRUCTURING_2.md` §3 (target layout) wherever the two disagree. It
keeps that plan's §8 rules, with the amendments in §6 below.

**Status labels.** Numbers marked *measured* come from the full build and the ML analyses of
REVIEW_3 §0. Numbers marked *checked* come from a PIDE dry run or a PIDE proof. Everything
else is an *estimate*, and every phase re-measures it.

---

## 0. The answer in one page

**Are these the right sessions?** Mostly. The library split of the first two plans is
sound: matrices, semicontinuity, second-order viscosity tools, martingales, Wiener measure
and path spaces are each coherent subjects. Four things are wrong.

1. **The paper session is two developments in one.**
   - Its probability-free half (the operator of Eq. (1.9), the envelopes, the viscosity
     predicates, Example 3.1 and all of Section 4) is 16 theories, 529 facts and ≈14 000
     lines. It needs nothing beyond `Symmetric_Matrix_Spectra`,
     `Second_Order_Viscosity_Analysis` and two `Semicontinuous_Analysis` theories (*checked*,
     REVIEW_3 §6.2).
   - Today it is built after the whole probability stack, and it is re-checked in every
     paper build.
2. **The paper session still holds a library.**
   - The six-theory path toolkit (≈17 000 lines) is paper-free and needs no
     `Second_Order_Viscosity_Analysis` (*checked*, §6.1).
   - The previous plan's gate for promoting it passed (PLAN_RESTRUCTURING_2 §11), but it
     was never promoted.
3. **Three parents are wrong.**
   - `Semicontinuous_Analysis` sits on HOL-Probability for one theory.
   - `Second_Order_Viscosity_Analysis` and `Wiener_Measure` re-check, inside their own
     builds, a session they could simply extend.
   - `Continuous_Path_Spaces` re-checks `HOL-Complex_Analysis` (226 s, 13 400 lines) for one
     theorem.
4. **A quarter of the code serves no deliverable** (≈31 000 lines, REVIEW_3 §2), including a
   complete second formalisation of the problem (the market layer). Because dead theories
   sit in the import chain, they also lengthen the build's critical path.

**Target:** ten sessions. Two are new (`Path_Space_Operations` and
`Relative_Arbitrage_Equation`). Four are re-parented: `Semicontinuous_Analysis`,
`Second_Order_Viscosity_Analysis`, `Wiener_Measure` and the paper session. The Statement
session loses its hidden `Statement_Auxiliary` theory. Section 1 has the layout and
section 2 the phases. Each phase ends with every session green.

**Expected effect** (estimates; each phase re-measures):

| metric | today (*measured*) | target (estimate) |
|---|---:|---:|
| lines | 120 625 | ≈ 95 000 |
| facts outside the closure of the declared roots | 2 371 of 4 793 | < 5 % |
| paper-session build, summed CPU | ≈ 1 190 s, of which ≈ 560 s re-checks | ≈ 480 s, of which ≈ 235 s re-checks |
| rebuild after editing a Section 4 theory | whole paper session (≈ 1 190 s) | `Relative_Arbitrage_Equation` ≈ 90 s, then the paper session |
| `Continuous_Path_Spaces` build | 87 % re-checks | `HOL-Complex_Analysis` (226 s) gone |
| critical path through user theories | 577 s over 35 theories | ≤ 350 s |
| statement hypotheses | `expandable K` and `K ≠ {}` for all clauses | the paper's: compact `K` for (0)–(3), `expandable K` for (4) |

---

## 1. Target layout

```
HOL-Analysis ─┬─ Semicontinuous_Analysis ··········································┐ (sessions)
              │                                                                    │
              └─ Symmetric_Matrix_Spectra ── Second_Order_Viscosity_Analysis ── Relative_Arbitrage_Equation   [NEW, paper, probability-free]
                                                                                                   ┊ (sessions)
HOL-Probability ── Continuous_Time_Martingales ─┬─ Wiener_Measure ································┊··┐ (sessions)
                                                │                                                  ┊  │
                                                └─ Continuous_Path_Spaces ── Path_Space_Operations ── Relative_Arbitrage ── Relative_Arbitrage_Statement
                                                                              [NEW, library]          [paper, §§2–3 + assembly]
```

The solid lines are parents (heaps). The dotted lines are `sessions` imports between our
sessions, re-checked at the join. `sessions` imports of AFP entries and
`Continuous_Path_Spaces`' import of `Semicontinuous_Analysis` are omitted.

The join sits at `Relative_Arbitrage`, and it is placed so that the cheap side is the one
re-checked:

- the analytic side costs ≈ 235 s;
- the probabilistic side would cost > 1 000 s, because Riesz, Standard Borel spaces, LPM,
  Disintegration and the S-finite monad come with it.

| session | parent | `sessions` | scope (one sentence, no mention of the paper for library sessions) | est. lines | status |
|---|---|---|---|---:|---|
| `Symmetric_Matrix_Spectra` | HOL-Analysis | — | the spectral theory of real symmetric matrices that HOL-Analysis stops short of (unchanged) | ≈ 7 500 | existing; gains ≈ 30 matrix lemmas from the paper session, loses library re-proofs and unrooted dead code |
| `Semicontinuous_Analysis` | **HOL-Analysis** (was HOL-Probability) | `Lower_Semicontinuous` | upper and lower semicontinuity on metric spaces: calculus, attainment, envelopes, Berge | ≈ 1 350 | re-parented; `Semicontinuous_Selection` leaves |
| `Second_Order_Viscosity_Analysis` | **`Symmetric_Matrix_Spectra`** (was HOL-Analysis + sessions) | — | Rademacher, Alexandrov, Jensen, the Crandall–Ishii theorem on sums, doubling and penalty tools, test functions | ≈ 15 000 | re-parented; dead generic layer deleted (G-G may re-create it); CIS kept as a root (D1) |
| `Continuous_Time_Martingales` | HOL-Probability | `Martingales` | what continuous-time martingale theory needs beyond `Martingales`, now including optional sampling at a stopping time, the dyadic ceiling, the fourth-moment estimate and stopped localisation | ≈ 11 000 | existing; gains from `Continuous_Path_Spaces` and `Path_Stopping_Times`; loses `Moment_Bounds` (paper, dead) and `cInf_mult_pos` |
| `Wiener_Measure` | **`Continuous_Time_Martingales`** (was HOL-Probability + sessions) | `Kolmogorov_Chentsov` | Brownian motion and the n-dimensional process it carries, with independent increments relative to the natural filtration | ≈ 3 400 | re-parented; gains ≈ 540 Brownian lines from `Exit_Class_Witness` |
| `Continuous_Path_Spaces` | `Continuous_Time_Martingales` | `Kolmogorov_Chentsov`, `Levy_Prokhorov_Metric`, `Standard_Borel_Spaces`, `Semicontinuous_Analysis` (**no `HOL-Complex_Analysis`**) | the Polish path space, weak convergence, tightness from increment moments, quadratic variation as a path functional, exit times, measurable selection of a usc payoff | ≈ 9 000 | existing; gains `Semicontinuous_Selection` and a local Arzelà–Ascoli; loses dead `Path_Tightness` blocks and the martingale material |
| **`Path_Space_Operations`** | `Continuous_Path_Spaces` | `Symmetric_Matrix_Spectra`, `Disintegration` | cutting, restarting, stopping and gluing continuous paths and their laws, for a process and its matrix-valued covariation: the measurable infrastructure of a dynamic programming principle | ≈ 13 000 | **new**: the six toolkit theories `Pair_Path_Space` … `Path_Law_Sampling`, moved as a block (dry run *checked*) |
| **`Relative_Arbitrage_Equation`** | `Second_Order_Viscosity_Analysis` | `Semicontinuous_Analysis` | (paper) the operator of Eq. (1.9) and its envelopes, Lemma 2.1, viscosity solutions of it, Example 3.1, and the comparison principle and uniqueness of Section 4 | ≈ 9 500 | **new**: 16 theories plus `Value_Function_Tangential_Field` (dry run *checked*) |
| `Relative_Arbitrage` | **`Path_Space_Operations`** (was `Continuous_Path_Spaces`) | `Wiener_Measure`, `Relative_Arbitrage_Equation` | (paper) the class of Eq. (1.7), its compactness, the dynamic programming principle, the viscosity property of the value function, and `Theorem_1_1.thy` assembling the five clauses | ≈ 22 500 | shrinks from 64 967 |
| `Relative_Arbitrage_Statement` | `Relative_Arbitrage` | — | the statement for the authors, with `Paper_Readings` holding every faithfulness theorem | ≈ 520 | `Statement_Auxiliary` removed |
| *total* | | | | *≈ 93 000–97 000* | |

**The paper entry** is `Relative_Arbitrage_Equation` plus `Relative_Arbitrage` (plus
`Relative_Arbitrage_Statement`, which stays out of the AFP as its ROOT says). The **library
entries** are the other seven sessions. Each can be submitted on its own in dependency order,
and none mentions the paper (phase 8 removes the 119 lines that still do).

### 1.1 What moves where

| from | what | to | evidence |
|---|---|---|---|
| `Relative_Arbitrage` (`Curvature_Operator` … `Comparison_Two_Domain`, 16 theories) | operator, envelopes, viscosity predicates, Section 4 | `Relative_Arbitrage_Equation` | dry run *checked*: 0 errors, no forbidden ancestor; only `cInf_mult_pos` and 24 `@{theory}` antiquotations had to change |
| `Relative_Arbitrage.Value_Function_Tangential_Field` | 28 of 29 facts, the tangential field | `Relative_Arbitrage_Equation` | placement *measured*; the 29th fact stays in the paper session |
| `Relative_Arbitrage` (`Pair_Path_Space` … `Path_Law_Sampling`) | path toolkit | `Path_Space_Operations` | dry run *checked* without SOVA; `Vitali_Convergence` and `Brownian_Finite_Dimensional_Distributions` imports also unnecessary |
| `Continuous_Time_Martingales.Integrability_Criteria` | `cInf_mult_pos` (used only by `Operator_Envelopes`, `Comparison_Strictness`) | `Relative_Arbitrage_Equation`, its first user | grep *measured* |
| `Semicontinuous_Analysis.Semicontinuous_Selection` | measurable selection (users: `Pair_Path_Space`, `Path_Law_Pasting`, `Exit_Class_Limits`, `Exit_Class_Optimizer`) | `Continuous_Path_Spaces` | its imports are HOL-Probability + `Standard_Borel_Spaces`, both visible there |
| `Relative_Arbitrage.Exit_Class_Witness` | ≈ 540 lines of Brownian-motion theory (18 of its 33 facts can live in `Wiener_Measure`, *measured* placement) | `Wiener_Measure` | reader + placement. The `sbmpair` package (into which `bmpair` collapses, *checked*) is typed at the toolkit's `pairpath`, so it stays in the paper session or goes to `Path_Space_Operations` |
| `Relative_Arbitrage` (several) | ≈ 30 matrix lemmas: `outerp` family, psd, onormal, threshold selection, rotation continuity, `eigval_ge_of_subspace`, general Poincaré separation | `Symmetric_Matrix_Spectra` | reader (REVIEW_3 §6.3) |
| `Relative_Arbitrage.Path_Stopping_Times` | optional sampling at a stopping time (one theorem replaces the CTM and toolkit twins), `pre_sigma_of` (or the bridge to `filtration.pre_sigma`), `dyceil` | `Continuous_Time_Martingales` | reader; 40-line bridge *checked* partially |
| `Continuous_Time_Martingales` (five dyadic-grid constructions) | one `Dyadic_Grids` theory | `Continuous_Time_Martingales` | reader |
| `Continuous_Path_Spaces.Increment_Moments` lines 1–1 975; `Stopped_Localization` | martingale fourth-moment estimate; stopped localisation | `Continuous_Time_Martingales` | reader: neither uses the path space. Imports *measured*: only CTM theories and each other |
| `Continuous_Path_Spaces.Equicontinuity` | import of `HOL-Complex_Analysis.Great_Picard` | a ≈ 180-line local Arzelà–Ascoli, with attribution | *measured* cost 226 s per build |
| `Statement.Statement_Auxiliary` | `theorem_1_1_iexit` and the clause re-exports | `Relative_Arbitrage.Theorem_1_1` | reader + closure |
| `Statement.Theorem_1_1_Statement` | (stays) | | restates by `rule` |

### 1.2 What is deleted

Subject to the roots protocol (§3), which protects evidence and library deliverables:

| what | lines | why |
|---|---:|---|
| market layer: `Volatile_Market`, `Ito_Market`, `Brownian_Market`, `Optimal_Exit_Time`, `Brownian_Optimal_Boundary`, `Value_Function_Market`, `Path_Tightness_Market`, `Exit_Time_Semicontinuity` | 4 901 | zero facts used (*measured*); twins of the class layer (REVIEW_3 §3.3) |
| `Comparison_Jets`, `Dynamic_Programming_Optional_Sampling` | 81 | no lemma at all |
| smooth ball strand: `Viscosity_Ball`, `Viscosity_Comparison_Interface`, 9 of 11 facts of `Ball_Solution` | ≈ 670 | dead; superseded by Section 4 |
| `Second_Order_Viscosity_Analysis.Viscosity_Solutions` and the five `_eq_gen` bridges | ≈ 170 | dead, and lacks the `env2` shape the statement uses (G-G re-creates it properly) |
| abandoned constructions: the simple-stopping-time kernel route (`Dynamic_Programming_Kernels`), the ball Euler chain and the plain Case 1, the deterministic-time quadratic subsolution chain | ≈ 3 500 | dead |
| Theorem 4.2(a) and its quadratic route (`Comparison_Principle`, parts of `_Localisation`, `_Strictness`) | ≈ 2 400 | dead and weaker than the paper; see decision D3 |
| `Continuous_Time_Martingales.Moment_Bounds` | 94 | paper material (Eq. 2.7), dead |
| `Path_Tightness`: projective limit, continuous modification (a twin of AFP `Kolmogorov_Chentsov`), scalar tightness | ≈ 2 350 | dead in this development; scope decision for `Continuous_Path_Spaces` (D6) |
| `Quadratic_Variation`: the stopped section | 300 | dead; AFP `Fair_Games_Theorem` covers the submartingale case |
| library re-proofs (REVIEW_3 §3.1) and statement-level clones (§3.2) | ≈ 950 | *checked* derivations |
| `ess_inf_pexit_usc`'s Laplace route | 947 | *checked* 69-line replacement |
| everything else outside the closure, iterated to convergence | ≈ 4 000 | measured per pass |

---

## 2. Phases

Rules for every phase:

- **One commit per item, one build per commit.** The build is `isabelle build -b -d . -D .
  -o timeout=900`, i.e. every session in the repository, not only the Statement chain. The
  Statement build never touches library theories that no paper theory imports
  (`Crandall_Ishii_Sums`, for instance, is not checked by it), so it is not a sufficient
  test.
- **Every phase ends with these checks green:**
  - all sessions build;
  - `Thm_Deps.all_oracles` is empty on the roots;
  - `Review_Analysis.thy` re-run, with the metrics of §5 appended to the completion note.

### Phase 0 — tooling and roots (no theory changes)

1. Write `notes/review_3/roots.txt`, one fact per line, `Session.Theory.fact`. It holds:
   - `theorem_1_1`, `example_3_1_closed_form` and every `Paper_Readings` theorem;
   - per library session, the deliverables its ROOT `description` promises (at least the
     named theorems: spectral theorem, Ky Fan, eigenvalue continuity, Poincaré separation,
     Rademacher, Alexandrov, Jensen, theorem on sums, Doob, optional sampling, Vitali,
     Brownian motion and its continuity, portmanteau, tightness, exit-time
     semicontinuity, Berge, measurable selection).

   Phase 1 adds the evidence lemmas.
2. Make `Review_Analysis.thy` read the roots from that file instead of its six hard-coded
   names.
3. Add `notes/review_3/check.sh`. It runs the build, the oracle check, the closure, `dead.py`
   and `critpath.py`, and prints the §5 metrics.
4. Remove the tracked `notes/restructuring_2/__pycache__/thy_parse.cpython-314.pyc` and add
   `__pycache__/` to `.gitignore`.

**Acceptance:** `check.sh` reproduces the numbers of REVIEW_3 §2 within 1 %, with the roots
file in place of the six names. With library roots counted, the numbers will move. That is
the point: the new baseline is "dead with respect to declared deliverables".

### Phase 1 — the statement says what the paper says, and its evidence is a root

Edits are confined to `Statement/` and to the theories holding the cited lemmas. Each item
is checked text: `notes/review_3/Faithfulness_Checks.thy`.

1. Replace the five-way conjunction of `theorem_1_1` with the paper's hypothesis structure,
   as `theorem_1_1_strong`:
   - clauses (0)–(3) for every compact `K`;
   - clause (4) as `expandable K ⟶ …`;
   - no `K ≠ {}`.

   Keep the old name for the new formula. `theorem_1_1` is cited only by the statement
   document and the HTML page.
2. Add `ell_op_sym_part` (F reads only the symmetric part of `M`) next to `ell_op` in the
   operator theory. Add the corollary that at symmetric `M` the envelopes over `ℝⁿ × ℝⁿˣⁿ`
   coincide with those over `ℝⁿ × 𝕊ⁿ`. Cite both from the statement prose that today
   asserts it.
3. Add to `Paper_Readings` a section on the literal reading of Eq. (1.5) (identity in the
   literal set; a non-scalar `a` driven to `−∞`), and correct the false "S would be empty"
   sentence in `Theorem_1_1_Statement.thy` and in `theorem_1_1_unfolded.html`.
4. Display `density_cond_def`. Rewrite lines 55–69 for the absolute-continuity reading, and
   drop the unproved "a singular part only makes X exit sooner".
5. Surface the dead evidence lemmas as displayed corollaries in `Paper_Readings`, which
   makes them roots:
   - `eigen_lb_iff_eigval_ge` (λ_(n−k) reading);
   - Lemma 2.1 as an equality (`lemma_2_1_exact` + `Pi_constraint` inclusion);
   - Eq. (3.5) in the paper's displayed form (`bracket_eq_sum`);
   - `convex_expandable`;
   - `paper_class_marginal` / `paper_class_lift`;
   - `paper_expandable_imp_expandable`.
6. Move the assembly (`theorem_1_1_iexit` and the clause lemmas it re-exports) into a last
   paper-session theory `Theorem_1_1.thy`. Delete `Statement_Auxiliary`, 7 of whose 14
   re-exports are dead. `Theorem_1_1_Statement` then restates by `rule`.
7. Correct the wrong prose listed in REVIEW_3 §1.2(f):
   - root.tex "k smallest eigenvalues";
   - the clause (0) comment;
   - `NOTES_FOR_AUTHORS.md` (stale theory name, "horizon does not bind", "mention nothing
     of this paper");
   - the stopped-market claims in `Exit_Time_Semicontinuity` (deleted in phase 2 anyway);
   - "Eq. (1.10)".
8. Decide Theorem 4.2(a) (D3).
9. Decide Proposition 2.4 (D4).

**Acceptance:**

- all sessions build.
- The document displays every definition its formula mentions (scripted check: every
  constant in a displayed `_def` is displayed or comes from a library session).
- `roots.txt` contains every `Paper_Readings` theorem.
- `theorem_1_1` has the paper's hypotheses.

**Risk:** low. All new statements are checked in `Faithfulness_Checks.thy`.

### Phase 2 — dead code, by the roots protocol (§3)

Order (each a commit, each with a full build):

1. **Re-home global declarations first.** The only one found is
   `declare transpose_matrix_vector [simp del]` in `Viscosity_Comparison_Interface`
   (line 38). Find the live theories whose proofs depend on it:
   - delete the declaration;
   - build;
   - add `[simp del]` locally (`supply` / `using … by (simp del: …)`) where proofs break.

   `Brownian_Market` has an `interpretation BM2`; it is dead with its theory.
2. **Re-point the conduit importers** (table in §3). Then rewrite the antiquotations that name
   a theory about to disappear. There are 5 in live theories (*measured*):
   - `Exit_Class_Witness:32` (`Brownian_Market`);
   - `Exit_Class_Limits:83,177` (`Exit_Time_Semicontinuity`);
   - `Value_Function_Uniqueness:77` (`Viscosity_Comparison_Interface`);
   - `Viscosity_Definitions:166` (`Viscosity_Solutions`).

   Grep again for line-broken ones.
3. Delete the market layer (8 theories), the 2 empty theories, the smooth ball strand and
   `Viscosity_Solutions`.
4. Delete the abandoned constructions in the paper session (§1.2), theory by theory, highest
   line count first.
5. Theorem 4.2(a) per D3.
6. Library dead code, only with the library roots in place. `Path_Tightness`'s dead blocks
   are per D6.
7. Re-run the closure, delete what has become dead, repeat until a pass finds nothing (the
   previous plan's `unused_thms` needed four rounds).

**Acceptance:**

- Outside-closure facts are below 5 % of the total.
- No theory is empty.
- Every remaining `@{theory}` antiquotation resolves.
- The market layer, `Comparison_Jets` and `Dynamic_Programming_Optional_Sampling` no longer
  appear on the critical path.

**Expected:** −20 000 to −24 000 lines. The paper-session build loses ≈ 57 s of market CPU
and ≈ 40 s of abandoned constructions (*measured* per theory).

**Risk:** medium, mechanical. The two known traps are the `[simp del]` declaration and the
antiquotations. A third possible trap is a `lemmas` bundle or `[intro]`/`[measurable]`
declaration on a dead fact that a live proof relies on implicitly. That trap is the reason
for one commit per deletion.

### Phase 3 — import hygiene (critical path)

1. `Pair_Path_Space`:
   - drop `Second_Order_Viscosity_Analysis.Sup_Convolution` and `.Doubling_Of_Variables`,
     plus `Vitali_Convergence` and `Brownian_Finite_Dimensional_Distributions`;
   - delete the stale `@{theory}` line in `Pair_Path_Laws` (line 203);
   - delete `Doubling_Of_Variables.norm_Pair_le`, which shadows HOL's.

   All *checked*.
2. Remove the imports that are used for nothing (*measured*, `actual_imports.txt`):
   - `Exit_Class_Infinite` imports `Dynamic_Programming_Assembly`; it needs only
     `Exit_Class_Pasting`;
   - `Exit_Class` imports `Ball_Solution`;
   - `Covariation_Density` imports `Exit_Class`.
3. Reduce every imports line to the maximal parents it needs (`actual_imports.txt`). This is
   cosmetic where `make_parents` already drops the implied ones (22 of 35 in
   `Pair_Path_Space`). It is real where a theory imports something it does not use.

**Acceptance:** critical path ≤ 418 s (*measured* bound with needed imports only), and
lower once phase 2 has run. No session's ancestors change except by removal.

### Phase 4 — clones and verified simplifications

**Verified items** (*checked* in PIDE, `data/verification_results.md`). Swap them in as they
stand:

| item | change | lines |
|---|---|---:|
| `ess_inf_pexit_usc` | swap in the 69-line direct proof (identical statement). Optionally state the 65-line version without `probs`/`prob` and with `0 ≤ T`. Then delete `pstep*`, `exp_pexit_integral_liminf`, the Laplace lemmas and the CTM helpers only they use | −947 |
| `exit_val_boundary_zero`, `diffquot_all_of_rational`, `exit_val_visc_subsol`, `exit_val_attained` | one- to five-line corollaries of their general forms | −320 |
| scale lemmas (three copies each) | keep one; with `cInf_mult_pos` moved, `ell_op_dilation`'s hand-made Inf-scaling argument shrinks too | −80 |
| `bmpair` package | `bmpair_eq_sbmpair` + move the `sbmpair` package to `Exit_Class_Witness` (checked there; phase 5 moves it on to `Wiener_Measure`) | −320 |
| quadratic doubling lemmas | one-line instances of `_gen`, unless CIS needs the quadratic statement (D1) | −95 |
| `outerp_eq_outer_prod` (second copy) | delete | −2 |
| library re-proofs | `Lipschitz_imp_absolutely_continuous`, `indep_vars_PiM_coordinate`, `martingale.add/diff`, `continuous_map_diff`, and the matcher's `EQUIV`/`INSTANCE` list (REVIEW_3 §3.1). Correct the three texts that claim the library lacks these | −200 |
| `second_moment_partition_bound` | 20 lines from CTM's energy identity (reader) | −115 |

**Proof-level twins** (REVIEW_3 §3.3). Each is a **pilot with a gate**: do it, measure it,
and keep it only if net lines saved ≥ ½ of the estimate and no proof gets more than 2×
slower. Largest first:

| twin | est. | approach |
|---|---:|---|
| `X` vs compensated process in `Path_Law_Sampling` (7 pairs) | ≈ 2 000 | one lemma over a continuous functional of the stopped pair path; both are instances |
| coordinate weak-limit chain vs the generic `F`-chain (`martingale_F_limit`) | ≈ 1 260 | instantiate `F := λp. fst p $ i` |
| "approach `t` from below", six copies | ≈ 480 | one lemma in `Continuous_Path_Spaces` |
| sup-convolution attainment (four proofs, seven corollaries) | ≈ 470 | `supconv_attained_usc` in `Sup_Convolution` |
| `tanp`/`uvec` vs `tanpU`/`uvecV` | ≈ 500 | one family with a centre `y0` |
| optional sampling by dyadic approximation, twice | ≈ 600 | one theorem in CTM (phase 5 moves it) |
| CTM grid sampling (four proofs), five dyadic-grid constructions | ≈ 440 | `Dyadic_Grids` |
| deterministic-time DPP `≥` vs the stopping-time half at constant `θ` | ≈ 350 | derive the former (if not already dead after phase 2) |
| martingale square, norm vs coordinate (WM) | ≈ 300 | one lemma over a bounded linear functional |
| `exit_val_ball_lower_plus` vs `_subspace` | ≈ 230 | one lemma |
| increment independence, three proofs | ≈ 200 | one lemma in WM |
| `iexit_class_qvmat` vs `xclass_qvmata` | ≈ 150 | one AE lemma next to `qvmat_eq_A_localised` |
| `Crandall_Ishii_Sums` internal duplication (staged vs closed parameter set-up; deconvolution algebra three times) and its re-proofs of `Semicontinuity` lemmas | ≈ 420 | per D1 |

**Not done:** rebasing the comparison on `Crandall_Ishii_Sums`. The skeleton was *checked*
feasible, but the rebase makes ≈ 3 200 unreachable lines live and needs 500–800 new ones
(REVIEW_3 §4).

**Acceptance:** each pilot's measured line count and timing goes in the completion note, and
so does each abandoned pilot.

### Phase 5 — library moves and parent changes

Each move starts with a dry run: copy the theories, change the imports, load them in PIDE,
and assert the ancestors with `Theory.nodes_of`, as in REVIEW_3 §6.2. Only then edit the
repository.

1. **`Semicontinuous_Analysis` → parent HOL-Analysis.**
   - `Semicontinuous_Selection` moves to `Continuous_Path_Spaces`, ahead of
     `Path_Exit_Times`.
   - `cInf_mult_pos` moves to the paper's operator layer, whose two theories are its only
     users.
2. **`Second_Order_Viscosity_Analysis` → parent `Symmetric_Matrix_Spectra`.** It imports
   only `Symmetric_Matrix_Spectra` (*measured*). If the `Crandall_Ishii_Sums` helpers are
   de-duplicated against `Semicontinuity`, add `sessions Semicontinuous_Analysis`.
3. **`Wiener_Measure` → parent `Continuous_Time_Martingales`.** Move in the Brownian material
   of `Exit_Class_Witness`: 18 of its 33 facts, ≈ 540 lines. Fold the three
   increment-independence proofs into one there.
4. **`Symmetric_Matrix_Spectra`** gains the ≈ 30 matrix lemmas of REVIEW_3 §6.3. It loses
   the 8 `Matrix_Algebra` distributivity lemmas and `trace_diff_matrix` (library clones).
5. **`Continuous_Time_Martingales`**:
   - gains optional sampling at a stopping time, `pre_sigma_of` (better: the 40-line bridge
     to HOL-Probability's `filtration.pre_sigma`, then use that) and `dyceil`;
   - gains `Dyadic_Grids`;
   - gains the martingale part of `Increment_Moments` (lines 1–1 975) and
     `Stopped_Localization`. Both are legal there by their imports (*measured*: they import
     only CTM theories and each other). The same holds for `Pathwise_Quadratic_Variation`
     and `Adapted_Quadratic_Variation`. Moving those two is a scope decision: they are
     advertised by `Continuous_Path_Spaces` as path functionals, so the default is to leave
     them;
   - loses `Moment_Bounds`, `cInf_mult_pos` and `bm_prj_measurable` (= `borel_measurable_nth`);
   - the grab-bag `Integrability_Criteria` is split by subject or dissolved into its users.
6. **`Continuous_Path_Spaces`**:
   - drops `HOL-Complex_Analysis`: `Equicontinuity` gets a local Arzelà–Ascoli (≈ 180
     lines, attributed to `HOL-Complex_Analysis.Great_Picard`), or the theorem is offered
     upstream to HOL-Analysis;
   - generalises the paper's `8C²` in `Path_Tightness` and `Increment_Moments` to a
     parameter (G-E), or moves it into the paper session.
7. Update every ROOT `description` and `document/root.tex` to the new contents.

**Acceptance:**

- all sessions build;
- ancestor assertions hold:
  - `Semicontinuous_Analysis` has no HOL-Probability ancestor;
  - `Continuous_Path_Spaces` has no `HOL-Complex_Analysis` ancestor;
- the `Continuous_Path_Spaces` build drops by ≈ 226 s;
- in the paper-session build, `Wiener_Measure`'s re-check disappears from the
  `Continuous_Time_Martingales` side and `Symmetric_Matrix_Spectra`'s from the
  `Second_Order_Viscosity_Analysis` side.

### Phase 6 — the two session splits

Both were dry-run *checked* (REVIEW_3 §6.1–6.2).

1. **`Path_Space_Operations`.**
   - Move the six toolkit theories, as a block, into a new directory with its own ROOT:
     `Path_Space_Operations = Continuous_Path_Spaces + sessions Symmetric_Matrix_Spectra
     Disintegration`.
   - Requalify their `@{theory}` antiquotations.
   - Change the paper session's parent to `Path_Space_Operations`.
2. **`Relative_Arbitrage_Equation`.**
   - Move the 16 operator and comparison theories (fewer after phase 2) and
     `Value_Function_Tangential_Field` into a new directory with its own ROOT:
     `Relative_Arbitrage_Equation = Second_Order_Viscosity_Analysis + sessions
     Semicontinuous_Analysis`.
   - Requalify the 24 `@{theory Relative_Arbitrage.X}` antiquotations (*measured*).
   - Add `Relative_Arbitrage_Equation` to the paper session's `sessions`.
3. Add both new directories to `ROOTS`, in dependency order.
4. Add an ancestor-assertion theory to `Relative_Arbitrage_Equation` (`document = false`)
   that fails the build if any HOL-Probability theory becomes an ancestor. This keeps the
   seam honest.
5. Split `document/root.tex` along the sessions. The equation session's document reads as
   Sections 1.9, 3 (definition) and 4 of the paper; the paper session's as Sections 2–3.

**Acceptance:**

- the paper-session build re-checks ≤ 300 s (*estimate* 235 s);
- `Relative_Arbitrage_Equation` builds without HOL-Probability;
- `Path_Space_Operations` has no SOVA ancestor.

### Phase 7 — generalisations (pilots, gated)

| id | pilot | gate (stop and record if missed) |
|---|---|---|
| G-B, finishing PLAN_2's G11 | migrate the ≈ 215 `exit_class` consumers to `covariation_class S` bottom-up, one theory per commit, starting with the four reverted lemmas (`exit_class_diffquot_full_mass` …) and threading `closed S`. Then state Lemma 2.2 for bounded `S` and Lemma 2.3 for compact convex `S`, as the paper does, and the DPP for abstract `S` | after the first three theories, ≥ 80 % of their statements are `S`-generic with no proof grown by more than 20 % |
| G-B, promotion | if the gate passes, move `covariation_class` and its compactness, pasting and DPP into a library session on top of `Path_Space_Operations` (name by subject, e.g. `Covariation_Constrained_Martingales`). The paper session keeps only `sconstraint`, `xclass`, `xval` and the bridge equations | the moved statements name no paper constant |
| G-C | lift Section 4 to an abstract operator. The comparison chain consumes exactly 23 operator facts (`data/operator_and_class_interface.txt`): ellipticity, positive homogeneity, continuity off `p = 0`, `F^*(0,0) < 1`, a small-shift bound, rotation and dilation invariance. State them as a locale, prove `ell_op` an instance, and move the chain into a library session (`Geometric_Viscosity_Comparison`) | the two raw unfoldings (`ell_op_def`, `feasible_def`) inside the chain can be replaced by interface facts in ≤ 200 lines |
| G-G | one viscosity predicate family, parametrised by test class and touching locality, covering the six used variants including `env2`. It lives in SOVA (re-creating the deleted `Viscosity_Solutions` in the shape that is used) | the six paper predicates become abbreviations or one-line definitions; `Statement` still displays what the authors expect |
| G-D | widen the ≈ 600 SOVA lines fixed to `real^'n` that mention no matrix, and the ≈ 110 toolkit statements typed at a product codomain they never inspect | uniform sort per layer first (PLAN_2 §11's lesson); `-o timeout=900` |
| G-F | drop the avoidable hypotheses: `ess_inf_pexit_usc` (`probs`, `prob`; *checked*), `jensen_lemma`'s `0 < ρ` | none needed |

### Phase 8 — prose, names and notes

1. Remove or rewrite the 168 "`X` lives in `Y`" pointer texts. Reattach the ≈ 60 orphaned
   text blocks and section headers to their lemmas. Delete the empty `section`s.
2. Renames:
   - `Curvature_Operator` → `Elliptic_Operator` (it defines `eigen_lb`, `feasible` and
     `ell_op`, and no curvature operator);
   - `Theorem_On_Sums` → a name for what it holds (doubling algebra and semiconvexity
     calculus);
   - `Value_Function_Supersolution_Case_1`/`_Case_2` → names matching their content (the
     live Case 1 is in `_Case_2`);
   - `Value_Function_Assembly` → merge into its user or rename.

   PLAN_2 §8 rule 7 (no abbreviations, no filler nouns) applies.
3. Remove the paper from library sessions: 119 lines in 28 theories. Fix "Lemma 3.1 of
   LaiShkolnikovSoner" in `Theorem_On_Sums` (it is Crandall–Ishii–Lions).
4. Refresh `UNUSED_THMS.md`, `OPEN_ITEMS.md`, `STATUS.md` and `NOTES_FOR_AUTHORS.md` against
   the new layout. `STATUS.md` still lists the deleted `eigen_lb_dim_obstruction` as done.
   `OPEN_ITEMS.md` gains Section 5 (D4b). Record in `UNUSED_THMS.md` that dead-code passes run against
   `roots.txt` only.

---

## 3. The dead-code protocol (used by phases 2 and 4)

1. **Roots.** Use `notes/review_3/roots.txt`:
   - the Statement session's theorems;
   - every theorem displayed in `Paper_Readings`;
   - for each library session, the deliverables named in its `ROOT` description. Make
     these explicit in a final `<Session>_Overview.thy` per session that restates them with
     `lemmas` bundles, so that they are reachable.

   Never run a pass without explicit roots. The last pass deleted the symmetric-part lemma
   the statement's prose relies on.
2. **Compute.** Run `Review_Analysis.thy` (closure over the roots) and `dead.py`.
3. **Before deleting a theory**, grep it for global `declare`, `lemmas … [simp]`,
   `[measurable]`, `notation`, `interpretation`, `setup`. Re-home each one first. The known
   case is `declare transpose_matrix_vector [simp del]` in `Viscosity_Comparison_Interface`.
4. **Re-point the live importers that use a dead theory only as a conduit.** None of them
   uses a fact from it; each needs only the imports it delivered:

   | dead theory | live importers |
   |---|---|
   | `Exit_Time_Semicontinuity` | `Exit_Class_Limits`, `Value_Function_Uniqueness` |
   | `Value_Function_Market` | `Value_Function_Uniqueness` |
   | `Viscosity_Comparison_Interface` | `Ball_Solution` |
   | `Comparison_Jets` | `Comparison_Strictness` |
   | `Dynamic_Programming_Optional_Sampling` | `Dynamic_Programming_Stopping_Clauses` |
   | `Moment_Bounds` | `Increment_Moments` |
   | `Viscosity_Solutions` | `Viscosity_Definitions` |
5. **Delete and build.** Rewrite `@{thm}` / `@{const}` / `@{theory}` antiquotations that
   named deleted entities into plain prose (the previous plan lost a build per kind of
   antiquotation).
6. **Repeat until a pass finds nothing.** Deleting a theorem frees its private helpers; the
   previous `unused_thms` passes took four rounds to converge.

---

## 4. Decisions

**D1 — `Crandall_Ishii_Sums`: keep it, as a root of `Second_Order_Viscosity_Analysis`.**
- It is the session's advertised headline.
- It costs the paper build nothing: no paper theory imports it, and the paper session
  re-checks 11 of the 12 SOVA theories, all except this one (*measured*).
- It was the largest dead block only because no root declared it.
- What changes: its internal duplication (≈ 300 lines) and its re-proofs of `Semicontinuity`
  lemmas (≈ 120) go in phase 4. The quadratic-penalty lemmas it needs stay as roots, and
  the rest become instances of `_gen`.
- Rejected alternatives:
  - rebasing the comparison on it (*checked*: the live path grows);
  - deleting it (an AFP entry on second-order viscosity theory without the theorem on sums
    would be odd).

**D2 — the market layer: delete it.**
- It is a second formalisation of the problem over abstract markets, and no deliverable uses
  any fact of it (*measured*).
- Its paper-free fragments (an exit-time semicontinuity block, `pball_exit`) either already
  have live twins in `Path_Exit_Times`, or are moved there in phase 2 before the deletion if
  `Continuous_Path_Spaces`' roots name them.

**D3 — Theorem 4.2(a).**
- Today it is formalised with an extra continuity hypothesis (`max_principle_boundary_holds`),
  through a quadratic-penalty route of ≈ 2 400 lines that nothing else uses.
- Pilot (≤ 300 lines): derive the faithful statement (usc/lsc data, the `env2` predicates)
  from the localisation `comparison_two_domain` already uses. The paper proves (a) and (b)
  in parallel from one doubling argument, so the shared steps exist:
  - the `x^ε ≠ y^ε` contradiction from `F^*(0,0) = 0`;
  - the Crandall–Ishii step.

  If the pilot succeeds, display it in `Paper_Readings` and delete the quadratic route.
- If it fails, delete `max_principle_boundary` and its route, and say in `Paper_Readings`
  that 4.2(a) is not formalised (4.2(b), 4.3 and 4.1 are).
- Either way, a weaker theorem under the paper's name does not stay.

**D4 — Proposition 2.4 (the DPP equality with attainment).**
- Pilot (≤ 150 lines) from the two halves in `Dynamic_Programming_*` and
  `exit_val_measurable_selector`.
- If it fails, change `root.tex`'s "proved here in full" to what is proved.

**D4b — Section 5 (continuity of `v` for convex `K`): out of scope for this
restructuring, with one cheap exception.**
- None of Section 5 is formalised (REVIEW_3 §1.2e).
- Proposition 5.1 (continuity on the interior of a convex `K`) and its corollary 5.2 are a
  pilot (≤ 200 lines). The pilot runs only after phase 6, once `Relative_Arbitrage_Equation`
  exports the dilation invariance and Theorem 4.2(b) it needs.
- Lemma 5.3 and Propositions 5.4 and 5.5 are new mathematics. They are recorded in
  `OPEN_ITEMS.md`, not planned here. The stale "done" entry for `eigen_lb_dim_obstruction`
  in `STATUS.md` is corrected in phase 8.

**D5 — where Section 4 lives: its own probability-free session, parented on SOVA.**
- This is the paper's own seam, and it lets Section 4 be developed and checked in ≈ 90 s
  without the probability stack.
- *Build-time alternative*, if iteration speed on the paper session matters more than the
  visible seam: parent `Relative_Arbitrage_Equation` on `Path_Space_Operations` instead,
  and keep its theory imports probability-free.
  - The ancestor-assertion theory (phase 6.4) still guards the seam.
  - The paper session then extends it with no re-check: about 280 s instead of 480 s.
- The theory files are identical under either choice, so this can be switched by editing
  two ROOT lines.

**D6 — the scope of `Continuous_Path_Spaces`.**
- It keeps what its description promises: path space, weak convergence, tightness from
  increment moments, quadratic variation as a path functional, exit times, and now
  measurable selection.
- `Path_Tightness`'s dead projective-limit and continuous-modification blocks are deleted,
  since AFP `Kolmogorov_Chentsov` has the continuous modification. The scalar tightness twin
  is deleted.
- If the author wants a projective-limit construction in the library, it belongs in
  `Wiener_Measure`, which already builds one.

**D7 — no aggregating "base" session.**
- An intermediate session holding every library theory would only move the re-checking:
  the join has to happen somewhere.
- It also breaks PLAN_2 §8 rule 7 (no filler names).
- The layout above already places the join on the cheap side.

---

## 5. Metrics (report after every phase)

| metric | how | baseline (*measured*) |
|---|---|---:|
| total lines, per session | `wc -l` | 120 625 |
| facts / outside closure of `roots.txt` | `Review_Analysis.thy` + `dead.py` | 4 793 / 2 371 (six roots) |
| oracles on the roots | `Thm_Deps.all_oracles` | none |
| per-session build CPU; re-check CPU by originating session | `recheck_costs` from the build log | `Relative_Arbitrage` ≈ 560 s re-check, `Continuous_Path_Spaces` 87 % |
| critical path through user theories | `critpath.py` | 577 s / 35 theories |
| statement-level clone pairs (after locale filtering) | `Review_Analysis.thy` `A2` | ≈ 50 |
| `@{theory Session.X}` antiquotations (each breaks when `X` moves) | grep | 309, of which 38 name `Relative_Arbitrage` theories |
| "lives in" pointer texts; paper mentions in library sessions | grep | 168; 119 lines in 28 theories |
| statement document pages; displayed definitions missing | build + script | (record in phase 0) |

---

## 6. Rules for the executing agent

PLAN_RESTRUCTURING_2 §8 applies, with these amendments:

1. **Rule 1 ("do not prove new mathematics") is relaxed for the items marked *checked*** in
   phases 1 and 4, and for the gated pilots D3, D4, D4b and phase 7. Each of these is a
   replacement whose statement is identical (`aconv`) or stronger. Nothing else gets a new
   proof.
2. **Rule 2 is extended:** never weaken `theorem_1_1` or any `Paper_Readings` statement, and
   never delete a fact named in `roots.txt`. If a deletion needs one gone, the roots file
   changes first, in its own commit, with the reason.
3. **Build everything** (`-D .`), not only the Statement chain, after every commit.
4. **A dry run precedes every move across a session boundary** (copy, load in PIDE, assert
   the ancestors).
5. **Antiquotations are part of the move.** Grep for `@{theory`, `@{thm`, `@{const`,
   `@{locale` naming the moved or deleted entity across all sessions, including line-broken
   occurrences.
6. **The completion note records refuted predictions.** If a number in this plan is wrong,
   the plan is wrong, not the development.
