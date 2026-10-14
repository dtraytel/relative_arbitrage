# Restructuring plan III

Date: 2026-10-07. Written for commit `1a5b6d7`. It is the companion to `notes/REVIEW_3.md`,
whose section numbers (§) it cites, and its data is in `notes/review_3/`.

It supersedes `PLAN_RESTRUCTURING_2.md` §3 (target layout) wherever the two disagree. It
keeps that plan's §8 rules, with the amendments in §6 below.

**Status labels.** Numbers marked *measured* come from the full build and the ML analyses of
REVIEW_3 §0. Numbers marked *checked* come from a PIDE dry run or a PIDE proof. Everything
else is an *estimate*, and every phase re-measures it.

**Revision of 2026-10-08.** Three things changed the draft of 2026-10-07:

1. **The owner's directive on independent interest** (§1.3). The draft deleted most of what
   lies outside the closure of Theorem 1.1. The revision keeps every result of independent
   interest: Crandall–Ishii, Theorem 4.2(a), the full Lemma 3.1, the Poincaré separation and
   Courant–Fischer evidence, and natural library interface. The decision for each of the
   ≈ 840 unused items is in `notes/review_3/data/independent_interest.md`, made by one
   classifier and one adversarial verifier per cluster. The deletion estimate falls from
   ≈ 25 000 lines to ≈ 17 000, the market layer included.
2. **A design panel** of three independent session layouts and two judges (§1.4). Both
   judges chose a paper-ordered layout with a `Paper_Map` theory. The grafts they asked for
   are adopted here: a probability-free `Relative_Arbitrage_Equation` on
   `Second_Order_Viscosity_Analysis`, `Continuous_Path_Spaces` on `Levy_Prokhorov_Metric`
   with a local Arzelà–Ascoli, `Semicontinuous_Analysis` on `Lower_Semicontinuous`, the
   generic viscosity layer reworked (G-G) rather than deleted, and mandatory re-homing of
   library material before the toolkit is promoted.
3. **Execution has started** (§7, progress log). Phases 0 and 1 are done, and phase 2 has
   deleted the market layer. All sessions build after each step.

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
| lines | 120 625 | ≈ 100 000 (independent-interest keeps included; §1.3) |
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
| `Semicontinuous_Analysis` | **`Lower_Semicontinuous`** (was HOL-Probability; panel graft) | — | upper and lower semicontinuity on metric spaces: calculus, attainment, envelopes, scaling of infima, Berge | ≈ 1 400 | re-parented; `Semicontinuous_Selection` leaves; gains `cInf_mult_pos` (panel graft) and the CIS copies of its lemmas |
| `Second_Order_Viscosity_Analysis` | **`Symmetric_Matrix_Spectra`** (was HOL-Analysis + sessions) | `Semicontinuous_Analysis` | Rademacher, Alexandrov, Jensen, Minty, sup-convolution, the Crandall–Ishii theorem on sums with semijets, doubling and penalty tools, test functions, and viscosity sub/supersolutions for an arbitrary operator | ≈ 16 500 | re-parented; CIS a root (D1); the generic viscosity layer reworked (G-G, D9), not deleted |
| `Continuous_Time_Martingales` | HOL-Probability | `Martingales` | what continuous-time martingale theory needs beyond `Martingales`, now including optional sampling at a stopping time, the dyadic ceiling, the fourth-moment estimate and stopped localisation | ≈ 11 000 | existing; gains from `Continuous_Path_Spaces` and `Path_Stopping_Times`; loses `Moment_Bounds` (paper, dead) and `cInf_mult_pos` |
| `Wiener_Measure` | **`Continuous_Time_Martingales`** (was HOL-Probability + sessions) | `Kolmogorov_Chentsov` | Brownian motion and the n-dimensional process it carries, with independent increments relative to the natural filtration | ≈ 3 400 | re-parented; gains ≈ 540 Brownian lines from `Exit_Class_Witness` |
| `Continuous_Path_Spaces` | **`Levy_Prokhorov_Metric`** (AFP heap holding Standard Borel and Riesz; panel graft) | `Continuous_Time_Martingales`, `Kolmogorov_Chentsov`, `Semicontinuous_Analysis` (**no `HOL-Complex_Analysis`**) | the Polish path space, weak convergence, tightness from increment moments, quadratic variation as a path functional, exit times, measurable selection of a usc payoff | ≈ 9 000 | existing; gains `Semicontinuous_Selection` and a local Arzelà–Ascoli; loses dead `Path_Tightness` blocks and the martingale material |
| **`Path_Space_Operations`** | `Continuous_Path_Spaces` | `Symmetric_Matrix_Spectra`, `Disintegration` | cutting, restarting, stopping and gluing continuous paths and their laws, for a process and its matrix-valued covariation: the measurable infrastructure of a dynamic programming principle | ≈ 13 000 | **new**: the six toolkit theories `Pair_Path_Space` … `Path_Law_Sampling`, moved as a block (dry run *checked*) |
| **`Relative_Arbitrage_Equation`** | `Second_Order_Viscosity_Analysis` | `Semicontinuous_Analysis` | (paper) the operator of Eq. (1.9) and its envelopes, Lemma 2.1, viscosity solutions of it, Example 3.1, and the comparison principle and uniqueness of Section 4 | ≈ 9 500 | **new**: 16 theories plus `Value_Function_Tangential_Field` (dry run *checked*) |
| `Relative_Arbitrage` | **`Path_Space_Operations`** (was `Continuous_Path_Spaces`) | `Wiener_Measure`, `Relative_Arbitrage_Equation` | (paper) the class of Eq. (1.7), its compactness, the dynamic programming principle, the viscosity property of the value function, and `Theorem_1_1.thy` assembling the five clauses | ≈ 22 500 | shrinks from 64 967 |
| `Relative_Arbitrage_Statement` | `Relative_Arbitrage` | — | the statement for the authors, with `Paper_Readings` holding the checked readings | ≈ 900 | `Statement_Auxiliary` removed (done) |
| *total* | | | | *≈ 100 000* | |

**Inside the two paper sessions (panel winner, "paper-first").** Theories follow the paper's
order. A theory is named after a paper result when it holds exactly that result
(`Example_3_1`, `Proposition_2_4`, `Theorem_1_1`). A last theory `Paper_Map` holds one
`theorem` per numbered item of the paper, proved by `rule` from the working lemma, with the
deviations written beside it. `Paper_Map` is both the reader's index and the root set of
every dead-code pass. `Paper_Readings` keeps the readings of the paper's wording. Planned
renames and merges (phase 8):
- `Curvature_Operator` → `Elliptic_Operator`;
- `Comparison_Principle` → `Maximum_Principle`;
- `Eigenvalue_Bound_Exact` into `Constraint_Set_Convexity`;
- `Operator_Continuity` into `Operator_Formula`;
- `Operator_Envelope_Continuity` into `Operator_Envelopes`;
- a `Control_Problem` theory for Eqs. (1.5)–(1.7).

Constant long names change with a theory rename, so the statement fingerprint is compared
modulo the rename map.

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
| `Continuous_Time_Martingales.Integrability_Criteria` | `cInf_mult_pos` (used only by `Operator_Envelopes`, `Comparison_Strictness`) | `Semicontinuous_Analysis.Semicontinuous_Envelopes` (panel graft: a fact about real infima belongs in a library) | grep *measured* |
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

Every item below is DELETE in `notes/review_3/data/independent_interest.md`, and none is
reachable from the roots of `roots.txt`. With the independent-interest keeps as roots, the
dead code left after the market layer is ≈ 12 150 lines (*measured*, 520 roots).

| what | lines | why |
|---|---:|---|
| market layer, 8 theories | 4 901 | **done** (`4d5f47e`). A second formalisation over abstract markets with Itô's formula as a locale axiom. Only `eigen_ub_diag` was moved out; the expected-exit-time bound is re-proved generically (D2) |
| `Comparison_Jets`, `Dynamic_Programming_Optional_Sampling` | 81 | no lemma at all |
| smooth ball strand: `Viscosity_Ball`, `Viscosity_Comparison_Interface`, 9 of 11 facts of `Ball_Solution` | ≈ 670 | superseded by Section 4. The refuted `comparison_principle` locale goes with it. The global `[simp del]` affects only these two theories, because simpset merges are unions; it is not replicated (panel) |
| `Dynamic_Programming_Kernels` (12 of 13 facts) | ≈ 1 060 | abandoned simple-stopping-time kernel route |
| value-function dead blocks | ≈ 2 350 | the ball Euler chain, plain Case 1, dead `tanp`/`tanSF` lemmas, the deterministic-time quadratic subsolution chain |
| comparison dead blocks | ≈ 1 500 | the quadratic route, exact-jet closing, the diagonal `p = 0` explorations, VCI twins. **Theorem 4.2(a) and its chain stay** (D3) |
| `Path_Tightness`: projective limit, continuous modification, scalar tightness | ≈ 1 590 | twins of AFP `Kolmogorov_Chentsov` and of HOL-Probability's Daniell–Kolmogorov. **The Kolmogorov–Chentsov tightness criterion stays** (FIX_THEN_KEEP: parameter instead of `8C²`) |
| `Doubling_Of_Variables` | ≈ 1 180 | the abandoned quadratic-penalty Theorem 4.2(a) route; the `_gen` toolbox and what CIS needs stay |
| the rest outside the new closure | ≈ 2 300 | iterated to a fixpoint |
| library re-proofs and verified clones (phase 4) | ≈ 950 | *checked* derivations |
| `ess_inf_pexit_usc`'s Laplace route (phase 4) | 947 | *checked* 69-line replacement |
| COROLLARY items that keep their names | (≈ 4 000 → a few hundred) | rewritten as one- to five-line corollaries of the general result (phase 4) |

### 1.3 Independent interest (owner's directive, 2026-10-07)

> "You are keeping SOVA, in particular Crandall Ishii, as this is a theorem of independent
> interest (even though only a specific instance is useful for the paper's main theorem).
> Reconsider your deletions wrt such 'independent interest' considerations."

**Rule.** A result outside the closure of Theorem 1.1 stays when it is any of the following:
- a statement of the paper, in any section;
- a classical or named theorem, or a genuinely general result that a library user would
  look up and that the distribution and the AFP lack;
- natural interface of a constant that a library keeps.

It goes when it is any of the following:
- a private helper of something that goes;
- an abandoned proof route;
- a twin of live or library code;
- a paper-specific variant that the live route supersedes.

Kept results become roots, so their helpers become live and no later pass removes them.

**Result** (line estimates over the ≈ 31 000 unused lines):

| verdict | lines | examples |
|---|---:|---|
| KEEP_ROOT | ≈ 2 100 | Lemma 2.1 exact; Lemma 3.1 in full (Eq. (3.6)); Minty's theorem; the hypersimplex decomposition; domination of finite Borel measures by continuous tests; Galmarino's half (`pstopped_vimage_pre_sigma`) |
| KEEP_EVIDENCE | ≈ 200 | `eigen_lb_iff_eigval_ge`, `convex_expandable`, the class bridge |
| FIX_THEN_KEEP | ≈ 6 800 | Crandall–Ishii (strengthen to the CIL (3.10) block inequality); Theorem 4.2(a) (usc/lsc data); Proposition 2.4 (from `exit_val_dpp_le_of_cond`); general Poincaré separation and Courant–Fischer (move to SMS); the Kolmogorov–Chentsov tightness criterion (parameter instead of `8C²`); the fourth-moment bound for L² martingales; the process-level Lemma 2.2 `path_laws_convergent_subsequence_market` (rename, move to CPS); the expected-exit-time bound (re-prove in CTM) |
| KEEP_API | ≈ 2 200 | semijet monotonicity, sup-convolution Lipschitz/convergence facts, `covariation_class` introduction/elimination, measurability of `qvps`/`qvmat`, `psd_diag_nonneg` |
| COROLLARY | ≈ 4 000 | special cases of live `_gen` lemmas: become one-liners or go |
| DELETE | ≈ 15 400 | market layer, abandoned routes, twins |

The review also found **six advertised library deliverables with no theorem behind them**
(`notes/review_3/data/library_deliverables.md`):
- general Poincaré separation and Courant–Fischer in SMS;
- Rademacher for locally Lipschitz functions;
- the theorem on sums with a general coupling at a local maximum;
- Vitali for convergence in probability;
- Doob's continuous-time weak inequality.

Each is either delivered (FIX_THEN_KEEP above) or its description is corrected in phase 8.

### 1.4 The design panel

Three designers worked independently: **afp-first** (maximise submittable libraries),
**build-first** (minimise build and iteration time) and **paper-first** (mirror the paper,
minimise migration risk). Two judges then scored all three: one through engineering
soundness, one through mathematical organisation.
- The engineering judge chose paper-first: 8, against 7 for build-first and 6 for afp-first.
- The mathematics judge ran twice, because a session limit cut off the first run. The first
  run preferred afp-first 8 to 7, the second paper-first 8 to 7.
- Both mathematics runs ask for the same synthesis: paper-first's paper side combined with
  afp-first's library side.

This plan is paper-first plus these grafts:

| graft | from | adopted as |
|---|---|---|
| `Relative_Arbitrage_Equation` as a probability-free sibling on SOVA, not chained on the toolkit | build-first, both judges | §1, D5 |
| `Continuous_Path_Spaces` on `Levy_Prokhorov_Metric` with a ≈ 180-line attributed Arzelà–Ascoli (drops `HOL-Complex_Analysis`, −226 s per build) | afp-first, build-first | §1, phase 5 |
| `Semicontinuous_Analysis` on `Lower_Semicontinuous`; `cInf_mult_pos` into it | afp-first | §1, phase 5 |
| G-G: rework `Viscosity_Solutions` (two generic predicates covering all six variants, bridge equations not abbreviations) instead of deleting it | afp-first, mathematics judge | D9 |
| library re-homing mandatory before the toolkit is promoted: Poincaré/Courant–Fischer, the `outerp` family, the onormal/threshold toolkit and `projmat`/`rank1proj` to SMS; Brownian blocks to WM; martingale moments, `Conditional_UI`, `Stopped_Localization`, optional sampling, `Dyadic_Grids` to CTM | afp-first, mathematics judge | phase 5 |
| check script: `-D .`, oracle check, paper-mention lint, ancestor checks, re-check whitelist from build logs | afp-first, build-first | phase 0 (`check.sh`), extended in phase 5 |
| statement fingerprints compared modulo the constant-rename map | engineering judge | phases 2–8 |
| `[simp del]`: delete VCI and `Ball_Solution`, put a proof-local `simp del` only into proofs moved out of them, never replicate the global declaration | engineering judge (measured: 46 of 48 RA theories already have the rule as simp) | phase 2 |

The panel's full output (three designs, three judge verdicts, the errors each judge found)
is in `notes/review_3/data/session_design_panel.md`.

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

### Phase 0 — tooling and roots (no theory changes) — **done** (`562a95e`, `bce6ac1`)

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

### Phase 1 — the statement says what the paper says, and its evidence is a root — **done** (`0db486f`), except items 8–9, which are pilots (D3, D4)

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

### Phase 2 — dead code, by the roots protocol (§3) — **in progress**

The roots are `roots.txt` with the independent-interest keeps (§1.3): ≈ 520 entries, each
kept fact annotated with its verdict. Order (each a commit, each with a full build):

1. ~~Delete the market layer (8 theories)~~ — **done** (`4d5f47e`). The conduit importers
   were re-pointed: `Exit_Class_Witness` now imports `Continuous_Brownian_Motion` directly,
   the route it had lost (computed by an import-closure diff). The five stale
   antiquotations were rewritten.
2. Delete the 2 empty theories (`Comparison_Jets`, `Dynamic_Programming_Optional_Sampling`),
   re-pointing their importers.
3. Delete the smooth ball strand (`Viscosity_Ball`, `Viscosity_Comparison_Interface`,
   `Ball_Solution`), after moving the two live `Ball_Solution` facts (`feasible_diag_bound`,
   `feasible_offdiag_abs_le`) next to `feasible`. The global `[simp del]` goes with them.
   Where a moved proof breaks, it gets a proof-local `simp del`; the declaration is never
   replicated (§1.4).
4. Delete `Dynamic_Programming_Kernels` after moving its one live fact
   (`exit_val_dpp_sup_ge_time_of_const`).
5. Delete the abandoned constructions in the paper session (§1.2), theory by theory,
   largest block first. Theorem 4.2(a) and its chain stay (D3).
6. Library dead code, only with the library roots in place. `Path_Tightness`'s dead blocks
   are per D6. `Viscosity_Solutions` stays (D9).
7. Re-run the closure, delete what has become dead, repeat until a pass finds nothing (the
   previous plan's `unused_thms` needed four rounds).

**Acceptance:**

- Outside-closure facts are below 5 % of the total.
- No theory is empty.
- Every remaining `@{theory}` antiquotation resolves.
- The market layer, `Comparison_Jets` and `Dynamic_Programming_Optional_Sampling` no longer
  appear on the critical path.

**Expected:** ≈ −17 000 lines in total: 4 901 (done) plus ≈ 12 150 (*measured* against the
new roots). The paper-session build loses ≈ 57 s of market CPU (done) and ≈ 40 s of
abandoned constructions (*measured* per theory).

**Risk:** medium, mechanical. The known traps are the `[simp del]` declaration and the
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

### Phase 4 — clones and verified simplifications — **done** (`b5b98ed`, `f8be660`)

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

### Phase 5 — library moves and parent changes — **done** (`9b8cb01`)

Each move starts with a dry run: copy the theories, change the imports, load them in PIDE,
and assert the ancestors with `Theory.nodes_of`, as in REVIEW_3 §6.2. Only then edit the
repository.

0. **Re-home library material first (mandatory; panel graft).** Nothing is promoted into a
   new session while a library fact still sits in a paper theory:
   - general Poincaré separation, Courant–Fischer, the `outerp` family, the
     onormal/threshold toolkit, `projmat`/`rank1proj` → `Symmetric_Matrix_Spectra`;
   - the Brownian blocks of `Exit_Class_Witness` → `Wiener_Measure` (item 3);
   - martingale moments, `Conditional_UI`, `Stopped_Localization`, optional sampling,
     `Dyadic_Grids` → `Continuous_Time_Martingales` (item 5);
   - `path_laws_convergent_subsequence_market`, renamed for what it states (a process-level
     Lemma 2.2), and `pstopped_vimage_pre_sigma` → `Continuous_Path_Spaces`.
1. **`Semicontinuous_Analysis` → parent `Lower_Semicontinuous`** (AFP; panel graft).
   - `Semicontinuous_Selection` moves to `Continuous_Path_Spaces`, ahead of
     `Path_Exit_Times`.
   - `cInf_mult_pos` moves into `Semicontinuous_Envelopes`. It is a fact about real
     infima, and the library is where a reader looks for it.
2. **`Second_Order_Viscosity_Analysis` → parent `Symmetric_Matrix_Spectra`, with
   `sessions Semicontinuous_Analysis`.** `Crandall_Ishii_Sums`' re-proofs of
   `Semicontinuity` lemmas are replaced by the originals (phase 4).
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
6. **`Continuous_Path_Spaces` → parent `Levy_Prokhorov_Metric`** (AFP heap holding Standard
   Borel and Riesz; panel graft), with `sessions Continuous_Time_Martingales
   Kolmogorov_Chentsov Semicontinuous_Analysis`:
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

### Phase 6 — the two session splits — **done** (`7773a54`)

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
| G-B, finishing PLAN_2's G11 | migrate the ≈ 215 `exit_class` consumers to `covariation_class S` bottom-up, one theory per commit, starting with the four reverted lemmas (`exit_class_diffquot_full_mass` …) and threading `closed S`. Then state Lemma 2.2 for bounded `S` and Lemma 2.3 for compact convex `S`, as the paper does, and the DPP for abstract `S` | after the first three theories, ≥ 80 % of their statements are `S`-generic with no proof grown by more than 20 % — **first round passed** (`5cf2c6c`–`a132065`: `Exit_Class_Limits` 12/14, `_Tightness` 5/6, `_Shift` 5/5; no proof grew); **second round passed** (`fabde7d`–`556d58d`: nine more theories, 110/117 statements S-generic (94 %), max proof growth +12 %; the DPP for abstract `S` stated in `Dynamic_Programming_Principle`); **third round passed** (`c89438a`–`e1791c6`: `Exit_Class_Infinite` 29/33, `_Marginals` 20/25, `_Expected_Exit_Time` 5/6, max proof growth +18 %; Lemma 2.2 for bounded and Lemma 2.3 for compact `S` of positive semidefinite matrices; the class parts of `Value_Function_Subsolution` and `_Euler_Construction` generic, the rest of the `Value_Function_*` theories specialised by content); **fourth round** (`697d7ba`–`ce4a78e`: `_Euler_Construction` 22/22, `_Case_1` 10/11, `_Subsolution` 17/22, max proof growth +1 %; Theorem 1.1's bound and usc clauses for abstract `S` in `_Uniqueness`; left specialised: the operator of Eq. (1.9) in `_Case_2`, `_Tangential_Field`, `_Assembly`, `_Uniqueness`, `Theorem_1_1`) |
| G-B, promotion | if the gate passes, move `covariation_class` and its compactness, pasting and DPP into a library session on top of `Path_Space_Operations` (name by subject, e.g. `Covariation_Constrained_Martingales`). The paper session keeps only `sconstraint`, `xclass`, `xval` and the bridge equations | the moved statements name no paper constant |
| G-C | lift Section 4 to an abstract operator. The comparison chain consumes exactly 23 operator facts (`data/operator_and_class_interface.txt`): ellipticity, positive homogeneity, continuity off `p = 0`, `F^*(0,0) < 1`, a small-shift bound, rotation and dilation invariance. State them as a locale, prove `ell_op` an instance, and move the chain into a library session (`Geometric_Viscosity_Comparison`) | the two raw unfoldings (`ell_op_def`, `feasible_def`) inside the chain can be replaced by interface facts in ≤ 200 lines |
| G-G (D9) | rework SOVA's `Viscosity_Solutions` into two generic predicates, parametrised by the operator, the set and the touching locality, covering the six used variants including `env2` | the six paper predicates are joined to them by proved equations (not abbreviations); `Statement` still displays what the authors expect |
| G-D | widen the ≈ 600 SOVA lines fixed to `real^'n` that mention no matrix, and the ≈ 110 toolkit statements typed at a product codomain they never inspect | uniform sort per layer first (PLAN_2 §11's lesson); `-o timeout=900` |
| G-F | drop the avoidable hypotheses: `ess_inf_pexit_usc` (`probs`, `prob`; *checked*), `jensen_lemma`'s `0 < ρ` | none needed — **done** (`99c0e36`) |

### Phase 8 — prose, names and notes

1. Remove or rewrite the 168 "`X` lives in `Y`" pointer texts. Reattach the ≈ 60 orphaned
   text blocks and section headers to their lemmas. Delete the empty `section`s.
2. Renames and merges (paper order, panel):
   - `Curvature_Operator` → `Elliptic_Operator` (it defines `eigen_lb`, `feasible` and
     `ell_op`, and no curvature operator);
   - `Comparison_Principle` → `Maximum_Principle` (it holds Theorem 4.2);
   - `Eigenvalue_Bound_Exact` into `Constraint_Set_Convexity`, `Operator_Continuity` into
     `Operator_Formula`, `Operator_Envelope_Continuity` into `Operator_Envelopes`;
   - new theories `Control_Problem` (Eqs. (1.5)–(1.7)), `Example_3_1`, `Proposition_2_4`;
   - every rename is applied to the fingerprint check's rename map in the same commit;
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

**D1 — `Crandall_Ishii_Sums`: keep it, as a root of `Second_Order_Viscosity_Analysis`
(owner's directive).**
- It is the session's advertised headline, and a theorem of independent interest even
  though Theorem 1.1 needs only one instance of it.
- It costs the paper build nothing: no paper theory imports it, and the paper session
  re-checks 11 of the 12 SOVA theories, all except this one (*measured*).
- It was the largest dead block only because no root declared it.
- What changes: its internal duplication (≈ 300 lines) and its re-proofs of `Semicontinuity`
  lemmas (≈ 120) go in phase 4. The quadratic-penalty lemmas it needs stay as roots, and
  the rest become instances of `_gen`.
- FIX_THEN_KEEP (§1.3): the classifier and the verifier agree that the formal statement is
  weaker than the classical one. It is strengthened to the block-matrix inequality of
  Crandall–Ishii–Lions (3.10) (phase 7, gated). The weaker form stays as a corollary.
- Rejected alternatives:
  - rebasing the comparison on it (*checked*: the live path grows);
  - deleting it (an AFP entry on second-order viscosity theory without the theorem on sums
    would be odd).

**D2 — the market layer: deleted (done, `4d5f47e`).**
- It was a second formalisation of the problem over abstract markets, and no deliverable used
  any fact of it (*measured*).
- Its one result of independent interest is a bound on the expected exit time from a ball.
  It is now re-proved generically (**done**, *checked*, independently re-checked as
  faithful). `Continuous_Time_Martingales.Expected_Exit_Times` gives, for a continuous
  martingale `Y − A` with `Y ≤ R` up to `τ` and `A` growing at rate at least `c`, the bound
  `c E[τ ∧ t] ≤ R − E[Y₀]` and integrability of `τ`. `Exit_Class_Expected_Exit_Time` applies
  it to the class: `E[τ_K] ≤ (r² − |x|²)/(n−k)` for closed `K ⊆ cball 0 r`.
- `eigen_ub_diag`, the one fact a live theory needed, moved to `Curvature_Operator`.

**D3 — Theorem 4.2(a): proved in the paper's form (pilot, *checked*; done).**
- `max_principle_usc_lsc` (`Comparison_Principle`) has the following hypotheses:
  - compact `K`;
  - `u` usc and `w` lsc relative to `K`;
  - `u` a viscosity subsolution and `w` a supersolution in the interior, in the
    Definition 3.1 reading (`env2`).

  It concludes that `u − w` attains its maximum over `K` at a boundary point.
- The bounds `|u|, |w| ≤ B` on `K` are explicit. The paper's proof uses `‖u‖∞`, `‖w‖∞`
  without saying so. `Paper_Map` records this.
- A Lebesgue number replaces the paper's subsequential limit of maximisers, so only
  semicontinuity is used.
- The continuous-data `max_principle_boundary_holds` is now a corollary. The continuity-only
  chain it used was deleted in phase 2.
- `viscosity_uniqueness_compact` stays, as a corollary.

**D4 — Proposition 2.4 (the DPP equality with attainment): proved (pilot, *checked*).**
- 282 lines with no `sorry` (batch check OK). Every optimiser of the value function attains
  the supremum of (2.9), at a deterministic time and at a path stopping time with values in
  `[0,T]`.
- It reuses `exit_val_cond_time` and `exit_val_dpp_sup_ge(_time)`. The `key` step of
  `exit_val_dpp_le_of_cond` becomes an exported lemma, `exit_val_dpp_ess_inf_mono_time`.
- It goes into a theory `Proposition_2_4` after `Dynamic_Programming_Assembly` and
  `Dynamic_Programming_Conditioning`. The empty section in `Dynamic_Programming_Conditioning`
  that announces it goes.
- **What it is not.** It is (2.9) for the internal value `exit_val` (horizon `T`, pair laws,
  path stopping times bounded by `T`). The paper states (2.9) for `v` on `[0,∞)` with
  arbitrary stopping times of `X`. The pilot report sizes the transfer:
  - ≈ 50 lines to identify `v` with `exit_val` at large horizons;
  - 200–400 lines of essential-infimum transport between the classes;
  - Galmarino's test for the coordinate filtration, not in the repository and genuinely hard;
  - a limit argument for unbounded `θ`.
- `Paper_Map` states what is proved and names the gap. `root.tex`'s "proved here in full"
  changes to match.
- Done as `Proposition_2_4` (`040c0c5`). The independent re-check confirmed the scope: the
  statements are faithful for the horizon-`T` problem. It also points out that the
  transfer to `v` for **bounded** `θ` should follow from existing bridges
  (`exit_val_horizon_cap`, `iexit_val_eq_exit_val(_ball)`, `exit_class_has_extension`)
  with `T ≥ sup θ + r_K²/(n−k)`. That is a follow-up pilot (≤ 300 lines, gated). Galmarino's
  test and unbounded `θ` stay out of scope.

**D4b — Section 5 (continuity of `v` for convex `K`): out of scope for this
restructuring, with one cheap exception.**
- None of Section 5 is formalised (REVIEW_3 §1.2e).
- Proposition 5.1 (continuity on the interior of a convex `K`) and its corollary 5.2 are a
  pilot (≤ 200 lines). The pilot runs only after phase 6, once `Relative_Arbitrage_Equation`
  exports the dilation invariance and Theorem 4.2(b) it needs.
- Lemma 5.3 and Propositions 5.4 and 5.5 are new mathematics. They are recorded in
  `OPEN_ITEMS.md`, not planned here. The stale "done" entry for `eigen_lb_dim_obstruction`
  in `STATUS.md` is corrected in phase 8.

**D5 — where Section 4 lives: `Relative_Arbitrage_Equation`, a probability-free sibling
on `Second_Order_Viscosity_Analysis` (panel graft; adopted).**
- This is the paper's own seam. Section 4 is checked in ≈ 90 s without the probability stack,
  and its probability-freeness holds by construction rather than by a regression test.
- The price: the paper session re-checks it, ≈ 90 s per cold build. The chained alternative
  (parent on `Path_Space_Operations`) saves that and costs ≈ 620 s of CPU per Section 4
  edit, so it is rejected.
- The theory files are the same under either choice, so it can be switched by editing two
  ROOT lines.

**D6 — the scope of `Continuous_Path_Spaces`.**
- It keeps what its description promises: path space, weak convergence, tightness from
  increment moments, quadratic variation as a path functional, exit times, and now
  measurable selection.
- `Path_Tightness`'s dead projective-limit and continuous-modification blocks are deleted,
  since AFP `Kolmogorov_Chentsov` has the continuous modification. The scalar tightness twin
  is deleted.
- The Kolmogorov–Chentsov tightness criterion (moments of increments imply tightness of the
  laws on path space) stays: it is a named theorem the AFP lacks. Its `8C²` becomes a
  parameter (G-E).
- If the author wants a projective-limit construction in the library, it belongs in
  `Wiener_Measure`, which already builds one.

**D7 — no aggregating "base" session, and no "extras" leaf.**
- An intermediate session holding every library theory would only move the re-checking:
  the join has to happen somewhere.
- It also breaks PLAN_2 §8 rule 7 (no filler names). The panel's build-first design proposed
  one (`Relative_Arbitrage_Base`, legal and measured), and both judges rejected it on that
  ground.
- Results of independent interest stay where the paper or the library puts them, not in an
  `Extras` leaf.

**D8 — `Paper_Map` (panel graft).**
- It is the last theory of `Relative_Arbitrage_Statement`. It has one `theorem` per numbered
  item of Sections 1–4, proved by `rule` from the working lemma, and states each deviation
  beside it. Section 5 is listed as not formalised.
- It replaces the paper wildcards in `roots.txt`, so the reader's index and the dead-code
  root set cannot drift apart.

**D9 — the generic viscosity layer: rework it (G-G), do not delete it.**
- `Second_Order_Viscosity_Analysis.Viscosity_Solutions` defines viscosity sub- and
  supersolutions for an arbitrary operator. The paper session does not use it: it has six
  variants of its own (plain, `env`, `env2`, `_K`, `_bc`, `_bc_K`).
- Rework: two generic predicates in SOVA, parametrised by the operator and the set. The six
  variants become instances, joined to them by proved equations rather than abbreviations.
- Then Theorems 4.2 and 4.3 are about the generic predicates, and the session's description
  ("viscosity solutions") becomes true. It is gated as phase 7 work; the fallback is to keep
  the layer as KEEP_API with its description corrected.

**D10 — the six undelivered library claims (§1.3).**
- Each is delivered, or its description is corrected, in phase 7 or 8. Courant–Fischer and the
  general Poincaré separation are delivered first: their evidence is now a root, and the
  general statements are FIX_THEN_KEEP.

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
   phases 1 and 4, for the gated pilots D2, D3, D4, D4b and phase 7, and for the
   FIX_THEN_KEEP items of §1.3. Each of these is a replacement whose statement is identical
   (`aconv`, modulo the rename map) or stronger, or a new statement of the paper. Nothing
   else gets a new proof.
2. **Rule 2 is extended:** never weaken `theorem_1_1` or any `Paper_Readings` statement, and
   never delete a fact named in `roots.txt`. If a deletion needs one gone, the roots file
   changes first, in its own commit, with the reason.
3. **Build everything** (`-D .`), not only the Statement chain, after every commit.
4. **A dry run precedes every move across a session boundary** (copy, load in PIDE, assert
   the ancestors). When PIDE is unavailable, a throwaway batch session on the target parent
   heap does the same job.
5. **Antiquotations are part of the move.** Grep for `@{theory`, `@{thm`, `@{const`,
   `@{locale` naming the moved or deleted entity across all sessions, including line-broken
   occurrences.
6. **The completion note records refuted predictions.** If a number in this plan is wrong,
   the plan is wrong, not the development.

---

## 7. Progress log

| date | commit | step | result |
|---|---|---|---|
| 2026-10-07 | `562a95e` | Phase 0: `roots.txt`, `Review_Analysis` reads it, `check.sh`, `.pyc` untracked | all sessions build; oracle check empty |
| 2026-10-07 | `0db486f` | Phase 1: `theorem_1_1` with the paper's hypotheses (clauses 0–3 for compact `K`, clause 4 under `expandable K ⟶`, no `K ≠ {}`); `Theorem_1_1.thy`; `Statement_Auxiliary` deleted; `ell_op_sym_part`; `Paper_Readings` extended (F over symmetric matrices, spectral conditions, Lemma 2.1 as an equality, convex sets are expandable, the literal reading of (1.5) and its unboundedness); the wrong prose corrected | all sessions build |
| 2026-10-07 | `bce6ac1` | analysis summary file with the oracle check | — |
| 2026-10-08 | `4d5f47e` | Phase 2.1: market layer deleted (8 theories, 4 901 lines) | all sessions build |
| 2026-10-08 | `90472c1` | independent-interest review (§1.3), design panel (§1.4), roots extended to ≈ 520 entries, this revision | analysis re-run against the new roots |
| 2026-10-08 | `61a7e9f` | Phase 2.2–2.4: empty theories, smooth ball strand (with the global `[simp del]`), `Dynamic_Programming_Kernels` | all sessions build |
| 2026-10-08 | `040c0c5` | Proposition 2.4 for the horizon-`T` value (pilot, D4); Lemma 3.1 in `Paper_Readings` | all sessions build |
| 2026-10-08 | `277512b` | roots: 23 COROLLARY verdicts that keep their name | — |
| 2026-10-08 | `518daa6` | Theorem 4.2(a) for usc/lsc data (pilot, D3); `Expected_Exit_Times` in CTM and its class corollary (pilot, D2) | all sessions build |
| 2026-10-08 | `d00dc3b` | Phase 2.5–2.7: the dead blocks of 52 theories against the 552 roots, by script (`delete_dead`: lemma blocks with no live fact and no remaining mention in code, texts that mention only deleted facts, emptied headers, unused definitions named nowhere else); `Moment_Bounds` emptied and deleted; `eigen_ub_diag` kept (FIX_THEN_KEEP); six facts the analysis called unused but live proofs still name are kept. A second pass found 196 dead lines left, all kept on purpose (interpretation-generated facts, facts named in proofs): fixpoint reached | all sessions build |
| 2026-10-08 | `ad9add6` | Phase 3a: `Pair_Path_Space` no longer imports SOVA (`Sup_Convolution`, `Doubling_Of_Variables`) or WM's finite-dimensional distributions; its one use was a copy of HOL's `norm_Pair_le`. `Exit_Class_Infinite` imports `Exit_Class_Pasting` | all sessions build |
| 2026-10-08 | `643de89` | analysis loads every leaf theory (483 theories, 575 roots; dead lines unchanged) | — |
| 2026-10-08 | `980b6fe` | Phase 2.8: 152 mentions of deleted lemmas in the prose of 31 theories rewritten (six writers on disjoint files, six reviewers) | all sessions build |

| 2026-10-08 | `4188265` | Phase 3.3: every theory imports exactly the maximal theories it needs (`minimize_imports.py`: needs are named facts and constants used in proofs, locales used by name, facts, constants and theories named in antiquotations, and every current HOL/AFP ancestor, kept for notation). 59 theories changed. Critical path through user theories: **280 s over 25 theories** (baseline 577 s over 35; acceptance ≤ 418 s; bound with needed dependencies only: 274 s) | all sessions build |

| 2026-10-08 | `34e6d91` | D8: `Paper_Map` (one theorem per numbered paper item, deviations stated; written by one agent, reviewed adversarially by another against the LaTeX source); its theorems are roots | Statement builds |

| 2026-10-09 | `bd84eff` + fix | Phase 4, first round: chunk 0 of groups G2 (SOVA), G3 (CTM/CPS: the direct `ess_inf_pexit_usc` proof, −940 lines with the Laplace route) and G5 (path toolkit). 38 twins or special cases gone, all users re-pointed; 46 fingerprints changed, all checked: equivalent (the new `pshift_law`/`aglue_law` abbreviations, an associativity merge) or stronger (`martingale_expectation_eq`, `norm_sq_*_expand`, `superjet_supconv_form_lower`). 102 140 lines. The rest of phase 4 (20 chunks over 8 groups; work list in `data/phase4/G*-items.json`; phases 5–6 move list in `data/phase56_scope.json`) was stopped by a usage limit; G1 and G4 left unverified work on branches `p4-G1`, `p4-G4` | all sessions build; dead code 196 lines |

| 2026-10-09 | (saved, not merged) | Phase 4, round 2 (paused by the owner): 11 more chunks finished and built in their worktrees, about −8 800 lines by the agents' estimates; not yet reviewed, merged or built together | see "Resuming phase 4" |

| 2026-10-13 | `b5b98ed` | Phase 4, round 2 finished: the remaining chunks of all eight groups, one reviewer per group (G4's reviewer dropped two orphaned texts; the others changed nothing), merged in the order G2, G3, G5, G7, G8, G4, G6, G1. 219 work items: 189 done or already done, 24 partly done, 6 skipped (per-group counts in `data/phase4/round2-results.json`). The merges fixed every cross-group breakage, where one group used a fact another deleted or restated (e.g. `exit_val_dpp_ge_const`, `fourth_abs_mono`, `weak_conv_closed_full_mass`, `fourth_moment_L2`'s new start hypothesis, G1's `matvec_*` → HOL-Analysis renames), and removed three duplicates (the max-principle corollaries of G7 and G8, the pair-path helpers of G4 and G5, a doubly moved `exit_val_boundary_zero`). Fingerprints against `34e6d91`: 89 changed, 331 gone, 147 new. Every change is equivalent or stronger except four, accepted: `max_principle_le` and `uniqueness_from_max_principle` (roots) no longer assume the interface predicate `max_principle_boundary`, which is now a theorem and was deleted; they carry the hypotheses of `paper_theorem_4_2_a` instead, and the old form differs only where the predicate held vacuously (e.g. `k = 0`); `exit_val_measurable_selector_kernel'` and `sbm_kernel_package` lost a Lévy–Prokhorov measurability conclusion whose only user (the `Kb` hypothesis of `exit_class_kglue_law'`) is gone. No gone fact is a root or named in `Statement/`; `Statement/` gained four `Paper_Readings` theorems and changed no statement | all sessions build; 569 roots resolve; no oracles |
| 2026-10-13 | `f8be660` | Phase 4 dead-code pass: 42 lemma blocks left without users (613 lines; e.g. the Householder rotation lemmas, whose user was the deleted rotation route). The second pass finds nothing: fixpoint | all sessions build |

**State after phase 4:** 85 149 lines in the eight sessions (102 848 at `bc034d3`):
SMS 5 594 (7 397), SemiC 1 999 (2 221), SOVA 14 290 (16 244), CTM 7 949 (8 939), WM 3 055
(3 774), CPS 9 318 (10 363), RA 41 154 (52 217), Statement 1 790 (1 693). User facts 4 049
(4 233 at `34e6d91`). A full rebuild of all sessions takes about 17 minutes of wall-clock
time with two threads; RA 5:46, CPS 5:26.

| date | commit | step | result |
|---|---|---|---|
| 2026-10-14 | `4039eaf` | Phase 5 move list re-scoped against the post-phase-4 tree (`data/phase5_rescope.json`: two scouts, two adversarial checkers). Already done by phase 4: the Brownian blocks of `Exit_Class_Witness` and the fourth moments (M26, M27), the HOL renames of the SMS re-proofs (F2). Illegal or not recommended, as before: `sbmpair` to WM (F5), `pstopped_vimage_pre_sigma` to CPS (F4, it goes with the toolkit), dropping SemiC from CPS's sessions (M29: `Semicontinuous_Selection` now needs `Berge`) | — |
| 2026-10-14 | `9b8cb01` | Phase 5, two tracks merged. **Parents:** SemiC on `Lower_Semicontinuous` (no HOL-Probability ancestor), SOVA on SMS, WM on CTM, CPS on `Levy_Prokhorov_Metric` without `HOL-Complex_Analysis` (Arzelà–Ascoli copied into `Equicontinuity` with attribution). **Moves (statements verbatim):** `Semicontinuous_Selection` to CPS; `cInf_mult_pos` to `Semicontinuous_Envelopes`; the CIS/`Sup_Convolution` semicontinuity lemmas to `Semicontinuity`; the `outerp` family, psd facts, Courant–Fischer bound, threshold lemma, rotation continuity, polarisation and form bounds into SMS, with the new `Orthogonal_Projections` (`rank1proj`, `projmat`); `Increment_Moments` (martingale part), `Conditional_UI`, `Stopped_Localization` and the new `Dyadic_Grids` and `Stopping_Time_Sampling` into CTM; the non-martingale tail of `Increment_Moments` into `Path_Tightness` and the new `Difference_Quotients`; the QV identifications into `Adapted_Quadratic_Variation`; the generic exit-time semicontinuity block into `Path_Exit_Times`; `pball_exit` into `Path_Stopping_Times`; generic `Essential_Infimum`, `Stopping_Times` and `Semidirect_Kernels` facts into CTM; the independence lemmas into `Product_Brownian_Motion`; `Integrability_Criteria` reduced to four lemmas on `HOL-Probability`. **Clone:** SMS's `outer_prod` and four of its lemmas replaced by HOL-Analysis's identical ones. One strengthening: `path_laws_convergent_subsequence_martingale` (was `…_market`) drops an unused hypothesis. ROOT descriptions and abstracts updated. Fingerprints against the end of phase 4: 0 changed, 7 gone (the five `outer_prod` twins, `usc_open_lt` = `open_usc_sublevel`, the rename). Dead code: none. Build (2 threads): CPS 6:19 → 1:47, RA 7:35 → 5:38, WM 2:11 → 1:00 | all sessions build; 574 roots resolve; no oracles |

**State after phase 5:** 85 262 lines: SMS 6 547, SemiC 1 356, SOVA 14 133, CTM 11 248, WM
3 308, CPS 8 331, RA 38 549, Statement 1 790. RA lost 2 605 lines to the libraries.
Left for phase 8 (reported by the reviewers): text-only sections in `Operator_Formula`,
the misplaced "constant-volatility Gaussian member" text in `Pair_Path_Space`, paper and
market wording in WM, `Path_Exit_Times` and `Adapted_Quadratic_Variation` prose, and
`Paper_Readings`' hidden `outer_prod_zero_left/_right`, which now duplicate HOL's (Statement
is frozen: owner decision). `Statement/theorem_1_1_unfolded.html` has stale line links (M38).

| date | commit | step | result |
|---|---|---|---|
| 2026-10-14 | `6031b78` | Phase 6.2: `Relative_Arbitrage_Equation` (RAE) = SOVA + sessions SemiC, by `git mv` of the 12 operator and comparison theories, plus `Subspace_Tangential_Field`, the probability-free half of `Value_Function_Tangential_Field` (19 facts); `No_Probability_Ancestor` fails the build if a probability, martingale, path-space or paper theory becomes an ancestor (negative controls checked). `sconstraint` stays in RA (F6) | all sessions build |
| 2026-10-14 | `a1f1b50`, `7773a54` | Phase 6.1: `Path_Space_Operations` (PSO) = CPS + sessions SMS, SemiC, `Disintegration`, the six toolkit theories by `git mv`; `No_Viscosity_Ancestor` (no SOVA, WM, RA, RAE or `HOL-Complex_Analysis` ancestor); the paper session's parent is PSO. 22 of the 25 `@{theory Relative_Arbitrage.X}` antiquotations requalified. Analysis scripts know both sessions; ROOTS in dependency order; ROOT descriptions and documents for both; `theorem_1_1_unfolded.html` links fixed against its pin. 522 facts moved, 0 statements changed; fingerprints against phase 5: 0 changed, 0 gone. **Acceptance:** paper session 218 s (target ≤ 300 s; RA was 355 s with RAE alone, 338 s at phase 5); RAE 51 s with no probability ancestor; PSO 134 s with no SOVA ancestor. **Refuted (rule 6):** the model behind the 235 s estimate assumed that theories reached through `sessions` load from heaps; Isabelle re-checks them (RA still re-checks 13 RAE, 11 SOVA and 8 WM theories). The saving comes from the toolkit moving into the parent heap. PSO's build took 134 s against an estimate of ≈ 311 s. **Found:** this container's TeX is a stub, so no document had ever been compiled to PDF; with a real TeX, RAE, PSO and RA compile (after Unicode fixes); SOVA (combining circumflex in 10 prose lines) and Statement (`Paper_Map.thy:19`, a raw `\<dots>`) do not: phase 8 | all sessions build; 574 roots resolve; no oracles |
| 2026-10-14 | `89351e3`, `99c0e36` | Phase 7 pilot G-F (no gate). `ess_inf_pexit_usc` (root) takes the statement of its `_min` twin: no `probs`, no `prob`, and `0 ≤ T` for `0 < T`; the twin is merged into it. Its user `ess_inf_pexit_pshift_usc` loses two `prob_space` side proofs and is weakened to `0 ≤ T` (it used nothing else). `jensen_lemma` (root) and `semiconvex_jensen_alexandrov_point` assume `0 < r` instead of `0 < ρ` (the reader's "derivable from `small` and `bnd`" holds only with `0 ≤ r`: for `ρ < r < 0` the ball is empty and the conclusion false, so the radius bound stays), and drop `0 < c`: the semiconvexity constant is raised to `max c 1` by adding a convex multiple of `‖z‖²` (`convex_on_norm_sq` moves from `Theorem_On_Sums` to `Convex_Subgradients` for this). `Doubling_Of_Variables` drops its positivity proof of the constant. Statement check against `b6b73e5`: 4 statements changed, all more general (each old form an instance), 1 fact merged (`ess_inf_pexit_usc_min`), 1 moved; `Statement/` untouched. Not done (outside the named facts): `doubled_supconv_jet_exists_shifted_gen` still assumes `0 < ρ`; REVIEW_3's other G-F item, Theorem 4.2(a)'s continuity hypothesis, was already settled by D3 (`518daa6`) | all sessions build |
| 2026-10-14 | `5cf2c6c`, `1e5d9b2`, `3340725`, `a132065` | Phase 7 pilot G-B, first round. PLAN_2's four reverted lemmas: `closedin_diffquot_constraint`, `_all` and `diffquot_all_sets` take any `closed S`; the start and difference-quotient full-mass and weak-limit lemmas become `covariation_class_start_full_mass`, `_start_limit` and `_diffquot_limit`. Then three consumer theories, bottom-up, one commit each: `Exit_Class_Limits` (Lemma 2.3's chain), `Exit_Class_Tightness` (Lemma 2.2's chain) and `Exit_Class_Shift` (shift structure, usc of the value). Each lemma reads `covariation_class S` (or `covariation_val S`) and takes from `S` only what it uses: a norm bound `B`, a diagonal bound `[0, D]`, `closed S`; the paper's case is `B = CARD('n)·L`, `D = L`, bundled as `sconstraint_bounds`. Kept as one-step instances because `Statement` applies or names them: `exit_class_fourth_moment` (constant `8L²`), `exit_class_weak_closed`, `tight_on_set_paper_pair_class`. **Gate: passed.** S-generic statements: Limits 12/14 (86 %), Tightness 5/6 (83 %), Shift 5/5 (100 %), together 22/25 (88 %); proof length (lines, generic vs. old): no proof grew (max +0 %, two shrank by 1–2 lines). `exit_class_X_martingale` moved to `Exit_Class` beside the other clause projections; `exit_class_Y_entry_bound_ae` and `exit_class_lipschitz_ae` became unused and went. Users re-pointed in 9 theories (+19 lines net, mostly `Exit_Class_Optimizer`, `Value_Function_Euler_Construction`, `Exit_Class_Witness`). Lesson: passing a rule-shaped fact such as `sconstraint_bounds[OF L]` through `OF` leaves its premise `a ∈ sconstraint ?k L` as a new premise with `?k` schematic; under `by (rule …)` the closing assumption step discharges it, but under `using … by blast` it sent `blast` into a 30-minute search — instantiate through `by (rule …)` and then unfold `exit_class_eq_covariation`. `Exit_Class` itself (the bridge) stays mostly paper-specific: 11/34 statements generic; its 1-line `exit_class_*` projections have users in ≈ 15 theories and go with the next rounds. **Review** (`e06822f`): every changed or renamed statement is the old one at `S = sconstraint k L`, `B = CARD('n)·L`, `D = L` (`closed_sconstraint` and `exit_class_eq_covariation` are unconditional); gate re-measured independently with the same result; the two deleted facts have generic twins in `Pair_Path_Laws`; stale "paper's class" prose in `Exit_Class_Limits` fixed. Counting `Exit_Class` itself among the first three theories would give 28/54 (52 %), but it is the bridge, not a consumer | all sessions build; 502 roots resolve |

**State after phase 6:** ten sessions: SMS, SemiC, SOVA, RAE, CTM, WM, CPS, PSO, RA (the
paper session, 26 theories) and Statement. A cut below RA would now need RAE or SOVA on
RA's parent chain, which a single-parent session graph cannot combine with PSO's
no-SOVA requirement.

| date | commit | step | result |
|---|---|---|---|
| 2026-10-14 | `0ff5f44`, `515f889`, `12756a9`, `d21b37a` | Phase 7 G-G (D9), branch `p7B`. SOVA's `Viscosity_Solutions` now has two predicates, `visc_subsol_gen T N F Ω u` and `visc_supersol_gen T N F Ω u` (plus `visc_sol_gen` as their conjunction): test class `T`, touching locality `N` as a filter at each point (`nhds` = local touching, `λ_. principal K` = touching over `K`), operator `F`, set `Ω`. Generic API: elementary forms at the two localities (`visc_*_gen_nhds`, `visc_*_gen_principal`), monotonicity in `F`, `Ω`, `T` and `N`, congruence in `u`, and the quartic global-to-local passage (`visc_*_gen_principal_local`). `Viscosity_Definitions` proves ten bridge equations (`*_eq_gen`), one per paper predicate: plain, `env`, `env2` (sub and super, the six on the path to Theorem 1.1), `visc_supersol_lsc` (function `lsc_env u`), `supersol_jet`, and the two solution conjunctions. The paper definitions are untouched. Then nine RAE lemmas became instances (env2 congruences, the three global-to-local quartic lemmas, `visc_*_imp_env`, `supersol_jet_cong_on`): −94 lines in RAE, statements unchanged; nothing in RA got shorter, so RA is unchanged. **Gate passed:** all six paper predicates (and four more) are joined to the generic ones by proved equations, and `Statement` is untouched (no statement changes, `visc_*_env2_def` displayed as before). Statement check against `b6b73e5`: 2 facts gone (`visc_*_gen_env_imp`, renamed `visc_*_gen_subset` in roots in their own commit, together with `visc_*_gen_env_def` → `visc_*_gen_principal`), 2 statements generalised (`visc_*_gen_mono`, now for every `T`, `N`), the three `visc_*_gen_def` generalised (old = instance `T = test_fun_at`, `N = nhds`, by `visc_*_gen_nhds`). Lines: SOVA +170 (the generic API), RAE −66 net | all sessions build |
| 2026-10-14 | `a80fbcd`, `3caf83c`, `62475ea` | Phase 7 G-C, branch `p7B`. **Gate measured first, passed:** inside the chain (`Comparison_Strictness` .. `Comparison_Two_Domain`, at `2d360cf`) the operator's raw structure was read at 4 sites: `ell_op_def` (with `ell_op_bdd_below`) once, in `ell_op_scaleR_matrix` (22 lines, positive homogeneity in `M`), and `feasible_nonempty` three times, each a one-line `ne` premise for ellipticity, `ell_op_M_gap` or homogeneity; `feasible_def` itself had no site left (the plan's count is from the older layout; refuted prediction). Replacing them cost 0 new chain lines: the homogeneity lemma moves unchanged to `Operator_Envelope_Continuity`, the `ne` steps disappear. Then: new RAE theory `Geometric_Operator` (imports SOVA, SMS, Semicontinuous_Analysis only): ereal envelopes `op_lsc`/`op_usc` of any operator with sandwich, nearby-point, usc-limit and transport facts (dilation, rotation), and the locale `geometric_operator` with **10 assumptions** (panel gate ≤ 15): ellipticity, homogeneity in `M`, dilation and rotation invariance, a shift bound `F(p,M) ≤ F(p,M+δI) + Cδ` (replaces `ell_op_M_gap`/`mgap_shift_id`), `F_* = F^* = F` off `p = 0` at symmetric `M`, `F_* = F` at `p = 0`, `F^*(0,0) < 1`, `F^*(q,−δI) < 1` uniformly. The six notions are locale abbreviations of the D9 generic predicates, so Theorems 4.2/4.3 in the locale are about the generic predicates (D9 completed). The four chain theories no longer import the operator layer; lemmas that read no operator property are stated outside the locale for any operator (so their old statements are instances), the rest inside. New theory `Comparison_Instance`: `ell_op_geometric_operator` (for `1 ≤ k < n`, `1 ≤ L`, 60 lines) and the paper statements consumed by RA, Statement and the roots, with unchanged statements. `Operator_Envelopes`' envelope facts became one-line instances of the generic ones (−208). Roots: D3 root → `Comparison_Instance.max_principle_usc_lsc`, four corollary roots → their locale versions, `Comparison_Instance.*` added (roots-only commit). Lines: RAE 8 756 → 9 168 (+412: `Geometric_Operator` +403, `Comparison_Instance` +228, chain −47, operator layer −172); Statement and RA unchanged except one import. **Session move not done:** a throwaway session `Geometric_Viscosity_Comparison` on SOVA with the five generic theories builds in 44 s (dry run), its only failure the `LaiShkolnikovSoner` citation; the theories still carry ≈ 41 lines of paper prose that a library session must not (phase 8 item 3), so the move follows that cleanup | all sessions build |
| 2026-10-14 | `6865ccb` | Phase 7 review of G-G and G-C, branch `p7B`. **Statements:** every changed or removed fact against `b6b73e5` (36 by name across files, plus the removed helpers) was restated in its old text in a throwaway session on the RAE heap and derived in one step from the new facts: the locale facts by `geometric_operator.X[OF ell_op_geometric_operator[OF kk LL]]` through the `*_eq_gen` and `ell_op_*_eq_op_*` bridges, the operator-free ones by instantiating `G`/`F`, `visc_subsol_scaled_uniform` with `ell_op_scale` and `ell_op_scaleR_matrix[OF _ ne]`, the old SOVA forms (two-argument `visc_*_gen`, `visc_*_gen_env`) as local copies of the old definitions: all 35 check lemmas build. The eleven paper statements in `Comparison_Instance` and `ell_op_scaleR_matrix` are textually identical to the old ones; `Statement` is untouched. **Roots:** all 523 resolve on the built heaps, qualifiers included; RAE (16 theories) has no probability ancestor and PSO (7) no SOVA ancestor. **Gates re-measured:** G-G: the ten bridges are `lemma`s proved by `simp`, the paper definitions unchanged. G-C: at `2d360cf` the chain read `ell_op_def` once and `feasible_nonempty` three times (`feasible_def` never); at HEAD the chain imports only `Geometric_Operator` and names no `ell_op` constant; interface cost 118 lines (locale part) + 49 (instance proof), chain −47 net, so under 200 lines however counted. The planned library-session move is not done (recorded above). **Fixed:** prose citing removed facts (`strict_contradiction`, `ell_op_(env_)strict_contradiction` in Comparison_Strictness, SOVA `Doubling_Of_Variables`, SMS `Symmetric_Spectral`; `ell_op_*_off_zero`/`_at_zero` where the locale assumptions are meant) and the RAE abstract's list of the ten assumptions. Left for phase 8: the orphaned `eq36` texts in `Comparison_Strictness` (now marked as about the operator of Eq. (1.9)) | all sessions build |
| 2026-10-14 | `fabde7d`–`556d58d`, `c3673d5` | Phase 7 pilot G-B, second round, branch `p7C`: nine consumer theories bottom-up (import order, which differs from the remaining list: Witness, Pasting, Optimizer, then the DP chain), one commit each except `Dynamic_Programming_Delayed_Class` + `_Assembly` together (the delayed class `pdelclass k L T s` became `pdelclass S T s`, so its only consumer had to move with it). Each lemma takes from `S` only what it uses; the recurring hypotheses are `closed S` (measurability of the constraint clause: cut, conditioning), `convex S` (pasting: a quotient across the glue time is a convex combination), a norm bound `B` and a diagonal bound `D` (integrability; compactness), a trace lower bound `θ` (Lemma 2.1's exit-time estimate, `covariation_val_le_ball_bound`), and some covariation rate `σ σᵀ ∈ S` (Brownian witness: nonemptiness, horizon monotonicity, upper semicontinuity of the value). **Gate (S-generic statements; max proof growth):** `Exit_Class_Witness` 23/27 (85 %; +11 %, `exit_val_usc_unconditional` 9→10 lines), `Exit_Class_Pasting` 20/20 (+0 %), `Exit_Class_Optimizer` 6/7 (86 %, counting the primed `covariation_class_kglue_law'`, which `gate.py`'s regex skips; +0 %), `Dynamic_Programming_Pasting` 6/6 (+12 %, `covariation_val_open_less` 8→9), `_Stopping_Clauses` 4/4, `_Additive_Glue` 4/4, `_Conditioning` 10/10, `_Delayed_Class` 23/23, `_Assembly` 14/16 (88 %), all +0 %. **The DPP for abstract `S`** (`556d58d`): new theory `Dynamic_Programming_Principle` states Proposition 2.4 (Eq. (2.9)) for `covariation_val S` at a deterministic time and at a path stopping time, with attainment, for closed convex `S` with `B`, `D` and some `σ σᵀ ∈ S` (9/9 generic, every proof shorter than its old `Proposition_2_4` form); `Proposition_2_4` (root) keeps its nine statements and names, each now a one-step instance. Paper instances kept (one-liners) because `Statement` or the value-function theories apply them: `exit_class_compactin_weak` (Paper_Map), `exit_val_usc_unconditional`, `exit_val_le_ball_bound`, `exit_val_boundary_zero`, `enn2real_paper_v_horizon_cap`, `exit_val_dpp_ge_const_time`; `Exit_Class` gains `mat_1_rate_in_sconstraint` (`I Iᵀ ∈ sconstraint k L` for `1 ≤ L`). Horizon variables named `S` in cut/monotonicity lemmas renamed `U`, selector variables `Sel`. Retired as their users moved: `exit_class_eval_measurable`, `_Y_entry_integrable`, `_compensated_entry_integrable`, `_sq_integrable`, `_sq_mean_le`; `exit_class_prob`/`_sets` stay (Statement), `_start`, `_compensated_integrable`, `_compensated_mean`, `_Y_bounded_ae` stay for the value-function theories, `_X_martingale`, `_compensated_martingale` for `Exit_Class_Infinite`. Prose naming renamed facts updated in CPS, PSO and WM. Statement check against `b8ec93d`: 39 statements changed, all generalisations (each old form the instance `S = sconstraint k L`, `B = CARD('n)·L`, `D = L`, `θ = n − k`, `σ = I`), 54 names gone (renames to `covariation_*`, and the five retired projections); `Statement/` untouched; roots unchanged. RA 19 220 → 19 567 lines (the new theory). **Not done (left specialised, with the reason):** the `Value_Function_*` theories are the viscosity verification of the operator of Eq. (1.9), which is defined from `sconstraint` (Lemma 2.1), so they are about the paper's set; `Exit_Class_Marginals` is the bridge to the paper's density class `xclass` (Lemma 2.1 again). **Remaining for the next round:** `Exit_Class_Infinite` needs a generic infinite-horizon class (`iexit_class k L x` is defined with `sconstraint` built in, like `exit_class` was), then `Exit_Class_Expected_Exit_Time` (root; trace rate `θ`); then Lemma 2.2 for bounded `S` and Lemma 2.3 for compact convex `S`. **Lessons:** (1) `OF` with a rule-shaped hypothesis such as `B: ⋀a. a ∈ S ⟹ norm a ≤ B` — even a local assumption — leaves the trivial premise `⋀a. a ∈ S ⟹ a ∈ S` (or `… ∈ sconstraint (?k a) L` for `sconstraint_bounds`) at the FRONT of the result: harmless under a final `by (rule …)`, but it breaks `then … by (rule …)` (the chained fact meets the leftover), `erule`, `using … by blast`, and a second `by` method aimed at the main goal; pass every premise through `OF` and close with `by (rule …)`, use `simp_all`/`blast+`, or, for a paper instance inside a `using`, first `have` the instance `by (rule …)`. `where S = "sconstraint k L"` does not help. (2) `simp` did not prove `sets (kglue_law' …) = sets (path_borel T)` after the generic weak-closedness rule; `sets_kglue_law'` given explicitly did. (3) Dev loop: a throwaway base session holding the RA theories below the target plus a session with copies of the target and its dependants (imports qualified) cut iteration to 1–4 min; library sessions must be passed by their real paths (symlinked dirs made Isabelle rebuild CPS and PSO). | all sessions build |
| 2026-10-14 | `c89438a`–`e1791c6` | Phase 7 pilot G-B, third round, branch `p7C`. **Lemmas 2.2 and 2.3 for an abstract `S`** (`c89438a`, in `Exit_Class_Optimizer`): `covariation_class_relatively_compact` (`S` bounded, of positive semidefinite matrices) and `covariation_class_compact` (`S` compact, of positive semidefinite matrices), from the `B`/`D` forms through `psd_diag_le_norm` (a diagonal entry of a psd matrix lies in `[0, norm a]`, so `B = D`). Round 2's guess that Lemma 2.3 needs psd to supply `D` is confirmed; the paper's convexity hypothesis is not needed (closedness under weak limits needs only `closed S`), so the formal Lemma 2.3 is stronger. **`Exit_Class_Infinite`** (`73e4926`): new `icovariation_class S x`, `icovariation_val S K x`, with `iexit_class_eq_icovariation`, `iexit_val_eq_icovariation_val` (the paper definitions unchanged); cut, both halves of the value identification, the extension (the continuation is Brownian motion pushed through any `σ` with `σ σᵀ ∈ S`, so `ibmpair`, `ibm_law`, `iextend` take `σ`; the old ones are `σ = mat 1`) and the identification at large horizons (trace rate `θ`, norm bound `B`) for closed convex `S`; paper instances kept: `iexit_val_eq_exit_val_ball` (Paper_Map), `_horizon` (`Value_Function_Uniqueness`). **`Exit_Class_Marginals` + `_Expected_Exit_Time`** (`d769af3`, one commit: the second uses the first's renamed lift lemmas): new `xcovariation_class S x`, `xcovariation_val S K x` (laws of `X` alone, density form) with bridges `xclass_eq_xcovariation`, `xval_eq_xcovariation_val` (`xclass_def`/`xval_def`, displayed by Statement, unchanged); the identification of the pair class with the `X`-class and of the two value functions holds for every closed convex `S` of psd matrices with entries bounded by `D` (`qvmata (4 D)`; boundedness from the entry bound, `bounded_of_entry_bound`). Refuted: round 2 left `Marginals` specialised as "the bridge to `xclass` (Lemma 2.1)"; the bridge reads the paper's set only through psd and the entry bound. The roots `iexit_class_marginal_in_xclass`, `xclass_lift_in_iexit_class` and `iexit_val_eq_xval` (Theorem_1_1, Faithfulness_Checks) are one-step instances. The expected exit time (root theory, `.*`) for `icovariation_class S` / `xcovariation_class S` with trace rate `θ` and entry bound `D`; `xclass_expected_exit_time` (Paper_Map) is the instance; the wildcard root covers the renamed helpers (`roots.txt` unchanged). `Exit_Class` gains `sconstraint_psd_entry`. **`Value_Function_Subsolution`** (`dead611`): its class part generic: the DPP capped at a `[0,T]`-valued time, optional sampling at a path stopping time (`covariation_class_*_stopped`, `_stopped_moments/_var/_normsq`), the averaged covariation at a stopping time lies in a closed convex `S` (`covariation_class_Y_stopped_mean_in`), the localised subsolution inequality (`covariation_val_subsol_quadratic_stopped`, `_ball`: some `b ∈ S` has `−tr(M b)/2 ≤ 1`); `exit_val_subsol_quadratic_stopped` stays as the instance its user needs. **`Value_Function_Euler_Construction`** (`0308fe6`): `covariation_class_weak_limit`, `covariation_class_increment_tail(_norm)`. **Gate (S-generic; max proof growth, `gate.py` with the `i`/`x` renames mapped):** `Exit_Class_Infinite` 29/33 (88 %; +17 %, `iextend_cut_in_covariation_class` 6→7; `ibmpair_measurable` +14 % for `σ`), `_Marginals` 20/25 (80 %; +7 %), `_Expected_Exit_Time` 5/6 (83 %; +18 %, `icovariation_class_entry_bound` 11→13); not gated (about the operator of Eq. (1.9)): `Value_Function_Subsolution` 13/22 (+14 %), `_Euler_Construction` 11/22 (+17 %, from round 2). **Retired** as their users moved: `exit_class_X_martingale`, `_compensated_martingale`, `_Y_bounded_ae`, the six `iexit_class_*` and four `xclass_*` projections. `exit_class_*` left: `prob`, `sets` (Statement), `start` (`Value_Function_Subsolution`, `_Case_2`, `_Tangential_Field`), `compensated_integrable`, `compensated_mean` (Euler). Statement check against `22edd57`: 17 statements changed, all generalisations (old = `S = sconstraint k L`, `B = CARD('n)·L`, `D = L` diagonal or entry bound, `θ = n − k`, `σ = mat 1`), 46 names gone (renames, retired projections); `Statement/` and `roots.txt` unchanged. RA 19 567 → 19 911 lines. **Left specialised, with the reason:** `Value_Function_Supersolution_Case_1/_2`, `_Tangential_Field`, `_Assembly`, `_Uniqueness`, the rest of `_Subsolution` and the Euler scheme: the viscosity verification for the operator of Eq. (1.9), defined from `sconstraint` (feasible and orthogonal directions, the tangential field), and the Euler constants (`xiC M L`, `sqrt L`) read off the cap `L`. **Lessons:** (1) `obtain … by (rule lemma[OF psd bd])` with a rule-shaped `psd` failed even under `by (rule …)` (an `obtains` conclusion); restate as a plain lemma and obtain the bound from `bounded_pos`. (2) `σ ** transpose σ ∈ S` does not fix the row type of `σ`: a theorem with `σ` only there needs `σ :: real^'n^'n` in `fixes`, or `OF` against `iextend σ` fails with "no unifiers". (3) a `@{thm}` antiquotation in a text before the fact is defined is an error. | all sessions build |
| 2026-10-14 | `697d7ba`–`ce4a78e`, `ebaa277` | Phase 7 pilot G-B, fourth round, branch `p7C`: the value-function theories, read again for what is about the class and what is about the operator of Eq. (1.9). Refuted: round 3's "the Euler constants (`xiC M L`, `sqrt L`) are read off the cap `L`" — the cap enters only as a diagonal bound, so the Euler scheme is generic. **`Value_Function_Euler_Construction` + `_Supersolution_Case_1`** (`697d7ba`, one commit: Case 1 applies every Euler lemma): the Euler kernel, the Euler process, its class membership, the variance bound of the grid functional (`xiC M D`), Chebyshev, the weak limit, conditional orthogonality, the quadratic lower bound along the grid, the vanishing bad event and the limit member with its growth (`eulerp_*`) for a closed convex `S` with `B`, `D` and a continuous field `SF z SF zᵀ ∈ S`; the single-matrix lemmas take what they read (`sbm_xi_mean0`, a root, drops all hypotheses: the singleton class `{S Sᵀ}` supplies the compensated mean; `sbm_entry_bound` and the variance bounds read one diagonal bound). Only `rotSF_exists` (the field is built from a `feasible` witness) stays specialised. **`Value_Function_Subsolution`** (`c3ddb03`): the anti-concentration dichotomy `covariation_val_touch_near_orth` (closed convex `S`, `B`, `D`, `σ σᵀ ∈ S`; time scale `1/(2n(D+1))` for `1/(2n²L)`, via the new `trace_le_diag_bound`) and its compactness step `covariation_val_touch_orth` (plus: `S` of psd matrices), `covariation_val_zero_outside` (any `S`); the paper instance `exit_val_subsol_quadratic_stopped` lost its only user and went. **`Value_Function_Uniqueness`** (`f871712`): clauses (0) and (1) of Theorem 1.1 for abstract `S`: `covariation_val_real_bounded`, `_ball_upper` (`B`, trace bound `θ > 0`), `covariation_val_real_usc` (closed `S`, `B`, `D`, `σ σᵀ ∈ S`), and for the infinite horizon `icovariation_val_le_ball_bound`, `icovariation_val_real_usc` (closed convex `S`); `exit_val_ball_fin` gives way to `covariation_val_neq_top`; `Theorem_1_1`'s `xval_bounded`/`xval_usc` (root, statements unchanged) instantiate them. **`Value_Function_Supersolution_Case_2`** (`ce4a78e`): `covariation_val_cap_inert` (`B`, `θ`), `case2_separation` for any function; `Exit_Class_Witness` gains `sconstraint_trace_bounds`, the `(B, θ)` bundle of `sconstraint k L`. **Gate (S-generic statements; max proof growth, `gate.py` with the renames mapped):** `_Euler_Construction` 22/22 (100 %; +0 %, six proofs shrank by 1–71 %), `_Case_1` 10/11 (91 %; +1 %, `eulerp_quad_lower_region` 136 → 137 lines), `_Subsolution` 17/22 (77 %, was 13/22; −1 % on the moved proofs), `_Uniqueness` 5/16, `_Case_2` 2/11 (not gated: Theorem 1.1 itself and the supersolution property of Eq. (1.9)); a few paper instances grew where they now pass the bundles (`theorem_1_1_uniqueness_faithful` 31 → 34, `exit_val_supersol_lsc_bounded` 5 → 7, `xval_bounded` 14 → 17, `xval_usc` 2 → 10 lines). `gate.py` reports a spurious +536 %/+1271 % where a removed `exit_val_*` instance maps onto an already existing `covariation_val_*` fact. **Retired:** `exit_class_compensated_integrable`, `_compensated_mean` (`3a466ec`), `exit_class_start` (`ebaa277`); `exit_class_*` left: `prob`, `sets` (Statement; `sets` also in `_Case_2`, `_Tangential_Field`). Statement check against `1380586`: 18 statements changed, all generalisations (old = `S = sconstraint k L`, `B = CARD('n)·L`, `D = L`, `θ = n − k`, `σ = mat 1`, psd by `sconstraint_psd_entry(1)`), 16 names gone (renames, retired instances and projections); `Statement/` and `roots.txt` unchanged since `b8ec93d`. RA 19 911 → 19 935 lines. **Left specialised, with the reason:** `_Tangential_Field` (the subspace-tangential field lies in `sconstraint` through `feasible`), `_Assembly` and the rest of `_Case_2`, `_Uniqueness`, `Theorem_1_1` (the operator of Eq. (1.9) and the paper's Theorem 1.1, Example 3.1). **Lessons:** (1) `OF` with a rule-shaped fact always leaves a premise; when the instance is closed (no schematic left, e.g. a local `B`), `[…, simplified trivial_premise_simps]` (new in `Exit_Class`: `implies_True_equals triv_forall_equality True_implies_equals`) removes it and leaves the conclusion untouched, so `note`/`using … by blast` work again; with `sconstraint_bounds` the leftover keeps a schematic `?k` and the rule must close under `by (rule …)`. (2) `bexI[OF X P]` with such an `X` misplaces `P` onto a leftover (`THM 0`); write `by (rule bexI[OF _ P]) (rule X)`. (3) `using that … by (rule …)` feeds `that` to the first premise, now a leftover: pass `that` through `OF`. (4) `where k = k` on a multi-conclusion lemma fails if one conclusion lacks `k`. (5) `field_simps` distributes `D + 1`; name it (`Dp`). | all sessions build |

**State after phase 2:** 104 811 lines (baseline 120 586 at `41fca32`), of which RA 53 206
(was 64 995), SOVA 16 687 (18 461), CPS 11 352 (13 503). Dead code: 196 lines, all kept on
purpose. Oracles on the roots: none.

### Phase 4 tools

The phase 4 runs used one git worktree and one Isabelle home per group, a two-slot build
lock, and a statement check against the base commit; the scripts are in
`notes/review_3/phase4_tools/` (their paths point to the session scratch directory and
must be adjusted). Two concurrent builds on a 15 GB machine fit only with
`--maxheap 4G` and `-Xmx1500m` per build. The per-chunk and per-review reports of round 2
are in `data/phase4/round2-results.json`; the branches themselves are merged.
