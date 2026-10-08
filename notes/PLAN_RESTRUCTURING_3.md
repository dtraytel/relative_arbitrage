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
| G-G (D9) | rework SOVA's `Viscosity_Solutions` into two generic predicates, parametrised by the operator, the set and the touching locality, covering the six used variants including `env2` | the six paper predicates are joined to them by proved equations (not abbreviations); `Statement` still displays what the authors expect |
| G-D | widen the ≈ 600 SOVA lines fixed to `real^'n` that mention no matrix, and the ≈ 110 toolkit statements typed at a product codomain they never inspect | uniform sort per layer first (PLAN_2 §11's lesson); `-o timeout=900` |
| G-F | drop the avoidable hypotheses: `ess_inf_pexit_usc` (`probs`, `prob`; *checked*), `jensen_lemma`'s `0 < ρ` | none needed |

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
| 2026-10-08 | (this commit) | independent-interest review (§1.3), design panel (§1.4), roots extended to ≈ 520 entries, this revision | analysis re-run against the new roots |
| 2026-10-08 | `61a7e9f` | Phase 2.2–2.4: empty theories, smooth ball strand (with the global `[simp del]`), `Dynamic_Programming_Kernels` | all sessions build |
| 2026-10-08 | `040c0c5` | Proposition 2.4 for the horizon-`T` value (pilot, D4); Lemma 3.1 in `Paper_Readings` | all sessions build |
| 2026-10-08 | `277512b` | roots: 23 COROLLARY verdicts that keep their name | — |
| 2026-10-08 | `518daa6` | Theorem 4.2(a) for usc/lsc data (pilot, D3); `Expected_Exit_Times` in CTM and its class corollary (pilot, D2) | all sessions build |
| 2026-10-08 | `d00dc3b` | Phase 2.5–2.7: the dead blocks of 52 theories against the 552 roots, by script (`delete_dead`: lemma blocks with no live fact and no remaining mention in code, texts that mention only deleted facts, emptied headers, unused definitions named nowhere else); `Moment_Bounds` emptied and deleted; `eigen_ub_diag` kept (FIX_THEN_KEEP); six facts the analysis called unused but live proofs still name are kept. A second pass found 196 dead lines left, all kept on purpose (interpretation-generated facts, facts named in proofs): fixpoint reached | all sessions build |
| 2026-10-08 | `ad9add6` | Phase 3a: `Pair_Path_Space` no longer imports SOVA (`Sup_Convolution`, `Doubling_Of_Variables`) or WM's finite-dimensional distributions; its one use was a copy of HOL's `norm_Pair_le`. `Exit_Class_Infinite` imports `Exit_Class_Pasting` | all sessions build |
| 2026-10-08 | `643de89` | analysis loads every leaf theory (483 theories, 575 roots; dead lines unchanged) | — |
| 2026-10-08 | `980b6fe` | Phase 2.8: 152 mentions of deleted lemmas in the prose of 31 theories rewritten (six writers on disjoint files, six reviewers) | all sessions build |

| 2026-10-08 | (this commit) | Phase 3.3: every theory imports exactly the maximal theories it needs (`minimize_imports.py`: needs are named facts and constants used in proofs, locales used by name, facts, constants and theories named in antiquotations, and every current HOL/AFP ancestor, kept for notation). 59 theories changed. Critical path through user theories: **280 s over 25 theories** (baseline 577 s over 35; acceptance ≤ 418 s; bound with needed dependencies only: 274 s) | all sessions build |

**State after phase 2:** 104 811 lines (baseline 120 586 at `41fca32`), of which RA 53 206
(was 64 995), SOVA 16 687 (18 461), CPS 11 352 (13 503). Dead code: 196 lines, all kept on
purpose. Oracles on the roots: none.

