# Restructuring plan II

A second refactoring pass over the whole development, asking of every lemma:

1. **Is it as general as it can cheaply be?** — is every hypothesis used, can the
   type be widened, is it stated about the object it is really about?
2. **Is it useful to somebody who does not care about this paper?**
3. **Is it in the right place** — right session, right theory, right layer?

and turning the answers into a target layout, a per-theorem disposition, a
generalisation catalogue and a deletion catalogue.

The first plan (`git show 4aba476:PLAN_RESTRUCTURING.md`) split six sessions into
eight, split five oversized theories and, in a final pass, moved 167 lemmas
out of the paper session. It closed the
question it asked — *which lemmas mention no project-defined constant at all* —
and that number is now 21. **This plan asks the harder version of the same
question: which lemmas mention no constant of _this paper_.** That number is
571, in 23 000 lines, and it is where the remaining reusable mathematics is.

**This is refactoring only.** Every change below is a move, a rename, a
deletion, a type widening, or the replacement of a fixed constant by a
parameter the proofs already treat as opaque. Nothing here asks for a new
mathematical argument. Items that could turn into one are marked **gated** and
carry an abandon rule.

---

## 0. Method, and how to re-run it

Everything quoted below is produced by `notes/restructuring_2/probes.py`
(with `thy_parse.py` beside it):

```bash
python3 notes/restructuring_2/probes.py
```

| probe | what it answers |
|---|---|
| `probe0` | parser self-check against `grep`; **must print 0 mismatches** |
| `probe1` | inventory: lines, statements, definitions per session |
| `probe2` | how paper-bound each `Relative_Arbitrage` statement is |
| `probe3` | statements that name nothing from their own session |
| `probe4` | statements equal up to renaming of short variables |
| `probe5` | statements named nowhere else (dead-code candidates) |
| `probe6` | direct imports from which nothing is named |

`notes/restructuring_2/dispositions.tsv` is the per-theorem output: one row per
top-level statement in the repository (2 754 of them), with the theory it is in,
the disposition (`STAY`, `MOVE`, `SPLIT`, `STAY-OR-UPSTREAM`, and a `UNUSED?`
flag), the target theory, and the rule that produced the row. §4 explains how to
read it, and where it must not be trusted blindly.

**One measurement trap, again.** The first plan warned that a comment stripper
counting `(*` depth goes unbalanced inside cartouches. There is a second, worse
one: the term `(*v)` — the matrix-vector product written as a bare operator —
*opens a comment* for any stripper that does not know it is inside a string
literal. Before this was fixed, the probe reported 1 lemma in
`Doubling_Of_Variables` instead of 141, and 93 in `Matrix_Algebra` instead of
147, and both misreadings looked entirely plausible. `thy_parse.scan` now tracks
string literals and cartouches; `probe0` is the guard, and it must be run after
every phase, because a silent re-break invalidates every other number.

---

## 1. The development as it stands

104 theories, 116 624 lines, 2 754 top-level statements, 194 definitions,
21 locales, 18 sublocales, no `sorry`.

| session | lines | statements | definitions |
|---|---:|---:|---:|
| `Symmetric_Matrix_Spectra` | 7 467 | 311 | 12 |
| `Semicontinuous_Analysis` | 2 318 | 71 | 8 |
| `Second_Order_Viscosity_Analysis` | 12 225 | 390 | 14 |
| `Wiener_Measure` | 1 617 | 50 | 9 |
| `Continuous_Time_Martingales` | 8 741 | 314 | 34 |
| `Continuous_Path_Spaces` | 11 355 | 264 | 23 |
| `Relative_Arbitrage` | 72 592 | 1 338 | 124 |
| `Relative_Arbitrage_Statement` | 413 | 16 | 0 |

`Relative_Arbitrage` is 62% of the lines and 49% of the statements. Of its
1 338 statements (`probe2`):

| bucket | statements | lines |
|---|---:|---:|
| statement mentions a constant **of this paper** | 767 | 46 131 |
| statement mentions only the **path toolkit** (`pcut`, `pglue`, `pexit`, `pstopped`, `path_stopping_time`, ...) | 404 | 16 590 |
| statement mentions only **lower sessions**, or nothing | 160 | 6 532 |
| statement mentions some other `Relative_Arbitrage` name | 7 | 477 |

**Four out of every ten statements in the paper session say nothing about the
paper.** That is the headline; §2 says what they are.

---

## 2. Findings

### 2.1 Finding A --- the path toolkit is the last buried library (404 statements, 16 590 lines)

Twenty-five definitions in `Relative_Arbitrage` are operations on paths and on
laws of paths, with no reference to the constraint set, the operator or the
value function:

| group | constants | declared in |
|---|---|---|
| cutting and splicing | `pcut`, `pglue`, `pfst`, `padd`, `pembed`, `prebase`, `pfut`, `pdel`, `pshift`, `iglue`, `ploc`, `pcoord` | `Exit_Class_Pasting`, `Dynamic_Programming_*` |
| stopping | `pstopped`, `pafter`, `path_stopping_time`, `pre_sigma_of`, `dyceil` | `Dynamic_Programming_Kernels`, `..._Optional_Sampling` |
| exit times | `pexit`, `iexit`, `pstep`, `vshift`, `rclamp` | `Exit_Semicontinuity`, `Exit_Class_Infinite`, `Exit_Time_Semicontinuity` |
| laws and kernels | `pair_law_of`, `pglue_law`, `pshift_law`, `kglue`, `kglue_law`, `aglue_law` | `Exit_Class_Witness`, `Exit_Class_Pasting`, `Exit_Class_Optimizer`, `Dynamic_Programming_Additive_Glue` |
| essential infimum | `ess_inf_time`, `ess_inf_enn` | `Value_Function_Market`, `Exit_Class_Infinite` |

and 404 statements are about nothing else. The definitions are one-liners of
function surgery:

```isabelle
pcut S w       = restrict w {0..S}
pglue r T w w' = restrict (%t. if t <= r then w t else w r + (w' (t-r) - w' 0)) {0..T}
pstopped T th w = restrict (%t. w (min t (th w))) {0..T}
pafter T th w   = restrict (%t. w (max t (th w)) - w (th w)) {0..T}
```

What sits on top of them is the measurable and law-level theory: that these maps
are measurable and continuous; that `path_stopping_time` behaves like a stopping
time and `pre_sigma_of` like the sigma-algebra of its past; that a law can be cut
at a stopping time and glued back to a kernel of continuations; that the glued
law is a probability measure with the right marginals; that the essential
infimum of an exit time is upper semicontinuous under weak convergence. That is
the measure-theoretic infrastructure of *any* dynamic programming argument in
the martingale-problem formulation — Larsson–Ruf Proposition 2.2 is exactly this
— and today none of it is reachable without importing a paper about relative
arbitrage.

Two whole theories are already 100% free of paper constants:
`Exit_Semicontinuity` (19 of 19 statements, 1 282 lines) and
`Dynamic_Programming_Optional_Sampling` (17 of 17, 593 lines).

The obstruction to calling it a library today is the **type**: everything is
stated at

```isabelle
type_synonym 'n pairpath = "real => (real^'n) * (real^'n^'n)"
```

Of the 404 statements, 53 mention neither the pair structure nor any measure —
pure function surgery, generalisable on the statement line; 48 more are
measure-theoretic but never look at the pair; 303 mention `fst`, `snd` or
`real^'n` somewhere. §5 (G1) is the type-generalisation programme, and §7 makes
the promotion to a session *conditional on its result*, because a "library"
pinned to this paper's pair type would not be one.

### 2.2 Finding B --- the second-order extraction stopped half-way

160 statements in `Relative_Arbitrage` name only material from lower sessions.
84 of them are in `Comparison_Principle`, and they are not scattered: they are
the rest of three clusters whose other half the first plan moved out.

| cluster | in `Second_Order_Viscosity_Analysis` | still in `Comparison_Principle` |
|---|---:|---:|
| `soft_pen`, `soft_grad`, `soft_hess`, `soft_shrink`, `quartic_pen` | 27 (`Soft_Penalty`) | 29 |
| `supconv_*` | 16 (`Sup_Convolution`) | 38 |
| `doubling_*`, `doubled_*`, `*jet*`, `block_*` | 45 (`Doubling_Of_Variables`) | 19 |

`Soft_Penalty` defines `soft_pen` and proves its radial and Lipschitz
properties; `Comparison_Principle` proves that its Hessian is symmetric, its
exact second-order expansion, its jet, its coercivity and its continuity —
general facts about a concrete penalty function, 6 000 lines from the
definition, inside a theory about a maximum principle. The same split runs
through the sup-convolution and the doubling material.

The other 76 of the 160 are elsewhere: 20 pure HOL, 20 matrix facts belonging in
`Symmetric_Matrix_Spectra`, about 30 measure-theoretic facts belonging in
`Continuous_Time_Martingales`/`Continuous_Path_Spaces`, 4 Gaussian facts
belonging in `Wiener_Measure`.

### 2.3 Finding C --- Brownian motion is stranded on the wrong side of a session boundary

`Brownian_Market.thy` (1 802 lines) and `Brownian_Continuous.thy` (439 lines)
sit in `Relative_Arbitrage`. What they contain is:

* independence of the past and an increment, under the Wiener measure and under
  the `n`-fold product (`wiener_pre_past_increment_indep`,
  `bm_paths_past_increment_indep`, `bm_filtration_increment_indep`);
* the `n`-dimensional product Brownian model `bm_paths` and its coordinate
  moments;
* the vector process `bmX x t w = x + (w_i t)_i`, its integrability, its
  martingale property (`martingale_bmX`) and the compensated square
  (`martingale_bm_square`, `martingale_bm_coord_square`);
* a continuous modification `Bcont`, the continuous vector process `cbmX`, and
  the same two martingale theorems for it.

Exactly two statements out of 51 mention a market constant. This is the
canonical vector Brownian motion with its martingale properties: the natural
content of `Wiener_Measure`, which today stops at the one-dimensional
construction and its continuous modification.

It is not there because of a **session boundary**: `Wiener_Measure` is based on
`HOL-Probability` + `Kolmogorov_Chentsov` and does not see the AFP's
`Martingales`, so it cannot say the word `martingale`. The first plan's
completion note recorded two lemmas stuck for this reason and concluded that
"moving them means moving a session boundary". That is the right diagnosis, and
moving it costs one import.

### 2.4 Finding D --- the viscosity predicates are welded to one operator

`Viscosity_Definitions.thy` holds ten predicates — `visc_subsol`,
`visc_supersol`, `visc_sol`, their `_env`, `_env2` and `_lsc` variants,
`supersol_jet`, `max_principle_boundary(_raw)` — all of the shape

```isabelle
visc_subsol k L Om u <-> (ALL x:Om. ALL phi g H. test_fun_at phi g H x -->
                            (touching) --> ell_op k L (g x) H <= 1)
```

with the operator `ell_op k L` and the level `1` hard-wired. Also there:
`test_fun_at` and `test_fun_C2`, which mention no operator at all and are pure
differential calculus ("`phi` is differentiable near `x` with gradient field `g`
and Hessian `H` at `x`"), and `expandable`, a purely geometric property of a set
(it can be expanded by a rotation-dilation-translation).

Nobody outside this paper can use any of it, and the cost of unwelding is small
and measured: the ten `_def` equations are unfolded in **52 places in the whole
repository** (`visc_subsol_def` 12, `visc_supersol_env2_def` 9, ...; plus
`test_fun_at_def` 32, which moves unchanged). A generic layer
`visc_subsol_gen F Om u` with the paper's predicate as an abbreviation

```isabelle
abbreviation visc_subsol k L == visc_subsol_gen (%p M. ereal (ell_op k L p M))
```

leaves every proof text alone except at those 52 sites, half of which are in the
definitions' own theory.

### 2.5 Finding E --- the class is welded to one constraint set (gated)

`exit_class k L T x` is the set of laws `Q` on the pair path space with: `Q` a
probability measure on the path sigma-algebra; `(X,Y)` starting at `(x,0)`; every
difference quotient of `Y` in `sconstraint k L`; `X` a martingale;
`outerp X - Y` a martingale. Exactly one of those five clauses mentions the
paper: the third, through `sconstraint k L`.

The interface that the 30 000 lines above it use of that set is small — by grep
over `Exit_Class*`, `Dynamic_Programming_*`, `Value_Function_*`:
`closed_sconstraint` (14 uses), `sconstraint_norm_le` (7),
`sconstraint_convex` (5), `sconstraint_trace_le`/`_ge` (8),
`sconstraint_orth_feasible` (4), `sconstraint_diag` (3),
`bounded_sconstraint` (2) — but `sconstraint_def` itself is unfolded **22
times**, and each of those is a place where a proof looks past the abstraction.

Replacing `k L` by a set parameter `S` (better: a locale fixing `S` with those
seven properties) would turn the DPP layer into "the dynamic programming
principle for a martingale problem with a compact convex covariation
constraint", which is a genuinely reusable theorem. It is also the most
expensive item here and the only one that can turn into mathematics, at those 22
sites. Scheduled last, gated, in a worktree, with a hard abandon rule (§7,
phase 11).

### 2.6 Finding F --- duplicates that survived the first pass

From `probe4`, plus targeted reading. `probe4` renames identifiers of six
characters or fewer, so it also reports pairs that differ only in a short
constant — `sets_bm_fdd`/`space_bm_fdd`, `convex_eigen_ub`/`closed_eigen_ub`,
`sconstraint_convex`/`closed_sconstraint`, `stopped_expectation`/`optional_sampling`,
`Xmeas`/`Ameas`, `path_stopping_time_min`/`_max`, and the locale-scoped
`stopped_integrable` pair. Those seven are **not** duplicates. The seven that
are, plus six more found by reading, are:

| # | duplicate | where | verdict |
|---|---|---|---|
| 1 | `trace_conj` / `trace_conjugate` | `Matrix_Algebra`:692 / :584 — **same file**, character-identical statement *and* proof | delete `trace_conj`; its `text` still claims it is "a local copy ... so that this theory need not import the `Operator_Envelopes` chain", which stopped being true when both moved |
| 2 | `bounded_linear_trace_mult_left` / `trace_mult_blin` | `Matrix_Algebra`:1235 / :1460 | keep one |
| 3 | `matrix_vector_mult_scaleR_gen` / `matvec_scaleR_right` | `Matrix_Algebra`:252 / :818 | keep one |
| 4 | `matrix_vector_mult_vec_diff` / `matvec_diff_right` | `Matrix_Algebra`:662 / :813 | keep one |
| 5 | `trace_matrix_commute` | `Matrix_Algebra`:798 | **HOL-Analysis has it**: `Determinants.trace_mul_sym`, at `'a::comm_semiring_1^'n^'m`, strictly more general. Delete, redirect |
| 6 | `transpose_scaleR` | `Matrix_Algebra`:150 | **HOL-Analysis has it**: `Finite_Cartesian_Product.transpose_scalar`. Delete, redirect |
| 7 | `convex_on_prod_add` / `convex_on_proj_sum` | `Doubling_Of_Variables`:795 / `Theorem_On_Sums`:348 | keep the `Theorem_On_Sums` one |
| 8 | `content_box_translate` / `content_cbox_translate` | `Rademacher`:1505 / :1725 | keep one |
| 9 | `Z_zero_expectation` / `Z_zero_expectation_const` | `Ito_Market`:149 / :643, two locales | one `ito_market_core` locale, one lemma — the first plan's §5.4, never executed |
| 10 | `ito_expected_stopped_time_bound` / `expected_stopped_time_bound` | `Ito_Market`:277 / `Volatile_Market`:236 | same statement in two locales; same fix |
| 11 | `outerp x = (chi i j. x$i * x$j)` vs `outer_prod u v` | `Exit_Class`:215 vs `Outer_Products` | make `outerp` an abbreviation for `outer_prod x x` — the first plan's §5.1, never executed |
| 12 | `ess_inf_time :: _ => ('a => real) => ennreal` / `ess_inf_enn :: _ => ('a => ennreal) => ennreal` | `Value_Function_Market` / `Exit_Class_Infinite` | one `ess_inf` on `ennreal`; `ess_inf_time M tau == ess_inf M (ennreal o tau)` — the first plan's §4.4, never executed |
| 13 | elementary power inequalities | `sq_diff_le` (`Quadratic_Variation`), `square_add_le_two` (`Moment_Bounds`), ~20 more in `Increment_Moments`, `Pathwise_Quadratic_Variation` | `Continuous_Time_Martingales/Power_Inequalities.thy` — the first plan's §5.5, never executed |

Nothing shadows anything any more: `probe1` finds 8 repeated declared names, all
locale-scoped and legitimate (`P`, `Tgt`, `Tgt_sets_F`, `Tgt_sets_M`,
`stopped_integrable`, and three `ito_*` locale headers). That part of the first
plan held.

**A sweep that has never been run**: *does HOL-Analysis already have this?*
Items 5 and 6 were found by accident, both in `Matrix_Algebra`, which is 147
short statements about traces, transposes and matrix products. §7 phase 1
schedules a `find_theorems` pass over that theory and over `Semicontinuity`,
`Outer_Products` and `Convex_Subgradients`.

### 2.7 Finding G --- 137 statements are named nowhere, and the record of that is stale

`probe5` lists 137 statements that no other statement, proof or comment names.
Most are the deliverable of their chain (`theorem_1_1`, `comparison_ball`,
`example_3_1_closed_form`) or the public face of a library theory, and stay. But
18 are in `Comparison_Principle` and 10 in `Doubling_Of_Variables` — the two
theories that lost material to the first plan's phases 7-8. They are what the
cascade left behind.

`notes/UNUSED_THMS.md` is stale: it lists `Exit_Class_DPP`,
`Value_Function_Viscosity`, `Deterministic_Radius_Market`,
`Exit_Class_Compactness`, `Eigenvalues` and a `Relative_Arbitrage`
`Poincare_Separation`, none of which have existed since the first plan. Its
*method* section is still the best description of how to run the analysis; its
data is worthless. Regenerate it, do not patch it.

### 2.8 Finding H --- two idioms that should be one word

* `borel_of (mtopology_of (path_metric T))` appears **332 times**, 306 of them in
  `Relative_Arbitrage`, and 95 times as the bare hypothesis
  `sets Q = sets (borel_of (mtopology_of (path_metric T :: ('n pairpath) metric)))`.
  An `abbreviation path_borel` in `Continuous_Path_Spaces.Path_Space` costs
  nothing — abbreviations unfold at parse time, so no proof changes — and makes a
  quarter of the class layer readable.
* The standing hypotheses of the paper layer are repeated by hand: `1 <= L` 189
  times, `k < CARD('n)` 122, `1 <= k` 104, `0 <= T` 212, `closed K` 80,
  `compact K` 25. A locale would collect them; that is a much larger change than
  an abbreviation, and it is gated (§5, G10).

### 2.9 Finding I --- import hygiene

`probe6` finds 18 direct imports from which nothing below is ever named. Two are
in the toolbox sessions and worth fixing for their own sake (`Soft_Penalty`
imports `Doubling_Of_Variables`; `Theorem_On_Sums` imports
`Symmetric_Matrix_Spectra.Matrix_Algebra`); the rest are `Relative_Arbitrage`
theories carrying imports their content no longer needs. Removing an import is
only safe when the build agrees — an imported theory may still be needed for a
`[simp]`/`[measurable]` declaration the text never names. Candidates, one build
each.

### 2.10 Finding J --- sizes are healthy except in five places

The first plan's "no theory over 12 000 lines" is achieved: 1 theory over 7 000
lines, 5 between 3 000 and 5 000, 98 under 3 000.

| theory | lines | why it should still be split |
|---|---:|---|
| `Comparison_Principle` | 7 731 | 84 of its 158 statements leave in phase 3; what remains is four separable arguments (§3.7) |
| `Dynamic_Programming_Conditioning` | 4 570 | two parts: conditioning on the past (1-3 997) and the conditional law / DPP statement (3 998-end) |
| `Value_Function_Euler_Construction` | 3 984 | two `section`s; the second (3 970 lines) is the Case 1 argument whose other half is already in `Value_Function_Supersolution_Case_1` |
| `Value_Function_Subsolution` | 3 974 | contains a self-contained matrix toolkit (sums of outer products, the threshold argument, lines 2 088-2 392) belonging in `Symmetric_Matrix_Spectra` |
| `Exit_Time_Semicontinuity` | 3 347 | its first section (1-720) is the general usc statement; the second is Lemma 2.3 for the market |

At the other end: `Moment_Bounds` (3 statements), `Stopped_Adaptedness` (1),
`Sampled_Martingale` (3), `Sampled_Quadratic_Variation` (5),
`Brownian_Optimal_Boundary` (1), `Viscosity_Comparison_Interface` (5). Small
focused theories are not a defect and most of these are fine; `Moment_Bounds`
and `Brownian_Optimal_Boundary` are fragments of their neighbours and are folded
in below.

### 2.11 What is right, and must not be "improved"

* `Symmetric_Matrix_Spectra`, `Semicontinuous_Analysis` and
  `Continuous_Time_Martingales` are correctly scoped, layered and named. Apart
  from the deletions in §2.6 they are done.
* `Path_Space` and `Path_Space_Infinite` are generic in `'b::polish_space`;
  `pexit` and `iexit` are already generic in `'b::polish_space`; `pre_sigma_of`
  is already generic in the measure. Do not re-specialise any of them.
* `Doubling_Of_Variables` and the semiconvexity calculus are at
  `'a::euclidean_space` after the first plan's phase 8. Correct.
* The locale layering of `Continuous_Time_Martingales`
  (`time_grid` -> `sampled_martingale` -> `sq_int_martingale` -> `stopped_*`) is
  the model for anything new.
* `Relative_Arbitrage_Statement` is the acceptance test and changes only when a
  constant it displays is renamed. It displays `outerp` (§2.6, item 11): that
  rename needs its surrounding prose re-read.
* The mathematics. No proof is to be improved, shortened or re-derived. A phase
  that cannot be carried out by moving text is not to be carried out.

---

## 3. Target layout

Nine sessions. Two edges change and one session is new.

```
Symmetric_Matrix_Spectra ────┬─→ Second_Order_Viscosity_Analysis ──────────┐
Semicontinuous_Analysis ─────┤                                             │
                             │                                             │
Continuous_Time_Martingales ─┼─→ Wiener_Measure  (NEW EDGE) ───────────────┤
                             │                                             │
                             └─→ Continuous_Path_Spaces ─→ Path_Space_Operations (NEW, gated)
                                                                     │     │
                                                                     └─────┴─→ Relative_Arbitrage ─→ Relative_Arbitrage_Statement
```

Each session must still be describable in one sentence that does not name this
paper. Below, "gains"/"loses" is relative to today.

### 3.1 `Symmetric_Matrix_Spectra` — unchanged in scope

*The spectral theory of real symmetric matrices that HOL-Analysis stops short
of.*

**Gains** (~35 statements, ~700 lines): `outerp` folded into `outer_prod` as an
abbreviation, with its 29 lemmas (`Exit_Class`, `Value_Function_*`); the
outer-product and threshold toolkit of `Value_Function_Subsolution`
(lines 2 088-2 392: `psd_kernel_eq`, `matvec_sum_outer`, `onormal_parseval`,
`onormal_span_parseval`, `weighted_min_value` and neighbours) into
`Outer_Products` / `Orthonormal_Families` / `Ky_Fan`; `rot_col_cont`
(`Value_Function_Supersolution_Case_1`) into `Householder_Rotation`;
`psd_diag_nonneg`, `psd_mat_1`, `psd_limit`, `psd_shifted_diff`,
`psd_of_abstract_le`, `hessian_lower_bound_of_psd`, `semiconvex_hessian_*`
into `Symmetric_Spectral`; `eigval_ge_of_subspace`, `bracket_upper_bound`,
`weighted_outer_sum_annihilates` (`Operator_Formula`) into `Ky_Fan` /
`Poincare_Separation`.

**Loses**: six duplicates (§2.6 items 1-6), two of them to HOL-Analysis.

### 3.2 `Semicontinuous_Analysis` — unchanged

Gains one statement (`tilted_local_touching` from
`Value_Function_Supersolution_Case_2`). Otherwise done.

### 3.3 `Second_Order_Viscosity_Analysis` — gains the definitional layer it was missing

*The complete second-order machinery for comparison proofs between viscosity
solutions.* Today that is true of the machinery but not of the notion: the
session proves the theorem on sums and the doubling toolbox but cannot say
"viscosity subsolution".

| theory | change |
|---|---|
| `Convex_Subgradients`, `Rademacher`, `Moreau_Envelope`, `Alexandrov`, `Jensen_Lemma`, `Theorem_On_Sums` | unchanged apart from §2.6 items 7-8 |
| `Sup_Convolution` | **gains 22** statements from `Comparison_Principle` (`supconv_bound_transfer`, `supconv_local_max_transfer(_ball)`, `supconv_onesided_descent`, `supconv_attain_radius`, `supconv_le_of_local_bound_usc`, `supconv_attained_usc_ball`, `attain_gate_of_positive`, `doubling_grad_lower_bound_supconv`, `doubling_maximiser_supconv`, `doubled_value_gap_supconv`, ...) |
| `Doubling_Of_Variables` | **gains 19** (`doubled_functional_semiconvex_gen`, `doubled_supconv_jet_exists(_shifted)(_gen)`, the block-matrix and slice lemmas still behind) |
| `Soft_Penalty` | **gains 29** — the whole `soft_*` and `quartic_*` remainder of `Comparison_Principle` (`soft_pen_expand`, `soft_pen_rem`, `soft_pen_jet_form`, `soft_hess_*`, `soft_grad_*`, `soft_shrink_lipschitz`, `soft_pen_zero/neg/mono_norm/ge_radial/coercive_outside/continuous`, `quartic_grad_derivative`) |
| **`Test_Functions.thy`** *(new)* | `test_fun_at`, `test_fun_C2`, their congruence/scaling/affine/constant lemmas (`test_fun_C2_const`, `test_fun_C2_add_const`, `test_fun_at_scaleR`, `test_fun_C2_scaleR`, `test_fun_at_affine`, `test_fun_C2_affine`, `test_fun_C2_quartic_shift`), and the jet-to-test-function bridges (`jet_test_fun_at`, `jet_test_fun_C2`, `test_fun_C2_imp_test_fun_at`, `jet_test_fun_at_abstract`). Mentions no operator |
| **`Viscosity_Solutions.thy`** *(new)* | the generic predicates of §2.4 over an abstract `F :: real^'n => real^'n^'n => ereal`: `visc_subsol_gen`, `visc_supersol_gen`, `visc_sol_gen`, the touching-over-a-set (`_env`) and `C2` (`_env2`) variants, `supersol_jet_gen`, `max_principle_boundary_gen`, and the implications between them that do not need the operator (`visc_subsol_env2_cong`, `visc_supersol_env2_mono`, `visc_supersol_env2_local`, `visc_subsol_env2_local`, `visc_subsol_env_imp_env2`, `visc_supersol_env_imp_env2`) |
| **`Expandable_Sets.thy`** *(new, small)* | `expandable` and `convex_expandable` — "a compact set that can be expanded by a rotation-dilation-translation", a hypothesis of Theorem 4.3 and a purely geometric notion |

### 3.4 `Wiener_Measure` — re-based, and finished

*Brownian motion as the projective limit of its Gaussian finite-dimensional
distributions, with independent increments, a continuous modification, and — new
— the `n`-dimensional vector process with its martingale properties.*

`ROOT`: base stays `HOL-Probability`; add `sessions Continuous_Time_Martingales`
(and keep `Kolmogorov_Chentsov`). This is the only session-graph edge added.

| theory | content |
|---|---|
| `Sorted_Lists`, `Gaussian_Increments`, `Brownian_Finite_Dimensional_Distributions`, `Brownian_Motion`, `Brownian_Motion_Continuity` | unchanged; `Gaussian_Increments` gains `gauss_measure_mean`, `gauss_measure_snd_moment`, `gauss_shifted_square` from `Brownian_Market` |
| **`Increment_Independence.thy`** *(new)* | `wiener_pre_past_increment_indep`, `bm_paths_past_increment_indep`, `bm_filtration_increment_indep`, `bmX_increment_eq` and the independence toolkit of `Brownian_Market` lines 26-200, 515-813 |
| **`Product_Brownian_Motion.thy`** *(new)* | `bm_paths`, `bmX`, coordinate moments, `martingale_bmX`, `martingale_bm_square`, `martingale_bm_coord_square` — the rest of `Brownian_Market`, whose 35 statements all move |
| **`Continuous_Brownian_Motion.thy`** *(new)* | `Bcont`, `cbmX`, `martingale_cbmX`, `martingale_cbmX_square`, `martingale_cbm_coord_square`, `cbmX_cont` — 14 of the 16 statements of `Brownian_Continuous` |

The two statements that stay — `Brownian_market_sufficiently_volatile` and
`sufficiently_volatile_market_nonvacuous`, both from `Brownian_Continuous` —
become a short `Brownian_Market.thy` in the market layer, which is what that
name should have meant all along.

### 3.5 `Continuous_Time_Martingales` — three small additions

| theory | change |
|---|---|
| **`Power_Inequalities.thy`** *(new)* | the ~25 elementary real inequalities of §2.6 item 13, collected from `Quadratic_Variation`, `Moment_Bounds`, `Increment_Moments`, `Pathwise_Quadratic_Variation`. `Moment_Bounds` (3 statements) is folded in here and disappears |
| **`Essential_Infimum.thy`** *(new)* | one `ess_inf` on `ennreal` (§2.6 item 12) and the 19 statements about it now spread over `Value_Function_Market` and `Exit_Class_Infinite` |
| `Semidirect_Kernels`, `Optional_Sampling`, `Stopping_Times`, `Natural_Filtration`, `Doob_Inequality`, `Quadratic_Variation`, `Integrability_Criteria` | gain the 19 measure-theoretic statements the `dispositions.tsv` assigns to them (`emeasure_ksemi_rect`, `AE_integrable_ksemi_section`, `ksemi_weak_conv`, `etime_shift_le_of_eroded`, `etime_shift_of_restrict`, `horizon_sq_int_martingale_stopped`, ...) |

### 3.6 `Continuous_Path_Spaces` — gains the exit-time theory

| theory | change |
|---|---|
| `Path_Space` | **gains** `abbreviation path_borel T == borel_of (mtopology_of (path_metric T))` (§2.8) and the 18 statements about the path metric/topology now in `Exit_Class*`, `Dynamic_Programming_*` (`space_of_path_sets`, `continuous_map_diffquot`, `pair_eval_coord_cont`, `mspace_path_metric_ne`, `Polish_space_path_metric`, `second_countable_path_metric`, `restrict_in_mspace`, ...) |
| **`Path_Exit_Times.thy`** *(new)* | `Exit_Semicontinuity.thy` moved whole (19 statements, 1 282 lines: `pexit`, `pstep`, the Laplace representation of the essential infimum, the portmanteau helpers, `ess_inf_pexit_usc`) plus `iexit` and its lemmas from `Exit_Class_Infinite`, plus `vshift`, `rclamp`, and the `pexit_*` statements scattered over eight paper theories. **Needs no generalisation: `pexit` and `iexit` are already at `'b::polish_space`** |
| `Pathwise_Quadratic_Variation`, `Adapted_Quadratic_Variation` | gain the 10 statements assigned to them |
| `Equicontinuity`, `Holder_Interpolation` | drop the imports `probe6` flags |

### 3.7 `Path_Space_Operations` — new, **gated on G1**

*Cutting a path at a time, restarting it, stopping it and gluing it back — and
the same four operations on laws: the measurable infrastructure a dynamic
programming principle needs.*

Content: 317 statements and 13 828 lines — the 404 of Finding A, minus the 43
exit-time statements that go to `Continuous_Path_Spaces` (§3.6), the 29 `outerp`
statements that go to `Symmetric_Matrix_Spectra` and the 19 `ess_inf` statements
that go to `Continuous_Time_Martingales`:

| theory | content | statements | lines |
|---|---|---:|---:|
| `Path_Splicing.thy` | `pcut`, `pglue`, `pfst`, `padd`, `pembed`, `prebase`, `pdel`, `pshift`, `iglue`, `ploc`, `pcoord`: the definitions, their pointwise equations, continuity, measurability | 189 | 6 231 |
| `Path_Stopping_Times.thy` | `path_stopping_time`, `pstopped`, `pafter`, `pre_sigma_of`, `dyceil`: a path functional that is a stopping time, its past, the stopped/after decomposition, the dyadic ceiling, and optional sampling on path space (`Dynamic_Programming_Optional_Sampling` moves whole) | 65 | 3 252 |
| `Path_Law_Pasting.thy` | `pair_law_of`, `pglue_law`, `pshift_law`, `kglue`, `kglue_law`, `aglue_law`: laws of concrete processes, the glued law, the kernel glue, the additive glue, their marginals and martingale clauses | 63 | 4 345 |

`Path_Splicing` at 6 231 lines is too big to stay one theory, and its provenance
says where to cut: 38 statements come from `Exit_Class_Limits`, 29 from
`Dynamic_Programming_Conditioning` (the `pfut` conditioning material: regular
conditional distributions on path space and their sections), 23 from
`Dynamic_Programming_Delayed_Class`, 16 from `Exit_Class_Pasting`. Split it into
`Path_Splicing.thy` and `Path_Space_Conditioning.thy` along that line at the end
of phase 6, once the real sizes are known.

**The gate.** This session is worth creating only if the material is stated at a
general path codomain. Today 303 of the 404 statements of Finding A mention
`fst`, `snd` or `real^'n`. G1 (§5) generalises the definitions to `real => 'b`
and the statements with them. Promote to a session when **at least 220 of the
317 are free of the pair type**; otherwise stop, keep the theories inside
`Relative_Arbitrage` as its lowest layer — which is still a large readability
win — and record the count. Do not promote a "library" that only works for
`(real^'n) * (real^'n^'n)`.

**Name.** If the block ends up dominated by the law-level results rather than
the path-level ones, `Path_Law_Pasting` is the better session name and
`Path_Space_Operations` becomes a theory in it. Decide after G1, not before.

### 3.8 `Relative_Arbitrage` — what is left, in six layers

After the moves: about 47 000 lines. The layers below are the order of the
`ROOT` `theories` list, and each is a `subsection` of the session's `root.tex`.

**L1 — the operator (Eqs. (1.5), (1.9), Lemma 2.1, Lemma 3.1)**

`Curvature_Operator` is misnamed — it defines `eigen_lb`, `eigen_ub`,
`feasible`, `ell_op`, `ball_v` and contains no curvature operator. Rename to
**`Elliptic_Operator.thy`**. Then: `Constraint_Set_Convexity`,
`Eigenvalue_Bound_Exact`, `Operator_Continuity`, `Operator_Formula`,
`Operator_Envelopes`, `Operator_Envelope_Continuity`, unchanged apart from
extractions. The `feasible_*` bounds at the tail of `Viscosity_Solutions`
(`feasible_diag_bound`, `feasible_offdiag_abs_le`, `feasible_bounded`) move here.

**L2 — viscosity solutions of *this* operator**

`Viscosity_Definitions.thy` keeps only the instantiations of §3.3's generic
predicates (ten abbreviations plus `ell_op_pair`, `ell_op_lsc`, `ell_op_usc`)
and the implications that need the operator's own calculus.
`Viscosity_Ball`, `Viscosity_Solutions` and `Viscosity_Comparison_Interface`
are one argument spread over three files (Example 3.1 as a smooth solution,
comparison against it, uniqueness on the ball without Crandall-Ishii): merge
into **`Ball_Solution.thy`**.

**L3 — comparison** — `Comparison_Principle` (7 731 lines) loses 84 statements
to §3.3 and splits at its own section boundaries into

| theory | content | source lines |
|---|---|---|
| `Comparison_Jets.thy` | the jet interface, Definition 3.1 with genuine `C2` test functions, the jet-to-test-function bridges that mention `ell_op` | 1-252, 2 251-3 450 |
| `Comparison_Strictness.thy` | `F` reads only the symmetric part; where strictness comes from; scaling a subsolution; the shifted-bound family | 253-1 600 |
| `Comparison_Localisation.thy` | locating the doubling maximiser away from the boundary, the parameter threading, the Skolemised family, the bounded-family contradiction | 4 431-6 736 |
| `Comparison_Assembly.thy` | reduction to bounded continuous data, the two branches, `max_principle_boundary`, uniqueness on a compact set, the map of the chain | 6 737-end |
| `Comparison_Two_Domain.thy` | unchanged |

**L4 — markets** — `Volatile_Market`, `Ito_Market` (with the `ito_market_core`
locale of §2.6 item 9), `Brownian_Market` (now 60 lines),
`Brownian_Optimal_Boundary` (1 statement; fold into `Optimal_Exit_Time`),
`Optimal_Exit_Time`, `Value_Function_Market`, `Path_Tightness_Market`,
`Exit_Time_Semicontinuity` (split: the general first section goes to
`Continuous_Path_Spaces`, Lemma 2.3 stays).

**L5 — the class and the dynamic programming principle** — `Exit_Class`,
`Exit_Class_Limits`, `Exit_Class_Tightness`, `Exit_Class_Shift`,
`Exit_Class_Witness`, `Exit_Class_Pasting`, `Exit_Class_Optimizer`,
`Exit_Class_Infinite`, `Exit_Class_Marginals`, `Dynamic_Programming_*`. Each
keeps only its class-specific half; the path-level half leaves in phase 6.
`Dynamic_Programming_Conditioning` splits at line 3 998 into
`Dynamic_Programming_Conditioning` and `Dynamic_Programming_Conditional_Law`.

**L6 — the value function and the theorem** — `Value_Function_Subsolution`,
`Value_Function_Euler_Construction` (split at its second `section` into
`Value_Function_Euler_Construction` and `Value_Function_Rotating_Field`),
`Value_Function_Supersolution_Case_1`, `_Case_2`, `Value_Function_Tangential_Field`,
`Value_Function_Assembly`, `Value_Function_Uniqueness`.

### 3.9 `Relative_Arbitrage_Statement` — unchanged

It moves only if a constant it displays is renamed: `outerp` (§2.6 item 11) is
the only one scheduled.

---

## 4. The per-theorem disposition

`notes/restructuring_2/dispositions.tsv` has one row per top-level statement:

```
session  theory  name  line  lines  disposition  target  rule
```

| disposition | rows | meaning |
|---|---:|---|
| `STAY` | 2 075 | stays in its theory (possibly renamed or split-renamed) |
| `MOVE` | 591 | moves to `target`, 24 905 lines in total |
| `SPLIT` | 76 | stays in `Relative_Arbitrage` but changes theory under §3.8's splits |
| `STAY-OR-UPSTREAM` | 12 | names nothing project-defined at all: candidates for HOL/AFP, else stay |

with a `/UNUSED?` suffix wherever `probe5` found no other mention (137 rows).
Move totals by destination:

| destination | statements | lines |
|---|---:|---:|
| `Path_Space_Operations/Path_Splicing` | 189 | 6 231 |
| `Path_Space_Operations/Path_Law_Pasting` | 63 | 4 345 |
| `Path_Space_Operations/Path_Stopping_Times` | 65 | 3 252 |
| `Continuous_Path_Spaces/Path_Exit_Times` | 43 | 1 722 |
| `Wiener_Measure/Product_Brownian_Motion` | 35 | 1 802 |
| `Wiener_Measure/Continuous_Brownian_Motion` | 14 | 245 |
| `Second_Order_Viscosity_Analysis/*` | 70 | 2 338 |
| `Symmetric_Matrix_Spectra/*` | 44 | 923 |
| `Continuous_Time_Martingales/*` | 38 | 1 796 |
| `Continuous_Path_Spaces/*` (other) | 29 | 2 167 |
| `Semicontinuous_Analysis/Semicontinuity` | 1 | 84 |

**How much of the table to trust.** The `rule` column says how each row was
derived, and the rules differ in reliability:

* *"paper statement"*, *"locale-bound"* — reliable; these are `STAY`.
* *"uses only X"* — reliable as a **permission** (the statement and the proof
  name nothing above `X`), not as an **instruction**: a step of a paper argument
  that happens to be stated in general terms may still read better next to its
  consumer. The executing agent decides; the default is to move, and the reason
  to keep is that the lemma is a scaffold with one consumer.
* *"statement only in path-toolkit terms"* — reliable for the four target
  theories being distinguished by which constant appears; where a statement
  mentions constants of two groups, the row picks by the priority
  laws > stopping > splicing > exit times, and the executing agent should
  re-read those.
* *"no project dependency: pure HOL"* — 12 rows; each needs a `find_theorems`
  check before it is moved anywhere.

The table is a work-list, not an oracle. Where it is wrong, the plan is wrong
(§8 rule 5).

---

## 5. Generalisations to try

Ordered by (value x confidence) / cost. Each says what to change, why it should
work, and what to do when it does not. **No entry here licenses a new proof.**

### G1 — the path toolkit: `'n pairpath` ⟶ `real => 'b` — *high value, medium-high confidence*

`'n pairpath = real => (real^'n) * (real^'n^'n)`. What the seventeen surgery and
stopping operations ask of the codomain is: nothing at all (`pcut`, `pstopped`,
`pembed`, `pshift`, `pfut`, `pdel`, `pcoord`, `pfst`, `ploc`), or `+` and `-`
(`pglue`, `pafter`, `padd`, `prebase`, `iglue`). Counts below are over the 404
statements of Finding A; the gate in §3.7 is over the 317 of them that reach the
new session.

*Method*, in three waves, each a separate commit:

1. **The definitions.** Restate the twelve splicing and five stopping
   definitions at `real => 'b` (`'b::real_normed_vector` where the definition
   subtracts, `'b` unconstrained otherwise). Nothing downstream should notice:
   `'n pairpath` is an instance.
2. **The 101 statements that never mention the pair** (53 pure surgery, 48
   measure-theoretic — `probe2` and the `pair=` column of the work-list).
   Change the `fixes`/type annotation, leave the proof. Precedent: the first
   plan widened 59 doubling and 32 semicontinuity lemmas this way with a 100%
   success rate and no proof edited.
3. **The 303 that do.** Split them: those that mention the pair only because
   the *type* is a pair (`fst (w t)` used as "the first component of whatever
   the path takes values in") generalise to `'b * 'c`; those that mention
   `real^'n` because they multiply matrices do not generalise and stay.

*Expected*: wave 1 free, wave 2 ≥ 90%, wave 3 perhaps half. The gate in §3.7 is
220 of 317.

*If a statement resists*: leave it at the pair type, in the same theory, with a
one-line comment saying which wave it failed and why. Do not weaken it, do not
prove anything new. Record the count; it is the gate's input.

*Watch for*: `path_stopping_time` (below, G5) and everything about the natural
filtration of the pair process — those genuinely read the components.

### G2 — the viscosity predicates over an abstract operator — *high value, high confidence*

§2.4. Add to `Second_Order_Viscosity_Analysis/Viscosity_Solutions.thy`

```isabelle
definition visc_subsol_gen ::
  "(real^'n => real^'n^'n => ereal) => (real^'n) set => (real^'n => real) => bool"
  where "visc_subsol_gen F Om u <-> (ALL x:Om. ALL phi g H. test_fun_at phi g H x -->
            (EX e>0. ALL y : ball x e. u y - phi y <= u x - phi x) --> F (g x) H <= 1)"
```

and the eight siblings, then in `Relative_Arbitrage/Viscosity_Definitions.thy`

```isabelle
abbreviation visc_subsol :: "nat => real => (real^'n) set => (real^'n => real) => bool"
  where "visc_subsol k L == visc_subsol_gen (%p M. ereal (ell_op k L p M))"
```

*Why it should work*: an `abbreviation` is unfolded at parse time, so every
statement that mentions `visc_subsol` still parses and every proof that does not
unfold the definition is untouched. The 52 sites that unfold `*_def` need the
`_gen` name instead; `grep -n 'visc_[a-z_]*_def\|supersol_jet_def\|max_principle_boundary_def'`
lists them exactly.

*Level*: keep `<= 1` rather than normalising to `<= 0`. The paper's equation is
`F = 1` and rewriting it would touch every consumer for no gain.

*If it fails*: the failure mode is an abbreviation that will not typecheck
because `ell_op`'s `k`/`L` cannot be inferred at a use site. Then use a plain
`definition` plus a `[simp]` unfolding lemma, and accept editing the 52 sites.

*Do not* try to generalise the comparison **proof** to an abstract `F` in this
phase. That is G11's sibling and is not scheduled.

### G3 — `soft_pen` at `'a::euclidean_space` — *medium value, medium confidence*

`soft_pen kappa x = kappa * (sqrt (norm x^2 + 1) - 1)`-shaped: it uses `norm`
and `inner` only. 11 of the 27 statements in `Soft_Penalty` mention no matrix.
`soft_hess` is a `real^'n^'n` and cannot move; so the theory would end up split
between two type generalities.

*Method*: widen `soft_pen`, `soft_shrink` and their 11 lemmas; leave
`soft_grad`/`soft_hess` and everything about them at `real^'n`. Do it **after**
the 29 statements of §3.3 have arrived, not before, or the same work is done
twice.

*If the split reads badly* (a theory half at `euclidean_space` and half at
`real^'n`), abandon and record: the penalty is used only at `real^'n` here.

### G4 — one essential infimum — *medium value, high confidence*

§2.6 item 12. `ess_inf M f = Sup {c. AE w in M. c <= f w}` on `ennreal`, in
`Continuous_Time_Martingales/Essential_Infimum.thy`; `ess_inf_time M tau` becomes
an abbreviation for `ess_inf M (ennreal o tau)`. The `ess_inf_time_*` and
`ess_inf_enn_*` lemma pairs collapse to one copy each (19 statements to 12 or so).

*If a proof breaks*: it will be one where `ennreal o tau` does not fold. Keep
`ess_inf_time` as a `definition` with an unfolding lemma instead.

### G5 — `path_stopping_time`: which continuity? — *design decision, do not guess*

```isabelle
path_stopping_time T th <-> (ALL w. 0 <= th w & th w <= T)
  & (ALL w w'. continuous_on {0..T} (%t. fst (w t)) --> continuous_on {0..T} (%t. fst (w' t))
      --> (ALL t : {0..th w}. w t = w' t) --> th w' = th w)
```

The continuity is required of the **first component only**. That is deliberate
(the memory of the development records that both paths need continuity, and that
this weakening is what unblocked stochastic localisation), and it is *not*
equivalent to continuity of the whole path. Under G1 the natural generalisation
is "continuous_on {0..T} w" for the whole path, which is a **different, stronger
hypothesis** and therefore a weaker theorem at every use site.

*Instruction*: parameterise instead — `path_stopping_time_on C T th` with `C` the
continuity predicate the definition quantifies over, and define both instances.
If that costs more than an hour, leave `path_stopping_time` at the pair type and
record it as a wave-3 failure of G1. **Do not silently change which component is
required to be continuous.**

### G6 — `pexit` and `iexit` — *low value, high confidence*

`iexit K f = (SUP T:{0..}. ennreal (pexit T K f))` is already defined from
`pexit`; the two families of lemmas are not shared. Merge them into
`Path_Exit_Times.thy` and delete whichever of each pair is derivable in one
line. Worth doing only because the two are moving into the same theory anyway.

### G7 — hypotheses that are stronger than the proof needs — *low value, medium confidence, mechanical*

Three families, each checked the same way: delete the hypothesis, rebuild the
theory, keep the change if it is green and revert it otherwise. There is no way
to do this by reading, and no reason to do it by guessing.

* `prob_space Q` where `finite_measure Q` or `subprob_space Q` would do — 34
  occurrences as an explicit hypothesis, mostly in the class layer.
* `'b::polish_space` where `'b::metric_space` would do — 82 sort constraints in
  the repository; the candidates are the `pexit`/`iexit` lemmas that use only an
  infimum and set membership.
* `closed K` alongside `compact K` (25 sites have both).

*Budget*: one afternoon, then stop. This is the lowest-yield item here.

### G8 — `ito_market_core` — *medium value, high confidence*

§2.6 items 9-10. `Ito_Market` declares `ito_volatile_market`,
`ito_stopped_market`, `ito_const_horizon_market` and proves the same Dynkin
identity in two of them (`Z_zero_expectation` / `Z_zero_expectation_const`,
`dynkin_quadratic_holds` / `const_dynkin_quadratic`); `Volatile_Market` proves
`expected_stopped_time_bound` a third time in `sufficiently_volatile_market`.
Introduce `ito_market_core` carrying the identity, make the three locales
sublocales, delete the copies. This is the first plan's §5.4, unexecuted.

### G9 — `path_borel` — *high value, zero risk*

§2.8. An `abbreviation`, not a `definition`: unfolded at parse time, so no
proof anywhere changes, and 332 occurrences of a 42-character term become one
word. Do it in phase 2, before anything moves, so that later diffs are moves
rather than reformattings.

### G10 — the standing hypotheses as a locale — *gated*

`1 <= L` (189), `k < CARD('n)` (122), `1 <= k` (104), `0 <= T` (212). A locale
`eigenvalue_constraint` fixing `k`, `L` with those assumptions would delete
about 600 hypothesis lines and make the paper layer readable.

*Why it is gated*: a locale fixes the type variable `'n` too, `Statement`
must still display the theorems with explicit hypotheses, and locale
interpretation interacts with the `'n::finite` sort constraints in ways that
cannot be predicted by reading.

*Pilot*: `Operator_Formula` alone (44 statements). If it goes through with no
proof edited and `Statement` still displays what it displays, continue with L1;
otherwise abandon the whole item and record the failure. **Do not start L4/L5.**

### G11 — the class over an abstract constraint set — *gated, last*

§2.5. `exit_class S T x` for a set `S` of matrices, with the paper's class as
`exit_class (sconstraint k L) T x`, and the seven structural facts
(`closed`, `convex`, `bounded`, the norm bound, the two trace bounds, the
diagonal bound, orthogonal feasibility) carried as hypotheses of the lemmas that
need them.

*Why it is worth trying*: it turns 30 000 lines about one paper's constraint
into a dynamic programming principle for a martingale problem with a compact
convex covariation constraint — the most reusable single object in the
development.

*Why it is gated*: 22 proofs unfold `sconstraint_def`. Each is a place where an
abstract `S` needs a named fact instead of the definition, and if that fact does
not exist the item becomes mathematics.

*Protocol*: in a worktree, on `Exit_Class.thy` alone. Count how many of its 45
statements need a hypothesis added, and how many of the 22 unfolding sites are
in it. **Abandon the item if more than three sites need a fact that does not
already exist**, and record the count in the completion note. Do not attempt
`Dynamic_Programming_*` until `Exit_Class`, `Exit_Class_Limits` and
`Exit_Class_Pasting` are green.

### G12 — non-generalisations: record and move on

State these so nobody spends a week on them.

* **`Path_Tightness`'s vector layer stays at `real^'m::finite`.** The first plan
  marked it speculative; it is a real proof change (index-set bookkeeping) and
  it is out of scope. Do not attempt.
* **The martingale index type stays `real`.** The first plan tried and refuted
  this: the lemmas fix `t0 = 0`, quantify over `0 <= i` and subtract `X 0`.
  Refuted once is enough.
* **The comparison proof stays specific to `F`.** Only the *definitions* are
  abstracted (G2). The proof consumes `ell_op_lsc_elliptic_le`,
  `ell_op_strict_contradiction`, `ell_op_scaleR_p`, `ell_op_M_gap`,
  `eq36_rhs_antitone` and the `feasible` calculus; a locale over "any degenerate
  elliptic `F` with a strictness property" is a design exercise, not a
  refactor.
* **`Increment_Moments` stays real-valued.** The vector case is obtained
  coordinatewise at the call sites; that is the right design and the first plan
  said so.
* **The spectral theorem stays at `real^'n^'n`.** An operator version is a
  different theorem.
* **`test_fun_at`'s Hessian stays a matrix.** A bilinear-form version would be
  more general and would disconnect it from `Symmetric_Matrix_Spectra`, where
  every consumer lives.

---

## 6. Deletions and hygiene

Do these first: they are pure subtraction and they shrink the input to
everything else.

### 6.1 Duplicates (§2.6)

Items 1-8 are deletions of one of two identical statements; items 5 and 6 are
deletions in favour of HOL-Analysis (`trace_mul_sym`, `transpose_scalar`).
Items 9-13 are the five unexecuted items of the first plan (`ito_market_core`,
`outerp`, `ess_inf`, `Power_Inequalities`, and the two-locale
`expected_stopped_time_bound`).

For each: `grep -rn '\bname\b' --include='*.thy' .` before the deletion, so the
number of expected edits is known in advance; fix the uses, do not leave an
alias.

### 6.2 The "is it already in HOL?" sweep

Two of 147 statements in `Matrix_Algebra` were re-proofs of HOL-Analysis
lemmas, and both were found by accident. Run the sweep properly, with
`find_theorems` in the PIDE session, over:

* `Symmetric_Matrix_Spectra/Matrix_Algebra` — all 147;
* `Symmetric_Matrix_Spectra/Outer_Products` — 7;
* `Semicontinuous_Analysis/Semicontinuity` — 12 (the AFP has
  `Lower_Semicontinuous`, which this session already builds on: check that the
  eps-delta calculus is not a second copy of it);
* `Second_Order_Viscosity_Analysis/Convex_Subgradients` — 15 (HOL-Analysis has a
  convexity library and the AFP has more).

Method: for each statement, `find_theorems` on its conclusion pattern with the
repository's own theories excluded. Record hits in the completion note even when
the lemma is kept for its `[simp]` attribute or its more convenient form.

### 6.3 Dead code

Re-run `unused_thms` as `notes/UNUSED_THMS.md` describes (its method section is
still correct), intersect with `probe5`, and delete the intersection minus:

* the deliverables of `Relative_Arbitrage_Statement` and the headline theorem of
  each chain;
* anything in a library session that is deliberate API (a library may export a
  lemma nothing here uses — that is what a library is for).

Expect the cascade to run through `Comparison_Principle` (18 unnamed statements)
and `Doubling_Of_Variables` (10). Then **rewrite** `notes/UNUSED_THMS.md`: its
data names six theories that have not existed since the first plan.

Six definitions are reachable from nothing (`visc_sol_env`, `quartic_pen`,
`Yint`, `pairX`, `pairY`, `tanpV`, per the old note). Decide each explicitly:
`pairX`/`pairY` are the paper's own notation and should either be used or
deleted; do not leave them as decoration.

### 6.4 Imports

The 18 candidates from `probe6`, one build each (§2.9).

### 6.5 Names

* `Curvature_Operator.thy` -> `Elliptic_Operator.thy` (it defines no curvature
  operator).
* `Viscosity_Ball` + `Viscosity_Solutions` + `Viscosity_Comparison_Interface`
  -> `Ball_Solution.thy`.
* `Brownian_Market.thy` keeps its name but keeps only market content (§3.4).
* Constant renames stay out of scope, with one exception: `outerp` disappears
  into `outer_prod` (§2.6 item 11), and `Relative_Arbitrage_Statement` displays
  it, so its surrounding prose must be re-read in the same commit.

---

## 7. Execution order

Thirteen phases. Each ends with a green `isabelle build -d . <session>` for
every session in `ROOTS`, a run of `probes.py probe0`, and one commit. No phase
depends on a later one. Phases 1-5 are mechanical and shrink the input to
everything after; phases 10-11 are gated and may end in "abandoned, recorded".

| # | phase | risk | size |
|---|---|---|---|
| 1 | **Delete.** §6.1 items 1-8 and §6.2's sweep of `Matrix_Algebra`. No file moves. | low | −300 lines |
| 2 | **`path_borel` and the first plan's five unexecuted items.** §6.1 items 9-13 (`ito_market_core`, `outerp`, `ess_inf`/`Essential_Infimum.thy`, `Power_Inequalities.thy`, the duplicated locale bound) and G9's abbreviation. Nothing moves session yet. | low | −400 lines, 332 sites reformatted |
| 3 | **Finish the second-order extraction.** The 70 statements of §3.3 into `Soft_Penalty`, `Sup_Convolution`, `Doubling_Of_Variables`; then split `Comparison_Principle` per §3.8 L3. | medium | 3 100 lines relocated |
| 4 | **Re-base `Wiener_Measure`.** Add `sessions Continuous_Time_Martingales` to its `ROOT`; move `Brownian_Market` (35) and `Brownian_Continuous` (14) into the three new theories of §3.4; leave the two market statements behind. | medium | 2 050 lines relocated |
| 5 | **`Path_Exit_Times`.** `Exit_Semicontinuity` whole, plus `iexit`, `vshift`, `rclamp` and the scattered `pexit_*`, into `Continuous_Path_Spaces`. No generalisation needed — these are already at `'b::polish_space`. Also the 18 path-metric statements into `Path_Space`. | low | 2 850 lines relocated |
| 6 | **Carve the path toolkit inside `Relative_Arbitrage`.** Create `Path_Splicing`, `Path_Stopping_Times`, `Path_Law_Pasting` (and `Path_Space_Conditioning`, see §3.7) *as theories of the paper session*, at the pair type, and move the 317 statements into them. The class layer above them must then mention no `pcut`/`pglue`/`pstopped` internals — if it does, the split point is wrong. | medium | 13 828 lines relocated |
| 7 | **G1 waves 1-2.** Generalise the definitions and the 101 pair-free statements to `real => 'b`. Count what widened. | medium | 0 net |
| 8 | **G1 wave 3 and the gate.** The pair-mentioning statements; count again. **If ≥ 220 of 317 are pair-free**, promote the four theories to the session `Path_Space_Operations` (new `ROOT`, `root.tex`, `ROOTS` entry, §3.7); otherwise stop, keep them as the paper session's lowest layer, and write the count into the completion note. | medium | 0 net |
| 9 | **G2.** `Test_Functions.thy`, `Viscosity_Solutions.thy`, `Expandable_Sets.thy` in `Second_Order_Viscosity_Analysis`; `Viscosity_Definitions.thy` becomes ten abbreviations plus the operator-specific implications. | medium | 0 net |
| 10 | **G10 pilot** (`Operator_Formula`), then L1 if green, else abandon and record. | gated | −600 lines if it lands |
| 11 | **G11 pilot** (`Exit_Class` in a worktree), then the class layer if green, else abandon and record. | gated | 0 net |
| 12 | **Split what is still oversized.** §2.10: `Dynamic_Programming_Conditioning`, `Value_Function_Euler_Construction`, `Value_Function_Subsolution`'s matrix toolkit (to `Symmetric_Matrix_Spectra`), `Exit_Time_Semicontinuity`. Rename per §6.5. | low | 0 net |
| 13 | **Sweep and document.** §6.3 (`unused_thms` to convergence), §6.4 (imports), rewrite `notes/UNUSED_THMS.md`, update every `ROOT` description and `root.tex` that changed, refresh `NOTES_FOR_AUTHORS.md`'s infrastructure section with the new session names, re-run all probes and write the completion note. | low | −500 lines |

### 7.1 Mechanics

* **Build after every theory move**, not after every phase. Ten moves between
  builds costs more than ten builds.
* **Move the `text ‹…›` block that precedes a lemma with the lemma.** The running
  commentary is an asset of this development; the first plan found 28 blocks
  that had been stranded and had to be rewritten, and the objective test it
  arrived at is the one to use here: *does this comment name an identifier that
  is declared only in `Relative_Arbitrage`?* If so it cannot go into a library
  session unedited.
* **Numbered results of the paper carry `\<^cite>\<open>LaiShkolnikovSoner\<close>`.**
  Keep that when moving; add it where a moved comment mentions "Lemma 2.3" and
  does not cite.
* **A green build does not prove that nothing is duplicated** — it proves that no
  name collides. After each phase, re-run `probe4` and `probe1`'s duplicate
  check over the moved names.
* **Session splits**: `ROOTS` entry, `ROOT` with the one-sentence description
  from §3, `document/root.tex` and `root.bib` copied and trimmed from the
  nearest neighbour, and the `theories` list in dependency order.
* **`Relative_Arbitrage_Statement` builds last, every phase.** If
  `Theorem_1_1_Statement.thy` still compiles and still displays the same
  definitions, the refactor preserved the deliverable. This is the acceptance
  test.
* **Commits**: one per phase, or one per theory inside phases 3, 5, 6 and 12.
  Existing style — imperative, lowercase after the session prefix.

### 7.2 The measurements to report

At the start and the end of every phase, and in the completion note:

| metric | today | target |
|---|---:|---|
| statements whose statement mentions a constant of this paper, in `Relative_Arbitrage` | 767 | 767 (invariant: this is the paper) |
| statements in `Relative_Arbitrage` that do **not** | 571 | < 120 |
| lines in `Relative_Arbitrage` | 72 592 | ≈ 47 000 |
| largest theory (lines) | 7 731 | < 3 500 |
| duplicate statement groups (`probe4`) | 14 reported, 7 real | 0 real |
| statements named nowhere (`probe5`) | 137 | < 60 |
| unused direct imports (`probe6`) | 18 | 0 |
| `sorry` | 0 | 0 |

---

## 8. Rules for the executing agent

1. **Do not prove new mathematics.** Every change here is a move, a rename, a
   deletion, a type widening or an abbreviation. If a change needs a new proof
   step, revert it and record it in the completion note.
2. **Never weaken a statement to make a move work.** If a lemma will not move
   without changing what it says, it stays where it is, and the reason goes in
   the note. G5 is the specific trap: the continuity hypothesis in
   `path_stopping_time` is deliberate.
3. **`sorry` is forbidden**, including transiently. The development's claim is
   that it contains none, and a commit that introduces one breaks that claim in
   the history.
4. **Run `probes.py probe0` after every phase.** A parser that silently blanks
   half a file (§0) makes every other number in this plan a fiction.
5. **When a prediction here is wrong, this plan is wrong, not the
   development.** Record the discrepancy; do not force the layout. The first
   plan's completion note is the model: it recorded four refuted predictions and
   two over-deliveries, and that record is why this plan could be written.
6. **Gated items (G10, G11) are pilots first.** Do the named pilot theory, count
   what the plan said would happen, and stop if the count is worse. An abandoned
   gated item with a recorded count is a success; a half-converted class layer is
   not.
7. **No abbreviated theory or session names.** The first plan's naming rules
   still bind: spell words out, name the subject rather than the method or the
   headline theorem, no filler nouns (`Extras`, `Misc`, `Utils`, `Aux`,
   `Toolkit`, `Machinery`, `Support`, `Base`). Proper names (`Ky_Fan`,
   `Rademacher`, `Alexandrov`, `Berge`) are not abbreviations.
8. **Constant renames are out of scope** except `outerp` (§6.5).
9. **Preserve `(*<*) … (*>*)` markers and `document = false` settings.** They are
   what keeps the `Statement` document to five pages.

---

## 9. The three questions, answered

**(1) Generality.** The library sessions are stated at the right generality;
the first plan's widening of the doubling and semicontinuity material held, and
`Path_Space`, `pexit`, `pre_sigma_of` and the Crandall-Ishii layer are already
as general as they should be. Three things are not, and all three are
*definitional* rather than proof-level: the path toolkit is pinned to this
paper's pair type when it uses at most `+` and `-` (G1, 404 statements); the
viscosity predicates are pinned to this paper's operator when the operator
appears once, applied, in each of them (G2, 10 definitions, 52 unfolding sites);
and the class is pinned to this paper's constraint set when four of its five
clauses never mention it (G11, gated). Beyond those, the hypotheses that look
redundant (`prob_space` for `finite_measure`, `polish_space` for
`metric_space`, `closed` beside `compact`) are worth about an afternoon (G7),
and there is no lemma in the development carrying an unused hypothesis of
substance that reading could find.

**(2) Usefulness to others.** 571 of the 1 338 statements in the paper session —
23 000 lines — say nothing about the paper. They are four coherent libraries:
the path toolkit (404 statements: cutting, gluing, stopping, restarting paths
and their laws — the infrastructure of any dynamic programming argument in the
martingale-problem formulation); the vector Brownian motion with its martingale
properties (49 statements, stranded only by a session boundary); the rest of the
Crandall-Ishii toolbox (70 statements whose other half is already extracted);
and the viscosity-solution notion itself (10 definitions that nobody outside can
instantiate). Everything else that was reusable was extracted by the first plan
and is where it should be.

**(3) Placement.** Two theories are in the wrong session outright
(`Brownian_Market`, `Brownian_Continuous`) and two more are 100% paper-free
where they stand (`Exit_Semicontinuity`, `Dynamic_Programming_Optional_Sampling`).
A definition and its calculus are 6 000 lines apart in three separate clusters
(`soft_pen`, `supconv_*`, `doubling_*`). One theory name describes something it
does not contain (`Curvature_Operator`), one argument is spread over three files
(the ball solution), and one 42-character term is written out 330 times. The
layout of §3 fixes all of it, and phases 1-6 deliver most of the benefit for
about a third of the work.

---

## 10. Completion note

Phases 1--13 were executed in order, each ending with a green
`isabelle build -d . <sessions>` and one commit.  There is no `sorry`, and
`Relative_Arbitrage_Statement` -- the acceptance test -- builds unchanged
throughout.

### The measurements of §7.2, re-run

| metric | before | after | target |
|---|---:|---:|---|
| statements in `Relative_Arbitrage` whose statement names a constant of this paper | 767 | 709 | invariant |
| statements in `Relative_Arbitrage` that do **not** | 571 | 425 | < 120 |
| ...of which sit inside the new path-toolkit layer | 0 | 349 | — |
| ...outside it | 571 | 76 | < 120 |
| lines in `Relative_Arbitrage` | 72 592 | 64 445 | ≈ 47 000 |
| largest theory | 7 731 | 4 023 | < 3 500 |
| real duplicate statement groups (`probe4`) | 7 | 0 | 0 |
| `sorry` | 0 | 0 | 0 |

Sessions gained: `Second_Order_Viscosity_Analysis` 12 225 → 15 809,
`Continuous_Path_Spaces` 11 355 → 13 506, `Wiener_Measure` 1 617 → 3 801,
`Continuous_Time_Martingales` 8 741 → 9 280, `Symmetric_Matrix_Spectra`
7 467 → 7 601.  111 theories in place of 104.

The line target for `Relative_Arbitrage` was not met and could not be: it
assumed the path toolkit would leave the session, and phase 8's gate says it
should not, yet.  The number that matters is the fourth row: **76 statements
outside the path layer still say nothing about the paper**, down from 571.

### What each phase did

1. Eight duplicated lemmas deleted, two of them re-proofs of HOL-Analysis
   (`trace_mul_sym`, `transpose_scalar`).
2. `path_borel` for the 332 spellings of the path Borel algebra; the
   essential infimum given one definition in `Continuous_Time_Martingales`;
   `Power_Inequalities` for 22 elementary real inequalities; the two one-line
   re-exports in `Ito_Market` deleted.
3. 71 statements (2 428 lines) of soft penalty, sup-convolution, doubling and
   psd facts into `Second_Order_Viscosity_Analysis` and
   `Symmetric_Matrix_Spectra`; `Comparison_Principle` split into four.
4. `Wiener_Measure` re-based over `Continuous_Time_Martingales` and given the
   n-dimensional Brownian motion (49 statements, 2 050 lines).
5. `Path_Exit_Times` in `Continuous_Path_Spaces`: `Exit_Semicontinuity` whole,
   plus 38 further statements.
6. The path toolkit carved out of the class layer: 414 statements, 16 546
   lines, four theories naming no constant of the paper.
7. Ten path operations widened from `'n pairpath` to `real ⇒ 'b`.
9. The test-function class moved into `Second_Order_Viscosity_Analysis`
   (1 240 lines), and the viscosity notions stated there for an arbitrary
   operator, with five bridge equations in the paper session.
12. `Pair_Path_Space` and `Path_Law_Pasting` split at their section
    boundaries.
13. Section headers, `ROOT` descriptions, `dispositions.tsv` and this note.

### Predictions that were wrong

* **`outerp` cannot be an abbreviation** (§6.1 item 11).  It typechecks and
  then breaks four proofs in `Value_Function_Subsolution` and one in
  `Value_Function_Supersolution_Case_1`: an abbreviation is unfolded in every
  simp set that mentions it, and the searches diverge -- reported as
  `Interrupt_Breakdown`, the ML heap giving out, not as a failed step.  The
  duplication is removed instead by `outerp_eq_outer_prod`.  The same
  reasoning then applied to the viscosity predicates in phase 9, which is why
  those got bridge equations rather than abbreviations.
* **Phase 8's gate fails, and the session is not created.**  Of the 317
  statements the plan wanted pair-free, 11 are.  `path_stopping_time` is the
  obstruction G5 half-anticipated: its continuity clause asks for continuity
  of the *first component* of the path, which is deliberate and is not
  expressible at a general codomain without deciding what a first component
  is.  Everything whose statement mentions it stays at the pair type.  The
  four theories therefore remain inside `Relative_Arbitrage`, as its lowest
  layer, which is where phase 6 put them.
* **`ito_market_core` is not worth its price** (§6.1 item 9).  The two
  locales share ten assumptions, but the entire yield of a shared ancestor is
  two one-line wrappers, against rewriting three locale-instantiation proofs,
  two of them fifty-line enumerations.  The wrappers were deleted instead.
* **`Moment_Bounds` does not disappear** (§3.5).  What is left of it after
  the inequality leaves is Eq. (2.7) of the paper: a named result, not a
  fragment.

### The mechanical lesson of the moves

Moving a proof is easy; moving its prose is not.  A `text` block carries
`@{theory ...}`, `@{const ...}` and `@{thm [source] ...}` antiquotations, and
at the destination some name a theory that is no longer an ancestor, some
name a fact declared *later in the same file*, and some are split across a
line break so a line-based rewriter cannot see them.  All three failed a
build in turn.  About 160 antiquotations are now plain prose.  Two further
traps cost a build each: a block of moved lemmas must be topologically
sorted against its new neighbours, and the sort must not sweep up the
closing `end`.

### The two gated items, measured and not started

* **G10 (standing hypotheses as a locale).**  The pilot theory
  `Operator_Formula` has 44 statements, of which 11 carry two or more of
  `1 ≤ k`, `k < CARD('n)`, `1 ≤ L`, and 21 carry exactly one.  A locale would
  delete about thirty hypothesis lines in the pilot, against fixing `'n` for
  the whole layer and re-checking what `Statement` displays.  The ratio does
  not justify starting; the count is the record.
* **G11 (the class over an abstract constraint set).**  `Exit_Class` unfolds
  `sconstraint_def` six times, and five of those are inside the proofs of
  `sconstraint_convex`, `closed_sconstraint`, `sconstraint_norm_le`,
  `bounded_sconstraint` and `sconstraint_diag` -- exactly the facts that would
  become the locale's assumptions, so they leave the abstract layer rather
  than blocking it.  That is more encouraging than §2.5 predicted.  The 16
  remaining unfoldings are downstream, in `Exit_Class_Pasting`,
  `Dynamic_Programming_*` and `Value_Function_*`.  Not started; the
  measurement says the item deserves a serious attempt.

### What is left

* The 76 statements outside the path layer that still name no paper
  constant, mostly in `Operator_Formula`, `Operator_Envelopes` and
  `Exit_Time_Semicontinuity`.  Each needs a judgement rather than a rule.
* The measure-theoretic half of G1: `path_borel`, `path_metric` and the
  measurability statements at `'b::{polish_space,real_normed_vector}`.  Nine
  were tried and reverted in phase 7 because their proofs use metric lemmas
  that have not been widened; the order to do it in is bottom-up.
* A fresh `unused_thms` pass (§6.3).  `probe5` gives the textual half; the
  proof-term half needs the ML run described in `notes/UNUSED_THMS.md`.
* The `find_theorems` sweep of §6.2, beyond the four library duplicates that
  turned up by accident (`trace_mul_sym`, `transpose_scalar`, `trace_I`, and
  `content_cbox_translate` inside the session).

---

## 11. G11 and the product codomain, after the fact

Two items the completion note left open were taken up afterwards.

### The path stopping time at a product codomain

Phase 8's gate failed on `path_stopping_time`, whose continuity clause reads
the *first component* of the path.  At a **product** codomain that clause has
a meaning, and the definition is now

```isabelle
path_stopping_time :: "real ⇒ ((real ⇒ 'a::topological_space × 'b) ⇒ real) ⇒ bool"
```

with the whole session rebuilding and no proof edited.  Eleven statements
about it widen with it, at
`'a::{topological_space,ab_group_add} × 'b::ab_group_add`.

Three do not, and they mark where the next wave starts: `padd_stopping_time`,
`pstopped_padd` and `pafter_padd` go through `padd_fst_continuous`, which is
still stated with `pairX` — the pair-typed abbreviation for `fst` — so the
general `fst` does not unify with it.  The generalisation propagates
bottom-up through the continuity and measurability helpers; they have to be
widened before their consumers, not after.  The gate itself is unchanged
until that is done.

### G11: the class over an abstract constraint set

The pilot measurement first, since it is what justified starting: **243
statements in the paper session mention `exit_class` or `exit_val`, and 13
of them use any property of `sconstraint k L`.**  Of the 6 `sconstraint_def`
unfoldings in `Exit_Class`, 5 are inside the proofs of the very facts that
become the abstract interface, so they leave the abstract layer rather than
blocking it.  §2.5 expected the abstraction to be expensive; it is not.

What is now in place, in the paper-free layer:

* `covariation_class S T x` — the laws of a pair path `(X,Y)` started at
  `(x,0)`, with every difference quotient of `Y` in `S`, `X` a martingale
  and `X X⇧T - Y` a martingale — with its six projections, an introduction
  rule, and monotonicity in `S`;
* `covariation_val S T K x` — the value of the minimum-exit-time problem
  over that class, monotone in `S`;
* thirteen consequences, of which **eight need nothing of `S`** and five
  need exactly one number: a norm bound (`covariation_class_lipschitz_ae`,
  `_Y_bounded_ae`, `_Y_entry_bound_ae`, `_Y_entry_integrable`,
  `_sq_integrable`, `_sq_mean_le`) or a two-sided bound on the diagonal
  (`_Y_diag_increment`).

and in the paper session, `exit_class_eq_covariation` and
`exit_val_eq_covariation_val` identify Eq. (1.7) and Eq. (1.6) with the
generic objects at `sconstraint k L`.  Fifteen lemmas of `Exit_Class` are
now three-line specialisations; about 280 lines of proof moved down with
them.

**What is left of G11.**  Four lemmas resisted and were reverted:
`exit_class_diffquot_full_mass`, `_start_full_mass`, `_start_limit` and
`_diffquot_limit`.  They go through `closedin_diffquot_constraint`, whose
generic form needs `closed S` threaded through two more layers, and through
a full-mass argument whose `OF` chains did not survive the substitution.
Beyond them, the remaining ~215 consumers of `exit_class` are a mechanical
rename — `exit_class k L T x` to `covariation_class S T x`, plus an
`S`-hypothesis in a dozen places — but they sit in fifteen theories and have
to be migrated bottom-up, one theory at a time.  The bridge equations mean
that can now happen without touching anything else.

### The gate, retried twice

The first retry, after widening `pairX`, `pairY`, `padd_fst_continuous` and
the three consumers that had been blocked on them, put the path layer at
**125 of 438 statements (29%)** free of the pair path type.  Everything that
came back was of one of two kinds, and only one of them was a real
obstruction:

* `pshift`, `pcoord` and `ploc` are genuinely pair-specific — `pshift` adds
  a vector to the *first* component, `pcoord` reads a matrix entry — so
  nothing that mentions them can or should leave the pair type;
* everything about the path *metric* failed on a **sort**, not on the
  mathematics: `Variable 'a::{polish_space,real_normed_vector} not of sort
  euclidean_space`.

The second is a one-line gap in the library.  `polish_space` is
`complete_space + second_countable_topology`; HOL declares both product
instances and not their conjunction, so a path space whose values are pairs
could only be seen as Polish by going through `euclidean_space`.  With

```isabelle
instance prod :: (polish_space, polish_space) polish_space ..
```

in `Continuous_Path_Spaces.Path_Space`, thirteen of the twenty-four
metric-and-measurability lemmas in `Path_Splicing` widen with their proofs
untouched, and the layer stands at **138 of 438 (32%)**.

The gate asks for 69%.

**That last paragraph, as first written, was wrong, and the error is worth
recording.**  It said the remaining measurability proofs (`pglue_measurable`,
`iglue_measurable`, `padd_measurable`, `Lipschitz_pglue`) read a metric
relation off the concrete pair type, so that widening them "means restating
the product-metric step, which is mathematics, not a move".  The product in
those proofs is not the pair `(x, A)` of a vector and a matrix; it is the
product of the *past* and *future* path spaces, which is already generic in
the codomain.  Nothing there is pair-specific.  What actually blocked the
batch were four defects in the mechanical widener and one in the base image:

* the dependency closure was not being computed, so consumers were widened
  before their producers;
* the type-rewriting regex did not match the spelling `('n::finite) pairpath`;
* the fresh type variables clashed with `'a`/`'b` already bound to the
  measure space in the same statement;
* proof-local `pairpath` types were spelled out and had to be rewritten too.

And one that produced 92 spurious "failures" in a single theory: **an earlier
committed batch had widened to `{polish_space,real_normed_vector}` while the
new batch used `{polish_space,banach}`, and the two sorts do not unify.**  The
failures read as type errors deep inside proofs; they were a naming
inconsistency at the *statements*.  Normalising the whole path layer to
`{polish_space,banach}` turned six theories from 92 errors to zero without
touching a proof.  When a widening pass is resumed later, first make the sort
uniform across everything already widened; only then look at real failures.

The one genuine dependency outside the layer was `pair_fst_borel` and
`pair_snd_borel` in `Continuous_Time_Martingales.Integrability_Criteria`,
stated at `(real^'n) × (real^'n^'n)`; a widened `fst` does not unify with
them.  They hold at any topological spaces with the same proof, and are now
stated that way.

With those fixed, the layer stands at **297 of 407 statements (73%)** free of
the pair type, and the three theories the gate is actually about at **219 of
224 (98%)**:

| theory | pair-free | total |
|---|---:|---:|
| `Path_Splicing` | 90 | 94 |
| `Path_Stopping_Times` | 59 | 60 |
| `Path_Law_Pasting` | 70 | 70 |
| `Pair_Path_Space` | 16 | 39 |
| `Pair_Path_Laws` | 53 | 119 |
| `Path_Law_Sampling` | 9 | 25 |

The gate (69%) therefore **passes**.  The five statements left in the gated
three are pair-specific by their mathematics, not by accident:
`pcoord_stopped_bounded` and `pcoord_stopped_paths_cont` read a matrix entry,
`padd_comp_norm_le` and `exit_component_dyceil_tendsto` bound a coordinate
norm, `ploc_eq_T_of_below` localises the first component.  The two `Pair_*`
theories and `Path_Law_Sampling` are the pair layer proper and are not meant
to leave it.

Promotion to a `Path_Space_Operations` session is thus unblocked and is the
next agent's first move; nothing in this plan changes because of it except
that §3.7 is no longer gated.

Two practical findings from the run, for whoever picks this up:

* A widening can turn a terminating proof into a divergent search.  One
  batch left a build running for thirty-five minutes on a proof that took
  seconds before; `isabelle build -o timeout=900` bounds it, and a mechanical
  widen-and-revert loop needs that bound to be usable at all.
* The widened statements cost check time: with them the paper session takes
  six minutes rather than one, because type inference at a general product
  does more work at every use site.
