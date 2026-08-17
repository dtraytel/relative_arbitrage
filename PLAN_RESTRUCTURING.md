# Restructuring plan

A refactoring plan for the whole development. It asks, of every lemma:

1. **Is it as general as it can cheaply be?** — are all hypotheses used, can the
   type be widened without redoing the proof?
2. **Is it useful outside this paper?** — would somebody formalising something
   else want it?
3. **Is it in the right place?** — right session, right theory, right layer.

and turns the answers into a target layout, a per-theory disposition, a
generalisation catalogue and a deduplication catalogue.

**This is refactoring only.** No new mathematics. Every generalisation listed
below is one of: widen a type class, drop a hypothesis the proof does not use,
delete a duplicate, or move a block of text. Where a generalisation might cost
a real proof change it is marked *speculative* and comes with an instruction to
abandon it rather than to prove something new.

---

## 0. How this analysis was done, and how to redo it

The measurements below are reproducible; the executing agent should re-run them
after each phase, because the numbers are the progress metric.

* **Inventory.** 58 theories, 115 987 lines, 2 804 top-level
  `lemma`/`theorem`/`corollary`/`proposition`, 225 `definition`/`locale`/
  `abbreviation`/`type_synonym`.
* **Genericity probe.** For each lemma, the set of *project-defined* constants
  occurring in its statement. 853 lemmas (30%) mention **none** — they are
  statements about matrices, measures, martingales, topology or arithmetic that
  happen to live in a paper theory. That set is the primary extraction target.
* **Duplicate probe.** Statements normalised by stripping the name; 18 groups
  of *textually identical* statements across different names or files, plus a
  larger set of same-content/different-notation pairs found by reading.
* **Placement probe.** For each theory, which *other* theories' constants it
  actually uses (comments stripped). Theories that use nothing from their own
  session's paper layer are misplaced.

Verification of the refactoring itself is `isabelle build -d . <SESSION>` for
each session in `ROOTS`, plus the `unused_thms` run described in
`UNUSED_THMS.md`. Isabelle is not available in the analysis environment, so
**every claim below about a proof still going through after a change is a
prediction, not a measurement.** The rule when a prediction fails is in §7.

---

## 1. Findings

### 1.1 The development is a paper proof with four general libraries fused into it

Four bodies of reusable mathematics are already separated into their own
sessions (`Alexandrov_Sup_Convolution`, `Wiener_Measure`, `Martingale_Sampling`,
`Path_Space_Tightness` — §2.10 renames three of them) and that separation was
the right call. But a fifth,
sixth and seventh are still buried inside `Relative_Arbitrage`:

| buried library | where it currently lives | size |
|---|---|---|
| real-matrix algebra, spectral theorem, Ky Fan sums, ordered eigenvalues, Poincaré separation | `Curvature_Operator`, `Eigenvalues`, `Eigenvalue_Continuity`, `Threshold_Chain`, `Poincare_Separation`, scattered | ≈ 6 500 lines |
| semicontinuity calculus and envelopes, Berge's maximum theorem, usc measurable selection | `Operator_Envelopes`, `Equicontinuity`, `Exit_Class_Compactness` | ≈ 1 800 lines |
| martingale algebra and transfer (products, projective products, image measures, restriction, uniform measure, time change, modifications, stopping) | `Exit_Class_Compactness`, `Exit_Class_DPP`, `Modification_Transfer`, `Stopped_Localization`, `Exit_Time` | ≈ 3 000 lines |

and an eighth — the Crandall–Ishii *doubling* toolbox — is split across
`Alexandrov_Sup_Convolution` (the abstract half) and `Comparison_Principle`
(the concrete half, ≈ 200 lemmas), which is why several of its lemmas exist
twice at two different type generalities.

### 1.2 Four theories are misplaced outright

Determined by the placement probe: these use **no** constant from the
`Relative_Arbitrage` paper layer at all, yet sit on top of it and import it.

| theory | uses only | currently imports | should be in |
|---|---|---|---|
| `Modification_Transfer` (684 lines) | nothing project-defined | `Ito_Market` | `Continuous_Time_Martingales` |
| `Exit_Time` (688 lines) | nothing project-defined | `Ito_Market` | `Continuous_Time_Martingales` |
| `Stopped_Localization` (865 lines) | `Martingale_Sampling` + `Exit_Time` + `Increment_Moments` | `Exit_Time` | `Continuous_Path_Spaces` |
| `Pathwise_Quadratic_Variation` (1 139 lines) | `Martingale_Sampling` only | `Increment_Moments` | `Continuous_Path_Spaces` |

`Exit_Time` importing `Ito_Market` — which drags in Brownian motion, the Wiener
measure and the market locales — to state *"the exit time of a closed set by a
continuous adapted process is a stopping time"* is the single worst import in
the development.

### 1.3 The eigenvalue theory is stacked upside down

The import chain is

```
Curvature_Operator → Constraint_Set_Convexity → Eigenvalue_Bound_Exact
                   → Eigenvalues → Eigenvalue_Continuity → Threshold_Chain
                   → Operator_Continuity → Poincare_Separation
```

so Ky Fan partial sums, ordered eigenvalues, their Lipschitz dependence on the
matrix, and the Poincaré separation inequality — all basis-free, all classical,
none of them about this paper — are built **on top of** `Pi_constraint`,
`suff_volatile` and Lemma 2.1, which are about this paper only. `Eigenvalues`
uses exactly two paper constants (`Pi_proj` in one section, `feasible`/
`eigen_ub` in another); removing those two sections from it makes the whole
eigenvalue tower paper-free and movable to the bottom.

### 1.4 Elementary matrix algebra is re-proved between three and six times

Confirmed textual duplicates (identical statements, different names or files):

| statement | copies |
|---|---|
| `trace (A ** B) = trace (B ** A)` | `trace_mul_comm` (Comparison_Principle), `trace_matrix_commute` (Operator_Envelopes), `trace_mult_commute` (Value_Function_Viscosity) |
| `A ** (B - C) = A ** B - A ** C` | `matrix_mul_diff_right` (Operator_Envelopes), `matrix_matrix_mult_diff_right` (Poincare_Separation), `matrix_msub_ldistrib` (Value_Function_Viscosity) |
| `(A - B) ** C = A ** C - B ** C` | `matrix_mul_diff_left` (Operator_Envelopes), `matrix_matrix_mult_diff_left` (Poincare_Separation), `matrix_msub_rdistrib` (Value_Function_Viscosity) |
| `(c *⇩R A) ** B = c *⇩R (A ** B)` | `matrix_mult_scaleR_left` (Comparison_Principle), `scaleR_matrix_matrix_left` (Operator_Continuity), `scaleR_matrix_mult` (Curvature_Operator — *rectangular, the most general of the three; keep this one*) |
| `A *v (x + y) = A *v x + A *v y` | `matvec_add_right'` (Comparison_Principle), `matvec_add_right` (Value_Function_Viscosity) |
| `A *v (r *⇩R x) = r *⇩R (A *v x)` | `matvec_scaleR_right'` (Comparison_Principle), `matvec_scaleR_right` (Operator_Envelopes), `matrix_vector_mult_scaleR_gen` (Comparison_Principle) |
| `trace (A - B) = trace A - trace B` | `trace_diff_matrix` (Poincare_Separation), `trace_matrix_diff` (Value_Function_Viscosity) |
| `y ∙ (A *v x) = (transpose A *v y) ∙ x` | `inner_matrix_transpose` (Operator_Envelopes **and** Value_Function_Viscosity, same name), `inner_transpose_matrix` (Curvature_Operator) |
| `trace (M ** (Qᵀ ** a ** Q)) = trace ((Q ** M ** Qᵀ) ** a)` | `trace_conj` (Operator_Continuity), `trace_conjugate` (Viscosity_Comparison_Interface) |
| `transpose (c *⇩R A) = c *⇩R transpose A` | `transpose_scaleR` (Constraint_Set_Convexity **and** Comparison_Principle), `transpose_scaleR_matrix` (Comparison_Principle) |
| `transpose (A + B) = transpose A + transpose B` | `transpose_add` (Constraint_Set_Convexity), `transpose_add_matrix` (Comparison_Principle) |
| `trace (∑ f) = ∑ trace ∘ f` | `trace_matrix_sum` (Curvature_Operator), `trace_sum_matrix` (Poincare_Separation **and** Value_Function_Viscosity) |
| `(a - b)² ≤ 2a² + 2b²` | `sq_diff_le` (Quadratic_Variation), `sq_diff_le_two` (Pathwise_Quadratic_Variation), `square_add_le_two` (Moment_Bounds), `diff_sq_le_double` (Value_Function_Viscosity) |
| `fst`/`snd` on `real^'n × real^'n^'n` is Borel | `pair_fst_borel`/`pair_snd_borel` (Exit_Class_Compactness), `measurable_fst_borel`/`measurable_snd_borel` (Exit_Class_DPP) |

Near-misses worth checking by hand while deduplicating, because they differ by
one side of a distributive law and are easy to conflate:
`matrix_vector_mult_add` (Operator_Continuity) is `(A + B) *v x = …`, *not* `A *v (x + y) = …`;
`scaleR_matrix_vector` (Curvature_Operator) is `(r *⇩R A) *v x = …`, *not* `A *v (r *⇩R x) = …`;
`matrix_mult_sum_left` (Constraint_Set_Convexity) and `matrix_mult_sum_right` (Curvature_Operator) are the two sides
of the same distributive law and should end up as a pair of adjacent lemmas.

Six of these are re-proved **under the very same name** in a theory that already
imports the one containing the original: `inner_matrix_transpose`,
`lsc_env_bdd_above`, `lsc_env_le_self`, `lsc_env_ge` (all Operator_Envelopes →
Value_Function_Viscosity), `outerp_borel` (Exit_Class_Compactness →
Exit_Class_Marginals), `pcut_pglue` (Exit_Class_DPP → Exit_Class_Infinite),
`martingale_cong_ge` (Exit_Class_Compactness → Exit_Class_DPP),
`measurable_mat_entries` (Exit_Class_Compactness → Pathwise_Quadratic_Variation
— these two are independent), `lsc_attains_inf_gen` (Operator_Envelopes at
`'a::metric_space` → Value_Function_Viscosity at `real^'n`, a *de*-generalisation).

### 1.5 Four definitions exist twice

* **`outer_prod`** is defined in `Curvature_Operator` (line 34) *and again* in
  `Comparison_Principle` (line 3406), verbatim. `Comparison_Principle` imports
  `Curvature_Operator` transitively, so the second declaration shadows the
  first inside that theory. This is a latent defect, not just noise.
* **`hh`** (`Operator_Envelopes`:677) and **`hrefl`**
  (`Value_Function_Viscosity`:8844) are the same Householder reflection,
  character for character.
* **`rotv u v = hh (u+v) ** hh u`** (`Operator_Envelopes`) and
  **`rotm q w = hrefl (‖w‖q + ‖q‖w) ** hrefl q`** (`Value_Function_Viscosity`)
  are the same two-reflection rotation; `rotm q w = rotv q (‖q‖/‖w‖ ·⇩R w)` up
  to normalisation. Each carries its own orthogonality/transport proofs.
* **`orth_mat`** (`Viscosity_Comparison_Interface`:79) is *definitionally*
  HOL-Analysis's `orthogonal_matrix`. Other theories in the same session already
  use `orthogonal_matrix` directly.

Also **`outerp x = (χ i j. x$i * x$j)`** (`Exit_Class`) is `outer_prod x x`.

### 1.6 The viscosity-solution predicate exists in five variants across four theories

`test_fun_at`, `visc_subsol`, `visc_supersol`, `visc_sol` (`Curvature_Operator`);
`visc_subsol_env`, `visc_supersol_env`, `visc_sol_env` (`Operator_Envelopes`);
`test_fun_C2`, `visc_subsol_env2`, `visc_supersol_env2`, `supersol_jet`
(`Comparison_Principle`); `visc_supersol_lsc` (`Value_Function_Viscosity`).

Each variant's relation to the others is proved somewhere, but the definitions
and the implications between them are scattered over 30 000 lines. They belong
in one theory of maybe 400 lines.

### 1.7 Four theories are too large to navigate

| theory | lines | lemmas | sections |
|---|---|---|---|
| `Exit_Class_DPP` | 16 792 | 312 | 28 |
| `Value_Function_Viscosity` | 16 324 | 285 | 29 |
| `Comparison_Principle` | 14 015 | 381 | 12 |
| `Exit_Class_Compactness` | 12 634 | 290 | 35 |
| `Sup_Convolution` | 7 544 | 228 | 2 (+55 subsections) |

Together that is 60% of the development in five files. Each has clean internal
section boundaries — the split points below are the existing `section` headers,
so splitting is textual.

### 1.8 One locale hierarchy duplicates work

`Ito_Market` defines `ito_volatile_market`, `ito_stopped_market` and
`ito_const_horizon_market`, and proves `Z_zero_expectation` twice
(`Z_zero_expectation` at line 118, `Z_zero_expectation_const` at line 656 — the
same statement in a different locale). `ito_stopped_market` is already a
sublocale of `ito_volatile_market`; `ito_const_horizon_market` should be too,
via a shared `ito_market_core` carrying the Dynkin identity once.

Similarly `Exit_Class_DPP` proves the same statement twice under
`aglue_inner_increment_comp` (line 11533) and `aglue_law_comp_increment`
(line 12078), and uses both.

### 1.9 What is already right, and should not be touched

State this explicitly so the executing agent does not "improve" it:

* `Path_Space` and `Path_Space_Infinite` are already generic in
  `'b::polish_space`. Correct.
* `Sup_Convolution`'s mathematics is already at `'a::euclidean_space`
  throughout — Rademacher, Alexandrov, Jensen, the theorem on sums. Only its
  *packaging* (one 7 544-line file) is wrong.
* `Wiener_Measure` is a clean projective-limit construction with no paper
  contamination.
* `Martingale_Sampling`'s locale layering (`time_grid` → `sampled_martingale`
  → `sq_int_martingale` → `stopped_*`) is good design and should be the model
  for the rest.
* `Dyadic_Chaining`, `Holder_Interpolation`, `Modulus_Tails`,
  `Increment_Tails`, `Vitali_Convergence`, `Conditional_UI` are small,
  single-purpose and correctly placed.
* The `Statement` session is exactly what it should be and changes only where
  a constant it displays gets renamed.

---

## 2. Target layout

Eight sessions instead of six. The two new ones are carved out of existing
material; nothing is invented.

```
ROOTS
  Symmetric_Matrix_Spectra         (new)      base: HOL-Analysis
  Semicontinuous_Analysis          (new)      base: HOL-Probability
  Second_Order_Viscosity_Analysis  (renamed from Alexandrov_Sup_Convolution, split, extended)
  Wiener_Measure                   (kept,      split)
  Continuous_Time_Martingales      (renamed from Martingale_Sampling, extended)
  Continuous_Path_Spaces           (renamed from Path_Space_Tightness, extended)
  Relative_Arbitrage               (kept,      much smaller, re-layered)
  Relative_Arbitrage_Statement     (kept)
```

### 2.0 Why each session exists

Every session must justify itself in one sentence, and that sentence is what its
`ROOT` `description` and its AFP abstract should say. If a session cannot be
described without naming this paper, it does not belong outside
`Relative_Arbitrage`.

| session | AFP? | why it exists |
|---|---|---|
| `Symmetric_Matrix_Spectra` | yes | The spectral theory of real symmetric matrices that HOL-Analysis stops short of — the spectral theorem, Ky Fan partial sums, the ordered eigenvalues as their differences, their Lipschitz dependence on the matrix, and Poincaré separation — for anyone who constrains a matrix through its spectrum rather than through its entries. |
| `Semicontinuous_Analysis` | yes | The semicontinuity toolkit that optimal control and viscosity-solution arguments all assume and Isabelle does not have: the ε-δ calculus, attainment on compacta, the semicontinuous envelopes, Berge's maximum theorem, and measurable selection of an upper semicontinuous payoff (Bertsekas–Shreve 7.33). |
| `Second_Order_Viscosity_Analysis` | yes | The complete second-order machinery for comparison proofs between viscosity solutions — Rademacher, Alexandrov, Jensen's lemma for semiconvex functions, the Crandall–Ishii theorem on sums, and the doubling-of-variables toolbox they exist to serve — without which no comparison principle can be formalised at all. |
| `Wiener_Measure` | yes | Brownian motion as the projective limit of its Gaussian finite-dimensional distributions, with independent increments and a continuous modification: the canonical construction, and the only one in Isabelle. |
| `Continuous_Time_Martingales` | yes | What continuous-time martingale theory needs beyond the AFP's `Martingales`: Doob's maximal inequality, optional sampling and stopping at a bounded stopping time, quadratic variation and its compensator, Vitali's theorem, exit times as stopping times, and the algebra of transporting the martingale property along images, products, restrictions and modifications. |
| `Continuous_Path_Spaces` | yes | Weak convergence of processes done properly: `C([0,T],'b)` as a Polish space with portmanteau and the continuous mapping theorem, tightness of a family of path laws from increment moments alone, and quadratic variation as an adapted, everywhere-continuous *path functional* with a summable `L²` rate. |
| `Relative_Arbitrage` | yes | Theorem 1.1 of Lai–Shkolnikov–Soner (arXiv:2512.17702): the value function of the minimum-exit-time problem under eigenvalue lower bounds is the unique bounded upper semicontinuous viscosity solution of the associated degenerate elliptic equation. Reusable only as a worked example of a stochastic-control verification argument; that is the point of the six sessions it stands on. |
| `Relative_Arbitrage_Statement` | **no** | The formal statement of Theorem 1.1 with every definition it mentions and nothing else, written for the paper's authors to check against their own — a five-page document, not a library. |

The `yes` column is an intention, not a promise: submission would need each
entry's `root.tex` written as an abstract rather than as a chapter of this
development, and §6 does not schedule that work.

Dependency order (each session may import anything above it):

```
Symmetric_Matrix_Spectra────┐
Semicontinuous_Analysis─────┼─→ Second_Order_Viscosity_Analysis ─┐
                            │                                    │
Wiener_Measure ─────────────┤                                    ├─→ Relative_Arbitrage ─→ Statement
Continuous_Time_Martingales─┴─→ Continuous_Path_Spaces ──────────┘
```

### 2.1 `Symmetric_Matrix_Spectra` (new)

Base `HOL-Analysis`. Purely linear algebra over `real^'n^'n`. Self-contained,
AFP-submittable on its own, and the thing most likely to be wanted by others.

| theory | content | drawn from |
|---|---|---|
| `Matrix_Algebra.thy` | trace/transpose/`**`/`*v` calculus, distributivity, `scaleR`, sums, `mat 1`, entries vs `axis`, `Basis` of `real^'n^'n`, Frobenius norm, submultiplicativity, continuity of the matrix operations, `closed {a. transpose a = a}` | the ~120 duplicated one-liners of §1.4 and §3.1 |
| `Outer_Products.thy` | `outer_prod`, `outerp` as abbreviation, `rank1proj`, norms, `bounded_linear` facts, projector calculus (`proj_inner_self`, `proj_norm_le`, `projmat`) | Curvature_Operator, Operator_Continuity, Exit_Class, Value_Function_Viscosity |
| `Orthonormal_Families.thy` | `onormal`, extension to a basis, completeness relation, traces in an orthonormal basis, `orthonormal_family_containing`, `orthonormal_dim_span` | Curvature_Operator §"Orthonormal families", Value_Function_Viscosity |
| `Householder_Rotation.thy` | one Householder reflection `hrefl`, one rotation `rotm`, orthogonality, `R a Rᵀ` conjugation invariance, continuity of the transport | merge of `hh`/`hrefl`, `rotv`/`rotm` |
| `Symmetric_Spectral.thy` | Rayleigh-quotient maximisers are eigenvectors, orthonormal eigenbases of invariant subspaces, the spectral theorem for real symmetric matrices, `psd`, degenerate ellipticity | Curvature_Operator §"The spectral theorem" (580–984) |
| `Ky_Fan.thy` | `is_proj`, `kyfan`, `eigval`, `possum`, `bracket`, the LP on the simplex in a box, threshold subsets and the threshold chain, monotonicity of the ordered eigenvalues, positive/negative parts | Eigenvalues, Threshold_Chain, the LP part of Poincare_Separation |
| `Eigenvalue_Continuity.thy` | `entrysum`, Lipschitz dependence of Ky Fan sums and eigenvalues on the matrix | Eigenvalue_Continuity (unchanged) |
| `Poincare_Separation.thy` | general Poincaré separation, Courant–Fischer min–max, `dim_inter_ge`, `subspace_inter_nonzero`, the spectrum of a compressed matrix | Poincare_Separation minus everything mentioning `Mp`, `ell_op`, `eq36_rhs` |

**Not** in this session: `feasible`, `ell_op`, `Pi_proj`, `Pi_constraint`,
`suff_volatile`, `sconstraint`, `Mp`, `eigen_lb`, `eigen_ub` — those are the
paper's, and stay in `Relative_Arbitrage`. (`eigen_lb`/`eigen_ub` are borderline:
they are Courant–Fischer characterisations of "λ₍ₘ₎ ≥ 1" and "λ₍₁₎ ≤ L". Keep
them in the paper session, but prove the bridge `eigen_lb a m ⟷ 1 ≤ eigval m a`
(`feasible_iff_eigval`, currently in `Poincare_Separation`) in the paper session
too, so `Ky_Fan` stays clean.)

### 2.2 `Semicontinuous_Analysis` (new)

Base `HOL-Analysis`. Everything about upper/lower semicontinuity that is not
about `F`.

| theory | content | drawn from |
|---|---|---|
| `Semicontinuity.thy` | ε-δ usc/lsc predicates, closure under `+`, positive scaling, `max`, difference with a continuous function; usc/lsc from continuity; attainment of sup/inf on a nonempty compact set | Operator_Envelopes §"Semicontinuity toolbox" (2017–2412), Value_Function_Viscosity `lsc_diff_continuous` |
| `Semicontinuous_Envelopes.thy` | `lsc_env`, `usc_env`, `lsc_envK` (envelope relative to a set), `Kext`, monotonicity, the usc fixpoint, boundedness, `usc_extension_bounded` | Operator_Envelopes 2912–3542, Value_Function_Viscosity duplicates deleted |
| `Berge.thy` | `usc_sup_over_compact`, `usc_sup_over_compactin`, `box_of_sequential`, `box_of_sequential_euclidean`, `compactin_of_seq_compact`, `closure_of_sequential_limit`, `seq_compact_closure_of` | Continuous_Path_Spaces/Equicontinuity 233–773 |
| `Semicontinuous_Selection.thy` | `usc_sel_set`, `usc_sel_good`, `usc_sel_code`, `usc_sel`, `usc_measurable_selection` (Bertsekas–Shreve 7.33) | Exit_Class_Compactness §"A measurable selection theorem" (10400–11061) |

`Semicontinuous_Selection` needs measure theory, so this session's base becomes
`HOL-Probability`. That is acceptable; alternatively put `Semicontinuous_Selection` alone
into `Continuous_Time_Martingales`. **Choose `HOL-Probability` as the base** — one
session boundary fewer.

### 2.3 `Second_Order_Viscosity_Analysis` (renamed from `Alexandrov_Sup_Convolution`, split and extended)

Split the 7 544-line monolith at its existing subsection boundaries, and pull
the abstract half of the Crandall–Ishii doubling machinery down from
`Comparison_Principle` into it.

| theory | content |
|---|---|
| `Convex_Subgradients.thy` | `subdiff`, `prox`, `moreau`, proximal map attained/unique, epigraph facts |
| `Rademacher.thy` | `dquot`, `dlim_set`, `dcrit`, `ddir`, `rat_dirs`, one-dimensional Rademacher, sections, box-integral machinery, `rademacher_AE`, `rademacher_vec_AE` |
| `Moreau_Envelope.thy` | resolvent differentiability, firm nonexpansiveness, gradient of the envelope, second-order differentiability, integral representation |
| `Alexandrov.thy` | second differences, symmetry of the Hessian, `convex_alexandrov`, `semiconvex_alexandrov`, `semiconvex_alexandrov_bounded` |
| `Jensen_Lemma.thy` | semiconvexity calculus, perturbed maximisers, `jensen_lemma`, `semiconvex_jensen_alexandrov_point` |
| `Sup_Convolution.thy` | `supconv` proper: semiconvexity, attainment, the rate, jet transfer back to `u`, sign flip, superjet ⇒ local max |
| `Theorem_On_Sums.thy` | block structure on the product, `product_form_block_diagonal`, `second_order_form_unique`, `sums_matrix_inequality`, `sums_gives_ordering` |
| **`Doubling.thy`** *(new)* | the abstract doubling toolbox at `'a::euclidean_space`: see §3.2 |
| **`Soft_Penalty.thy`** *(new)* | `soft_pen`, `soft_grad`, `soft_hess`, `soft_shrink`: a coercive, semiconcave penalty vanishing on the diagonal with a nowhere-vanishing gradient off it, plus its exact second-order expansion. Genuinely reusable in any viscosity comparison argument. |

### 2.4 `Wiener_Measure` (split)

`Brownian_Motion.thy` (1 361 lines) is fine but does three things. Split:

| theory | content |
|---|---|
| `Gaussian_Increments.thy` | `gauss_measure`, its moments, translation invariance of `lborel`, the convolution law |
| `Brownian_Finite_Dimensional_Distributions.thy` | `prevt`, `inc_prod`, `csum`, `bm_fdd`, `wr`, `ins`, rectangle formula, projectivity |
| `Brownian_Motion.thy` | `wiener_pre` as the projective limit, marginals, increments, the fourth-moment bound, independent increments |
| `Brownian_Motion_Continuity.thy` | unchanged |

Move `sorted_wrt_less_nth_iff`, `sorted_wrt_less_set_take`,
`sorted_wrt_less_Max_last`, `prod_indicator_conj` to a 40-line
`Wiener_Measure/Sorted_Lists.thy`, or upstream them — they are list lemmas with
no Brownian content.

### 2.5 `Continuous_Time_Martingales` (renamed from `Martingale_Sampling`, extended)

The rename is §2.10's: sampling was the method, continuous time is the subject.
Keep the existing theories; add:

| theory | content | drawn from |
|---|---|---|
| `Martingale_Algebra.thy` | `martingale_add`, `martingale_diff`, `martingale_add_const`, `martingale_sub_initial`, `martingale_cong_ge`, `martingale_cong_AE`, `martingale_time_change`, `martingale_time_change_cong`, `martingale_coarser_filtration`, `martingale_bounded_linear_image`, `martingale_vec_nth`/`_mat_nth`/`_vecI`/`_matI`/`_vec_component`/`_mat_component`, `martingale_mean_zero_of_start`, `martingale_mult_measurable`, `martingale_cross_measurable`, `martingale_stopped_const`, `martingale_bounded_test` | Exit_Class_Compactness, Exit_Class_DPP, Exit_Class, Ito_Market, Exit_Time_Semicontinuity, Exit_Class_Infinite, Pathwise_Quadratic_Variation |
| `Martingale_Transfer.thy` | `martingale_distr`, `martingale_restrict_full` and the whole `*_restrict_full` package, `martingale_uniform_measure` + the `uniform_measure` lemmas, `martingale_pair_fst`/`_snd`/`_snd_param`/`_mult`, `filtered_measure_pair`, `filtered_measure_PiM`, `martingale_PiM_component`, `sets_PiM_mono`, `sets_pair_measure_mono`, `prob_space_pair_measure`, `distr_pair_snd` | Exit_Class_Compactness, Exit_Class_DPP, Stopped_Localization |
| `Natural_Filtration.thy` | `natural_filtration_pull`, `natural_filtration_eval`, `natural_filtration_cong_space`, `sets_natural_filtration_mono`, `sets_natural_filtration_subset`, `adapted_of_natural_filtration`, `subalgebra_self`, `set_integral_zero_of_generator`, `AE_zero_of_set_integral_zero`, `AE_nonpos_of_set_integral_zero`, `AE_mem_of_emeasure_1` | Exit_Class_Marginals, Modification_Transfer, Exit_Class_DPP |
| `Modification_Transfer.thy` | moved verbatim from `Relative_Arbitrage` | — |
| `Stopping_Times.thy` | `etime`, `eroded`, `qtimes`, `cont_adapted_process`, the countable description of the hitting event, `etime_stopping_time`, `etime_stays_in_cball`, `infdist_measurable`, `open_gt_infdist`, `shift_stays_off`, `positive_of_countable_UN` | `Exit_Time.thy` moved verbatim |
| `Kernels.thy` | `ksemi`, `ksemi_sets_kernel`, `ksemi_Pair_measurable`, `ksemi_kernel_measurable`, `integral_ksemi_measurable`, `measurable_integral_kernel`, `integral_kernel_measurable`, `kernel_mix_measurable` | Exit_Class_Compactness, Exit_Class_DPP |

Also fold the four copies of `(a-b)² ≤ 2a² + 2b²` into one lemma in
`Quadratic_Variation.thy`, and put the small real-arithmetic helpers
(`abs_prod_le_sq`, `sq_times_sq`, `pow4_*`, `abs_pow4`, `two_abs_prod_le_squares`,
`prod_sq_le_half_pow4`, `four_prod_cube_le`, `pow4_binomial`, `sq_le_half_add_half_pow4`,
`abs_cube_prod_le_pow4`, `abs_prod_cube_le_pow4`) into one
`Continuous_Time_Martingales/Power_Inequalities.thy`.

### 2.6 `Continuous_Path_Spaces` (renamed from `Path_Space_Tightness`, extended)

Keep as is, minus `Equicontinuity`'s topology half (to `Semicontinuous_Analysis`),
plus:

* `Pathwise_Quadratic_Variation.thy` — moved from `Relative_Arbitrage`.
  Its `qvp`/`qvps`/`qvmat` construction (quadratic variation as a *pathwise
  Borel functional* with an `L²` rate, rather than by Doob–Meyer) is one of the
  more original pieces of infrastructure here, and it has nothing to do with the
  paper.
* `Adapted_Quadratic_Variation.thy` — `qvp_good`, `qvp_goodupto`, `qvpc`, `qvsa`,
  `qvmata` and their continuity/adaptedness lemmas, currently the first six
  subsections of `Exit_Class_Marginals` (lines 1–~1400). Same remark: this is a
  general construction (an adapted, everywhere-continuous version of the
  quadratic-variation functional) and the paper only consumes it.
* `Stopped_Localization.thy` — moved from `Relative_Arbitrage`.
* `Weak_Convergence_Transfer.thy` — `weak_conv_on_pushforward`,
  `weak_conv_on_nn_integral_le`, `weak_conv_on_prob_space`,
  `weak_conv_closed_full_measure`, `weak_conv_open_positive_eventually`,
  `weak_conv_on_integral_unif_integrable`, `weak_conv_integral_of_L2_bound`,
  `unif_integrable_of_L2_bound`, `metric_measure_eqI_bounded_cts`,
  `metric_measure_mono_bounded_cts` — currently split between `Path_Space`,
  `Path_Tightness`, `Exit_Class` and `Exit_Time_Semicontinuity`.

### 2.7 `Relative_Arbitrage` (re-layered)

After the extractions this session should be roughly 55 000 lines rather than
90 000, in five clearly named layers.

**L1 — the operator (Eqs. (1.5), (1.9), (3.4)–(3.6), Lemma 2.1, Lemma 3.1)**

| theory | content | from |
|---|---|---|
| `Constraint_Set.thy` | `eigen_lb`, `eigen_ub`, `feasible`, `ell_op`, feasibility from projections, bounds on the feasible set, perturbation bounds, `feasible_iff_eigval` | Curvature_Operator 321–579, 985–1139; Viscosity_Solutions; Poincare_Separation tail |
| `Constraint_Convexity.thy` | `is_proj`-based `Pi_proj`, `Pi_constraint`, `suff_volatile`, both inclusions of Lemma 2.1 | Constraint_Set_Convexity |
| `Constraint_Exact.thy` | the exact (unclosed) form of Lemma 2.1 | Eigenvalue_Bound_Exact |
| `Operator_Formula.thy` | `Mp`, `rank1proj` specialisation, Eq. (3.5), the index shift of Eq. (3.6), continuity of `F` away from `p=0`, `feasible_bounded`, closedness of the feasible set | Operator_Continuity + the paper half of Poincare_Separation |
| `Operator_Envelopes.thy` | `ell_op_pair`, `ell_op_lsc`, `ell_op_usc`, `mgap`, the `p=0` clause, `F* = F` off the origin, the invariances (4.4), transport along `F`-preserving homeomorphisms | Operator_Envelopes minus the semicontinuity toolbox |
| `Operator_Envelope_Continuity.thy` | `eq36_rhs`, Lemma 3.1 assembled, degenerate ellipticity | unchanged |

**L2 — viscosity solutions**

| theory | content |
|---|---|
| `Viscosity_Definitions.thy` | **all** of `test_fun_at`, `test_fun_C2`, `visc_subsol`, `visc_supersol`, `visc_sol`, `visc_subsol_env`, `visc_supersol_env`, `visc_sol_env`, `visc_subsol_env2`, `visc_supersol_env2`, `visc_supersol_lsc`, `supersol_jet`, `sym_part`, `max_principle_boundary`, `max_principle_boundary_raw`, `comparison_principle`, `expandable`, `Tidx`-free — together with every implication between them (`visc_subsol_imp_env`, `visc_supersol_imp_env`, `visc_supersol_lsc_iff_env`, `ell_op_envelopes_eq_off_zero`, the "envelope-free notions are stronger" section, `max_principle_boundary_counterexample`) |
| `Viscosity_Ball.thy` | `ball_v`, its derivatives, Example 3.1 as a smooth viscosity solution, `comparison_ball`, `ball_v_unique_solution`, `ball_v_unique_solution_smooth`, uniqueness on the ball without Crandall–Ishii |
| `Comparison_Principle.thy` | only the `F`-specific chain: strictness from the operator, the two branches, `max_principle_boundary_holds`, uniqueness on a compact set |
| `Comparison_Two_Domain.thy` | Theorem 4.2(b), Theorem 4.3, Proposition 4.1, the `T_ι` hypothesis and its convex instance (Comparison_Principle 12702–end) |

**L3 — markets** (`Volatile_Market`, `Ito_Market`, `Brownian_Market`,
`Brownian_Continuous`, `Optimal_Exit_Time`, `Brownian_Optimal_Boundary`,
`Value_Function_Market`, `Path_Tightness_Market`, `Exit_Semicontinuity`,
`Exit_Time_Semicontinuity`) — unchanged apart from the extractions and the
`ito_market_core` refactor of §1.8.

**L4 — the class** (split of the two 12–17k-line files):

`Exit_Class_Compactness` splits at its own `section` boundaries into:

| new theory | content | lines |
|---|---|---|
| `Exit_Class_Limits.thy` | Lemma 2.3, closure under weak limits | 26–3459 |
| `Exit_Class_Tightness.thy` | tightness and sequential compactness | 3460–3896 |
| `Exit_Class_Shift.thy` | shift equivariance, upper semicontinuity of the value function | 3897–5110 |
| `Exit_Class_Witness.thy` | laws of concrete pair processes, nonemptiness | 5111–6392 |
| `Exit_Class_Pasting.thy` | horizon shortening, concatenation, Proposition 2.4 | 6393–10235 |
| `Exit_Class_Optimizer.thy` | attainment, Larsson–Ruf 2.2(ii), the Giry kernel, semidirect products | 10236–end, minus the selection theorem, which moves out |

`Exit_Class_DPP` — whose own name is one of the abbreviations §2.9 forbids —
splits into:

| new theory | content | lines |
|---|---|---|
| `Dynamic_Programming_Pasting.thy` | the pasting bound | 13–850 |
| `Dynamic_Programming_Conditioning.thy` | conditioning on the past, the four clauses for the conditional law | 851–5874 |
| `Dynamic_Programming_Kernels.thy` | kernels into the class, measurability and repair | 5875–8165 |
| `Dynamic_Programming_Optional_Sampling.thy` | optional sampling at two stopping times | 8166–8955 — *general material; test for a move to `Continuous_Time_Martingales`* |
| `Dynamic_Programming_Stopping_Clauses.thy` | clause (iv) at a stopping time | 8956–9991 |
| `Dynamic_Programming_Additive_Glue.thy` | the additive glue and its clauses | 9992–12497 |
| `Dynamic_Programming_Delayed_Class.thy` | the delayed class, the horizon-parametrised selector | 12498–15656 |
| `Dynamic_Programming_Assembly.thy` | the pathwise bound, the exit bound, the `≥` half at a stopping time | 15657–end |

`Value_Function_Viscosity` splits into:

| new theory | content | lines |
|---|---|---|
| `Value_Function_Subsolution.thy` | Itô for quadratic test functions, the localised subsolution inequality, clause (2) subsolution half | 37–4310 |
| `Value_Function_Euler_Construction.thy` | the Euler scheme, its weak limit, the exact quadratic lower bound | 4311–≈9000 |
| `Value_Function_Supersolution_Case_1.thy` | the rotating covariance field, the nonzero-gradient case | ≈9000–12201 |
| `Value_Function_Supersolution_Case_2.thy` | touching the lower envelope, the tilted-quadratic case | 12202–14799 |
| `Value_Function_Tangential_Field.thy` | the subspace-tangential field for Example 3.1 at general `k` | 14800–15905 |
| `Value_Function_Assembly.thy` | clause (2) assembled | 15906–end |

`Exit_Class` and `Exit_Class_Infinite` stay as they are;
`Exit_Class_Marginals` loses its first six subsections to
`Continuous_Path_Spaces/Adapted_Quadratic_Variation.thy` and keeps the `xclass`
identification.

**L5 — the theorem**: `Value_Function_Uniqueness.thy`, unchanged.

### 2.8 `Relative_Arbitrage_Statement`

Unchanged except for constants renamed by §4 (`outerp` → `outer_prod`,
`orth_mat` → `orthogonal_matrix` — the latter does not appear in the statement
document, the former does at line 61).

### 2.9 Naming rule for theories and sessions

Three rules, in order of how often they are broken.

**(a) Spell words out. No initialisms, no acronyms, no truncations.** A theory
name is read far more often than it is typed, and it is what appears in
`imports`, in `ROOT`, in the generated document's table of contents and in
every `@{theory …}` antiquotation in the running commentary. `DPP`, `VF`, `QV`,
`FDD`, `Usc` and `Sc` are all forbidden; `Dynamic_Programming`,
`Value_Function`, `Quadratic_Variation`, `Finite_Dimensional_Distributions`,
`Semicontinuous` are what they abbreviate.

**(b) Name the subject, not the method or the headline theorem.** A session
outgrows a name taken from whatever it was doing on the day it was created.
`Martingale_Sampling` was accurate when sampling on dyadic grids was the whole
content, and became wrong once stopping, transfer and modification joined it;
`Path_Space_Tightness` names one theorem out of the eleven theories under it;
`Alexandrov_Sup_Convolution` names two of the five ingredients and none of the
purpose. The replacement names — `Continuous_Time_Martingales`,
`Continuous_Path_Spaces`, `Second_Order_Viscosity_Analysis` — name what the
session is *about*, which does not change when a theory is added.

**(c) No filler nouns.** `Extras`, `Misc`, `Utils`, `Aux`, `Toolkit`,
`Machinery`, `Support`, `Base` carry no information and postpone the naming
problem rather than solving it. If the only honest name for a group of theories
is `Extras`, the group is not a session — either it belongs inside an existing
one, or it is two things that each deserve a name. (This is why the plan's
earlier `Martingale_Extras` and `Matrix_Spectral_Extras` are gone.)

Consequences already applied above, and to be applied to anything the executing
agent invents later:

* `Exit_Class_DPP` is the one existing theory whose name breaks rule (a). It
  disappears in phase 12; no separate rename is needed.
* Proper names are not abbreviations and stay: `Ky_Fan`, `Berge`, `Rademacher`,
  `Alexandrov`, `Moreau_Envelope`, `Poincare_Separation`, `Householder_Rotation`,
  `Brownian_Motion`, `Doob_Inequality`, `Vitali_Convergence`.
* Ordinary English words that merely look short are fine, at *theory* level,
  where the enclosing session already supplies the subject: `Doubling`,
  `Pasting`, `Kernels`, `Assembly`, `Witness`, `Tightness`, `Limits`, `Shift`.
  Rule (b) binds sessions strictly and theories loosely, for exactly that
  reason.
* The paper's own numbering may be used as a suffix where it is the clearest
  label, spelled with an underscore: `Value_Function_Supersolution_Case_1`, not
  `Case1` and not `C1`.
* This rule is about **theory and session names only**. Existing *constant*
  names (`qvp`, `qvsa`, `qvmat`, `lsc_env`, `usc_sel`, `psd`, `kyfan`, `Mp`)
  are out of scope: they appear in the `Statement` document and in
  `NOTES_FOR_AUTHORS.md`, and renaming them is a separate decision with a
  separate cost. Do not rename them as part of this refactor.

### 2.10 Session renames, and the alternatives that were rejected

Four sessions change name. The reasoning is recorded because the names are a
judgement call and are cheap to revisit before phase 1, and impossible after.

| from | to | why, and what else was considered |
|---|---|---|
| `Martingale_Sampling` | `Continuous_Time_Martingales` | Sampling was the *method*; the subject is the continuous-time layer that the AFP's `Martingales` does not provide. Rejected: `Martingale_Extras` (rule (c)); `Martingale_Sampling_and_Transfer` (accurate but names two methods rather than the subject, and grows again the next time something is added). **If the breadth of the name is uncomfortable**, the honest alternative is not a longer name but a split: `Martingale_Sampling` keeps grids, Doob, optional sampling, quadratic variation and stopping times, and a sibling `Martingale_Transfer` takes `Martingale_Algebra`, `Martingale_Transfer`, `Natural_Filtration`, `Modification_Transfer` and `Kernels` (≈ 3 000 lines, both over the AFP's `Martingales`, neither importing the other). That gives two precise names instead of one broad one, at the cost of a session boundary. |
| `Path_Space_Tightness` | `Continuous_Path_Spaces` | Tightness is one theorem of eleven theories, and after absorbing pathwise quadratic variation and localisation it is not even the largest. Rejected: `Path_Space_Weak_Convergence` (excludes the pathwise-functional half). |
| `Alexandrov_Sup_Convolution` | `Second_Order_Viscosity_Analysis` | Names the purpose rather than two of the five ingredients; "second-order" distinguishes it from first-order Hamilton–Jacobi theory, which needs none of this. Rejected: `Crandall_Ishii` (names the summit but hides Rademacher and Alexandrov, and says nothing about viscosity); `Viscosity_Comparison` (there is no comparison *theorem* in the session, only the machinery, and it would collide with `Comparison_Principle` in `Relative_Arbitrage`). Discoverability of the classical theorems is preserved by the theory names `Rademacher.thy`, `Alexandrov.thy`, `Jensen_Lemma.thy`, `Theorem_On_Sums.thy`. |
| — (new) | `Symmetric_Matrix_Spectra` | Was `Matrix_Spectral_Extras` in an earlier draft of this plan; rule (c). The entry is about the spectrum of a real symmetric matrix and nothing else. |

`Wiener_Measure`, `Semicontinuous_Analysis`, `Relative_Arbitrage` and
`Relative_Arbitrage_Statement` keep their names: each already names its subject.

---

## 3. Extraction lists

These are the lemma names to move, by destination. The lists are derived from
the genericity probe and are believed exhaustive for the categories named; the
executing agent should re-run the probe after each batch and pick up stragglers.

### 3.1 → `Symmetric_Matrix_Spectra/Matrix_Algebra.thy`

From **Comparison_Principle**: `trace_transpose_eq`, `trace_mul_comm`,
`trace_mult_sym_right`, `trace_add_eq`, `matrix_mult_scaleR_left`,
`matrix_mult_add_left`, `norm_transpose_eq`, `transpose_scaleR`,
`transpose_scaleR_matrix`, `transpose_add_matrix`, `transpose_shifted_block`,
`matrix_shift_apply`, `norm_shifted_block`, `shift_cancel_matrix`,
`matrix_vector_neg_left`, `matrix_vector_mult_diff_gen`,
`matrix_vector_mult_scaleR_gen`, `matvec_add_right'`, `matvec_scaleR_right'`,
`matrix_apply_eq`, `matrix_diff_vec`, `inner_matrix_sym`, `inner_matrix_axis`,
`matrix_Basis_cases`, `quad_form_shift_identity`, `quad_form_shift_identity_neg`,
`neg_shift_matrix_apply`, `tendsto_entry`, `transpose_limit`,
`tendsto_quadratic_form`, `conj_mat_continuous`, `affine_linear`,
`affine_has_derivative`, `affine_inv_dist`, `norm_le_card_Basis_bound`.

From **Operator_Envelopes**: `matvec_minus_right`, `matvec_diff_right`,
`matvec_scaleR_right`, `matrix_mul_diff_right`, `matrix_mul_diff_left`,
`inner_matrix_transpose`, `trace_matrix_commute`, `orth_preserves_inner`,
`matvec_orth_inv`, `conj_orth_inv`, `norm_orthogonal_matrix_vector`,
`norm_matrix_sq_trace`, `norm_conj_orthogonal`, `transpose_shift_add`,
`transpose_shift_diff`, `continuous_on_matrix_entry`,
`continuous_on_matrix_mult`, `continuous_on_matrix_transpose`,
`continuous_on_conj_trace`, `inner_scaleR_diff_eq`, `halfspace_not_antipodal`,
`open_orth_image`, `open_affine_image`, `affine_interior_sub`,
`affine_inv_shape`, `affine_inv_left`, `affine_inv_right`,
`affine_interior_image`.

From **Poincare_Separation**: `matrix_matrix_mult_diff_right`,
`matrix_matrix_mult_diff_left`, `trace_diff_matrix`, `trace_sum_matrix`,
`transpose_sum_matrix`, `inner_transpose_self`, `matrix_mult_entry_inner`,
`norm_matrix_mult_le`, `norm_mat_1`, `conj_diff_expand`, `norm_conj_diff_le`,
`entry_abs_le_norm`, `continuous_on_matrix_entry`, `continuous_on_quadform`,
`closed_symmetric_matrices`, `norm_unit_diff_le`, `subspace_inter_nonzero`,
`dim_inter_ge`.

From **Curvature_Operator**: `trace_matrix_sum`, `transpose_matrix_sum`,
`matrix_vector_mult_sum`, `matrix_mult_sum_right`, `matrix_add_rdistrib`,
`scaleR_matrix_mult`, `trace_scaleR`, `scaleR_matrix_vector`,
`neg_matrix_vector`, `inner_transpose_matrix`, `sym_inner_swap`.

From **Operator_Continuity**: `matrix_vector_mult_add`,
`matrix_vector_mult_diff`, `transpose_diff_matrix`, `scaleR_matrix_matrix_left`,
`trace_scaleR_matrix`, `trace_conj`.

From **Constraint_Set_Convexity**: `matrix_vector_mult_vsum`,
`matrix_mult_sum_left`, `transpose_scaleR`, `transpose_add`,
`trace_mult_convex_comb`.

From **Value_Function_Viscosity**: `trace_mult_sum`, `trace_mult_diff`,
`trace_mult_scaleR`, `trace_mult_add`, `trace_mult_zero_right`,
`trace_mult_commute`, `trace_matrix_diff`, `trace_sum_matrix`,
`trace_msub_mat`, `transpose_matrix_diff`, `transpose_sub_smat`,
`matrix_msub_rdistrib`, `matrix_msub_ldistrib`, `matmul_scaleR_right`,
`matvec_add_right`, `matvec_scaleR_right`, `matvec_sum_right`, `matvec_axis1`,
`matvec_blin`, `matvec_norm_le`, `matmul_sandwich_blin`, `sandwich_mat1`,
`bounded_linear_trace_mult_left`, `bounded_linear_trace_mult_right`,
`bounded_linear_quadform`, `bounded_linear_transpose`, `trace_mult_blin`,
`quadform_abs_le`, `axis1_inner`, `axis1_self`, `inner_matrix_transpose`,
`unit_normalize`, `colmat_matvec`, `invertible_matrix_vector_inj`,
`singular_matrix_avoids_range`, `quad_taylor_step`, `quad_shift`,
`quad_grad_shift`, `quad_diff_bound`, `quad_diff_bound_gen`,
`quad_soften_split`, `quad_form_bounded_below`, `continuous_on_quad_tilt`,
`exists_enum_of_card`.

From **Viscosity_Solutions**: `inner_axis_one`, `matrix_vector_axis_one`,
`quadform_axis_pair`, `quadform_axis_pair_minus`, `matrix_vector_mult_vec_diff`,
`norm_less_of_ball`.

From **Exit_Class_Compactness**: `mat_inner_axis`, `mat_Basis_cases`,
`norm_outer_prod`, `bounded_linear_trace`, `bounded_linear_cross`,
`bounded_linear_cross_pair`.

From elsewhere: `trace_mat1` (Brownian_Market), `diag_eq_inner_axis` and
`trace_nonneg_psd` (Ito_Market), `diag_entry_quadform` (Path_Tightness_Market —
same statement as `diag_eq_inner_axis`), `inner_mv_axis` (Pathwise_Quadratic_Variation),
`quadform_convex_comb`, `continuous_on_trace_mult_right`,
`closed_trace_proj_halfspace` (Exit_Class), `inner_diff_self_expand`
(Exit_Time_Semicontinuity), `trace_conjugate` (Viscosity_Comparison_Interface),
`matrix_vec_apply` and `matrix_of_symmetric` and `matrix_symmetric_swap` and
`has_derivative_quadratic_form` and `quadratic_test_derivative` and
`quadratic_test_grad_derivative` (Sup_Convolution — these are the only
`real^'n`-specific lemmas in that session and they do not belong there),
`compact_cball_bound` (Value_Function_Uniqueness),
`continuous_on_vec_lambda` and `measurable_vec_components` and
`integrable_vec_components` (Brownian_Continuous/Brownian_Market —
these last three are measurability, so they go to `Continuous_Time_Martingales` instead).

**Deduplicate while moving**: of each group in §1.4 keep one name. Suggested
canonical names, all following HOL-Analysis convention: `trace_mul_comm`,
`matrix_mul_diff_right`, `matrix_mul_diff_left`, `matrix_mul_scaleR_left`,
`matrix_vector_add_right`, `matrix_vector_scaleR_right`, `trace_diff`,
`inner_matrix_transpose`, `trace_conj`, `transpose_scaleR`, `transpose_add`,
`trace_sum`.

### 3.2 → `Second_Order_Viscosity_Analysis/Doubling.thy`

The whole doubled-maximum apparatus, generalised to `'a::euclidean_space`
(see §4.1). From **Comparison_Principle**:

`doubling_partial_max_fst`, `doubling_partial_min_snd`, `doubling_diagonal_max`,
`doubling_diagonal_max_gen`, `doubling_off_diagonal`, `doubling_off_diagonal_gen`,
`doubling_grad_nonzero`, `doubling_penalty_bound`, `doubling_penalty_bound_gen`,
`doubling_dist_bound`, `doubling_ge_diagonal`, `doubling_maximiser_exists`,
`doubling_maximiser_exists_gen`, `doubling_upper_bound_exists`,
`doubling_grad_lower_bound`, `doubling_grad_norm_lower_bound`,
`doubling_maximiser_far_from_boundary`, `doubling_maximiser_value_transfer_gen`,
`doubled_maximiser_over_UNIV_snd`, `mxK_of_UNIV_snd`, `diagonal_max_increments`,
`norm_lt_of_penalty_bound_gen`, `penalty_difference_identity`,
`penalty_difference_identity_snd`, `penalty_gradient_nearby_bound`,
`penalty_gradient_nearby_bound_gen`, `penalty_gradient_nearby_upper`,
`penalty_gradient_nearby_upper_gen`, `diff_displacement_bound`,
`doubled_penalty_jet`, `doubled_jet_slice_fst`, `doubled_jet_slice_fst_gen`,
`doubled_jet_slice_snd`, `doubled_jet_slice_snd_gen`, `doubled_jet_slices_at_max`,
`doubled_slice_numerator_fst`, `doubled_slice_numerator_snd`,
`filterlim_slice_fst`, `filterlim_slice_snd`, `tilt_absorb`,
`doubled_tilted_interior_max`, `tilted_doubled_jet_slices`,
`tilted_doubled_jet_slices_gen`, `tilted_doubled_hessian_nonpositive`,
`tilted_doubled_hessian_nonpositive_gen`, `global_max_imp_interior_max`,
`interior_radius_pos`, `gradient_vanishes_at_interior_max`,
`gradient_is_minus_tilt`, `shifted_annulus_bound`, `shifted_annulus_bound_split`,
`shifted_annulus_bound_split_gen`, `shifted_jensen_smallness`,
`jet_transfer_quadratic`, `semiconvex_shift_perturb`, `semiconvex_penalty_gen`,
`convex_on_prod_diff`, `convex_on_prod_add`, `convex_on_norm_lift`,
`norm_sq_prod_split`, `doubled_semiconvexity_constant_pos`,
`polarization_symmetric`, `parallelogram_norm`, `symmetric_form_bound`,
`symmetric_form_bound_unit`, `hessian_abs_bound_of_two_sided`,
`norm_matrix_le_of_form_bound`, `block_form_bound_fst`, `block_form_bound_snd`,
`block_form_bound_fst_gen`, `block_form_bound_snd_gen`,
`norm_block_matrices_bounded`, `norm_block_matrices_bounded_gen`,
`linear_block_fst`, `linear_block_snd`, `linear_block_fst_gen`,
`linear_block_snd_gen`, `sym_block_fst`, `sym_block_snd`, `sym_block_fst_gen`,
`sym_block_snd_gen`, `transpose_matrix_block_fst`, `transpose_matrix_block_snd`,
`transpose_matrix_block_fst_gen`, `transpose_matrix_block_snd_gen`,
`block_fst_matrix_apply`, `block_snd_matrix_apply`, `block_fst_matrix_apply_gen`,
`block_snd_matrix_apply_gen`, `linear_of_bounded_linear_prod`,
`sums_matrix_inequality_gen`, `sums_gives_ordering`, `sums_gives_ordering_gen`,
`sums_ordering_at_interior_max`, `sums_ordering_at_interior_max_gen`,
`jet_imp_local_max_test`, `jet_imp_local_min_test`,
`jet_imp_local_min_test_onesided`, `superjet_local_max_onesided`,
`quad_bdd_above_on_bounded`, `quad_bdd_below_on_bounded`,
`quadratic_grad_derivative_at`, `supconv_radius_uniform`,
`bounded_seq_limit_point`, `bounded_seq_limit_point_triple`,
`nearby_of_convergent`, `nearby_of_convergent_shifted`,
`nearby_of_convergent_shifted_neg`, `gradient_sequences_align`,
`gradient_sequences_align_of_bound`, `tendsto_of_norm_bound`,
`positive_separation_of_value_gap`, `uniform_modulus_on_compact`,
`continuous_extension_bounded`, `bounded_on_compact`, `usc_extend_const_below`,
`two_domain_gap`, `fary_of_pin`, `cball_subset_interior_of_far_from_boundary`,
`cball_prod_subset_of_far_from_boundary`, `compact_frontier_nonempty`,
`cont_pos_near`, `norm_Pair_le`, `choice4`, `tilt_sequence_pos`,
`tilt_sequence_lt`, `tilt_sequence_tendsto`, `tilt_sequence_admissible`,
`jensen_tilt_threshold_pos`, `jensen_tilt_small_enough`,
`shifted_family_parameters`.

Those whose statements mention `real^'n^'n` matrices (`norm_block_matrices_*`,
`transpose_matrix_block_*`, `block_*_matrix_apply*`, `sums_matrix_inequality_gen`,
`jet_imp_local_*_test`, `matrix`-valued ones) stay at `real^'n` and go into a
companion `Doubling_Matrix.thy` in `Symmetric_Matrix_Spectra` — or, if that
creates an awkward dependency, keep them at the bottom of `Doubling.thy` and
let `Second_Order_Viscosity_Analysis` import `Symmetric_Matrix_Spectra`. **Prefer the
latter**: one import edge is cheaper than a split file.

### 3.3 → `Second_Order_Viscosity_Analysis/Soft_Penalty.thy`

`soft_pen`, `soft_grad`, `soft_hess`, `soft_shrink` and everything named for
them: `soft_pen_T_tendsto`, `soft_pen_bracket_tendsto`,
`soft_pen_second_summand_tendsto`, `soft_pen_rem_aux`, `soft_pen_radial_mono`,
`soft_pen_kappa_exists`, `soft_R_lipschitz`, `soft_R_gt_one`,
`soft_grad_coeff_pos`, `soft_gap_pos`, `soft_rho_exists`, `soft_grad_norm_pos`,
`norm_le_soft_R`, `sqrt_norm_sq_add_one_ge_one`, plus the exact square-root
expansion `sqrt_second_order_exact`, `sqrt_diff_exact`, `sqrt_rhs_aux`,
`sqrt_shift_diff_bound`, `sqrt_lt_half_plus_one`, `radial_profile_pos`,
`inner_sq_over_norm_sq_le`, `inner_sq_quotient_bounded`, `rem_split_aux`,
`div_mul_div_cancel_aux`, `quartic_pen` and its jet.

### 3.4 → `Semicontinuous_Analysis`

`Semicontinuity.thy`: `usc_attains_sup_gen`, `lsc_attains_inf_gen`,
`lsc_attains_inf_ex`, `usc_eps_add`, `usc_eps_scale`, `usc_eps_of_continuous`,
`lsc_diff_continuous`, `usc_extension_bounded`, `max_principle_boundary_attains`
(rename to `sup_diff_attained_on_compact`).

`Semicontinuous_Envelopes.thy`: `lsc_env`, `usc_env`, `lsc_envK`, `Kext` and all their
lemmas (`lsc_env_bdd_above`, `lsc_env_bdd_below_ball`, `lsc_env_le_self`,
`lsc_env_ge`, `Kext_proj_bound`, `Kext_proj_near`, the envelope-monotonicity
and usc-fixpoint sections).

`Berge.thy`: as listed in §2.2.

`Semicontinuous_Selection.thy`: as listed in §2.2, plus `Least_nat_eq_iff`.

### 3.5 → `Continuous_Time_Martingales`

As listed in §2.5. Additionally the measure-theoretic odds and ends currently
in paper theories: `integrable_of_sq_integrable`, `bounded_measurable_integrable`,
`clamp_integrable`, `tail_indicator_measurable`, `tail_integrable`,
`integrable_mult_of_sq`, `integrable_cmult`, `integral_cmult`,
`integral_pos_of_AE_pos`, `integrable_bounded`, `set_integral_lborel_singleton`,
`set_integral_at_origin`, `set_integral_vec_component`,
`set_integral_mat_component`, `measurable_mat_entries`, `integrable_mat_entries`,
`ennreal_Sup_image`, `ennreal_min_eq`, `ennreal_strict_between`,
`cInf_shift_real`, `cInf_mult_pos` (**two copies**),
`AE_tendsto_zero_of_summable_sq`, `exp_neg_time_integrable`,
`exp_neg_time_integral_lower`, `integral_of_bounded_linear`,
`set_integral_of_bounded_linear`, `indep_var_distr_iff`,
`indep_var_PiM_components`.

### 3.6 → `Symmetric_Matrix_Spectra/Ky_Fan.thy`, from combinatorics currently scattered

`exists_top_subset`, `sum_weighted_le_top_subset`, `finite_arg_min_on`,
`threshold_sum_maximal`, `threshold_remove_min` (Eigenvalues);
`threshold_shrink_one`, `threshold_chain_aux`, `threshold_chain`
(Threshold_Chain); `reduce_weights_to_exact`, `box_program_bound`,
`lp_upper_bound`, `sum_min_le_threshold` (Poincare_Separation);
`exists_min_subset` (Value_Function_Viscosity); `two_fractional` (Eigenvalue_Bound_Exact).

These are statements about finite index sets and real weights with no matrix in
sight; they could equally form a `Finite_Threshold_Sets.thy`. **Do that** — it
keeps `Ky_Fan.thy` about eigenvalues.

---

## 4. Generalisations to try

Ordered by (value × confidence) / cost. Each entry says what to change, why it
should work, and what to do if it does not.

### 4.1 Doubling toolbox: `real^'n::finite` ⟶ `'a::euclidean_space` — **high value, high confidence**

The ≈130 lemmas of §3.2 are stated over `real^'n::finite ⇒ real` but their
proofs use only `norm`, `inner`, `dist`, `compact`, `convex_on` and `Basis` —
never `transpose`, `**`, `*v`, `mat`, `axis` or `CARD('n)`. The precedent is
inside the development: `Sup_Convolution` already states `doubling_ge_diagonal`,
`doubling_antitone`, `doubling_penalty_squeeze`, `doubling_limit_maximises`,
`sums_matrix_inequality`, `product_form_block_diagonal`, `superjet_local_max`
and the whole semiconvexity calculus at `'a::euclidean_space`, with proofs of
the same shape.

*Method*: change the `fixes` clause, replace `real^'n` by `'a::euclidean_space`
in the statement, leave the proof; `real^'n` is an instance of
`euclidean_space` so all instantiations at the call sites keep working with no
edit. Expect ≥90% to go through untouched.

*If it fails*: for the residue, keep the `real^'n` statement, do **not** attempt
a new proof, and record the lemma in a "resisted generalisation" section of the
plan's completion note with the error message.

*Exception*: anything whose statement produces a matrix (`matrix W`,
`transpose`, `mat 1`) must stay at `real^'n`. That is about 25 of the 130.

### 4.2 Semicontinuity envelopes: `real^'n` ⟶ `'a::metric_space` — **high value, high confidence**

`lsc_env`, `usc_env`, `lsc_envK`, `Kext` are defined over `real^'n` but use only
`ball`, `INF`, `SUP`, `closest_point`. Move to `'a::metric_space` (`Kext` needs
`closest_point`, so `'a::euclidean_space` or a `convex`/`closed` side condition —
use `'a::euclidean_space` for `Kext` and `'a::metric_space` for the other three).

`lsc_attains_inf_gen` and `usc_attains_sup_gen` are already at
`'a::metric_space` in `Operator_Envelopes` and were re-proved at `real^'n` in
`Value_Function_Viscosity`; keep the general one and delete the specialisation.

### 4.3 Martingale index type: `real` ⟶ the AFP's generic index — **medium value, high confidence**

Many of the martingale lemmas in §2.5 are stated at index type `real` when the
AFP `Martingales` entry supports
`'b::{second_countable_topology, order_topology, linorder_topology}`. Again
there is an in-repo precedent: `martingale_diff` exists at the generic index in
`Pathwise_Quadratic_Variation` and at `real` in `Exit_Class_DPP`; keep the
generic one. Candidates: `martingale_add`, `martingale_add_const`,
`martingale_cong_ge`, `martingale_cong_AE`, `martingale_sub_initial`,
`martingale_diff`, `martingale_bounded_linear_image`, `martingale_vec_nth`,
`martingale_mat_nth`, `martingale_pair_fst`, `martingale_pair_snd`,
`martingale_PiM_component`, `martingale_distr`, `martingale_restrict_full`.

*Caveat*: `martingale_time_change` and everything stopping-related genuinely
needs a real index (it uses `min`, `0 ≤ u`, dyadic grids). Leave those.

### 4.4 Unify the two essential infima — **medium value, high confidence**

`ess_inf_time :: 'a measure ⇒ ('a ⇒ real) ⇒ ennreal` (Value_Function_Market) and
`ess_inf_enn :: 'a measure ⇒ ('a ⇒ ennreal) ⇒ ennreal` (Exit_Class_Infinite) are
the same construction at two payoff types. Define once:

```
definition ess_inf :: "'a measure ⇒ ('a ⇒ ennreal) ⇒ ennreal"
  where "ess_inf M f = Sup {c. AE ω in M. c ≤ f ω}"
```

in `Continuous_Time_Martingales`, then `ess_inf_time M τ ≡ ess_inf M (ennreal ∘ τ)` and
`ess_inf_enn = ess_inf`. The lemmas `ess_inf_time_mono`,
`ess_inf_time_ge_iff_measure` and their `enn` counterparts collapse to one copy
each.

### 4.5 `Exit_Time`/`pexit`/`iexit` type classes — **low value, high confidence**

`etime` is already fully generic. `pexit` and `iexit` are stated at
`'b::polish_space`; they use only `- K` membership and an infimum, so
`'b::topological_space` suffices for the definition and `'b::metric_space` for
the semicontinuity lemmas. Worth doing only because it removes a spurious
`polish_space` from the paper's exit-time statements. Do it if free; skip on
first resistance.

### 4.6 Restriction package: full-measure event ⟶ conull set — **low value, medium confidence**

The `*_restrict_full` family in `Stopped_Localization` assumes `G` is a
full-measure event of a probability space. The proofs should go through for any
`G ∈ sets M` with `emeasure M G = emeasure M (space M)` on a finite measure.
Try; abandon quickly.

### 4.7 Holder subsequence extraction: drop `real_normed_vector` — **low value, low confidence, speculative**

`holder_family_subsequence` is at `'b::{real_normed_vector,heine_borel}` and
`holder_family_subsequence_dist` is its `dist`-phrased corollary. The metric
version ought to hold at `'b::heine_borel` alone. This is a genuine proof change
(the Arzelà–Ascoli step uses `norm (F m t - F m s)`). **Marked speculative:
attempt only if everything else is done, and abandon at the first failed step.**

### 4.8 Path tightness in a general Euclidean codomain — **medium value, low confidence, speculative**

`Path_Tightness`'s vector-valued layer is stated for `real^'m::finite`. The
argument is coordinatewise, so `'b::euclidean_space` should work by summing over
`Basis` instead of over `UNIV::'m set`. This *is* a proof change (index-set
bookkeeping), so it is speculative. **Do not attempt** unless the executing
agent finds the change is mechanical; the payoff is not worth a rewrite.

### 4.9 Non-generalisations — record and move on

State these so nobody spends time on them:

* `Doob_Inequality`, `Quadratic_Variation`, `Optional_Sampling` are real-valued
  because Doob needs an order. Correct as is.
* `Increment_Moments`' fourth-moment package is real-valued for the same reason;
  the vector case is obtained coordinatewise at the call sites and that is the
  right design.
* `unif_integrable` is defined on `nat`-indexed sequences. A filter-indexed
  version would be more general but Vitali's theorem is applied only along
  sequences here. Leave.
* `Curvature_Operator`'s spectral theorem is for `real^'n^'n`. A
  `euclidean_space` operator version is a different theorem. Leave.
* The paper-specific constants (`feasible`, `ell_op`, `Pi_proj`, `sconstraint`,
  `exit_class`, `exit_val`, …) are already as general as they should be; they
  are the paper's objects.

---

## 5. Deduplication catalogue

Do these first: they are pure deletions and they shrink everything else.

### 5.1 Definitions

| action | detail |
|---|---|
| delete `outer_prod` in `Comparison_Principle`:3406 | it shadows the identical `Curvature_Operator`:34; after the move both become `Symmetric_Matrix_Spectra.Outer_Products.outer_prod` |
| delete `hh` (Operator_Envelopes:677) **or** `hrefl` (Value_Function_Viscosity:8844) | keep one, in `Householder_Rotation.thy`, named `hrefl`; port `hh_sym`, `hh_mv` and the `hrefl_*` lemmas into one set |
| unify `rotv` and `rotm` | keep `rotm` (the normalised form the supersolution proof needs) and derive `rotv`'s uses from it, or keep both with one proved from the other — but prove orthogonality once |
| delete `orth_mat` (Viscosity_Comparison_Interface:79) | replace by HOL-Analysis `orthogonal_matrix`; delete `orth_mat_inner`, `orth_mat_surj`, `orth_mat_transpose` if HOL-Analysis has them, else rename them to `orthogonal_matrix_*` |
| make `outerp` an abbreviation | `outerp x ≡ outer_prod x x`; keeps `Statement/Theorem_1_1_Statement.thy`:61 displaying something meaningful — **check the displayed definition still reads well and adjust the surrounding prose if not** |
| `is_proj` | keep, but move to `Ky_Fan.thy`; it is "orthogonal projection matrix", not a paper notion |

### 5.2 Lemmas re-proved under the same name in an importing theory (delete the later copy)

`inner_matrix_transpose`, `lsc_env_bdd_above`, `lsc_env_le_self`, `lsc_env_ge`
(Value_Function_Viscosity, all present in Operator_Envelopes);
`lsc_attains_inf_gen` (Value_Function_Viscosity copy is *less* general than the Operator_Envelopes original — delete
the Value_Function_Viscosity one); `outerp_borel` (Exit_Class_Marginals, present in
Exit_Class_Compactness); `pcut_pglue` (Exit_Class_Infinite, present in
Exit_Class_DPP); `martingale_cong_ge` (Exit_Class_DPP, present in
Exit_Class_Compactness); `trace_sum_matrix` (Value_Function_Viscosity, present in
Poincare_Separation).

Verified instances with line numbers, all of which shadow an already-imported
fact of the same name or statement:

| duplicate | shadows |
|---|---|
| `Comparison_Principle`:1112 `transpose_scaleR` | `Constraint_Set_Convexity`:542 `transpose_scaleR` — **and** is re-proved a third time at `Comparison_Principle`:9521 as `transpose_scaleR_matrix` |
| `Comparison_Principle`:9526 `transpose_add_matrix` | `Constraint_Set_Convexity`:545 `transpose_add` |
| `Comparison_Principle`:1035 `cInf_mult_pos` | `Operator_Envelopes`:2415 `cInf_mult_pos` |
| `Comparison_Principle`:5827 `matrix_apply_eq` | `Sup_Convolution`:7194 `matrix_vec_apply` |
| `Comparison_Principle`:3406 `outer_prod` (definition) | `Curvature_Operator`:34 `outer_prod` |
| `Value_Function_Viscosity`:12221 `lsc_env_bdd_above` | `Operator_Envelopes`:2035 `lsc_env_bdd_above` |

### 5.3 Lemmas with the same statement under different names (keep one)

All groups of §1.4. Plus, inside one file:
`aglue_inner_increment_comp` (Exit_Class_DPP:11533) and
`aglue_law_comp_increment` (Exit_Class_DPP:12078) — identical statements, both
used; keep the first, redirect the two uses.

### 5.4 Locale duplication

Introduce `ito_market_core` in `Ito_Market` carrying the Dynkin identity, make
`ito_volatile_market`, `ito_stopped_market` and `ito_const_horizon_market`
sublocales of it, and delete `Z_zero_expectation_const` (and any other
statement proved twice across those three locales — check
`dynkin_quadratic_holds` vs `const_dynkin_quadratic`, which look like the same
identity at a deterministic and at a random horizon).

### 5.5 Elementary real inequalities

One canonical home, `Continuous_Time_Martingales/Power_Inequalities.thy`, for
`square_add_le_two` / `sq_diff_le` / `sq_diff_le_two` / `diff_sq_le_double`
(one lemma), `abs_prod_le_sq`, `two_abs_prod_le_squares`,
`abs_prod_le_half_squares`, `sq_le_half_add_half_pow4`, `prod_sq_le_half_pow4`,
`pow4_nonneg`, `zero_le_fourth`, `pow4_diff_le`, `fourth_power_sum_bound`,
`abs_cube_prod_le_pow4`, `abs_prod_cube_le_pow4`, `four_prod_cube_le`,
`pow4_binomial`, `sq_times_sq`, `abs_pow4`, `sq_mono_abs`, `fourth_mono_abs`,
`sq_abs_mono`, `fourth_abs_mono`, `sq_diff_le_fourth`, `prod_minus_sq_bound`,
`sum_sq_le_sq_sum`, `abs_diff_le_two`, `sum_pow4_le_max_times_sum`,
`prod_le_K_split`.

The one-off arithmetic helpers of `Comparison_Principle`
(`small_multiple_exists`, `shift_limit_absurd`, `shift_limit_absurd2`,
`exists_small_rho_aux`, `gap_split_aux`, `exists_eps_aux`, `eps_mono_aux`,
`theta_exists_aux`, `soft_pen_rem_aux`, `rem_split_aux`,
`div_mul_div_cancel_aux`) are proof scaffolding, not results. Leave them where
their consumers are; do **not** promote them to a toolbox. If a batch of them
becomes unreachable after the extractions, delete them (`unused_thms` will say).

---

## 6. Execution order

Fourteen phases. Each ends with a green `isabelle build -d . <sessions>` and a
commit; no phase depends on a later one. Phases 1–5 are mechanical and should be
done first because they shrink the input to everything after.

| # | phase | risk | rough size |
|---|---|---|---|
| 1 | **Deduplicate.** §5.1–§5.5, in place, no files move. Delete same-name re-proofs, unify definitions, redirect uses. | low | −1 500 lines |
| 2 | **Rename the sessions and move the four misplaced theories.** Apply the three renames of §2.10 (`Martingale_Sampling` → `Continuous_Time_Martingales`, `Path_Space_Tightness` → `Continuous_Path_Spaces`, `Alexandrov_Sup_Convolution` → `Second_Order_Viscosity_Analysis`) across `ROOTS`, every `ROOT`, every `imports` and every `@{theory …}` antiquotation — do this *before* any content moves, so later diffs are content-only. Then move `Modification_Transfer` and `Exit_Time`→`Stopping_Times` into `Continuous_Time_Martingales`, and `Stopped_Localization`, `Pathwise_Quadratic_Variation` into `Continuous_Path_Spaces`. | low | 3 400 lines relocated |
| 3 | **Create `Symmetric_Matrix_Spectra`.** Move §3.1 and §3.6, carve `Symmetric_Spectral`, `Ky_Fan`, `Eigenvalue_Continuity`, `Poincare_Separation`, `Householder_Rotation`, `Orthonormal_Families`, `Outer_Products` out of the paper session. Break the upside-down chain of §1.3 by leaving `feasible_iff_eigval` and the two `Pi_proj`/`feasible` sections of `Eigenvalues` behind in `Relative_Arbitrage`. | medium | ≈ 7 000 lines relocated |
| 4 | **Create `Semicontinuous_Analysis`.** §3.4. | low | ≈ 1 800 lines |
| 5 | **Extract the martingale toolbox.** §2.5, §3.5. Largest single win in the readability of `Exit_Class_Compactness` and `Exit_Class_DPP`. | medium | ≈ 3 000 lines |
| 6 | **Split `Sup_Convolution`.** §2.3, textual split only. | low | 0 net |
| 7 | **Extract `Doubling.thy` and `Soft_Penalty.thy`** from `Comparison_Principle` into `Second_Order_Viscosity_Analysis`, at `real^'n` still. | medium | ≈ 5 500 lines relocated |
| 8 | **Generalise the doubling toolbox** to `'a::euclidean_space` (§4.1). Do this *after* the move so the diff is one file. | medium | 0 net |
| 9 | **Generalise the envelopes** (§4.2), the martingale index (§4.3), unify `ess_inf` (§4.4). | medium | −300 lines |
| 10 | **Consolidate the viscosity definitions** into `Viscosity_Definitions.thy` (§2.7 L2) and split `Comparison_Principle`/`Comparison_Two_Domain`. | medium | 0 net |
| 11 | **Split `Exit_Class_Compactness`** into six theories at the section boundaries of §2.7. | low | 0 net |
| 12 | **Split `Exit_Class_DPP`** into eight; test whether `Dynamic_Programming_Optional_Sampling` moves to `Continuous_Time_Martingales`. | medium | 0 net |
| 13 | **Split `Value_Function_Viscosity`** into six; move `Adapted_Quadratic_Variation` out of `Exit_Class_Marginals`. | low | 0 net |
| 14 | **Split `Wiener_Measure/Brownian_Motion`** (§2.4); re-run `unused_thms` across everything and delete the fourth-pass residue that `UNUSED_THMS.md` predicts; refresh `UNUSED_THMS.md`, `NOTES_FOR_AUTHORS.md` §"Infrastructure that had to be built" (it should now name the new sessions), and `ROOTS`. | low | −500 lines |

After phase 14, re-run the three probes of §0 and put the numbers in the
completion note.

### 6.1 Mechanics

* **Names.** Every new theory and session name obeys §2.9: words spelled out,
  no initialisms. If a name proposed in §2 turns out to fit the content badly,
  replace it with another *spelled-out* name rather than shortening it.
* **Renames.** When a lemma changes name, do not leave an alias. Fix the uses.
  The build will find them. `grep -rn '\bold_name\b' --include=*.thy .` before
  each rename, so the count of expected edits is known in advance.
* **Moves.** Move the `text ‹…›` block that precedes a lemma with it. The
  running commentary is a real asset of this development and must not be
  stranded.
* **Session splits.** Add the new session to `ROOTS` and give it a `ROOT` whose
  `description` is that session's line from §2.0, plus `root.tex` and
  `root.bib` copied and trimmed from the nearest existing session. Update the
  `description` of every session whose contents change — `Martingale_Sampling`'s
  current one no longer describes what it will hold.
* **Documents.** Each session's `root.tex` lists theories; update it in the same
  commit as the split, or the document build breaks silently.
* **`Statement`.** Build it last, every phase. It is the acceptance test: if
  `Theorem_1_1_Statement.thy` still compiles and still displays the same
  definitions, the refactor preserved the deliverable.
* **Commit granularity.** One commit per phase, or per theory within a phase for
  phases 3, 5, 7 and 12. Commit messages in the existing style (imperative,
  lowercase after the session prefix).

---

## 7. Rules for the executing agent

1. **Do not prove new mathematics.** Every change here is a move, a rename, a
   deletion, or a type-class widening that leaves the proof text untouched. If a
   generalisation needs a new proof step, revert it and record it.
2. **Never weaken a statement to make a move work.** If a lemma will not move
   without changing what it says, leave it where it is and record why.
3. **`sorry` is forbidden**, including transiently. The development's claim is
   that it contains none; a commit that introduces one, even to be removed
   later, breaks that claim in the history.
4. **Build after every theory move**, not after every phase. A broken import
   chain found ten moves later costs more than ten builds.
5. **When a prediction in this plan is wrong**, the plan is wrong, not the
   development. Record the discrepancy in the completion note; do not force the
   layout.
6. **Preserve the `(*<*) … (*>*)` markers** and the `document = false` settings;
   they are what keeps the `Statement` document to five pages.
7. **No abbreviated theory or session names**, ever, including for scratch or
   intermediate files that survive a phase. See §2.9.
8. **The four probes of §0 are the progress metric.** Report them at the start
   and end: theory count, line count, lemma count, and the number of lemmas
   whose statements mention no project-defined constant *while sitting in a
   paper session*. That last number is currently **589**; the target is < 50.

---

## 8. Answers to the three questions, summarised

**(1) Generality.** The mathematics is stated at the right generality wherever
it was written to be reused (`Sup_Convolution`, `Path_Space`, `Modification_Transfer`,
`Exit_Time`, the AFP-facing sessions). It is stated too narrowly wherever it was
written as a step of the paper proof and later turned out to be general: about
130 doubling lemmas pinned to `real^'n` that want `'a::euclidean_space`, the
semicontinuity envelopes pinned to `real^'n` that want `'a::metric_space`, and
a dozen martingale lemmas pinned to a real index. No lemma was found carrying an
unused hypothesis of substance; the hypotheses that look redundant
(`prob_space` where `finite_measure` would do, `polish_space` where
`metric_space` would do) are listed in §4.5–§4.6 and are worth about 20 lemmas
between them.

**(2) Usefulness to others.** 853 of 2 804 lemmas mention no project-defined
constant, and 589 of those sit inside a paper session. Grouped, they are
seven reusable libraries: matrix algebra, the spectral theorem and Ky Fan
theory, semicontinuity and Berge, the Crandall–Ishii doubling toolbox, the
martingale algebra/transfer package, pathwise quadratic variation as a Borel
functional, and the usc measurable selection theorem. Each is a plausible AFP
entry on its own; none is currently reachable without importing a paper about
relative arbitrage.

**(3) Placement.** Four theories are in the wrong session outright (§1.2), the
eigenvalue tower is stacked on top of the paper layer instead of under it
(§1.3), the viscosity-solution predicate is spread over four theories (§1.6),
and five files hold 60% of the development (§1.7). The layout of §2 fixes all
four, and phases 1–5 of §6 deliver most of the benefit for a quarter of the
work.

---

## 9. Completion note

All fourteen phases are done, each in its own commit, each ending with a green
`isabelle build` of all eight sessions and zero `sorry`.

### The probes of §0, re-run

| probe | before | after | target |
|---|---|---|---|
| theories | 58 | 103 | — |
| lines | 115 987 | 116 086 | — |
| top-level statements | 2 821 | 2 752 | — |
| definitions | 204 | 201 | — |
| **generic lemmas inside a paper session** | **597** | **200** | < 50 |

The line count is the one number that did not move, and that is what a
refactor of moves and splits should look like: 24 theorems and one definition
went in the phase-14 sweep, and the seven new theory headers and roughly sixty
pointer comments put the lines back.

`Relative_Arbitrage` is 76 400 lines across 47 theories, not the ≈ 55 000 §2.7
predicted. The 21 000-line shortfall is almost exactly the material probe 4
still counts: §3.1's extraction lists were written against the file layout of
the time and were only ever partly executable.

**Probe 4 stalls at 200 and phases 13–14 could not move it**, because from
phase 8 onward the plan schedules generalisation, splitting and dead-code
removal, none of which relocates a lemma out of the paper session. Reaching
< 50 needs a further extraction pass, mostly out of `Operator_Envelopes` (23),
`Comparison_Principle` (19) and the six `Value_Function_*` theories (about 60
between them). That work is not in this plan.

*Caution on measuring probe 4.* A comment stripper that counts `(*` depth goes
unbalanced on `(*` inside Isabelle cartouches and silently eats most of a large
theory; one such run reported 144 when the figure was 371. Blank only the
bodies of `text`/`section`/`subsection` cartouches, by `\<open>`/`\<close>`
depth, and leave `(* *)` alone. The corrected script reproduces this plan's own
stated 589 baseline as 597.

### §1.7, closed

All five oversized theories are gone. `Sup_Convolution` (7 544) became seven;
`Exit_Class_Compactness` (12 634) six; `Exit_Class_DPP` (16 792) eight;
`Value_Function_Viscosity` (16 324) six; `Comparison_Principle` (14 015) lost
its doubling toolbox and its two-domain half and is 8 055, the largest theory
in the development.

### Predictions that were wrong

Recorded per §7.5 rather than forced.

* **§4.3 (martingale index) is refuted.** Those lemmas are pinned to `real` by
  content, not by annotation: they fix `t0 = 0::real`, quantify over `0 ≤ i`,
  and `martingale_sub_initial` subtracts `X 0`, so the index type needs a zero
  that the AFP's index sort does not provide. Exactly one lemma survived the
  type change and then failed to apply the one below it.
* **§2.7 L2's `Viscosity_Definitions.thy` holds the definitions only.** The
  implications between the variants cannot follow them: half are proved from
  the `Operator_Envelopes` calculus, which is downstream of the only join point
  where all nineteen definitions can sit. `ell_op_pair`, `ell_op_lsc` and
  `ell_op_usc` had to move with them.
* **`Dynamic_Programming_Optional_Sampling` does not move** to
  `Continuous_Time_Martingales`. It is stated over `'n pairpath`, and so is the
  `path_stopping_time`/`pstopped`/`pre_sigma_of` block it consumes.
* **§3.2 assumed §3.1 was finished.** It was not; ten doubling lemmas depended
  on nine matrix lemmas still in `Comparison_Principle`, so phase 7 had to
  complete that part of §3.1 first.
* **§3.3's list is incomplete** — `abs_norm_diff_le`, `soft_grad_nonzero` and
  `exists_small_rho_aux` are needed by its own lemmas.

By contrast §4.1 and §4.2 over-delivered: 59 doubling lemmas and 32
semicontinuity lemmas widened on the statement line alone, 100% success, with
no proof step and no call site edited.

### Duplicates the catalogue missed

§5.2 lists the same-name re-proofs known at the time. Nine more were found by
sweeping every moved name after each phase, and every one of them survived a
green build, because a green build proves that no name *collides*, not that
nothing is duplicated — a later copy shadows an earlier one silently:

`trace_proj_psd_nonneg`, `onormal_subset`, `norm_outer_prod` (left behind by
phase 3); `martingale_diff`, `measurable_mat_entries` (phase 5);
`doubling_ge_diagonal`, `ess_inf_time_mono`, `ess_inf_time_distr`,
`feasible_scale`; and `AE_kglue_law'`, which was two different lemmas under one
name and had to be renamed rather than deleted. `Brownian_Continuous` was also
re-proving HOL-Analysis's own `continuous_on_vec_lambda`, without its
`[continuous_intros]` attribute.

The remaining repeated names — `Tgt`, `Tgt_sets_F`, `Tgt_sets_M`,
`stopped_integrable` in `Continuous_Time_Martingales` — are locale-scoped and
legitimate.

### Left open

* §1.4 group 9: `trace_conj` and `trace_conjugate`, same statement, both still
  in `Relative_Arbitrage`; and `Matrix_Algebra` has no trace-commute lemma at
  all, the group having collapsed onto the copy that stayed behind.
* §2.5: `Power_Inequalities.thy` was never created, and `sq_diff_le` /
  `square_add_le_two` are still two copies of `(a-b)² ≤ 2a² + 2b²`.
* §3.1: `matrix_vec_apply`, `matrix_of_symmetric`, `matrix_symmetric_swap`,
  `has_derivative_quadratic_form`, `quadratic_test_derivative`,
  `quadratic_test_grad_derivative` are still in
  `Second_Order_Viscosity_Analysis/Theorem_On_Sums.thy`. Phase 7 added the
  `Symmetric_Matrix_Spectra` edge, so the move is unblocked.
* §1.5: `outerp` is still its own definition in `Exit_Class`.
* Six definitions are reachable from nothing and were kept deliberately:
  `visc_sol_env`, `quartic_pen`, `Yint`, `pairX`, `pairY`, `tanpV`.
* `Doubling.thy` and `Soft_Penalty.thy` carry about twenty prose references to
  Theorem 4.2, Definition 3.1 and `ell_op`. Harmless to the build, but they are
  paper narrative inside a session §2.0 wants AFP-submittable. §2.0 says that
  rewrite is deliberately not scheduled.
