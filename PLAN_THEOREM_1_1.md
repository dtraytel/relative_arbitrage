# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Rewritten 2026-08-04 after the clause-(1) packaging and the N4 opening;
status refreshed 2026-08-05 after **NC-5, NC-1 and NC-4 CLOSED**
(commits `48d176f`, `382be79`, `c3ab9df`).
This document is the single source of truth for what is proved, what is
open, and what to do next. Everything referenced below is PIDE-verified
unless marked open — including ALL of `Deterministic_Radius_Market.thy`
(6,023 commands green), `Theorem_1_1.thy` (369 commands green, now
importing `Section_2_Usc` + `Deterministic_Radius_Market`) and ALL of
`Exit_Semicontinuity.thy` (2,676 commands green, crown
`ess_inf_pexit_usc` and the cap-invisibility lemmas included); the user's
batch build remains the final cross-check. WORKFLOW (user request):
develop DIRECTLY in the theory files via the PIDE MCP edit tool — the
current server session has the full ROOT and elaborates the tree
theories by name; scratches are only for throwaway probes. History and
superseded scoping live in git (`git log -p PLAN_THEOREM_1_1.md`) — do
not resurrect them.

**Remaining road to Theorem 1.1** (in recommended order). USER
DECISION 2026-08-04: formalize PRECISELY the paper's result — clause
statements must match the paper (proof techniques free); the law-level
restatement of clause (1) is a stepping stone, not a deliverable:
1. NC — the canonical market ("the closure adds no value"), now ON the
   critical path. §3/NC.
2. N5 — the essinf weak DPP; reading done, fit assessed, build order
   (a)–(d) scripted in §3/N5. Unblocks clause (2) together with the
   (now complete) N4 witness.
3. Clause (3) beyond the ball / general `n − k ≥ 2` — spherical BM on
   the discrete route (needed for the paper's general-K statement).

Sources: the paper (Lai/Shkolnikov/Soner, arXiv:2512.17702), its main
reference for Section 2 (Larsson–Ruf, *Minimum curvature flow and martingale
exit times*, EJP 29 (2024), arXiv:2003.13611, "LR" below), and Bouchard–Touzi
(SICON 49 (2011) 948–962) for the weak DPP.

---

## 0. The target and where it stands

Five clauses. TWO value functions are in play: the bare-locale
`val_fn k L K` (`Value_Function.thy`, supremum over all
`sufficiently_volatile_market` instances) and the PAPER-CLASS
`stopped_val_fn k L K` (`Section_2_Usc.thy`, supremum over `stopped_market`
— the locale plus the stopped/killed/integrable side conditions of the
paper's class (1.7)). `stopped_val_fn ≤ val_fn` by index inclusion;
equality is Doob's optional stopping for the whole class and is NOT
provable from the bare locale (the repo's `optional_stopping` needs an
integrable envelope of the unstopped process, which the locale does not
carry). **Downstream work should consume `stopped_val_fn`** — it is the
faithful rendering of the paper's Eq. (1.6).

| | clause | status |
|---|---|---|
| (0) | `v < ⊤` | **DONE** — `val_fn_finite_bounded`, `stopped_val_fn_finite_bounded` |
| (1) | regularity (usc) | **DONE in law-level form** — `clause_one_law_level`; the identification `w = ` class-sup ("the closure adds no value") is the canonical-market construction, §3/NC |
| (2) | `visc_sol k L (interior K) v` | open — needs N5 (DPP); the N4 witness input is now DONE |
| (3) | `v = 0` on `K − interior K` | ball case **DONE** — `val_fn_boundary_zero`, `stopped_val_fn_boundary_zero`; **and the interior value is REALIZED exactly for `n−k=1`**: `Theorem_1_1.stopped_val_fn_ball_eq_2d` — `stopped_val_fn 1 L (cball 0 r) x = ennreal (ball_v r 1 x)` for `0 < ¦x¦ ≤ r` (N4, complete); general `n−k ≥ 2` open (spherical BM, discrete route) |
| (4) | uniqueness | **DONE** — `theorem_1_1_uniqueness_general` via Theorem 4.2(a) |

**The clause-(1) headline** (`Section_2_Usc.clause_one_law_level`): for
`K ⊆ cball 0 r`, open `A` with `A ∩ K = {}`, and any horizon
`T ≥ r²/(n−k)` (uniform over `K` by `ball_v_le`), the law-level value
function

    w x = Sup (vshift T A x ` mkt_law_closure k L (cball 0 (2r)) 0 T)

is upper semicontinuous in `x` (`clause_one_usc`) and dominates the
paper-class value function on `K` (`clause_one_dom`:
`stopped_val_fn k L K x ≤ ennreal (w x)`). Cite this single theorem for
clause (1) unless/until the canonical market closes the gap.

---

## 1. How the paper proves Theorem 1.1 (orientation — read this first)

**Theorem 1.1 is two independent theorems.** *Uniqueness* (Section 4) is the
comparison machinery — fully formalised, closed. *Existence* (Sections 2, 3,
5) says the value function `v(x) = sup_{P ∈ P_x} P-essinf τ_K` is an usc
viscosity solution with zero boundary values. Only existence remains.

The existence half, structurally:

- **Lemma 2.1** — the convexified constraint set. *Proved:
  `Lemma_2_1_Exact.thy`.*
- **Lemma 2.2** — `P_x` relatively compact: 4th-moment bound → Kolmogorov
  continuity → Arzelà–Ascoli → Prokhorov. *Proved at the market class —
  §2.1 below.*
- **Lemma 2.3** — `P_x` closed. *Handled by the closure design — §2.2. The
  mathematical content the paper puts here resurfaces inside item NC.*
- **Prop 2.4** — usc of `v` + DPP + attainment. The paper's proof is "repeat
  LR word by word"; LR invoke a measurable-selection theorem
  (Bertsekas–Shreve 7.33) for TWO conclusions at once. Only the DPP needs
  selection; usc of `v` needs only Berge's maximum theorem (upper half),
  proved here as `usc_sup_over_compactin`. The DPP is item N5.
- **§3 (viscosity property)** — the envelope computation is proved
  (`Lemma_3_1.thy`); the sub/supersolution arguments need the DPP (N5) and
  Example 3.1 (N4).
- **Example 3.1** — the deterministic-radius market driving `v > 0` on
  `int K` and clause (3). A Brownian market can NOT substitute: Brownian
  exit times are arbitrarily small with positive probability, so their
  essinf is 0. The determinism of the radius is the whole point. Item N4.

**LR Prop 2.2(ii), the pivot for clause (1):** `P_x` consists of the
pushforwards `(x+·)_*P` with `P ∈ P₀` (laws started at the origin), so
`v(x) = sup_{P∈P₀} f(x,P)` with `f(x,P) = ((x+·)_*P)-essinf τ_K` — and usc
of `v` follows from Berge over compact `P₀`. Everything Berge needs is
proved, and the pushforward half is `stopped_val_fn_le_law_sup`; what is
NOT proved is the reverse ("the closure adds no value"). That is item NC.

---

## 2. What is DONE — the map of the machinery

Treat everything here as available and verified; do not re-derive, re-scope,
or "improve" it without a failing use case.

### 2.1 Lemma 2.2 at the market class

`Path_Tightness_Market.market_path_laws_convergent_subsequence`: for any
sequence of `sufficiently_volatile_market` instances (fixed `k L K x0`,
horizons `tt i`) that are

1. stopped at their horizon (`X s ω = X (min s (tau ω)) ω` pointwise),
2. confined: `K ⊆ cball 0 r`,
3. `acov s ω = 0` for `s > tau ω` pointwise,
4. diagonal `acov` entries pathwise `set_integrable` (AE),

the path laws `path_law (MM i) (XX i) T` admit a weakly convergent
subsequence. Conditions 1–4 are part of the paper's class (1.7), not extra
assumptions.

Under the hood, in dependency order:

- `sufficiently_volatile_market` (`Relative_Arbitrage_Stochastic.thy`) now
  matches the paper's class (1.7): `coord_Z_martingale` (componentwise
  compensated square is a martingale), `tau_stopping`, `X_paths_cont`
  (pointwise path continuity). Threaded through the three Ito locales; all
  Brownian witnesses rebased onto the continuous modification `cbmX` and
  MOVED to `Brownian_Continuous.thy` (import-cycle constraint; the
  coordinate transfer is `martingale_cbm_coord_square`; the stopped
  coordinate chain `cbmC`/`coord_Z_cbmA` is in `Brownian_Stopped.thy`).
- The AE→pointwise gap between the locale and the tightness adapter is
  closed by RESTRICTION, not strengthening: the transfer package at the end
  of `Stopped_Localization.thy` (`prob_space_restrict_full`,
  `integrable_restrict_full`, `integral_restrict_full`,
  `set_integral_restrict_full`, `distr_restrict_full`,
  `filtered_measure_restrict_full`,
  `sigma_finite_filtered_measure_restrict_full`,
  `adapted_process_restrict_full`, `martingale_restrict_full`) shows the
  whole filtered structure descends to a full-measure event, and
  `distr_restrict_full` makes the restriction invisible to path laws.
  Premise order everywhere: `prob_space M`, `G ∈ sets M`,
  `AE ω in M. ω ∈ G`.
- Per-coordinate rate bounds come from the eigenvalue constraint through
  diagonal entries: `psd_diag_nonneg`, `eigen_ub_diag`
  (`Path_Tightness_Market.thy`).
- The tightness core (`Path_Tightness.thy`): `tight_on_set_path_laws_vec`,
  `path_laws_convergent_subsequence_vec`, fed by
  `Increment_Moments.fourth_moment_bound_bounded` (4th moment from the
  compensator, no Itô, no BDG — constant `8C²` against the paper's `66C²`).

### 2.2 Lemma 2.3 by closure, and the unconditional usc theorem

Design decision (deliberate): the compact family for Berge is
**`Section_2_Usc.mkt_law_closure k L K x0 T`**, the closure of
`mkt_path_laws k L K x0 T` (set comprehension over the atomic predicate
`mkt_law_witness`, which bundles the four conditions of §2.1) in the weak
topology `weak_conv_topology (mtopology_of (path_metric T))`. With the
closure, "the limit lies in the family" is definitional; sequential
compactness needs only Lemma 2.2 on the base plus metrizability:

- `Section_2_Compactness.closure_of_sequential_limit` — a closure point is a
  sequential limit of base points (metrizable space).
- `Section_2_Compactness.seq_compact_closure_of` — subsequence extraction on
  `A` extends to `closure_of A`, limit again in the closure (approximate
  within `1/(n+1)`, extract on the base, triangle inequality).
- `Section_2_Usc.mkt_path_laws_seq_extraction` — Lemma 2.2 restated for the
  family (choice by iterated `SOME` over `mkt_law_witness`).
- `Section_2_Usc.mkt_law_closure_seq_compact` — the discharged obligation.
- `Section_2_Usc.weak_conv_on_prob_limit` / `mkt_law_closure_prob` — closure
  points are probability measures (total mass survives weak limits; test
  against the constant 1).

**Headline: `Section_2_Usc.vshift_sup_usc_mkt`** — for `0 ≤ T`, open `A`,
`K ⊆ cball 0 r`, `mkt_path_laws k L K x0 T ≠ {}`:

    x ↦ Sup (vshift T A x ` mkt_law_closure k L K x0 T)

is upper semicontinuous (eventually-form). No compactness hypothesis
anywhere. `vshift T A y Q = enn2real (Q-essinf τ_A(y + ·))`, and
`vshift_path_law` carries it to markets:
`vshift T A y (path_law M X T) = enn2real (ess_inf_time M (etime T A (λs ω. y + X s ω)))`.

### 2.3 The Berge/usc machinery this feeds (all proved)

In `Section_2_Usc` / `Section_2_Compactness` / `Exit_Time` / `Path_Space`:
`usc_sup_over_compact(in)`, `box_of_sequential(_euclidean)`,
`etime_usc_on_paths`, `essinf_etime_usc`, `etime_shift_box`, the erosion
operator (`Exit_Time.eroded` and its laws), open/closed-set Portmanteau
wrappers (`weak_conv_closed_full_measure`,
`weak_conv_open_positive_eventually`), `metrizable_weak_conv_path_topology`,
`compactin_of_seq_compact`, `vshift_sup_usc`,
`vshift_sup_usc_of_seq_compact`.

### 2.4 The RQ-A toolkit (proved; superseded for the confined class)

The linear-inequality route that avoids Skorokhod representation:
`Relative_Arbitrage_Convexity.support_characterisation`,
`Path_Tightness.weak_conv_on_integral_unif_integrable`,
`Path_Space.weak_conv_on_nn_integral_le`,
`Increment_Moments.sq_tail_bound_of_fourth_moment`,
`clamp_integral_error`, `tendsto_real_of_approximants`.

As predicted, for the CONFINED class all covariation functionals are
bounded and plain weak convergence sufficed everywhere in §2.5–2.6; the UI
machinery was not needed for clause (1). It remains available for N4/N5.

### 2.5 The Section-2 law-level layer (all in `Section_2_Usc.thy`)

- **Nonemptiness**: `mkt_path_laws_nonempty` — the immediate-stop market
  (helper `set_integral_at_origin`); `stopped_exit_vals_nonempty`.
- **Pushforward half**: `mkt_law_witness_shift` (markets shift by
  constants), `mkt_law_witness_mono_K`, `witness_value_le_vshift`,
  `witness_value_le_law_sup`, hypothesis-free form
  `witness_value_le_law_sup_ball` (any `T ≥ ball_v r k x0`, via
  `witness_value_le_ball_v` and Lemma 2.1's `expected_exit_time_bound`).
- **Paper-class value function**: `stopped_market` (= `mkt_law_witness`
  minus its path-law clause; `mkt_law_witness_iff`), `stopped_exit_vals`,
  `stopped_val_fn`; `stopped_val_fn_le_val_fn`;
  **`stopped_val_fn_le_law_sup`** (the per-witness domination lifted
  through `Sup_least`); transfers `stopped_val_fn_finite_bounded`,
  `stopped_val_fn_le_ball_v`, `stopped_val_fn_boundary_zero`.
- **Clause-(1) packaging**: `ball_v_le` (`ball_v r k x ≤ r²/(n−k)`),
  **`clause_one_law_level`** = `clause_one_usc` + `clause_one_dom` (§0).
- **Closure supports**: `confined_paths` (closed;
  `closedin_confined_paths`), `mkt_path_laws_confined`,
  `mkt_law_closure_confined(_AE)`.

### 2.6 The integrated identities on closure laws (all in `Section_2_Usc.thy`)

The two structural facts a canonical market would carry out of a limit law
— proved from members and passed through weak limits, then upgraded from
continuous tests to the full past σ-algebra:

- **Clamp toolkit**: `rclamp` with `rclamp_bound/rclamp_id/rclamp_cont`;
  `mkt_law_witness_bound` (confinement makes the clamp invisible on
  members); continuity plumbing `martingale_test_functional_cont`,
  `past_test_functional_cont`, `covariation_test_functional_cont`.
- **Market-level cores**: `martingale_bounded_test` (cond-exp pull-out:
  `Z` `F s`-measurable, `Y` martingale ⟹ `E[Z·Y_t] = E[Z·Y_s]`);
  `witness_compensator_increment_bounds` (`0 ≤ ΔA_i ≤ L(t−s)` a.e. from
  psd/eigen-ub before the horizon and `acov = 0` after);
  `coord_sq_bounded_test` (`E[Z(X_t$i−X_s$i)²] = E[Z·ΔA_i]` via the
  vanishing cross term).
- **Continuous tests**: `mkt_path_laws_martingale_test`,
  `mkt_law_closure_martingale_test` (= 0);
  `mkt_path_laws_covariation_test`, `mkt_law_closure_covariation_test`
  (≤ `L(t−s)·∫h`), `covariation_test_nonneg`.
- **Measure-theoretic engines** (generic, metric-space level):
  `metric_measure_eqI_bounded_cts` — finite Borel measures agreeing on
  bounded continuous functions are EQUAL (constant-sequence Portmanteau
  both ways + closed-set generator `sets_borel_of_closed`);
  `metric_measure_mono_bounded_cts` — one-sided domination on continuous
  `[0,1]` tests gives domination on ALL Borel sets (Urysohn sandwich
  `Urysohn_lemma_uniform` + shrinking neighbourhoods + continuity from
  above for closed sets; `finite_measure.inner_regular'` from AFP
  Riesz_Representation for the extension — one-sided bounds do NOT extend
  from a generator by Dynkin, the regularity detour is essential).
- **Event-level identities** (via pos/neg-part densities pushed through
  the restriction map): `mkt_law_closure_martingale_event`,
  `mkt_law_closure_covariation_event`, and for closed `K` the UNCLAMPED
  forms `mkt_law_closure_increment_event` (= 0) and
  `mkt_law_closure_sq_increment_event` (≤ `L(t−s)·Λ(B)`-form): under any
  closure law the canonical process is a martingale w.r.t. its natural
  filtration whose squared coordinate increments grow conditionally at
  most `L(t−s)`.

---

## 3. OPEN WORK ITEMS

### NC. The canonical market — "the closure adds no value" (clause (1) gap)

**AUTHOR-FIDELITY DECISION (user, 2026-08-04): formalize PRECISELY the
paper's result.** The former item 4 (restating clause (1) at law level)
is OFF THE TABLE as a final target: `clause_one_law_level` stays as a
proven stepping stone, but Theorem 1.1's clause (1) must be delivered
for the paper's own value function `v(x) = sup_{P ∈ P_x} P-essinf τ_K`
(faithful rendering: `stopped_val_fn` — see §0). Proof TECHNIQUE
remains free (e.g. the weak DPP may replace LR's measurable selection),
but every clause STATEMENT must match the paper. Hence NC is now ON the
critical path.

**RE-SCOPED 2026-08-04 after reading the paper's own Lemma 2.3 proof
(arXiv:2512.17702 pp. 3–6) and LR's Section 2 (arXiv:2003.13611
pp. 9–11).**  The paper's actual argument needs NO Doléans measures,
NO Radon–Nikodym on products, and NO Skorokhod representation if we
substitute portmanteau (see NC-3).  Their class (1.7) on
`Ω = C([0,∞), ℝⁿ)`: X is a coordinate-process martingale from x with
`Π_m(d⟨X⟩/dt) ≥ m − k` (m = k+1..n) and `λ_(1)(d⟨X⟩/dt) ≤ L` a.e. —
i.e. `d⟨X⟩/dt ∈ S` for the COMPACT CONVEX
`S = {a ⪰ 0 : Π_m(a) ≥ m−k ∀m, λ_(1)(a) ≤ L}` (Lemma 2.1 = our
`Lemma_2_1_Exact` says S is the convex hull of the unconvexified
(1.4)-set).  Their Lemma 2.3 (closedness):
carry `⟨X⟩` along as a SECOND PATH COMPONENT; it is uniformly
Lipschitz (bounded by tr ≤ nL), so the pair laws are tight; in the
limit `(X∞, Y∞)`: X∞ and X∞X∞ᵀ − Y∞ martingales (Vitali + moments);
difference quotients `(Y∞(t)−Y∞(s))/(t−s) ∈ S` a.s. because averages
of S-valued densities lie in the closed convex S; then 1-d
a.e.-differentiability + FTC give `dY∞/dt ∈ S` a.e.

**PAPER READING COMPLETE (pp. 7–9 of 2512.17702, 2026-08-04):**
- **Prop 2.4** = usc of `v` + the DPP `(2.9): v(x) = sup_{P∈P_x}
  P-essinf(θ ∧ τ_K + v(X(θ))·1_{θ≤τ_K})`, attained; proof is "repeat
  LR Prop 2.2(ii),(iii) word by word" — Berge (HAVE:
  `usc_sup_over_compactin`) + Bertsekas–Shreve selection + the
  concatenation-by-kernel construction (LR p. 11, read).  This is the
  EXACT N5 target statement.
- **Definition 3.1/Lemma 3.1** (viscosity + envelopes): already
  formalized (`Lemma_3_1.thy`).
- **Example 3.1 for general n** (p. 9): `v(x) = max(r²−|x|²,0)/(n−k)`
  = `ball_v` ✓.  Upper bound (3.10): Itô + the trace lower bound —
  our `stopped_val_fn_le_ball_v` route.  Lower bound: the sphere
  process runs in the FIRST `n' = n−k+1` coordinates (relabeled so
  `x_{[n']} ≠ 0`), REMAINING COORDINATES CONSTANT; and `x = 0` is
  handled by COMPACTNESS (laws `P*_{x^m}` for `x^m → 0` have a
  convergent subsequence; the limit has `τ_K = r²/(n−k)` a.s.).
  ⇒ N4-DELTAS for the paper-faithful Example 3.1 at `n−k = 1`,
  arbitrary `n`: (i) embed the 2-d circle process
  (`Deterministic_Radius_Market`) into `n` coordinates with the rest
  constant (product/embedding of the witness — mechanical but real);
  (ii) the `x = 0` compactness argument (needs exactly the NC-2/3
  closedness machinery).  Our `stopped_val_fn_ball_eq_2d` is the
  `n = 2` instance.

**NC STATUS TABLE (2026-08-05).  NC IS *NOT* DONE**: the five
sub-items below are individually complete or nearly so, but the
HEADLINE of NC — "the closure adds no value", i.e. the identification
of `stopped_val_fn` with the class supremum — is NOT proved, and one
genuine obstruction to it was found today (see BLOCKER below).

| item | content | status |
|---|---|---|
| NC-1 | pair-law encoding of class (1.7) | **DONE** |
| NC-2 | pair compactness + tightness | **criterion DONE**, instantiation open |
| NC-3 | limit identities without Skorokhod | **engines DONE**, instantiation open |
| NC-4 | density recovery `dY/dt ∈ S` a.e. | **DONE** |
| NC-5 | value-side usc of the essinf | **DONE** |

`Paper_Class.thy` is PIDE-green (2,002 commands, `overall_status ok`).
In ROOT after `Exit_Semicontinuity`; imports `Path_Space`,
`Path_Tightness`, `Exit_Semicontinuity`, `Poincare_Separation` and
`Relative_Arbitrage_Comparison` (the last two deterministic-side, no
cycle).  What it carries:

- **NC-1.**  `type_synonym 'n pairpath = real ⇒ (real^'n) × (real^'n^'n)`
  — NOTE `real^'n × real^'n^'n` PARSES AS `real^('n × real)^'n^'n`,
  which is why the synonym exists.  `sconstraint k L = Pi_constraint k
  ∩ {a. eigen_ub a L}`, `outerp`, `paper_pair_class k L T x` (pair laws
  starting at `(x, 0)`, difference quotients of `Y` in `sconstraint`
  a.s., `X` and `outerp X − Y` martingales for the pair natural
  filtration), `paper_v` = Eq. (1.6) capped at `T`.
- **NC-2, deterministic half.**  `sconstraint_convex`,
  `closed_sconstraint` (via `closed_Pi_constraint`, resting on
  `Pi_proj_ge_iff`: on the psd cone `c ≤ Pi_proj a m` is EXACTLY the
  family of linear inequalities `c ≤ trace (a ** P)` over rank-`m`
  projections), `sconstraint_norm_le` / `bounded_sconstraint` /
  `compact_sconstraint`.
- **NC-2, tightness.**  A Lipschitz bound IS a Hölder-`ga` bound on a
  bounded horizon (`lipschitz_imp_holder_bound`), so the two component
  moduli add through `norm_Pair_le` into ONE Hölder ball of the PRODUCT
  type (`pair_holder_of_components`) — and
  `Path_Space.compactin_path_holder_ball` applies VERBATIM at the pair
  type (`compactin_pair_holder_ball`), since products of
  `polish_space`/`real_normed_vector`/`heine_borel` are again such.
  Packaged: `tight_on_set_pair_holder_charge`,
  `pair_holder_charge_split`.  NO matrix-valued Kolmogorov criterion is
  needed.
- **NC-3.**  `Exit_Semicontinuity` also exports the CLOSED half of the
  path-space portmanteau (`weak_conv_closed_limsup`,
  `weak_conv_closed_full_mass`).  On top:
  `continuous_map_diffquot`, `closedin_diffquot_constraint`,
  `diffquot_constraint_weak_limit` (the Skorokhod replacement), and
  `diffquot_all_of_rational` (rationals → all real `s < t`, since
  portmanteau only gives one closed set per pair).  For the martingale
  identities — integrals of CONTINUOUS but UNBOUNDED functionals —
  `unif_integrable_of_L2_bound` + `weak_conv_integral_of_L2_bound` feed
  `Path_Tightness.weak_conv_on_integral_unif_integrable`.
- **NC-4 (complete).**  `diffquot_lipschitz`,
  `diffquot_deriv_in_constraint`, `diffquot_density_ae`.  Library calls:
  `Lipschitz_imp_has_bounded_variation`, `Lebesgue_differentiation_thm`.
  The step once feared to be the hard analytic core is a library call.
- **Class-level forms.**  `paper_pair_class_lipschitz_ae` (the
  `Y`-event of the tightness split has probability ONE) and
  `paper_pair_class_density_ae`.

- **The Lemma 2.1 step (needed by the bridge either way).**
  `average_in_closed_convex`: the average of a density taking values in
  a CLOSED CONVEX set again lies in that set — proved by separation
  (`separating_hyperplane_closed_point`, then `integral_inner_left` to
  pull the functional under the integral).  The average IS the
  difference quotient of `Y t = ∫₀ᵗ a`, so this is the mathematical
  heart of the covariation condition.  Specialised by
  `suff_volatile_cap_in_sconstraint` (via the EASY inclusion
  `lemma_2_1_easy`; the hard `lemma_2_1_exact` is not needed for this
  direction) and `diffquot_of_density_in_sconstraint`.

- **The continuation value exists.**  `mat_1_in_sconstraint`: under
  the paper's standing `L ≥ 1` (Theorem 1.1) the IDENTITY matrix is
  admissible — `Π⇩m(I) = m ≥ m − k` and `λ⇩(⇩1⇩)(I) = 1 ≤ L` — with
  `psd_mat_1`, `Pi_proj_mat_1`, `sconstraint_nonempty`.  This is the
  matrix the faithful bridge continues a stopped witness with; `L ≥ 1`
  is exactly what makes it available.

- **The continuation construction (the faithful bridge's volatility
  side) — DONE.**  `acont a tv s = (if s ≤ tv then a s else mat 1)`,
  with `acont_in_sconstraint` (S-valued for EVERY `s ≥ 0`: before `tv`
  by `suff_volatile_cap_in_sconstraint`, after `tv` by
  `mat_1_in_sconstraint` — this is where `L ≥ 1` is used) and
  `diffquot_of_continued_density` (hence every difference quotient of
  the continued running covariation lies in `S`, for all `0 ≤ s < t`
  with NO stopping caveat, exactly as (1.7) demands).

- **The running covariation, packaged.**  `Yint a t =
  set_lebesgue_integral lborel {0..t} a`, with `Yint_0` (starts at `0`),
  `Yint_increment` (`Yint a t − Yint a s = ∫_{s..t} a`, via
  `set_integral_Un_AE` — the AE-disjoint union rule avoids the
  `{s<..t}` measurability detour, since `{0..s}` and `{s..t}` overlap
  only in the null set `{s}`) and `Yint_diffquot_in_sconstraint`.
  **The volatility side of the faithful bridge is COMPLETE**: from a
  witness density one now gets a `Y` starting at `0` whose difference
  quotients lie in `S` for every `0 ≤ s < t`, i.e. the covariation half
  of `paper_pair_class` verbatim.

**THE WITNESS/CLASS MISMATCH — RESOLVED FROM THE SOURCE 2026-08-05.**
Re-read of arXiv:2512.17702 p. 3, definitions (1.6)–(1.8), settles it:
`P_x` is the set of laws on `Ω := C([0,∞), ℝⁿ)` (Borel σ-algebra for the
topology of LOCALLY UNIFORM CONVERGENCE) under which the coordinate
process `X` is a martingale from `x` and BOTH constraints of (1.7) hold
"a.e. `t ≥ 0`", almost surely.  Only THEN, separately, does (1.8) define
`τ_K := inf{t ≥ 0 : X(t) ∉ K}`.

CONSEQUENCES, and they are decisions, not options:

1. **THE AUTHORS DO NOT STOP THE PROCESS.**  The constraint holds for
   ALL time; `τ_K` is merely a path functional defined after the class.
   There is no stopped member of `P_x`.  Our `stopped_market` locale is
   OUR technical device — a stopped witness is NOT an element of the
   paper's class, which is exactly why `Y t = ∫₀ᵗ acov` fails to land in
   `paper_pair_class` (`acov = 0` after `tau`, and `0 ∉ sconstraint k L`
   for `k < n`).  The faithful bridge therefore CONTINUES each witness
   past `tau` with any `S`-admissible volatility.  This is legitimate
   and changes nothing: by (1.8) `τ_K` depends only on the path up to
   the first exit from `K`, so continuing after the exit leaves it
   untouched.  DO NOT instead weaken `paper_pair_class` to constrain
   only up to the exit time — that would be a different class from the
   paper's.
2. **`paper_pair_class` is right in substance**: it constrains the
   difference quotients on the whole of `[0,T]` with no reference to
   stopping.  Keep it that way.
3. **The horizon cap is OURS — PATH-LEVEL INVISIBILITY NOW PROVED.**
   The paper works on `C([0,∞), ℝⁿ)` with locally uniform convergence;
   we cap at `T`.  `Exit_Semicontinuity` now carries `pexit_mono_T`
   (the capped exit is monotone in the horizon) and
   `pexit_stable_above_T` (once a path exits strictly before `T`,
   raising the horizon does not move its value at all), AND the
   law-level `ess_inf_time_cong_AE` / `ess_inf_pexit_cap_invisible`:
   if the exit is a.s. before `T` then every `T' ≥ T` gives the SAME
   essential infimum.  **The cap-invisibility obligation is DISCHARGED**
   at both levels; all that a caller must supply is that `T` exceeds
   the uniform value bound `r²/(n−k)` (repo: `ball_v_le`), which makes
   the exit a.s. before `T`.
4. The constraint is on `d⟨X_i,X_j⟩/dt`, i.e. the DENSITY must exist
   a.e. — which is why carrying `⟨X⟩` as a Lipschitz second component
   and recovering the density by Lebesgue differentiation (NC-4) is the
   faithful encoding, not a convenience.

STILL OPEN in NC-2/3: instantiating the X-side
estimate at the pair laws (`path_law_holder_ball_bound_vec` into
`pair_holder_charge_split` and `tight_on_set_pair_holder_charge`), and
instantiating `weak_conv_integral_of_L2_bound` with the class's own
second-moment bound (§2.6 `martingale_bounded_test` /
`coord_sq_bounded_test` supply the identities on members).  Also still
recorded: cap-invisibility for large `T` (Lemma 1.9/(3.10)).

Faithful decomposition (statuses of ingredients in brackets):

1. **Pair-law encoding of (1.7).**  Operational reading (equivalent to
   (1.7) by compensator uniqueness): `P ∈ P_x` iff X is a martingale
   from x and THERE EXISTS an adapted process Y with Y 0 = 0,
   t ↦ Y t ω Lipschitz with difference quotients in S, and
   `X Xᵀ − Y` a martingale.  Define the paper's `P_x` this way on path
   space; bridge to `stopped_market` witnesses (their Y := ∫₀ acov).
   [`Lemma_2_1_Exact` DONE; martingale/covariation machinery §2.6
   DONE; matrix-valued paths need a second component type — the
   `mkt_path_laws` sample-type pin must be generalized or the pair
   packed into `real^('n × 'n + 'n)`-style coordinates.]
2. **Pair tightness.**  X-side: DONE (4th-moment → Kolmogorov →
   Arzelà–Ascoli, `Path_Tightness_Market`).  Y-side: deterministic
   Lipschitz modulus — Arzelà–Ascoli directly; product tightness.
   [Moderate; reuses `Path_Tightness`.]
3. **Limit identities WITHOUT Skorokhod.**  The paper uses Skorokhod's
   representation (NOT in the AFP); substitute our proven technique:
   integrated identities against bounded continuous past functionals
   pass through weak limits, then monotone-class to events (§2.6
   engines `metric_measure_eqI_bounded_cts` /
   `metric_measure_mono_bounded_cts`).  The difference-quotient
   constraint is CLOSED-SET portmanteau: for fixed rational s < t,
   `{(x-path, y-path): (y(t)−y(s))/(t−s) ∈ S}` is closed (S closed,
   evaluation continuous), so the limit law gives it mass 1; then all
   real s < t by path continuity.  [Engines DONE; applications new.]
4. **Density recovery = library call.**  Lipschitz ⇒ BV ⇒ a.e.
   differentiable is `HOL-Analysis.Lebesgue_Differentiation`
   (`Lebesgue_differentiation_thm_open`, real ⇒ euclidean_space —
   covers matrix values componentwise); derivative ∈ S a.e. since the
   difference quotients are and S is closed; FTC for Lipschitz
   (Y t − Y s = ∫ Y′) to recover the compensator form — check
   `Henstock`/`Equivalence_Lebesgue_Henstock_Integration` for the AC
   FTC, else derive from BV + a.e. derivative + dominated convergence.
   [KEY INGREDIENT EXISTS — this was believed the "hard analytic
   core"; it is not.]
5. **Value side (LR Lemma 2.1 trick) — DONE 2026-08-05 (commit
   `48d176f`), the whole of `Exit_Semicontinuity.thy` is PIDE-green
   (2,245 commands).**  Theory in ROOT after `Section_2_Usc`; imports
   only `Path_Space` + `Exit_Time` + `Value_Function`, so its cone is
   small.  What it exports, in dependency order:
   - `pexit T K = etime T (−K) (λr g. g r)` — the capped exit time read
     off a PATH; `pexit_le_T`, `pexit_nonneg`, `pexit_less_iff`.
   - `pexit_sublevel_open` — strict sublevels are open in
     `mtopology_of (path_metric T)` (witness time in the open
     complement + `continuous_map_path_eval`); `pexit_measurable`.
   - L1 `ess_inf_time_le_laplace` (+ `exp_neg_time_integrable`,
     `exp_neg_time_integral_lower`): `essinf τ ≤ −(1/λ) ln E[e^{−λτ}]`.
   - L2 `ess_inf_time_eq_laplace_inf`: `essinf τ = INF_{λ>0} f_λ`.
   - L3a `pstep` + `pstep_sandwich`: the uniform-grid telescoping step
     minorant `ψ_N = e^{−lT} + Σ_{j=1}^{N−1}(e^{−l s_j} − e^{−l s_{j+1}})
     ·1_{pexit < s_j}` with `ψ_N ≤ e^{−l·pexit} ≤ ψ_N + (1 − e^{−lT/N})`.
   - L3b `pstep_integral`, `weak_conv_open_liminf` (open-set portmanteau
     liminf along `weak_conv_on`), `weak_conv_total_mass`,
     `pstep_integral_liminf`, `pstep_integrable`.
   - L3 `exp_pexit_integral_liminf` — the squeeze `N → ∞`:
     `liminf_i ∫e^{−l·pexit} dΛ_i ≥ ∫e^{−l·pexit} dΛ`.
   - **CROWN `ess_inf_pexit_usc`**: for `0 < T`, `closed K`, probability
     laws with `weak_conv_on Λi Λ sequentially (mtopology_of
     (path_metric T))`,
     `Limsup_i (ess_inf_time (Λi i) (pexit T K)) ≤ ess_inf_time Λ
     (pexit T K)`.
   This is the value-side semicontinuity Prop 2.4 and the DPP consume;
   it replaces the `vshift` route entirely.
   TRAPS worth keeping (all cost real time here): state EVERY lemma
   about a time functional with `fixes tau :: "'a ⇒ real"` — without it
   τ generalizes to a Banach algebra and every real-specific rule fails
   to APPLY with no type error; unqualified `integrable_const`
   resolves to Henstock's `integrable_on` lemma — the Bochner fact is
   `finite_measure.integrable_const`, so either interpret
   `finite_measure`/`prob_space` first or pass `[OF fm]` explicitly;
   `ennreal_le_epsilon` carries a `y < top` premise the block must
   `assume`; never put `ennreal_plus[symmetric]` in a simpset (loops);
   nn-integrals need the `⇧+` sup-block (a raw superscript-plus is a
   lexical error through the MCP encoder); `LeastI_ex` not
   `LeastI[of]`; `sum.mono_neutral_cong_right` not `sum.inter_filter`;
   the ∀f clause of `weak_conv_on_def` needs MANUAL instantiation at
   `f = 1` (auto rewrites `∫1` to a measure first); `⇢` already carries
   `sequentially`; chain `<`/`≤` with `by order` or an explicit
   `rule less_le_trans[OF _ …]`.
Do NOT believe shortcuts through usc of `vshift` in the law argument:
usc gives `vshift(Λ) ≥ limsup vshift(Qₘ)` — the WRONG direction.

### N4. Example 3.1 / clause (3) general (RQ-C)

Eq. (3.11): `dX = a(X)^{1/2} dW`, `a(y) = I − yyᵀ/|y|²`, deterministic
radius `|X(t)|² = |x|² + (n−k)t`, hence `essinf τ = (r²−|x|²)/(n−k) > 0`.

**The cheap route for `n − k = 1` — falsification POSITIVE (2026-08-04).**
For `x ≠ 0` in the plane (prototype `n = 2`, `k = 1`):

    X_t = √(|x|² + t) · (cos(W_{c(t)} + φ₀), sin(W_{c(t)} + φ₀)),
    c(t) = ln(1 + t/|x|²),  (cos φ₀, sin φ₀) = x/|x|,

with NO SDE theory: martingale and compensated-square identities follow
from Gaussian conditional trigonometric expectations
(`E[cos(a·W_{c(t)} + b) | F_{c(s)}] = cos(a·W_{c(s)} + b)·e^{−a²(c(t)−c(s))/2}`;
`R(t)e^{−c(t)/2} = |x|` is constant, so the drift cancels). The covariance
is `a(X) = I − XXᵀ/|X|²` (trace 1), and with the constant horizon
`τ ≡ r² − |x|²` the market lies in the stopped class with
`ess_inf_time = ennreal (ball_v r 1 x)` — with `stopped_val_fn_le_ball_v`
this gives `stopped_val_fn = ball_v` at `0 < |x| ≤ r` for `k = n − 1`.
General `n − k ≥ 2` needs spherical Brownian motion (embed the
construction in an `(n−k+1)`-dim coordinate subspace) — that part stays on
the discrete route (`Random_Walk_Market.thy`,
`Relative_Arbitrage_Discrete.thy`,
`Path_Tightness.projective_limit_of_consistent_path_laws`).

Brick status (new theory `Deterministic_Radius_Market.thy`, in ROOT;
bricks 1–2b PIDE-scratch-verified, awaiting batch cross-check):

1. **DONE** `bm_increment_distr` — coordinate increment of the product
   model `= gauss_measure (t−s)` (`bm_paths_component` +
   `wiener_pre_increment`).
2. **DONE** `char_gauss_measure` — `char (gauss_measure v) a =
   exp(−a²v/2)` (change of variables to `std_normal_distribution`,
   `char_std_normal_distribution`).
   **DONE** `gauss_measure_cos` / `gauss_measure_sin` (Re/Im ∘ char via
   `integral_Re/Im` + `prob_space.integrable_iexp`, `iexp → cis`).
3. **DONE** `bm_increment_has_cond_exp` — for bounded measurable `g`,
   `has_cond_exp bm_paths (natural_filtration bm_paths 0 (bmX x0) s)
   (λω. g (ω i t − ω i s)) (λω. ∫ y. g y ∂gauss_measure (t−s))`
   (`has_cond_expI'` + `indep_var_lebesgue_integral` over
   `bm_indicator_increment_indep_var`); AE form
   `bm_increment_cond_exp_AE`; the generalized independence
   `bm_past_increment_indep_var` (any past-measurable `Z`, the
   indicator proof verbatim) and the product factorization
   `bm_past_increment_cond_exp`
   (`cond_exp (Z·g(Δ)) =AE Z·∫g dgauss`); and the cosine instance
   **DONE**: `bm_cos_cond_exp` —
   `E[cos(a·ω_t+b)|F_s] =AE cos(a·ω_s+b)·e^{−a²(t−s)/2}` (angle
   addition + `cond_exp_diff` + the product factorization +
   `gauss_measure_cos/sin`).  A `bm_sin_cond_exp` twin (same proof with
   `sin_add`) will be needed for the second coordinate — write it when
   brick 4 consumes it.  The Gaussian toolkit is COMPLETE.
4. The process.  Design points settled 2026-08-04:
   - the sine twin `bm_sin_cond_exp` is DONE (commit d02f134);
   - parametrize by `q > 0` (the squared start radius) and a phase `φ`,
     NOT by `x0` — instantiate at the end via `sincos_total`-style polar
     decomposition (`∃φ. x0 $ 1 = |x0| cos φ ∧ x0 $ 2 = |x0| sin φ`);
   - `X t ω = √(q+t) ·⇩R (χ j. if j = 1 then cos (W (c t) ω + φ)
     else sin (W (c t) ω + φ))` on the 2-dim product model, driven by
     ONE coordinate; `c t = ln (1 + t/q)`; filtration `G t := F (c t)`
     (deterministic increasing time change of the natural filtration);
   - martingale property: `E[X_t | G_s] = R(t)e^{−(c(t)−c(s))/2}·(…)`
     and `R(t)e^{−c(t)/2} = √q` is constant — from
     `bm_cos_cond_exp`/`bm_sin_cond_exp` at `a = 1`,
     `s ↦ c(s), t ↦ c(t)`;
   - the locale demands POINTWISE path continuity, so the process must
     be built on the CONTINUOUS modification `cbmX` (its coordinate).
     TRANSFER INTERFACE CONFIRMED (2026-08-04):
     `Modification_Transfer.set_integral_zero_transfer` moves
     "∫_B D dM = 0 for all B in the natural filtration of X at s" to
     the natural filtration of any modification X', given AE-equality
     of the D's and of the processes on `{0..s}`.  So: state
     `bm_cos/sin_cond_exp` as centered set-integral identities
     (D := cos(a·W_t+b) − cos(a·W_s+b)e^{−a²(t−s)/2}), transfer, and
     re-package as `has_cond_exp` on the cbmX side via `has_cond_expI'`.
     ANALYTIC LAYER COMPLETE (commits …, 1c83b51, a7c8763):
     `bm_cos/sin_set_integral`, `cbm_cos/sin_set_integral`, and the
     repackaged **`cbm_cos_cond_exp` / `cbm_sin_cond_exp`** —
     `E[cos/sin(a·Bcont_t(ω i)+b) | F^cbmX_s] =
      cos/sin(a·Bcont_s(ω i)+b)·e^{−a²(t−s)/2}` AE.  At `a = 1` these
     give the martingale property (with `R(t)e^{−c(t)/2} = √q`), at
     `a = 2` the `coord_Z` compensator identities via double angle
     (`cos² u = (1+cos 2u)/2`, `sin² u = (1−cos 2u)/2`,
     `sin u cos u = (sin 2u)/2`).  THE PROCESS IS DEFINED AND ITS FIRST
     COMPONENT IS A MARTINGALE (commits 7cf4aef, a6015de):
     `drc`/`drR` with `drc_cont`, `drc_(strict_)mono` (via
     `ln_le/less_cancel_iff` — do NOT try `ln_mono`, wrong name), the
     crown constancy `drR_decay: drR q t·e^{−(c_t−c_s)/2} = drR q s`
     (via `exp_neg_ln_half` and `frac_eq_eq` cross-multiplication —
     plain `field_simps` explodes); `drW u ω = Bcont u (ω 1)`;
     `drX q φ t ω` as scripted; `drX_norm` (deterministic radius,
     opaque-atom trick for `cos²+sin²`); and
     **`martingale_drX_cos`**: `t ↦ drR q t · cos(drW (drc q t) ω + φ)`
     is a martingale w.r.t.
     `G t = natural_filtration bm_paths 0 (cbmX 0) (drc q t)`.
     Proof-shape notes for the next agent (each cost a round-trip):
     the filtration axioms of `adapted_process` include the
     `filtered_measure` clauses — discharge sets-mono with
     `dest: Gmono[THEN subsetD]`, not `intro: Gmono`;
     `cbm_cos_cond_exp` instantiates by stating the specialized `have`
     with literal `1 *` and `(1::real)⇧2` and closing `by (rule …)`
     then `simp` (the `where`-attribute mysteriously fails with
     "No such variable ?x"); instantiate `drR_decay` by `OF q ij(1)
     ij(2)` (passing `drc`-composed nonneg facts silently instantiates
     `s := drc q i` — WRONG); the final pointwise step is
     `metis Ydecay mult.assoc mult.commute`.

   NEXT MICRO-STEPS in brick 4, in order (each a scratch-and-copy
   iteration; the martingale_drX_cos proof is the template):
   a. **DONE** (commit c6788ff) `martingale_drX_sin` — verbatim twin.
   b. **DONE** (commit c6788ff) `martingale_drX` — the VECTOR
      MARTINGALE of `drX q φ` via `martingale_vecI` + `exhaust_2`
      component split.
   c. **DONE** (commit e119204) `martingale_stopped_deterministic` —
      GENERIC: `martingale M F 0 Y ⟹ 0 ≤ T0 ⟹
      martingale M F 0 (λt. Y (min t T0))` (case split `T0 ≤ i` /
      `i < T0`; `cond_exp_F_meas` above the horizon, the base property
      at `min j T0` below — no optional stopping); instance
      `martingale_drXs` for `drX`.  Proof-shape notes: in the
      `martingale.intro` assembly, `unfold_locales` for the
      `adapted_process` part leaves ONLY the `F i`-adaptedness goal
      (plain-`M` measurability is auto-discharged — a leftover `show`
      for it fails to refine); lift adaptedness with
      `MY.subalgebra_F[OF m0, of i]` + `measurable_from_subalg`.
      Same commit: the two `stochastic_process` side conditions in
      `cbm_cos/sin_cond_exp` are now
      `by unfold_locales (auto intro: measurable_cbmX)` — the previous
      `(intro measurable_cbmX, simp)` had silently regressed in PIDE
      (failed `have`s still feed downstream, so the regression was
      invisible until a full-file `get_state`; CHECK `errors` on the
      WHOLE file after big edits, not just the new region).
   d. IN PROGRESS (2026-08-04).  Worked-out mathematical shape: with
      `Θ_t = W_{c(t)} + φ`, both coordinate obligations reduce to the
      SINGLE process `drN t := (q+t)·cos(2Θ_t) + ∫_0^t cos(2Θ_u) du`
      being a martingale — `coord_Z (drX q φ) (dra q φ) 1 = q/2 + drN/2`
      and for coordinate 2 `= q/2 − drN/2` (double angle
      `cos² = (1+cos 2u)/2`, `sin² = (1−cos 2u)/2`, and
      `R(t)² − t = q`); the stopped versions then follow from
      `martingale_stopped_deterministic` since
      `∫_0^t (stopped integrand) = ∫_0^{min t T0} (unstopped)`.
      The conditional-expectation computation:
      `E[cos 2Θ_t|G_s] = cos 2Θ_s·((q+s)/(q+t))²` (a = 2 decay), and
      `∫_s^t ((q+s)/(q+u))² du = (q+s) − (q+s)²/(q+t)` — the two terms
      cancel so `∫_B (drN_t − drN_s) dM = 0`.
      DONE so far (commit 8f889f7): the measure-theoretic engine —
      `borel_measurable_continuous_time_process` (continuous in t +
      measurable in ω ⇒ jointly measurable; dyadic discretization,
      `measurable_compose_countable'` + `borel_measurable_LIMSEQ_real`;
      searched HOL + AFP: no such lemma existed), corollary
      `borel_measurable_time_integral` (ω ↦ ∫_{a..b} f u ω du
      measurable), and `time_integral_swap_event` (bounded integrand:
      `∫_B ∫_{a..b} f du dM = ∫_{a..b} ∫_B f dM du` via
      `pair_sigma_finite.Fubini_integral` on `lborel ⨂⇩M M`).
      Proof-shape notes: pair measure is `⨂⇩M` = `\<Otimes>\<^sub>M`
      (CAPITAL Otimes — lowercase ⊗ is a lexical error); direct python
      edits to the scratch are NOT picked up by the PIDE buffer — go
      through the MCP `edit` tool; `emeasure M B < ∞` for a finite
      measure via `emeasure_eq_measure` (metis on
      `emeasure_finite`/`top.not_eq_extremum` fails);
      `integrable (case_prod F)` from the fst/snd form via
      `case_prod_beta'` (unprimed `case_prod_beta` does not rewrite).
      DONE (commits b10515b, d75bafe, 07e9c1d): the clamped
      double-angle process `drC2 q φ u ω = cos(2·drW(drc q (max u 0))ω
      + 2φ)` with continuity/measurability/adaptedness; the decay
      `drC2_set_integral_decay` (∫_B drC2_u = ((q+s)/(q+u))²·∫_B drC2_s
      for B in the filtration at s); `drc_exp_diff_sq`;
      `drN_compensator_integral` (FTC); `drN q φ t = (q+t)·drC2_t +
      ∫_0^t drC2_u du` with `drN_set_integral_identity` (T1 decay
      cancels against T3 Fubini compensator increment) and
      **`martingale_drN`**.  IMPORTANT WORKFLOW CHANGE (user request
      2026-08-04): after a PIDE restart wiped the scratch, development
      now happens DIRECTLY in `Deterministic_Radius_Market.thy` via the
      MCP edit tool (a restarted server has the current ROOT snapshot,
      so the theory loads by name; downstream Theorem_1_1 is not open
      in PIDE so edits don't trigger huge re-elaboration).  The theory
      is fully PIDE-green: 4537 commands, 0 failures.  This also
      surfaced and fixed silently-broken committed proofs
      (`drc_mono`/`drc_strict_mono` had stale `ln_mono?` placeholder
      text) — failed lemma-level proofs abort the LEMMA (undefined
      fact downstream), unlike failed `have`s inside proofs.
      Traps: `drC2_max` is a FUNCTION equality — needs `(intro ext)`
      before simp; `filtered_measure_def` clauses need
      `subalgebra_def` in the simp set; the `adapted_process` goal in
      the martingale assembly uses the exact drX_cos combination
      `(auto intro: drG_subalgebra drN_adapted[OF q] dest:
      Gmono[THEN subsetD])` — other combinations loop.
      (d) IS COMPLETE (commits b9d97fc, e0e9aa1): `dra q φ = vvᵀ`
      with `v = (sin Θ, −cos Θ)` (`dra_11/22` diagonal =
      sin²/cos²), compensators `dra_compensator_11/22 = t/2 ∓
      (∫drC2)/2`, coordinate identities `coord_Z_drX_1/2 = q/2 ±
      drN/2` (t ≥ 0), and **`martingale_coord_Z_drX`** — both
      compensated coordinate squares are martingales (manual assembly:
      identity-rewrite per fixed nonneg time; negative-time
      measurability from the empty compensator; cond_exp
      add/const/scaleR chain + drN property under eventually_elim).
      Traps: `d / 2 *⇩R x` parses as `d / (2 *⇩R x)` — parenthesize;
      in a `cases "i = 1"` True-branch simp rewrites `i` before an
      i-form rule LHS can match — instantiate component equations by
      hand via `fun_eq_iff drX_def True`; final linear identities
      close with `argo` (linarith balks); conditional trig rewrites
      die when simp first distributes `2*(x+φ)` — use `drC2_eq
      drW_def`.
      OLD SPEC (kept for reference): `coord_Z` for the stopped process with
      `acov j k t ω := (if t ≤ r² − q then …trig products at
      (drW (drc q t) ω + φ)… else 0)`; the compensated-square
      martingale property reduces, via `cos² u = (1 + cos 2u)/2` and
      the compensator integral `∫_s^t sin²/cos²`, to
      `cbm_cos_cond_exp/cbm_sin_cond_exp` at `a = 2` plus a
      deterministic ODE-style identity
      `d/dt [R(t)² cos²-part-expectation]` — work it out on paper
      first; the expected shape is
      `E[(drX_t $ 1)² − ∫_0^t sin²(...) du | G_s]
         = (drX_s $ 1)² − ∫_0^s sin²(...) du`
      via the DOUBLED-angle decay `e^{−2(c_t−c_s)}
      = ((q+s)/(q+t))²` and explicit integration of
      `u ↦ (q+u)⁻¹`-type integrands (all deterministic calculus).
   e. Locale membership (`sufficiently_volatile_market` at
      `k = 1, CARD = 2`, `K = cball 0 r`, `x0` from polar
      `sincos_total`, `tau ≡ r² − q`): eigen bounds for the projection
      matrix (`eigen_lb` at dim 1 via the tangent direction,
      `eigen_ub` with `L ≥ 1`); `stopped_market` side conditions are
      definitional (stopped, killed, bounded diag).
      ESSENTIALLY DONE (commits 1916b50, 8423cc5, 5eef1b8):
      **`deterministic_radius_sufficiently_volatile`** — for
      `0 < q ≤ r²`, `0 ≤ r`, `1 ≤ L`, the stopped pair
      `(drXs q φ (r²−q), dras q φ (r²−q))` with constant horizon,
      `K = cball 0 r`, start `√q·(cos φ, sin φ)` satisfies ALL
      clauses of `sufficiently_volatile_market` at `k=1, CARD=2`.
      Spectral layer: `drv` (unit tangent), `dra = drv drvᵀ`,
      `dra_psd`, `dra_eigen_lb` (span of the tangent, `dim_eq_0` +
      linarith — the `by simp` route loops on span-subset rewrites),
      `dra_eigen_ub` (Cauchy–Schwarz), `dra_trace = 1`.
      CROSS-THEORY CAVEAT: `stopped_market` is defined in
      `Section_2_Usc`, NOT in this theory's import closure — an
      undefined name in a shows-clause silently becomes a FREE
      variable (only symptom: "Undefined fact: stopped_market_def").
      The packaging must live in a theory importing BOTH
      `Section_2_Usc` and `Deterministic_Radius_Market` (natural
      place: `Theorem_1_1.thy`, together with (f)); the three extra
      clauses are exported as `drXs_stopped`, `dras_killed`,
      `dras_diag_time_integrable`.
      Other traps: `CARD(2) − 1` normalizes to `Suc 0` — instantiate
      `dra_eigen_lb[unfolded One_nat_def]`; don't put `trace_def` in
      a simpset where `dra_trace` (stated about `trace`) must fire;
      `if_weak_cong` blocks rewriting under unresolved if-branches —
      add `cong: if_cong`.
      History of the block: `drXs q φ T0 t = drX q φ (min t T0)`,
      `dras q φ T0 u = (if u ≤ T0 then dra q φ u else 0)`;
      `set_integral_stopped_split` (generic killed-compensator
      reduction), `dra_diag_drC2` (diagonal = `(1 ∓ drC2)/2`),
      `dra_diag_set_integrable`, `coord_Z_drXs_eq`, and
      **`martingale_coord_Z_drXs`** — the stopped pair's coord_Z
      obligations, via `martingale_stopped_deterministic`.  Both
      X-martingale (`martingale_drXs`) and coord_Z martingales for the
      stopped market are now in place; remaining for (e): the locale's
      pointwise/integrability clauses (X_start via `drX` at 0;
      X_in_K with `K = cball 0 r` from `drX_norm`; psd/eigen bounds of
      the rank-1 projection `dra`; trace integrability;
      stopped_sq_integrable; compensator_integrable; dynkin_quadratic;
      tau_stopping for constant tau — the event is `{}` or `space`;
      X_paths_cont from `Bcont_cont` composition) and the final
      `interpretation`/lemma stating membership.
   f. **DONE AND PIDE-VERIFIED** (commits 631cb8c, 8cee2a6):
      `Theorem_1_1.thy` now imports `Section_2_Usc` +
      `Deterministic_Radius_Market` (the only place both are in scope)
      and is green end to end: `ess_inf_time_const`,
      `deterministic_radius_stopped_market` (the `stopped_market`
      packaging), and the HEADLINE **`stopped_val_fn_ball_eq_2d`** —
      for `x :: real^2`, `0 < ¦x¦ ≤ r`, `1 ≤ L`:
      `stopped_val_fn 1 L (cball 0 r) x = ennreal (ball_v r 1 x)`.
      ≤ is `stopped_val_fn_le_ball_v`; ≥ exhibits the witness with
      `essinf τ = r² − ¦x¦²` (polar representation via
      `sincos_total_2pi`; membership in `stopped_exit_vals` by
      EXPLICIT `exI` where-pins — blast diverges on the 5-fold ∃;
      `power_mono` needs `[of 2]`; per-component vector equality via
      `exhaust_2` in a `for i` have).
      ITEM N4 (n − k = 1) IS COMPLETE.  General `n − k ≥ 2` (spherical
      BM) remains on the discrete route as noted above.

WORKFLOW for this item: develop each brick in a PIDE scratch importing
`Arbitrage.Brownian_Continuous` (fast iteration, no downstream
re-elaboration), then copy the verified text into
`Deterministic_Radius_Market.thy`. A freshly started PIDE snapshots ROOT
and cannot load the new theory — the user's batch build is the
cross-check for the copied file.

### N5. The weak DPP (RQ-B; ~1,500–3,000 lines, HIGH risk)

Bouchard–Touzi's weak DPP avoids measurable selection by replacing `v` with
test functions — exactly the form the viscosity proofs consume. Read BT09
and arXiv:1105.0745 against Definition 3.1's needs BEFORE formalising
anything: this is a stochastic-target problem with an essinf objective and
the fit is unverified. Unblocks clause (2) together with N4.

**READING DONE (2026-08-04; BT09 = SIAM J. Control Optim. 49(3)
948–962, fetched from ceremade.dauphine.fr/~bouchard/pdf/BT09.pdf,
pp. 948–955 read).** Structure of BT09: Mayer-form
`V(t,x) = sup_ν E[f(X_T)]`; assumptions A1 (controls/state
𝔽ᵗ-progressively measurable, independent of ℱ_t), A2 (causality),
A3 (concatenation stability at stopping times — implies A5,
bifurcation along an ℱ-partition), A4a/b (tower-compatibility of the
conditional reward at stopping times).  Theorem 3.5: (3.1)
`V ≤ sup_ν E[V*(θ_ν, X(θ_ν))]` (USC envelope; only the tower property
+ A4a) and (3.2) for every USC minorant `φ ≤ V` (with `J(·;ν)` LSC in
the initial condition): `V ≥ sup_ν E[φ(θ_ν, X(θ_ν))]`.  Measurable
selection is replaced by: ε-optimal control per point + LSC of J +
Lindelöf countable cover of half-open boxes `B(s,y;r) =
{(t',x'): t' ∈ (s−r,s], |x'−y| < r}` + countable pasting via A3/A5.

FIT ASSESSMENT for our Definition 3.1 (objective
`stopped_val_fn = Sup {essinf_M τ}`):
1. The objective is a SUP of ESSENTIAL INFIMA, not of expectations —
   BT09's reward calculus (tower property, dominated convergence in
   (3.2)'s proof) does NOT transfer verbatim.  The essinf analogue of
   the tower property is essinf-pasting:
   `essinf τ = θ + essinf(shifted τ)` under concatenation at a
   deterministic/stopping time θ — this needs the CLASS to be closed
   under (i) conditioning/shifting at stopping times and (ii)
   countable pasting along a past-measurable partition.
2. (ii) is the crux: pasting stopped_market witnesses into one
   measure = gluing via regular conditional distributions on the
   Polish path space.  INFRASTRUCTURE EXISTS: AFP `Disintegration`
   (`measure_disintegration`, built on Standard_Borel_Spaces — already
   a session dependency) gives disintegration of measures on standard
   Borel spaces; the path space is Polish (Path_Space.thy).  Still a
   large step (~2–4k lines): shift/concatenation operators on path
   measures + closure of `stopped_market` under both.
3. The ≤-half of the DPP (our Eq. (2.9) upper bound) needs only the
   shift/conditioning closure (BT09's A4a analogue) — substantially
   easier than the ≥-half, and may suffice for ONE of the two
   viscosity inequalities of clause (2) (check which one Definition
   3.1's supersolution proof consumes before building the ≥-half).
4. The Lindelöf-cover trick itself is formalizable (countable cover
   by rational boxes; Isabelle: `Lindelof_space` or direct second-
   countability) and is NOT the bottleneck.
RECOMMENDED ORDER: (a) shift operator on path laws + class closure
under conditioning (reusable from NC's canonical-market needs);
(b) the ≤-half of the essinf DPP; (c) assess which viscosity
inequality remains; only then (d) the pasting ≥-half via
Disintegration.

### Fallback

If NC's differentiation step and N4's spherical case both look infeasible,
the bounded alternative target is the rest of Section 4 (Theorem 4.2(b),
4.3, Prop 4.1 — 3,000–7,000 lines, reusing the Crandall–Ishii investment).

---

## 4. Working notes for the next agent

- **Verify with PIDE MCP, not batch builds** (user instruction; the user
  runs the batch build at the end). The loop is: edit →
  `get_progress`/`get_state`; `commands_failed = 0` at 100% IS
  verification. The first load after a server restart re-elaborates the
  whole graph (several minutes). If a theory sits in "queued for loading"
  forever, the server is wedged — ask the user for a restart. Treat any
  `still_running_possibly_nonterminating` flag as a stop condition, even
  at `timing_ms 1` (e.g. `of_real_mult[symmetric]` in simp loops —
  convert `iexp` to `cis` instead of reversing distribution rules).
- **Editing upstream theories re-elaborates everything downstream** —
  prototype in `create_scratch` files (imports like
  `Arbitrage.Brownian_Continuous` work) and copy verified text into the
  tree in one edit. New theories cannot be loaded by a running PIDE
  (ROOT snapshot); register them in ROOT and rely on the batch build.
- **Proof-engineering traps** (each cost a round-trip): eliminating a
  multi-`∃` whose conjuncts contain `∀`/`AE` with `obtain … by blast`
  diverges — keep set-comprehension bodies ATOMIC (`mkt_law_witness`) and
  do choice by iterated `SOME` + `someI_ex`; instantiate multi-parameter
  theorems with explicit `where`-pins (bare `OF` mangles function
  arguments by higher-order unification); when a lemma's conclusion is
  literally the goal, use `unfolding defs by (rule lemma[OF …])`;
  type-annotate every statement-level function variable AND every
  `obtain`ed variable when a clause is dropped (`σ :: nat ⇒ _`, Urysohn's
  `f :: 'a ⇒ real`) — otherwise they stay polymorphic and everything
  downstream type-fails; `auto` will not instantiate bounded quantifiers
  like `∀t∈{0..T}. f t ∈ K` mid-chain — project with `blast` first.
- The broader environment traps (dev Isabelle without `nlinarith`, simp
  preferring cancellation, PIDE desync symptoms and fixes, …) are in the
  agent memory file `isabelle-pide-mcp-environment`; read it before long
  proof work.
- `mkt_path_laws` pins the market sample type to `('m ⇒ real ⇒ real)` for
  the same reason `val_fn` does: HOL cannot quantify over sample-space
  types, and `bm_paths` lives there. Keep new market constructions on that
  type.
- Zero `sorry` across the session is an invariant; the last one
  (`Sup_Convolution.subdiff_nonempty`) was closed 2026-08-03 —
  `supporting_hyperplane_frontier` exists in this Isabelle
  (`HOL/Analysis/Starlike.thy`), despite an old note claiming otherwise.
