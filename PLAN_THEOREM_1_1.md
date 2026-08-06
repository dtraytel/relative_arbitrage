# Plan: reaching Theorem 1.1 of arXiv:2512.17702

**HANDOVER, 2026-08-05 (second session of the day).** This document is the
single source of truth for what is proved, what is open, and what to do
next. Everything referenced is PIDE-verified unless explicitly marked
otherwise; the user runs the batch build as the final cross-check. Read §0
for the clause-by-clause status, §1 for how the paper argues, §2 for the
machinery you may assume, §3 for the open items, and **§4 before touching
anything** — it lists the traps that have each cost a round-trip or a
server restart.

**Verified green as of this handover** (`get_progress`, `commands_failed
= 0` at 100%):

| theory | cmds | theory | cmds |
|---|---|---|---|
| `Relative_Arbitrage_Stochastic` | 531 | `Exit_Semicontinuity` | 2,676 |
| `Ito_Market` | 1,446 | `Paper_Class` | 2,496 |
| `Brownian_Continuous` | 952 | `Paper_Bridge` | 357 |
| `Deterministic_Radius_Market` | 6,100 | `Path_Tightness_Market` | 838 |
| `Theorem_1_1` | 369 | `Value_Function` | 724 |
| `Section_2_Usc` | 7,005 | | |

**THE TWO PENDING DISCHARGES ARE CONFIRMED.** The previous handover left
`Value_Function` and `Section_2_Usc` unverified because that session's PIDE
loader would not schedule the branch. Both loaded clean on the first
`get_progress` of this session — `Value_Function` 724, `Section_2_Usc`
7,005 (up from 6,995, the ten extra commands being the inherited
`acov_time_measurable` discharges). **The locale upgrade is fully verified
at all six discharge sites.** Nothing about it is open.

WORKFLOW (user instruction): develop DIRECTLY in the tree theory files
via the PIDE MCP `edit` tool; scratches are only for throwaway probes.
History and superseded scoping live in git
(`git log -p PLAN_THEOREM_1_1.md`) — do not resurrect them.

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
| (1) | regularity (usc) | **DONE in law-level form** — `clause_one_law_level`; for the PAPER's `v` the target is now usc of `Paper_Class.paper_v` = Eq. (1.6) directly, via Lemma 2.3 in the class + Berge, §3/NC and §4.5 |
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
| NC-2 | pair compactness + tightness | **criterion DONE**, instantiation open (and NOT mechanical — see below) |
| NC-3 | limit identities without Skorokhod | **engines DONE; the two CLOSED clauses (start, covariation) INSTANTIATED; the X-martingale clause carried to the limit in EVENT form (steps (i)–(iii))**; step (iv) and the second martingale clause open |

**⚠ THE CLASS DEFINITION WAS VACUOUS UNTIL 2026-08-05 (commit `080bd30`).**
Points of `mspace (path_metric T)` are EXTENSIONAL on `{0..T}`, so
`ω u = undefined` for `u > T`. The two martingale clauses of
`paper_pair_class` were quantified over ALL `u ≥ 0`, which therefore
compared `X_t` with the conditional expectation of the CONSTANT
`fst undefined` and forced the coordinate process to be a.s. constant;
together with the covariation clause (which excludes a vanishing `Y`,
since `0 ∉ sconstraint k L` for `k < n`) that makes the class EMPTY for
every `T > 0`, and every theorem about it vacuous. The clauses now stop
the process at `T` (`fst (ω (min t T))`, `outerp (fst (ω (min t T))) −
snd (ω (min t T))`), saying exactly what (1.7) says on `[0,T]` and
nothing beyond. The FILTRATION needs no cap — evaluations past `T` are
constant maps and generate nothing.

**LESSON, and it generalises:** on the CAPPED path space every statement
quantified over unbounded time is a trap. Before proving anything about a
new class of path laws, prove (or at least sanity-check) that it is
NONEMPTY — the Brownian pair law with `Y t = t · mat 1` is the obvious
witness and is still not formalised. That check would have caught this
immediately.
| NC-4 | density recovery `dY/dt ∈ S` a.e. | **DONE** |
| NC-5 | value-side usc of the essinf | **DONE** |

**NC-3, closed clauses — DONE 2026-08-05 (commit `9a4db3c`).** For a
weakly convergent sequence of class members the limit law satisfies both
clauses of (1.7) that are closed conditions on a single path:

- `paper_pair_class_prob` / `paper_pair_class_sets` / `space_of_path_sets`
  — projections out of the class definition (`space Q = mspace (path_metric
  T)`), used everywhere below.
- `closedin_start_point`, `paper_pair_class_start_full_mass`,
  **`paper_pair_class_start_limit`** — `AE ω. fst (ω 0) = x ∧ snd (ω 0) = 0`
  passes to the limit (evaluation at `0` continuous, `{(x,0)}` closed).
- `paper_pair_class_diffquot_full_mass` and the headline
  **`paper_pair_class_diffquot_limit`** — the covariation clause of (1.7)
  holds under the limit law for ALL real `0 ≤ s < t ≤ T`.  Portmanteau
  yields one closed set per RATIONAL pair (`diffquot_constraint_weak_limit`);
  `AE_ball_countable'` conjoins the countably many; and
  `diffquot_all_of_rational` — the paper's own closing "by continuity" step
  — extends to every real pair, using `mspace_path_metricD` for the path
  continuity.
- `paper_pair_class_Y_bounded_ae` (commit `2167fc2`) — `‖Y t‖ ≤ n·L·T` on
  `[0..T]` a.s., from `paper_pair_class_lipschitz_ae` plus `Y 0 = 0`.  No
  probabilistic input.  This is the step that will make `X` square
  integrable under a class law: the martingale clause gives integrability of
  `outerp X − Y`, and a bounded `Y` transfers it to `outerp X` — which is
  exactly the `L2` input `weak_conv_integral_of_L2_bound` wants for the
  martingale clauses.

- `paper_pair_class_eval_measurable` and **`paper_pair_class_sq_integrable`**
  (commit `c3434e8`) — path evaluation is `Q`-measurable, and
  `E[(X_t$i)²] < ∞` for `t ∈ [0..T]`.  The route matters: a class member is
  neither stopped nor confined, so square integrability CANNOT come from a
  uniform bound on `X`; it comes from the `outerp X − Y` martingale clause
  plus the bounded `Y`.

**NC-3, THE X-MARTINGALE CLAUSE THROUGH THE WEAK LIMIT — steps (i)–(iii)
DONE 2026-08-05** (commits `6502c11`, `754edd9`, `ac1ca9b`, `512a989`,
`99a0be1`; all in `Paper_Bridge.thy`, which is where the class and the
Section-2 law machinery are both in scope). The four-step route and where
it stands:

- **(i) the identity at a member** — `paper_pair_class_martingale_test`:
  `E[h(restrict ω {0..s})·(X_t$i − X_s$i)] = 0` for bounded Borel `h`, via
  `Section_2_Usc.martingale_bounded_test`. The enabling step is
  `restrict_measurable_natural_filtration`: the non-trivial inclusion
  `σ(restriction to [0,s]) ⊆ 𝔉_s` is EXACTLY what
  `Path_Space.pathify_measurable` proves — the restriction map IS the path
  map of the coordinate process on `{0..s}`, and that theorem reduces a
  ball of the path metric to countably many evaluation conditions. Also
  `martingale_bounded_linear_image` / `martingale_vec_nth` /
  `martingale_mat_nth` (Paper_Class): a bounded linear map carries a
  martingale to a martingale, proved through the set-integral
  characterisation so that no conditional expectation has to be moved.
- **(ii) through the weak limit** —
  `paper_pair_class_martingale_test_limit`. This is where the paper uses
  Skorokhod; we use `weak_conv_integral_of_L2_bound` fed by the class's
  uniform second moment. The integrand is continuous but UNBOUNDED (no
  clamp is available: the paper's processes are neither stopped nor
  confined), so all fifteen hypotheses are discharged from one input, the
  `L²` bound, in nn-integral form so that `weak_conv_on_nn_integral_le`
  carries it to the limit without presupposing anything there
  (`paper_pair_class_sq_nn_bound`, `pair_law_limit_sq_nn_bound`,
  `pair_test_integrable`, `pair_test_sq_bound`, plus the generic
  `clamp_integrable` / `tail_integrable`).
- **(iii) continuous tests → past events** —
  `paper_pair_class_martingale_event_limit`: the same identity against
  `1_B(restrict ω {0..s})` for EVERY Borel past event `B`. Positive and
  negative parts of the increment are pushed through the restriction map
  as densities; step (ii) says the two image measures integrate every
  bounded continuous function alike, and
  `Section_2_Usc.metric_measure_eqI_bounded_cts` makes them EQUAL. Wrinkle
  handled: that engine supplies tests bounded only on the TOPSPACE while
  step (ii) wants a global bound — compose with `Section_2_Usc.rclamp`.
  Unlike the confined market laws the density is only INTEGRABLE, not
  bounded, so finiteness of the pushforwards comes from
  `nn_integral_eq_integral`.
- **(iv) reassemble — OPEN.** Feed step (iii) into
  `sigma_finite_filtered_measure.martingale_of_set_integral_eq`. Two
  obligations remain: the σ-algebra step `𝔉_s ⊆ σ(restriction)` (the
  converse of the inclusion already proved — easy direction: for `u ≤ s`,
  `ω u = ev_u (restrict ω {0..s})` and `ev_u` is continuous on the
  `s`-path space, so the preimage σ-algebra contains all generators), and
  the locale obligations (`stochastic_process` for the coordinate process
  — note evaluations past `T` are constant on the space, so measurable —
  then `finite_filtered_measure_natural_filtration`).

**(iv) DONE 2026-08-05 (commit `210cb0a`)** —
`paper_pair_class_coord_martingale_limit` and its vector form
`paper_pair_class_X_martingale_limit`: under the limit law the coordinate
process IS a martingale for the natural filtration. The enabling lemma is
`natural_filtration_eq_restrict_vimage`, the converse inclusion
`𝔉_s ⊆ σ(restriction)` — easy, since for `u ≤ s` the evaluation factors as
`ev_u ∘ restrict` and `ev_u` is continuous on the `s`-path space
(AFP `measurable_family_iff_sets` + `sets_vimage_algebra2`). Also
`pair_law_eval_measurable` (evaluations past the horizon are the CONSTANT
`undefined` on the capped space, hence measurable), `fst_coord_borel`, and
`Ito_Market.martingale_vecI` to assemble the vector martingale from its
coordinates. **`paper_pair_class_limit_three_clauses`** states the
resulting position of Lemma 2.3 explicitly and machine-checked: the limit
satisfies the START, COVARIATION and X-MARTINGALE clauses.

Trap: `stochastic_process` is shadowed by Kolmogorov_Chentsov's homonym
(different arity); write `Stochastic_Process.stochastic_process`, and do
not break a qualified name across lines at the dot.

**THE SECOND MARTINGALE CLAUSE IS BLOCKED ON A FOURTH MOMENT, and it is
the SAME obstruction as NC-2's tightness.** Carrying
`outerp X − Y` through the weak limit needs an `L²` bound on
`(outerp X)$i$j = X_i X_j`, i.e. a uniform FOURTH-moment bound on `X`
under the class. The repo's supplier
`Increment_Moments.fourth_moment_bound_bounded` assumes a uniform sup
bound on the process, true for confined market witnesses and false for
class members.

**Do NOT try to generalise that theorem — the sup bound is structural, not
incidental** (checked 2026-08-05). It is used twice: to get
`integrable M (X u ^ 4)` (that use IS incidental), and inside
`remainder_tendsto_zero`, whose whole estimate runs through the constant
`B = 4R²C(T − s) + C²(T − s)²` and `sum_sq_squared_bound`. Replacing `R`
by an `L⁴` hypothesis means redoing the remainder argument with a
different domination.

**THE ROUTE THAT AVOIDS ALL OF THAT IS LOCALIZATION, and it needs no BDG
and no change to `Increment_Moments`.** Apply the EXISTING bounded theorem
to the STOPPED process, which is bounded by construction:

1. `τ_R ω = inf {t ∈ [0,T]. R ≤ ¦X_t ω¦}` (capped at `T`) — a stopping
   time for the natural filtration, since `X` is continuous and adapted.
2. `X^{τ_R}_t = X_{t ∧ τ_R}` satisfies `¦X^{τ_R}_t¦ ≤ max (¦x$i¦) R` by
   path continuity, so `fourth_moment_bound_bounded` applies to it with
   `R' = max (¦x$i¦) R` and rate `C = L`, giving
   `E[(X_{T∧τ_R} − X_{s∧τ_R})⁴] ≤ 8L²(T − s)²` UNIFORMLY in `R`.
   Inputs: the stopped process is a martingale, and its compensator is
   `A^{τ_R}` with the same rate — both are optional stopping, for which the
   repo has `Optional_Sampling.thy` and
   `Deterministic_Radius_Market.martingale_stopped_deterministic`.
3. PATHWISE, `ω` is continuous on the compact `[0,T]`, so
   `sup_{[0,T]} ¦X¦ < ∞` and `τ_R > T` for all large `R` — hence
   `(X_{T∧τ_R} − X_{s∧τ_R})⁴ → (X_T − X_s)⁴` pointwise.
4. Fatou gives `E[(X_T − X_s)⁴] ≤ 8L²(T − s)²`, and with the start
   condition the absolute fourth moment follows.

That single estimate unblocks BOTH the second martingale clause of
Lemma 2.3 AND NC-2's tightness (`path_law_holder_ball_bound_vec`); they
stand or fall together, so build it once. Estimated a few hundred lines,
the bulk being optional stopping at the path-space level.

Proof-shape notes: chaining a non-AE fact into `eventually_elim` fails with
"RSN: no unifiers" — use `by (rule eventually_mono) (use … in auto)`;
`bounded_linear.integrable` does not exist — the name is
`integrable_bounded_linear`; `norm_nth_le` is AMBIGUOUS (two lemmas, the
`Topology_Euclidean_Space` one about `x ∙ i` shadows) — qualify it
`Finite_Cartesian_Product.norm_nth_le`; `borel_measurable_nth` is only the
real-valued instance `real^'n ⇒ real`, so the matrix row map
`real^'n^'n ⇒ real^'n` needs `borel_measurable_continuous_onI` +
`linear_continuous_on[OF bounded_linear_vec_nth]`;
`AE_ball_countable'` (primed) is the intro form, `AE_ball_countable` is the
`iff`; `prob_space.prob_Collect_eq_1` converts full mass ↔ AE and wants the
set written as `{ω ∈ space Q. …}`, so `unfolding sp` where
`sp : space Q = mspace …`.

`Paper_Class.thy` is PIDE-green (2,496 commands, `overall_status ok`).
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

**SESSION WEDGED 2026-08-05 — READ BEFORE RESUMING.**  `Paper_Bridge.thy`
(new, downstream of BOTH `Paper_Class` and `Section_2_Usc`) was written
and registered in `ROOT`; registering a NEW theory mid-session wedges
the PIDE server, which snapshots `ROOT` at startup.  Every theory then
reports "Malformed theory", INCLUDING already-green ones, and reverting
the `ROOT` edit does NOT recover it.  A server restart is required.

**`Paper_Bridge.thy` IS VERIFIED** (79 commands, `overall_status ok`;
commit `63bf783`).  In ROOT after `Paper_Class`; imports `Paper_Class`
and `Section_2_Usc` so neither of those has to import the other.  It
exports `stopped_market_acont_in_sconstraint`: for ANY `stopped_market`
witness, the CONTINUED volatility lies in `sconstraint k L` at every
time `s ≥ 0`, almost surely — the witness side of the faithful bridge.
Plus `stopped_market_acov_leaves_sconstraint`, recording the contrast
that the witness's OWN volatility is `0`, hence outside the constraint
set, from the stopping time onward.

Also `stopped_market_acont_integrable`: the continued volatility is
`set_integrable` on every `{s..t}` (boundedness via `acont_bounded` →
`sconstraint_norm_le`, then `Bochner_Integration.integrable_bound`).

**THE VOLATILITY SIDE OF THE BRIDGE IS COMPLETE.**
`stopped_market_Yint_diffquot_in_sconstraint`: for a `stopped_market`
witness the CONTINUED running covariation has every difference quotient
in `sconstraint k L`, a.s., for all `0 ≤ s < t` — verbatim the
covariation clause of `paper_pair_class`, no stopping caveat.  The
chain is: witness `acov` → `acont` (continue past `tau` with `mat 1`,
admissible since `L ≥ 1`) → integrable on bounded intervals
(`acont_bounded` + Bochner bound) → `Yint` (additive by
`set_integral_Un_AE`) → quotients in `S` (`average_in_closed_convex`,
the paper's Lemma 2.1 step).

**CORRECTION 2026-08-05 — THE BRIDGE NEEDS A CONTINUED *PROCESS*, NOT
JUST A CONTINUED VOLATILITY.  Read this before starting the martingale
side; the previous handover understated the work by a large factor.**

The volatility side above is correct and complete, but it does NOT pair
with the witness's own `X`.  A `stopped_market` witness has
`X s ω = X (min s (tau ω)) ω`, so after `tau` the process is FROZEN while
`Yint (acont …)` keeps growing at rate `mat 1`.  Then

    E[outerp X_t − Y_t | F_s] = outerp X_s − Y_s − (t − s)·mat 1
                              ≠ outerp X_s − Y_s

for `s ≥ tau`, so `outerp X − Y` is *not* a martingale and the pair
`(X, Yint (acont …))` is *not* a member of `paper_pair_class`.  This is
not a proof-engineering gap; it is forced by (1.7), which admits no
volatility that vanishes (`0 ∉ sconstraint k L` for `k < n`).

Consequently the faithful bridge must CONTINUE THE PROCESS as well:
after `tau`, run an independent Brownian motion, i.e. work on a product
space `M ⊗⇩M bm_paths` with

    X̃ t ω = X (min t (tau ω)) ω + (B t − B (min t (tau ω)))

whose covariation density is `acov` before `tau` and `mat 1` after —
exactly `acont`.  That means: product measure, product filtration, the
martingale property of the concatenation, and the compensated-square
identity.  Realistically ~1–2k lines, and it is the true content of "the
martingale side of the bridge".

The pay-off is still worth it and the value estimate is unchanged: `tau`
is a PRE-exit time (`X_in_K` up to `tau`), so the first exit of the
continued path is `≥ tau`, giving `stopped_val_fn ≤ paper_v`.

WHAT REMAINS for the bridge, in order: (i) the product/continuation
construction of `X̃` just described; (ii) `X̃` and `outerp X̃ − Yint (acont …)`
as martingales for the PAIR natural filtration; (iii) the pair-law
construction itself (pushforward of `(X̃, Y)` to the pair path space).

**LOCALE UPGRADED (2026-08-05, commit `6125a9a`) — the gap below is
CLOSED in the locale, verification of two sites pending.**
`sufficiently_volatile_market` now carries
`acov_time_measurable: AE ω in M. (λs. acov s ω) ∈ borel_measurable
lborel`.  Faithful, not a strengthening: the paper's (1.7) constrains
`d⟨X⇩i,X⇩j⟩(t)/dt`, an a.e. derivative of a continuous
finite-variation function, whose time-measurability is automatic; our
locale takes `acov` as primitive so it must be stated.  Six discharge
sites: `Ito_Market` ×2 (mirrored as a sub-locale assumption),
`Value_Function`, `Section_2_Usc` ×2 (inherited / `measurable_If` for
the degenerate market) — ALL FOUR VERIFIED; `Brownian_Continuous`
(constant `mat 1`) and `Deterministic_Radius_Market` (new `dra_cont`
+ `dras_measurable_time`, by the `drC2_cont` route) — WRITTEN, NOT YET
PIDE-CHECKED, see below.  Once checked, drop the `meas` hypothesis
from `Paper_Bridge.stopped_market_acont_integrable`.

**LOCALE ASSUMPTION RESTATED ON `{0..}` (commit `d94b760`).**  It now
reads `acov_time_measurable: AE ω in M. set_borel_measurable lborel
{0..} (λs. acov s ω)`.  MORE faithful — the paper's (1.7) constrains the
density for "a.e. `t ≥ 0`" — and forced by a real bug: the
all-of-`ℝ` form is FALSE for the deterministic-radius witness, since
`dras q φ T0 u ω = dra q φ u ω` for `u < 0`, which is not
`dra q φ (max u 0) ω`.  On `{0..}` the truncation is invisible and
`dra_cont` applies.

**LOCALE UPGRADE VERIFIED (2026-08-05, commit `fcd26dd`).**
`Relative_Arbitrage_Stochastic` 531, `Ito_Market` 1446,
`Brownian_Continuous` 952, `Deterministic_Radius_Market` 6100 — all
`ok`.  That covers the upgraded locale itself, the `{0..}` restatement,
and BOTH discharges that needed real proofs (`dra_cont` +
`dras_measurable_time` for the deterministic-radius witness; the
constant `mat 1` for the Brownian one).  A duplicated `show`, left by
the earlier git-checkout/MCP interleaving, was found and removed here.

**ALL SIX DISCHARGES VERIFIED (2026-08-05, second session).**  The two
that the previous session could not schedule loaded clean on the first
`get_progress`: `Value_Function` 724, `Section_2_Usc` 7,005.  Nothing about
the locale upgrade is open, and the buffer-corruption episode described in
the previous handover did not recur after the restart.

**THE MEASURABILITY GAP IS CLOSED END TO END (commit `297d340`).**  The
locale carries `acov_time_measurable`; `Paper_Class.acont_set_borel_measurable`
transports it to the continuation (`set_borel_measurable lborel {0..}`), and
`set_borel_measurable_subset` cuts it to `{s..t}` — legitimate because
`0 ≤ s` puts `{s..t}` inside `{0..}`.  Both `Paper_Bridge` integrability
results have LOST their `meas` hypothesis; the volatility side of the
bridge is now HYPOTHESIS-FREE.  Do not reintroduce a measurability
assumption downstream — take it from the locale.

**PERFORMANCE FIX (2026-08-05, commit `40e3796`).**  The three `GG`
lemmas in `Path_Tightness_Market` each ran `auto simp: GG_def`, which
unfolds the definition into the goal and lets the simplifier rewrite
underneath the resulting `SOME`-term — inside the `AE` and inside the
big `good` predicate.  `GG3` never finished (>143 s CPU) and blocked
the whole downstream chain in PIDE; it would hang the batch build the
same way.  Fixed by extracting the `someI_ex` conjunction ONCE as
`GGspec` and projecting: now 3 ms.  The same shape in
`Section_2_Compactness` (~583, ~631) is 5 ms — its `SOME` predicate is
small — and was deliberately left alone.

The three theories touched this cycle all re-confirmed green after the
restart: `Exit_Semicontinuity` 2,676, `Paper_Class` 2,002,
`Paper_Bridge` 335 (and `Section_2_Usc` 6,995, `Path_Tightness_Market`
838 after the performance fix).  The mass "failures" seen while the session was wedged
were artifacts of the ROOT snapshot, exactly as suspected.  Then re-confirm `Paper_Class` (2,002) and
`Exit_Semicontinuity` (2,676), whose reported failures were artifacts.

LESSON (also in memory `isabelle-pide-stale-root`): do NOT register a
new theory in `ROOT` mid-session.  If new material needs imports an
existing theory lacks, ADD THE IMPORT to that existing theory — editing
an existing `imports` line works fine in-session.

STILL OPEN in NC-2/3: instantiating the X-side
estimate at the pair laws (`path_law_holder_ball_bound_vec` into
`pair_holder_charge_split` and `tight_on_set_pair_holder_charge`), and
instantiating `weak_conv_integral_of_L2_bound` with the class's own
second-moment bound (§2.6 `martingale_bounded_test` /
`coord_sq_bounded_test` supply the identities on members).  Also still
recorded: cap-invisibility for large `T` (Lemma 1.9/(3.10)).

**WARNING (2026-08-05): the NC-2 X-side instantiation is NOT a plug-in.**
The chain `path_law_holder_ball_bound_vec` consumes a fourth-moment bound,
and the repo's supplier `Increment_Moments.fourth_moment_bound_bounded`
assumes a UNIFORM SUP BOUND on the process (`bnd: AE ω. ¦X u ω¦ ≤ R`), used
to get `X⁴` integrable.  That hypothesis holds for market witnesses because
they are CONFINED to `K ⊆ cball 0 r` up to `tau` — it does NOT hold for a
member of `paper_pair_class`, whose process is neither stopped nor confined
(the paper's (1.7)–(1.8), §3/NC).  So the fourth-moment estimate has to be
redone from square-integrability alone (`paper_pair_class_Y_bounded_ae` is
the entry point: bounded `Y` ⟹ `E[¦X_t¦²] < ∞` through the `outerp X − Y`
martingale clause), or `fourth_moment_bound_bounded` has to be generalised
to replace `bnd` by an `L⁴`-integrability hypothesis.  Budget for it
accordingly; do not schedule it as "instantiation".

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

## 4. Working notes for the next agent — READ BEFORE EDITING

### 4.1 The three ways to lose a session (all cost a user restart)

1. **Never register a NEW theory in `ROOT` mid-session.** The PIDE server
   snapshots `ROOT` at startup. Registering a new node makes every theory
   in the project report "Malformed theory", including already-green ones,
   and REVERTING THE ROOT EDIT DOES NOT RECOVER IT. If new material needs
   imports an existing theory lacks, ADD THE IMPORT to that existing
   theory — that works fine in-session (verified: `Path_Tightness` was
   added to `Paper_Class`'s imports without incident). Create separate
   theories only when a restart is already due. `Paper_Bridge` exists
   because this rule was broken; it cost two restarts.
2. **Route EVERY edit through the MCP `edit` tool.** The server keeps its
   own buffer per file and treats it, not the disk, as authoritative. A
   `git checkout`, a Write/Edit-tool write, or a script edit desyncs it;
   a later `mcp edit` then writes *the stale buffer plus your change*
   back to disk, silently reverting your work. **The resync tool is
   `read`** — its own description says so, and it works immediately where
   `unload`, `touch` and `git checkout` all fail. Reach for `read` FIRST
   on any disk/PIDE discrepancy.
3. **Never use `edit_all` without inspecting every occurrence.** It
   silently edits matches you did not look at. In this session it
   corrupted `Brownian_Continuous`'s buffer outright (reported as a
   7-line fragment, unrecoverable by `unload`) and separately left a
   duplicated `show` that only the prover caught.

### 4.2 Verifying

- **PIDE MCP, not batch builds** (user instruction). The loop is: edit →
  `get_progress` / `get_state`; `commands_failed = 0` at 100% IS
  verification. The first load after a restart re-elaborates the whole
  graph — budget 30-45 minutes and do non-prover work meanwhile.
- **Do not judge a theory mid-elaboration.** Failure counts are not final
  until `percentage_commands_processed` is 100 and nothing is listed as
  running. Several "22 failures" scares in this session resolved to 0.
- **`still_running_possibly_nonterminating` is ambiguous.** A FINISHED
  command can carry the flag with "No subgoals!". The diagnostic is
  whether `timing_ms` is GROWING between polls, plus `ps` on the Poly/ML
  process: real work shows ~100% CPU on one core. If both the JVM and
  Poly/ML sit at ~0% while `get_state` answers "queued for loading",
  nothing is being scheduled and only a restart helps.
- Editing an upstream theory re-elaborates everything downstream; batch
  related edits into one pass.

### 4.3 Proof-engineering traps seen repeatedly

- **Name collisions with the Henstock library.** `integrable_const` and
  `integrable_bound` resolve to the gauge-integral lemmas about
  `integrable_on cbox`. Use `Bochner_Integration.integrable_bound` and
  `finite_measure.integrable_const[OF fm]` (the latter lives in the
  locale; interpreting `finite_measure`/`prob_space` first also works).
- **"OF: multiple unifiers"** — let the conclusion drive unification:
  `proof (rule L)` with explicit `show`s, not an `OF` chain. Same for
  bare `OF` mangling function arguments; pin with `where`.
- **Always `fixes tau :: "'a ⇒ real"`** (or the analogous annotation) on
  statements about time functionals. Without it the variable generalises
  to a Banach algebra and every real-specific rule fails to APPLY with no
  type error — the symptom is rule-application failures on obviously
  correct goals.
- **Type-annotate `obtain`ed and statement-level function variables**;
  otherwise they stay polymorphic and everything downstream type-fails.
- `auto` will not instantiate bounded quantifiers (`∀t∈{0..T}. …`)
  mid-chain — project with `blast` first.
- `eventually_mono` is the reliable way to weaken an `AE` fact;
  `AE_mp`-as-elimination repeatedly failed to thread.
- Four tactic patterns HANG rather than fail: `unfolding open_openin`;
  `blast` asked to invent an existential witness; `(use … in blast)+` on
  schematic side conditions; and `auto simp: f_def` where
  `f = (λi. SOME x. P i x)` and `P` is large — that one measured >143 s
  without finishing in `Path_Tightness_Market` and is now 3 ms
  (`someI_ex` once, then `conjunct1`/`conjunct2`/`bspec`).
- **`lborel` is POLYMORPHIC and `real^'n^'n` has an `ord` instance.** In a
  goal `(λu. …) ∈ borel_measurable lborel` an unannotated binder can
  silently elaborate at the MATRIX type rather than at `real`. The symptoms
  do not point at types at all: `show`s that "fail to refine any pending
  goal" while printing *identically* to the goal, and `simp` unable to prove
  `open {..<0}`. Pin `lborel :: real measure` and annotate every binder.
  (Cost ~8 round-trips on a three-line measurability lemma; see
  `Paper_Class.acont_set_borel_measurable`, where the trap is also written
  into the theory text.)
- Related: the `measurable` method turns an indicator branch condition into
  a goal about the branch SET. `if u < 0 then … else …` leaves the true
  `open {..<0}`; the `indicat_real {0..}` form leaves the FALSE `open {0..}`
  and cannot be closed. Prefer the strict-inequality form.
- Chaining a NON-`AE` fact into `eventually_elim` fails with
  `exception THM 1 … RSN: no unifiers`. Use
  `by (rule eventually_mono) (use … in auto)` instead.
- **`stochastic_process` is SHADOWED** by Kolmogorov_Chentsov's homonym,
  which has a different arity; the symptom is a type error blaming the
  `t⇩0` argument ("No type arity measure :: zero"). Write
  `Stochastic_Process.stochastic_process` — and note a qualified name may
  NOT be broken across lines at the dot.
- `measurable_cong` refuses to apply as `rule measurable_cong` on a
  measurability goal (it is an `iff` and over-generalises, cf. the older
  note). To prove a function measurable because it is CONSTANT on the
  space, go through `measurableI` and compute the preimage
  (`= (if c ∈ C then space M else {})`).
- Fuller lists live in the agent memory files
  (`isabelle-pide-mcp-environment`, `isabelle-nonterminating-tactics`,
  `isabelle-mcp-buffer-desync`, `isabelle-pide-stale-root`); read them
  before long proof work.

### 4.4 Design constraints you must not "simplify"

- **The paper's class has NO stopping** ((1.7)-(1.8), p. 3): `X` is a
  martingale on all of `[0,∞)` with the covariation constraint for a.e.
  `t ≥ 0`, and `τ_K` is merely a functional of the path. A
  `stopped_market` witness is therefore NOT a class member. The bridge
  CONTINUES the witness past `tau` (`acont`, with `mat 1`, admissible
  because the locale carries the paper's standing `L ≥ 1`). Do NOT
  instead weaken `paper_pair_class` to constrain only up to the exit
  time — that is a different class from the paper's.
- **Do not confuse that with the `min t T` in the martingale clauses.**
  Two different stoppings are in play and only one of them is forbidden.
  Forbidden: stopping at `τ_K` (or at a market's `tau`), which would
  change the class. Required: stopping at the HORIZON `T`, because our
  path space is capped there and its points are `undefined` beyond `T`
  (see the extensionality bullet below). On `[0,T]` the clause says
  exactly what (1.7) says; `min t T` is only how one writes "martingale
  on `[0,T]`" inside the AFP's `martingale` locale, which quantifies over
  all times. The alternative is to move the whole development to
  `C([0,∞),ℝⁿ)` as the paper does — a redesign of the entire Section-2
  toolchain (path metric, tightness, portmanteau), not a local change.
  Worth recording for the record: the two classes have the same value,
  because a continuous martingale on `[0,T]` obeying (1.7) extends to
  `[0,∞)` by continuing with `mat 1` (admissible since `L ≥ 1`) — the
  same continuation the bridge needs, so prove it once.
- The horizon cap at `T` is OURS, not the paper's (they work on
  `C([0,∞),ℝⁿ)` with locally uniform convergence). Its invisibility is
  discharged at both path and law level; keep it that way.
- `real^'n × real^'n^'n` PARSES AS `real^('n × real)^'n^'n`. Use the
  `'n pairpath` type synonym.
- **The capped path space is EXTENSIONAL.** `ω ∈ mspace (path_metric T)`
  implies `ω u = undefined` for `u ∉ {0..T}`, so ANY clause of a path-law
  class that quantifies over unbounded time silently talks about a
  constant. That made `paper_pair_class` empty for a whole session (§3/NC,
  commit `080bd30`). Every time-quantified clause must carry `≤ T` or
  `min t T`.
- `mkt_path_laws` pins the market sample type to `('m ⇒ real ⇒ real)`
  because HOL cannot quantify over sample-space types and `bm_paths`
  lives there. Keep new market constructions on that type.
- Zero `sorry` across the development is an invariant.

### 4.5 Where to pick up

**REORDERED 2026-08-05 (second session).** The bridge is no longer the
cheapest way forward — see the CORRECTION in §3/NC: its martingale side
needs a product construction with an independent Brownian continuation
(~1–2k lines), because a stopped `X` cannot be paired with a growing `Y`.
Finish Lemma 2.3 *inside the class* first; it needs no witnesses at all,
half of it is now done, and it is what clause (1) actually consumes.

**UPDATED 2026-08-05 (second session).** Items 1(a),(b) below are DONE and
the whole four-step route to the martingale clauses is scripted in §3/NC;
steps (i)–(iii) are proved, step (iv) is the next thing to write. Read the
vacuity warning in §3/NC first — and before proving anything about a class
of path laws, prove it NONEMPTY.

In priority order:

0. **`paper_pair_class` NONEMPTINESS.** Not proved, and until it is, every
   theorem about the class is only conditionally useful. The witness is the
   Brownian pair law with `Y t = t · mat 1` (admissible since `L ≥ 1`,
   `mat_1_in_sconstraint`); the work is the off-diagonal covariation, i.e.
   `X_i X_j` a martingale for `i ≠ j`, which needs the independence of the
   Brownian coordinates. This would have caught the vacuity bug on day one.
0. ~~**THE UNIFORM FOURTH MOMENT**~~ — **DONE 2026-08-05**, commit
   `6ffd5b4`. **`Paper_Bridge.paper_pair_class_fourth_moment`**: for every
   member of `paper_pair_class` and `0 ≤ s ≤ T`,
   `E[(X_T$i − X_s$i)⁴] ≤ 8L²(T−s)²` (nn-integral form). No BDG, no change
   to `Increment_Moments`. This was the obstruction shared by the
   compensated clause of Lemma 2.3 and by NC-2's tightness; both are now
   unblocked. Details below.

1. **THE UNIFORM FOURTH MOMENT, BY LOCALIZATION — ALL FOUR STEPS DONE.**
   It unblocked BOTH the second martingale clause of Lemma 2.3 AND NC-2's
   tightness, and needed no BDG and no change to `Increment_Moments`.

   **DONE 2026-08-05** (commits `e6d1db1`, `9206228`, `a9f031d`,
   `b607cb6`), all in `Paper_Bridge.thy`:
   - `pcoord` / `ploc` — the class member's stopped coordinate process and
     the localizing time `τ_R`; `paper_pair_class_cont_adapted` and
     **`paper_pair_class_ploc_stopping`** (it IS a stopping time, via
     `Exit_Time.etime_stopping_time`); `pcoord_stopped_bounded` (the
     stopped process never leaves `[−R,R]` — this needs CONTINUITY, not
     just the infimum, because at `τ_R` the path is exactly at `R`, and
     `Exit_Time.etime_stays_in_cball` is that statement).
   - **`paper_pair_class_stopped_coord_martingale`** and
     **`paper_pair_class_stopped_comp_martingale`** — optional stopping
     for `X` AND for `X² − Y_ii`. This is the step the plan long recorded
     as out of reach: `Optional_Sampling.optional_stopping` wants an
     INTEGRABLE ENVELOPE of the unstopped process, which the market locale
     cannot supply. For a class member it exists —
     `Doob_Inequality.horizon_sq_int_martingale` builds `Dsup` out of
     nothing but square-integrability, which `paper_pair_class_sq_integrable`
     provides, and `Dsup_sq_integrable` covers the compensated envelope
     `Dsup² + n·L·T`.
   - Supporting: `paper_pair_class_coord_adapted`, `_path_cont`,
     `_coord_paths_cont`, `_comp_paths_cont` (continuity on the WHOLE
     half-line — the stopped process is constant after `T`, and `{0..}` is
     the form `stopped_adapted_of_cont` and `optional_stopping` ask for),
     `paper_pair_class_compensated_coord_martingale`.

   **THE FOUR STEPS, ALL VERIFIED** (commits `47b26a5`, `50e9286`,
   `f6301f3`, `4379916`, `6ffd5b4`):
   - (a) `sconstraint_diag` (a constraint matrix has diagonal entries in
     `[0,L]`), `paper_pair_class_Y_diag_increment` (the diagonal form of
     the covariation clause) and `paper_pair_class_stopped_compensator_rate`
     — stopping only shrinks an interval, so the rate survives it.
   - (b) `paper_pair_class_stopped_cond_exp` —
     `E[(ΔX^τ)²|𝔉_u] = E[ΔA^τ|𝔉_u]`, the usual expansion: the cross term
     is pulled out because `X^τ_u` is `𝔉_u`-measurable
     (`cond_exp_measurable_mult`), and the compensated martingale converts
     `E[(X^τ_v)²|𝔉_u]`. Every integrability side condition is FREE because
     the stopped pair is bounded (`paper_pair_class_stopped_abs_le`,
     `_stopped_A_abs_le`) — that is exactly what localizing buys.
   - (c) `paper_pair_class_stopped_fourth_moment` — `fourth_moment_bound_bounded`
     at the stopped pair, uniformly in `R`.
   - (d) `ploc_eq_T_of_below` + `paper_pair_class_fourth_moment` — pathwise
     `τ_R = T` once `R` exceeds the (finite, by compactness) sup of the
     path, so the stopped increments are eventually EQUAL to the unstopped
     ones along `R_m = ¦x$i¦+1+m`, and `nn_integral_liminf` finishes.

   Traps met: `prob_space.integrable_const` does not resolve — use
   `finite_measure.integrable_const[OF fm]` (same shadowing family as
   `integrable_bound`); a calculational chain through `¦a²¦` breaks when
   simp normalises it away, so state the square bound via `power_mono` on
   `¦a¦` (that also cleared a `still_running_possibly_nonterminating`
   flag); and this dev `linarith` failed (after 5.9 s) on
   `¦a−b¦ ≤ 2C` from `¦a−b¦ ≤ ¦a¦+¦b¦`, `¦a¦ ≤ C`, `¦b¦ ≤ C` when the
   atoms were large `pcoord …` terms — abstracting it into a standalone
   lemma over plain reals (`abs_diff_le_two`, `simp add: abs_le_iff`)
   closes it instantly. **The recurring rule: state arithmetic at the
   level of plain reals, never over big application terms.**

   **NEXT, now that the bound exists:** feed it into (i) the compensated
   clause of Lemma 2.3 — rerun steps (i)–(iv) of §3/NC with the process
   `(outerp X − Y)$i$j`, whose `L²` bound is now available since
   `(X_i X_j)² ≤ (X_i⁴ + X_j⁴)/2`; and (ii) NC-2's tightness, feeding
   `path_law_holder_ball_bound_vec`.
2. **NC-3, Lemma 2.3.** THREE of the four clauses now pass to the weak
   limit (`paper_pair_class_limit_three_clauses`: start, covariation,
   X-martingale — steps (i)–(iv), §3/NC). The fourth is the compensated
   clause and follows the same four-step route once item 1 supplies its
   `L²` bound. The route, for reference:
   (a) **DONE** (commit `c3434e8`) — `paper_pair_class_sq_integrable`:
   square-integrability of `X` under a class law, from `martingale.integrable`
   on the `outerp X − Y` clause plus `paper_pair_class_Y_bounded_ae`, with
   `integrable_bounded_linear[OF bounded_linear_vec_nth]` to get at the
   `(i,j)` entry; supporting `paper_pair_class_eval_measurable`;
   (b) the L2 BOUND — `E[(X_t$i)²] ≤ (x$i)² + n·L·T`, uniform over the class.
   Scouted: it needs only CONSTANCY OF THE MEAN of `outerp X − Y`, no
   conditioning and no tower property. Take `martingale.set_integral_eq`
   (premises in the order `A ∈ F i`, `t₀ ≤ i`, `i ≤ j`) at `A = space Q`,
   convert with `set_integral_space`, evaluate the `t = 0` side by
   AE-congruence to the constant `outerp x`, and pull the `(i,i)` entry
   through the integral. NOTE there is no `integral_bounded_linear` in the
   library — go through `has_bochner_integral_bounded_linear` +
   `has_bochner_integral_integral_eq`;
   (c) `unif_integrable_of_L2_bound` + `weak_conv_integral_of_L2_bound`
   to carry the integrated identities to the limit; (d) upgrade continuous
   tests to events with the §2.6 engines (`metric_measure_eqI_bounded_cts`,
   `metric_measure_mono_bounded_cts` — they live in `Section_2_Usc`, so this
   step belongs in `Paper_Bridge` or needs an import added; do NOT create a
   new theory mid-session, §4.1); (e) assemble with the AFP's
   `sigma_finite_filtered_measure.martingale_of_set_integral_eq`, the
   set-integral characterisation, which is the right interface for
   integrated identities.
2. **NC-2, tightness of the class.** Read the WARNING in §3/NC first: this
   is NOT an instantiation, because `fourth_moment_bound_bounded` assumes a
   uniform sup bound the class does not have.
3. **NC, the shift structure (LR Prop 2.2(ii))** — `paper_pair_class k L T x`
   is the image of `paper_pair_class k L T 0` under
   `ω ↦ restrict (λt. (x + fst (ω t), snd (ω t))) {0..T}`. Needed so Berge
   gets a *fixed* compact index set. Scouted this session; the enabling
   facts are: `natural_filtration M t₀ Y = (λt. family_vimage_algebra
   (space M) {Y i | i ∈ {t₀..t}} borel)` depends ONLY on `space M` and the
   process, so the natural filtration is LITERALLY THE SAME measure for `Q`
   and its shift; and the martingale clauses then transfer through
   `martingale_of_set_integral_eq` + `integral_distr`, with
   `outerp (x + v) = outerp v + outerp x + (χ i j. x$i·v$j + v$i·x$j)`
   splitting the second clause into the first clause, a constant, and a
   linear function of `X`. Watch extensionality: points of
   `mspace (path_metric T)` are `extensional {0..T}`, so the shift must
   `restrict` (hence it depends on `T`).
4. **NC headline** — with 1–3, clause (1) is Berge (`usc_sup_over_compactin`)
   against `Exit_Semicontinuity.ess_inf_pexit_usc`, applied to `paper_v`
   DIRECTLY. Note this is a cleaner target than "identify `stopped_val_fn`
   with the class supremum": `paper_v` *is* Eq. (1.6), so proving it usc IS
   clause (1) for the paper's own value function. The bridge
   (`stopped_val_fn ≤ paper_v`) is then only needed for the clause-(3)
   lower bound via N4, not for clause (1).
5. **NC, the bridge's martingale side** — the product/continuation
   construction, per the CORRECTION in §3/NC.
6. **N5, the weak DPP** — untouched. Prop 2.4's (2.9) is the exact
   target; build order scripted in §3/N5. Unblocks clause (2) with N4.
7. Clause (3) beyond the ball / general `n − k ≥ 2`.

Realistic assessment: NC and N5 are each substantial multi-thousand-line
items. Do not expect Theorem 1.1 to fall out of a single session, and do
not let the goal-hook pressure you into writing unverified proof text —
committing material the prover has not checked is worse than committing
nothing.

**Getting the paper.** `curl -sL https://arxiv.org/html/2512.17702v1`
returns the full LaTeXML HTML; strip tags and keep each `<math>`'s
`alttext` attribute to recover the formulas. (`WebFetch` summarises and is
useless for statements.) LR is at `https://arxiv.org/pdf/2003.13611` —
note the versioned URL `…/2003.13611v3` 404s.

---

## SESSION 2026-08-06: NC-3 COMPLETE, NC-2 COMPLETE, CLASS SEQUENTIALLY COMPACT

Two of the four remaining NC items are done and PIDE-verified (43 theories
ok; `Paper_Bridge` 6792 commands, `Paper_Class` 3107).

**Commit `d4cbf8b` — NC-3, the compensated clause; the class is weakly
closed.** `paper_pair_class_weak_closed`: a weak limit of members of (1.7)
is a member. New material, in dependency order:
`prod_minus_sq_bound` ((ab−c)² ≤ a⁴+b⁴+2c²), `fourth_power_sum_bound`
((a+b)⁴ ≤ 8(a⁴+b⁴)), `zero_le_fourth`, `comp_entry_eq`/`_cont`,
`paper_pair_class_fourth_moment_abs` (the fourth moment of the coordinate
ITSELF, from NC-1 plus the start clause), `paper_pair_class_comp_entry_sq_nn`
(the uniform L² bound on `(outerp X − Y)$i$j` — the single input the generic
weak-limit chain was missing), then `martingale_matI` and its three helpers
`measurable_mat_entries` / `integrable_mat_entries` /
`set_integral_mat_component`, then
`paper_pair_class_comp_entry_martingale_limit`,
`paper_pair_class_comp_martingale_limit`, `paper_pair_class_weak_closed`.

  *Why `martingale_matI` had to be written:* `Ito_Market.martingale_vecI`
  does NOT iterate to `real^'n^'n`. All three of its helpers
  (`measurable_vec_components`, `integrable_vec_components`,
  `set_integral_vec_component`) are stated for REAL entries only. The matrix
  analogues are proved from the euclidean structure instead: `Basis` of a
  matrix is `{axis i (axis j 1)}` and `A ∙ axis i (axis j 1) = A$i$j`, so
  measurability comes from `borel_measurable_euclidean_space`, integrability
  from `norm_le_l1` + `integrable_bound`, and the component identity from
  `bounded_linear_compose` of two `bounded_linear_vec_nth`.

**Commit `9870e98` — NC-2, tightness; and sequential compactness.**
`paper_pair_class_convergent_subsequence`: every sequence of members has a
subsequence converging weakly to a MEMBER. Chain:
`paper_pair_class_fourth_moment_integrable` / `_bochner` (the NC-1 bound as
a *Bochner* integral — integrability is free, a nonnegative function with a
finite `nn_integral` is integrable), `path_coord_cont_on`,
`paper_pair_class_pair_holder_charge`, `paper_pair_class_charge_small`,
`tight_on_set_paper_pair_class`, `paper_pair_class_weak_limit_prob_space`.

  *Why `path_law_holder_ball_bound_vec` could not be applied off the
  shelf* (this is what the §3/NC WARNING was about, and the resolution):
  its conclusion is about the push-forward `path_law M X T` of an abstract
  process, whereas a class member IS already a law on paths; and it wants
  the start condition `X₀ = x` POINTWISE, whereas a class member has it only
  almost surely. So its ARGUMENT is re-run natively on the pair path space:
  the dyadic bad events are built directly from `fst (ω ·) $ i`
  (`pair_law_eval_measurable` is already all-`u`, because off the horizon
  the evaluation is the constant `undefined`), and the failure of the
  start-and-Lipschitz event is charged to a null set. That also removes the
  need for the `Y`-event of `pair_holder_charge_split` to be measurable, so
  the split lemma is not used at all.

  *Why the limit still has mass one:* Prokhorov
  (`tight_on_set_imp_convergent_subsequence`) only gives `≤ 1`. Tightness is
  used a SECOND time: the compact charging set is closed, so
  `weak_conv_closed_limsup` keeps at least `1 − e` of the mass in the limit,
  for every `e`.

### Traps recorded this session

- **`ennreal_plus` is a DEFAULT simp rule in the SPLITTING direction.**
  Adding `ennreal_plus[symmetric]` to a simpset LOOPS. To recombine
  `ennreal a + ennreal b` into `ennreal (a+b)`, apply `ennreal_plus` as a
  RULE (or state the equation the other way round and `rule sym`).
- **On `ennreal`, `∞` and `⊤` are DIFFERENT terms** — `∞` is a definition,
  only simp-identified with `⊤`. An Isar `show` must use whichever the rule
  states (`integrableI_nonneg` states `< ∞`), or it "fails to refine any
  pending goal" while printing identically.
- **`linarith` again failed on a plainly LINEAR goal** ((a²+b²)² ≤ 2(a⁴+b⁴)
  from two equations); `argo` closes it instantly. Same family as the
  earlier notes.
- **The MCP `edit` tool normalises `*` inside `text ‹…›` blocks to `\<sqdot>`.**
  A later `edit` whose `old_text` spans such a block will not match. Anchor
  replacements on code, not on prose.

### What is left in NC

0. **Nonemptiness of `paper_pair_class k L T 0`.** Still open, and now the
   only thing standing between the compactness result and a non-vacuous
   headline. Brownian pair law with `Y t = t · mat 1` (needs `L ≥ 1` via
   `mat_1_in_sconstraint`); the work is the off-diagonal covariation
   `X_i X_j` being a martingale.
1. **The shift structure (LR Prop 2.2(ii))** — unchanged from the previous
   session's scouting (see item 3 of the previous list).
2. **The NC headline** — `paper_v` usc. The glue is now visible:
   `paper_v k L T K x = Sup ((λQ. ess_inf_time Q (λω. pexit T K (λt. fst (ω t))))
   ` paper_pair_class k L T x)`, and `pexit T K f = etime T (−K) (λr g. g r) f`,
   while `vshift T A y Q = enn2real (ess_inf_time Q (etime T A (λs w. y + w s)))`.
   So with `A = {p. fst p ∉ K}` (open for closed `K`) and `y = (x, 0)`,
   `vshift T A (x,0)` on the 0-started class is exactly the `x`-started
   value — PROVIDED the shift structure of item 1. Then
   `Section_2_Usc.vshift_sup_usc_of_seq_compact` applies verbatim, its `seq`
   hypothesis being `paper_pair_class_convergent_subsequence`.

### Commit `73ecbe2` — the shift structure is DONE

`paper_pair_class_shift_image`: for `0 ≤ T`,
`paper_pair_class k L T x = pshift_law T x ` paper_pair_class k L T 0`.

Ingredients, all in `Paper_Bridge`: `pshift` (the pathwise translation,
which must `restrict`), `pshift_in_mspace` / `_zero` / `_pshift` /
`_inverse` / `Lipschitz_pshift` / `pshift_measurable` /
`pshift_filtration_measurable`; `pshift_law` with `sets`/`space`/
`prob_space`/`natural_filtration_pshift_law`; `martingale_add`,
`martingale_add_const`, `martingale_cong_ge` (none of them in the AFP);
`AE_pshift_law`; `comp_shift_split`, `bounded_linear_cross`;
`martingale_pshift_law`; `paper_pair_class_pshift`.

Two design points worth keeping:
- the FILTRATION does not move under the shift (`natural_filtration`
  depends only on `space M` and the process), so the martingale transfer is
  a statement about one filtration, not two;
- `AE_pshift_law` needs NO measurability hypothesis on the property,
  because the shift is a bijection with measurable inverse — the null set
  can be pushed forward explicitly.

### What is left in NC, after this session

1. **Nonemptiness of `paper_pair_class k L T 0`.** The only thing between
   the compactness/shift results and a non-vacuous headline. Brownian pair
   law with `Y t = t · mat 1` (`mat_1_in_sconstraint` needs `L ≥ 1`); the
   work is the off-diagonal covariation `X_i X_j` being a martingale.
2. **The NC headline, `paper_v` usc.** All the structure is now present;
   what remains is glue, and it is fully scouted:
   - `ess_inf_time (pshift_law T x Q) g = ess_inf_time Q (λω. g (pshift T x ω))`
     — both inclusions from `AE_pshift_law` (the reverse one by applying it
     at `−x` to the shifted law).
   - with `A = {p. fst p ∉ K}` (open for closed `K`) and `y = (x, 0)`,
     `etime T A (λs w. y + w s) ω` and
     `pexit T K (λt. fst (pshift T x ω t))` are the SAME infimum: for
     `r ∈ {0..T}`, `fst ((x,0) + ω r) = x + fst (ω r) = fst (pshift T x ω r)`.
   - hence `paper_v k L T K x
       = Sup ((λQ. ennreal (vshift T A (x,0) Q)) ` paper_pair_class k L T 0)`
     (`ennreal (enn2real ·)` is harmless because `pexit ≤ T`).
   - then `Section_2_Usc.vshift_sup_usc_of_seq_compact` applies verbatim,
     with `C = paper_pair_class k L T 0`, `seq` =
     `paper_pair_class_convergent_subsequence`, `sC` =
     `paper_pair_class_sets`, `pC` = `paper_pair_class_prob`, `neC` = item 1.
   - finally, usc in `x ∈ real^'n` follows from usc at `(x,0)` because
     `x ↦ (x,0)` is continuous.

---

## SESSION 2026-08-06 (continued): THE NC HEADLINE IS PROVED

**Commit `3f80e4d` — `paper_v_usc`.** For `0 < T`, `0 ≤ L`, `closed K` and a
NONEMPTY class at `0`:

```
paper_v k L T K x < b  ⟹  eventually (λy. paper_v k L T K y < b) (nhds x)
```

`paper_v` IS Eq. (1.6), so this is clause (1) of Theorem 1.1 for the paper's
own value function. New glue: `pshift_law_compose`, `pshift_law_zero`,
`AE_pshift_law_iff`, `ess_inf_time_pshift_law`, `pexit_pshift_eq_etime`,
`ennreal_Sup_image`, `paper_v_eq_vshift_sup`, `paper_v_usc`.

Two things worth keeping:
- going through `AE_pshift_law_iff` avoids ever needing `etime` to be Borel
  measurable — the repo does not have that, `Section_2_Usc` only ever uses
  its SUBLEVEL sets (`open_etime_shift_less`);
- in `assumes ne: "paper_pair_class k L T 0 ≠ {}"` the `0` MUST be annotated
  `(0 :: real^'n)`. Without it the class in the assumption elaborates at a
  fresh type variable, silently and with no warning, and `rule ne` then
  fails against a goal that prints identically.

**Commit `9e9ef5b` — the reusable core of nonemptiness.** `pair_law_of`,
`phi_filtration_measurable`, `martingale_pair_law`: a pair PROCESS pushes
forward to a pair LAW, and a martingale for the process's own filtration is
a martingale for the law's NATURAL filtration.

## THE ONE REMAINING NC ITEM: nonemptiness of `paper_pair_class k L T 0`

Everything else in NC is done. Target witness (needs `1 ≤ L`, `1 ≤ k`,
`k < CARD('n)`):

```
φ ω = restrict (λt. (cbmX 0 t ω, t *⇩R mat 1)) {0..T}   on  bm_paths
Q   = pair_law_of T φ bm_paths
```

**The Brownian layer IS reachable from `Paper_Bridge`** — the chain is
`Paper_Bridge → Section_2_Usc → Value_Function → Brownian_Optimal_Boundary
→ Brownian_Continuous` — so NO import change (and no ROOT edit) is needed.
`cbmX`, `bm_paths`, `martingale_cbmX`,
`Brownian_market_sufficiently_volatile` are all in scope.

Checklist, in dependency order:

1. `φ` measurable into the path Borel σ-algebra — `Path_Space.pathify_measurable`
   (component measurability + path continuity; `cbmX` is exactly the
   continuous modification, that is what `Brownian_Continuous` supplies).
2. START clause: `AE ω. cbmX 0 0 ω = 0` (see `Brownian_market_sufficiently_volatile`'s
   own `X_start` step, which chains `cbmX_ae_eq` with `bmX_start`), and
   `0 *⇩R mat 1 = 0`.
3. COVARIATION clause: `(1/(t−s)) *⇩R ((t *⇩R mat 1) − (s *⇩R mat 1)) = mat 1`,
   then `Paper_Class.mat_1_in_sconstraint`. Deterministic, no probability.
4. X-MARTINGALE clause: `martingale_pair_law` at `Z u ω = fst (ω (min u T))`,
   whose hypothesis is `martingale bm_paths F 0 (λu ω. cbmX 0 (min u T) ω)`.
   That is `martingale_cbmX` STOPPED AT A DETERMINISTIC TIME. The repo's
   `Deterministic_Radius_Market.martingale_stopped_deterministic` is NOT
   reachable from `Paper_Bridge`, so write a local `martingale_stopped_const`
   (≈30 lines via `martingale_of_set_integral_eq`; the three cases are
   `u ≤ v ≤ T`, `u ≤ T ≤ v`, `T ≤ u`, and adaptedness is `F_{min u T} ⊆ F_u`).
5. COMPENSATED clause: `martingale_pair_law` at
   `Z u ω = outerp (fst (ω (min u T))) − snd (ω (min u T))`, whose hypothesis
   is that `outerp (cbmX 0 t) − t *⇩R mat 1` is a matrix-valued martingale.
   Assemble it from entries with `martingale_matI` (this session's lemma).
   - DIAGONAL entries: `(W_i)² − t` is `coord_Z X acov i` at `acov = mat 1`,
     available from `Brownian_market_sufficiently_volatile`'s
     `coord_Z_martingale`.
   - **OFF-DIAGONAL entries `W_i W_j`, `i ≠ j`: THIS IS THE ONE GENUINELY
     MISSING MATHEMATICAL INPUT.** The market locale only ever asserts the
     diagonal (`coord_Z_martingale`), so it has to be proved for the
     Brownian witness. Two routes:
     (a) *polarization*: `4 W_i W_j = ((W_i+W_j)² − 2t) − ((W_i−W_j)² − 2t)`,
         which needs "for a fixed unit direction `e`, `(e ∙ W)² − |e|² t` is a
         martingale" — i.e. the `coord_Z` result in a ROTATED coordinate.
         Cheapest if the repo can be made to give rotation invariance of
         `bm_paths`;
     (b) *direct*: expand `W_i(t)W_j(t) − W_i(s)W_j(s)` into
         `W_i(s)ΔW_j + W_j(s)ΔW_i + ΔW_i ΔW_j` and kill each term with
         independence of the increments from the past and of the coordinates
         from each other (`bm_paths` is built as a product of independent
         one-dimensional motions, so the second is structural).
     Budget this as the real work; everything else on the list is plumbing.

### The off-diagonal covariation, scouted precisely (2026-08-06)

`Brownian_Stopped.thy`'s `sorry` is filled (commit `0941c46`) and
`isabelle build -d . Arbitrage` is GREEN again — it had been red since
2026-08-03, when `sufficiently_volatile_market` gained
`acov_time_measurable` and that instance was not updated.

For NC nonemptiness, the last missing input — `W_i W_j` a martingale for
`i ≠ j` — reduces to exactly TWO facts about `bm_paths`, and the relevant
infrastructure has now been located:

- `bm_paths = Pi⇩M UNIV (λ_. wiener_pre)` (`Brownian_Market.thy:466`), so the
  COORDINATES are independent by construction.
- `Brownian_Market.bm_filtration_increment_indep` gives
  `indep_set (F_s) (vimage_algebra (space M) (λω. bmX x0 t ω − bmX x0 s ω) borel)`
  — the FULL VECTOR increment is independent of the past.
- `Brownian_Market.bm_indicator_increment_indep_var` turns that into
  `indep_var (indicator A) (λω. ω i t − ω i s)` for `A ∈ F_s`; and
  `bm_meas_increment_product` gives `∫ g·Δ_i = 0` for `F_s`-measurable
  integrable `g`. That kills the two CROSS terms of

      W_i(t)W_j(t) − W_i(s)W_j(s) = W_i(s)Δ_j + W_j(s)Δ_i + Δ_iΔ_j

  immediately (take `g = indicator A · W_i(s)`, resp. `· W_j(s)`).

So only the LAST term needs new work, and it splits into:

1. `indep_var (indicator A) (λω. Δ_i ω * Δ_j ω)` for `A ∈ F_s`. This is a
   near-copy of `bm_indicator_increment_indep_var` — that proof only ever
   uses that its second function factors through the VECTOR increment
   `λω. bmX x0 t ω − bmX x0 s ω`, and `v ↦ v$i · v$j` factors through it
   just as `v ↦ v$i` does. Cheap.
2. `E[Δ_i Δ_j] = 0` for `i ≠ j`. This is the genuinely new one: it needs
   independence ACROSS the components of the `Pi⇩M`. The repo's
   `Brownian_Market.indep_var_PiM_components` is NOT the right shape (it
   makes two componentwise-applied FAMILIES independent, not two distinct
   components). The tool to reach for is
   `HOL-Probability.Independent_Family.indep_vars_iff_distr_eq_PiM`, or a
   direct `product_sigma_finite` Fubini computation on
   `Pi⇩M UNIV (λ_. wiener_pre)` — each factor contributing
   `∫ (w t − w s) ∂wiener_pre = 0`, which is
   `Brownian_Market.bm_increment_component_integral` at the single-coordinate
   level.

With those two, the compensated clause assembles by `martingale_matI` from
`coord_Z_martingale` (diagonal) and the new off-diagonal, and the rest of
the nonemptiness checklist above is plumbing that is already written
(`martingale_pair_law`, `martingale_stopped_const`, `pathify_measurable`,
`mat_1_in_sconstraint`).
