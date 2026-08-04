# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Rewritten 2026-08-04 after the clause-(1) packaging and the N4 opening.
This document is the single source of truth for what is proved, what is
open, and what to do next. Everything referenced below is PIDE-verified
(commit `04d679f`) unless marked open; `Deterministic_Radius_Market.thy`
additionally awaits the batch-build cross-check (see §3/N4). History and
superseded scoping live in git (`git log -p PLAN_THEOREM_1_1.md`) — do not
resurrect them.

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
| (2) | `visc_sol k L (interior K) v` | open — items N4, N5 |
| (3) | `v = 0` on `K − interior K` | ball case **DONE** — `val_fn_boundary_zero`, `stopped_val_fn_boundary_zero`; general open — N4 |
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

Goal: for `Λ ∈ mkt_law_closure`, `vshift T A x Λ ≤` the class supremum;
then `w = stopped_val_fn`-sup and the law-level clause (1) becomes the
paper's. Do NOT believe shortcuts through usc of `vshift` in the law
argument: usc gives `vshift(Λ) ≥ limsup vshift(Qₘ)` — the WRONG direction.

Status: the integrated inputs are DONE (§2.6). Remaining, in order:

1. **The LOWER (trace / `eigen_lb`) constraint at the law level.** Its
   integrated form involves `min(t, τ)`, which is not a continuous path
   functional; decide its encoding (path exit time from the closed
   confinement set, or only inside the canonical-market step) together
   with 2.
2. **`acov` by Lebesgue differentiation** of the conditional
   quadratic-variation compensator — the hard analytic core; no repo
   infrastructure; PROTOTYPE before committing.
3. **Packaging**: canonical process, natural filtration, exit-time horizon
   into a `sufficiently_volatile_market`/`stopped_market` instance on path
   space (`mkt_path_laws` pins the sample type `('m ⇒ real ⇒ real)`;
   path-space markets need the same type — reuse `bm_paths`-style tricks
   or generalize the pin).
4. **Author-level alternative, worth deciding FIRST**: restate clause (1)
   and the downstream §3 arguments for the LAW-level value function `w`
   directly. If the sub/supersolution proofs only consume the DPP and
   `v > 0`, the identification is deferrable for the whole existence half
   — that demotes 1–3 from the critical path. Under this alternative,
   clause (1) is COMPLETE (`clause_one_law_level`).

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
   c. The stopped process `drXs q φ r t := drX q φ (min t (r² − q))`
      with the constant horizon `τ ≡ r² − q` (assume `q ≤ r²`):
      martingale because a deterministically-stopped martingale is one
      (reindex; for `s ≤ t`: if `τ0 ≤ s` both sides equal `drX τ0`, if
      `s < τ0` use the base property at `min t τ0` — NO optional
      stopping needed, the time is deterministic).
   d. `coord_Z` for the stopped process with
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
   f. `ess_inf_time = ennreal (r² − q)` (constant tau) and the headline
      `stopped_val_fn 1 L (cball 0 r) x = ennreal (ball_v r 1 x)` for
      `CARD = 2`, `0 < |x| ≤ r`, via `stopped_val_fn_le_ball_v` for ≤
      and this witness for ≥.

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
