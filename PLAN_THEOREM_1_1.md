# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Rewritten 2026-08-03 (evening) after the Lemma 2.2/2.3 milestone. This
document is the single source of truth for what is proved, what is open, and
what to do next. Everything referenced below is PIDE-verified at commit
`1d80e06` unless marked open. History and superseded scoping live in git
(`git log -p PLAN_THEOREM_1_1.md`) — do not resurrect them.

Sources: the paper (Lai/Shkolnikov/Soner, arXiv:2512.17702), its main
reference for Section 2 (Larsson–Ruf, *Minimum curvature flow and martingale
exit times*, EJP 29 (2024), arXiv:2003.13611, "LR" below), and Bouchard–Touzi
(SICON 49 (2011) 948–962) for the weak DPP.

---

## 0. The target and where it stands

Five clauses, with `v = enn2real ∘ val_fn k L K` (`Value_Function.thy`):

| | clause | status |
|---|---|---|
| (0) | `val_fn k L K x < ⊤` | **DONE** — `val_fn_finite_bounded` |
| (1) | regularity (paper: usc) | **usc PROVED for the law-level value function** (`vshift_sup_usc_mkt`, no compactness hypothesis left); identification with `val_fn` open — items N1–N3 |
| (2) | `visc_sol k L (interior K) v` | open — items N4, N5 |
| (3) | `v = 0` on `K − interior K` | ball case done (`val_fn_boundary`); general open — item N4 |
| (4) | uniqueness | **DONE** — `theorem_1_1_uniqueness_general` via `max_principle_boundary_holds` (Theorem 4.2(a)) |

Items N4/N5 carry research risk (see §3). Items N1–N3 are the current
critical path and are scoped.

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
  mathematical content the paper puts here resurfaces inside item N3.*
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
proved; what is NOT yet proved is that this supremum equals the repo's
`val_fn` (a supremum over abstract markets, not laws). That is items N1–N3.

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

### 2.4 The RQ-A toolkit (proved; needed by item N3)

The linear-inequality route that avoids Skorokhod representation:

- `Relative_Arbitrage_Convexity.support_characterisation` — a symmetric
  matrix lies in a closed convex `S` iff it satisfies every supporting
  inequality `tr(Ma) ≤ h_S(M)`.
- `Path_Tightness.weak_conv_on_integral_unif_integrable` — weak convergence
  plus uniform integrability passes integrals to the limit;
  `Path_Space.weak_conv_on_nn_integral_le` for nonnegative integrands
  (truncate + monotone convergence, no integrability needed).
- `Increment_Moments.sq_tail_bound_of_fourth_moment`,
  `clamp_integral_error`, `tendsto_real_of_approximants`.

NOTE: for the confined class (paths in `cball 0 r`) all covariation
functionals are BOUNDED, so plain weak convergence of bounded continuous
test functions may suffice and the UI machinery may be unnecessary. Check
this before deploying the UI route in N3 — it shortens the work.

---

## 3. NEXT WORK ITEMS (critical path for clause (1), then the rest)

In order. N1 is a warm-up; N2 is structural plumbing; N3 is the hard core.

### N1. Nonemptiness witness — DONE 2026-08-03 (commit 28b5011)

`Section_2_Usc.mkt_path_laws_nonempty`: the immediate-stop market inhabits
the family whenever `x0 ∈ K` (plus the numeric side conditions).  Helper:
`set_integral_at_origin`.  The original scoping follows for reference.

#### N1 as originally scoped

`vshift_sup_usc_mkt` assumes `mkt_path_laws k L K x0 T ≠ {}`. Provide the
IMMEDIATE-STOP market, in the class whenever `x0 ∈ K`, `1 ≤ k`,
`k < CARD('m)`, `1 ≤ L`:

    X s ω   = x0                       (deterministic, constant in time)
    tau ω   = 0
    acov s ω = (if s = 0 then mat 1 else 0)
    M       = bm_paths                 (any prob space works; bm_paths keeps
                                        the sample type ('m ⇒ real ⇒ real)
                                        that mkt_path_laws pins)
    F       = natural_filtration bm_paths 0 X

Check-list against the locale + witness conditions: martingale (constant
process), `coord_Z` constant because `∫₀ᵗ acov$i$i ds = 0` (integrand
nonzero only on the Lebesgue-null `{0}`), eigen bounds needed only AT
`s = 0` where `acov = mat 1` (reuse the `elb`/`eub` blocks from
`Brownian_market_sufficiently_volatile` in `Brownian_Continuous.thy`),
`X_stopped` and `acov = 0` after `tau` immediate, diagonal entries pathwise
integrable (bounded step function). Put it in `Section_2_Usc.thy` next to
the definitions.

### N2. The pushforward half — DONE 2026-08-03 (commit b62098b)

All in `Section_2_Usc`: `mkt_law_witness_shift` (markets shift; the
coord_Z/dynkin transfers go through `martingale.{diff,add,scaleR_const}`,
`martingale_vec_component`, `martingale_expectation_eq`),
`mkt_law_witness_mono_K`, `witness_value_le_vshift` (the value is dominated
by the vshift of the shifted law when the open target `A` is disjoint from
`K` and the value is ≤ the horizon — hypothesis `vT`, dischargeable from
`expected_exit_time_bound` via mono to the ball), and the assembly
`witness_value_le_law_sup`:

    ess_inf_time M tau
      ≤ ennreal (Sup (vshift T A x0 ` mkt_law_closure k L (cball 0 (2r)) 0 T)).

So every WITNESS value sits under the unconditionally-usc law-level
majorant of `vshift_sup_usc_mkt`.  Still missing on this side, besides N3:
(a) `val_fn` quantifies over ALL class markets, witnesses only over stopped
confined ones — either prove "stopping a market preserves the class and the
value" (optional-stopping closure; `stopped_martingale_L2` machinery) or
restate clause (1) for the stopped subclass; (b) discharge `vT` uniformly
(T := r²/(CARD − k) works via `ball_v`).  The original scoping follows.

#### N2 as originally scoped

Goal: relate `val_fn k L K x` to the law family started at the origin.

- Shift lemma on markets: if `(M,F,X,acov,tau)` is a market for `(K, x0)`,
  then `(M,F,(λs ω. c + X s ω),acov,tau)` is one for `(c + K, c + x0)` —
  every locale axiom is shift-invariant (martingale property because
  constants are `F 0`-measurable; `coord_Z` changes by an affine
  martingale; check `dynkin_quadratic`, whose right side becomes
  `(c+x0)∙(c+x0)`).
- Then `mkt_exit_vals k L K x` matches vshift-values of 0-started laws for
  the shifted domain, in the form `vshift T A x ` mkt_path_laws k L K' 0 T`.
- CAREFUL with the two K's: `vshift T A x Q` shifts the PATH by `x` and
  exits from a FIXED open `A`; the market class fixes `K`. In the paper
  both move together. Work the bookkeeping out on paper first; the mismatch
  between "shift the start" and "shift the domain" is the likely source of
  a silently wrong statement. `etime_shift_box` / `vshift_path_law` are
  already phrased for shifted paths — follow their convention.
- Also needed: `ess_inf_time M tau` (what `val_fn` collects) vs the essinf
  of the capped exit time `etime T A` (what `vshift` collects). For a
  market of the class, `tau ≤` the path's exit time from open `A ⊇ K`
  a.e., so `ess_inf_time M tau ≤` the vshift value; write this against the
  `ess_inf_time_*` helpers in `Value_Function.thy`.

Deliverable: `val_fn ≤` the law supremum (one half of the identification).
Combined with `vshift_sup_usc_mkt`: `val_fn` is dominated by an usc
function that EQUALS it once N3 closes.

### N3 — OPENED 2026-08-03 (commit 39e9807); the hard core remains

Done: closure laws inherit start and confinement.
`Section_2_Usc.confined_paths` is closed in the path topology
(`closedin_confined_paths`); members carry full mass on it
(`mkt_path_laws_confined`); the closed-set Portmanteau pushes it to every
closure point (`mkt_law_closure_confined`, AE form
`mkt_law_closure_confined_AE`).  Also the N2 domination is now
hypothesis-free: `witness_value_le_ball_v` + `witness_value_le_law_sup_ball`
(any `T ≥ ball_v r k x0`).

Done (commit 8faef17, 2026-08-03): the integrated MARTINGALE identity and
its passage to the closure.  `rclamp` (clamped increments, with
`rclamp_bound/rclamp_id/rclamp_cont`); witness paths live in `cball 0 r`
(`mkt_law_witness_bound`), so the clamp is invisible on members;
`martingale_bounded_test` is the cond_exp pull-out core (`Z`
`F s`-measurable bounded, `Y` martingale ⟹ `E[Z·Y_t] = E[Z·Y_s]`);
`martingale_test_functional_cont` gives continuity of
`λf. rclamp c (f t $ i − f s $ i) * h (restrict f {0..s})` on path space.
Members satisfy `(LINT f|Q. rclamp (2r) (f t $ i − f s $ i) *
h (restrict f {0..s})) = 0` (`mkt_path_laws_martingale_test`) and every
closure point inherits it (`mkt_law_closure_martingale_test`, via the
bounded-continuous integral clause of `weak_conv_on_def` +
`LIMSEQ_unique`) — i.e. step 1 (martingale part) and step 2 below are
DISCHARGED for the drift identity.

Done (commit c93e615, 2026-08-03): the COVARIATION upper bound and its
passage to the closure.  `witness_compensator_increment_bounds` squeezes
the `coord_Z` compensator increment into `[0, L·(t−s)]` a.e. (psd +
eigenvalue upper bound give `0 ≤ acov $ i $ i ≤ L` before the horizon,
the witness kills `acov` after it); `coord_sq_bounded_test` is the
market-level core: `E[Z·(X_t$i − X_s$i)²] = E[Z·(A_t − A_s)]` via
`martingale_bounded_test` at `coord_Z` plus the vanishing cross term.
Members satisfy `∫ (rclamp (2r) (f t $ i − f s $ i))² · h(restrict f
{0..s}) dQ ≤ L(t−s) · ∫ h(restrict f {0..s}) dQ` for nonnegative bounded
continuous past-measurable `h` (`mkt_path_laws_covariation_test`), every
closure point inherits it (`mkt_law_closure_covariation_test`, via the
integral clause of weak convergence + `LIMSEQ_le`), and the matching
lower bound is pointwise trivial (`covariation_test_nonneg`).
Continuity plumbing: `past_test_functional_cont`,
`covariation_test_functional_cont`.

NOTE the deliberate scope cut: the LOWER covariation constraint from
`eigen_lb` (sufficient volatility, `trace acov ≥ n − k` before the
horizon) is NOT yet stated at the law level — its natural integrated
form involves the horizon `min(t, τ)`, which is not a continuous path
functional; how to encode it (via the path's exit time from the closed
confinement set, or only in the canonical-market step) is entangled with
(b) below and should be decided together with it.

Done (commit 992ed8c, 2026-08-03): the PAPER-CLASS value function and
its usc majorant.  `stopped_market` (the witness predicate minus its
path-law clause; `mkt_law_witness_iff` relates them) captures the
paper's class (1.7) — the process stopped at its horizon, `acov` killed
after it, diag entries pathwise integrable.  `stopped_exit_vals` /
`stopped_val_fn` form its value function; `stopped_val_fn_le_law_sup`
lifts the per-witness domination through `Sup_least`:

    K ⊆ cball 0 r, x0 ∈ K, open A with A ∩ K = {}, T ≥ ball_v r k x0 ⟹
    stopped_val_fn k L K x0
      ≤ ennreal (Sup (vshift T A x0 ` mkt_law_closure k L (cball 0 (2r)) 0 T))

and the RHS is usc in x0 by `vshift_sup_usc_mkt`.  Also
`stopped_val_fn_le_val_fn` (index inclusion) and
`stopped_exit_vals_nonempty` (the immediate-stop market).

RESOLVED SCOPE for item (c): the bare-locale `val_fn` vs the paper class.
Aligning them is Doob's optional stopping applied to every class market;
the repo's `Optional_Sampling.optional_stopping` +
`Stopped_Adaptedness.stopped_adapted_of_cont` exist and fit, BUT they
require domination of the UNSTOPPED process on bounded time intervals
(an integrable envelope `D u`), and the bare locale controls `X` only up
to `tau` (`X_in_K`) — beyond the horizon nothing is integrable-bounded.
So `val_fn = stopped_val_fn` is not provable from the locale as stated;
either (i) treat `stopped_val_fn` as THE value function of the paper
(faithful to (1.7), recommended), or (ii) add a post-horizon
integrability axiom to the locale and run optional stopping.  Downstream
work (DPP, viscosity clauses) should consume `stopped_val_fn`.

Done (commit c975f4e, 2026-08-03): the MONOTONE-CLASS step of the
canonical-market construction.  `metric_measure_eqI_bounded_cts`: a
finite Borel measure on a metric space is determined by integrals of
bounded continuous functions (constant-sequence Portmanteau in both
directions + `measure_eqI_generator_eq` over the closed-set generator
`sets_borel_of_closed`).  `mkt_law_closure_martingale_event`: for a
closure point `Λ` and ANY Borel event `B` of the s-path space,
`∫ rclamp (2r) (f t $ i − f s $ i) · 1_B(restrict f {0..s}) dΛ = 0` —
the canonical coordinate process is a martingale under `Λ` w.r.t. its
natural filtration, in integrated clamped form.  Proof pattern (reuse
it for the covariation upgrade): split the increment into `gp/gm`
(positive/negative parts), push both through the restriction map as
`distr (density Λ ·)` image measures; the continuous-test identity
makes the two image measures agree on bounded continuous functions,
hence they are EQUAL.

Done (commit e74b4fd, 2026-08-03): the event-level COVARIATION upper
bound.  `metric_measure_mono_bounded_cts` is the one-sided companion of
the uniqueness lemma: domination on continuous `[0,1]`-valued tests
gives domination on every Borel set — closed sets via the Urysohn
sandwich (`Urysohn_lemma_uniform`, open `1/(m+1)`-neighbourhoods
decreasing to the closed set, continuity from above), general sets via
`finite_measure.inner_regular'` (AFP Riesz_Representation, reachable
through the Lévy–Prokhorov imports).  `mkt_law_closure_covariation_event`:
`∫ (rclamp (2r)(f t $ i − f s $ i))² · 1_B(restrict f {0..s}) dΛ ≤
L(t−s) · ∫ 1_B(restrict f {0..s}) dΛ` for every past Borel event `B`.
With `mkt_law_closure_martingale_event`, the canonical process under a
closure law is a martingale (in integrated clamped form) whose squared
coordinate increments grow conditionally at most `L·(t−s)` — the two
integrated inputs the `acov`-differentiation step consumes.

Done (commit 6b74fef, 2026-08-04): CLAUSE (1) PACKAGED, law-level form.
`clause_one_law_level` (Section_2_Usc): for `K ⊆ cball 0 r`, open `A`
disjoint from `K`, `T ≥ r²/(n−k)` (uniform over `K` by `ball_v_le`),
the law-level value function `w x = Sup (vshift T A x ` mkt_law_closure
k L (cball 0 (2r)) 0 T)` is usc (`clause_one_usc`) and dominates the
paper-class value function on `K` (`clause_one_dom`:
`stopped_val_fn k L K x ≤ ennreal (w x)`).  This is the single theorem
downstream sections should cite for clause (1) until/unless the
canonical market closes the `w = stopped_val_fn`-sup gap.

Done (commit 5322748, 2026-08-04): the UNCLAMPED event-level identities.
For closed `K ⊆ cball 0 r`, closure laws are supported on confined
paths, so the clamp is the identity a.e. and

    mkt_law_closure_increment_event:
      ∫ (f t $ i − f s $ i) · 1_B(restrict f {0..s}) dΛ = 0
    mkt_law_closure_sq_increment_event:
      ∫ (f t $ i − f s $ i)² · 1_B(…) dΛ ≤ L(t−s) · ∫ 1_B(…) dΛ

for every past Borel event `B` — the two integrated inputs of the
canonical-market construction in their FINAL form: raw increments, full
past σ-algebra, no clamp.

Still open, in order of attack: (a) the law-level form of the LOWER
(trace / `eigen_lb`) constraint, see the note above; (b) the rest of
the canonical-market construction — `acov` by differentiation of the
compensator (Lebesgue differentiation — the hard analytic core), and
the natural filtration/exit-time packaging into a
`sufficiently_volatile_market` instance on path space; OR the
author-level decision to restate clause (1) at the law level, under
which clause (1) is COMPLETE as `vshift_sup_usc_mkt` +
`stopped_val_fn_le_law_sup` and the canonical market is only needed for
"the closure adds no value".

#### N3 as originally scoped

Goal: for `Λ ∈ mkt_law_closure`, `vshift T A x Λ ≤ Sup` over the base
family; then the closure supremum equals the base supremum, and with N2 the
law-level usc function IS `enn2real ∘ val_fn`.

Do not believe shortcuts through usc of `vshift` in the law argument: usc
gives `vshift(Λ) ≥ limsup vshift(Qₘ)` — the WRONG direction.

The honest route is LR's: an admissible limit law is itself the law of a
market — the CANONICAL one on path space. Sub-steps:

1. Every `Q ∈ mkt_path_laws` satisfies the INTEGRATED admissibility
   identities, written against bounded continuous `𝔉_s`-measurable test
   functions `g`: `E_Q[(ω_t − ω_s) g] = 0`, and for symmetric `M` the
   covariation inequalities `E_Q[tr(M(ω_t−ω_s)(ω_t−ω_s)ᵀ) g] ⋚
   (t−s)·h_S(M)·E_Q[g]` in the appropriate directions. Derive from
   `coord_Z_martingale` / `Stopped_Localization.stopped_covariation`-style
   conditional identities.
2. Pass them to weak limits. Confinement makes every functional bounded —
   try plain weak convergence first (`weak_conv_on_def`'s integral clause);
   fall back to the RQ-A UI toolkit (§2.4) only if genuinely needed.
3. From the integrated identities on a limit law `Λ`, build the canonical
   market: canonical process, natural filtration; martingale property by a
   monotone-class/functional-approximation argument (continuous test
   functions determine conditional expectations — real but standard);
   `acov` by DIFFERENTIATION of the quadratic-variation compensator — the
   Lebesgue-differentiation step LR do. This is the hard core, has no repo
   infrastructure yet, and should be PROTOTYPED before committing to the
   rest.
4. Alternative worth deciding FIRST, with the author: can clause (1) and
   the downstream §3 arguments be stated for the LAW-level value function
   directly, bypassing `val_fn`? If the sub/supersolution proofs only ever
   consume the DPP and `v > 0`, the identification may be deferrable for
   the whole existence half — that would demote step 3 from the critical
   path.

### N4. Example 3.1 / clause (3) (RQ-C; ~2,000–4,000 lines, HIGH risk)

Eq. (3.11): `dX = a(X)^{1/2} dW`, `a(y) = I − yyᵀ/|y|²`, giving the
DETERMINISTIC radius `|X(t)|² = |x|² + (n−k)t`, hence
`essinf τ = (r²−|x|²)/(n−k) > 0`. Route to prototype: discrete
approximation (`Random_Walk_Market.thy`, `Relative_Arbitrage_Discrete.thy`,
`Path_Tightness.projective_limit_of_consistent_path_laws`); the covariation
constraint passes to the limit by the RQ-A toolkit; the radius identity is
a closed path condition and survives weak limits directly. Falsify cheaply
before building.

**SCOPING RESULT (2026-08-04), the cheap route for `n − k = 1`:** the
Example 3.1 process admits an EXPLICIT representation with no SDE
theory.  For `x ≠ 0` in the plane (prototype `n = 2`, `k = 1`):

    X_t = √(|x|² + t) · (cos(W_{c(t)} + φ₀), sin(W_{c(t)} + φ₀)),
    c(t) = ln(1 + t/|x|²),  (cos φ₀, sin φ₀) = x/|x|.

Both the martingale property and the compensated-square identities
follow from GAUSSIAN CONDITIONAL TRIGONOMETRIC EXPECTATIONS:
`E[cos(a·W_{c(t)} + b) | F_{c(s)}] = cos(a·W_{c(s)} + b)·e^{−a²(c(t)−c(s))/2}`,
and `R(t)·e^{−(c(t))/2} = |x|` is constant — the drift cancels
identically.  The covariance works out to `a(X_t) = I − X Xᵀ/|X|²`
(trace 1 = n − k), the radius is deterministic, and with the constant
horizon `τ ≡ r² − |x|²` the market lies in the (stopped) class with
`ess_inf_time = ennreal (r² − |x|²) = ennreal (ball_v r 1 x)` —
matching `stopped_val_fn_le_ball_v`, hence `stopped_val_fn = ball_v` at
such `x`.  For general `k < n` the same construction embedded in an
`(n−k+1)`-dimensional coordinate subspace needs SPHERICAL Brownian
motion for `n − k ≥ 2` — that part stays on the discrete route.

Ingredient inventory (all in `Brownian_Market.thy` except the last):
past/increment independence (`bm_paths_past_increment_indep`, the
"Increments are independent of the natural filtration" section),
Gaussian moments (`gauss_measure_mean`, `gauss_measure_snd_moment`);
MISSING: the Gaussian trig integral `∫ cos(a·ξ) dgauss(τ) = e^{−a²τ/2}`
(derive from HOL-Probability's normal characteristic function or by
differentiating under the integral) and its conditional form for
bounded `g(increment)·past` factorizations.  First brick: a
`bm_increment_cond_exp` lemma — for bounded measurable `g`,
`AE ω. cond_exp M (F s) (λω. g (W_t ω − W_s ω)) ω = ∫ g dgauss(t−s)` —
then the trig instances.

### N5. The weak DPP (RQ-B; ~1,500–3,000 lines, HIGH risk)

Bouchard–Touzi's weak DPP avoids measurable selection by replacing `v` with
test functions — exactly the form the viscosity proofs consume. Read BT09
and arXiv:1105.0745 against Definition 3.1's needs BEFORE formalising
anything: this is a stochastic-target problem with an essinf objective and
the fit is unverified. Unblocks clause (2) together with N4.

### Fallback

If N3 step 3 and N4 both look infeasible, the bounded alternative target is
the rest of Section 4 (Theorem 4.2(b), 4.3, Prop 4.1 — 3,000–7,000 lines,
reusing the Crandall–Ishii investment).

---

## 4. Working notes for the next agent

- **Verify with PIDE MCP, not batch builds** (user instruction). The loop
  is: edit → `get_progress`/`get_state`; `commands_failed = 0` at 100% IS
  verification. Both import branches (Value_Function and
  Path_Tightness_Market) can be held simultaneously; the first load after a
  server restart takes a couple of minutes. If a theory sits in "queued for
  loading" forever, the server is wedged — ask the user for a restart; do
  not silently fall back to long builds. Treat any
  `still_running_possibly_nonterminating` flag as a stop condition, even at
  `timing_ms 1`.
- **Proof-engineering traps specific to this layer** (each cost a round-trip
  this session): eliminating a multi-`∃` whose conjuncts contain `∀`/`AE`
  with `obtain … by blast` diverges or fails — keep set-comprehension
  bodies ATOMIC (that is what `mkt_law_witness` is for) and do choice by
  iterated `SOME` + `someI_ex`; instantiate multi-parameter theorems with
  explicit `where`-pins for every function argument (bare `OF` mangles them
  by higher-order unification); when a lemma's conclusion is literally the
  goal, use `unfolding defs by (rule lemma[OF …])`, never
  eliminate-and-reintroduce; type-annotate every statement-level function
  variable (`fixes τ :: "nat ⇒ …"`) — an under-constrained one fails far
  away, or worse, gets masked by a stale PIDE state.
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
