# Items against the paper

One item is OPEN: the identification of the formal class with the paper's
`P_x` (section 0 below).  Two further items, recorded in sections 1 and 2, are
closed.  `Statement/Theorem_1_1_Statement.thy` states all five clauses of
Theorem 1.1 in the paper's own terms.  See `NOTES_FOR_AUTHORS.md` for the
differences that never were gaps.

---

## 0. The `P_x` bridge --- OPEN, plan below

### What is missing, precisely

`iexit_class k L x` is a set of laws of the PAIR `(X, <X>)` on
`C([0,inf), R^n x R^(nxn))`; the paper's `P_x` is a set of laws of `X` alone on
`C([0,inf), R^n)`, constrained through `d<X>(t)/dt`.  Theorem 1.1 is a statement
about the value function built from `P_x`; every clause we prove is about the
one built from `iexit_class`.  Until the two classes are identified, these are
different objects that share a name.

The identification is: *the `X`-marginals of `iexit_class k L x` are exactly
`P_x`*.  Four obligations:

| | |
|---|---|
| (a) `X` is a martingale for its OWN filtration, not the pair's | DONE, `iexit_class_X_own_filtration` |
| (b) the second coordinate really IS `<X>` | DONE, `qvmat_eq_A_sym` |
| (c) `<X>` available as a MEASURABLE PATH FUNCTIONAL, to build a pair law from a `P_x`-law | DONE, `qvmat` / `qvmat_measurable` |
| (d) the four clauses of `iexit_class` for that pushforward | open (T5--T7) |

(b) and (c) were not two problems.  They were the same missing theorem, gating
BOTH inclusions --- so the honest description was not "one direction is missing"
but "one theorem is missing, and it is needed twice".  That theorem is now
proved (T1--T4, `Relative_Arbitrage/Continuous_QV.thy`); what is left of the
bridge is the class-level bookkeeping (d), i.e. T5--T7 below.

Nothing to borrow: the AFP has `Martingales` (conditional expectation,
general-index martingales) and `Kolmogorov_Chentsov` (modifications), but no
continuous-time quadratic variation, and this repo's `qvar` is
`(nat => 'a => real)` --- discrete-time and scalar.

### The idea that makes it cheap

Do NOT construct `<X>` by Doob--Meyer.  DEFINE it as the pathwise `limsup` of
dyadic sums.  Two payoffs:

* Each finite sum is a Borel function of the path, so measurability is free ---
  which is exactly obligation (c).
* The functional is `F^X`-adapted, so `F^(X,QV) = F^X` and the filtration
  worry collapses.

And do NOT use the classical `E[max_k |dX_k|^2 <X>]` argument, which needs a
delicate uniform-continuity estimate.  In THIS setting `A` is Lipschitz and the
fourth moment is already bounded, and those two facts give the convergence with
a RATE by a three-line computation --- see T1.

### The load-bearing theorem (T1)

Let `X` be a square-integrable martingale, `A` continuous adapted with
`A 0 = 0`, `X^2 - A` a martingale, and `0 <= A v - A u <= C * (v - u)`.  Write
`S_n` for the sum of squared increments over the dyadic grid of `[0,u]`.  Put
`M_k = (dX_k)^2 - dA_k`.  Then:

1. `M_k` are MARTINGALE DIFFERENCES: `E[M_k | F_(t_k)] = 0`.  This is
   `Sampled_Quadratic_Variation.cond_exp_increment_sq` combined with the
   compensator relation --- and it is precisely the `covA` hypothesis that
   `Increment_Moments.fourth_moment_bound_bounded` already takes.
2. Hence the cross terms vanish and
   `E[(S_n - (A_u - A_0))^2] = sum_k E[M_k^2] <= 2 sum_k (E[(dX_k)^4] + E[(dA_k)^2])`.
3. `E[(dX_k)^4] <= 8 C^2 (dt)^2` by `fourth_moment_bound_bounded` (Eq. (2.7));
   `E[(dA_k)^2] <= C^2 (dt)^2` by the Lipschitz bound.
4. With `2^n` terms of width `u/2^n`: `E[(S_n - (A_u - A_0))^2] <= 18 C^2 u^2 / 2^n`.

The RATE is the point.  It is summable, so Chebyshev plus Borel--Cantelli give
a.s. convergence of the FULL dyadic sequence --- no subsequence, and therefore
`limsup S_n` is the limit a.s., which is what makes the `limsup` definition in
T2 legitimate.  Note also that path continuity is not needed for T1 itself.

### Work items

**T1--T4 are DONE**, in `Relative_Arbitrage/Continuous_QV.thy`.  What they
deliver, and where the plan below was wrong:

* **T1** --- `qv_dyadic_L2`: `E[(S_n - A_T)^2] <= 18 C^2 T^2 / 2^n`, exactly as
  planned.  The orthogonality step is `qv_orthogonality`, off
  `Quadratic_Variation.expectation_sq_qvar`; `compensator_cond_increment` is the
  bridge from "`X^2 - A` is a martingale" to the `covA` hypothesis that
  `fourth_moment_bound_bounded` takes.  The AFP has no `martingale_diff`, but it
  does have `martingale.add`/`.diff`/`.scaleR_const` --- locale-bound, so they
  are invisible to `find_theorems` on the predicate.
* **T2** --- `qvp` and `qvps`, plus `qvp_measurable`/`qvps_measurable`.  Scalar,
  not `real^'n^'n`: the matrix functional is assembled in T3 instead, so the
  scalar theory never has to know about matrices.
* **T3** --- `qvmat` and `qvmat_eq_A`.  The polarisation is applied to
  `X_i + c X_j` for `c = 1, -1` via the locale interpretation `polarised`.  There
  is NO `outerp` bookkeeping: the matrix locale states the compensator relation
  entrywise (`X_i X_j - A_ij` a martingale), which is what the class supplies
  anyway and avoids importing `Exit_Class`.  `qvmat_eq_A` gives the SYMMETRIC
  PART `(A_ij + A_ji)/2`; `qvmat_eq_A_sym` specialises to symmetric `A`.
* **T4** --- `qvps_eq_A`.  The plan said "extend by continuity of both sides";
  that is not what happens and could not be, since `t |-> qvp w t` has no
  continuity off the convergence event.  Instead `qvps` is DEFINED as the
  left-regularisation `SUP {qvp w q | q rational, 0 <= q < t}`, and the Lipschitz
  rate on `A` makes that supremum exactly `A t` --- no continuity argument, and
  no special case at `t = 0`, where the index set is empty and both sides vanish.
  Bonus: the supremum uses only times `< t`, so adaptedness is immediate.

Two hypotheses the plan did not name, both needed: the increments of `A` are
positive semidefinite (this is what makes the polarised scalar compensators
nondecreasing — polarisation at `e_i +- e_j` is exactly a quadratic form), and
`X` is uniformly bounded (this discharges every integrability side condition, so
the locale states none of them).

**The boundedness one is FALSE in the class**, and that turned out to gate T5–T7.
It is now removed, in `Relative_Arbitrage/Px_Bridge.thy`:

* `qvps_eq_A_stopped` — the identification at one localisation level.
* `qvps_eq_A_localised` — scalar, no uniform bound: an `L^2` continuous
  martingale with a Lipschitz compensator suffices.
* `qvmat_eq_A_localised` — the same for the matrix functional.

The route is `tau_R = etime (Suc R) {y. B + Suc R <= norm y} X`: stopping makes
the process bounded, `Stopped_Localization.stopped_martingale_L2` and
`stopped_compensated_square` carry the martingale and compensator properties
through unconditionally, `Exit_Time.etime_stopping_time` and
`etime_stays_in_cball` supply the stopping time and the bound, and the three
`qvp`/`qvps` congruences make stopping invisible to the functional below the
stopping time. Levels are indexed by naturals, so one countable intersection
serves all of them. Note the hypotheses are POINTWISE on `space M`, not a.e. —
that is what the stopping arguments need; `Stopped_Localization`'s
`restrict_full` package is the intended way to get there from an a.e. statement.

**T5 is DONE**: `xclass` and `xval` in `Relative_Arbitrage/Px_Bridge.thy`, with
the destructor lemmas `xclass_prob`/`_sets`/`_start`/`_martingale`/`_compensator`.
The shape is as planned below, so the design note is kept for the record.

**T5 --- the paper's class.**  Define

    xclass k L x = {Q. prob_space Q & sets Q = borel(ipath) & AE X 0 = x
                     & martingale Q (natural_filtration of X) 0 X
                     & (EX A. continuous, adapted, A 0 = 0,
                          X X^T - A a martingale,
                          ALL s<t. (A t - A s)/(t-s) : sconstraint k L)}

Phrasing the covariation EXISTENTIALLY is the modelling choice that makes both
inclusions fall out of T4, because such an `A` is forced to equal `<X>`, hence
`qvp`.  It is faithful: the paper's `d<X>/dt : S` says exactly that `<X>` is
such an `A`, and the compensator is unique up to indistinguishability.  Flag it
in the statement document as a stated choice, next to the Lipschitz-vs-a.e.
reading already recorded there.

**T6 --- the two inclusions.**
* `iexit_class -> xclass`: take `A` = second coordinate; (a) is already proved.
* `xclass -> iexit_class`: push forward along `w |-> (w, qvmat w)`.  Measurable
  by `qvmat_measurable`; `qvmat = A` a.s. by `qvmat_eq_A_sym`, so all four
  clauses transfer.  The martingale clause is where `F^(X,qvmat) = F^X` earns
  its keep.

  Both bullets need `qvmat_eq_A_localised`, not just the second: under the
  pushforward the compensator has to be recovered as `qvmat w`, a functional of
  the path, because the second coordinate is not one. So T6 is now unblocked in
  both directions, and what is left is the pushforward bookkeeping.

  **The recipe, with the machinery identified.** For the `iexit_class -> xclass`
  direction, `Q = ipath_law P (\t w. fst (w t))`, i.e. `distr P ipath_space phi`
  with `phi = \w. restrict (\t. fst (w t)) {0..}`:

  * `phi` is measurable by `Path_Space_Infinite.ipathify_measurable` (its two
    hypotheses are the componentwise measurability from the class martingale and
    path continuity, the latter free since `space P = ipath`).
  * The martingale clause is `Exit_Class_Compactness.martingale_distr`, whose
    `pull` hypothesis is discharged by `natural_filtration_pull` (proved, in
    `Px_Bridge.thy`). `martingale_pair_law` is NOT reusable here — it is
    specialised to `pair_law_of` on the capped pair path metric.
  * The compensator for `Q` must be `qvmat`, supplied by
    `qvmat_eq_A_localised`.

  **The one piece of plumbing this needs.** `qvmat_eq_A_localised` takes its
  hypotheses POINTWISE on `space M`, but the class states the start value, `A 0 =
  0` and the difference-quotient constraint only almost everywhere. Move to a
  full-measure `G` and use the `restrict_full` locale of
  `Stopped_Localization` (`prob_space_restrict_full`, `martingale_restrict_full`,
  `distr_restrict_full`, `integrable_restrict_full`), then transfer the
  conclusion back — `AE` in `restrict_space P G` gives `AE` in `P` because `G` is
  full. This is the intended use of that package and is why it exists.

  **Obligation (b) is now DONE**: `iexit_class_qvmat` in `Px_Bridge.thy` says
  that for a member of the pair class, `qvmat` of the first coordinate equals
  the second at every time, a.s. That is the theorem both inclusions consume.

  **The continuous-version construction is needed by BOTH directions**, not just
  the pushforward into the pair space as stated below. Reason: transferring an
  a.e. statement along `distr` (`AE_distr_iff`) needs the exceptional set to be
  MEASURABLE, and `xclass`'s difference-quotient clause quantifies over all real
  pairs `s < t`. That is a countable condition only once `t |-> A t w` is known
  continuous — which `qvmat w` is not, for an arbitrary `w`. Restricting the
  clause to rational `s, t` does not help by itself, for the same reason.
  So build the continuous version FIRST; it unblocks the constraint clause of
  direction 1 as well as the pushforward of direction 2.

  One step here is NOT covered by T1--T4 and should be planned for: the pair
  space is `C([0,inf), R^n x R^(nxn))`, so the pushforward needs `qvmat w` to be
  a CONTINUOUS path for EVERY `w`, not merely almost every one.  `qvmat` is a
  supremum of limsups and is continuous only on the convergence event.  The fix
  is the usual one --- redefine it to `0` off the (measurable) set where
  `t |-> qvmat w t` is continuous, nondecreasing and vanishes at `0`; those
  conditions are countable intersections of Borel conditions over rational
  times, so the set is Borel and the redefinition keeps both measurability and
  the a.s. identification.

**T7 --- the value functions.**  `iexit_val = xval`, hence every clause of
Theorem 1.1 is a statement about the paper's `v`.  Then rewrite the pair-law
caveat in `Statement/Theorem_1_1_Statement.thy` (the bullet under
`iexit_class_def`) from "not formalised" to the theorem name.

### Placement and cost

`fourth_moment_bound_bounded` lives in `Path_Space_Tightness.Increment_Moments`,
which is ABOVE `Martingale_Sampling` --- so T1--T4 CANNOT go in
`Martingale_Sampling` where `qvar` lives.  They went into
`Relative_Arbitrage/Continuous_QV.thy`, importing only
`Path_Space_Tightness.Increment_Moments`, which transitively has
`qvar_compensates_sampled`, `cond_exp_increment_sq`, Doob and the dyadic grids
of `horizon_sq_int_martingale`.  Placing it in `Relative_Arbitrage` rather than
`Path_Space_Tightness` keeps the `Path_Space_Tightness` heap valid and leaves it
editable under `-R Relative_Arbitrage`; it costs nothing, because nothing below
`Relative_Arbitrage` needs it.  It deliberately does NOT import `Exit_Class`,
which would drag most of the session into every PIDE load for the sake of
`outerp` and `martingale_vec_nth`; the entrywise phrasing avoids both.

T5--T7 need `iexit_class`, so they go in a new
`Relative_Arbitrage/Px_Bridge.thy` after `Exit_Class_Infinite`.  Only the
`Relative_Arbitrage` ROOT changes, and only that heap is invalidated.

Estimate: 2000--4000 lines.  Treat the lower end sceptically; the W3 threading
in this same development was estimated at ~6 sites and turned out to be ~13
lemmas, and the shape was the same --- a clean core with more plumbing around
it than expected.

### Risks, in the order they are likely to bite

1. The martingale-difference orthogonality in T1.  Everything else is arithmetic.
2. `F^(X,qvp) = F^X` in T6.  Intuitively immediate, fiddly in the API.
3. Polarisation bookkeeping in T3 against `outerp`.
4. The rational-intersection/continuity step in T4 --- routine but long.

### If it stalls

T1--T4 are worth having ALONE: they give the development a genuine
continuous-time quadratic variation with a convergence rate, which is
reusable and is the part with no AFP substitute.  T5--T7 are then bookkeeping.
Stopping after T4 leaves the repo strictly better off and the caveat in the
statement document still accurate.

---

## 1. The envelope: `real^'n` versus `K` --- CLOSED 2026-08-13

The paper's solutions are functions `u : K -> R` and its lower envelope `u_*`
is the liminf **within K**.  Here they are `real^'n => real` and `lsc_env`
takes the liminf over balls of `real^'n`.  Always `lsc_env u <= u_*`, with
equality at interior points of `K`, so the two differ exactly on
`K - interior K` --- which is where the boundary gate of clause (3) is read.

**Both directions of the gap were real.**  An earlier note here said clause (3)
was merely *stronger* than the paper's, because our gate `{lsc_env u < 0}`
contains the paper's `{u_* < 0}`.  That reasoning only looked at the gate.  It
misses that the FUNCTION being touched from below also changes: raising a
function on part of `K` makes it easier for a test function to touch it there,
so more test functions have to be checked, and the paper's clause (3) is in
fact the stronger of the two.  On the value function the two gates are both
empty (it is nonnegative), and the difference is entirely in the function ---
by Lemma 5.3 the cube with `k = 2` has `v > 0` on the open two-dimensional
faces, so its liminf within `K` is positive there while its liminf over balls
of `real^'n` is `0`.  Neither clause implied the other; the paper's had to be
proved.

**What closed it.**  `Operator_Envelopes` now carries the paper's envelope

    lsc_envK K u x = (SUP e:{0<..}. INF (u ` (ball x e Int K)))

and a bridge to `lsc_env`, so the machinery, which is all phrased in terms of
functions on `real^'n`, can be pointed at hypotheses that only speak about `K`.

* Clause (2b) and clause (3), where the envelope is a CONCLUSION, needed no
  extension.  The touching in the supersolution proof is global over `K` but
  the proof only ever uses it near the touching point, so the local form is the
  one really proved (`exit_val_supersol_lsc_local`).  Stated locally, the
  paper's envelope follows at once: the two envelopes agree at interior points,
  and a small enough ball around an interior point meets `K` only in interior
  points.
* Clause (4), where the envelope is a HYPOTHESIS on the competitor, needed an
  extension of `u : K -> R` to `real^'n`.  This is the delicate half, because
  the extension has to do two things that pull against each other: stay high
  enough off `K` not to lower the infimum over a ball (or the two envelopes
  differ), and stay low enough at `K - interior K` for upper semicontinuity to
  survive (or the comparison machinery does not apply).  Extending by the
  constant `sup_K u` --- the plan recorded here previously --- does the first
  and FAILS the second at every boundary point where `u < sup_K u`.
  What works is `Kext K u = usc_env (u o closest_point K)`: off `K` the value
  is a value of `u` at a point at most twice as far away, which is enough for
  the infimum, and it tends to `u z` as one approaches `z` in `K`, which is
  enough for semicontinuity; the outer `usc_env` repairs the one remaining
  failure, at points outside `K` where the projection jumps, without touching
  `K`.  Then `lsc_env (Kext K u) = lsc_envK K u` on `K` (`lsc_env_Kext`), and
  the whole of clause (4) transports.

Clause (4) is therefore now stated with every hypothesis about `K` alone: upper
semicontinuity relative to `K`, boundedness on `K`, and the paper's envelope.

## 2. Strictness in `L` --- CLOSED 2026-08-13

Clauses (2b), (3b) and (4) are now proved for every `1 <= L`, `L = 1`
included, and `Statement/Theorem_1_1_Statement.thy` states them that way.
What follows is the record of what the obstruction was and how it was removed;
nothing here is open.

**What was blocking.**  `Value_Function_Viscosity.feasible_strict_eigendata`
produced a margin `m > 0` with `lam u <= L - m` on the eigenbasis and
`1 + m <= lam u` on the top `n - k` of it, so that

    feasible k L p = {a. psd a & a *v p = 0 & eigen_lb a (n-k) & eigen_ub a L}

had room to be perturbed.  At `L = 1` the interval `[1 + m, L - m]` is empty:
`eigen_lb a (n-k)` puts the top `n - k` eigenvalues at `>= 1` and
`eigen_ub a 1` puts all of them at `<= 1`, so they are pinned to `1` exactly
and the witness sits on a corner of the feasible set.  This is the paper's own
step --- Case 1 of Section 3 modifies `a` so that
`lambda_(1)(a), ..., lambda_(n-k)(a)` lie in the OPEN interval `(1,L)`.  It is
also exactly the case Remark 1.1(c) singles out, the arrival time formulation
of the Ambrosio--Soner co-dimension mean curvature flow.

**Why the margin was there.**  Not for the witness itself: `a` is already
admissible for the class, since `feasible k L p` is contained in
`sconstraint k L`.  It was there for the FIELD.  The paper's covariance field
(3.24) has columns `S_i grad phi(y)` with `S_i` skew, so as `y` moves off the
touching point the frame leaves the eigenframe of `a` and the eigenvalues
drift by `O(|y - x|)`; the margin absorbs the drift.

**What removed it.**  A field of exact rotations.  Let `R(y)` carry the frozen
gradient `q = grad phi(x)` to the current gradient `grad phi(y)`, as the
product of two Householder reflections

    hrefl v = mat 1 - (2 / (v . v)) *R outer_prod v v
    rotm q w = hrefl (norm w *R q + norm q *R w) ** hrefl q

which is orthogonal for every `q` and `w` (unconditionally --- the degenerate
`v = 0` gives the identity, since division by zero is zero here), carries `q`
onto the ray through `w` whenever the two are not opposed, and is the identity
at `w = q`.  The field is `R(y) a R(y)^T`, and conjugation by an orthogonal
matrix moves neither the spectrum of `a` nor its membership of the feasible
set (`Operator_Envelopes.feasible_conj`, which was already there).  So

* it lies in `sconstraint k L` at every `y`, with no margin, hence at `L = 1`;
* it annihilates `grad phi(y)`, because `a` annihilates `q` and
  `R(y) q` is parallel to `grad phi(y)`;
* the trace the DPP reads, `trace (M ** R a R^T)`, is continuous in `y` and
  equals `trace (M ** a)` at `y = x`, so the trace margin comes from
  continuity at the touching point instead of from three explicit smallness
  estimates.

That is `rotSF_exists` (subsection "Exact rotations" of
`Value_Function_Viscosity`), and it carries no hypothesis on `L` at all.  The
two Case 1 arguments --- `exit_val_supersol_contradiction_case1` and its `_lsc`
twin --- consume it in place of the strict eigendata, and `1 < L` was then
weakened to `1 <= L` through the whole chain down to
`Statement/Theorem_1_1_Statement.thy`.

**Left over: nothing.**  The skew-field cluster the rotation replaced --- 29
entities, `skewv`, `skewfield`, `skewSF`, `skewfield_properties`,
`skewSF_package`, `perturbed_columns_*`, `small_radius_exists`,
`feasible_eigen_count`, `feasible_strict_eigendata` and their private helpers,
about 1600 lines --- was dead once the two Case 1 arguments stopped calling it,
and has been deleted.  The set was computed as a fixpoint (an entity is dead
when nothing live, in any theory of the repository, names it) and diffed
against the same computation on the previous commit, so exactly what the
rotation killed came out, and nothing else.  Note the file had 58 dead entities
BEFORE this change as well; those are untouched here.

**Still open, and a different question.**  Remark 1.1(c) also conjectures that
the value function does not depend on `L` when `K` is convex, and says the
authors could not show it.  Nothing here bears on that: `F` itself depends on
`L`, and what is proved above is that each `L >= 1` --- separately --- has its
value function characterised.
