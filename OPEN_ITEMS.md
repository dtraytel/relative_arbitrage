# Items against the paper

No item is open.  Section 0 below records the `P_x` bridge, which was the last
one and is now closed; sections 1 and 2 record two further items, also closed.
`Statement/Theorem_1_1_Statement.thy` states all five clauses of Theorem 1.1 in
the paper's own terms.  See `NOTES_FOR_AUTHORS.md` for the differences that
never were gaps.

---

## 0. The `P_x` bridge --- CLOSED 2026-08-14

### What was missing

`iexit_class k L x` is a set of laws of the PAIR `(X, <X>)` on
`C([0,inf), R^n x R^(nxn))`; the paper's `P_x` is a set of laws of `X` alone on
`C([0,inf), R^n)`, constrained through `d<X>(t)/dt`.  Theorem 1.1 is a statement
about the value function built from `P_x`; every clause we prove is about the
one built from `iexit_class`.  Until the two classes were identified, these were
different objects that shared a name.

The identification is: *the `X`-marginals of `iexit_class k L x` are exactly
`P_x`*.  All four obligations are discharged, in
`Relative_Arbitrage/Pathwise_Quadratic_Variation.thy` and `Relative_Arbitrage/Paper_Class_Equivalence.thy`:

| | |
|---|---|
| (a) `X` is a martingale for its OWN filtration, not the pair's | `iexit_class_X_own_filtration` |
| (b) the second coordinate really IS `<X>` | `qvmat_eq_A_sym`, `iexit_class_qvmat` |
| (c) `<X>` available as a MEASURABLE PATH FUNCTIONAL | `qvmat` / `qvmata` and their measurability |
| (d) the four clauses of `iexit_class` for the pushforwards | `iexit_class_marginal_in_xclass`, `xclass_lift_in_iexit_class` |

Headline results:

* `iexit_class_marginal_in_xclass` --- `ipath_law P (\t w. fst (w t))` lies in
  `xclass k L x` for every `P` in the pair class.
* `xclass_lift_in_iexit_class` --- `ipath_law Q (\t w. (w t, qvmata (4L) w t))`
  lies in `iexit_class k L x` for every `Q` in the paper's class.
* `iexit_val_eq_xval` --- the two value functions are equal, so every clause of
  Theorem 1.1 is a statement about the paper's own `v` of Eq. (1.6).

`Statement/Theorem_1_1_Statement.thy` states `xclass`, `xval` and the three
theorems above (`paper_class_marginal`, `paper_class_lift`,
`paper_value_function_agrees`).

### The idea that made it cheap

Do NOT construct `<X>` by Doob--Meyer.  DEFINE it as the pathwise `limsup` of
dyadic sums.  Each finite sum is a Borel function of the path, so measurability
is free; and the functional is `F^X`-adapted, so `F^(X,QV) = F^X` and the
filtration worry collapses.

And do NOT use the classical `E[max_k |dX_k|^2 <X>]` argument.  Here `A` is
Lipschitz and the fourth moment is already bounded, and those two facts give the
convergence with a RATE (`qv_dyadic_L2`: `18 C^2 T^2 / 2^n`).  The rate is
summable, so Chebyshev plus Borel--Cantelli give a.s. convergence of the FULL
dyadic sequence --- no subsequence, which is what makes the `limsup` definition
legitimate.

### What T1--T4 delivered, and where the original plan was wrong

* **T1** --- `qv_dyadic_L2`, orthogonality off `Quadratic_Variation`.
* **T2** --- `qvp` and the left-regularisation `qvps`.  The plan said "extend by
  continuity of both sides"; that is impossible, since `t |-> qvp w t` has no
  continuity off the convergence event.  `qvps w t = SUP {qvp w q : q rational,
  0 <= q < t}` instead, and the Lipschitz rate on `A` makes that supremum
  exactly `A t`.  Bonus: it uses only times `< t`, so it is adapted.
* **T3** --- `qvmat` and `qvmat_eq_A_sym`, by polarisation.  There is NO `outerp`
  bookkeeping: the matrix locale states the compensator relation entrywise.
* **T4** --- `qvps_eq_A`.

Two hypotheses the plan never named, both needed: the increments of `A` are
positive semidefinite (this is what makes the polarised scalar compensators
nondecreasing), and `X` is uniformly bounded.  **The boundedness one is FALSE in
the class**, and gated BOTH inclusions; it is removed by localisation
(`qvps_eq_A_stopped` -> `qvps_eq_A_localised` -> `qvmat_eq_A_localised`) along
`tau_R = etime (Suc R) {y. B + Suc R <= norm y} X`.

### The one design decision that had to be revisited

The pushforward into the pair space needs the covariation functional to be a
CONTINUOUS path for EVERY path, so a cut-down version is unavoidable.  The
first version cut at the GLOBAL good event --- `qvp_good C w`, "the rational-time
data of `qvp w` is nondecreasing, `C`-Lipschitz and vanishes at 0".  That is
continuous for every path, and Borel, but it is
**not adapted**: the good event reads the path at all times.  Adaptedness is
exactly the `pull` hypothesis of `martingale_distr`, which BOTH inclusions go
through, so the global cut is unusable there.

The repair is to cut at a TIME rather than globally.  `qvpc C w t q` keeps the
value `qvp w q` only when the rational data BELOW `q` is already nondecreasing
and `C`-Lipschitz (`qvp_goodupto`), and `qvsa C w t` is the supremum of the kept
values strictly below `t`.  It reads only times `< t`, so it is adapted; it is
monotone and `C`-Lipschitz by an epsilon argument comparing a kept value beyond
`s` with one kept just below `s`, hence continuous for EVERY path; and on the
good event nothing is discarded, so `qvsa = qvps` there.  `qvmata` polarises it.
`qvp_good` survives as the statement of that event; the global cut-down
functional itself was deleted once it was clear it could not be used.

The constant is `4L`, not `L`: polarisation at `e_i +- e_j` turns an
`L`-Lipschitz matrix compensator into a `4L`-Lipschitz scalar one.

### Two further things worth knowing

1. Transferring an almost-everywhere statement along `distr` needs the
   exceptional set MEASURABLE, and the constraint clause quantifies over all
   real pairs `s < t`.  That is a countable condition once the compensator is
   continuous in `t` --- which `qvmata` is for every path, and on the pair path
   space every point is a continuous path anyway.  `diffquot_all_of_rational`
   and `closed_sconstraint` do the reduction.
2. The compensated martingale clause is, in both directions, a MODIFICATION of
   the one the source class supplies.  `martingale_of_modification_gen` is
   real-valued, so it is applied entrywise and reassembled by
   `martingale_matI`; adaptedness of the modification is where `qvmata` earns
   its keep a second time.

### Placement

`fourth_moment_bound_bounded` lives in `Path_Space_Tightness.Increment_Moments`,
which is ABOVE `Martingale_Sampling` --- so T1--T4 CANNOT go in
`Martingale_Sampling` where `qvar` lives.  They went into
`Relative_Arbitrage/Pathwise_Quadratic_Variation.thy`, which deliberately does NOT import
`Exit_Class`; T5--T7 need `iexit_class` and went into
`Relative_Arbitrage/Paper_Class_Equivalence.thy` after `Exit_Class_Infinite`.

The estimate was 2000--4000 lines; the two theories together are about 4000.

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
