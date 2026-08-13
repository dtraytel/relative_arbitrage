# Items against the paper --- both now closed

Nothing here is open.  This file is the record of the two places where the
formal statement and arXiv:2512.17702 did not line up, and of how each was
closed; `Statement/Theorem_1_1_Statement.thy` now states all five clauses of
Theorem 1.1 in the paper's own terms.  See `NOTES_FOR_AUTHORS.md` for the
differences that never were gaps.

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
