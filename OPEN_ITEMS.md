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
| (b) the second coordinate really IS `<X>` | open |
| (c) `<X>` available as a MEASURABLE PATH FUNCTIONAL, to build a pair law from a `P_x`-law | open |
| (d) the four clauses of `iexit_class` for that pushforward | routine once (c) holds |

(b) and (c) are not two problems.  They are the same missing theorem, and it
gates BOTH inclusions --- so the honest description is not "one direction is
missing" but "one theorem is missing, and it is needed twice".

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

**T1 --- scalar convergence with a rate.**  As above.  Hypothesis bundle is
deliberately the same as `fourth_moment_bound_bounded`'s so the two compose.
The one real step is the orthogonality of martingale differences; the AFP
conditional-expectation API and the tower patterns already used in
`Exit_Class_DPP` are the model.

**T2 --- the path functional.**  `qvp :: (real => real^'n) => real => real^'n^'n`,
defined as a `limsup` of dyadic sums; Borel by composition of evaluations.
Prove `qvp` is `F^X`-adapted (the grid of `[0,t]` uses only times `<= t`).

**T3 --- matrix version by polarisation.**  Do NOT redo T1 for matrices.  Use
`<X_i,X_j> = (<X_i+X_j> - <X_i-X_j>)/4`, so the scalar theory is applied
`n(n+1)/2` times.  Watch the `outerp` bookkeeping.

**T4 --- the process, all times at once.**  T1 gives `qvp t = A t` a.s. for each
fixed `t`.  Intersect over rational `t` and extend by continuity of both sides
--- the `rat:` pattern in `Exit_Class_DPP` (the `AE ... ALL p:Q. ALL q:Q` step)
is the precedent.

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
* `xclass -> iexit_class`: push forward along `w |-> (w, qvp w)`.  Measurable by
  T2; `qvp = A` a.s. by T4, so all four clauses transfer.  The martingale clause
  is where `F^(X,qvp) = F^X` earns its keep.

**T7 --- the value functions.**  `iexit_val = xval`, hence every clause of
Theorem 1.1 is a statement about the paper's `v`.  Then rewrite the pair-law
caveat in `Statement/Theorem_1_1_Statement.thy` (the bullet under
`iexit_class_def`) from "not formalised" to the theorem name.

### Placement and cost

`fourth_moment_bound_bounded` lives in `Path_Space_Tightness.Increment_Moments`,
which is ABOVE `Martingale_Sampling` --- so T1--T4 CANNOT go in
`Martingale_Sampling` where `qvar` lives.  Put them in a new
`Path_Space_Tightness/Continuous_QV.thy` importing `Increment_Moments`, which
transitively has `qvar_compensates_sampled`, `cond_exp_increment_sq`, Doob and
the dyadic grids of `horizon_sq_int_martingale`.  T5--T7 need `iexit_class`, so
they go in a new `Relative_Arbitrage/Px_Bridge.thy` after `Exit_Class_Infinite`.

Both ROOTs change, so both session heaps are invalidated: expect a full rebuild
and a server restart before any of it can be checked.  Do the ROOT edits FIRST,
in one go, and restart once --- PIDE snapshots ROOT at startup.

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
