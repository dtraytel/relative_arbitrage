# Items against the paper

Refreshed 2026-10-14 for the session layout of `PLAN_RESTRUCTURING_3.md`
(phase 8). Session abbreviations: SMS, SemiC, SOVA, RAE
(`Relative_Arbitrage_Equation`), CTM, WM, CPS, PSO (`Path_Space_Operations`),
CCM (`Covariation_Constrained_Martingales`), RA (`Relative_Arbitrage`, the
paper session) and Statement (`Relative_Arbitrage_Statement`).

**Theorem 1.1: no item is open.** Section 0 below records the `P_x` bridge,
which was the last one and is now closed; sections 1 and 2 record two further
items, also closed. `Statement/Theorem_1_1_Statement.thy` states all five
clauses of Theorem 1.1 in the paper's own terms. See `NOTES_FOR_AUTHORS.md`
for the differences that never were gaps.

**The rest of the paper: two items are open**, both outside Theorem 1.1:
Section 5 (section 3 below) and Proposition 2.4 for `v` itself (section 4).
`Statement/Paper_Map.thy` lists every numbered item of the paper with its
formal counterpart and its deviations; it is the complete list, and this file
only records what is missing.

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
`P_x`*.  All four obligations are discharged. Since phase 7 they are proved
for an abstract constraint set `S` (closed, convex, of positive semidefinite
matrices with bounded entries), in CPS `Pathwise_Quadratic_Variation` and
`Adapted_Quadratic_Variation` and CCM `Covariation_Class_Marginals`; the
paper's statements, at `S = sconstraint k L`, are one-step instances in RA
`Exit_Class_Marginals`:

| | |
|---|---|
| (a) `X` is a martingale for its OWN filtration, not the pair's | inside `icovariation_class_marginal_in_xcovariation_class`, through `martingale_distr` (CTM `Martingale_Transfer`) |
| (b) the second coordinate really IS `<X>` | `qvmat_eq_A_sym` (CPS), `icovariation_class_qvmat` (CCM) |
| (c) `<X>` available as a MEASURABLE PATH FUNCTIONAL | `qvmat` / `qvmata` and their measurability (CPS) |
| (d) the four clauses of the class for the pushforwards | `icovariation_class_marginal_in_xcovariation_class`, `xcovariation_class_lift_in_icovariation_class` (CCM); `iexit_class_marginal_in_xclass`, `xclass_lift_in_iexit_class` (RA) |

Headline results:

* `iexit_class_marginal_in_xclass` --- `ipath_law P (\t w. fst (w t))` lies in
  `xclass k L x` for every `P` in the pair class.
* `xclass_lift_in_iexit_class` --- `ipath_law Q (\t w. (w t, qvmata (4L) w t))`
  lies in `iexit_class k L x` for every `Q` in the paper's class.
* `iexit_val_eq_xval` --- the two value functions are equal, so every clause of
  Theorem 1.1 is a statement about the paper's own `v` of Eq. (1.6).

`Statement/Theorem_1_1_Statement.thy` states Theorem 1.1 for `xval` over
`xclass` directly and displays both definitions; the three bridges above are
roots (`notes/review_3/roots.txt`) and reach the statement through RA
`Theorem_1_1` (`xval_eq_iexit_val`). The statement's earlier re-exports
`paper_class_marginal`, `paper_class_lift` and `paper_value_function_agrees`
are gone with that change.

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
   the one the source class supplies, so `martingale_cong_AE` carries it over
   directly, matrix-valued; adaptedness of the modification is where `qvmata`
   earns its keep a second time.

### Placement

At the time, `fourth_moment_bound_bounded` lived in
`Continuous_Path_Spaces.Increment_Moments`, so T1--T4 could not go into
`Continuous_Time_Martingales` beside `qvar`, and went into the paper session
together with T5--T7. The estimate was 2000--4000 lines; the two theories
together were about 4000.

Now: `fourth_moment_bound_bounded` is in CTM `Increment_Moments` (phase 5);
T1--T4 are CPS `Pathwise_Quadratic_Variation` (the pathwise functional, `qvp`,
`qvps`, `qvmat`) and `Adapted_Quadratic_Variation` (the adapted cut-down
`qvpc`, `qvsa`, `qvmata` and the localised identifications), advertised there
as quadratic variation as a path functional; T5--T7 are CCM
`Covariation_Class_Infinite` and `Covariation_Class_Marginals` for an abstract
`S`, with the paper's `iexit_class`, `xclass` and `xval` in RA
`Exit_Class_Infinite` and `Exit_Class_Marginals`.

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

**What closed it.**  The paper's envelope is now in SemiC
`Semicontinuous_Envelopes` (it was in `Operator_Envelopes`, now RAE)

    lsc_envK K u x = (SUP e:{0<..}. INF (u ` (ball x e Int K)))

and a bridge to `lsc_env`, so the machinery, which is all phrased in terms of
functions on `real^'n`, can be pointed at hypotheses that only speak about `K`.

* Clause (2b) and clause (3), where the envelope is a CONCLUSION, needed no
  extension.  The touching in the supersolution proof is global over `K` but
  the proof only ever uses it near the touching point, so the local form is the
  one really proved (now `covariation_val_supersol_lsc_local`, RA
  `Value_Function_Supersolution`).  Stated locally, the
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

**What was blocking.**  `Value_Function_Viscosity.feasible_strict_eigendata` (deleted)
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
set (`feasible_conj`, RAE `Operator_Envelopes`, which was already there).  So

* it lies in `sconstraint k L` at every `y`, with no margin, hence at `L = 1`;
* it annihilates `grad phi(y)`, because `a` annihilates `q` and
  `R(y) q` is parallel to `grad phi(y)`;
* the trace the DPP reads, `trace (M ** R a R^T)`, is continuous in `y` and
  equals `trace (M ** a)` at `y = x`, so the trace margin comes from
  continuity at the touching point instead of from three explicit smallness
  estimates.

That was `rotSF_exists` (subsection "Exact rotations" of
`Value_Function_Viscosity`), and it carries no hypothesis on `L` at all.  The
two Case 1 arguments --- `exit_val_supersol_contradiction_case1` and its `_lsc`
twin --- consumed it in place of the strict eigendata, and `1 < L` was then
weakened to `1 <= L` through the whole chain down to
`Statement/Theorem_1_1_Statement.thy`.

Now (phase 7): the rotated field is `covariation_rotSF_exists` (RA
`Euler_Limit_Growth`, subsection "Exact rotations"), for any set of rates
invariant under orthogonal conjugation; the paper's set is one
(`sconstraint_conj`, same theory). The surviving Case 1 argument is
`covariation_val_supersol_contradiction_case1_lsc` (RA
`Value_Function_Supersolution`); the plain twin is gone.

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

---

## 3. Section 5 of the paper (continuity of `v` for convex `K`) --- OPEN, out of scope

Decision D4b of `PLAN_RESTRUCTURING_3.md`. Nothing of Section 5 is formalised,
and nothing of Theorem 1.1 depends on it. `Statement/Paper_Map.thy` (its last
section) states this item by item.

* **Proposition 5.1** (for convex `K`, `v` is continuous on `interior K`) and
  **Corollary 5.2** (if moreover `v = 0` on `∂K`, `v` is continuous on `K`):
  a gated pilot of at most 200 lines, not yet run. Its precondition, the
  session `Relative_Arbitrage_Equation` (phase 6), now holds. The paper's
  proof dilates `v` into `interior K` and compares the dilated `v`, as a
  subsolution, with `v_*` by Theorem 4.2(b). What exists: Theorem 4.2(b)
  (`paper_theorem_4_2_b`; `comparison_two_domain`, RAE `Comparison_Two_Domain`
  and `Comparison_Instance`), the scaling of the operator and of its upper
  envelope (`ell_op_scale`, `ell_op_usc_scale`, RAE `Operator_Envelopes`), and
  the dilation invariance of Definition 3.1 for supersolutions
  (`visc_supersol_env_affine`, RAE `Comparison_Instance`). What is missing: the same invariance for
  subsolutions, and the argument itself. Corollary 5.2 needs, besides
  Proposition 5.1, only `v ≥ 0` and upper semicontinuity (`xval_usc`, RA
  `Theorem_1_1`).
* **Lemma 5.3** (`v(x) = 0` iff the face of `K` containing `x` in its relative
  interior has dimension at most `n − k`): new mathematics for this
  development, recorded here and not planned. Its deterministic core (a
  covariance degenerate on a subspace `W` satisfies `eigen_lb a m` only if
  `m + dim W ≤ n`) was once proved as `eigen_lb_dim_obstruction`, but no
  theory contains it now: it was removed before the repository's history
  begins. `STATUS.md` listed it as done; that entry is corrected.
* **Propositions 5.4** (`k ≤ 2`) **and 5.5** (polytopes): their proofs defer
  "word by word" to Lemmas 5.6, 5.7 and Corollary 5.9(iii) of Larsson and
  Ruf, *Minimum curvature flow and martingale exit times*, none of which is in
  the repository. New mathematics; not planned.
* **Remark 1.1(c)** conjectures that `v` does not depend on `L` when `K` is
  convex, and says the authors could not show it. That is open in the paper
  itself (see the end of section 2).

## 4. Proposition 2.4 for `v` itself --- OPEN (follow-up pilot)

Decision D4 of `PLAN_RESTRUCTURING_3.md`. Proposition 2.4 (Eq. (2.9) with
attainment by every optimiser) is proved for the horizon-`T` value
`exit_val k L T K` over `exit_class` (RA `Proposition_2_4`: `exit_val_dpp`,
`exit_val_dpp_time`, `exit_val_dpp_time_optimizer`), and for an abstract
closed convex `S` (CCM `Dynamic_Programming_Principle`). The stopping times
are path stopping times of the pair `(X, A)` with values in `[0,T]`. The
paper states (2.9) for `v` on `[0,∞)` and arbitrary stopping times of `X`.
Upper semicontinuity of `v` itself is proved (`xval_usc`).

What a transfer to `v` needs (sizes from the D4 pilot report):

* the identification of `v` with `exit_val` at large horizons: exists
  (`iexit_val_eq_exit_val_ball`, RA `Exit_Class_Infinite`;
  `xval_eq_iexit_val`, RA `Theorem_1_1`; generic
  `icovariation_val_eq_covariation_val`, CCM `Covariation_Class_Infinite`);
* 200--400 lines transporting essential infima between the class of Eq. (1.7)
  and `exit_class`;
* Galmarino's test for the coordinate filtration on `C([0,∞))`: not in the
  repository, and genuinely hard;
* a limit argument for unbounded `θ`.

For **bounded** `θ`, the independent re-check of D4 expects the transfer to
follow from existing bridges (`covariation_val_horizon_cap`, CCM
`Dynamic_Programming_Delayed_Class`; `iexit_val_eq_exit_val_ball`;
`covariation_class_has_extension`, CCM `Covariation_Class_Infinite`) with
`T ≥ sup θ + r_K²/(n − k)`. That is a follow-up pilot of at most 300 lines,
gated and not yet run. Galmarino's test and unbounded `θ` stay out of scope.
