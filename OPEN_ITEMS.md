# Open items against the paper

One place where the formal statement and arXiv:2512.17702 do not yet line up.
Everything else in `Statement/Theorem_1_1_Statement.thy` matches; see
`NOTES_FOR_AUTHORS.md` for the differences that are settled.

## 1. The envelope: `real^'n` versus `K`

The paper's solutions are functions `u : K -> R` and its lower envelope `u_*`
is the liminf **within K**.  Here they are `real^'n => real` and

    lsc_env u x = (SUP e:{0<..}. INF y:ball x e. u y)

takes the liminf over balls of `real^'n`.  Always `lsc_env u <= u_*`, with
equality at interior points of `K` (small balls stay inside), so the two
differ exactly on `K - interior K` --- which is where the boundary gate of
clause (3) is evaluated.

Direction of the gap, which is not uniform:

* clause (4): the envelope is a HYPOTHESIS on the competitor.  Our gate
  `{x : dK. lsc_env u x < 0}` contains the paper's `{x : dK. u_* x < 0}`, so we
  demand more.  Our uniqueness clause is WEAKER than Theorem 1.1.
* clause (3): the envelope is a CONCLUSION.  We prove the inequality at more
  points, so that clause is STRONGER than the paper's.

**It is reparable.**  A function `K -> R` reaches `real^'n` only through an
extension, and extending by any constant `M >= sup_K u` makes the two agree on
`K`.  The crux is proved (scratch theory, 0 errors):

    lemma INF_ball_eq_on_K:
      assumes "bdd_below (range u)"
        and "!!y. y : K ==> u y <= M" and "!!y. y ~: K ==> M <= u y"
        and "x : K" and "0 < e"
      shows "(INF y:ball x e. u y) = (INF y:(ball x e Int K). u y)"

The points the larger ball adds are all `>= M >= u x`, and `u x` is already in
the smaller one, so they never lower the infimum.

Plan (~150--250 lines):

1. Define `lsc_envK K u x = (SUP e:{0<..}. INF (u ` (ball x e Int K)))`.
2. Move `INF_ball_eq_on_K` into `Operator_Envelopes` beside it, and derive
   `lsc_env ubar x = lsc_envK K u x` for `x : K` under the extension
   hypothesis, by a SUP congruence.
3. Restate clause (4) for `u : K -> R` under the paper's hypotheses, applying
   the present theorem to `ubar y = (if y : K then u y else Sup (u ` K))`; the
   sup exists since `K` is compact and `u` bounded.
4. Restate clause (3) with `lsc_envK`; that direction weakens what is already
   proved, so it follows.

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

**Left over.**  The skew-field cluster of the section "The supersolution half:
skew-symmetric covariance fields" (`skewv`, `skewfield`, `skewSF`,
`skewfield_properties`, `skewSF_package`, `perturbed_columns_*`,
`small_radius_exists`, `feasible_strict_eigendata`) is now dead: nothing
outside it refers to it.  It is retained for now because it is the paper's own
construction, and marked as superseded at `feasible_strict_eigendata`.
Deleting it is a separate cleanup, and one worth doing before an AFP
submission.

**Still open, and a different question.**  Remark 1.1(c) also conjectures that
the value function does not depend on `L` when `K` is convex, and says the
authors could not show it.  Nothing here bears on that: `F` itself depends on
`L`, and what is proved above is that each `L >= 1` --- separately --- has its
value function characterised.
