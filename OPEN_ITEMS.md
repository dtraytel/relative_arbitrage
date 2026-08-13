# Open items against the paper

Two places where the formal statement and arXiv:2512.17702 do not yet line up.
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

## 2. Strictness in `L`

The paper's standing assumption is `L >= 1`.  Clauses (2b), (3b) and (4) here
assume `1 < L`.  The single consumer is
`Value_Function_Viscosity.feasible_strict_eigendata`, whose own comment says
so: it produces a margin `m > 0` with

    lam u <= L - m   for all u in the basis,      1 + m <= lam u   on Bp

so that the eigenvalue data survives perturbation along the path.  At `L = 1`
the interval `[1 + m, L - m]` is empty and the lemma is false: `sconstraint k 1`
forces the top `n - k` eigenvalues to equal `1` exactly (`>= 1` from the
eigenvalue lower bound, `<= 1` from `eigen_ub a 1`), so the feasible set has no
slack and there is no strictly interior witness to perturb.

So at `L = 1`:

* clause (0), clause (1), clause (2a), clause (3a) and Example 3.1 hold --- all
  are proved under `1 <= L`;
* clauses (2b), (3b) and (4) are NOT proved.

Whether they are FALSE at `L = 1` is not established here.

**This is the case the paper singles out.**  Remark 1.1(c) reads

> "When L=1, the partial differential equation F(grad v, grad^2 v)=1 with zero
> boundary condition becomes the arrival time formulation of a co-dimension
> mean curvature flow from [AS96]."

and Theorem 1.1 assumes only `L >= 1`, so `L = 1` is inside its scope.  The
strictness therefore sits exactly on the Ambrosio--Soner co-dimension mean
curvature flow --- the geometric payoff of the paper --- and the uniqueness
clause is unproved precisely there.  This is the most consequential of the two
items and should be the first thing put to the authors.

**The paper's own proof appears to need `L > 1` at the same step.**  In Case 1
of the supersolution argument (`grad phi(x) != 0`) the paper writes

> "We can modify a such that lambda_(1)(a), lambda_(2)(a), ..., lambda_(n-k)(a)
> in (1,L)"

--- the OPEN interval `(1,L)`, empty when `L = 1`.  That is the same move as
`feasible_strict_eigendata`, so the strictness here is not an artefact of the
formalisation: it reproduces the paper's argument faithfully, dependence on
`L > 1` included.  Theorem 1.1 is nevertheless stated for `L >= 1`, and no
approximation `L \<down> 1` appears.

CAVEAT: the quotation above and the claim that no approximation argument
appears were obtained by automated extraction from the arXiv HTML, not by
reading Section 3 through.  Verify against the paper before putting this to
the authors --- an earlier conclusion in this project about what the paper says
was wrong for exactly this reason.

Adjacent, and explicitly open in the paper (Remark 1.1(c)):

> "In view of the right-hand side of (1.6), it is natural to conjecture that
> the value function v does not depend on L, at least when K is convex.  We
> were not able to show this and leave it as a tantalizing open problem."

That is a different question --- `L`-independence of `v`, not uniqueness at
`L = 1` --- and it does not settle this one, since `F` itself depends on `L`.

Nothing found shows (2b)/(3b)/(4) are FALSE at `L = 1`.  What is established is
that the only known route to them, in the paper and here alike, breaks there.

### Correction: which set is rigid at `L = 1`

Two different sets are in play, and an earlier note in this project conflated
them.

* `feasible k L p = {a. psd a & a *v p = 0 & eigen_lb a (n-k) & eigen_ub a L}`
  --- the OPERATOR's set, Eq. (1.9).  `eigen_lb a (n-k)` puts the `n-k` largest
  eigenvalues at `>= 1`, `eigen_ub a L` puts all of them at `<= L`.  At `L = 1`
  the `n-k` largest are pinned to `1` exactly.  THIS is what is rigid, and it
  is what Case 1 of Section 3 and `feasible_strict_eigendata` both try to
  perturb.
* `sconstraint k L = Pi_constraint k Int {a. eigen_ub a L}` --- the CLASS's set,
  Eq. (1.5), the convexified constraint.  This is NOT rigid at `L = 1`.  For
  `n = 2, k = 1` the only condition is `m = 2`, so `trace a >= 1` with both
  eigenvalues `<= 1`, and `0.6 * I` qualifies: the top eigenvalue is `0.6`, not
  `1`.

So at `L = 1` the admissible controls are still plentiful; only the operator's
feasible set degenerates.  That is a reason to expect the clauses may well be
true at `L = 1` and merely out of reach of this argument --- but it is an
expectation, not evidence.

### A test that could decide it

Example 3.1 is proved here under `1 <= L`, so on a ball the value function is
known in closed form AT `L = 1`:

    v(x) = max((r^2 - |x|^2)/(n-k), 0).

`F` depends on `L`, so being a supersolution for `L > 1` does not transfer.
But the `L = 1` operator applied to this explicit `v` is a finite computation.
Checking the supersolution inequality for it at interior points of the ball
either produces a counterexample --- settling (2b) negatively at `L = 1` --- or
gives the first real evidence that the clauses survive.  That is the cheapest
next experiment, and it needs no new machinery.

Two routes out, neither attempted:

* a different witness at `L = 1`, since the rigidity means the perturbation
  must move inside the pinned set rather than off it;
* approximation `L \<down> 1`, which needs stability of the supersolution property
  as `L` decreases to `1` --- note `sconstraint k L` shrinks as `L` does, so the
  value functions are monotone in `L` and a limit argument is plausible, but
  the viscosity property does not transfer for free.
