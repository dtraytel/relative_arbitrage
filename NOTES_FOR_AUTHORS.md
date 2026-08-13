# Notes for the authors of arXiv:2512.17702

Theorem 1.1 of

> J.-H. Lai, M. Shkolnikov, H. M. Soner,
> *Relative arbitrage problem under eigenvalue lower bounds*, arXiv:2512.17702

has been formalised in Isabelle/HOL. The development contains no `sorry` and
no admitted step, so everything asserted below was settled by the proof
assistant. The formal statement, with every definition it mentions and nothing
else, is the single theory `Statement/Theorem_1_1_Statement.thy`.

Notation follows the paper: `n` is the dimension, `k` the eigenvalue index,
`v` the value function of Eq. (1.6), `F` the operator of Eq. (1.9), `S` the
constraint set of Eq. (1.5), `𝒫ₓ` the class of Eq. (1.7).

---

## Three things you may not expect

### 1. Section 3.1 needs no stochastic calculus at all

The subsolution half of Theorem 1.1 is proved with no Itô formula, no
exponential local martingale, no optional sampling, no stopping time, and no
stochastic integral — none of (3.17)–(3.19).

The reason is that for a **quadratic** test function the expansion is not an
approximation but an identity. Write `z · (M z) = tr(M z zᵀ)`. That is a
*linear* functional of clause (iv) of (1.7), and every condition defining `S`
is a linear (in)equality in the matrix: the spectral bounds constrain
`z · (a z)`, and the projection bound `m − k ≤ tr(a P)` is an intersection of
half-spaces. So `S` passes through the Bochner integral, and for `φ` quadratic
with Hessian `M`,

    E[φ(X_t)] − φ(x) = (t/2) · tr(M b)   for some b ∈ S,

exactly. Feed that to the `≤` half of the dynamic programming principle — an
almost-sure bound, which survives integration — and the subsolution inequality
drops out, with the operator of (1.9) itself, orthogonality constraint
included. Passing from quadratic test functions to arbitrary ones is then the
usual second-order Taylor step.

The whole development contains no stochastic integral. What survives of
stochastic calculus is Doob's inequality and optional sampling at a bounded
stopping time, and those are used only in the supersolution half, to localise
at the exit time of a small ball.

This also explains the asymmetry between the two halves, which the paper's
symmetric presentation hides: the subsolution half consumes an almost-sure
bound, and almost-sure bounds survive integration; the supersolution half
needs a lower bound on an *essential infimum*, which no mean can supply. That
is exactly why the supersolution half, and only it, needs the constraint
`a p = 0` of (1.9) — a direction annihilated by the averaged covariation is
frozen almost surely (the quadratic identity at `M = p pᵀ` turns the second
moment of `p · X_t` into `p · (E[Y_t] p)`, so the variance vanishes precisely
when that number does), and feasibility therefore kills the first-order term
`q · (X_t − x)` identically rather than merely in mean.

### 2. Example 3.1 does not need a weak solution of (3.11)

Equation (3.11) is a bounded, continuous, **degenerate, non-Lipschitz** SDE on
the punctured space, and it is the one ingredient in the paper for which no
existence theorem is cited by name. It is also the only thing standing between
the paper and the interior lower bound `v ≥ ball_v`.

No such existence theorem was formalised, and Example 3.1 is proved anyway,
for every `1 ≤ k < n`:

    v(x) = max((r² − |x|²)/(n − k), 0)   on the ball of radius r,

whenever the horizon does not bind. The route is a direct construction rather
than a weak solution. For `y ≠ 0`, take the `(n − k + 1)`-dimensional subspace
`V` spanned by an orthonormal family whose first member is `y/|y|`, so that
`y ∈ V`, and run a subspace-tangential covariation field inside `V`. Its
growth rate is `dim V − 1 = n − k`, which is exactly the constant in (3.1), so
the bound comes out sharp rather than up to a factor. The remaining cases are
elementary: outside the ball the exit time is `0`, on the sphere the value is
`0`, and the centre follows by upper semicontinuity rather than by running the
field from `0`.

If this route survives scrutiny, Example 3.1 is independent of the SDE theory
the paper appeals to.

### 3. Proposition 2.4 at a stopping time cannot be reached by discretisation

Proposition 2.4 is deferred to Larsson–Ruf, Proposition 2.2(ii),(iii), "word
by word". The natural way to get the `≥` half at a general stopping time `θ`
is to prove it at simple stopping times, which is straightforward, and then
approximate `θ` from above by finite-valued `θₙ ↓ θ`. **That does not work,
and not because it is hard: the inequality it needs is false.**

Take `θₙ ≥ θ` finite-valued, and a path that survives to `θ` but exits at some
`τ ∈ (θ, θₙ]`. The integrand at `θₙ` is then `τ`, while the integrand at `θ`
is `θ + v(T − θ, X_θ)`, and `v` can exceed `τ − θ` by any amount. So pointwise
domination fails on that event. Approximating from below gives the mirror
failure.

Nothing repairs it — not dyadic ceilings or floors, not horizon monotonicity
of `v`, not a modulus of continuity for `v` in space. The glue has to be
performed at `θ` itself, which means re-basing and re-clocking the future so
that the past and the future live in *fixed* path spaces despite the random
remaining horizon `T − θ`. In the formalisation the split at `θ` is additive
and stays on one clock, so reassembly is addition and never needs `θ` back.

The `≤` half is unaffected: it is an almost-sure pathwise statement and holds
for an arbitrary `θ`.

---

## Two smaller points

**The constant in Eq. (2.7).** The paper derives the fourth-moment bound
through Burkholder–Davis–Gundy, with constant `66 C²`. Iterating
Cauchy–Schwarz and the tower property gives the same bound with `8 C²`, and
avoids BDG entirely.

**Uniform convergence of sup-convolutions fails for usc data.** With `u = 1`
at `0` and `u = 0` elsewhere on the unit ball, `uᵋ(x) ≥ max(1 − |x|²/2ε, 0)`,
so at `|x| = √ε` the gap is at least `1/2` for every `ε`. Sup-convolutions of
usc functions decrease to them pointwise, never uniformly. In the comparison
argument the uniform bound is needed in exactly one place — attainment — and
there a local argument suffices, since the competitor is usc, bounded above,
and below its value at `x` outside an explicit ball.

---

## Differences between the paper's statement and the formal one

| | paper | formalisation |
|---|---|---|
| time horizon | none; `C([0,∞))` | finite `T`, proved to give the same value function as yours on `C([0,∞))` |
| regularity in the uniqueness clause | bounded usc | the same |
| zero boundary condition | Definition 3.1, viscosity sense | the same; the pointwise identity `v = 0` on `∂K` is proved only on a ball, where Lemma 5.3 says it holds |
| hypothesis on `K` for uniqueness | the `T_ι` family of Section 4 | an explicit predicate, proved to hold for every compact convex `K` with nonempty interior |
| standing assumption on `L` | `L ≥ 1` | `L ≥ 1`, except that the supersolution half consumes the strict `L > 1` |
| Example 3.1 | `1 ≤ k < n` | the same |

The finite horizon is not a restriction. Your class and your value function are
formalised as you write them — laws on `C([0,∞))`, the covariation constraint
at every pair of times, no stopping in the martingale clauses — and the two
value functions are proved equal: every member of the horizon-`T` class is the
restriction of a member of your class, obtained by gluing an independent
Brownian continuation with covariation `t·I` onto it at time `T`. For a `K`
inside a ball of radius `r` the hypothesis is automatic once
`T > (r² − |x|²)/(n − k)`, which is the a priori bound of Eq. (3.10) anyway.
The finite horizon is therefore a device of the proof, not of the statement.

---

## Infrastructure that had to be built

None of the following existed in Isabelle/HOL or its Archive of Formal Proofs;
each is packaged as a reusable entry.

* Rademacher's theorem, Alexandrov's theorem, Jensen's lemma for semiconvex
  functions, and the Crandall–Ishii theorem on sums.
* Wiener measure as a projective limit, with independent increments.
* Doob's maximal inequality; optional sampling at a bounded stopping time in
  continuous time; quadratic variation and its compensator.
* Vitali's convergence theorem; uniform integrability of a family of
  conditional expectations.
* `C([0,T], ℝⁿ)` as a Polish space, with the continuous mapping theorem and
  portmanteau; tightness from increment moments.
* Measurable selection for upper semicontinuous payoffs on compact sets —
  the Bertsekas–Shreve Proposition 7.33 that Larsson–Ruf appeal to. It is
  proved here by a greedy nested bisection; a countably valued ε-selector does
  not exist, so some such construction is forced.
