# Notes for the authors of arXiv:2512.17702

What a machine-checked formalisation of Theorem 1.1 of

> J.-H. Lai, M. Shkolnikov, H. M. Soner,
> *Relative arbitrage problem under eigenvalue lower bounds*, arXiv:2512.17702

turned up. The development is in Isabelle/HOL; it contains no `sorry` and no
admitted step, so every claim below about what is or is not provable was
settled by the proof assistant rather than by reading.

The formal statement, with every definition it mentions and nothing else, is
in the session `Relative_Arbitrage_Statement` (one theory,
`Theorem_1_1_Statement.thy`). Reading that theory is the fastest way to check
that what was proved is what you stated.

Notation below follows the paper: `n` is the dimension, `k` the eigenvalue
index, `K` the compact set, `v` the value function of Eq. (1.6), `F` the
operator of Eq. (1.9), `𝒫ₓ` the class of Eq. (1.7).

---

## 1. Places where the statement had to be read more carefully than it reads

### 1.1 The zero boundary condition is a viscosity condition

Clause (1.10) invites the reading "`v = 0` on `∂K`". That reading is false,
and the paper's own Lemma 5.3 refutes it: for convex `K`, `v(x) = 0` exactly
when the face containing `x` has dimension at most `n − k`. The cube in `ℝ³`
with `k = 2` therefore has `v > 0` on the open two-dimensional faces of its
boundary.

What Definition 3.1 actually says — and what is formalised — is that the sub-
and supersolution inequalities are demanded also at boundary points, gated by
the sign of the envelope: at `x ∈ ∂K` with `u*(x) > 0` a touching from above
must still satisfy `F_*(∇φ, ∇²φ) ≤ 1`, and at `x ∈ ∂K` with `u_*(x) < 0` a
touching from below must satisfy `F*(∇φ, ∇²φ) ≥ 1`.

An earlier version of this formalisation targeted the pointwise reading and
could not prove it; the correction cost a fair amount of work. A sentence in
the statement of Theorem 1.1 pointing at Definition 3.1 for the meaning of
"zero boundary condition" would prevent that.

The pointwise identity *is* proved here where it holds, namely on a ball,
where it is part of Example 3.1.

### 1.2 Continuity of `v` is not part of Theorem 1.1

Proposition 4.1 gives uniqueness among **bounded upper semicontinuous**
solutions, and Theorem 1.1 needs nothing more. Continuity is proved only in
Section 5, under extra hypotheses on `K`. This is clear once Section 4 is
read, but Theorem 1.1 read alone suggests continuity is in play, and an
earlier version of the formalisation carried continuity as a hypothesis —
which is a strictly weaker theorem than yours.

### 1.3 The uniqueness clause carries a hypothesis on `K`

Theorem 4.3 and Proposition 4.1 need the family `T_ι`, `ι ∈ (1,2]`, of
rotation–dilation–translations with `K ⊆ (T_ι K)°` and `T_ι → id`. Theorem 1.1
as stated does not mention it. In the formalisation it is an explicit
predicate (`expandable`), and that every compact convex `K` with nonempty
interior satisfies it is proved (`convex_expandable`), so the hypothesis is
visibly non-vacuous.

### 1.4 A comparison statement with no regularity hypothesis is refutable

This is a remark about how comparison must be phrased, not a defect in
Theorem 4.2, which does carry the regularity. An intermediate interface in
this development asserted comparison for sub-/supersolutions with no
regularity assumption on `u` and `w`. It is false, and the refutation is
formalised (`comparison_principle_refuted`): sub- and supersolution are
conditions *local to* `Ω`, so values outside `Ω` are unconstrained. Take
`u = v + 1` on the ball — still a subsolution, since a constant shifts neither
gradient nor Hessian of a test function — and `w` equal to `v` inside and to
`v + 1` outside. Then `w` is a supersolution, `u = w` on the boundary, and
`u > w` at the centre.

---

## 2. Steps the paper leaves to the reader, and what they cost

### 2.1 Proposition 2.4

The proof given is that it suffices to repeat Larsson–Ruf, Proposition
2.2(ii),(iii) word by word. Discharging it took two substantial pieces.

**A measurable selection theorem.** Larsson–Ruf appeal to Bertsekas–Shreve
(1978), Proposition 7.33 — measurable selection for upper semicontinuous
payoffs on compact sets. Nothing of the kind exists in Isabelle/HOL or its
Archive of Formal Proofs, so it was proved here, by a greedy nested bisection
along a countable dense sequence of the class. Worth recording: a
*countably valued* ε-selector does not exist, so the bisection is not a
convenience — some such construction is forced.

**Conditioning.** The `≤` half of the dynamic programming principle goes
through a regular conditional distribution, which is your route (Larsson–Ruf
condition with an r.c.d., citing Stroock–Varadhan Theorem 1.3.4). It works.
Two negative results are worth reporting:

* *Conditioning on a positive-measure event does not work.* It pins the
  endpoint only to a small ball, so the comparison leaks into an
  ε-enlargement of `K` and would need `v(·, K_ε) → v(·, K)`. The obvious
  portmanteau argument runs the wrong way, since `τ_K ≤ τ_{K_ε}` makes the set
  inclusion go backwards. Conditioning by an r.c.d. avoids the enlargement
  entirely, because the conditioned law starts at a single point.
* *The stopping-time version cannot be obtained by discretisation.* Lifting
  the principle from simple stopping times to general ones by approximating
  the time from above makes the required inequality false. The pasting has to
  be performed at the stopping time itself.

The `≥` half is a pasting construction. Both halves are proved at a
deterministic time and at a stopping time.

### 2.2 The lower bound in Example 3.1

As presented, `v ≥ ball_v` at interior points follows from a global weak
solution of the degenerate, non-Lipschitz SDE (3.11) on the punctured space,
for which no existence theorem is cited by name. That gap is real: no such
theorem was available, and constructing one was not attempted.

Example 3.1 is nevertheless proved here for every `1 ≤ k < n`, by a different
route — see §3.6 — so the conclusion stands even though the stated proof was
not followed.

---

## 3. Where the formalisation deviates from the paper's proofs

### 3.1 Itô's formula is not needed for the subsolution half

Section 3 uses Itô's formula for class members, an exponential local
martingale, and optional sampling ((3.18)–(3.19)). For a *quadratic* test
function none of that is needed, and the expansion is exact rather than
approximate:

    E[φ(X_t)] − φ(x) = (t/2) · tr(M b),   b ∈ S,

because `z · (M z) = tr(M z zᵀ)` is a **linear** functional of clause (iv) of
(1.7), and every condition defining the constraint set `S` is a linear
(in)equality in the matrix — the spectral bounds constrain `z · (a z)`, and
the projection bound `m − k ≤ tr(a P)` is an intersection of half-spaces — so
`S` passes through the Bochner integral. The subsolution inequality then
follows with no stopping time anywhere.

No stochastic integration appears in this development at all.

### 3.2 What the constraint `a p = 0` in (1.9) buys

A direction annihilated by the averaged covariation is *frozen*: the process
does not move along it, almost surely. The proof is the quadratic identity at
`M = p pᵀ`, which turns the second moment of `p · X_t` into `p · (E[Y_t] p)`,
so the variance vanishes exactly when that number does.

Consequently, for a quadratic test function with gradient `q` at `x`,
feasibility kills the first-order term `q · (X_t − x)` identically — not
merely in mean. That is why the constraint belongs in (1.9) and not in (1.7),
and it explains the asymmetry between the two viscosity inequalities: the
subsolution half consumes an almost-sure bound, which survives integration,
whereas the supersolution half needs a lower bound on an essential infimum,
which no mean can give.

### 3.3 The localisation in Theorem 4.2(b)

The boundary maximiser is localised here by a **constant extension** rather
than by a compactness/subsequence argument. Definition 3.1(a) reads `u` only
on `K`, so it transfers verbatim to any function agreeing with `u` there;
extending `u` off the closed `K` by a constant at or below its minimum puts
the sup-convolution back down at that constant far from `K`, so a maximiser
over `Q × K'` is a maximiser over `ℝⁿ × K'`, and the localisation asks nothing
of the `x` coordinate.

Two smaller deviations in the same proof. The single domain `Ω` running
through the Crandall–Ishii chain is a signature accident — it is used only
through the subsolution side and the supersolution side, never jointly — so
splitting it into `Ω_u`/`Ω_w` is free, and that is exactly what the two-domain
statement needs. And replacing `w` by `max(w, 0)` is what makes both the
boundary gate and the pinning work; it agrees with `w` where `w ≥ 0`.

Also worth recording, since it looks plausible and is false: explicit penalty
jets do **not** replace Crandall–Ishii. Freezing one variable gives the same
gradient `p` but Hessians `X = q''` and `Y = −q''`; for convex `q` this gives
`Y ⪯ 0 ⪯ X`, and since `F` decreases in the Hessian, `F_*(p,X) ≤ 1 ≤ F*(p,Y)`
is perfectly consistent. It is `X ⪯ Y` that closes the argument, and only the
theorem on sums supplies it.

### 3.4 Sup-convolutions of upper semicontinuous data

The uniform upper bound for sup-convolutions is false for usc data:
with `u = 1` at `0` and `0` elsewhere on the unit ball,
`u^ε(x) ≥ max(1 − |x|²/2ε, 0)`, so at `|x| = √ε` the gap is at least `1/2` for
every `ε`. Sup-convolutions of usc functions decrease to them pointwise,
never uniformly.

The uniform bound is needed in exactly one place — attainment — and there a
local argument suffices: the competitor is usc, bounded above, and below its
value at `x` outside an explicit ball, so attainment on that ball is
attainment globally.

### 3.5 The finite horizon

The paper works on `C([0,∞))` with the uncapped exit time. The formalisation
caps at a horizon `T`, which is the one place where the formal statement is
not literally yours. The cap is inert: for laws under which the exit happens
before `T` almost surely, every larger horizon gives the same essential
infimum, and the optimizer is horizon-independent. Wherever the horizon
appears in a hypothesis below, it says only that it does not bind.

### 3.6 Example 3.1 for general `k`

Example 3.1 is obtained from an interior lower bound at the sharp rate
`n − k`: for `y ≠ 0`, take the `(n − k + 1)`-dimensional subspace `V` spanned
by an orthonormal family whose first member is `y/|y|`, and run the
subspace-tangential field inside `V`; its growth rate `dim V − 1 = n − k` is
exactly the constant in (3.1). The weak solution of (3.11) is not needed.

### 3.7 The fourth-moment estimate of Eq. (2.7)

Eq. (2.7) is derived in the paper through the Burkholder–Davis–Gundy
inequality, giving the constant `66 C²`. Formalising BDG was not attractive,
so the estimate was proved directly, by iterating Cauchy–Schwarz and the tower
property. The constant that comes out is `8 C²`.

---

## 4. Infrastructure that had to be built

None of the following existed in Isabelle/HOL or its Archive of Formal Proofs.
Each is reusable and is packaged as a separate entry.

* Rademacher's theorem, Alexandrov's theorem, Jensen's lemma for semiconvex
  functions, and the Crandall–Ishii theorem on sums.
* Wiener measure as a projective limit, with independent increments and the
  Gaussian fourth moment.
* Doob's maximal inequality; optional sampling at a bounded stopping time in
  continuous time, by dyadic approximation; quadratic variation and its
  compensator.
* Vitali's convergence theorem, and uniform integrability of a family of
  conditional expectations.
* `C([0,T], ℝⁿ)` as a Polish space, with the continuous mapping theorem and
  portmanteau; tightness from increment moments.
* Measurable selection for usc payoffs on compact sets (§2.1).

---

## 5. Summary of the differences between your statement and the formal one

| | paper | formalisation |
|---|---|---|
| time horizon | none | finite `T`, kept inert by an explicit hypothesis |
| regularity of `v` in the uniqueness clause | bounded usc | the same |
| zero boundary condition | Definition 3.1, viscosity sense | the same |
| hypothesis on `K` for uniqueness | `T_ι` family (Section 4) | `expandable K`, proved for compact convex `K` with interior |
| standing assumption on `L` | `L ≥ 1` | `L ≥ 1`, except that the supersolution half consumes `L > 1` |
| Example 3.1 | `1 ≤ k < n` | the same |
