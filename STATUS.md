> **This file is a development diary and is out of date from here down.**
> It predates the restructuring into sessions and the theory renames, so its
> file names, session name (`Arbitrage`) and theory count no longer apply.
>
> Current state (2026-08-14): Theorem 1.1 of arXiv:2512.17702 is formalised in
> full, with no `sorry` and no `axiomatization`. The formal statement of the
> theorem and of every definition it mentions is
> `Statement/Theorem_1_1_Statement.thy`; what the authors of the paper should
> read is `NOTES_FOR_AUTHORS.md`.
> The paper's own uncapped class and value function on `C([0,∞))` are
> formalised in `Relative_Arbitrage/Exit_Class_Infinite.thy` and proved equal
> to the horizon-capped ones used throughout the proofs. The paper's class
> `P_x` itself — laws of `X` alone, not of the pair `(X, <X>)` — is
> `Relative_Arbitrage/Px_Bridge.thy`, together with both inclusions and the
> equality of the two value functions (`iexit_val_eq_xval`), so no item is
> open against the paper; see `OPEN_ITEMS.md`.
>
> The `Relative_Arbitrage_Unused` session — the discrete market, the discrete
> stochastic integral built on it, and layers 1-4 of an abandoned Skorokhod
> representation — has been deleted; the diary below still describes it. None
> of it was reachable from Theorem 1.1, and none of it stood on its own: the
> integral is a martingale transform over this project's own locales, and the
> Skorokhod development stops short of the theorem it was aiming at, which
> Levy-Prokhorov from the AFP supplied instead. It is in the git history.

---

# HANDOVER (2026-08-02)

# *** THEOREM 4.2(a) IS PROVED ***

    theorem max_principle_boundary_holds:      (Comparison_Assembly.thy)
      fixes K :: "(real^'n::finite) set"
      assumes cK: "compact K" and neK: "K ~= {}"
        and kk: "1 <= k" "k < CARD('n)" and LL: "1 <= L"
      shows "max_principle_boundary k L K"

where `max_principle_boundary` is the CORRECTED, continuity-carrying predicate
at Lemma_3_1_Envelopes.thy:722. (The refutable interface was renamed
`max_principle_boundary_raw` in an earlier session and is kept only as the
target of `max_principle_boundary_counterexample`.)

Verified: `isabelle build -d . Arbitrage` exit 0; **zero `sorry`/`oops` across
all 57 theories**; no `axiomatization`. `Comparison_Assembly.thy` is at 385
lemmas/theorems.

`K ~= {}` is a genuine side condition, not an artefact — the predicate is FALSE
for `K = {}` (hypotheses vacuous, conclusion asserts membership in the empty
set). Recorded at `compact_frontier_nonempty`.

## The chain, top down

    max_principle_boundary_holds
      <- comparison_soft_complete            (case split on xh = yh)
           <- doubling_localised_maximiser_soft   (produces the maximiser)
           <- comparison_soft_off_diagonal    (A)
           <- comparison_soft_diagonal        (B)
      <- bounded_on_compact, continuous_extension_bounded,
         visc_subsol_extend / visc_supersol_extend,
         max_principle_boundary_attains, compact_frontier_nonempty,
         theta_gap_preserved, theta_exists_aux

## THEOREM 1.1: the target, and where it stands

Scoped 2026-08-02. In THIS project's vocabulary (every constant below exists;
`v` needs a `defines` because there is no real-valued value-function constant):

    theorem theorem_1_1:
      assumes "1 <= k" "k < CARD('n)" "1 <= L" "compact K" "K ~= {}"
      defines "v == (%x. enn2real (val_fn k L K x))"
      shows "!!x. x : K ==> val_fn k L K x < top"        -- (0) finiteness
        and "continuous_on K v"                          -- (1) regularity (usc surrogate)
        and "visc_sol k L (interior K) v"                -- (2) Eq. (1.9)
        and "!!x. x : K - interior K ==> v x = 0"        -- (3) Eq. (1.10)
        and "<uniqueness>"                               -- (4)

**Clause (4) is DONE** — `viscosity_uniqueness_compact` (Comparison_Assembly)
and its re-export `theorem_1_1_uniqueness_general` (Theorem_1_1.thy):

    compact K, K ~= {}, u and w continuous on K and both visc_sol on interior K,
    agreeing on K - interior K  ==>  u x = w x for all x in K

Both directions are the same argument with roles swapped, via
`max_principle_boundary_holds`. This generalises the third clause of
`theorem_1_1_ball_fragment`, which was tied to `K = cball 0 r` because it went
through the explicit Example 3.1 formula `ball_v` rather than through comparison.

**Clauses (0)-(3) are NOT started, and the gap is bigger than "Phases A-D"
suggested.** Established by grep, not assumed: there is NO dynamic programming
statement, NO semicontinuity result for `val_fn`, and NO theorem that `val_fn`
is a viscosity sub- or supersolution anywhere in the repository. `val_fn` occurs
in exactly TWO files — its definition at Value_Function.thy:174 and
Theorem_1_1.thy. The theories that look relevant (Relative_Arbitrage_Stochastic,
_Ito, _PDE, _Comparison) prove things about `ball_v`, the EXPLICIT Example 3.1
formula, never about the sup-over-markets object

    val_fn k L K x0 = Sup (mkt_exit_vals k L K x0)
    mkt_exit_vals k L K x0 = {ess_inf_time M tau | sufficiently_volatile_market ...}

So the bridge from `val_fn` to the PDE does not exist at all. Building it is the
whole probabilistic half of the paper: weak existence for Eq. (3.11), the
Section 3.1 martingale construction, the dynamic programming principle, then
Prop 2.4 via Lemmas 2.2/2.3. That is a different body of work from the PDE
comparison theory this session completed, and 4.2(a) being done does not
shorten it.

NOTE clause (3) IS known for the ball (`val_fn_boundary`); for general `K` it
needs the eigenvalue lower bound to force immediate exit from a boundary point,
which is a real argument, not a definitional one.

**CLAUSE (0) IS ALSO DONE** — `val_fn_finite_bounded` (Value_Function.thy):
`bounded K ==> val_fn k L K x0 < top`. Free: a bounded `K` sits inside some
`cball 0 a`, `val_fn` is monotone in `K` (`val_fn_mono`), and on a ball it is
bounded by the explicit Example 3.1 value (`val_fn_le_ball_v`). Also added
`comparison_compact` (Comparison_Assembly) — the ORDERED-boundary-data
comparison principle on general compact `K`, weaker hypotheses than
`viscosity_uniqueness_compact` and the form most uses want.

**CLAUSE (3) IS DONE FOR THE BALL** — `ball_v_boundary_zero`,
`val_fn_boundary_zero`, `val_fn_zero_on_frontier_ball` (Value_Function.thy).
`ball_v r k x = max (r^2 - x.x) 0 / (CARD('n) - k)` vanishes exactly when
`x.x >= r^2`, so on the sphere; combined with `val_fn_boundary` that is the zero
boundary condition of Eq. (1.10) on `cball 0 r - interior (cball 0 r)`.
For a GENERAL compact `K` this is Lemma 5.3 of the paper, which reuses the
measure built in Example 3.1 and is therefore behind the same weak-existence
result as clauses (1) and (2).

So Theorem 1.1 stands at:

  (0) finiteness   PROVED, general K       `val_fn_finite_bounded`
  (1) continuity   OPEN                    -- needs Prop 2.4
  (2) visc_sol     OPEN                    -- needs Prop 2.4 + the DPP
  (3) v = 0 on dK  PROVED for the ball     `val_fn_zero_on_frontier_ball`
                   OPEN for general K      -- Lemma 5.3, needs Example 3.1
  (4) uniqueness   PROVED, general K       `viscosity_uniqueness_compact`

**EVEN "THEOREM 1.1 FOR THE BALL" IS NOT BOUNDED WORK.** Clauses (1) and (2)
for `K = cball 0 r` both reduce to the LOWER bound `ball_v <= v`, which is
Example 3.1's hard half and needs weak existence for Eq. (3.11) — a global weak
solution of a bounded, continuous, DEGENERATE, NON-LIPSCHITZ SDE on the
punctured space, for which the paper cites no theorem by name and which does not
exist in Isabelle/HOL or the AFP. The `<=` half (`val_fn_le_ball_v`) has been
available all along; it is the `>=` half that is missing, and it is missing for
a structural reason, not for want of assembly.

### A SECOND REFUTABLE INTERFACE, found while scoping Theorem 1.1

`comparison_principle` (Relative_Arbitrage_Uniqueness.thy:469) axiomatises
comparison with **NO continuity hypothesis** on `u` and `w`. That is the same
defect the project already found and repaired in `max_principle_boundary_raw`,
and it is fatal for the same reason: `visc_subsol`/`visc_supersol` are LOCAL
conditions on `Omega`, so values OUTSIDE `Omega` are unconstrained and can be
moved to violate any boundary comparison.

**PROVED** (`comparison_principle_refuted`, Theorem_1_1.thy):

    1 <= k, k < CARD('n), 1 <= L, 0 < r  ==>  ~ comparison_principle k L (ball 0 r)

Witness: `u = ball_v + 1` (a subsolution — `visc_subsol_shift`, also new: adding
a constant changes neither gradient nor Hessian of a test function) against `w'`
equal to `ball_v` INSIDE the ball and `ball_v + 1` outside. `visc_supersol_cong_on`
keeps `w'` a supersolution; on `closure (ball 0 r) - ball 0 r` the two are EQUAL
so the locale's boundary hypothesis holds; the locale then forces
`ball_v + 1 <= ball_v` at the centre.

**CONSEQUENCE: `ball_v_unique_solution` (Relative_Arbitrage_Uniqueness.thy:499),
which carries `comparison_principle k L (ball 0 r)` as a hypothesis, is VACUOUS
for every `r > 0`.** It should be restated against `comparison_compact` or
`viscosity_uniqueness_compact`, both now unconditional;
`theorem_1_1_uniqueness_general` is the replacement.

PROOF NOTE: the last step resisted `simp` and `auto`, which both left the literal
reflexivity `ball_v r k 0 = ball_v r k 0` unclosed (an invisible type-variable
mismatch coming out of the `define`). `unfolding w'_def by (rule if_P[OF zin])`
sidesteps simp entirely and works. Do not "simplify" it back.

### CORRECTIONS to this file's own earlier wording (from reading the paper)

 - **"the PDE (1.9)-(1.10)" is WRONG.** (1.9) is the DEFINITION of `F` only, and
   is restated verbatim as (3.1). (1.10) is the geometric-nonlinearity identity
   `F(c1 p, c1 M + c2 p p^T) = c1 F(p,M)` from Remark 1.1(b) — a property of `F`,
   not part of the equation. The PDE is never a numbered display: it appears
   inline in Theorem 1.1 and is given its meaning by **Definition 3.1**, whose
   two inequalities are (3.2) and (3.3).
 - **"the Section 3.1 martingale construction" is WRONG.** Eq. (3.11) lives in
   **Example 3.1**, which precedes Subsection 3.1. Subsection 3.1 is titled
   "Subsolution property of the value function".
 - **Theorem 1.1 has TWO independent halves**: existence (v is an usc viscosity
   solution, for ANY compact K) and uniqueness (CONDITIONAL on an extra
   `T_iota` hypothesis).

### THE DECISIVE FACT ABOUT REACHABILITY

**Proposition 2.4 has NO proof in the paper.** Its entire proof is the sentence
"It suffices to repeat [larsson_minimum_2022, proofs of Proposition 2.2(ii),
(iii)] word by word." It supplies THREE of the five ingredients of the existence
half: usc of `v`, the DPP, and attainment of the sup. Under this project's
standing rule (known theorems proved, not assumed) that sentence has to become
two AFP-entry-sized developments — a universally measurable selection theorem
over analytic sets (Bertsekas Prop. 7.33) and a Skorokhod representation on
`C([0,inf))`, NEITHER of which exists in Isabelle/HOL, the AFP, or this repo.

Scoping estimate for the remainder: **50,000-100,000 lines**, one to two times
the entire current project. Four required pieces are each a standalone AFP entry
and none exists. **Theorem 1.1 is not reachable as bounded work.**

### On the Ito layer — CHECKED, and the alarming version of the claim is unfair

The scoping agent called the Ito layer "a facade at exactly the load-bearing
point": `sint` (Relative_Arbitrage_Ito.thy:95) is DEFINED to be the value Ito's
formula would assign, so `ito_formula_quadratic` is `by (simp add: sint_def)`.

**Substantively true, but the code states this plainly in place, so it is a
declared scope boundary and not a hidden circularity.** Verbatim from the
source, immediately above the definition:

    "The stochastic integral of the gradient strategy, defined by the value
     that Ito's formula assigns to it for the quadratic test function w.
     NO ASSUMPTION ABOUT STOCHASTIC INTEGRATION IS MADE."

and in the surrounding commentary:

    "The identification of the explicitly given process sint with the
     stochastic integral of the gradient strategy is exactly Ito's formula and
     REMAINS OUTSIDE THE FORMALIZATION; all results below hold for the
     explicit process."

So: Ito's formula is genuinely NOT proved, and any downstream result is a
statement about the explicit process `sint`, not about a stochastic integral.
That is a real limitation and it is on the critical path for Theorem 1.1. But it
is documented at the point of use, which is the right thing to have done — do
not read it as a defect in the existing work.

---

## State: build exit 0, 0 `sorry`/`oops` in all 57 theories, nothing unverified.

`Comparison_Assembly.thy` is 7607 lines / 9658 commands, all green in PIDE.

### Assembly 1 is DONE: `comparison_supconv_maximiser_complete`

The shifted analogue of stage 10, and the end of the first of the two assemblies
the previous handover named. It takes a PLAIN maximiser of the doubled
sup-convolution functional over `cball xi0 r` — **no strict gap** — plus the
gradient lower bound there and the attainment balls, and derives `False`. The
gap is manufactured internally by `shifted_jensen_family` at the tilts
`delta_i = D0/(2+i)`.

All three `O(delta_i)` costs land where the generalised interfaces expect them:

* gradients shift by `2 delta_i (. - xi0)` — absorbed by the abstract `au`/`aw`;
* block Hessians shift by `+-2 delta_i I` — absorbed by the asymptotic `psdi`
  with `cs_i = 4 delta_i`, via `shift_cancel_matrix`;
* **Hessian NORMS shift too** — the third cost, not budgeted for in the previous
  handover. It needs no limit: `delta_i < D0` uniformly, so it is absorbed into
  the constants (`norm_shifted_block` + `Cuni`/`habs` inside the theorem).

### Four obstructions to the TOP LEVEL found and removed

The previous handover called the top level "pure transcription". It is not —
three of its inputs could not be supplied at all, and one was outright false to
ask for. All four are now fixed, each with a named result:

1. **The `+1` attainment radius was fatal, not cosmetic.**
   `supconv_attained_ball` demanded `cball x (sqrt(...) + 1) ⊆ Omega`, i.e. a
   ball of radius ONE inside `interior K`. No bounded `K` satisfies that.
   `supconv_attained_ball_rad` / `_in_rad` / `_family_in_rad` take the radius as
   a parameter (any `R > sqrt (max 0 (2 eps (Bu - u x)))`), so the requirement
   splits into a geometric one (`cball x R ⊆ Omega`) and a smallness one on
   `eps`. `comparison_supconv_maximiser_complete` now uses that form.
2. **The Lipschitz hypothesis on `w` was unsuppliable.**
   `doubling_grad_lower_bound` converts a value gap into a position gap with a
   Lipschitz modulus; `max_principle_boundary` carries only continuity.
   `positive_separation_of_value_gap` replaces it by compactness (pairs
   realising a fixed gap `gamma > 0` are bounded away from the diagonal, else a
   convergent subsequence forces `gamma <= 0`), and
   `doubling_grad_lower_bound_sep` / `_norm_lower_bound_sep` /
   `_supconv_sep` are the Lipschitz-free chain. The separation `d` depends on
   `gamma`, `K`, `v` but **not on alpha**, which is the only uniformity used.
3. **The data are local, the sup-convolution is global.**
   `continuous_extension_bounded` (Tietze) + `bounded_on_compact` give a global
   bounded continuous representative; `visc_subsol_extend` /
   `visc_supersol_extend` carry the viscosity property across, using the same
   locality that made `max_principle_boundary_raw` refutable.
4. **The ball hypotheses all reduce to one geometric fact.**
   `cball_subset_interior_of_far_from_boundary`: a point of a closed `K` further
   than `kappa` from every point of `K - interior K` has its whole `kappa`-ball
   in `interior K` (a segment cannot leave `K` without meeting `frontier K`).
   `cball_prod_subset_of_far_from_boundary` is the product version for
   `cball xi0 r ⊆ K x K`.

### The localisation of the maximiser — abstract half proved

    supconv_le_of_local_bound      a local upper bound for u bounds supconv u eps
    supconv_radius_uniform         the threshold is O(sqrt eps), uniformly in x
    supconv_sandwich               u x <= supconv u eps x <= u x + sigma
    uniform_modulus_on_compact     the modulus, from compact_uniformly_continuous
    doubling_maximiser_value_transfer   Phi(xhat,yhat) >= Phi(z,z), with the
                                        two sigma errors and the penalty kept
    norm_lt_of_penalty_bound       penalty bound => |xhat - yhat| < beta
    doubling_maximiser_far_from_boundary
                                   the conclusion: kappa < dist xhat b for every
                                   b in K - interior K, from the single
                                   inequality `m + 2 sigma + tau + tau' < M`

Each small quantity is at the disposal of one parameter: `sigma` of `eps`,
`tau` of `alpha`, `tau'` of `kappa`; `m < M` is the gap being contradicted.

### The bridge is proved too: `comparison_from_localised_maximiser`

Given the doubling maximiser `xi0` over `K x K` TOGETHER with the single fact
that both components are further than `kappa` from `K - interior K`, EVERY
geometric hypothesis of `comparison_supconv_maximiser_complete` is derived and
`False` follows. Three derivations:

* `mxK` — a maximiser over `K x K` is one over `cball xi0 r` once that ball is
  inside `K x K` (`cball_prod_subset_of_far_from_boundary`, needs `r <= kappa`);
* `radu`/`radw` — `supconv_radius_uniform`, uniformly in the base point;
* `subu`/`subw` — triangle inequality plus `rho + R_u <= kappa`.

So the quantitative inputs left are exactly four inequalities
(`r <= kappa`, `rho + R_u <= kappa`, `rho + R_w <= kappa`, `2|alpha|rho < c`)
and two smallness conditions on `eps`
(`2 eps (Bu - Blu) < R_u^2`, `2 eps (Bw - Blw) < R_w^2`).

### THE `p = 0` OBLIGATION IS DISCHARGED — this is the session's main result

**Correction to an earlier claim in this same block: a mathematical gap DID
remain, and it was already documented** (Comparison_Assembly, the text after
`env_contradiction_at_zero`): the closing chain required `p != 0`, i.e. the
doubling maximiser off the diagonal, or else the no-gap condition
`eq36_rhs k L X <= F(0,X)`. That mattered acutely for the top level, because
the localisation argument *drives* `alpha` up, and large `alpha` drives the
maximiser ONTO the diagonal. The route as it stood was self-defeating.

Both disjuncts are now unnecessary:

    small_multiple_exists              delta with delta*C < g, C,g > 0
    mgap_shift_id                      mgap L M (M +- delta I) = delta*n*L/2
    shift_limit_absurd, ..._absurd2    the two bare-variable contradictions
    strict_contradiction_of_shifts_any_p
    comparison_env_from_jets_any_p     = comparison_env_from_jets minus `p != 0`

Why it works. The obligation looked unremovable only because the argument was
routed through the ENVELOPES, where the `p = 0` gap `F(0,M) < F*(0,M)` is real —
the constraint `a p = 0` in `feasible` drops a dimension as `p -> 0`, so the
infimum genuinely jumps. But the envelopes were never needed:
`subsol_shifted_bound` and `supersol_shifted_bound` already give bounds on
`ell_op` ITSELF at `X + delta I` and `Y - delta I` for every `delta`, and
`ell_op_M_gap` bounds the movement of `ell_op` under a matrix shift by
`mgap L M N`, which for `delta I` is `delta*n*L/2 -> 0`. So `delta` comes off by
an explicit estimate rather than by a semicontinuous envelope, leaving

    1 <= F(p,Y) <= F(p,X) <= theta < 1,

middle step `ell_op_elliptic_le`, outer steps the two shifted bounds. Nothing in
it mentions `p`.

**Scope of the consequence — read this carefully, it is narrower than it looks.**
`strict_contradiction_of_shifts_any_p` needs the two operator bounds at the SAME
`p`, exactly. That is the case whenever the two jets share their gradient
exactly, and there `p != 0` is now gone for good.

It does **not** by itself remove `p != 0` from the FAMILY chain. At the limit,
`env_strict_contradiction_of_shifted_limits` only has bounds at gradients `p'`,
`p''` that are NEAR `p` (they come from `Pu i -> p`, `Pw i -> p`), and moving
them onto a common `p` is exactly what the envelopes do — and what fails at
`p = 0`, since `ell_op` is discontinuous in `p` there. So the family chain still
carries `pnz`, and the earlier draft of this section overstated the result.

The obstruction at each finite index is concrete and worth naming: Jensen's
tilt. `tilted_doubled_jet_slices` gives the two slice gradients
`-fst pt + G` and `-(snd pt + G)`; they are exact negatives of one another iff
`fst pt + snd pt = 0`, which Jensen's lemma does not deliver (the admissible
tilts are a full-measure set, not a subspace). That mismatch is `O(||pt||)` and
vanishes only in the limit — which is why the limit, and with it continuity in
`p`, is there at all.

Environment note worth carrying: **`linarith` here fails on division by a
numeral** — `tt <= (x-y)/2 ==> 2*tt <= x-y` is rejected. State such steps
without divisions (see `shift_limit_absurd`).

### WHAT ACTUALLY REMAINS (read this before planning)

TWO things, in this order.

**(A) The `p = 0` obligation is RESOLVED — the paper's device is a QUARTIC
penalty, and the crux fact is now proved.**

Checked against the paper (arXiv:2512.17702). Two findings:

* Its Definition 3.1 uses the envelopes the way this development's limit
  produces them — subsolution `F_*(∇φ,∇²φ) ≤ 1`, supersolution
  `F^*(∇φ,∇²φ) ≥ 1`. So the envelope assignment here is right and there is no
  definitional escape.
* Its proof of Theorem 4.2(a) doubles with a **higher-order (quartic) penalty in
  `x - y`**, not the quadratic used throughout this theory. At a diagonal
  maximiser `x_eps = y_eps` a quartic penalty has vanishing gradient AND
  vanishing Hessian in `y`, so the test function the supersolution sees has
  second-order jet `(0,0)`, and the supersolution property reads
  `1 <= F^*(0,0) = 0`. Absurd — so the diagonal case cannot occur at all, and
  off the diagonal the common gradient is the penalty's gradient, hence nonzero
  automatically. That is the disjunct "arrange the doubling off the diagonal",
  achieved by changing the ORDER of the penalty rather than by tilting it.

The fact that makes it work is proved, in `subsection "A supersolution has no
vanishing second-order jet"`:

    ell_op_zero_matrix         F(p, 0) = 0 for EVERY p, origin included
    supersol_no_vanishing_jet  a supersolution has no (0,0) jet at an
                               interior point

The second is the formal content of `1 <= F^*(0,0) = 0`: `supersol_shifted_bound`
gives `1 <= F(0, -delta I)`, `ell_op_M_gap` gives
`F(0,-delta I) <= F(0,0) + delta*n*L/2 = delta*n*L/2`, and `small_multiple_exists`
kills it.

**So what remains for 4.2(a) is engineering, not mathematics: redo the doubling
with a quartic penalty.** The obstacle is localised — the theorem-on-sums layer
here is set up for a penalty with CONSTANT Hessian (`alpha*I` appears explicitly
in `tilted_doubled_jet_slices`, `tilted_doubled_psd_ordering`,
`norm_block_matrices_bounded`). With a quartic the block Hessian at the
maximiser is `P''(xhat-yhat)`, still symmetric and still with the
`[[Z,-Z],[-Z,Z]]` block structure, so the shape of every one of those lemmas
survives; `alpha` is replaced by the matrix `P''(xhat-yhat)` throughout. Budget
it as a re-run of stages 3-10 with `alpha *_R v` replaced by `Z *v v`.

**The quartic penalty's calculus is already in place** (subsection "The quartic
penalty and its exact second-order expansion"), so the refactor starts from
proved ground:

    quartic_pen                        P(d) = (beta/4)(d.d)^2
    quartic_pen_expand                 the EXACT expansion (no differentiability
                                       machinery: (s+t)^2 - s^2 collected by
                                       powers of h)
    quartic_pen_remainder              the O(|h|^3) tail is o(|h|^2)
    quartic_pen_jet                    gradient beta(d.d)d, quadratic form
                                       h |-> beta(d.d)(h.h) + 2beta(d.h)^2
    quartic_pen_grad_zero_iff          the gradient vanishes ONLY at d = 0
                                       — this is what makes the device work
    quartic_pen_vanishing_jet_at_zero  at d = 0 BOTH gradient and quadratic form
                                       vanish, i.e. the (0,0) jet that
                                       supersol_no_vanishing_jet refutes

The last two are the whole point: off the diagonal the common gradient is
nonzero automatically, and on the diagonal the configuration is impossible.

**The refactor is STARTED and its keystone is proved.** The two slice lemmas —
the ones that produce the two jets with exact-negative gradients, and the only
place where the quadratic's exact expansion was really being used — now exist in
general form:

    doubled_jet_slice_fst_gen   jet of a at xhat: gradient  fst q + G,
                                Hessian  fst (W (h,0)) + Z h
    doubled_jet_slice_snd_gen   jet of b at yhat: gradient  snd q - G,
                                Hessian  snd (W (0,h)) + Z h

They take the penalty as an abstract `P` plus its jet `(G, Z)` at `xhat - yhat`,
and are exactly the quadratic statements with `alpha *_R (xhat - yhat)` replaced
by `G` and `alpha *_R h` by `Z *v h`. Both compiled essentially first try, which
is the evidence that the rest of the substitution really is mechanical.

The proof pattern is worth knowing before continuing: the quadratic versions
rewrite the slice numerator by an EXACT identity (a quadratic's expansion is
exact); for a general `P` the expansion has a remainder, so instead of a rewrite
one ADDS the two limits — the slice numerator of `Psi` and the jet remainder of
`P` sum exactly to the slice numerator of `a`, because `P(d+h) - P(d)` cancels.
`tendsto_add` then does the whole job. The `snd` version additionally transports
the `P`-jet along `h |-> -h` (a filter isomorphism of `at 0`, `negfilt`); both
sign flips in `(-h) . (Z (-h))` cancel, which is precisely why the two slice
gradients come out as exact negatives.

Two more done in the same style, both green essentially first try:

    tilted_doubled_jet_slices_gen           q = -pt plus the two slices, for a
                                            general P. Pure transcription:
                                            global_max_imp_interior_max and
                                            gradient_is_minus_tilt were already
                                            abstract in Psi.
    tilted_doubled_hessian_nonpositive_gen  v . W v <= 0. Needs NO jet of P at
                                            all — second_order_interior_max is
                                            about the FULL functional's Hessian,
                                            and P only has to be present for the
                                            maximum to be a maximum.

**THE ONE NON-MECHANICAL STEP IS NOW PROVED.** `doubled_penalty_jet` (green,
first try, eps-delta and all) — see `subsection "The doubled penalty's jet, for
an arbitrary penalty"`. With it, EVERYTHING remaining in the psd chain is
transcription of the kind already done four times. The analysis that led to it is
kept below because it explains why the lemma has the shape it does.

The psd chain is `sums_matrix_inequality` (Sup_Convolution:7171) ->
`sums_gives_ordering` -> `sums_ordering_at_interior_max` ->
`sums_psd_at_interior_max` -> `sums_psd_from_jet` ->
`tilted_doubled_psd_ordering`. The top five are transcriptions. The bottom one
is not: its proof `define`s the penalty's Hessian operator
`P k = alpha *_R (fst k - snd k, snd k - fst k)` and gradient
`g0 = alpha *_R (fst zh - snd zh, -(fst zh - snd zh))`, and then uses an EXACT
identity `pen` for the quadratic. For a general penalty that identity becomes
asymptotic, so it has to be replaced by a lemma. State it as

    lemma doubled_penalty_jet:
      assumes Pjet: "((%h. (P ((fst zh - snd zh) + h) - P (fst zh - snd zh)
          - G . h - (h . (Z *v h))/2) / (norm h)^2) ---> 0) (at 0)"
      shows "((%k. (P (fst (zh+k) - snd (zh+k)) - P (fst zh - snd zh)
          - (G, -G) . k
          - (k . (Z *v (fst k - snd k), Z *v (snd k - fst k)))/2)
            / (norm k)^2) ---> 0) (at 0)"

i.e. the Hessian operator is `k |-> (Z(fst k - snd k), Z(snd k - fst k))` and the
gradient is `(G, -G)`, exactly the quadratic's shapes with `alpha *_R` replaced
by `Z *v`.

The proof has two halves. **Algebra** (all one `simp`, given a local
`Z *v (u - v) = Z *v u - Z *v v` proved entrywise): writing `e k = fst k - snd k`,
one has `fst (zh+k) - snd (zh+k) = (fst zh - snd zh) + e k`,
`(G,-G) . k = G . (e k)`, and
`k . (Z(e k), Z(-(e k))) = (e k) . (Z *v (e k))` — so the whole numerator is
exactly `R (e k)`, where `R` is the numerator of `Pjet`.

**Limit** (the only real work, an eps-delta argument, ~40 lines): one needs
`R (e k)/||k||^2 -> 0` from `R h/||h||^2 -> 0`. Note `||e k|| <= 2||k||`, so for
`e k /= 0`, `|R (e k)|/||k||^2 <= 4 |R (e k)|/||e k||^2`; and for `e k = 0`
(the diagonal, where `k /= 0` is possible) `R 0 = 0` so the quotient is `0`.
Hence: given `eps > 0`, take `delta` from `Pjet` at `eps/4`, and use `||k|| <
delta/2`. Use `tendstoI` / `tendstoD` with `eventually_at`; do NOT try to route
it through `filterlim_compose`, since `e` is not injective near `0`.

Both halves are formalised. The one trap worth repeating: do NOT route the limit
through `filterlim_compose` — `e` is not injective near `0`, and the diagonal
`e k = 0` with `k /= 0` is exactly the case that makes the composition view
wrong and the eps-delta view easy (`R 0 = 0`, so the quotient is `0` there).

Three more of the psd chain are now done and green:

    matrix_vector_mult_scaleR_gen     Z *v (s *_R u) = s *_R (Z *v u)
    sums_matrix_inequality_gen        the ordering, with doubled_penalty_jet
                                      ADDED to expPsi where the quadratic
                                      version rewrote by the exact identity `pen`
    sums_gives_ordering_gen           the same in <= form
    sums_ordering_at_interior_max_gen with `neg` discharged at the interior max

One snag worth remembering: the `rem` step needs `by simp argo`, not `by simp` —
`- (x/2) - y/2 = - ((y + x)/2)` is the division-by-numeral case this dev
`linarith`/`simp` will not do (see the memory note).

The psd packaging is done too:

    inner_matrix_sym        v . (Z *v z) = z . (Z *v v) for symmetric Z
    linear_block_fst_gen / _snd_gen
    sym_block_fst_gen / _snd_gen
    sums_psd_at_interior_max_gen

The quadratic versions route through `linear_slice_fst` / `sym_slice_fst`, which
have the penalty's shape baked in; the general ones are proved DIRECTLY instead,
which is shorter. Two traps hit here: (i) `linear_of_bounded_linear_prod` is
defined further down the file than the new block, so use
`linear_conv_bounded_linear` instead; (ii) simp normalises `(x,0) + (y,0)` back
to `(x+y,0)`, so an `unfolding e ... by simp` of the additivity step silently
does nothing — use a calculational `also`/`finally` chain.

`tilted_doubled_psd_ordering_gen` is done too — **the psd half of the refactor is
complete**. No separate `sums_psd_from_jet_gen` or general
`doubled_tilted_interior_max` was needed: the tilt absorption is one
`inner_prod_def` step, done inline, and `sums_psd_at_interior_max_gen` already
carries the linearity and symmetry.

The Hessian norm bounds are done too, and the library had what was needed after
all (no entrywise proof required):

    norm_matrix_vector_le        ||Z v|| <= (sum_ij |Z_ij|) * ||v||, from
                                 onorm_le_matrix_component_sum + onorm
    quadform_matrix_bound        |v . (Z v)| <= (sum_ij |Z_ij|) * ||v||^2,
                                 by Cauchy_Schwarz_ineq2
    block_form_bound_fst_gen / _snd_gen
    norm_block_matrices_bounded_gen

The block bounds take the constant abstractly (`KZ`), so a caller with a sharper
bound for its own `Z` — the quartic's Hessian `beta((d.d) I + 2 d d^T)` has norm
`O(beta ||d||^2)` — can supply it instead of the entry sum.

**Item 4 is under way.** Proved and green, in order:

    doubled_functional_semiconvex_gen        transcription; the penalty was
                                             already isolated in one step
    doubled_supconv_jet_exists_gen           Jensen, one line
    semiconvex_shift_perturb                 the strict-gap perturbation, stated
                                             PENALTY-AGNOSTICALLY (the cost
                                             delta*||z||^2 - delta*||z-xi||^2 is
                                             AFFINE, so it works for any
                                             semiconvex Psi and the constant
                                             rises by exactly 2 delta)
    doubled_supconv_jet_exists_shifted_gen   Jensen for the shifted functional
    shifted_annulus_bound_split_gen          the annulus bound; also
                                             penalty-agnostic

Three consecutive layers turned out not to depend on the penalty at all — only
the jet-level lemmas ever did. That is why the shifted development needed no
parallel re-derivation.

`shifted_jensen_family_gen` is **PROVED** as well — placed immediately after
`shifted_jensen_family` (not with the other `_gen` lemmas) because `choice4` and
`shifted_family_parameters` are declared much further down the file. Two traps
it cost, both worth remembering:

  * **Check scope before choosing an insertion point.** Third instance tonight of
    "the helper is declared later in the file than the new block"
    (`linear_of_bounded_linear_prod`, `norm_sq_prod_split`, and these two).
  * **`OF: multiple unifiers`** on `shifted_annulus_bound_split_gen[OF mxK ...]`.
    Pinning `delta` alone was NOT enough — the ambiguity is higher-order, in how
    `?A (fst y) + ?B (snd y) - ?Pn (fst y - snd y)` splits against `mxK`. Pin all
    of `A`, `B`, `Pn`, `xi0`, `r` as well.

**ITEM 4 IS COMPLETE.** The entire Theorem 4.2(a) chain now runs under an
abstract penalty. Both remaining assembly theorems are proved and green:

 - `comparison_supconv_maximiser_complete_gen` (~430 lines) — the transcription
   of `comparison_supconv_maximiser_complete` with `alpha *_R v |-> Zf d *v v`,
   `alpha *_R (xhat-yhat) |-> Gf d` and `(alpha/2)||d||^2 |-> Pn d`, where
   `d = fst (zf i) - snd (zf i)` is the displacement of the `i`-th maximiser.
 - `comparison_from_localised_maximiser_gen` — the bridge.

Plus seven support lemmas needed along the way: `block_fst_matrix_apply_gen`,
`block_snd_matrix_apply_gen`, `transpose_matrix_block_fst_gen`,
`transpose_matrix_block_snd_gen`, `diff_displacement_bound`,
`penalty_gradient_nearby_upper_gen`, `penalty_gradient_nearby_bound_gen`.

**`comparison_supconv_bounded_family` and `comparison_supconv_sequence_complete`
needed no generalisation** — checked, not guessed. They never mention the penalty
in their hypotheses: they take `jetu`, `jetw`, `symX`, `symY`, `psdi`, `bX`,
`bY`, `au`, `aw`, `glb` as abstract data about matrices and gradients. The
penalty only ever enters in how that data is PRODUCED. Both are reused verbatim.

Two design points worth keeping:

 - **The jet hypothesis must be a FIELD, not a single jet.** `Pjet` is
   universally quantified over the base point `d`, because the point where the
   penalty's jet is needed is `fst (zf i) - snd (zf i)`, which varies with `i`
   and is only produced INSIDE the proof by Jensen's lemma. Same for `symZ`.
   `bZ` and `lipG` are likewise uniform in `d`. This is why the signature carries
   `Gf, Zf :: real^'n => _` rather than `G, Z`.
 - **`jet_transfer_quadratic` is still correct here** — contrary to what an
   earlier version of this file said. The `-delta*||x-c||^2` tilt introduced by
   Jensen's lemma is genuinely quadratic and is NOT part of the penalty, so it
   still transfers by the quadratic rule. `jet_transfer_linear` is unused in this
   chain.

**THE INSTANTIATION AT `soft_pen` IS COMPLETE.** All five obligations green:

 | obligation | discharged by | constant |
 |---|---|---|
 | `sc`   | `soft_pen_semiconcave` | |
 | `symZ` | `soft_hess_sym`        | |
 | `Pjet` | `soft_pen_jet_field`   | gradient field `soft_grad k`, Hessian field `soft_hess k` |
 | `bZ`   | `soft_hess_bound`      | `KZ = 2k` |
 | `lipG` | `soft_grad_lipschitz`  | `KG = 3k` |

and `comparison_from_localised_maximiser_soft` is the whole chain with no
abstract penalty data at all — it mentions only `kappa_P`.

**CORRECTION — the earlier "do NOT prove this algebraically, differentiate
instead" note in this file was WRONG, and cost nothing only because it was
re-examined.** The algebraic route fails only for the SHARP constant 1. But `KG`
is a FREE PARAMETER of the chain, so a non-sharp constant is just as good, and
for a non-sharp constant the algebra is easy. The whole thing is ~120 lines and
needed no differentiation, no `differentiable_bound`, no `onorm`, and no
operator-norm-of-a-PSD-matrix theory:

 1. `soft_R_lipschitz` — `R` is 1-Lipschitz. From `R x^2 - R y^2 = |x|^2 - |y|^2`
    and `(Rx - Ry)(Rx + Ry) = Rx^2 - Ry^2`, get
    `|Rx - Ry|(Rx + Ry) = ||x|-|y||(|x|+|y|)`, then `||x|-|y|| <= |x-y|` and
    `|x|+|y| <= Rx+Ry` and cancel the positive factor.
 2. `soft_shrink_lipschitz` — `d |-> d/R d` is **2**-Lipschitz (not 1, and that
    is fine). With `s = Rx`, `t = Ry`: `(st)(x/s - y/t) = tx - sy
    = t(x-y) + (t-s)y`, so `st|shrink x - shrink y| <= t|x-y| + |x-y|t`; cancel
    `t > 0`, then use `s >= 1`.
 3. `soft_grad_lipschitz` — `soft_grad k d = k*d - k*(shrink d)`, so `3k`.

**Method lesson worth keeping:** before committing to a heavy analytic route,
check whether the constant actually has to be sharp. Here it did not, and the
non-sharp version was an order of magnitude cheaper.

Every step is stated as a PRODUCT inequality and cancelled at the end, never as
a quotient — this dev `linarith` refuses divisions by numerals and `field_simps`
unfolds `sqrt t ^ 2` unhelpfully.

**The diagonal dichotomy and the parameter choice are done too.** These are what
supply `glb` and `rsmall`:

 - `soft_grad_zero`, `soft_hess_zero` — at `d = 0` BOTH the gradient and the
   Hessian of `soft_pen` vanish. This is exactly the property the penalty was
   designed to have: at a diagonal maximiser the supersolution's test function
   would have jet `(0,0)`, which `supersol_no_vanishing_jet` forbids. So the
   diagonal configuration is impossible and `d != 0` is automatic.
 - `soft_R_gt_one`, `soft_grad_coeff_pos`, `soft_grad_nonzero`,
   `soft_grad_norm_pos` — off the diagonal the gradient is nonzero as soon as
   `kappa > 0`, since `R d > 1` makes `kappa(1 - 1/R d)` strictly positive.
 - `soft_grad_norm_eq`, `soft_rsmall_of_rho`, `soft_gap_pos`,
   `exists_small_rho_aux`, `soft_rho_exists` — the parameter choice.

**`kappa` CANCELS in `rsmall`.** Taking the natural `c` (the actual gradient norm
at the maximiser), `(3k)(2rho) < norm (soft_grad k d) = k(1 - 1/R d)|d|` becomes
`6 rho < (1 - 1/R d)|d|` — independent of `k`. So the non-sharp constant `3k`
costs exactly a factor three in the `rho` threshold and nothing else. An
adversarial check of the whole chain confirmed **there is no lower bound on
`rho` anywhere**; every constraint on it is an upper bound.

**The localisation layer ports with two lemmas.** Of its eleven lemmas only two
mention the penalty, and `doubling_maximiser_far_from_boundary` — the one that
PRODUCES `farx`/`fary` — is already penalty-free (it takes the penalty only
through the abstracted `tr` and `near`). Done:

 - `doubling_maximiser_value_transfer_gen` — needs only `Pn 0 = 0`, supplied by
   `soft_pen_zero`.
 - `norm_lt_of_penalty_bound_gen` — needs only coercivity, and in general form
   not even monotonicity; one-line contraposition. `soft_pen`'s coercivity comes
   from `sqrt_shift_diff_bound` + `soft_pen_radial_mono` + `soft_pen_mono_norm`.

**The existence layer ports with a one-line substitution.** `doubling_maximiser_exists`
uses the penalty in exactly ONE step — `cpen`, its continuity — and everything
else is `compact_Times` + `continuous_attains_sup`. So
`doubling_maximiser_exists_gen` just takes `continuous_on UNIV Pn` as a
hypothesis, and `doubling_maximiser_exists_soft` discharges it with
`soft_pen_continuous`. Both green.

**#6 is SMALLER than this file said elsewhere — the target already exists in
corrected form.** `max_principle_boundary` (Lemma_3_1_Envelopes.thy:722) is
already the continuity-carrying predicate; the refutable one was renamed
`max_principle_boundary_raw` and is kept only as the counterexample's target.
See the detailed block at "STOP: `max_principle_boundary` IS FALSE" below, which
records this properly. So #6 is "prove the existing predicate", NOT "design and
prove a replacement". Note the project deliberately chose CONTINUITY over the
sharper "u usc, w lsc" — this HOL-Analysis has no semicontinuity library, and
only `max_principle_boundary_attains` would need reproving to sharpen it.

**The dichotomy layer is ported.** `doubling_diagonal_max_gen`,
`doubling_off_diagonal_gen`, `doubling_diff_nonzero_gen`,
`doubling_penalty_bound_gen`, `doubling_ge_diagonal_gen` — all green first try,
each using the penalty only through `Pn 0 = 0`, exactly as predicted by reading
them.

**A GAP the port would otherwise have hit, now closed.** `doubling_complete`'s
second conjunct is `(norm (xh-yh))^2 <= 2*(C - (u z - w z))/alpha` — it INVERTS
the quadratic penalty by dividing by `alpha`. That step has NO analogue for a
general penalty: `doubling_penalty_bound_gen` yields only `Pn d <= C0`, and
turning that into `norm d < beta` needs coercivity.

The fix rests on a fact worth stating plainly: **`soft_pen` is LINEAR IN
`kappa`**. Writing `soft_pen k d = k * h(|d|^2)` with
`h(s) = s/2 - sqrt(s+1) + 1`, positivity of `h` for `s > 0` is one squaring
after the substitution `s = 2c`: `sqrt(2c+1) < c+1` iff `2c+1 < c^2+2c+1` iff
`0 < c^2`. Substituting removes every division, which is what makes it go
through in this dev. So at a fixed radius `beta` the penalty grows like `kappa`
and eventually beats the fixed `C0` — the `kappa -> infinity` mechanism, exactly
parallel to `alpha -> infinity`. Proved: `sqrt_lt_half_plus_one`,
`radial_profile_pos`, `soft_pen_ge_radial`, `soft_pen_coercive_outside` (in
exactly the shape `norm_lt_of_penalty_bound_gen` consumes), `soft_pen_kappa_exists`.

**The `kappa -> infinity` step is DONE.** `doubling_near_soft` and
`doubling_close_maximiser_soft` — the `soft_pen` analogue of
`doubling_dist_bound`. For the quadratic penalty one divides `(alpha/2)|d|^2 <= C0`
by `alpha`; here one instead uses that the penalty at radius `beta` grows
linearly in `kappa` and so eventually exceeds the FIXED `C0`, forcing the
maximiser inside radius `beta`.

**Note the quantifier order, which is the whole point:** `beta` is given FIRST
and `kappa` chosen afterwards to match it. The maximiser then depends on
`kappa`, so the statement must produce `kappa` AND the maximiser together —
one cannot fix a maximiser and then ask for a `kappa`. This is the shape the
rest of the assembly has to follow.

**The `epsilon -> 0` step is DONE too.** `supconv_uniform_upper`:
`exists eps > 0` such that `supconv u eps x <= u x + sigma` for ALL `x` in `K`.
`supconv_sandwich` is pointwise and needs a LOCAL modulus on a ball that sticks
out of `K`; the assembly needs it at the doubling maximiser, which is not known
in advance, hence the uniform form. The fix: run `uniform_modulus_on_compact`
not on `K` but on a `cball 0 R` containing the 1-neighbourhood of `K`, and cap
the modulus radius at 1 so the ball around any point of `K` stays inside.
**This is where the earlier reduction to globally continuous, globally bounded
data (`continuous_extension_bounded`, `visc_subsol_extend`) pays off** — without
it there would be no modulus to take just outside `K`. Helper: `exists_eps_aux`.

**Both steps are also available in the sup-convolution shape the assembly
actually consumes**: `doubling_maximiser_supconv_soft` and
`doubling_close_maximiser_supconv_soft`. The sign flip is the standard one —
instantiate the general form at `u := supconv (theta u) eps` and
`w := %y. - supconv (-w) eps y`, so `u x - w y` becomes
`supconv (theta u) eps x + supconv (-w) eps y`, then close with `simp`.

**Inventory of the four smallness steps** (all four now exist as standalone
verified lemmas — what remains is threading them, not proving them):

 | step | supplies | lemma |
 |---|---|---|
 | `kappa_P -> infinity` | `near`: `dist xh yh < beta` | `doubling_close_maximiser_supconv_soft` |
 | `eps -> 0` | `sigma`: `supconv <= . + sigma` on `K` | `supconv_uniform_upper` |
 | modulus at `beta` | `tau` in `modg` | `uniform_modulus_on_compact` |
 | modulus at `kappa` | `tau'` in `modF` | `uniform_modulus_on_compact` |
 | `rho` | `glb` + `rsmall` | `soft_rho_exists`, `soft_rsmall_of_rho` |

**THE PARAMETER THREADING IS DONE.** `doubling_localised_maximiser_soft`
(~150 lines) produces, from a compact `K`, bounded/continuous data, and an
interior/boundary gap `m < M`:

    exists eps > 0, kappa_g > 0, kappa_P > 0, xh in K, yh in K.
        (xh,yh) maximises the soft_pen-doubled sup-convolution functional
      AND both components are further than kappa_g from K - interior K

which is exactly the `mxKK`/`xK`/`yK`/`farx`/`fary` package that
`comparison_from_localised_maximiser_soft` consumes. The order it threads:

    G = M - m, split as sigma = tau = tau' = G/8   (so m + 2sigma+tau+tau' < M)
    tau  -> beta0    (modulus of g on K)
    tau' -> kappa0   (modulus of f+g on K)
    kappa_g = kappa0/2, beta = min beta0 (kappa0/2), so kappa_g + beta <= kappa0
    sigma -> eps     (supconv_uniform_upper TWICE, then the minimum)
    beta  -> kappa_P and with it the maximiser
    doubling_maximiser_far_from_boundary at radius kappa_g + beta

**A CONSTRAINT ON `eps` THAT THE BOUNDARY ARGUMENT CANNOT SEE.** Found only when
checking the connection to `comparison_from_localised_maximiser_soft`, and the
theorem as first proved was NOT enough without it. That consumer wants

    smallu: 2*eps*(Bu - Blu) < R_u^2      and     fitu: rho + R_u <= kappa

so `R_u` must be simultaneously LARGE relative to `eps` and SMALL relative to
`kappa_g`. That forces `eps` small in a way nothing in the boundary argument
mentions. It is consistent only because `kappa_g` is fixed at step 4, BEFORE
`eps` is chosen at step 5 — if the order were reversed there would be no way to
satisfy both. `doubling_localised_maximiser_soft` therefore also delivers

    2*eps*(Bu - Blu) < (kappa_g/4)^2   and   2*eps*(Bw - Blw) < (kappa_g/4)^2

so downstream one may take `R_u = R_w = kappa_g/4`, leaving `rho <= 3*kappa_g/4`
and `r = kappa_g`. Factored helper: `eps_mono_aux` (the shrink-eps step, which
was duplicated inside `supconv_uniform_upper`).

Two more things worth keeping:

 - **The `yh` bound is free.** Apply the boundary theorem at radius
   `kappa_g + beta`; then `dist yh b >= dist xh b - dist xh yh > kappa_g`. No
   second modulus for `f` is needed — the quadratic development never had one
   either.
 - **`soft_pen_nonneg` is needed for `tr`.** `doubling_maximiser_value_transfer_gen`
   yields `f z + g z + Pn(xh-yh) <= f xh + g yh + 2 sigma`, but
   `doubling_maximiser_far_from_boundary` wants it WITHOUT the penalty term, so
   the penalty has to be dropped — which needs it non-negative.

**TRAP, and it cost a round:** closing this theorem with a single
`... by blast` over the nested existential made PIDE flag
`still_running_possibly_nonterminating`. Per the standing note in this file,
that flag MEANS IT even when the same entry shows `timing_ms: 1` and
`No subgoals!`. Replaced with an explicit
`rule exI[of _ t], rule conjI[OF ...], ..., rule bexI[OF _ ...]` chain and the
flag cleared. Do not "simplify" it back to `blast`.

### THE DIAGONAL BRANCH IS A SEPARATE SUB-ARGUMENT. Read this before assembling.

Connecting `doubling_localised_maximiser_soft` to
`comparison_from_localised_maximiser_soft` needs `glb`:
`c <= norm (soft_grad kappa_P (xh - yh))` with `c > 0`, hence `xh != yh`. I
traced how to get that and it is NOT available from the doubling alone:

 - `doubling_off_diagonal_gen` would give `xh != yh`, but its hypothesis `gt` is
   `A xh + B xh < A x + B x` for some `x in K` — i.e. the maximiser does not
   also maximise along the DIAGONAL. Nothing so far supplies that.
 - Suppose instead `xh = yh`. Then `doubling_diagonal_max_gen` gives
   `A x + B x <= A xh + B xh` for all `x in K`, and combining with
   `M <= A z + B z` and the uniform upper bounds yields
   `theta u xh - w xh >= M - 2 sigma > m`. So `xh` is interior — CONSISTENT with
   everything proved, no contradiction. **Worked through explicitly; the
   diagonal branch does not close by doubling/boundary reasoning.**

That is not a defect, it is the structure of the argument: the diagonal case
says the regularised `u - w` attains its maximum at an interior point, which is
exactly what 4.2(a) asserts is impossible — so refuting it IS the theorem, and
it must be closed by the PDE, not by the doubling. This is precisely what the
penalty was designed for and the pieces are already proved:

    soft_grad_zero, soft_hess_zero    the penalty's jet at d = 0 is (0,0)
    soft_pen_vanishing_jet_at_zero    the raw quotient form
    doubled_penalty_jet               transports (G,Z) to the product space;
                                      at G = 0, Z = 0 the doubled penalty
                                      contributes nothing
    supersol_no_vanishing_jet         a supersolution has no (0,0) jet at an
                                      interior point  ==>  contradiction

So the remaining work splits cleanly in TWO, and they are independent:

 (A) OFF-DIAGONAL — **DONE**: `comparison_soft_off_diagonal`. Given the
     localised maximiser AND `xh != yh`, every remaining parameter is
     determined and `False` follows. The choices, all forced:
       `R_u = R_w = kappa_g/4`  (so `smallu`/`smallw` are EXACTLY what
                                 `doubling_localised_maximiser_soft` delivers)
       `r = kappa_g`
       `rho < 3*kappa_g/4` and small enough for the gradient threshold, by
                                 `soft_rho_exists`
       `c = norm (soft_grad kappa_P (xh-yh))`, positive by `soft_grad_norm_pos`
       `D_0 = 1`
     `rsmall` is `soft_rsmall_of_rho`; `glb` holds by reflexivity because `c` IS
     the gradient norm.
 (B) DIAGONAL — REMAINS, and there are TWO CONCRETE OBSTACLES, both found by
     reading the statements rather than assuming. Do not start writing until
     these are resolved; task #16.

     What a diagonal maximiser DOES give is now proved:
       `soft_pen_neg`                  `soft_pen k (-d) = soft_pen k d`
       `diagonal_max_increments`       `B y - B p <= Pn (p - y)` and
                                       `A x - A p <= Pn (x - p)`
       `diagonal_max_increment_soft`   `B (p+h) - B p <= soft_pen k h`

     OBSTACLE 1 — TWO-SIDEDNESS — **RESOLVED. The two-sided hypothesis is NOT
     needed, and the one-sided replacements are now proved.**
     `jet` is never inspected where it is assumed; it is forwarded four hops:
       `supersol_no_vanishing_jet` -> `supersol_shifted_bound`
       -> `jet_imp_local_min_test` -> `superjet_local_max` (Sup_Convolution.thy:7637)
     and `superjet_local_max` is the SOLE consumer. It derives `|q| < delta/2`
     from `tendstoD` and then, two lines later, `using babs by linarith` keeps
     only `q < delta/2` — **the lower half is discarded immediately and nothing
     downstream recovers it.**

     Proved (additive; the two-sided versions are left untouched):
       `superjet_local_max_onesided`  — hypothesis
           "!!c. 0 < c ==> eventually (%kk. (u(xh+kk) - u xh - p.kk
                - (kk . X kk)/2) / (norm kk)^2 < c) (at 0)"
       `onesided_of_tendsto`          — the old hypothesis implies the new one,
                                        so this is a genuine WEAKENING and any
                                        existing caller can be routed through it.

     **The quantifier over the threshold `c` is necessary, not cosmetic**: in
     `supersol_no_vanishing_jet` the `delta` is produced INSIDE the proof by
     `small_multiple_exists`, after the hypothesis has been fixed. A version
     with `c` fixed to `delta/2` would not compose.

     **THE FULL ONE-SIDED CHAIN IS NOW PROVED**, all five links, all additive
     (the two-sided originals are untouched and still used everywhere else):
       `superjet_local_max_onesided`
       `onesided_of_tendsto`                 (the weakening bridge)
       `jet_imp_local_min_test_onesided`
       `supersol_shifted_bound_onesided`
       `supersol_no_vanishing_jet_onesided`
     Each of the last three is its two-sided proof VERBATIM with the hypothesis
     swapped and the call redirected to the `_onesided` predecessor — exactly as
     the investigation predicted, zero proof-step changes.

     **STEP 2 OF THE WIRING IS ALSO DONE.** The bridge from "increment is
     dominated by something `o(|h|^2)`" to the one-sided hypothesis:
       `onesided_of_tendsto_gen`      generic, any `D`
       `onesided_of_dominated`        `dom` stated EVENTUALLY, not globally —
                                      the maximiser inequality only holds while
                                      `p + h` stays in `K`, which for interior
                                      `p` is a neighbourhood condition
       `soft_pen_little_o`            `soft_pen k h / |h|^2 --> 0`
       `diagonal_increment_onesided`  the two combined, at `soft_pen`

     **ALL FOUR WIRING STEPS NOW EXIST AS VERIFIED LEMMAS:**

       1. `diagonal_max_increment_soft`   `B(p+h) - B p <= soft_pen k h`
       2. `diagonal_increment_onesided`   that IS the one-sided hypothesis shape
       3. `supconv_onesided_descent`      descends it from `supconv u eps` at
                                          `x` to `u` at the attainment point `ys`
       4. `supersol_no_vanishing_jet_onesided`   contradiction

     Step 3 is the interesting one. `supconv_local_max_transfer_ball` descends a
     local max for a FIXED quadratic; the `o(|h|^2)` version is obtained by
     applying it ONCE PER THRESHOLD — given `c`, the one-sided bound at
     threshold `c/2` is exactly a local max for the quadratic `c *_R mat 1` with
     ZERO gradient, and the descent then yields `u z - u ys <= (c/2)|z-ys|^2` on
     a ball around `ys`, which is the one-sided bound at threshold `c` for `u`
     at `ys`. **Quantifying over `c` is what makes the Hessian effectively zero
     without ever having to produce a jet with a vanishing second-order term
     directly** — that is the trick that makes the whole diagonal branch work.

     **CHAINED AND PROVED: `comparison_soft_diagonal`.** At a diagonal maximiser
     `p` (interior, which the localisation already gives), it obtains the
     attainment point from `supconv_attained_in_rad`, derives the neighbourhood
     condition from `p in interior K`, and applies steps 1-4 in order.

     Note it uses NO property of the subsolution side at all — only the `B` half
     of the maximiser inequality is consumed. That is why the diagonal case is
     genuinely a different argument from the off-diagonal one, which needs the
     full jet machinery on both sides.

**SO BOTH BRANCHES OF THE COMPARISON ARGUMENT NOW CLOSE:**

    comparison_soft_off_diagonal   (A)  xh ~= yh
    comparison_soft_diagonal       (B)  xh  = yh

and `doubling_localised_maximiser_soft` produces the maximiser that feeds
either.

## THE COMPARISON ARGUMENT IS COMPLETE: `comparison_soft_complete`

Batch-verified. It states: compact nonempty `K`, bounded and globally
continuous `theta*u` and `-w`, a viscosity sub/supersolution pair on
`interior K`, a point `z` in `K` with `M <= theta u z - w z`, and
`theta u c - w c <= m` on `K - interior K` with `m < M`  ==>  `False`.

Supplying branch (B)'s geometric hypotheses from the localisation was the only
work in the case split:
  `xh in interior K`  — a boundary `xh` would give `kappa_g < dist xh xh = 0`
  `cball xh (kappa_g/4) subset interior K` —
      `cball_subset_interior_of_far_from_boundary` at `kappa_g`, then shrink
  the attainment radius bound — `supconv_radius_uniform`, whose smallness
      hypothesis is EXACTLY the extra `eps`-bound that
      `doubling_localised_maximiser_soft` was strengthened to deliver two
      rounds earlier. The two decisions turned out to be the same decision.

## WHAT REMAINS FOR 4.2(a): only #6, the packaging

`max_principle_boundary` (Lemma_3_1_Envelopes.thy:722) is already the corrected
continuity-carrying predicate. Every piece needed exists:

 1. `K ~= {}` and `0 < CARD('n)` as side conditions — **the predicate is FALSE
    for `K = {}`**: the hypotheses hold vacuously but the conclusion asserts
    membership in the empty set. Recorded at `compact_frontier_nonempty`.
 2. `bounded_on_compact` gives `B` bounding `|u|`, `|w|` on `K`.
 3. `continuous_extension_bounded` extends to globally continuous, globally
    bounded `u'`, `w'` agreeing on `K`.
 4. `visc_subsol_extend` / `visc_supersol_extend` transfer the viscosity
    properties (they rest on the LOCALITY of the definition, i.e.
    `visc_subsol_cong_on`).
 5. `max_principle_boundary_attains` gives the maximiser `xs`; set
    `M = u xs - w xs`.
 6. For contradiction assume no BOUNDARY maximiser. `K - interior K` is compact
    (closed subset of compact) and NONEMPTY (`compact_frontier_nonempty`), so
    `continuous_attains_sup` gives `m` = max over the boundary, with `m < M`.
 7. `theta_gap_preserved` — for `theta < 1` close enough to 1 the gap survives
    the scaling; needs `(1-theta)*(2B) < M - m`.
 8. `comparison_soft_complete` gives `False`.

Estimate ~200 lines; the fiddly parts are threading the extension (3-4) and
choosing `theta` (7).

     BONUS, worth exploiting: `ell_op_zero_matrix` is proved for an ARBITRARY
     `p`, and `feasible_nonempty` / `ell_op_M_gap` / `mgap_shift_id` are all
     `p`-agnostic. So the tail of `supersol_no_vanishing_jet` goes through with
     jet data `(p, 0)` for any `p` — **only the HESSIAN has to vanish, not the
     gradient.** (Reported analytically, not machine-checked; verify before
     relying on it.)

     OBSTACLE 2 — THE SUP-CONVOLUTION GAP — **RESOLVED: the lemma exists.**
     The descent from a local-max statement about `supconv u eps` at `x` to one
     about `u` at the ATTAINMENT point `ys` is

         `supconv_local_max_transfer_ball`   (Comparison_Assembly.thy:5407)

     which takes `opt: supconv u eps x = u ys - (dist x ys)^2 / (2*eps)` plus a
     local-max statement for `supconv u eps` on a ball around `x`, and returns
     the corresponding local-max statement for `u` on a ball around `ys`. It is
     packaged for the supersolution side as `supersol_shifted_bound_supconv`.
     The attainment point itself comes from `supconv_attained_in_rad`. So the
     diagonal branch reuses exactly the machinery the off-diagonal chain uses;
     nothing new is required here.

Do NOT try to close (B) with more doubling estimates — that was checked and it
does not work.

Remaining for 4.2(a) — every ingredient now exists:

 0. **NOTE `supconv_uniform_upper`'s SHAPE.** It concludes
    `exists eps0 > 0. forall eps. 0 < eps --> eps <= eps0 --> ...`, not just
    `exists eps`. That is deliberate and load-bearing: the assembly needs ONE
    `eps` serving BOTH sup-convolutions (`theta u` and `-w`), so it applies the
    lemma twice and takes `min eps0 eps0'`. The bound survives shrinking `eps`
    because `Bu - Bl >= 0` always (the function's own bounds bracket it).
    If you re-derive this, do not weaken it back to a bare existential.

 1. **The parameter-threading assembly.** Produce the maximiser with
    `doubling_maximiser_supconv_soft` (already in the `+ supconv (- w)` shape
    `mxKK` wants), run `doubling_off_diagonal_gen` to get `d != 0`, get
    `farx`/`fary` from `doubling_maximiser_far_from_boundary` (penalty-free) fed
    by `doubling_maximiser_value_transfer_gen` and
    `norm_lt_of_penalty_bound_gen` + `soft_pen_coercive_outside`, pick `rho` by
    `soft_rho_exists`, set `c = norm (soft_grad kappa_P d)` and discharge
    `rsmall` by `soft_rsmall_of_rho`. Feed
    `comparison_from_localised_maximiser_soft`.

    **This is the hard part that remains, and it is bookkeeping, not
    mathematics: the QUANTIFIER ORDER.** The parameters are chosen in a
    dependent sequence — the boundary gap fixes `kappa` (the geometric one),
    the modulus fixes `epsilon`, coercivity fixes `kappa_P`, and only then does
    the gradient at the resulting maximiser fix `rho`. Getting that order wrong
    is the classic way this argument fails to assemble. Expect this to be the
    largest single remaining piece.
 2. Then #6: prove `max_principle_boundary k L K` from that.

Remaining for 4.2(a):
 3. **Semiconvexity of the quartic-doubled functional — a REAL design problem,
    found while starting it. READ THIS BEFORE PLANNING.**

    The existing infrastructure asks for GLOBAL semiconvexity:
    `doubled_functional_semiconvex_shifted` proves
    `convex_on UNIV (%z. Psi z + (C/2)||z||^2)` and
    `semiconvex_jensen_alexandrov_point` consumes exactly that. In the doubled
    functional `a(x) + b(y) - P(x-y)` the penalty enters as `-P`, so what is
    needed is that `P` be semiCONCAVE — Hessian bounded ABOVE by a constant.

    A quadratic penalty has constant Hessian, so this is free. **A globally
    quartic penalty does not: its Hessian `beta((d.d) I + 2 d d^T)` grows like
    `beta||d||^2`, so no single constant works on all of UNIV.** So the
    substitution that carried the whole refactor does NOT go through here. This
    is the one place where the quartic is not just "the quadratic with
    `alpha *_R v` replaced by `Z *v v`".

    Two ways out, neither started:

    (a) **Localise the Jensen/Alexandrov layer** — weaken `convex_on UNIV` to
        `convex_on (cball xi r)` through `semiconvex_jensen_alexandrov_point`
        and its dependencies. Semiconvexity is only ever used on the ball where
        the argument runs, so this is mathematically right; but it touches the
        Alexandrov development, the deepest part of the project.

    (b) **Use a penalty that is quartic near 0 and quadratic far out.** Only the
        near-diagonal behaviour matters: the point of the quartic is the
        vanishing 2-jet at `d = 0`, and the doubling maximiser has
        `||xhat - yhat||` small. E.g. `P d = (beta/4) * g (d.d)` with `g s = s^2`
        for `s <= 1` and `g s = 2s - 1` beyond — globally semiconcave with an
        explicit constant, agreeing with the pure quartic near 0, hence the same
        `(0,0)` jet there. It is only `C^1` at the seam, but semiconcavity needs
        a bounded second DIFFERENCE, not a continuous second derivative, so that
        is probably fine — check what `semiconvex_alexandrov` actually assumes
        before committing.

    (b) looks much cheaper than (a) and leaves the Alexandrov layer untouched.

    **UPDATE — the abstraction this needs is now PROVED, so the open question is
    narrowed from "how" to "which concrete P".** `semiconvex_penalty_gen`
    (green) takes `P` semiconcave with constant `kappa`, i.e.
    `convex_on UNIV (%d. (kappa/2)||d||^2 - P d)`, and yields
    `convex_on UNIV (%z. -P (fst z - snd z) + ((2 kappa)/2)||z||^2)` — exactly
    the shape `doubled_functional_semiconvex` plugs in, with doubled constant
    `1/eps + 1/eps + 2 kappa`, matching the quadratic case at `kappa = alpha`.
    Helpers: `convex_on_prod_diff`, `convex_on_prod_add`.

    The identity that makes it go:

        -P(x-y) + kappa||z||^2 = [(kappa/2)||x-y||^2 - P(x-y)] + (kappa/2)||x+y||^2

    both summands convex — the first is the semiconcavity hypothesis composed
    with `z |-> fst z - snd z`, the second a norm-square composed with
    `z |-> fst z + snd z`. For a quadratic `P` the first bracket vanishes
    identically and this collapses to `semiconvex_penalty`, which is exactly how
    that lemma is proved; so this is the honest generalisation, not a new
    argument.

    **UPDATE 2 — the concrete penalty is PROVED, and it is neither the quartic
    nor the hybrid.** There is a closed form that makes semiconcavity free:

        soft_pen kappa d = (kappa/2)||d||^2 - kappa*(sqrt(||d||^2 + 1) - 1)

    The gap the hypothesis asks for, `(kappa/2)||d||^2 - P d`, is then EXACTLY
    `kappa*(sqrt(||d||^2+1) - 1)`; and `sqrt(||d||^2+1) = norm (d,1)` in
    `'a x real`, so it is the norm composed with the affine map `d |-> (d,1)` —
    convex for free, no Hessian computation, no piecewise analysis.

    Proved (all green):

        soft_pen                          the definition
        convex_on_norm_lift               convex_on UNIV (%d. norm (d,1))
        soft_pen_gap                      (kappa/2)||d||^2 - P d = kappa*norm(d,1) - kappa
        soft_pen_semiconcave              hence convex, i.e. P semiconcave
        soft_pen_quotient                 P h/||h||^2 = kappa/2 - kappa/(sqrt(||h||^2+1)+1)
        soft_pen_vanishing_jet_at_zero    hence -> 0: the (0,0) jet at the origin

    Near `0` it behaves as `(kappa/8)||d||^4` — it IS a quartic there, which is
    the only place the device needs one; far out it grows quadratically, which is
    exactly what the pure quartic could not do. `quartic_pen*` remains as the
    record of the near-diagonal behaviour but is not the penalty to use.

    **So item 3 is done** in the sense that matters for semiconvexity. One piece
    of `soft_pen` is still missing and is the immediate next step:

    **`Pjet` for `soft_pen` at a GENERAL `d`.** The chain needs the second-order
    jet at `d = fst zh - snd zh` (the Jensen point), not only at `0`. Derivatives,
    computed by hand — verify before trusting:

        s        = d . d
        grad P d = kappa * (1 - (s+1)^(-1/2)) *_R d
        Hess P d = kappa * (1 - (s+1)^(-1/2)) *_R I
                     + kappa * (s+1)^(-3/2) *_R (d d^T)

    Sanity checks that hold: at `d = 0`, `s = 0`, so `1 - 1 = 0` and `d d^T = 0`,
    giving gradient `0` and Hessian `0` — consistent with
    `soft_pen_vanishing_jet_at_zero`, which is proved independently. The Hessian
    is symmetric (both `I` and `d d^T` are), discharging the `transpose Z = Z`
    hypothesis the general psd chain carries.

    It also gives the `KZ` for `norm_block_matrices_bounded_gen` for free:
    `kappa(1 - (s+1)^(-1/2)) <= kappa` and
    `kappa (s+1)^(-3/2) ||d||^2 = kappa s (s+1)^(-3/2) <= kappa` (since
    `s <= (s+1)^(3/2)` for `s >= 0`), so the quadratic form is bounded by
    `2 kappa ||v||^2`, i.e. **`KZ = 2 kappa`**.

    Formalising the jet means differentiating `sqrt` twice. **I checked for a
    bridge from twice-differentiability to the `o(||h||^2)` jet form, and there
    is NONE.** The Alexandrov development builds its jets from the prox map
    (`f_taylor_limit`, `taylor_remainder_identity`), not from classical
    derivatives, and nothing converts `has_derivative` data into the limit form
    the chain consumes. So the next step is really two:

      (i) write the bridge — "twice differentiable at `x` with gradient `G` and
          Hessian `Z` implies `(f(x+h) - f x - G.h - (h.(Z *v h))/2)/||h||^2 -> 0`".
          Standard second-order Taylor; the proof goes along segments via the
          mean value theorem. It is reusable and worth having on its own.
      (ii) apply it to `soft_pen`, whose derivatives are the ones displayed
           above.

    **UPDATE — route (ii) is now half done: the square-root expansion is PROVED,
    and it is EXACT rather than asymptotic.** See `subsection "Second-order
    expansion of the square root"`:

        sqrt_diff_exact             S - R = D/(S+R)   (conjugate identity)
        second_order_algebra_aux    the bare-variable algebra
        sqrt_second_order_quotient  (S - R - D/(2R))/D^2 = -(1/(2R(S+R)^2))

    The point: the second-order remainder is a QUOTIENT, identically — no
    differentiation and no Taylor theorem. The `o(D^2)` statement is then just
    continuity of `D |-> 1/(2R(S+R)^2)` at `D = 0`, where it takes the value
    `1/(8R^3)` — the Taylor coefficient, recovered rather than assumed.

    So the general bridge (i) is NOT needed for `soft_pen`. **The composition is
    now PROVED as well** — `sqrt_second_order_exact` (the non-quotient form,
    valid for every `Delta` including `0`, so no side condition propagates) and
    `soft_pen_expand`, plus helpers `sqrt_rhs_aux`, `neg_div_cancel_aux`.
    `soft_pen_expand` gives the increment EXACTLY:

        soft_pen k (d+h) - soft_pen k d
          = (k/2)*Delta
            - k*( Delta/(2R) - Delta^2/(2R*(sqrt(u+Delta)+R)^2) )

    with `u = ||d||^2+1`, `R = sqrt u`, `Delta = 2(d.h) + h.h`.

    **The collection step is proved too** — `soft_pen_rem` (with bare-real helper
    `soft_pen_rem_aux`). Subtracting the gradient `kappa(1-1/R)(d.h)` and the
    Hessian form `[kappa(1-1/R)(h.h) + kappa(d.h)^2/R^3]/2` from the increment
    leaves EXACTLY

        Rem h = kappa*Delta^2/(2R*T^2) - kappa*(d.h)^2/(2R^3),
        T = sqrt(u + Delta) + R

    an identity, by pure cancellation: `(kappa/2)Delta - kappa*Delta/(2R)` IS the
    gradient term plus half the Hessian form.

    **UPDATE 3 — `soft_pen_jet_form` IS PROVED. The penalty layer is complete in
    quadratic-form.** The jet holds at every `d`, with gradient
    `kappa(1 - 1/R) *_R d` and Hessian quadratic form
    `kappa(1 - 1/R)(h.h) + kappa(d.h)^2/R^3`, `R = sqrt(||d||^2+1)`.

    **UPDATE 4 — the matrix form is PROVED too. THE PENALTY LAYER IS COMPLETE.**

        outer_prod / soft_hess     Z = kappa(1-1/R) I + (kappa/R^3) d d^T
        soft_hess_entry            entrywise
        soft_hess_sym              transpose Z = Z  <-- the extra hypothesis the
                                   general psd chain carries, discharged
        soft_hess_quadform         h.(Z *v h) = the jet's quadratic form

    Combined with `soft_pen_jet_form`, `soft_pen` now supplies every hypothesis
    the `_gen` chain asks of a penalty: the jet `(G, Z)` at every `d`, symmetry
    of `Z`, and semiconcavity (`soft_pen_semiconcave`). **Item 3 is DONE.** The
    only remaining work for Theorem 4.2(a) is item 4 — stages 9-10 and the
    assemblies (task 13).

    (Superseded note on what was then the last step:)
    convert the quadratic form to the matrix the chain consumes, i.e. exhibit
    `Z = kappa(1 - 1/R) *_R I + (kappa/R^3) *_R (d d^T)` with
    `h . (Z *v h) = kappa(1-1/R)(h.h) + kappa(d.h)^2/R^3` and
    `transpose Z = Z`. Needs an `outer_prod` definition (`(chi i j. d$i * e$j)`);
    both facts are entrywise computations. `transpose Z = Z` is exactly the extra
    hypothesis the general psd chain carries, and `KZ = 2 kappa` (derived above)
    feeds `norm_block_matrices_bounded_gen`.

    (Ingredients, all proved:)

        inner_sq_quotient_bounded         (d.h)^2/||h||^2 <= ||d||^2
        soft_pen_T_tendsto                T h -> 2R
        soft_pen_bracket_tendsto          2/(R T^2) - 1/(2R^3) -> 0
        soft_pen_second_summand_tendsto   k(4a+b)/(2R T^2) -> 0
        rem_split_aux                     the quotient split, on bare reals

    To finish `soft_pen_jet_form`: (1) an `eventually` (h /= 0) instance of
    `soft_pen_rem` divided through, rewritten by `rem_split_aux` with
    `b := h.h` and `(norm h)^2 = h.h` (`power2_norm_eq_inner`); (2)
    `Lim_null_comparison` for the product `((d.h)^2/||h||^2) * (k * bracket)`,
    bounded by `||d||^2 * |k * bracket|`; (3) `tendsto_add` with the second
    summand; (4) `Lim_transform_eventually`. No new analytic content — every
    limit needed is in the list above. Note `0 <= sqrt x` needs `0 <= x` supplied
    in this Isabelle, so carry the `0 <= ||d+h||^2 + 1` fact (proved inline in
    `soft_pen_expand` as `uD`) when constructing `T h > 0`.

    (Original statement of what was left:)
    **The ONLY thing left in the whole penalty layer is `Rem h/||h||^2 -> 0`.**
    With `a = d.h`, `b = h.h = ||h||^2` and `Delta^2 = 4a^2 + 4ab + b^2`:

        Rem h/||h||^2 = (a^2/b) * kappa*(2/(R T^2) - 1/(2R^3))
                        + kappa*(4a + b)/(2R T^2)

    First summand: `a^2/b <= ||d||^2` by Cauchy-Schwarz — BOUNDED — times a
    bracket tending to `0` (because `T -> 2R`, giving `2/(R*4R^2) = 1/(2R^3)`);
    close it with `Lim_null_comparison`. Second summand: numerator `-> 0`,
    denominator `-> 8R^3 /= 0`; pure continuity. That is the entire remaining
    proof, and it is the only place in the layer needing more than algebra.

    After it, one mechanical step converts the quadratic-form statement into the
    matrix form the chain consumes (`G . h` and `h . (Z *v h)`), for which the
    matrix is `Z = kappa(1-1/R) I + (kappa/R^3) d d^T` — needs an `outer_prod`
    definition, symmetric by inspection.

    Write `u = (d.d) + 1`, `R = sqrt u`, `S = sqrt (u + Delta)` with
    `Delta = 2(d.h) + (h.h)`; note `(d+h).(d+h) + 1 = u + Delta`. Then

      P(d+h) - P(d)
        = [ kappa (d.h) + (kappa/2)(h.h) ]            (the exact quadratic part)
          - kappa [ S - R ]
        = kappa (d.h) + (kappa/2)(h.h)
          - kappa [ Delta/(2R) - Delta^2/(2R(S+R)^2) ]   (by sqrt_second_order_quotient)
        = kappa (1 - 1/R) (d.h)                       <-- gradient term
          + (kappa/2)(1 - 1/R)(h.h)                    \
          + kappa (d.h)^2 / (2 R^3)                    /  <-- Hessian term
          + Rem h

    so `grad P d = kappa (1 - 1/R) *_R d` and the Hessian quadratic form is
    `kappa (1 - 1/R)(h.h) + kappa (d.h)^2 / R^3` — matching the hand computation
    recorded above, and vanishing at `d = 0` (there `R = 1`, so `1 - 1/R = 0` and
    `(d.h) = 0`), consistent with `soft_pen_vanishing_jet_at_zero`.

    The remainder is
    `Rem h = kappa Delta^2/(2R(S+R)^2) - kappa (d.h)^2/(2 R^3)`, and

      Rem h / ||h||^2
        = 4 kappa (d.h)^2/||h||^2 * [ 1/(2R(S+R)^2) - 1/(8R^3) ]
          + kappa [ 4(d.h) + ||h||^2 ] / (2R(S+R)^2)

    using `Delta^2 = 4(d.h)^2 + 4(d.h)(h.h) + (h.h)^2` and `(h.h) = ||h||^2`.
    Both terms vanish as `h -> 0`: the first because `(d.h)^2/||h||^2 <= ||d||^2`
    is BOUNDED (Cauchy-Schwarz) while the bracket tends to `0` (since `S -> R`);
    the second because the numerator tends to `0` and the denominator to
    `8R^3 /= 0`. Note the first term is the only place a bounded-times-vanishing
    argument is needed — everything else is continuity.

    An alternative that avoids (i): expand by hand. `P(d+h) - P(d)` splits into
    the exact quadratic part `kappa (d.h) + (kappa/2)(h.h)` plus
    `-kappa[sqrt(s'+1) - sqrt(s+1)]` with `s' - s = 2(d.h) + h.h`, so all that is
    really needed is the ONE-VARIABLE expansion
    `sqrt(u+D) - sqrt(u) = D/(2 sqrt u) - D^2/(8 u^(3/2)) + o(D^2)` and then
    substitution. That may well be shorter than the general bridge, but the
    bridge is the better investment if anything else will ever need a jet.

    Then the remaining work is item 4.

 4. Stages 9-10 and the assemblies, under `alpha *_R v |-> Z *v v` and
    `alpha *_R (xhat-yhat) |-> G`.

Note the general chain carries one hypothesis the quadratic one did not:
`transpose Z = Z`. True for the quartic, whose Hessian is
`beta((d.d) I + 2 d d^T)`; it will have to be discharged at the point of use.

After that: `norm_block_matrices_bounded` (needs only `norm Z` bounded, easy on a
bounded region), the semiconvexity of the quartic-doubled functional, then
stages 9-10 and the assemblies.

Practical note for whoever continues: MCP `edit` with `mode: "prepend"` bit again
here (`theorem foo:theorem foo:` on the seam). Read the seam after every prepend.

Cost refinement, checked: the DEEP lemma is already penalty-agnostic.
`sums_psd_from_jet` bakes in `(alpha/2)||x-y||^2`, but its proof just delegates
to `sums_psd_at_interior_max`, which takes the two block maps abstractly as
`lX`, `lY` hypotheses and never mentions the penalty — the penalty enters only
through `mx` (there is a max) and `expPsi` (there is a jet), both of which hold
for any penalty. Likewise the `psd (Y - X)` conclusion follows for ANY penalty
of the form `P(x - y)`, because such a penalty is CONSTANT along the diagonal
direction `(v,v)`, which is the direction the psd test uses. So the refactor is
a substitution at the STATEMENT layer, not a reproof of the hard content.

**Superseded diagnosis (kept because the negative results are still useful).**
Before checking the paper I had concluded the blocker was unresolvable by
reparametrising the doubling. That conclusion was right about what it tested and
wrong about the scope — it never considered changing the penalty's order. The
facts established remain valid and are worth not re-deriving:

1. The gradient the viscosity conditions actually see is `grad a (xhat)`, where
   `a = supconv(theta u) eps` and `xhat` is the doubling maximiser. It vanishes
   exactly when `xhat` is a critical point of `a`.
2. **No reparametrisation of the doubling removes that.** I tried the
   antisymmetric linear tilt `- eta e.(x-y)`: it keeps the two slice gradients
   exact negatives and gives `q = alpha(xhat-yhat) + eta e`, but the tilted
   first-order condition is `grad a (xhat) - eta e = alpha(xhat-yhat)`, i.e.
   `q = grad a (xhat)` again — the tilt relocates `xhat`, it cannot make `a`
   non-critical there. Correspondingly the penalty bound picks up an
   `eta*||xhat-yhat||` term and degrades by exactly what the tilt gained. The
   failed attempt is written up in full at
   `subsection "The antisymmetric linear tilt of the doubling"`, with the two
   (true, reusable) lemmas `antisym_tilt_grad_lower_bound` and
   `jet_transfer_linear` that came out of it. **Do not retry this.**
3. At `p = 0`, `ell_op` is genuinely discontinuous — `feasible k L p` carries the
   constraint `a p = 0`, which drops a dimension as `p -> 0`, so the infimum
   jumps. `eq36_rhs` is the value in the TOP-EIGENVECTOR direction and exceeds
   `ell_op k L 0 M` by roughly `(L/2)max(eigval 1 M, 0)`. So the no-gap
   condition is false for any `M` with a positive top eigenvalue.

Why `strict_contradiction_of_shifts_any_p` does not already settle it: it needs
both operator bounds at the SAME `p`. Jensen's tilt makes the two slice
gradients `-fst pt + G` and `-(snd pt + G)`, exact negatives only if
`fst pt + snd pt = 0`, which Jensen does not deliver. Exactness is recovered
only in the limit, and the limit is what cannot cross the `p = 0`
discontinuity.

Both of those remain true; the quartic penalty sidesteps them by making the
`p = 0` configuration impossible rather than by trying to survive it.

One loose end worth noting: this project's `visc_subsol`/`visc_supersol` use
plain `ell_op`, whereas the paper uses `F_*` / `F^*`. Since `F_* <= F <= F^*`,
both of this project's notions are STRONGER than the paper's, so every theorem
proved from them is valid but applies to fewer functions. Whether to relax the
definitions to match the paper is a separate decision; it does not affect
correctness of anything currently proved.

**(B) The concrete instantiation.** For compact nonempty `K`:

1. Negate `max_principle_boundary`, take the maximiser of `u - w` with
   `max_principle_boundary_attains`, get `m < M` on `K - interior K`.
2. Extend `u`, `w` globally (obstruction 3), pick `theta` by
   `theta_gap_preserved`.
3. Fix `sigma`, then `kappa` and `tau'` by `uniform_modulus_on_compact` on
   `theta u - w`; fix `beta` and `tau` likewise for `-w`; check
   `m + 2 sigma + tau + tau' < M`.
4. Choose `alpha` large (so `norm_lt_of_penalty_bound` gives `|xhat-yhat| < beta`)
   and `eps` small (so `supconv_sandwich` gives the two `sigma`s, and
   `supconv_radius_uniform` gives `R_u`, `R_w < kappa/2`).
5. `doubling_maximiser_supconv` for `xi0`;
   `doubling_maximiser_far_from_boundary` for the `farx`/`fary` of
   `comparison_from_localised_maximiser`; then `rho < r <= kappa`, any `D0 > 0`.
   (After (A) there is no `glb` to discharge. Until then it would need
   `doubling_grad_lower_bound_supconv_sep` + `positive_separation_of_value_gap`
   AND `xhat != yhat`, which for large `alpha` is exactly what fails — hence
   (A) is not optional.)
6. Feed `comparison_from_localised_maximiser` (NOT
   `comparison_supconv_maximiser_complete` directly — the bridge already does
   `mxK`, `radu`/`radw`, `subu`/`subw`).

The cost is the **interdependence of the parameter choices in steps 3-4**, which
is genuinely fiddly (each of `sigma, tau, tau', kappa, beta, alpha, eps` is
constrained from two sides) but involves no new mathematics.

Note `doubling_maximiser_far_from_boundary` is stated for abstract `f`, `g` and
abstract moduli; at the point of use `f = theta u`, `g = -w`, and its `tr`
hypothesis is `doubling_maximiser_value_transfer` with the (nonnegative)
penalty dropped, its `near` is `norm_lt_of_penalty_bound` applied to the same
transfer, and its `modg`/`modF` are two instances of
`uniform_modulus_on_compact`.

---

# HANDOVER (2026-07-31, later session)

## Nothing is unverified. Nothing is blocked.

The previous handover left one unverified edit in the tree and an undiagnosed
build failure. Both are resolved:

* **The unverified edit failed, and has been replaced by a stronger result.**
  `mkt_exit_vals_mono` did not compile (three errors: the locale's sample type
  is polymorphic, so an unannotated `obtain` and an unannotated `step`
  hypothesis could not unify with `mkt_exit_vals`, which pins the type to
  `('n => real => real) measure`). Rather than patch the annotations, the
  unsuppliable `step` hypothesis was ELIMINATED — see below.
* **The exit-137 builds did not recur.** A fresh Isabelle session loaded
  `Value_Function` (365 commands), `Comparison_Assembly` (6376 commands) and
  batch-built the whole session without incident. Treat the previous session's
  SIGKILLs as an exhausted long-running process, not a property of the theories.
  No further diagnosis is warranted unless it recurs.

## What was added this session (all green, all checked in PIDE)

### `Value_Function.thy` — domain monotonicity, now unconditional

    sufficiently_volatile_market_mono_K   K <= K' ==> the locale transfers
    mkt_exit_vals_mono                    K <= K' ==> set inclusion
    val_fn_mono                           K <= K' ==> val_fn k L K x0 <= val_fn k L K' x0

The locale half — recorded by the previous handover as "NOT written ... the
fiddly part" — turned out to be four lines. With the smaller-domain locale
INTERPRETED, `unfold_locales` discharges the entire `martingale` ancestor
automatically and leaves exactly the fourteen `assumes`; thirteen are reused
verbatim and `X_in_K` is weakened by one `eventually_elim`. Discharging all
fourteen at once with `(unfold_locales; blast intro: sv.k_lb ... K')` works and
is worth reusing: `blast` handles the `!!t. 0 <= t ==> ...` assumptions (it
solves the side condition from the assumption list) which a bare `rule` does not.

NOTE the shape change: `val_fn_mono_of_market_mono` is GONE. It took the locale
implication as a hypothesis — precisely the "green statement with hypotheses
nothing can supply" failure mode the previous handover warns about. The
replacement takes `K <= K'`.

### `Comparison_Assembly.thy` — stage 9 of the Theorem 4.2(a) chain

New closing section, `From a BOUNDED family to the contradiction` (~390
commands). It exists because stage 8's endpoint
`comparison_supconv_sequence_complete` demands FOUR CONVERGENT sequences and the
doubling only ever produces BOUNDS. Four results:

    norm_le_card_Basis_bound        norm <= DIM * (coordinate bound), from norm_le_l1
    norm_matrix_le_of_form_bound    |k . W k| <= c|k|^2  ==>  norm (matrix W) <= DIM*c
    hessian_abs_bound_of_two_sided  lower bound + (<=0)  ==>  |k . W k| <= C|k|^2
    block_form_bound_fst / _snd     product-space bound  ==>  per-block bound
    norm_block_matrices_bounded     ==> norm X, norm Y <= DIM * (C + |alpha|)
    tilted_doubled_jet_slices       one Jensen output -> the two component jets
    tilted_doubled_hessian_nonpositive   v . W v <= 0 at the tilted maximum
    bounded_seq_limit_point_triple  ONE subsequence for three bounded sequences
    comparison_supconv_bounded_family   stage 8, with bounds instead of limits

Three things are worth carrying forward from this.

1. `norm_matrix_le_of_form_bound` is the step stage 6 stopped one short of.
   Stage 6 ended at `symmetric_form_bound_unit` (`|u . W v| <= c` for UNIT
   vectors) — an entrywise bound — and Bolzano-Weierstrass wants a norm bound.
   `norm_le_l1` closes it with constant `card Basis`; no spectral theory. The
   basis of `real^'n^'n` is enumerated by `matrix_Basis_cases` (peel
   `Basis_vec_def` twice; `Basis :: real set = {1}`).
2. `tilted_doubled_jet_slices`: **the tilt does not have to be absorbed into the
   two summands.** That was the expected route (via `tilt_absorb` /
   `doubled_tilted_interior_max`) and it is unnecessary: at an interior maximum
   of the TILTED functional, `gradient_is_minus_tilt` gives `q = -p` for the
   UNTILTED jet, so `doubled_jet_slice_fst`/`_snd` apply to Jensen's expansion
   exactly as it stands and the tilt enters only through that one equation.
   The two block gradients come out as `-fst p + G` and `-(snd p + G)` with
   `G = alpha(xhat - yhat)` — which is `Pu` and `-Pw` in the form the family
   theorem consumes, and matches `gradient_sequences_align` on the nose.
3. Simultaneous subsequence extraction is FREE: a tuple of euclidean spaces is
   euclidean, so ONE `bounded_seq_limit_point` on the bundled sequence does it.
   No diagonal argument. (`norm_Pair_le` supplies the bundled bound.)
   `p /= 0` is NOT closed and does not survive on its own; what survives is a
   uniform lower bound `c <= norm (G i)`, which is the shape
   `doubling_grad_norm_lower_bound` already delivers with `c = alpha*gamma/Lw`,
   independent of the index.

## Where Theorem 4.2(a) now stands

The chain map at the END of `Comparison_Assembly.thy` is updated and is the
authoritative account — read it, not this file, for the mathematics. Summary:
stages 1-9 are proved. What remains is ONE instantiation, and TWO of its inputs
are real work, not transcription:

* ~~**(a) The two-sided Hessian bound.**~~ **DONE — see below.**
* ~~**(b) The gradient lower bound.**~~ **DONE — see below.**

**Both are now closed, AND the assembly on top of them is written.**

### Stage 10: `comparison_supconv_doubling_complete` — the engine of Thm 4.2(a)

    theorem comparison_supconv_doubling_complete:
      (* two viscosity properties; theta, eps, alpha; Jensen data xi, r, rho, m;
         bounds and continuity; subu/subw; glb; rsmall *)
      shows False

It assumes **nothing** about jets, Hessians or gradients — all of them are
produced. Internally: run Jensen at the shrinking tilts `D/(2+i)` with
`D = (Phi(xi) - m)/(2r)` (so the smallness condition holds at every index),
skolemise with `choice4`, and feed `comparison_supconv_bounded_family`.

Supporting pieces added for it:

    tilted_doubled_psd_ordering        the ordering psd(Y-X) at the tilted max
    supconv_attained_ball / _in / _family_in   attaining points lie in an
                                       EXPLICIT O(sqrt eps) ball
    penalty_gradient_nearby_upper      the matching upper bound on |G_i|

Two things I got wrong earlier and corrected here. First, I wrote that the tilt
never has to be absorbed into the two summands — true for the GRADIENTS
(`gradient_is_minus_tilt` avoids it) but **false for the psd ordering**, where
`sums_psd_from_jet` wants a plain untilted maximum and
`doubled_tilted_interior_max` must supply it. Second, `y_s in Omega` was going
to be an unsuppliable hypothesis; strengthening `supconv_attained` to carry its
own (already-constructed) radius turns it into a smallness condition on `eps`.

### STOP: `max_principle_boundary` IS FALSE. Do not try to prove it.

Before assembling stage 10 into Theorem 4.2(a) I checked the target, and the
interface the whole Section 4 chain is conditional on does not hold as written:

    max_principle_boundary_counterexample   (Comparison_Assembly.thy)
      visc_subsol k L (interior K) u
      ==> visc_supersol k L (interior K) w
      ==> interior K ~= {}
      ==> ~ max_principle_boundary k L K

The cause is `visc_supersol_cong_on` (also proved): `visc_subsol k L (interior K)`
constrains only points of `interior K`, and its local condition can always be
shrunk into that OPEN set — so **the boundary values of a sub- or supersolution
are completely free**. `max_principle_boundary` asserts `u - w` attains its max
over `K` on `K - interior K`; raise `w` on the boundary and no boundary point
can be a maximiser. Nothing about the operator, dimension or geometry is used.

So the old interface is refutable whenever one sub/supersolution pair exists,
and vacuous otherwise. Either way it cannot be discharged. This was NOT a known
gap — it was recorded as "the one genuine gap, isolated to a single named
interface", i.e. as something waiting to be proved.

**THE INTERFACE HAS BEEN FIXED IN PLACE** in `Lemma_3_1_Envelopes.thy`, where
it is declared. The name `max_principle_boundary` is unchanged and now carries
`continuous_on K u` and `continuous_on K w`:

    max_principle_boundary_raw       the old, refutable form — KEPT, solely as the
                                     target of the counterexample so the fix
                                     cannot be quietly undone
    max_principle_boundary           corrected: + continuous_on K u/w
    max_principle_boundary_attains   under those, u - w DOES attain its max on
                                     compact K (what the raw form presupposed)
    max_principle_boundary_intro     threads the two continuity hypotheses
    max_principle_le                 |
    comparison_from_max_principle    |  all three restated with cu, cw;
    uniqueness_from_max_principle    |  proofs otherwise unchanged

Nothing else in the development referenced these, so the refactor was contained:
`Relative_Arbitrage_Comparison.thy:447` mentions the interface only in prose.
`Comparison_Assembly.thy` keeps the counterexample (retargeted to
`max_principle_boundary_raw`) and points at the upstream repair.

Continuity rather than usc/lsc because that is what the rest of the development
already carries (`theorem_1_1_ball_fragment` states its uniqueness clause for
`continuous_on (cball 0 r) u`) and this HOL-Analysis has no semicontinuity
library; usc/lsc is the sharp hypothesis and only
`max_principle_boundary_attains` would need reproving to get it.

### Stage 14: everything the shifted family assembly needs

    tilted_shifted_jet_slices    the two component jets for the SHIFTED
                                 functional, already transferred back to jets of
                                 the plain sup-convolutions
    transpose_shifted_block      symmetry survives the 2*delta*I shift
    psd_shifted_diff             the ORDERING is untouched (same shift on both
                                 Hessians cancels in the difference)
    norm_shifted_block           norm bound degrades by exactly |2delta|*|I|
    shifted_family_parameters    delta_i = D0/(2+i), dd_i = delta_i*rho^2/(4r);
                                 satisfies shifted_jensen_smallness with a
                                 factor of two to spare, both -> 0

So no part of stage 9's matrix work has to be redone for the shifted family: it
just carries a `delta`-dependent constant that vanishes with `delta_i`.

### What remains for Theorem 4.2(a) PROPER — do not mistake stage 10 for it

**SUPERSEDED by the 2026-08-01 handover at the top of this file.** The estimate
below ("another assembly of the same size as stage 10") was wrong in two ways:
assembly 1 is now DONE (`comparison_supconv_maximiser_complete`), and the top
level turned out to need four *new* results, not transcription — the `+1`
attainment radius, the Lipschitz hypothesis, the global extension, and the
boundary-distance geometry. All four are now in place. Read the top block.

Stage 10 is the engine, not the theorem: it still takes Jensen's geometric data
as hypotheses. To reach `max_principle_boundary_cont` for a given `K` one must
still PRODUCE that data — the doubling maximiser `xi` for the sup-convolutions
(`doubling_maximiser_exists`), `bnd` and `gapm`, and `glb` by chaining
`doubled_value_gap_supconv` and `supconv_lipschitz` into
`doubling_grad_norm_lower_bound` — then choose `eps` and `rho` for `subu`/`subw`
and `rsmall`.

### The strict-gap step — DONE (this was the one non-bookkeeping piece)

`gapm` wants a STRICT gap between `Phi(xi)` and the annulus maximum, which a
plain maximiser of `Phi` does not give (Phi may be flat near it). The repair —
perturb by `-delta*|z - xi0|^2` — is now proved through:

    norm_sq_diff_shift                     (Sup_Convolution) |z|^2 - |z-c|^2 affine
    doubled_functional_semiconvex_shifted  (Sup_Convolution) the perturbed doubled
                                           functional is semiconvex, constant + 2delta
    norm_sq_prod_split                     the perturbation SPLITS across blocks
    doubled_supconv_jet_exists_shifted     Jensen for the perturbed functional
    shifted_annulus_bound                  Phi y - delta|y-xi0|^2 <= Phi xi0 - delta*rho^2
    shifted_centre_gap                     ... < the value at the centre
    shifted_jensen_smallness               and 2*dd*r < delta*rho^2 suffices

Two things made this tractable. The perturbation **splits across the two
blocks** (`|z-xi0|^2 = |fst z - fst xi0|^2 + |snd z - snd xi0|^2`), so the
perturbed functional keeps the doubled form `a (fst z) + b (snd z) - penalty`
that every lemma in stages 3-10 is stated for — nothing there had to be redone.
And the whole cost of the perturbation is **affine** (`|z|^2 - |z-xi0|^2 =
2 z.xi0 - |xi0|^2`), so semiconvexity survives by `convex_on_add`.

Note `shifted_jensen_smallness` reduces Jensen's smallness condition to
`2*dd*r < delta*rho^2` — a condition on the free parameters ALONE, with no
reference to `Phi`. So `dd` can always be chosen after `delta` and `rho`.

`jet_transfer_quadratic` moves jets from `a - delta|.-x0|^2` back to `a`:
gradient `+2delta(xhat-x0)`, Hessian `+2delta I`, **remainder unchanged** — the
quadratic's expansion is exact, so this is a rewrite, not an estimate.

### Stage 13: the rest of Jensen's data, and the alignment made abstract

    doubling_maximiser_supconv          the maximiser xi0 for the SUP-CONVOLUTIONS
    doubling_grad_lower_bound_supconv   the glb chain, complete

`doubling_maximiser_supconv` needs no regularity of `u`/`w` beyond boundedness:
`supconv_continuous` manufactures the continuity `doubling_maximiser_exists`
asks for. That is where the sup-convolution earns its keep.

**The structural obstacle I flagged is gone.** It looked as though stage 10
would need a two-parameter rework, because the perturbation shifts the jet
gradients by `2*delta*(zhat-x0)` and that does not vanish for fixed `delta`.
Instead `comparison_supconv_bounded_family` was **generalised**: its alignment
hypothesis is now the abstract

    au: (%i. Pu i - G i) ---> 0        aw: (%i. Pw i - G i) ---> 0

rather than the concrete `Pu i = -fst (Pt i) + G i` with a shrinking tilt. That
is what the proof actually used, it is strictly weaker, and it accommodates any
family whose gradients approach the penalty gradients — including the perturbed
one with `delta i -> 0`. Stage 10 needed no change beyond supplying the two
limits (`pt0` + `tendsto_fst`/`tendsto_snd`).

### Stage 14: the SECOND O(delta) error — the one I missed

The gradient shift was not the only cost of the perturbation. Writing assembly
1's second half surfaced another, of exactly the same shape:

> the perturbation raises **both** block Hessians by `2*delta`. `X` becomes
> `X + 2delta I` and `Y` becomes `Y - 2delta I` (because `Y` enters the jets
> negated), so `(Y - 2delta I) - (X + 2delta I) = (Y - X) - 4delta I`, which is
> **not psd even when `Y - X` is**. The per-index ordering is genuinely lost.

Cured the same way — `delta_i -> 0` — but unlike the gradients this needed the
interface weakened, because `psd` is only recovered in the limit:

    psd_diff_limit_shifted    psd (Y i - X i + cs i *R mat 1), cs ---> 0
                              ==> psd (Y0 - X0)

and the ordering hypothesis generalised through the chain:

    env_strict_contradiction_of_shifted_limits   psdi  -->  p0 : psd (Y0 - X0)
    comparison_supconv_sequence_complete         psdi  -->  p0
    comparison_supconv_bounded_family            psdi  -->  asymptotic + cs ---> 0

A strict generalisation: stage 10 still goes through, supplying `cs = (%_. 0)`.
It cost four edits and no duplicated proofs, because `psdi` was only ever used
to reach the limit ordering — `env_strict_contradiction_of_shifted_limits`
called `psd_diff_limit` on it and nothing else.

**Lesson for whoever finishes this**: the perturbation costs an `O(delta)` error
in every quantity the family theorem constrains. Gradients and the ordering are
now handled. Check the Hessian NORM bound (`bX`/`bY`) the same way before
assuming it survives — `norm_shifted_block` exists for exactly that.

Everything else in `comparison_supconv_bounded_family`'s hypothesis list is
supplied by a named result: `family_of_tilt_construction_shrinking` for the
family, `doubled_supconv_jet_exists` for each member, `supconv_attained_family`
for `optu`/`optw`, `tilted_doubled_jet_slices` for `jetu`/`jetw`,
`block_matrices_from_jet` for `symX`/`symY`/`psdi`, `tilt_sequence_admissible`
for the shrinking tilts, `norm_block_matrices_bounded` for `bX`/`bY`.

### Item (a) closed: the Hessian bound, end to end

Two statements were widened to carry a clause their own proofs already had —
the `semiconvex_alexandrov` failure mode again, one level up:

    semiconvex_jensen_alexandrov_point   (Sup_Convolution.thy)
    doubled_supconv_jet_exists           (Comparison_Assembly.thy)

Both now conclude `ALL k. -(C*|k|^2) <= k . W k` alongside the jet, with
`C = 1/eps + 1/eps + 2*alpha`. The widening is free: the `N` set in Jensen's
proof just quotes `semiconvex_alexandrov_bounded` instead of
`semiconvex_alexandrov`, and everything else in the proof is unchanged. There
were NO proof-level consumers of either statement, so nothing downstream broke.

The new chain from there to `bX`/`bY`:

    hessian_abs_bound_of_two_sided  lower + (<=0)  ==>  |k . W k| <= C|k|^2
    block_form_bound_fst / _snd     the PRODUCT-space bound restricts to the
                                    two blocks, constant C + |alpha|
    norm_block_matrices_bounded     ==> norm X, norm Y <= DIM * (C + |alpha|)

Two points worth keeping. The two-sided bound needs **no sign hypothesis on
`C`**: `-C|k|^2 <= k.W k <= 0` already forces `0 <= C|k|^2`. And the block
restriction is just testing `W` against `(k,0)` and `(0,k)` — the product inner
product kills the other component and `norm (k,0) = norm k` — with the penalty
`alpha *R k` contributing exactly `alpha*|k|^2`.

### Item (b) closed: the gradient lower bound, in three pieces

    supconv_lipschitz               (Sup_Convolution.thy) supconv inherits the
                                    Lipschitz constant EXACTLY, no eps-dependence
    supconv_le_of_lipschitz         (Sup_Convolution.thy) supconv u eps
                                    <= u + eps*L^2/2, an EXPLICIT rate
    doubled_value_gap_supconv       the value gap transfers, cost eps(Lu^2+Lw^2)/2
    penalty_gradient_nearby_bound   a lower bound at the ball CENTRE transfers to
                                    any point within rho, at cost 2|alpha|rho

Two geometric one-liners carry the whole section. For `supconv_lipschitz`:
translating the competitor `z` by `y - x` leaves the penalty unchanged
(`dist y (z + (y - x)) = dist x z`), so the comparison collapses to the
Lipschitz estimate on `u`. For `supconv_le_of_lipschitz`: completing the square,
`Lr - r^2/(2 eps) = eps L^2/2 - (r - eps L)^2/(2 eps) <= eps L^2/2` — the
Lipschitz gain is linear in the distance and the penalty is quadratic, so a
competitor can only win by the amount at the turning point `r = eps L`. Note
this direction needs NO bound on `u` (`cSUP_least` wants only nonemptiness).

**The last one is why item (b) turned out easy, and the estimate I gave for it
was wrong.** I had costed it as "genuine mathematics ... uniformity at the two
competing points", planning to route through `supconv_tendsto`. That is the
wrong route: with the explicit rate above, sandwiching
`u <= supconv u eps <= u + eps L^2/2` bounds the two terms at `xh` from above
and the two at `z` from below, and the gap loss is just the sum of the two
rates. No limit, no uniformity argument.

## Where Theorem 1.1 stands — UNCHANGED, and this is the honest headline

`Theorem_1_1.thy` still names three missing pieces, and this session advanced
only the third:

  1. usc of `v` + the viscosity property (Prop 2.4 via Lemmas 2.2/2.3) — UNTOUCHED
  2. lower bound `ball_v <= v` at interior points (Section 3.1 martingale
     construction, needs weak existence for Eq. (3.11))                — UNTOUCHED
  3. general compact `K` — Theorem 4.2(a)                              — advanced

Items (1) and (2) are the probabilistic line (Phases A4-G). NOT ONE LINE OF THEM
IS WRITTEN, and they are together comparable in size to all of Phase E. Note the
asymmetry: item (3) buys GENERALITY (arbitrary compact `K`); items (1) and (2)
are what stand between the project and Theorem 1.1 FOR THE BALL, which needs no
Crandall-Ishii at all. A session aiming at Theorem 1.1 rather than at Theorem
4.2(a) should start at Phase A, not here.

`val_fn_mono` is the first brick of that line and is now in place.

## Verification state

  * `isabelle build -d . Arbitrage` — run at the end of this session, see the
    build log; PIDE `commands_failed = 0` for every theory touched.
  * `Value_Function.thy` 311 lines — 365 commands, 0 failed, 0 warnings.
  * `Comparison_Assembly.thy` 5459 lines — 0 failed. All warnings are
    `Ignoring duplicate rewrite rule` and are benign.
  * `Sup_Convolution.thy` 7563 lines — 0 failed.
  * placeholder audit `grep -cw 'sorry\|oops' *.thy` — CLEAN.
  * `git status`: modified ROOT, Sup_Convolution.thy, Theorem_1_1.thy,
    Value_Function.thy; untracked Comparison_Assembly.thy, STATUS.md,
    STATUS_ARCHIVE_2026-07-29.md. NOTHING IS COMMITTED.

## Workflow rules (carried forward, plus this session's)

  * `Comparison_Assembly.thy` is NOT batch-only; PIDE holds it fine (~4 s to
    reprocess in full). The same claim in `Theorem_1_1.thy`'s header is still
    UNTESTED.
  * DO NOT run `isabelle build` per edit. Loop: `edit` -> `get_state` with
    `commands_limit: 0`. That returns the error text and the failing goal;
    the build is not needed for diagnosis. Reserve builds for final confirmation.
  * PIDE does NOT see edits written to disk by shell/python. Call `read` once to
    resync, or edit through the MCP `edit` tool.
  * The MCP `edit` tool matches `old_text` against the UNICODE form of Isabelle
    symbols. In particular `\<open>` is the character U+2039 and `\<close>` is
    U+203A — an `old_text` containing the backslash-escaped forms will NOT
    match. Replacement `text` may use escapes, and for the tendsto arrow it MUST.
    Cheapest habit: anchor `old_text` on a pure-ASCII fragment.
  * NEW: `card (Basis :: 'a set) * c` type-checks with `c :: nat` and silently
    coerces the whole product — write `real (card (Basis :: 'a set)) * c`.
  * NEW: `OF` on a lemma whose hypothesis is `!!i. P (?A i)` can leave a
    flex-flex pair (`?A := %i. G (?j i)`) instead of the intended `%i. G i`, and
    the following `blast` then fails with a confusing goal. Pin it with
    `[where A = G, OF ...]`.
  * NEW: `norm (axis m (1::real)) = 1` is `norm_axis_1`, not `norm_axis`.

## Recurring failure mode worth carrying forward

Green statements with hypotheses nothing can supply. It bit again this session:
the tree's `val_fn_mono_of_market_mono` was exactly this. When adding a lemma
with a hypothesis, name the lemma that will discharge it, and if there isn't
one, write that down. `comparison_supconv_bounded_family` was designed to this
rule: every one of its hypotheses is annotated above with its intended source,
and the two that have NO source yet are called out as items (a) and (b).

Related: a corollary can silently DROP a clause its own proof establishes —
`semiconvex_alexandrov` discarded the psd Hessian bound that `convex_alexandrov`
proves. That one is now fixed (`semiconvex_alexandrov_bounded`), and the stale
"ACTION FOR A FUTURE SESSION" note in `Comparison_Assembly.thy` that asked for
it has been updated. Before proving a new estimate, check whether an upstream
statement already has it.
---

# Formalization status — arXiv:2512.17702

Lai, Shkolnikov, Soner, *Relative arbitrage problem under eigenvalue lower
bounds*.

Goal: formalize **every** result of the paper in Isabelle/HOL, assumption-free
(no placeholder proofs, known theorems proved rather than assumed). Props 5.4
and 5.5 are excluded by the user's instruction (they are not self-contained:
the paper says to repeat [LR24] word by word). Prop 2.4 is NOT excluded despite
the same phrasing — Theorem 1.1 depends on it twice (its usc clause and the
DPP), so it must be reconstructed from [LR24]; see Phase C below.

This file was rewritten 2026-07-29 for organization. The full chronological
log it replaced is `STATUS_ARCHIVE_2026-07-29.md` — consult it for the
fine-grained history of any completed item.

## Headline state (updated 2026-07-30, later)

**ALEXANDROV'S THEOREM IS PROVED**, in full generality, for finite convex
functions on any Euclidean space, together with the semiconvex corollary that
Crandall-Ishii actually consumes. Neither Rademacher's nor Alexandrov's theorem
exists anywhere in Isabelle/HOL or the AFP (both greps empty), so both were
built from scratch. `Sup_Convolution.thy` is now ~5290 lines / ~10660 commands,
batch-green.

The two headline statements:

```isabelle
theorem convex_alexandrov:
  assumes "convex_on UNIV f"
  shows "negligible {y. ~ (EX p B. bounded_linear B & (ALL k. 0 <= k . B k)
      & (ALL u v. u . B v = v . B u)
      & ((%k. (f (y+k) - f y - p . k - (k . B k)/2) / (norm k)^2) ---> 0) (at 0))}"

corollary semiconvex_alexandrov:
  assumes "convex_on UNIV (%x. u x + (c/2) * (norm x)^2)"
  shows "negligible {y. ~ (EX p B. bounded_linear B & (ALL v w. v . B w = w . B v)
      & ((%k. (u (y+k) - u y - p . k - (k . B k)/2) / (norm k)^2) ---> 0) (at 0))}"
```

### What Phase E now contains

1. **Sup-convolution calculus** - `supconv_semiconvex`, `supconv_continuous`,
   `supconv_near_optimizer`, `supconv_tendsto`.
2. **Convex analysis / Minty** - `subdiff_nonempty`, `subdiff_monotone`,
   `convex_subdiff`, `prox_attained`/`prox_unique`/`prox_min`,
   `minimizer_subdiff`, `prox_subdiff`, `subdiff_prox` (the CONVERSE: `prox f
   (y+p) = y` whenever `p` is a subgradient at `y`), `prox_nonexpansive`,
   `minty_surjective`, `prox_lipschitz_on`, `continuous_on_prox`.
3. **`rademacher_AE`** - Rademacher's theorem in R^n, plus `rademacher_vec_AE`.
4. **Alexandrov for the Moreau envelope** - `moreau_alexandrov_AE` and, with
   the Hessian symmetry now proved, `moreau_alexandrov_sym_AE`: a.e. point has
   a second-order expansion whose form is bounded, SYMMETRIC and psd.
5. **Hessian symmetry** - `moreau_second_difference_limit` (the second
   difference divided by `t^2` converges to the UNSYMMETRISED `u . A v`) and
   `moreau_hessian_symmetric` (`u . (v - D v) = v . (u - D u)`), obtained by
   running that limit on both orderings of `u`,`v` and applying
   `tendsto_unique` to `second_difference_symmetric`.
6. **The transport envelope -> f** (this session's main work). The resolvent
   `R = prox f` is the bridge; the chain is:
   - `f_increment_exact` - the EXACT bookkeeping identity. With
     `G z = z - R z`, the increment of `f` between two proximal points measured
     against `G x` equals the increment of the envelope measured against the
     same vector, minus `norm(g)^2/2` where `g` is the increment of `G`. The
     first-order terms in `G` cancel identically; this is what lets a
     second-order expansion survive the transport.
   - `prox_deriv_inj_subdiff_singleton` - where `DR` is injective the
     subdifferential downstream is a SINGLETON. Two subgradients at `R x` would
     make `R` constant on a nondegenerate segment through `x` (using convexity
     of `subdiff` and `subdiff_prox`), so `DR` would kill that direction.
   - `prox_fibre_bounded` / `prox_fibre_compact` /
     `prox_local_inverse_continuous` - local invertibility of `R` WITHOUT an
     inverse function theorem: the fibre `{z. dist (R z) y <= 1}` is compact
     (bounded because `z - R z` is a subgradient at `R z` and subgradients are
     locally bounded, `subdiff_norm_le`), and on it `z |-> dist (R z) y`
     vanishes only at `x`, so it is bounded below outside any ball around `x`.
   - `taylor_remainder_identity` - the algebra: with `A u = u - D u`,
     `B u = D' u - u`, `k = D h - rho`, `g = A h + rho`, the leading terms
     `D h . A h` cancel identically and only rho-carrying terms remain.
   - `f_taylor_limit` - the analytic assembly (quantified by
     `prox_remainder_small`, `moreau_taylor_bound`, `inj_linear_bounded_below`).
   - `transported_form_symmetric` / `transported_form_psd` / `f_alexandrov_at`.
7. **The measure-theoretic assembly** - `convex_alexandrov`. Every `y` is
   `R z` for some `z` (Minty). The exceptional `z` split into `Nd` (`R` not
   differentiable; negligible by Rademacher, and its image is negligible by
   `negligible_locally_Lipschitz_image` since `R` is 1-Lipschitz) and `Sg`
   (`DR` singular; its image is negligible by `baby_Sard`, using
   `dim_range_lt_of_not_inj`). Bridging lemma `AE_lborel_negligible` converts
   an `AE ... in lborel` statement into `negligible` via
   `null_sets_completionI` + `negligible_iff_null_sets`.

NEXT (task #9): E4 Jensen is now PROVED (see below); remaining are E5 the
Crandall-Ishii theorem on sums and E6 `max_principle_boundary`. The probabilistic
line (Phases A4-G, tasks #4-#7) is independent of all of this and untouched.

## Build and audits

```bash
~/isabelle/bin/isabelle build -d . Arbitrage
```

- Session `Arbitrage`, ~50 theory files, 34 in ROOT (rest reached as imports).
  ~70 s warm, exit 0. ROOT `sessions`: `Martingales`, `Kolmogorov_Chentsov`,
  `Levy_Prokhorov_Metric`, `Standard_Borel_Spaces`, `HOL-Complex_Analysis`
  (all heaps prebuilt).
- No placeholder proofs anywhere. Check with `grep -cw 'sorry\|oops' *.thy`
  (`-cw` matters: plain grep false-positives on "loops"; and never write the
  keyword in prose in a `.thy`, even in a text block — it trips the audit).
  PIDE's `commands_bad = 0` is the authoritative check.
- Locale-axiom audit (a locale `assumes` is an assumption the grep cannot
  see):

  ```bash
  grep -n -A3 '^locale ' *.thy | grep -B1 assumes
  grep -rn 'comparison_principle\|max_principle_boundary' *.thy
  ```

  The only non-structural locale axiom is `comparison_principle` (see "The
  two named gaps"). Everything else claimed proved is proved.

## Scoreboard: paper results

| Paper result | Status | Where |
|---|---|---|
| **Thm 1.1** (main theorem) | ball fragment assembled; rest = THE PLAN below | `Theorem_1_1.thy` |
| Eq. (1.6) value function `v`, `v <= ball_v` | done; plus `val_fn_mono` (monotone in the domain, unconditional) | `Value_Function.thy` |
| Eq. (1.9) `F` as `ell_op`, `feasible`; Eq. (1.10) geometricity | done | `Relative_Arbitrage_PDE.thy` |
| **Lemma 2.1** (both directions, no closure) | done | `Lemma_2_1_Exact.thy` |
| **Lemma 2.2** (relative compactness of `P_x`) | fixed-horizon + diagonal + consistency DONE; remaining: Phase A below | `Path_Tightness*.thy` |
| **Lemma 2.3** (compactness = closedness too) | deterministic cores done; remaining: Phase B | task refs in Phase B |
| **Prop 2.4** (usc of `v` + DPP) | `ess_inf_time` calculus done; remaining: Phase C | `Value_Function.thy` |
| **Def. 3.1**, Eq. (3.4), **Eq. (3.5)**, **Eq. (3.6)**, **Lemma 3.1** (all clauses) | **done** | `Relative_Arbitrage_PDE/Lemma_3_1*/Poincare_Separation/Envelopes.thy` |
| Sections 3.1/3.2 (`v` is a viscosity solution) | not started; remaining: Phase D | — |
| **Example 3.1** (ball, puncture removed) | done | `Brownian_Optimal_Boundary.thy`, `Envelopes.thy` |
| **Thm 4.2(a)** general `K` | Crandall-Ishii chain stages 1-10 PROVED, ending at `comparison_supconv_doubling_complete` (the engine). Its TARGET was found FALSE and the interface corrected — see the handover. Remains: produce Jensen's geometric data | `Comparison_Assembly.thy` (chain map at end), `Sup_Convolution.thy`, `Lemma_3_1_Envelopes.thy` |
| **Thm 4.2** smooth-strict case, any compact `K` | **done** | `Relative_Arbitrage_Comparison.thy` |
| **Thm 4.2(b)**, **4.3**, **Prop 4.1** from the 4.2(a) interface | **done** | `Lemma_3_1_Envelopes.thy` |
| **Thm 4.3**, **Prop 4.1** for the BALL, unconditional | **done** | `Relative_Arbitrage_Comparison.thy` |
| **Prop 5.1**, **5.2** (continuity of `v`) | behind Prop 2.4: Phase F | — |
| **Lem 5.3** deterministic core | **done** | `Poincare_Separation.thy` |
| **Prop 5.4**, **5.5** | SKIPPED by instruction | — |

## The two named gaps (assumption audit)

1. `locale comparison_principle` (Relative_Arbitrage_Uniqueness.thy:469) —
   the Crandall-Ishii comparison principle, ASSUMED, never interpreted; its
   only consumer takes it as an explicit hypothesis. No unconditional result
   depends on it. Discharging it is Phase E.
2. `max_principle_boundary` — Theorem 4.2(a) isolated as an explicit
   predicate; the general-`K` Section 4 chain is conditional on it, the ball
   chain is not. **CORRECTED 2026-07-31**: the original hypothesis-free form
   was FALSE (`max_principle_boundary_counterexample`), so it was not a gap
   waiting to be filled but a gap that could not be filled. The predicate now
   carries continuity of `u` and `w` on `K`; the old form survives as
   `max_principle_boundary_raw` only as the refutation's target. Anyone
   auditing this gap should read the handover section before working on it.

# THE PLAN: finishing Theorem 1.1 in full

Theorem 1.1 states: `v` is the unique upper semicontinuous viscosity solution
of Eq. (1.9)-(1.10) on `K` with zero boundary values. `Theorem_1_1.thy`
(`theorem_1_1_ball_fragment`) already assembles, for `K = cball 0 r`:
`v <= ball_v` everywhere, `v = ball_v` on the sphere, and the uniqueness
clause (any continuous viscosity solution with `ball_v`'s boundary data IS
`ball_v` — no Crandall-Ishii). What is missing to instantiate it at `u = v`,
and to reach general `K`, decomposes into six phases. A and (B,C) are
sequential; D needs A-C; E is independent; F needs C; assembly G needs all.

```
A (finish Lemma 2.2)
  └─> B (Lemma 2.3)
        └─> C (Prop 2.4: usc + DPP)
              ├─> D (§3.1-3.2: v is a viscosity solution)  ─┐
              └─> F (§5: Props 5.1-5.2, continuity of v)   ─┼─> G (assembly,
                                                            │    Theorem_1_1.thy)
E (Crandall-Ishii -> Thm 4.2(a); GENERAL K only, ball-free) ┘
```

Decision point: Theorem 1.1 **restricted to the ball** does not need Phase E
(the ball's Section 4 is unconditional). Full generality does. Do the ball
first; E is a separate, generic-infrastructure project.

## Phase A — finish Lemma 2.2 (weak relative compactness of `P_x`)

DONE so far (see archive of completed work below for mechanisms):
per-horizon tightness and subsequence extraction, scalar + vector + from the
martingale package (`tight_on_set_path_laws_vec`,
`path_laws_convergent_subsequence_market`); the diagonal subsequence over all
integer horizons (`path_laws_diagonal_subsequence`); projective consistency
of the limit family (`path_laws_diagonal_consistent`); the continuous-mapping
theorem (`weak_conv_on_pushforward`); evaluation continuity + the Fatou
transfer of moment bounds to limits (`continuous_map_path_eval`,
`weak_conv_on_nn_integral_le`).

Architecture (RESOLVED — do not revisit): no `C([0,inf))` metric space.
Diagonal over integer horizons + Daniell-Kolmogorov. Remaining work items,
in order:

- **A1. Moment transfer corollary — DONE (2026-07-29).**
  `path_law_limit_moment_bound` (Path_Tightness.thy): any weak limit of path
  laws whose processes carry the Eq. (2.7) package satisfies the coordinate
  fourth-moment bound as an `nn_integral`. Kit added:
  `continuous_map_real_diff` (missing from the `continuous_map_real_*`
  family; proved via `continuous_map_atin` + `tendsto_diff`),
  `continuous_map_path_eval_nth` (evaluation composed with `vec_nth` through
  the [simp] bridge `continuous_map_iff_continuous2`),
  `continuous_map_path_moment` (with library `continuous_map_real_pow`).
  Proof: `weak_conv_on_nn_integral_le` + `nn_integral_distr` on the
  approximating laws (`restrict` evaluates under the binder by simp) +
  `nn_integral_eq_integral` + the Bochner `mom` package. Applies verbatim to
  the diagonal limits `N m` by instantiating at the subsequence.
- **A2. Projective-limit assembly — DONE (2026-07-29).**
  **`projective_limit_of_consistent_path_laws`** (Path_Tightness.thy): from
  any horizon-consistent family of prob path laws `N m` (exact conclusion
  shape of `path_laws_diagonal_consistent` + prob_space, the latter supplied
  by the new `weak_conv_on_prob_space` in Path_Space.thy — test against the
  constant 1), ONE probability measure `L` on
  `PiM {0..} (%_. borel :: real^'m measure)` whose finite-`J` marginal is the
  `J`-marginal of `N m` for EVERY horizon `m` covering `J`. Construction:
  `mm J := LEAST m. J <= {0..real m}` (existence by `real_arch_simple` +
  `Max_ge`); horizon-independence of the marginals by `consist` +
  `distr_distr` + the restrict-restrict collapse; the projective property is
  the same collapse one level up (`measurable_component_singleton` +
  `measurable_restrict` for the `PiM H -> PiM J` map); the locale
  interpretation discharges the three RAW ancestor axioms of
  `prob_space (P J)` (sigma-finite cover `{space (P J)}`, finiteness, mass
  one) because `unfold_locales` decomposes them — the recorded trap;
  marginal identification of `lim` via `emeasure_distr` + `prod_emb_def` +
  `emeasure_lim_emb` + `measure_eqI`. Kit: `marginal_map_measurable`
  (path-space-to-`PiM J` restriction, from `continuous_map_path_eval`).
- **A3. Continuity of the limit's paths.** DETERMINISTIC CORE DONE
  (2026-07-29, second brick, Path_Tightness.thy, all green):
  **`dyadic_pair_modulus`** (continuity-free chaining bound for pairs of
  same-level dyadics, any metric space — `dyadic_chaining` with
  `c j := E * 2 powr (-g j)`; this is `modulus_of_good_path`'s K-step freed
  of the continuity hypothesis and with a general prefactor `E`);
  **`dyadic_ext`** — the extension operator `lim (%k. f (danchor k t))` at
  `'b::complete_space`, with `modulus_level_choice` (pick a level with
  modulus below any `e`), `dyadic_ext_tendsto` (anchors are Cauchy:
  two anchors past level `Suc n'` are within `1/2^n'`; `metric_CauchyI` +
  `Cauchy_convergent` + `convergent_LIMSEQ_iff`), `dyadic_ext_dyadic`
  (agrees with `f` at dyadic points — eventually-constant anchor sequence),
  `dyadic_ext_dist_le` (the SAME modulus for all real pairs at strict gap
  `< 1/2^n'` — anchor error absorbed via Archimedean choice +
  `tendsto_dist`/`tendsto_upperbound`), `dyadic_ext_continuous_on`.
  PROBABILISTIC HALF, first pieces (same day, all green):
  `lim_coordinate_measurable`, `lim_coordinate_moment_package` (Bochner
  adapter from the `nn_integral` bound via `integrableI_nonneg`), and
  **`lim_dyadic_good_AE`** — almost every sample of the projective limit
  satisfies the dyadic moduli from some level on, at EVERY integer horizon
  and coordinate simultaneously (`dyadic_bad_event_tail_mom` per `(T,l)`,
  the level intersection is null since its measure sits under a geometric
  tail, `AE_all_countable` over the countable horizon-coordinate pairs;
  extraction of the good property from the complement via the search-free
  `E_def`+blast+linarith pattern — `fastforce simp: not_le` on the raw
  complement DIVERGED and `auto` could not instantiate the bounded
  quantifiers). ALSO DONE (same run): **`dyadic_ext_continuous_on_all`**
  (continuity on all of `{0..}` from per-horizon good bounds — each point is
  inside horizon `nat floor t + 1`, `dyadic_ext` is horizon-free, delta
  capped by `min (1/2^n') (real T - t)`); **`dyadic_bad_event_sets_strict`**
  and **`lim_good_set`** — the good set IS measurable: complement of
  strict-threshold bad events (countable unions, harmless on empty ranges),
  assembled by `countable_INT'`/`countable_UN''`; the set equality proved by
  the structured two-inclusion pattern (an `auto ... blast+` attempt was
  FLAGGED still-running — the trap again).
  MODIFICATION IDENTITY DONE (2026-07-30): **`lim_vector_increment_tail`**
  (vector Chebyshev at the fourth moment: coordinate tails via
  `fourth_moment_tail`, union bound over coordinates, threshold `e/CARD('m)`)
  and **`dyadic_ext_modification`** — `AE \<omega> in L. dyadic_ext \<omega> t = \<omega> t` for
  every `t >= 0`: the truncated distances `min (dist (\<omega>(danchor k t)) (\<omega> t)) 1`
  have `nn_integral <= e + O((t - danchor k t)^2)` (Chebyshev), converge a.s.
  to the truncated extension distance (on the good event, with the vector
  bound assembled by `choice` over per-coordinate levels + `Max (range nl)`),
  and Fatou (`nn_integral_liminf` + `lim_imp_Liminf` + `Liminf_mono`) gives
  `nn_integral <= ennreal e` for every `e`, hence `= 0` (`ennreal_le_epsilon`)
  and a.e. equality (`nn_integral_0_iff_AE`). TRAPS hit and recorded: the
  unanchored-`define` fresh-type trap struck TWICE more (the `u`-family and
  the final `fix \<omega>` — annotate both); `intro ennreal_leI` cannot target `<= 1`
  (write `<= ennreal 1`); `use <quantified fact> in linarith` fails (fix the
  variable first); the conditional simp rule `ennreal_eq_zero_iff` interferes
  with `ennreal_eq_0_iff` (supply nonnegativity and use plain simp).
  **A3 COMPLETE (2026-07-30): `lim_continuous_modification`** — the bundle:
  from the moment package alone, the projective limit carries a process `Y`
  (= `dyadic_ext` gated on the measurable good set) with measurable time
  sections, EVERYWHERE-continuous paths on `{0..}`, and `Y t = \<omega> t` a.s. at
  every time. The obsolete assembly note follows for the record: define
  `Y t \<omega> := dyadic_ext \<omega> t` gated on `lim_good_set`'s set (vector good bound
  `E = CARD('m)` via `norm_le_l1_cart` + Max over coordinates of the per-`l`
  levels), continuity everywhere from `dyadic_ext_continuous_on_all`,
  per-`t` measurability (`dyadic_ext` is DEFINITIONALLY `lim` along anchors,
  so `borel_measurable_lim_metric` applies directly; `danchor_nonneg` keeps
  anchor times in `{0..}`), and the modification identity
  `AE \<omega>. Y t \<omega> = \<omega> t` (a.s. anchor convergence versus convergence in
  probability from `fourth_moment_tail` at the anchors, glued by the
  truncated-distance Fatou argument as in Vitali's `tail_bound_limit`).
  FIRST BRICK (same day):
  **`lim_coordinate_moment_bound`** (Path_Tightness.thy) — the Eq. (2.7)
  package holds for the COORDINATES of the projective limit: the increment
  moment is a function of the two-point marginal `J = {u,v}`, which `L`
  inherits from `N m` (both `nn_integral_distr` steps need measurability
  stated wrt the DISTR — transport `hmJ` with
  `measurable_cong_sets[OF sets_distr refl]`; and the `measurable` method
  needs the `vec_nth`-composed evaluations declared, not just the raw ones).
  REMAINING: the `lim` measure lives on the
  product sigma-algebra where continuity is not an event. Route:
  `dyadic_bad_event_tail_mom` + Borel-Cantelli give a measurable full-measure
  set on which all dyadic moduli hold from some level; on it,
  `holder_of_good_dyadics` gives uniform continuity on dyadics; define the
  process as the continuous MODIFICATION (limit along dyadics — the
  Kolmogorov-Chentsov pattern; the AFP KC entry is the reference but is
  incompatible with Martingales imports, so build on our own
  `Modulus_Tails`/`Holder_Interpolation` machinery, which is exactly shaped
  for this). Medium-large. This yields: a prob space + a process, continuous
  paths everywhere (on a full set), with the prescribed finite-dimensional
  laws.
- **A4. Currying to the `P_x` sample type.** `mkt_exit_vals` fixes the
  sample type `('n => real => real) measure`. Transport the A3 measure along
  the measurable bijection between `real => real^'n` (product sigma-algebra)
  and `'n => real => real`; laws and processes move by `distr` +
  `ess_inf_time_distr`. Small-medium bookkeeping.
- **A5. Statement of Lemma 2.2.** Package A1-A4: every sequence in the
  admissible family has a subsequence and a limit LAW on the `P_x` sample
  type whose finite-dimensional distributions converge and whose canonical
  process has continuous paths. (The paper's "relative compactness in
  C([0,inf))" is used downstream only through this.)
- **A6. AE/stopping bridges** to `sufficiently_volatile_market`: the locale's
  hypotheses are AE and stopped at `tau`; the tightness machinery wants
  everywhere-hypotheses for the STOPPED process. Bridges:
  restrict to the full-measure set (or AE-variants of the adapter);
  `stopped_martingale_L2` / `stopped_compensated_square`
  (Stopped_Localization) keep the package under stopping; per-coordinate
  compensator `A_l = integral of (acov)_ll` has rate `<= L` by
  `feasible_diag_bound`. Small-medium.

## Phase B — Lemma 2.3 (the limit law is admissible: closedness)

- **B1. Skorokhod representation, layer 5.** Layers 1-4 done
  (`Measure_Continuity_Sets.thy`: null-boundary balls, covers, partitions;
  `Stacking_Intervals.thy`: the slab partition of `[0,1)`). Remaining:
  nest the partitions over `e = 1/k`, build the coupling maps
  `[0,1) -> path space` matching partition masses (weak convergence gives
  convergence on the null-boundary pieces), Borel-Cantelli for a.s.
  convergence. Large but fully scoped; the classical Billingsley
  construction. NOTE the two rejected routes (do not retry): transferring
  the 1-D `Skorohod` along a Borel isomorphism (statement is topological);
  Strassen-Dudley coupling (AFP has no coupling/Wasserstein development).
- **B2. Martingale property closed under weak limits.** Inputs DONE:
  `Vitali_Convergence.thy` (uniform integrability + Vitali), and
  `Conditional_UI.thy` (`unif_integrable_of_averaging`,
  `cond_exp_family_unif_integrable` — UI of conditional-expectation families,
  built exactly for this). Combine with B1's a.s. representation: pass the
  martingale identity `E[X_t; A] = E[X_s; A]` (for `A` in a generator of
  `F_s` with null-boundary sets) through a.s. convergence + Vitali; the
  moment bounds from A1 give the UI hypothesis. Medium-large.
- **B3. Covariation/admissibility constraint closed under weak limits.**
  Deterministic core DONE: `closed_feasible` (+ `feasible_bounded`) — the
  constraint set is COMPACT and convex (`Relative_Arbitrage_Convexity`).
  Remaining: the paper's argument that a.s. limits keep
  `d<X>/dt` in the (compact convex) feasible set — via the energy identity,
  Vitali, and Lemma 2.1's exact characterization (both directions proved).
  Medium.
- **B4. Statement of Lemma 2.3**: `P_x`-type admissible sets are closed under
  the Phase-A limits; with Lemma 2.2, sequentially compact. Assembly.

## Phase C — Prop 2.4 (usc of `v` + dynamic programming principle)

- **C0. `ess_inf_time` calculus: DONE** (`ess_inf_timeI`, `ess_inf_time_AE`
  — the nontrivial one, via `ennreal_Sup_countable_SUP` + `AE_all_countable`
  — `_mono`, `_superadd`, `_le_nn_integral`, `_distr`).
- **C1. usc of `v`.** From compactness (Phases A+B): a maximizing sequence
  of laws at `x_j -> x` has a convergent subsequence; the limit is admissible
  for `x`; `ess_inf_time` is usc along the convergence (uses B1's a.s.
  representation). Medium.
- **C2. Concatenation of laws at a stopping time.** Machinery AVAILABLE:
  AFP `Disintegration` (`measure_disintegration`, Disintegration.thy:1539);
  its session needs only `S_Finite_Measure_Monad` beyond what ROOT has.
  Build: given an admissible law and a stopping time, disintegrate, replace
  the conditional continuation by another admissible family, reglue; verify
  admissibility of the concatenation. Large.
- **C3. Measurable selection.** ABSENT from Isabelle+AFP entirely (searched:
  `measurable_selection`, Kuratowski, Ryll-Nardzewski — nothing
  measure-theoretic). Needed to pick near-optimal continuations measurably in
  the starting point. Build Kuratowski–Ryll-Nardzewski for Polish spaces
  from scratch. THE critical-path item of the whole plan; generic
  infrastructure, AFP-worthy on its own. Large.
- **C4. The DPP** (Eq. (2.9)): `<=` from C2 (concatenation cannot increase
  beyond the split essential infima — uses `ess_inf_time_superadd`); `>=`
  from C3 (measurable near-optimal selection); usc clause from C1.
  Reconstructed from [LR24, Prop 2.2(ii),(iii)] — there is no proof text in
  this paper; budget as original work.

## Phase D — Sections 3.1-3.2: `v` is a viscosity solution

Not started; needs A-C. Two halves:

- **D1. Subsolution** (paper Eqs. (3.17)-(3.25)): test function at an
  interior maximum; the DPP + Ito on the test function (QUADRATIC/smooth
  case only — the repo's `ito_volatile_market` interface plus
  `Z_martingale_of_cond_covariation`) force `F(Dphi, D2phi) <= 1` via the
  compactness of the feasible set (`closed_feasible` + `feasible_bounded`)
  and optimizer extraction (Lemma 2.2/2.3).
- **D2. Supersolution** (Eq. (3.26)): requires EXHIBITING near-optimal
  controlled diffusions with prescribed covariance — weak existence for the
  SDE Eq. (3.11). This is the remaining substantive piece of task 15
  (stochastic integration): weak solutions via time-changed/rotated Brownian
  motion built from the repo's own Brownian construction
  (`Brownian_Motion*.thy`). The simple-integrand stochastic integral, its
  isometry and L2 closure are DONE (`Stochastic_Integral_Simple/L2`,
  `L2_Limits`); what D2 adds is the construction of solutions, not more
  integration theory. Large.

## Phase E — Crandall-Ishii (general `K` only)

**E1 STARTED (2026-07-30): `Sup_Convolution.thy`** (new, in ROOT, green —
imports only `HOL-Analysis.Analysis`, so it loads standalone in PIDE and is
independent of both existing heavy chains): `supconv u e x =
SUP y. u y - (dist x y)^2/(2e)` with `supconv_bdd_above`, `supconv_ge`
(`u <= supconv u e`), `supconv_le` (bounded by `u`'s bound),
`cSUP_plus_const` (constants move through conditional SUPs — antisymmetry,
no library lemma found), `convex_on_cSUP` (a pointwise-bounded SUP of convex
functions is convex; note `convex_onI` in this HOL-Analysis requires the
`convex UNIV` side goal, and `convex_onD`'s instance order is
`[of t x1 x2]` for `(1-t)x1 + t x2`), `convex_on_affine_inner`,
`supconv_square_decomp` (completing the square:
`u y - |x-y|^2/2e + |x|^2/2e = (u y - |y|^2/2e) + x.(y/e)`, affine in `x`),
and the headline **`supconv_semiconvex`**: `supconv u e + |.|^2/(2e)` is
CONVEX — a supremum of affine functions.

**E1 CORE DONE (2026-07-30)**, same theory, all green + batch-built:
`supconv_continuous` (continuity of `supconv u e` on UNIV, with NO Lipschitz
computation: it is (semiconvex combo) − |x|^2/2e, and `convex_on_continuous`
[HOL-Analysis, open S + convex_on ⟹ continuous_on] does the rest),
`supconv_near_optimizer` (the attainment/"magic" estimate: for any δ>0 a
near-optimizer y has `supconv u e x ≤ u y − d²/2e + δ` and
`d² ≤ 2e(B − u x + δ)`, via `less_cSUP_iff`), and `supconv_tendsto`
(`supconv u e x ⟶ u x` in `at_right 0` at every continuity point of u:
near-optimizers localize in an O(√e) ball). E1 remaining (deferred until the
consumers exist): subsolution transfer (needs the PDE operator — heavy
chain, so it lives in a later theory, not Sup_Convolution).

**E3a DONE (2026-07-30)** (in `Sup_Convolution.thy`, section "Subgradients
of convex functions"): `subdiff` (global subdifferential of a finite convex
function on R^n), `subdiffI/D`, `subdiff_monotone` (crosswise addition),
`closed_epigraph_UNIV`, `epigraph_frontier_point`, and the meat
**`subdiff_nonempty`** via `supporting_hyperplane_frontier` [Starlike]
applied to the epigraph (`convex_epigraphI`, `mem_epigraph` exist in
Convex.thy): the hyperplane cannot be vertical (else its horizontal part
dies against `y := x − p0`), and normalizing by the vertical component
yields the subgradient. Note the product-space inner product is
`inner_prod_def`; `(0,0) ≠ 0` needs `zero_prod_def`.

**E3b DONE (2026-07-30)** (same theory, "The proximal map"): `prox_attained`
(the objective `f · + dist x ·²/2` attains its min: affine minorant from
`subdiff_nonempty` at 0 + AM-GM makes the sublevel set of the objective
bounded, `closed_Collect_le` + `continuous_attains_inf` finish),
`midpoint_dist_identity` (parallelogram-law midpoint identity — NO
parallelogram law exists in this HOL-Analysis; proved by inner expansion),
`prox_unique` (midpoint strictly beats two distinct minimizers),
`prox` (THE-definition) + `prox_min`, `prox_step_expand`,
`minimizer_subdiff` (`x − prox f x ∈ subdiff f (prox f x)`: convexity turns
the quadratic minimality error into a linear inequality via a `t → 0`
perturbation and `field_le_epsilon`), **`prox_nonexpansive`** (the resolvent
is 1-Lipschitz: subdifferential monotonicity + Cauchy-Schwarz), and
**`minty_surjective`** (`id + subdiff f` is onto — witnessed by prox).

**E3 route (revised, MATERIALLY DE-RISKED by library audit 2026-07-30):**
this dev Isabelle contains `HOL-Analysis.Lebesgue_Differentiation` with
**`Lebesgue_differentiation_thm`** (BV functions on a real interval are
differentiable a.e. — `_increasing`/`_decreasing` corollaries for monotone
functions) and `HOL-Analysis.Absolute_Continuity` (Lipschitz ⟹ absolutely
continuous, FTC for AC functions). That is the hard 1D core of Rademacher.
`Change_Of_Vars` supplies `borel_measurable_partial_derivatives`,
`baby_Sard`, `integral_on_image_ubound`, `m_diff_image_weak` (the
`|g(A)| ≤ ∫_A |det Dg|` area bound — the measure-theoretic core of Jensen's
lemma E4 in the smooth case). Plan: E3c Rademacher in R^n (1D core along
lines + Fubini + rational directions + Lipschitz uniformity), E3d Alexandrov
via the Minty resolvent: `prox_nonexpansive` makes `prox f` a 1-Lipschitz
map defined on ALL of R^n, Rademacher differentiates it a.e., and where the
derivative is invertible the subdifferential/gradient of `f` is
differentiable — Alexandrov without distributional Hessians. Neither
Rademacher nor Alexandrov exists anywhere in Isabelle/AFP (grepped both).

**E3c STARTED (2026-07-30)** (same theory, "Rademacher, dimension one"):
`lipschitz_differentiable_ae_1d` (a Lipschitz `real ⇒ 'a::euclidean_space`
map is differentiable a.e.: Lipschitz ⟹ `absolutely_continuous_on` each
`{-n..n}` [`Lipschitz_imp_absolutely_continuous`] ⟹ BV
[`absolutely_continuous_on_imp_has_bounded_variation_on`, second premise
`bounded_closed_interval`] ⟹ `Lebesgue_differentiation_thm` [+
`is_interval_cc`]; countable union over n via `negligible_Union_nat` and
`real_arch_simple`), and `lipschitz_line_section_diff_ae` (sections of a
Lipschitz map along any line are differentiable at a.e. parameter — the
slicing input to the Fubini step).

**E3c R2 DONE (2026-07-30) — directional derivatives exist a.e.** This is
the first genuinely n-dimensional milestone of Rademacher, all in
`Sup_Convolution.thy`, green + batch-built:
- `dquot f v x t = (f (x + t *R v) - f x) /R t`, `dlim_set f v` = points
  where the quotient has a limit as `t -> 0`, `dcrit f v k m` = the Cauchy
  criterion at accuracy `1/Suc k` over the punctured window `1/Suc m`.
- `closed_dcrit` + `dlim_set_eq_dcrit` + **`borel_dlim_set`**: `dlim_set` is
  Borel. KEY SIMPLIFICATION vs the textbook proof: no rational indexing is
  needed — `dcrit` is an intersection of ARBITRARILY many closed sets
  (`closed_INT` has no countability hypothesis), so only the two accuracy
  indices must be countable. The Cauchy-to-limit direction runs through the
  sequence `t = 1/Suc n` (`metric_CauchyI`, `Cauchy_convergent`) and then
  upgrades to the filter limit.
- **`negligible_of_basis_sections`**: a BOREL set whose every line in a
  fixed basis direction is negligible is negligible. Proof: `lborel_eq`
  (Lebesgue measure is the pushforward of `PiM Basis lborel` under
  `λf. Σ b∈Basis. f b *R b`) + `product_nn_integral_insert` (peel the `b`
  coordinate) + `null_sets_completion_iff` (`lebesgue ≡ completion lborel`,
  so for Borel sets `negligible ⟷ null in lborel`, recorded as
  `negligible_iff_null_lborel`). Borel-ness is essential, not cosmetic.
- `dquot_of_differentiable` (a differentiable curve's difference quotient
  converges — via `vector_derivative_works`/`has_vector_derivative_def`, so
  the derivative is literally `λh. h *R L`, plus `has_derivative_at` and
  `Lim_transform_eventually`), `lipschitz_continuous_on_UNIV`, and the
  headline **`negligible_no_dderiv_basis`**: for Lipschitz `f` and
  `b ∈ Basis`, `negligible (- dlim_set f b)`.
NOTE the codomain must be `'b::{euclidean_space,banach}` — the 1D core
(`Lebesgue_differentiation_thm`) needs a Euclidean codomain.

**E3c R2' DONE (2026-07-30) — ARBITRARY directions.** `dlim_set_precompose`
(`dlim_set (f o T) u = T -` dlim_set f (T u)` for linear T) and
**`negligible_no_dderiv`**: for Lipschitz `f` and ANY `v \<noteq> 0`,
`negligible (- dlim_set f v)`. Construction: `orthogonal_transformation_exists`
gives orthogonal `S` with `S (norm v *R b) = v` for a basis vector `b`
(`norm_Basis`, `nonempty_Basis`); `T = S o (norm v) *R (-)` is linear,
injective and SURJECTIVE (`orthogonal_transformation_surj` — do NOT reach for
`linear_injective_imp_surjective`, which lives in `vector_space_pair` with a
dimension hypothesis); then `negligible_linear_image_eq` +
`surj_image_vimage_eq` transport the basis-direction result. Surjectivity is
genuinely needed: `T ` (T -` X) = X ∩ range T` only equals `X` when `T` is
onto.
- NOTE `negligible_eq_zero_density` (Vitali_Covering_Theorem) characterizes
  negligibility with NO measurability of S — kept in reserve.
**E3c R3a DONE (2026-07-30) — the derivative as a measurable function.**
`ddir f v x = lim (λn. dquot f v x (inverse (Suc n)))` names the directional
derivative by the SEQUENTIAL limit; `ddir_tendsto` shows that on `dlim_set`
it IS the filter limit (`filterlim_inverse_Suc` = `filterlim_at` +
`LIMSEQ_inverse_real_of_nat`, composed with `filterlim_compose`, then
`limI`), so nothing is lost — and the gain is `borel_measurable_ddir` in one
line from `borel_measurable_lim_metric` (which absorbs the non-convergent
points internally, so no restriction to `dlim_set` appears in the
statement). `norm_ddir_le`: `|D_v f| ≤ B |v|` wherever it exists, by
`tendsto_upperbound` against the eventual quotient bound — this is the
integrability input for R3.

**E3c R3b DONE (2026-07-30) — FTC along a line.** `ddir_line_eq` identifies
the two derivative notions (`ddir f v (z + t*R v) = vector_derivative
(λs. f (z + s*R v)) (at t)` wherever the line section is differentiable; the
proof needs `dquot_tendsto_vector_derivative`, which is the strengthened form
of `dquot_of_differentiable` that NAMES its limit, plus `tendsto_unique` with
`at_neq_bot`). Then **`ftc_along_line`**:
`(λs. ddir f v (z + s*R v)) has_integral (f (z + c*R v) - f (z + a*R v))` on
`{a..c}` for Lipschitz `f` — by `Lipschitz_imp_absolutely_continuous` +
`fundamental_theorem_of_calculus_absolutely_continuous` (whose exceptional set
is exactly the negligible `lipschitz_line_section_diff_ae` set) +
`vector_derivative_works` + `has_vector_derivative_at_within`.

**E3c R4a/R4b DONE (2026-07-30) — structure of the direction map.** Proved
BEFORE linearity is available, and independent of R3:
`dquot_scale`/**`ddir_scale`** (positive homogeneity: `x ∈ dlim_set f v` and
`c ≠ 0` give `x ∈ dlim_set f (c *R v)` with `D_{cv} f x = c *R D_v f x`; the
proof reparametrises `t ↦ c*t` as a `filterlim ... (at 0) (at 0)` and
transports with `Lim_transform_eventually`),
**`ddir_lipschitz_in_direction`** (`|D_u f x − D_v f x| ≤ B |u − v|` whenever
both exist — the SAME constant as `f`; via `tendsto_upperbound` on the
quotient difference), and **`negligible_no_dderiv_countable`** (for a
countable set `V` of nonzero directions, `- (⋂v∈V. dlim_set f v)` is
negligible, i.e. ALL directions in `V` are differentiable simultaneously
a.e.). Together these are the whole "uniform control" half of R4: once
linearity holds on a countable dense set of directions, the Lipschitz
estimate extends the `o(t)` bound to every direction uniformly.

**E3c R4c DONE (2026-07-30) — directional ⟹ FULL differentiability.**
**`differentiable_of_dense_linear_ddir`**: if `f` is Lipschitz and at a point
`x` the difference quotients along a DENSE set `D` of directions converge to
`T w` for a bounded linear `T`, then `(f has_derivative T) (at x)`. Mechanism:
the quotients are equi-Lipschitz in the direction (constant `B`), the unit
sphere is compact (`compact_sphere` + `compactE_image`), so finitely many
`w ∈ D` δ-cover it and a `Min` over their thresholds gives ONE `d0` that works
for every direction — i.e. pointwise control on a dense set upgrades to the
uniform `o(|h|)` estimate. No measure theory at all.

**This makes R3 the ONLY missing ingredient of Rademacher's theorem.** The
chain is now: R2/R2' (directional derivatives exist a.e. in every direction)
+ R4a/R4b (homogeneity, `B`-Lipschitz dependence on direction, countably many
directions simultaneously) + R4c (dense linear directional ⟹ Fréchet) — so
Rademacher follows from R3 alone.

**R3 STARTED (2026-07-30) — the reduction is now a single named statement.**
`dquot_add_split` (exact algebra: `dquot f (u+v) x t = dquot f v (x + t*R u) t
+ dquot f u x t`; note the sum-of-quotients step needs
`scaleR_add_right[symmetric]` applied by `rule`, since simp collapses the
telescoped numerator first and then cannot re-distribute) and
**`ddir_add_of_shifted_limit`**: if `x ∈ dlim_set f u` and the SHIFTED
quotient `t ↦ dquot f v (x + t*R u) t` converges to `D_v f x`, then
`D_{u+v} f x = D_u f x + D_v f x`. So all of R3's analytic content is now
concentrated in the shifted-quotient convergence — which is FALSE pointwise
(`D_v f` need not be continuous) but true after integration, which is exactly
why R3 is an a.e. statement.

**R3 — remaining plan (library audit 2026-07-30).** The step
that classically needs mollifiers (absent from Isabelle) can instead use
**`absolutely_integrable_approximate_continuous`** (HOL-Analysis
`Absolute_Continuity`, line 2955): for `f` absolutely integrable on a
measurable `S` and `e > 0` it produces a CONTINUOUS BOUNDED `g` with
`∫_S |f − g| < e`. That is L¹-density of continuous functions, which is
exactly what the mollifier was for. Recipe:
**R3 step-2 measure half DONE (2026-07-30):** `inner_sum_scaleR_Basis`
(`(Σi∈Basis. c i *R i) ∙ j = c j`), `content_box_int_translate`
(`content (cbox a b ∩ cbox (a+w) (b+w)) = ∏i∈Basis. max 0 (min (b∙i) ((b+w)∙i)
− max (a∙i) ((a+w)∙i))` — the `max 0` form is what REMOVES the degenerate-box
case split from the limit, since a nonpositive factor makes the product 0
exactly when `content_cbox_cases` gives 0), and
**`content_box_int_translate_tendsto`**: the overlap content tends to
`content (cbox a b)` as `w → 0`, purely by `tendsto_intros` on the product
formula. So `measure (B Δ (B+w)) = 2(content B − content (B ∩ (B+w))) → 0`.

**R3 step-4 DONE (2026-07-30):** **`AE_zero_of_box_integrals_zero`** — a
bounded Borel `g` whose `∫_box g⁺ = ∫_box g⁻` for EVERY open box vanishes a.e.
Built with `density lborel (ennreal o g)` vs `density lborel (ennreal o (-g))`
and `measure_eqI_generator_eq` on the box generator (template copied from
`lborel_eqI`: `Int_stable_def` + `box_Int_box`, `borel_eq_box`,
`UN_box_eq_UNIV`), then testing the resulting equality on `{g > 0}` and
`{g < 0}` with `nn_integral_0_iff_AE`. Traps met: `X ∈ range (λ(a,b). box a b)`
does NOT yield `l`,`u` by `auto`/`case_prod_beta` — obtain the PAIR by `blast`
and split it with `(cases ab)`; and `≠ ∞` will not unify with `neq_top_trans`'s
`≠ top`, so finish finiteness with `(auto simp: top_unique)`. Also, once simp
folds `f x * indicator S x` into the `∫⁺x∈S.` abbreviation, `nn_integral_cong`
no longer applies — prove the integrand is the zero FUNCTION by `ext` instead.

**R3 step-2 DCT DONE (2026-07-30):** `ddir_LIMSEQ` (on `dlim_set`, the
quotients along `t = 1/(n+1)` converge to `ddir` — immediate from
`ddir_tendsto` + `filterlim_inverse_Suc`) and
**`box_integral_dquot_tendsto`**: for Lipschitz `f`, `v ≠ 0` and any Borel `S`
of finite measure, `∫ dquot f v · (1/(n+1)) · 1_S → ∫ ddir f v · 1_S`. Because
`ddir` was DEFINED as the limit along that very sequence, no reparametrisation
is needed; `integral_dominated_convergence` applies with dominating function
`(B‖v‖)·1_S` (integrable since `S` has finite measure) and the a.e.
convergence supplied by `negligible_no_dderiv`. TRAP: `auto` normalises
`real (Suc n)` to `1 + real n`, so a chained `ddir_LIMSEQ` no longer matches —
close the pointwise goal with an explicit `tendsto_mult[OF h tendsto_const]`.

**R3 step-2 TRANSLATION DONE (2026-07-30):** `indicator_box_translate`
(`1_{box (l+c) (r+c)} (x+c) = 1_{box l r} x`, by `mem_box` + `inner_add_left`)
and **`integral_translate_box`**: `∫ h(x+c)·1_{box l r} dx =
∫ h·1_{box (l+c) (r+c)}`, i.e. the shift moves from the integrand onto the
domain. Proof: `integral_distr` along `(+) c` composed with
`lborel_distr_plus`. So BOTH halves of R3 step 2 are now proved
(`box_integral_dquot_tendsto` for the limit, this for the shift).

**R3 step-3 DONE (2026-07-30):** `dquot_indicator_bound`,
`integrable_dquot_indicator` and **`box_integral_add_split`** — for every
`t ≠ 0` the EXACT identity
`∫ dquot f (u+v) · 1_B = ∫ dquot f v · 1_{B + t·u} + ∫ dquot f u · 1_B`.
Proof: `dquot_add_split` pointwise, `Bochner_Integration.integral_add` (both
summands integrable by domination), then `integral_translate_box` moves the
shift onto the box. TRAPS: use `¦B¦` in the dominating function — matching
`integrable_bound`'s `norm (dominating)` otherwise needs `0 ≤ B`, which is not
assumed; and state finite-measure side conditions as `< top`, NOT `< ∞`,
because the two do not unify (same trap as `neq_top_trans` above).

**R3 moving-box, first half DONE (2026-07-30):** **`L1_dquot_tendsto`** — the
quotients converge to `ddir` in L1 on any finite-measure set, not merely
pointwise (`integral_dominated_convergence` on `|q_n − D_v f|`, dominated by
`2|B|‖v‖·1_S` using `norm_dquot_le` and `norm_ddir_le`). L1 convergence is
what survives a moving domain; pointwise would not.

**R3 moving-box, measure half DONE (2026-07-30):** `content_box_translate`
(translating a box does not change its content — straight from the
`content_box_cases` product formula plus `inner_add_left`),
**`box_translate_defect_tendsto`** (the defect
`2(content B − content (B ∩ (B+w))) → 0` as `w → 0`), and
`indicator_diff_abs` (`|1_A − 1_C| = 1_A + 1_C − 2·1_{A∩C}`, the pointwise
identity behind the symmetric-difference bound).
CAUTION: `content_box_int_translate_tendsto` and hence
`box_translate_defect_tendsto` are stated for CLOSED boxes (`cbox`), while the
Borel generator used in step 4 is the OPEN box. The bridge is
`content_box_cbox` (`measure lborel (box a b) = measure lborel (cbox a b)`)
plus `box_Int_box`; do that conversion when assembling.

**R3 moving-domain bound DONE (2026-07-30):** `integrable_bounded_indicator`,
`integral_indicator_symdiff` and **`integral_domain_shift_bound`**:
`|∫ h·1_A − ∫ h·1_C| ≤ |M|·(measure A + measure C − 2·measure (A ∩ C))` for
bounded measurable `h` and finite-measure Borel `A`, `C`. Combined with
`box_translate_defect_tendsto` this is exactly the moving-domain error term.
TRAPS: write `(indicator A x :: real)` in intermediate steps or the polymorphic
indicator picks a different type instance than the goal's `indicat_real`;
`|h·1_A − h·1_C| = |h|·|1_A − 1_C|` needs `right_diff_distrib` FIRST (simp
distributes the wrong way); and to move an equation inside `|·|` before a final
`linarith`, rewrite the abs term itself — linarith cannot rewrite under `abs`.

**R3 limit-passage enablers DONE (2026-07-30):** `integral_box_cbox_eq`
(integrals over an open box and its closure agree — they differ on the
frontier, negligible by `negligible_frontier_interval`; this reconciles the
OPEN boxes of the Borel generator with the CLOSED boxes of the overlap
estimate, resolving the caveat noted above), `filterlim_scaleR_inverse_Suc`
(`u/(n+1) → 0` within the punctured filter `at 0`, for `u ≠ 0`), and
**`defect_seq_tendsto`** (the defect along `w_n = u/(n+1)` tends to 0, by
composing `box_translate_defect_tendsto` with it).

**R3 MOVING-BOX LIMIT DONE (2026-07-30):** `content_cbox_translate` and
**`shifted_box_integral_tendsto`** — the quotient integrated over the
TRANSLATED box `cbox (a + u/(n+1)) (b + u/(n+1))` converges to
`∫ ddir f v · 1_{cbox a b}`. The error splits as
`|∫ q_n 1_{A_n} − ∫ D 1_C| ≤ |B‖v‖|·defect_n + |∫ q_n 1_C − ∫ D 1_C|`, the
first term by `integral_domain_shift_bound` (the quotients are uniformly
bounded, so ONE bound serves all `n`) with `content_cbox_translate` making
`content A_n = content C`, the second by `box_integral_dquot_tendsto`;
`Lim_null_comparison` finishes. This was the hard half of R3's limit passage.

**R3 BOX ADDITIVITY DONE (2026-07-30):** **`box_integral_ddir_add`** —
`∫_{cbox a b} D_{u+v} f = ∫_{cbox a b} D_v f + ∫_{cbox a b} D_u f` for every
box and all nonzero `u`, `v`, `u+v`. Passing to the limit in
`box_integral_add_split` (open→closed via `integral_box_cbox_eq`), with the
three limits supplied by `box_integral_dquot_tendsto` (twice) and
`shifted_box_integral_tendsto`, then `LIMSEQ_unique`. This is R3's analytic
content COMPLETE.

**R3 ennreal BRIDGE DONE (2026-07-30):**
`nn_integral_pos_neg_eq_of_integral_zero` (for integrable `h` with `∫h = 0`,
the positive and negative parts have equal nonnegative integrals — split
`h = max h 0 − max (−h) 0` and apply `nn_integral_eq_integral` to each) and
`ennreal_mult_indicator_eq`. ALSO: `AE_zero_of_box_integrals_zero` now takes
an **a.e.** bound `AE x. |g x| ≤ M` instead of a pointwise one (proof switched
to `nn_integral_mono_AE`) — ESSENTIAL, because `ddir` is bounded only on
`dlim_set`; off it `ddir` is a `lim` of a divergent sequence and no pointwise
bound exists.

## R3 IS PROVED (2026-07-30)

**`ddir_add_AE`**: for a Lipschitz `f` and nonzero `u`, `v`, `u+v`,
`AE x. D_{u+v} f x = D_u f x + D_v f x`. Assembled from
`box_integral_ddir_add` (all box integrals of the defect balance),
`integrable_ddir_indicator` + `AE_dlim_set` (the defect is a.e. bounded — NOT
pointwise, hence the a.e. version of `AE_zero_of_box_integrals_zero`),
`nn_integral_pos_neg_eq_of_integral_zero` (Bochner → ennreal) and
`AE_zero_of_box_integrals_zero` (boxes generate Borel).
TRAP: `unfolding` a FUNCTION equality does not reach inside
`∫⁺x. ennreal (...)`, because the lambda there is `λx. ennreal (…)`, not the
function being rewritten — convert pointwise with `nn_integral_cong` instead.

**Candidate derivative DONE (2026-07-30):** `bounded_linear_coord_combination`
— `v ↦ Σ b∈Basis. (v∙b) · c b` is bounded linear for ANY coefficients `c`
(bound `Σ|c b|` via `Basis_le_norm` and `sum_abs`). Instantiating `c b` with
`ddir f b x` gives the candidate derivative at a good point `x`; the work left
is showing it agrees with `ddir` on a dense set of directions.

**RADEMACHER now needs only the final assembly**: pick a countable dense set
`D` of directions (e.g. rational combinations of `Basis`), intersect the
co-negligible sets from `negligible_no_dderiv_countable` with the countably
many a.e. additivity statements from `ddir_add_AE` and homogeneity from
`ddir_scale`, so that a.e. `x` has `v ↦ D_v f x` linear on `D`; then
`differentiable_of_dense_linear_ddir` gives differentiability at such `x`.

**Direction set DONE (2026-07-30):** `rat_dirs` (rational combinations of
`Basis`), with `countable_rat_dirs` (`countable_PiE` + `countable_image` +
`countable_rat`) and `rat_dirs_dense` (`∀v ∀e>0 ∃w∈rat_dirs. ‖v − w‖ < e`,
via `norm_le_l1`, `Rats_dense_in_real` per coordinate, `sum_strict_mono`, and
`inner_sum_scaleR_Basis` to read off the coordinates). TRAP: `bchoice` inside
an `obtain` must be applied as `using bchoice[OF fact] by blast` — `by (rule
bchoice)` fails because the obtain goal is already in eliminated form.

**A.E. AGGREGATION DONE (2026-07-30):** `AE_all_rat_dirs` (a.e. `x` has
directional derivatives along EVERY nonzero rational direction),
`AE_add_rat_dirs` (a.e. `x` satisfies additivity for every pair of them with
nonzero sum) and `AE_scale_rat_dirs` (a.e. `x` satisfies homogeneity for every
nonzero rational scalar) — each by `AE_ball_countable` over the countable
index set (`countable_SIGMA` for the pairs). TRAP: `AE_ball_countable` is an
IFF; `simp`/chaining will not fire it (higher-order `P`), so use
`unfolding AE_ball_countable[OF countable] by (rule …)`.

**INDUCTION PREREQUISITES DONE (2026-07-30):** `inner_sum_scaleR_subset`
(a PARTIAL basis combination `Σ_{b∈S} c b *R b` with `S ⊆ Basis` has
coordinate `c j` at `j ∈ S`) and `coeffs_zero_of_sum_zero` (such a
combination vanishes only if every coefficient does). The second is exactly
what keeps the partial sums of the final induction nonzero once zero
coefficients are skipped — necessary because `ddir` additivity is available
only for nonzero directions.

**MEMBERSHIP FACTS DONE (2026-07-30):** `partial_rat_dir_mem` (every partial
sum `Σ_{b∈S} c b *R b`, `S ⊆ Basis`, is itself a rational direction — extend
the coefficients by zero, `sum.mono_neutral_cong_right`) and
`Basis_subset_rat_dirs` (`Basis ⊆ rat_dirs`). TRAPS: the unanchored-`define`
type-variable trap struck again (annotate the `0`/`1` in the coefficient
function as `::real`); and `force` on the `rat_dirs` image membership FLAGGED
still-running — replace with `image_eqI[OF _ mem]` plus the explicit equation.

# RADEMACHER'S THEOREM IS PROVED (2026-07-30)

**`rademacher_AE`**: a Lipschitz `f :: 'a::euclidean_space ⇒ real` is
differentiable at almost every point. This closes E3c, the item recorded at
the start of this project as the long pole of Phase E (neither Rademacher nor
Alexandrov exists anywhere in Isabelle/AFP — both greps came back empty).
Assembly: intersect the three a.e. conditions; at a good point the candidate
derivative is `T = (λv. Σ b∈Basis. (v∙b)·ddir f b x)`, bounded linear by
`bounded_linear_coord_combination`; `ddir_rat_dir_sum` (with `S = Basis`, the
coefficients read off by `inner_sum_scaleR_Basis`) shows `ddir f w x = T w`
for every rational direction, the `w = 0` case being immediate since
`dquot f 0 x t = 0`; `differentiable_of_dense_linear_ddir` with
`rat_dirs_dense` then gives `(f has_derivative T) (at x)`. Note the Lipschitz
constant is passed as `|B|` so the lemma's `0 ≤ B` side condition is free.

## E3d ALEXANDROV — **COMPLETE** (2026-07-30); see the headline block for the finished statements and the transport chain

Proved so far, all in `Sup_Convolution.thy`, green + batch-built:
- `lipschitz_component`, **`rademacher_vec_AE`** — Rademacher for VECTOR-valued
  Lipschitz maps (componentwise, reassembled by `euclidean_representation`);
  this is what lets Rademacher be applied to the resolvent, which maps
  `R^n → R^n`.
- `prox_lipschitz`, **`prox_differentiable_AE`** — the resolvent of a finite
  convex function is differentiable a.e. (Minty's device: `prox_nonexpansive`
  makes it 1-Lipschitz on ALL of the space).
- **`prox_firm_nonexpansive`** — `|R x − R y|² ≤ (x − y)·(R x − R y)`, i.e. the
  resolvent is FIRMLY nonexpansive, straight from `subdiff_monotone` through
  `prox_subdiff`. Strictly stronger than the 1-Lipschitz bound.
- `has_derivative_dir_limit` — a Fréchet derivative gives the directional
  difference-quotient limit (needed to differentiate along lines).
- **`prox_deriv_psd`** — wherever the resolvent is differentiable,
  `|DR h|² ≤ h · DR h`. So `DR` is positive semidefinite AND `‖DR‖ ≤ 1`
  (equivalently `I − DR` is psd). This is the matrix inequality that carries
  Alexandrov's theorem.

- `moreau` (the Moreau envelope `min_y (f y + |x−y|²/2)`), `moreau_le`,
  `moreau_upper`, `moreau_lower` and **`moreau_has_derivative`** — the envelope
  is differentiable EVERYWHERE with gradient `x − prox f x`, and the error is
  QUADRATIC (`≤ (5/2)|h|²`), so the envelope is C^1 with a 1-Lipschitz
  gradient. Both inequalities come from testing each minimum against the other
  point's minimiser; the lower one needs `prox_lipschitz` to control
  `prox f x − prox f (x+h)`. CONSEQUENCE: `prox f = id − ∇(moreau f)`, i.e.
  the resolvent is the identity minus a GRADIENT FIELD — the standard route to
  symmetry of `DR`, and hence to a symmetric Hessian in Alexandrov.

- `prox_deriv_norm_le` (`‖DR h‖ ≤ ‖h‖`, from the psd inequality plus
  Cauchy–Schwarz), `moreau_hessian_psd` (`0 ≤ h·(h − DR h)`),
  `moreau_grad_has_derivative`, and **`moreau_twice_differentiable_AE`** — the
  MOREAU ENVELOPE of a finite convex function is twice differentiable almost
  everywhere with positive semidefinite Hessian `I − DR`. This is the first
  second-order result of the development and an Alexandrov-type theorem in its
  own right (for the C^1,1 envelope rather than for `f` itself).

- `moreau_line_vector_derivative` and **`moreau_ftc`** — the increment of the
  envelope along a segment is the INTEGRAL of its gradient:
  `(λs. h·((x + s·h) − prox f (x + s·h))) has_integral (e(x+h) − e(x))` on
  `{0..1}`, by `diff_chain_within` + the ordinary
  `fundamental_theorem_of_calculus` (no Lipschitz hypothesis needed, since the
  gradient is known everywhere). Feeding the FIRST-order expansion of the
  gradient at a point of twice-differentiability into this integral is what
  produces the quadratic term of the Taylor expansion — that is the next step.

- `has_integral_affine_unit` (`∫₀¹ (c + s·d) ds = c + d/2`, by FTC on
  `c·s + d·s²/2`) and **`has_integral_gradient_model`**
  (`∫₀¹ h·(g + A(s·h)) ds = h·g + (h·A h)/2` for bounded linear `A`) — the
  QUADRATIC TERM. Combining this with `moreau_ftc` reduces the second-order
  Taylor expansion to the error estimate
  `|∫₀¹ h·(G(x+s·h) − G x − A(s·h)) ds| ≤ ε|h|²`, which follows from
  differentiability of `G` at `x` and `has_integral_bound`.

- **`moreau_second_order_taylor`** — THE SECOND-ORDER TAYLOR EXPANSION of the
  envelope: wherever the resolvent is differentiable with derivative `D`,
  `e(x+h) = e(x) + h·(x − prox f x) + (h·(h − D h))/2 + o(‖h‖²)`. Proof:
  `moreau_ftc` writes the increment as an integral, `has_integral_gradient_model`
  writes the model quadratic as an integral, `has_integral_diff` subtracts them,
  and the integrand is `≤ ε‖h‖²` uniformly on the segment (Cauchy–Schwarz plus
  differentiability of the gradient at `x`, using `‖s·h‖ ≤ ‖h‖`), so
  `has_integral_bound` over a unit interval preserves the bound. TRAP: take the
  δ for ε/2, not ε, or the final step yields `≤ ε` where `< ε` is required; and
  keep the quotient `E/‖h‖²` as ONE atom (simp's `E*2/‖h‖²` normalisation
  defeats linarith), so finish with a `dist ... = |...| ≤ e2 < ε` calculation.

Combined with `prox_differentiable_AE` this gives: the Moreau envelope of a
finite convex function admits an a.e. second-order Taylor expansion with psd
quadratic form — Alexandrov's theorem for the C^1,1 envelope.

- **`moreau_alexandrov_AE`** — headline: a.e. second-order Taylor expansion of
  the envelope with psd quadratic form. Alexandrov's theorem for the C^1,1
  envelope, assembled from all of the above.
- `second_difference_symmetric` and **`moreau_second_difference_integral`** —
  the second difference `Δ(u,v) = e(x+u+v) − e(x+u) − e(x+v) + e(x)` is
  symmetric for trivial reasons, and equals a difference of two gradient
  integrals along PARALLEL segments (two applications of `moreau_ftc` plus
  `integral_unique`). Inserting the gradient's first-order expansion into
  those integrals and comparing with the trivial symmetry is what will force
  `u·A v = v·A u`, i.e. SYMMETRY OF THE HESSIAN. That estimate is the same
  shape as the one already done in `moreau_second_order_taylor`.

REMAINING for Alexandrov (for `f` itself): transport the a.e. statement along the surjection
from `minty_surjective`, and convert `DR` into the second-order expansion of
`f` at `prox f x` using `prox_subdiff` (`x − prox f x ∈ subdiff f (prox f x)`)
— the Hessian being `(I − DR) DR^{-1}` on the range of `DR`.

**Route recap: E3d Alexandrov.** Apply `rademacher_AE` componentwise to the resolvent
`prox f` (1-Lipschitz on ALL of R^n by `prox_nonexpansive`), then use
`minimizer_subdiff`/`prox_subdiff` to convert a.e. differentiability of the
resolvent into a second-order expansion of the convex `f`. Then E4 Jensen
(`m_diff_image_weak` in Change_Of_Vars is the area bound), E5 theorem on sums
(feeds on `supconv_semiconvex`, `supconv_near_optimizer`, `supconv_tendsto`),
E6 `max_principle_boundary` via `max_principle_boundary_intro`.

**BASIS INDUCTION DONE (2026-07-30):** **`ddir_rat_dir_sum`** — at a point
where the three a.e. conditions hold, `ddir f (Σ_{b∈S} c b *R b) x
= Σ_{b∈S} c b · ddir f b x` for every `S ⊆ Basis` with nonzero partial sum.
`finite_induct` with the subset hypothesis carried; three cases per step
(`c b0 = 0` → drop the term; partial sum zero → all its coefficients vanish by
`coeffs_zero_of_sum_zero`, so only homogeneity is needed; otherwise → pairwise
additivity via `gadd`, with membership from `partial_rat_dir_mem` and
`Basis_subset_rat_dirs`).

REMAINING FOR RADEMACHER: at an a.e. point, `ddir f w x = T w` for `w ∈
rat_dirs` where `T = (λv. Σ b∈Basis. (v∙b) · ddir f b x)` is bounded linear by
`bounded_linear_coord_combination` — read the coefficients of `w` off with
`inner_sum_scaleR_Basis` so that `ddir_rat_dir_sum` (with `S = Basis`) matches
`T w`; then `differentiable_of_dense_linear_ddir` with `rat_dirs_dense`.

CONCRETE RECIPE for the rest of the assembly (all inputs proved):
- a.e. `x` lies in `⋂_{w∈D} dlim_set f w` (`negligible_no_dderiv_countable`),
  satisfies `ddir_add_AE` for all pairs in the countable set `D × D` with
  nonzero sum, and `ddir_scale` for the countably many rational scalars —
  intersect with `AE_ball_countable`.
- at such `x`, induct over `Basis` (order it, skip zero coefficients so every
  partial sum stays nonzero — basis independence guarantees this) to get
  `ddir f w x = Σ b∈Basis. (w∙b) · ddir f b x` for `w ∈ D`, i.e. `ddir` agrees
  on `D` with the bounded linear map of
  `bounded_linear_coord_combination`.
- conclude by `differentiable_of_dense_linear_ddir`; the exceptional set is
  Borel-measurable and negligible, giving Rademacher's theorem.

OLD PLAN TEXT (superseded): convert to the ennreal
form of `AE_zero_of_box_integrals_zero` (via `real_lebesgue_integral_def`,
both parts finite); then a.e. additivity + `ddir_scale` +
`negligible_no_dderiv_countable` + `differentiable_of_dense_linear_ddir`
gives Rademacher. OLD PLAN TEXT BELOW (superseded where it repeats the above):
let `t → 0` in
`box_integral_add_split` along `t = 1/(n+1)`. Two of the three limits are
already `box_integral_dquot_tendsto`; the third has a MOVING box
`B + t·u`, handled by splitting
`|∫ q_n 1_{B_n} − ∫ D_v f 1_B| ≤ ∫ |q_n − D_v f| 1_{B'} + M·measure (B_n Δ B)`
over a fixed enclosing box `B'` (first term → 0 by the same DCT applied to
`|q_n − D_v f|`, second by `content_box_int_translate_tendsto`). Then
`AE_zero_of_box_integrals_zero` converts the resulting box identity into a.e.
additivity, and `differentiable_of_dense_linear_ddir` finishes Rademacher.

SIMPLER ROUTE FOUND — L¹-continuity of translation is NOT needed:
1. Integrate `dquot_add_split` over a box `B`. The shifted term becomes
   `∫_B dquot f v (x + t*R u) t dx = ∫_{B + t*R u} dquot f v y t dy` by
   translation invariance — the tool is **`lborel_distr_plus`**
   (`distr lborel borel ((+) c) = lborel`, general euclidean space, in
   `Lebesgue_Measure`) combined with `integral_distr`. Dominating function and
   measurability for the DCT are `norm_dquot_le` and `borel_measurable_dquot`
   (both DONE 2026-07-30).
2. Split the error: `|∫_{B+w} q_t − ∫_B D_v f|` ≤
   `∫_{B'} |q_t − D_v f|` (over a FIXED slightly larger box `B' ⊇ B + w` for
   small `w`, → 0 by dominated convergence with the `norm_ddir_le` bound and
   a.e. pointwise convergence) + `M · measure (B Δ (B+w))` (→ 0 because
   `Int_interval` makes `B ∩ (B+w)` a box whose `emeasure_lborel_cbox_eq`
   product formula is continuous in `w`). No density/mollifier argument.
3. That gives `∫_B D_{u+v} f = ∫_B D_u f + ∫_B D_v f` for EVERY box `B`.
4. Upgrade to a.e. equality: the two finite measures `A ↦ ∫_A g⁺`,
   `A ↦ ∫_A g⁻` (restricted to a big box) agree on the ∩-stable generator of
   boxes, so `measure_eqI_generator_eq` makes them agree on all Borel sets;
   testing on `{g > 0}` and `{g < 0}` forces `g = 0` a.e.; exhaust by an
   increasing sequence of boxes.
`absolutely_integrable_approximate_continuous` (continuous bounded L¹
approximants — the mollifier substitute) is kept in reserve in case step 2's
dominated-convergence form needs it.
Combined with `ddir_scale` this gives linearity of `v ↦ D_v f x` a.e. on a
countable dense set of directions, and `differentiable_of_dense_linear_ddir`
then delivers **Rademacher**. After that: E3d Alexandrov via the resolvent
(`prox_nonexpansive` is 1-Lipschitz on all of R^n, so Rademacher applies to
it), then E4 Jensen (`m_diff_image_weak` is the area bound), E5 theorem on
sums, E6 `max_principle_boundary`.

**Why E6 cannot be short-circuited (checked 2026-07-30).**
`max_principle_boundary k L K` asks that `u − w` attain its max over `K` on
`K − interior K` for ANY viscosity sub/supersolution pair. The equation
`ell_op k L (∇u) (D²u) = 1` has NO zeroth-order term, so there is no
strict-monotonicity trick; and `u`, `w` are both merely semicontinuous, so
neither can serve as the other's test function. That is precisely the
configuration the Crandall–Ishii lemma exists to resolve — the ball case
escaped it only because the barrier `ball_v` is SMOOTH. So the sup-convolution
/ Jensen / theorem-on-sums route is required, as originally planned.
- R3 (linearity `D_v f = v ∙ ∇f` a.e.) WITHOUT mollifiers/test functions
  (none exist in HOL-Analysis): show `∫_B D_v f = ∫_B v ∙ ∇f` for every
  box B, by (i) `∫_B ∂_i f` via 1D FTC along lines (FTC for absolutely
  continuous functions EXISTS: `fundamental_theorem_of_calculus_absolutely_continuous`)
  + Fubini slicing, (ii) `∫_B (f(x+tv) − f x)/t dx = (∫_{B+tv} f − ∫_B f)/t`
  by translation invariance, whose t → 0 limit is a boundary flux =
  `Σ v_i ∫_B ∂_i f` (DCT with the Lipschitz bound dominating quotients).
  Then "equal integrals over all boxes ⟹ equal a.e." by pure measure
  theory (boxes are an ∩-stable generator; `measure_eqI_generator_eq` /
  Dynkin on the positive and negative parts) — NO Lebesgue density theorem
  needed.
- R4 (totality): at a.e. x, D_v f(x) = v∙∇f(x) holds simultaneously for a
  countable dense set of directions v; the Lipschitz bound makes
  v ↦ (f(x+tv)−f x)/t uniformly Lipschitz in v, so the o(t) estimate
  extends to all v uniformly ⟹ differentiability. (Evans–Gariepy §3.1.)
- E3d Alexandrov via Minty: `prox_nonexpansive` + Rademacher differentiate
  the resolvent a.e.; where `DR` exists (+ symmetric psd structure from
  monotonicity, invertibility on the relevant a.e. set via
  `inverse_function_theorem`-free arguments on `R = (id + ∂f)^{-1}`), the
  gradient `∇f = (id − R)∘R^{-1}`-type identities yield second-order
  expansion of f at a.e. point.

Then E4 (Jensen's lemma: smooth case via `m_diff_image_weak` + passage to
Alexandrov points), E5 (theorem on sums), E6 (Thm 4.2(a) via
`max_principle_boundary_intro`).

Discharge `locale comparison_principle`: sup-convolutions, semiconvexity,
Alexandrov's theorem (a.e. twice differentiability), Jensen's lemma, the
theorem on sums, then Thm 4.2(a) via `max_principle_boundary_intro`.
NOTHING usable exists in the distribution or AFP (no viscosity solutions, no
Alexandrov, no Rademacher). An independent development, plausibly larger than
the whole eigenvalue chain. Only needed for `K` beyond the ball; Sections
4.2(b)/4.3/4.1 already follow from the interface (`Lemma_3_1_Envelopes.thy`).

## E4 JENSEN'S LEMMA — **PROVED** (2026-07-30)

```isabelle
theorem jensen_lemma:
  assumes cvx: "convex_on UNIV (%z. phi z + (c/2) * (norm z)^2)"
    and c: "0 < c" and rho: "0 < rho" "rho < r"
    and bnd: "!!y. y : cball xi r ==> rho <= dist y xi ==> phi y <= m"
    and d: "0 < d" and small: "2 * d * r < phi xi - m"
  shows "~ negligible {x : cball xi r. EX p. norm p <= d
      & (ALL y : cball xi r. phi y + p . y <= phi x + p . x)}"
```

**The determinant requirement was eliminated.** The textbook proof bounds
`measure (K d)` from below by a Jacobian determinant, which needs Hadamard's
inequality or a spectral theorem. The AFP does have `Hadamard's_inequality`
(`LLL_Basis_Reduction/Gram_Schmidt_2.thy`) but only for `real mat` in the
Jordan_Normal_Form framework, its session is not prebuilt here, and bridging
JNF matrices to `eucl.det` on an abstract `euclidean_space` would need an
HMA-style connection that does not exist for abstract Euclidean spaces (the
Perron_Frobenius one targets `real^'n`). None of that is needed: only
POSITIVITY of the measure is ever used downstream, and positivity follows with
no determinants at all.

The chain, all in `Sup_Convolution.thy`:

- `perturbed_maximiser_interior`, `perturbed_maximiser_deep_interior` —
  bounding `phi` on the whole ANNULUS `rho <= dist y xi <= r` (not just the
  sphere) puts every maximiser inside `ball xi rho`, so all maximisers keep a
  COMMON margin `r - rho` from the boundary. That uniform margin is what makes
  the co-coercivity argument localisable.
- `interior_max_subdiff_unique` / `interior_max_subdiff` — at an interior
  maximiser the subdifferential of `psi = phi + (c/2)*(norm -)^2` is the
  SINGLETON `{c *R x - p}`, with no differentiability hypothesis. Hence
  `psi` is differentiable at every point of `K`, and `P x = c *R x - grad psi x`
  is a genuine FUNCTION on `K` mapping it ONTO `cball 0 d`. This is what
  removes the covering gap the textbook glosses over.
- `max_semiconcave_bound` — the reverse inequality with the same vector, so on
  `K` the Bregman divergence of `psi` is pinned between `0` and
  `(c/2)*norm(z-x)^2`.
- `le_of_le_plus_small` — the `t -> 0+` helper (`tendsto_lowerbound` on
  `at_right 0`).
- `bregman_cocoercive_step` — co-coercivity for ANY step `s` with `s*c <= 1`,
  not just the optimal `s = 1/c`. Allowing a smaller `s` is exactly what keeps
  the test point `x - s *R (q - q')` inside the ball.
- `subdiff_lipschitz_of_semiconcave` — the localised REVERSE BAILLON-HADDAD
  implication: adding the two co-coercivity estimates collapses the Bregman
  divergences into `(q - q') . (x - x')`, and Cauchy-Schwarz gives
  `s * norm (q - q') <= norm (x - x')`.
- `semiconvex_continuous`, `semiconvex_max_exists`, `not_negligible_cball` —
  set-up.
- `jensen_lemma` — assembles: `P` is Lipschitz on `K` with constant
  `c + 1/s` for an explicit `s = min (1/c) ((r-rho)/(2*Qb+1))`, and
  `cball 0 d <= P ` K`. A negligible `K` would give a negligible image by
  `negligible_locally_Lipschitz_image`, but the image contains a ball.

NEXT (task #9): E5 the Crandall-Ishii theorem on sums (consumes
`supconv_semiconvex`, `supconv_near_optimizer`, `supconv_tendsto`,
`semiconvex_alexandrov` and now `jensen_lemma`), then E6
`max_principle_boundary`. The probabilistic line (Phases A4-G, tasks #4-#7)
is independent of all of this and untouched.

## E5 THEOREM ON SUMS — started (2026-07-30)

### Already available (do not redo)

- **Degenerate ellipticity is DONE and in the exact form Section 4 needs**:
  `ell_op_elliptic` and `ell_op_elliptic_le` in `Lemma_3_1_Envelopes.thy`
  (`M \<preceq> N ==> ell_op k L p N <= ell_op k L p M`), resting on
  `ell_op_pointwise_elliptic` in `Relative_Arbitrage_PDE.thy`. This is the
  final step of the comparison contradiction, so E5 only has to deliver the
  two jets and the matrix inequality `X \<preceq> Y`.
- Sup-convolution calculus (`supconv_semiconvex`, `supconv_continuous`,
  `supconv_near_optimizer`, `supconv_tendsto`), `semiconvex_alexandrov`,
  `jensen_lemma` — all proved, in `Sup_Convolution.thy`.

### Proved this session (doubling of variables)

The quantitative core of Crandall-Ishii-Lions Lemma 3.1, in purely algebraic
form (no semicontinuity, no compactness, only the two maximality statements) —
`Sup_Convolution.thy`:

- `doubling_ge_diagonal` — testing the doubled functional on the diagonal:
  `u x - w x <= Ma` for every `x` in `K`.
- `doubling_ring_identity` — the ring step, isolated because `algebra_simps`
  will not clear the `/2`s (use `field_simps`).
- `doubling_penalty_squeeze` — testing `Phi_beta` at the maximiser OF
  `Phi_alpha` gives
  `((alpha - beta)/2) * norm (xa - ya)^2 <= Mb - Ma`.
- `doubling_antitone` — hence `Ma <= Mb` for `beta <= alpha`.

Together: `M_alpha` is nonincreasing and bounded below by
`sup (u - w)`, so it converges, and the squeeze then forces
`alpha * norm (x_alpha - y_alpha)^2 -> 0`. That is what drives the two
maximisers together.

### Also proved: the limit half of Lemma 3.1

- `antitone_bdd_below_convergent_at_top` — an antitone function bounded below
  on `[1,\<infinity>)` converges along `at_top` (to `Inf` of its range). Its two
  hypotheses are exactly what `doubling_antitone` and `doubling_ge_diagonal`
  supply, so `M_alpha` converges.
- `doubling_penalty_tendsto_zero` — given that convergence, applying the
  squeeze with `beta = alpha/2` traps `(alpha/4) * pen alpha` between `0` and
  `M(alpha/2) - M alpha`, both of which go to `0`. Hence
  `alpha * norm (x_alpha - y_alpha)^2 -> 0`: the PENALTY vanishes, not merely
  the distance. That is what lets the two maximisers be treated as one point
  in the limit.

### Also proved: composition and the Crandall-Ishii engine

- `supconv_semiconvex'` — restates `supconv_semiconvex` in the `(c/2)*(norm x)^2`
  form (with `c = 1/eps`) that `jensen_lemma` and `semiconvex_alexandrov`
  consume. Without this the three theorems do not compose.
- `supconv_alexandrov` — the sup-convolution of ANY bounded-above function is
  twice differentiable a.e.
- `supconv_jensen` — Jensen's lemma applies to the sup-convolution verbatim.
- **`supconv_jensen_alexandrov_point`** — THE ENGINE. Jensen gives a
  non-negligible set of perturbed maximisers, Alexandrov a full-measure set of
  twice-differentiable points; a non-negligible set cannot sit inside a
  negligible one, so the two MEET. There is a single point that is
  simultaneously a maximiser of a small linear perturbation AND a point of
  genuine second-order expansion.
- **`second_order_interior_max`** — at an interior maximiser carrying a
  second-order expansion with data `(q, X)`, one gets `q . v = 0` and
  `v . X v <= 0` for every `v`. Both come from the same limit
  `R (t *R w) / t^2 -> 0` along `at_right 0`: divide the maximality inequality
  by `t` for the first, by `t^2` for the second. This upgrades the Alexandrov
  expansion at the Jensen point into a genuine second-order JET with a
  negative semidefinite matrix.

### What remains for E5

1. **The compactness half of Lemma 3.1** — that some subsequence of
   `x_alpha` converges and its limit maximises `u - w`. Needs usc/lsc plus
   compactness of `K` (the project already has usc machinery in
   `Value_Function.thy`); the quantitative work is now all done.
2. **The theorem on sums itself**, in the special case the comparison
   principle needs (k = 2, `phi (x,y) = (alpha/2) * norm (x-y)^2`): from a
   local max of `u x - w y - phi` at `(xh,yh)` produce symmetric `X`, `Y` with
   `(alpha *R (xh - yh), X)` a second-order superjet of `u` at `xh`,
   `(alpha *R (xh - yh), Y)` a second-order subjet of `w` at `yh`, and
   `X \<preceq> Y`. The route is now stocked end to end: apply
   `supconv_jensen_alexandrov_point` to the DOUBLED function on `'a \<times> 'a`
   (a Euclidean space, so all of the above applies unchanged), read off the
   jet with `second_order_interior_max`, and pass to the limit with
   `supconv_tendsto`.

   The BLOCK STRUCTURE is now PROVED (`Sup_Convolution.thy`):
   - `block_diagonal_test` — testing the product-form negativity on the
     DIAGONAL (`w = v`) makes the penalty term vanish and leaves exactly
     `v . X v <= v . Y v`, the matrix inequality of the theorem on sums.
   - `expansion_restrict_fst` / `expansion_restrict_snd` — a second-order
     expansion on `'a * 'b` restricts to each slice, with gradient `fst q` /
     `snd q` and matrix `h |-> fst (Z (h,0))` / `h |-> snd (Z (0,h))`. This is
     what lets the single product Hessian be read as two separate matrices on
     the factors. Supporting: `norm_Pair_right_zero`, `norm_Pair_left_zero`;
     the embeddings `h |-> (h,0)`, `h |-> (0,h)` are `filterlim ... (at 0) (at 0)`
     via `filterlim_atI`.

   The SEMICONVEXITY CALCULUS for the product is now proved too, without which
   none of the machinery can even be pointed at the doubled functional:
   - `convex_on_norm_sq` — `(norm -)^2` is convex on any convex set (via the
     identity `(1-t)|x|^2 + t|y|^2 - |(1-t)x+ty|^2 = t(1-t)|x-y|^2`).
   - `semiconvex_add` — semiconvexity adds, with the constants adding.
   - `convex_on_fst` / `convex_on_snd` — convexity survives composition with the
     projections, so a semiconvex function of one factor is semiconvex on the
     product.

   And the DOUBLED FUNCTIONAL IS NOW KNOWN SEMICONVEX
   (`doubled_functional_semiconvex`), with constant `1/eps + 1/eps + 2*alpha`:

   ```isabelle
   theorem doubled_functional_semiconvex:
     assumes "!!y. u y <= Bu" "!!y. v y <= Bv" "0 < eps" "0 <= alpha"
     shows "convex_on UNIV (%z::'a*'a.
         (supconv u eps (fst z) + supconv v eps (snd z)
           - (alpha/2) * (norm (fst z - snd z))^2)
         + ((1/eps + 1/eps + 2*alpha)/2) * (norm z)^2)"
   ```

   Supporting: `convex_on_scaleR_nonneg`, `convex_on_proj_sum`, `norm_prod_sq`,
   `semiconvex_penalty` (the penalty is semiconvex with constant `2*alpha`),
   `semiconvex_of_fst`, `semiconvex_of_snd`. This is the hypothesis EVERY one of
   Rademacher, Alexandrov, Jensen and `supconv_jensen_alexandrov_point` needs
   before it can be pointed at the doubling of variables.

   Two further pieces are now proved:
   - `semiconvex_jensen_alexandrov_point` — the engine restated for an ARBITRARY
     semiconvex function (the sup-convolution version only ever used
     semiconvexity, and the doubled functional is semiconvex without being a
     sup-convolution), strengthened with the interiority `dist x xi < rho` that
     `second_order_interior_max` needs.
   - `second_order_form_unique` — the quadratic form in a second-order expansion
     is UNIQUE (restricting to a ray makes the difference quotient constant in
     `t`, and a constant tending to 0 is 0).

   **`second_order_form_unique` removes the need for the `A + eps*A^2` matrix
   argument of the textbook proof.** For a function of the form
   `a (fst z) + b (snd z)` the two slice expansions
   (`expansion_restrict_fst`/`_snd`) reassemble into a block-DIAGONAL quadratic
   form; by uniqueness the product form must EQUAL it, so the off-diagonal
   blocks vanish EXACTLY rather than only after an eps-perturbation. Testing the
   resulting negativity on the diagonal `(v,v)`, where the penalty contributes
   nothing, then gives `X <= Y` via `block_diagonal_test`. This matters because
   the `A + eps*A^2` route needs matrix inverses and the psd order, i.e. exactly
   the spectral machinery this HOL-Analysis lacks (same gap as Hadamard).

   And BLOCK DIAGONALITY IS NOW PROVED:
   - `expansion_ray_limit` — along a fixed direction the second-order expansion
     says exactly `F (t *R w) / t^2 -> (w . Q w)/2` on `at_right 0`. Stated with
     only the SCALING hypothesis `Q (s *R u) = s *R Q u` (all the proof uses),
     so the slice matrices can be fed to it with no bounded-linear plumbing.
   - `product_form_block_diagonal` — for `a (fst z) + b (snd z)`,
     `(h,g) . W (h,g) = h . fst (W (h,0)) + g . snd (W (0,g))`: the off-diagonal
     blocks vanish IDENTICALLY. Proof: along the ray `t *R (h,g)` the difference
     quotient of the product splits as the sum of the two slice quotients
     (`add_divide_distrib` on the numerator identity), and the three ray limits
     plus `tendsto_unique` force the identity.

   The PENALTY's exact expansion is proved too:
   - `penalty_exact` — the penalty is a quadratic, so its second-order expansion
     has NO remainder: gradient `alpha *R (Dz, -Dz)` at `zh` and quadratic form
     `k |-> alpha * norm (fst k - snd k)^2`, written as honest vectors and maps
     on the product so they can be ADDED to the expansion of `Psi` to recover
     the expansion of `Psi + pen`, which is the separated form
     `a (fst z) + b (snd z)` that `product_form_block_diagonal` requires.
   - `penalty_form_scaleR` — that quadratic form scales, so it can be fed to
     `expansion_ray_limit` (which needs only scaling).
   - `penalty_form_diagonal` — it VANISHES on the diagonal `(v,v)`. This is
     precisely why testing there kills the penalty and leaves only `X <= Y`.

   **THE THEOREM ON SUMS (matrix inequality) IS PROVED**:
   `sums_matrix_inequality`. Given a second-order expansion of the doubled
   functional `a (fst z) + b (snd z) - (alpha/2)*norm (fst z - snd z)^2` at `zh`
   with a NEGATIVE SEMIDEFINITE form `W` (which an interior maximum supplies via
   `second_order_interior_max`), adding `penalty_exact` turns the form into
   `WP = W + P` and the functional into the SEPARATED form
   `a (fst z) + b (snd z)`; `product_form_block_diagonal` splits `WP` into its
   two slice matrices; and testing on the diagonal `(v,v)` — where the penalty
   contributes nothing, `penalty_form_diagonal` — leaves exactly

   ```
   v . fst (W (v,0) + alpha *R (v-0, 0-v)) + v . snd (W (0,v) + alpha *R (0-v, v-0)) <= 0
   ```

   With `b = -w` the second slice matrix is `-Y`, so this reads `X <= Y`, which
   is what the comparison principle feeds to `ell_op_elliptic_le`.

   (`product_form_block_diagonal` was weakened to need only the SCALING property
   `W (s *R u) = s *R W u` rather than `linear W`, so the combined map `W + P`
   can be fed to it directly from `scW` + `penalty_form_scaleR`.)

   **LEMMA 3.1 IS NOW COMPLETE.** `doubling_limit_maximises`: if `M -> L`,
   `M n <= u (X n) - w (Y n)`, `S <= M n`, and the two semicontinuity
   `eventually` statements hold along `X`, `Y` towards `xh`, then
   `S <= u xh - w xh`. So the common limit point of the two maximisers MAXIMISES
   `u - w`. Usc/lsc enter only through those two `eventually` statements, so no
   semicontinuity predicate is fixed here and a caller with any formulation
   (e.g. the one in `Value_Function.thy`) can supply them. Together with
   `doubling_ge_diagonal` this pins `lim M_alpha = S`.

   **THE eps-PASSAGE IS PROVED, and it needs no limit at all.** The
   sup-convolution's MAGIC PROPERTY does it in one step:
   - `supconv_dominates_shift` — if the sup defining `supconv u eps x` is
     ATTAINED at `ys`, then shifting BOTH arguments by the same `k` leaves the
     penalty unchanged, so
     `u (ys+k) - u ys <= supconv u eps (x+k) - supconv u eps x`.
   - `supconv_jet_transfer` — in quotient form: the difference quotient for `u`
     at `ys` is dominated by the one for `supconv u eps` at `x`, which tends to
     `0`. So `(p, X)` is a second-order SUPERJET of `u` at `ys`.

   The jet therefore moves from the regularisation back to `u` itself with NO
   loss and with no eps-limit or compactness extraction, which is a genuine
   simplification over the textbook route (there one passes eps to 0 and
   extracts convergent subsequences of the matrices).
3. **Assembly into `max_principle_boundary`** (E6). STARTED: the first bridge is
   proved. The project's viscosity notions (`test_fun_at`, `visc_subsol`,
   `visc_supersol` in `Relative_Arbitrage_PDE.thy`) speak of a MATRIX `H` acting
   by `H *v h` and require `transpose H = H`, whereas everything in
   `Sup_Convolution.thy` produces a bounded linear `X` with the ABSTRACT
   symmetry `v . X w = w . X v`. `matrix_vec_apply` and `matrix_of_symmetric`
   bridge the two: HOL-Analysis's `matrix` represents `X` faithfully
   (`matrix_works`, via `linear_matrix_vector_mul_eq` which converts between
   `Vector_Spaces.linear (*s) (*s)` and the real-vector-space `linear` -- these
   are DIFFERENT predicates and `matrix_works` wants the former), and the
   abstract symmetry is exactly matrix symmetry because
   `v . (transpose A *v w) = w . (A *v v)` (`dot_lmul_matrix` +
   `transpose_matrix_vector`).

   The TEST-FUNCTION CONSTRUCTION is proved too. For a jet `(p, H)` at `x` put
   `phi z = p . (z - x) + ((z - x) . (H *v (z - x)))/2` and
   `g z = p + H *v (z - x)`; then
   - `quadratic_test_derivative` — `phi` has derivative `(%h. g y . h)` at every
     `y` (chain rule through the shift, then `has_derivative_quadratic_form`);
   - `quadratic_test_grad_derivative` — `g` has derivative `(%h. H *v h)` at `x`.
   These are exactly the two non-symmetry conjuncts of `test_fun_at phi g H x`;
   the symmetry conjunct is `matrix_of_symmetric`. They are stated in raw form
   because `test_fun_at` lives in `Relative_Arbitrage_PDE.thy`, which
   `Sup_Convolution.thy` deliberately does not import (that would create a
   PIDE-unloadable diamond over draft theories); the packaging into
   `test_fun_at` belongs in a downstream theory.

   **A NEW THEORY `Comparison_Assembly.thy` NOW EXISTS** (added to ROOT, batch
   build green; verified genuinely checked by a deliberate-error test, since a
   silently-skipped theory would be worthless). It imports BOTH
   `Sup_Convolution` and `Lemma_3_1_Envelopes`, which is where the two sides
   meet: `Sup_Convolution.thy` sits directly on `HOL-Analysis.Analysis` so PIDE
   can hold it, and therefore states everything in raw analytic form; this new
   theory packages that into the project's predicates. (CORRECTION 2026-07-31:
   the claim below that it is batch-only is WRONG - see the note at the end of
   this file. PIDE holds it fine.) Note it is batch-only
   (two project chains), so verify it with `isabelle build`, not PIDE.

   Proved there:
   - `jet_test_fun_at` — for symmetric `H`, the quadratic
     `phi z = p . (z-x) + ((z-x) . (H *v (z-x)))/2` with gradient field
     `g z = p + H *v (z-x)` satisfies `test_fun_at phi g H x`.
   - `jet_test_fun_at_abstract` — the same for a jet whose matrix arrives as an
     abstract symmetric bounded linear map, which is how everything in
     `Sup_Convolution.thy` produces it (via `matrix_of_symmetric`).

   - `test_grad_at_point` — at the test point the jet test function's gradient
     field is just `p`, which is what `visc_subsol`/`visc_supersol` feed to
     `ell_op`.
   - `ell_op_sandwich` — subsolution `F(p,X) <= 1`, supersolution
     `1 <= F(p,Y)`, and `X <= Y` (theorem on sums) plus `ell_op_elliptic_le`
     give `F(p,Y) <= F(p,X)`; the three SANDWICH both values at `1`.
   - `ell_op_strict_contradiction` — a STRICT subsolution inequality at the test
     point is already inconsistent with the supersolution inequality.

   - `feasible_scaleR_p` — `feasible k L (theta *R p) = feasible k L p` for
     `theta ~= 0`. The feasible set does not see the LENGTH of `p` at all: the
     only constraint involving `p` is `a *v p = 0`.

   **WHERE THE STRICTNESS COMES FROM.** `F` has no zeroth-order term, so a
   subsolution cannot be made strict by subtracting a constant. But `F` IS
   positively homogeneous in `M`, and by `feasible_scaleR_p` the feasible set is
   invariant under rescaling `p`. So scaling a subsolution by `theta` in `(0,1)`
   sends the jet `(p, X)` to `(theta p, theta X)` and turns `F(p,X) <= 1` into
   `F(theta p, theta X) = theta * F(p,X) <= theta < 1` — STRICT, which is
   exactly what `ell_op_strict_contradiction` consumes. The remaining half is
   the homogeneity identity `ell_op k L p (theta *R M) = theta * ell_op k L p M`
   for `theta > 0`, which needs `trace_scaleR`/`scaleR_matrix_matrix` (already
   proved locally in this project) plus scaling of a `cInf`.

   **The sandwich alone is not absurd, and this is the real remaining obstacle.**
   The equation `F = 1` has no zeroth-order term (the degeneracy recorded much
   earlier in this file as the reason 4.2(a) resists a direct argument), so the
   contradiction must come from STRICTNESS.
   `ell_op_strict_contradiction` isolates exactly what is needed, and **THE
   STRICT PERTURBATION IS NOW PROVED**:
   - `cInf_mult_pos` — scaling a conditionally-complete infimum by a positive
     constant.
   - `ell_op_scaleR_matrix` — POSITIVE HOMOGENEITY:
     `ell_op k L p (theta *R M) = theta * ell_op k L p M` for `theta > 0`
     (via `scaleR_matrix_matrix_left`, `trace_scaleR_matrix`, `ell_op_bdd_below`).
   - `ell_op_scaleR_p` — `ell_op` does not see the length of `p`
     (from `feasible_scaleR_p`).
   - `ell_op_scaled_strict` — hence for `theta` in `(0,1)`,
     `ell_op k L p X <= 1` implies
     `ell_op k L (theta *R p) (theta *R X) < 1`: STRICT.

   So a scaled subsolution and an unscaled supersolution sharing a jet pair
   `X <= Y` are inconsistent (`ell_op_strict_contradiction`), which IS the
   contradiction of Theorem 4.2(a).

   **AND THE SCALED SUBSOLUTION IS NOW PROVED:**
   - `transpose_scaleR`, `test_fun_at_scaleR` — a test function scales: for
     `c > 0`, `test_fun_at phi g H x` gives
     `test_fun_at (%z. c * phi z) (%z. c *R g z) (c *R H) x`.
   - `visc_subsol_scaled_strict` — if `u` is a subsolution and `theta` in
     `(0,1)`, then at any test point of `theta * u` the operator inequality is
     STRICT: `ell_op k L (g x) H < 1`. (Divide the maximality by `theta`, apply
     the subsolution to the scaled test function, and use the two `ell_op`
     scaling laws.)

   The DOUBLING argument is under way:
   - `doubling_partial_max_fst` / `doubling_partial_min_snd` — freezing one
     variable at the joint maximiser converts the two-variable maximum into the
     one-variable data `visc_subsol`/`visc_supersol` consume: `xh` maximises `u`
     against `x |-> (alpha/2)*norm (x - yh)^2`, and `yh` MINIMISES `w` against
     `y |-> -(alpha/2)*norm (xh - y)^2`. Both test functions are smooth
     quadratics, so no regularity of `u` or `w` is used here.
   - `frozen_penalty_gradient_fst` / `frozen_penalty_gradient_snd` — BOTH frozen
     penalties have gradient `alpha *R (xh - yh)` (at `xh` and at `yh`
     respectively). The two agreeing is what lets the subsolution and
     supersolution inequalities be evaluated at a COMMON `p`.
   - `scaleR_mat1_vec`, `frozen_penalty_hessian_fst`,
     `frozen_penalty_hessian_snd` — the two Hessians, `alpha *R mat 1` and
     `- alpha *R mat 1`.

   Note the two frozen penalties share that SAME gradient (which is what lets
   the two viscosity inequalities be compared at a common `p`), while their
   Hessians `alpha*I` and `-alpha*I` are ordered the WRONG way. That is exactly
   why naive doubling fails and the theorem on sums is needed to replace them
   by an ordered pair `X <= Y`.

   - `frozen_penalty_test_fun_fst` / `_snd` — both frozen penalties packaged as
     `test_fun_at` in the project's sense.
   - `doubling_viscosity_inequalities` — feeding them into `visc_subsol` and
     `visc_supersol` gives the two operator inequalities AT THE COMMON VECTOR
     `p = alpha *R (xh - yh)`, with Hessians `alpha*I` and `-alpha*I`.
   - `frozen_hessians_not_ordered` — and the obstruction, made precise:
     `(-alpha)*I - alpha*I = (-2*alpha)*I`, which for `alpha > 0` is NEGATIVE
     definite. So `ell_op_elliptic_le` cannot be applied to the naive pair: the
     Hessians are ordered the worst possible way. Replacing `(alpha I, -alpha I)`
     by an ORDERED pair `X <= Y` is exactly the service `sums_matrix_inequality`
     performs, and is why the whole Rademacher/Alexandrov/Jensen development was
     necessary.

   The SIGN-FLIP glue is proved (`Sup_Convolution.thy`). The doubling
   regularises `u` and `- w` by sup-convolution (that is what produces
   semiconvexity), but the supersolution condition speaks about `w` and needs a
   SUBjet:
   - `neg_jet_quotient` — the difference quotient for `- w` with data `(p, X)`
     is exactly MINUS the one for `w` with data `(-p, -X)`.
   - `supconv_neg_jet_transfer` — hence an upper bound on the first is a LOWER
     bound on the second, which is what `visc_supersol` consumes.

   The `psd` BRIDGE is proved (`Comparison_Assembly.thy`):
   - `matrix_diff_vec` — the difference of the representing matrices represents
     the difference of the maps.
   - `psd_of_abstract_le` — from `linear X`, `linear Y`, both abstractly
     symmetric, and `v . X v <= v . Y v` for all `v`, conclude
     `psd (matrix Y - matrix X)`. Since `psd a` is BY DEFINITION
     `transpose a = a & (ALL x. 0 <= x . (a *v x))`, this is exactly the form
     `ell_op_elliptic_le` wants, so the abstract conclusion of
     `sums_matrix_inequality` now feeds degenerate ellipticity directly.
     (`transpose_diff` does not exist in this HOL-Analysis and is proved inline
     entrywise via `transpose_def`/`vec_eq_iff`.)

   **THE CLOSING CHAIN OF THEOREM 4.2(a) IS PROVED**:
   `comparison_contradiction` (`Comparison_Assembly.thy`). Given a subsolution
   `u`, a supersolution `w`, a scaling `theta` in `(0,1)`, and an ORDERED jet
   pair (`linear` + abstractly symmetric `X`, `Y` with `v . X v <= v . Y v`)
   touching at a COMMON `p` at points `xh`, `yh`, it derives `False`. The
   scaling supplies strictness (`visc_subsol_scaled_strict`), the ordering
   supplies `psd` (`psd_of_abstract_le`), and degenerate ellipticity closes
   (`ell_op_strict_contradiction`).

   So Theorem 4.2(a) is now reduced to PRODUCING its three hypotheses `ord`,
   `subtest`, `suptest` from the doubling — which is precisely what the
   Rademacher / Alexandrov / Jensen / theorem-on-sums development in
   `Sup_Convolution.thy` exists to do, and every one of those results is proved.
   `sums_ord_of_inequality` (`Sup_Convolution.thy`) reads the theorem on sums as
   exactly that `ord` hypothesis: `sums_matrix_inequality` concludes
   `v . X v + v . Yb v <= 0` where `Yb` is the slice matrix of the SECOND
   factor; since that factor carries `- w`, the matrix the supersolution needs
   is `Y = - Yb`, and the inequality becomes `v . X v <= v . Y v`.

   `linear_slice_fst` and `linear_slice_snd` (`Sup_Convolution.thy`) supply BOTH
   `linear` hypotheses of `comparison_contradiction`, for the slice maps
   `%z. fst (W (z,0) + alpha *R (z-0, 0-z))`. PITFALL WORTH KNOWING: for
   `W :: 'a*'a => 'a*'a`, `linear_iff` states the two laws in PAIR form
   (`ALL x y. W (x+y) = W x + W y`), NOT split into components. An attempt to
   extract a component-split version failed twice; the working pattern is to
   take the pair form by `unfolding linear_iff by blast`, apply it at
   `(z1,0) + (z2,0)` resp. `c *R (z,0)`, and let simp normalise the pair
   arithmetic. (The `snd` map carries the extra minus sign, since the second
   factor holds `- w`.)

   `sym_slice_fst` / `sym_slice_snd` supply the two abstract SYMMETRY
   hypotheses `symX`, `symY`. Pairing against `(u,0)` resp. `(0,u)`
   (`inner_fst_pair`, `inner_snd_pair`) turns `u . fst P` into an inner product
   on the PRODUCT space, so the symmetry of `W` — which
   `semiconvex_jensen_alexandrov_point` already supplies — transfers to each
   slice; the penalty contributes `alpha * (v . w)`, symmetric on its own.

   So of `comparison_contradiction`'s hypotheses, `lX`, `lY`, `symX`, `symY`
   and `ord` are ALL now available from the theorem-on-sums output. The only
   ones still to produce are `subtest` and `suptest`.

   For those, `superjet_local_max` supplies the jet-to-test-function step: a
   superjet does NOT by itself make `u - phi` have a local maximum (the
   remainder is only `o(norm k^2)` and can be positive), but adding a strictly
   convex correction `(delta/2)*norm k^2` absorbs it and the maximum becomes
   genuine.

   **THE REMAINING SUBTLETY, now precisely located.** That `delta` must
   eventually be removed. This is exactly why the theorem on sums is normally
   stated for CLOSED second-order jets: the subsolution inequality has to be
   extended from `J^{2,+}` to its closure, which needs LOWER SEMICONTINUITY of
   the operator in `(p, M)`. That is precisely what `ell_op_lsc` and the
   envelope machinery in `Envelopes.thy` were built for — `visc_subsol_env` /
   `visc_supersol_env` are already stated via `ell_op_lsc` / `ell_op_usc`, and
   `Envelopes.thy` already proves the envelope-free notions are the STRONGER
   ones. So the last step of E6 is to run the argument against the ENVELOPE
   forms and appeal to that existing comparison, NOT to invent new machinery.

   CONFIRMED PRESENT (checked): `Envelopes.thy` already proves
   `visc_subsol_imp_env` and `visc_supersol_imp_env` — for OPEN `Omega` with
   `Omega <= K`, an envelope-free sub/supersolution IS one in the envelope
   sense. Together with `ell_op_lsc_at_zero` / `ell_op_lsc_at_zero_iff`,
   `ell_op_lsc_le_ell_op` and `ell_op_le_ell_op_usc` (all in `Envelopes.thy`),
   the delta-removal has all its tooling. So E6's final step is a COMPOSITION of
   existing results, with no new analytic content required.

   That composition is now WIRED UP in `Comparison_Assembly.thy`:
   - `ell_op_envelope_sandwich` — `ell_op_lsc <= ereal (ell_op) <= ell_op_usc`.
   - `doubling_env_forms` — on an open `Omega <= K`, the project's
     envelope-free subsolution/supersolution ARE envelope sub/supersolutions,
     so the whole doubling argument may be run in the envelope setting, which
     is where the `delta -> 0` passage is legitimate.

   **ENVELOPE CONTRADICTION NOW PROVED, AND ITS LIMIT IS SHARP.** With envelope
   ellipticity in hand the closing step goes through directly in the envelope
   setting, but ONLY off the origin, and the reason is structural rather than a
   defect of the proof:

     theorem ell_op_env_strict_contradiction:
       psd (Y-X) ==> transpose X = X ==> transpose Y = Y ==> p ~= 0
         ==> 1 <= k ==> k < CARD('n) ==> 1 <= L
         ==> ell_op_lsc k L p X < 1 ==> 1 <= ell_op_usc k L p Y ==> False

     theorem ell_op_env_sandwich:   (* non-strict form, same hypotheses *)
       ... ==> ell_op k L p X = 1 /\ ell_op k L p Y = 1

   WHY p ~= 0 IS ESSENTIAL (do not try to remove it). The two mixed-envelope
   inequalities do NOT close against each other by themselves. Envelope
   ellipticity gives `F^*(p,Y) <= F^*(p,X)`, so the supersolution yields
   `1 <= F^*(p,X)`; together with `F_*(p,X) < 1` that is consistent, because
   the sandwich `F_* <= F <= F^*` permits exactly this whenever the envelopes
   are SEPARATED at `(p,X)`. So the mixed inequalities close iff the envelopes
   COINCIDE at the test jet, which is precisely Lemma 3.1's last clause:
   `ell_op_lsc_off_zero` / `ell_op_usc_off_zero`.

   At `p = 0` they provably do NOT coincide: `ell_op_lsc_at_zero` gives
   `F_*(0,M) = F(0,M)`, while `eq36` gives `F^*(0,M) = eq36_rhs k L M`, whose
   index range has moved up by one (the eigenvalue lambda_(1)(M) is missing).
   And ellipticity cannot close the gap, because it moves the MATRIX argument
   and both envelopes are monotone in it in the SAME direction, so the gap is
   preserved. Consequence for the remaining work: the doubling has to be
   arranged so the shared gradient at the doubled maximum is nonzero. That is a
   real constraint on the E6 assembly, now established rather than assumed.

   **THE DICHOTOMY THE SIDE CONDITION FORCES IS NOW PROVED.** Since the shared
   gradient at the doubled maximum is `p = alpha*(xh - yh)`, the side condition
   `p ~= 0` is exactly "the maximising pair is off the diagonal". Proved in
   Comparison_Assembly.thy:

     doubling_grad_zero_iff:  alpha ~= 0 ==> (alpha *R (xh-yh) = 0) = (xh = yh)
     doubling_diagonal_max:   xh = yh ==> xh is a max of (u - w) over K
     doubling_off_diagonal:   (u-w) xh < (u-w) x  ==>  xh ~= yh
     doubling_grad_nonzero:   ... ==> alpha *R (xh - yh) ~= 0

   So E6's assembly branches cleanly: EITHER the pair is off the diagonal and
   `ell_op_env_strict_contradiction` applies directly, OR `u - w` attains its
   maximum over K at the common point, which is the degenerate branch where the
   penalty term has contributed nothing and which the assembly must dispose of
   separately. `doubling_grad_nonzero` is the usable form: it converts "xh is
   not a maximiser of u - w" into the nonvanishing gradient the envelope
   contradiction needs.

   **THE PENALTY ESTIMATE IS NOW PROVED** (it was missing entirely, and every
   Crandall-Ishii comparison argument needs it). Comparison_Assembly.thy:

     doubling_penalty_bound:  (alpha/2)*|xh-yh|^2 <= C - (u z - w z)
     doubling_dist_bound:     0 < alpha ==> |xh-yh|^2 <= 2*(C - (u z - w z))/alpha
     doubling_ge_diagonal:    (u-w) z <= Phi(xh,yh)  for every z in K

   The proof is the comparison of Phi at the maximiser against Phi at an
   arbitrary DIAGONAL point (z,z), where the penalty vanishes. `doubling_dist_bound`
   is the O(1/alpha) statement that drives xh - yh -> 0; it carries an explicit
   constant, so no compactness or subsequence extraction is needed to use it.

   `doubling_ge_diagonal` closes the loop with the dichotomy: the doubling can
   only ever improve on the diagonal value, never lose to it, which is why the
   off-diagonal branch is the informative one and the diagonal branch is where
   the penalty has contributed nothing.

   **THE alpha -> infinity PASSAGE IS NOW PROVED, WITHOUT SUBSEQUENCES.**
   Comparison_Assembly.thy:

     doubling_max_antimono:      alpha <= beta ==> Phi_beta(xb,yb) <= Phi_alpha(xa,ya)
     tendsto_const_divide_at_top: ((%a. D/a) ---> 0) at_top
     doubling_dist_tendsto:      |X a - Y a|^2 <= 2*D/a  ==>  |X a - Y a|^2 ---> 0

   Antimonotonicity holds because the penalty enters with a minus sign and the
   maximiser for the larger alpha is an admissible competitor for the smaller
   one. Combined with `doubling_ge_diagonal` this pins the family between two
   alpha-independent bounds, so the limit exists with NO compactness argument.

   And because `doubling_dist_bound` carries an EXPLICIT constant, the merging
   of the two components is a sandwich between 0 and 2D/alpha - neither
   compactness of K nor subsequence extraction is needed. This is the third
   time in this development that an explicit rate has replaced a soft textbook
   argument (the others: the sup-convolution dominance property removing the
   subsequence extraction from the epsilon-limit, and `second_order_form_unique`
   removing the A + eps*A^2 matrix perturbation). The common cause is that this
   HOL-Analysis lacks the spectral machinery the soft arguments rely on, so
   explicit-constant routes are strictly preferable wherever they exist.

   **THE DIAGONAL BRANCH IS NOW SETTLED (conditionally, and sharply).**
   Comparison_Assembly.thy:

     eq36_rhs_antitone:       psd (N-M) ==> eq36_rhs k L N <= eq36_rhs k L M
     env_gap_at_zero_nonneg:  F(0,M) <= eq36_rhs k L M
     env_contradiction_at_zero:
        psd (Y-X) ==> ... ==> eq36_rhs k L X <= F(0,X)
          ==> F_*(0,X) < 1 ==> 1 <= F^*(0,Y) ==> False

   `eq36_rhs_antitone` is a free corollary of `ell_op_usc_envelope_elliptic_le`
   plus `eq36`, and is a statement purely about the eigenvalue expression of
   Eq. (3.6) that the project did not previously have.

   WHY THE BRANCH DOES NOT CLOSE UNCONDITIONALLY, now as an explicit chain
   rather than a remark. At p = 0: `F_*(0,X) = F(0,X)` (ell_op_lsc_at_zero) and
   `F^*(0,Y) = eq36_rhs k L Y` (eq36). Antitonicity turns the supersolution into
   `1 <= eq36_rhs k L X`; the subsolution gives `F(0,X) < 1`. These are
   CONSISTENT, precisely because `F(0,X) <= eq36_rhs k L X` with room to spare.
   A contradiction exists exactly when the two coincide. Hence the no-gap
   hypothesis in `env_contradiction_at_zero` is not an assumption about the
   problem but a checkable numeric condition on X, and the theorem discharges
   the branch whenever it holds.

   RESIDUAL OBLIGATION FOR E6, now single and sharply stated: EITHER arrange the
   doubling so the maximising pair is off the diagonal (`doubling_grad_nonzero`
   reduces this to "xh is not a maximiser of u - w"), OR establish the no-gap
   condition `eq36_rhs k L X <= F(0,X)` at the subsolution's matrix. Nothing
   else is missing from the closing chain.

   **EXISTENCE OF THE MAXIMISING PAIR IS NOW PROVED** (it was missing; every
   doubling lemma above took the maximising property as a HYPOTHESIS, and the
   assembly has to discharge it). Comparison_Assembly.thy:

     doubling_maximiser_exists:
       compact K ==> K ~= {} ==> continuous_on K u ==> continuous_on K w
         ==> EX xh:K. EX yh:K. (xh,yh) maximises Phi over K x K
     doubling_maximiser_with_bounds:
       ... ==> the same, packaged with the diagonal lower bound at any z in K

   Proof is attainment of a supremum by a continuous function on the compact
   product K x K (`compact_Times` + `continuous_attains_sup`); the continuity of
   the doubled functional is assembled from `continuous_on_compose2` against fst
   and snd plus `continuous_intros` for the penalty.

   **THE DOUBLING IS NOW HYPOTHESIS-FREE.** The penalty estimates still carried
   a bare `u xh - w yh <= C`; nothing produced such a C. Same gap class as the
   maximiser hypothesis. Comparison_Assembly.thy:

     doubling_upper_bound_exists: compact K, ne, cont u, cont w ==> EX C. ...
     doubling_complete:
       compact K ==> K ~= {} ==> continuous_on K u ==> continuous_on K w
         ==> 0 < alpha ==> z : K
         ==> EX C. EX xh:K. EX yh:K.
               (xh,yh) maximises Phi  /\  |xh-yh|^2 <= 2*(C - (u z - w z))/alpha

   `doubling_complete` has NO hypotheses beyond compactness, nonemptiness and
   continuity: the maximiser, the constant, and the O(1/alpha) merging estimate
   all come out together.

   GAP CLASS WORTH REMEMBERING: over several turns every doubling lemma
   (`doubling_penalty_bound`, `doubling_dist_bound`, `doubling_diagonal_max`,
   `doubling_max_antimono`) took "(xh,yh) maximises Phi" and "u xh - w yh <= C"
   as HYPOTHESES. Each looked complete on its own; nothing in the project
   produced either object. When a development is assembled from lemmas that
   each assume the previous stage's output, the missing existence statements are
   invisible until something tries to chain them. Check for this class directly
   rather than trusting per-lemma greenness.

   **THE subtest/suptest HYPOTHESES ARE NOW PRODUCED.** Third instance of the
   same gap class: `comparison_contradiction` takes the local max/min statements
   for the jet test function as bare hypotheses, and nothing produced them.
   Comparison_Assembly.thy:

     quad_form_shift_identity:      k . ((A + d*I) *v k) = k . (A *v k) + d*|k|^2
     quad_form_shift_identity_neg:  k . ((A - d*I) *v k) = k . (A *v k) - d*|k|^2
     matrix_vector_neg_left:        (-B) *v x = - (B *v x)
     jet_imp_local_max_test:  Alexandrov jet of v at xh with data (p,A), d > 0
        ==> the `subtest` local-max statement for the matrix A + d*I
     jet_imp_local_min_test:  subjet of v at yh
        ==> the `suptest` local-min statement for the matrix A - d*I

   MECHANISM: `superjet_local_max` leaves a (d/2)|k|^2 slack. That slack is
   EXACTLY the extra quadratic form contributed by d*I, so correcting the test
   matrix by +d*I on the sub side and -d*I on the super side absorbs it exactly.
   This is why the delta-corrected matrices appear in the plan at all; it is not
   a technical convenience but the precise bookkeeping of that slack.

   Both bridges are stated in the exact syntactic shape of `comparison_contradiction`'s
   subtest/suptest, so they plug in directly.

   NOTE ON THE MIRROR LEMMA: deriving the min form from the max form by applying
   it to `-v` does NOT work smoothly, because simp normalises `- (A - d*I)` to
   `d*I - A` and then the negation rewrite no longer fires. The min form is
   proved directly from `superjet_local_max` instead. Same class of trap as the
   eta-contraction and `unfolding`-does-not-fire issues recorded elsewhere.

   **THE delta-REMOVAL IS NOW PROVED, AND MY EARLIER PLAN FOR IT WAS WRONG.**
   Comparison_Assembly.thy:

     ell_op_lsc_le_one_of_shifts:
       (ALL d. 0<d<D --> F(p, M + d*I) <= 1) ==> F_*(p,M) <= 1
     ell_op_usc_ge_one_of_shifts:
       (ALL d. 0<d<D --> 1 <= F(p, M - d*I)) ==> 1 <= F^*(p,M)

   WHY delta CANNOT BE ABSORBED. After correcting to X + d*I and Y - d*I one
   would need `Y - X >= 2d*I`, and the theorem on sums gives only `Y - X >= 0`.
   So the correction must be removed by a LIMIT, not cancelled.

   WHY THE NAIVE READING GOES THE WRONG WAY. Degenerate ellipticity gives
   `F(p, M + d*I) <= F(p, M)`, so `F(p, M + d*I) <= 1` does NOT yield
   `F(p,M) <= 1`. What it yields is a bound at points arbitrarily close to
   (p,M), which is exactly the content of F_*: since (p, M + d*I) -> (p,M) as
   d -> 0, every ball around (p,M) contains such a point, so every inner infimum
   is <= 1 and hence so is their supremum.

   CORRECTION TO AN EARLIER STATUS NOTE: the plan recorded several turns ago
   named `ell_op_lsc_at_zero` as the tool for removing delta. That was wrong.
   `ell_op_lsc_at_zero` is about the GRADIENT being zero and has nothing to do
   with delta. The right tool is lower semicontinuity in the MATRIX argument,
   which is what the two theorems above establish.

   **THE CLOSING CHAIN OF THEOREM 4.2(a) IS NOW ASSEMBLED, delta-FREE.**
   Comparison_Assembly.thy:

     ell_op_lsc_le_of_shifts:  (ALL d in (0,D). F(p, M+d*I) <= c) ==> F_*(p,M) <= c
     ell_op_usc_ge_of_shifts:  (ALL d in (0,D). c <= F(p, M-d*I)) ==> c <= F^*(p,M)
     env_strict_contradiction_of_shifts:
       psd (Y-X), sym X, sym Y, p ~= 0, 1<=k<CARD('n), 1<=L, 0<D, c<1,
       (ALL d in (0,D). F(p, X+d*I) <= c),
       (ALL d in (0,D). 1 <= F(p, Y-d*I))
         ==> False

   WHY THE BOUND HAD TO BE GENERALISED FROM 1 TO c. The `_one` versions proved
   last turn are enough to reach the SANDWICH but not the CONTRADICTION: the
   limit turns `F(p, X+d*I) < 1` into `F_*(p,X) <= 1` and the strict inequality
   is LOST. That is fatal here, because the equation has no zeroth-order term
   and the non-strict sandwich is consistent (see `ell_op_sandwich`).

   The fix: the strictness from the theta-scaling is UNIFORM in delta. It gives
   `F(theta*p, theta*X) = theta*F(p,X) <= theta` with theta < 1 independent of
   delta, and a uniform bound DOES survive the limit. Hence the restatement with
   an arbitrary c.

   `env_strict_contradiction_of_shifts` hypotheses match what the doubling
   delivers: uniform strict bound on the sub side, supersolution bound on the
   super side, ordering X <= Y from the theorem on sums, and p ~= 0 from
   `doubling_grad_nonzero`. No delta survives in the conclusion.

   **E6 IS NOW COMPOSED. Theorem 4.2(a) closes from jets, delta-free.**
   Comparison_Assembly.thy:

     visc_subsol_scaled_uniform:  ... ==> ell_op k L (g x) H <= theta
        (same proof as visc_subsol_scaled_strict, stopped one step earlier -
         the existing lemma derives `<= theta` and then WEAKENS it to `< 1`,
         and that weakening is exactly what destroyed uniformity)
     transpose_shift_add / transpose_shift_diff:  X +- d*I stays symmetric
     subsol_shifted_bound:    jet of theta*u at xh ==> F(p, Xm + d*I) <= theta
     supersol_shifted_bound:  jet of -w at yh     ==> 1 <= F(p, Ym - d*I)
     comparison_env_from_jets:
       visc_subsol, visc_supersol, 0<theta<1, xh,yh in Omega, Xm Ym symmetric,
       psd (Ym - Xm), p ~= 0, 1<=k<CARD('n), 1<=L,
       second-order jet of theta*u at xh with data (p,Xm),
       second-order jet of -w at yh with data (-p,-Ym)
         ==> False
     comparison_env_from_jets_offdiag:
       same, with `p ~= 0` replaced by "xh does not maximise u - w over K",
       via doubling_grad_nonzero

   NO DELTA APPEARS IN EITHER STATEMENT. The correction is introduced internally
   to turn the asymptotic jets into genuine local extrema (jet_imp_local_max_test
   / jet_imp_local_min_test) and removed again by the envelopes
   (ell_op_lsc_le_of_shifts / ell_op_usc_ge_of_shifts). The hypotheses are
   exactly the output of the Rademacher / Alexandrov / Jensen / theorem-on-sums
   development in Sup_Convolution.thy.

   **THE THEOREM ON SUMS IS NOW WIRED TO THE psd HYPOTHESIS.**
   Comparison_Assembly.thy:

     sums_gives_ordering:  v . X v <= v . Y v,  where
         X v = fst (W (v,0)) + alpha *R v
         Y v = - (snd (W (0,v)) + alpha *R v)
     sums_gives_psd:  ... + linearity + symmetry of the two blocks
         ==> psd (matrix Y - matrix X)

   HOW TO READ THE RAW OUTPUT of `sums_matrix_inequality`. It delivers

     v . fst (W (v,0) + alpha*(v,-v)) + v . snd (W (0,v) + alpha*(-v,v)) <= 0

   which is an ordering between the two DIAGONAL BLOCKS of W. The block for the
   first argument is X; the block for the second is NEGATED to give Y, because
   the supersolution enters the doubled functional as -w. The `+ alpha*v` in
   each block is the second derivative of the penalty -(alpha/2)|x-y|^2
   restricted to that block - it is what makes the two blocks comparable at all,
   and it is why the raw statement carries the shifts alpha*(v,-v) and
   alpha*(-v,v) rather than being a bare statement about W.

   `sums_gives_psd` produces exactly the `psd (Ym - Xm)` hypothesis of
   `comparison_env_from_jets`.

   **THE NEGATIVITY HYPOTHESIS IS NOW DISCHARGED TOO.**
   Comparison_Assembly.thy:

     sums_ordering_at_interior_max:
       bounded_linear W, 0 < d, Psi has an interior max at zh over the d-ball,
       Alexandrov jet of Psi at zh with data (q,W)
         ==> v . X v <= v . Y v   (blocks as in sums_gives_ordering)
     sums_psd_at_interior_max:  ... + linearity/symmetry of blocks ==> psd (Ym - Xm)

   `k . W k <= 0` was the last bare hypothesis of `sums_gives_ordering`, and it
   is not an assumption about the problem: `second_order_interior_max`
   (Sup_Convolution.thy) supplies it at any interior maximum, and the doubled
   functional has one by construction. The remaining inputs are exactly the
   maximum property, the jet, and linearity/symmetry of the two diagonal blocks
   - all outputs of the Alexandrov development.

   ENVIRONMENT NOTE: neither `bounded_linear.scaleR` nor
   `bounded_linear_imp_linear` exists in this Isabelle. The project's own idiom
   (used inside `second_order_interior_max`) is
     using blX by (simp add: linear_simps)
   to get `X (t *R w) = t *R X w` from `bounded_linear X`. Use that.

   **INSTANTIATED AT THE DOUBLED SUP-CONVOLUTIONS.**
   Comparison_Assembly.thy:

     doubled_semiconvexity_constant_pos:  0 < 1/eps + 1/eps + 2*alpha
     doubled_supconv_jet_exists:
       u, w bounded above; 0 < eps; 0 <= alpha; Jensen data (rho < r, bound m,
       dd > 0, 2*dd*r < Psi(xi) - m)
         ==> EX zh p q W. dist zh xi < rho /\ norm p <= dd
               /\ (tilted Psi has a max at zh over cball xi r)
               /\ bounded_linear W /\ W symmetric
               /\ Alexandrov jet of Psi at zh with data (q,W)

   where Psi is the doubled functional built from the SUP-CONVOLUTIONS,
   supconv u eps (fst z) + supconv w eps (snd z) - (alpha/2)|fst z - snd z|^2.

   The semiconvexity constant is 1/eps + 1/eps + 2*alpha: one 1/eps from each
   sup-convolution and 2*alpha from the penalty. Strictly positive as soon as
   eps > 0, which is what Jensen's lemma requires.

   This delivers exactly the input of `sums_psd_at_interior_max`. Note the
   maximum Jensen returns is a GLOBAL max of the TILTED functional over
   cball xi r (tilt p . y with norm p <= dd), not a bare local max; converting
   to the interior-max form is a restriction to a ball inside cball xi r around
   zh, which dist zh xi < rho < r permits.

   ENVIRONMENT NOTE (cost three build cycles): in a lemma whose only numeric
   content is `0 < eps ==> 0 < 1/eps + ...`, type inference does NOT default to
   real, and the class it picks lacks the lemmas one expects -
   `divide_pos_pos` will not fire as an intro rule and
   `positive_imp_inverse_positive` reports "no unifiers". FIX: declare
   `fixes eps alpha :: real` explicitly. Note also that `0 <= 1/eps` IS closed
   by simp here while `0 < 1/eps` is NOT (cf. the `0 < norm v + 1` entry).

   **THE TILTED-MAX / INTERIOR-MAX JOIN IS NOW WRITTEN.**
   Comparison_Assembly.thy:

     tilt_absorb:                 the tilt splits across the two summands
     global_max_imp_interior_max: global max on cball xi r ==> interior max on
                                  the ball of radius r - dist zh xi around zh
     interior_radius_pos:         dist zh xi < r ==> 0 < r - dist zh xi
     doubled_tilted_interior_max: Jensen's output, in the exact interior-max
                                  shape sums_ordering_at_interior_max consumes

   WHY JENSEN'S TILT COSTS NOTHING HERE (the substantive point). Jensen returns
   a max of the TILTED functional Psi + p . (.), not of Psi. But `p . z` splits
   as `fst p . fst z + snd p . snd z`, so it absorbs into the two summands a and
   b, leaving the doubled form (two functions of the SEPARATE arguments, minus
   the penalty) intact. The tilt therefore does not disturb the block structure
   that the theorem on sums relies on - which is the only property of the
   doubled functional that matters downstream.

   ISABELLE NOTE: `global_max_imp_interior_max` applied by `rule ... [OF ...]`
   raises "OF: multiple unifiers" - the pattern `?Psi y <= ?Psi zh` against
   `Psi ?y <= Psi zh` is higher-order and admits several instantiations.
   Pinning zh and k is NOT enough; all of Psi, xi, r, zh, k must be given via
   `where` before the `OF`.

   **THE BLOCK HYPOTHESES ARE NOW DERIVED FROM THE JET ITSELF.**
   Comparison_Assembly.thy:

     linear_of_bounded_linear_prod: bounded_linear W ==> linear W
        (this Isabelle has no `bounded_linear_imp_linear`; prove via linearI
         with `simp add: linear_simps` for each law)
     linear_block_fst / linear_block_snd
     sym_block_fst / sym_block_snd
     sums_psd_from_jet:
       bounded_linear W, W symmetric, interior max, Alexandrov jet
         ==> psd (matrix Y - matrix X)

   So the psd ordering needs NOTHING beyond the jet and the maximum property.
   Every side condition of `sums_psd_at_interior_max` is discharged from the
   Alexandrov data itself.

   ONLY OBSTACLE WAS SYNTACTIC: the slice lemmas in Sup_Convolution.thy
   (`linear_slice_fst` etc.) are phrased with the shifts written out as
   `alpha *R (z - 0, 0 - z)`, while the blocks here use the reduced form
   `+ alpha *R z`. Equal by simp, so the bridges are one-liners - but the
   mismatch makes the slice lemmas look inapplicable at first reading.

   **THE JET TRANSFER BACK TO u IS NOW WIRED IN.**
   Comparison_Assembly.thy:

     supconv_bound_transfer:
       supconv attained at ys; increment bound c for supconv at x
         ==> u (ys+k) - u ys <= c
     supconv_local_max_transfer:
       quadratic local upper bound for supconv at x
         ==> the SAME quadratic local upper bound for u at ys, SAME (p,A)
     supconv_local_max_transfer_ball:
       the ball form, i.e. exactly the maxloc hypothesis that visc_subsol and
       `subsol_shifted_bound` consume, stated for u itself

   THE POINT: nothing about the jet is recomputed. If the sup-convolution at x
   is ATTAINED at ys, then increments of u at ys are dominated by increments of
   supconv at x with the SAME increment vector k, so a quadratic bound transfers
   verbatim with the same (p,A). No subsequence, no limit. This is the
   sup-convolution's "magic property" in the form the comparison argument
   consumes, and it is why the whole development avoids the textbook's
   subsequence extraction in the epsilon-limit.

   Note the base point SHIFTS: a local statement about supconv near x becomes a
   local statement about u near ys, on a ball of the same radius.

   **ALL THREE MATRIX HYPOTHESES NOW COME FROM THE JET.**
   Comparison_Assembly.thy:

     transpose_matrix_block_fst / transpose_matrix_block_snd:
        bounded_linear W + W symmetric ==> the block matrices are symmetric,
        via `matrix_of_symmetric` (Sup_Convolution.thy) fed by the block lemmas
     block_matrices_from_jet:
        one theorem giving all three matrix hypotheses of
        `comparison_env_from_jets` - transpose Xm = Xm, transpose Ym = Ym,
        psd (Ym - Xm) - from bounded_linear W, symmetry of W, the interior
        maximum, and the Alexandrov jet

   So NO property of Xm or Ym is assumed anywhere in the closing argument; all
   three are derived from the Alexandrov data.

   **THE GRADIENT ALIGNMENT IS PROVED, AND IT COLLAPSES TO q = 0.**
   Comparison_Assembly.thy:

     gradient_vanishes_at_interior_max:
        bounded_linear W, interior max, Alexandrov jet ==> q = 0
     doubled_jet_no_gradient:
        hence the jet at the doubled maximum has NO first-order term
     common_gradient_split: the trivial arithmetic that follows

   WHY THIS WAS NOT A RENAMING. `comparison_env_from_jets` needs the jets of
   theta*u at xh and of -w at yh to share a common gradient, p and -p. Writing
   q = (q1,q2) for the gradient of Psi at zh, and noting the penalty
   -(alpha/2)|x-y|^2 contributes -alpha*(x-y) to the first block and
   +alpha*(x-y) to the second, the gradient of a at xh is q1 + alpha*(xh-yh)
   and that of b at yh is q2 - alpha*(xh-yh). For these to be p and -p one needs
   exactly q1 + q2 = 0.

   That holds for the strongest possible reason: at an interior maximum the
   gradient VANISHES. `second_order_interior_max` already yields `q . v = 0` for
   EVERY v; taking v = q gives q . q = 0, hence q = 0.

   CONSEQUENCE WORTH KEEPING: the common gradient is therefore p = alpha*(xh-yh),
   which is precisely the vector whose nonvanishing `doubling_grad_nonzero`
   establishes. So the off-diagonal condition and the gradient alignment are the
   SAME condition, not two independent ones - the p ~= 0 side condition of
   `ell_op_env_strict_contradiction` is discharged by the very same fact that
   makes the two jets align.

   **E6 IS COMPOSED END TO END.** Comparison_Assembly.thy:

     comparison_env_complete:
       visc_subsol k L Omega u, visc_supersol k L Omega w, 0<theta<1,
       xh,yh in Omega, 1<=k<CARD('n), 1<=L,
       bounded_linear W, W symmetric, 0 < dd,
       interior max of Psi = a(fst) + b(snd) - (alpha/2)|fst-snd|^2 at zh,
       Alexandrov jet of Psi at zh with data (q,W),
       alpha*(xh-yh) ~= 0,
       jet of theta*u at xh with (alpha*(xh-yh), Xm),
       jet of -w at yh with (-alpha*(xh-yh), -Ym)
         ==> False
     where Xm = matrix (%v. fst (W (v,0)) + alpha *R v)
           Ym = matrix (%v. - (snd (W (0,v)) + alpha *R v))

     comparison_env_complete_offdiag:
       same, with `alpha*(xh-yh) ~= 0` traded for "xh does not maximise u - w
       over K" via doubling_grad_nonzero

   EVERY matrix hypothesis is DERIVED from the Alexandrov data of the doubled
   functional (block_matrices_from_jet), not assumed. The shared gradient is
   alpha*(xh-yh) on both sides, which is forced by q = 0 at the interior max.
   What remains as hypotheses are the genuine inputs only: the two viscosity
   properties, the scaling parameter, the interior maximum with its jet, the
   off-diagonal condition, and the two component jets.

   REMAINING FOR E6: none of the links. What is still not written is the
   instantiation of a and b at theta*supconv u eps and -supconv w eps together
   with the supconv_local_max_transfer step, i.e. deriving the two COMPONENT
   jets from the doubled jet rather than taking them as hypotheses. All the
   pieces for that exist (product_form_block_diagonal, second_order_form_unique,
   supconv_local_max_transfer).

   **THE FIRST COMPONENT JET IS NOW DERIVED FROM THE DOUBLED JET.**
   Comparison_Assembly.thy:

     penalty_difference_identity:
        (alpha/2)|x+h-y|^2 - (alpha/2)|x-y|^2 = alpha*((x-y).h) + (alpha/2)|h|^2
        EXACT, no remainder - the penalty is a quadratic
     filterlim_slice_fst / filterlim_slice_snd:  h -> (h,0) maps at 0 to at 0
     norm_slice_fst / norm_slice_snd:            norm (h,0) = norm h
     doubled_slice_numerator_fst:                the numerator identity
     doubled_jet_slice_fst:
        Alexandrov jet of Psi at zh with data (q,W)
          ==> jet of a at fst zh with gradient  fst q + alpha*(fst zh - snd zh)
              and Hessian block  fst (W (h,0)) + alpha *R h

   WHAT THE COMPUTATION SHOWS: the b terms cancel outright (the second argument
   does not move), the penalty contributes alpha*(xh-yh).h to the gradient and
   alpha*h to the Hessian, and W contributes its first diagonal block. That is
   exactly the block X of the theorem on sums - so the block decomposition is
   not a definition chosen to make things work, it is what restriction to a
   coordinate slice produces.

   ISABELLE NOTES (this one cost five build cycles):
   * `filterlim_compose[OF tendsto slice]` yields the composed function as
     `f o g`; add `by (simp add: o_def)` or the statement will not match.
   * Do NOT try to rewrite the composed limit with `simp add:` - simp normalises
     the numerator into a different shape first and the numerator lemma then
     never fires. Prove the quotient identity separately as `eq ... for h` and
     use `comp[unfolded eq]`.
   * `norm_slice_fst` will not fire under `simp only` in that position; use
     `unfolding <numerator lemma>` then `simp add: norm_Pair`.
   * The numerator identity needs `inner_commute` in the simp set, otherwise
     `h . fst zh` and `fst zh . h` are left as distinct terms.

   STILL TO DO for the component jets: the snd-slice analogue (all four
   ingredients are already proved, only the numerator lemma and the theorem
   need mirroring), and then feeding both into `comparison_env_complete`.

   **BOTH COMPONENT JETS ARE NOW DERIVED FROM THE DOUBLED JET.**
   Comparison_Assembly.thy:

     penalty_difference_identity_snd
     doubled_slice_numerator_snd
     doubled_jet_slice_snd:
        jet of b at snd zh with gradient  snd q - alpha*(fst zh - snd zh)
        and Hessian block  snd (W (0,h)) + alpha *R h
     doubled_jet_slices_at_max:
        BOTH slices at once, with q = 0 already substituted, so the two
        gradients are  alpha*(xh-yh)  and  -(alpha*(xh-yh))

   THE SIGN STRUCTURE, which is the point. The penalty moves the SECOND argument
   on the snd slice, so its LINEAR contribution changes sign: the gradient of b
   at yh is q2 - alpha*(xh-yh), the negative of the first slice's shift. But the
   QUADRATIC contribution alpha*h to the Hessian has the SAME sign on both
   slices. That asymmetry in the gradient together with symmetry in the Hessian
   is exactly what makes the two jets share a common p and -p while BOTH blocks
   carry `+ alpha*v` - which is what the theorem on sums needs.

   `doubled_jet_slices_at_max` produces the two jets in precisely the form
   `comparison_env_complete` takes as hypotheses.

   ISABELLE NOTE: in `penalty_difference_identity_snd` the closing
   `by (simp add: field_simps)` after a `finally` FAILS - the residual goal is
   the hypothesis multiplied by 2*alpha, and with alpha a variable neither
   linarith nor field_simps will scale it. Restructure: state the squared-norm
   expansion as its own fact e1, derive e2 = (alpha/2)*e1, then close with
   `using e2 by (simp add: algebra_simps)`.

   **THEOREM 4.2(a) NOW FOLLOWS FROM THE DOUBLED JET ALONE.**
   Comparison_Assembly.thy:

     matrix_apply_eq:            linear X ==> matrix X *v h = X h
     block_fst_matrix_apply / block_snd_matrix_apply
     comparison_from_doubled_jet:
       visc_subsol, visc_supersol, 0<theta<1, xh,yh in Omega, 1<=k<CARD, 1<=L,
       bounded_linear W, W symmetric, 0 < dd, fst zh = xh, snd zh = yh,
       interior max of  theta*u(x) - w(y) - (alpha/2)|x-y|^2  at zh,
       Alexandrov jet of that functional at zh with data (q,W),
       alpha*(xh-yh) ~= 0
         ==> False

   THE COMPONENT JETS ARE NO LONGER HYPOTHESES. They are produced from the
   doubled jet by `doubled_jet_slices_at_max` and matched to their matrices by
   the two block lemmas. What is assumed is only the doubled data itself, the
   two viscosity properties, and the off-diagonal condition.

   ISABELLE NOTE: `matrix_works` is stated for `Vector_Spaces.linear`, not the
   real-vector-space `linear`, so route through `linear_matrix_vector_mul_eq`:
     using lin by (simp add: matrix_works linear_matrix_vector_mul_eq)

   ===================================================================
   CORRECTION (2026-07-31): Comparison_Assembly.thy is NOT batch-only.
   ===================================================================
   An earlier entry in this file says Comparison_Assembly must be batch-built
   because it imports two project chains (Sup_Convolution and
   Lemma_3_1_Envelopes). That is WRONG. PIDE holds it: `list_loaded_theories`
   shows Arbitrage.Comparison_Assembly loaded, and `get_state` reports
   922 commands, commands_bad 0, errors 0, commands_failed 0, total 621 ms.

   Consequence for future sessions: use the PIDE MCP tools on this file rather
   than a ~80 s `isabelle build` per edit. That is roughly a 60x faster edit
   loop, and this session spent a great many builds that did not need to be
   builds. The diamond-import rule recorded in memory is about a diamond over a
   LOCAL DRAFT theory; two independent project chains are fine.

   **THE SUBSOLUTION BOUND NOW COMES STRAIGHT FROM A SUP-CONVOLUTION JET.**
   Comparison_Assembly.thy:

     subsol_shifted_bound_supconv:
       visc_subsol k L Omega u, 0 < theta, ys in Omega, Xm symmetric,
       1<=k<CARD('n), 1<=L, theta*u bounded above, 0 < eps,
       supconv (theta*u) eps x = theta*u ys - dist(x,ys)^2/(2 eps)   [ATTAINED]
       jet of supconv (theta*u) eps at x with data (p, Xm), 0 < delta
         ==> ell_op k L p (Xm + delta*I) <= theta

   WHY THIS WAS NEEDED. The comparison argument never has jets of theta*u to
   hand: the doubled functional is built from the SUP-CONVOLUTIONS, because
   those are what is semiconvex and hence what Jensen's lemma applies to. So the
   jet produced at the doubled maximum is a jet of supconv (theta*u) eps, NOT of
   theta*u. `subsol_shifted_bound` (the earlier version) assumed the latter.

   The delta-corrected quadratic bound for the sup-convolution at x transfers by
   `supconv_local_max_transfer_ball` to the SAME bound for theta*u at the
   ATTAINING point ys - same p, same matrix - and there the viscosity property
   applies. NOTE THE BASE POINT MOVES from x to ys, so it is ys, not x, that
   must lie in Omega.

   PIDE NOTE (2026-07-31, refining the correction above): PIDE holds
   Comparison_Assembly, but it does NOT pick up edits made by writing the file
   on disk - `get_state` kept reporting the stale 922-command/621 ms snapshot
   after a python write. Use the MCP `edit`/`create_file` tools so the PIDE
   buffer is updated; disk writes still require `isabelle build` to verify.

   **THEOREM 4.2(a) NOW CLOSES FROM SUP-CONVOLUTION JETS.**
   Comparison_Assembly.thy:

     neg_shift_matrix_apply:  ((-B) + d*I) *v h = - ((B - d*I) *v h)
     supersol_shifted_bound_supconv:
       visc_supersol k L Omega w, ys in Omega, Ym symmetric, (-w) bounded above,
       0 < eps, supconv (-w) eps x ATTAINED at ys,
       jet of supconv (-w) eps at x with data (-p, -Ym), 0 < delta
         ==> 1 <= ell_op k L p (Ym - delta*I)
     comparison_supconv_complete:
       both viscosity properties, 0<theta<1, the two attaining points in Omega,
       Xm Ym symmetric, psd (Ym - Xm), p ~= 0, 1<=k<CARD('n), 1<=L,
       theta*u and -w bounded above, 0 < eps,
       both sup-convolutions ATTAINED, and their two jets
         ==> False

   Both bounds now come from jets of the SUP-CONVOLUTIONS - what the doubled
   functional actually carries - and the two attaining points ysu, ysw are where
   the viscosity properties get applied. The uniform bound theta < 1 is what
   survives the delta -> 0 limit and gives the STRICT envelope inequality;
   p ~= 0 is what identifies both envelopes with F itself. No delta in the
   conclusion.

   PIDE WORKFLOW NOW IN USE (and it works). After `read` re-synchronises the
   PIDE buffer with the on-disk file, edits through the MCP `edit` tool are
   checked in SECONDS: `get_progress` returned overall_status ok /
   commands_failed 0 for both of the above on the FIRST attempt. Compare ~80 s
   per `isabelle build`. The earlier "Comparison_Assembly is batch-only" note
   was simply wrong and cost this session a great many unnecessary builds.
   Workflow: `read` to sync -> `edit` -> `get_progress` -> occasional
   `isabelle build` as a final cross-check (PIDE tolerates a missing final
   `end`, the build does not).

   **THEOREM 4.2(a) NOW CLOSES FROM THE DOUBLED SUP-CONVOLUTION JET ALONE.**
   Comparison_Assembly.thy:

     comparison_supconv_from_doubled_jet:
       visc_subsol, visc_supersol, 0<theta<1, ysu,ysw in Omega,
       1<=k<CARD('n), 1<=L, bounded_linear W, W symmetric, 0 < dd,
       interior max at zh of
         supconv (theta*u) eps (fst z) + supconv (-w) eps (snd z)
           - (alpha/2)|fst z - snd z|^2,
       its Alexandrov jet with data (q,W),
       alpha*(fst zh - snd zh) ~= 0,
       theta*u and -w bounded above, 0 < eps,
       each sup-convolution ATTAINED at ysu / ysw
         ==> False

   The two component jets are no longer hypotheses: they are the coordinate
   slices of the doubled jet (doubled_jet_slices_at_max with a, b instantiated
   at the two sup-convolutions), matched to matrices by the block lemmas; the
   three matrix hypotheses come from block_matrices_from_jet.

   **NEWLY IDENTIFIED OBSTACLE - JENSEN'S TILT DOES NOT COMPOSE FOR FREE.**
   The natural next step is to feed `doubled_supconv_jet_exists` (Jensen) into
   the theorem above. It does NOT fit as-is, and the reason is worth recording
   because an earlier note in this file claimed the tilt "costs nothing".

   That earlier note is right about the BLOCK STRUCTURE: the tilt p . z splits
   as p1 . fst z + p2 . snd z and absorbs into the two summands, so the doubled
   form survives. But it is WRONG about the GRADIENTS. At the interior maximum
   of the TILTED functional, `gradient_vanishes_at_interior_max` gives
   grad(Psi + p . .) = 0, hence grad(Psi) = -p. The two block gradients of the
   UNTILTED summands are then
       -p1 + alpha*(xh-yh)   and   -p2 - alpha*(xh-yh),
   and for these to be P and -P one needs p1 + p2 = 0, which Jensen does NOT
   provide. (Compare the untilted case, where q = 0 gives the alignment for
   free - see the gradient-alignment entry above.)

   So a further limit is required: Jensen supplies norm p <= dd with dd at our
   disposal, and the strictness margin 1 - theta is uniform, so the tilt can be
   absorbed by taking dd small. That step is NOT written. It is a genuine
   analytic step, not bookkeeping.

   **THE TILT OBSTACLE NOW HAS THE RIGHT TOOL.** Comparison_Assembly.thy:

     ell_op_lsc_le_of_nearby:
       (ALL e>0. EX p' M'. dist (p',M') (p,M) < e /\ F(p',M') <= c)
         ==> F_*(p,M) <= c
     ell_op_usc_ge_of_nearby:   dual
     env_strict_contradiction_of_nearby:
       psd (Y-X), sym X, sym Y, p ~= 0, 1<=k<CARD('n), 1<=L, c < 1,
       bounds holding ARBITRARILY NEAR (p,X) and (p,Y)
         ==> False

   WHY THIS IS THE RIGHT GENERALISATION. The earlier shift theorems move only
   the MATRIX, by delta*I. Jensen's tilt also moves the GRADIENT, by an amount
   <= dd which is at our disposal but never zero, so no shift lemma can absorb
   it. The correct statement is not another shift lemma but the general one: a
   bound holding at points ARBITRARILY CLOSE to (p,M) - however produced -
   passes to the lower envelope. That is precisely what F_* means, and it
   subsumes both the delta*I shifts and the tilt.

   THE LOAD-BEARING DETAIL: the nearby point may DEPEND ON THE RADIUS. That is
   what permits dd to be chosen AFTER e, i.e. re-running Jensen with a smaller
   tilt for each radius, which is exactly how the analytic argument goes. A
   fixed perturbed point would not work, since it cannot be shrunk.

   STILL TO DO: supply those nearby points, i.e. show that re-running Jensen at
   tilt dd gives bounds within e of (p,X) and (p,Y) for dd small enough. That
   requires controlling how the maximiser and its jet move with dd, and is the
   remaining analytic content of E6.

   **E6 IS NOW REDUCED TO ONE QUANTITATIVE HYPOTHESIS PER SIDE.**
   Comparison_Assembly.thy:

     nearby_of_tilt_family / nearby_of_tilt_family_ge:
        0 <= kappa, 0 < D,
        dist ((P dd, Mf dd)) (p,M) <= kappa*dd   for 0 < dd < D,
        the operator bound at (P dd, Mf dd)      for 0 < dd < D
          ==> the nearby-point hypothesis at (p,M)
     env_strict_contradiction_of_tilt_families:
        psd (Y-X), sym X, sym Y, p ~= 0, 1<=k<CARD('n), 1<=L, c < 1,
        both tilt families with the linear-rate estimate and their bounds
          ==> False

   NO CONVERGENCE OF THE JETS IS NEEDED - only the estimate
   dist ((P dd, Mf dd)) (p,M) <= kappa*dd, and kappa may be arbitrary, because
   the radius is chosen AFTER it. That is the whole remaining analytic content
   of E6: show that the doubled maximiser and its jet move at most linearly in
   the Jensen tilt parameter dd. Everything else on this path - envelopes,
   strictness, ordering, off-diagonal condition, block decomposition, jet
   transfer - is proved.

   ISABELLE NOTES:
   * `kappa * e < e * (2*(kappa+1))` is NOT closed by
     `using e0 kap by (simp add: algebra_simps)`: the residual is
     `0 < kappa*e + e*2`, and simp will not supply `0 <= kappa*e` (a product of
     unknowns). Prove `0 <= kappa*e` by `mult_nonneg_nonneg`, expand the RHS
     explicitly, then close with `linarith`.
   * THE PIDE `edit` TOOL MATCHES `old_text` AGAINST THE UNICODE FORM. The
     on-disk file may hold `\<kappa>` while the PIDE buffer holds the unicode
     character; passing the backslash-escape form gives
     "old_text not found in the given range". Always write Isabelle symbols as
     unicode in `old_text` (and in `text`).

   **A SECOND ROUTE PAST THE TILT, WITH NO LIMIT AT ALL.**
   Comparison_Assembly.thy:

     gradient_is_minus_tilt:
       interior max of the TILTED functional Psi + p . (.),
       Alexandrov jet of the UNTILTED Psi with data (q,W)
         ==> q = -p
     antisym_tilt_block_gradients / antisym_tilt_aligns_gradients:
       if the tilt is ANTISYMMETRIC, p = (p0, -p0), then q = (-p0, p0) and the
       two block gradients  fst q + alpha*(xh-yh)  and  snd q - alpha*(xh-yh)
       are EXACT NEGATIVES

   So there are now two independent routes past Jensen's tilt:
     (i)  linear-rate: dist ((P dd, Mf dd)) (p,M) <= kappa*dd, then
          nearby_of_tilt_family. Needs an ESTIMATE on how the maximiser moves.
     (ii) antisymmetric tilt: no limit, no rate, no smallness - the tilt need
          only satisfy p = (p0, -p0). Needs a STRUCTURAL property of Jensen's
          output instead.
   Route (ii) asks a different question from route (i), which is why both are
   worth keeping: (i) is an analytic estimate, (ii) is a question about whether
   Jensen's lemma can be arranged to deliver an antisymmetric perturbation.

   ISABELLE NOTES:
   * THE TENDSTO ARROW MUST BE WRITTEN AS THE ESCAPE `\<longlongrightarrow>`.
     Typing the unicode arrow directly gives the BOOLEAN implication character,
     which looks nearly identical and fails with
     "Type unification failed: Clash of types _ => _ and bool". Only `old_text`
     needs unicode; the replacement `text` may (and for this arrow must) use
     escapes.
   * Rewriting inside a tendsto lambda: proving the pointwise NUMERATOR identity
     and then `using expPsi by simp` does NOT work (simp will not push it under
     the lambda). State the identity for the whole QUOTIENT as `eq ... for k`
     and close with `unfolding eq by (rule expPsi)`. Same trap as recorded for
     doubled_jet_slice_fst.

   **THE PROJECT ALREADY PROVES THE COMPACTNESS INPUT AND THEN DISCARDS IT.**
   Comparison_Assembly.thy:

     hessian_lower_bound_of_psd:   (ALL v. 0 <= v . B v)
                                     ==> -(c*|k|^2) <= k . (B k - c *R k)
     semiconvex_hessian_two_sided: -(c*|k|^2) <= k . W k <= 0
     semiconvex_hessian_abs_bound: |k . W k| <= c*|k|^2

   THE FINDING. `convex_alexandrov` (Sup_Convolution.thy) delivers a Hessian B
   WITH the clause `ALL k. 0 <= k . B k` - it is right there in the statement.
   Its corollary `semiconvex_alexandrov` obtains exactly that B, sets
   W = (%w. B w - c *R w), and then states its conclusion WITHOUT the psd
   clause. Since `k . (B k - c *R k) = k . B k - c*|k|^2`, the discarded clause
   is ONE REWRITE from the lower bound `-c*|k|^2 <= k . W k`.

   Combined with `k . W k <= 0` from `second_order_interior_max`, the Hessian at
   a maximum of a semiconvex function is pinned between -c and 0 in the
   quadratic-form order. That is exactly the compactness input route (i) was
   missing, and it costs nothing to recover.

   **DONE THIS TURN** (Sup_Convolution.thy:5294):

     corollary semiconvex_alexandrov_bounded:
       convex_on UNIV (%x. u x + (c/2)*|x|^2)
         ==> negligible {y. ~ (EX p B. bounded_linear B /\ B symmetric
               /\ (ALL k. -(c*|k|^2) <= k . B k)
               /\ Alexandrov jet of u at y with data (p,B))}

   i.e. the same statement as `semiconvex_alexandrov` but PROPAGATING the psd
   clause. Added as a separate corollary rather than by editing the existing
   one, so no downstream user is disturbed. Sup_Convolution.thy is now 7509
   lines; PIDE reports it ok with 14634 commands and the batch build is green.

   That removes the last STRUCTURAL gap on route (i). What remains there is the
   genuinely analytic step of turning boundedness into a limit point.

   GENERAL LESSON worth carrying: a corollary that specialises a theorem can
   silently drop a clause its own proof establishes. When a downstream argument
   seems to need a new estimate, check whether an UPSTREAM statement already
   proves it and the intermediate corollary just failed to propagate it.

   **THE QUADRATIC-FORM BOUND IS NOW A GENUINE OPERATOR BOUND - NO SPECTRAL
   THEORY.** Comparison_Assembly.thy:

     polarization_symmetric:  4*(u . W v) = (u+v).W(u+v) - (u-v).W(u-v)
     parallelogram_norm:      |u+v|^2 + |u-v|^2 = 2|u|^2 + 2|v|^2
     symmetric_form_bound:    |k . W k| <= c|k|^2 for all k
                                ==> |u . W v| <= c*(|u|^2 + |v|^2)/2
     symmetric_form_bound_unit: ... and |u| = |v| = 1 ==> |u . W v| <= c

   WHY THIS MATTERS. The two-sided Hessian bound proved last turn controls only
   the DIAGONAL k . W k. Compactness needs the whole operator. The textbook
   route is "for a symmetric operator the norm is the sup of the quadratic
   form", which is SPECTRAL and unavailable here (no spectral theorem in this
   HOL-Analysis - see the library-gap note near the top of this file).

   It is not needed. POLARISATION recovers the off-diagonal entries from the
   diagonal ones by pure algebra, and the parallelogram law converts the
   estimate into a bound uniform over the unit sphere. So the Hessians at the
   doubled maxima are bounded ENTRYWISE by the semiconvexity constant,
   uniformly in the tilt - exactly what Bolzano-Weierstrass consumes.

   This is the FOURTH time in this development that an elementary argument has
   replaced a spectral one (the others: the sup-convolution dominance property
   removing subsequence extraction from the epsilon-limit;
   `second_order_form_unique` removing the A + eps*A^2 perturbation; the
   explicit O(1/alpha) constant in `doubling_dist_bound` removing compactness
   of K). The pattern is now reliable enough to try FIRST: when a step seems to
   need spectral machinery, look for a polarisation / explicit-constant /
   exact-identity route before concluding the library is inadequate.

   **THE COMPACTNESS STEP IS NOW WRITTEN; THE LIMIT POINT IS PRODUCED.**
   Comparison_Assembly.thy:

     bounded_seq_limit_point:
       (ALL i. norm (Z i) <= B)  ==>  EX Z0 r. strict_mono r /\ Z o r ---> Z0
     nearby_of_convergent:
       Z ---> Z0, P holds along Z, 0 < e  ==>  EX z. dist z Z0 < e /\ P z
     nearby_of_bounded_family:
       bounded family with P holding along it
         ==>  EX Z0. ALL e>0. EX z. dist z Z0 < e /\ P z

   Short, because the operator bound made it available: the perturbed data live
   in a ball of a FINITE-DIMENSIONAL space, `cball` is compact, and compactness
   is sequential compactness in a metric space. Stated for an arbitrary
   euclidean space, so it covers the PAIR (gradient, Hessian) at once - same
   `prod is euclidean_space` instance the doubled functional uses.
   `nearby_of_convergent` is stated for an arbitrary predicate P, so one lemma
   serves both the sub- and the supersolution side.

   WHAT THIS DOES NOT SETTLE, stated precisely so it is not mistaken for done:
   the limit point is produced, but the closing argument also needs, AT THE
   LIMIT, the ordering X <= Y, symmetry of both matrices, and p ~= 0. Symmetry
   and the ordering are CLOSED conditions and pass to the limit. `p ~= 0` is NOT
   closed and needs a positive lower bound on |p| along the family. That is now
   the single remaining analytic requirement on route (i).

   ISABELLE NOTE: `bounded_seq_limit_point[OF bnd]` inside an `obtain` unifies
   Z with the higher-order pattern `%i. Z (?f i)` and the `obtain` then fails to
   apply. Pin with `[where Z = Z and B = B, OF bnd]`.

   **THE LAST ANALYTIC REQUIREMENT ON ROUTE (i) IS PROVED.**
   Comparison_Assembly.thy:

     doubling_grad_lower_bound:
       (xh,yh) maximises Phi over K x K, z in K, 0 <= alpha,
       u xh - w xh + gamma <= u z - w z      [xh misses the max by gamma]
       w Lipschitz on K with constant Lw > 0
         ==> gamma / Lw <= norm (xh - yh)
     doubling_grad_norm_lower_bound:
       same with 0 < alpha ==> alpha*(gamma/Lw) <= norm (alpha *R (xh - yh))

   THE MECHANISM, which is NOT the same as `doubling_grad_nonzero`. Comparing
   Phi at (xh,yh) against the diagonal point z gives

       gamma + (alpha/2)|xh-yh|^2  <=  w xh - w yh,

   so a gap in the VALUE of u - w forces a gap in w between the two components;
   a modulus of continuity then converts that into a gap in POSITION. For
   Lipschitz w the conversion is exact and the bound gamma/Lw is INDEPENDENT OF
   alpha. Note the penalty term appears on the left with a positive sign, so
   discarding it only weakens the conclusion - the penalty helps here.

   This is what makes `p ~= 0` survive the passage to the limit:
   `doubling_grad_nonzero` gives nonvanishing at each member of the family,
   which is not a closed condition; the bound above gives a POSITIVE LOWER
   BOUND uniform along the family, which is.

   STATUS OF ROUTE (i): every step is now proved -
     operator bound (polarisation) -> boundedness -> limit point
     (bounded_seq_limit_point) -> nearby points (nearby_of_bounded_family)
     -> envelopes (ell_op_lsc_le_of_nearby) -> contradiction
     (env_strict_contradiction_of_nearby), with p ~= 0 preserved by
     doubling_grad_norm_lower_bound.
   What is NOT written is the single theorem threading them with matching
   instantiations, and the verification that the ordering and symmetry pass to
   the limit (both closed conditions, so expected to be routine - but this
   session has repeatedly found that "expected routine" steps are not).

   ISABELLE NOTE: `norm (alpha *R v) = alpha * norm v` for `0 < alpha` must be
   proved via `norm_scaleR` and then `unfolding (abs_of_pos)`; doing it with
   `simp` leaves `¦alpha¦` in the GOAL and simp then splits on
   `xh = yh | ¦alpha¦ = alpha`. Avoid simp on goals containing `norm (a *R v)`.

   **THE CLOSED CONDITIONS NOW PROVABLY PASS TO THE LIMIT.**
   Comparison_Assembly.thy:

     tendsto_entry:           convergence in real^'n^'n is entrywise
     transpose_limit:         symmetry survives a limit
     tendsto_quadratic_form:  x . (A i *v x) ---> x . (A0 *v x)
     psd_limit:               psd survives a limit
     psd_diff_limit:          psd (Y i - X i) ==> psd (Y0 - X0)

   All proved entrywise: convergence in real^'n^'n is convergence of every entry
   (`tendsto_vec_nth` applied twice), and symmetry and positive semidefiniteness
   are each preserved by limits of reals. No spectral input.

   ROUTE (i) IS NOW COMPLETE AS A CHAIN OF PROVED LEMMAS:
     polarisation -> operator bound (symmetric_form_bound)
     -> boundedness -> limit point (bounded_seq_limit_point)
     -> nearby points (nearby_of_bounded_family)
     -> envelopes (ell_op_lsc_le_of_nearby / ell_op_usc_ge_of_nearby)
     -> contradiction (env_strict_contradiction_of_nearby)
   with the three side conditions at the limit supplied by
   `transpose_limit`, `psd_diff_limit` and `doubling_grad_norm_lower_bound`.
   What is still not written is the single theorem threading them with matching
   instantiations.

   ISABELLE NOTES:
   * `LIMSEQ_le_const` takes its second premise in the form
     `EX N. ALL n>=N. a <= X n`, so `using nn by (rule LIMSEQ_le_const)` FAILS
     when nn is a plain pointwise fact. Use
     `by (rule LIMSEQ_le_const) (use nn in blast)`.
   * Nested `proof (unfold vec_eq_iff, intro allI)` for a matrix equality gives
     "Failed to refine any pending goal" at the inner `qed`. One
     `by (simp add: vec_eq_iff transpose_def <entry equation>)` does the whole
     thing; the permutative entry equation is oriented by simp without looping.

   **ROUTE (i) IS THREADED. The single theorem exists.**
   Comparison_Assembly.thy:

     env_strict_contradiction_of_limits:
       X ---> X0, Y ---> Y0, Pu ---> p, Pw ---> p,
       transpose (X i) = X i, transpose (Y i) = Y i, psd (Y i - X i)  [ALONG
         the sequence only],
       p ~= 0  [at the limit],
       1<=k<CARD('n), 1<=L, c < 1,
       ell_op k L (Pu i) (X i) <= c,  1 <= ell_op k L (Pw i) (Y i)
         ==> False

   Everything is supplied as SEQUENCES of perturbed data - which is what
   re-running Jensen with a shrinking tilt produces - together with their
   limits. Symmetry and the ordering are required only ALONG the sequence;
   `transpose_limit` and `psd_diff_limit` carry them to the limit. Only p ~= 0
   is needed AT the limit, because it is the one non-closed condition, and
   `doubling_grad_norm_lower_bound` supplies it in the doubling setting.

   THE REMAINING HYPOTHESIS TO DISCHARGE: the two gradient sequences must
   converge to the SAME p. That is the gradient alignment, and it is exactly
   where the tilt must have been dealt with - by the linear rate (route (i)) or
   by antisymmetry (route (ii)). Everything else in route (i) is now proved and
   threaded.

   ISABELLE NOTES:
   * `[where Z = ... and Z0 = ...]` on `nearby_of_convergent` misbound the
     variables and gave "Clash of types _ x _ and _ => _". Pin ONLY the
     higher-order variable (`where P = ...`) and let `OF` determine the rest.
   * The PIDE `edit` tool found TWO matches for old_text "end" near the end of
     the file: the final `end` and the "end" inside "t-end-sto_diff". When
     appending before the closing `end`, restrict start_line/end_line to the
     last line rather than relying on uniqueness.

   **THE GRADIENT ALIGNMENT IS DISCHARGED. Route (i) has no open hypothesis
   that is not supplied by the doubling.** Comparison_Assembly.thy:

     tendsto_of_norm_bound:  norm (Z i) <= D i, D ---> 0  ==>  Z ---> 0
     gradient_sequences_align:
       Pt ---> 0, G ---> g
         ==> (%i. - fst (Pt i) + G i) ---> g
         and (%i.   snd (Pt i) + G i) ---> g
     gradient_sequences_align_of_bound:  same, with the tilts bounded by
       dd i ---> 0, which is what re-running Jensen supplies

   WHY THE ALIGNMENT IS FREE. With tilt p_i the jet of the untilted functional
   has gradient -p_i (`gradient_is_minus_tilt`), so the two block gradients are
     -fst p_i + alpha*(xh_i - yh_i)   and   snd p_i + alpha*(xh_i - yh_i).
   Their DIFFERENCE is fst p_i + snd p_i, bounded by the TILT ALONE - the
   maximiser does not appear in it. So once the tilts vanish the two sequences
   share a limit whatever the maximisers do, provided only that the penalty
   gradients converge.

   That is the point that makes route (i) work: it needs the tilt to shrink but
   NOT the maximisers to be controlled. The linear-rate estimate I spent two
   turns isolating (`nearby_of_tilt_family`) is therefore NOT needed for the
   alignment - only for locating the limit point, where boundedness plus
   Bolzano-Weierstrass already suffices.

   **THE DIAGONAL STEP IS WRITTEN: BOTH LIMITS AT ONCE.**
   Comparison_Assembly.thy:

     nearby_of_convergent_shifted:
       (%i. (Pz i, Mz i)) ---> Z0,  Q (Pz i) (Mz i + delta*I) for 0<delta<D
         ==> EX p' M'. dist (p',M') Z0 < e /\ Q p' M'
     env_strict_contradiction_of_shifted_limits:
       the full contradiction from bounds at the DELTA-CORRECTED matrices along
       a sequence of tilts - which is exactly what the doubling delivers

   WHY A SEPARATE STEP WAS NEEDED. `env_strict_contradiction_of_limits` wants
   the operator bound AT X_i, but `subsol_shifted_bound_supconv` only ever
   delivers it at X_i + delta*I. Two limits (i -> infinity and delta -> 0) have
   to be taken together. The nearby-point formulation makes it painless: choose
   i so the pair is within e/2 of the limit, then delta so the shift costs less
   than e/2. NO relation between i and delta is needed, because the shift bound
   is independent of i.

   ISABELLE NOTE (cost one rewrite of the whole block): take the predicate
   CURRIED, as `Q p' M'`, not uncurried as `P (p', M')`. With an uncurried
   predicate the instantiated hypothesis arrives as
   `P (fst (Z i), snd (Z i) + delta*I)` with the projections UNREDUCED, and `OF`
   then reports "no unifiers" against the natural statement of the bound. The
   curried form also makes the conclusion match
   `env_strict_contradiction_of_nearby` directly, so the two `obtain`/`intro
   exI` blocks disappear entirely.

   **SIGN CORRECTION: THE TWO CORRECTIONS RUN IN OPPOSITE DIRECTIONS.**
   Comparison_Assembly.thy:

     nearby_of_convergent_shifted_neg:  the mirror of the diagonal step, for
       the shift Mz i - delta*I
     env_strict_contradiction_of_shifted_limits:  RESTATED with
       1 <= ell_op k L (Pw i) (Y i - delta*I)   on the supersolution side

   As first written, that theorem asked for the supersolution bound at
   `Y i + delta*I`. That is WRONG and would not have been supplied by anything:
   `supersol_shifted_bound_supconv` delivers `1 <= ell_op k L p (Ym - delta*I)`,
   with the correction running the OTHER WAY - which is the whole point of the
   `+delta*I` / `-delta*I` asymmetry recorded with `jet_imp_local_min_test`.
   The estimate in the diagonal step is unaffected (the shift has the same norm
   either way), so the mirror lemma is the same proof with the sign flipped.

   Worth noting how this was caught: not by the checker (the theorem was green,
   because a hypothesis nothing supplies is still a valid hypothesis) but by
   trying to DISCHARGE the hypothesis from the lemma that was meant to supply
   it. Green statements with unsuppliable hypotheses are the failure mode this
   file has flagged repeatedly; the only reliable detector is composition.

   **PHASE E: THEOREM 4.2(a) NOW CLOSES FROM A SEQUENCE OF SUP-CONVOLUTION
   JETS.** Comparison_Assembly.thy:

     comparison_supconv_sequence_complete:
       visc_subsol k L Omega u, visc_supersol k L Omega w, 0<theta<1,
       1<=k<CARD('n), 1<=L, 0<eps, theta*u and -w bounded above,
       ysu i, ysw i in Omega,  X i, Y i symmetric,  psd (Y i - X i),
       both sup-convolutions ATTAINED at ysu i / ysw i,
       their two jets at xu i / xw i with data (Pu i, X i) and (-Pw i, -Y i),
       X ---> X0, Y ---> Y0, Pu ---> p, Pw ---> p, p ~= 0
         ==> False

   Everything is indexed by i, the index of the Jensen application: each i
   supplies a maximiser, its jet, and the attaining point. Per-index operator
   bounds come from `subsol_shifted_bound_supconv` /
   `supersol_shifted_bound_supconv`; `env_strict_contradiction_of_shifted_limits`
   takes both limits (i -> infinity and delta -> 0) together.

   WHAT IS NOT ASSUMED: nothing about how the sequence was produced, no rate,
   no relation between i and the correction delta. The four convergence
   hypotheses are exactly what the boundedness results
   (`bounded_seq_limit_point` via `symmetric_form_bound`) and
   `gradient_sequences_align_of_bound` supply.

   WORKFLOW RULE (user instruction, 2026-07-31): do NOT run `isabelle build`
   after every small change. Once the PIDE buffer is synced, `edit` ->
   `get_progress` IS the verification loop; `overall_status: ok` with
   `commands_failed: 0` at 100% is a check, in seconds rather than ~80 s.
   Reserve the batch build for a final confirmation, for reading actual error
   text when something fails, and after edits made outside the MCP tools.

   **STRUCTURAL FINDING: Theorem_1_1.thy EXISTS, AND PHASE E WAS NOT CONNECTED
   TO IT.** Theorem_1_1.thy (66 lines) has been in ROOT all along, holding
   `theorem_1_1_ball_fragment` and a header that names the THREE missing pieces:
     (1) usc of v and the viscosity property (Prop 2.4 via Lemmas 2.2/2.3),
     (2) the lower bound ball_v <= v at interior points (Section 3.1 martingale
         construction, needs weak existence for Eq. (3.11)),
     (3) general compact K -- "Theorem 4.2(a), behind Crandall-Ishii".

   Item (3) is exactly what this whole Phase E effort addresses. But
   Theorem_1_1 did NOT import Comparison_Assembly, so none of it was visible at
   the assembly point.

   FIXED THIS TURN: `Comparison_Assembly` added to Theorem_1_1's imports. The
   build is green, so the feared diamond does not bite. Theorem_1_1's header now
   records what Comparison_Assembly supplies and what still blocks item (3).

   WHAT STILL BLOCKS GENERAL K is therefore NOT the Crandall-Ishii analysis -
   that runs end to end to `comparison_supconv_sequence_complete` - but the
   CONSTRUCTION feeding it: producing the indexed family (doubled maximiser,
   Alexandrov jet, sup-convolution attaining point) from the doubling of
   theta*u against w on K x K with a shrinking Jensen tilt. The existence
   ingredients are all proved (`doubling_maximiser_exists`, `doubling_complete`,
   `doubled_supconv_jet_exists`); what is missing is their instantiation as one
   indexed family.

   LESSON: I spent this entire session extending Comparison_Assembly without
   checking whether the assembly point could see it. Before deepening a
   development, check that the theory naming the goal actually imports it -
   `grep -n imports <goal theory>.thy` is the whole check.

   **THE SHRINKING TILT IS ALWAYS AVAILABLE.** Comparison_Assembly.thy:

     jensen_tilt_threshold_pos:  m < Psixi, 0 < r ==> 0 < (Psixi-m)/(2r)
     jensen_tilt_small_enough:   dd < (Psixi-m)/(2r) ==> 2*dd*r < Psixi - m
     tilt_sequence_pos / _lt / _tendsto / tilt_sequence_admissible:
       D/(2 + real i) is a concrete admissible tilt sequence: positive,
       below D, and converging to 0

   So "re-run Jensen with a smaller tilt" is NOT an extra hypothesis to be
   discharged later. Jensen's smallness condition `2*dd*r < Phi(xi) - m` holds
   for EVERY sufficiently small tilt as soon as the centre beats the boundary
   value at all, and an explicit admissible sequence exists. This is the input
   `gradient_sequences_align_of_bound` needs.

   WORKFLOW NOTE: `get_state` on a line range returns the ACTUAL goal and error
   text, not just counts - so the batch build is not needed for diagnosis
   either. Correcting the note above: reserve `isabelle build` for a final
   confirmation and for edits made outside the MCP tools; use
   `get_progress` for the pass/fail check and `get_state` (with
   start_line/end_line and a small commands_limit) to read the failing goal.

   ISABELLE NOTES:
   * `D/(2 + real i) < D` is NOT closed by `field_simps` even with
     `0 <= D * real i` in scope - the residual `0 < D + D*real i` is left and
     simp will not use the product fact. Use
     `divide_strict_left_mono[OF den D]` against `D / 1` instead.
   * A `shows A and (!!x. P x ==> Q x)` lemma proved by `show`, then `fix`,
     `assume`, `show` inside one `proof -` block is fragile; splitting into two
     lemmas is both shorter and more robust.

   **THE SUP-CONVOLUTION IS ATTAINED - the last unsupplied hypothesis class.**
   Comparison_Assembly.thy:

     supconv_attained:
       u bounded above by Bu, 0 < eps, u continuous on UNIV
         ==> EX ys. supconv u eps x = u ys - dist(x,ys)^2/(2*eps)

   `comparison_supconv_sequence_complete` takes the attaining points ys as
   hypotheses (`optu`, `optw`) and nothing in the project produced them - the
   same gap class flagged repeatedly in this file.

   PROOF IS BY COERCIVITY WITH AN EXPLICIT RADIUS. Beyond
   R = sqrt (max 0 (2*eps*(Bu - u x))) + 1 the penalty already pushes the
   competitor strictly below the value at x itself, so the supremum over the
   whole space equals the supremum over the single compact ball cball x R,
   where continuity attains it. No compactness of the domain, no diagonal
   argument, no subsequence - the radius is computed from the data.

   That is the FIFTH time an explicit-constant argument has replaced a soft one
   in this development (see the polarisation entry for the list). The pattern
   holds well enough that it should be the first thing tried.

   ISABELLE NOTES:
   * `0 <= sqrt M` is NOT closed by bare `simp` - it reduces to `0 <= M` and
     needs the nonnegativity fact in scope (`using M0 by simp`).
   * `continuous_intros` on `%y. u y - (dist x y)^2/(2*eps)` leaves the side
     condition `ALL x:S. 2*eps ~= 0`; close it with `(use e in auto)` as a
     terminal method.

   **THE ATTAINING POINTS AS A FAMILY.** Comparison_Assembly.thy:

     supconv_attained_family:
       u bounded above, 0 < eps, u continuous
         ==> EX ys. ALL i. supconv u eps (xs i)
                            = u (ys i) - dist(xs i, ys i)^2/(2*eps)

   Countable choice over `supconv_attained`; no uniformity in i is needed
   because the attainment at each base point is unconditional. This is the
   `optu`/`optw` input of `comparison_supconv_sequence_complete` in the form it
   consumes.

   REMAINING FOR E6, precisely: the analogous family construction for the JETS
   - i.e. running `doubled_supconv_jet_exists` at each tilt `dd i` and choosing
   (zh i, q i, W i) simultaneously - and then reading off X i, Y i, Pu i, Pw i
   from the block decomposition. The pattern is the same countable choice used
   above, but the existential there has four components and the conclusion is
   the long jet statement, so it is bookkeeping of some size rather than a
   one-liner.

   **SKOLEMISATION OVER AN INDEX.** Comparison_Assembly.thy:

     choice2 / choice3 / choice4:
       (!!i. EX a b [c [d]]. P i a b [c [d]])
         ==> EX A B [C [D]]. ALL i. P i (A i) (B i) [(C i) [(D i)]]

   `doubled_supconv_jet_exists` produces FOUR objects at once (maximiser, tilt,
   gradient, Hessian), so plain `choice` does not apply to it directly. These
   are pure skolemisation, nothing to do with the doubling, and each is closed
   by `metis`.

   Recorded separately because the shape recurs: every "run the construction at
   each index and collect the results into sequences" step in this development
   needs one of these.

   WHAT IS LEFT for the E6 family construction is now purely the instantiation:
   apply `choice4` to `doubled_supconv_jet_exists` at tilt `dd i`, then read off
   X i, Y i, Pu i, Pw i from the block decomposition (`doubled_jet_slices_at_max`
   plus the block-matrix lemmas). Long but mechanical; every ingredient is
   proved.

   **THE FAMILY CONSTRUCTION, ABSTRACTED.** Comparison_Assembly.thy:

     family_of_tilt_construction:
       (!!dd. 0 < dd ==> dd < D ==> EX zh p q W. Q dd zh p q W),
       0 < ddf i, ddf i < D
         ==> EX zh p q W. ALL i. Q (ddf i) (zh i) (p i) (q i) (W i)
     family_of_tilt_construction_shrinking:
       ... with the concrete tilt sequence D/(2 + real i), which ALSO returns
       its convergence to 0

   ABSTRACTING OVER Q WAS THE RIGHT MOVE. The conclusion of
   `doubled_supconv_jet_exists` is some fifteen lines of jet statement;
   transcribing it into a family theorem would be fifteen lines of
   transcription with fifteen chances to mistype a subscript. Abstracted, the
   step is four lines and applies verbatim, with `Q dd zh p q W` read as
   "running the construction at tilt dd yields maximiser zh, tilt vector p,
   gradient q and Hessian W".

   The shrinking variant returns the tilt convergence alongside the family,
   which is exactly what `gradient_sequences_align_of_bound` consumes to align
   the two gradient sequences - closing the alignment hypothesis of
   `env_strict_contradiction_of_shifted_limits`.

   **A CONCRETE STARTING POINT FOR THE A-SIDE (read this before starting A4).**
   Read of Value_Function.thy and Relative_Arbitrage_Stochastic.thy this turn:

     val_fn k L K x0 = Sup (mkt_exit_vals k L K x0)
     mkt_exit_vals k L K x0 = {ess_inf_time M tau | there is a market
        (M,F,X,acov,tau) with sufficiently_volatile_market ... k L K x0 tau}

   and the locale `sufficiently_volatile_market` (Relative_Arbitrage_Stochastic.thy:93)
   has fourteen assumptions, of which K OCCURS IN EXACTLY ONE:

     X_in_K: "AE w in M. ALL s. 0 <= s --> s <= tau w --> X s w : K"

   CONSEQUENCE, and this is the first A-side lemma to write: K <= K' implies
   `sufficiently_volatile_market ... K ... ==> sufficiently_volatile_market
   ... K' ...` by re-interpreting the locale with X_in_K weakened (one
   `eventually_elim` step; every other assumption is reused verbatim). Hence
   `mkt_exit_vals k L K x0 <= mkt_exit_vals k L K' x0` and so

     val_fn k L K x0 <= val_fn k L K' x0.

   That is MONOTONICITY OF THE VALUE FUNCTION IN THE DOMAIN, which the project
   does not have and which the DPP work will need repeatedly. It is small, and
   it does not depend on any of the Section 2 machinery.

   NOTE ON WHERE IT GOES: Value_Function.thy is in the probabilistic chain and
   is NOT currently PIDE-loaded, so verify it with `isabelle build` (this is the
   "edits outside the MCP tools" case of the workflow rule) rather than trying
   to load that chain into PIDE, which has OOMed before.

   What remains of E6 is to actually run `comparison_contradiction` in that
   envelope setting: apply `superjet_local_max` at `X + delta*I` and
   `Y - delta*I`, use `doubling_env_forms` to land in `visc_*_env`, and let
   `ell_op_lsc_at_zero` / the sandwich remove `delta`.

   **OBLIGATION IDENTIFIED, AND NOW DISCHARGED.** The envelope route needs
   MONOTONICITY OF THE ENVELOPES in the matrix argument, i.e. the analogue of
   `ell_op_elliptic_le` for `ell_op_lsc` / `ell_op_usc`. This is NOT immediate
   from `ell_op_elliptic_le`, because
   `ell_op_lsc k L p M = (SUP e>0. INF w : ball (p,M) e. ell_op_pair k L w)`
   takes the infimum over a ball in the PRODUCT variable `(p,M)`, so shifting
   `M` moves the ball as well as the integrand, and the pointwise ellipticity
   does not transfer termwise.

   (Warning for the reader: `ell_op_usc_elliptic_le` in Lemma_3_1_Envelopes.thy
   is MISNAMED. Despite the name it is a statement about `ell_op`, not about
   `ell_op_usc`; it is just `ell_op_elliptic_le` with the `k`/`L` hypotheses
   packaged in place of the nonemptiness side condition. Before this turn there
   was no envelope-level ellipticity anywhere in the project.)

   Route taken (route (a) of the two considered): translate the ball. The key
   observation is that the ball moves by a TRANSLATION, and the translation is
   by exactly `(0, N - M)`, which is precisely the increment the pointwise
   ellipticity consumes. `ball_prod_shift_snd` proves
   `w : ball (p,M) e ==> w + (0, N-M) : ball (p,N) e`, since the two difference
   vectors literally coincide; `ell_op_pair_shift_snd_le` proves the integrand
   only decreases along that bijection. Then `INF_mono` / `SUP_mono` at a fixed
   radius, and `SUP_mono` / `INF_mono` over the radius, give:

     theorem ell_op_lsc_elliptic_le:
       psd (N - M) ==> 1 <= k ==> k < CARD('n) ==> 1 <= L
         ==> ell_op_lsc k L p N <= ell_op_lsc k L p M

     theorem ell_op_usc_envelope_elliptic_le:
       psd (N - M) ==> 1 <= k ==> k < CARD('n) ==> 1 <= L
         ==> ell_op_usc k L p N <= ell_op_usc k L p M

   Both in Comparison_Assembly.thy, batch-verified. Note the ellipticity has to
   be applied at the PERTURBED gradient `fst w`, not at `p`, which is why the
   `k`/`L` form is the one needed: it supplies nonemptiness of `feasible k L q`
   uniformly in `q` rather than at a single `p`. This is the reason route (b)
   (keeping the ordering step envelope-free) turned out to be unnecessary.

   ALSO NOTE: `visc_subsol_env` requires a GLOBAL max over `K` (not a local one
   on a ball), so the doubling maximum has to be produced globally on `K` —
   which is what `doubling_partial_max_fst` / `doubling_partial_min_snd` already
   give when the joint maximum is taken over `K x K`.

   What is left is the instantiation: apply `doubled_functional_semiconvex` +
   `semiconvex_jensen_alexandrov_point` + `second_order_interior_max` +
   `sums_matrix_inequality` to the regularised frozen problem, then move the
   jets back with `supconv_jet_transfer` / `supconv_neg_jet_transfer`.

   What remains for E6: doubling + the two jets +
   `ell_op_elliptic_le` gives `1 <= ell_op ... Y <= ell_op ... X <= 1` at a
   strictly interior maximum, the contradiction; then
   `max_principle_boundary_intro` (`Lemma_3_1_Envelopes.thy`) discharges the
   interface and everything downstream (4.2(b), Thm 4.3, Prop 4.1) becomes
   unconditional.

## Phase F — Section 5 (Props 5.1, 5.2)

Continuity of `v`: both go through the DPP (C4) plus barrier/comparison
arguments already available (ball case unconditional; Lem 5.3's
deterministic core `eigen_lb_dim_obstruction` done). Medium, after C.

## Phase G — assembly

Grow `theorem_1_1_ball_fragment` into Theorem 1.1: instantiate the
uniqueness clause at `u = v` using D (viscosity property), C1 (usc), F
(continuity where the statement needs it), and Example 3.1 (done) for the
identification with `ball_v`; general `K` additionally via E. The theory
header of `Theorem_1_1.thy` tracks exactly which clause consumes which
phase.

# Library availability (audited — trust this, don't re-search)

AVAILABLE and load-bearing: Kolmogorov-Chentsov criterion (AFP
`Kolmogorov_Chentsov`, but its main theory clashes with `Martingales` —
only `Dyadic_Interval`/`Holder_Continuous`/`_Extras` co-import);
Arzela-Ascoli (`HOL-Complex_Analysis.Great_Picard`); Prokhorov + weak
convergence + Levy-Prokhorov metric (AFP `Levy_Prokhorov_Metric`:
`Prokhorov_theorem_LP`, `tight_on_set_imp_convergent_subsequence`,
`metrizable_weak_conv_topology`); `cfunspace` Polishness (HOL-Analysis
`mcomplete_cfunspace` + AFP `Standard_Borel_Spaces`
`separable_space_cfunspace`, `continuous_map_measurable`, `borel_of_*`);
Daniell-Kolmogorov (`HOL-Probability.Projective_Limit`); disintegration
(AFP `Disintegration`); diagonal subsequences
(`HOL-Library.Diagonal_Subsequence`, reachable via HOL-Probability);
Riesz-Fischer's hard half (`cauchy_L1_AE_cauchy_subseq`,
HOL-Analysis Set_Integral:1473).

MISSING entirely (searched distribution + all AFP): Burkholder-Davis-Gundy
(NOT needed — Eq. (2.7) was proved with constant `8C^2` without it);
Doob-Meyer (NOT needed — covariation is data); Ito for general C^2 (NOT
needed for 2.2; D2 needs only weak SDE existence); measurable selection
(C3 — must build); Skorokhod representation beyond 1-D (B1 — building);
Vitali convergence (BUILT: `Vitali_Convergence.thy`); uniform integrability
(BUILT: same); coupling/Wasserstein (rejected route); viscosity solutions /
Alexandrov / Rademacher (E — must build); `nlinarith` (dev snapshot lacks
it — use `linarith` + explicit monotonicity).

# Archive of completed work (compressed; details in STATUS_ARCHIVE)

**Eigenvalue/PDE line** (all green): `Eigenvalues.thy` (Ky Fan sums,
ordered `eigval`, `possum`, `bracket`); `Eigenvalue_Continuity.thy`
(`kyfan_lipschitz`, `eigval_lipschitz`, `entrysum_le_norm` — NOTE this
lemma exists at Poincare_Separation:3546 too; a duplicate broke a build);
`Threshold_Chain.thy`; `Poincare_Separation.thy` (Courant-Fischer
`eigval_ge_of_subspace`, general Poincare separation, Frobenius kit,
`Mp_lipschitz_away_from_zero`, `ell_op_lipschitz_in_p`, Eq. (3.5)
`ell_op_eq_half_bracket` via the box-program chain + `bracket_attained`
witness, Lem 5.3 core `eigen_lb_dim_obstruction`, `feasible_iff_eigval`,
and the NEW closedness kit `closed_feasible` etc.); `Lemma_3_1*.thy` +
`Envelopes.thy` (Eq. (3.4), Eq. (3.6) `eq36`, all of Lemma 3.1 —
`ell_op_envelopes_eq_off_zero`); `Relative_Arbitrage_Convexity.thy`
(convexity of the feasible set); `Relative_Arbitrage_Comparison.thy`
(Route 1 smooth-strict maximum principle `visc_subsol_le_smooth_strict`;
Route 2 unconditional ball chain `comparison_ball`, `uniqueness_ball`,
`ball_v_unique_solution_smooth`; `feasible_bounded`,
`feasible_offdiag_abs_le`); `Lemma_3_1_Envelopes.thy` (Route 3: the
`max_principle_boundary` interface chain, degenerate ellipticity at the
infimum, `feasible_trace_bound`, `ell_op_ball_bound`).

**Brownian/martingale line** (all green): `Brownian_Motion*.thy`,
`Brownian_Continuous.thy` (construction); `Quadratic_Variation.thy`,
`Optional_Sampling.thy`, `Doob_Inequality.thy` (incl.
`horizon_sq_int_martingale` with the `Dsup` dominating-function kit —
this is what makes optional stopping free for L2 martingales);
`Exit_Time.thy` (`etime_stopping_time`, `etime_stays_in_cball`);
`Ito_Market.thy` + instances (`Brownian_Exit.thy`,
`Random_Walk_Market.thy`); `Sampled_Martingale.thy`
(`martingale_sampled` — the sampling bridge that transfers ALL discrete
theory to continuous time along partitions),
`Sampled_Quadratic_Variation.thy` (quadratic Ito + energy identity along
partitions, `cond_exp_increment_sq`); `Ito_Covariation.thy`
(`Z_martingale_of_cond_covariation` — `Z_martingale` REDUCED to the paper's
defining covariation hypothesis; additive change, no locale surgery);
`Stochastic_Integral_Simple.thy` (simple integral = `mtrans` of the sampled
process; martingale property, L2, Ito isometry,
`compensated_square_decomposition`); `L2_Limits.thy` (Riesz-Fischer via
AM-GM, no Cauchy-Schwarz); `Stochastic_Integral_L2.thy`
(`simple_itg_L2_closure`). Established NON-needs: Doob-Meyer (covariation
is data — `acov` is a free locale parameter, `Z_martingale` is not
derivable and should not be), general C^2 Ito.

**Section 2 line** (all green): `Moment_Bounds.thy`
(`fourth_moment_of_compensated`); `Increment_Moments.thy` (Eq. (2.7): the
partition bound with explicit remainder `fourth_moment_partition_bound`
(const `8C^2` vs paper's `66C^2`, NO BDG), the four a2-lim steps,
`remainder_tendsto_zero`, `fourth_moment_bound_bounded`,
`weighted_interval_bound`, `sum_sq_squared_bound`, `upart` kit,
`expectation_cond_exp`, pointwise + integrability kits);
`Increment_Tails.thy` (Markov at the 4th power, per-level union bound);
`Dyadic_Chaining.thy` (deterministic `dyadic_chaining` UNIFORM in the
level — what the AFP KC entry does not provide — and
`dyadic_modulus_extension`); `Modulus_Tails.thy`
(`dyadic_bad_event_tail_mom` — abstract Eq. (2.7) package only —
`modulus_of_good_path`, `powr_ratio_lt_1`); `Conditional_UI.thy` (UI of
conditional-expectation families); `Stopped_Localization.thy` (A3:
`stopped_martingale_L2` with NO domination hypothesis via `Dsup`,
`stopped_compensated_square`, `stopped_covariation`, `fourth_moment_L2`
+ `_integrable`/`_bochner` — Eq. (2.7) for UNBOUNDED L2 martingales by
localization at ball exits + Fatou); `Section_2_Compactness.thy`
(Arzela-Ascoli step `holder_family_subsequence`);
`Vitali_Convergence.thy` (`unif_integrable`, `vitali_convergence`,
`unif_integrable_of_moment_bound`); `Measure_Continuity_Sets.thy` +
`Stacking_Intervals.thy` (Skorokhod layers 1-4); `Holder_Interpolation.thy`
(`holder_of_dyadic_moduli` with constant
`E*2 powr g + 2E*2^n*2 powr (-g n) * max 1 (T powr (1-g))`);
`Path_Space.thy` (path space Polish — separability via the AFP cfunspace
lemma, feared hard, was free; `compactin_path_holder_ball`;
`pathify_measurable` via countable rational time grids; `path_law`;
restriction maps 1-Lipschitz + `path_law_restrict`;
`weak_conv_on_pushforward`; `continuous_map_path_eval`;
`weak_conv_on_nn_integral_le`); `Path_Tightness.thy` (per-law Holder-ball
bound, `tight_on_set_path_laws(_vec)`,
`path_laws_convergent_subsequence(_vec)`, `path_laws_diagonal_subsequence`,
`path_laws_diagonal_consistent`); `Path_Tightness_Market.thy` (the
martingale-package form; BATCH-ONLY).

**Value function**: `Value_Function.thy` (`ess_inf_time` calculus C0,
`mkt_exit_vals`/`val_fn`, `val_fn_le_ball_v`, `val_fn_boundary`,
`mkt_exit_vals_nonempty`). `Theorem_1_1.thy` (ball fragment; BATCH-ONLY).

# Mathematical insights worth not rediscovering

- **`F` cannot see the antisymmetric part of `M`** (`ell_op_sym_part`) —
  lets symmetric-matrix results apply in balls around symmetric matrices.
- **The correction coefficient of `M_p` does not depend on `p`** — so `p`-
  and `M`-variations SEPARATE; no product-topology reasoning anywhere.
- **`rank1proj` depends only on the line through `p`** — the paper's lower
  bound sequence for Eq. (3.6) is constant in `m`.
- **The Lipschitz constant `4/|p|` for `rank1proj` blows up at 0** — that IS
  the discontinuity making Eq. (3.6) a different formula at the origin.
- **Poincare separation is an equality at a top eigenvector** — evaluating
  there gives Eq. (3.6)'s matching bound.
- **One feasible witness suffices for lower bounds on `F`** (it is an Inf);
  `bracket_attained` picks the threshold set inside `B - {q}` to annihilate
  `p`, possible exactly because `k >= 1`.
- **`eigen_lb a m <-> 1 <= eigval m a`** — converts the subspace existential
  into a condition on a Lipschitz function; this is what closedness
  (`closed_feasible`) and Lemma 2.3 rest on. WARNING: `kyfan_ge_of_eigen_lb`
  is NOT strong enough for step (A) of Eq. (3.5) — the fact needed is
  `eigval m a >= 1`.
- **A rank obstruction underlies Lemma 5.3**: degeneracy on `W` forces
  `m + dim W <= n`.
- **Eq. (2.7) without BDG**: expand `(Y+d)^4` along partitions; the mesh
  limit of `SUM E[d^4]` is the only genuinely continuous-time step, closed
  by the four a2-lim steps for bounded martingales, then localization for
  L2 ones. Constant `8C^2` (paper: `66C^2`).
- **`holder_on` quantifies its constant per function** — "every path
  Holder" does NOT give the common constant Arzela-Ascoli needs; the
  uniform fourth-moment package exists to produce it.
- **The paper's `P_x` covariation is DATA, not a theorem** — `Z_martingale`
  is the formal content of `d<X>/dt = a`; proving it from the rest would be
  circular.
- **The tail machinery needs only the abstract Eq. (2.7) package** — laws
  in Lemma 2.2 are unstopped and unbounded; localization bridges.
- **`sufficiently_volatile_market` fixes the sample type
  `('n => real => real) measure`** — fixed-type family statements fit `P_x`
  directly; no type quantification needed.

# PIDE MCP workflow (binding; re-read every session)

Source: `~/isabelle-pide-mcp/.claude/skills/{pide-mcp,isabelle-proof-development,isabelle-formalization}/SKILL.md`.

- NEVER edit a PIDE-held `.thy` outside MCP; if PIDE and disk disagree,
  re-`read` the file. PIDE red + batch green = stale buffer: re-read the
  PARENT, not the child.
- `get_state` after EVERY edit; clean = `commands_bad = 0` AND `errors = 0`
  AND `commands_failed = 0`. Add material incrementally.
- **`commands_still_running_possibly_nonterminating` is a STOP condition**,
  even with `timing_ms 0/1` and "No subgoals!" (stale first reading — poll
  twice). Restructure the proof; never run the batch build "to check".
  Confirmed diverging cases: `blast` on an `obtain` from a big existential;
  `blast` closing `space M = topspace X` from `sets_eq_imp_space_eq`;
  `auto` on a `sets M` goal; `blast`/`metis` on `obtains`-elimination.
- Never run two batch builds at once; never batch-build during a PIDE
  first-time heavy chain load (OOM host crash, 2026-07-28). Stop builds with
  TaskStop; NEVER `pkill poly` (that is the PIDE server).
- Chain co-residency: PIDE holds the Levy-Prokhorov+Standard_Borel chains
  TOGETHER with the Martingales/Increment chain (Path_Tightness works). It
  cannot hold Envelopes+Eigenvalues together. A theory whose imports form a
  DIAMOND over a local draft (Path_Tightness_Market, Theorem_1_1) cannot
  load into PIDE at all — batch-only, note it in the theory header.
- Find facts with `find_theorems`/`find_consts` (cheap, transitive imports
  only; grep the AFP for the rest). Close goals: one-shot guess -> `try0`
  -> `sledgehammer` (poll at 5/10 s; prefer `auto` > `fastforce` > `metis`
  > `smt`). Develop in `create_scratch` with the target's imports; copy back.
- `isabelle build` emits nothing until done; ROOT changes re-check the whole
  session; duration says nothing about looping; `timeout N isabelle build`
  kills the wrapper only.

# Trap catalog (each cost at least one debugging round)

## MCP editing

- `edit` needs `old_text` in UNICODE rendering (not `\<...>` escapes); its
  success echo returns the whole file — read outcomes with `get_state`.
- A line-range edit with EMPTY `old_text` replaces the ENTIRE range
  (silently ate code twice). Re-`read` the range before and after.
- Successive inserts anchored on the same header land in REVERSE order;
  anchor on the previous block's last line.
- A short `old_text` like `end` can match INSIDE identifiers (`tendsto`);
  give it its own line range.
- `get_state` output can overflow only WHILE a chain is loading; slice the
  saved JSON dump with python, not Read.
- A theory FILE CREATED AFTER the PIDE server started (via `create_file`)
  may never load: "queued for loading" forever, even after adding it to
  ROOT (session metadata is cached at server start). Workaround: fold the
  material into an already-loaded theory (e.g. Sup_Convolution for
  HOL-Analysis-only content) and split at a batch-level refactor later.

## Automation quirks (this dev Isabelle)

- **linarith can fail on plainly LINEAR goals** mixing division-by-numeral
  with several squared-dist atoms (struck three times in prox development,
  e.g. `t²/4 ≤ D ⟹ t² ≤ 4(max D 0 + 1)` and the prox-uniqueness one-shot).
  **`argo` succeeds on exactly these goals** — reach for it first on
  linear-arith-with-atoms; nlinarith does not exist here at all.
- linarith atomizes nonlinear products SYNTACTICALLY: `2*t*I` is the atom
  `(2*t)*I`, unrelated to `t*I`; `(1-t)*f y` is one atom, unrelated to
  `t*f y`. Pre-normalize with `algebra_simps`/`power2_eq_square` into
  literal-times-atom form (`2*(t*I)`, `f y - t*f y`) before the linarith.
- simp can MANGLE a fact passed with `using`: `t²*d2 = t*(t*d2)` became
  `d2 = 0 ∨ t² = t*t` (cancellation). Rewrite the target fact instead
  (`using h1 by (simp add: power2_eq_square mult.assoc)`).
- `/⇩R` vs `*⇩R` normalization: simp rewrites `(a+b) /⇩R 2` to
  `(1/2) *⇩R (a+b)` in goals, so a lemma stated with `/⇩R` won't fire as a
  simp rule; use it via `[of ...]` + `rule`/`argo` instead.
- `the_equality[OF fact]` can hit "OF: multiple unifiers" when the fact's
  ∀-form matches both premises; use `proof (rule the_equality)` with
  explicit shows.
- **`\<longlongrightarrow>` (tendsto) and `\<longrightarrow>` (implication)
  render as the SAME-looking long arrow in `read` output.** Round-tripping a
  proof through the unicode rendering silently turned every tendsto into an
  implication, giving a 30-error cascade of "Clash of types _ ⇒ _ and bool".
  When re-sending existing proof text through MCP `edit`, write the ARROWS AS
  ESCAPES (`\<longlongrightarrow>`, `\<longlonglongrightarrow>`); the edit tool
  accepts escapes and PIDE converts on write. Same hazard class as the
  `x/2 + x/2` numeral traps: prefer escapes for anything ambiguous.
- A rule whose premise is a `⋀`-statement cannot be discharged by chaining
  (`using lip by (intro rule)` fails, and `[OF lip]` reports "OF: no
  unifiers"): instantiate the parameters that occur only in the premise and
  discharge separately — `by (rule thm[where B = B and f = f]) (rule lip)`.
- `sets.compl_sets` yields `space M - A`, not `- A`; close with
  `simp add: Compl_eq_Diff_UNIV`. `simp add: Bas` where
  `Bas : insert b (Basis - {b}) = Basis` can be pre-empted by
  `insert_Diff_single` rewriting `insert b (Basis - {b})` to `insert b Basis`
  first — use `simp only: Bas`.
- A line-range MCP `edit` whose replacement text ends in `end` can leave the
  ORIGINAL `end` in place (seen as `endendend` on one line, and later as a
  duplicated final `end` that PIDE reports as "missing theory context for
  command end"). Check the tail with `sed -n` after such an edit.
- **`unfolding eq` where `eq` fixes a variable does NOT fire inside a
  set-comprehension binder that shadows it**: with `x` fixed and goal
  `x ∈ {x. P x}` (from `unfolding foo_def`), a rewrite `g x = h x` never
  matches the bound `x`. Resolve membership FIRST (`have lhs: "x ∈ foo = (∃L.
  ...)" unfolding foo_def by simp`), then rewrite. Symptom: `by simp` fails
  with the goal displayed in exactly the form your rewrite should have hit.
- `negligible_linear_image_eq` etc. as simp rules get pre-empted: simp
  rewrites the GOAL `negligible (T ` (T -` X))` to `negligible (X ∩ range T)`
  via `image_vimage_eq` before the equivalence can fire. Use
  `by (subst negligible_linear_image_eq[OF lin inj]) (rule fact)`.
- The server can wedge (duplicated buffers, endless "queued for loading",
  edits not picked up): stop editing verified files and ask for a restart.

## Isar / proof methods

- `unfolding thm1 thm2` rewrites JOINTLY (innermost first), not
  sequentially — a rule rewriting inside another's redex wins regardless of
  order; chain separate steps or use `simp`.
- `unfolding foo_def` unfolds EVERY occurrence including the goal's RHS;
  instantiate (`foo_def[of x]`). A definition whose RHS mentions its LHS
  (`spectral_decomposition`) LOOPS under unfolding — bind values with
  `define` first. Failed `qed` with "Failed to refine any pending goal"
  after clean inner steps = over-eager unfolding at the top.
- `intro rule facts` cannot instantiate variables occurring only in the
  rule's PREMISES (`?x`, `?C` stayed schematic) — pin with `[where ...]`.
- `by (rule X)` premise leftovers close at `qed` by assumption (so
  `by (intro X facts)` works); but `by m1 m2` applies `m2` to the FIRST
  goal only — use `simp_all` or pre-instantiate.
- `[of a b c]` binds by order of FIRST APPEARANCE in the statement, not
  `fixes` order — use `[where ...]`.
- `OF` against a fact with meta-premises leaves residual trivial goals.
- The `obtain`/`obtains` cluster: state helpers with EXISTENTIAL
  conclusions; eliminate with `obtain x where "A ∧ B" using ex by (rule
  exE)` + `conjunct1/2` (blast/metis can diverge); use `obtains`-theorems
  as elimination rules with parameters FIXED (`proof (rule thm) fix ...`);
  `obtains` silently under-constrains types — annotate binders and treat
  the "Introduced fixed type variable" WARNING as an error.
- A `have` between `also` and `finally` resets `this`; `also` cannot
  rewrite proper subterms (state those as named facts, close with
  `unfolding`/`simp add`).
- `fix a b c :: real` types ALL of them; `for u' v' :: real` in a `have ...
  if` needs explicit types or unification fails far away.
- Locale pitfalls: re-interpreting an interpreted locale is silently
  skipped (qualified facts never exist); a locale predicate takes only
  parameters occurring in axioms; `unfold_locales` decomposes parents to
  raw axioms (use `intro_locales`/predicate facts); locale-level facts for
  free variables become schematic in the wrong position (`[of]`
  mis-instantiates — use `by (rule fact)` against an explicit goal).

## simp / automation specifics

- `simp add: eigval_1`-style rules die on `1 -> Suc 0` normalization: state
  the instance as a named `have`, close with `unfolding`.
- simp prefers cancelling to evaluating (`x•x - 0 = x•x` -> `x = 0`): use
  explicit rules (`diff_zero`, `inner_axis'`,
  `measure_lborel_Icc[OF nonneg]`).
- `ennreal`/`max` goals: simp drops `max` and re-associates products —
  state calculations with `ennreal_leI`/`ennreal_plus`/`ennreal_mult'` by
  `rule`.
- `field_simps` with the same denominator on both sides causes polynomial
  blowup — chain `diff_divide_distrib`/`right_diff_distrib`; compound
  denominators need explicit `nonzero_mult_div_cancel_*`.
- `sum` goals with `if j = i` need a `sum.cong` step before `sum.delta`;
  interval reindexing via `sum.reindex_bij_witness`;
  `sum.mono_neutral_right` already goes `B -> U` (no `[symmetric]`).
- `auto` does not apply `AE_I2` even via `intro:` (duplicate-unsafe-intro):
  split `by (rule AE_I2) (auto ...)`.
- `nn_integral_monotone_convergence_SUP[symmetric]` does not `rule`-apply
  unless the goal's side is literally `nn_integral (SUP ...)` — rewrite
  pointwise with `nn_integral_cong` first.
- `linarith` treats powers/products as atoms (`zero_le_power2`,
  `sum_squares_bound` help); `nlinarith` DOES NOT EXIST in this snapshot.
- higher-order `rule` uses of chaining lemmas need `[where f=...]` or
  "Unification bound exceeded" noise appears.
- `let`-bound event families break `auto` reindexing — `define` instead.
- `measurable_cong[OF eq]` over-generalizes; state the iff explicitly.

## Library facts and gotchas

- Matrix lemmas that DO NOT exist (prove locally, all one-liners):
  `transpose_diff`, `scaleR_matrix_matrix`, `trace_scaleR`,
  `(A-B) *v x`, `A ** (B-C)`, `(A-B) ** C`, `trace (A-B)`,
  `trace (sum ...)`, `card_UNIV_pos` (use `card_gt_0_iff`),
  `scaleR_right_commute`, `matrix_sub_rdistrib`. DO exist:
  `matrix_transpose_mul`, `trace_mul_sym`, `matrix_add_rdistrib`,
  `trace_add`, `matrix_vector_mul_assoc`, `matrix_eq`, `transpose_mat`,
  `trace_I`, `outer_prod_mv`, `onormal_complete`, `onormal_card_dim_span`,
  `dim_sums_Int` (additive form), `dim_eq_0` (apply explicitly),
  `matrix_scaleR_vector_ac`, `scaleR_matrix_vector_assoc`,
  `norm_le_l1_cart`, `norm_nth_le`, `borel_measurable_nth`,
  `continuous_on_component`, `vector_minus_component`.
- `integrable_bound` is SHADOWED by the Henstock-Kurzweil one — use
  `Bochner_Integration.integrable_bound[OF dom]`.
- `stopping_time_le_const`/friends live INSIDE `locale filtration`;
  interpret `filtration (space M) F` to use them.
- Only import HOL-Probability theories inside `HOL-Probability.Probability`
  (importing `HOL-Probability.Stopping_Time` silently poisons children).
- AFP `Kolmogorov_Chentsov` main theory + `Martingales` clash (duplicate
  `stochastic_process`); `Dyadic_Interval`/`Holder_Continuous` are safe.
- `weak_conv_on` is an ABBREVIATION for `limitin (weak_conv_topology X)`;
  the iff-lemma `weak_conv_on_def` unfolds both forms.
  `N (space N)` parses via the GLOBAL `[[coercion emeasure]]`.
- `sets.countable_INT'`/`countable_UN''` are the usable primed forms
  (`countable_INT''` needs `UNIV ∈ sets`); `disjointed_def` produces
  `{0..<k}` not `{..<k}` — match it.
- `emeasure M (space M) < top`: `finite_emeasure_space less_top by blast`.
- `integral_dominated_convergence` is a single fact (no `(3)` selection);
  companions are `integrable_dominated_convergence(2)`.
- `borel_measurable_lim_metric` (not `borel_measurable_lim`) for pointwise
  limits with non-convergent points.
- `adapted_process.adaptedD` has TWO premises — `intro ... order.refl`.
- Notation: scaleR is `*\<^sub>R` (bare `*R` is multiplication by R);
  inner needs `unbundle inner_syntax`; `f(x := y)` breaks after a Greek
  identifier (use ascii binders); `(*)` inside a comment opens a nested
  comment; antiquotations in `text` before the theory header fail; `@{thm
  [source]}` of facts from LATER theories fails the batch build (use
  cartouches); superscripts inside `text` cartouches are document
  antiquotations; the integral binder rejects type annotations on its bound
  variable.
