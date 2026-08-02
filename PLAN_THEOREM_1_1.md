# Plan: reaching Theorem 1.1

Written 2026-08-02, after reading the paper source, the paper it defers to
(Larsson–Ruf, *Minimum curvature flow and martingale exit times*, EJP 29 (2024),
arXiv:2003.13611), and auditing the AFP and this repository.

**This plan supersedes the pessimistic scoping recorded in STATUS.md and task
#17.** That scoping made three claims that are wrong, and they matter:

| earlier claim | actual |
|---|---|
| "Prokhorov's theorem does not exist in the AFP" | **It does**: `Levy_Prokhorov_Metric.Prokhorov_theorem_LP` |
| "Proposition 2.4 needs Bertsekas measurable selection" | Needed for the *measurable map*, **not for usc of `v`** — see §2 |
| "Lemma 2.2 needs Ito + BDG, which are unavailable" | This repo **already routed around it**: `fourth_moment_bound_bounded` |

The corrected estimate is **8,000–15,000 lines**, not 50,000–100,000 — *provided*
three genuine research questions (§6) resolve favourably. Two of them are the
real risk and neither is a matter of transcription.

---

## 0. The target

Five clauses, with `v = enn2real ∘ val_fn k L K`:

| | clause | status |
|---|---|---|
| (0) | `val_fn k L K x < ⊤` | **DONE** `val_fn_finite_bounded` |
| (1) | regularity (paper: usc; here: continuity surrogate) | open — §2 |
| (2) | `visc_sol k L (interior K) v` | open — §4 |
| (3) | `v = 0` on `K − interior K` | ball done; general open — §5 |
| (4) | uniqueness | **DONE** `theorem_1_1_uniqueness_general` |

---

## 0.5 How the paper actually proves Theorem 1.1

Read this before the work items — the structure explains why the items are what
they are.

### Theorem 1.1 is TWO independent theorems

**Existence.** For *any* compact `K`, the value function `v` of Eq. (1.6) is an
usc viscosity solution of `F(∇v,∇²v) = 1` on `K` with zero boundary condition.

**Uniqueness.** *Conditional* on an extra hypothesis: a family
`T_ι : ℝⁿ → ℝⁿ`, `ι ∈ (1,2]`, each a composition of a rotation, a dilation and a
translation, with `K ⊂ int T_ι(K)` and `T_ι → I` as `ι ↓ 1`. The paper notes this
holds for every compact convex `K` with nonempty interior.

The two halves share nothing but the statement of the PDE. Uniqueness is
Section 4; existence is Sections 2, 3 and 5.

### The uniqueness half (Section 4) — the half now formalised here

Proposition 4.1 rests on **Theorem 4.2** (Maximum Principle — part (a) is
`max_principle_boundary_holds`, proved) and **Theorem 4.3** (Comparison).

The `T_ι` hypothesis exists to make Theorem 4.3 work. Given a subsolution `u` and
a supersolution `w` on `K`, transport `w` to the slightly larger `T_ι(K)` by
`w^ι(x) = w(T_ι⁻¹x)` and rescale by `c_ι²`, the dilation factor. The engine is the
equivariance identity (4.4)

    F(p, M) = c_ι² · F(Oᵀp, c_ι⁻² Oᵀ M O)      (O orthogonal)

proved by conjugating the competitor `a ↦ O a Oᵀ`, which preserves `a ⪰ 0`,
`a p = 0` and both eigenvalue constraints. Hence `c_ι² w^ι` is a supersolution on
`T_ι(K)`, and `K` now sits COMPACTLY INSIDE that domain — which manufactures the
strict boundary ordering comparison needs. Then let `ι ↓ 1`.

This is the geometric analogue of the usual "subtract `δ`" trick: rather than
perturb the function, inflate the domain, and the scaling invariance of the
nonlinearity pays for it.

### The existence half (Sections 2, 3, 5) — the half still open

**§2, the admissible set `P_x`** (martingale laws with `d⟨X⟩/dt` in the
constraint set):

- **Lemma 2.1** — the convexified constraint set is the convex hull of
  `{λ_(n−k)(a) ≥ 1}`. Hyperplane separation plus an eigenvalue-rearrangement
  estimate. *Proved here: `Lemma_2_1_Exact.thy`.*
- **Lemma 2.2** — `P_x` relatively compact. Chain: fourth-moment bound (2.7) →
  Kolmogorov continuity → Arzelà–Ascoli → Prokhorov. *See §1 below: ~90% done.*
- **Lemma 2.3** — `P_x` closed, hence compact. Prokhorov + **Skorokhod
  representation** for a.s. convergence, Vitali to pass the martingale property,
  then convexity and closedness of `S` plus Lebesgue differentiation to recover
  `d⟨X⟩/dt ∈ S` a.e. *See RQ-A.*
- **Proposition 2.4** — usc of `v`, the pointwise DPP (2.9), and attainment of
  the supremum. *See below and §2.*

**§3, the viscosity property.** `Lemma 3.1` computes the semicontinuous
envelopes: `F_* = F`, while `F^*` differs from `F` only at `p = 0`. *That single
discrepancy is the origin of the whole `p ≠ 0` difficulty that dominated the
Theorem 4.2(a) work.* **Example 3.1** is the explicit radial construction; then
§3.1 proves the subsolution property and §3.2 the supersolution property, both by
test-function arguments run against the DPP.

**§5** supplies continuity on `int K` (Prop 5.1), the characterisation of where
`v = 0` (Lemma 5.3, a face-dimension trichotomy), and Props 5.4/5.5 — excluded
from this project by an earlier instruction.

### Where it is genuinely hard, and why

Two places, and they are exactly what the research questions below target.

**(a) Proposition 2.4 has no proof in the paper.** Its entire proof is
*"It suffices to repeat [Larsson–Ruf, proofs of Proposition 2.2(ii),(iii)] word by
word."* Following that reference, the argument is: `P_x` consists of the
pushforwards `(x+·)_*P` with `P ∈ P₀`, so `v(x) = sup_{P∈P₀} f(x,P)` where
`f(x,P) = ((x+·)_*P)-essinf τ_K`; `f` is jointly usc; `P₀` is compact; and then a
measurable selection theorem (Bertsekas–Shreve Prop. 7.33) yields usc of `v`
**as well as** a measurable optimiser `x ↦ P*_x`, which in turn drives the DPP.

**The observation this plan turns on**: selection is invoked for two conclusions
but is needed for only one. Usc of a supremum of a jointly usc function over a
COMPACT set is five lines (Berge, upper half). Only the *measurable* optimiser
needs Prop. 7.33 — and only the DPP needs that. See §2b.

**(b) Example 3.1 is load-bearing and cannot be cheapened.** It supplies
`v > 0` on `int K`, which §3.1 needs before it can begin. A Brownian market will
NOT substitute: Brownian exit times are arbitrarily small with positive
probability, so their essential infimum is `0` — which is precisely why
`mkt_exit_vals_nonempty`, built from the stopped Brownian market, yields only
`v ≥ 0`. The determinism of the radius is the entire point, and it is what forces
the specific degenerate non-Lipschitz SDE (3.11) onto the critical path. See RQ-C.

**Summary of the existence half's foundations**: a proposition the paper does not
prove (2.4), a representation theorem absent from Isabelle and the AFP
(Skorokhod), and a weak-existence result for which the paper cites no source
(3.11). That is why the remaining work is three separate pieces of
infrastructure rather than assembly.

---

## 1. Lemma 2.2 (relative compactness of `P_x`) — ~90% DONE ALREADY

The paper's chain is: fourth-moment bound (2.7) → Kolmogorov continuity →
Arzelà–Ascoli → Prokhorov. **Every link already exists**, and the repository's
own `Section_2_Compactness.thy` header analyses this correctly.

- (2.7) `E|X(t)−X(s)|⁴ ≤ C'(t−s)²` — **`Increment_Moments.fourth_moment_bound_bounded`**
  proves `≤ 8C²(T−s)²` from the conditional-variance identity
  `cond_exp((X_v−X_u)²) = cond_exp(A_v−A_u)` plus `0 ≤ A_v−A_u ≤ C(v−u)`.
  **This bypasses Ito + BDG entirely** — the paper gets (2.7) from BDG twice;
  this repo gets it from the compensator directly. That is the single most
  important thing the earlier scoping missed.
- Kolmogorov continuity — `Kolmogorov_Chentsov` (AFP, already used here).
- Arzelà–Ascoli — `HOL-Complex_Analysis`; packaged as
  `Section_2_Compactness.holder_family_subsequence`.
- Prokhorov — `Levy_Prokhorov_Metric.Prokhorov_theorem_LP`.
- Assembled: **`Path_Tightness.tight_on_set_path_laws_vec`** and
  **`path_laws_convergent_subsequence_vec`** — a uniform 4th-moment bound gives a
  weakly convergent subsequence. *That is Lemma 2.2.*

### Work item 1 — RESCOPED 2026-08-02: it is NOT low risk, and it is not about lines

Instantiating Lemma 2.2 at `P_x` runs into a **missing hypothesis in the market
class**, not a shortage of work. Trace the chain:

| step | needs |
|---|---|
| `Path_Tightness.tight_on_set_path_laws_vec` | a uniform 4th-moment bound per component |
| `Increment_Moments.fourth_moment_bound_bounded` | `covA`: `cond_exp (F u) ((X v − X u)²) = cond_exp (F u) (A v − A u)` |
| `Stopped_Localization.stopped_covariation` (the only thing that discharges `covA`) | `mgZ`: **`martingale M F 0 (λt ω. (X t ω)² − A t ω)`** |

But `sufficiently_volatile_market` (`Relative_Arbitrage_Stochastic.thy:93`) assumes
only

    dynkin_quadratic:  E[X_{t∧τ}·X_{t∧τ}] − E[∫₀^{t∧τ} tr(acov s) ds] = x0·x0

which is **unconditional**, about the **trace**, and **stopped**. It says the
expectation of `|X|² − ∫tr(acov)` is constant in `t`. `mgZ` says the compensated
square is a martingale, componentwise. Constant expectation does not imply the
martingale property, and a trace identity does not imply componentwise ones, so
`mgZ` is **not derivable** from the locale as it stands. A grep confirms nothing
in the development derives it for a general market of this class.

**Three ways out, and only one is real.**

1. *Strengthen the locale* to assume the componentwise martingale property of the
   compensated square. This is arguably the FAITHFUL axiomatisation — the paper's
   class (1.7) is a martingale problem, in which `X` and `X Xᵀ − ∫a` are both
   martingales — so the current locale is WEAKER than the paper's class, and the
   fix makes it match. Cost: `P_x` shrinks, so `val_fn` changes, and every
   existing consumer of the locale must be re-checked. **This is a decision about
   what the formalisation asserts, and it belongs to the author, not to a
   mechanical fix.**
2. *Derive `mgZ` from `dynkin_quadratic`* — impossible, see above.
3. *Go through quadratic-variation calculus and Itô's formula* — the route the
   paper takes, and the one this development explicitly declares out of scope
   (`Relative_Arbitrage_Ito.thy:95`).

Until item 1 is resolved, clause (1) of Theorem 1.1 is complete only as a
conditional statement: `Section_2_Usc.vshift_sup_usc_of_seq_compact` proves it
GIVEN sequential weak compactness of the law family, and everything downstream of
that hypothesis — including the market-to-law bridge `vshift_path_law` — is
verified.

### Work item 1, as originally scoped (~300–600 lines, LOW risk) — superseded above
Instantiate the above at `P_x`. Concretely:
1. From `sufficiently_volatile_market`, derive the hypotheses of
   `fourth_moment_bound_bounded`: `A = tr⟨X⟩`, rate bound `C = nL` from
   `eigen_ub`, the conditional-variance identity, and boundedness of `X`
   (automatic — `X` is stopped on exit from the compact `K`).
2. Feed `path_laws_convergent_subsequence_vec`.
3. Conclude `lemma_2_2`: `P_x` relatively compact.

---

## 2. Lemma 2.3 (closedness) and usc of `v` — the selection theorem is NOT needed

### 2a. What the paper actually says
Prop 2.4's entire proof is *"It suffices to repeat [Larsson–Ruf, proofs of
Proposition 2.2(ii),(iii)] word by word."* A commented-out block in the source
(lines 393–401) sketches the intent, and Larsson–Ruf's Proposition 2.2(ii) reads
**verbatim**:

> `P_x` consists of the pushforwards `(x+·)_*P` with `P ∈ P_0`. Thus
> `v(x) = sup_{P∈P_0} f(x,P)`, where `f(x,P) = g((x+·)_*P)` and
> `g(P) = P-essinf τ_K`. By Lemma 2.1, `g` is upper semicontinuous. Since `f` is
> the composition of `g` with the continuous function `(x,P) ↦ (x+·)_*P` … it is
> also upper semicontinuous. Moreover `P_0` is compact by (i). A suitable
> selection theorem, see e.g. [Bertsekas–Shreve, Proposition 7.33], yields upper
> semicontinuity of `v` **as well as** a measurable map `x ↦ Q_x` …

### 2b — DONE 2026-08-02: `Section_2_Compactness.usc_sup_over_compact`

The Berge step is **proved and batch-verified**:

    theorem usc_sup_over_compact:
      fixes F :: "'a::topological_space => 'b::topological_space => real"
      assumes "compact C" "C ~= {}" "!!y. bdd_above (F y ` C)"
          and "Sup (F x ` C) < c"
          and box: "!!P d. P : C ==> F x P < d ==>
                EX U V. open U & open V & x : U & P : V
                      & (ALL y:U. ALL Q:V. F y Q < d)"
      shows "eventually (%y. Sup (F y ` C) < c) (nhds x)"

`box` is joint upper semicontinuity at `(x,P)`, written as a product
neighbourhood rather than through `nhds (x,P)` so the proof does not depend on
how the product topology is packaged.

**This is the theorem that removes Bertsekas 7.33 from the critical path for
clause (1).** What remains for clause (1) is only to verify its hypotheses at
`F = f`, `C = P_0` — i.e. items 2.1–2.4 below plus Lemma 2.3.

Two traps cost a build each, both worth remembering:

 - `from ex P obtain U V where ... by blast` where `ex : ALL P:C. EX U V. ...`
   **does not terminate**. Chaining the bounded-`ALL` instantiation into the same
   `blast` as the two `EX`-eliminations sends it searching. `from bspec[OF ex P]
   obtain U V ... by blast` is instant — instantiate first, eliminate second.
 - `open_INT` takes a BOUNDED-`ALL` premise (`ALL x:A. open (B x)`), not a
   `!!`-rule. Passing `!!P. P : D ==> open (UU P)` fails with
   `OF: no unifiers`.

### 2b. THE KEY OBSERVATION
The selection theorem is invoked for **two** conclusions at once. Only the second
needs it. `v(x) = sup_{P∈C} f(x,P)` with `C` compact and `f` jointly usc is usc by
a five-line argument (the upper half of Berge's maximum theorem):

> take `x_n → x`; pick `P_n` with `f(x_n,P_n) ≥ v(x_n) − 1/n`; by compactness pass
> to `P_{n_k} → P ∈ C`; then
> `limsup v(x_{n_k}) ≤ limsup f(x_{n_k},P_{n_k}) ≤ f(x,P) ≤ v(x)`.

**So clause (1) does not need Bertsekas 7.33.** The measurable map is needed only
for the DPP — see §3.

### 2c. Larsson–Ruf Lemma 2.1, verbatim, is elementary
> `ω ↦ τ_K(ω)` is usc: if `ω_n → ω` locally uniformly and `ω(τ_K(ω)+ε) ∉ K`, then
> for large `n`, `ω_n(τ_K(ω)+ε) ∉ K`, so `τ_K(ω_n) ≤ τ_K(ω)+ε`.
> Then for every `λ>0`, Portmanteau gives that
> `P ↦ f_λ(P) = −(1/λ) log E_P[e^{−λτ_K}]` is usc; so is
> `inf_{λ>0} f_λ(P) = P-essinf τ_K`.

Portmanteau's closed-set/limsup form **is in the AFP**
(`Levy_Prokhorov_Metric.General_Weak_Convergence`, the
`Limsup (measure (Ni n) A) ≤ measure N A` for closed `A` family).

### The two Portmanteau directions, by exact AFP name

Both are in `Levy_Prokhorov_Metric.General_Weak_Convergence`, inside the
`Metric_space` locale (so `Self`, `mtopology`, `M` are the locale's):

    mweak_conv2   closedin mtopology A
                    ⟹ Limsup F (λx. ereal (measure (Ni x) A)) ≤ ereal (measure N A)

    mweak_conv3   (⋀A. closedin mtopology A ⟹ Limsup F … ≤ measure N A)
                    ⟹ ((λn. measure (Ni n) M) ⟶ measure N M) F
                    ⟹ openin mtopology U
                    ⟹ measure N U ≤ Liminf F (λn. measure (Ni n) U)

**Item 2.3 wants `mweak_conv2`** (closed sets): `{τ_K ≥ c}` is closed because
`τ_K` is usc, and `Nᵢ{τ ≥ c} = 1` for all `i` forces `N{τ ≥ c} = 1` since
`1 = limsup Nᵢ(A) ≤ N(A) ≤ 1`.

**Item 2.4 wants `mweak_conv3`** (open sets): the eroded event `G` is open, and
`liminf Qₘ(G) ≥ Q(G) > 0` keeps its mass positive as the measure moves.

Note `mweak_conv3` takes the closed-set statement as a HYPOTHESIS rather than
deriving it, so item 2.4 will need `mweak_conv2` too, plus the total-mass
convergence `(λn. measure (Ni n) M) ⟶ measure N M`.

### 2c — SIMPLIFICATION: skip Larsson–Ruf's Laplace transform entirely

LR prove `P ↦ P-essinf τ_K` usc by writing it as `inf_{λ>0} f_λ` with
`f_λ(P) = −(1/λ)·log E_P[e^{−λτ_K}]` and applying Portmanteau to each `f_λ`.
**That detour is unnecessary here.** Upper semicontinuity is exactly closedness
of every superlevel set `{P : c ≤ P-essinf τ}`, and

    ess_inf_time_ge_iff  (PROVED)
        c ≤ ess_inf_time M tau  ⟷  (AE ω in M. c ≤ ennreal (tau ω))

turns that set into `{P : P{τ ≥ c} = 1}`. Since `τ_K` is usc, `{τ_K ≥ c}` is
CLOSED, and the closed-set form of Portmanteau — `limsup Pₘ(A) ≤ P(A)` for closed
`A`, which is precisely the form `Levy_Prokhorov_Metric` provides — closes it in
one step. No Laplace transform, no `inf` over `λ`.

So work item 2.2 (`essinf_eq_inf_log_laplace`) is **deleted from the plan**.

### Work item 2 — PROGRESS 2026-08-02

- 2.1 `tau_K_usc` — **DONE 2026-08-02**, `Path_Tightness_Market.etime_usc_on_paths`.
  The two halves were proved on the two import branches and joined there:
  - `Exit_Time.etime_less_iff` — being strictly below `c` is WITNESSED by a
    single time `r < c` at which the path is already in `A`; plus
    `etime_less_of_open_witness`.
  - `Path_Space.open_hit_strictly_before` — the witnessed condition
    `{f. ∃r. 0 ≤ r ≤ T, r < c, f r ∈ A}` is OPEN in the path topology, because
    evaluation at a fixed time is continuous (`continuous_map_path_eval`, which
    already existed) and an open `A` pulls back to an open set of paths; the
    union over admissible witness times stays open.

  **Note the split.** `Exit_Time` imports `Ito_Market`; `Path_Space` imports the
  AFP Prokhorov entry and `Section_2_Compactness`. They are on DIFFERENT import
  branches and neither sees the other, so the exit-time content and the
  topological content had to be proved separately and joined downstream. The
  join happens in `Path_Tightness_Market`, the ONLY theory in the development
  reaching both (verified by a reachability sweep over every theory's imports).

  The join has TWO branches, not one — the earlier "one step" reading was
  incomplete. For `¬ T < c` the two sets coincide by `etime_less_iff`. But when
  `T < c` the witnessed characterisation does NOT apply: a path that never
  enters `A` still has exit time `T`, so EVERY path qualifies and the set is the
  whole `mspace` — open by `openin_topspace`, via `etime_le_T`.
- 2.2 — **deleted**, see 2c.
- 2.3 `essinf_usc` — **DONE 2026-08-02**, `Section_2_Usc.essinf_etime_usc`,
  resting on two new lemmas:
  - `Path_Space.weak_conv_closed_full_measure` — the closed-set Portmanteau in
    the only shape this argument uses: if `A` is closed and `measure (Nᵢ) A = 1`
    for every `i`, then `measure N A = 1`. Proved by interpreting the AFP's
    `mweak_conv_fin` locale (all four parameters come out of `weak_conv_on_def`)
    and reading off `mweak_conv2`.
  - `Section_2_Usc.etime_superlevel_closed` — `{f : c ≤ ennreal (τ_K f)}` is
    closed, from `etime_usc_on_paths` by complementation.

  Three details that were NOT visible from the plan sketch:
  1. The `ennreal` threshold forces a case split. On `c = ⊤` the superlevel set
     is EMPTY (the exit time is a real capped at `T`), so its complement is the
     whole space; only the `c = ennreal r` branch reduces to `etime_usc_on_paths`,
     and that reduction needs `etime_nonneg` to invoke `ennreal_less_iff`.
  2. `weak_conv_on_def` gives `sets (Nᵢ) = sets (borel_of X)` only EVENTUALLY,
     while the Portmanteau wrapper wants full measure at every index. Fixed by
     shifting the sequence past the threshold `n₀` and rebuilding `weak_conv_on`
     for the shifted family (`LIMSEQ_ignore_initial_segment`); weak convergence
     does not see a finite prefix.
  3. `Section_2_Usc` had to be a NEW leaf theory: `Value_Function` (market/Ito
     branch) and `Path_Tightness_Market` (AFP Prokhorov branch) had no common
     descendant. Registered in `ROOT` after `Path_Tightness_Market`.
- 2.4 `translation_pushforward_continuous` — **the crux device is proved**;
  the assembly remains.

  *Do not reach for joint continuity of `(x,P) ↦ (x+·)_*P`.* The Berge
  hypothesis `box` only asks that `f(x,P) < d` persists on a product
  neighbourhood, and unfolding is much cheaper:

      f(x,P) < d   ⟺   P{ω : τ_K(x+ω) < d} > 0

  (`ess_inf_time_ge_iff` negated), and by `etime_less_iff` that event is
  witnessed at a single time `r` by `x + ω(r) ∈ A`.

  **The obstruction is uniformity**: each `ω` has its own room to move `x`, and
  a pointwise `ε(ω)` is useless against a measure. The fix is to erode `A`:

      Exit_Time.open_gt_infdist   open {z. d < infdist z S}          (PROVED)
      Exit_Time.shift_stays_off   d < infdist z S ⟹ dist z w < d ⟹ w ∉ S  (PROVED)

  The sets `{z. d < infdist z (−A)}` are open, increase to `A` as `d ↓ 0`, and
  give a margin `d` INDEPENDENT of `ω`. Pick `d` so the eroded event still has
  positive mass; then shifting `x` by less than `d` keeps every witness inside
  `A`, uniformly. `shift_stays_off` needs neither closedness nor completeness —
  if `w ∈ S` then `infdist z S ≤ dist z w < d` contradicts the margin outright.

  And because the eroded event is OPEN, the open-set form of Portmanteau
  (`liminf Qₘ(G) ≥ Q(G)`) keeps its mass positive as the measure moves. So the
  same erosion handles BOTH varying arguments — that is why no joint-continuity
  theorem is needed.

  **The countable reduction is also proved**:

      Exit_Time.positive_of_countable_UN
        countable R ⟹ (⋀r. r ∈ R ⟹ H r ∈ sets M)
          ⟹ emeasure M (⋃r∈R. H r) ≠ 0 ⟹ ∃r∈R. emeasure M (H r) ≠ 0

  This is why the reduction to `qtimes` (via the pre-existing `hit_iff_qtimes`)
  must happen FIRST: over an uncountable index set the step is simply false, and
  a countable union of null sets being null is the whole content.

  And the bridge from the essential infimum to a MEASURE, which is the form
  Portmanteau consumes:

      Value_Function.ess_inf_time_less_iff
        {ω ∈ space M. ennreal (tau ω) < d} ∈ sets M ⟹
          (ess_inf_time M tau < d ⟷ emeasure M {ω ∈ space M. ennreal (tau ω) < d} ≠ 0)

  **PROGRESS 2026-08-02: the erosion device is now an OPERATOR, not a recipe.**
  `Exit_Time` defines

      eroded d A = (if A = UNIV then UNIV else {z. d < infdist z (- A)})

  with `open_eroded`, `eroded_subset` (for `0 ≤ d`), `eroded_mono`,
  `eroded_shift` (`z ∈ eroded d A ⟹ dist z w < d ⟹ w ∈ A` — the uniform margin),
  and `eroded_exhausts` (`(⋃n. eroded (1/Suc n) A) = A` for open `A`).

  The `A = UNIV` split in the definition is NOT bookkeeping and was missed by the
  earlier sketch: Isabelle's `infdist z {} = 0`, so the naive
  `{z. d < infdist z (−A)}` is EMPTY exactly when `A` is everything — the one
  case needing no erosion at all. With the split all five laws hold
  unconditionally.

  And the measure-theoretic companion, which is what actually gets used:

      Exit_Time.positive_mass_at_some_erosion
        open A ⟹ (⋀n. {ω ∈ space M. Y ω ∈ eroded (1/Suc n) A} ∈ sets M)
          ⟹ emeasure M {ω ∈ space M. Y ω ∈ A} ≠ 0
          ⟹ ∃n. emeasure M {ω ∈ space M. Y ω ∈ eroded (1/Suc n) A} ≠ 0

  This is the step that turns "positive mass in `A`" into "positive mass with a
  margin uniform over the WHOLE sample space", at the cost of an unspecified
  level. It is a direct instantiation of `positive_of_countable_UN` at
  `R = UNIV :: nat set`.

  **All FIVE ingredients of 2.4 now exist:**

  | role | lemma |
  |---|---|
  | essinf ↔ positive mass | `ess_inf_time_less_iff` |
  | positive mass ↔ a witness time | `etime_less_iff` |
  | one witness time suffices | `positive_of_countable_UN` |
  | margin uniform in `ω` | `open_gt_infdist`, `shift_stays_off` |
  | margin survives moving `P` | same erosion + open-set Portmanteau |

  **PROGRESS 2026-08-02: the `x`-perturbation half of 2.4 is DONE.**
  `Section_2_Usc.etime_shift_box_half`: from `f(x,P) < d` ALONE — no continuity
  of the pushforward map, no joint continuity — there is `δ > 0` and an OPEN set
  `G` of paths with `P G > 0` such that `τ_K(y+ω) < d` for every `ω ∈ G` and
  every `y` with `dist x y < δ`. Supporting lemmas, in dependency order:

      Exit_Time.etime_less_iff_qtimes_open   (rational witness for OPEN A)
      Path_Space.open_eval_preimage          (the brick open_hit_strictly_before used inline)
      Path_Space.mspace_path_metricD         (a path IS continuous on {0..T})
      Section_2_Usc.open_shifted_eval_preimage
      Section_2_Usc.etime_shift_le_of_eroded (the uniform margin)
      Section_2_Usc.positive_mass_at_some_qtime  (countable reduction, at measure level)
      Section_2_Usc.etime_shift_uniform_margin

  `hit_iff_qtimes` turned out to be the WRONG tool: it reduces hitting a CLOSED
  set and pays an `infdist < 1/Suc m` approximation. For an open target the
  reduction is exact — openness gives room around the witness, so the witness
  slides onto a rational — hence the new `etime_less_iff_qtimes_open`. It also
  shows where `¬ T < c` earns its keep: it forces `r < c ≤ T`, so the witness is
  strictly interior and there IS room to slide right.

  Two Isabelle traps here, both the same shape and both costing a build: applying
  a lemma whose premise contains `?X ?r ?ω` by chaining a fact into it leaves a
  higher-order unification with several solutions (`OF: multiple unifiers`). The
  fix is always to let the CONCLUSION drive — `proof (rule …)` with explicit
  `show`s — so the process and path are fixed before the premises are matched.
  Separately, `etime T A (λs w. x + w s) ω` and `etime T A (λs w'. x + ω s) ω`
  are equal but not syntactically so; `etime` only ever applies its process to
  the one path, and `unfolding etime_def by simp` bridges them.

  **2.4 is DONE in sequential form — `Section_2_Usc.etime_shift_box`.** Both
  perturbations at once: if `yᵢ → x` and `Qᵢ → P` weakly, then the event
  `{τ_K(yᵢ + ·) < d}` eventually has positive `Qᵢ`-mass. Two further lemmas:

      Path_Space.weak_conv_open_positive_eventually  (open-set Portmanteau)
      Section_2_Usc.open_etime_shift_less            (the event is OPEN)

  The single set `G` does all the work, and this is what makes the erosion device
  pay off twice: erosion makes `G` survive moving `x`, and OPENNESS of `G` makes
  it survive moving `P`. Had the erosion been closed instead, Portmanteau would
  point the wrong way.

  `weak_conv_open_positive_eventually` assumes the `sets` equation at EVERY index
  rather than eventually. That is forced: `mweak_conv3` needs convergence of the
  total mass, which here is the constant 1 only because `space (Nᵢ) = mspace m`
  with no exceptions. The measurability of the target event, needed for the final
  monotonicity step, comes from `open_etime_shift_less` — the event is a
  COUNTABLE union of open sets, by the same `qtimes` decomposition.

  **The sequential-to-topological bridge — DONE 2026-08-02.**
  `usc_sup_over_compact`'s `box` wants open `U ∋ x` and `V ∋ P`; item 2.4 proves
  the sequential statement. `Section_2_Compactness.box_of_sequential` converts
  one into the other for any two METRIZABLE spaces:

      metrizable_space X ⟹ metrizable_space Y ⟹ x ∈ topspace X ⟹ P ∈ topspace Y
        ⟹ (⋀yi Qi. limitin X yi x sequentially ⟹ limitin Y Qi P sequentially
              ⟹ eventually (λi. R (yi i) (Qi i)) sequentially)
        ⟹ ∃U V. openin X U ∧ openin Y V ∧ x ∈ U ∧ P ∈ V ∧ (∀y∈U. ∀Q∈V. R y Q)

  and `Path_Space.metrizable_weak_conv_path_topology` supplies the hypothesis for
  the law space, from the AFP's `metrizable_weak_conv_topology` (Lévy–Prokhorov)
  plus metrizability and separability of the path space, both already proved.

  Two things worth knowing before touching this proof. `metrizable_space_def`
  quantifies over the CARRIER as well as the metric, so the carrier must be
  identified with `topspace X` afterwards — assuming it IS `topspace X` makes the
  `obtain` fail. And the contrapositive needs countable choice to assemble the
  per-`n` counterexamples into two sequences, which is exactly why metrizability
  (or at least first countability) cannot be weakened away.

  **One obstruction the plan had not named.** Berge's `box` hypothesis asks for
  an OPEN neighbourhood `V` of `P`, but `mweak_conv3` is a statement about
  filters/limits. Converting one to the other needs the weak topology to be
  first countable at `P` — true here, since the Lévy–Prokhorov metric metrizes
  it on a Polish space (that is what the AFP entry is for), but it is a real
  step, not a rewriting. Budget for it separately from the 200–350 lines.
- 2.5 Berge — **DONE**, `usc_sup_over_compact`, plus **`usc_sup_over_compactin`**
  (2026-08-02), the same theorem with the SECOND factor over a `topology` value
  instead of a type class.

  That variant is not a convenience. The weak topology is `weak_conv_topology X`,
  a `topology` VALUE; it cannot be a type-class instance on `'a measure`, because
  the type carries no canonical topology and different base spaces induce
  different weak topologies on the same type. So `compact`/`open` on the law side
  had to become `compactin`/`openin`. Only the covering step changes: `compactinD`
  returns a finite SET of opens rather than a finite index set, and the indices
  come back via `finite_subset_image`. The conclusion stays in the type class,
  since it is about `nhds x` in `real^'n`.
- 2.6 — **DONE 2026-08-02**, `Section_2_Usc.vshift_sup_usc`: for a weakly
  COMPACT family `C` of laws, `x ↦ Sup {P-essinf τ_K(x+·) : P ∈ C}` is upper
  semicontinuous. Every hypothesis of Berge is discharged; the only assumption
  left standing is compactness of `C`, i.e. Lemma 2.3.

  Supporting definitions and lemmas:

      Section_2_Usc.vshift T A y Q = enn2real (Q-essinf τ_K(y+·))
      Section_2_Usc.vshift_le                     (bounded by T)
      Section_2_Usc.vshift_less_iff_positive_mass (the ennreal/real bridge)
      Section_2_Compactness.box_of_sequential_euclidean

  **A case the plan had not anticipated.** Berge quantifies `box` over EVERY
  threshold `d` above `F x P`, including `d > T`. Nothing excludes it — `vshift`
  could be `0` while `d` is huge — so `¬ T < d` is NOT available, and the whole
  item-2.4 witness machinery assumes it. That branch is trivial rather than
  impossible (the exit time never exceeds `T`, so the whole space works), but it
  has to be split off explicitly.

  **Three Isabelle traps, each costing a build or worse.**
  1. `unfolding open_openin` DOES NOT TERMINATE. `euclidean` is the abbreviation
     `topology open`, so rewriting `open S → openin euclidean S` rewrites the bare
     `open` inside `euclidean` and regenerates its own redex. The `[symmetric]`
     orientation is the declared simp rule precisely because it is the safe one.
     The conversion is now done once, in `box_of_sequential_euclidean`.
  2. `blast` asked to prove `∃U V. …` with `U = UNIV` does not terminate — it has
     to INVENT the witness. Supply the instance first, then `blast` only has to
     apply `exI`.
  3. `(use … in blast)+` to discharge side conditions of a rule application is a
     silent hazard for the same reason; explicit `have`s are cheap insurance.

### Work item 2 (~800–1,500 lines, MEDIUM risk)
- 2.1 `tau_K_usc`: `ω ↦ τ_K` usc on path space. Uses `Path_Space` and
  `Exit_Time.thy`. ~150 lines.
- 2.2 `essinf_eq_inf_log_laplace`: `inf_{λ>0} −(1/λ) log E_P[e^{−λτ}] = P-essinf τ`.
  Pure measure theory. ~200 lines. **Check first** whether `ess_inf_time` in
  `Value_Function.thy` is already in a form that makes this easy.
- 2.3 `essinf_usc`: usc of `P ↦ P-essinf τ_K` via Portmanteau. ~200 lines.
- 2.4 `translation_pushforward_continuous`: `(x,P) ↦ (x+·)_*P` continuous. ~150 lines.
- 2.5 `berge_usc_sup`: the five-line argument, stated abstractly. ~100 lines.
- 2.6 `val_fn_usc` — **clause (1)**. ~100 lines.

**Prerequisite**: `P_0` compact, i.e. Lemma 2.3. See §6, research question A.

---

## 3. The dynamic programming principle — use the WEAK DPP

The paper's DPP (2.9) is proved with the measurable selection. Bouchard & Touzi,
*Weak dynamic programming principle for viscosity solutions* (SICON 49 (2011)
948–962), give a weaker DPP that **is designed precisely to avoid measurable
selection** and is, in their words, tailor-made for deriving the dynamic
programming equation in the viscosity sense. The relaxation replaces `v` in the
DPP by a smooth test function touching it, which is exactly the form the
subsolution/supersolution proofs consume.

Note the paper's own Remark after Prop 2.4 identifies its DPP as the *stochastic
target* type of Soner–Touzi, which is the setting Bouchard–Touzi address.

### Work item 3 (~1,500–3,000 lines, HIGH risk — see research question B)
- 3.1 Formulate the weak DPP in this development's vocabulary.
- 3.2 Prove the two inequalities. The `≥` direction is usually easy
  (any admissible `P` gives a lower bound); the `≤` direction is where the
  selection would have been used and where the test function replaces it.

---

## 4. Clause (2): the viscosity property

Reading §3.1 and §3.2 of the paper, the subsolution proof needs exactly:
`v* = v` (clause 1); `F_* = F` (**already proved here — `Lemma_3_1.thy`**);
`v > 0` on `int K` (Example 3.1 — §5); **an optimiser `P ∈ P_x` at a single `x`**;
and the DPP.

**Attainment at a single `x` needs no selection**: `P ↦ P-essinf τ_K` is usc on the
compact `P_x`, so it attains its supremum. That is `continuous_attains_sup`'s usc
analogue and is ~50 lines.

The supersolution proof (Case 1, `∇φ(x) ≠ 0`) builds a *second* SDE from matrices
`S_i = λ_i^{1/2}(q_i ∇φ(x)^T − ∇φ(x) q_i^T)/|∇φ(x)|²` and needs a weak solution of
`dY = Σ(Y) dW` with `Σ(y)` the matrix whose columns are `S_i ∇φ(y)`. This is
Eq. (3.24) and is a second weak-existence obligation.

### Work item 4 (~2,000–4,000 lines, HIGH risk)
- 4.1 `optimiser_exists`: usc attains sup on compact `P_x`. ~50 lines.
- 4.2 Subsolution property. ~800–1,500 lines.
- 4.3 Supersolution property, Case 1 (`∇φ(x) ≠ 0`) — needs Eq. (3.24). ~800–1,500.
- 4.4 Supersolution property, Case 2 (`∇φ(x) = 0`) — needs `E^y[τ_{B_ε(x)}] < ∞`.
- 4.5 `visc_sol` — clause (2).

---

## 5. Example 3.1 and clause (3)

Eq. (3.11) is `dX_{[n']} = a(X_{[n']})^{1/2} dW`, `n' = n−k+1`,
`a(y) = I − yy^T/|y|²` (`a(0) = I`). Three facts drive it:
`a^{1/2}` is bounded and continuous off `0`; `a(y)y = 0`, so the radial part has no
martingale term; `tr a = n−k`. Ito then gives the **deterministic** identity
`|X_{[n']}(t)|² = |x_{[n']}|² + (n−k)t`, so the exit time from a ball is
deterministic and `P*-essinf τ_K = (r²−|x|²)/(n−k)`.

That determinism is the whole point: **a Brownian market will not do**, because
`essinf τ = 0` for Brownian motion — its exit time is arbitrarily small with
positive probability. This is exactly why `mkt_exit_vals_nonempty` (which uses the
stopped Brownian market, `τ ≡ 0`) gives only `v ≥ 0`.

Clause (3) for general convex `K` is the paper's Lemma 5.3, which uses this same
`P*` plus a face-dimension trichotomy.

### Work item 5 (~2,000–4,000 lines, HIGH risk — research question C)

---

## 6. The three research questions — where the real risk is

These are the parts I could not settle by reading, and each should be resolved
*before* committing to the schedule above.

### A. Can Lemma 2.3 (closedness) avoid Skorokhod representation?
**No Skorokhod representation exists in the AFP** (checked). The paper's closedness
proof uses Prokhorov + Skorokhod + Vitali + Lebesgue differentiation.

*Promising route*: characterise the constraint by a family of **linear** inequalities
that are manifestly weakly closed. For convex compact `S` and each symmetric `M`,
`d⟨X⟩/dt ∈ S` a.e. is equivalent to
`E[tr(M (X_t−X_s)(X_t−X_s)^T) g] ≤ (t−s) sup_{a∈S} tr(Ma) E[g]`
for all bounded continuous `F_s`-measurable `g ≥ 0`. Both sides are weakly
continuous given uniform integrability, which the 4th-moment bound supplies via
`Vitali_Convergence.vitali_convergence` (**already in this repo**). Convexity of `S`
is exactly what makes the linear description faithful, and `Lemma_2_1_Exact.thy`
already proves the constraint set is convex.
**If this works, Skorokhod is off the critical path.** Estimated 1,500–3,000 lines.
*Verify this before anything else — it gates §2 and therefore everything.*

### A — UPDATE 2026-08-02: the finite-dimensional crux is PROVED

`Relative_Arbitrage_Convexity.support_characterisation` (batch-verified):

> for closed convex `S` of symmetric matrices, if for every symmetric `M` there is
> `b ∈ S` with `M∙a ≤ M∙b`, then `a ∈ S`.

That is exactly what makes the linear-inequality description FAITHFUL, and it is
where closedness and convexity are used. `lemma_2_1_exact` supplies the convexity.
What remains of RQ-A is the measure-theoretic half: that the inequalities

    E[tr(M(X_t−X_s)(X_t−X_s)^T) g] ≤ (t−s) h_S(M) E[g]

pass to weak limits. Working this out further gave a simplification and exposed
one open point — **read both before starting**:

*The simplification.* The integrand `F_M = (X_t−X_s)^T M (X_t−X_s)` is unbounded,
so weak convergence does not apply directly, and the obvious fix is uniform
integrability via `Vitali_Convergence`. But **for `M ⪰ 0` no uniform
integrability is needed at all**: `F_M ≥ 0`, so truncate at `R`, use that
`min(F_M,R)·g` is bounded continuous to pass to the limit, and then let `R → ∞`
by monotone convergence:

    E_P[min(F_M,R) g] = lim_m E_{P_m}[min(F_M,R) g]
                      ≤ lim_m E_{P_m}[F_M g]  ≤ (t−s) h_S(M) lim_m E_{P_m}[g]

and the left side increases to `E_P[F_M g]`. That is a much shorter route than
Vitali, and it is exact rather than approximate.

*The open point.* That argument needs `M ⪰ 0`, whereas
`support_characterisation` quantifies over all symmetric `M`. For general
symmetric `M = M⁺ − M⁻` the inequality splits into two of opposite sign and the
monotone-convergence trick fails, putting uniform integrability back.

*The open point, now SETTLED — negatively.* **PSD `M` alone do not suffice.**
The set cut out by `{a : tr(Ma) ≤ h_S(M) ∀ M ⪰ 0}` is the *downward* closure of
`S` in the psd order. But `S` carries LOWER bounds (`Π_m(a) ≥ m−k`), so it is not
downward closed: `0 ⪯ a` for any `a ∈ S`, yet `0 ∉ S` since `Π_m(0) = 0 < m−k`.

Splitting the constraint does not rescue it either. The upper part `a ⪯ L·I` is
`tr(vvᵀa) ≤ L|v|²` — psd normal, `≤` direction, monotone convergence applies. The
lower part is `tr(Pa) ≥ m−k` over rank-`m` projections — psd normal but the `≥`
direction, and there weak convergence gives only Fatou,
`liminf ∫h dPₘ ≥ ∫h dP`, which is the wrong way round.

So **uniform integrability is genuinely required**, and RQ-A follows option (ii).
That is not bad news: the fourth-moment bound already supplies it, and the
supplying lemma is now proved —

    Increment_Moments.sq_tail_bound_of_fourth_moment
        E[Z² · 1_{Z²>R}] ≤ E[Z⁴]/R

(with `sq_tail_le_fourth_moment_pointwise` the pointwise estimate). Together with
`fourth_moment_bound_bounded` this bounds the tail of the squared increment
uniformly over the family, which is exactly `unif_integrable`.

**RQ-A inventory as of 2026-08-02** — four of the five pieces are proved:

| role | lemma | |
|---|---|---|
| finite-dimensional crux: a symmetric `a` lies in a closed convex `S` iff it satisfies every supporting linear inequality | `Relative_Arbitrage_Convexity.support_characterisation` | PROVED |
| uniform integrability from the 4th-moment bound | `Increment_Moments.sq_tail_bound_of_fourth_moment` | PROVED |
| truncation error ≤ the same tail | `Increment_Moments.clamp_integral_error` | PROVED |
| the `3ε` limit passage, measure theory removed | `Increment_Moments.tendsto_real_of_approximants` | PROVED |
| assembling these against the AFP weak-convergence vocabulary | `Path_Tightness.weak_conv_on_integral_unif_integrable` | **PROVED** |

    lemma weak_conv_on_integral_unif_integrable:
      assumes wc: "weak_conv_on Ni N sequentially X"
          and f:  "continuous_map X euclideanreal f"
          and ... integrability side conditions ...
          and ui: "!!e. 0 < e ==> EX R >= 0. (ALL i. tail_i R <= e) & tail_N R <= e"
      shows "(%i. LINT x|Ni i. f x) ----> (LINT x|N. f x)"

**RQ-A IS ANSWERED: YES, Lemma 2.3 can avoid Skorokhod representation.** The
complete toolkit is now proved. Contrast with `weak_conv_on_nn_integral_le`,
which was already in the repo: that handles a NON-NEGATIVE integrand by
truncation plus monotone convergence and needs no integrability at all — it
covers exactly the `a ⪯ L·I` half. The lemma above is what covers the other
half, the lower bounds `Π_m(a) ≥ m−k`, where weak convergence alone gives only
the Fatou direction.

**Remaining for Lemma 2.3 is instantiation, not invention**: apply the above at
the covariation functionals `f(ω) = tr(M (X_t−X_s)(X_t−X_s)ᵀ)·g(ω)`, discharge
`ui` from `sq_tail_bound_of_fourth_moment` + `fourth_moment_bound_bounded`, and
conclude membership via `support_characterisation`.

**The target is now a single named obligation (2026-08-02).**
`Section_2_Usc.vshift_sup_usc_of_seq_compact` reduces clause (1) to exactly

    ⋀σ. range σ ⊆ P₀ ⟹ ∃L r. L ∈ P₀ ∧ strict_mono r
          ∧ weak_conv_on (σ ∘ r) L sequentially (mtopology_of (path_metric T))

and nothing else about `P₀` is used. That IS Lemmas 2.2 and 2.3 together, in
their natural form: 2.2 extracts the subsequence, 2.3 puts the limit back.
The conversion to Berge's `compactin` is `Section_2_Compactness.compactin_of_seq_compact`
(sequential compactness = compactness in a metrizable space, transported from
`Metric_space.compactin_sequentially` to a `topology` value).

Two hypotheses that do NOT have to be proved separately: membership of `P₀` in
the weak topology's carrier is derivable from `prob_space` plus the `sets`
equation, and boundedness of the value family comes from `ess_inf_time_le_const`.

**The market-to-law bridge is now closed too (2026-08-02).** Everything above
speaks about LAWS on the path space, while `Value_Function.val_fn` is a supremum
over MARKETS. `Path_Space.path_law` connects them, and

    Section_2_Usc.vshift_path_law
      vshift T A y (path_law M X T)
        = enn2real (P-essinf (etime T A (λs ω. y + X s ω)))

carries the essential infimum of the exit time across it, resting on
`ess_inf_time_distr` (an `AE_distr_iff` argument), `etime_shift_of_restrict`
(the exit time never inspects times outside `[0,T]`, so `path_law`'s restriction
is invisible to it) and `etime_shift_superlevel_closed`.

That last one splits on `ennreal T < c` rather than on `ennreal_cases`: above the
cap every path qualifies, and below it the threshold is automatically a real `r`
with `¬ T < r`, which is exactly what `open_etime_shift_less` needs. Splitting on
`ennreal_cases` instead leaves the `T < r` sub-case to be redone by hand.

**Note the theory placement.** This lemma needs BOTH `Increment_Moments` (for
`clamp_integral_error`, `tendsto_real_of_approximants`) and `Path_Space` (for
`weak_conv_on`). Those are different import branches; the only theory reaching
both is `Path_Tightness`, which is why it lives there rather than next to
`weak_conv_on_nn_integral_le` in `Path_Space`.

`tendsto_real_of_approximants` is the shape the whole argument reduces to: a
sequence uniformly within `e` of some convergent sequence, whose limit is within
`e` of `z`, for EVERY `e`, converges to `z`. Isolating it means the
measure-theoretic assembly never does `ε`-juggling inline.

**What remains of RQ-A**, and it is now a single well-posed lemma:

> weak convergence upgraded by uniform integrability — if `Pₘ → P` weakly, `f` is
> continuous, and `sup_m ∫|f|^{1+δ} dPₘ < ∞`, then `∫f dPₘ → ∫f dP`.

Proof is the standard 3ε: truncate `f` at `R` (bounded continuous, so weak
convergence applies), control both tails by uniform integrability, and note `P`
inherits the moment bound by Portmanteau. Note this is a *different* shape from
`Vitali_Convergence.vitali_convergence`, which varies the function against a
fixed measure; here the measure varies against a fixed function. Estimated
300–600 lines. **After that, RQ-A is assembly.**

### B. Does the Bouchard–Touzi weak DPP suffice here?
Their result is for standard control and mixed control-stopping problems; this is a
*stochastic target* problem with a **pointwise** (essinf) rather than expectation
objective. Bouchard–Touzi and successors (Bouchard–Nutz, *Weak dynamic programming
for generalized state constraints*) do cover target-type problems, but the exact
form must be checked against Definition 3.1's needs.
**Read [BT09](https://www.ceremade.dauphine.fr/~bouchard/pdf/BT09.pdf) and
[arXiv:1105.0745](https://arxiv.org/pdf/1105.0745) before starting §3.**

### C. Can Eq. (3.11) be built explicitly, avoiding general weak-existence theory?
No SDE/weak-existence library exists in Isabelle or the AFP, and building
Stroock–Varadhan for a degenerate non-Lipschitz coefficient is an AFP entry in
itself.

First, why nothing cheaper will do. The constraint set is satisfied *exactly* by
`a(y) = I − yy^T/|y|²`: in `R^n` it has eigenvalue `1` with multiplicity `n−k` and
`0` with multiplicity `k`, so `λ_(n−k)(a) = 1 ≥ 1` and `λ_(1)(a) = 1 ≤ L`. But a
market with *constant* `a` (e.g. the orthogonal projection onto a fixed
`(n−k)`-dimensional subspace) satisfies the same constraint and is useless,
because it is a Brownian motion in an affine subspace and **`essinf τ = 0` for
Brownian motion** — `P(τ < ε) > 0` for every `ε`. The deterministic radius is not
a convenience; it is the only known way to force `essinf τ > 0`.

*Route C1 — explicit, via spherical Brownian motion.* Writing `X(t) = ρ(t)U(t)`
with `ρ(t) = √(|x|²+(n−k)t)` and `|U| = 1`, matching the drift of spherical BM
(which is `−((n'−1)/2)U` with `n'−1 = n−k`) against `ρ' = (n−k)/(2ρ)` forces the
time change `τ' = 1/ρ²`, i.e.

    X(t) = √(|x|² + (n−k)t) · Θ( log(1 + (n−k)t/|x|²) / (n−k) )

with `Θ` a Brownian motion on `S^{n'−1}` started at `x/|x|`. Fully explicit, but it
needs spherical BM, a manifold-valued diffusion that does not exist in Isabelle.

*Route C2 — discrete approximation, and RQ-A makes it viable.* Build the process
as a weak limit of discrete-time martingales that step on spheres of the
prescribed growing radius, then:
- tightness and subsequence extraction from `Path_Tightness` (already here);
- **the covariation constraint passes to the limit by `support_characterisation`
  — the RQ-A machinery, now proved**;
- the radius identity `|X(t)|² = |x|² + (n−k)t` is a *closed* condition on the
  path and so passes to the limit directly;
- the repo already has `Random_Walk_Market.thy`,
  `Relative_Arbitrage_Discrete.thy` and
  `Path_Tightness.projective_limit_of_consistent_path_laws`.

**So RQ-A de-risks RQ-C**: the same linear-inequality characterisation that avoids
Skorokhod in Lemma 2.3 is what lets a discrete approximation be certified as a
member of `P_x`. Route C2 is the one to prototype, and it should be attempted
*after* finishing RQ-A's measure-theoretic half, not before.
If it works, clauses (2) and (3) both unblock.

---

## 7. Order of work

```
  RQ-A (closedness without Skorokhod)      ← do FIRST, gates everything
     │
     ├─→ item 1  Lemma 2.2 at P_x                      300–600
     ├─→ item 2  Lemma 2.3 + usc of v  = CLAUSE (1)   800–1,500
     │
  RQ-C (explicit (3.11))                   ← do SECOND, prototype only
     └─→ item 5  Example 3.1 + Lemma 5.3 = CLAUSE (3) 2,000–4,000
     │
  RQ-B (weak DPP)                          ← do THIRD
     └─→ item 3  DPP                                1,500–3,000
            └─→ item 4  viscosity        = CLAUSE (2) 2,000–4,000
```

**Total 8,000–15,000 lines** if all three research questions resolve favourably;
**30,000+** if RQ-A and RQ-C both fail and Skorokhod plus a weak-existence theory
must be built from scratch.

For calibration: this session produced ~2,000 lines of finished Isabelle including
Theorem 4.2(a). So the optimistic branch is on the order of four to seven sessions
of comparable output; the pessimistic branch is not bounded work.

## 8. Recommended decision point

Spend one session on **RQ-A and RQ-C only**, as prototypes, with no attempt to
finish either. Both are cheap to falsify and expensive to discover late. If both
look viable, the plan above is a real schedule. If either fails, retarget to
Section 4 (Theorem 4.2(b), 4.3, Prop 4.1 — 3,000–7,000 lines, bounded, and the
only other target that uses the Crandall–Ishii investment).
