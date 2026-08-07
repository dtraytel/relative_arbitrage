# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Single source of truth for **what is proved, what is left, and in what
order**. Everything named here is machine-checked: `isabelle build -d .
Arbitrage` is green and there is no `sorry` anywhere in the session.

Last restructured 2026-08-07 (after the `≥` half of the DPP (2.9) was
assembled and the `≤` half was reduced to a single conditioning statement).
Superseded scoping, session logs and dead ends live in `PLAN_HISTORY.md` and
in `git log -p`. Do not resurrect them; do not re-derive anything in §1.

**Sources.** The paper (Lai/Shkolnikov/Soner, arXiv:2512.17702); its Section-2
reference Larsson–Ruf, *Minimum curvature flow and martingale exit times*,
EJP 29 (2024), arXiv:2003.13611 ("LR"); Bouchard–Touzi, SICON 49 (2011)
948–962 ("BT09") for the weak DPP.

**Author-fidelity rule (user decision, 2026-08-04).** Formalize PRECISELY the
paper's result: clause statements must match the paper. Proof techniques are
free. Law-level restatements are stepping stones, not deliverables.

---

## 0. Status

Theorem 1.1 has five clauses about the value function of Eq. (1.6). The
faithful rendering of that value function is

    Paper_Class.paper_v k L T K x
      = Sup ((λQ. ess_inf_time Q (λω. pexit T K (λt. fst (ω t))))
             ` paper_pair_class k L T x)

the supremum, over the paper's class (1.7) written as laws of the pair
`(X, ⟨X⟩)` on the capped path space, of the essential infimum of the exit
time from `K`.

| | clause | status |
|---|---|---|
| (0) | `v < ⊤` | **DONE for `paper_v`** (`paper_v_le_T`, and sharply `paper_v_le_ball_bound`) and for `val_fn` / `stopped_val_fn` |
| (1) | regularity (usc) | **DONE for `paper_v`** — `Paper_Bridge.paper_v_usc_unconditional` |
| (2) | `visc_sol k L (interior K) v` | **OPEN** — needs the DPP (Prop. 2.4) *and* §3's Itô/SDE layer; §2.1–§2.3 |
| (3) | `v = 0` on `K − interior K` | ball case **DONE for `paper_v`** (`paper_v_boundary_zero`); interior value REALIZED for `n−k=1` (`Theorem_1_1.stopped_val_fn_ball_eq_2d`); general `n−k ≥ 2` **OPEN**, §2.4; transfer to `paper_v` §2.5 |
| (4) | uniqueness | **DONE** — `Theorem_1_1.theorem_1_1_uniqueness_general` |

**Three value functions exist**, and the theorem must end up about ONE.
`val_fn` (all `sufficiently_volatile_market` instances), `stopped_val_fn`
(the locale plus the paper's stopped/killed side conditions) and `paper_v`
(the class (1.7) as pair laws). Clauses (0), (1), (3)-ball and (4) are
proved for `paper_v` itself. What still lives only on the market-side
functions is the `n−k=1` realization inside clause (3)
(`stopped_val_fn_ball_eq_2d`); transferring it is §2.5, and it is needed
only if §2.4 turns out to want it.

**Where the DPP stands.** Proposition 2.4's two ingredients are the
MEASURABLE SELECTOR and the KERNEL PASTING that consumes it. Both are
**done** (§1.7, §1.8), and so is the assembly: the **`≥` half of (2.9) at a
deterministic time is proved** (`paper_v_dpp_sup_ge`, §1.9). The `≤` half
is **reduced to exactly one statement about conditioning**
(`paper_v_dpp_le_of_cond`, §2.1) — everything off the survival event is
unconditional. That one statement, and the extension from deterministic
times to stopping times, is all that is left of the DPP.

**Remaining budget, roughly.**

| item | § | lines | risk |
|---|---|---|---|
| the conditioning statement (`cond`) | 2.1 | 700–1,400 | high — r.c.d. + conditional martingale property |
| the DPP at a STOPPING time | 2.2 | 500–1,200 | high — both clocks random |
| §3, the two viscosity inequalities | 2.3 | 2,000–4,000 | high — Itô, exponential local martingales, weak SDE solutions |
| clause (3) for `n−k ≥ 2` | 2.4 | 1,500–3,000 | high |

---

## 1. What is DONE — assume it, do not re-derive it

### 1.1 Uniqueness (clause 4) — closed

`theorem_1_1_uniqueness_general` via Theorem 4.2(a) and the Crandall–Ishii
comparison machinery (`Relative_Arbitrage_Comparison`, `Envelopes`,
`Sup_Convolution`, `Comparison_Assembly`).

### 1.2 Section 2, market level

- **Lemma 2.1** — `Lemma_2_1_Exact.thy` (convexified constraint set); the
  exit-time estimate it feeds is
  `Relative_Arbitrage_Stochastic.expected_exit_time_bound`.
- **Lemma 2.2** — `Path_Tightness_Market.market_path_laws_convergent_subsequence`,
  over `Path_Tightness.tight_on_set_path_laws_vec` and
  `Increment_Moments.fourth_moment_bound_bounded` (4th moment from the
  compensator; no Itô, no BDG).
- **Lemma 2.3 by closure** — `Section_2_Usc.mkt_law_closure` and its
  sequential compactness (`mkt_law_closure_seq_compact`), with
  `vshift_sup_usc_mkt` as the law-level usc headline and
  `clause_one_law_level` as the packaged clause (1) at that level.
- **Integrated identities on closure laws** — `mkt_law_closure_martingale_event`,
  `mkt_law_closure_sq_increment_event`, and the generic measure engines
  `metric_measure_eqI_bounded_cts`, `metric_measure_mono_bounded_cts`.

### 1.3 The paper's class as pair laws (NC) — closed end to end

All in `Paper_Bridge.thy` unless noted. `paper_pair_class k L T x`
(`Paper_Class.thy`) is (1.7) as laws of `(X, Y)` on the capped path space.

| result | content |
|---|---|
| `paper_pair_class_fourth_moment` | uniform 4th moment, by localization at `ploc` + optional stopping + Fatou — no BDG |
| `paper_pair_class_weak_closed` | all four clauses of (1.7) survive a weak limit (NC-3) |
| `tight_on_set_paper_pair_class` | the class is tight (NC-2) |
| `paper_pair_class_convergent_subsequence` | hence sequentially compact |
| `paper_pair_class_shift_image` | the class at `x` is the `x`-translate of the class at `0` |
| `bmpair_law_in_paper_pair_class`, `paper_pair_class_nonempty` | the class is NONEMPTY: Brownian motion paired with `Y_t = t·I`, capped at `T` |
| `paper_v_usc_unconditional` | **clause (1) for `paper_v`** |
| `paper_pair_class_norm_mean_le`, `paper_pair_class_inner_mean_le`, `paper_pair_class_comp_norm_mean_le` | bounds uniform over the class |

Reusable machinery built for the above, none of it in the AFP — use it, do
not rebuild it:

- matrix-valued martingales: `martingale_matI`, `measurable_mat_entries`,
  `integrable_mat_entries`, `set_integral_mat_component`
  (`Ito_Market.martingale_vecI` does NOT iterate to `real^'n^'n`);
- martingale algebra: `martingale_add`, `martingale_add_const`,
  `martingale_cong_ge`, `martingale_stopped_const`, `martingale_cong_AE`,
  `martingale_time_change`, `martingale_sub_initial`, `martingale_distr`;
- path-law transfer: `pair_law_of`, `martingale_pair_law`,
  `phi_filtration_measurable`;
- the shift: `pshift`, `pshift_law`, `martingale_pshift_law`,
  `AE_pshift_law(_iff)`, `ess_inf_time_pshift_law`, `Lipschitz_pshift`,
  `mdist_pshift_pshift`;
- the `X`-component map: `pfst`, `pfst_measurable`, `pexit_pfst`,
  `Lipschitz_pfst`, `ess_inf_time_pfst`;
- norm/linearity helpers: `norm_outer_prod`, `norm_outerp`,
  `bounded_linear_cross_pair`, `outerp_add`, `outerp_zero`, `outerp_borel`,
  `cross_borel`, `nat_filt_eval`;
- Brownian off-diagonal covariation (the market locale asserts only the
  DIAGONAL `coord_Z_martingale`): `bm_coordinates_indep`,
  `bm_increment_cross`, `bm_meas_increment_fun_indep_var`,
  `bm_cross_set_integral_zero`, `martingale_bm_cross`,
  `martingale_cbm_cross`, `martingale_cbm_outerp`.

### 1.4 Example 3.1 for `n − k = 1` (N4) — closed

`Deterministic_Radius_Market.thy` builds the trig process
`X_t = √(q+t)·(cos(W_{c(t)}+φ), sin(W_{c(t)}+φ))`, `c(t) = ln(1+t/q)`, with
no SDE theory (Gaussian conditional trig expectations only), and
`deterministic_radius_sufficiently_volatile` places it in the locale.
`Theorem_1_1.stopped_val_fn_ball_eq_2d`: `stopped_val_fn 1 L (cball 0 r) x
= ennreal (ball_v r 1 x)` for `0 < |x| ≤ r`.

### 1.5 `paper_v` itself — clauses (0), (1), (3)-ball, and the horizon

- **`paper_v` is bounded** — `paper_v_le_T` (`paper_v k L T K x ≤ ennreal T`).
- **Lemma 2.1's estimate at the class level** — `sconstraint_trace_ge`
  (`n − k ≤ trace a` on the constraint set, via `Pi_proj_le` at the identity
  projection), `bounded_linear_trace`, `trace_outerp`,
  `paper_pair_class_trace_martingale` (`|X|² − trace Y` is a martingale),
  `paper_pair_class_trace_rate`, and

      paper_pair_class_sq_norm_mean_ge:
        x∙x + (n−k)·t ≤ E[X_t ∙ X_t]   for 0 ≤ t ≤ T

  proved at a FIXED time — no stopping, no optional sampling.
- **Clause (3) at the ball** — `paper_v_boundary_zero`: for `k < CARD('n)`,
  `0 < T`, `0 ≤ L`, `norm x = r`, `paper_v k L T (cball 0 r) x = 0`.
- **Example 3.1's bound (3.10)** — `paper_v_le_ball_bound`: for
  `K ⊆ cball 0 r`, `paper_v k L T K x ≤ ennreal ((r*r − x∙x)/(n − k))`.
  Note the bound does NOT mention `T`; the paper uses Itô and optional
  stopping, this proof uses neither.
- **Horizon-cap invisibility** — `paper_v_horizon_stable` (the `≥` half, via
  `paper_pair_class_pcut`, `pexit_pcut_ge`, `ennreal_min_eq`),
  `paper_v_horizon_mono` (the `≤` half, by pasting the Brownian witness onto
  the tail with `paper_pair_class_pglue_law` and `pexit_pglue_ge`), and
  together `paper_v_horizon_eq`: for closed `K ⊆ cball 0 r` and
  `(r²−x∙x)/(n−k) ≤ S ≤ T`, `paper_v k L T K x = paper_v k L S K x`.
  **So `paper_v`, defined on the CAPPED path space, computes the paper's
  uncapped `v` of (1.6).**
- **`theorem_1_1_paper_v_fragment`** bundles clauses (0), (1), (3)-ball and
  horizon invisibility, and its theory text says explicitly what is NOT in it.
- **`paper_v_attained`**: the supremum in (1.6) is a MAXIMUM. §3.1 of the
  paper consumes this independently of the DPP, since that proof opens by
  fixing an optimizer. Route: `paper_pair_class_convergent_subsequence` for a
  weakly convergent subsequence, `Lipschitz_pfst` (with `pfst_mspace`) and
  `Path_Space.weak_conv_on_pushforward` to reach the VECTOR path space where
  `Exit_Semicontinuity.ess_inf_pexit_usc` lives, `ess_inf_time_pfst` to
  transport back, and `ennreal_Sup_countable_SUP` + `LIMSEQ_SUP` +
  `LIMSEQ_subseq_LIMSEQ` to identify the `Limsup` with the supremum.

### 1.6 Pasting with a FIXED or COUNTABLY-CHOSEN continuation

- **(a) closure under shortening the horizon.** `paper_pair_class_pcut`:
  `Q ∈ paper_pair_class k L T x`, `0 ≤ S ≤ T` ⟹
  `pair_law_of S (pcut S) Q ∈ paper_pair_class k L S x`, over `pcut`,
  `pcut_measurable`, `pcut_adapted`, plus the factored-out rational reduction
  `paper_pair_class_diffquot_of_pairs`.
- **(b) concatenation at the path level.** `pglue r T ω ω'` runs `ω` to `r`,
  then `ω'` re-based at `ω r` (`pglue_le/_ge/_zero`, `continuous_on_pglue`,
  `pglue_in_mspace`, `pglue_measurable` via `pathify_measurable`, and
  `pglue_diffquot` — where the `s < r < t` case is a CONVEX COMBINATION of
  the two pieces' quotients, so `sconstraint_convex` is exactly what makes
  pasting legal).
- **(b′) independent concatenation at the law level.**

      paper_pair_class_pglue_law:
        Q ∈ paper_pair_class k L r x ⟹ R ∈ paper_pair_class k L (T−r) 0
          ⟹ 0 ≤ r ≤ T ⟹ pglue_law r T Q R ∈ paper_pair_class k L T x.

  `pglue_law r T Q R = pair_law_of T (λp. pglue r T (fst p) (snd p)) (Q ⨂⇩M R)`
  with `sets_pglue_law`, `space_pglue_law`, `prob_space_pglue_law`, the
  transfer principle `AE_pglue_law`, and clauses (i)–(ii) `pglue_law_start`,
  `pglue_law_diffquot`. New machinery, all reusable and none of it in the AFP:

  | result | content |
  |---|---|
  | `sets_pair_measure_mono`, `filtered_measure_pair` | the pointwise product of two filtrations is a filtration on the product measure |
  | `martingale_pair_fst`, `martingale_pair_snd`, `martingale_pair_snd_param` | a martingale of one factor, read on the product, is a martingale for the product filtration; the `_param` form allows dependence on the other coordinate |
  | `martingale_pair_mult` | the PRODUCT of a first-factor martingale with a second-factor martingale is a martingale — where independence is genuinely used |
  | `distr_pair_snd` | the `snd` twin of the library's `distr_pair_fst` |
  | `pglue_law_X_martingale`, `pglue_law_comp_martingale` | clauses (iii), (iv) of (1.7) for the pasted law |

  **The proof idea worth keeping.** The lifting theorems avoid conditional
  expectations on the product AND any π-λ argument: Fubini turns the set
  integral over `A ∈ F u ⊗ₘ G u` into an iterated integral, and the section
  of `A` at a fixed coordinate is a set of `F u` (resp. `G u`) by
  `sets_Pair2`/`sets_Pair1` — so the FACTOR's `set_integral_eq` applies to it
  directly and the outer integrand is constant. **This recipe does NOT carry
  over to the semidirect product — see §2.1.**

  The compensated clause expands `outerp (Xᵣ + W) − (Yᵣ + ⟨W⟩)` into one
  compensated martingale from each factor plus the cross term
  `Xᵣ ⊗ W + W ⊗ Xᵣ`, handled entrywise through `martingale_matI` and
  `martingale_pair_mult`. The decomposition holds only a.e. — it uses
  `X'(0) = 0` from the second factor — hence `martingale_cong_AE`.
- **(c) a continuation chosen by the endpoint, COUNTABLY.**

      paper_pair_class_kglue_law:
        0 ≤ r ≤ T, Q ∈ paper_pair_class k L r x,
        RR j ∈ paper_pair_class k L (T−r) 0 for every j,
        N measurable for the natural filtration of Q at time r
          ⟹ kglue_law r T N Q RR ∈ paper_pair_class k L T x

  where `kglue r T N p = pglue r T (fst p) (snd p (N (fst p)))` and the
  second factor is `Pi⇩M UNIV RR`, one probability space carrying the whole
  family, and the index enters through `measurable_compose_countable`.
  Supporting: `sets_PiM_mono`, `filtered_measure_PiM`,
  `martingale_PiM_component` (split the coordinate off with
  `distr_pair_PiM_eq_PiM`, use `martingale_pair_fst`, transport back),
  `distr_PiM_component`, `kglue_measurable`, `kglue_law`,
  `prob_space_kglue_law`, `AE_kglue_law`, `kglue_law_start`,
  `kglue_law_diffquot`, `kglue_param_martingale`, `kglue_law_X_martingale`,
  `kglue_law_comp_martingale`.

  Two design points worth keeping:

  - write the cross term's first factor at the FIXED time `r`, not `min u r`.
    Both give the same value, but with `r` fixed, freezing the first
    coordinate turns it into a CONSTANT, so the cross term is a
    bounded-linear image of the second factor's martingale — no product of
    two martingales needed;
  - the integrability split. A summand whose inner integral depends on `ω`
    only through the countably-valued `N ω` is handled by
    `integrable_const_bound` against a class-uniform bound. A summand whose
    inner integral ALSO depends on `ω` continuously is not obviously
    measurable — dominate it by `2‖fst (fst p r)‖·‖b‖`, apply
    `Fubini_integrable` to THAT, and finish with `integrable_bound`.

  **This is a stepping stone, not the final pasting step**: see §1.7's
  negative result about countably-valued selectors.

### 1.7 The measurable selector — Larsson–Ruf Proposition 2.2(ii)

**Headline.** `paper_v_measurable_selector`: for `0 < T`, `1 ≤ L`,
`closed K` there is

    S ∈ borel →⇩M borel_of (weak_conv_topology (mtopology_of (path_metric T)))

with `S y ∈ paper_pair_class k L T 0`,
`pshift_law T y (S y) ∈ paper_pair_class k L T y`, and
`ess_inf_time (pshift_law T y (S y)) (τ_K ∘ fst) = paper_v k L T K y`.
`paper_v_measurable_selector_kernel` restates it with `S` measurable into
`prob_algebra` — a genuine Giry-monad kernel, which is the interface kernel
pasting consumes.

Four layers, all new:

1. **The abstract selection theorem.** `Metric_space.usc_measurable_selection`:
   for a nonempty COMPACT metric space `M`, a payoff
   `f :: 'b ⇒ 'a ⇒ ennreal` usc in the second argument for each parameter in
   `space P`, whose supremum over every CLOSED set is `P`-measurable in the
   parameter, there is `s ∈ P →⇩M borel_of mtopology` with `s x ∈ M` and
   `f x (s x) = Sup (f x ` M)`. **Nothing of this kind is in the AFP or the
   distribution** — grepped for Kuratowski–Ryll-Nardzewski, Jankov–von
   Neumann, `measurable_selection`, `analytic_set`; no hits. Do not look
   again.

   The construction is a GREEDY NESTED BISECTION, not Bertsekas–Shreve's
   analytic-set machinery. `usc_sel_set` is the set reached by an index
   sequence into a dense sequence `z` (`compact_space_dense_seq`, also new);
   each step intersects with the closed ball of radius `2⁻ⁿ⁻¹` around `z j`
   for the LEAST `j` that keeps the set nonempty and does not lower the
   supremum. `usc_sel_good_ex` — such a `j` exists because the balls cover
   the current compact set, so finitely many do, and a supremum over a finite
   union is the maximum of the pieces'. **That step uses NO semicontinuity**,
   so `usc_sel` is total in the payoff and the measurability argument never
   case-splits on it; semicontinuity enters only in `usc_sel_optimal`.

   **Why the greedy recipe.** The chosen index sequence — the CODE — is a
   countably valued function of the parameter, so on each cell of a countable
   measurable partition the whole nested family is a FIXED compact set, and
   for open `U` the preimage `{x. s x ∈ U}` is the countable union of the
   cells whose set lies in `U`. No limits and no analytic sets. Supporting:
   `ennreal_strict_between`, `Least_nat_eq_iff`.
2. **The class is a COMPACT METRIC SPACE.**
   `paper_pair_class_compactin_weak` (the class is `compactin` the
   weak-convergence topology) and `paper_pair_class_compact_metric_space`
   (the three facts the selection theorem consumes:
   `Metric_space (paper_pair_class k L T x) (Levy_Prokhorov.LPm …)`, its
   `mtopology` being the subspace topology of weak convergence, and
   `compact_space` of it).

   AFP `Levy_Prokhorov_Metric` did the work and was ALREADY a session
   dependency — do not rebuild any of it. The `Levy_Prokhorov` locale IS
   `Metric_space`, so `interpret LP: Levy_Prokhorov "mspace m" "mdist m"` is
   one line. `LPmtopology_eq_weak_conv_topology` identifies `LPm.mtopology`
   with `General_Weak_Convergence.weak_conv_topology`, the topology our
   `weak_conv_on` is a `limitin` of; `Prokhorov_Theorem.
   tight_imp_relatively_compact` converts tightness (NC-2);
   `LPm.closure_of_sequentially` reduces the closure to sequences so the
   sequential `paper_pair_class_weak_closed` (NC-3) collapses it; `Submetric`
   restricts the metric.
3. **Joint continuity and joint usc.** `pshift_law_weak_conv_joint`:
   `y_m → y` and `R_m ⇒ R` imply `(y_m)_*R_m ⇒ y_*R`.
   `ess_inf_pexit_pshift_usc`: hence
   `Limsup_m ess_inf_time ((y_m)_*R_m) (τ_K∘fst) ≤ ess_inf_time (y_*R) (τ_K∘fst)`.

   **No tightness is needed**, contrary to the obvious worry. Weak
   convergence may be tested against bounded UNIFORMLY continuous functions
   (`mweak_conv_fin.mweak_conv_eq1`), and shifting a path by a constant
   vector moves it by exactly that vector in the sup metric
   (`mdist_pshift_pshift`), so the test function is displaced uniformly over
   the whole path space and the split
   `|∫f(y_m+·)dR_m − ∫f(y+·)dR_m| + |∫f(y+·)dR_m − ∫f(y+·)dR|` closes.
4. **The assembly.** Two steps of bookkeeping inside
   `paper_v_measurable_selector`: (a) usc IN THE LAW is the joint statement
   along a CONSTANT parameter sequence plus `closure_of_sequentially`;
   (b) `(λy. Sup (f y ` C))` is Borel for closed `C ⊆ 𝒞₀` because
   `{y. c ≤ Sup (f y ` C)}` is closed — `closed_sequential_limits`,
   `compactin_sequentially` for the subsequence, `borel_measurableI_ge`.
   **Attainment of the supremum is NOT needed** for (b), only `b < c` for
   every `b` below `c`. Measurability into the subspace lifts to the ambient
   space for free because the selector lands in the class:
   `s -` (U ∩ 𝒞₀) = s -` U`. `paper_pair_class_shift_image` then turns
   `Sup (f y ` 𝒞₀)` into `paper_v k L T K y`.
   The `prob_algebra` restatement uses
   `Space_of_Finite_Measures.weak_conv_topology_eq_prob_algebra` (which is
   why `Paper_Bridge` now imports that theory) and `Polish_space_path_metric`.

**The negative result that forced all of this.** An ε-version with a
COUNTABLY VALUED selector DOES NOT EXIST: the supremum of a usc function
over a countable dense subset can be strictly smaller than its supremum, so
no fixed countable family of candidates is ε-optimal at every parameter.
Hence §1.6(c)'s `paper_pair_class_kglue_law` cannot be the final pasting
step. The BT09-style ε-cover of the STATE space fails for the mirror reason:
it needs `y ↦ g(y,R)` LOWER semicontinuous, and exit times from a closed set
are upper.

### 1.8 Kernel pasting with a genuine kernel — CLOSED

`ksemi M N Kr = M ⤜ (λω. distr (Kr ω) (M ⨂⇩M N) (Pair ω))`, the Giry
semidirect product: run `M`, then continue with the law the kernel picks.

| result | content |
|---|---|
| `ksemi_sets_kernel`, `ksemi_Pair_measurable`, `ksemi_kernel_measurable` | the plumbing; `measurable_distr2` is exactly the right tool |
| `sets_ksemi` | **its `sets` are the ORDINARY product's**, so every measurability fact already proved for `Q ⨂⇩M R` transfers verbatim by `measurable_cong_sets` |
| `space_ksemi`, `prob_space_ksemi` | |
| `AE_ksemi` | `(AE p in ksemi. P p) = (AE ω in M. AE ω' in Kr ω. P (ω,ω'))` |
| `nn_integral_ksemi` | the same disintegration for nonnegative integrals |
| `kglue_law' r T Kr Q`, `kglue_law'_measurable`, `prob_space_kglue_law'` | the glued law; `pglue_measurable` is REUSED unchanged |
| `AE_kglue_law'` | the almost-sure transfer; its only difference from `AE_kglue_law` is that the second-coordinate property may depend on the FIRST — it has to, since the kernel does |
| `kglue_law'_start` | **clause (i)** of (1.7) |
| `kglue_law'_diffquot` | **clause (ii)** — the first place the kernel's values are required to lie in the class at the origin |
| `kglue_law'_start` … and then, by a CHANGE OF ROUTE, clauses (iii) and (iv) too: | |

**`paper_pair_class_kglue_law'` — the class is closed under concatenation
with a continuation chosen by an ARBITRARY measurable kernel.** The two
martingale clauses were never proved for the semidirect product, because
they never had to be. The martingale route has two real obstructions —
`integral_bind` in the distribution is only for BOUNDED REAL integrands,
and the FIRST-factor martingale property is FALSE for a semidirect product
(the weight `(Kr ω)(A_ω)` in the disintegrated set integral is only
`ℱ_r`-measurable). **Neither has to be faced.**

Instead: the class is weakly closed, the glue with a COUNTABLY valued
index is already in it (§1.6(c)), and the class at the origin is a COMPACT
metric space — hence separable, so any kernel into it is a pointwise limit
of countably valued ones. Round the kernel; each rounded glue is a
legitimate pasting and IS the kernel glue at the rounded kernel; the
semidirect products converge weakly; the glue is continuous; weak
closedness finishes.

| result | content |
|---|---|
| `second_countable_path_metric`, `borel_of_path_prod` | separable + metrizable ⟹ second countable, hence `borel_of X ⨂⇩M borel_of Y = borel_of (prod_topology X Y)` |
| `mdist_pglue_le`, `Lipschitz_pglue` | the glue is 3-Lipschitz from the product metric — the second piece counts twice because it is re-based at its own initial value |
| `integral_ksemi_bounded`, `integral_ksemi_measurable` | the disintegration for BOUNDED REAL integrands — exactly what `integral_bind` covers, and exactly what weak-convergence test functions are |
| `ksemi_weak_conv` | pointwise weak convergence of the KERNELS gives weak convergence of the semidirect products, by dominated convergence over the first coordinate |
| `Metric_space.countably_valued_approx`, `limitin_of_dist_half` | a measurable map into a compact metric space is a uniform limit of countably valued measurable ones; rounding is measurable because `{y. d a y < c}` is an OPEN BALL |
| `kglue_law_eq_kglue_law'` | with a countably valued index the product-of-all-candidates and the semidirect product give the SAME law; both reduce to `∫⁺ω. (RR (N ω)) {ω'. pglue r T ω ω' ∈ A} ∂Q` |
| `paper_pair_class_kglue_law'` | **the headline** |

**Do not restart the martingale route.** Both obstructions are real — in
particular `martingale_pair_fst` has no `ksemi` analogue, and that is a
theorem, not a proof-technique inconvenience.

### 1.9 The `≥` half of (2.9) at a deterministic time — CLOSED

*(Everything in this subsection now lives in `Paper_DPP.thy`, not
`Paper_Bridge.thy` — see the file-layout note in §2.1.)*

The DPP of Prop. 2.4 is

    v(x) = sup_{P ∈ 𝒫ₓ} P-essinf( θ ∧ τ_K + v(X_θ) · 1_{θ ≤ τ_K} ).

At a DETERMINISTIC `θ = r` both summands are read off the first piece:
`θ ∧ τ_K` is the exit time capped at `r`, i.e. `pexit r K`, and the
indicator `1_{θ ≤ τ_K}` is **`pexit r K … = r ∧ fst (ω r) ∈ K`** — that
equivalence is exact for the capped exit time and needs NO path continuity
(the exit set on `[0,r]` is empty iff the infimum is `r` and the endpoint is
still in `K`). Use that form; it is measurable straight off
`pexit_path_measurable` and the coordinate map.

| result | content |
|---|---|
| `paper_v_kpaste_ge` | the kernel analogue of `paper_v_paste_ge`: an a.s. lower bound on the exit time of the SEMIDIRECT-product glue bounds `paper_v` |
| `pexit_pglue_split'` | `pexit_pglue_split` with the continuation only required to stay in `K` on the HALF-OPEN `{0..<c}` — the same proof, and the strict form is what an essential infimum supplies |
| `pexit_pglue_dpp` | **the pathwise DPP bound**: `pexit r K ω + (if survived then c else 0) ≤ pexit T K (pglue r T ω ω')`; off the survival event it degenerates to `pexit_pglue_ge` |
| `paper_v_measurable_selector_kernel'` | the selector packaged with BOTH measurability facts `paper_pair_class_kglue_law'` wants — into `prob_algebra` (its `Kp`) and into the CLASS with its Lévy–Prokhorov metric (its `Kb`). The second is free: the selector lands in the subspace, and `paper_pair_class_compact_metric_space(2)` identifies the class's metric topology with the subspace topology of weak convergence |
| `paper_v_open_less`, `paper_v_neq_top`, `paper_v_borel_measurable` | usc + the horizon bound make `enn2real ∘ paper_v` a random variable — needed to even STATE the integrand |
| `paper_v_dpp_ge_const` | the construction: restrict `P` to `[0,r]` (`paper_pair_class_pcut`), feed the kernel `ω ↦ S (fst (ω r))`, paste, and read off `paper_v_kpaste_ge` |
| `paper_v_dpp_ge` | the same with `ess_inf_time` in place of the constant |
| `paper_v_dpp_sup_ge` | **the headline**: `(SUP P ∈ 𝒫ₓ. essinf(…)) ≤ paper_v k L T K x` |

Two things worth not rediscovering. The `pcut`-invariance of the integrand
is what lets the AE hypothesis be stated on `P` and used on the restricted
law — but `AE_distr_iff` only transfers it because the integrand is
MEASURABLE, which is why `paper_v_borel_measurable` had to be proved first.
And `simp` splits `¬ (A ∧ B)` into an implication and then cannot discharge
an `if` guarded by `A ∧ B`; use `if_not_P` by `rule`.

### 1.10 Supporting layers

Berge/usc (`usc_sup_over_compactin`, `vshift_sup_usc_of_seq_compact`,
`Exit_Semicontinuity.ess_inf_pexit_usc`), the path space and its metric
(`Path_Space`, `path_metric_polish`, `Polish_space_path_metric`),
Doob/optional sampling (`Doob_Inequality`, `Optional_Sampling`), the
Brownian layer (`Brownian_Motion`, `Brownian_Market`, `Brownian_Continuous`,
`Brownian_Stopped`), modification transfer (`Modification_Transfer`),
`pexit_path_measurable`, `paper_v_paste_ge`, `pexit_pglue_split`,
`paper_v_paste_lower`.

---

## 2. What is LEFT

In dependency order. §2.4 and §2.5 are independent of §2.1–§2.3 and can be
interleaved.

### 2.1 The conditioning statement — all that is left of the DPP at a deterministic time

*(This was §2.2 in the numbering used before the 2026-08-07 restructure: it
is the `≤` half of (2.9).)*

`paper_v_dpp_le_of_cond` (proved, §1.9's companion) reduces the `≤` half of
(2.9), hence (2.9) itself at a deterministic time, to ONE hypothesis:

    cond: P ∈ paper_pair_class k L T x ⟹
          (AE ω in P. c ≤ pexit T K (λt. fst (ω t))) ⟹
          (AE ω in P. pexit r K (λt. fst (ω t)) = r ∧ fst (ω r) ∈ K
              ⟶ c ≤ r + enn2real (paper_v k L (T - r) K (fst (ω r))))

*"If `P` survives to time `c`, then on the survival event the value at the
position reached is at least the time still to run."* Everything OFF the
survival event is already unconditional, by `pexit_cap_eq` — a path that has
left `K` by time `r` has the same exit time at either horizon, including the
boundary case of a path that exits exactly AT `r` (`pexit_stable_above_T`
does NOT cover that; it wants `pexit r K f < r`).

**The key structural fact (established 2026-08-07, and it changes the
route).** Conditioning on an event of the PAST does not disturb the FUTURE's
membership in the class:

> for `A ∈ ℱ_r` with `P A > 0`, the law of the rebased future
> `pfut r T ω = (λs. ω (r+s) - ω r)` under `P(· | A)` lies in
> `paper_pair_class k L (T-r) 0`.

The martingale clauses survive because the conditioning density `1_A / P A`
is `ℱ_r`-measurable, hence `ℱ_{r+s}`-measurable for every `s`, so the set
integral over `C ∈ ℱ_{r+s}` simply becomes one over `C ∩ A ∈ ℱ_{r+s}` — no
approximation, no monotone class. That is `paper_pair_class_future_of_past`
(§2.1(a) below). **No regular conditional distribution is needed for class
membership.**

What r.c.d. would still buy is the *localization*: under the conditional law
given `ℱ_r`, the starting point `X_r` is a CONSTANT, so `paper_v(X_r)` can be
compared directly. Conditioning on a positive-measure `A` only makes `X_r`
lie in a small ball, and the comparison then leaks into an ε-enlargement
`K_ε` of the target set. So there are two ways to finish, and they trade one
hard step for another:

| route | remaining obligation |
|---|---|
| **(a) positive-measure conditioning** (`paper_pair_class_future_of_past` — elementary, no AFP `Disintegration`) | usc of `paper_v` in the TARGET SET: `paper_v k L U K⇩ε y → paper_v k L U K y` as `ε ↓ 0`. Provable by the existing compactness/usc machinery generalized to a decreasing sequence `K_n ↓ K` — the witness step is: `ω⇩n → ω` and `ω s ∉ K` give `dist (ω s) K = d > 0`, so `ω⇩n s ∉ K_ε⇩n` once `ε⇩n < d/2`. |
| **(b) regular conditional distributions** (AFP `Disintegration.measure_disintegration`, locale `projection_sigma_finite_standard`; the path spaces are standard Borel by `Path_Space.path_metric_polish`; the entry is NOT yet a session dependency — see (b1)) | the CONDITIONAL martingale property at a.e. `ω`: a countable determining family of test functions plus a monotone-class step to get "a.s., for all `A ∈ ℱ⁰_s`" out of "for each `A`, a.s.". |

Route (a) is preferred: every step is elementary and the K-usc lemma is a
variant of machinery that already exists (`ess_inf_pexit_usc`,
`paper_v_usc`), whereas route (b)'s monotone-class step has no analogue in
the development. A hybrid is also possible — (a) for class membership, (b)
only to make `X_r` constant.

**Already proved for this section** (2026-08-07, all green, no `sorry`):

| result | content |
|---|---|
| `cInf_shift_real` | `Inf ((+) r ` S) = r + Inf S` |
| `pexit_split_at_r` | on the survival event the exit time SPLITS: `pexit T K f = r + pexit (T-r) K (λs. f (r+s))`. The two exit sets are exact translates of one another, so this is an identity, not an inequality |
| `pfut`, `pfut_apply/_zero/_fst`, `pfut_in_mspace`, `Lipschitz_pfut`, `pfut_measurable(_law)`, `pexit_pfut` | the rebased future `ω ↦ (λs. ω (r+s) - ω r)` as a **2-Lipschitz** map of path spaces (the base point is subtracted, so it counts once more) |
| `uniform_measure_density_real`, `integral_uniform_measure_eq`, `integrable_uniform_measureI`, `set_integral_uniform_measure_eq` | the change-of-measure layer for `M(· | A)`, taking `uniform_measure` to a REAL density so `integral_density` / `integrable_density` apply |
| **`martingale_uniform_measure`** | **the structural fact**: `A ∈ sets (F 0)` and `0 < measure M A` ⟹ every `F`-martingale under `M` is an `F`-martingale under `M(· | A)` |

**File layout (2026-08-07).** The value-function layer now lives in
**`Paper_DPP.thy`** (imports `Paper_Bridge`): the pasting bound, the `≥`
half of (2.9), the reduction of the `≤` half, and the conditioning layer.
`Paper_Bridge.thy` keeps the CLASS layer and is back to ~13,100 lines. New
DPP work goes in `Paper_DPP`. Note the PIDE session snapshots `ROOT` at
startup, so a newly registered theory needs a server restart before it can
be loaded — develop-and-verify in `Paper_Bridge`'s tail and move, or restart.

**What is left in route (a), concretely.**

1. ~~`paper_pair_class_future_of_past`~~ — **DONE** (2026-08-07). All four
   clauses of (1.7) for `pair_law_of (T-r) (pfut r T) (P | A)`,
   `A ∈ ℱ_r`, `P A > 0`, via `pfut_law_start` / `pfut_law_diffquot` /
   `pfut_law_X_martingale` / `pfut_law_comp_martingale`. Clause (iv) needed
   four lemmas that existed nowhere: `martingale_mult_measurable`,
   `martingale_cross_measurable`, `integrable_mult_of_sq`, `martingale_diff`.
2. ~~`ℱ_r`-measurability of the survival event~~ — **DONE**,
   `survival_event_filtration`: for continuous paths against a closed `K`,
   "never leaves `K` on `[0,r]`" is decided by the rational times alone.
3. **The usc-in-`K` lemma — this is the whole of what is left, and it is
   HARDER than it looked.** Route (a) localizes by conditioning on
   `A = Surv ∩ {X_r ∈ cball (y⇩i, ε⇩i)}`, which only pins `X_r` to a small
   ball, so the surviving paths are known to stay in `K` around a MOVING
   centre and the comparison lands on the ε-enlargement:

       paper_v (K⇩ε, y⇩i) ≥ c - r   while   paper_v (K, y⇩i) < c - r,

   and closing that gap needs `paper_v k L U K⇩ε y → paper_v k L U K y`.
   **The obvious proof does not work.** Take optimizers `Q⇩n` for `K_{1/n}`,
   extract a weak limit `Q` by compactness, and try Portmanteau on the OPEN
   set `V = {ω. pexit U K ω < c'}`: one needs `Q⇩n V` small, but all that is
   known is `Q⇩n {pexit K_{1/n} < c'} = 0`, and since `pexit K ≤ pexit
   K_{1/n}` the inclusion runs `{pexit K_{1/n} < c'} ⊆ V` — the WRONG way.
   A `Q⇩n` may survive in `K_{1/n}` while leaving `K` at once. No
   counterexample is known either, so the statement is open, not false;
   expect a genuinely different argument (some quantitative control of how
   fast a class member can leave `K⇩ε` but not `K`, e.g. off the
   ball estimates of §1.5).

**ROUTE (b) IS THE CHOSEN PATH (user decision, 2026-08-07).** With item 3
open, route (a) is blocked on a statement nobody has proved. Route (b) got
cheaper at the same time: the conditions defining the class are all LINEAR
in the measure — `μ C = 1` for the start and covariation clauses,
`∫ (X_t - X_s) 1_A dμ = 0` for the martingale clauses — so passing from
"`μ_A ∈ 𝒞₀` for every `A ∈ ℱ_r`" to "`κ ω ∈ 𝒞₀` a.s." needs **no separation
theorem**, only a COUNTABLE determining family (rational times,
rational-corner cylinder sets) plus one Dynkin step at fixed `ω`.

Steps, in order:

| step | content | status |
|---|---|---|
| (b0) | `AE_zero_of_set_integral_zero` — a `𝒢`-measurable function whose `𝒢`-set integrals all vanish is a.e. `0`. THE workhorse: it is what converts each linear condition from "for every `A`" to "at a.e. `ω`" | **DONE** |
| (b1) | the kernel itself: `paper_pair_class_rcd` (the AFP disintegration) and `paper_pair_class_rcd_ksemi` (its conversion to our `ksemi`, via `emeasure_ksemi_rect` and agreement on the rectangle π-system) | **DONE** |
| (b2) | clauses (i)/(ii) for `κ ω` a.s. | general lemma `AE_kernel_full` **DONE**; clause (i) `pfut_rcd_start` **DONE**; clause (ii) is now pure assembly of `ksemi_rect_null_of_AE` → `AE_kernel_full` → `AE_mem_of_emeasure_1` → `AE_ball_countable'` over rational pairs → `paper_pair_class_diffquot_of_rational_pairs`, all four of which are proved |
| (b3) | clauses (iii)/(iv) for `κ ω` a.s. — (b0) for each `(s,t,A')` in a countable determining family, then ONE Dynkin step at fixed `ω` (`measure_eqI_generator_eq` on the positive and negative parts), then rational-to-real by path continuity | open |
| (b4) | assembly of `cond`: under `κ ω` the starting point `X_r ω` is a CONSTANT, so `pshift_law (T-r) (X_r ω) (κ ω) ∈ 𝒞_{X_r ω}` and its essinf is `≤ paper_v` by definition — no localization, no `K_ε` | open |

Budget 400–800 lines. Unlike route (a) it has no open sub-statement.

**The AFP `Disintegration` API, mapped 2026-08-07 — do not re-explore it.**

- `locale projection_sigma_finite X Y ν` assumes only `sets ν = sets (X ⨂⇩M Y)`
  and `sigma_finite_measure (marginal_measure X Y ν)`;
  `projection_sigma_finite_standard = projection_sigma_finite + standard_borel_ne Y`.
- `standard_borel M ⟺ ∃S. Polish_space S ∧ sets M = sets (borel_of S)` — so
  for `Y = borel_of (mtopology_of (path_metric (T-r)))` it is **immediate**
  from `Polish_space_path_metric` with `S` the topology itself; `space_ne`
  needs only one path (the constant `0`, via `mspace_path_metricI`).
- `measure_disintegration` yields `κ` with `prob_kernel X Y κ` and
  `measure_kernel.disintegration X Y κ ν νx`, where
  `νx = marginal_measure X Y ν` and `disintegration` constrains **RECTANGLES
  ONLY**: `ν (A × B) = ∫⁺x∈A. κ x B ∂νx`. The all-sets version is a separate
  predicate `mixture_of`, and the AFP proves only `mixture_of ⟹
  disintegration`, not the converse.

**Therefore the concrete shape of (b1):**

1. `ν := distr P (?BR ⨂⇩M ?MR) (λω. (pcut r ω, pfut r T ω))`, with
   `?BR = borel_of (mtopology_of (path_metric r))` as `X` and `?MR` (horizon
   `T-r`) as `Y`. Then `sets ν = sets (X ⨂⇩M Y)` holds by construction and
   `marginal_measure X Y ν = pair_law_of r (pcut r) P`, a probability
   measure, hence σ-finite.
2. Interpret `projection_sigma_finite_standard` and obtain `κ`.
3. **Then convert to OUR `ksemi`**, rather than fighting the
   rectangles-only form: two probability measures on `X ⨂⇩M Y` agreeing on
   the rectangle π-system are equal (`measure_eqI_generator_eq`), so
   `ν = ksemi νx ?MR κ`. From there `AE_ksemi` and `nn_integral_ksemi` —
   both already proved in `Paper_Bridge` for the kernel-pasting work — give
   the almost-sure and integral forms for free, and no measure-theoretic
   induction from indicators to general integrands is needed.

That reuse of `ksemi` is the point: it is why (b2)/(b3) reduce to
`AE_zero_of_set_integral_zero` plus one Dynkin step, with no bespoke
disintegration calculus.

### 2.2 The DPP at a STOPPING time

At a stopping time `θ` BOTH clocks `u ∧ θ` and `(u − θ)⁺` are random, so the
product-filtration structure that carries §1.6(b′) and §1.9 breaks down. The
literature does the stopping-time version via regular conditional
distributions rather than product measures; expect a different construction.
§3.2 uses the exit time of a small ball, which is not deterministic, so this
IS needed — but it should be attempted only after §2.1, which builds the
r.c.d. layer it will reuse.

Note `paper_v_dpp_ge_const` is already stated for an arbitrary real constant
`c` and an arbitrary a.s. bound, so the deterministic-time machinery
generalizes without restatement once the glue at a random time exists.

### 2.3 §3 — the two viscosity inequalities → clause (2)

**Which half of the DPP feeds which inequality** (read out of §3.1 and §3.2
of the paper on 2026-08-06; do not redo this):

| viscosity inequality | DPP half it consumes |
|---|---|
| **subsolution** (§3.1, display (3.17)) | the DPP **at the optimizer**: `v(x) ≤ t∧θ + v(X(t∧θ))` P-a.s. for the fixed optimizer P. This is the CONDITIONING half, §2.1. |
| **supersolution** (§3.2, after (3.25), and again in Case 2 after (3.30)) | `v(y) ≥ P_y-essinf (τ_{B_ε(x)} + v(X(τ_{B_ε(x)})))` for a SPECIFIC constructed `P_y`. This is the `≥` half, i.e. PASTING — **PROVED at a deterministic time**, §1.9; at `τ_{B_ε}` it needs §2.2. |

Beyond the DPP, §3 consumes machinery this development does not have:
Itô's formula for class members, an exponential local martingale plus
optional sampling ((3.18)–(3.19)), and weak solutions of the SDEs (3.11) and
(3.24). **Budget §3 separately from the DPP.**

### 2.4 Clause (3) for general `n − k ≥ 2`

`n − k = 1` is done (§1.4). The general case needs spherical Brownian
motion — embed the deterministic-radius construction in an `(n−k+1)`-
dimensional coordinate subspace. Planned on the discrete route:
`Random_Walk_Market.thy`, `Relative_Arbitrage_Discrete.thy`,
`Path_Tightness.projective_limit_of_consistent_path_laws`.

### 2.5 `stopped_val_fn ≤ paper_v` (only if §2.4 needs it)

The bridge from market witnesses to class members. NOTE the recorded
obstruction — a `stopped_market` witness is NOT a class member, because the
paper's class never stops; the bridge must CONTINUE the witness past `tau`
with an admissible volatility, and the martingale side needs an independent
Brownian continuation, not just `Paper_Class.acont`. Build this only if
clause (3)/(2) actually need the market-side results transported.

### Fallback

If §2.1–§2.3 and §2.4 both stall, the bounded alternative is the rest of
Section 4 (Theorem 4.2(b), 4.3, Prop 4.1 — 3,000–7,000 lines, reusing the
Crandall–Ishii investment).

---

## 3. Rules of engagement — read before editing

### 3.1 Three ways to lose a session

1. **Never register a NEW theory in `ROOT` mid-session.** The PIDE server
   snapshots `ROOT` at startup; a new node makes every theory report
   "Malformed theory", and reverting the edit does NOT recover it. If new
   material needs an import an existing theory lacks, ADD THE IMPORT to that
   theory — that works fine in-session (this is how
   `Levy_Prokhorov_Metric.Space_of_Finite_Measures` was added to
   `Paper_Bridge`), at the cost of a full reload of that theory.
2. **Route every edit to a PIDE-held file through the MCP `edit` tool.** The
   server treats its own buffer, not the disk, as authoritative; a
   Write/Edit/script/`git checkout` write desyncs it and a later `mcp edit`
   writes the stale buffer back. **The resync tool is `read`.** Files the
   server does NOT hold (e.g. this plan) are fine to edit normally.
3. **Never use `edit_all` without inspecting every occurrence.**

### 3.2 Verifying

- The loop is: `edit` → `get_state` on the touched range. `commands_failed =
  0` with nothing unprocessed IS verification. Reserve `isabelle build -d .
  Arbitrage` (~1.5 min when heaps are warm) for a final cross-check before
  ending a session, and for files PIDE does not hold.
- Do not judge a theory mid-elaboration; counts are not final until 100%.
- Treat `still_running_possibly_nonterminating` as a STOP condition even when
  the same entry says "No subgoals!" — restructure the step.
- Zero `sorry` is an invariant.

### 3.3 Design constraints you must not "simplify"

- **The paper's class has NO stopping** ((1.7)–(1.8)): `X` is a martingale on
  all of `[0,∞)` with the covariation constraint for a.e. `t ≥ 0`, and `τ_K`
  is merely a functional of the path. Do not weaken `paper_pair_class` to
  constrain only up to the exit time — that is a different class.
- **Do not confuse that with the `min t T` in the martingale clauses.**
  Stopping at `τ_K` is forbidden; stopping at the HORIZON `T` is required,
  because the path space is capped there. On `[0,T]` the clause says exactly
  what (1.7) says.
- **The capped path space is EXTENSIONAL**: `ω ∈ mspace (path_metric T)`
  implies `ω u = undefined` for `u ∉ {0..T}`, so any clause quantified over
  unbounded time silently talks about a constant. This made
  `paper_pair_class` empty for a whole session. Every time-quantified clause
  must carry `≤ T` or `min t T`. **Corollary: prove a new path-law class
  NONEMPTY before trusting anything proved about it.**
- `real^'n × real^'n^'n` PARSES AS `real^('n × real)^'n^'n`; use the
  `'n pairpath` synonym.
- `mkt_path_laws` pins the market sample type to `('m ⇒ real ⇒ real)`
  because HOL cannot quantify over sample-space types; keep new market
  constructions on that type.

### 3.4 Proof-engineering traps

The full list lives in the agent memory file
`isabelle-pide-mcp-environment.md`. The ones that have cost the most:

- **Under-constrained types are invisible.** A goal produced by a rule whose
  type instantiation you did not spell out can sit at a type where component
  lemmas no longer match *even though everything prints identically*
  (`continuous_on {0..T} (λt. t *⇩R mat 1)`, twice). Likewise an assumption
  like `paper_pair_class k L T 0 ≠ {}` elaborates its `0` at a fresh type
  variable with no warning. Annotate intermediate statements fully.
- **This dev `linarith` fails on plainly linear goals**; `argo` closes
  exactly those. And a division by a numeral in a premise makes it fail
  outright — restate the arithmetic without divisions.
- **`OF` against a `⋀`-bound premise can leave a schematic in the CONCLUSION.**
  `paper_pair_class_convergent_subsequence[OF T L0 Qm]` with
  `Qm: "⋀i. Qm i ∈ ?C"` produced `(λm. Qm (?i1 m)) ∘ a` — the higher-order
  match instantiated the sequence, not the index. `blast` then searched for
  168 seconds and failed. State the conclusion with an explicit `have` and
  discharge with `(rule …[OF …]) (rule …)` so the conclusion drives
  unification: 4 ms. Related: a `for m`-bound fact used as `prC[OF RmC]`
  carries a schematic index, so a subsequence must be written `(Rm ∘ a)`
  rather than `(λm. Rm (a m))`. And `measurable_sets` wants the measurability
  fact FIRST, so give it by `OF`, not by chaining.
- **`unfolding paper_v_def` unfolds `paper_v` on BOTH sides.** A DPP goal has
  `paper_v k L T K x` on the left and `paper_v k L (T-r) K (fst (ω r))`
  inside the right, so unfolding the definition silently changes the target
  and every later `show` reports "Failed to refine any pending goal" with an
  exported rule that looks identical. Prove a ground equation
  `pv: "paper_v k L T K x = (SUP Q∈…. …)"` by `unfolding paper_v_def ..` and
  `unfold pv` instead.
- **`simp` cannot discharge an `if` guarded by `A ∧ B` from `¬ (A ∧ B)`** —
  it first rewrites the hypothesis to `A ⟶ ¬ B` and then the guard no longer
  matches. Produce the `= 0` equation explicitly with `by (rule if_not_P)`.
  Cost: three separate failures in one session.
- **`ennreal_enn2real` wants `x < ⊤`, not `x ≠ ⊤`** (`OF: no unifiers`), and
  a chained fact carrying schematic variables (`pexit_nonneg[OF T0]` with
  `?K ?f` still open) makes `simp` fail outright rather than ignore it —
  instantiate with `of` first.
- **In the AFP `martingale` locale, use `sets_F_subset`, not `subalgebras`,
  to get `A ∈ sets M` from `A ∈ sets (F i)`.** `subalgebras` plus
  `subalgebra_def` leaves `auto` stuck on a goal that prints as if it were
  one step away. And `prob_space_uniform_measure` has only TWO premises
  (`emeasure M A ≠ 0`, `≠ ∞`) — supplying `A ∈ sets M` first gives
  "OF: no unifiers".
- **`divide_ennreal` will not fire on `1 / ennreal c`** because the literal
  `1 :: ennreal` is not syntactically `ennreal 1`. Insert the step
  `… = ennreal 1 / ennreal c` by hand first.
- **`ess_inf_time_distr` is AMBIGUOUS.** `Section_2_Usc.ess_inf_time_distr`
  takes a set-measurability premise, `Value_Function.ess_inf_time_distr`
  takes `tau ∈ borel_measurable N`. `rule` picks the former and reports
  "OF: no unifiers". Qualify the name.
- **The product-measure symbol is `\<Otimes>` (⨂, U+2A02), not `\<otimes>`
  (⊗, U+2297).** The latter is the ring tensor; every statement containing it
  fails with "Inner lexical error", which does not point at the character.
- **The `⇢` arrow already carries `sequentially`.** Writing
  `((λn. f n) ⇢ L) sequentially` is a TYPE ERROR, not a redundancy.
- **A lemma of the shape `∫ c ∂M = c` is useless as a simp rule on a
  probability space** — simp turns it into `c = 0 ∨ measure (space M) = 1`.
  Apply it `by (rule …)` inside a calculation instead.
