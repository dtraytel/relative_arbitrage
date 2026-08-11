# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Single source of truth for **what is proved, what is left, and in what
order**. Everything named here is machine-checked in PIDE with
`commands_failed = 0`, and there is no `sorry` anywhere in the session.

Last updated 2026-08-09: §2.1's first results (`Paper_Viscosity.thy`) and the
`path_stopping_time` refactor (DONE — see §1.10).
Restructured 2026-08-08, after **the DPP of Prop. 2.4 was proved at a
STOPPING time** (§1.9), which emptied the old §2.1 and renumbered the queue.
§1 is an INDEX of closed work — do not re-derive any of it, and do not expand
it; construction narratives, dead ends and session logs live in
`PLAN_HISTORY.md` and in `git log -p`. §2 is the queue.

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
| (2) | `visc_sol k L (interior K) v` | **DONE — BOTH halves, 2026-08-11.**  Subsolution `Paper_Viscosity.paper_v_visc_subsol`, with the paper's own operator (1.9), orthogonality included, in the envelope-FREE form (STRONGER than Def. 3.1(a)).  Supersolution `Paper_Viscosity.paper_v_supersol_lsc`, Def. 3.1(b) verbatim, plus `paper_v_supersol_lsc_bounded` with the horizon hypothesis discharged for bounded `K`.  Gaps 1 and 2 CLOSED; no stochastic integration and no weak SDE solution anywhere — §1.10 |
| (3) | `v = 0` on `K − interior K` | ball case **DONE for `paper_v`** (`paper_v_boundary_zero`); interior value REALIZED for `n−k=1` (`Theorem_1_1.stopped_val_fn_ball_eq_2d`); general `n−k ≥ 2` **OPEN**, §2.2; transfer to `paper_v` §2.3 |
| (4) | uniqueness | **DONE** — `Theorem_1_1.theorem_1_1_uniqueness_general`, and since 2026-08-11 stated over the paper's **Definition 3.1** rather than the repo's stronger envelope-free notions, so it is Theorem 4.2(a) as written — §1.11 |
| (2)+(4) | `paper_v` IS the solution | **DONE modulo continuity** — `Theorem_1_1.paper_v_unique_viscosity_solution`.  The join needed Theorem_1_1 to import Paper_Viscosity: clause (2) lived in a LEAF and the comparison principle in Comparison_Assembly, so the two had never been visible to each other.  Open: continuity of `paper_v`, §2.0 |

**Three value functions exist**, and the theorem must end up about ONE.
`val_fn` (all `sufficiently_volatile_market` instances), `stopped_val_fn`
(the locale plus the paper's stopped/killed side conditions) and `paper_v`
(the class (1.7) as pair laws). Clauses (0), (1), (2), (3)-ball and (4)
are proved for `paper_v` itself. What still lives only on the market-side
functions is the `n−k=1` realization inside clause (3)
(`stopped_val_fn_ball_eq_2d`); transferring it is §2.3, and it is needed
only if §2.2 turns out to want it.

**Where the DPP stands — Prop. 2.4 IS PROVED, INCLUDING AT A STOPPING TIME.**
At a deterministic time: `paper_v_dpp` (2026-08-07, §1.7), `≥` from the
measurable selector and kernel pasting (§1.6), `≤` from the regular conditional
distribution. At a stopping time: `paper_v_dpp_sup_ge_time` (2026-08-08, §1.9)
and `paper_v_cond_time`. **The DPP is no longer a blocker for anything.** The
alternative route through positive-measure conditioning is a dead end and stays
one — see §1.7.

**Remaining budget, roughly.**

| item | § | lines | risk |
|---|---|---|---|
| continuity of `paper_v` on `K` | 2.0 | ? | the ONLY thing between clause (2) and a characterisation; properly the paper's Theorem 4.3 |
| clause (3) for `n−k ≥ 2` | 2.2 | 1,500–3,000 | high — needs spherical Brownian motion |
| `stopped_val_fn ≤ paper_v` | 2.3 | ? | only if §2.2 wants it |

Closed since this table was last priced, and moved into §1: the two viscosity
inequalities (was §2.1, now §1.10 — and the weak SDE solution the table feared
turned out not to be needed) and the uniqueness interface (now §1.11).

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

### 1.6 Pasting, the measurable selector, and kernel pasting — ALL CLOSED

The three layers Prop. 2.4's `≥` half is built from. **Construction
narratives archived** to `PLAN_HISTORY.md` ("Archived 2026-08-07 (late):
old §1.6–§1.8); what follows is the index plus the results that are
warnings.

**(a) Shortening the horizon.** `paper_pair_class_pcut` (over `pcut`,
`pcut_measurable`, `pcut_adapted`, `paper_pair_class_diffquot_of_pairs`).

**(b) Concatenation.** `pglue r T ω ω'` runs `ω` to `r`, then `ω'` re-based
at `ω r` (`pglue_le/_ge/_zero`, `continuous_on_pglue`, `pglue_in_mspace`,
`pglue_measurable`, `pglue_diffquot` — where the `s < r < t` case is a CONVEX
COMBINATION of the two pieces' quotients, so `sconstraint_convex` is exactly
what makes pasting legal). At the law level with an INDEPENDENT continuation:
`paper_pair_class_pglue_law`, over `sets_pglue_law`, `AE_pglue_law`,
`pglue_law_start/_diffquot/_X_martingale/_comp_martingale`, and the
product-filtration lifting layer `filtered_measure_pair`,
`martingale_pair_fst/_snd/_snd_param/_mult`, `distr_pair_snd`.

**(c) A continuation chosen COUNTABLY.** `paper_pair_class_kglue_law`, over
`filtered_measure_PiM`, `martingale_PiM_component`, `distr_PiM_component`,
`kglue_measurable`, `kglue_law_start/_diffquot/_X_martingale/_comp_martingale`.
A stepping stone only — see the negative result below.

**(d) The measurable selector — LR Prop. 2.2(ii).**
`paper_v_measurable_selector`: for `0 < T`, `1 ≤ L`, `closed K` there is a
Borel `S` with `S y ∈ 𝒞₀`, `pshift_law T y (S y) ∈ 𝒞_y`, and
`ess_inf_time (pshift_law T y (S y)) (τ_K ∘ fst) = paper_v k L T K y`;
`paper_v_measurable_selector_kernel` restates it as a Giry kernel. Built from
`Metric_space.usc_measurable_selection` (a GREEDY NESTED BISECTION — **there
is no Kuratowski–Ryll-Nardzewski, Jankov–von Neumann, `measurable_selection`
or `analytic_set` anywhere in the AFP or the distribution; do not look
again**), `paper_pair_class_compact_metric_space` (AFP
`Levy_Prokhorov_Metric` does the work — do not rebuild it), and
`pshift_law_weak_conv_joint` / `ess_inf_pexit_pshift_usc`.

**(e) Kernel pasting.** `ksemi M N Kr` is the Giry semidirect product;
`sets_ksemi` says **its `sets` are the ORDINARY product's**, so every
measurability fact proved for `Q ⨂⇩M R` transfers by `measurable_cong_sets`,
and `AE_ksemi` / `nn_integral_ksemi` / `integral_ksemi_bounded` give the
disintegration. Headline: `paper_pair_class_kglue_law'` — the class is closed
under concatenation with an ARBITRARY measurable kernel.

**Two negative results. Do not restart either route.**

1. **A countably valued ε-selector DOES NOT EXIST.** The supremum of a usc
   function over a countable dense subset can be strictly smaller than its
   supremum, so no fixed countable family is ε-optimal at every parameter.
   Hence (c) cannot be the final pasting step. The BT09-style ε-cover of the
   STATE space fails for the mirror reason: it needs `y ↦ g(y,R)` LOWER
   semicontinuous, and exit times from a closed set are upper.
2. **The martingale clauses are FALSE for the semidirect product** — the
   first-factor martingale property fails, because the weight `(Kr ω)(A_ω)`
   in the disintegrated set integral is only `ℱ_r`-measurable; and
   `integral_bind` is bounded-real only. `martingale_pair_fst` has no `ksemi`
   analogue, and that is a theorem, not an inconvenience. (e) sidesteps both
   by ROUNDING the kernel to countably valued ones and using weak closedness.


### 1.7 The DPP at a deterministic time (Prop. 2.4) — CLOSED

*(All of it lives in `Paper_DPP.thy`, not `Paper_Bridge.thy`; see §3.1.)*

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

(The `pcut`-invariance of the integrand is what lets the AE hypothesis be
stated on `P` and used on the restricted law — but `AE_distr_iff` only
transfers it because the integrand is MEASURABLE, which is why
`paper_v_borel_measurable` had to come first.)

**Both halves together — `paper_v_dpp`.** For `0 ≤ r < T`, `1 ≤ L`,
`closed K`,

    paper_v k L T K x
      = (SUP P ∈ 𝒫ₓ. ess_inf_time P (λω. pexit r K (X ω)
          + (if pexit r K (X ω) = r ∧ fst (ω r) ∈ K
             then enn2real (paper_v k L (T−r) K (fst (ω r))) else 0)))

The `≥` half is the table above. The `≤` half is `paper_v_dpp_le_of_cond`
with its one hypothesis discharged by `paper_v_cond`, proved through the
REGULAR CONDITIONAL DISTRIBUTION — which is the authors' own route: the paper defers
Prop. 2.4 to Larsson–Ruf Prop. 2.2(iii), and LR condition with an r.c.d.
citing Stroock–Varadhan Thm 1.3.4.

| step | result |
|---|---|
| (b0) | `AE_zero_of_set_integral_zero` — a `𝒢`-measurable function whose `𝒢`-set integrals all vanish is a.e. `0`. It is what converts each clause from "for every `A`" to "at a.e. `ω`" |
| (b1) | `paper_pair_class_rcd` (AFP `Disintegration`) and `paper_pair_class_rcd_ksemi`, converting it to the development's own `ksemi` — after which `AE_ksemi` and `nn_integral_ksemi` come free |
| (b2) | `pfut_rcd_start`, `pfut_rcd_diffquot` — clauses (i), (ii) |
| (b3) | `pfut_rcd_X_martingale`, `pfut_rcd_comp_martingale` — clauses (iii), (iv); with (b1)/(b2) they package as `paper_pair_class_rcd_member`: `AE p'. κ p' ∈ 𝒞₀` |
| (b4) | `paper_v_cond` — the conditioning statement, hence `paper_v_dpp` |

**Three things worth keeping.** Everything else — the route (a) analysis, the
AFP `Disintegration` API map, the blow-by-blow of (b0)–(b4) — is in
`PLAN_HISTORY.md` under "Archived 2026-08-07 (late)".

1. **Route (a), conditioning on a positive-measure event, is a DEAD END, and
   route (b) is why that no longer matters.** Route (a) pins `X_r` only to a
   small BALL, so the comparison leaks into an ε-enlargement and needs
   `paper_v k L U K_ε y → paper_v k L U K y`; nobody has proved that, and the
   obvious portmanteau argument runs the WRONG WAY (`pexit K ≤ pexit K_ε`, so
   the set inclusion goes backwards). Under `κ p'` the starting point is a
   single VECTOR, so no enlargement ever appears. **Do not revisit route (a).**
2. **Two quantifiers must be made countable, and by DIFFERENT means.**
   *The conditioning set* `A'`, by a countable π-system: `ℱ_s` IS the pullback
   of the `s`-path space's Borel sets along `pcut s`
   (`sets_natural_filtration_eq_pcut_vimage`), so a countable base of that
   space closed under finite intersections works, and
   `set_integral_zero_of_generator` widens it back to all of `ℱ_s`. Do NOT
   build the π-system from the coordinate EVALUATIONS — that forces the time
   index down to the rationals and then needs a
   limit-of-measurable-functions argument; through `pcut`, path continuity
   already sits in the TOPOLOGY and second countability does the rest.
   *The time* `i`, by rationals, widened back with UNIFORM INTEGRABILITY
   (`integrable_and_set_integral_eq_of_rational_times`, built on
   `Conditional_UI.unif_integrable_of_averaging` and
   `Vitali_Convergence.vitali_convergence` — both already in the repo, and
   written for exactly this). **No Doob `L²` bound and no integrable running
   supremum are needed**; an earlier version of this plan budgeted them,
   wrongly. The same UI argument also supplies integrability at the
   irrational times, which is not otherwise available (it is an a.s.
   statement in `p'`, so only countably many times are reachable).
3. **Express the coupling through `pglue`, not `pshift`.** The hypothesis
   `c ≤ τ_K(ω)` has to become a MEASURABLE property of
   `(pcut r ω, pfut r T ω)` before the r.c.d. can see it. `pglue_pcut_pfut`
   says gluing the past back onto the rebased future recovers the path, and
   `pglue_measurable` composed with `pexit_path_measurable` gives the
   measurability off the shelf. `pshift` is Lipschitz in the path only for a
   FIXED shift, so the joint version would have to be built.

Reusable machinery this produced, none of it path-specific and none of it in
the AFP: `sets_natural_filtration_path` (the coordinate evaluations GENERATE
the path space's Borel sets), `sets_natural_filtration_mono`,
`natural_filtration_cong_space`, `subalgebra_natural_filtration_path` and its
`sigma_finite_` twin, `set_integral_zero_of_generator` (the Dynkin step),
`AE_integrable_ksemi_section` and `integral_ksemi_real` (the unbounded
Bochner disintegration, Banach valued),
`martingale_of_rational_set_integral_eq`, and
`paper_pair_class_pfut_comp_martingale` (extracted so both conditioning
routes share it).

### 1.8 Supporting layers

Berge/usc (`usc_sup_over_compactin`, `vshift_sup_usc_of_seq_compact`,
`Exit_Semicontinuity.ess_inf_pexit_usc`), the path space and its metric
(`Path_Space`, `path_metric_polish`, `Polish_space_path_metric`),
Doob/optional sampling (`Doob_Inequality`, `Optional_Sampling`), the
Brownian layer (`Brownian_Motion`, `Brownian_Market`, `Brownian_Continuous`,
`Brownian_Stopped`), modification transfer (`Modification_Transfer`),
`pexit_path_measurable`, `paper_v_paste_ge`, `pexit_pglue_split`,
`paper_v_paste_lower`.

---
### 1.9 The DPP at a STOPPING time — CLOSED 2026-08-08

**`paper_v_dpp_sup_ge_time`** (Paper_DPP): for any path stopping time `θ`,
`closed K`, `1 ≤ L`, `0 < T`,

    (SUP P ∈ paper_pair_class k L T x. ess_inf_time P
       (λω. pexit (θ ω) K X + (if survived then v(T − θ ω, X_(θ ω)) else 0)))
      ≤ paper_v k L T K x

With `paper_v_cond_time` (the `≤` half, 2026-08-07) this closes **Prop. 2.4 at
a stopping time**. This was §2.1 of the queue until 2026-08-08; nothing in it
is open, and §2 has been renumbered accordingly.

**The architecture.** The split at `θ` is ADDITIVE and stays on ONE clock:

    pstopped T θ ω t = ω (min t (θ ω))   pafter T θ ω t = ω (max t (θ ω)) − ω (θ ω)
    padd T p' w      = restrict (λt. p' t + w t) {0..T}

Reassembly is addition, so it never needs `θ` back, and the random horizon
`T − θ` never appears as a SPACE. The continuation lives on the fixed
`T`-space as a DELAYED law (`pdelclass k L T s`, the `pembed s T`-image of
`paper_pair_class k L (T−s) 0`).

| piece | theorem |
|---|---|
| glue is in the class | `paper_pair_class_aglue`; with the kernel, `paper_pair_class_aglue_selector` |
| kernel = selector | `selker`, `selker_measurable`, `paper_v_measurable_selector_horizon` |
| pathwise DPP bound | `pexit_padd_dpp`, `pexit_delayed_rebase` |
| law-level exit bound | `aglue_law_pexit_ge`, `selector_value_AE` |
| past factor (8 clauses) | `pstopped_law_prob/_start/_idem/_diffquot/_cont/_horizon_component/_horizon_compensated` |
| kernel (9 clauses) | `pdelclass_prob/_frozen(_at)/_diffquot/_X_mean/_comp_mean/_X_int/_comp_int/_X_increment/_comp_increment` |
| side conditions (6) | `aglue_law_X_integrable`, `aglue_law_comp_integrable`, `aglue_msec_X/_C`, `aglue_gint_X/_C` |
| assembly | `paper_v_ge_of_stopped_bound`, `paper_v_dpp_ge_const_time` |

#### The five findings that made it work — do NOT re-derive or re-attempt

1. **The horizon enters `paper_v` only as a CAP.**
   `paper_v_horizon_cap`: `paper_v k L S K x = min (paper_v k L T K x) (ennreal S)`
   for `0 ≤ S ≤ T`, because `pexit S K f = min (pexit T K f) S`
   (`pexit_min_horizon`) and capping commutes with `ess_inf_time`
   (`ess_inf_time_min_const`) and with the sup over the class.
   **Consequence: the optimizer is horizon-INDEPENDENT.** The
   "horizon-parametrised selector", recorded for two sessions as a genuine new
   measurable-selection theorem, is the FIXED-horizon selector pushed forward
   along `pembed`, with `s` clamped to `[0,T]` (`pdel`) so the parameter can
   live in plain `borel`. **Do NOT build compactness of `pdelclass k L T s`,
   closedness of `⋃_s pdelclass k L T s`, or a graph-space selection.** The
   proof touches no topology at all.
   The same identity later closed the LAST gap: `paper_v` at a random horizon
   is measurable with no joint-measurability theorem
   (`enn2real_paper_v_horizon_cap`, `dpp_integrand_measurable_stopping`).

2. **Delaying is a TIME CHANGE.** A delayed path read at `u` is the base path
   read at `ρ u = min (max (u−s) 0) (T−s)`, nondecreasing, so
   `martingale_time_change` gives a martingale for the time-changed filtration
   `ℱ^μ_(ρ u)` — and that is the filtration `martingale_pair_law` needs to push
   it forward along `pembed`. Using the base's OWN filtration makes the
   statement FALSE. Hence `pdelclass_X_martingale`, `pdelclass_comp_martingale`.
   For the STOPPED past there is NO time change — a stopped path carries no
   more information than the past — so `pstopped_law_horizon_*` uses `P`'s own
   filtration.

3. **Clause (iv) for the additive glue needs no weak-closedness detour.** The
   deterministic `paper_pair_class_kglue_law'` rounds the kernel and appeals to
   `paper_pair_class_weak_closed`; the additive split is INVERTIBLE
   (`pstopped_padd`, `pafter_padd`) and the conditioning set collapses, so a
   four-cell split on `{θ ≤ i}` does it directly. The outer step is NOT
   pointwise: on `{θ > i}` the inner integrals genuinely differ and only their
   `Q`-integral over that event vanishes.

4. **`pafter` is the DELAYED future.** Its time index is ABSOLUTE, so the
   sampling family is `u ∨ θ`, NOT the offset family `(θ+i) ∧ T`. A whole layer
   was first built for the offset family and none of it instantiates;
   `stopped_increment_of_horizon_gen` is the version to use.

5. **Discretising `θ` cannot give the INEQUALITY.** For `θ_n ≥ θ` finite-valued
   there are paths where `integrand_θ > integrand_(θ_n)`, so
   `paper_v_dpp_ge_const_list` cannot be lifted; approximating from below fails
   in mirror image. (Rounding `θ` is fine for class MEMBERSHIP — a different
   use — but the assembly does not need that either.)

#### Two hypothesis defects found here, and the rules they teach

* **Never state a hypothesis about a path law POINTWISE on its space.**
  `sets N = sets ?B_T` forces `space N` to be EVERY continuous path, so
  `⋀w. w ∈ space N ⟹ P w` is unsatisfiable for any `P` that depends on the law.
  `Kfr`, `K0` and `Qst` were all written that way; `K0` was deleted (it is
  `Kfr` at `u = 0`) and the other two became `AE`. Weakening later is not free:
  the consumers use the fact pointwise inside
  `Bochner_Integration.integral_cong[OF refl]`, and moving to
  `set_lebesgue_integral_cong_AE` then demands measurability of the integrands
  at a RANDOM time.
* **Constrain a conditioning set in the space it is READ IN.** `gintX`/`gintC`
  quantified over `BB` and `i` unconstrained. That is not merely weak: whether
  `w ↦ indicator BB (pcut i (padd T p' w)) · …` is measurable depends on `p'`,
  so for a non-measurable `BB` the outer function is neither the intended
  integral nor uniformly zero. The right hypothesis is
  `BB ∈ sets (borel_of (path_metric i))` — the `i`-horizon space, since `pcut i`
  lands there — plus `0 ≤ i ≤ T` where `i` is bound by the hypothesis rather
  than by the lemma. Ordering the premises that way let every pass-through
  match shape-for-shape; only the two innermost calls discharge anything.

#### Reusable machinery this produced

`martingale_time_change_cong`, `martingale_cong_ge`,
`horizon_sq_int_martingale_stopped` (Doob's `Dsup` supplies both the dominating
function `optional_stopping` wants and the square-integrability that promotes
the conclusion back to a `horizon_sq_int_martingale`; the original
`paper_pair_class_stopped_coord_martingale` used its localisation time only
through nonnegativity and the stopping property, so it generalised verbatim),
`integrable_ksemi_fst`, `integrable_ksemi_of_bound`,
`integrable_ksemi_of_past_bound` (the inner bound may be a FUNCTION of the past
— that is what the quadratic `outerp` cross terms need),
`integral_kernel_measurable` (state it CURRIED: paired, `OF` cannot unify
`?g (ω,ω')` against a beta-reduced integrand), `aglue_section_measurable`,
`aglue_section_integrable`, `path_eval_natural_filtration`,
`pstopped_eval_filtration` (the stopped path is adapted AS A PATH POINT — read
it off the `u`-cut; no componentwise decomposition),
`pstopped_fixed_set_measurable`, `pexit_min_horizon`, `ess_inf_time_min_const`,
`ess_inf_time_mono`, `padd_comp_norm_le` (`outerp_add` + `norm_outer_prod`),
`pdelclass_norm_mean_le`, `pdelclass_comp_norm_mean_le`.

---

### 1.10 Clause (2): the two viscosity inequalities — CLOSED 2026-08-11

**Which half of the DPP feeds which inequality** (read out of §3.1 and §3.2
of the paper on 2026-08-06; do not redo this):

| viscosity inequality | DPP half it consumes |
|---|---|
| **subsolution** (§3.1, display (3.17)) | the DPP **at the optimizer**: `v(x) ≤ t∧θ + v(X(t∧θ))` P-a.s. for the fixed optimizer P. This is the CONDITIONING half — **PROVED at a deterministic time**, §1.7. |
| **supersolution** (§3.2, after (3.25), and again in Case 2 after (3.30)) | `v(y) ≥ P_y-essinf (τ_{B_ε(x)} + v(X(τ_{B_ε(x)})))` for a SPECIFIC constructed `P_y`. This is the `≥` half, i.e. PASTING — **PROVED at a deterministic time**, §1.7, and **at a STOPPING time**, §1.9 — so `τ_{B_ε}` is covered. |

The paper's §3 uses Itô's formula for class members, an exponential local
martingale plus optional sampling ((3.18)–(3.19)), and weak solutions of the
SDEs (3.11) and (3.24). **The first two turned out to be avoidable** — see the
Gap 1 and Gap 2 entries below — and the SUBSOLUTION half is now proved without
any of them. Only the weak SDE solution is genuinely needed, and only for the
supersolution half.

#### Progress 2026-08-09 — `Paper_Viscosity.thy` (1,300 lines, green, 0 `sorry`)

**Itô is NOT needed for quadratic test functions**, and that removes the
first blocker outright. `z ∙ (M *v z) = trace (M ** outerp z)` is a LINEAR
functional of clause (iv) of (1.7), so the expansion is exact:

    paper_pair_class_quadform_mean:
      E[X_t ∙ (M *v X_t)] = x ∙ (M *v x) + trace (M ** E[Y_t])
    paper_pair_class_Y_mean_sconstraint:
      (1/t) ⋅ E[Y_t] ∈ sconstraint k L
    paper_pair_class_quadratic_mean:
      E[φ(X_t)] − φ(x) = (t/2) ⋅ trace (M ** b),  b ∈ sconstraint k L

The second holds because EVERY condition defining `sconstraint` is a linear
(in)equality in the matrix — `psd`/`eigen_ub` constrain `z ∙ (a *v z)`, and
`Pi_proj_ge` turns the projection bound into an intersection of half-spaces
`m−k ≤ trace (a ** P)` — so the set passes through the Bochner integral.

**Proved:** `paper_v_subsol_quadratic_global` — for a quadratic touching
`enn2real ∘ paper_v` from above GLOBALLY at `x`, `ell_op_s k L M ≤ 1`. Route:
`paper_v_attained` → a.s. exit bound → `paper_v_cond_time` at the CONSTANT
time `T/2` → `enn2real_paper_v_horizon_cap` → touching → integrate. **No
stopping time anywhere.**

**Why the subsolution and not the supersolution:** the `≤` half of the DPP is
an ALMOST SURE bound and a.s. bounds survive integration; the `≥` half needs
a LOWER bound on an essential infimum, which no mean gives.

**Two gaps were named at that point. BOTH ARE NOW CLOSED** — see the two
dated entries below. Kept because the dead routes are still worth not
retrying.

1. **Localisation** (local touching → global). Two routes were checked and
   PROVABLY FAIL; do not retry: (a) penalising by `A|·−x|²` does globalise
   (since `paper_v ≤ T`) but shifts the Hessian to `M + 2A·1`, and
   `trace b ≥ n−k > 0` makes the conclusion `−trace(M**b)/2 ≤ 1 + A·trace b`
   strictly weaker; (b) splitting the integral off the ball leaves a LINEAR
   error term `p ∙ (X_h − x)` of order `O(h)/ε` — the same order as the term
   it is compared against — even though a fourth moment handles the quadratic
   part at `O(h^{3/2})`. What works is STOCHASTIC localisation at `τ_ball ∧ h`,
   which needs optional sampling, which needed `path_stopping_time` weakened to
   the path space — **that refactor is now DONE**, see below.

2. **Orthogonality — CLOSED 2026-08-10, see below.** (1.9) infimises over
   `feasible` (`a *v p = 0`); the class
   only constrains covariation to `sconstraint`. `feasible ⊆ sconstraint`
   (`feasible_subset_sconstraint`), hence `ell_op_s ≤ ell_op`: the relaxed
   statement is WEAKER for a subsolution and STRONGER for a supersolution
   (`visc_supersol_s_imp_visc_supersol`). **So attack the supersolution half
   entirely in `ell_op_s` — Gap 2 does not arise there at all.**

**What the constraint `a *v p = 0` is FOR** (`paper_pair_class_frozen_direction`,
proved): a direction annihilated by the averaged covariation is FROZEN a.s.
For a quadratic with gradient `q` at `x`, feasibility kills the first-order
term `q ∙ (X_t − x)` identically, leaving a purely second-order increment —
which is the device that makes an essential infimum and a mean agree to first
order. That is why the constraint sits in (1.9) and not in (1.7), and why the
supersolution half is the one that needs it.

#### The `path_stopping_time` refactor — DONE 2026-08-09

`path_stopping_time`'s congruence clause now constrains only CONTINUOUS paths.
`Paper_DPP` verifies clean end to end (19,106 commands, 0 errors, 0 `sorry`),
and `Paper_Viscosity.pball_exit_path_stopping_time` is the payoff: **the exit
time of a ball is a legitimate stopping time**, so `paper_v_dpp_sup_ge_time`
applies at it and optional sampling at `τ ∧ h` is available.

Three things worth not re-deriving:

* **BOTH paths must be continuous, not just the first.** The one-sided version
  (which the asymmetry of `pexit_cong_stopping` suggests, and which halves the
  work) is REFUTED by `path_stopping_time_min`: on the branch `θ ω > i` it
  argues by contradiction *from the perturbed path*. Two-sidedness is free
  everywhere else — every perturbed path here is a `pstopped` or `padd` of a
  continuous one.
* **The restriction is forced, not chosen.** `pexit_mem_of_less_T`: attainment
  of the infimum genuinely fails off the path space, so no redefinition of an
  exit time could have avoided it. And it costs nothing, since
  `space Q = mspace (path_metric T)` IS the set of continuous paths.
* **Three helpers carry the whole thing** — `path_sets_fst_continuous`
  (continuity from space membership), `pstopped_fst_continuous`,
  `padd_fst_continuous` — and each consumer is one of two shapes: thread a `cw`
  hypothesis through a pathwise lemma, or, where `ω` ranges over a SPACE,
  supply continuity per `ω` via `Collect_cong` / `eventually_elim` with
  `AE_space` chained in.

#### Gap 1 (localisation) — DONE 2026-08-10

`Paper_Viscosity.paper_v_visc_subsol_s`: **`enn2real ∘ paper_v` is a viscosity
subsolution on `interior K` for the relaxed operator `ell_op_s`**, for every
`0 < T`, `1 ≤ L`, closed `K`. Verified end to end (2,747 lines, 0 `sorry`).
The chain: `pball_exit_measurable` (closed-complement route: attainment via
`etime_le_iff` + rationals of `[0,t]` + `t`; ~200 lines, the only genuinely
new piece, as predicted), `pball_exit_stays_cball` (IVT),
`integral_pos_of_AE_pos` (archimedean exhaustion — no `AE_False` gymnastics),
optional sampling read off the ALREADY-PROVED stopped-law martingales
(`pstopped_law_horizon_component/_compensated` at horizon `T`, transported
along `pair_law_of` as a `distr` — no new probability),
`paper_pair_class_Y_stopped_mean_sconstraint` (the weighted half-space
argument), `paper_v_subsol_quadratic_ball` (exact expansion at the stopping
time — no remainder anywhere), `test_fun_quadratic_dominates` (Taylor bump,
one-dimensional along rays via `DERIV_nonpos_imp_nonincreasing`), then
`δ → 0` through `sconstraint_trace_le` + `field_le_epsilon`.

Traps recorded for reuse: two 288-second simp loops from
`fun_eq_iff + divide_inverse + ac_simps` on large integrands (use
`bounded_linear (λr. r/2)` instead); scaleR-cancellation simp rules mangle
matrix equalities into disjunctions (project entries with `arg_cong`, cancel
with `mult_left_cancel`); `etime_le_iff` needs `where`-instantiation (the
higher-order unifier picks a constant path); the `$`-projection DISTRIBUTES
over matrix differences under simp, so entrywise mean facts must be stated in
distributed form where simp will compare them.

#### Gap 2 (orthogonality) — DONE 2026-08-10, and NOT by the paper's route

`Paper_Viscosity.paper_v_visc_subsol`: **`enn2real ∘ paper_v` is a viscosity
subsolution on `interior K` for `ell_op` itself** — the operator of Eq. (1.9),
orthogonality constraint included — for every `0 < T`, `1 ≤ L`, closed `K` and
`k < CARD('n)`. `paper_v_visc_subsol_s` (the relaxed form) is kept as the
intermediate result, because the supersolution half should be attacked there.

**The paper's route ((3.13)–(3.19)) was NOT used and should not be built.** It
kills the non-orthogonal times with an exponential local martingale under
optional sampling at `τ_{B_ε} ∧ v(x)`, which needs stochastic integrals against
the class member. Two elementary steps replace it.

1. **Anti-concentration** (`paper_v_touch_near_orth`, ~700 lines). The touching
   inequality here is ALMOST SURE, so one positive-probability fluctuation
   contradicts it — no measure change. At `θ' = τ_{B_ε} ∧ t` with `t = βε²`,
   `β = 1/(2n²L)`: the increment `W = q ∙ (X_{θ'} − x)` is **BOUNDED** by `|q|ε`,
   has mean `0`, and variance exactly `q ∙ (E[Y_{θ'}] *v q)`
   (`paper_pair_class_stopped_var` — the frozen-direction identity), while the
   touching forces `W⁻ ≤ t + C_M ε²/2` a.s. **Boundedness replaces the fourth
   moment**: an indicator split bounds `E[W⁻]` above by `|q|²ε²` times a tail
   probability and below by the variance, and Chebyshev on the exit
   (`ε² P(τ < t) ≤ trace E[Y] ≤ n²Lt`) gives `E[θ'] ≥ t/2`. For `ε < εK` the two
   bounds collide. **So the planned Doob / `Increment_Moments` fourth-moment
   detour was unnecessary — do not build it.** Output: for every `ε₀ > 0` a
   `b ∈ sconstraint k L` with `−trace(M**b)/2 ≤ 1` and `q ∙ (b *v q) < ε₀`.
   `paper_v_touch_orth` then takes the limit: `bounded_sconstraint` +
   `closed_sconstraint` give `b*` with `q ∙ (b* *v q) = 0`, hence `b* *v q = 0`
   by psd Cauchy–Schwarz (`psd_kernel_eq`).

2. **Capped spectral split** (`sconstraint_orth_feasible`, ~250 lines).
   **The planned face argument through `lemma_2_1_exact` DOES NOT WORK** — the
   `suff_volatile` generators need not respect the eigenvalue CAP `L`, so an
   atom of the decomposition need not be in `feasible k L q`. What works is
   direct and cheaper: diagonalise `b*` (`symmetric_eigenbasis`), cap the
   eigenvalues at `1`; `Pi_constraint_capped_trace` says the capped eigenvalues
   still sum to `≥ n−k`; a threshold argument (`exists_min_subset`,
   `weighted_min_value`) selects a subset `S` of eigendirections carrying that
   mass; the witness is the projection `P_S` plus a remainder of size `≤ L−1`,
   so its eigenvalues cap at `1 + (L−1) = L` exactly. **Orthogonality is free**:
   `b* *v q = 0` puts `q` in the zero eigenspace, and every direction the
   witness uses has POSITIVE `b*`-eigenvalue, hence is orthogonal to `q`.

Then `δ → 0` on the Hessian bump through `feasible_trace_le` (`trace a ≤ nL` on
the feasible set) and `field_le_epsilon`, exactly as in the relaxed case.

#### Both inequalities proved, 2026-08-11

**Subsolution.** `paper_v_visc_subsol` (Paper_Viscosity), in the
envelope-FREE form, which is STRONGER than the paper's Definition 3.1(a).

**Supersolution.** `paper_v_supersol_lsc` (Paper_Viscosity): Definition
3.1(b) verbatim for `paper_v`, via `paper_v_supersol_contradiction_case1_lsc`
(∇φ ≠ 0, the skew trick) and `paper_v_case2` (∇φ = 0, the dichotomy).
The weak SDE solution feared below was NOT needed: Euler pasting of
endpoint-frozen Gaussian kernels plus a weak limit replaces it, and
Case 2 needed no bump function — applying `test_fun_quadratic_minorates`
at level ε/2 and splitting `H − (ε/2)·1 = (H − ε·1) + (ε/2)·1` supplies
all three properties the paper's φᵐ was built for.

**One hypothesis, and it is the paper's own setting.** The supersolution
carries `v_* < T/2` on the interior — the horizon cap must not bind. It
cannot be dropped: where `v ≡ T` on an open set the inequality is
genuinely FALSE, since a constant test function would demand
`1 ≤ F*(0,0) = 0`. The paper has no horizon at all, so a large `T` IS its
setting, and for bounded `K` the hypothesis is discharged from
`paper_v_le_ball_bound`.

**The design notes that follow are kept as the record of HOW this was
done — they are no longer a plan.**

#### The original design (2026-08-10, paper §3.2 read)

**Statement design first — the repo's plain `visc_supersol` is TOO STRONG.**
The paper's supersolution inequality (Def. 3.1(b)) is `F*(∇φ(x),∇²φ(x)) ≥ 1`
with the USC ENVELOPE `F*`, and `F* ≠ F` exactly at `p = 0` (their Lemma
"compute F"). The plain form `1 ≤ ell_op k L 0 H` is REFUTABLE at an interior
local min (take `φ` const: `ell_op k L 0 0 = 0`). `Envelopes.thy` anticipated
this: the target is **`visc_supersol_env`** (with `ell_op_usc`), already
imported by `Paper_Viscosity`. Consequence for assembly:
`theorem_1_1_uniqueness_general` consumes the strong `visc_sol`; its
supersolution hypothesis must eventually be weakened to the envelope form
(the comparison proof uses `F*` at the Crandall–Ishii step anyway, and at
`p ≠ 0` plain = envelope once Lemma 3.1's `F* = F` off zero is in — the
`Envelopes.thy` header records what that needs: Ky Fan + `Poincare_Separation`).

**The paper's §3.2 mechanism (Case 1, `∇φ(x) ≠ 0`) — the SKEW trick.** Given
`ell_op < 1`: a witness `a` with `1 + tr(a∇²φ(x))/2 > 0`, `a∇φ(x) = 0`;
modified so its top `n−k` eigenvalues are STRICTLY inside `(1,L)`. Set
`S_i := λ_i^{1/2}|∇φ(x)|⁻²(q_i∇φ(x)ᵀ − ∇φ(x)q_iᵀ)` (SKEW-symmetric) and run
`dX = Σ_i S_i∇φ(X)dW_i`. Skewness kills the Itô martingale term IDENTICALLY
(`∇φᵀS_i∇φ = 0`), so `τ + φ(X_τ) ≥ φ(y)` holds PATHWISE — which is what an
essinf bound needs; means cannot reach it. The margin `δ` comes from strict
touching, not from `τ`. Case 2 (`∇φ(x) = 0`) is a PDE-side reduction:
perturb by `−yᵀη`; either nonzero-gradient touchings exist arbitrarily close
(→ Case 1 → envelope limit) or `v_*` is quadratically pinched ⟹ locally
constant ⟹ contradicted by the DPP + a positive interior lower bound.

**The Girsanov-free replacement of their SDE (3.24) — Euler + kernel-pasting
+ weak limit.** No stochastic integration and no SDE well-posedness:

1. Quadratic minorant `ψ` (MIRROR of `test_fun_quadratic_dominates`, applied
   to `−φ`): Hessian `M := H − δ·1`; the same `δ` buys the sphere margin.
2. `ell_op k L q H < 1` (`q := g x ≠ 0`) gives `a ∈ feasible k L q` with
   `1 + tr(Ma)/2 ≥ 2η`; perturb to strict interior `(1,L)` (NEEDS `1 < L`;
   `L = 1` is rigid — excluded by hypothesis for now, as in the paper's own
   "(1,L)" step).
3. Covariance field `ā(z) := Σ(π(z))Σ(π(z))ᵀ`, `Σ(y)` = skew field of the
   paper, `π` = clamp onto `cball x r₀` (Lipschitz). Facts: `ā` continuous;
   `ā(z) ∈ feasible k L 0 ⊆ sconstraint` (constraint at `p = 0` is vacuous —
   `eigen_lb` via the variational witness `span{S_i q(π z)}`, Gram ≈
   `diag λ_i`); `ā(z) *v (q + M(π(z)−x)) = 0` everywhere (skewness);
   `1 + tr(M ā(z))/2 ≥ η'` on the ball (continuity margin).
4. Constant-`Σ` Gaussian member `gbmpair`: `X = z + Σ·W`, `Y_t = t·ΣΣᵀ`
   pathwise; class membership mirrors `bmpair_law_in_paper_pair_class`
   (Paper_Bridge 5874–6222) — linear images of the cbm martingales; needs
   `ΣΣᵀ ∈ sconstraint` only. 4th moment `E|X_t−z|⁴ ≤ Ct²` from BM moments.
5. Kernel `κ(z)` := recentred `gbmpair`-law with covariance `ā(z)`;
   LP-measurable by CONTINUITY of `Σ ↦ law` in the weak topology (dominated
   convergence; `paper_pair_class_compact_metric_space(2)` identifies the
   subtopology). Euler iterate `P^h` := fold of `paper_pair_class_kglue_law'`
   at constant times `jh` — IN THE CLASS by the kglue theorem, no new
   probability.
6. Pathwise per-step identity under `P^h`: `ψ(X_{t_{j+1}}) − ψ(X_{t_j}) =
   q(X_{t_j})ᵀΔ_j + ½Δ_jᵀMΔ_j` (exact, quadratic); the FROZEN-direction
   lemma (`paper_pair_class_frozen_direction` for the kernel member,
   `E[Y_t] = t·ā` deterministic) kills the first term a.s. on the in-ball
   event. Fluctuations `ξ_j := tr(M(outerp Δ_j − h·ā))`: conditionally
   mean-zero (clause (iv) of the kernel member through the ksemi Fubini),
   `E[ξ_j²] ≤ Ch²`. Per-grid-point Chebyshev: `P^h(bad_m) ≤ CTh/β²`.
   NO Doob needed.
7. Weak limit `P* ∈ class` (compactness, `paper_pair_class_compact_metric_space(3)`).
   The bad events are OPEN (`ball` for the in-ball clause, strict `<` for the
   dip), so the open-set portmanteau (`P*(G) ≤ liminf P^h(G)`) kills each in
   the limit; countable union over grids and `β ∈ 1/ℕ`, then path continuity:
   a.s. `∀t ≤ τ_{r₂}: ψ(X_t) − ψ(x) ≥ −(1−η)t`.
8. Contradiction: `θ := pball_exit r₂ ∧ c` into `paper_v_dpp_sup_ge_time`;
   the reduced horizon via `enn2real_paper_v_horizon_cap`
   (`v_S = min(v_T, S)`); exit branch gets the sphere margin `δr₂²/4`,
   no-exit branch gets `ηc` — BOTH positive, so
   `essinf ≥ v(x) + margin > v(x)`. Needs `T` beyond the ball bound
   (`paper_v_le_ball_bound`) so the cap never binds.

**The same keystone yields Example 3.1's `≥` half** — the item recorded as
blocked on weak solutions of (3.11): take `ā(z)` = spherical-tangential
around `y₀` (clamped near the singular centre, harmless because the radial
coordinate is FROZEN + increasing: `|X_t−y₀|²` evolves DETERMINISTICALLY at
rate `tr(ā) ≥ n−1`), so the ball exit time is deterministic and positive —
`essinf τ > 0`, giving interior positivity `v > 0` and the quantitative ball
lower bound. This unblocks clause (3)'s missing half AND supplies the
positivity that Case 2's "locally constant" contradiction consumes.

**Batches — ALL FIVE DONE.** (1)–(3) as planned; (4) Case 2 landed
without the bump; (5) the uniqueness interface turned out to be a
RE-BASING, not a reconciliation — see the new §1.11 below.

### 1.11 The uniqueness interface — RE-BASED on Definition 3.1, 2026-08-11

Batch (5) was mis-scoped as "reconciliation". What it actually needed was
to re-base the whole comparison/uniqueness chain on the paper's
Definition 3.1, because sub/supersolution are HYPOTHESES there and the
repo was assuming the STRONGER envelope-free notions — making its
comparison theorem WEAKER than Theorem 4.2. Done:
`max_principle_boundary`, `max_principle_le`,
`comparison_from_max_principle`, `uniqueness_from_max_principle`,
`max_principle_boundary_intro`, `comparison_compact`,
`viscosity_uniqueness_compact` and `theorem_1_1_uniqueness_general` now
all take `visc_subsol_env` / `visc_supersol_env`.

Two facts made this asymmetric, and they are worth not rediscovering:
* `F* ≠ F` exactly at `p = 0`, so the supersolution side needed the jet
  predicate `supersol_jet`, the `p ≠ 0` corollaries via
  `ell_op_usc_eq_at_nonzero`, and `ell_op_usc_small_shift_lt_one` for the
  diagonal case. **The paper's own diagonal argument is `1 ≤ F*(0,0) = 0`
  — `F*(0,0) = 0` FORBIDS a vanishing jet, it does not permit one.**
* `F_* = F` EVERYWHERE (`ell_op_lsc_at_zero` + `ell_op_lsc_off_zero`), so
  the subsolution side needed no operator change at all — only the
  quartic globalisation `visc_subsol_env_local`.

`visc_subsol`/`visc_supersol` are NOT deleted and should not be: they are
sound, they are the stronger notions, and `max_principle_boundary_raw`'s
counterexample genuinely depends on them (it moves `w` outside
`interior K`, which Definition 3.1's global touching would notice — that
non-transfer is exactly the defect the envelope form repairs).

#### The join — DONE

**The join is DONE.** `paper_v_cap_inert` and
`paper_v_supersol_lsc_bounded` (Paper_Viscosity) discharge the horizon
hypothesis from `paper_v_le_ball_bound`, so on a bounded `K` with `T`
large the supersolution property is unconditional. And
`paper_v_unique_viscosity_solution` (Theorem_1_1, which now also imports
Paper_Viscosity — the two sides had never been visible to each other,
`Paper_Viscosity` being a leaf) states that any continuous viscosity
solution in the sense of Definition 3.1 agreeing with `paper_v` on
`K - interior K` equals `paper_v`.

The one hypothesis it still carries is CONTINUITY of `paper_v` on `K`.
That is **§2.0**, and it is a Section-4 job — see there for why it should
NOT be attacked by proving `paper_v` continuous.

---

## 2. What is LEFT

In dependency order.  **§2.0 is the top of the queue** — it is all that stands
between clause (2) and a genuine characterisation.  §2.2 and §2.3 are
independent of it.  (The DPP at a stopping time, which was §2.1 until
2026-08-08, is now §1.9; the two viscosity inequalities, which were §2.1 until
2026-08-11, are now §1.10, and the uniqueness interface is §1.11.)

### 2.0 Continuity of `paper_v` on `K` — the last gap in clause (2)

`paper_v_unique_viscosity_solution` (§1.11) carries exactly one hypothesis that
is not discharged: `isCont (\<lambda>z. enn2real (paper_v k L T K z)) y` for `y \<in> K`.
What is proved is UPPER semicontinuity (`paper_v_usc_unconditional`);
`visc_supersol_lsc_iff_env` needs both, since it rests on `lsc_env u = u`.

**Do not attack this by proving `paper_v` continuous.**  The paper's Theorem
1.1 asserts the unique UPPER SEMICONTINUOUS viscosity solution, so continuity
would be a STRONGER statement than the paper makes, and the intended route is
the paper's **Theorem 4.3** — comparison with semicontinuous boundary data.
That is a Section-4 job, not more work on §1.10.

### 2.2 Clause (3) for general `n − k ≥ 2`

`n − k = 1` is done (§1.4). The general case needs spherical Brownian
motion — embed the deterministic-radius construction in an `(n−k+1)`-
dimensional coordinate subspace. Planned on the discrete route:
`Random_Walk_Market.thy`, `Relative_Arbitrage_Discrete.thy`,
`Path_Tightness.projective_limit_of_consistent_path_laws`.

### 2.3 `stopped_val_fn ≤ paper_v` (only if §2.2 needs it)

The bridge from market witnesses to class members. NOTE the recorded
obstruction — a `stopped_market` witness is NOT a class member, because the
paper's class never stops; the bridge must CONTINUE the witness past `tau`
with an admissible volatility, and the martingale side needs an independent
Brownian continuation, not just `Paper_Class.acont`. Build this only if
clause (3)/(2) actually need the market-side results transported.

### Fallback

If §2.1 and §2.2 both stall, the bounded alternative is the rest of
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

- **NEVER run `isabelle build`** (user instruction, 2026-08-07). The loop is
  `edit` → `get_progress`, or `get_state` on the touched range;
  `commands_failed = 0` with nothing unprocessed IS verification, and it
  takes seconds. Do not build "to confirm" before committing or before
  ending a session. After an edit made outside the MCP tools, re-`read` the
  file into PIDE instead.
- One class of defect PIDE structurally cannot see: a SESSION-QUALIFIED
  `\<^theory>` antiquotation checks green under the `Arbitrage` session and
  breaks every other one. Just write such cross-references as prose.
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
- **Name shadowing produces errors that point everywhere except the cause.**
  `OO` is the relation-composition operator, so a base named `OO` makes the
  `obtain` fail to parse and yields a hundred *type-unification* errors on
  unrelated lines. A local fact named `exE` shadows `HOL.exE`, and a later
  `by (rule exE)` then resolves against the local one and reports "Failed to
  apply initial proof method" on a goal that is exactly `exE`'s shape. When a
  batch of type errors appears at lines you did not touch, look for a bad
  NAME at the top of the block.
- **`auto`/`simp` with a `Metric_space` interpretation in scope can run for
  ten minutes and then SUCCEED.** Measured on
  `MS.mball f e = {ω ∈ space ℱ. mdist m f ω < e}`. The AFP additions make the
  locale's claset and simpset enormous. Use a calculation through
  `MS.in_mball` closed by `simp only`. Nothing marks this as a problem, which
  is what makes it dangerous.
- **`blast` on the existential behind an IMAGE membership** (`A ∈ f ` S`
  unfolds to `∃x. …`) sets `still_running_possibly_nonterminating` — it has
  to invent the witness. Introduce with `image_eqI`, eliminate with a named
  `imageE` wrapper.
- **`simp` distributes a component projection over a difference** (`$ c` over
  `a − b`) and thereby destroys the left-hand side of the very rewrite you
  handed it. State such steps as equations of FUNCTIONS and consume them with
  `unfolding`.
- **`enn2real_mono` wants `< ⊤`, not `≠ ⊤`** — the same shape as the recorded
  `ennreal_enn2real` trap; `OF` reports "no unifiers".
- **A chained fact carrying schematics is IGNORED by `simp`** (not an error).
  `using pfut_fst[OF m] by simp` does nothing; `by (simp add: pfut_fst[OF m])`
  works, because a simp RULE may have schematics while a chained fact may not.

### 3.5 Traps found while closing the stopping-time DPP (§1.9, 2026-08-08)

- **`\<^const>` is for CONSTANTS.** Writing `\<^const>‹some_lemma›` in a `text`
  block gives "Undefined constant"; theorem names need
  `@{thm [source] some_lemma}`. Cost four round-trips across the session.
- **`OF` against `?g (ω, ω')` has no unifiers.** A kernel-integral lemma must
  take its integrand CURRIED (`g :: 'a ⇒ 'b ⇒ real`); then `g ω ω'` is a
  higher-order pattern and unification succeeds.
- **`OF` against `0 ≤ ?θ ?ω` likewise.** Instantiating a `⋀ω`-schematic
  bound is not a pattern; use `proof (rule L)` with explicit `show`s so the
  conclusion fixes the variables first.
- **A local `have … for u e` exports with schematics named `?u1 ?e1`**, so
  `[where e = e]` fails with "No such variable"; use `[of u e]`.
- **`measurable` will not prove `f x = g x` as a predicate.** Rewrite it as
  `f x − g x = 0` first.
- **`blast` over a dozen residual side goals does not terminate.** Shape the
  hypotheses to match the target's premise lists exactly and pass them
  positionally instead.
- **`(m1, m2)` does not peel two goals.** It is sequential composition on goal
  1. Use an explicit `proof (rule …)` block with one `show` per goal.
- **`integrable_iff_bounded` wants measurability w.r.t. `ksemi M N Kr`**, not
  `M ⨂⇩M N`; `sets_ksemi` bridges them, which is why `space M ≠ {}` appears as
  a hypothesis in the `ksemi` integrability lemmas.
- **The MCP buffer desyncs after a run of edits** — it reports spliced-syntax
  errors while the file on disk is correct. Check the disk with `awk`, then
  resync with the MCP `read` tool. It happened three times in one session.
