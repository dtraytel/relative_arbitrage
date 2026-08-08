# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Single source of truth for **what is proved, what is left, and in what
order**. Everything named here is machine-checked in PIDE with
`commands_failed = 0`, and there is no `sorry` anywhere in the session.

Last restructured 2026-08-07 (late), after **the DPP of Prop. 2.4 was proved
at a deterministic time**. §1 is an INDEX of closed work — do not re-derive
any of it, and do not expand it; construction narratives, dead ends and
session logs live in `PLAN_HISTORY.md` and in `git log -p`. §2 is the
queue.

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
| (2) | `visc_sol k L (interior K) v` | **OPEN** — but the DPP (Prop. 2.4) is now **DONE at a deterministic time** (`paper_v_dpp`); what is left is §2.1 (a STOPPING time) and §3's Itô/SDE layer |
| (3) | `v = 0` on `K − interior K` | ball case **DONE for `paper_v`** (`paper_v_boundary_zero`); interior value REALIZED for `n−k=1` (`Theorem_1_1.stopped_val_fn_ball_eq_2d`); general `n−k ≥ 2` **OPEN**, §2.3; transfer to `paper_v` §2.4 |
| (4) | uniqueness | **DONE** — `Theorem_1_1.theorem_1_1_uniqueness_general` |

**Three value functions exist**, and the theorem must end up about ONE.
`val_fn` (all `sufficiently_volatile_market` instances), `stopped_val_fn`
(the locale plus the paper's stopped/killed side conditions) and `paper_v`
(the class (1.7) as pair laws). Clauses (0), (1), (3)-ball and (4) are
proved for `paper_v` itself. What still lives only on the market-side
functions is the `n−k=1` realization inside clause (3)
(`stopped_val_fn_ball_eq_2d`); transferring it is §2.4, and it is needed
only if §2.3 turns out to want it.

**Where the DPP stands — Prop. 2.4 IS PROVED AT A DETERMINISTIC TIME**
(`paper_v_dpp`, 2026-08-07; §1.7). The `≥` half is `paper_v_dpp_sup_ge`, from
the measurable selector and kernel pasting (§1.6); the `≤` half is
`paper_v_cond`, from the regular conditional distribution. **The only thing
left of the DPP is the extension to STOPPING times, §2.1.** The alternative
route through positive-measure conditioning is a dead end and stays one —
see §1.7.

**Remaining budget, roughly.**

| item | § | lines | risk |
|---|---|---|---|
| the DPP at a stopping time, `≥` half | 2.1 | 400–1,000 | high — pasting at a random time; the `≤` half is **DONE** (`paper_v_cond_time`) |
| §3, the two viscosity inequalities | 2.2 | 2,000–4,000 | high — Itô, exponential local martingales, weak SDE solutions |
| clause (3) for `n−k ≥ 2` | 2.3 | 1,500–3,000 | high — needs spherical Brownian motion |
| `stopped_val_fn ≤ paper_v` | 2.4 | ? | only if §2.3 wants it |

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

## 2. What is LEFT

In dependency order. §2.3 and §2.4 are independent of §2.1–§2.2 and can be
interleaved. **§2.1 is the top of the queue.**

### 2.1 The DPP at a STOPPING time — the top of the queue

At a stopping time `θ` BOTH clocks `u ∧ θ` and `(u − θ)⁺` are random, so the
product-filtration structure that carries §1.6(b′) breaks down. The paper's
§3.2 uses the exit time of a small ball, which is not deterministic, so this
IS needed for clause (2).

**The CONDITIONING half is DONE — `paper_v_cond_time`** (2026-08-07):

    P ∈ 𝒫ₓ, AE ω in P. c ≤ τ_K(ω)
      ⟹ AE ω in P. c ≤ θ ω + enn2real (paper_v k L (T − θ ω) K (X_{θ ω} ω))

for an ARBITRARY function `θ` of the path — no stopping-time property, no
measurability, no adaptedness, and no survival hypothesis. This is what the
paper's §3.1 (subsolution) consumes. It cost far less than the estimate
below because it is an almost-sure PATHWISE statement, so it reduces to the
deterministic `paper_v_cond` at countably many RATIONAL times plus a limit
at each path. Two facts make that work, and both are worth keeping:

- below `c` the survival event is FREE (`pexit_surv_of_less`), so
  `paper_v_cond`'s conditional conclusion becomes unconditional there;
- approach `θ ω` from ABOVE through rationals: that keeps the residual
  horizon SMALLER, and `paper_v` is monotone in the horizon
  (`paper_v_horizon_mono`), so the bound survives replacing `T − t_n` by
  `T − θ ω`. What is left is a limit in the SPACE variable — clause (1),
  `paper_v_usc_unconditional`. Approaching from BELOW grows the horizon and
  monotonicity points the wrong way.

**What is LEFT: the `≥` half**, i.e. pasting at a random time, and only
there does θ have to be a genuine stopping time (the integrand must be
measurable for `ess_inf_time`, and the construction glues at θ). The paper's
§3.2 (supersolution) needs it at `τ_{B_ε}`.

**The `≥` half is now down to ONE statement — `paper_v_dpp_sup_ge_time_of_const`**
(2026-08-08). The passage from a constant lower bound to the essential
infimum never used determinism of the time: it needs only that the integrand
lies in `[0, T]`, which holds for ANY `θ` with `0 ≤ θ ω ≤ T` — no
measurability, no stopping-time property. So

    (⋀P c. P ∈ 𝒫ₓ ⟹ (AE ω in P. c ≤ integrand_θ ω) ⟹ ennreal c ≤ paper_v k L T K x)
      ⟹ (SUP P ∈ 𝒫ₓ. ess_inf_time P integrand_θ) ≤ paper_v k L T K x

is proved, mirroring how `paper_v_dpp_le_of_cond` isolated the `≤` half.
**Discharge that hypothesis and §2.1 is closed.** Do not restate the SUP
form; state and prove the constant form and feed it in.

**The construction to build, concretely.** It does NOT need a new pasting
theorem at a random time. A stopping time with FINITELY many values
`t_1 < … < t_m` reduces to `m` applications of the FIXED-time
`paper_pair_class_kglue_law'`, because the regular conditional distribution
— now available as `paper_pair_class_rcd_member` — supplies a "do nothing"
branch:

    glue at t_j with   κ_j p' = if p' ∈ {θ = t_j} then S (X_{t_j} p')
                                else  (the r.c.d. of the current law at t_j)

`{θ = t_j}` is an `ℱ_{t_j}`-event exactly because θ is a stopping time, so
the kernel is a legitimate function of the past; gluing with a law's OWN
r.c.d. reproduces that law (`pglue_pcut_pfut` is the pathwise half of this);
and both branches take values in `𝒞₀`, which is what `paper_pair_class_kglue_law'`
demands. So the step is: optimal continuation on `{θ = t_j}`, unchanged
elsewhere. Induct on `m`.

Pieces already in place, and what each still needs:

| piece | status |
|---|---|
| `kernel_class_LP_measurable` — `prob_algebra`-measurable + values in the class ⟹ measurable into the LP-metric class space (`paper_pair_class_kglue_law'`'s `Kb`) | **DONE** |
| `paper_pair_class_sets_prob_algebra` — the class is a MEASURABLE set of laws (compact ⟹ closed, since the weak topology is the LP metric topology hence Hausdorff) | **DONE** |
| `kernel_repair_into_class` — hence an a.e.-into-the-class kernel can be redirected to the Brownian witness off the good set, which `Kc`'s for-all demands | **DONE** |
| `kernel_mix_measurable` — optimal on `A`, conditional law off it | **DONE** |
| `kglue_law'_rcd_eq` — gluing a law onto its OWN r.c.d. returns the law | **DONE** |
| **`paper_pair_class_kglue_mixed`** — the one-step engine: the mixed glue at a fixed `r` is again a class member | **DONE** |
| **`paper_v_dpp_sup_ge_time_of_const`** — SUP form at a random time ⟸ constant form; the whole remaining obligation is now that one hypothesis | **DONE** |
| `pcut_pglue`, `pcut_pglue_self` — gluing at `r` does not touch the `r`-cut, so an `ℱ_r`-event survives a glue at `r` | **DONE** |
| `AE_kglue_law'` — the a.s. transfer through a glue, base measure FREE (else `unfolding pair_law_of_def` also unfolds the `pair_law_of` hiding inside `Q`) | **DONE** |
| **`paper_pair_class_kglue_mixed`, 4th conclusion** — off `A` the mixed glue inherits every a.s. property of `P`: `(AE ω in P. Φ ω) ⟹ AE ω in R. pcut r ω ∈ A ∨ Φ ω`. Proof: `κ₀ = κ` a.e. by `paper_pair_class_rcd_member`, then `AE_kglue_law'` → `AE_ksemi` → `eq` → `pglue_pcut_pfut` back to `P` | **DONE** |
| **`paper_pair_class_kglue_mixed`, 5th conclusion** — the mirror ON `A`: `(⋀p' ∈ A. AE ω' in S (fst (p' r)). Φ (pglue r T p' ω')) ⟹ AE ω in R. pcut r ω ∉ A ∨ Φ ω` | **DONE** |
| `paper_v_horizon_zero` (`paper_v k L 0 K y = 0`), `pexit_pglue_selector_ge` (the selector's optimality on the glued path, extracted from `paper_v_dpp_ge_const`'s `inner`) | **DONE** |
| **`paper_v_dpp_ge_const_two` / `paper_v_dpp_sup_ge_two`** — the `≥` half, constant form AND SUP form, at the two-valued stopping time `θ = (if pcut r ω ∈ A then r else T)` for an arbitrary `ℱ_r`-event `A`. ONE glue: `paper_v_horizon_zero` collapses the `θ = T` branch to the plain exit time, so only the `θ = r` branch is constructed, and the two transfer conclusions cover the two branches. `A` is shrunk to `A ∩ {c ≤ g}`, legal because `paper_v_borel_measurable` makes `g` a random variable | **DONE — the first genuinely random time that closes end to end** |
| ~~the mirror-image conclusion ON `A`~~ | ~~open~~ **DONE, see above.** Same chain, but the inner AE is under `S (fst (p' r))` instead of `κ p'`, so the input is `Sval` (the selector's optimality) transported through `pshift_law` exactly as in `paper_v_dpp_ge_const`'s `opt` block, lines ~500–535. With this and the 4th conclusion, `θ ∈ {r, T}` — a genuine two-valued stopping time — closes in ONE glue, because `paper_v k L 0 K y = 0` makes the `θ = T` branch's integrand just `pexit T K` |
| **`paper_v_dpp_ge_step`** — THE INDUCTION STEP. `paper_v_dpp_ge_const_two` with `Ψ` left free: `AE ω in P. (pcut r ω ∈ A ⟶ c ≤ g_r ω) ∧ (pcut r ω ∉ A ⟶ Ψ ω)` ⟹ `∃R ∈ 𝒞_x. AE ω in R. (pcut r ω ∈ A ∧ c ≤ τ_K ω) ∨ Ψ ω`. The conclusion records `pcut r ω ∈ A` alongside the bound on purpose — at the next value the already-fixed paths have `θ ω = r`, so they are not in `A_j` and the next glue leaves them alone | **DONE** |
| **`dpp_chain`, `dpp_disj`, `dpp_chain_measurable`, `paper_v_dpp_ge_const_list`** — the `≥` half's constant form at ANY simple (finite-valued) stopping time. Iterate `paper_v_dpp_ge_step` down a list of `(t_j, A_j)`, carrying `D` = "already glued and already good"; invariant `D ω ∨ dpp_chain rs ω`. `D` implies the bound AND implies no *remaining* event fires, so no later glue touches those paths — the second is why the step's conclusion keeps `pcut r ω ∈ A` | **DONE — simple stopping times are CLOSED** |
| ~~the induction from two values to `m` values~~ | ~~open~~ **DONE, see above.** `paper_v_dpp_ge_const_two` is the base case with `m = 2`; the step is the SAME one-step engine applied at `t_j` with `A_j = {θ = t_j}`, and both transfer conclusions are in hand. What has to be tracked through the `m` steps is that `θ` is preserved, which holds because gluing at `t_j` changes only the future of paths in `A_j` and `pcut_pglue_self` says the `t_j`-cut is untouched. The engine is in place; what it needs is the bookkeeping. Glue at `t_1, …, t_m` in turn with `A_j = {θ = t_j}`; `θ` is PRESERVED by each step, because gluing at `t_j` changes only the future of paths in `{θ = t_j}` and that event is decided by the path up to `t_j`. The verification at the end is `pexit_pglue_dpp` (the pathwise DPP bound, §1.7) plus the selector's optimality. The delicate part is tracking "the law is unchanged off `A_j`" through the `m` steps, for which `kglue_law'_rcd_eq` is the pointwise input |
| general θ | **THE ONE OPEN ITEM OF §2.1. DO NOT TRY TO APPROXIMATE — the approximation inequality is FALSE, not merely circular.** Established 2026-08-08. For `θ_n ≥ θ` finite-valued, take a path that survives to `θ` but exits at some `τ ∈ (θ, θ_n]`. Then `integrand_{θ_n} ω = τ` while `integrand_θ ω = θ + v(T−θ, X_θ)`, and `v` can exceed `τ − θ` by any amount — so `integrand_θ ≤ integrand_{θ_n}` fails outright on that event. Approximating from BELOW gives the mirror failure. There is no discretisation of `θ` that dominates it, so `paper_v_dpp_ge_const_list` cannot be lifted. <br>**The only remaining route is to glue GENUINELY AT `θ`**, i.e. to build the re-based, re-clocked future map that lands `pcut θ` and `pfut θ T` in FIXED path spaces despite the random horizon `T − θ` — the move §1.7's notes already predicted would be needed for `paper_pair_class_rcd_member` at a stopping time. Everything else that construction needs is now in place: the mixed glue with both transfer conclusions, the selector, and `paper_v_dpp_ge_step`. <br>**What the PAPER does, and the design it dictates.** The paper defers Prop. 2.4 to Larsson–Ruf Prop. 2.2(iii), which conditions with an r.c.d. citing **Stroock–Varadhan Thm 1.3.4 / 6.1.2 — the concatenation theorem AT A STOPPING TIME.** S–V work on `C([0,∞))` and therefore *never rebase the time axis*: the continuation lives on the SAME path space and is spliced in place. There is no re-clocking anywhere in the literature argument, so do not build one. <br>Transplanted to the capped space, the split is **ADDITIVE** (`Paper_DPP`, done 2026-08-08): <br>  `pstopped T θ ω t = ω (min t (θ ω))` &nbsp;&nbsp; `pafter T θ ω t = ω (max t (θ ω)) − ω (θ ω)` <br>Both are maps `?B_T → ?B_T`, and `pstopped_add_pafter` gives `pstopped + pafter = ω` pointwise on `{0..T}` with NO membership hypothesis. The random horizon `T − θ` never appears, and — the point that kills the freeze-and-rebase design's crux — reassembly is addition, so it **does not need `θ` back**. `pafter_zero` gives the continuation's `0` start; `pafter_before`/`pstopped_after` say the two halves live on disjoint stretches of time. <br>**Done since:** `path_eval_at_measurable_time` — evaluating a path at a random time is Borel measurable (dyadic approximation from above + `measurable_compose_countable` + `borel_measurable_LIMSEQ_metric`; only POINTWISE path continuity, no uniform continuity). <br>**REUSE — the repo's stopped-process theories are written for exactly this, check them before building anything:** <br>• `Stopped_Adaptedness.stopped_adapted_of_cont` runs the same dyadic argument for a REAL-valued adapted process and yields the sharper **`ℱ_v`-measurability** of `(λω. Z (min v (τ ω)) ω)`. That is the version to reuse when the kernel must be a function of the PAST. Two bridges: it is real-valued (our paths are `(real^'n) × (real^'n^'n)`, so go componentwise, cf. `measurable_mat_entries`), and it wants continuity on all of `{0..}`, so cap the paths as `ω (min s T)`. <br>• **`Stopped_Localization`** — `stopped_martingale_L2`, `stopped_compensated_square`, `stopped_covariation`. These are the class's own two martingale clauses and its covariation constraint, *stopped*. They are what class membership of `pstopped`-laws should be built from; do NOT re-derive optional stopping. <br>• `Optional_Sampling` (no dominating supremum needed), `Sampled_Martingale.martingale_sampled`. <br>Also done: `pstopped_mspace`/`pafter_mspace` (both halves are again capped paths). <br>**The immediate next lemma** is `pstopped T θ`, `pafter T θ` measurable *as maps into* `?B_T`. The codomain is `pstopped_mspace`/`pafter_mspace`, every evaluation is `path_eval_at_measurable_time`, and the criterion joining them is that `sets ?B_T` is generated by the evaluations — that is `sets_natural_filtration_path` (b3), fed to `measurable_sigma_sets`. Do NOT try to prove it by continuity of `ω ↦ pstopped T θ ω`: for a random `θ` that route needs uniform continuity of each path (Heine–Cantor) plus limit-measurability into the Polish path space, which is strictly more work. <br>**Step (1) is CLOSED** (2026-08-08): `mdist_measurable_of_eval` (distance to a fixed path = countable sup of evaluations over `ℚ`, via `path_mdist_le_iff`) discharges hypothesis (ii) of `measurable_into_path_metric`, and with `pstopped_mspace`/`pafter_mspace` for (i) that gives **`pstopped_measurable`** and **`pafter_measurable`**: both halves are Borel maps `?B_T → ?B_T`. Only Borel measurability of `θ` is used; the stopping-time property enters later, via `stopped_adapted_of_cont`, to make the KERNEL a function of the past. Two traps: `measurable_ident` is stated for `id`, not `(λw. w)` — use `measurable_ident_sets[OF refl]`; and `path_eval_at_measurable_time` needs `X` and `g` pinned by `where`, since HO unification cannot split `w (g w)`. <br>**Step (2) is CLOSED** (2026-08-08): `path_rcd` / `path_rcd_ksemi` restate `paper_pair_class_rcd(_ksemi)` with the two maps `\u03c6\u2081, \u03c6\u2082` and the two horizons `u, v` FREE \u2014 nothing in either proof was specific to the deterministic split \u2014 and `paper_pair_class_rcd_stopping` is the instance `u := v := T`, `\u03c6\u2081 := pstopped T \u03b8`, `\u03c6\u2082 := pafter T \u03b8`: the conditional law of the increments AFTER `\u03b8` given the path STOPPED at `\u03b8`, as a Giry semidirect product. Two traps: **`thm` is a command keyword** (rename it; cf. the `OO`/`exE`/`bundle` family), and **`OF` against a slot `\u22c0\u03c9. A \u03c9 \u27f9 B \u03c9` resolves only the CONCLUSION and leaves `A` as an unprovable subgoal** \u2014 `pstopped_measurable`'s bounds are unguarded, so pass unguarded facts. <br>**Step (3), the DESIGN, is settled** (2026-08-08). `pafter T \u03b8 \u03c9` is frozen on `[0,\u03b8]`, so it is NOT in `paper_pair_class k L T 0` \u2014 the covariation constraint fails while the path stands still. It is the DELAYED EMBEDDING of the ordinary rebased future: with `pembed s T w = restrict (\u03bbt. w (max (t\u2212s) 0)) {0..T}` and `prebase s T w = restrict (\u03bbu. w (s+u)) {0..T\u2212s}`, <br>&nbsp;&nbsp;`pafter_eq_pembed`: `pafter T \u03b8 \u03c9 = pembed (\u03b8 \u03c9) T (pfut (\u03b8 \u03c9) T \u03c9)` &nbsp;&nbsp; `prebase_pafter`: `prebase (\u03b8 \u03c9) T (pafter T \u03b8 \u03c9) = pfut (\u03b8 \u03c9) T \u03c9`. <br>So the class statement for the kernel is about `prebase \u2218 pafter`, and that map is exactly what `paper_pair_class_rcd_member` already talks about. **The statement to prove is** <br>&nbsp;&nbsp;`AE \u03c9 in P. distr (\u03ba (pstopped T \u03b8 \u03c9)) ?B_(T\u2212\u03b8 \u03c9) (prebase (\u03b8 \u03c9) T) \u2208 paper_pair_class k L (T \u2212 \u03b8 \u03c9) 0` <br>which is well-formed with no `\u03b8`-recovery: inside an a.s. statement `\u03b8 \u03c9` is a fixed number, and the one place a FIXED space was needed \u2014 the kernel's codomain \u2014 is already handled by keeping `pafter` on the `T`-space. **This is the remaining bulk of \u00a72.1**: it is the stopping-time analogue of the whole (b1)\u2013(b3) chain. Clauses (i)/(ii) should be cheap (they are linear in \u03bc, cf. `AE_kernel_full`); clauses (iii)/(iv) are the work, and the b3 proof's conditioning rectangles move from `\u2131_(r+i)` to `\u2131_(\u03b8+i)` \u2014 which is where the STOPPING-TIME property finally enters (so far only Borel measurability of \u03b8 has been used). `Stopped_Localization` (`stopped_martingale_L2`, `stopped_compensated_square`, `stopped_covariation`) is the intended source for the martingale/covariation content; do not re-derive optional stopping. <br>**Step (3) progress** (2026-08-08): clause (i) is `prob_space_distr_prebase` (via `prebase_mspace`/`prebase_measurable` \u2014 re-basing at a FIXED time is an ordinary path-space map, which is all that is needed since `\u03b8 \u03c9` is a fixed number inside an a.s. statement); clause (ii) is `AE_rcd_stopping_start_zero` (pathwise seed `pafter_before` at `t = \u03b8 \u03c9`, pushed through by `AE_distr_iff` \u2192 the r.c.d. equation \u2192 `AE_ksemi`). The stopping-time property is spent exactly once so far, in `path_stopping_time_stopped`: the kernel is indexed by the STOPPED path, so the clock must be read off it. <br>**Clause (iii) \u2014 the covariation constraint \u2014 next, and the template is `pfut_rcd_diffquot` (line ~2747)**: `AE_kernel_full` for each RATIONAL pair `p < q` (measurability of the constraint set from `borel_of_closed[OF closedin_diffquot_constraint]`), then `AE_ball_countable'` twice over `\u211a`, then a pathwise continuity extension to real times. Two changes for the stopping-time case: state it on the FIXED `T`-space about `w`'s increments AFTER `\u03b8 p'` (guard `\u03b8 p' \u2264 p` inside the predicate) rather than on the varying `(T\u2212\u03b8)`-space \u2014 the guard makes it a PAIR-set, so `AE_kernel_full` is replaced by the `AE_ksemi` chain already used for clause (ii); and the pathwise content is free, because `pafter`'s increments after `\u03b8` ARE `\u03c9`'s increments (the `\u2212 \u03c9 (\u03b8 \u03c9)` cancels). <br>**Clauses (i), (ii), (iii) are DONE for the stopping-time kernel** (2026-08-08): `prob_space_distr_prebase`, `AE_rcd_stopping_start_zero`, `AE_rcd_stopping_diffquot`. For (iii) the chain was: `AE_rcd_stopping_diffquot_at` (one pair of times; the guard `\u03b8 p' \u2264 p` sits INSIDE the predicate, making the conditioning set a PAIR-set, so the transfer is the `AE_ksemi` chain, not `AE_kernel_full`) \u2192 `AE_rcd_stopping_diffquot_rat` (four `AE_ball_countable'` passes: two on the past-law, two INSIDE on `\u03ba p'` to move the a.s. quantifier over `w` out of the countable conjunction) \u2192 `diffquot_all_of_rational_ge` (the rational-to-real step WITH a lower guard \u2014 the guard is free, because the rationals `diffquot_all_of_rational` picks satisfy `p\u2099 > s \u2265 r`). The grid must stay in the ORIGINAL time scale; `paper_pair_class_diffquot_of_rational_pairs` is unusable because its grid lives in the rebased scale where `s\u2080 + s` is not rational. <br>**Clause (iv) \u2014 the two martingale clauses \u2014 is the real remaining work, and the MISSING TOOL is now identified.** The (b3) argument conditions on rectangles `A' \u00d7 (increment between i and j)` with `A' \u2208 \u2131_r`; at a stopping time `A'` ranges over `\u2131_\u03b8` and the increments run between the RANDOM times `(\u03b8+i) \u2227 T` and `(\u03b8+j) \u2227 T`, so the input is no longer the plain martingale property but **optional sampling** \u2014 `Optional_Sampling.set_optional_sampling` gives `\u222b 1\u2090 Z_(u\u2227\u03c4) = \u222b 1\u2090 Z_(v\u2227\u03c4)` for `A \u2208 \u2131\u1d65` \u2014 ONE stopping time `\u03c4`, sampled at DETERMINISTIC `v \u2264 u`. What (iv) needs is the TWO-stopping-time form `E[Z_(\u03c3\u2c7c) | \u2131_(\u03c3\u1d62)] = Z_(\u03c3\u1d62)` at `\u03c3\u1d62 = (\u03b8+i)\u2227T \u2264 \u03c3\u2c7c = (\u03b8+j)\u2227T`, i.e. a set-integral statement for `A \u2208 \u2131_(\u03c3\u1d62)`. That is NOT in the repo. The standard derivation is: stop at `\u03c3\u2c7c` (`optional_stopping`, line 1078, gives that `Z^(\u03c3\u2c7c)` is a martingale), then sample the stopped martingale at `\u03c3\u1d62` \u2014 but that second sampling is again at a stopping time, so a genuine `\u2131_\u03c3` layer (`pre_sigma`, cf. `Doob_Convergence/Stopping_Time.thy`) is needed first. **The layer is BUILT** (2026-08-08): `pre_sigma_of M F \u03c3` with `sigma_algebra_pre_sigma_of`, `pre_sigma_of_mono`, `pre_sigma_of_const`, `pre_sigma_of_band`, `pre_sigma_of_value_slice`. And on top of it **`set_martingale_sampling_simple`**: for `A \u2208 \u2131_\u03c3` and a \u03c3 taking finitely many values in `[0,U]`, `\u222b_A Y_\u03c3 = \u222b_A Y_U`. It needs NO optional-sampling machinery \u2014 split `A` along the values, each piece is in `F v` by the value-slice lemma, then the ordinary DETERMINISTIC-time `martingale.set_integral_eq`. That is the whole point of the layer. <br>**(iv)'s TOOL IS BUILT** (2026-08-08). `set_martingale_sampling`: for a martingale `Y`, a bounded stopping time `\u03c3` with values in `[0,U]`, and `A \u2208 pre_sigma_of M F \u03c3`, `\u222b_A Y_\u03c3 = \u222b_A Y_U`. Route: `\u2131_\u03c3` layer (`pre_sigma_of` + `sigma_algebra_pre_sigma_of`, `_mono`, `_const`, `_band`, `_value_slice`) \u2192 `set_martingale_sampling_simple` (split `A` along the finitely many values, each piece is in `F v`, then the ORDINARY deterministic-time `martingale.set_integral_eq` \u2014 no optional-sampling machinery at all) \u2192 `dyceil` + `borel_measurable_at_simple_time` \u2192 dominated convergence. Also `path_stopping_time_cut`/`_event` (pathwise \u21d2 filtration notion) and `path_stopping_time_shift` (`(\u03b8+i)\u2227T` is again a stopping time). <br>**What is left for (iv), three steps:** (a) refine `path_stopping_time_event` from `sets ?B_T` to `sets (\u2131_t)` \u2014 the stopped path only reads `[0,t]`, so feed `measurable_into_path_metric` + `mdist_measurable_of_eval` with the source measure `\u2131_t`; NOTE `path_eval_measurable_natural_filtration` is stated at the TERMINAL time, so the intermediate-`t` version needs `sets_natural_filtration_path_subset`. (b) instantiate `set_martingale_sampling` for the class's two martingales at `\u03c3\u1d62 = (\u03b8+i)\u2227T \u2264 \u03c3\u2c7c = (\u03b8+j)\u2227T`, discharging `cont` from path continuity and `Dbd`/`Dint` from `paper_pair_class_fourth_moment`. (c) feed the increment-zero statements into the horizon-agnostic (b3) machinery. <br>**(b) IS DONE, BOTH CLAUSES** (2026-08-08). `stopped_increment_of_horizon` gives the \u2131_\u03c3-conditioned increment identity for ANY real `Y` that is a `horizon_sq_int_martingale` with continuous paths, and BOTH class clauses now have that interpretation: `paper_pair_class_horizon_component` (the `X` side) and `paper_pair_class_horizon_compensated` (the compensated entry, via the new `martingale_mat_component` plus `paper_pair_class_comp_entry_sq_integrable`). Supporting tools built: `pre_sigma_of` + 5 lemmas, `set_martingale_sampling_simple`, `dyceil` + 7 lemmas, `set_martingale_sampling`, `set_martingale_sampling_two`, `path_stopping_time_cut`/`_event`/`_event_filtration`/`_shift`/`_shift_event`, `borel_measurable_at_simple_time`, `paper_component_dyceil_tendsto`. <br>**ALL THAT REMAINS OF (iv) IS (c)**: transfer the two increment identities from `P` to the KERNEL. That is the disintegration step, and `pfut_rcd_X_increment_zero` / `pfut_rcd_comp_increment_zero` are the templates \u2014 express the conditioning set as a rectangle through `(pstopped T \u03b8, pafter T \u03b8)`, then move to the kernel with `AE_integrable_ksemi_section` and the unbounded `integral_ksemi`. Those are horizon-agnostic; what changes is only that the rectangle sits in `\u2131_((\u03b8+i)\u2227T)` rather than `\u2131_(r+i)`, and `paper_pair_class_rcd_stopping` already supplies the r.c.d. equation. <br>(superseded:) (b) for the X-component (2026-08-08): `stopped_increment_of_horizon` gives `\u222b_A Y_((\u03b8+i)\u2227T) = \u222b_A Y_((\u03b8+j)\u2227T)` for ANY real `Y` that is a `horizon_sq_int_martingale` with continuous paths, and `paper_pair_class_horizon_component` supplies that interpretation for the `X`-component. **The one missing input is a MATRIX-entry component lemma**: `Ito_Market.martingale_vec_component` is typed `X :: real \u21d2 'a \u21d2 real^'n` \u2014 REAL entries \u2014 so it does not apply to the compensated clause, whose process is `real^'n^'n`-valued. Mirror its proof for `X t \u03c9 $ c $ d` (it is ~30 lines at `Ito_Market`:807); then `paper_pair_class_compensated_martingale` plus `paper_pair_class_comp_entry_sq_nn` (`Paper_Bridge`:3307) give the second interpretation and `stopped_increment_of_horizon` applies verbatim. <br>**Status 2026-08-08 (end of session):** (a) is DONE (`path_stopping_time_event_filtration`), and the comparison form `set_martingale_sampling_two` is DONE. For (b) every hypothesis now has a supplier \u2014 `martingale_vec_component` (`Ito_Market`) for the componentwise step, `path_stopping_time_shift` + `path_stopping_time_event_filtration` for the stopping-time and filtration facts, `sets_natural_filtration_mono` for `mono` \u2014 **except the dominating function**. `set_martingale_sampling` needs an integrable `D` with `\u2223Y s \u03c9\u2223 \u2264 D \u03c9` for ALL `s \u2208 [0,T]`, i.e. an integrable bound on the RUNNING SUPREMUM of the path. The class supplies only a fourth-moment bound (`paper_pair_class_fourth_moment`), so the bridge is `Doob_Inequality`'s `gsup`/`gsup_L2`/`gsup_integrable`, which were built for exactly this. **Do that first** \u2014 it is the only remaining input to (b). CAVEAT checked 2026-08-08: `gsup n` is the sup over the DYADIC GRID at level `n`, not over all of `[0,T]`, so it does not dominate `\u2223Y s \u03c9\u2223` for arbitrary real `s` as it stands; either take the monotone limit in `n` (each `gsup n` is integrable by `gsup_integrable`, and the limit is the running sup by path continuity), or \u2014 cheaper-LOOKING but WRONG \u2014 weaken `set_martingale_sampling`'s `Dbd` to the values `dyceil n U (\u03c3 \u03c9)` its dominated-convergence step actually uses. That second route does NOT work: those values are dyadic at LEVEL `n`, so the only bound available is `gsup n`, which depends on `n`, whereas `D` must be a single function. **So option 1 is forced.** Concretely: `gsup n` is nondecreasing in `n` (finer grids), its limit is the running supremum by path continuity, `gsup_L2` bounds `E[(gsup n)\u00b2]` uniformly (Doob), so Fatou gives `E[(gsup \u221e)\u00b2] < \u221e` and hence integrability. ~60\u201380 lines, and it is the LAST input to (b). <br>(superseded note:) (a) the GENERAL bounded \u03c3, by dyadic approximation from above \u2014 `\u03c3\u2099 = min U (\u23082\u207f\u03c3\u2309/2\u207f)` is simple, `\u03c3 \u2264 \u03c3\u2099`, so `A \u2208 \u2131_\u03c3 \u2286 \u2131_(\u03c3\u2099)` by `pre_sigma_of_mono`, and the limit needs path continuity + an integrable dominating function (exactly `optional_stopping`'s `paths`/`dom`/`D_int`). NOTE `Optional_Sampling.dceil` is LOCALE-BOUND (it carries the horizon `u`), so a free-standing dyadic ceiling has to be defined; the fiddly step is that `{\u03c3\u2099 \u2264 t}` is `{\u03c3 \u2264 (largest grid point \u2264 t)}`. (b) feed the two-stopping-time identity at `\u03c3\u1d62 = (\u03b8+i)\u2227T \u2264 \u03c3\u2c7c = (\u03b8+j)\u2227T` into the (b3) machinery, which is horizon-agnostic. `Stopped_Localization` supplies the covariation half. Everything downstream of that (the countable \u03c0-system through `pcut`, the Dynkin step, the UI/Vitali rational-to-real step) is horizon-agnostic and should transfer verbatim. <br>**What is left: (3)'s clauses (iii)/(iv) and (4).** (3) class membership of that r.c.d. \u2014 the analogue of `paper_pair_class_rcd_member`, with (b3) as the structural template and `Stopped_Localization` (`stopped_martingale_L2`, `stopped_compensated_square`, `stopped_covariation`) doing the martingale and covariation work; (4) class membership of the additive glue, where `paper_pair_class_kglue_law'` should transfer since addition is simpler than `pglue`. <br>(Superseded refactor note:) `paper_pair_class_rcd_ksemi` (line ~2404) already does exactly this for `(pcut r, pfut r T)`, and its proof body uses the specific maps only through the two lines `have mcut: pcut r ∈ P →⇩M ?X` and `have mfut: pfut r T ∈ P →⇩M ?Y`. Generalise it to <br>&nbsp;&nbsp;`path_rcd_ksemi`: `prob_space P` ⟹ `sets P = sets ?B_T` ⟹ `φ⇩1 ∈ P →⇩M ?B_u` ⟹ `φ⇩2 ∈ P →⇩M ?B_v` ⟹ `∃κ ∈ ?B_u →⇩M prob_algebra ?B_v. distr P (?B_u ⊗⇩M ?B_v) (λω. (φ⇩1 ω, φ⇩2 ω)) = ksemi (pair_law_of u φ⇩1 P) ?B_v κ` <br>by turning those two `have`s into assumptions and the two horizons into free `u`, `v`. Then `paper_pair_class_rcd_ksemi` is the instance `u := r, v := T−r`, and step (2) is the instance `u := v := T`, `φ⇩1 := pstopped T θ`, `φ⇩2 := pafter T θ`. <br>**What is left after that:** the r.c.d. of `pafter` given `pstopped` (analogue of `paper_pair_class_rcd_ksemi`); its class membership (analogue of `paper_pair_class_rcd_member`, (b3) is the template, now with `Stopped_Localization` doing the martingale/covariation work); and class membership of the additive glue, where `paper_pair_class_kglue_law'` should transfer since addition is simpler than `pglue`. <br>An unrelated small lemma that will be wanted either way and is cheap: `paper_v k L S K y ≤ paper_v k L (S−h) K y + h`, from `pexit S K ω ≤ pexit (S−h) K (pcut (S−h) ω) + h` plus `paper_pair_class_pcut` |

**What carries over from §1.7, and what does not.**

- `paper_pair_class_rcd_member` — the r.c.d. of the rebased future given the
  past lands in the class — has nothing DETERMINISTIC in its statement, but
  its proof does, in three places: `pcut r` and `pfut r T` are maps of FIXED
  path spaces; `rect_vimage_natural_filtration` puts the conditioning
  rectangle in `ℱ_{r+i}`; and the future space's horizon is the constant
  `T−r`. At a stopping time that horizon is random. The likely move is to
  re-base AND re-clock the future so it is again a map into a FIXED space.
- `paper_v_dpp_ge_const` is already stated for an arbitrary real constant `c`
  and an arbitrary a.s. bound, so the `≥` half generalizes without
  restatement once the glue at a random time exists.
- `survival_event_filtration`, `pexit_split_at_r` and `pglue_pcut_pfut` are
  all stated at a fixed `r`; their stopping-time analogues are the real work.

**What the session does not have yet: an `ℱ_θ` layer.** AFP
`Doob_Convergence/Stopping_Time.thy` has `pre_sigma`, `sets_pre_sigmaI`,
`mono_pre_sigma`, `stopping_time_measurable_le/less/ge/gr` and
`borel_measurable_stopping_time_pre_sigma`, and looks like the right source;
the entry is NOT a session dependency yet, and adding one needs a server
restart (§3.1). HOL-Probability's own `stopping_time_le_const` and friends
live INSIDE `locale filtration`, so they need an interpretation.

### 2.2 §3 — the two viscosity inequalities → clause (2)

**Which half of the DPP feeds which inequality** (read out of §3.1 and §3.2
of the paper on 2026-08-06; do not redo this):

| viscosity inequality | DPP half it consumes |
|---|---|
| **subsolution** (§3.1, display (3.17)) | the DPP **at the optimizer**: `v(x) ≤ t∧θ + v(X(t∧θ))` P-a.s. for the fixed optimizer P. This is the CONDITIONING half — **PROVED at a deterministic time**, §1.7. |
| **supersolution** (§3.2, after (3.25), and again in Case 2 after (3.30)) | `v(y) ≥ P_y-essinf (τ_{B_ε(x)} + v(X(τ_{B_ε(x)})))` for a SPECIFIC constructed `P_y`. This is the `≥` half, i.e. PASTING — **PROVED at a deterministic time**, §1.7; at `τ_{B_ε}` it needs §2.1. |

Beyond the DPP, §3 consumes machinery this development does not have:
Itô's formula for class members, an exponential local martingale plus
optional sampling ((3.18)–(3.19)), and weak solutions of the SDEs (3.11) and
(3.24). **Budget §3 separately from the DPP.**

### 2.3 Clause (3) for general `n − k ≥ 2`

`n − k = 1` is done (§1.4). The general case needs spherical Brownian
motion — embed the deterministic-radius construction in an `(n−k+1)`-
dimensional coordinate subspace. Planned on the discrete route:
`Random_Walk_Market.thy`, `Relative_Arbitrage_Discrete.thy`,
`Path_Tightness.projective_limit_of_consistent_path_laws`.

### 2.4 `stopped_val_fn ≤ paper_v` (only if §2.3 needs it)

The bridge from market witnesses to class members. NOTE the recorded
obstruction — a `stopped_market` witness is NOT a class member, because the
paper's class never stops; the bridge must CONTINUE the witness past `tau`
with an admissible volatility, and the martingale side needs an independent
Brownian continuation, not just `Paper_Class.acont`. Build this only if
clause (3)/(2) actually need the market-side results transported.

### Fallback

If §2.1–§2.2 and §2.3 both stall, the bounded alternative is the rest of
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

## §2.1 step (3), clause (iv), step (c) — status 2026-08-08 (later)

**(c) is DONE for the `X` martingale clause; the compensated clause needs one
more P-side result first.**

New material in `Paper_DPP.thy` (all green, zero `sorry`):

* The **rectangle** at a stopping time. `pafter T θ ω t = ω (max t (θ ω)) − ω (θ ω)`
  is the DELAYED future, so the time on the second factor is an ABSOLUTE `u`,
  not an offset, and the sampling time attached to it is **`u ∨ θ`**, not
  `(θ+i) ∧ T`. Built: `path_stopping_time_cut_eq`, `pstopped_cut_compose`,
  `pcut_pafter_cut_compose` (below a deterministic `t` both factors are read
  off the path stopped at `t`), `path_stopping_time_max`,
  `path_stopping_time_event_filtration_all` (the horizon restriction removed),
  `pre_sigma_ofI_le`, `pre_sigma_of_Int`, `pstopped_vimage_pre_sigma`,
  `pafter_vimage_pre_sigma` (an `ℱ_u`-set of the path space is a `pcut u`-preimage,
  by `sets_natural_filtration_eq_pcut_vimage`, so only the delayed future ON
  `[0,u]` matters), and **`rect_vimage_pre_sigma_stopping`** — the analogue of
  `rect_vimage_natural_filtration`.
* The **`u ∨ θ` sampling family**: `stopped_increment_of_horizon_gen` (the
  increment identity for an ARBITRARY ordered pair of bounded path stopping
  times — `set_martingale_sampling_two` was already abstract in them) and
  `integrable_at_bounded_stopping_time` / `integrable_at_path_stopping_time`
  (integrability of the SAMPLED process, which the deterministic development
  got for free from the martingale locale).
* The **disintegration**: `pafter_rcd_increment_zero`, stated once for an
  arbitrary real integrand `h` on the future factor together with the pullback
  identity `h (pafter T θ ω) = Y (max j (θ ω)) ω − Y (max i (θ ω)) ω`, and its
  instance **`paper_pair_class_rcd_X_increment_zero`**.

**What remains of (iv).** The compensated clause is NOT an instance of
`pafter_rcd_increment_zero` as it stands, and the reason is mathematical, not
bookkeeping: `outerp` is QUADRATIC, so `outerp(fst (pafter T θ ω u))` is not
`outerp(fst (ω u))` up to a cancelling constant. Writing `b = fst (ω (θ ω))`,

  `outerp(X_u − b) − (⟨X⟩_u − ⟨X⟩_θ) = (outerp X_u − ⟨X⟩_u) − X_u bᵀ − b X_uᵀ + outerp b + ⟨X⟩_θ`

so the pullback `Y` that `pafter_rcd_increment_zero` needs is the DELAYED-FUTURE
compensated process, and the missing input is that **it is a
`horizon_sq_int_martingale` of `P`**. That is the stopping-time analogue of
`paper_pair_class_pfut_comp_martingale`: `b` is `ℱ_θ`-measurable (not constant),
so the cross terms need a martingale-times-known-square-integrable-factor
identity at a stopping time, on top of the class's own compensated clause.
Once that single interpretation exists, `pafter_rcd_increment_zero` applies to
it verbatim, exactly as `paper_pair_class_rcd_X_increment_zero` does.

## §2.1 step (3), clause (iv) — CLOSED 2026-08-08

Both martingale clauses of the class now transfer to the r.c.d. kernel:
`paper_pair_class_rcd_X_increment_zero` and
`paper_pair_class_rcd_comp_increment_zero`. Step (3)'s clauses (i)–(iv) are
therefore all done, and what remains of §2.1 is step (4), class membership of
the additive glue.

The compensated clause needed one genuinely new result, because `outerp` is
quadratic and so does NOT ride along on the additive split. With `σ = i ∨ θ`,
`ρ = j ∨ θ` and `b = fst (ω (θ ω))` the pathwise expansion is

  `h (pafter T θ ω) = (Ym_ρ − Ym_σ) − (Yc_ρ − Yc_σ)·b$d − (Yd_ρ − Yd_σ)·b$c`

— a compensated increment plus two CROSS TERMS. The constants `outerp b` and
`⟨X⟩_θ` cancel between the two times, which is why only the cross terms are
new. They are killed by **`set_integral_increment_times_known`**: for a
square-integrable `ℱ_σ`-measurable `Z`, `∫_A (Y_ρ − Y_σ)·Z dP = 0`.

That lemma needs NO approximation by simple functions. `pre_sigma_of` is
already a σ-algebra, so `sigma (space P) (pre_sigma_of P F σ)` is a genuine
sub-σ-algebra of `P`, `finite_measure_subalgebra_is_sigma_finite` makes it a
`sigma_finite_subalgebra`, and then it is textbook: `cond_exp` of the
increment vanishes (`AE_zero_of_set_integral_zero` against
`stopped_increment_of_horizon_gen`), and `Z` pulls out
(`cond_exp_measurable_mult`). The one quantitative input is square
integrability of the sampled increment — **`Doob_Inequality.Dsup_sq_integrable`**,
which already existed.

Also new: `pafter_rcd_increment_zero` now takes the set-integral hypothesis
`inc` directly rather than a martingale plus a pullback identity, so both
clauses instantiate it; and `pstopped_comp_vimage_pre_sigma` (a function of
the stopped path is `ℱ_θ`- and a fortiori `ℱ_(u ∨ θ)`-measurable).

## §2.1 step (4) — foundation laid 2026-08-08

The glue map is **`padd T p' w = restrict (λt. p' t + w t) {0..T}`**, defined on
the SAME pair of `T`-path spaces the r.c.d. of step (2) lives on, and carrying
no `θ` — that is the point of having chosen the additive split.

Done and green: `padd_apply`, `padd_outside`, `padd_mspace` (the glue lands in
the path space), **`padd_measurable`** (as a map out of `?B_T ⨂⇩M ?B_T`, via
`measurable_into_path_metric` + `mdist_measurable_of_eval`, exactly as
`pstopped_measurable`/`pafter_measurable` were built), and the two inversion
lemmas: **`padd_pstopped_pafter`** (the glue inverts the split — no membership
hypothesis beyond being a path) and, given that the continuation stands still
up to `θ`, **`padd_stopping_time`** / **`pstopped_padd`** / **`pafter_padd`**
(the split inverts the glue). So nothing is lost in either direction, and the
stopping time reads only the stopped factor.

**What remains of (4)** is the glued-law theorem itself:

  `distr (ksemi Q ?B_T κ') ?B_T (λp. padd T (fst p) (snd p)) ∈ paper_pair_class k L T x`

for `Q` the law of `pstopped T θ` under a class member and `κ'` a kernel whose
values are continuations frozen on `[0, θ p']` and in the class after. Clauses
(i)/(ii) are cheap; (iii) is the concatenation of two covariation constraints
with a crossing pair `s < θ < t`, as in `paper_pair_class_kglue_law`'s (iii);
(iv) is the one that needs the weak-closedness route of
`paper_pair_class_kglue_law'` (round `κ'` to a countably valued kernel by
`Metric_space.countably_valued_approx`, glue each, pass to the weak limit),
transposed from `pglue` to `padd`. `Lipschitz_pglue` has to become a
Lipschitz/continuity statement for `padd`, which should be easier — addition
is 1-Lipschitz in each argument — but the DELAYED class (`κ' p'` frozen until
`θ p'`) must be shown compact metric first, since that is what
`countably_valued_approx` rounds inside.

### (4): do NOT prove compactness of the delayed class — round θ instead

The note above suggested rounding `κ'` inside a "delayed class". That route has
a defect worth recording before anyone spends time on it. `countably_valued_approx`
returns `z_j` close to `κ' p'` in Lévy–Prokhorov, but nothing forces `z_j` to be
frozen on `[0, θ p']` — it is only frozen on `[0, s_j]` for some nearby `s_j`. A
continuation whose freezing time differs from the past's stopping time is NOT a
legitimate pasting, so the rounded glues are not in the class and the weak-limit
argument has nothing to stand on. Compactness of the delayed class, even if
proved, does not repair this.

**Round `θ`, not `κ'`.** `dyceil` and `dyceil_stopping` are already built (they
were made for clause (iv)). For a SIMPLE stopping time every value slice is a
deterministic time, so on each slice `paper_pair_class_kglue_law'` applies
verbatim and `paper_pair_class_kglue_mixed` assembles the slices — that is
exactly the `paper_v_dpp_ge_const_list` pattern, which is already done. Then let
`θ_n ↓ θ` and pass to the weak limit with `paper_pair_class_weak_closed`.

Note this does NOT contradict [[dpp-stopping-time-no-approximation]]. That result
says the DPP *inequality* cannot be obtained by discretising `θ`, because the
dominating inequality between the integrands is false. Here the object being
approximated is a *law*, the target property (class membership) is weakly closed,
and no inequality between integrands is involved. The two uses of "approximate
`θ`" are unrelated.

The one analytic input still needed is that the glue is continuous in the pair,
so that `padd (pstopped T θ_n ω) w_n → padd (pstopped T θ ω) w`; addition is
1-Lipschitz in each argument, and `padd_measurable`'s evaluation lemmas already
supply the pointwise handle.

### (4) status 2026-08-08 (later): clauses (i)–(iii) DONE, (iv) is the crux

New in `Paper_DPP.thy`, all green, zero `sorry`:

* **`aglue_law T κ Q = distr (ksemi Q ?B_T κ) ?B_T (λp. padd T (fst p) (snd p))`**
  — the stopping-time analogue of `kglue_law'`, structurally identical except
  that `padd` replaces `pglue`.
* `sets_aglue_law`, `padd_measurable_ksemi`, **`prob_space_aglue_law`** — clause (i).
* **`AE_aglue_law`** — the transfer lemma (analogue of `AE_kglue_law'`; base
  measure kept a free variable, per the recorded trap).
* **`aglue_law_start`** — clause (ii).
* **`padd_diffquot`** + **`aglue_law_diffquot`** — clause (iii). The pathwise
  core is the same three-case argument as `pglue_diffquot`: below `θ` only the
  past moves, above `θ` only the continuation, and a straddling pair is a
  CONVEX COMBINATION of the two difference quotients (`sconstraint_convex`).
  Lifting to the law is `paper_pair_class_diffquot_of_pairs` (one pair of
  deterministic times, predicate closed by `closedin_diffquot_constraint`)
  composed with `AE_aglue_law`.

**What is left is clause (iv) only** — the two martingale clauses for
`aglue_law`. This is the same obstruction the deterministic development hit:
`paper_pair_class_kglue_law'` does NOT prove (iv) directly either, it rounds the
kernel and uses weak closedness. A direct argument would need
`E[X_j − X_i ∣ ℱ_i]= 0` under the glued law, and the glued path's natural
filtration at `u` is generated by `p' s + w s` for `s ≤ u`, which does not
factor over the two components — that non-factoring is exactly why the
deterministic proof went around it.

So (iv) needs the route recorded above: glue at a SIMPLE `θ` slice by slice
(each slice is a deterministic time, so `paper_pair_class_kglue_law'` +
`paper_pair_class_kglue_mixed` apply verbatim — the `paper_v_dpp_ge_const_list`
pattern), then `dyceil` for `θ_n ↓ θ` and `paper_pair_class_weak_closed` for the
limit. The remaining analytic input is weak convergence of the glued laws,
for which `padd` being 1-Lipschitz in each argument is the handle.

### (4) clause (iv): the shape of the remaining work (2026-08-08)

Everything except clause (iv) is proved. For (iv), two findings change its shape:

**1. `martingale_pair_law` (Paper_Bridge:5188) removes the transport layer.**
It lifts a martingale from a base measure `M` along a path map `φ` to
`pair_law_of T φ M`. Since `aglue_law T κ Q` is exactly the pushforward of
`ksemi Q ?B_T κ` along `λp. padd T (fst p) (snd p)`, clause (iv) reduces to the
martingale property ON THE SEMIDIRECT PRODUCT, plus two cheap side conditions
(`adap`, and `Zm` from `path_eval_measurable_natural_filtration'`). Do NOT
rebuild the transport by hand — and do not reach for `kglue_law_X_martingale`'s
route, which carries a countably-valued index `N` that the additive split does
not need.

**2. On the product the two components separate, and the filtration is
`ℱ^Q_{u ∧ θ} ⊗ G_u`.** Because `fst (padd p' w (min u T)) = fst (p' (min u T))
+ fst (w (min u T))`, and
* the past summand is a STOPPED martingale under `Q` — its filtration index is
  the stopping time `min u θ`, so this is the `pre_sigma_of` layer built for
  clause (iv) of step (3) (`set_martingale_sampling_two`,
  `stopped_increment_of_horizon_gen`), not new analysis;
* the continuation summand is a martingale under `κ p'` for each `p'`.

The two collapses that make the cross-conditioning work are now proved:
**`pcut_padd_before`** (on `{θ > i}` the glued path agrees with the past on
`[0,i]`, so an `ℱ_i`-set of the glue does not constrain `w` at all) and
**`pcut_padd_section`** (`pcut i (padd T p' w) = padd i (pcut i p') (pcut i w)`,
so for fixed past the `w`-section of an `ℱ_i`-set is an `ℱ_i`-set of the
continuation). Together with `AE_aglue_law` and `integral_aglue_law` these are
all the plumbing (iv) needs.

Expect the compensated clause to need the `outerp` expansion AGAIN — on the
product, `outerp (p' + w) = outerp p' + p' wᵀ + w p'ᵀ + outerp w` — so
`set_integral_increment_times_known` (built for step (3)) is the tool to reuse
for its cross terms rather than anything new.

## §2.1 step (4) — CLOSED 2026-08-08

**`paper_pair_class_aglue`**: the additive glue of a stopped past `Q` and a
continuation kernel `κ` lands in `paper_pair_class k L T x`. No martingale
hypothesis remains; the surviving hypotheses are all about the two FACTORS.

The chain, per martingale clause:

  `aglue_inner_increment(_comp)` → `aglue_law_X_increment` / `aglue_law_comp_increment`
    → `aglue_law_X_martingale` / `aglue_law_comp_martingale`

**The argument, and why no weak-closedness detour was needed.** The
deterministic `paper_pair_class_kglue_law'` does not prove clause (iv)
directly — it rounds the kernel and appeals to `paper_pair_class_weak_closed`.
The additive split does not need that, because it is INVERTIBLE
(`pstopped_padd`, `pafter_padd`) and the conditioning set collapses on each
half of `{θ ≤ i}`. Writing an `ℱ_i`-set of the glue as `pcut i -` B`
(`sets_natural_filtration_eq_pcut_vimage`), the four cells are:

| | past increment | continuation increment |
|---|---|---|
| `θ > i` | `pcut_padd_before` ⟹ set is w-free ⟹ 0 by `stopped_increment_of_horizon_gen` at `σ = i∧θ ≤ ρ = j∧θ`, conditioning set from `pcut_after_in_pre_sigma` | `w(i∧T)=0` and `E[W_j]=W_0=0` |
| `θ ≤ i` | `P_{j∧θ} = P_{i∧θ}` by `pstopped_eval_min` ⟹ cancels | w-section is an `ℱ_i`-set of `κ p'` by `section_padd_in_filtration` |

The outer step is NOT pointwise: on `{θ > i}` the two inner integrals differ
and only their `Q`-integral over that event vanishes, so it is a set-integral
split of `Q` along `{i < θ}`.

**The compensated clause needed NO cross-term machinery.** `outerp` is
quadratic, so on the product
`(outerp (fst (padd p' w s)) − snd (padd p' w s)) $ c $ d = Zp + Zw + (p'$c·w$d + w$c·p'$d)`.
But inside the inner `κ p'` integral the past factor is a CONSTANT, so the two
cross terms pull straight out and die by `Kmean` (on `{θ > i}`) and `Kinc`
(on `{θ ≤ i}`). `set_integral_increment_times_known`, earmarked for this, is
not used.

**Supporting lemmas built for (4):** `padd` + `padd_mspace`/`padd_measurable`/
`padd_pstopped_pafter`/`padd_stopping_time`/`pstopped_padd`/`pafter_padd`;
`aglue_law` + `sets_aglue_law`/`prob_space_aglue_law`/`AE_aglue_law`/
`integral_aglue_law`; `aglue_law_start` (ii); `padd_diffquot` +
`aglue_law_diffquot` (iii); `path_stopping_time_min`, `pstopped_eval_min`,
`pcut_padd_before`, `pcut_padd_section`, `section_padd_in_filtration`,
`pcut_after_in_pre_sigma`.

**What remains of §2.1** is the `≥` half itself: feed
`paper_pair_class_aglue` (with the optimal-continuation kernel) into
`paper_v_dpp_sup_ge_time_of_const`, which is already stated for an arbitrary
`θ`. Steps (1)–(4) are all closed.

## §2.1: what is left after steps (1)–(4) — the HORIZON-PARAMETRISED SELECTOR

Steps (1)–(4) are closed. The `≥` half reduces, via
`paper_v_dpp_sup_ge_time_of_const` (already stated for an arbitrary `θ`), to the
CONSTANT form: given `P` in the class with

  `AE ω. c ≤ pexit (θ ω) K X + (if survived then v(T − θ ω, X_(θ ω)) else 0)`

build a competitor in the class whose exit value is `≥ c`. Step (4)
(`paper_pair_class_aglue`) supplies "the glue is in the class", so the only
missing ingredient is the CONTINUATION KERNEL itself.

**The blocker, identified 2026-08-08.** `paper_v_measurable_selector_kernel'`
selects an optimal continuation measurably in the START POINT `y`, but for a
FIXED horizon `T`. At a stopping time the continuation is needed at horizon
`T − θ p'`, which varies with `p'`. So what is required is a selector jointly
measurable in the PAIR `(s, y)`:

  `S ∈ (borel ⊗⇩M borel) →⇩M prob_algebra ?B_T`, with `S (s, y)` the
  `pembed s T`-image of a law in `paper_pair_class k L (T − s) 0` attaining
  `paper_v k L (T − s) K y`.

Note the statement is only well-formed because `pembed` puts every horizon's
class into the COMMON `T`-space — the same device step (3) used. This is a
genuine new theorem (a measurable selection with the horizon as a parameter),
not assembly of existing parts.

**Do NOT try to avoid it by discretising `θ`.** Rounding `θ` to a simple `θ_n`
would let the existing fixed-horizon selector apply on each value slice, but
the resulting competitor is glued at `θ_n`, and recovering the `θ` statement
needs `integrand_θ ≤ integrand_(θ_n) + o(1)`, which is exactly the inequality
recorded as FALSE in [[dpp-stopping-time-no-approximation]]. Horizon-Lipschitz
continuity of `paper_v` does not repair it. The `θ_n` route is blocked for the
INEQUALITY even though it is fine for CLASS MEMBERSHIP.

## §2.1: the horizon-parametrised selector is DONE — and it was not a new selection theorem

**`paper_v_measurable_selector_horizon` (Paper_DPP, 2026-08-08).** For `0 < T`,
`1 ≤ L`, `closed K` there is

  `Sel ∈ (borel ⨂⇩M borel) →⇩M prob_algebra ?B_T`

with, for every `0 ≤ s ≤ T`: `Sel (s,y) ∈ pdelclass k L T s`; its `prebase s T`
image lies in `paper_pair_class k L (T−s) 0`; and that image attains
`paper_v k L (T−s) K y`.

**The blocker recorded above was wrong, and here is why.** The note said a
selector jointly measurable in `(s,y)` is "a genuine new theorem (a measurable
selection with the horizon as a parameter)". It is not, because of ONE identity:

  `pexit_min_horizon`: `0 ≤ S ≤ T ⟹ pexit S K f = min (pexit T K f) S`.

The horizon enters the payoff only as an OUTER CAP. Capping by a constant
commutes with the essential infimum (`ess_inf_time_min_const`) and with the
supremum over the class, so

  **`paper_v_horizon_cap`**: `paper_v k L S K x = min (paper_v k L T K x) (ennreal S)`
  for `0 ≤ S ≤ T`, `1 ≤ L`, `closed K`.

(`≤` is `paper_v_horizon_mono` + `paper_v_le_T`; `≥` cuts a competitor back with
`paper_pair_class_pcut` and applies the two lemmas above.) Since `min c ·` is
monotone, **the maximiser does not depend on the horizon**: the fixed-horizon
optimizer, CUT to `T−s`, is optimal at `T−s`. So there is nothing to select
again — only a pushforward to carry `s` through.

**Do NOT build the compactness of `pdelclass k L T s`, nor the closedness of
`⋃_{s∈[0,T]} pdelclass k L T s`, nor a graph-space selection.** Those were the
prerequisites of the abandoned route; none of them is needed. (Nor is the
Lévy–Prokhorov machinery: this proof touches no topology at all.)

**What the construction actually needs.** `Sel (s,y) = distr (S0 y) ?B_T (pdel s T)`
for `S0` the existing `paper_v_measurable_selector_kernel'`, where
`pdel s T = pembed (max 0 (min s T)) T` — the CLAMP is what makes the map total,
so the parameter can live in plain `borel` rather than a restricted space.
Supporting lemmas, all green:

* `pembed_pcut` — `pembed s T (pcut (T−s) ω) = pembed s T ω` for ALL `ω`
  (no membership hypothesis). This is what identifies the pushforward of a
  `T`-law with the pushforward of its cut, i.e. with a member of `pdelclass`.
* `pembed_mspace_full` / `pembed_measurable_full` — `pembed s T` maps the
  `T`-space to itself, so no horizon bookkeeping.
* `pdel_measurable_pair` — JOINT measurability in `(s,ω)`, via
  `measurable_into_path_metric` + `mdist_measurable_of_eval` +
  `path_eval_at_measurable_time` (each evaluation of `pembed s T ω` is an
  evaluation of `ω` at a time depending measurably on `s`).
* `measurable_distr2` (HOL-Probability) lifts that to the kernel; then
  `measurable_prob_algebraI`. There is no Giry `bind` anywhere.
* `pshift_pcut_comm` / `pshift_law_pcut` / `ess_inf_pexit_pcut_law` — the value
  of a cut law is the value of the original, capped.

### What is left of §2.1

Steps (1)–(4) and the selector are all closed. The `≥` half now reduces to
plumbing `Sel` into `paper_pair_class_aglue` and then into
`paper_v_dpp_sup_ge_time_of_const`. Concretely, TWO packages remain:

1. **`pdelclass` ⟹ the kernel hypotheses of `paper_pair_class_aglue`.** Already
   supplied: `Kp` (`Selm`), prob/sets (`pdelclass_prob`), `K0`
   (`pdelclass_frozen_at` at `u = 0`), `Kfr` (`pdelclass_frozen`). Still to
   prove, for `ν ∈ pdelclass k L T s` with `θ p' = s`: `Kcov`, `Kmean`,
   `KmeanC`, `Kint`, `KintC`, `Kinc`, `KincC`. All seven are the corresponding
   class facts at horizon `T−s` transported through `pembed s T`; the time
   reindexing is `u ↦ max (u−s) 0`, and the frozen stretch contributes `0`,
   which is exactly why the martingale clauses survive the delay.
2. **The `aglue` side conditions** `RXint`, `RCint`, `msecX`, `msecC`, `gintX`,
   `gintC` — integrability and measurability of the `w`-sections. These are
   Fubini-type statements about `ksemi Q ?B_T κ`, not new probability.

Then `paper_v_dpp_sup_ge_time_of_const` (already stated for arbitrary `θ`)
closes the `≥` half, and with `paper_v_cond_time` (the `≤` half, done) §2.1 is
finished.

## §2.1: the continuation kernel is COMPLETE (2026-08-08)

All nine kernel hypotheses of `paper_pair_class_aglue` are now supplied by
`pdelclass`, so the continuation side of step (4) is closed.

**The structural theorem** is that a delayed law keeps BOTH class martingales:

  `pdelclass_X_martingale` / `pdelclass_comp_martingale`

for `ν ∈ pdelclass k L T s`, on the fixed `T`-space, in `ν`'s OWN natural
filtration. **Delaying is a time change.** A delayed path read at `u` is the
base path read at `ρ u = min (max (u−s) 0) (T−s)`, which is nondecreasing, so
`martingale_time_change` gives a martingale for the time-changed filtration
`ℱ^μ_(ρ u)` — and that is exactly the filtration `martingale_pair_law` needs to
push it forward along `pembed`. Taking the base's OWN filtration instead makes
the statement FALSE (`ℱ^μ_u ⊋ ℱ^μ_(ρ u)` and the conditional expectation moves).

New generic tool: **`martingale_time_change_cong`** — the time change plus a
congruence for `u ≥ 0`, needed because the delayed process term and the
time-changed one agree only there, and a locale fact is about the term.

Derived: `pdelclass_X_int`/`comp_int` (Kint/KintC), `pdelclass_X_increment`/
`comp_increment` (Kinc/KincC), `pdelclass_X_mean`/`comp_mean` (Kmean/KmeanC,
via `martingale_mean_zero_of_start` + `pdelclass_start_zero`).
`pdelclass_diffquot` is Kcov, by the guarded rational route
(`closedin_diffquot_constraint` → `AE_distr_iff` → two `AE_ball_countable'`
passes → `diffquot_all_of_rational_ge`).

### Two hypothesis defects fixed on the way — and the rule they teach

`K0` and `Qst` were stated POINTWISE on `space (κ p')` / `space Q`. Since
`sets = sets ?B_T` forces the space to be the whole path space, both are
UNSATISFIABLE — the same defect `Kfr` had. `K0` was deleted (it is `Kfr` at
`u = 0`); `Qst` was weakened to `AE p' in Q. pstopped T θ p' = p'`, which cost
a refactor of `aglue_inner_increment` and its compensated twin: the two local
facts consuming it gain an idempotence hypothesis, and the three consumers move
from `Bochner_Integration.integral_cong[OF refl]` to
`set_lebesgue_integral_cong_AE`, which demands measurability of the integrands
at a RANDOM time (`path_eval_at_measurable_time`).

**Rule: never state a hypothesis about a path law pointwise on its space.**
See [[pointwise-on-space-is-unsatisfiable]].

### What is left of §2.1

1. **The PAST factor.** `paper_pair_class_aglue` still needs, for
   `Q = pair_law_of T (pstopped T θ) P` with `P` in the class: `PQ`, `setsQ`,
   `Q0`, `Qst` (now AE — `pstopped_idem` plus `path_stopping_time_stopped`),
   `Qcov`, `QH`, `QHC`, `Qcont`. `Stopped_Localization` and
   `paper_pair_class_stopped_*` are the intended sources; none of it is new
   probability.
2. **The glue side conditions** `RXint`, `RCint`, `msecX`, `msecC`, `gintX`,
   `gintC` — integrability and measurability of the `w`-sections of
   `ksemi Q ?B_T κ`. Fubini, not new probability.
3. **Assembly**: feed the result into `paper_v_dpp_sup_ge_time_of_const`.

## §2.1 past factor — status 2026-08-08 (end of session)

**Done, all green:** `pstopped_fixed_set_measurable`, `pstopped_law_prob` (PQ),
`pstopped_law_idem` (Qst), `pstopped_law_start` (Q0), `pstopped_law_cont`
(Qcont), **`pstopped_law_diffquot` (Qcov)**, and the adaptedness input
**`pstopped_eval_filtration`**.

Two things worth not re-deriving:

* **Qcov needs no guarded rational lemma.** Instantiate
  `diffquot_all_of_rational`'s HORIZON parameter with `θ p'` instead of `T`;
  the rationals it picks then satisfy `q < t ≤ θ p'` automatically. (This is
  different from step (3)'s clause (iii), which needed
  `diffquot_all_of_rational_ge` because there the guard was a LOWER bound.)
* **`pstopped_eval_filtration` avoids the componentwise route.** `(λω. pstopped
  T θ ω r)` is `ℱ_u`-measurable for `r ≤ u` AS A PAIR-PATH POINT. Read it off
  the `u'`-cut (`u' = u ∧ T`) rather than the whole path: `pcut u'` is
  measurable into the `u'`-horizon space by the very description of the natural
  filtration (`sets_natural_filtration_eq_pcut_vimage`), `r ∧ θ` is
  `ℱ_u'`-measurable (`{r ∧ θ ≤ t}` is everything, or `{θ ≤ t}` with `t < r`, or
  empty), and `path_eval_at_measurable_time` joins them. Do NOT decompose into
  `fst … $ i` and `snd … $ i $ j` and reassemble — that was the expected route
  and it is not needed.

### The three remaining pieces of §2.1, in order

**(A) `QH` / `QHC` — the stopped law's two square-integrable martingales.**
Everything needed is now in place; the shape is:

1. Under `P`, the class's coordinate process STOPPED at `θ` is a martingale.
   Template: `paper_pair_class_stopped_coord_martingale` (Paper_Bridge:1672)
   and `paper_pair_class_stopped_comp_martingale` (1746) — they do exactly this
   for the localisation time `ploc T i R`; substitute `θ`, whose stopping-time
   property is `path_stopping_time_event_filtration_all` in place of
   `paper_pair_class_ploc_stopping`. The engine is `optional_stopping[where
   D = HM.Dsup]` with `HM : horizon_sq_int_martingale`, and the adaptedness
   side condition is `stopped_adapted_of_cont`.
2. Push that forward along `pstopped T θ` with `martingale_pair_law`, whose
   `adap` is `pstopped_eval_filtration` and whose `FF` is `P`'s OWN natural
   filtration (no time change here — unlike the delayed class, the stopped path
   carries no more information than the past).
   Note `pstopped T θ ω (min u T) = ω (min (min u T) (θ ω))`, which is the
   template's `X (min u (θ ω)) ω` after `min`-associativity.
3. Square integrability of the stopped process transfers by
   `integrable_distr_eq`; the base bound is `paper_pair_class_sq_integrable`
   (and `paper_pair_class_comp_entry_sq_integrable` for the compensated entry).

**(B) The six glue side conditions** `RXint`, `RCint`, `msecX`, `msecC`,
`gintX`, `gintC` — integrability and measurability of the `w`-sections of
`ksemi Q ?B_T κ`. Fubini over the semidirect product; the tools are
`AE_integrable_ksemi_section` and the unbounded `integral_ksemi`, already used
in step (3).

**(C) Assembly.** `paper_pair_class_aglue` then gives the competitor, and
`paper_v_dpp_sup_ge_time_of_const` (already stated for arbitrary `θ`) turns it
into the `≥` half. The continuation kernel is
`λp'. Sel (θ p', fst (p' (θ p')))` with `Sel` the horizon-parametrised
selector; its `Kp` is `Selm`, and the nine kernel clauses are the `pdelclass_*`
family.

## §2.1 — status after the past factor (2026-08-08, later)

**The past factor is COMPLETE.** All eight `Q`-clauses of
`paper_pair_class_aglue` hold for `Q = pair_law_of T (pstopped T θ) P`:

| clause | lemma |
|---|---|
| `PQ` | `pstopped_law_prob` |
| `setsQ` | `sets_pair_law_of` |
| `Q0` | `pstopped_law_start` |
| `Qst` | `pstopped_law_idem` |
| `Qcov` | `pstopped_law_diffquot` |
| `Qcont` | `pstopped_law_cont` |
| `QH` | `pstopped_law_horizon_component` |
| `QHC` | `pstopped_law_horizon_compensated` |

**The engine for QH/QHC** is `horizon_sq_int_martingale_stopped`, abstracted
out of `paper_pair_class_stopped_coord_martingale` — whose proof uses the
localisation time ONLY through nonnegativity and the stopping property, so it
generalises to any stopping time verbatim. Doob's envelope `Dsup` supplies
both the dominating function `optional_stopping` wants AND the
square-integrability of the STOPPED process, which is what promotes the
conclusion back to a `horizon_sq_int_martingale`. Then `martingale_pair_law`
pushes it forward along `pstopped`, with `pstopped_eval_filtration` as the
adaptedness input and **`P`'s own filtration** — a stopped path carries no more
information than the past, so, unlike the delayed class, there is NO time
change here. `martingale_cong_ge` bridges the terms, which agree only for
`u ≥ 0`.

### What is left of §2.1: the six side conditions, then assembly

**(B) `RXint`, `RCint`, `msecX`, `msecC`, `gintX`, `gintC`.** These are Fubini
statements about `ksemi Q ?B_T κ`. Beyond the per-`p'` integrability that
`Kint`/`KintC` already give, each needs an OUTER bound — one that does not
depend on `p'`. **That input is now in hand**: `pdelclass_norm_mean_le` and
`pdelclass_comp_norm_mean_le` bound the inner first moments by constants in
`CARD('n)`, `L`, `T` alone, uniformly over the freezing time `s`, because a
delayed law reads the base law at an earlier time and the class's own bound
(`paper_pair_class_norm_mean_le`, `paper_pair_class_comp_norm_mean_le`) is
monotone in the horizon. The remaining work is the Fubini bookkeeping:
`AE_integrable_ksemi_section` and the unbounded `integral_ksemi` (both already
used in step (3)) plus `integrable_bound` against the constant.

**(C) Assembly.** `paper_pair_class_aglue` then yields the competitor, and
`paper_v_dpp_sup_ge_time_of_const` (already stated for arbitrary `θ`) converts
it into the `≥` half. The continuation kernel is
`λp'. Sel (θ p', fst (p' (θ p')))` with `Sel` from
`paper_v_measurable_selector_horizon`; `Kp` is its measurability, and the nine
kernel clauses are the `pdelclass_*` family. The optimality input on the glued
path is `pexit_pglue_dpp` transported through `padd`, exactly as
`paper_v_dpp_ge_const` does at a deterministic time.
