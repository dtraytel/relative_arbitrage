# Plan: reaching Theorem 1.1 of arXiv:2512.17702

Single source of truth for **what is proved, what is left, and in what
order**. Everything named here is machine-checked: `isabelle build -d .
Arbitrage` is green and there is no `sorry` anywhere in the session.

Superseded scoping, session logs and dead ends live in `PLAN_HISTORY.md`
and in `git log -p`. Do not resurrect them; do not re-derive anything in §1.

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
| (2) | `visc_sol k L (interior K) v` | **OPEN** — needs the DPP (Prop. 2.4) *and* §3's Itô/SDE layer, §2.1 |
| (3) | `v = 0` on `K − interior K` | ball case **DONE for `paper_v`** (`paper_v_boundary_zero`) and for `val_fn`/`stopped_val_fn`; interior value REALIZED for `n−k=1` (`Theorem_1_1.stopped_val_fn_ball_eq_2d`); general `n−k ≥ 2` **OPEN**, §2.2; transfer to `paper_v` §2.3 |
| (4) | uniqueness | **DONE** — `Theorem_1_1.theorem_1_1_uniqueness_general` |

**The one structural gap that spans clauses.** Three value functions exist:
`val_fn` (all `sufficiently_volatile_market` instances), `stopped_val_fn`
(the locale plus the paper's stopped/killed side conditions) and `paper_v`
(the class (1.7) as pair laws). Clauses (0), (1), (3)-ball and (4) are now
proved for `paper_v` itself. What still lives only on the market-side
functions is the `n−k=1` realization inside clause (3)
(`stopped_val_fn_ball_eq_2d`); transferring it, and the horizon-cap
argument, is the rest of §2.3.

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
| `paper_pair_class_shift_image` | the class at `x` is the `x`-translate of the class at `0` (LR Prop. 2.2(ii)) |
| `bmpair_law_in_paper_pair_class` | the class is NONEMPTY: Brownian motion paired with `Y_t = t·I`, capped at `T` |
| `paper_v_usc_unconditional` | **clause (1) for `paper_v`** |

Reusable machinery built for the above, none of it in the AFP — use it, do
not rebuild it:

- matrix-valued martingales: `martingale_matI`, `measurable_mat_entries`,
  `integrable_mat_entries`, `set_integral_mat_component`
  (`Ito_Market.martingale_vecI` does NOT iterate to `real^'n^'n`);
- martingale algebra: `martingale_add`, `martingale_add_const`,
  `martingale_cong_ge`, `martingale_stopped_const`;
- path-law transfer: `pair_law_of`, `martingale_pair_law`,
  `phi_filtration_measurable`;
- the shift: `pshift`, `pshift_law`, `martingale_pshift_law`,
  `AE_pshift_law(_iff)`, `ess_inf_time_pshift_law`;
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

### 1.5 Supporting layers

Berge/usc (`usc_sup_over_compactin`, `vshift_sup_usc_of_seq_compact`,
`Exit_Semicontinuity.ess_inf_pexit_usc`), the path space and its metric
(`Path_Space`), Doob/optional sampling (`Doob_Inequality`,
`Optional_Sampling`), the Brownian layer (`Brownian_Motion`,
`Brownian_Market`, `Brownian_Continuous`, `Brownian_Stopped`),
modification transfer (`Modification_Transfer`).

---

## 2. The path to Theorem 1.1

Three items, in this order. §2.3 is small and can be interleaved.

### 2.1 The dynamic programming principle (Proposition 2.4) → clause (2)

**This is the only large item left.** Estimated 1,500–3,000 lines, high risk.

**The paper's exact statement** (Prop. 2.4, verbatim modulo notation). For
any `x ∈ ℝⁿ` and any stopping time `θ` of the filtration generated by the
coordinate process `X`,

    (2.9)   v(x) = sup_{P ∈ 𝒫ₓ} P-essinf ( θ ∧ τ_K + v(X(θ))·1_{θ ≤ τ_K} ),

and the supremum is attained by any optimizer `P` of (1.6). The paper's
proof is one line — "repeat [LR24, proofs of Proposition 2.2(ii),(iii)] word
by word" — so the argument must be reconstructed from Larsson–Ruf.

**Which half feeds which viscosity inequality** (assessment done 2026-08-06
by reading §3.1 and §3.2 of the paper; do not redo it):

| viscosity inequality | DPP half it consumes |
|---|---|
| **subsolution** (§3.1, display (3.17)) | the DPP **at the optimizer**: `v(x) ≤ t∧θ + v(X(t∧θ))` P-a.s. for the fixed optimizer P. This is the CONDITIONING half. |
| **supersolution** (§3.2, after (3.25), and again in Case 2 after (3.30)) | `v(y) ≥ P_y-essinf (τ_{B_ε(x)} + v(X(τ_{B_ε(x)})))` for a SPECIFIC constructed `P_y`. This is the `≥` half, i.e. **pasting**. |

So both halves are needed; neither can be skipped. Beyond the DPP, §3 also
consumes machinery this development does not have: Itô's formula for class
members, an exponential local martingale plus optional sampling (3.18)–(3.19),
and weak solutions of the SDEs (3.11)/(3.24). **Budget §3 separately from the
DPP.**

**Build order and status.**

- **(a) closure under shortening the horizon — DONE.**
  `Paper_Bridge.paper_pair_class_pcut`: `Q ∈ paper_pair_class k L T x`,
  `0 ≤ S ≤ T` ⟹ `pair_law_of S (pcut S) Q ∈ paper_pair_class k L S x`, over
  `pcut`, `pcut_measurable`, `pcut_adapted`, plus the factored-out rational
  reduction `paper_pair_class_diffquot_of_pairs`.
- **(b) concatenation — path level DONE, law level PART DONE.**
  `pglue r T ω ω'` runs `ω` to `r`, then `ω'` re-based at `ω r`
  (`pglue_le/_ge/_zero`, `continuous_on_pglue`, `pglue_in_mspace`,
  `pglue_measurable` via `pathify_measurable`, and `pglue_diffquot` — where
  the `s < r < t` case is a CONVEX COMBINATION of the two pieces' quotients,
  so `sconstraint_convex` is exactly what makes pasting legal).
  `pglue_law r T Q R = pair_law_of T (λp. pglue r T (fst p) (snd p)) (Q ⊗⇩M R)`
  with `sets_pglue_law`, `space_pglue_law`, `prob_space_pglue_law`, the
  transfer principle `AE_pglue_law`, and clauses (i)–(ii) of (1.7):
  `pglue_law_start`, `pglue_law_diffquot`.
- **(b′) the two martingale clauses of `pglue_law` — DONE.**

      paper_pair_class_pglue_law:
        Q ∈ paper_pair_class k L r x ⟹ R ∈ paper_pair_class k L (T−r) 0
          ⟹ 0 ≤ r ≤ T ⟹ pglue_law r T Q R ∈ paper_pair_class k L T x.

  **The class is closed under independent concatenation.** New machinery,
  all reusable and none of it in the AFP:

  | result | content |
  |---|---|
  | `sets_pair_measure_mono`, `filtered_measure_pair` | the pointwise product of two filtrations is a filtration on the product measure |
  | `martingale_pair_fst`, `martingale_pair_snd` | a martingale of one factor, read on the product, is a martingale for the product filtration |
  | `martingale_pair_mult` | the PRODUCT of a first-factor martingale with a second-factor martingale is a martingale — where independence is genuinely used |
  | `martingale_cong_AE`, `martingale_time_change` | pass to an a.e.-equal adapted process; reparametrise time by a nondecreasing map |
  | `distr_pair_snd` | the `snd` twin of the library's `distr_pair_fst` |
  | `pglue_law_X_martingale`, `pglue_law_comp_martingale` | clauses (iii), (iv) of (1.7) for the pasted law |
  | `outerp_add`, `outerp_zero` | the algebra behind the cross term |

  **The proof idea worth keeping.** The lifting theorems avoid conditional
  expectations on the product AND any π-λ argument: Fubini turns the set
  integral over `A ∈ F u ⊗ₘ G u` into an iterated integral, and the section
  of `A` at a fixed coordinate is a set of `F u` (resp. `G u`) by
  `sets_Pair2`/`sets_Pair1` — so the FACTOR's `set_integral_eq` applies to it
  directly and the outer integrand is constant. For `martingale_pair_mult`,
  Fubini runs once in each variable, moving one factor's time index at a
  time.

  The compensated clause expands `outerp (Xᵣ + W) − (Yᵣ + ⟨W⟩)` into one
  compensated martingale from each factor plus the cross term
  `Xᵣ ⊗ W + W ⊗ Xᵣ`, handled entrywise through `martingale_matI` and
  `martingale_pair_mult`. The decomposition holds only a.e. — it uses
  `X'(0) = 0` from the second factor — hence `martingale_cong_AE`.

- **(c) the essinf DPP itself — IN PROGRESS.**

  Done so far:

  | result | content |
  |---|---|
  | `pexit_path_measurable` | the exit time of the X-component is Borel on the path space |
  | `paper_v_paste_ge` | if the glued path's exit time is a.s. `≥ c` then `ennreal c ≤ paper_v k L T K x` |
  | `pexit_pglue_split` | the glued path's exit time is `≥ r + c` once the first piece stays in `K` to `r` and the re-based continuation a further `c` |
  | `paper_v_paste_lower` | the two combined: **the pasting lower bound `ennreal (r + c) ≤ paper_v k L T K x`** — the `≥` half of (2.9) with ONE continuation |
  | `martingale_pair_snd_param` | the second-factor lift for a process that depends on the first coordinate too — the enabling lemma for an endpoint-DEPENDENT continuation |

  `pglue` re-bases the continuation at the endpoint automatically, so a single
  `R` started at `0` already supplies a continuation from EVERY endpoint. What
  (2.9) needs on top is to CHOOSE that law per endpoint. Remaining, in
  dependency order:

  1. **Kernel pasting at a deterministic time — PART DONE.**
     `kglue r T N p = pglue r T (fst p) (snd p (N (fst p)))`: run the first
     piece to `r`, then continue with the candidate the endpoint's index `N`
     selects. The second factor is `Pi⇩M UNIV RR`, the product of ALL
     candidates, so one probability space carries the family.

     | result | content |
     |---|---|
     | `sets_PiM_mono`, `filtered_measure_PiM` | `Pi⇩M` is monotone in the factors' σ-algebras; a pointwise product of filtrations is a filtration |
     | `martingale_distr` | transport of the martingale property along a pushforward — the general form of `martingale_pair_law` |
     | `martingale_PiM_component` | the `i`-th coordinate process is a martingale for the product filtration (split `i` off with `distr_pair_PiM_eq_PiM`, use `martingale_pair_fst`, transport back) |
     | `kglue`, `kglue_measurable`, `kglue_law`, `prob_space_kglue_law` | the construction; the index enters through `measurable_compose_countable` |
     | `AE_kglue_law`, `kglue_law_start`, `kglue_law_diffquot` | clauses (i)–(ii) of (1.7) |

     **Clause (iii) — DONE**, `kglue_law_X_martingale`. The decomposition is
     POINTWISE, unlike `pglue_law`'s: with `σ u = (u−r)⁺`, `τ u = min (σ u) (T−r)`,

         fst (kglue r T N p (min u T))
           = fst (fst p (min u r))
           + (fst (snd p (N (fst p)) (τ u)) − fst (snd p (N (fst p)) 0)),

     and subtracting the continuation's initial value makes the second
     summand LITERALLY `0` for `u ≤ r` — which is what makes it adapted
     there, since `N` is only `ℱ^Q_r`-measurable. First summand:
     `martingale_pair_fst`. Second: `martingale_pair_snd_param`, whose
     frozen-`ω` premise is `kglue_param_martingale` at the constant index
     `N ω`. Integrability is `Fubini_integrable`, with the inner integral
     computed by `distr_PiM_component` and bounded uniformly over the family
     by the new `paper_pair_class_norm_mean_le`.

     **Clause (iv) — the last piece.** Design settled, not yet written. Take

         D u p = (outerp b − Yb) + ((A p ⊗ b) + (b ⊗ A p)),
         A p = fst (fst p r),
         b  = fst (snd p i (τ u)) − fst (snd p i 0),
         Yb = snd (snd p i (τ u)) − snd (snd p i 0),   i = N (fst p),

     and `C u p = CQ u (fst p) + D u p` with `CQ` the first factor's
     compensated martingale on the clock `min u r`. Two points make this work:

     - use `fst (fst p r)` in the cross term, NOT `fst (fst p (min u r))`.
       Both give the same value (for `u ≤ r` the factor `b` is `0`, so the
       cross term vanishes whatever `A` is), but with `r` fixed the frozen
       process has a CONSTANT `A`, so the cross term is a bounded-linear
       image of the `b`-martingale (`martingale_bounded_linear_image`) rather
       than a product of two martingales. **No parametrized
       `martingale_pair_mult` is needed after all** — the earlier plan entry
       saying otherwise was wrong.
     - `outerp b − Yb` is only ALMOST everywhere the `i`-th coordinate's
       compensated martingale (it uses `X'(0) = 0` and `Y'(0) = 0`), so
       `martingale_cong_AE` on `Pi⇩M UNIV RR` is the last step there.

     What clause (iv) still needs beyond clause (iii)'s machinery: three
     integrability bounds on the product — for `outerp b` (quadratic, so
     `paper_pair_class_sq_mean_le` summed over coordinates), for `Yb` (an
     a.s. bound, `paper_pair_class_Y_bounded_ae`), and for `A ⊗ b` (a product
     of a first-factor and a second-factor variable, so
     `paper_pair_class_norm_mean_le` on each side — which must first be
     generalised from start `0` to a general start `x` for the `Q` factor).
     Estimated 600–800 lines.


  2. **ε-optimal selection.** For each `y` pick `R_y` with essinf `≈ v(y)`;
     BT09's Lindelöf cover of `K` by balls on which `v` varies by `< ε` gives
     the countable Borel partition. Formalizable, not the bottleneck.
  3. **The `≥` half of (2.9)** from 1 + 2, first at a deterministic time, then
     at a stopping time.
  4. **The `≤` half** — conditioning, i.e. regular conditional distributions on
     the Polish path space via AFP `Disintegration` (`measure_disintegration`,
     already a session dependency; `Path_Space.path_metric_polish`).

  **Warning about stopping times.** At a stopping time `θ` BOTH clocks `u ∧ θ`
  and `(u − θ)⁺` are random, so the product-filtration structure that carries
  (b′) — `F^Q_{min u r} ⊗ₘ F^R_{(u−r)⁺}` — breaks down. That is why the
  literature does this via regular conditional distributions rather than
  product measures; expect the stopping-time version to need a different
  construction from the deterministic-time one.

- **(d) §3**, the two viscosity inequalities — see the table above.

### 2.2 Clause (3) for general `n − k ≥ 2`

`n − k = 1` is done (§1.4). The general case needs spherical Brownian
motion — embed the deterministic-radius construction in an `(n−k+1)`-
dimensional coordinate subspace. Planned on the discrete route:
`Random_Walk_Market.thy`, `Relative_Arbitrage_Discrete.thy`,
`Path_Tightness.projective_limit_of_consistent_path_laws`.

### 2.3 Consolidating the clauses onto `paper_v`

Needed for the theorem to be about ONE object.

- **`paper_v` is bounded** — **DONE**, `paper_v_le_T`
  (`paper_v k L T K x ≤ ennreal T`, since `pexit T K f ≤ T`). That is
  clause (0) for the paper's value function.
- **Lemma 2.1's estimate at the class level** — **DONE**:
  `sconstraint_trace_ge` (`n − k ≤ trace a` on the constraint set, via
  `Pi_proj_le` at the identity projection), `bounded_linear_trace`,
  `trace_outerp`, `paper_pair_class_trace_martingale` (`|X|² − trace Y` is
  a martingale), `paper_pair_class_trace_rate` (`trace Y` grows at rate
  `≥ n − k`), and

      paper_pair_class_sq_norm_mean_ge:
        x∙x + (n−k)·t ≤ E[X_t ∙ X_t]   for 0 ≤ t ≤ T

  proved at a FIXED time — no stopping, no optional sampling.
- **Clause (3) for `paper_v` at the ball** — **DONE**,
  `paper_v_boundary_zero`: for `k < CARD('n)`, `0 < T`, `0 ≤ L` and
  `norm x = r`, `paper_v k L T (cball 0 r) x = 0`. If a member had a
  positive essential infimum for the exit time, almost every path would
  stay in the ball up to it, so the expected squared norm at an interior
  time would be `≤ r²` — against `≥ r² + (n−k)t` from
  `paper_pair_class_sq_norm_mean_ge`. No optional stopping.
- **Example 3.1's bound (3.10) for `paper_v`** — **DONE**,
  `paper_v_le_ball_bound`: for `k < CARD('n)`, `0 ≤ T`, `0 ≤ L` and any
  `K ⊆ cball 0 r`,

      paper_v k L T K x ≤ ennreal ((r*r − x∙x) / real (CARD('n) − k)).

  Same fixed-time estimate as above, no Itô and no optional stopping (the
  paper uses both). `paper_v_boundary_zero` is the case `|x| = r`, and this
  is the sharp form of clause (0) — note the bound does NOT mention `T`.
- **Horizon-cap invisibility** — **DONE, both halves.**
  `paper_v_horizon_stable` (the `≥` half, no pasting needed): cutting a
  horizon-`T` member back with `paper_pair_class_pcut` shortens the exit time
  only to `min τ S`, and `paper_v_le_ball_bound` says the value never exceeds
  `S` anyway. Supporting: `pfst`, `pexit_pfst`, `pfst_measurable`,
  `ennreal_min_eq`, `pexit_pcut_ge`.
  `paper_v_horizon_mono` (the `≤` half): paste the Brownian witness onto the
  tail with `paper_pair_class_pglue_law`; the glued path agrees with the
  original on `[0,S]`, so it cannot exit earlier (`pexit_pglue_ge`).
  Together, `paper_v_horizon_eq`: for `K ⊆ cball 0 r` closed and
  `(r²−x∙x)/(n−k) ≤ S ≤ T`,

      paper_v k L T K x = paper_v k L S K x.

  **So `paper_v`, defined on the CAPPED path space, computes the paper's
  uncapped `v` of (1.6).** The last discrepancy between the formalised object
  and the paper's is gone.
- **`stopped_val_fn ≤ paper_v`**: the bridge from market witnesses to class
  members. NOTE the recorded obstruction — a `stopped_market` witness is
  NOT a class member, because the paper's class never stops; the bridge must
  CONTINUE the witness past `tau` with an admissible volatility, and the
  martingale side needs an independent Brownian continuation, not just
  `Paper_Class.acont`. Only build this if clause (3)/(2) actually need the
  market-side results transported.

### Fallback

If §2.1 and §2.2 both stall, the bounded alternative is the rest of Section 4
(Theorem 4.2(b), 4.3, Prop 4.1 — 3,000–7,000 lines, reusing the
Crandall–Ishii investment).

---

## 3. Rules of engagement — read before editing

### 3.1 Three ways to lose a session

1. **Never register a NEW theory in `ROOT` mid-session.** The PIDE server
   snapshots `ROOT` at startup; a new node makes every theory report
   "Malformed theory", and reverting the edit does NOT recover it. If new
   material needs an import an existing theory lacks, ADD THE IMPORT to that
   theory — that works fine in-session.
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
`isabelle-pide-mcp-environment.md`. The two that have cost the most:

- **Under-constrained types are invisible.** A goal produced by a rule whose
  type instantiation you did not spell out can sit at a type where component
  lemmas no longer match *even though everything prints identically*
  (`continuous_on {0..T} (λt. t *⇩R mat 1)`, twice). Likewise an assumption
  like `paper_pair_class k L T 0 ≠ {}` elaborates its `0` at a fresh type
  variable with no warning. Annotate intermediate statements fully.
- **This dev `linarith` fails on plainly linear goals**; `argo` closes
  exactly those. And a division by a numeral in a premise makes it fail
  outright — restate the arithmetic without divisions.
