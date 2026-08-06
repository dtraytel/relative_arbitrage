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
| (0) | `v < ⊤` | **DONE for `paper_v`** (`paper_v_le_T`) and for `val_fn` / `stopped_val_fn` |
| (1) | regularity (usc) | **DONE for `paper_v`** — `Paper_Bridge.paper_v_usc_unconditional` |
| (2) | `visc_sol k L (interior K) v` | **OPEN** — needs the weak DPP, §2.1 |
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

### 2.1 The weak dynamic programming principle → clause (2)

**This is the only large item left.** Bouchard–Touzi's weak DPP replaces `v`
by test functions and so avoids measurable selection, which is exactly the
form the viscosity proofs consume. Estimated 1,500–3,000 lines, high risk.

BT09 is read and the fit assessed. Structure: Mayer form `V(t,x) = sup_ν
E[f(X_T)]`; assumptions A1–A4; Theorem 3.5 gives (3.1) `V ≤ sup_ν
E[V*(θ_ν, X(θ_ν))]` from the tower property alone, and (3.2) `V ≥ sup_ν
E[φ(θ_ν, X(θ_ν))]` for USC minorants `φ ≤ V`, using ε-optimal controls +
LSC of `J` + a Lindelöf cover of half-open boxes + countable pasting.

What does NOT transfer verbatim, and what to do about it:

1. Our objective is a sup of ESSENTIAL INFIMA, not of expectations. The
   essinf analogue of the tower property is essinf-pasting: `essinf τ = θ +
   essinf (shifted τ)` under concatenation at a stopping time `θ`. That
   needs the class closed under (i) conditioning/shifting at stopping times
   and (ii) countable pasting along a past-measurable partition.
2. (ii) is the crux — gluing via regular conditional distributions on the
   Polish path space. AFP `Disintegration` (`measure_disintegration`, built
   on `Standard_Borel_Spaces`, already a session dependency) supplies the
   core; the path space is Polish (`Path_Space.path_metric_polish`).
3. The ≤-half of the DPP needs only the shift/conditioning closure and is
   substantially easier than the ≥-half. Check which of the two viscosity
   inequalities of Definition 3.1 consumes which half BEFORE building the
   ≥-half.
4. The Lindelöf-cover step is formalizable and is not the bottleneck.

**Build order.** (a) shift operator on path laws + closure of the class
under conditioning — `pshift`/`pshift_law`/`martingale_pshift_law` (§1.3)
are the deterministic-shift prototype to generalise; (b) the ≤-half of the
essinf DPP; (c) assess which viscosity inequality remains; only then (d)
the pasting ≥-half via `Disintegration`.

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
- **Horizon-cap invisibility**: `paper_v` caps the exit time at `T`, while
  the paper's `v` does not. For `K ⊆ cball 0 r` and `T ≥ r²/(n−k)` the cap
  does not bind — same `ball_v_le` argument used for
  `clause_one_law_level`. The sharp form `paper_v ≤ ennreal (ball_v r k x)`
  follows from the same estimate but needs optional stopping at `pexit`
  (`Optional_Sampling.optional_stopping` with the `Doob_Inequality` envelope,
  as in the NC-1 localization).
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
