# Formalization status — arXiv:2512.17702

Lai, Shkolnikov, Soner, *Relative arbitrage problem under eigenvalue lower bounds*.

Goal: formalize **every** result of the paper in Isabelle/HOL, assumption-free
(no `sorry`, known theorems proved rather than assumed). Props 5.4 and 5.5 are
excluded by the user's instruction: they are not self-contained (the paper says
to repeat [LR24, Lemmas 5.7/5.6] and [LR24, Cor 5.9(iii)] word by word).

## Build

```bash
~/isabelle/bin/isabelle build -d . Arbitrage
```

- Session `Arbitrage`, 45 theory files on disk, 31 listed in ROOT (the rest are
  reached as imports), ~37 s warm, exit 0.
- ROOT `sessions`: `Martingales`, `Kolmogorov_Chentsov`, `Levy_Prokhorov_Metric`,
  `HOL-Complex_Analysis`. The last two were added for Section 2; both heaps were
  already built, so neither costs build time.
- No `sorry` / `oops` anywhere (check with `grep -cw 'sorry\|oops' *.thy`;
  note a plain `grep sorry\|oops` gives a FALSE POSITIVE on the word "loops").
  SECOND false-positive source, created and then removed on 2026-07-27: writing
  the literal keyword in a `text` block ("no sorry here") also trips the audit.
  Do not name the keyword in prose. PIDE's `commands_bad` count is the
  authoritative check and is immune to this.
- ASSUMPTION-FREE, WITH ONE NAMED EXCEPTION. A `sorry` check is not sufficient:
  a locale `assumes` is equally an assumption and is invisible to it. Audited —
  the only non-structural locale axiom is `comparison_principle`
  (Crandall-Ishii), which is never interpreted and on which no unconditional
  result depends; Theorem 4.2(a) is likewise isolated as the explicit predicate
  `max_principle_boundary`. Everything else that is claimed proved is proved.
  Re-run the audit with:

  ```bash
  grep -n -A3 '^locale ' *.thy | grep -B1 assumes   # locale axioms
  grep -rn 'comparison_principle\|max_principle_boundary' *.thy   # the two gaps
  ```

## Paper results

| Paper result | Status | Where |
|---|---|---|
| **Thm 1.1** (main theorem) | TODO | task 28 |
| Eq. (1.6) value function `v`, `v <= ball_v` | done | `Value_Function.thy` |
| Eq. (1.9) `F` as `ell_op`, `feasible` | done | `Relative_Arbitrage_PDE.thy` |
| Eq. (1.10) geometricity of `F` | done | `Relative_Arbitrage_PDE.thy` |
| **Lemma 2.1** (both directions, no closure) | done | `Lemma_2_1_Exact.thy` |
| **Lemma 2.2**, **2.3** (compactness of martingale laws) | 2.2 fixed-horizon subsequence extraction DONE (`path_laws_convergent_subsequence`); remaining: A5d architecture + vector bookkeeping; 2.3 open | task 25 |
| **Prop 2.4** (usc of `v` + pointwise DPP) | TODO — REQUIRED by Thm 1.1; `ess_inf_time` calculus done, see 25b/25g | task 25 |
| **Def. 3.1** (viscosity sub/super-solutions) | done | `Relative_Arbitrage_PDE.thy` |
| Eq. (3.4) `M_p`, `trace_Mp`, `ell_op_Mp` | done | `Lemma_3_1.thy` |
| **Eq. (3.5)** both inequalities (`ell_op_eq_half_bracket`) | **done** | `Poincare_Separation.thy` |
| **Eq. (3.6)** (`F^*` at `p = 0`, index shift) (`eq36`) | **done** | `Lemma_3_1_Envelopes.thy` |
| **Lemma 3.1** clause `F_* = F` at `p = 0` | done | `Envelopes.thy` |
| **Lemma 3.1** clause `F_* = F^* = F` off `p = 0` (`ell_op_envelopes_eq_off_zero`) | **done** | `Lemma_3_1_Envelopes.thy` |
| **Lemma 3.1** — all clauses, so LEMMA 3.1 IS COMPLETE | **done** | — |
| **Example 3.1** (ball, puncture removed) | done | `Brownian_Optimal_Boundary.thy` |
| **Thm 4.2** — smooth-strict case, any compact `K` (`visc_subsol_le_smooth_strict`) | **done** | `Relative_Arbitrage_Comparison.thy` |
| **Thm 4.2(a)** — two semicontinuous functions, general `K` | TODO, needs Crandall-Ishii | task 26 |
| **Thm 4.2(b)**, **Thm 4.3**, **Prop 4.1** — general `K`, from the 4.2(a) interface | **done** | `Lemma_3_1_Envelopes.thy` |
| **Thm 4.3**, **Prop 4.1** — for `K` a ball, UNCONDITIONALLY (`comparison_ball`, `uniqueness_ball`) | **done** | `Relative_Arbitrage_Comparison.thy` |
| **Prop 5.1**, **5.2** (continuity of `v`) | TODO, behind task 25 | task 27 |
| **Lem 5.3** — deterministic core (`eigen_lb_dim_obstruction`) | **done** | `Poincare_Separation.thy` |
| **Prop 5.4**, **5.5** | SKIPPED by instruction | — |

## Supporting development (not numbered in the paper)

| Component | Status | File |
|---|---|---|
| Spectral theorem, eigenbasis existence (`symmetric_eigenbasis`) | done | `Relative_Arbitrage_PDE.thy` |
| Ky Fan sums, ordered eigenvalues, `possum`, `bracket` | done | `Eigenvalues.thy` |
| Eigenvalue Lipschitz continuity | done | `Eigenvalue_Continuity.thy` |
| Threshold chains, `possum` on threshold sets | done | `Threshold_Chain.thy` |
| Courant-Fischer lower bound (`eigval_ge_of_subspace`) | done | `Poincare_Separation.thy` |
| General Poincare separation (`poincare_separation`) | done | `Poincare_Separation.thy` |
| Frobenius norm: transpose invariance, submultiplicativity | done | `Poincare_Separation.thy` |
| `M_p` Lipschitz in `p` off the origin (`Mp_lipschitz_away_from_zero`) | done | `Poincare_Separation.thy` |
| `F` Lipschitz in `p` (`ell_op_lipschitz_in_p`), ball bound | done | `Poincare_Separation.thy`, `Lemma_3_1_Envelopes.thy` |
| Degenerate ellipticity of `F` at the infimum (`ell_op_elliptic_le`) | done | `Lemma_3_1_Envelopes.thy` |
| Feasible set entrywise/trace bounds (`feasible_trace_bound`) | done | `Lemma_3_1_Envelopes.thy` |
| Brownian motion construction | done | `Brownian_Motion*.thy`, `Brownian_Continuous.thy` |
| Quadratic variation, optional sampling, Doob | done | `Quadratic_Variation.thy`, `Optional_Sampling.thy`, `Doob_Inequality.thy` |
| Ball uniqueness WITHOUT Crandall-Ishii (`ball_v_unique_solution_smooth`) | done | `Relative_Arbitrage_Comparison.thy` |
| Crandall-Ishii / theorem on sums | **NOT PROVED — assumed** | `locale comparison_principle`, see task 26 |
| Section 4 chain below 4.2(a) (`uniqueness_from_max_principle`) | done | `Lemma_3_1_Envelopes.thy` |
| Ito interface + discrete and Brownian market instances | done | `Ito_Market.thy`, `Random_Walk_Market.thy`, `Brownian_Exit.thy` |
| Feasible set bounded (`feasible_bounded`, `feasible_offdiag_abs_le`) | done | `Relative_Arbitrage_Comparison.thy` |
| `ess_inf_time` calculus for Eq. (2.9) (`ess_inf_time_AE`, `_superadd`) | done | `Value_Function.thy` |
| Measurable selection (needed by Prop 2.4) | **absent from Isabelle+AFP** | task 25, see 25g |
| Arzela-Ascoli step of Lemma 2.2 (`holder_family_subsequence`) | done | `Section_2_Compactness.thy` |
| Eq. (2.7) assembly (`fourth_moment_of_compensated`) | done | `Moment_Bounds.thy` |
| Increment second-moment bound (`increment_second_moment_bound`) | done | `Increment_Moments.thy` |
| Localised second-moment bound (`second_moment_partition_bound`) | done | `Increment_Moments.thy` |
| **Eq. (2.7) with explicit remainder** (`fourth_moment_partition_bound`, const `8C^2` vs paper's `66C^2`) | **done** | `Increment_Moments.thy` |
| Weighted interval bound (`weighted_interval_bound`) | done | `Increment_Moments.thy` |
| Uniform `L^2` bound on `SUM d^2` (`sum_sq_squared_bound`) | done | `Increment_Moments.thy` |
| Uniform partitions of `[s,T]` (`upart` + kit) | done | `Increment_Moments.thy` |
| a2-lim steps 1-2 (`sum_pow4_le_max_times_sum`, `prod_le_K_split`) | done | `Increment_Moments.thy` |
| a2-lim step 3 (`expectation_max_sq_tendsto_zero`) | done | `Increment_Moments.thy` |
| a2-lim step 4 (`remainder_tendsto_zero`) | done | `Increment_Moments.thy` |
| **Eq. (2.7), bounded case** (`fourth_moment_bound_bounded`, const `8C^2`) | **done** | `Increment_Moments.thy` |
| Ito isometry in process form (`ito_isometry_process`) | done | `Stochastic_Integral_Simple.thy` |
| Compensated square = simple integral + discrepancy (`compensated_square_decomposition`) | done | `Stochastic_Integral_Simple.thy` |
| Mesh limit of the remainder `SUM E[d^4]` | **the one remaining gap** (plan A2) | task 25, see 25f/25h |
| Sampling bridge: continuous-time martingale to discrete (`martingale_sampled`) | done | `Sampled_Martingale.thy` |
| Quadratic Ito + energy identity along a partition | done | `Sampled_Quadratic_Variation.thy` |
| Conditional increment identity (`cond_exp_increment_sq`) | done | `Sampled_Quadratic_Variation.thy` |
| `Z_martingale` reduced to the covariation hypothesis (`martingale_of_cond_increment`) | done | `Sampled_Martingale.thy` |
| `Z_martingale` as a THEOREM at `ito_Z` (`Z_martingale_of_cond_covariation`) | done | `Ito_Covariation.thy` |
| Simple stochastic integral: martingale, L^2, Ito isometry | done | `Stochastic_Integral_Simple.thy` |
| `L^2` limits / Riesz-Fischer (`L2_cauchy_ae_limit`) | done | `L2_Limits.thy` |
| `L^2` closure of the simple integrals (`simple_itg_L2_closure`) | done | `Stochastic_Integral_L2.thy` |
| Burkholder-Davis-Gundy | **absent** — blocked behind task 15 | task 25, needed by Lem 2.2 |
| Skorokhod layers 1-3: continuity sets, small cover, small PARTITION | done | `Measure_Continuity_Sets.thy` |
| Skorokhod layer 4: stacking masses into intervals (`slab_UN`) | done | `Stacking_Intervals.thy` |
| Skorokhod representation on a Polish space | layer 5 remaining | task 25, see 25d |
| Vitali convergence theorem + uniform integrability | **done — built here** | `Vitali_Convergence.thy` |
| Dyadic-to-Holder interpolation (`holder_of_dyadic_moduli`) | done | `Holder_Interpolation.thy` |
| Path space `C({0..T})` Polish + compact Holder balls + `path_law` | done | `Path_Space.thy` |
| **Tightness of path-law families** (`tight_on_set_path_laws`) | **done** | `Path_Tightness.thy` |
| **Lemma 2.2 subsequence extraction, fixed horizon** (`path_laws_convergent_subsequence`) | **done** | `Path_Tightness.thy` |
| **Vector (`R^n`-valued) versions of all three** (`path_law_holder_ball_bound_vec`, `tight_on_set_path_laws_vec`, `path_laws_convergent_subsequence_vec`) | **done** | `Path_Tightness.thy` |
| **Lemma 2.2 from the MARTINGALE package** (`path_laws_convergent_subsequence_market`: per-coordinate L2 martingale + compensated square + adapted rate-`C` compensator, no moment hypotheses) | **done** | `Path_Tightness_Market.thy` (BATCH-ONLY: draft diamond over Increment_Moments) |
| Continuous-mapping theorem for weak convergence (`weak_conv_on_pushforward`) | **done** | `Path_Space.thy` |
| Projective consistency of diagonal limits (`path_laws_diagonal_consistent`) | **done** | `Path_Tightness.thy` |
| Path-space evaluation continuity + Fatou for weak limits (`continuous_map_path_eval`, `weak_conv_on_nn_integral_le`) | **done** | `Path_Space.thy` |
| Feasible set CLOSED (Lemma 2.3 B3 core, `closed_feasible`) | **done** | `Poincare_Separation.thy` |
| `ess_inf_time` under pushforward (`ess_inf_time_distr`) | **done** | `Value_Function.thy` |
| Theorem 1.1 ball fragment (`theorem_1_1_ball_fragment`) | **done** | `Theorem_1_1.thy` (BATCH-ONLY) |

## Open tasks

### 24 — DONE: Lemma 3.1 complete

All three clauses proved. Eq. (3.5) is `ell_op_eq_half_bracket`; Eq. (3.6) is
`eq36`; the continuity clause off the origin is
`ell_op_envelopes_eq_off_zero`, via `ell_op_lsc_off_zero` /
`ell_op_usc_off_zero`.

The continuity clause rests on: `ell_op_sym_part` (`F` cannot see the
antisymmetric part of `M`, so nearby NON-symmetric matrices are covered);
`bracket_lipschitz_norm`; `norm_rank1proj_diff_le` (constant `4/||p||`, which
blows up at the origin -- exactly why Eq. (3.6) is a different formula there);
`norm_matrix_mult_le` and `norm_transpose_matrix` (Frobenius, neither in this
HOL-Analysis); `Mp_lipschitz_away_from_zero`; `ell_op_lipschitz_in_p`;
`ell_op_ball_bound`; then `ereal_le_epsilon2`.

Two facts made it tractable and are worth remembering: the correction
coefficient `min(eigval n M) 0` in `Mp` does NOT depend on `p`, so `Mp`'s only
`p`-dependence is `rank1proj p`; and combined with the symmetric-part reduction
this makes the `p`- and `M`-variations separate, so NO product-topology
reasoning is needed.

### 31 — DONE: Eq. (3.5), both inequalities

`ell_op_eq_half_bracket` (Poincare_Separation.thy).

Upper inequality, an unbroken chain:

```
eigval_ge_of_eigen_lb        Courant-Fischer: eigen_lb a m ==> 1 <= eigval m a
  -> sum_min_weights_ge      step (A): real m <= sum_{u in B} min (u.(a *v u)) 1
  -> box_program_bound       step (B): box program over t in [0,1], sum t >= m
  -> lp_upper_bound          assembly via w = t + s, s in [0, L-1]
  -> sum_min_le_threshold    arbitrary size-m set dominated by a threshold set
  -> bracket_upper_bound     ... <= bracket m L N
  -> trace_le_bracket_feasible   trace (M ** a) <= bracket (n-k) L (Mp p M)
  -> ell_op_ge_half_bracket  -(1/2) * bracket (n-k) L (Mp p M) <= ell_op k L p M
```

Reverse inequality: `bracket_attained` EXHIBITS the optimum. Weights `L` on the
positive eigendirections of `Mp p M`, `1` on a top-`m` threshold set chosen
INSIDE `B - {q}` with `q = p/|p|`; choosing it away from `q` is what gives
`a *v p = 0`, possible because `m = n-k <= n-1` when `k >= 1`. The value is
EXACTLY the bracket. Feasibility via `psd_weighted_outer_sum`,
`weighted_outer_sum_annihilates`, `eigen_ub_weighted_outer_sum`,
`eigen_lb_weighted_outer_sum`.

### 32 — DONE: Courant-Fischer lower bound

`eigval_ge_of_subspace` (general constant `c`; the `eigen_lb` form is the
corollary `eigval_ge_of_eigen_lb`). Dimension count via `dim_inter_ge`,
`dim_hyperplane`, `subspace_inter_nonzero`.

WARNING recorded here because it cost a wrong plan: `kyfan_ge_of_eigen_lb` is
NOT strong enough for step (A). It gives only `real m <= kyfan m a`; for `m = 2`
and eigenvalues `(10, 0, ...)` that holds while `sum_j min(mu_j,1) = 1 < 2`. The
fact needed is `eigval m a >= 1`, which is what `eigval_ge_of_eigen_lb` gives.

### 25 — Section 2 (Lemmas 2.2, 2.3, Prop 2.4)

DONE so far — the deterministic layer, all of it:

- `inner_axis_one`, `matrix_vector_axis_one` — coordinate-vector computations;
- `feasible_diag_bound` — `0 <= a$i$i <= L` on the feasible set;
- `feasible_trace_bound` — `0 <= trace a <= real CARD('n) * L`;
- `feasible_offdiag_abs_le`, `feasible_bounded` — Lemma 2.2's hypothesis
  ("S bounded") for the paper's S. Via `quadform_axis_pair`; the earlier note
  that this was "the next step" is now stale.
- `eigen_lb_iff_eigval_ge`, `feasible_iff_eigval` — turn the eigenvalue lower
  bound into a closed condition on a Lipschitz function of `a`, which is what
  Lemma 2.3's compactness (bounded + closed) needs. Convexity is already in
  `Relative_Arbitrage_Convexity.thy` — do not reprove.

DONE — the Arzela-Ascoli step (`Section_2_Compactness.thy`, new, green):

- `holder_bound_norm` — a Holder path on `{0..T}` is bounded by its initial
  value plus `c * T powr ga`;
- `holder_equicontinuous` — a Holder bound with a constant COMMON to the family
  gives equicontinuity, with the explicit modulus `d = (e/(c+1)) powr (1/ga)`;
- `holder_family_subsequence` — THE Arzela-Ascoli step of Lemma 2.2: a family
  of paths sharing an initial value and a Holder constant has a uniformly
  convergent subsequence whose limit has the same initial value and the same
  Holder bound. Built on `HOL-Complex_Analysis.Arzela_Ascoli`; the two limit
  transfers are `LIMSEQ_const_iff` and `tendsto_upperbound`;
- `holder_family_subsequence_dist` — the same phrased with `dist`, so it
  composes directly with the AFP's `holder_on`;
- `holder_onI_bound` — a uniform bound gives `ga-holder_on`.

### DEPENDENCY AUDIT for Section 2 — done thoroughly, record it

The paper's own reference lists (checked against the arXiv HTML) are:

- Lemma 2.2 uses Ito's formula, Burkholder-Davis-Gundy, Kolmogorov's continuity
  criterion [RY99 I.2.1], Prokhorov, Arzela-Ascoli.
- Lemma 2.3 uses Lemma 2.2, Prokhorov, Skorokhod representation, Vitali
  convergence, Lebesgue's FTC.

AVAILABLE (verified by name, not by guessing):

| Need | Where |
| --- | --- |
| Kolmogorov continuity criterion | AFP `Kolmogorov_Chentsov.Kolmogorov_Chentsov` (line 1355). Hypothesis is LITERALLY Eq. (2.7) with `a = 4`, `b = 1`, `C = 66 C^2`; conclusion is a modification with `local_holder_on ga {0..}` for `ga < b/a = 1/4`. |
| local Holder -> Holder on a compact | AFP `Kolmogorov_Chentsov.local_holder_compact_imp_holder` |
| Arzela-Ascoli | `HOL-Complex_Analysis.Great_Picard.Arzela_Ascoli` (line 694). General: `'a::euclidean_space -> 'b::{real_normed_vector,heine_borel}`. NOT in HOL-Analysis — grepping HOL/Analysis for it finds nothing, which is what made an earlier note say it was missing. |
| Prokhorov | AFP `Levy_Prokhorov_Metric.Prokhorov_theorem_LP`, plus `tight_on_set_imp_convergent_subsequence` and `relatively_compact_imp_tight_LP` |
| `C(X, R^n)` complete + separable (Polish) | `HOL-Analysis.Urysohn.cfunspace` (def line 3375) with `mcomplete_cfunspace`; separability is AFP `Standard_Borel_Spaces.separable_space_cfunspace`. This is the SET-BASED `Metric_space` framework — the same one `Levy_Prokhorov_Metric` uses, so they compose. |
| Lebesgue FTC | HOL-Analysis |

WAS MISSING FROM ISABELLE ENTIRELY — searched the distribution and all 1135 AFP
sessions. One of the three has now been BUILT here; the status of each:

1. **Vitali convergence theorem — DONE, added** (`Vitali_Convergence.thy`, 860
   commands, green). `uniformly_integrable` occurred nowhere in HOL-Analysis,
   HOL-Probability, or any AFP entry, and HOL-Analysis
   `Vitali_Covering_Theorem` is an unrelated result, so this was written from
   scratch. See the section on it below.
2. **Burkholder-Davis-Gundy — still missing.** No hit for
   `Burkholder`/`BDG`/`Davis_Gundy` anywhere. BLOCKED: every route to BDG runs
   through the continuous-time stochastic integral, i.e. open task 15, which the
   user deferred. Do not attempt before 15.
3. **Skorokhod representation on a Polish space — IN PROGRESS, layer 1 done.**
   The distribution has `HOL-Probability.Weak_Convergence.Skorohod` (line 123,
   note the spelling), but it is the classical ONE-DIMENSIONAL version —
   signature `real measure` and `nat => real => real`, proved through
   `cdf_distribution` and the quantile transform. Lemma 2.3 needs it on
   `C([0,inf), R^n)`. The AFP has no `Skorohod`/`Skorokhod` at all.

   Two routes were checked and REJECTED, record them so they are not retried:
   (a) transferring the 1-D version along a Borel isomorphism — invalid, the
   statement is topological, not merely Borel; (b) the coupling/Strassen-Dudley
   route via the Levy-Prokhorov metric — the AFP has no coupling, Wasserstein or
   Kantorovich development at all (the AFP entry named `Transport` is about
   transporting properties along equivalences, nothing to do with measures).

   So it needs the Billingsley construction: nested finite Borel partitions into
   small-diameter pieces with null boundaries, then the coupling built on
   `[0,1)` under Lebesgue measure, then Borel-Cantelli. Layer 1 of that is now
   DONE — see 25d.
4. **Ito's formula for continuous semimartingales** — this is open task 15,
   deferred by the user.

### 25c — DONE: Vitali's convergence theorem (`Vitali_Convergence.thy`)

Built because Lemma 2.3 invokes it and Isabelle did not have it. Green, no
`sorry`, imports only `HOL-Probability.Probability`.

- `unif_integrable M f` — the definition, as a tail condition:
  every `f n` integrable, and for each `e > 0` some `K >= 0` with
  `(nn_integral of max 0 (|f n x| - K)) <= e` for ALL `n`. Stated with
  `nn_integral` so the definition needs no integrability side condition to make
  sense; `tail_bochner_le` converts it to the Bochner integral where needed.
- `tail_bound_limit` — the tail bound passes to an a.e. limit. This is the Fatou
  step: `nn_integral_liminf` plus `lim_imp_Liminf` to identify the liminf, plus
  `Limsup_bounded` and `Liminf_le_Limsup` for the numeric bound.
- `clamp_diff_abs`, `clamp_abs_le`, `integrable_tail`, `integrable_clamp` — the
  truncation `T y = max (-K) (min K y)` and its two defining identities
  `|y - T y| = max 0 (|y| - K)` and `|T y| <= K`. NOTE `integrable_tail` needs
  `0 <= K`: for negative `K` the bound `max 0 (|y|-K) <= |y|` is false.
- `unif_integrable_limit_integrable` — the a.e. limit of a uniformly integrable
  sequence is integrable, via `integrableI_bounded` and
  `|g| <= max 0 (|g| - K) + K`.
- **`vitali_convergence`** — the theorem: on a finite measure space, uniform
  integrability plus a.e. convergence gives `L^1` convergence,
  `(integral of |f n x - g x|) ---> 0`. The proof is the classical
  three-term split
  `|f n - g| <= (|f n| - K)^+ + |T(f n) - T(g)| + (|g| - K)^+`,
  with the outer two terms `<= e/4` by uniform integrability and its transfer to
  the limit, and the middle term `---> 0` by
  `integral_dominated_convergence` dominated by the constant `2 * K`.
- `tail_le_moment`, `unif_integrable_of_moment_bound` — the practical criterion:
  a uniform bound on the `p`-th moments for any `p > 1` implies uniform
  integrability, via `max 0 (|y| - K) <= |y| powr p / K powr (p-1)` and
  `K = max 1 ((C/e) powr (1/(p-1)))`. This is the entry point a moment bound of
  the shape of Eq. (2.7) would use.

So the remaining probabilistic content of Lemma 2.2 is exactly: derive Eq. (2.7)
(needs Ito + BDG, i.e. task 15 plus a new BDG), then produce a Holder constant
that is UNIFORM over the family. The second half is the subtle one and is worth
stating explicitly: `ga-holder_on` quantifies its constant existentially per
function, so "every path is Holder" does NOT give the common constant that
Arzela-Ascoli requires. Getting it is what the fourth-moment bound is for.

### 25e — Eq. (2.7) and what Lemma 2.2 actually needs from task 15

FROM REREADING THE PAPER (structure of Lemma 2.2's proof, confirmed against the
arXiv HTML):

- Eq. (2.7) is `E |X t - X s| ^ 4 <= 66 * C ^ 2 * (t - s) ^ 2`.
- Ito's formula is applied to `Z t = |X t - X s| ^ 2 - tr (qvar X t) + tr (qvar X s)`,
  which is a martingale because `X` is.
- BDG is used to get `E [qvar Z t] <= 8 * C ^ 2 * (t - s) ^ 2`, and thence (2.7).
- Kolmogorov's criterion then gives Holder exponent `gamma` in `(0, 1/4)`
  (= `b/a` with `a = 4`, `b = 1`).

**IMPORTANT SCOPE FINDING.** The test function is QUADRATIC. Lemma 2.2 does NOT
need Ito's formula for general `C^2` functions -- only for `|x| ^ 2`. That is
exactly the shape of the `Z_martingale` assumption in `locale ito_volatile_market`
(`Ito_Market.thy:52`), and the discrete analogue `ito_discrete_quadratic` is
already proved, as is `|B t| ^ 2 - n * t` for the constructed Brownian motion
(task 16). So task 15 does NOT have to reach full `C^2` Ito before Lemma 2.2
becomes reachable; the continuous-time QUADRATIC case suffices. Layer (6) of
task 15 should be re-scoped accordingly.

DONE: the assembly step, `Moment_Bounds.thy` (green, no `sorry`):

- `square_add_le_two` — `(a + b)^2 <= 2a^2 + 2b^2`;
- `integral_square_le_of_bound` — a bounded function on a probability space has
  second moment at most the square of the bound;
- **`fourth_moment_of_compensated`** — given the split `D = Z + T` of the squared
  increment into compensated martingale plus trace increment, a second-moment
  bound `E[Z^2] <= K (t-s)^2`, and the rate bound `|T| <= C (t-s)`, conclude
  `E[D^2] <= (2K + 2C^2) (t-s)^2`. Since `D = |X t - X s| ^ 2`, `E[D^2]` IS the
  fourth moment, so this is Eq. (2.7) modulo its two inputs, both task-15 items.

So Lemma 2.2 now reduces to exactly TWO stochastic-calculus inputs — the
quadratic Ito martingale and a second-moment bound on it — with every other step
(assembly, Kolmogorov, Arzela-Ascoli, Prokhorov) proved or available.

### 25b — Proposition 2.4: scope question RESOLVED — it is REQUIRED

The arXiv HTML confirms the proof of Prop 2.4 reads, in full, that it suffices to
repeat [LR24], proofs of Proposition 2.2(ii), (iii) *word by word* — the same
phrasing by which the user excluded Props 5.4 and 5.5.

BUT THE EXCLUSION DOES NOT TRANSFER, and the reason is downstream reach, not proof
style. Checked against the paper (2026-07-27): **Theorem 1.1 depends on Prop 2.4**,
in two separate ways.

1. **Upper semicontinuity of `v` is part of Theorem 1.1's own STATEMENT** — the
   theorem asserts `v` is an UPPER SEMICONTINUOUS viscosity solution, and Prop 2.4's
   first clause is exactly that. Dropping 2.4 would weaken the main theorem, not
   merely shorten the development.
2. **The DPP is used inside the viscosity proofs** — Section 3.1's subsolution
   argument (around Eqs. (3.17), (3.25)) and Section 3.2's supersolution argument
   (around Eq. (3.26)).

Prop 5.2 also depends on Prop 2.4, so task 27 inherits the dependency.

By contrast Props 5.4/5.5 feed only Section 5's tail; nothing Theorem 1.1 needs
passes through them. THAT is why excluding them costs nothing while excluding 2.4
would cost the main theorem. The shared "word by word" phrasing is a red herring —
the criterion that matters is downstream reach.

CONSEQUENCE FOR THE WORK, and it is a real one: because the paper's own proof of
Prop 2.4 is a POINTER rather than an argument, formalizing it means RECONSTRUCTING
[LR24]'s proof of their Prop 2.2(ii),(iii) — measurable selection to paste controls
together, plus the upper-semicontinuity argument — not transcribing anything from
this paper. Budget it as original work. This is the ONE place in the development
where the instruction "follow the paper closely" cannot be obeyed literally,
because there is no proof text to follow.

### 25g — Prop 2.4: dependency audit and the `ess_inf_time` calculus

DEPENDENCY AUDIT for the DPP, done 2026-07-27:

- **Regular conditional probability / disintegration: AVAILABLE.** AFP entry
  `Disintegration`, with `measure_disintegration` (`Disintegration.thy:1539`). Its
  session needs `Standard_Borel_Spaces` and `S_Finite_Measure_Monad`;
  `Standard_Borel_Spaces` is already pulled in by `Levy_Prokhorov_Metric`, which is
  in our ROOT and builds, so the extra cost is only `S_Finite_Measure_Monad`.
  This is the machinery for CONCATENATING martingale laws at a stopping time.
- **Measurable selection: ABSENT.** Searched the whole AFP for
  `measurable_selection`, `Kuratowski`, `Ryll_Nardzewski`, `selection_theorem` —
  every hit is graph-theoretic Kuratowski, nothing measure-theoretic. This is the
  hard gate for the direction of the DPP that must EXHIBIT a near-optimal control
  measurably in the starting point, and for "the supremum is attained by any
  optimizer".

DONE — the `ess_inf_time` calculus (`Value_Function.thy`, green first try):

The value function of Eq. (1.6) is a supremum of ESSENTIAL INFIMA of exit times
(`val_fn = Sup (mkt_exit_vals ...)`, `ess_inf_time M tau = Sup {c. AE. c <= tau}`),
so Eq. (2.9) is an identity between essential infima and this calculus is needed
however the pasting is eventually done.

- `ess_inf_timeI` — any almost-sure lower bound is below the essential infimum;
- **`ess_inf_time_AE`** — the essential infimum is ITSELF an almost-sure lower
  bound. NOT immediate: it is a supremum over an uncountable family of almost-sure
  statements, and such suprema need not be almost sure. It works because the
  supremum is over CONSTANTS in `ennreal`, so
  `ennreal_Sup_countable_SUP` extracts a countable cofinal sequence whose
  almost-sure statements can be intersected with `AE_all_countable`.
- `ess_inf_time_mono` — monotone in the time, almost surely;
- **`ess_inf_time_superadd`** — `ess_inf f + ess_inf g <= ess_inf (f + g)` for
  nonnegative `f`, `g`. This is the shape in which Eq. (2.9) splits the exit time
  into the part before the stopping time and the continuation value.

WHAT REMAINS for Prop 2.4, in order: (i) clause (a), upper semicontinuity of `v`,
which needs compactness of `P_x` and so sits behind Lemma 2.3 and hence behind the
single remaining Lemma 2.2 gap of 25f; (ii) the concatenation of admissible laws at
a stopping time, for which AFP `Disintegration` supplies the machinery; (iii) the
measurable-selection step, which has no library support at all and must be built
from scratch — treat that as the critical path item for this proposition.

### 25d — Skorokhod layers 1-3 DONE: continuity sets and small covers (`Measure_Continuity_Sets.thy`)

Green, no `sorry`, imports only `HOL-Probability.Probability`. This is the
partition step's foundation: the Billingsley construction needs small Borel
pieces whose BOUNDARIES are null for the limit measure, and these supply them.

- `closed_sphere_metric`, `sphere_in_borel` — HOL-Analysis's `closed_sphere` is
  restricted to `real_normed_vector` + `heine_borel`, so the general metric-space
  version is proved here from `sphere x r = cball x r - ball x r`.
- `sphere_disjoint`, `disjoint_family_on_sphere` — spheres of distinct radii
  about a common centre are disjoint.
- **`finite_heavy_spheres`** — for a finite Borel measure, only FINITELY many
  spheres about a given centre have measure `> c`. The argument is the nice one:
  `n` such spheres are disjoint, so their measures sum to more than `n * c`,
  which must stay under `measure M (space M)`; pick `n` past that by
  `reals_Archimedean3` and `infinite_arbitrarily_large`.
- **`countable_positive_spheres`** — hence only countably many spheres carry any
  mass at all (countable union over `c = 1 / Suc k`).
- **`exists_null_sphere`** — therefore every open interval of radii contains a
  radius whose sphere is null, since the interval is uncountable
  (`uncountable_open_interval`).
- `frontier_ball_subset_sphere`, `null_frontier_ball_of_null_sphere`,
  **`exists_small_null_boundary_ball`** — the usable form: about any point there
  are arbitrarily small balls that are CONTINUITY SETS of `M`, i.e. with
  `measure M (frontier (ball x r)) = 0`. Weak convergence gives convergence of
  measures on exactly such sets, which is what makes the partition step work.

NOTE these are stated with `finite_measure M` as a HYPOTHESIS, not inside the
locale: the `finite_measure` locale already fixes its type without a sort, so a
`metric_space` constraint on it is rejected there ("Sort constraint metric_space
inconsistent with default type for type variable 'a").

LAYER 2 ALSO DONE, same file:

- `frontier_diff_subset` — `frontier (S - T) <= frontier S Un frontier T`, via
  `S - T = S Int (- T)` with `frontier_Int_subset` and `frontier_complement`.
  Needed because disjointifying a cover takes set differences, and the null
  boundaries have to survive that.
- **`exists_small_null_boundary_cover`** — on a metric space that is also
  `second_countable_topology`, for every `e > 0` there is a COUNTABLE family
  `B :: nat => 'a set` of open sets covering the whole space, each of diameter
  `< e` and each with `measure M (frontier (B k)) = 0`. Built from a countable
  dense set (`countable_dense_setE`) enumerated by `from_nat_into`, with radii
  chosen in `(e/4, e/2)` by `exists_null_sphere` — the lower bound `e/4` is what
  makes the family cover, the upper bound `e/2` is what bounds the diameter.

LAYER 3 ALSO DONE, same file: **`exists_small_null_boundary_partition`** — the
cover disjointified into a genuine partition, still small and still with null
boundaries. Built on the library's `disjointed`, so `disjoint_family_disjointed`
and `UN_disjointed_eq` give disjointness and the union for free; what needed
proof is that the boundaries survive the set differences, via
`frontier_diff_subset` and `frontier_UN_finite_subset`, plus
`null_measure_UN_finite`. WATCH OUT: `disjointed_def` produces `{0..<k}`, not
`{..<k}`, and the mismatch is silent -- state intermediate steps with `{0..<k}`.

LAYER 4 DONE, `Stacking_Intervals.thy` (green, no `sorry`): the cutting of the
unit interval that carries the coupling.

- `psum p n = (SUM i<n. p i)`, `slab p n = {psum p n ..< psum p (Suc n)}`;
- `psum_mono`, `psum_nonneg`;
- **`measure_slab`** — `measure lborel (slab p n) = p n`;
- **`disjoint_family_slab`** — the slabs are pairwise disjoint;
- **`slab_UN`** — for nonnegative summable `p`, the slabs exhaust exactly
  `{0 ..< suminf p}`. The forward inclusion uses `sum_le_suminf`; the reverse
  takes `k = (LEAST m. x < psum p m)`, which is a successor because
  `psum p 0 = 0 <= x`, and then `psum p j <= x < psum p (Suc j)`.

So for a partition with masses summing to 1, the slabs are a Lebesgue partition
of `[0,1)` with exactly the right measures -- which is what layer 5 maps into the
partition pieces.

REMAINING LAYERS for Skorokhod, in order: (3b) nest the layer-3 partitions over
`e = 1/k`;
(4) the stacking construction on `[0,1)` under Lebesgue measure matching
partition-set masses; (5) Borel-Cantelli to upgrade to a.s. convergence.

Note layer 2 is stated for the TYPE CLASS `{metric_space, second_countable_topology}`.
The eventual application is the path space, which lives in the SET-BASED
`Metric_space`/`cfunspace` framework (see task 25's dependency table), so a
translation layer will be needed there; the mathematics is unaffected.

### 26 — Section 4 (IN PROGRESS)

Unblocked by task 24 and started. Already proved in `Lemma_3_1_Envelopes.thy`:

- `ell_op_elliptic`, `ell_op_elliptic_le`, `ell_op_usc_elliptic_le` —
  degenerate ellipticity AT THE LEVEL OF THE INFIMUM, i.e. Eq. (4.3)
  `F(p,N) <= F(p,M)` when `N - M` is psd. Note
  `ell_op_pointwise_elliptic` (Relative_Arbitrage_PDE.thy) only gives this for a
  single feasible `a`; passing to the Inf is what Section 4 uses.
- `ell_op_lsc_off_zero_iff`, `ell_op_usc_off_zero_iff` — off the origin
  Definition 3.1's envelope inequalities ARE the envelope-free ones, so Section 4
  can work with `ell_op` directly.
- `ell_op_pinched`, `ell_op_strict_no_crossing`,
  `ell_op_strict_no_crossing_env` — the algebraic core of Thm 4.2's doubling
  argument: with `X <= Y`, sub- at `X` and super- at `Y` pin both values to `1`,
  and any strictness on the subsolution side is already a contradiction.

THREE INDEPENDENT ROUTES ARE NOW PROVED, and between them they cover everything
in Section 4 except one case.

ROUTE 1 — a GENERAL maximum principle whenever one function is smooth, with no
Crandall-Ishii input (`Relative_Arbitrage_Comparison.thy`):

- `visc_subsol_le_smooth_strict` — on any compact `K`, a subsolution is below any
  smooth STRICT supersolution that dominates it on the boundary;
- `smooth_strict_le_visc_supersol` — the dual.

The mechanism: at an interior maximum of `u - psi` the smooth `psi` IS an
admissible test function, so the subsolution property forces
`F(grad psi, hess psi) <= 1` there, contradicting strictness; hence the maximum
sits on the boundary. This is `visc_subsol_le_ball_v`'s argument abstracted away
from the ball, and it applies on any `K` carrying a smooth strict supersolution.

ROUTE 2 — the BALL case, fully unconditional
(`Relative_Arbitrage_Comparison.thy`): `comparison_ball`,
`comparison_ball_zero_boundary`, `uniqueness_ball`. Here the explicit solution
`ball_v` is INTERPOSED (`u <= ball_v <= w`), so Theorem 4.3 and Proposition 4.1
hold outright. This is the case Theorem 1.1 needs for Example 3.1, so task 28
has an unconditional Section 4 input.

ROUTE 3 — the general chain below 4.2(a), from a named interface
`max_principle_boundary k L K` (`Lemma_3_1_Envelopes.thy`):

- `max_principle_le` — Thm 4.2(b): zero boundary data for `u`, nonnegative for
  `w`, gives `u <= w` on `K`;
- `comparison_from_max_principle` — Thm 4.3 in the form used;
- `uniqueness_from_max_principle` — Prop 4.1, both directions;
- `max_principle_boundary_intro` — the single discharge obligation.

WHAT IS ACTUALLY LEFT: Theorem 4.2(a) for two MERELY SEMICONTINUOUS functions on
a general compact `K`. Neither can serve as a test function for the other, so
Routes 1 and 2 do not reach it; that case is genuinely Crandall-Ishii and nothing
short of it will do. Note this is not a gap in the ball case at all (Route 2).

CORRECTION, and this matters. An earlier version of this file said
"`Relative_Arbitrage_Comparison.thy` already has the Crandall-Ishii lemma". THAT
IS FALSE. What that theory actually contains is uniqueness for the BALL case
proved deliberately WITHOUT Crandall-Ishii (`ball_v_unique_solution_smooth`), by
using the explicit smooth solution as a test function. Its own header says so.
Task 10, titled "Formalize Crandall-Ishii comparison lemma", is mislabelled for
the same reason.

WHERE CRANDALL-ISHII ACTUALLY STANDS. It is ASSUMED, nowhere proved:
`locale comparison_principle` (Relative_Arbitrage_Uniqueness.thy:469) fixes the
comparison principle as an axiom. Mitigating facts, checked:
it is NEVER interpreted; its only consumer takes
`comparison_principle k L (ball 0 r)` as an explicit hypothesis; and the
unconditional ball result avoids it. So no assumption-free result in the repo
rests on it — but nothing proves it either.

Searched and NOT FOUND anywhere: the AFP has nothing on viscosity solutions;
this HOL-Analysis has neither Alexandrov's theorem (a.e. twice differentiability
of semiconvex functions) nor a Rademacher-type result. Proving 4.2(a) therefore
means building sup-convolutions -> semiconvexity -> Alexandrov/Jensen -> theorem
on sums: an independent development, plausibly larger than the eigenvalue chain,
and generic viscosity-solution infrastructure with nothing specific to this
paper. The paper itself only CITES [CI90].

NOTE ON A `sorry` AUDIT BLIND SPOT: a locale `assumes` is exactly as much an
assumption as a `sorry`, and `grep -cw 'sorry\|oops'` does not see it. Any claim
that this development is "assumption-free" must also audit locale axioms. The
audit was done: the only non-structural one is `comparison_principle` above; the
rest (markets, martingales, integrands) are parameter bundles that are
instantiated.

### 27 — Section 5

Lemma 5.3's DETERMINISTIC CORE IS DONE: `eigen_lb_dim_obstruction`,
`not_eigen_lb_of_large_degeneracy`, `feasible_empty_of_large_degeneracy`. A
covariance degenerate on a subspace `W` cannot satisfy `eigen_lb a m` unless
`m + dim W <= n`; on a face `F_x` this forces `dim F_x >= n-k`, and
contrapositively `dim F_x < n-k` leaves no admissible covariance at all, which
is the `v(x) = 0` side of Lemma 5.3.

Props 5.1 and 5.2 are NOT deterministic — both go through Prop 2.4's DPP, so
they are behind task 25. Skip 5.4 and 5.5.

### 28 — Theorem 1.1

**ASSEMBLY POINT CREATED (2026-07-29): `Theorem_1_1.thy`** (imports
Value_Function + Relative_Arbitrage_Comparison — BATCH-ONLY, draft diamond;
green, in ROOT). **`theorem_1_1_ball_fragment`**, the part of Theorem 1.1
provable today for `K = cball 0 r`: (1) `val_fn k L (cball 0 r) x0 <=
ennreal (ball_v r k x0)` everywhere (`val_fn_le_ball_v`); (2) equality on the
sphere (`val_fn_boundary`); (3) UNIQUENESS: any continuous viscosity solution
with `ball_v`'s boundary data equals `ball_v` on the ball (antisymmetry of
`visc_subsol_le_ball_v` / `ball_v_le_visc_supersol` — no Crandall-Ishii).
Once task 25 delivers usc + the viscosity property of `v` and Section 3.1's
lower bound, Theorem 1.1 for the ball follows by instantiating clause (3) at
`u = v`. The theory's header records exactly which inputs are missing and
where each comes from.

Example 3.1 is DONE (`ball_v_visc_sol_env` in Envelopes.thy proves `ball_v` is a
viscosity solution in the envelope sense with zero boundary values; the reverse
`E[tau] >= v(x0)` inequality is discharged in `Brownian_Optimal_Boundary.thy`).
An earlier version of this file listed "finish Example 3.1" as outstanding —
that is stale.

CORRECTION (2026-07-27): an earlier version of this entry said task 28 assembles
Thm 1.1 from "Lemma 2.1 + Lemma 3.1 + Section 4's uniqueness + Section 5's
continuity". That list was INCOMPLETE — it omitted Section 2. Checked against the
paper: Theorem 1.1 depends on Prop 2.4 and on Lemmas 2.2/2.3 as well. The full
dependency list for task 28 is:

- Lemma 2.1 (done);
- **Lemma 2.2 / 2.3** (task 25) — compactness of `P_x`, used to extract optimizers
  in the sub/supersolution arguments;
- **Prop 2.4** (task 25) — see 25b, needed TWICE (upper semicontinuity of `v`, and
  the DPP itself);
- Lemma 3.1 (done) and Example 3.1 (done);
- Section 4's uniqueness (task 26);
- Section 5's continuity (task 27), which itself needs Prop 2.4 via Prop 5.2.

Genuinely downstream; nothing to peel off — but it is downstream of MORE than the
earlier note claimed.

### 15 — Stochastic integration, continuous time

WHY IT IS NEEDED. The locale `ito_volatile_market` (`Ito_Market.thy:52`)
*assumes*

```
Z_martingale: "martingale M F 0 (ito_Z X acov)"
```

i.e. that `|X_t|^2 - int_0^t tr(a_s) ds` is a martingale -- which is exactly
Ito's formula for the quadratic test function. Task 15 replaces that assumption
by a theorem. It is needed for:

1. discharging the Ito interface for a GENERAL market; at present the locale is
   only instantiated concretely (Brownian ball exit, task 17; random walk,
   task 14), where `Z_martingale` was proved by hand;
2. weak existence for Eq. (3.11), the SDE the paper solves to build a controlled
   diffusion with prescribed covariance;
3. Prop 2.4 (DPP), where controls are concatenated.

It is NOT needed for Section 3's PDE side (deterministic linear algebra) nor for
Example 3.1 (already discharged concretely). It is needed for Theorem 1.1's
probabilistic half.

ALREADY DONE, layer 1, in `Stochastic_Integral.thy`, no assumptions:
- `mtrans`, `mtrans_vec`, `martingale_mtrans_vec` -- Eq. (1.1) as a genuine
  integral of the strategy against the market martingale;
- `ito_discrete_quadratic` -- discrete-time Ito for Example 3.1's test function;
- `dV_eq_value_process` -- identifies the relative value process of
  `Relative_Arbitrage_Discrete` as the gradient strategy's value process.

DEPENDENCY AUDIT (done properly, record it): there is NO stochastic integral, NO
Ito formula and NO Doob-Meyer decomposition anywhere in the Isabelle distribution
or the AFP. Searched for `Ito`, `ito_integral`, `stochastic_integral`,
`Doob_Meyer`; the only near-name hits are AFP `Stochastic_Matrices` (linear
algebra) and the MFOTL monitoring entries. So all of task 15 is from scratch.

What DOES exist and should be built on: AFP `Martingales` is INDEX-GENERIC. Its
`filtered_measure` fixes an arbitrary order-topology index, and it ships
`real_filtered_measure` / `real_sigma_finite_filtered_measure`. So continuous-time
filtrations and martingales are already expressible; only the integral is missing.

DONE, layer 2, in `Sampled_Martingale.thy` (green, no `sorry`, imports only
`Martingales.Martingale`):

- **`martingale_sampled`** — if `X` is a martingale for a REAL filtration `F`, and
  `t :: nat => real` is monotone and nonnegative, then `%k. X (t k)` is a
  martingale for the sampled filtration `%k. F (t k)`.
- `nat_filtered_of_sampled` — the sampled filtration is a
  `nat_sigma_finite_filtered_measure`, which is exactly the interface the
  repository's discrete development is stated over.
- `martingale_sampled_uniform` — the uniform-mesh case `t k = real k * dt`, the
  one used to build the integral by refinement.

WHY THIS IS THE RIGHT LAYER 2, and the observation to keep: for a SIMPLE
predictable integrand subordinate to a partition, the stochastic integral IS a
discrete martingale transform of the sampled process along the sampled
filtration. So `mtrans`, `martingale_mtrans`, `qvar`, `qvar_compensates` and
`expectation_sq_qvar` -- all already proved for `nat` -- transfer wholesale once
sampling is known to preserve the martingale property. That is what makes the
continuous theory reachable without redoing the discrete work.

Proof note: `unfold_locales` on the goal `martingale M (%k. F (t k)) 0 (%k. X (t k))`
produces exactly SEVEN raw subgoals (subalgebras, sets_F_mono, subalgebra at 0,
the raw sigma-finiteness existential, adapted, integrable, martingale_property).
Discharge the fourth with
`sigma_finite_measure.sigma_finite_countable[OF sigma_finite_subalgebra.sigma_fin_subalg[OF sf]]`
where `sf : sigma_finite_subalgebra M (F (t 0))` comes from
`X.sigma_finite_subalgebra_F`.

DONE, layer 3, in `Sampled_Quadratic_Variation.thy` (green first try, 76 commands,
272 ms; imports `Quadratic_Variation` and `Sampled_Martingale` -- both sit directly
on `Martingales.Martingale`, a SESSION theory, so this is not a draft diamond and
PIDE loads it fine):

- **`sq_int_martingale_sampled`** — the sampled process satisfies the locale
  `sq_int_martingale`. All three obligations discharge from the bridge:
  `nat_filtered_of_sampled`, `martingale_sampled`, and square-integrability of `X`.
  This is the key move: it makes the ENTIRE discrete quadratic-variation theory
  available in continuous time along an arbitrary monotone partition.
- `qvar_sampled_eq` — the sampled `qvar` written out as the sum of squared
  increments over the partition intervals.
- **`qvar_compensates_sampled`** — the QUADRATIC ITO FORMULA along a partition:
  `n |-> (X (t n))^2 - SUM k<n (X (t (Suc k)) - X (t k))^2` is a martingale.
- **`expectation_sq_sampled`** — the ENERGY IDENTITY: along any partition,
  `E[(X (t n))^2] = E[(X (t 0))^2] + E[SUM k<n (X (t (Suc k)) - X (t k))^2]`.
  This is exactly the second-moment input that Eq. (2.7) needs (see 25e).

### Z_martingale: VERIFIED AGAINST THE PAPER, AND REDUCED (2026-07-27)

The reading was checked against the arXiv HTML and CONFIRMED. The admissible family
`P_x` of Eqs. (1.6)-(1.8) is DEFINED by imposing: (i) `X` is a continuous martingale
with `X 0 = x`; (ii) the eigenvalue bounds on `d<X_i,X_j>(t)/dt`; and the `d/dt`
notation means absolute continuity of the covariation is part of the formulation.
So the covariation is DATA -- a constraint picking out which laws are admissible --
not something to be constructed. **No Doob-Meyer decomposition is needed anywhere.**

FINDING, and it settles what "prove Z_martingale" can mean: `Z_martingale` is NOT
derivable from the other assumptions of `locale ito_volatile_market`. Inspect the
locale (`Ito_Market.thy:52ff`): `acov` is a FREE PARAMETER, constrained only by
`acov_psd`, `acov_eigen_lb`, `acov_eigen_ub` and `acov_trace_integrable`. Nothing
among those ties `acov` to the covariation of `X`. `Z_martingale` IS the formal
content of the paper's defining hypothesis `d<X_i,X_j>/dt = a`. Any attempt to
"prove" it from the rest would be either circular or false.

WHAT WAS DONE INSTEAD -- reduce it to that hypothesis in primitive form, so the
locale no longer has to assume a martingale property of a compensated process.
In `Sampled_Quadratic_Variation.thy`, both green:

- **`cond_exp_increment_sq`** — specialising the partition to the TWO points `s, u`
  turns the energy identity into its conditional form:
  `cond_exp (F s) ((X u - X s)^2) = cond_exp (F s) ((X u)^2) - (X s)^2` a.e.
  So the conditional expectation of a squared increment IS a conditional variance.
  Proof: two-point partition, `qvar_compensates_sampled` at index `Suc 0`,
  `S.qvar_integrable` for the integrability of the increment, `cond_exp_diff` to
  split. NOTE the partition instance must be stated with `Suc 0`, not `1`: simp
  normalises the literal, so `t 1 = u` never fires (this is the recorded
  `eigval_1` trap in a new guise, and it caused all four initial failures).
- **`martingale_of_cond_increment`** — the reduction: `Sq - A` is a martingale as
  soon as `cond_exp (F s) (Sq u - Sq s) = cond_exp (F s) (A u - A s)` a.e. for all
  `0 <= s <= u`, given adaptedness and integrability of `Sq` and `A` separately.
  Proof: `martingale_of_cond_exp_diff_eq_zero` plus `cond_exp_diff` on the
  rearrangement `(Sq j - A j) - (Sq i - A i) = (Sq j - Sq i) - (A j - A i)`.

Taking `Sq t = X t . X t` and `A t = integral_{0..t} (trace o acov)`, these two
compose to: `Z_martingale` holds as soon as the conditional VARIANCE of each
increment of `|X|^2` matches the increment of `integral tr(acov)` -- which is
exactly the paper's defining condition, with nothing assumed about the compensated
process itself. That is the honest completion of this item.

LANDED (2026-07-27), in `Ito_Covariation.thy`. Build green, 39 s, exit 0.

DESIGN CHOICE, and why: the obvious edit -- rewrite `locale ito_volatile_market`
to assume the covariation condition instead of `Z_martingale` -- would force every
concrete instance (`Brownian_Exit.thy`, `Random_Walk_Market.thy`) to re-discharge
new obligations, and would trade one substantive assumption for one substantive
plus three regularity ones. Instead the change is PURELY ADDITIVE: `Z_martingale`
is now available as a THEOREM that a user can apply, and nothing existing changed.
Confirmed by the build: all three locales carrying the assumption
(`ito_volatile_market` at line 52, `ito_stopped_market` at 321,
`ito_const_horizon_market` at 563) and both concrete instances still check.

- `cond_covariation M F X acov` — the covariation condition as a definition: for
  all `0 <= s <= u`, the conditional expectation of the increment of `X . X` over
  `F s` agrees with that of the increment of `integral trace (acov)`. Plus
  `cond_covariationD` to use it.
- **`Z_martingale_of_cond_covariation`** — concludes literally
  `martingale M F 0 (ito_Z X acov)`, i.e. VERBATIM the `Z_martingale` assumption,
  from: `sigma_finite_filtered_measure`, adaptedness of `ito_Z`, integrability of
  `X . X` and of the compensator at each horizon, and `cond_covariation`. Proof is
  `martingale_of_cond_increment` instantiated at `Sq t = X t . X t` and
  `A t = integral_{0..t} (trace o acov)`, whose difference IS `ito_Z X acov`.

So the substantive probabilistic content of `Z_martingale` is now reduced to the
paper's defining condition; what remains alongside it are only regularity
hypotheses of the same character as those the locale already had.

IMPORT NOTE: `Ito_Covariation` imports `Ito_Market` and `Sampled_Martingale`, whose
only common ancestor is the SESSION theory `Martingales.Martingale` -- so no draft
diamond, and the batch build accepts it. This is why `martingale_of_cond_increment`
was moved OUT of `Sampled_Quadratic_Variation` (which imports the draft
`Quadratic_Variation`, and would have created one) and into `Sampled_Martingale`.
It never needed `qvar` anyway.

TRAP recorded from this edit: an antiquotation `@{thm [source] foo}` in a `text`
block fails the BUILD with `Undefined fact` if `foo` lives in a theory ABOVE the
current one in import order. Moving a theorem between theories can therefore break
prose that cites its neighbours. Cite such facts as plain cartouches instead.

DONE, the simple-integral layer, in `Stochastic_Integral_Simple.thy` (green,
434 commands, 634 ms). A SIMPLE predictable integrand is one subordinate to a
partition, with the value on the interval starting at `t k` measurable for
`F (t k)`. Its integral is the finite sum `SUM k<n. H k * (X (t (Suc k)) - X (t k))`,
which IS the discrete martingale transform `mtrans` of the sampled process.

- `sq_int_martingale_of_sampled` — the bridge lemma, re-derived locally (see the
  import note below);
- `simple_itg`, `simple_itg_Suc`, **`simple_itg_eq_mtrans`** — the definition and
  its identification with `mtrans`;
- **`martingale_simple_itg`** — "the stochastic integral of a predictable
  integrand against a martingale is a martingale", in continuous time. Proved by
  interpreting `discrete_integrand` at the sampled process and invoking
  `martingale_mtrans`;
- `sq_sum_le_two`, **`simple_itg_sq_integrable`** — square-integrability of the
  integral, for a BOUNDED integrand. Boundedness is genuinely needed and is the
  standard hypothesis: the integral is a SUM of products, so squaring it produces
  cross terms that would otherwise need a fourth moment of `H` and of the
  increments. Proved by induction along the partition;
- **`ito_isometry_simple`** — the ITO ISOMETRY:
  `E[(simple_itg H X t n)^2] = E[SUM k<n. (H k * (X (t (Suc k)) - X (t k)))^2]`.
  Via `expectation_sq_qvar` applied to the integral itself, whose `qvar` is the
  sum of squared increments `(H k * dX k)^2`;
- `simple_itg_diff`, **`ito_isometry_simple_diff`** — linearity in the integrand
  and the isometry in DIFFERENCE form. This is the gateway to the `L^2` extension:
  it says `H |-> simple_itg H X t n` is an isometry, so a Cauchy sequence of simple
  integrands has a Cauchy sequence of integrals.

IMPORT NOTE, and it is a real constraint: `Stochastic_Integral_Simple` imports
`Stochastic_Integral` and `Sampled_Martingale`, whose only common ancestor is the
SESSION theory `Martingales.Martingale`. Importing `Sampled_Quadratic_Variation`
instead would have made a diamond over the DRAFT `Quadratic_Variation` (reached by
`Stochastic_Integral` via `Relative_Arbitrage_Discrete`), which breaks loading.
That is why `sq_int_martingale_of_sampled` is restated there rather than reused.

### Task 15: what is DONE, what is NOT, and what is NOT NEEDED

DONE: the discrete layer; the sampling bridge (`martingale_sampled`); quadratic
Ito and the energy identity along a partition; the conditional increment identity;
the `Z_martingale` reduction (`Ito_Covariation`); and the simple stochastic
integral with its Ito isometry.

NOT NEEDED for this paper, established rather than assumed:
- **Doob-Meyer.** The covariation is DATA -- see the verification above. There is
  nothing to decompose.
- **Ito's formula for general `C^2` functions.** Lemma 2.2 applies Ito only to the
  QUADRATIC test function; see 25e.

ALSO DONE (2026-07-27): the `L^2` CLOSURE. An earlier revision of this file called
it a substantial separate project; that was too pessimistic, because the hard step
turned out to be already in the distribution.

`L2_Limits.thy` (green, 332 commands):
- `abs_le_am_gm` — the pointwise arithmetic-geometric bound
  `|h| <= e/2 + h^2/(2e)`, valid for every `e > 0` because it rearranges to
  `0 <= (e - |h|)^2`. This is what replaces Cauchy-Schwarz, which is NOT needed.
- `integral_abs_le_of_sq`, `integrable_of_sq_integrable` — on a probability space,
  the `L^1` norm is controlled by the `L^2` norm, and `L^2` is inside `L^1`.
- **`cauchy_L2_imp_cauchy_L1`** — an `L^2`-Cauchy sequence is `L^1`-Cauchy, in
  exactly the shape the distribution's lemma wants.
- **`L2_cauchy_ae_limit`** — Riesz-Fischer: an `L^2`-Cauchy sequence has a
  subsequence converging almost everywhere, with a measurable limit.

KEY FIND that made this cheap: `HOL-Analysis.Set_Integral` line 1473 already has
**`cauchy_L1_AE_cauchy_subseq`** — `L^1`-Cauchy implies an almost-everywhere-Cauchy
subsequence — which is the entire hard half of Riesz-Fischer. Its own comment says
it is easier to use than the one in `Bochner_Integration`. So only the
`L^2`-to-`L^1` step had to be written. Measurability of the pointwise limit is
`borel_measurable_lim_metric` (Borel_Space:1676), which handles the
non-convergent points internally -- do NOT reach for `borel_measurable_lim`, which
does not apply.

REJECTED alternative, recorded so it is not retried: AFP `Lp` has
`Lp_complete : complete_N (LL p M)`, but it is phrased in a bespoke quasinorm
framework (`complete_N`, `LL p M`, `defect`) and its session depends on
`Ergodic_Theory`. Neither heap is prebuilt. The hand-rolled route above is far
cheaper and framework-free.

`Stochastic_Integral_L2.thy` (green first try, 118 commands):
- `simple_itg_integrable` — the simple integral is in `L^1`;
- **`simple_itg_L2_closure`** — the EXTENSION: if the approximating simple
  integrands are uniformly bounded and Cauchy in the integrand norm
  `E[SUM (H i - H j)^2 (dX)^2]`, then their integrals converge almost everywhere
  along a subsequence to a measurable limit. Proof: `ito_isometry_simple_diff`
  turns integrand-Cauchy into `L^2`-Cauchy for the integrals, then
  `L2_cauchy_ae_limit`.

So task 15's construction layers are all built. What a full library would still
add beyond this is the DENSITY theorem -- which general predictable processes are
approximable by simple ones -- which is a statement about the predictable
sigma-algebra rather than about the integral, and is not needed by this paper.

- For Lemma 2.2 specifically the open link is narrower than the whole `L^2` theory
  -- see 25f below, which pins it down exactly after task 15 was finished.

### 25h — PLAN for finishing #25 (2026-07-27), with statuses

Written after a full re-analysis; supersedes scattered next-step notes above.
Task #25 = Lemma 2.2 + Lemma 2.3 + Prop 2.4. Three phases, ordered by dependency.

**PHASE A — Lemma 2.2 (relative compactness).**

| step | content | status |
|---|---|---|
| A1 | fourth-moment bound along partitions, explicit remainder | **DONE, this session** — `fourth_moment_partition_bound`, constant `8 C^2`, remainder `3 SUM E[d_k^4]`; see 25f |
| A2 | mesh limit for BOUNDED martingales: remainder -> 0 | **DONE** — `remainder_tendsto_zero` + `fourth_moment_bound_bounded` = Eq. (2.7), see 25i |
| A3 | unbounded case: Eq. (2.7) for UNBOUNDED martingale laws (required — the paper's Lemma 2.2 laws are unstopped and unbounded, pp. 5-6) | **DONE (2026-07-29)**, see 25k/25l: `Conditional_UI.thy` (UI infrastructure, also feeds B2) + `Stopped_Localization.thy` (`stopped_martingale_L2`, `stopped_compensated_square`, `stopped_covariation`, `fourth_moment_L2` + Bochner corollaries). Eq. (2.7) with constant 8C² now holds for unbounded L2 martingales with deterministic start and adapted Lipschitz-rate compensator; plugs into `dyadic_bad_event_tail_mom` |
| A4 | quantitative Kolmogorov: uniform Holder TAIL bound from uniform (2.7) | **DONE (2026-07-28)**, see 25j: `Increment_Tails.thy` + `Dyadic_Chaining.thy` + `Modulus_Tails.thy` (all green, all in ROOT). Deliverables: `dyadic_bad_event_tail` (P(some dyadic increment at some level `j >= n` exceeds `2 powr (-gamma j)`) `<= 8 C^2 T q^n/(1-q)`, `q = 2 powr (-(1-4 gamma)) < 1` for `gamma < 1/4`) and `modulus_of_good_path` (on the complement, for continuous paths: ALL pairs in `[0,T]` at distance `< 1/2^n` are within `3 * 2 powr (-gamma n)/(1 - 2 powr (-gamma))`). Both threshold and probability explicit in `(C,T,gamma,n)` only — uniform over the family of laws, which is what tightness needs |
| A5 | path-space infrastructure: the path space as a Polish space, laws, weak topology | **A5a DONE (2026-07-29)**: `Path_Space.thy` (green, in ROOT; ROOT `sessions` now also lists `Standard_Borel_Spaces`) — `path_metric T := cfunspace (top_of_set {0..T}) euclidean_metric` at any `'b::polish_space`; `mcomplete_path_metric` via HOL-Analysis `Metric_space.mcomplete_cfunspace`; `separable_path_metric` via AFP Standard_Borel_Spaces `Metric_space.separable_space_cfunspace` (KEY FIND — separability was feared to need a from-scratch Stone-Weierstrass rationalization, but the AFP lemma gives it for free: target separable+complete, domain compact metrizable; the Met_TC/euclidean_metric conversion idiom is copied from Levy_Prokhorov's Alaoglu_Theorem lines 43-50); `path_metric_polish` in exactly the `Metric_space.mcomplete`/`separable_space mtopology` form that `Prokhorov_theorem_LP` consumes. **A5b DONE (2026-07-29, same file)**: `mspace_path_metricI` (restriction of a continuous function is a path) and **`compactin_path_holder_ball`** — the Holder ball `{f ∈ mspace (path_metric T). f 0 = x ∧ (∀s,t ∈ {0..T}. norm (f t − f s) ≤ c|t−s|^ga)}` is `compactin (mtopology_of (path_metric T))`. Proof: `Metric_space.compactin_sequentially` + the type-class `holder_family_subsequence` (Section_2_Compactness) transported via `cfunspace_mdist_le` and the `[simp]` bridges `continuous_map_iff_continuous` / `mbounded_iff_bounded` / `mtopology_of_euclidean`; the `obtains`-lemma is consumed as an ELIMINATION rule with `fix L and k :: "nat ⇒ nat"` (the memory-file trap about obtain-from-obtains higher-order unification struck again and this pattern fixed it). **A5c first half DONE (2026-07-29, same file)**: `Icc_rats_dense` + `le_on_Icc_of_rats` (rational density in `{0..T}`, `≤`-transfer by continuity via `continuous_le_on_closure`); `mspace_path_metric_continuous`; `path_mdist_le_iff` (sup-distance `≤ q` iff pointwise `≤ q` at RATIONAL times — `cfunspace_mdist_le` + density); **`pathify_measurable`** — `ω ↦ restrict (λt. X t ω) {0..T}` is measurable `M →ₘ borel_of (mtopology_of (path_metric T))` whenever each `X t` is measurable and paths are continuous. Route: `separable_space_def2` gives a countable dense `D`; `generated_by_countable_balls` + `borel_of_second_countable'` present the Borel algebra as `sigma` of the countable ball family; ball preimages decompose as rational unions of `{mdist ≤ q}` sets, which by `path_mdist_le_iff` are countable intersections of one-time-point constraints (`sets.countable_INT'`/`countable_UN''`; note `countable_INT''` needs `UNIV ∈ sets` — wrong lemma, use the primed ones). Plus `path_law` (the pushforward defining the members of `P_x`), `sets_path_law`, `prob_space_path_law`. **A5c DONE IN FULL (2026-07-29).** The interpolation draft landed as `Holder_Interpolation.thy` (green, 750 commands: `exists_dyadic_level`, `telescope_grid`, `holder_of_dyadic_moduli` with constant `E*2 powr g + 2*E*2^n*2 powr (-g n) * max 1 (T powr (1-g))`), and the tightness assembly is the new **`Path_Tightness.thy`** (imports Path_Space + Holder_Interpolation — the FIRST theory merging the Levy-Prokhorov and Martingales chains; PIDE loads and holds both at once, 630 commands green; batch green). Contents: `dyadic_bad_event_sets` (measurability of the bad event, mirrors the Esets argument); `holder_const g T n` (the explicit Holder constant, a function of `(g,T,n)` only, hence COMMON to every law); `holder_of_good_dyadics` (`modulus_of_good_path` applied at every level `>= n`, composed with `holder_of_dyadic_moduli`); **`path_law_holder_ball_bound`** (a path law puts mass `<= 8C^2 T q^n/(1-q)` outside the compact Holder ball; `measure_distr` + `finite_measure_mono` + `dyadic_bad_event_tail_mom`); **`tight_on_set_path_laws`** (tightness of ANY family of path laws with a common start `x` and common moment constant `C`, over a common sample type; the compact-per-`e` is chosen via `LIMSEQ_realpow_zero`); and **`path_laws_convergent_subsequence`** (the Lemma 2.2 subsequence extraction at a fixed horizon, via AFP `tight_on_set_imp_convergent_subsequence`; `metrizable_space` from `Metric_space.metrizable_space_mtopology`, mass bound from `prob_space.emeasure_space_1` — note `N (space N)` parses via the GLOBAL `[[coercion emeasure]]` of Sigma_Algebra). **The vector layer is ALSO DONE (same day):** `path_law_holder_ball_bound_vec`, `tight_on_set_path_laws_vec`, `path_laws_convergent_subsequence_vec` — same statements for `X :: real => 'a => real^'m` with PER-COORDINATE `int4`/`mom` hypotheses (which is what `fourth_moment_L2` delivers, since the repo treats coordinates via the sublocale at `%s w. X s w $ i`). Mechanism: coordinate bad events, union bound (factor `CARD('m)` in the probability), `norm_le_l1_cart` to assemble the vector Holder bound with constant `CARD('m) * holder_const g T n`, `compactin_path_holder_ball` at `'b = real^'m` (type classes all hold: `real^'m` is polish + real_normed_vector + heine_borel). Component kit: `borel_measurable_nth` (compose for coordinate measurability), `continuous_on_component` (coordinate continuity), `vector_minus_component` [simp]. Note `mkt_exit_vals` (Value_Function.thy) fixes the sample type as `('n => real => real) measure`, so the fixed-'a family shape fits `P_x` directly. **The martingale-package wiring is ALSO DONE (same day):** `Path_Tightness_Market.thy` — `path_laws_convergent_subsequence_market` restates the subsequence extraction with the stochastic hypotheses the paper's Eqs. (1.7)-(1.8) provide (per coordinate: martingale, `L2`, everywhere-continuous vector paths on `{0..}`, deterministic start, compensated square `X_l^2 - A_l` a martingale with adapted `A_l`, `A_l 0 = 0`, pathwise rate `0 <= dA_l <= C dt`), discharging `int4`/`mom` via `fourth_moment_L2_integrable`/`fourth_moment_L2_bochner` per coordinate (`continuous_on_component` for coordinate continuity, `continuous_on_subset` for the horizon restriction). Its imports (Path_Tightness + Stopped_Localization) form a DIAMOND over the draft `Increment_Moments`, so the theory is BATCH-ONLY (green first try, 1:14); do not try to load it into PIDE. REMAINING for Lemma 2.2: only A5d — the `C([0,inf))`/finite-horizon architecture decision (projective limit over `T ∈ ℕ` vs per-horizon statement) and its interaction with `val_fn`/`sufficiently_volatile_market` (note `mkt_exit_vals` fixes the sample type as `('n => real => real) measure`, so the fixed-'a family statements fit `P_x` directly) |

**PHASE B — Lemma 2.3 (compactness = A + closedness).**

| step | content | status |
|---|---|---|
| B1 | Skorokhod layer 5: coupling map on `[0,1)` + a.s. convergence | open; layers 1-4 done (`Measure_Continuity_Sets`, `Stacking_Intervals`) |
| B2 | martingale property closed under weak limits | open; via B1 + `Vitali_Convergence` (done) + uniform integrability from A1 |
| B3 | covariation constraint closed under weak limits | deterministic core **DONE (2026-07-29)**: **`closed_feasible`** (Poincare_Separation.thy, batch green) — the feasible set is CLOSED; with `feasible_bounded` it is COMPACT. Route: `feasible_iff_eigval` trades the existential `eigen_lb` for `1 <= eigval (n-k) a`; `eigval` is Lipschitz on the closed set of symmetric matrices (`eigval_lipschitz` + the PRE-EXISTING `entrysum_le_norm` at line 3546 — a fresh copy collided, "Duplicate fact declaration" broke the build once; grep before adding); kit lemmas `continuous_on_matrix_entry` (two `continuous_on_component`), `continuous_on_quadform` (double-sum expansion + `continuous_intros`), `closed_symmetric_matrices`, `closed_psd`, `closed_annihilator`, `closed_eigen_ub` (all via `closed_Collect_eq`/`closed_Collect_le` + `closed_INT`), `eigval_continuous_on_sym` (`lipschitz_onI` + `lipschitz_on_continuous_on`, C = 2m·n²). Probabilistic half (transfer along weak limits via Vitali) still open |

**PHASE C — Prop 2.4 (usc of `v` + DPP).**

| step | content | status |
|---|---|---|
| C1 | usc of `v` | behind Phase A+B |
| C2 | concatenation of laws at a stopping time | machinery available: AFP `Disintegration` (verified) |
| C3 | measurable selection | absent from Isabelle+AFP entirely; build from scratch — the largest single item; reconstruct from [LR24] |
| C0 | `ess_inf_time` calculus | **DONE** (`ess_inf_time_AE`, `_mono`, `_superadd`); extended 2026-07-29 with **`ess_inf_time_distr`** (Value_Function.thy): the essential infimum computes on either side of a pushforward (`AE_distr_iff`) — needed when Lemma 2.3 exhibits weak limits as `P_x` members and when Prop 2.4 concatenates laws |

### 25i — A2's uniform-L^2 pillar DONE (2026-07-27, second session pass)

All in `Increment_Moments.thy`, PIDE-green (2182 commands, 0 errors), batch green.

- `interval_sq_eq_dA`, `interval_sq_le` — the per-interval energy identity
  `E[d_k^2] = E[dA_k] <= C dt_k`, standalone (extracted from the second-moment
  proof so the double-sum computation can cite it per interval).
- **`weighted_interval_bound`** — `E[f^2 d_k^2] <= C dt_k E[f^2]` for ANY weight
  `f` measurable at the LEFT endpoint `F (t k)` with `f^4` integrable. The
  conditional pull-out chain from EY2d2, generalised. Taking `f` to be an earlier
  increment gives every off-diagonal term of `E[(SUM d^2)^2]`.
- `interval_pow4_le` — diagonal: for `|X| <= R` a.e. at partition points,
  `E[d_k^4] <= 4 R^2 C dt_k` (via `|d| <= 2R` and the energy identity).
- **`sum_sq_squared_bound`** — THE pillar:

    `E[(SUM_{k<n} d_k^2)^2] <= 4 R^2 C (t n - t 0) + C^2 (t n - t 0)^2`

  for EVERY partition. Proof: expand by `sum_product`, `integral_sum` twice,
  per-pair bound (`per_pair`) splitting diagonal (interval_pow4_le, padded by the
  nonnegative `C^2 dt^2`) vs off-diagonal (`weighted_interval_bound` +
  `interval_sq_le`, with a commuted second case), then `sum.distrib`,
  `sum_distrib_left`, `sum_product[symmetric]`, delta-sums, and
  `sum_lessThan_telescope`.

TRAP note: the final assembly needed explicit BRIDGE equations
(`C^2*((SUM dt)*(SUM dt)) = C^2*((t n - t 0)*(t n - t 0))` etc. via the telescope
fact) because linarith cannot substitute an equation INSIDE a product atom.

A2 IS COMPLETE (2026-07-28): all four a2-lim steps DONE, all green
(`Increment_Moments.thy`, 3600+ commands, 0 errors; batch green). The headline:

- **`remainder_tendsto_zero`** — along the uniform partitions of `[s,T]`,
  `SUM_k E[d_k^4] -> 0`, for a bounded continuous martingale with compensator
  rate at most `C`. Proof: `E[SUM d^4] <= E[W*S]` (step 1 + integral_mono),
  `<= K*E[W] + (4R^2/K)*E[S^2]` (step 2 + integral_mono_AE),
  `E[S^2] <= B` (`sum_sq_squared_bound`), `E[W] -> 0` (step 3); epsilon-argument
  with `K := (8R^2*B + r)/r`, which gives `(r/2)*K = 4R^2*B + r/2 >= 4R^2*B`
  with NO case split.
- **`fourth_moment_bound_bounded` — Eq. (2.7)**:

    `E[(X_T - X_s)^4] <= 8 C^2 (T-s)^2`

  for a bounded continuous martingale, from `fourth_moment_partition_bound`
  (which gives the bound plus `3 * remainder` for EVERY partition) and
  `LIMSEQ_le_const` on the vanishing remainder. Constant `8 C^2` against the
  paper's `66 C^2`; NO Burkholder-Davis-Gundy, NO stochastic integral anywhere.
  Hypotheses: global compensator `A` with `AE: 0 <= A_v - A_u <= C(v-u)`, the
  conditional covariation identity per pair of times, `|X| <= R` a.e. per time,
  and a.s.-continuous paths on `[s,T]`. Fourth-moment integrability is DERIVED
  (`integrable_pow4_of_bounded`), not assumed.

Earlier progress record (superseded but kept for the trap notes):

DONE:
- `upart s T m k = s + (T-s) * min k (Suc m) / Suc m` — the m-th uniform
  partition of `[s,T]`, with `Suc m` intervals (never zero, so Max over the
  increments is well defined), capped at `T` so it is total and monotone on all
  of nat, matching the partition theorems' interface. Kit: `upart_zero`,
  `upart_top`, `upart_mono`, `upart_ge_s/le_T/mem/nonneg`, `upart_diff_le`
  (mesh bound `<= (T-s)/Suc m`).
- step 1: **`sum_pow4_le_max_times_sum`** — `SUM d^4 <= Max(d^2) * SUM d^2`.
- step 2: **`prod_le_K_split`** — `W*S <= K*W + (B/K)*S^2` for
  `0 <= W <= B, 0 <= S, K > 0`; by cases `S <= K` (absorb into `K*W`) vs `S > K`
  (then `S <= S^2/K`).
- step 3: **`expectation_max_sq_tendsto_zero`** — `E[Max_k d_k^2] -> 0` along the
  uniform partitions, for a bounded process with a.s.-continuous paths on
  `[s,T]`. Pointwise: `compact_uniformly_continuous` + `reals_Archimedean2`
  (pick `Suc m > (T-s)/delta`), with `e := min 1 r` so `e^2 <= r` avoids sqrt.
  Expectations: `integral_dominated_convergence`, dominator `4R^2`. AE
  boundedness at ALL partition points of ALL partitions by two nested
  `AE_all_countable`. NO martingale structure used.

STILL OPEN — step 4, the assembly, all inputs now proved:
  `E[SUM d^4] <= E[W*S] <= K*E[W] + (4R^2/K)*E[S^2]` (steps 1-2 + integral_mono),
  `E[S^2] <= B := 4R^2 C(T-s) + C^2(T-s)^2` (`sum_sq_squared_bound`),
  `E[W] -> 0` (step 3); epsilon-argument with `K := (8R^2 B + r)/r` (so
  `(r/2)*K = 4R^2 B + r/2 >= 4R^2 B`, no case split) gives
  `SUM_k E[d_k^4] -> 0`; then `fourth_moment_partition_bound` +
  `LIMSEQ_le_const` deliver Eq. (2.7) for bounded continuous martingales:
  `E[(X_T - X_s)^4] <= 8 C^2 (T-s)^2`. Hypothesis packaging: a GLOBAL
  compensator `A` (per-partition `dA k := A(t(Suc k)) - A(t k)`), rate
  `AE: 0 <= A v - A u <= C(v-u)` for `0 <= u <= v`, and the conditional
  covariation identity per pair of times; `q4` is DERIVABLE from boundedness
  (`|X^4| <= R^4` a.e. + integrable_bound), so it drops out of the hypothesis
  list.

TRAP notes from this pass: `field_simps` on an equation with a `/ real (Suc m)`
on BOTH sides cleared denominators and produced an un-simpable polynomial blowup
— chain `diff_divide_distrib` then `right_diff_distrib` instead, never clearing
the division. And `{..<Suc m} ~= {}` is NOT closed by `simp` (use `auto`), while
membership of the k=0 element must go through `imageI` BEFORE simp can rewrite
`upart _ _ _ 0` to `s` on one side only.

### 25j — A4 DONE: tail bounds, uniform dyadic chaining, modulus tails (2026-07-28)

Three new theories, all PIDE-green and batch-green, all in ROOT.

**`Increment_Tails.thy`** (imports `Increment_Moments`):
- `fourth_moment_tail` — Markov at the 4th power: `P(l <= |f|) <= E[f^4]/l^4`.
  Uses the distribution's `integral_Markov_inequality_measure` with its vestigial
  `A : sets M` assumption instantiated at `A := space M` (via `sets.top`).
- `fourth_moment_bound_subinterval` — Eq. (2.7) on any `[u,v] <= [s,T]`
  (`continuous_on_subset` inside `eventually_elim`).
- `partition_max_tail_bound` — union bound over one uniform partition level:
  `P(exists k < Suc m. l <= |d_k|) <= 8 C^2 (T-s)^2 / (Suc m * l^4)`.
  The `1/Suc m` decay is what makes the level sum converge.

**`Dyadic_Chaining.thy`** (imports `Kolmogorov_Chentsov.Dyadic_Interval`; purely
deterministic — no measure theory):
- anchors `danchor j u = floor(2^j u)/2^j` with `danchor_self/_le/_gt/_mem`;
  `anchor_succ_cases` (successive anchors equal or one level-`Suc j` step apart,
  via `floor_double_bounds`).
- `anchor_chain` — telescoping induction: `dist (f (danchor n u)) (f u) <=
  SUM_{n<j<=m} c j` for `u` dyadic at level `m`, given per-level increment
  bounds `c j`.
- **`dyadic_chaining`** — the chaining bound: `u, v` level-`m` dyadics in
  `[0,T]`, `|u-v| <= 1/2^n`, `n <= m`, per-level bounds `c j` on ALL adjacent
  level-`j` increment pairs (`n <= j <= m`) imply
  `dist (f u) (f v) <= c n + 2 SUM_{n<j<=m} c j`. UNIFORM in the level `n` —
  this is the statement the AFP's Kolmogorov-Chentsov entry does NOT provide
  (its constants depend on the sample point through the `SOME`-defined `n_0`).
- **`dyadic_modulus_extension`** — for `f` continuous on `[0,T]`: a bound `K` on
  all same-level dyadic pairs at distance `<= 1/2^n` extends to ALL real pairs
  at distance STRICTLY below `1/2^n` (anchor approximation + `tendsto_dist`;
  the strictness absorbs the anchor error `2/2^m`).

**`Modulus_Tails.thy`** (imports `Increment_Tails` + `Dyadic_Chaining`; tranche
3, the probabilistic assembly — DONE same day):
- `dyadic_level_tail` — union bound over the level-`j` dyadic grid directly
  (NOT via `upart`; `fourth_moment_tail` + `fourth_moment_bound_subinterval` do
  the work): `P(exists k in {1..floor(2^j T)}. l <= |X(k/2^j) - X((k-1)/2^j)|)
  <= 8 C^2 T (1/2^j) / l^4`.
- `powr_level_calc`, `powr_ratio_lt_1` — the powr calculus: at `l = 2 powr
  (-gamma j)` the level bound is `8 C^2 T q^j` with `q = 2 powr (-(1-4 gamma))`,
  and `q < 1` iff `gamma < 1/4`.
- **`dyadic_bad_event_tail`** — countable union over levels `j >= n`:
  `P(exists j >= n, exists adjacent level-j pair with increment >= 2 powr
  (-gamma j)) <= 8 C^2 T q^n / (1-q)`. Via `finite_measure_subadditive_countably`
  + geometric comparison/`suminf_geometric`. The event is a countable union of
  MEASURABLE finite unions — no modulus-of-continuity measurability needed.
- `geometric_tail_sum_le` — `SUM_{n<j<=m} r^j <= r^(Suc n)/(1-r)` (reindex via
  `sum.shift_bounds_nat_ivl`, then `sum_le_suminf`).
- **`modulus_of_good_path`** — deterministic: a continuous path on `[0,T]` whose
  level-`j` dyadic increments are `<= 2 powr (-gamma j)` for ALL `j >= n`
  satisfies `|f u - f v| <= 3 * 2 powr (-gamma n) / (1 - 2 powr (-gamma))` for
  ALL `u,v in [0,T]` with `|u - v| < 1/2^n`. (Chaining at level `max m n` via
  `dyadic_interval_step_mono`, then `dyadic_modulus_extension`.)

Together: the quantitative Kolmogorov tail estimate — both the modulus threshold
and the exceptional probability explicit in `(C, T, gamma, n)` and geometrically
decaying in `n`, uniform over every law satisfying the Eq. (2.7) package. This
is the exact input for tightness in Lemma 2.2 (equicontinuity part of
Arzela-Ascoli / Prokhorov on `C([0,T])`).

**Same-day refactor after rereading the paper (pp. 5-6):** the paper's Lemma 2.2
laws are UNSTOPPED, UNBOUNDED continuous martingale laws on `C([0,inf),R^n)`
(relative compactness for weak convergence; tightness checked per `C([0,T],R^n)`
via Holder balls, alpha in (0,1/4)). Our boundedness hypothesis `|X| <= R` is
NOT in the paper. Therefore `Modulus_Tails` was refactored so the tail machinery
consumes ONLY the abstract Eq. (2.7) package:
- `dyadic_level_tail_mom`, `dyadic_bad_event_tail_mom` — hypotheses are just
  measurability, integrability of fourth powers of increments, and
  `E[(X_v - X_u)^4] <= 8 C^2 (v-u)^2` for `0 <= u <= v <= T`.
- `dyadic_level_tail`, `dyadic_bad_event_tail` (bounded-package forms) are now
  thin corollaries discharging the hypotheses via
  `fourth_moment_bound_subinterval`.
This makes A3 precise: for the paper-exact Lemma 2.2 the missing link is
Eq. (2.7) for UNBOUNDED martingales, to be obtained by LOCALIZATION: stop `X` at
the exit of a radius-`rho` ball (a bounded martingale — needs a continuous-time
stopped-martingale lemma, cf. the discrete `martingale_stopped` + sampling
bridge), apply `fourth_moment_bound_bounded` to the stopped process (its
compensator package restricts fine), and let `rho -> inf` with Fatou on
`|X^rho(v) - X^rho(u)|^4 -> |X(v) - X(u)|^4` a.s. (path continuity). The
integrability hypothesis also follows from Fatou + the uniform bound.

TRAP notes from this pass: (i) OF-composition against a fact with its own
meta-premises (`A_int`, `covA`, `bnd`) leaves RESIDUAL trivial goals
(`0<=u ==> 0<=u`) — a structured `proof (rule ...)` discharges them at `qed`
via assumption, but a one-liner `by (rule ...) m2` applies `m2` to the FIRST
goal only: use `simp_all`, or pre-instantiate the premise (`kk`) before OF.
(ii) `n * (K * ((D/n)^2) / l^4) = K*D^2/(n l^4)`-type cancellations: `field_simps`
combines fractions but cannot prove compound denominators nonzero — do numerator
arithmetic (`power2_eq_square algebra_simps`) + one explicit
`mult_divide_mult_cancel_left`/`nonzero_mult_div_cancel_right`. (iii) `let`-bound
event families get syntactically expanded, breaking `auto` on index reindexing —
use `define E where ...` for opacity, unfold `E_def` only where content matters.
(iv) higher-order `rule` applications of chaining lemmas need `[where f=f]` or
"Unification bound exceeded" warnings appear (harmless but noisy).

### 25k — A3 part (a) DONE: Conditional_UI.thy (2026-07-28)

New theory `Conditional_UI.thy` (imports `Vitali_Convergence` + `Increment_Moments`),
PIDE-green, in ROOT. Two classical facts absent from distribution+AFP:

- **`integral_abs_small_sets`** (in `finite_measure`): for integrable `f`, e>0
  there is `delta>0` with `set-integral of |f| over A <= e` whenever
  `measure A < delta`. Proof: truncate at integer levels, dominated convergence
  sends the tail `E[max 0 (|f|-N)]` below `e/2`, then `delta = e/(2(N+1))`.
- **`cond_exp_family_unif_integrable`** (in `prob_space`): for a FIXED
  integrable `Y` and any sequence `G n` of sigma-finite subalgebras,
  `unif_integrable M (%n. cond_exp M (G n) Y)`. The truncation level
  `K = E|Y|/delta + 1` is UNIFORM over the subalgebras: the exceedance set
  `A = {cond_exp (G n) |Y| > K}` lies in `sets (G n)`, so
  `cond_exp_set_integral` collapses the tail to `E[|Y|; A]` with
  `P(A) < delta` by Markov.

Also there (the consumer-facing interface for the optional-stopping rework):
- `unif_integrable_cong_AE` — UI transfers along per-index AE equality.
- **`unif_integrable_of_averaging`** (in `prob_space`): a sequence `f n` that is
  `G n`-measurable, integrable, and satisfies the SET-INTEGRAL identity
  `∫_A Y = ∫_A f n` for all `A ∈ sets (G n)` is uniformly integrable — by
  `cond_exp_charact` (AFP Martingales) such `f n` IS `cond_exp M (G n) Y` a.e.
  This matches `set_optional_sampling`'s output shape directly (with
  `G n := F (dceil n v)`-style algebras), so the rework of `optional_stopping`
  never has to construct stopped sigma-algebras.

Proof-engineering notes: `integrable_real_mult_indicator` puts the indicator on
the RIGHT of the product — `(subst mult.commute)` first; `expectation_cond_exp`
(Increment_Moments) needs `space M ∈ sets G` (get it from `sets.top` + the
subalgebra space equation); the `⋀e`-form after `intro conjI allI impI` on
`unif_integrable_def` is NOT the `∀e>0`-form — fix/assume directly; consuming an
`obtains`-lemma with a `⋀n`-quantified clause via `from ... obtain ... .` can
fail to unify — unfold the definition and `obtain` the `∀`-form with blast.

**MAJOR SIMPLIFICATION discovered right after (2026-07-28): no optional-stopping
surgery is needed at all.** The repo's `Doob_Inequality.thy` (phase 12/13 era,
imported by Optional_Sampling) contains locale `horizon_sq_int_martingale`
(martingale + L2 at each time + prob space + horizon `u > 0`) whose section "An
integrable bound for the running maximum" delivers exactly the missing
dominating function: `Dsup` with
- `Dsup_dominates`: continuous paths ==> `AE w. ∀s∈[0,u]. |Y s w| <= Dsup w`
  — VERBATIM the `dom` hypothesis of `optional_stopping`;
- `Dsup_integrable` — verbatim `D_int`;
- `Dsup_sq_integrable` — `E[Dsup^2] < inf` (via `gsup_L2`, Doob L2).

Revised A3 execution (all bricks exist, pure wiring):
(c') X_i is L2 (the covariation package presupposes integrable squares), paths
continuous, tau_rho := `etime` of `cball 0 rho` is a stopping time
(`etime_stopping_time`); interpret `horizon_sq_int_martingale` per horizon,
discharge `optional_stopping` with `D := Dsup` ==> the stopped coordinate
`X_i^rho` is a martingale, and `|X_i^rho| <= max rho |x_i|` by
`etime_stays_in_cball`.
(c'') Z := X·X − A is a martingale (Z_martingale/`cond_covariation`);
`|Z s| <= Dsup^2 + C u` on `[0,u]`, integrable by `Dsup_sq_integrable` ==> same
theorem stops Z ==> `Z^rho` martingale ==> covariation package for `X^rho` with
compensator `A^rho = A(· ∧ tau_rho)` (rate <= C preserved).
(d) `fourth_moment_bound_bounded` applies to `X^rho`.
(e) rho → inf: tau_rho → inf a.s. (continuous paths are locally bounded), a.s.
convergence of increments, Fatou gives Eq. (2.7) + integrability for UNBOUNDED
X; feed `dyadic_bad_event_tail_mom`.

`Conditional_UI.thy` stays: `unif_integrable_of_averaging` and
`cond_exp_family_unif_integrable` are the UI inputs that B2 (martingale property
closed under weak limits, Lemma 2.3) needs anyway.

### 25l — A3 (c') DONE: Stopped_Localization.thy (2026-07-28)

New theory `Stopped_Localization.thy` (imports `Stopped_Adaptedness` +
`Increment_Moments`), PIDE-green (85 commands, first try), in ROOT.

- **`stopped_martingale_L2`**: for a prob space, an `L2` martingale `X` (each
  `X s` square-integrable) with everywhere-continuous paths on `{0..}`, and any
  stopping time `tau` (nonneg, `{tau <= s} ∈ sets (F s)`):
  `martingale M F 0 (λv ω. X (min v (tau ω)) ω)` — NO domination hypothesis.
  Proof: per horizon `u`, interpret `horizon_sq_int_martingale` and package its
  `Dsup` via `SOME` into the `D` that `optional_stopping` wants
  (`Dsup_dominates` + `Dsup_integrable`); `stopped_adapted_of_cont` gives the
  adaptedness hypothesis, `martingale.axioms(2)` extracts `adapted_process`.

Also DONE in the same theory (2026-07-28/29, all green, batch-green):
- **`stopped_compensated_square`** (c''): `Z = X² − A` stopped at any stopping
  time is a martingale. `Z` is generally NOT `L2`, so the dominator is built by
  hand: `|Z s| <= Dsup² + C u` on `[0,u]`, integrable by `Dsup_sq_integrable`.
  Hypotheses: the pathwise (everywhere-on-`space M`) rate bound `A_rate`,
  `A 0 = 0`, `C >= 0`, plus the `stopped_martingale_L2` package for `X`.
- `rate_continuous_on` — a nonneg-Lipschitz rate bound gives continuity on
  `{0..}` (via `lipschitz_onI` + `lipschitz_on_continuous_on`).
- **`stopped_covariation`**: the conditional covariation identity transfers to
  the stopped process: `E[(X^tau_v − X^tau_u)² | F_u] = E[A^tau_v − A^tau_u | F_u]`
  a.e. Proof: `cond_exp_increment_sq` (conditional variance identity, needs
  square-integrability of `X^tau_s` — obtained by dominating with `Dsup` at
  horizon `s+1`), the martingale property of the stopped `Z`, `cond_exp_diff`,
  and `cond_exp_F_meas` on the ADAPTED stopped compensator (adaptedness of
  `A^tau` via `stopped_adapted_of_cont`, continuity of `A`-paths from the rate).
  Extra hypothesis vs (c''): `adapted_process M F 0 A`.

**A3 COMPLETE (2026-07-29).** Same theory, all green (1219 commands), plus:
- `etime_eq_T_of_no_hit` — no visit to the exit set on `[0,T]` means the capped
  exit time equals the horizon.
- **`fourth_moment_L2`** (the A3 deliverable): for a prob space, an `L2`
  martingale `X` with everywhere-continuous paths, deterministic start
  `X 0 = x0`, compensated square `X² − A` a martingale with ADAPTED `A`,
  `A 0 = 0`, pathwise rate `0 <= dA <= C dt`:
  `∫⁺ (X_v − X_u)^4 <= ennreal (8 C² (v−u)²)` for all `0 <= u <= v` —
  NO boundedness. Proof exactly as planned: radii `r n = |x0| + n + 1`,
  `tau n := etime v {y. r n <= norm y} X` (stopping time via
  `cont_adapted_process.etime_stopping_time`; NOTE Exit_Time.thy was missing
  from the import chain — Stopped_Localization now imports it),
  `|X^tau_s| <= r n` via `etime_stays_in_cball`, `fourth_moment_bound_bounded`
  on each stopped process (martingale/rate/covA hypotheses from
  `stopped_martingale_L2` + `stopped_covariation`), and Fatou: each continuous
  path is bounded on `[0,v]`, so `tau n = v` eventually and the stopped
  increments are EVENTUALLY EQUAL to the plain ones.
- `fourth_moment_L2_integrable`, `fourth_moment_L2_bochner` — the Bochner
  forms, ready to discharge `int4`/`mom` of `dyadic_bad_event_tail_mom`
  (Modulus_Tails). **The full quantitative Kolmogorov tail chain for the
  paper's Lemma 2.2 (UNBOUNDED laws) is now closed end-to-end**, modulo the
  wiring of the compensated-square hypothesis to `cond_covariation`
  (Z_martingale reduction, Ito_Covariation.thy) and the per-coordinate/vector
  bookkeeping at the P_x level.

Traps this pass: (i) `fix ω u' v' :: real` types ALL THREE as real — write
`fix ω and u' v' :: real`; (ii) applying `etime_stays_in_cball` by `rule` AFTER
`unfolding tau_def` in the goal invites higher-order unification garbage
(`X := (λa b. b)`) — prepare every premise as a named fact (incl. `sle` in
un-unfolded form) and give one fully-OF'd rule application; (iii) `¦a − b¦ <=
2r` from `¦a¦,¦b¦ <= r` needs `abs_triangle_ineq4` before linarith; (iv) a
`have` between the last `also` and `finally` resets `this` and breaks the
calculation — put auxiliary facts before the calc.

**TRAP (severe, cost a machine crash + hours):** a `commands_still_running_
possibly_nonterminating` entry with `timing_ms 0` whose goal display shows
"No subgoals!" is NOT stale bookkeeping — it was a genuinely DIVERGING `by auto`
(the `Esets` closing step in `Modulus_Tails`, fine interactively only because
PIDE hadn't scheduled it; in batch it spun at 800% CPU for 20+ minutes).
Treat that flag as a STOP condition ALWAYS: replace the proof, never dismiss the
flag. The fix (by the human user): `ultimately show ?thesis by (metis (lifting)
countable_Un_Int(1))` in place of `by auto`. Also: never run two `isabelle
build`s concurrently, and don't run a batch build while PIDE is doing a
first-time load of a heavy import chain — the combination OOM-crashed the host.

### 25m — A5d analysis (2026-07-29): the architecture RESOLUTION, recorded before building

Written after A5c + vector layer + market adapter all landed green. The question:
Lemma 2.2's statement lives on `C([0,inf), R^n)`; everything built is per-horizon
`C({0..T})`. Three findings that fix the plan:

1. **Do NOT build the metric space `C([0,inf))`** (sum of scaled sup-metrics).
   Nothing downstream needs the topology as such; what Lemma 2.3 and Prop 2.4
   consume is (i) a subsequence converging weakly AT EVERY HORIZON and (ii) a
   LIMIT LAW on the full-time sample type. (i) is a DIAGONAL argument over
   integer horizons `m ∈ ℕ` on top of `path_laws_convergent_subsequence_market`
   — note its hypotheses are horizon-uniform (contX on `{0..}`, rate for all
   `u <= v`), so one package serves every horizon. (ii) is the
   **Daniell-Kolmogorov projective limit, which the distribution ALREADY HAS:
   `HOL-Probability.Projective_Limit`** (polish-valued projective families) —
   assemble the limit measure on the function space from the consistent family
   of per-horizon limit laws. Consistency of the family = the restriction map
   `C({0..m'}) -> C({0..m})` is continuous and intertwines `path_law M X m'`
   with `path_law M X m` (a small lemma to add to Path_Space).
2. **The P_x sample type is `('n => real => real) measure`** (`mkt_exit_vals`,
   Value_Function.thy) — coordinate-then-time, full time line, NO topology in
   the type. So the limit object Lemma 2.3 must produce is a measure on that
   function space carrying (AE) continuous paths — exactly what the projective
   limit + per-horizon path-space supports give. The `real ⇒ real^'n` vs
   `'n ⇒ real ⇒ real` currying mismatch is a measurable-isomorphism layer to
   write once.
3. **The market adapter's hypotheses match `sufficiently_volatile_market`
   up to two known deltas** (Relative_Arbitrage_Stochastic.thy:93): (a) the
   locale's start/continuity/rate hypotheses are AE, the adapter's are
   everywhere — bridge by restricting to the full-measure set (or the
   `AE`-variant of the adapter, to be added when needed); (b) the locale's
   eigenvalue/trace bounds hold only up to the stopping time `tau` — Lemma 2.2
   applies to the laws STOPPED at `tau` (that is the paper's reading, pp. 5-6),
   and the stopped process keeps the package by `stopped_martingale_L2` /
   `stopped_compensated_square` (Stopped_Localization). Per-coordinate
   compensator is `A_l = integral of (acov)_ll`, rate `<= L` by
   `feasible_diag_bound` — better than the trace rate `n*L`.

ORDER OF WORK for finishing Lemma 2.2 end-to-end: (i) restriction-map
consistency lemma (Path_Space); (ii) diagonal extraction over `m ∈ ℕ`
(new, on top of `path_laws_convergent_subsequence_market`); (iii) projective
limit assembly via `HOL-Probability.Projective_Limit`; (iv) the currying
isomorphism to the `P_x` sample type; (v) the AE-vs-everywhere and stopping
bridges of finding 3. Steps (i), (ii), (v) are routine; (iii)-(iv) are the
substantial ones.

**Step (iii), first half DONE (2026-07-29, second /goal):** two new results.
(1) **`weak_conv_on_pushforward`** (Path_Space.thy, now 1161 commands) — the
CONTINUOUS-MAPPING THEOREM for weak convergence, absent from the AFP's
Levy-Prokhorov development: a `continuous_map X Y r` pushes
`weak_conv_on Ni N F X` to the distr's on `borel_of Y`. Proof through
`weak_conv_on_def` (an IFF-lemma — `weak_conv_on` is an abbreviation for
`limitin (weak_conv_topology X)`, so the lemma also unfolds goals stated in
limitin form): test functions compose (`continuous_map_compose`, bound via
`continuous_map_image_subset_topspace`), integrals transfer by
`integral_distr` (measurability from `continuous_map_measurable` +
`borel_of_euclidean`, moved between measures by `measurable_cong_sets`), and
the eventual side conditions ride along by `eventually_mono`/`tendsto_cong`.
(2) **`path_laws_diagonal_consistent`** (Path_Tightness.thy, now 1428
commands) — the diagonal limits form a PROJECTIVE FAMILY:
`distr (N m') _ (restrict to {0..m}) = N m` for `m <= m'`. The `N` is
extracted from the diagonal theorem by `SOME`+`someI_ex`; consistency =
pushforward along the restriction map (continuous by
`Lipschitz_restrict_path_metric`) + `path_law_restrict` to identify the
pushed sequence with the horizon-`m` laws + uniqueness of weak limits
(`metrizable_weak_conv_topology` -> `metrizable_imp_Hausdorff_space` ->
`limitin_Hausdorff_unique` with `trivial_limit_sequentially`).
TRAP note: `obtain a where "strict_mono a" and "∀m. ∃Nm. <big conj>" using
<∃-fact> by blast` DIVERGES (flagged still-running at 5 ms — the recorded
blast-on-big-existential trap in a new guise); the search-free pattern
(`obtain ... "A ∧ B" by (rule exE)` + `conjunct1/2`) fixes it.
REMAINING in step (iii): assemble ONE measure on the full-time function space
from the consistent family via `HOL-Probability.Projective_Limit`
(finite-dimensional marginals of `N m` under evaluation maps, consistency
from THIS theorem), together with step (iv)'s currying isomorphism.

**ALSO DONE toward (iii)/(v) (same second-/goal session), in Path_Space.thy
(now 1473 commands, green; batch green):**
- `Lipschitz_path_eval` / **`continuous_map_path_eval`** — evaluation at
  `t ∈ {0..T}` is 1-Lipschitz on the path space (via `path_mdist_le_iff_all`
  at `q := mdist f g`), hence continuous into `euclidean`
  (`mtopology_of_euclidean` [simp] closes the target conversion). This is
  what makes coordinate moments CONTINUOUS test functions on path space, and
  will also give the marginal maps of the projective family.
- **`weak_conv_on_nn_integral_le`** — the FATOU step for weak limits: a
  uniform bound `∫⁺ f dNi <= B` on a NONNEGATIVE CONTINUOUS (possibly
  unbounded) `f` passes to the weak limit. Proof by truncation
  `fK K = min f K`: `continuous_map_real_min` keeps continuity, bounded so
  the weak-convergence integrals converge (`tendsto_upperbound` +
  `eventually_sequentially` for the eventual side conditions), and
  `nn_integral_monotone_convergence_SUP` + `LIMSEQ_SUP`/`tendsto_unique`
  recover the untruncated bound. With `continuous_map_path_eval` this
  transfers the Eq. (2.7) package to the limit laws `N m` — the input for
  running the modulus machinery ON THE LIMIT (continuity of its paths).
  TRAP notes: (i) `using sN sets_eq_imp_space_eq space_borel_of by blast`
  DIVERGES (flagged at 0 ms) — use
  `sets_eq_imp_space_eq[OF sN]` + `simp add: space_borel_of`; (ii) `auto`
  does NOT apply `AE_I2` even with `intro:` (duplicate-unsafe-intro warning)
  — split as `by (rule AE_I2) (auto ...)`; (iii)
  `nn_integral_monotone_convergence_SUP[symmetric]` cannot apply by `rule`
  when the goal's RHS is not literally `∫⁺ (SUP ...)` — rewrite pointwise
  with `nn_integral_cong` first; (iv) a bare `end` as MCP-edit `old_text`
  matches inside `tendsto` — anchor on its own line range.

**Step (ii) ALSO DONE (2026-07-29, same session):** `path_laws_diagonal_subsequence`
(Path_Tightness.thy, now 1288 commands, green first try): from the
horizon-uniform per-coordinate moment package (`int4`/`mom` with NO horizon cap,
`cont` on `{0..}`), ONE strict-mono subsequence along which the path laws
converge weakly at EVERY integer horizon simultaneously. Built on HOL-Library
`Diagonal_Subsequence` (locale `subseqs` — reachable through
HOL-Probability, no new session import): `Q m s := ∃N. ... weak_conv_on
(laws-at-horizon-m ∘ s) N`; `ex_subseq` is the per-horizon extraction applied
to the reindexed family (reindexing is free since the hypotheses are
index-uniform); subsequence-stability is `limitin_subsequence` (weak_conv_on
IS a limitin, so no unfolding needed); `diagseq_holds` gives convergence of
the `Suc m`-tail of the diagonal, and `limitin_sequentially_offset_rev`
(after an `add.commute` massage of `(+) (Suc m)`) removes the tail shift.
NOTE: the limit measures N are per-horizon and quantified INSIDE the ∀m —
their projective consistency (that `distr` of `N (Suc m)` under restriction
is `N m`, via `path_law_restrict` + continuity of the restriction map +
uniqueness of weak limits on a metrizable space) is part of step (iii).

**Step (i) DONE (2026-07-29, same session):** appended to `Path_Space.thy`
(now 1019 commands, PIDE-green, batch-green): `path_mdist_le_iff_all` (the
all-reals form of the sup-distance iff, extracted from `path_mdist_le_iff`'s
internal `iff1`); `restrict_mspace_path_metric`;
`Lipschitz_restrict_path_metric` (the restriction map `C({0..m'}) -> C({0..m})`
is 1-Lipschitz — via HOL-Analysis `Lipschitz_continuous_map_def`, and note
`Lipschitz_continuous_imp_continuous_map` + Standard_Borel_Spaces'
`continuous_map_measurable` turn this into Borel measurability with no work:
`restrict_measurable_path_borel`); and **`path_law_restrict`** — the
consistency identity `distr (path_law M X m') _ (restrict-to-{0..m})
= path_law M X m`, by `distr_distr` + the restrict-restrict collapse.
All green first try in the scratch, then landed.

### 25f — Lemma 2.2 after task 15: exactly one link left, and why

`Increment_Moments.thy` (green first try, 196 commands) supplies the FIRST analytic
link of Lemma 2.2:

- `martingale_expectation_eq` — a martingale has constant expectation, via
  `martingale.set_integral_eq` at `A = space M` plus `set_integral_space`;
- `expectation_increment_sq` — the energy identity at a TWO-POINT partition:
  `E[(X u - X s)^2] = E[(X u)^2] - E[(X s)^2]`;
- **`increment_second_moment_bound`** — `E[(X u - X s)^2] <= C (u - s)` whenever the
  compensator of the square grows at rate at most `C`. For the paper's admissible
  family that hypothesis IS `trace (acov) <= C`, since the compensator there is
  `integral (trace o acov)`. No stochastic integral is used.

Also added, in `Stochastic_Integral_Simple.thy`:

- **`ito_isometry_process`** — the isometry in PROCESS form: the compensator of the
  square of the integral is `SUM H^2 (dX)^2`. This is
  `<integral H dX> = integral H^2 d<X>` for a simple integrand.

STATE OF LEMMA 2.2's CHAIN (updated 2026-07-27 — the gap is now A2, not the
quadratic-variation bound):

| link | status |
| --- | --- |
| `E[(X u - X s)^2] <= C (u-s)` | done, `increment_second_moment_bound`; localised form `second_moment_partition_bound` |
| **Eq. (2.7) with explicit remainder** | **DONE — `fourth_moment_partition_bound`**: `E[(X t - X s)^4] <= 8 C^2 (t-s)^2 + 3 SUM_k E[d_k^4]` along ANY partition |
| remainder `SUM E[d_k^4] -> 0` in the mesh limit | THE remaining gap (plan step A2) |
| Kolmogorov's criterion | available, AFP `Kolmogorov_Chentsov` (but see A4: tail-bound form needed) |
| Arzela-Ascoli step | done, `holder_family_subsequence` |
| Prokhorov | available, AFP `Levy_Prokhorov_Metric` |

HOW `fourth_moment_partition_bound` WAS PROVED (Increment_Moments.thy, ~560 new
lines, all green; NO BDG, NO stochastic integral): expand `(Y+d)^4` along the
partition. Per step, `E[Y^3 d] = 0` (pull-out `cond_exp_measurable_mult(2)` +
`cond_exp_diff_eq_zero`); `E[Y^2 d^2] = E[Y^2 dA] <= C dt E[Y^2] <= C^2 dt (t_k-s)`
(pull-out twice, the covariation hypothesis in the middle, then the second-moment
bound); `4 E[Y d^3] <= 2 E[Y^2 d^2] + 2 E[d^4]` (pointwise `4yd^3 <= 2y^2d^2+2d^4`
from the two-square bound). Total per step: `8 C^2 dt (t_k-s) + 3 E[d^4]`; sum and
`ab <= b^2`. The paper's route via BDG gives 66 C^2; this gives 8 C^2.

Supporting lemmas worth reusing: `expectation_cond_exp` (E[cond_exp f] = E[f], via
`cond_exp_set_integral` at `space M` — note `integrable_cond_exp` and
`borel_measurable_cond_exp'` live at TOP LEVEL and INSIDE `sigma_finite_subalgebra`
respectively, a trap); the pointwise kit (`two_abs_prod_le_squares`,
`prod_sq_le_half_pow4`, `pow4_diff_le`, `abs_cube_prod_le_pow4`,
`four_prod_cube_le`, `pow4_binomial` — all via `algebra` + `linarith`, no
nlinarith); the L^4-integrability kit (`integrable_pow4_diff`,
`integrable_sq_of_pow4`, `integrable_prod_sq_sq`, `integrable_cube_prod`,
`integrable_prod_cube`).

Fourth-moment integrability of `X` is a HYPOTHESIS, discharged in the intended
application by localisation: up to the exit time paths live in compact `K`
(`X_in_K` in `ito_volatile_market`), so all moments exist there.

WHY THE REMAINING GAP RESISTS THE PARTITION ROUTE, and what was proved about it.

The decomposition is now an Isabelle theorem, **`compensated_square_decomposition`**
(`Stochastic_Integral_Simple.thy`, pure algebra, no hypotheses on the processes):
along ANY partition, with `Y k = X (t k) - X (t 0)`,

    `Y n^2 - (A (t n) - A (t 0))
       = simple_itg (2 Y) X t n + SUM k<n. ((dX k)^2 - (dA k))`

EXACTLY -- no limit. So the compensated square is a simple stochastic integral PLUS
the accumulated discrepancy between squared increments of `X` and increments of the
compensator. That splits the remaining work cleanly:

- FIRST term: a simple integral. The isometry applies (`ito_isometry_process`), and
  its contribution is controlled using `increment_second_moment_bound`. Concretely
  `E[(2 Y_k dX_k)^2] = 4 E[Y_k^2 dA_k] <= 4 C dt_k E[Y_k^2] <= 4 C^2 dt_k (t_k - s)`,
  which sums to at most `4 C^2 (t-s)^2` for ANY partition. Reachable.
- SECOND term: the discrepancy. Its second moment involves `E[((dX)^2 - dA)^2]`,
  i.e. a FOURTH moment of the increments -- which is exactly Eq. (2.7), the thing
  being proved. So no fixed-partition argument can close the gap; the term vanishes
  only in the mesh limit, and that is precisely where the fourth-moment control has
  to come from.

CORRECTION to 25e, which was too optimistic. 25e recorded that Lemma 2.2 needs Ito
only for the quadratic test function. That is right about `Z_martingale` (which IS
just the covariation hypothesis, see the verification above) but WRONG as a claim
about Eq. (2.7): deriving (2.7) needs the continuous-time representation
`Z = 2 integral (X - X_s) dX`, i.e. the mesh-refinement limit of the simple
integral. Equivalently one may apply Ito to `x^4` directly and get
`E[Y_t^4] = 6 E[integral Y^2 d<X>] <= 3 C^2 (t-s)^2`; either way a genuine
continuous-time limit is required. It is NOT more `L^2` theory and NOT Doob-Meyer.
That mesh limit is the single remaining piece of continuous-time Ito.

Superseded plan items (the mesh-refinement limit described in an earlier revision
of this file):
(4) L^2 closure of the simple integrands; (5) quadratic variation of a continuous
martingale (Doob-Meyer); (6) Ito's formula for general C^2 functions. Layer (6) is
what discharges `Z_martingale` and unblocks Burkholder-Davis-Gundy, hence
Lemma 2.2.

## Dependency graph (read this before planning any parallel work)

An earlier version of this file said tasks 25 (Section 2) and 26 (Section 4)
"depend only on ell_op / feasible ... so they cannot collide" and could be run in
parallel with the eigenvalue work. That was WRONG about 26, and the error cost
real time. The actual graph:

```
  23 Eigenvalues ─┬─ 29 Eigenvalue_Continuity ── 30 Threshold_Chain
                  │        │
                  │        └── 32 Courant-Fischer ── 31 Eq.(3.5) ─┐
                  │                                               │
                  └───────────────────────────────────────────────┴─ 24 Lemma 3.1
                                                                        │
                                                                        ▼
   25 §2 (compactness, DPP) ─────┐                                  26 §4
        │                        │                                      │
        ▼                        │                                      │
   27 §5 Props 5.1, 5.2 ─────────┼──────────────────────────────────────┤
                                 │                                      │
   27 Lem 5.3 (done, indep.)     │                                      │
                                 ▼                                      ▼
                                 └──────────── 28 Theorem 1.1 ◄─────────┘

   15 stochastic integration — independent of all of the above
```

Why 26 needs 24: Theorem 4.2 reaches its contradiction through Eq. (4.3),
`F(p_eps, M_eps) >= F(p_eps, N_eps)`, and to pass from that to the limit it uses
Lemma 3.1's clause `F_* = F^* = F` off the origin. Until that clause existed,
Section 4 could not be started at all.

Why 27's Props 5.1/5.2 need 25: both go through Prop 2.4's dynamic programming
principle. Lemma 5.3 is the exception — its geometric core is deterministic and
is already proved.

CONSEQUENCE FOR PLANNING. There are exactly TWO independent lines of work left,
not four:

1. `25 -> 27 (Props 5.1, 5.2)` — the probabilistic line. This is the long pole:
   weak-topology compactness of martingale-law sets plus a DPP needing
   measurable selection. Start with the deterministic prerequisites listed under
   task 25 (the off-diagonal bound is a small, self-contained first step).
2. `26 -> ` — Section 4, now unblocked and started.

Task 28 (Theorem 1.1) is the join of both and cannot precede them. Task 15 is
orthogonal and can be picked up at any time.

## Mathematical insights worth not rediscovering

These are the non-obvious facts that made the hard parts tractable. Each was
found the slow way.

- **`F` cannot see the antisymmetric part of `M`** (`ell_op_sym_part`). Every
  feasible `a` is symmetric, and the trace pairing against a symmetric `a` cannot
  distinguish `M` from `M^T`. This is what lets results assuming
  `transpose M = M` be applied to the arbitrary, non-symmetric matrices that
  appear in a ball around a symmetric one — without it the envelope arguments do
  not get off the ground.
- **The correction coefficient of `M_p` does not depend on `p`.** In
  `M_p = (I - pp'/|p|^2) M (I - pp'/|p|^2) + min(lambda_(n)(M), 0) pp'/|p|^2`
  the scalar `min(lambda_(n)(M), 0)` is a function of `M` alone. So the only
  `p`-dependence of `M_p` is through `rank1proj p`. Combined with the previous
  point, the `p`-variation and the `M`-variation SEPARATE, and no product-topology
  reasoning is needed anywhere — the two are handled by
  `ell_op_lipschitz_in_p` and `ell_op_M_gap` independently and then added.
- **`rank1proj` depends only on the LINE through `p`** (`rank1proj_scaleR`,
  `Mp_scaleR`, `ell_op_scaleR_dir`). Hence the paper's sequence `(q_1/m, M)` used
  for the lower bound in Eq. (3.6) is CONSTANT in `m`, and no limit has to be
  computed — only `p^m -> 0` matters.
- **The Lipschitz constant for `rank1proj` is `4/|p|`**, which blows up at the
  origin (`norm_rank1proj_diff_le`). That is not a defect of the estimate: it is
  exactly the failure of continuity at `p = 0` that makes Eq. (3.6) a genuinely
  different formula there. A bound uniform near `0` would have been a red flag.
- **Poincare separation is an EQUALITY when `p` is an eigenvector.** The paper
  only needs the inequality `lambda_(i)(M_p) >= lambda_(i+1)(M)`
  (`poincare_separation`), but at `p = q_1` a top eigenvector the shift is exact
  (`eigval_Mp_top_eigenvector`), which is why evaluating there gives the matching
  bound for Eq. (3.6).
- **Only ONE feasible witness is needed for a lower bound on `F`**, because
  `ell_op` is an infimum. `bracket_attained` exhibits it: weight `L` on the
  positive eigendirections, `1` on a top-`m` threshold set chosen inside
  `B - {q}`. Choosing the threshold set away from `q = p/|p|` is what makes
  `a *v p = 0` hold, and it is possible precisely because `m = n-k <= n-1` when
  `k >= 1`.
- **Section 2 does have deterministic content.** Lemma 2.2's hypothesis is "S
  bounded", which for the paper's `S` is linear algebra, not probability. An
  earlier version of this file asserted the opposite; see task 25.
- **`eigen_lb a m <-> 1 <= eigval m a`** converts an existential over subspaces
  into a condition on a Lipschitz function of `a`, which is how Lemma 2.3's
  closedness requirement should be attacked.
- **A rank obstruction underlies Lemma 5.3.** A covariance degenerate on a
  subspace `W` cannot satisfy `eigen_lb a m` unless `m + dim W <= n`
  (`eigen_lb_dim_obstruction`). On a face `F_x` of a convex `K` this forces
  `dim F_x >= n-k`; contrapositively `dim F_x < n-k` leaves no admissible
  covariance at all, which is the `v(x) = 0` side of the lemma.

## Standard workflow (PIDE MCP) — READ FIRST

Source: `~/isabelle-pide-mcp/.claude/skills/{pide-mcp,isabelle-proof-development,isabelle-formalization}/SKILL.md`.
These are binding. RE-READ THEM AT THE START OF EVERY SESSION, not just once —
they were re-read on 2026-07-26 and again on 2026-07-27, and each re-read caught
a rule being violated in the work then in progress.

**The rule most expensive to ignore, confirmed the hard way on 2026-07-27:**
`get_state` reporting `commands_still_running_possibly_nonterminating` MEANS IT,
even when the same entry shows `timing_ms: 1` and `goal: No subgoals!`. A
`by blast` in `slab_UN` was flagged exactly that way; I judged it a rendering
artifact and ran the batch build, which then ran past 600 s instead of its normal
37 s. Replacing the `blast` with `by (rule UN_I[OF UNIV_I])` made the flag
disappear and the build return to 37 s. So: a nonzero
`commands_still_running_possibly_nonterminating` is a STOP condition — restructure
the proof before building, never build "to check". The skills say this in two
places ("suspect a loop - restructure rather than wait"); it is not advisory.

To stop a runaway build, use `TaskStop` on the background task id. Do NOT
`pkill -f poly`: the two long-lived `poly` processes are the PIDE MCP server
itself, and killing them ends the session's Isabelle state. Several were violated repeatedly earlier in this development,
each time with a cost recorded under "Environment and proof traps"; the entries
below say which.

**Editing.**
- NEVER edit a `.thy` file outside MCP — not with shell, python, or the plain
  Edit tool. PIDE then holds a stale buffer and reports errors the batch build
  does not. This happened FOUR times here. Reading via `grep` for exploration of
  UNLOADED theories (e.g. the AFP) is fine.
- If PIDE and disk disagree, re-`read` the affected file to resynchronise.
- `edit` needs `old_text` in PIDE's UNICODE rendering, not the on-disk
  `\<open>` escapes.
- Add material INCREMENTALLY — a few definitions/lemmas at a time — and call
  `get_state` after each edit. Do not batch several edits then check.

**Checking.**
- `get_state` after EVERY edit. Clean means `commands_bad = 0` AND
  `errors = 0` AND `commands_failed = 0`.
- `sorry` is reported as `commands_bad`, NOT as an error. So PIDE already
  audits for `sorry`; the `grep -cw` check is a backstop, not the primary.
- Restrict with `start_line` / `end_line`. Dumping whole-theory state on a
  3000-line file overflows the tool output limit.
- If commands run > ~30 s, suspect a loop and RESTRUCTURE rather than wait.
  Proof methods normally finish in < 5 s.
- `get_progress` for a global view / when the server seems stuck.

**Finding things — do this INSTEAD of grepping for lemma names.**
- `find_theorems` / `find_consts` search all transitively imported theories and
  are very cheap. Every invented lemma name in this development
  (`matrix_vector_mult_diff_rdistrib`, `norm_le_l1_cart` misapplied to matrices,
  `card_UNIV_pos`, `scaleR_right_commute`, ...) would have been caught by one
  `find_theorems` call. Patterns need `?x` or `_`, not free variables.
- `find_entities` for defined entities; `print_facts` for the current context.
- `list_session_directories` to see what libraries are available, then import
  session-qualified. Grep ROOT files for the qualifiers.
- Only IMPORTED theories are searchable; grep the AFP for the rest.

**Closing goals — do this INSTEAD of guessing.**
- Default order: one-shot guess → `try0` (< 5 s) → `sledgehammer` (< 30 s, poll
  at 5/10/... s). Do not hand-write `metis`/`rule` invocations you could not
  one-shot; sledgehammer finds them in seconds.
- Prefer `simp`/`auto` over explicit `metis`/`rule`. Prefer the fastest, simplest
  reconstruction sledgehammer offers (`auto` > `fastforce` > `metis` > `smt`).
- When automation is brittle, switch to structured Isar with intermediate steps.

**Developing a nontrivial proof.**
1. State the theorem with `sorry`.
2. Write the skeleton with `sorry`s for the larger gaps, plus comments.
3. Fill gaps one at a time, `get_state` after each.
- `create_scratch` for experiments and alternatives (same imports as the target
  theory); copy successful proofs back. Do not import scratch theories.
- Prefer adding an intermediate named lemma over getting stuck inside a big one.

**Before defining or proving anything**, look for it in the distribution and the
AFP first. `https://search.isabelle.in.tum.de` also works.

## Environment and proof traps

Hard-won; each cost at least one debugging round.

### Added this session

- **`unfolding thm1 thm2` applies all equations JOINTLY (innermost redexes
  first), NOT sequentially.** A rule that rewrites a subterm of another rule's
  LHS wins regardless of list order: in Path_Tightness, `unfolding spN pl` let
  `pl : path_law M X T = distr ...` fire inside `spN`'s redex
  `space (path_law M X T)` and spN never applied. Chain separate `unfolding`
  steps, or close with `simp` (here `space_distr` is simp).
- **`intro rule facts` cannot instantiate variables that occur only in the
  rule's PREMISES.** Applying `tight_on_set_path_laws` by `intro` left `?x`/`?C`
  schematic (they do not occur in the conclusion) and the `start`/`mom`
  obligations then failed to finish. Pin them: `[where x = x and C = C]`.
- **A `text` block placed BEFORE the `theory` header must not use antiquotations.**
  There is no theory context yet, so `@{term "t :: nat => real"}` fails with
  `Undefined type name: "nat"` and `@{term "a <= b <= c"}` with `Inner lexical
  error`. Use plain cartouches `\<open>...\<close>` for code-ish prose there.
  The error is reported against the whole `text` command, which makes it look far
  worse than it is.
- **`obtain x where ... by (rule some_obtains_lemma)` leaves ONE residual goal**
  of the shape `!!D. (!!D. P D ==> thesis) ==> P D ==> thesis`; append a method:
  `by (rule countable_dense_setE) blast`. (Earlier notes said `by (rule L)` "does
  not work" — more precisely, it does not FINISH.)
- **A line-range `edit` with empty `old_text` silently DESTROYS the tail of the
  range — and I hit this twice.** The second time it truncated the lemma
  `exists_null_sphere` mid-statement, and the only symptom was
  `Undefined fact: "exists_null_sphere"` reported at the *next* lemma, 30 lines
  below. ALWAYS `read` the exact range immediately before a line-range edit, and
  when a fact defined earlier in the same file is reported undefined, suspect a
  clobbered range rather than a naming problem.
- **`simp` mangles `ennreal`/`max` goals; go explicit.** Two separate failures in
  one proof: `simp` rewrote `ennreal (max 0 (|g x| - K))` by DROPPING the `max`,
  and it reassociated `ennreal (c * h x)` into `ennreal (h x / d)` before
  `ennreal_mult'` could fire. Fix both by stating the step as a calculation with
  `ennreal_leI`, `ennreal_plus[OF max.cobounded1 K]`, and
  `ennreal_mult'[OF nn]` applied by `rule`, never by `simp add:`.
- **`emeasure M (space M) < top` is `finite_emeasure_space less_top by blast`,
  not `simp`.** `by (simp add: less_top)` and `top.not_eq_extremum` both fail;
  sledgehammer found the `blast` form in 5 s. A reminder that `try0`/
  `sledgehammer` beats a third guess.
- **`obtains` under-constrains types silently.** `obtains L k where
  "strict_mono k" ... "norm (F (k m) t - L t) < e"` gives `k :: 'a => nat`, not
  `nat => nat`, because nothing in the body pins the domain (`strict_mono` is
  polymorphic and `m` only needs `order`). PIDE says "Introduced fixed type
  variable(s) 'c" as a WARNING and the failure surfaces much later as a
  `Type unification failed` on `that[OF ...]`. Fix: annotate in the statement,
  `obtains L and k :: "nat => nat" where ...`. Treat that warning as an error.
- **Eliminating an `obtains`-theorem with `obtain ... by (rule thm)` can trigger
  higher-order unification** and produce garbage like `F (?m6 (k m))`, or make
  `blast` diverge. Robust fix: use it as an elimination rule instead, with the
  parameters FIXED:
  `show ?thesis proof (rule thm[OF ...]) fix L and k :: "nat => nat" assume ...
   show thesis by (rule that[OF ...]) qed`. No schematics, no HO unification.
- **`by (rule mult_left_mono)` needs the premises in the order
  `a <= b`, then `0 <= c`.** `using c by (simp add: mult_left_mono)` fails on
  `c * x <= c * (e/(c+1))` because simp reassociates the RHS to `c * e / (c+1)`
  first; `using c by (rule mult_left_mono)` closes it.
- **A line-range `edit` with empty `old_text` replaces the WHOLE range**,
  including lines you meant to keep. It silently ate a `have` and glued `qed`
  to `end` ("qedend"). Re-`read` the range before and after.
- **MCP `edit` needs `old_text` in PIDE's UNICODE rendering**, not the `\<open>`
  escapes stored on disk. With escapes it reports "old_text mismatch" and echoes
  the unicode form — copy that. Its success echo returns the WHOLE file, which
  blows the tool output limit on a 3000-line theory, so read the outcome with
  `get_state`, not the edit result.
- **PIDE red + batch build green means a STALE BUFFER, every time.** Symptom: a
  batch of `Undefined fact: "..."` errors in a CHILD theory while
  `isabelle build` is clean. Cause: a parent was edited outside MCP. Fix:
  re-`read` the PARENT (a 4-line range suffices), poll `get_state` once, and the
  errors vanish. Do NOT "fix" the child. This fired twice in one session.
- **`get_state` overflows the output limit only WHILE the chain is loading** (the
  `commands_unprocessed` and warning arrays carry full source). Once loading
  finishes the same call is ~10 KB even for a 3000-line theory. If it does
  overflow, the dump is saved to a file whose lines are too long for `Read` —
  slice it with `python3 -c "import json; d=json.load(open(p)); print(d['errors']['count'])"`.
- **Anchoring successive inserts on the same section header silently REVERSES
  their order.** Each new block lands immediately before the anchor, so the block
  added last ends up first. This put a theorem before the lemma it depended on and
  produced a confusing `Undefined fact`. Anchor on the previous block's last line,
  or append at the end and reorder deliberately.
- **`[of a b c]` binds schematics in order of FIRST APPEARANCE in the statement,
  not in `fixes` order.** `norm_conj_diff_le[of M Q D]` silently instantiated
  `Q := M, D := Q, M := D`. Use `[where M = ... and Q = ...]`.
- **Build TIMINGS are unreliable while PIDE is reprocessing.** A 25 s build read
  1:52 because PIDE was re-checking a 6700-command chain concurrently (cpu time
  2:15 -> 4:54 for the same work). I misattributed this to `smt`, then to my own
  proofs, before spotting the contention. Kill competing processes before
  concluding a proof is slow.
- **`grep 'sorry\|oops'` FALSE-POSITIVES on the word "loops".** Use `grep -cw`.
  My "no sorry" claims rested on the broken check for several turns.
- **`simp` will not close `sum` goals of the form
  `sum_j f j * (if j = i then 1 else 0)`** — pull the `if` out with an explicit
  `sum.cong` step first, then `sum.delta` applies. Use `inner_axis'` for axis
  inner products; plain `inner_axis` does not fire.
- **`sum.mono_neutral_right` already goes `B -> U`**; adding `[symmetric]` sends
  it the wrong way. For interval reindexing prefer
  `sum.reindex_bij_witness[where i = "\<lambda>i. i - 1" and j = Suc]`, which is
  immune to the numeral normalisation that breaks
  `sum.shift_bounds_cl_Suc_ivl` under `simp`.
- **`spectral_decomposition` LOOPS as a rewrite rule** — its right-hand side
  mentions `a` again, so `unfolding adecomp` raises
  `exception Interrupt_Breakdown`. Bind the eigenvalues first:
  `define lam where "lam = (\<lambda>v. v \<bullet> (a *v v))"`. Same trap with
  `eig[OF u]` and with any `foo_def` whose RHS contains its own LHS.
- **A DEFINITION unfolds all occurrences and beats a specific instance.**
  `unfolding lamq lam_def` rewrote `lam q` via `lam_def` rather than via the
  instance `lamq`. Supply instances only (`unfolding lamq lu`), never the
  definition alongside them.

- **New theory files cannot be loaded into PIDE in this setup.** The header
  reports a bare `Malformed theory` and every later command cascades into
  `Inner lexical error / Failed to parse type` (no theory context, so
  `real^'n^'n` will not parse). Those cascades are ARTIFACTS. Develop new files
  against the batch build (~22 s warm, reports all errors at once) and use PIDE
  only for files it already holds.
- **PIDE cannot hold the Envelopes chain and the Eigenvalues chain at once.**
  It evicts one and queues forever. This is why `Lemma_3_1.thy` imports
  `Threshold_Chain` and NOT `Envelopes`: `ell_op` / `feasible` already come from
  `Relative_Arbitrage_PDE` via the Eigenvalues chain, and the only Envelopes-side
  fact needed was `trace_conjugate`, reproved locally as `trace_conj`.
- **`spectral_decomposition` loops as a rewrite rule**: its RHS mentions `a`
  again, so `unfolding adecomp` raises `exception Interrupt_Breakdown`. Bind the
  eigenvalues first: `define lam where "lam = (%v. v . (a *v v))"`, then state
  the decomposition in terms of `lam`. Same trap with `eig[OF u]`.
- **`unfolding foo_def` unfolds EVERY occurrence**, including on the goal's RHS.
  Symptom: the closing `qed` fails with "Failed to refine any pending goal" while
  every inner step checks. Always instantiate: `unfolding kyfan_def[of m A]`.
- **`simp add: eigval_1` fails silently** because simp rewrites the literal
  `1::nat` to `Suc 0` in the goal but not in the rule. State the instance as a
  named `have` and close with `unfolding`.
- **`blast` can diverge inside an induction**: with the IH and all of
  `Suc.prems` in scope it searches instead of eliminating. In
  `Threshold_Chain.thy` this ran 2.7 s and climbing versus 152 ms for the whole
  file once replaced. Introduce existentials with
  `by (rule exI[of _ t]) (intro conjI f1 f2 f3)`, eliminate with
  `obtain x where xP: "P x & Q x" using ex by (rule exE)`, and project each
  conjunct with its own `using xP by simp`.
- **`obtains` lemmas used inside `obtain`**: `by (rule L)` does not work; `by
  metis` diverges when one conclusion is a `!!`-statement. Prefer stating helper
  lemmas with an EXISTENTIAL conclusion.
- **`sum.mono_neutral_right` already goes `B -> U`.** Adding `[symmetric]` sends
  it the wrong way and leaves goals `finite U` and `B <= U`.
- **PIDE flags slow steps with a stale first reading.** The same command read
  2 ms on one poll and 2704 ms on the next. Poll twice and compare `timing_ms`
  before concluding a step is fine.
- **`isabelle build` emits no partial output, and duration says nothing about
  looping.** Adding a theory to ROOT invalidates the session image, so
  everything re-checks (10-40 min with an empty log). Do not infer "looping
  proof" from a long silent build. `timeout N isabelle build` does not work
  either -- it kills the wrapper, not the `poly` children; use
  `pkill -f "[p]oly"`.
- Facts that do NOT exist in this HOL-Analysis and must be proved locally:
  `transpose_diff`, `scaleR_matrix_matrix`, `trace_scaleR`,
  `(A - B) *v x = A *v x - B *v x`, `A ** (B - C)` and `(A - B) ** C`,
  `trace (A - B) = trace A - trace B`, `trace (sum f S) = sum (trace o f) S`,
  `card_UNIV_pos` (use `by (simp add: card_gt_0_iff)`), `scaleR_right_commute`.
  Ones that DO exist: `matrix_transpose_mul`, `trace_mul_sym`,
  `matrix_add_rdistrib`, `trace_add`, `matrix_vector_mul_assoc`, `matrix_eq`,
  `transpose_mat`, `trace_I`, `outer_prod_mv`, `onormal_complete`,
  `onormal_card_dim_span`, `dim_sums_Int` (in ADDITIVE form:
  `dim {x+y|..} + dim (S inter W) = dim S + dim W`), `dim_eq_0` (apply
  explicitly, `auto` will not use it).
- `nlinarith` does NOT exist in this Isabelle (a development snapshot). Use
  `linarith` plus explicit monotonicity steps.
