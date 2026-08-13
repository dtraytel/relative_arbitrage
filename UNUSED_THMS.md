# Theorems reported unused by `unused_thms`

From Isabelle's own proof-term analysis. Run from a theory importing
`Statement/Theorem_1_1_Statement.thy`:

```
ML \<open>
  val base = map Thy_Info.get_theory
    ["HOL-Probability.Probability", "Martingales.Martingale"];
  val res = Thm_Deps.unused_thms_cmd (base, [@{theory}]);
\<close>
```

That reports 3126 facts, of which 288 are actionable. **181 of them have been
deleted** (about 4600 lines, 26 files); the remaining 107 are listed below with
the reason each was kept.

## How the list has to be filtered

Three filters, and all three earned their place by a mistake:

1. **Theory-qualified names only** (`Theory.fact`, declared at top level in
   that very file). The 1316 locale-qualified reports (`Theory.Locale.fact`)
   under our theory names are mostly facts inherited through `interpretation`
   and belong to the AFP sessions. Matching those back by short name conflates
   an inherited copy with the original: `Foo.BM.trace_bound_pointwise` being
   unused says nothing about the `trace_bound_pointwise` declared here, which
   is used.
2. **No textual reference anywhere else.** `unused_thms` answers "does a proof
   term use this fact", not "does the source name it". A fact listed in a
   `simp add:` that simp did not need leaves no proof term, so it is reported
   unused --- and deleting it still breaks the build with `Undefined fact`.
   `Poincare_Separation.transpose_mat_one` is exactly that. The same filter
   catches names surviving in `@{thm [source] ...}` antiquotations and in
   prose.
3. **Paper-specific sessions only.** An unused lemma in
   `Alexandrov_Sup_Convolution`, `Path_Space_Tightness`, `Martingale_Sampling`
   or `Wiener_Measure` is not obviously waste --- those are general toolboxes.

When deleting, note also that a lemma block runs to the next top-level command,
which swallows the `(*<*)` before a closing `end` unless trailing blank and
comment-marker lines are trimmed back.

Deleting one lemma can make its private helpers unused in turn, so the list
should be regenerated after each pass until it reaches a fixpoint. This is the
state after one pass.


## Kept: the deliverable (10)

- `clause_0_finite` --- `Statement/Theorem_1_1_Statement.thy`
- `clause_1_upper_semicontinuous` --- `Statement/Theorem_1_1_Statement.thy`
- `clause_2_subsolution` --- `Statement/Theorem_1_1_Statement.thy`
- `clause_2_supersolution` --- `Statement/Theorem_1_1_Statement.thy`
- `clause_3_boundary_subsolution` --- `Statement/Theorem_1_1_Statement.thy`
- `clause_3_boundary_supersolution` --- `Statement/Theorem_1_1_Statement.thy`
- `clause_4_uniqueness` --- `Statement/Theorem_1_1_Statement.thy`
- `convex_sets_are_expandable` --- `Statement/Theorem_1_1_Statement.thy`
- `example_3_1_closed_form` --- `Statement/Theorem_1_1_Statement.thy`
- `uncapped_value_function_agrees` --- `Statement/Theorem_1_1_Statement.thy`

## Kept: general-purpose toolbox (53)

- `L1_dquot_tendsto` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `antitone_bdd_below_convergent_at_top` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `block_diagonal_test` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `content_box_translate` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `ddir_add_of_shifted_limit` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `ddir_lipschitz_in_direction` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `doubling_antitone` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `doubling_ge_diagonal` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `doubling_limit_maximises` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `doubling_penalty_tendsto_zero` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `ennreal_mult_indicator_eq` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `ftc_along_line` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `interior_max_subdiff` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `minty_surjective` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `moreau_alexandrov_AE` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `moreau_alexandrov_sym_AE` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `moreau_second_difference_integral` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `moreau_twice_differentiable_AE` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `negligible_no_dderiv_countable` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `perturbed_maximiser_interior` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `second_difference_symmetric` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `second_order_form_unique` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `sums_ord_of_inequality` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `supconv_jensen_alexandrov_point` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `supconv_neg_jet_transfer` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `supconv_tendsto` --- `Alexandrov_Sup_Convolution/Sup_Convolution.thy`
- `qvar_nonneg` --- `Martingale_Sampling/Quadratic_Variation.thy`
- `martingale_of_cond_increment` --- `Martingale_Sampling/Sampled_Martingale.thy`
- `qvar_compensates_sampled` --- `Martingale_Sampling/Sampled_Quadratic_Variation.thy`
- `grid_expected_qvar_indep` --- `Martingale_Sampling/Time_Discretisation.thy`
- `unif_integrable_of_moment_bound` --- `Martingale_Sampling/Vitali_Convergence.thy`
- `holder_family_subsequence_dist` --- `Path_Space_Tightness/Equicontinuity.thy`
- `holder_onI_bound` --- `Path_Space_Tightness/Equicontinuity.thy`
- `usc_sup_over_compact` --- `Path_Space_Tightness/Equicontinuity.thy`
- `increment_second_moment_bound` --- `Path_Space_Tightness/Increment_Moments.thy`
- `pow4_binomial` --- `Path_Space_Tightness/Increment_Moments.thy`
- `sq_tail_bound_of_fourth_moment` --- `Path_Space_Tightness/Increment_Moments.thy`
- `sq_times_sq` --- `Path_Space_Tightness/Increment_Moments.thy`
- `partition_max_tail_bound` --- `Path_Space_Tightness/Increment_Tails.thy`
- `dyadic_bad_event_tail` --- `Path_Space_Tightness/Modulus_Tails.thy`
- `dyadic_level_tail` --- `Path_Space_Tightness/Modulus_Tails.thy`
- `sets_ipath_law` --- `Path_Space_Tightness/Path_Space_Infinite.thy`
- `dyadic_ext_continuous_on` --- `Path_Space_Tightness/Path_Tightness.thy`
- `dyadic_ext_dyadic` --- `Path_Space_Tightness/Path_Tightness.thy`
- `flip_measurable` --- `Path_Space_Tightness/Path_Tightness.thy`
- `lim_continuous_modification` --- `Path_Space_Tightness/Path_Tightness.thy`
- `lim_coordinate_moment_bound` --- `Path_Space_Tightness/Path_Tightness.thy`
- `path_law_limit_moment_bound` --- `Path_Space_Tightness/Path_Tightness.thy`
- `path_laws_convergent_subsequence` --- `Path_Space_Tightness/Path_Tightness.thy`
- `path_laws_diagonal_consistent` --- `Path_Space_Tightness/Path_Tightness.thy`
- `projective_limit_of_consistent_path_laws` --- `Path_Space_Tightness/Path_Tightness.thy`
- `bm_increments_indep` --- `Wiener_Measure/Brownian_Motion.thy`
- `gauss_measure_conv` --- `Wiener_Measure/Brownian_Motion.thy`

## Kept: still named in the source (44)

- `bm_compensator_coord` --- `Relative_Arbitrage/Brownian_Market.thy`
- `comparison_contradiction` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `comparison_supconv_doubling_complete` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `comparison_supconv_maximiser_complete` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `doubled_value_gap_supconv` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `doubling_grad_lower_bound_supconv` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `doubling_maximiser_supconv` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `doubling_maximiser_supconv_soft` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `doubling_partial_max_fst` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `doubling_partial_min_snd` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `ell_op_lsc_elliptic_le` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `env_strict_contradiction_of_limits` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `gradient_sequences_align_of_bound` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `max_principle_boundary_counterexample` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `positive_separation_of_value_gap` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `psd_shifted_diff` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `semiconvex_hessian_abs_bound` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `shifted_jensen_smallness` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `soft_grad_norm_pos` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `strict_contradiction_of_shifts_any_p` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `supersol_no_vanishing_jet` --- `Relative_Arbitrage/Comparison_Principle.thy`
- `coord_Z_drX_meas_neg` --- `Relative_Arbitrage/Deterministic_Radius_Market.thy`
- `pair_holder_charge_split` --- `Relative_Arbitrage/Exit_Class.thy`
- `stopped_market_acov_leaves_sconstraint` --- `Relative_Arbitrage/Exit_Class_Compactness.thy`
- `exit_class_future_of_past` --- `Relative_Arbitrage/Exit_Class_DPP.thy`
- `kglue_law'_rcd_eq` --- `Relative_Arbitrage/Exit_Class_DPP.thy`
- `pafter_padd` --- `Relative_Arbitrage/Exit_Class_DPP.thy`
- `pstopped_padd` --- `Relative_Arbitrage/Exit_Class_DPP.thy`
- `pcut_pglue` --- `Relative_Arbitrage/Exit_Class_Infinite.thy`
- `mkt_law_closure_increment_event` --- `Relative_Arbitrage/Exit_Time_Semicontinuity.thy`
- `mkt_law_closure_sq_increment_event` --- `Relative_Arbitrage/Exit_Time_Semicontinuity.thy`
- `transpose_mat_one` --- `Relative_Arbitrage/Operator_Continuity.thy`
- `ell_op_envelopes_eq_off_zero` --- `Relative_Arbitrage/Operator_Envelope_Continuity.thy`
- `uniqueness_from_max_principle` --- `Relative_Arbitrage/Operator_Envelope_Continuity.thy`
- `ell_op_lsc_at_zero_iff` --- `Relative_Arbitrage/Operator_Envelopes.thy`
- `usc_extension_bounded` --- `Relative_Arbitrage/Operator_Envelopes.thy`
- `ess_inf_time_mono` --- `Relative_Arbitrage/Value_Function_Market.thy`
- `mkt_exit_vals_nonempty` --- `Relative_Arbitrage/Value_Function_Market.thy`
- `theorem_1_1_ball_fragment` --- `Relative_Arbitrage/Value_Function_Uniqueness.thy`
- `theorem_1_1_uniqueness_general` --- `Relative_Arbitrage/Value_Function_Uniqueness.thy`
- `exit_val_case2_tilt_step` --- `Relative_Arbitrage/Value_Function_Viscosity.thy`
- `exit_val_subsol_quadratic_global` --- `Relative_Arbitrage/Value_Function_Viscosity.thy`
- `ball_v_unique_solution` --- `Relative_Arbitrage/Viscosity_Comparison_Interface.thy`
- `feasible_bounded` --- `Relative_Arbitrage/Viscosity_Solutions.thy`
