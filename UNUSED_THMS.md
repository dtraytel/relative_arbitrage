# Theorems reported unused by `unused_thms`

From Isabelle's own proof-term analysis, not a textual scan. Run from a theory
importing `Statement/Theorem_1_1_Statement.thy`:

```
ML \<open>
  val base = map Thy_Info.get_theory
    ["HOL-Probability.Probability", "Martingales.Martingale"];
  val res = Thm_Deps.unused_thms_cmd (base, [@{theory}]);
\<close>
```

That reports 3126 facts. Only the ones below are actionable, and the filtering
matters:

* **Keep only theory-qualified names** (`Theory.fact`), where `Theory` is one
  of ours and the fact is declared in that very file: 288 facts.
* **Discard the locale-qualified ones** (`Theory.Locale.fact`): 1316 of them
  sit under our theory names. Most are facts inherited through
  `interpretation` and belong to the AFP sessions, not here. They cannot be
  matched back to a declaration by short name --- a locale-inherited
  `Foo.BM.trace_bound_pointwise` being unused says nothing about the
  `trace_bound_pointwise` this repository declares, which is used. Acting on a
  short-name match deletes live lemmas; that mistake was made once and
  reverted.

Ten of the entries are in `Statement/Theorem_1_1_Statement.thy` and are unused
*by construction* --- they are the clauses of Theorem 1.1, which nothing is
supposed to consume. The `Alexandrov_Sup_Convolution`, `Path_Space_Tightness`,
`Martingale_Sampling` and `Wiener_Measure` entries are in general-purpose
toolboxes, where an unused lemma is not obviously waste.

Deleting one of these can make its private helpers unused in turn, so the list
has to be regenerated after each pass until it reaches a fixpoint. Nothing on
this list has been deleted.


## Relative_Arbitrage/Comparison_Principle.thy (77)

- `test_grad_at_point` (line 361)
- `ell_op_scaled_strict` (line 495)
- `doubling_partial_max_fst` (line 607)
- `doubling_partial_min_snd` (line 617)
- `doubling_viscosity_inequalities` (line 762)
- `frozen_hessians_not_ordered` (line 797)
- `comparison_contradiction` (line 860)
- `ell_op_envelope_sandwich` (line 918)
- `ell_op_lsc_elliptic_le` (line 959)
- `ell_op_env_sandwich` (line 1066)
- `doubling_grad_zero_iff` (line 1105)
- `doubling_diff_nonzero_gen` (line 1275)
- `doubling_ge_diagonal_gen` (line 1303)
- `doubling_max_antimono` (line 1329)
- `doubling_dist_tendsto` (line 1362)
- `env_gap_at_zero_nonneg` (line 1406)
- `env_contradiction_at_zero` (line 1418)
- `strict_contradiction_of_shifts_any_p` (line 1486)
- `doubling_maximiser_with_bounds` (line 1647)
- `doubling_complete` (line 1710)
- `ell_op_lsc_le_one_of_shifts` (line 2013)
- `ell_op_usc_ge_one_of_shifts` (line 2076)
- `supersol_shifted_bound_onesided_ne` (line 2419)
- `quartic_pen_grad_zero_iff` (line 2506)
- `quartic_pen_jet` (line 2555)
- `quartic_pen_vanishing_jet_at_zero` (line 2579)
- `sqrt_second_order_quotient` (line 3017)
- `soft_grad_zero` (line 3828)
- `soft_hess_zero` (line 3834)
- `soft_grad_norm_pos` (line 3886)
- `doubled_supconv_jet_exists_gen` (line 4018)
- `supersol_no_vanishing_jet` (line 4587)
- `comparison_env_from_jets_offdiag` (line 4658)
- `sums_gives_psd` (line 4738)
- `shifted_centre_gap` (line 4976)
- `shifted_jensen_smallness` (line 4991)
- `shifted_centre_value` (line 5044)
- `antisym_tilt_grad_lower_bound` (line 5066)
- `jet_transfer_linear` (line 5119)
- `doubled_jet_no_gradient` (line 5589)
- `common_gradient_split` (line 5608)
- `comparison_env_complete_offdiag` (line 5673)
- `norm_slice_fst` (line 5769)
- `norm_slice_snd` (line 5774)
- `comparison_from_doubled_jet` (line 6166)
- `comparison_supconv_from_doubled_jet` (line 6451)
- `env_strict_contradiction_of_tilt_families` (line 6724)
- `antisym_tilt_aligns_gradients` (line 6800)
- `semiconvex_hessian_abs_bound` (line 6856)
- `nearby_of_bounded_family` (line 7023)
- `doubling_grad_lower_bound_supconv` (line 7114)
- `doubling_maximiser_supconv` (line 7150)
- `env_strict_contradiction_of_limits` (line 7337)
- `gradient_sequences_align_of_bound` (line 7432)
- `positive_separation_of_value_gap` (line 7813)
- `doubling_grad_lower_bound_supconv_sep` (line 7946)
- `supconv_attained_family` (line 8099)
- `supconv_usc_eventually_below` (line 8337)
- `supersol_jet_mono_dom` (line 8390)
- `soft_pen_coercive` (line 8998)
- `doubling_maximiser_supconv_soft` (line 9244)
- `choice2` (line 9692)
- `choice3` (line 9697)
- `family_of_tilt_construction_shrinking` (line 10003)
- `quadform_matrix_bound` (line 10212)
- `psd_shifted_diff` (line 10331)
- `matrix_add_scaleR_id` (line 10347)
- `doubled_value_gap_supconv` (line 10449)
- `tilted_shifted_jet_slices` (line 10631)
- `comparison_supconv_doubling_complete` (line 11138)
- `comparison_supconv_maximiser_complete` (line 11342)
- `max_principle_boundary_counterexample` (line 12477)
- `comparison_compact` (line 13493)
- `comparison_failure_gives_theta` (line 14041)
- `supconv_attain_gate_open` (line 14084)
- `doubled_maximiser_in_gate` (line 14101)
- `two_domain_doubled_maximiser` (line 14125)

## Relative_Arbitrage/Exit_Class_DPP.thy (30)

- `pexit_pfut` (line 1088)
- `exit_class_future_of_past` (line 1984)
- `survival_event_filtration` (line 2049)
- `pfut_increment` (line 3081)
- `pexit_split_pshift_pfut` (line 5419)
- `exit_val_dpp` (line 5775)
- `kglue_law'_rcd_eq` (line 6131)
- `exit_val_dpp_sup_ge_two` (line 7029)
- `exit_val_dpp_ge_const_list` (line 7406)
- `pafter_zero` (line 7588)
- `pstopped_after` (line 7603)
- `exit_class_rcd_stopping` (line 8093)
- `pafter_eq_pembed` (line 8160)
- `prebase_pafter` (line 8182)
- `pafter_pstopped` (line 8317)
- `prob_space_distr_prebase` (line 8398)
- `AE_rcd_stopping_start_zero` (line 8434)
- `AE_rcd_stopping_diffquot` (line 8856)
- `pre_sigma_of_const` (line 9034)
- `pre_sigma_of_simple_partition` (line 9090)
- `path_stopping_time_event` (line 9647)
- `exit_class_stopped_increment` (line 9959)
- `exit_class_rcd_X_increment_zero` (line 10891)
- `exit_class_rcd_comp_increment_zero` (line 11239)
- `padd_pstopped_pafter` (line 11685)
- `pstopped_padd` (line 11752)
- `pafter_padd` (line 11789)
- `pembed_continuous_map` (line 14235)
- `integrable_ksemi_fst` (line 16602)
- `integrable_ksemi_of_bound` (line 16631)

## Alexandrov_Sup_Convolution/Sup_Convolution.thy (26)

- `supconv_tendsto` (line 300)
- `minty_surjective` (line 717)
- `ftc_along_line` (line 1395)
- `ddir_lipschitz_in_direction` (line 1495)
- `negligible_no_dderiv_countable` (line 1535)
- `ddir_add_of_shifted_limit` (line 1714)
- `L1_dquot_tendsto` (line 2163)
- `content_box_translate` (line 2246)
- `ennreal_mult_indicator_eq` (line 2663)
- `moreau_twice_differentiable_AE` (line 3625)
- `moreau_alexandrov_AE` (line 3863)
- `second_difference_symmetric` (line 3895)
- `moreau_second_difference_integral` (line 3901)
- `moreau_alexandrov_sym_AE` (line 4284)
- `perturbed_maximiser_interior` (line 5360)
- `interior_max_subdiff` (line 5493)
- `doubling_ge_diagonal` (line 5928)
- `doubling_antitone` (line 5959)
- `doubling_penalty_tendsto_zero` (line 5980)
- `antitone_bdd_below_convergent_at_top` (line 6020)
- `supconv_jensen_alexandrov_point` (line 6118)
- `block_diagonal_test` (line 6301)
- `second_order_form_unique` (line 6775)
- `doubling_limit_maximises` (line 7111)
- `supconv_neg_jet_transfer` (line 7337)
- `sums_ord_of_inequality` (line 7361)

## Relative_Arbitrage/Exit_Class_Compactness.thy (14)

- `stopped_market_acont_in_sconstraint` (line 34)
- `stopped_market_Yint_diffquot_in_sconstraint` (line 188)
- `stopped_market_acov_leaves_sconstraint` (line 237)
- `ploc_le_T` (line 1558)
- `exit_class_trace_martingale` (line 6242)
- `space_pglue_law` (line 7011)
- `exit_val_paste_lower` (line 8607)
- `space_kglue_law` (line 8900)
- `cross_borel` (line 9658)
- `theorem_1_1_paper_v_fragment` (line 10495)
- `space_kglue_law'` (line 12081)
- `kglue_law'_start` (line 12205)
- `kglue_law'_diffquot` (line 12245)
- `borel_of_path_prod` (line 12310)

## Relative_Arbitrage/Value_Function_Viscosity.thy (14)

- `ell_op_le_one_of_witness` (line 58)
- `exit_class_feasible_freezes_gradient` (line 660)
- `ell_op_s_le_ell_op` (line 753)
- `exit_val_subsol_quadratic_global` (line 781)
- `trace_eq_sum_axis` (line 3094)
- `matrix_norm_le_sum_abs` (line 5064)
- `transpose_kill` (line 6675)
- `exit_val_supersol_env_case1` (line 10013)
- `lsc_env_attains_inf` (line 13405)
- `exit_val_case2_tilt_step` (line 13920)
- `tanpV_feasible` (line 15463)
- `tanpV_idem` (line 15501)
- `tanpV_radial_kill` (line 15545)
- `tanpV_trace_projmat` (line 16372)

## Relative_Arbitrage/Operator_Envelopes.thy (10)

- `mem_ball_self` (line 59)
- `ell_op_lsc_at_zero_iff` (line 554)
- `ball_v_visc_sol_env` (line 669)
- `hh_orth` (line 822)
- `halfspace_open` (line 1217)
- `halfspace_nonzero` (line 1226)
- `usc_extension_bounded` (line 2431)
- `ell_op_hess_scale` (line 2547)
- `visc_subsol_env_mono` (line 3011)
- `visc_subsol_at_local_min` (line 3651)

## Statement/Theorem_1_1_Statement.thy (10)

- `uncapped_value_function_agrees` (line 97)
- `convex_sets_are_expandable` (line 139)
- `clause_0_finite` (line 158)
- `clause_1_upper_semicontinuous` (line 167)
- `clause_2_subsolution` (line 178)
- `clause_2_supersolution` (line 196)
- `clause_3_boundary_subsolution` (line 213)
- `clause_3_boundary_supersolution` (line 221)
- `clause_4_uniqueness` (line 243)
- `example_3_1_closed_form` (line 264)

## Path_Space_Tightness/Path_Tightness.thy (9)

- `path_laws_convergent_subsequence` (line 336)
- `path_laws_diagonal_consistent` (line 795)
- `path_law_limit_moment_bound` (line 991)
- `projective_limit_of_consistent_path_laws` (line 1074)
- `lim_coordinate_moment_bound` (line 1274)
- `dyadic_ext_dyadic` (line 1520)
- `dyadic_ext_continuous_on` (line 1596)
- `lim_continuous_modification` (line 2313)
- `flip_measurable` (line 2430)

## Relative_Arbitrage/Exit_Time_Semicontinuity.thy (8)

- `essinf_etime_usc` (line 78)
- `mkt_law_closure_finite` (line 1033)
- `covariation_test_nonneg` (line 2967)
- `stopped_exit_vals_nonempty` (line 3032)
- `mkt_law_closure_increment_event` (line 3806)
- `mkt_law_closure_sq_increment_event` (line 3898)
- `stopped_val_fn_finite_bounded` (line 4046)
- `stopped_val_fn_boundary_zero` (line 4059)

## Relative_Arbitrage/Viscosity_Solutions.thy (8)

- `closure_ball_minus_zero` (line 126)
- `ball_v_unique_on_cball` (line 408)
- `comparison_ball_zero_boundary` (line 479)
- `uniqueness_ball` (line 505)
- `visc_subsol_le_smooth_strict` (line 548)
- `smooth_strict_le_visc_supersol` (line 598)
- `feasible_trace_bound` (line 695)
- `feasible_bounded` (line 795)

## Relative_Arbitrage/Operator_Envelope_Continuity.thy (7)

- `ell_op_envelopes_eq_off_zero` (line 467)
- `ell_op_lsc_off_zero_iff` (line 548)
- `ell_op_pinched` (line 579)
- `ell_op_strict_no_crossing_env` (line 615)
- `ell_op_lsc_at_zero_eq` (line 646)
- `uniqueness_from_max_principle` (line 760)
- `max_principle_boundary_intro` (line 788)

## Relative_Arbitrage/Poincare_Separation.thy (7)

- `box_program_bound_exact` (line 966)
- `trace_expand_adapted` (line 1360)
- `ell_op_eq_eigval_sum` (line 1804)
- `ell_op_eq_half_bracket_sym_part` (line 2881)
- `norm_transpose_matrix` (line 3066)
- `feasible_empty_of_large_degeneracy` (line 3440)
- `closed_feasible` (line 3776)

## Relative_Arbitrage/Value_Function_Uniqueness.thy (7)

- `theorem_1_1_ball_fragment` (line 21)
- `comparison_principle_refuted` (line 100)
- `theorem_1_1_uniqueness_general` (line 138)
- `stopped_val_fn_ball_eq_2d` (line 195)
- `exit_val_unique_viscosity_solution` (line 286)
- `iexit_val_supersol_lsc` (line 870)
- `iexit_val_supersol_bc` (line 911)

## Relative_Arbitrage/Exit_Class.thy (6)

- `compact_sconstraint` (line 230)
- `diffquot_of_density_in_sconstraint` (line 716)
- `sconstraint_nonempty` (line 789)
- `Yint_0` (line 900)
- `exit_class_density_ae` (line 996)
- `pair_holder_charge_split` (line 1609)

## Relative_Arbitrage/Value_Function_Market.thy (6)

- `ess_inf_time_ge_zero` (line 33)
- `ess_inf_time_mono` (line 187)
- `ess_inf_time_superadd` (line 202)
- `val_fn_ge_zero` (line 259)
- `mkt_exit_vals_nonempty` (line 266)
- `val_fn_zero_on_frontier_ball` (line 479)

## Relative_Arbitrage/Exit_Class_Infinite.thy (5)

- `iexit_le` (line 91)
- `ess_inf_enn_ge_zero` (line 114)
- `iexit_class_pcut_measurable` (line 215)
- `pcut_pglue` (line 531)
- `exit_val_le_iexit_val` (line 1227)

## Relative_Arbitrage/Deterministic_Radius_Market.thy (4)

- `bm_increment_cond_exp_AE` (line 261)
- `drN_event_integrable` (line 2310)
- `drC2_cos2` (line 2685)
- `coord_Z_drX_meas_neg` (line 2834)

## Path_Space_Tightness/Increment_Moments.thy (4)

- `increment_second_moment_bound` (line 78)
- `pow4_binomial` (line 212)
- `sq_times_sq` (line 892)
- `sq_tail_bound_of_fourth_moment` (line 2137)

## Relative_Arbitrage/Eigenvalues.thy (3)

- `kyfan_ge_of_eigen_lb` (line 485)
- `kyfan_le_of_eigen_ub` (line 531)
- `possum_nonneg` (line 1126)

## Path_Space_Tightness/Equicontinuity.thy (3)

- `holder_family_subsequence_dist` (line 182)
- `holder_onI_bound` (line 220)
- `usc_sup_over_compact` (line 258)

## Relative_Arbitrage/Viscosity_Comparison_Interface.thy (3)

- `ell_op_orth_equivariant` (line 309)
- `ell_op_geometric` (line 446)
- `ball_v_unique_solution` (line 500)

## Relative_Arbitrage/Brownian_Continuous.thy (2)

- `bm2_expected_square` (line 453)
- `ito_const_horizon_market_nonvacuous` (line 595)

## Wiener_Measure/Brownian_Motion.thy (2)

- `gauss_measure_conv` (line 267)
- `bm_increments_indep` (line 1174)

## Relative_Arbitrage/Constraint_Set_Convexity.thy (2)

- `lemma_2_1` (line 1110)
- `support_characterisation` (line 1131)

## Relative_Arbitrage/Curvature_Operator.thy (2)

- `ball_v_hessian` (line 571)
- `ball_solves_pde` (line 596)

## Relative_Arbitrage/Modification_Transfer.thy (2)

- `cylset_space` (line 37)
- `adapted_process_natural_filtration_of` (line 675)

## Path_Space_Tightness/Modulus_Tails.thy (2)

- `dyadic_level_tail` (line 127)
- `dyadic_bad_event_tail` (line 304)

## Relative_Arbitrage/Operator_Continuity.thy (2)

- `transpose_mat_one` (line 66)
- `ell_op_Mp` (line 339)

## Relative_Arbitrage/Brownian_Market.thy (1)

- `bm_compensator_coord` (line 2054)

## Relative_Arbitrage/Brownian_Optimal_Boundary.thy (1)

- `optimal_exit_time_value_boundary` (line 92)

## Relative_Arbitrage/Eigenvalue_Bound_Exact.thy (1)

- `lemma_2_1_eq` (line 779)

## Relative_Arbitrage/Exit_Semicontinuity.thy (1)

- `ess_inf_pexit_cap_invisible` (line 155)

## Relative_Arbitrage/Exit_Time.thy (1)

- `eroded_mono` (line 156)

## Path_Space_Tightness/Increment_Tails.thy (1)

- `partition_max_tail_bound` (line 99)

## Path_Space_Tightness/Path_Space_Infinite.thy (1)

- `sets_ipath_law` (line 100)

## Martingale_Sampling/Quadratic_Variation.thy (1)

- `qvar_nonneg` (line 102)

## Martingale_Sampling/Sampled_Martingale.thy (1)

- `martingale_of_cond_increment` (line 113)

## Martingale_Sampling/Sampled_Quadratic_Variation.thy (1)

- `qvar_compensates_sampled` (line 60)

## Relative_Arbitrage/Stopped_Localization.thy (1)

- `AE_restrict_full` (line 650)

## Martingale_Sampling/Time_Discretisation.thy (1)

- `grid_expected_qvar_indep` (line 151)

## Martingale_Sampling/Vitali_Convergence.thy (1)

- `unif_integrable_of_moment_bound` (line 339)
